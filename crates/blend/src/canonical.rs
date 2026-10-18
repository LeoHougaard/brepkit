//! Canonical analytic contacts and material-oriented blend patches.
//!
//! A rational quadratic circle is recognized by its complete Bezier control
//! net and weights, never by fitting sampled points. Keeping that support
//! analytic gives trimming, measurement and STEP the same circle/arc domain.
use crate::BlendError;
use brepkit_math::{curves::Circle3D, nurbs::NurbsCurve, vec::Point3};
use brepkit_topology::{
    Topology,
    edge::{EdgeCurve, EdgeId},
    explorer::face_edges,
    face::{FaceId, FaceSurface},
    wire::{OrientedEdge, Wire},
};
use std::collections::HashMap;

/// A clamped, positive-weight, degree-one two-point curve has exactly the
/// straight segment as its image, regardless of its rational parameterization.
#[allow(clippy::float_cmp)]
pub fn rational_line(curve: &NurbsCurve) -> bool {
    let k = curve.knots();
    curve.degree() == 1
        && curve.control_points().len() == 2
        && k.len() == 4
        && k[0] == k[1]
        && k[2] == k[3]
        && k[1] < k[2]
        && curve.weights().iter().all(|&w| w.is_finite() && w > 0.0)
}

// Knot multiplicities are exact identities in the rational Bezier encoding.
#[allow(clippy::float_cmp)]
pub fn rational_circle(curve: &NurbsCurve) -> Option<Circle3D> {
    let p = curve.control_points();
    let w = curve.weights();
    let k = curve.knots();
    if curve.degree() != 2
        || p.len() < 3
        || p.len().is_multiple_of(2)
        || w.len() != p.len()
        || k.len() != p.len() + 3
        || w[0].abs() < 1e-15
    {
        return None;
    }
    let pieces = (p.len() - 1) / 2;
    if k[0] != k[1]
        || k[1] != k[2]
        || k[k.len() - 1] != k[k.len() - 2]
        || k[k.len() - 2] != k[k.len() - 3]
    {
        return None;
    }
    let mut previous = k[2];
    for i in 0..pieces - 1 {
        let index = 3 + 2 * i;
        if k[index] != k[index + 1] || k[index] <= previous {
            return None;
        }
        previous = k[index];
    }
    if k[k.len() - 1] <= previous {
        return None;
    }
    let weight = w[1] / w[0];
    if !(0.0..1.0).contains(&weight) {
        return None;
    }
    let midpoint = Point3::new(
        f64::midpoint(p[0].x(), p[2].x()),
        f64::midpoint(p[0].y(), p[2].y()),
        f64::midpoint(p[0].z(), p[2].z()),
    );
    let center = midpoint + (midpoint - p[1]) * (weight * weight / (1.0 - weight * weight));
    let a = p[0] - center;
    let b = p[2] - center;
    let radius = a.length();
    let normal = a.cross(b).normalize().ok()?;
    if radius < 1e-9 {
        return None;
    }
    let tol = 1e-10 * radius.max(1.0)
        + 128.0 * f64::EPSILON * (center.x().abs() + center.y().abs() + center.z().abs());
    let mut angle = 0.0;
    for i in 0..pieces {
        let a = p[2 * i] - center;
        let b = p[2 * i + 2] - center;
        let weight = w[2 * i + 1] / w[0];
        if !(0.0..1.0).contains(&weight)
            || (w[2 * i] / w[0] - 1.0).abs() > 1e-12
            || (w[2 * i + 2] / w[0] - 1.0).abs() > 1e-12
        {
            return None;
        }
        if (a.length() - radius).abs() > tol
            || (b.length() - radius).abs() > tol
            || a.dot(normal).abs() > tol
            || b.dot(normal).abs() > tol
        {
            return None;
        }
        let expected = center + (a + b) * (0.5 / (weight * weight));
        if (p[2 * i + 1] - expected).length() > tol {
            return None;
        }
        let turn = normal.dot(a.cross(b)).atan2(a.dot(b));
        if turn <= 0.0 || (weight - (turn * 0.5).cos()).abs() > 1e-12 {
            return None;
        }
        angle += turn;
    }
    if angle > std::f64::consts::TAU + 1e-9 {
        return None;
    }
    Circle3D::new_with_ref(center, normal, radius, a.normalize().ok()?).ok()
}

/// Orient a toroidal blend from its actual support owners. The cap's outward
/// normal selects the correct hemisphere between the two contact circles.
/// Reversing the wire with the face preserves every shared effective coedge.
/// This works for complete periodic bands and bounded arc bands alike.
pub fn orient_toroidal_blends(
    topo: &mut Topology,
    result_faces: &[FaceId],
    blend_faces: &[FaceId],
) -> Result<(), BlendError> {
    let mut uses: HashMap<EdgeId, Vec<FaceId>> = HashMap::new();
    for &face in result_faces {
        for edge in face_edges(topo, face)? {
            uses.entry(edge).or_default().push(face);
        }
    }
    for &id in blend_faces {
        let FaceSurface::Torus(torus) = topo.face(id)?.surface().clone() else {
            continue;
        };
        let mut circles: Vec<Circle3D> = Vec::new();
        let mut cap_normal = None;
        let mut wall = false;
        for edge_id in face_edges(topo, id)? {
            let EdgeCurve::Circle(circle) = topo.edge(edge_id)?.curve() else {
                continue;
            };
            if circle.normal().cross(torus.z_axis()).length() > 1e-9 {
                continue;
            }
            let delta = circle.center() - torus.center();
            if (delta - torus.z_axis() * delta.dot(torus.z_axis())).length() > 1e-8 {
                continue;
            }
            if !circles.iter().any(|c| {
                (c.center() - circle.center()).length() < 1e-8
                    && (c.radius() - circle.radius()).abs() < 1e-8
            }) {
                circles.push(circle.clone());
            }
            for &neighbor in uses
                .get(&edge_id)
                .into_iter()
                .flatten()
                .filter(|&&f| f != id)
            {
                let face = topo.face(neighbor)?;
                match face.surface() {
                    FaceSurface::Plane { normal, .. }
                        if normal.cross(torus.z_axis()).length() < 1e-9 =>
                    {
                        let outward = *normal * if face.is_reversed() { -1.0 } else { 1.0 };
                        if cap_normal
                            .is_some_and(|n: brepkit_math::vec::Vec3| n.dot(outward) < 1.0 - 1e-9)
                        {
                            return Err(BlendError::PlanningFailure {
                                reason: "toroidal blend has conflicting oriented planar supports"
                                    .into(),
                            });
                        }
                        cap_normal = Some(outward);
                    }
                    FaceSurface::Cylinder(_) | FaceSurface::Cone(_) => wall = true,
                    _ => {}
                }
            }
        }
        let Some(normal) = cap_normal.filter(|_| wall && circles.len() == 2) else {
            continue;
        };
        let a = torus.project_point(circles[0].evaluate(0.0)).1;
        let b = torus.project_point(circles[1].evaluate(0.0)).1;
        let span =
            (b - a + std::f64::consts::PI).rem_euclid(std::f64::consts::TAU) - std::f64::consts::PI;
        if span.abs() < 1e-9 || span.abs() > std::f64::consts::PI - 1e-9 {
            continue;
        }
        let reversed = torus.normal(0.0, a + span * 0.5).dot(normal) < 0.0;
        let face = topo.face(id)?;
        if reversed == face.is_reversed() {
            continue;
        }
        let wires: Vec<_> = std::iter::once(face.outer_wire())
            .chain(face.inner_wires().iter().copied())
            .collect();
        for wire in wires {
            let edges = topo
                .wire(wire)?
                .edges()
                .iter()
                .rev()
                .map(|oe| OrientedEdge::new(oe.edge(), !oe.is_forward()))
                .collect();
            *topo.wire_mut(wire)? = Wire::new(edges, true)?;
        }
        topo.face_mut(id)?.set_reversed(reversed);
    }
    Ok(())
}
