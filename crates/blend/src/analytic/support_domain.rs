//! Admission of straight contacts on finite planar supports.
use super::{ANALYTIC_TOL_ANG, BlendError, EdgeCurve, FaceId, FaceSurface, Point3, Topology, Vec3};
use brepkit_math::curves::Circle3D;
use brepkit_math::filtered::{SegmentIntersection, segment_intersection};
use brepkit_math::predicates::point_in_polygon;
use brepkit_math::vec::Point2;

const TOL: f64 = brepkit_math::tolerance::Tolerance::new().linear;

enum Boundary {
    Polygon(Vec<Point2>),
    Circle(Circle3D, Point2),
}
impl Boundary {
    // -1 outside, 0 on the boundary, +1 strictly inside. Wire orientation
    // does not change which region is material, including reversed holes.
    fn position(&self, point: Point2) -> i8 {
        match self {
            Self::Circle(circle, center) => {
                let distance = (point - *center).length() - circle.radius();
                if distance.abs() <= TOL {
                    0
                } else if distance < 0.0 {
                    1
                } else {
                    -1
                }
            }
            Self::Polygon(points) => {
                for (&a, &b) in points.iter().zip(points.iter().cycle().skip(1)) {
                    let edge = b - a;
                    let length_sq = edge.length_squared();
                    if length_sq <= TOL * TOL {
                        continue;
                    }
                    let t = ((point - a).dot(edge) / length_sq).clamp(0.0, 1.0);
                    if (point - (a + edge * t)).length() <= TOL {
                        return 0;
                    }
                }
                if point_in_polygon(point, points) {
                    1
                } else {
                    -1
                }
            }
        }
    }
}

fn failure(reason: &str) -> BlendError {
    BlendError::PlanningFailure {
        reason: reason.to_owned(),
    }
}

/// Return the single material interval of a contact's normalized axial range.
/// End clipping is legitimate at tapered supports and blend junctions. A gap
/// through a hole or a concave notch needs multiple stripes, which this path
/// cannot construct. Partitioning at every exact crossing makes one winding
/// classification per interval sufficient; this is not curve sampling.
///
/// Mixed arcs, ellipses and NURBS boundaries retain their existing downstream
/// trimming behavior. This gate does not claim to certify those domains.
fn contact_interval(
    topo: &Topology,
    face: FaceId,
    a: Point3,
    b: Point3,
) -> Result<Option<(f64, f64)>, BlendError> {
    let data = topo.face(face)?;
    let FaceSurface::Plane { normal, d } = data.surface() else {
        return Ok(None);
    };
    let frame = crate::builder_utils::PlaneAdapter::from_normal_and_d(*normal, *d);
    let project = |p: Point3| Point2::new((p - a).dot(frame.u_dir), (p - a).dot(frame.v_dir));
    let direction = b - a;
    let length_sq = direction.length_squared();
    if length_sq <= TOL * TOL {
        return Err(failure("blend contact has zero finite length"));
    }
    let param_tol = TOL / length_sq.sqrt();
    let p0 = project(a);
    let p1 = project(b);
    let parameter = |p: Point2| (p - p0).dot(p1 - p0) / length_sq;
    let mut boundaries = Vec::new();
    for wire in std::iter::once(data.outer_wire()).chain(data.inner_wires().iter().copied()) {
        let edges = topo.wire(wire)?.edges();
        if edges.len() == 1 {
            let edge = topo.edge(edges[0].edge())?;
            if let EdgeCurve::Circle(circle) = edge.curve()
                && (topo.vertex(edge.start())?.point() - topo.vertex(edge.end())?.point()).length()
                    <= TOL
                && circle.normal().dot(*normal).abs() > 1.0 - ANALYTIC_TOL_ANG
            {
                boundaries.push(Boundary::Circle(circle.clone(), project(circle.center())));
                continue;
            }
        }
        let mut points = Vec::with_capacity(edges.len());
        for oe in edges {
            let edge = topo.edge(oe.edge())?;
            if !matches!(edge.curve(), EdgeCurve::Line) {
                return Ok(None);
            }
            points.push(project(topo.vertex(oe.oriented_start(edge))?.point()));
        }
        if points.len() < 3 {
            return Ok(None);
        }
        boundaries.push(Boundary::Polygon(points));
    }
    if [a, b]
        .iter()
        .any(|p| (Vec3::new(p.x(), p.y(), p.z()).dot(*normal) - d).abs() > TOL)
    {
        return Err(failure("blend contact is not on its bounded support plane"));
    }
    let mut cuts = vec![0.0, 1.0];
    for boundary in &boundaries {
        match boundary {
            Boundary::Polygon(points) => {
                for (&u, &v) in points.iter().zip(points.iter().cycle().skip(1)) {
                    match segment_intersection(p0, p1, u, v) {
                        SegmentIntersection::Point { t1, .. } => cuts.push(t1),
                        SegmentIntersection::Overlap { start, end } => {
                            cuts.extend([parameter(start), parameter(end)]);
                        }
                        SegmentIntersection::None => {}
                    }
                }
            }
            Boundary::Circle(circle, _) => {
                cuts.extend(
                    circle
                        .intersect_segment(a, b, TOL)
                        .iter()
                        .map(|(p, _)| (*p - a).dot(direction) / length_sq),
                );
            }
        }
    }
    for cut in &mut cuts {
        *cut = cut.clamp(0.0, 1.0);
    }
    cuts.sort_by(f64::total_cmp);
    cuts.dedup_by(|b, a| (*b - *a).abs() <= param_tol);
    let mut interval: Option<(f64, f64)> = None;
    for cut in cuts.windows(2).filter(|c| c[1] - c[0] > param_tol) {
        let mid = p0 + (p1 - p0) * f64::midpoint(cut[0], cut[1]);
        if boundaries[0].position(mid) != 1
            || boundaries[1..].iter().any(|hole| hole.position(mid) != -1)
        {
            continue;
        }
        match &mut interval {
            Some((_, end)) if cut[0] - *end <= param_tol => *end = cut[1],
            Some(_) => {
                return Err(failure(
                    "blend contact crosses a hole or disconnected support domain",
                ));
            }
            None => interval = Some((cut[0], cut[1])),
        }
    }
    interval
        .map(Some)
        .ok_or_else(|| failure("blend contact lies outside its finite support face"))
}

pub(super) fn require_contacts(
    topo: &Topology,
    contacts: [(FaceId, Point3, Point3); 2],
) -> Result<(), BlendError> {
    let first = contact_interval(topo, contacts[0].0, contacts[0].1, contacts[0].2)?;
    let second = contact_interval(topo, contacts[1].0, contacts[1].1, contacts[1].2)?;
    if let (Some((lo1, hi1)), Some((lo2, hi2))) = (first, second)
        && (hi1.min(hi2) - lo1.max(lo2)) * (contacts[0].2 - contacts[0].1).length() <= TOL
    {
        return Err(failure(
            "blend contacts have no common finite support interval",
        ));
    }
    Ok(())
}
