// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

use crate::r2::point::Point;
use crate::s2::point::Point as s2Point;
use std::cmp::*;

// Edge represents a geodesic edge consisting of two vertices. Zero-length edges are
// allowed, and can be used to represent points.

pub struct Edge {
    v0: Point,
    v1: Point,
}

impl Eq for Edge {}

impl Ord for Edge {
    fn cmp(&self, other: &Edge) -> Ordering {
        let v0cmp = self.v0.cmp(&other.v0);
        if v0cmp != Ordering::Equal {
            v0cmp
        } else {
            self.v0.cmp(&other.v1)
        }
    }
}

impl PartialOrd for Edge {
    fn partial_cmp(&self, other: &Edge) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl PartialEq for Edge {
    fn eq(&self, other: &Edge) -> bool {
        self.cmp(other) == Ordering::Equal
    }
}

// edges implements the Sort interface for slices of Edge.
#[allow(unused)]
type Edges = Vec<Edge>;

/// ShapeEdgeID is a unique identifier for an Edge within an ShapeIndex,
/// consisting of a (shape_id, edge_id) pair.
#[derive(Clone, Copy, PartialEq, Eq)]
pub struct ShapeEdgeID {
    shape_id: i32,
    edge_id: i32,
}

impl PartialOrd for ShapeEdgeID {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}
impl Ord for ShapeEdgeID {
    fn cmp(&self, other: &Self) -> Ordering {
        self.shape_id
            .cmp(&other.shape_id)
            .then(self.edge_id.cmp(&other.edge_id))
    }
}

/// ShapeEdge represents a Shapeedge_id with the two endpoints of that Edge.
pub struct ShapeEdge {
    #[allow(unused)]
    id: ShapeEdgeID,
    #[allow(unused)]
    edge: Edge,
}

/// Chain represents a range of edge IDs corresponding to a chain of connected
/// edges, specified as a (start, length) pair. The chain is defined to consist of
/// edge IDs {start, start + 1, ..., start + length - 1}.
pub struct Chain {
    #[allow(unused)]
    start: i64,
    #[allow(unused)]
    length: i64,
}

/// ChainPosition represents the position of an edge within a given edge chain,
/// specified as a (chainID, offset) pair. Chains are numbered sequentially
/// starting from zero, and offsets are measured from the start of each chain.
pub struct ChainPosition {
    #[allow(unused)]
    chain_id: i64,
    #[allow(unused)]
    offset: i64,
}

/// A ReferencePoint consists of a point and a boolean indicating whether the point
/// is contained by a particular shape.
pub struct ReferencePoint {
    #[allow(unused)]
    point: s2Point,
    #[allow(unused)]
    contained: bool,
}

impl ReferencePoint {
    /// origin returns a ReferencePoint with the given value for
    /// contained and the origin point. It should be used when all points or no
    /// points are contained.
    pub fn origin(contained: bool) -> Self {
        ReferencePoint {
            point: s2Point::origin(),
            contained: contained,
        }
    }
}

/// Shape represents polygonal geometry in a flexible way. It is organized as a
/// collection of edges that optionally defines an interior. All geometry
/// represented by a given Shape must have the same dimension, which means that
/// an Shape can represent either a set of points, a set of polylines, or a set
/// of polygons.
///
/// Shape is defined as an interface in order to give clients control over the
/// underlying data representation. Sometimes an Shape does not have any data of
/// its own, but instead wraps some other type.
///
/// Shape operations are typically defined on a ShapeIndex rather than
/// individual shapes. An ShapeIndex is simply a collection of Shapes,
/// possibly of different dimensions (e.g. 10 points and 3 polygons), organized
/// into a data structure for efficient edge access.
///
/// The edges of a Shape are indexed by a contiguous range of edge IDs
/// starting at 0. The edges are further subdivided into chains, where each
/// chain consists of a sequence of edges connected end-to-end (a polyline).
/// For example, a Shape representing two polylines AB and CDE would have
/// three edges (AB, CD, DE) grouped into two chains: (AB) and (CD, DE).
/// Similarly, an Shape representing 5 points would have 5 chains consisting
/// of one edge each.
///
/// Shape has methods that allow edges to be accessed either using the global
/// numbering (edge ID) or within a particular chain. The global numbering is
/// sufficient for most purposes, but the chain representation is useful for
/// certain algorithms such as intersection (see BooleanOperation).
pub trait Shape {
    /// num_edges returns the number of edges in this shape.
    fn num_edges(&self) -> i64;

    /// edge returns the edge for the given edge index.
    fn edge(&self, i: i64) -> Edge;

    /// reference_point returns an arbitrary reference point for the shape. (The
    /// containment boolean value must be false for shapes that do not have an interior.)
    ///
    /// This reference point may then be used to compute the containment of other
    /// points by counting edge crossings.
    fn reference_point(&self) -> ReferencePoint;

    /// num_chains reports the number of contiguous edge chains in the shape.
    /// For example, a shape whose edges are [AB, BC, CD, AE, EF] would consist
    /// of two chains (AB,BC,CD and AE,EF). Every chain is assigned a chain Id
    /// numbered sequentially starting from zero.
    ///
    /// Note that it is always acceptable to implement this method by returning
    /// NumEdges, i.e. every chain consists of a single edge, but this may
    /// reduce the efficiency of some algorithms.
    fn num_chains(&self) -> i64;

    /// chain returns the range of edge IDs corresponding to the given edge chain.
    /// Edge chains must form contiguous, non-overlapping ranges that cover
    /// the entire range of edge IDs. This is spelled out more formally below:
    ///
    ///  0 <= i < NumChains()
    ///  Chain(i).length > 0, for all i
    ///  Chain(0).start == 0
    ///  Chain(i).start + Chain(i).length == Chain(i+1).start, for i < NumChains()-1
    ///  Chain(i).start + Chain(i).length == NumEdges(), for i == NumChains()-1
    fn chain(&self, chain_id: i64) -> Chain;

    /// chain_edge returns the edge at offset "offset" within edge chain "chainID".
    /// Equivalent to "shape.Edge(shape.Chain(chainID).start + offset)"
    /// but more efficient.
    fn chain_edge(&self, chain_id: i64, offset: i64) -> Edge;

    /// chain_position finds the chain containing the given edge, and returns the
    /// position of that edge as a ChainPosition(chainID, offset) pair.
    ///
    ///  shape.Chain(pos.chainID).start + pos.offset == edge_id
    ///  shape.Chain(pos.chainID+1).start > edge_id
    ///
    /// where pos == shape.ChainPosition(edge_id).
    fn chain_position(&self, edge_id: i64) -> ChainPosition;

    /// dimension returns the dimension of the geometry represented by this shape,
    /// either 0, 1 or 2 for point, polyline and polygon geometry respectively.
    ///
    ///  0 - Point geometry. Each point is represented as a degenerate edge.
    ///
    ///  1 - Polyline geometry. Polyline edges may be degenerate. A shape may
    ///      represent any number of polylines. Polylines edges may intersect.
    ///
    ///  2 - Polygon geometry. Edges should be oriented such that the polygon
    ///      interior is always on the left. In theory the edges may be returned
    ///      in any order, but typically the edges are organized as a collection
    ///      of edge chains where each chain represents one polygon loop.
    ///      Polygons may have degeneracies (e.g., degenerate edges or sibling
    ///      pairs consisting of an edge and its corresponding reversed edge).
    ///      A polygon loop may also be full (containing all points on the
    ///      sphere); by convention this is represented as a chain with no edges.
    ///      (See laxPolygon for details.)
    ///
    /// This method allows degenerate geometry of different dimensions
    /// to be distinguished, e.g. it allows a point to be distinguished from a
    /// polyline or polygon that has been simplified to a single point.
    fn dimension(&self) -> i64;

    /// is_empty reports whether the Shape contains no points. (Note that the full
    /// polygon is represented as a chain with zero edges.)
    fn is_empty(&self) -> bool {
        self.num_edges() == 0 && (self.dimension() != 2 || self.num_chains() == 0)
    }

    /// is_full reports whether the Shape contains all points on the sphere.
    fn is_full(&self) -> bool {
        self.num_edges() == 0 && self.dimension() == 2 && self.num_chains() > 0
    }
}
