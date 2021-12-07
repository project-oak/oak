/*
Copyright 2014 Google Inc. All rights reserved.
Copyright 2017 Jhyun Yu. All rights reserved.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    http://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
*/

use crate::consts::search_lower_by;
use crate::r3::vector::Vector;
use crate::s2::cap::Cap;
use crate::s2::cell::Cell;
use crate::s2::cellid::*;
use crate::s2::metric::*;
use crate::s2::point::Point;
use crate::s2::rect::Rect;
use crate::s2::region::Region;

/// A CellUnion is a collection of CellIDs.
///
/// It is normalized if it is sorted, and does not contain redundancy.
/// Specifically, it may not contain the same CellID twice, nor a CellID that
/// is contained by another, nor the four sibling CellIDs that are children of
/// a single higher level CellID.
#[derive(Debug, Clone, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
pub struct CellUnion(pub Vec<CellID>);

impl CellUnion {
    /// from_range creates a CellUnion that covers the half-open range
    /// of leaf cells [begin, end). If begin == end the resulting union is empty.
    /// This requires that begin and end are both leaves, and begin <= end.
    /// To create a closed-ended range, pass in end.next().
    pub fn from_range(begin: CellID, end: CellID) -> Self {
        let mut v = Vec::new();
        let mut cur = begin.max_tile(&end);
        while cur != end {
            v.push(cur);
            cur = cur.next().max_tile(&end);
        }
        CellUnion(v)
    }

    /// normalize normalizes the CellUnion.
    pub fn normalize(&mut self) {
        let v = &mut self.0;
        v.sort();

        let mut output: Vec<CellID> = Vec::with_capacity(v.len());
        for ci in v.into_iter() {
            // The first two passes here either ignore this new candidate,
            // or remove previously accepted cells that are covered by this candidate.

            // Ignore this cell if it is contained by the previous one.
            // We only need to check the last accepted cell. The ordering of the
            // cells implies containment (but not the converse), and output has no redundancy,
            // so if this candidate is not contained by the last accepted cell
            // then it cannot be contained by any previously accepted cell.
            if let Some(true) = output.last().map(|last| last.contains(&ci)) {
                continue;
            }

            // Discard any previously accepted cells contained by this one.
            // This could be any contiguous trailing subsequence, but it can't be
            // a discontiguous subsequence because of the containment property of
            // sorted S2 cells mentioned above.
            while let Some(true) = output.last().map(|last| ci.contains(last)) {
                output.pop();
            }

            // See if the last three cells plus this one can be collapsed.
            // We loop because collapsing three accepted cells and adding a higher level cell
            // could cascade into previously accepted cells.
            let mut ci = *ci;
            while output.len() >= 3 {
                {
                    let fin = &output[(output.len() - 3)..];

                    // fast XOR test; a necessary but not sufficient condition
                    if fin[0].0 ^ fin[1].0 ^ fin[2].0 ^ ci.0 != 0 {
                        break;
                    }

                    // more expensive test; exact.
                    // Compute the two bit mask for the encoded child position,
                    // then see if they all agree.
                    let mut mask = ci.lsb() << 1;
                    mask = !(mask + (mask << 1));
                    let should = ci.0 & mask;
                    if (fin[0].0 & mask != should)
                        || (fin[1].0 & mask != should)
                        || (fin[2].0 & mask != should)
                        || ci.is_face()
                    {
                        break;
                    }
                }

                // output = &output[0..(output.len() - 3)];
                for _ in 0..3 {
                    output.pop();
                }
                ci = ci.immediate_parent();
            }
            output.push(ci);
        }

        // self.0 = output;
        v.clear();
        v.extend_from_slice(&output);
    }

    /// intersects_cellid reports whether this cell union intersects the given cell ID.
    /// This method assumes that the CellUnion has been normalized.
    pub fn intersects_cellid(&self, id: &CellID) -> bool {
        let v = &self.0;
        // Find index of array item that occurs directly after our probe cell:
        let i = search_lower_by(v.len(), |i| id.0 < v[i].0);
        if i != v.len() && v[i].range_min() <= id.range_max() {
            return true;
        }
        i != 0 && v[i - 1].range_max() >= id.range_min()
    }

    /// contains_cellid reports whether the cell union contains the given cell ID.
    /// Containment is defined with respect to regions, e.g. a cell contains its 4 children.
    ///
    /// This method assumes that the CellUnion has been normalized.
    pub fn contains_cellid(&self, id: &CellID) -> bool {
        let v = &self.0;
        // Find index of array item that occurs directly after our probe cell:
        let i = search_lower_by(v.len(), |i| id.0 < v[i].0);
        if i != v.len() && v[i].range_min().0 <= id.0 {
            return true;
        }
        i != 0 && v[i - 1].range_max().0 >= id.0
    }

    /// denormalize replaces this CellUnion with an expanded version of the
    /// CellUnion where any cell whose level is less than minLevel or where
    /// (level - minLevel) is not a multiple of levelMod is replaced by its
    /// children, until either both of these conditions are satisfied or the
    /// maximum level is reached.
    pub fn denormalize(&mut self, min_level: u64, level_mod: u64) {
        let mut v: Vec<CellID> = Vec::new();
        for &id in self.0.iter() {
            let level = id.level();
            let mut new_level = level;
            if new_level < min_level {
                new_level = min_level;
            }
            if level_mod > 1 {
                new_level += (MAX_LEVEL - (new_level - min_level)) % level_mod;
                if new_level > MAX_LEVEL {
                    new_level = MAX_LEVEL;
                }
            }
            if new_level == level {
                v.push(id);
            } else {
                for id in id.child_iter_at_level(new_level) {
                    v.push(id);
                }
            }
        }
        self.0.clear();
        self.0.extend_from_slice(&v);
    }

    /// leaf_cells_covered reports the number of leaf cells covered by this cell union.
    /// This will be no more than 6*2^60 for the whole sphere.
    pub fn leaf_cell_covered(&self) -> u64 {
        let mut num_leaves = 0u64;
        for c in self.0.iter() {
            num_leaves += 1 << ((MAX_LEVEL - (c.level() as u64)) << 1);
        }
        num_leaves
    }
}

impl Region for CellUnion {
    // cap_bound returns a Cap that bounds this entity.
    fn cap_bound(&self) -> Cap {
        if self.0.is_empty() {
            return Cap::empty();
        }

        // Compute the approximate centroid of the region. This won't produce the
        // bounding cap of minimal area, but it should be close enough.
        let mut centroid = Point(Vector {
            x: 0.,
            y: 0.,
            z: 0.,
        });

        for ci in self.0.iter() {
            let area = AVG_AREAMETRIC.value(ci.level() as u8);
            centroid = centroid + (Point::from(ci) * area);
        }

        if centroid.0.x == 0. && centroid.0.y == 0. && centroid.0.z == 0. {
            centroid = Point::from_coords(1., 0., 0.);
        } else {
            centroid = Point(centroid.0.normalize());
        }

        // Use the centroid as the cap axis, and expand the cap angle so that it
        // contains the bounding caps of all the individual cells.  Note that it is
        // *not* sufficient to just bound all the cell vertices because the bounding
        // cap may be concave (i.e. cover more than one hemisphere).
        let mut cap = Cap::from(&centroid);
        for ci in self.0.iter() {
            cap = cap + Cell::from(ci).cap_bound();
        }
        cap
    }

    /// rect_bound returns a Rect that bounds this entity.
    fn rect_bound(&self) -> Rect {
        let mut bound = Rect::empty();
        for c in self.0.iter() {
            bound = bound.union(&Cell::from(c).rect_bound());
        }
        bound
    }

    // contains_cell reports whether this cell union contains the given cell.
    fn contains_cell(&self, c: &Cell) -> bool {
        self.contains_cellid(&c.id)
    }

    // intersects_cell reports whether this cell union intersects the given cell.
    fn intersects_cell(&self, c: &Cell) -> bool {
        self.intersects_cellid(&c.id)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_cellunion_normalization() {
        let mut cu = CellUnion(vec![
            CellID(0x80855c0000000000), // A: a cell over Pittsburg CA
            CellID(0x80855d0000000000), // B, a child of A
            CellID(0x8085634000000000), // first child of X, disjoint from A
            CellID(0x808563c000000000), // second child of X
            CellID(0x80855dc000000000), // a child of B
            CellID(0x808562c000000000), // third child of X
            CellID(0x8085624000000000), // fourth child of X
            CellID(0x80855d0000000000), // B again
        ]);

        let exp = CellUnion(vec![
            CellID(0x80855c0000000000), // A
            CellID(0x8085630000000000), // X
        ]);

        cu.normalize();

        assert_eq!(cu, exp);

        // add a redundant cell
        /* TODO(dsymonds)
        cu.Add(0x808562c000000000)
        if !reflect.DeepEqual(cu, exp) {
            t.Errorf("after redundant add, got %v, want %v", cu, exp)
        }
        */
    }

    #[test]
    fn test_cellunion_basic() {
        let mut empty = CellUnion(vec![]);
        empty.normalize();
        assert_eq!(empty.0.len(), 0);

        let face1_id = CellID::from_face(1);
        let face1_cell = Cell::from(&face1_id);
        let mut face1_union = CellUnion(vec![face1_id.clone()]);
        face1_union.normalize();
        assert_eq!(face1_union.0.len(), 1);
        assert_eq!(face1_id, face1_union.0[0]);
        assert_eq!(true, face1_union.contains_cell(&face1_cell));

        let face2_id = CellID::from_face(2);
        let face2_cell = Cell::from(&face2_id);
        let mut face2_union = CellUnion(vec![face2_id.clone()]);
        face2_union.normalize();
        assert_eq!(face2_union.0.len(), 1);
        assert_eq!(face2_id, face2_union.0[0]);
        assert_eq!(true, face2_union.contains_cell(&face2_cell));

        assert_eq!(false, face1_union.contains_cell(&face2_cell));
    }

    fn test_cellunion_case(
        cells: &[CellID],
        contained: &[CellID],
        overlaps: &[CellID],
        disjoint: &[CellID],
    ) {
        let mut v = Vec::with_capacity(cells.len());
        v.extend_from_slice(cells);
        let mut union = CellUnion(v);
        union.normalize();

        // Ensure self-containment tests are correct.
        for id in cells {
            assert_eq!(true, union.intersects_cellid(&id));
            assert_eq!(true, union.contains_cellid(&id));
        }

        // Test for containment specified in test case.
        for id in contained {
            assert_eq!(true, union.intersects_cellid(&id));
            assert_eq!(true, union.contains_cellid(&id));
        }

        // Make sure the CellUnion intersect these cells but do not contain.
        for id in overlaps {
            assert_eq!(true, union.intersects_cellid(&id));
            assert_eq!(false, union.contains_cellid(&id));
        }

        // Negative cases make sure the CellUnion neither contain nor intersect these cells
        for id in disjoint {
            assert_eq!(false, union.intersects_cellid(&id));
            assert_eq!(false, union.contains_cellid(&id));
        }
    }

    #[test]
    fn test_cellunion() {
        test_cellunion_case(
            &[
                // Single cell around NYC, and some simple nearby probes
                CellID(0x89c25c0000000000),
            ],
            &[
                CellID(0x89c25c0000000000).child_begin(),
                CellID(0x89c25c0000000000).child_begin_at_level(28),
            ],
            &[
                CellID(0x89c25c0000000000).immediate_parent(),
                // the whole face
                CellID::from_face(CellID(0x89c25c0000000000).face() as u64),
            ],
            &[
                // Cell next to this one at same level
                CellID(0x89c25c0000000000).next(),
                // Cell next to this one at deep level
                CellID(0x89c25c0000000000).next().child_begin_at_level(28),
                // Big(er) neighbor cell
                CellID(0x89c2700000000000),
                // Very big next door cell.
                CellID(0x89e9000000000000),
                // Very big cell, smaller value than probe
                CellID(0x89c1000000000000),
            ],
        );

        test_cellunion_case(
            &[
                // NYC and SFO:
                CellID(0x89c25b0000000000), // NYC
                CellID(0x89c2590000000000), // NYC
                CellID(0x89c2f70000000000), // NYC
                CellID(0x89c2f50000000000), // NYC
                CellID(0x8085870000000000), // SFO
                CellID(0x8085810000000000), // SFO
                CellID(0x808f7d0000000000), // SFO
                CellID(0x808f7f0000000000), // SFO
            ],
            &[
                CellID(0x808f7ef300000000), // SFO
                CellID(0x808f7e5cf0000000), // SFO
                CellID(0x808587f000000000), // SFO
                CellID(0x89c25ac000000000), // NYC
                CellID(0x89c259a400000000), // NYC
                CellID(0x89c258fa10000000), // NYC
                CellID(0x89c258f174007000), // NYC
            ],
            &[
                CellID(0x808c000000000000), // Big SFO
                CellID(0x89c4000000000000), // Big NYC
            ],
            &[
                CellID(0x89c15a4fcb1bb000), // outside NYC
                CellID(0x89c15a4e4aa95000), // outside NYC
                CellID(0x8094000000000000), // outside SFO (big)
                CellID(0x8096f10000000000), // outside SFO (smaller)
                CellID(0x87c0000000000000), // Midwest very big
            ],
        );

        test_cellunion_case(
            &[
                CellID(0x8100000000000000), // starting around california
                CellID(0x8740000000000000), // adjacent cells at increasing
                CellID(0x8790000000000000), // levels, moving eastward.
                CellID(0x87f4000000000000),
                CellID(0x87f9000000000000), // going down across the midwest
                CellID(0x87ff400000000000),
                CellID(0x87ff900000000000),
                CellID(0x87fff40000000000),
                CellID(0x87fff90000000000),
                CellID(0x87ffff4000000000),
                CellID(0x87ffff9000000000),
                CellID(0x87fffff400000000),
                CellID(0x87fffff900000000),
                CellID(0x87ffffff40000000),
                CellID(0x87ffffff90000000),
                CellID(0x87fffffff4000000),
                CellID(0x87fffffff9000000),
                CellID(0x87ffffffff400000), // to a very small cell in Wisconsin
            ],
            &[
                CellID(0x808f400000000000),
                CellID(0x80eb118b00000000),
                CellID(0x8136a7a11d000000),
                CellID(0x8136a7a11dac0000),
                CellID(0x876c7c0000000000),
                CellID(0x87f96d0000000000),
                CellID(0x87ffffffff400000),
            ],
            &[
                CellID(0x8100000000000000).immediate_parent(),
                CellID(0x8740000000000000).immediate_parent(),
            ],
            &[
                CellID(0x52aaaaaaab300000),
                CellID(0x52aaaaaaacd00000),
                CellID(0x87fffffffa100000),
                CellID(0x87ffffffed500000),
                CellID(0x87ffffffa0100000),
                CellID(0x87fffffed5540000),
                CellID(0x87fffffed6240000),
                CellID(0x52aaaacccb340000),
                CellID(0x87a0000400000000),
                CellID(0x87a000001f000000),
                CellID(0x87a0000029d00000),
                CellID(0x9500000000000000),
            ],
        );
    }

    /*
    func addCells(id CellID, selected bool, input *[]CellID, expected *[]CellID, t *testing.T) {
        // Decides whether to add "id" and/or some of its descendants to the test case.  If "selected"
        // is true, then the region covered by "id" *must* be added to the test case (either by adding
        // "id" itself, or some combination of its descendants, or both).  If cell ids are to the test
        // case "input", then the corresponding expected result after simplification is added to
        // "expected".

        if id == 0 {
            // Initial call: decide whether to add cell(s) from each face.
            for face := 0; face < 6; face++ {
                addCells(CellIDFromFace(face), false, input, expected, t)
            }
            return
        }

        if id.IsLeaf() {
            // The oneIn() call below ensures that the parent of a leaf cell will always be selected (if
            // we make it that far down the hierarchy).
            if selected != true {
                t.Errorf("id IsLeaf() and not selected")
            }
            *input = append(*input, id)
            return
        }

        // The following code ensures that the probability of selecting a cell at each level is
        // approximately the same, i.e. we test normalization of cells at all levels.
        if !selected && oneIn(maxLevel-id.Level()) {
            //  Once a cell has been selected, the expected output is predetermined.  We then make sure
            //  that cells are selected that will normalize to the desired output.
            *expected = append(*expected, id)
            selected = true

        }

        // With the rnd.OneIn() constants below, this function adds an average
        // of 5/6 * (kMaxLevel - level) cells to "input" where "level" is the
        // level at which the cell was first selected (level 15 on average).
        // Therefore the average number of input cells in a test case is about
        // (5/6 * 15 * 6) = 75.  The average number of output cells is about 6.

        // If a cell is selected, we add it to "input" with probability 5/6.
        added := false
        if selected && !oneIn(6) {
            *input = append(*input, id)
            added = true
        }
        numChildren := 0
        for child := id.ChildBegin(); child != id.ChildEnd(); child = child.Next() {
            // If the cell is selected, on average we recurse on 4/12 = 1/3 child.
            // This intentionally may result in a cell and some of its children
            // being included in the test case.
            //
            // If the cell is not selected, on average we recurse on one child.
            // We also make sure that we do not recurse on all 4 children, since
            // then we might include all 4 children in the input case by accident
            // (in which case the expected output would not be correct).
            recurse := false
            if selected {
                recurse = oneIn(12)
            } else {
                recurse = oneIn(4)
            }
            if recurse && numChildren < 3 {
                addCells(child, selected, input, expected, t)
                numChildren++
            }
            // If this cell was selected but the cell itself was not added, we
            // must ensure that all 4 children (or some combination of their
            // descendants) are added.

            if selected && !added {
                addCells(child, selected, input, expected, t)
            }
        }
    }

    func TestCellUnionNormalizePseudoRandom(t *testing.T) {
        // Try a bunch of random test cases, and keep track of average statistics
        // for normalization (to see if they agree with the analysis above).

        inSum := 0
        outSum := 0
        iters := 2000

        for i := 0; i < iters; i++ {
            input := []CellID{}
            expected := []CellID{}
            addCells(CellID(0), false, &input, &expected, t)
            inSum += len(input)
            outSum += len(expected)
            cellunion := CellUnion(input)
            cellunion.Normalize()

            if len(expected) != len(cellunion) {
                t.Errorf("Expected size of union to be %d, but got %d.",
                    len(expected), len(cellunion))
            }

            // Test GetCapBound().
            cb := cellunion.CapBound()
            for _, ci := range cellunion {
                if !cb.ContainsCell(CellFromCellID(ci)) {
                    t.Errorf("CapBound %v of union %v should contain cellID %v", cb, cellunion, ci)
                }
            }

            for _, j := range input {
                if !cellunion.ContainsCellID(j) {
                    t.Errorf("Expected containment of CellID %v", j)
                }

                if cellunion.IntersectsCellID(j) == false {
                    t.Errorf("Expected intersection with %v.", j)
                }

                if !j.isFace() {
                    if cellunion.IntersectsCellID(j.immediateParent()) == false {
                        t.Errorf("Expected intersection with parent cell %v.", j.immediateParent())
                        if j.Level() > 1 {
                            if cellunion.IntersectsCellID(j.immediateParent().immediateParent()) == false {
                                t.Errorf("Expected intersection with parent's parent %v.",
                                    j.immediateParent().immediateParent())
                            }
                            if cellunion.IntersectsCellID(j.Parent(0)) == false {
                                t.Errorf("Expected intersection with parent %v at level 0.", j.Parent(0))
                            }
                        }
                    }
                }

                if !j.IsLeaf() {
                    if cellunion.ContainsCellID(j.ChildBegin()) == false {
                        t.Errorf("Expected containment of %v.", j.ChildBegin())
                    }
                    if cellunion.IntersectsCellID(j.ChildBegin()) == false {
                        t.Errorf("Expected intersection with %v.", j.ChildBegin())
                    }
                    if cellunion.ContainsCellID(j.ChildEnd().Prev()) == false {
                        t.Errorf("Expected containment of %v.", j.ChildEnd().Prev())
                    }
                    if cellunion.IntersectsCellID(j.ChildEnd().Prev()) == false {
                        t.Errorf("Expected intersection with %v.", j.ChildEnd().Prev())
                    }
                    if cellunion.ContainsCellID(j.ChildBeginAtLevel(maxLevel)) == false {
                        t.Errorf("Expected containment of %v.", j.ChildBeginAtLevel(maxLevel))
                    }
                    if cellunion.IntersectsCellID(j.ChildBeginAtLevel(maxLevel)) == false {
                        t.Errorf("Expected intersection with %v.", j.ChildBeginAtLevel(maxLevel))
                    }
                }
            }

            for _, exp := range expected {
                if !exp.isFace() {
                    if cellunion.ContainsCellID(exp.Parent(exp.Level() - 1)) {
                        t.Errorf("cellunion should not contain its parent %v", exp.Parent(exp.Level()-1))
                    }
                    if cellunion.ContainsCellID(exp.Parent(0)) {
                        t.Errorf("cellunion should not contain the top level parent %v", exp.Parent(0))
                    }
                }
            }

            var test []CellID
            var dummy []CellID
            addCells(CellID(0), false, &test, &dummy, t)
            for _, j := range test {
                intersects := false
                contains := false
                for _, k := range expected {
                    if k.Contains(j) {
                        contains = true
                    }
                    if k.Intersects(j) {
                        intersects = true
                    }
                }
                if cellunion.ContainsCellID(j) != contains {
                    t.Errorf("Expected contains with %v.", (uint64)(j))
                }
                if cellunion.IntersectsCellID(j) != intersects {
                    t.Errorf("Expected intersection with %v.", (uint64)(j))
                }
            }
        }
        t.Logf("avg in %.2f, avg out %.2f\n", (float64)(inSum)/(float64)(iters), (float64)(outSum)/(float64)(iters))
    }
    */

    fn test_denorm_case(
        name: &str,
        min_level: u64,
        level_mod: u64,
        mut cu: CellUnion,
        exp: CellUnion,
    ) {
        cu.denormalize(min_level, level_mod);
        assert_eq!(exp, cu, "{}", name);
    }

    fn cfbl(face: u64, level: u64) -> CellID {
        CellID::from_face(face).child_begin_at_level(level)
    }

    #[test]
    fn test_cellunion_denormalize() {
        test_denorm_case(
            "not expanded, level mod == 1",
            10,
            1,
            CellUnion(vec![cfbl(2, 11), cfbl(2, 11), cfbl(3, 14), cfbl(0, 10)]),
            CellUnion(vec![cfbl(2, 11), cfbl(2, 11), cfbl(3, 14), cfbl(0, 10)]),
        );

        test_denorm_case(
            "not expanded, level mod > 1",
            10,
            2,
            CellUnion(vec![cfbl(2, 12), cfbl(2, 12), cfbl(3, 14), cfbl(0, 10)]),
            CellUnion(vec![cfbl(2, 12), cfbl(2, 12), cfbl(3, 14), cfbl(0, 10)]),
        );

        test_denorm_case(
            "expended, (level - min_level) is not multiple of level mod",
            10,
            3,
            CellUnion(vec![cfbl(2, 12), cfbl(5, 11)]),
            CellUnion(vec![
                cfbl(2, 12).children()[0],
                cfbl(2, 12).children()[1],
                cfbl(2, 12).children()[2],
                cfbl(2, 12).children()[3],
                cfbl(5, 11).children()[0].children()[0],
                cfbl(5, 11).children()[0].children()[1],
                cfbl(5, 11).children()[0].children()[2],
                cfbl(5, 11).children()[0].children()[3],
                cfbl(5, 11).children()[1].children()[0],
                cfbl(5, 11).children()[1].children()[1],
                cfbl(5, 11).children()[1].children()[2],
                cfbl(5, 11).children()[1].children()[3],
                cfbl(5, 11).children()[2].children()[0],
                cfbl(5, 11).children()[2].children()[1],
                cfbl(5, 11).children()[2].children()[2],
                cfbl(5, 11).children()[2].children()[3],
                cfbl(5, 11).children()[3].children()[0],
                cfbl(5, 11).children()[3].children()[1],
                cfbl(5, 11).children()[3].children()[2],
                cfbl(5, 11).children()[3].children()[3],
            ]),
        );

        test_denorm_case(
            "expended, level < min_level",
            10,
            3,
            CellUnion(vec![cfbl(2, 9)]),
            CellUnion(vec![
                cfbl(2, 9).children()[0],
                cfbl(2, 9).children()[1],
                cfbl(2, 9).children()[2],
                cfbl(2, 9).children()[3],
            ]),
        );
    }
}

/*
func TestCellUnionRectBound(t *testing.T) {
    tests := []struct {
        cu   *CellUnion
        want Rect
    }{
        {&CellUnion{}, EmptyRect()},
        {
            &CellUnion{CellIDFromFace(1)},
            Rect{
                r1.Interval{-math.Pi / 4, math.Pi / 4},
                s1.Interval{math.Pi / 4, 3 * math.Pi / 4},
            },
        },
        {
            &CellUnion{
                0x808c000000000000, // Big SFO
            },
            Rect{
                r1.Interval{
                    float64(s1.Degree * 34.644220547108482),
                    float64(s1.Degree * 38.011928357226651),
                },
                s1.Interval{
                    float64(s1.Degree * -124.508522987668428),
                    float64(s1.Degree * -121.628309835221216),
                },
            },
        },
        {
            &CellUnion{
                0x89c4000000000000, // Big NYC
            },
            Rect{
                r1.Interval{
                    float64(s1.Degree * 38.794595155857657),
                    float64(s1.Degree * 41.747046884651063),
                },
                s1.Interval{
                    float64(s1.Degree * -76.456308667788633),
                    float64(s1.Degree * -73.465162142654819),
                },
            },
        },
        {
            &CellUnion{
                0x89c4000000000000, // Big NYC
                0x808c000000000000, // Big SFO
            },
            Rect{
                r1.Interval{
                    float64(s1.Degree * 34.644220547108482),
                    float64(s1.Degree * 41.747046884651063),
                },
                s1.Interval{
                    float64(s1.Degree * -124.508522987668428),
                    float64(s1.Degree * -73.465162142654819),
                },
            },
        },
    }

    for _, test := range tests {
        if got := test.cu.RectBound(); !rectsApproxEqual(got, test.want, epsilon, epsilon) {
            t.Errorf("%v.RectBound() = %v, want %v", test.cu, got, test.want)
        }
    }
}

func TestCellUnionLeafCellsCovered(t *testing.T) {
    tests := []struct {
        have []CellID
        want int64
    }{
        {},
        {
            have: []CellID{},
            want: 0,
        },
        {
            // One leaf cell on face 0.
            have: []CellID{
                CellIDFromFace(0).ChildBeginAtLevel(maxLevel),
            },
            want: 1,
        },
        {
            // Face 0 itself (which includes the previous leaf cell).
            have: []CellID{
                CellIDFromFace(0).ChildBeginAtLevel(maxLevel),
                CellIDFromFace(0),
            },
            want: 1 << 60,
        },
        /*
            TODO(roberts): Once Expand is implemented, add the two tests for these
            // Five faces.
            cell_union.Expand(0),
            want: 5 << 60,
            // Whole world.
            cell_union.Expand(0),
            want: 6 << 60,
        */
        {
            // Add some disjoint cells.
            have: []CellID{
                CellIDFromFace(0).ChildBeginAtLevel(maxLevel),
                CellIDFromFace(0),
                CellIDFromFace(1).ChildBeginAtLevel(1),
                CellIDFromFace(2).ChildBeginAtLevel(2),
                CellIDFromFace(2).ChildEndAtLevel(2).Prev(),
                CellIDFromFace(3).ChildBeginAtLevel(14),
                CellIDFromFace(4).ChildBeginAtLevel(27),
                CellIDFromFace(4).ChildEndAtLevel(15).Prev(),
                CellIDFromFace(5).ChildBeginAtLevel(30),
            },
            want: 1 + (1 << 6) + (1 << 30) + (1 << 32) +
                (2 << 56) + (1 << 58) + (1 << 60),
        },
    }

    for _, test := range tests {
        cu := CellUnion(test.have)
        cu.Normalize()
        if got := cu.LeafCellsCovered(); got != test.want {
            t.Errorf("CellUnion(%v).LeafCellsCovered() = %v, want %v", cu, got, test.want)
        }
    }
}

func TestCellUnionFromRange(t *testing.T) {
    for iter := 0; iter < 100; iter++ {
        min := randomCellIDForLevel(maxLevel)
        max := randomCellIDForLevel(maxLevel)
        if min > max {
            min, max = max, min
        }

        cu := CellUnionFromRange(min, max.Next())
        if len(cu) <= 0 {
            t.Errorf("len(CellUnionFromRange(%v, %v)) = %d, want > 0", min, max.Next(), len(cu))
        }
        if min != cu[0].RangeMin() {
            t.Errorf("%v.RangeMin of CellUnion should not be below the minimum value it was created from %v", cu[0], min)
        }
        if max != cu[len(cu)-1].RangeMax() {
            t.Errorf("%v.RangeMax of CellUnion should not be above the maximum value it was created from %v", cu[len(cu)-1], max)
        }
        for i := 1; i < len(cu); i++ {
            if got, want := cu[i].RangeMin(), cu[i-1].RangeMax().Next(); got != want {
                t.Errorf("%v.RangeMin() = %v, want %v", cu[i], got, want)
            }
        }
    }

    // Focus on test cases that generate an empty or full range.

    // Test an empty range before the minimum CellID.
    idBegin := CellIDFromFace(0).ChildBeginAtLevel(maxLevel)
    cu := CellUnionFromRange(idBegin, idBegin)
    if len(cu) != 0 {
        t.Errorf("CellUnionFromRange with begin and end as the first CellID should be empty, got %d", len(cu))
    }

    // Test an empty range after the maximum CellID.
    idEnd := CellIDFromFace(5).ChildEndAtLevel(maxLevel)
    cu = CellUnionFromRange(idEnd, idEnd)
    if len(cu) != 0 {
        t.Errorf("CellUnionFromRange with begin and end as the last CellID should be empty, got %d", len(cu))
    }

    // Test the full sphere.
    cu = CellUnionFromRange(idBegin, idEnd)
    if len(cu) != 6 {
        t.Errorf("CellUnionFromRange from first CellID to last CellID should have 6 cells, got %d", len(cu))
    }

    for i := 0; i < len(cu); i++ {
        if !cu[i].isFace() {
            t.Errorf("CellUnionFromRange for full sphere cu[%d].isFace() = %t, want %t", i, cu[i].isFace(), true)
        }
    }
}

func BenchmarkCellUnionFromRange(b *testing.B) {
    x := CellIDFromFace(0).ChildBeginAtLevel(maxLevel)
    y := CellIDFromFace(5).ChildEndAtLevel(maxLevel)
    for i := 0; i < b.N; i++ {
        CellUnionFromRange(x, y)
    }
}
*/

// BUG: Differences from C++:
//  Contains(CellUnion)/Intersects(CellUnion)
//  Union(CellUnion)/Intersection(CellUnion)/Difference(CellUnion)
//  Expand
//  ContainsPoint
//  AverageArea/ApproxArea/ExactArea
//
