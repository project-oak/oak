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

use std;
use std::cmp::min;
use std::collections::BinaryHeap;

use crate::consts::clamp;
use crate::s2::cap::Cap;
use crate::s2::cell::Cell;
use crate::s2::cellid::*;
use crate::s2::cellunion::CellUnion;
use crate::s2::rect::Rect;

/// A Region represents a two-dimensional region on the unit sphere.
///
/// The purpose of this interface is to allow complex regions to be
/// approximated as simpler regions. The interface is restricted to methods
/// that are useful for computing approximations.
pub trait Region {
    /// cap_bound returns a bounding spherical cap. This is not guaranteed to be exact.
    fn cap_bound(&self) -> Cap;

    /// rect_bound returns a bounding latitude-longitude rectangle that contains
    /// the region. The bounds are not guaranteed to be tight.
    fn rect_bound(&self) -> Rect {
        let cap = self.cap_bound();
        cap.rect_bound()
    }

    /// contains_cell reports whether the region completely contains the given region.
    /// It returns false if containment could not be determined.
    fn contains_cell(&self, cell: &Cell) -> bool {
        self.cap_bound().contains_cell(cell)
    }

    /// intersects_cell reports whether the region intersects the given cell or
    /// if intersection could not be determined. It returns false if the region
    /// does not intersect.
    fn intersects_cell(&self, cell: &Cell) -> bool {
        self.cap_bound().intersects_cell(cell)
    }

    fn cell_union_bound(&self) -> Vec<CellID> {
        self.cap_bound().cell_union_bound()
    }
}

/// RegionCoverer allows arbitrary regions to be approximated as unions of cells (CellUnion).
/// This is useful for implementing various sorts of search and precomputation operations.
///
/// Typical usage:
///
///	rc := &s2.RegionCoverer{MaxLevel: 30, MaxCells: 5}
///	r := s2.Region(CapFromCenterArea(center, area))
///	covering := rc.Covering(r)
///
/// This yields a CellUnion of at most 5 cells that is guaranteed to cover the
/// given region (a disc-shaped region on the sphere).
///
/// For covering, only cells where (level - MinLevel) is a multiple of LevelMod will be used.
/// This effectively allows the branching factor of the S2 CellID hierarchy to be increased.
/// Currently the only parameter values allowed are 0/1, 2, or 3, corresponding to
/// branching factors of 4, 16, and 64 respectively.
///
/// Note the following:
///
///  - MinLevel takes priority over MaxCells, i.e. cells below the given level will
///    never be used even if this causes a large number of cells to be returned.
///
///  - For any setting of MaxCells, up to 6 cells may be returned if that
///    is the minimum number of cells required (e.g. if the region intersects
///    all six face cells).  Up to 3 cells may be returned even for very tiny
///    convex regions if they happen to be located at the intersection of
///    three cube faces.
///
///  - For any setting of MaxCells, an arbitrary number of cells may be
///    returned if MinLevel is too high for the region being approximated.
///
///  - If MaxCells is less than 4, the area of the covering may be
///    arbitrarily large compared to the area of the original region even if
///    the region is convex (e.g. a Cap or Rect).
///
/// The approximation algorithm is not optimal but does a pretty good job in
/// practice. The output does not always use the maximum number of cells
/// allowed, both because this would not always yield a better approximation,
/// and because MaxCells is a limit on how much work is done exploring the
/// possible covering as well as a limit on the final output size.
///
/// Because it is an approximation algorithm, one should not rely on the
/// stability of the output. In particular, the output of the covering algorithm
/// may change across different versions of the library.
///
/// One can also generate interior coverings, which are sets of cells which
/// are entirely contained within a region. Interior coverings can be
/// empty, even for non-empty regions, if there are no cells that satisfy
/// the provided constraints and are contained by the region. Note that for
/// performance reasons, it is wise to specify a MaxLevel when computing
/// interior coverings - otherwise for regions with small or zero area, the
/// algorithm may spend a lot of time subdividing cells all the way to leaf
/// level to try to find contained cells.
#[derive(Clone, Debug)]
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
pub struct RegionCoverer {
    /// the minimum cell level to be used.
    pub min_level: u8,
    /// the maximum cell level to be used.
    pub max_level: u8,
    /// the level_mod to be used.
    pub level_mod: u8,
    /// the maximum desired number of cells in the approximation.
    pub max_cells: usize,
}

struct Coverer<'a, R>
where
    R: Region + 'static,
{
    constraint: &'a RegionCoverer,
    region: &'a R,
    result: Vec<CellID>,
    pq: BinaryHeap<Candidate>,
    interior_covering: bool,
}

#[derive(Debug)]
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
struct Candidate {
    cell: Cell,
    terminal: bool,
    children: Vec<Candidate>,
    priority: isize,
}

impl std::cmp::PartialEq for Candidate {
    fn eq(&self, other: &Candidate) -> bool {
        self.cell.id == other.cell.id
    }
}
impl std::cmp::Eq for Candidate {}
impl std::cmp::PartialOrd for Candidate {
    fn partial_cmp(&self, other: &Candidate) -> Option<std::cmp::Ordering> {
        Some(self.priority.cmp(&other.priority))
    }
}
impl std::cmp::Ord for Candidate {
    fn cmp(&self, other: &Candidate) -> std::cmp::Ordering {
        self.priority.cmp(&other.priority)
    }
}

impl<'a, R> Coverer<'a, R>
where
    R: Region,
{
    // new_candidate returns a new candidate with no children if the cell intersects the given region.
    // The candidate is marked as terminal if it should not be expanded further.
    fn new_candidate(&self, cell: Cell) -> Option<Candidate> {
        if !self.region.intersects_cell(&cell) {
            return None;
        }

        let level = cell.level();
        let mut cand = Candidate {
            cell: cell.clone(),
            terminal: false,
            children: Vec::new(),
            priority: 0,
        };

        if level >= self.constraint.min_level {
            if self.interior_covering {
                if self.region.contains_cell(&cell) {
                    cand.terminal = true;
                } else if level + self.constraint.level_mod > self.constraint.max_level {
                    return None;
                }
            } else if level + self.constraint.level_mod > self.constraint.max_level
                || self.region.contains_cell(&cell)
            {
                cand.terminal = true;
            }
        };

        Some(cand)
    }

    /// expand_children populates the children of the candidate by expanding the given number of
    /// levels from the given cell.  Returns the number of children that were marked "terminal".
    fn expand_children(&self, cand: &mut Candidate, cell: Cell, mut num_levels: i32) -> usize {
        num_levels -= 1;
        let mut num_terminals = 0;
        for ci in cell.id.child_iter() {
            let child_cell = Cell::from(ci);
            if num_levels > 0 {
                if self.region.intersects_cell(&child_cell) {
                    num_terminals += self.expand_children(cand, child_cell, num_levels);
                }
                continue;
            }

            if let Some(child) = self.new_candidate(child_cell) {
                if child.terminal {
                    num_terminals += 1;
                }
                cand.children.push(child);
            }
        }
        num_terminals
    }

    /// add_candidate adds the given candidate to the result if it is marked as "terminal",
    /// otherwise expands its children and inserts it into the priority queue.
    /// Passing an argument of nil does nothing.
    fn add_candidate(&mut self, mut cand: Candidate) {
        if cand.terminal {
            self.result.push(cand.cell.id);
            return;
        }

        // Expand one level at a time until we hit minLevel to ensure that we don't skip over it.
        let level = cand.cell.level();
        let num_levels = if level < self.constraint.min_level {
            1
        } else {
            self.constraint.level_mod
        };

        let cand_cell = cand.cell.clone();
        let num_terminals = self.expand_children(&mut cand, cand_cell, i32::from(num_levels));
        let max_children_shift = self.constraint.level_mod * 2;
        if cand.children.is_empty() {
            return;
        }

        if !self.interior_covering
            && num_terminals == (1 << max_children_shift)
            && level >= self.constraint.min_level
        {
            // Optimization: add the parent cell rather than all of its children.
            // We can't do this for interior coverings, since the children just
            // intersect the region, but may not be contained by it - we need to
            // subdivide them further.
            cand.terminal = true;
            self.add_candidate(cand);
            return;
        }

        // We negate the priority so that smaller absolute priorities are returned
        // first. The heuristic is designed to refine the largest cells first,
        // since those are where we have the largest potential gain. Among cells
        // of the same size, we prefer the cells with the fewest children.
        // Finally, among cells with equal numbers of children we prefer those
        // with the smallest number of children that cannot be refined further.
        cand.priority = -((((((level as usize) << max_children_shift) + cand.children.len())
            << max_children_shift)
            + num_terminals) as isize);
        self.pq.push(cand)
    }

    /// adjust_cell_levels ensures that all cells with level > minLevel also satisfy levelMod,
    /// by replacing them with an ancestor if necessary. Cell levels smaller
    /// than minLevel are not modified (see AdjustLevel). The output is
    /// then normalized to ensure that no redundant cells are present.
    fn adjust_cell_levels(&self, cells: &mut Vec<CellID>) {
        if self.constraint.level_mod == 1 {
            return;
        }
        let mut out: Vec<CellID> = Vec::new();

        for &ci in cells.iter() {
            let level = ci.level() as u8;
            let new_level = self.constraint.adjust_level(level);
            let cur = if new_level != level {
                ci.parent(new_level.into())
            } else {
                ci
            };

            let mut pop_last = false;
            if let Some(last) = out.last() {
                if last.contains(&cur) {
                    continue;
                }
                if cur.contains(&last) {
                    pop_last = true;
                }
            }
            if pop_last {
                out.pop();
            }
            out.push(cur);
        }
        cells.clear();
        cells.extend_from_slice(&out);
    }

    /// initial_candidates computes a set of initial candidates that cover the given region.
    fn initial_candidates(&mut self) {
        // Optimization: start with a small (usually 4 cell) covering of the region's bounding cap.
        let temp = RegionCoverer {
            min_level: 0,
            max_level: self.constraint.max_level,
            level_mod: 1,
            max_cells: min(self.constraint.max_cells, 4),
        };

        let mut cells = temp.fast_covering(self.region);
        let mut v = &mut cells.0;
        self.adjust_cell_levels(&mut v);
        for ci in v.iter() {
            if let Some(cand) = self.new_candidate(Cell::from(ci)) {
                self.add_candidate(cand);
            }
        }
    }

    /// covering_internal generates a covering and stores it in result.
    /// Strategy: Start with the 6 faces of the cube.  Discard any
    /// that do not intersect the shape.  Then repeatedly choose the
    /// largest cell that intersects the shape and subdivide it.
    ///
    /// result contains the cells that will be part of the output, while pq
    /// contains cells that we may still subdivide further. Cells that are
    /// entirely contained within the region are immediately added to the output,
    /// while cells that do not intersect the region are immediately discarded.
    /// Therefore pq only contains cells that partially intersect the region.
    /// Candidates are prioritized first according to cell size (larger cells
    /// first), then by the number of intersecting children they have (fewest
    /// children first), and then by the number of fully contained children
    /// (fewest children first).
    fn covering_internal(&mut self) {
        self.initial_candidates();

        while let Some(mut cand) = self.pq.pop() {
            if !(!self.interior_covering || self.result.len() < self.constraint.max_cells) {
                break;
            }

            // For interior covering we keep subdividing no matter how many children
            // candidate has. If we reach MaxCells before expanding all children,
            // we will just use some of them.
            // For exterior covering we cannot do this, because result has to cover the
            // whole region, so all children have to be used.
            // candidate.numChildren == 1 case takes care of the situation when we
            // already have more then MaxCells in result (minLevel is too high).
            // Subdividing of the candidate with one child does no harm in this case.
            if self.interior_covering
                || cand.cell.level() < self.constraint.min_level
                || cand.children.len() == 1
                || self.result.len() + self.pq.len() + cand.children.len()
                    <= self.constraint.max_cells
            {
                for child in cand.children {
                    if !self.interior_covering || self.result.len() < self.constraint.max_cells {
                        self.add_candidate(child)
                    }
                }
            } else {
                cand.terminal = true;
                self.add_candidate(cand)
            }
        }

        self.pq.clear();
    }
}

impl RegionCoverer {
    fn new_coverer<'a, R>(&'a self, region: &'a R) -> Coverer<'a, R>
    where
        R: Region,
    {
        Coverer {
            constraint: self,

            region,
            result: Vec::new(),
            pq: BinaryHeap::new(),
            interior_covering: false,
        }
    }

    /// covering returns a CellUnion that covers the given region and satisfies the various
    /// restrictions.
    pub fn covering<R>(&self, region: &R) -> CellUnion
    where
        R: Region + 'static,
    {
        let mut covering = self.cellunion(region);
        covering.denormalize(
            clamp(self.min_level, 0, MAX_LEVEL as u8).into(),
            clamp(self.level_mod, 1, 3).into(),
        );
        covering
    }

    /// interior_covering returns a CellUnion that is contained within the given region and
    /// satisfies the various restrictions.
    pub fn interior_covering<R>(&self, region: &R) -> CellUnion
    where
        R: Region + 'static,
    {
        let mut int_covering = self.interior_cellunion(region);
        int_covering.denormalize(
            clamp(self.min_level, 0, MAX_LEVEL as u8).into(),
            clamp(self.level_mod, 1, 3).into(),
        );
        int_covering
    }

    /// cellunion returns a normalized CellUnion that covers the given region and
    /// satisfies the restrictions except for minLevel and levelMod. These criteria
    /// cannot be satisfied using a cell union because cell unions are
    /// automatically normalized by replacing four child cells with their parent
    /// whenever possible. (Note that the list of cell ids passed to the CellUnion
    /// constructor does in fact satisfy all the given restrictions.)
    fn cellunion<'a, R>(&self, region: &'a R) -> CellUnion
    where
        R: Region + 'static,
    {
        let mut c = self.new_coverer(region);
        c.covering_internal();
        let mut cu = CellUnion(c.result);
        cu.normalize();
        cu
    }

    /// interior_cellunion returns a normalized CellUnion that is contained within the given region and
    /// satisfies the restrictions except for minLevel and levelMod. These criteria
    /// cannot be satisfied using a cell union because cell unions are
    /// automatically normalized by replacing four child cells with their parent
    /// whenever possible. (Note that the list of cell ids passed to the CellUnion
    /// constructor does in fact satisfy all the given restrictions.)
    pub fn interior_cellunion<'a, R>(&self, region: &'a R) -> CellUnion
    where
        R: Region + 'static,
    {
        let mut c = self.new_coverer(region);
        c.interior_covering = true;
        c.covering_internal();
        let mut cu = CellUnion(c.result);
        cu.normalize();
        cu
    }

    /// FastCovering returns a CellUnion that covers the given region similar to Covering,
    /// except that this method is much faster and the coverings are not as tight.
    /// All of the usual parameters are respected (MaxCells, MinLevel, MaxLevel, and LevelMod),
    /// except that the implementation makes no attempt to take advantage of large values of
    /// MaxCells.  (A small number of cells will always be returned.)
    ///
    /// This function is useful as a starting point for algorithms that
    /// recursively subdivide cells.
    pub fn fast_covering<'a, R>(&self, region: &'a R) -> CellUnion
    where
        R: Region,
    {
        let mut cu = CellUnion(region.cell_union_bound());
        self.normalize_covering(&mut cu);
        cu
    }
}

impl RegionCoverer {
    /// adjustLevel returns the reduced "level" so that it satisfies levelMod. Levels smaller than minLevel
    /// are not affected (since cells at these levels are eventually expanded).
    fn adjust_level(&self, level: u8) -> u8 {
        if self.level_mod > 1 && level > self.min_level {
            level - ((level - self.min_level) % self.level_mod)
        } else {
            level
        }
    }

    /// normalizeCovering normalizes the "covering" so that it conforms to the current covering
    /// parameters (MaxCells, minLevel, maxLevel, and levelMod).
    /// This method makes no attempt to be optimal. In particular, if
    /// minLevel > 0 or levelMod > 1 then it may return more than the
    /// desired number of cells even when this isn't necessary.
    ///
    /// Note that when the covering parameters have their default values, almost
    /// all of the code in this function is skipped.
    fn normalize_covering(&self, covering: &mut CellUnion) {
        // If any cells are too small, or don't satisfy level_mod, then replace them with ancestors.
        if self.max_level < (MAX_LEVEL as u8) || self.level_mod > 1 {
            for ci in covering.0.iter_mut() {
                let level = ci.level() as u8;
                let new_level = self.adjust_level(min(level, self.max_level));
                if new_level != level {
                    *ci = ci.parent(new_level.into());
                }
            }
        }

        // If there are still too many cells, then repeatedly replace two adjacent
        // cells in CellID order by their lowest common ancestor.
        covering.normalize();
        while covering.0.len() > self.max_cells {
            {
                let mut best_index = -1isize;
                let mut best_level = -1isize;

                let v = &mut covering.0;
                for i in 0..(v.len() - 1) {
                    if let Some(level) = v[i].common_ancestor_level(&v[i + 1]) {
                        let level = self.adjust_level(level as u8) as isize;
                        if level > best_level {
                            best_level = level;
                            best_index = i as isize;
                        }
                    }
                }

                if best_level < self.min_level as isize {
                    break;
                }
                v[best_index as usize] = v[best_index as usize].parent(best_level as u64);
            }

            covering.normalize();
        }

        // Make sure that the covering satisfies minLevel and levelMod,
        // possibly at the expense of satisfying MaxCells.
        if self.min_level > 0 || self.level_mod > 1 {
            covering.denormalize(self.min_level.into(), self.level_mod.into());
        }
    }
}

// BUG(akashagrawal): The differences from the C++ version FloodFill, SimpleCovering

#[cfg(test)]
mod tests {
    use super::*;
    use crate::s2::cell::*;
    use crate::s2::metric::*;
    use crate::s2::random;
    use rand::Rng;
    use std::f64::consts::PI;

    #[test]
    fn test_coverer_random_cells() {
        let mut rng = random::rng();
        let rc = RegionCoverer {
            min_level: 0,
            max_level: 30,
            level_mod: 1,
            max_cells: 1,
        };

        for _ in 0..10000 {
            let id = random::cellid(&mut rng);

            let covering = rc.covering(&Cell::from(&id));
            assert_eq!(covering.0.len(), 1);
            assert_eq!(covering.0[0], id);
        }
    }

    use std::collections::{hash_map, HashMap};

    fn check_covering<R>(rc: &RegionCoverer, r: &R, covering: &CellUnion, interior: bool)
    where
        R: Region,
    {
        // Keep track of how many cells have the same rc.min_level ancestor.
        let mut min_level_cells = HashMap::new();
        for ci in covering.0.iter() {
            let level = ci.level() as u8;
            assert!(rc.min_level <= level && level <= rc.max_level);
            assert_eq!((level - rc.min_level) % rc.level_mod, 0);

            let parent = ci.parent(rc.min_level.into());
            match min_level_cells.entry(parent) {
                hash_map::Entry::Occupied(mut e) => {
                    let v = e.get_mut();
                    *v = *v + 1;
                }
                hash_map::Entry::Vacant(e) => {
                    e.insert(1);
                }
            }
        }

        if covering.0.len() > rc.max_cells {
            // If the covering has more than the requested number of cells, then check
            // that the cell count cannot be reduced by using the parent of some cell.
            for (_, count) in min_level_cells.iter() {
                assert_eq!(*count, 1);
            }
        }
        if interior {
            for ci in covering.0.iter() {
                assert!(true, r.contains_cell(&Cell::from(ci)));
            }
        } else {
            let mut temp_coverer = covering.clone();
            temp_coverer.normalize();
            check_covering_tight(r, &temp_coverer, true, CellID(0));
        }
    }

    // check_covering_tight checks that "cover" completely covers the given region.
    // If "check_tight" is true, also checks that it does not contain any cells that
    // do not intersect the given region. ("id" is only used internally.)
    fn check_covering_tight<R>(r: &R, cover: &CellUnion, check_tight: bool, id: CellID)
    where
        R: Region,
    {
        if !id.is_valid() {
            for f in 0..6 {
                check_covering_tight(r, cover, check_tight, CellID::from_face(f));
            }
            return;
        }

        let cell = Cell::from(&id);
        if !r.intersects_cell(&cell) {
            // If region does not intersect id, then neither should the covering.
            if check_tight {
                assert_eq!(false, cover.intersects_cellid(&id));
            }
        } else if !cover.contains_cellid(&id) {
            // The region may intersect id, but we can't assert that the covering
            // intersects id because we may discover that the region does not actually
            // intersect upon further subdivision.  (IntersectsCell is not exact.)
            assert_eq!(false, r.contains_cell(&cell));
            assert_eq!(false, id.is_leaf());

            for child in id.child_iter() {
                check_covering_tight(r, cover, check_tight, child);
            }
        }
    }

    #[test]
    fn test_coverer_random_caps() {
        let mut rng = random::rng();
        for _ in 0..1000 {
            let mut min_level = rng.gen_range(0, (MAX_LEVEL + 1) as u8);
            let mut max_level = rng.gen_range(0, (MAX_LEVEL + 1) as u8);
            if min_level > max_level {
                let tmp = max_level;
                max_level = min_level;
                min_level = tmp;
            }
            assert!(min_level <= max_level);

            let level_mod = rng.gen_range(1, 4);
            let max_cells = random::skewed_int(&mut rng, 10);

            let rc = RegionCoverer {
                min_level,
                max_level,
                level_mod,
                max_cells,
            };

            let max_area =
                (4. * PI).min((3. * (max_cells as f64) + 1.) * AVG_AREAMETRIC.value(min_level));

            let r = random::cap(&mut rng, 0.1 * AVG_AREAMETRIC.value(max_level), max_area);

            let mut covering = rc.covering(&r);
            check_covering(&rc, &r, &covering, false);

            let interior = rc.interior_covering(&r);
            check_covering(&rc, &r, &interior, true);

            // Check that Covering is deterministic.
            let covering2 = rc.covering(&r);
            assert_eq!(covering, covering2);

            // Also check Denormalize. The denormalized covering
            // may still be different and smaller than "covering" because
            // s2.RegionCoverer does not guarantee that it will not output all four
            // children of the same parent.
            covering.denormalize(min_level as u64, level_mod as u64);
            check_covering(&rc, &r, &covering, false);
        }
    }
}
