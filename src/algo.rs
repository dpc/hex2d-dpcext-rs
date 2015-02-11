/// Breadth First Search
pub mod bfs {

    use hex2d::Coordinate;

    use std;
    use std::hash;
    use std::num::{SignedInt, FromPrimitive};
    use num::integer::{Integer};
    use std::collections::ring_buf::RingBuf;
    use std::collections::HashMap;
    use std::collections::hash_map::Entry::{Occupied,Vacant};

    struct Visited<H, I = i32>
        where I : SignedInt+hash::Hash<std::collections::hash_map::Hasher> {
        prev : Coordinate<I>,
        dist : u32,
    }

    /// Breadth First Search
    ///
    /// Use BFS to find closest (in walk steps) Coordinates that satisfy `is_dest` and can be
    /// reached with a walk through coordinates for which `can_pass` returns true.
    pub struct Traverser<FCanPass, FIsDest, H, I = i32> where
        I : SignedInt+hash::Hash<std::collections::hash_map::Hasher>,
        FCanPass : Fn(Coordinate<I>) -> bool,
        FIsDest : Fn(Coordinate<I>) -> bool
    {
        visited : HashMap<Coordinate<I>, Visited<H, I>>,
        to_traverse : RingBuf<Coordinate<I>>,
        can_pass : FCanPass,
        is_dest : FIsDest,
        start : Coordinate<I>,
    }

    impl<FCanPass, FIsDest, H, I> Traverser<FCanPass, FIsDest, H, I> where
        I : SignedInt+FromPrimitive+Integer+hash::Hash<std::collections::hash_map::Hasher>,
        FCanPass : Fn(Coordinate<I>) -> bool,
        FIsDest : Fn(Coordinate<I>) -> bool
    {

        /// Create a Traverser instance with initial conditions
        pub fn new(can_pass : FCanPass, is_dest : FIsDest, start: Coordinate<I>) -> Traverser<FCanPass, FIsDest, H, I> {
            let mut to_traverse = RingBuf::new();
            to_traverse.push_back(start);

            let mut visited = HashMap::new();
            visited.insert(start, Visited{prev: start, dist: 0});

            Traverser {
                visited: visited,
                to_traverse: to_traverse,
                can_pass: can_pass,
                is_dest: is_dest,
                start: start,
            }
        }

        /// Find next closest coordinate.
        ///
        /// Can be called multiple times, each time returning next coordinate
        pub fn find(&mut self) -> Option<Coordinate<I>> {

            loop {
                let pos = match self.to_traverse.pop_front() {
                    None => return None,
                    Some(coord) => coord,
                };

                // Traverse before returning, so `find` can be call subsequently
                // for more than just first answer
                if (self.can_pass)(pos) {

                    let &Visited{dist, ..} = self.visited.get(&pos).expect("BFS: Should have been visited already");

                    let dist = dist + 1;

                    for &npos in pos.neighbors().iter() {
                        match self.visited.entry(npos) {
                            Occupied(_) => { /* already visited */ }
                            Vacant(entry) => {
                                entry.insert(Visited{prev: pos, dist: dist});
                                self.to_traverse.push_back(npos);
                            }
                        }
                    }
                }

                if (self.is_dest)(pos) {
                    return Some(pos);
                }
            }
        }

        /// Return neighbor Coordinate to `pos` that is one step closer to
        /// `start` from initial conditions.
        ///
        /// Useful for finding whole path to a Coordinate returned by `find`.
        ///
        /// Returns `None` for Coordinates that were not yet visited.
        /// Returns `start` for `start` (from initial conditions)
        pub fn backtrace(&self, pos : Coordinate<I>) -> Option<Coordinate<I>> {
            self.visited.get(&pos).map(|entry| entry.prev)
        }

        /// Perform a recursive `backtrace` walk to find a neighbor of `start` that leads to the
        /// Coordinate returned by `find()`.
        ///
        /// Returns `None` for Coordinates that were not yet visited.
        /// Returns `start` for `start` (from initial conditions)
        pub fn backtrace_last(&self, mut pos : Coordinate<I>) -> Option<Coordinate<I>> {
            loop {
                pos = match self.visited.get(&pos) {
                    None => return None,
                    Some(entry) => {
                        if entry.prev == self.start {
                            return Some(pos);
                        } else {
                            entry.prev
                        }
                    }
                }
            }
        }
    }
}

/// Very tricky, but (hopefully) good enough, recursive LoS algorithm
pub mod los {
    use hex2d::Angle::{Left,Right};
    use hex2d::Direction;
    use hex2d::Coordinate;
    use std::num::{SignedInt, FromPrimitive};
    use num::integer::{Integer};

    fn los_rec<FOpaqueness, FVisible, I=i32>(
        opaqueness : &FOpaqueness,
        visible : &mut FVisible,
        light: I,
        p : Coordinate<I>,
        main_dir : Direction,
        dir : Option<Direction>,
        pdir : Option<Direction>,
    ) where
        I : SignedInt+FromPrimitive+Integer,
        FOpaqueness : Fn(Coordinate<I>) -> I,
        FVisible : FnMut(Coordinate<I>)
        {
            visible(p);

            let mut light = light;
            let opaq = opaqueness(p);

            if opaq >= light {
                return;
            } else {
                light = light - opaq;
            }

            let neighbors = match (dir, pdir) {
                (Some(dir), Some(pdir)) => {

                    if main_dir == dir {
                        visible(p + (main_dir + Right));
                        visible(p + (main_dir + Left));
                    }

                    if dir == pdir {
                        vec!(dir)
                    } else {
                        vec!(dir, pdir)
                    }
                },
                (Some(dir), None) => {
                    if main_dir == dir {
                        visible(p + (main_dir + Right));
                        visible(p + (main_dir + Left));
                        vec!(dir, dir + Left, dir + Right)
                    } else {
                        visible((p + main_dir));
                        vec!(dir, main_dir)
                    }
                },
                _ => {
                    visible(p + main_dir);
                    visible(p + (main_dir + Left));
                    visible(p + (main_dir + Right));
                    vec!(main_dir, main_dir + Left, main_dir + Right)
                }
            };

            for &d in neighbors.iter() {
                let n = p + d;
                match dir {
                    Some(_) => los_rec::<FOpaqueness, FVisible, I>(opaqueness, visible, light, n, d, Some(d), dir),
                    None => los_rec::<FOpaqueness, FVisible, I>(opaqueness, visible, light, n, main_dir, Some(d), dir),
                }
            }
        }


    /// Starting from `pos` in direction `dir`, call `visible` for each visible Coordinate.
    ///
    /// Use `light` as starting range of the LoS. For each visible Coordinate, the value returned
    /// by `opaqueness` will be subtracted from `light` to check if the LoS should finish due to
    /// "lack of visibility". `opaqueness` should typically return 1 for fully transparent
    /// Coordinates, and anything bigger than initial `light` for fully opaque Coordinates.
    pub fn los<FOpaqueness, FVisible, I=i32>(
        opaqueness : &FOpaqueness,
        visible : &mut FVisible,
        light: I,
        pos : Coordinate<I>,
        dirs : &[Direction],
    ) where
        I : SignedInt+FromPrimitive+Integer,
        FOpaqueness : Fn(Coordinate<I>) -> I,
        FVisible : FnMut(Coordinate<I>)
        {
            for dir in dirs.iter() {
                los_rec::<FOpaqueness, FVisible, I>(opaqueness, visible, light, pos, *dir, None, None);
            }
        }
}
