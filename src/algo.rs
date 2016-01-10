/// Breadth First Search
pub mod bfs {

    use hex2d::Coordinate;
    use hex2d;

    use std::hash;
    use std::collections::VecDeque;
    use std::collections::HashMap;
    use std::collections::hash_map::Entry::{Occupied,Vacant};

    struct Visited<I = i32>
        where I : hex2d::Integer
        {
            prev : Coordinate<I>,
            dist : u32,
        }

    /// Breadth First Search
    ///
    /// Use BFS to find closest (in walk steps) Coordinates that satisfy `is_dest` and can be
    /// reached with a walk through coordinates for which `can_pass` returns true.
    pub struct Traverser<FCanPass, FIsDest, I = i32> where
        I : hex2d::Integer,
        I : hash::Hash,
        FCanPass : Fn(Coordinate<I>) -> bool,
        FIsDest : Fn(Coordinate<I>) -> bool
    {
        visited : HashMap<Coordinate<I>, Visited<I>>,
        to_traverse : VecDeque<Coordinate<I>>,
        can_pass : FCanPass,
        is_dest : FIsDest,
        start : Coordinate<I>,
    }

    impl<FCanPass, FIsDest, I> Traverser<FCanPass, FIsDest, I> where
        I : hex2d::Integer,
        I : hash::Hash,
        FCanPass : Fn(Coordinate<I>) -> bool,
        FIsDest : Fn(Coordinate<I>) -> bool
    {

        /// Create a Traverser instance with initial conditions
        pub fn new(can_pass : FCanPass, is_dest : FIsDest, start: Coordinate<I>) -> Traverser<FCanPass, FIsDest, I> {
            let mut to_traverse = VecDeque::new();
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
    use hex2d;
    use hex2d::Angle::{Left,Right};

    use hex2d::Direction;
    use hex2d::Coordinate;

    fn los_rec<FOpaqueness, FVisible, I=i32>(
        opaqueness : &FOpaqueness,
        visible : &mut FVisible,
        light: I,
        pos : Coordinate<I>,
        start_dir : Direction,
        main_dir : Direction,
        dir : Option<Direction>,
        pdir : Option<Direction>,
    ) where
        I : hex2d::Integer,
        FOpaqueness : Fn(Coordinate<I>) -> I,
        FVisible : FnMut(Coordinate<I>, I)
        {

            let mut light = light;
            let opaq = opaqueness(pos);

            if opaq >= light {
                return;
            } else {
                light = light - opaq;
            }

            visible(pos, light);

            let neighbors = match (dir, pdir) {
                (Some(dir), Some(pdir)) => {
                    if dir == pdir {
                        vec!(dir)
                    } else {
                        vec!(dir, pdir)
                    }
                },
                (Some(dir), None) => {
                    if main_dir == dir {
                        vec!(dir, dir + Left, dir + Right)
                    } else {
                        vec!(dir, main_dir)
                    }
                },
                _ => {
                    vec!(main_dir, main_dir + Left, main_dir + Right)
                }
            };

            for &d in neighbors.iter() {
                let npos = pos + d;
                match dir {
                    Some(_) => los_rec::<FOpaqueness, FVisible, I>(opaqueness, visible, light, npos, start_dir, d, Some(d), dir),
                    None => los_rec::<FOpaqueness, FVisible, I>(opaqueness, visible, light, npos, start_dir, main_dir, Some(d), dir),
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
        I : hex2d::Integer,
        FOpaqueness : Fn(Coordinate<I>) -> I,
        FVisible : FnMut(Coordinate<I>, I)
        {
            for dir in dirs.iter() {
                los_rec::<FOpaqueness, FVisible, I>(opaqueness, visible, light, pos, *dir, *dir, None, None);
            }
        }
}

/// Combination of tricky Los with straight line checking
pub mod los2 {
    use hex2d;
    use hex2d::Angle::{Left, Right, Forward};
    use hex2d::Direction;
    use hex2d::Coordinate;
    use num::{FromPrimitive};
    use std::collections::HashSet;
    use std::hash;
    use std::ops::{Add};
    use std::cmp;

    fn los_check_line<FOpaqueness, I=u32>(
        opaqueness : &FOpaqueness,
        light: I,
        start : Coordinate<I>,
        pos : Coordinate<I>,
        dir : Direction,
        ) -> (bool, I)
        where
        I : hex2d::Integer,
        I : hash::Hash+Eq,
        for <'a> &'a I: Add<&'a I, Output = I>,
        FOpaqueness : Fn(Coordinate<I>) -> I,
    {

        let mut opaq_sum1 : I = FromPrimitive::from_i8(0).unwrap();
        let mut last1 = start;

        let mut opaq_sum2 : I = FromPrimitive::from_i8(0).unwrap();
        let mut last2 = start;

        for &(c1, c2) in start.line_to_with_edge_detection(pos).iter() {
            if opaq_sum1 < light {
                let opaq1 = opaqueness(c1);
                opaq_sum1 = opaq_sum1 + opaq1;
                last1 = c1;
            }

            if opaq_sum2 < light {
                let opaq2 = opaqueness(c2);
                opaq_sum2 = opaq_sum2 + opaq2;
                last2 = c2;
            }
        };

        match (last1 == pos, last2 == pos) {
            (true, true) => (true, light - cmp::min(opaq_sum1, opaq_sum2)),
            (true, false) => (true, light - opaq_sum1),
            (false, true) => (true, light - opaq_sum2),
            (false, false) => (false, light - light),
        }
    }

    fn los_rec<FOpaqueness, FVisible, I=i32>(
        opaqueness : &FOpaqueness,
        visible : &mut FVisible,
        light: I,
        start : Coordinate<I>,
        pos : Coordinate<I>,
        dir : Direction,
        visited : &mut HashSet<Coordinate<I>>,
    ) where
        I : hex2d::Integer,
        I : hash::Hash+Eq,
        for <'a> &'a I: Add<&'a I, Output = I>,
        FOpaqueness : Fn(Coordinate<I>) -> I,
        FVisible : FnMut(Coordinate<I>, I)
        {
            if visited.contains(&pos) {
                return;
            } else {
                visited.insert(pos);
            }

            let (directly_visible, v_light) = los_check_line(
                opaqueness,
                light,
                start,
                pos,
                dir);

            if directly_visible {
                visible(pos, v_light);
            } else {
                let dir_to = start.direction_to_cw(pos).unwrap_or(dir);
                let neighbors = vec!(Left, Right);
                for npos in neighbors.iter()
                    .map(|&rd| dir_to + rd)
                        .map(|dir| pos + dir) {

                            let (side_visible, v_light) = los_check_line(
                                opaqueness,
                                light,
                                start,
                                npos,
                                dir);

                            if side_visible {
                                visible(pos, v_light);
                            }
                        }
                return;
            }

            let neighbors = vec!(Forward, Left, Right);

            for &a in neighbors.iter() {
                let npos = pos + (dir + a);
                los_rec::<FOpaqueness, FVisible, I>(
                    opaqueness, visible, light, start, npos, dir, visited
                    );
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
        I : hex2d::Integer,
        I : hash::Hash,
        for <'a> &'a I: Add<&'a I, Output = I>,
        FOpaqueness : Fn(Coordinate<I>) -> I,
        FVisible : FnMut(Coordinate<I>, I)
        {
            for dir in dirs.iter() {
                let mut visited = HashSet::new();
                los_rec::<FOpaqueness, FVisible, I>(
                    opaqueness, visible, light, pos, pos, *dir, &mut visited
                    );
            }
        }
}
