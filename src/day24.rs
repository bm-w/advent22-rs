// Copyright (c) 2022 Bastiaan Marinus van de Weerd


#[cfg_attr(test, derive(Debug))]
#[derive(Clone, Copy)]
enum Dir { Backward, Forward }

#[cfg_attr(test, derive(Debug))]
struct Blizzard {
	/// Initial distance from corresponding edge (wall).
	start: usize,
	/// Northward / southward for blizzards corresponding to the north edge (wall),
	/// eastward / westward for those corresponding to the west edge (wall).
	dir: Dir,
}

#[cfg_attr(test, derive(Debug))]
struct Valley {
	/// Also implies valley size (East->West and North->South, excluding walls).
	blizzards: [Vec<Vec<Blizzard>>; 2],
}

enum Axis { X, Y }

impl Valley {

	// X span (excl. east / west walls), Y span (incl. north / south walls), & area (the product).
	fn geometry(&self) -> ([usize; 2], usize) {
		let [dx, dy] = [self.blizzards[0].len(), self.blizzards[1].len() + 2];
		([dx, dy], dx * dy)
	}

	fn adjacent_positions(&self, pos: usize) -> impl Iterator<Item = usize> + '_ {
		let ([dx, _], area) = self.geometry();
		[
			pos.checked_add_signed(-(dx as isize)),
			(pos % dx > 0).then_some(pos.checked_add_signed(-1)).flatten(),
			(pos % dx < dx - 1).then_some(pos + 1),
			(pos < area - dx).then_some(pos + dx),
		].into_iter().flatten()
	}

	fn for_each_blizzard_hit<'s>(
		&'s self,
		pos: usize,
		time: usize,
		mut f: impl FnMut(Axis, &'s Blizzard, &mut bool)
	) {
		if pos == 0 { return }
		let ([dx, dy], area) = self.geometry();
		let [x, y] = [pos % dx, pos / dx];
		if pos == area - 1 { return }

		let mut stop = false;

		for b in &self.blizzards[1][y - 1] {
			let bx = match b.dir {
				Dir::Backward => (b.start + dx - time % dx) % dx,
				Dir::Forward => (b.start + time) % dx,
			};
			if bx == x { f(Axis::X, b, &mut stop) }
			if stop { return }
		}

		for b in &self.blizzards[0][x] {
			let by = match b.dir {
				Dir::Backward => 1 + (b.start + dy - 2 - time % (dy - 2)) % (dy - 2),
				Dir::Forward => 1 + (b.start + time) % (dy - 2),
			};
			if by == y { f(Axis::Y, b, &mut stop) }
			if stop { return }
		}
	}

	#[cfg(test)]
	/// Blizzards in X & Y directions, backward & forward
	fn blizzard_hits(&self, pos: usize, time: usize) -> [[Option<&Blizzard>; 2]; 2] {
		let mut hits = [[None, None], [None, None]];

		let axis_idx = |axis| match axis { Axis::X => 0, _ => 1 };
		let dir_idx = |dir| match dir { Dir::Backward => 0, _ => 1 };
		self.for_each_blizzard_hit(pos, time, |axis, blizzard, _| {
			hits[axis_idx(axis)][dir_idx(blizzard.dir)] = Some(blizzard)
		});

		hits
	}

	fn is_position_hit_by_blizzard(&self, pos: usize, time: usize) -> bool {
		let mut is_hit = false;
		self.for_each_blizzard_hit(pos, time, |_, _, stop| { is_hit = true; *stop = true });
		is_hit
	}

	fn accessible_adjacent_positions(&self, pos: usize, time: usize)
	-> impl Iterator<Item = usize> + '_ {
		let ([dx, _], area) = self.geometry();
		self.adjacent_positions(pos).filter(move |&pos| {
			if pos == 0 || pos == area - 1 { return true } // Start & end positions
			if pos < dx || pos >= area - dx { return false } // North & south walls
			!self.is_position_hit_by_blizzard(pos, time)
		})
	}
}


fn input_valley_from_str(s: &str) -> Valley {
	s.parse().unwrap()
}


fn part1_impl(input_valley: Valley) -> usize {

	// A* with square distance to target as heuristic
	use std::collections::{BinaryHeap, HashMap, hash_map::Entry};

	#[cfg_attr(test, derive(Debug))]
	#[derive(PartialEq, Eq)]
	struct State {
		pos: usize,
		steps: usize,
		elapsed: usize,
		heur: usize,
		#[cfg(LOGGING)]
		dbg_prev_pos: Option<usize>
	}

	impl State {
		fn estimated_elapsed(&self) -> usize {
			self.elapsed + self.heur
		}
	}

	impl PartialOrd for State {
		fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
			Some(self.cmp(other))
		}
	}
	
	impl Ord for State {
		fn cmp(&self, other: &Self) -> std::cmp::Ordering {
			self.estimated_elapsed().cmp(&other.estimated_elapsed()).reverse()
				.then_with(|| self.heur.cmp(&other.heur).reverse())
				.then_with(|| self.steps.cmp(&other.steps).reverse())
				.then_with(|| self.pos.cmp(&other.pos))
		}
	}

	let (heur, end_pos) = {
		let ([dx, dy], area) = input_valley.geometry();
		let [x_end, y_end] = [dx - 1, dy - 1];
		(move |pos| {
			let [x, y] = [x_end - pos % dx, y_end - pos / dx];
			x + y
			// let dsq = x * x + y * y;
			// for d in 0.. { if (d + 1) * (d + 1) >= dsq { return d } }
			// unreachable!()
		}, area - 1)
	};

	let mut heap = BinaryHeap::new();
	heap.push(State { pos: 0, steps: 0, elapsed: 0, heur: heur(0),
		#[cfg(LOGGING)]
		dbg_prev_pos: None,
	});
	let mut steps = HashMap::new();

	#[cfg(LOGGING)]
	let mut dbg_prev_poss = HashMap::new();

	#[cfg(LOGGING)]
	let mut dbg_i = 0;
	while let Some(state) = heap.pop() {
		#[cfg(LOGGING)]
		let _dbg_i = { dbg_i += 1; dbg_i - 1 };

		if state.pos == end_pos {
			#[cfg(LOGGING)]
			{
				use std::fmt::Write as _;
				let path = (1..state.elapsed)
					.rev()
					.scan(state.dbg_prev_pos.unwrap(), |acc, time| {
						let prev_pos = *acc;
						*acc = dbg_prev_poss[&(prev_pos, time)];
						Some(prev_pos)
					})
					.collect::<std::collections::HashSet<_>>();
				let mut s = String::new();
				input_valley.fmt_time(&mut s,
					|pos| if pos == end_pos { Some('E') }
						else if path.contains(&pos) { Some('~') }
						else { None },
					state.elapsed).unwrap();
				s.write_char('\n').unwrap();
				println!("{}{dbg_i}: {state:?}; {}", s, state.estimated_elapsed());
			}
			return state.elapsed
		}

		match steps.entry((state.pos, state.elapsed)) {
			Entry::Vacant(entry) => { entry.insert(state.steps); }
			Entry::Occupied(mut entry) => {
				if *entry.get() <= state.steps { continue }
				entry.insert(state.steps);
			}
		}

		#[cfg(LOGGING)]
		if dbg_i % 1000 == 0 {
			// use std::fmt::Write as _;
			let mut _s = String::new();
			// s.write_char('\n').unwrap();
			// input_valley.fmt_time(&mut s,
			// 	|pos| (pos == state.pos).then_some('E'),
			// 	state.elapsed).unwrap();
			// s.write_char('\n').unwrap();
			println!("{}  {dbg_i}: {state:?}; {}", _s, state.estimated_elapsed());
		}

		#[cfg(LOGGING)]
		if let Some(dbg_prev_pos) = state.dbg_prev_pos {
			dbg_prev_poss.insert((state.pos, state.elapsed), dbg_prev_pos);
		}

		let elapsed = state.elapsed + 1;
		if !input_valley.is_position_hit_by_blizzard(state.pos, elapsed) {
			heap.push(State { elapsed,
				#[cfg(LOGGING)]
				dbg_prev_pos: Some(state.pos),
				..state });
		}
		for pos in input_valley.accessible_adjacent_positions(state.pos, elapsed) {
			heap.push(State { pos, steps: state.steps + 1, elapsed, heur: heur(pos),
				#[cfg(LOGGING)]
				dbg_prev_pos: Some(state.pos),
			});
		}
	}

	todo!()
}

pub(crate) fn part1() -> usize {
	part1_impl(input_valley_from_str(include_str!("day24.txt")))
}


pub(crate) fn part2() -> &'static str {
	"WIP"
}


mod parsing {
	use std::str::FromStr;
	use super::{Dir, Blizzard, Valley};

	fn try_strip_prefix<'s>(s: &'s str, prefix: &str) -> Result<&'s str, &'s str> {
		s.strip_prefix(prefix).ok_or_else(|| {
			let p = s.bytes().zip(prefix.bytes()).position(|(s, p)| s != p);
			&s[p.unwrap_or(s.len())..]
		})
	}

	macro_rules! str_offset { ( $s0:expr, $s:expr ) => {
		// SAFETY: It is assumed that `$s0` and `$s` point into the same string slice
		unsafe { $s.as_ptr().offset_from($s0.as_ptr()) as usize }
	} }

	#[allow(dead_code)]
	#[derive(Debug)]
	pub(super) enum ValleyError {
		LineLen { line: usize, len: Option<usize>, found: usize },
		InvalidByte { line: usize, column: usize, found: u8 },
		EndOfString,
	}

	impl FromStr for Valley {
		type Err = ValleyError;
		fn from_str(s: &str) -> Result<Self, Self::Err> {
			use ValleyError as E;

			let mut blizzards = (Option::<Vec<Vec<Blizzard>>>::None, vec![]);
			macro_rules! len { () => { blizzards.0.as_ref().map(|bb| bb.len()) } }

			let (mut c, mut l, mut cx0, mut south_edge) = (0, 0, 0, false);

			macro_rules! inv_byte_err { ( $c:expr, $found:expr ) => {
				E::InvalidByte { line: l + 1, column: $c + 1, found: $found }
			} }

			while c < s.len() {
				if Some(c) == len!() { return Err(
					E::LineLen { line: l + 1, len: len!(), found: c + 1 }) }
				match blizzards.0.as_mut() {
					None => {
						_ = try_strip_prefix(s, "#.#").map_err(|e| if e.is_empty() {
							E::LineLen { line: 1, len: None, found: str_offset!(s, e) }
						} else {
							inv_byte_err!(s.len() - e.len(), e.as_bytes()[0])
						})?;

						let len = s.bytes().position(|b| b == b'\n').ok_or(E::EndOfString)?;
						blizzards.0 = Some(Vec::from_iter(
							std::iter::from_fn(|| Some(vec![])).take(len - 2)));
						l = 1;
						c = len + 1;
						cx0 = c;
					}
					Some(x_blizzards) => {
						if c >= s.len() { return Err(E::EndOfString); }
						let (cx, len) = (c - cx0, x_blizzards.len() + 2);

						macro_rules! ret_line_len_err { () => {
							return Err(E::LineLen { line: l + 1, len: Some(len), found: cx + 1 })
						} }

						match s.as_bytes()[c] {
							b'\n' => {
								if cx + 1 < len { ret_line_len_err!() }
								l += 1;
								cx0 = c + 1;
							}
							_ if cx == len => ret_line_len_err!(),
							b'#' if cx == 0 || cx == len - 1 => (),
							b'#' if cx == 1 => { south_edge = true },
							b'#' if south_edge && cx < len - 2 => (),
							b'.' if south_edge && cx == len - 2 => (),
							found if south_edge => return Err(inv_byte_err!(cx, found)),
							_ if blizzards.1.len() < l => {
								// dbg!(l, cx, s.as_bytes()[c] as char, blizzards.1.len());
								blizzards.1.push(vec![]); continue }
							b'.' if cx > 0 && cx < len - 1 => (),
							b @ (b'^'|b'v') => {
								let dir = if b == b'^' { Dir::Backward } else { Dir::Forward };
								x_blizzards[cx - 1].push(Blizzard { start: l - 1, dir })
							}
							b @ (b'<'|b'>') => {
								let dir = if b == b'<' { Dir::Backward } else { Dir::Forward };
								blizzards.1.last_mut().unwrap().push(
									Blizzard { start: cx - 1, dir })
							}
							found => return Err(inv_byte_err!(cx, found))
						}

						c += 1;
					}
				}
			}

			let Some(blizzards_x) = blizzards.0 else { return Err(E::EndOfString) };
			if !south_edge || c > cx0 && c - cx0 < blizzards_x.len() + 2 {
				return Err(E::EndOfString) };

			Ok(Valley { blizzards: [blizzards_x, blizzards.1] })
		}
	}
}


#[cfg(test)]
impl Valley {
	fn fmt_time(&self,
		f: &mut impl std::fmt::Write,
		pos: impl Fn(usize) -> Option<char>,
		time: usize,
	) -> std::fmt::Result {
		// use std::fmt::Write;
		let ([dx, dy], area) = self.geometry();

		writeln!(f, "#{}{}", pos(0).unwrap_or('.'), "#".repeat(dx))?;
		for y in 1..dy - 1 {
			f.write_char('#')?;
			for x in 0..dx {
				let p = y * dx + x;
				f.write_char(pos(p).unwrap_or_else(|| match self.blizzard_hits(y * dx + x, time) {
					[[None, None], [None, None]] => '.',
					[[Some(_), None], [None, None]] => '<',
					[[None, Some(_)], [None, None]] => '>',
					[[None, None], [Some(_), None]] => '^',
					[[None, None], [None, Some(_)]] => 'v',
					hits => (b'a' + hits.into_iter()
						.flatten()
						.enumerate()
						.map(|(i, b)| u8::from(b.is_some()) << (3 - i))
						.fold(0, |acc, b| acc | b)) as char,
				}))?
			}
			f.write_char('#')?;
			f.write_char('\n')?;
		}
		write!(f, "{}{}#", "#".repeat(dx), pos(area - 1).unwrap_or('.'))?;

		Ok(())
	}
}

#[cfg(test)]
impl std::fmt::Display for Valley {
	fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
		self.fmt_time(f, |_| None, 0)
	}
}


#[test]
fn tests() {
	const INPUTS: [&str; 2] = [
		indoc::indoc! { "
			#.#####
			#.....#
			#>....#
			#.....#
			#...v.#
			#.....#
			#####.#
		" },
		indoc::indoc! { "
			#.######
			#>>.<^<#
			#.<..<<#
			#>v.><>#
			#<^v^^>#
			######.#
		" },
	];
	assert_eq!(part1_impl(input_valley_from_str(INPUTS[0])), 10);
	assert_eq!(part1_impl(input_valley_from_str(INPUTS[1])), 18);
	assert_eq!(part1(), 322);
}
