// Copyright (c) 2022 Bastiaan Marinus van de Weerd


enum Dir { North, East, South, West, }

struct Valley {
	/// Blizzard direction (if any) initially at corresponding position.
	blizzards: Vec<Option<Dir>>,
	/// West-east valley length.
	stride: usize,
}

impl Valley {
	// West-east valley length (excl. walls), south-north valley length (incl. walls), & area.
	fn geometry(&self) -> ([usize; 2], usize) {
		let [dx, dy] = [self.stride, self.blizzards.len() / self.stride + 2];
		([dx, dy], dx * dy)
	}

	/// Positions adjacent to `pos` regardless of walls or blizzard hits.
	fn adjacent_positions(&self, pos: usize) -> impl Iterator<Item = usize> + '_ {
		let ([dx, _], area) = self.geometry();
		[
			pos.checked_add_signed(-(dx as isize)),
			(pos % dx > 0).then_some(pos.checked_add_signed(-1)).flatten(),
			(pos % dx < dx - 1).then_some(pos + 1),
			(pos < area - dx).then_some(pos + dx),
		].into_iter().flatten()
	}

	/// Hits from blizzards at `pos` & `time`.
	fn blizzard_hits(&self, pos: usize, time: usize) -> [bool; 4] {
		if pos == 0 { return [false, false, false, false] }
		let ([dx, dy], area) = self.geometry();
		let [x, y] = [pos % dx, pos / dx];
		if pos == area - 1 { return [false, false, false, false] }

		macro_rules! blizzard_matches_dir { ( $bx:expr, $by:expr, $dir:ident ) => {
			matches!(self.blizzards[dx * $by + $bx], Some(Dir::$dir))
		} }

		let north = blizzard_matches_dir!(x, (y - 1 + time) % (dy - 2), North);
		let east = blizzard_matches_dir!((x + dx - time % dx) % dx, y - 1, East);
		let south = blizzard_matches_dir!(x, (y + dy - 3 - time % (dy - 2)) % (dy - 2), South);
		let west = blizzard_matches_dir!((x + time) % dx, y - 1, West);

		[north, east, south, west]
	}

	/// Returns whether any blizzard hits `pos` at `time`.
	fn is_position_hit_by_blizzard(&self, pos: usize, time: usize) -> bool {
		self.blizzard_hits(pos, time).contains(&true)
	}

	/// Non-wall positions adjacent to `pos` not hit by any blizzards at `time`.
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

fn input_valley() -> Valley {
	input_valley_from_str(include_str!("day24.txt"))
}


fn part1and2_impl<const REVERSE: bool>(input_valley: &Valley, start_time: usize) -> usize {

	// A* with elapsed time plus Manhattan distance to the target as estimated cost
	use std::collections::{BinaryHeap, HashMap, hash_map::Entry};

	#[cfg_attr(LOGGING, derive(Debug))]
	#[derive(PartialEq, Eq)]
	struct State {
		pos: usize,
		steps: usize,
		elapsed: usize,
		heur: usize,
		#[cfg(LOGGING)]
		prev_pos: Option<usize>
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

	let (heur, start_pos, end_pos) = {
		let ([dx, dy], area) = input_valley.geometry();
		let [x_end, y_end, end_pos] = [dx - 1, dy - 1, area - 1];
		(move |pos| {
			let [x, y] = [pos % dx, pos / dx];
			if REVERSE { x + y } else { x_end - x + y_end - y }
		}, if REVERSE { end_pos } else { 0 }, if REVERSE { 0 } else { end_pos })
	};

	let mut heap = BinaryHeap::new();
	heap.push(State { pos: start_pos, steps: 0, elapsed: 0, heur: heur(start_pos),
		#[cfg(LOGGING)]
		prev_pos: None,
	});
	let mut steps = HashMap::new();

	#[cfg(LOGGING)]
	let mut prev_poss = HashMap::new();
	macro_rules! _set_prev_pos { ( $state:expr ) => {
		if let Some(prev_pos) = $state.prev_pos {
			prev_poss.insert(($state.pos, start_time + $state.elapsed), prev_pos);
		}
	} }

	macro_rules! _print_path { ( $state:expr ) => {
		use std::fmt::Write as _;
		let path = (1..$state.elapsed)
			.rev()
			.scan($state.prev_pos.unwrap(), |acc, elapsed| {
				let prev_pos = *acc;
				*acc = prev_poss[&(prev_pos, start_time + elapsed)];
				Some(prev_pos)
			})
			.collect::<std::collections::HashSet<_>>();
		let mut s = String::new();
		input_valley.fmt_time(&mut s,
			|pos| if pos == end_pos { Some('E') }
				else if path.contains(&pos) { Some('~') }
				else { None },
			start_time + $state.elapsed).unwrap();
		s.write_char('\n').unwrap();
		println!("{}{:?}; {}", s, $state, $state.estimated_elapsed());
	} }

	while let Some(state) = heap.pop() {
		if state.pos == end_pos {
			#[cfg(LOGGING)]
			_print_path!(state);
			return state.elapsed
		}

		match steps.entry((state.pos, start_time + state.elapsed)) {
			Entry::Vacant(entry) => { entry.insert(state.steps); }
			Entry::Occupied(mut entry) => {
				if *entry.get() <= state.steps { continue }
				entry.insert(state.steps);
			}
		}

		#[cfg(LOGGING)]
		_set_prev_pos!(state);

		let elapsed = state.elapsed + 1;

		// Wait if possible
		if !input_valley.is_position_hit_by_blizzard(state.pos, start_time + elapsed) {
			heap.push(State { elapsed,
				#[cfg(LOGGING)]
				prev_pos: Some(state.pos),
				..state });
		}

		// Move to any accessible adjacent positions
		for pos in input_valley.accessible_adjacent_positions(state.pos, start_time + elapsed) {
			heap.push(State { pos, steps: state.steps + 1, elapsed, heur: heur(pos),
				#[cfg(LOGGING)]
				prev_pos: Some(state.pos),
			});
		}
	}

	panic!("Could not find path");
}


fn part1_impl(input_valley: Valley) -> usize {
	part1and2_impl::<false>(&input_valley, 0)
}

pub(crate) fn part1() -> usize {
	part1_impl(input_valley())
}


fn part2_impl(input_valley: Valley, part1: Option<usize>) -> usize {
	let t0 = part1.unwrap_or_else(|| part1and2_impl::<false>(&input_valley, 0));
	let t1 = part1and2_impl::<true>(&input_valley, t0);
	t0 + t1 + part1and2_impl::<false>(&input_valley, t0 + t1)
}

fn part2_cached(part1: Option<usize>) -> usize {
	part2_impl(input_valley(), part1)
}

pub(crate) fn part2() -> usize {
	part2_cached(None)
}


mod parsing {
	use std::str::FromStr;
	use super::{Dir, Valley};

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

			let mut blizzards = vec![];
			let mut len = None;

			let (mut c, mut l, mut cx0, mut south_edge) = (0, 0, 0, false);

			macro_rules! inv_byte_err { ( $c:expr, $found:expr ) => {
				E::InvalidByte { line: l + 1, column: $c + 1, found: $found }
			} }

			while c < s.len() {
				if Some(c) == len { return Err(
					E::LineLen { line: l + 1, len, found: c + 1 }) }
				match len {
					None => {
						_ = try_strip_prefix(s, "#.#").map_err(|e| if e.is_empty() {
							E::LineLen { line: 1, len: None, found: str_offset!(s, e) }
						} else {
							inv_byte_err!(s.len() - e.len(), e.as_bytes()[0])
						})?;

						len = Some(s.bytes().position(|b| b == b'\n').ok_or(E::EndOfString)?);
						c = len.unwrap() + 1;
						cx0 = c;
					}
					Some(len) => {
						if c >= s.len() { return Err(E::EndOfString); }
						let cx = c - cx0;

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
							b'.' if cx > 0 && cx < len - 1 => blizzards.push(None),
							b @ (b'^'|b'v') => {
								let dir = if b == b'^' { Dir::North } else { Dir::South };
								blizzards.push(Some(dir));
							}
							b @ (b'<'|b'>') => {
								let dir = if b == b'<' { Dir::West } else { Dir::East };
								blizzards.push(Some(dir));
							}
							found => return Err(inv_byte_err!(cx, found))
						}

						c += 1;
					}
				}
			}

			let Some(len) = len else { return Err(E::EndOfString) };
			if !south_edge || c > cx0 && c - cx0 < len { panic!() }//return Err(E::EndOfString) };

			Ok(Valley { blizzards, stride: len - 2 })
		}
	}
}


#[cfg(LOGGING)]
impl Valley {
	fn fmt_time(&self,
		f: &mut impl std::fmt::Write,
		pos: impl Fn(usize) -> Option<char>,
		time: usize,
	) -> std::fmt::Result {
		let ([dx, dy], area) = self.geometry();

		writeln!(f, "#{}{}", pos(0).unwrap_or('.'), "#".repeat(dx))?;
		for y in 1..dy - 1 {
			f.write_char('#')?;
			for x in 0..dx {
				let p = y * dx + x;
				f.write_char(pos(p).unwrap_or_else(|| match self.blizzard_hits(y * dx + x, time) {
					[false, false, false, false] => '.',
					[true, false, false, false] => '^',
					[false, true, false, false] => '>',
					[false, false, true, false] => 'v',
					[false, false, false, true] => '<',
					hits => (b'a' + hits.into_iter()
						.enumerate()
						.map(|(i, b)| u8::from(b) << (3 - i))
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

#[cfg(LOGGING)]
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
	assert_eq!(part2_impl(input_valley_from_str(INPUTS[0]), Some(10)), 30);
	assert_eq!(part2_impl(input_valley_from_str(INPUTS[1]), Some(18)), 54);
	assert_eq!(part2_cached(Some(322)), 974);
}
