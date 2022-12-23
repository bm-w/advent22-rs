// Copyright (c) 2022 Bastiaan Marinus van de Weerd


struct Elves(std::collections::HashSet<[isize; 2]>);

impl Elves {
	fn adjacent_positions(pos: [isize; 2]) -> [[isize; 2]; 8] {
		let [x, y] = pos;
		[
			[x - 1, y - 1], [x, y - 1], [x + 1, y - 1],
			[x - 1, y],                 [x + 1, y],
			[x - 1, y + 1], [x, y + 1], [x + 1, y + 1],
		]
	}

	/// Returns whether any elves moved.
	fn tick(&mut self, t: usize) -> bool {
		use std::collections::{HashMap, hash_map::Entry};

		let mut proposed_moves = HashMap::new();
		for elf_pos in &self.0 {
			let adj_poss = Self::adjacent_positions(*elf_pos);
			if !adj_poss.iter().any(|pos| self.0.contains(pos)) { continue }

			for (i, adj_pp) in [[1, 2, 0], [6, 7, 5], [3, 5, 0], [4, 7, 2]]
				.into_iter()
				.enumerate()
				.cycle()
				.skip(t % 4)
				.take(4)
			{
				if adj_pp.into_iter().any(|p| self.0.contains(&adj_poss[p])) { continue }

				let proposed_move = match i {
					0 => [elf_pos[0], elf_pos[1] - 1],
					1 => [elf_pos[0], elf_pos[1] + 1],
					2 => [elf_pos[0] - 1, elf_pos[1]],
					_ => [elf_pos[0] + 1, elf_pos[1]],
				};

				match proposed_moves.entry(proposed_move) {
					Entry::Vacant(entry) => { entry.insert(Some(*elf_pos)); true }
					Entry::Occupied(mut entry) => { entry.insert(None); false }
				};

				break
			}
		}

		#[cfg(LOGGING)]
		{
			let mut s = String::new();
			self.fmt_proposed_moves(&mut s, &proposed_moves).unwrap();
			println!("t = {t}\n{s}\n");
		}

		let mut any_moved = false;
		for (proposed_pos, from_pos) in proposed_moves {
			let Some(from_pos) = from_pos else { continue };
			assert!(self.0.remove(&from_pos));
			assert!(self.0.insert(proposed_pos));
			any_moved = true;
		}
		any_moved
	}

	fn bounds_proposed_moves(&self,
		proposed_moves: &std::collections::HashMap<[isize; 2], Option<[isize; 2]>>,
	) -> Option<[std::ops::RangeInclusive<isize>; 2]> {
		use itertools::Itertools as _;
		let poss = self.0.iter().chain(proposed_moves.iter().map(|(p, _)| p));
		let x = poss.clone().map(|[x, _]| *x).minmax().into_option()?;
		let y = poss.map(|[_, y]| *y).minmax().into_option()?;
		Some([x.0..=x.1, y.0..=y.1])
	}

	fn bounds(&self) -> Option<[std::ops::RangeInclusive<isize>; 2]> {
		self.bounds_proposed_moves(&Default::default())
	}
}


fn input_elves_from_str(s: &str) -> Elves {
	s.parse().unwrap()
}

fn input_elves() -> Elves {
	input_elves_from_str(include_str!("day23.txt"))
}



fn part1_impl(mut input_elves: Elves) -> usize {
	if input_elves.0.is_empty() { return 0 }
	for t in 0..10 { if !input_elves.tick(t) { break } }
	let [x, y] = input_elves.bounds().unwrap();
	x.size_hint().0 * y.size_hint().0 - input_elves.0.len()
}

pub(crate) fn part1() -> usize {
	part1_impl(input_elves())
}


fn part2_impl(mut input_elves: Elves) -> usize {
	for t in 0.. { if !input_elves.tick(t) { return t + 1 } }
	unreachable!()
}

pub(crate) fn part2() -> usize {
	part2_impl(input_elves())
}


mod parsing {
	use std::str::FromStr;
	use super::Elves;

	#[allow(dead_code)]
	#[derive(Debug)]
	pub(super) enum GridError {
		InvalidByte { line: usize, column: usize, found: u8 },
	}

	impl FromStr for Elves {
		type Err = GridError;
		fn from_str(s: &str) -> Result<Self, Self::Err> {
			let mut poss = std::collections::HashSet::<[isize; 2]>::new();

			let [mut cx0, mut y] = [0, 0];
			for (c, b) in s.bytes().enumerate() {
				match b {
					b'#' => { poss.insert([(c - cx0) as isize, y as isize]); },
					b'.' => (),
					b'\n' => { y += 1; cx0 = c + 1 }
					found => return Err(
						GridError::InvalidByte { line: y + 1, column: c - cx0 + 1, found }),
				}
			}

			Ok(Elves(poss))
		}
	}
}


#[cfg(test)]
impl Elves {
	fn fmt_proposed_moves(&self,
		f: &mut impl std::fmt::Write,
		proposed_moves: &std::collections::HashMap<[isize; 2], Option<[isize; 2]>>,
	) -> std::fmt::Result {
		let Some([rx, ry]) = self.bounds_proposed_moves(proposed_moves)
			else { return f.write_char('.') };

		for y in ry.clone() {
			for x in rx.clone() {
				f.write_char(if let Some(from_pos) = proposed_moves.get(&[x, y]) {
					if let Some(from_pos) = from_pos {
						if from_pos[0] < x { '>' }
						else if from_pos[0] > x { '<' }
						else if from_pos[1] < y { 'v' }
						else { '^' }
					} else {
						'x'
					}
				} else if self.0.contains(&[x, y]) {
					'#'
				} else {
					'.'
				})?
			}
			if y < *ry.end() { f.write_char('\n')? }
		}

		Ok(())
	}
}

#[cfg(test)]
impl std::fmt::Display for Elves {
	fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
		self.fmt_proposed_moves(f, &Default::default())
	}
}


#[test]
fn tests() {
	const INPUTS: [&str; 2] = [
		indoc::indoc! { "
			.....
			..##.
			..#..
			.....
			..##.
			.....
		" },
		indoc::indoc! { "
			....#..
			..###.#
			#...#.#
			.#...##
			#.###..
			##.#.##
			.#..#..
		" },
	];
	assert_eq!(part1_impl(input_elves_from_str(INPUTS[0])), 25);
	assert_eq!(part1_impl(input_elves_from_str(INPUTS[1])), 110);
	assert_eq!(part1(), 4241);
	assert_eq!(part2_impl(input_elves_from_str(INPUTS[0])), 4);
	assert_eq!(part2_impl(input_elves_from_str(INPUTS[1])), 20);
	assert_eq!(part2(), 1079);
}
