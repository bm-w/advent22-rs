// Copyright (c) 2022 Bastiaan Marinus van de Weerd


enum Dir { Up, Down, Left, Right }
struct Move(Dir, usize);


fn input_moves_from_str(s: &str) -> impl Iterator<Item = Move> + '_ {
	parsing::moves_from_str(s).map(|r| r.unwrap())
}

fn input_moves() -> impl Iterator<Item = Move> {
	input_moves_from_str(include_str!("day09.txt"))
}


fn part1and2_impl<const TAIL_LEN: usize>(input_moves: impl Iterator<Item = Move>) -> usize {
	use {std::collections::BTreeSet, Dir::*};

	let mut head = [0_isize; 2];
	let mut tail = [[0_isize; 2]; TAIL_LEN];
	let mut tail_visited = BTreeSet::new();
	tail_visited.insert(tail[TAIL_LEN - 1]);

	for Move(dir, amount) in input_moves {
		let dir = match dir { Up => [0, 1], Down => [0, -1], Left => [-1, 0], Right => [1, 0] };
		for _ in 0..amount {
			head[0] += dir[0];
			head[1] += dir[1];

			for i in 0..TAIL_LEN {
				let (mid, tail) = tail.split_at_mut(i);
				let (target, tail) = (mid.last().unwrap_or(&head), &mut tail[0]);

				let delta = [target[0] - tail[0], target[1] - tail[1]];
				// Benchmarks suggest this is faster than `delta[0].abs() <= 1 && …[1]…`
				if delta[0] * delta[0] + delta[1] * delta[1] <= 2 { break }

				tail[0] += delta[0].signum();
				tail[1] += delta[1].signum();
				if i == TAIL_LEN - 1 { tail_visited.insert(*tail); }
			}
		}
	}

	tail_visited.len()
}

pub(crate) fn part1() -> usize {
	part1and2_impl::<1>(input_moves())
}

pub(crate) fn part2() -> usize {
	part1and2_impl::<9>(input_moves())
}


mod parsing {
	use {std::{num::ParseIntError, str::FromStr}, itertools::Itertools as _};
	use super::{Dir, Move};

	impl TryFrom<u8> for Dir {
		type Error = ();
		fn try_from(b: u8) -> Result<Self, Self::Error> {
			match b {
				b'U' => Ok(Dir::Up),
				b'D' => Ok(Dir::Down),
				b'L' => Ok(Dir::Left),
				b'R' => Ok(Dir::Right),
				_ => Err(())
			}
		}
	}

	#[derive(Debug)]
	pub(super) enum DirError {
		Len(usize),
		Invalid(char),
	}

	impl FromStr for Dir {
		type Err = DirError;
		fn from_str(s: &str) -> Result<Self, Self::Err> {
			let b = s.bytes().exactly_one()
				.map_err(|i| DirError::Len({ let (l, h) = i.size_hint(); h.unwrap_or(l) }))?;
			b.try_into().map_err(|_| DirError::Invalid(b as char))
		}
	}

	#[derive(Debug)]
	pub(super) enum MoveError {
		NoSpace,
		Dir(DirError),
		Amount(ParseIntError)
	}

	impl FromStr for Move {
		type Err = MoveError;
		fn from_str(s: &str) -> Result<Self, Self::Err> {
			let (dir, amount) = s.split_once(' ').ok_or(MoveError::NoSpace)?;
			let dir = dir.parse().map_err(MoveError::Dir)?;
			let amount = amount.parse().map_err(MoveError::Amount)?;
			Ok(Move(dir, amount))
		}
	}

	#[allow(dead_code)]
	#[derive(Debug)]
	pub(super) struct MovesError {
		line: usize,
		source: MoveError,
	}

	pub(super) fn moves_from_str(s: &str) -> impl Iterator<Item = Result<Move, MovesError>> + '_ {
		s.lines().enumerate()
			.map(|(l, line)| line.parse()
				.map_err(|e| MovesError { line: l + 1, source: e }))
	}
}


#[cfg(test)]
mod tests {
	use super::*;

	const INPUTS: [&str; 2] = [
		indoc::indoc! { "
			R 4
			U 4
			L 3
			D 1
			R 4
			D 1
			L 5
			R 2
		" },
		indoc::indoc! { "
			R 5
			U 8
			L 8
			D 3
			R 17
			D 10
			L 25
			U 20
		" },
	];

	#[test]
	fn part1_impl() {
		assert_eq!(super::part1and2_impl::<1>(input_moves_from_str(INPUTS[0])), 13);
	}

	#[test]
	fn part1() {
		assert_eq!(super::part1(), 6314);
	}

	#[test]
	fn part2_impl_short() {
		assert_eq!(super::part1and2_impl::<9>(input_moves_from_str(INPUTS[0])), 1);
	}

	#[test]
	fn part2_impl_long() {
		assert_eq!(super::part1and2_impl::<9>(input_moves_from_str(INPUTS[1])), 36);
	}

	#[test]
	fn part2() {
		assert_eq!(super::part2(), 2504);
	}

	#[cfg(BENCHING)]
	mod bench {
		extern crate test;

		#[bench]
		fn part1(b: &mut test::Bencher) {
			b.iter(|| super::part1())
		}

		#[bench]
		fn part2(b: &mut test::Bencher) {
			b.iter(|| super::part2())
		}
	}
}
