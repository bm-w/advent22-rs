// Copyright (c) 2022 Bastiaan Marinus van de Weerd


#[derive(PartialEq, Eq, PartialOrd, Ord, Clone, Copy)]
struct Cube { pos: [isize; 3] }

impl Cube {
	fn adjacent_cubes(&self) -> [Cube; 6] {
		let [x, y, z] = self.pos;
		[
			Cube { pos: [x - 1, y, z] },
			Cube { pos: [x + 1, y, z] },
			Cube { pos: [x, y - 1, z] },
			Cube { pos: [x, y + 1, z] },
			Cube { pos: [x, y, z - 1] },
			Cube { pos: [x, y, z + 1] },
		]
	}
}

type Cubes = std::collections::BTreeSet<Cube>;


fn input_cubes_from_str(s: &str) -> Cubes {
	parsing::try_cubes_from_str(s).unwrap()
}

fn input_cubes() -> Cubes {
	input_cubes_from_str(include_str!("day18.txt"))
}


fn part1_impl(input_cubes: Cubes) -> usize {
	input_cubes.iter()
		.map(|cube| cube.adjacent_cubes().into_iter()
			.filter(|adj_cube| !input_cubes.contains(adj_cube))
			.count())
		.sum()
}

pub(crate) fn part1() -> usize {
	part1_impl(input_cubes())
}


fn part2_impl(input_cubes: Cubes) -> usize {
	let Some(cube) = input_cubes.first() else { return 0 };

	type Hull = [std::ops::RangeInclusive<isize>; 3];
	let hull = input_cubes.iter().skip(1).fold([
		cube.pos[0]..=cube.pos[0],
		cube.pos[1]..=cube.pos[1],
		cube.pos[2]..=cube.pos[2],
	], |acc, &Cube { pos: [x, y, z] }| [
		x.min(*acc[0].start())..=x.max(*acc[0].end()),
		y.min(*acc[1].start())..=y.max(*acc[1].end()),
		z.min(*acc[2].start())..=z.max(*acc[2].end()),
	]);

	// TODO(bm-w): Figure out how to use a `hull`-capturing closure here
	fn is_hull_cube(&Cube { pos: [x, y, z] }: &Cube, hull: &Hull) -> bool {
		x <= *hull[0].start() || x >= *hull[0].end()
			|| y <= *hull[1].start() || y >= *hull[1].end()
			|| z <= *hull[2].start() || z >= *hull[2].end()
	}

	// Flood-fill from each adjacent “cube” until the hull is reached
	let mut cubes_or_interior_voids = input_cubes.clone();
	for cube in &input_cubes {
		'pathing: for adj_cube in cube.adjacent_cubes() {
			if cubes_or_interior_voids.contains(&adj_cube) { continue }
			if is_hull_cube(&adj_cube, &hull) { continue }

			let mut maybe_interior_voids = Cubes::new();
			let mut queue = std::collections::VecDeque::new();
			queue.push_back(adj_cube);

			while let Some(cube) = queue.pop_front() {
				if cubes_or_interior_voids.contains(&cube) { continue }
				if !maybe_interior_voids.insert(cube) { continue }
				if is_hull_cube(&cube, &hull) { continue 'pathing }
				queue.extend(cube.adjacent_cubes());
			}

			cubes_or_interior_voids.extend(maybe_interior_voids);
		}
	}

	part1_impl(cubes_or_interior_voids)
}

pub(crate) fn part2() -> usize {
	part2_impl(input_cubes())
}


mod parsing {
	use std::{num::ParseIntError, str::FromStr};
	use super::{Cube, Cubes};

	macro_rules! str_offset { ( $s0:expr, $s:expr ) => {
		// SAFETY: It is assumed that `$s0` and `$s` point into the same string slice
		unsafe { $s.as_ptr().offset_from($s0.as_ptr()) as usize }
	} }

	#[allow(dead_code)]
	#[derive(Debug)]
	pub (super) enum CubeError {
		Format { column: usize },
		X(ParseIntError),
		Y(ParseIntError),
		Z(ParseIntError),
	}

	fn try_cube_from_str(s: &str) -> Result<(Cube, &str), CubeError> {
		use CubeError as E;

		let s0 = s;
		macro_rules! c { ( $s:expr ) => { str_offset!(s0, $s) } }

		let (x, s) = s.split_once(',').ok_or(E::Format { column: 1 })?;
		let x = x.parse().map_err(E::X)?;
		let (y, s) = s.split_once(',').ok_or(E::Format { column: c!(s) + 1 })?;
		let y = y.parse().map_err(E::X)?;
		let (z, s) = s.split_once(|c: char| !c.is_ascii_digit()).unwrap_or((s, &s[s.len()..]));
		let s = &s0[c!(s) - usize::from(!s.is_empty())..];
		let z = z.parse().map_err(E::X)?;
		Ok((Cube { pos: [x, y, z] }, s))
	}

	impl FromStr for Cube {
		type Err = CubeError;
		fn from_str(s: &str) -> Result<Self, Self::Err> {
			let (cube, r) = try_cube_from_str(s)?;
			if !r.is_empty() { return Err(CubeError::Format { column: str_offset!(s, r) + 1 }) }
			Ok(cube)
		}
	}

	#[allow(dead_code)]
	#[derive(Debug)]
	pub(super) struct CubesError { line: usize, source: CubeError }

	pub(super) fn try_cubes_from_str(s: &str) -> Result<Cubes, CubesError> {
		s.lines()
			.enumerate()
			.map(|(l, line)| line.parse()
				.map_err(|e| CubesError { line: l + 1, source: e }))
			.collect()
	}
}


#[test]
fn tests() {
	const INPUT: &str = indoc::indoc! { "
		2,2,2
		1,2,2
		3,2,2
		2,1,2
		2,3,2
		2,2,1
		2,2,3
		2,2,4
		2,2,6
		1,2,5
		3,2,5
		2,1,5
		2,3,5
	" };
	assert_eq!(part1_impl(input_cubes_from_str(INPUT)), 64);
	assert_eq!(part1(), 4302);
	assert_eq!(part2_impl(input_cubes_from_str(INPUT)), 58);
	assert_eq!(part2(), 2492);
}
