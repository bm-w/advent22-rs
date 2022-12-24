// Copyright (c) 2022 Bastiaan Marinus van de Weerd


enum Space { Open, Wall }

struct Region {
	x: std::ops::Range<usize>,
	dy: usize,
}

struct Map {
	spaces: Vec<Space>,
	regions: Vec<Region>,
	start_space: usize,
}

enum Turn { Left, Right }

struct PathDescription {
	steps_turns: Vec<(usize, Turn)>,
	last_steps: usize,
}

impl PathDescription {
	fn iter(&self) -> impl Iterator<Item = (&usize, Option<&Turn>)> + '_ {
		self.steps_turns.iter()
			.map(|(s, t)| (s, Some(t)))
			.chain(std::iter::once((&self.last_steps, None)))
	}
}

#[cfg_attr(LOGGING, derive(Debug))]
#[derive(Clone, Copy)]
enum Facing {
	Right = 0,
	Down = 1,
	Left = 2,
	Up = 3,
}

impl Facing {
	fn turn(&mut self, turn: &Turn) {
		use Facing::*;
		match (&self, turn) {
			(Down, Turn::Left) | (Up, Turn::Right) => *self = Right,
			(Left, Turn::Left)| (Right, Turn::Right)  => *self = Down,
			(Up, Turn::Left) | (Down, Turn::Right) => *self = Left,
			(Right, Turn::Left)| (Left, Turn::Right)  => *self = Up,
		}
	}
}

impl Map {
	/// Returns the [`Region`]’s index, X & Y ranges, and starting position
	fn pos_region(&self, pos: usize) -> (usize, [std::ops::Range<usize>; 2], usize) {
		let mut acc = (0, 0);
		for (i, region) in self.regions.iter().enumerate() {
			let ret = (i, [region.x.clone(), acc.1..acc.1 + region.dy], acc.0);
			if pos == acc.0 { return ret }
			acc.0 += region.x.len() * region.dy;
			acc.1 += region.dy;
			if pos < acc.0 { return ret }
		}
		panic!("Position {pos} out of bounds")
	}

	fn pos_xy(&self, pos: usize) -> [usize; 2] {
		let (_, [rx, ry], rpos) = self.pos_region(pos);
		let rdx = rx.len();
		let y = (pos - rpos) / rdx;
		let x = pos - rpos - y * rdx;
		[rx.start + x, ry.start + y]
	}

	fn wrapped_pos_down(&self, x: usize) -> usize {
		let mut acc_pos = 0;
		for region in &self.regions {
			if region.x.contains(&x) { return acc_pos + x - region.x.start }
			acc_pos += region.x.len() * region.dy
		}
		panic!("X position {x} out of bounds")
	}

	fn wrapped_pos_up(&self, x: usize) -> usize {
		let mut acc_pos = self.spaces.len();
		for region in self.regions.iter().rev() {
			if region.x.contains(&x) { return acc_pos + x - region.x.end }
			acc_pos -= region.x.len() * region.dy
		}
		panic!("X position {x} out of bounds")
	}

	fn r#move(&self, pos: &mut usize, facing: &Facing) -> bool {
		use Facing::*;

		let (ri, [rx, ry], rpos) = self.pos_region(*pos);
		let [rdx, rdy] = [rx.len(), ry.len()];
		let ry = (*pos - rpos) / rdx;
		let x = rx.start + *pos - rpos - ry * rdx;

		let next_pos = match facing {
			Right => rpos + ry * rdx + (x - rx.start + 1) % rdx,
			Down => {
				if *pos + rdx > rpos + rdx * rdy {
					if ri + 1 == self.regions.len() {
						self.wrapped_pos_down(x)
					} else {
						let next_region = &self.regions[ri + 1];
						if x < next_region.x.start || x >= next_region.x.end {
							self.wrapped_pos_down(x)
						} else {
							*pos + rx.end - next_region.x.start
						}
					}
				} else {
					*pos + rdx
				}
			}
			Left => rpos + ry * rdx + (x - rx.start + rdx - 1) % rdx,
			Up => {
				if rpos + rdx > *pos {
					if ri == 0 {
						self.wrapped_pos_up(x)
					} else {
						let next_region = &self.regions[ri - 1];
						if x < next_region.x.start || x >= next_region.x.end {
							self.wrapped_pos_up(x)
						} else {
							*pos + rx.start - next_region.x.end
						}
					}
				} else {
					*pos - rdx
				}
			}
		};

		if matches!(&self.spaces[next_pos], Space::Wall) { return false }
		*pos = next_pos;
		true
	}
}


fn input_from_str(s: &str) -> (Map, PathDescription) {
	parsing::try_input_from_str(s).unwrap()
}

fn input() -> (Map, PathDescription) {
	input_from_str(include_str!("day22.txt"))
}


fn part1_impl(input: (Map, PathDescription)) -> u64 {
	let (input_map, input_path_description) = input;

	let mut state = (input_map.start_space, Facing::Right);
	for (steps, turn) in input_path_description.iter() {
		for _ in 0..*steps { if !input_map.r#move(&mut state.0, &state.1) { break } }
		if let Some(turn) = turn { state.1.turn(turn) }
	}

	let [x, y] = input_map.pos_xy(state.0);
	(y as u64 + 1) * 1000 + (x as u64 + 1) * 4 + state.1 as u64
}

pub(crate) fn part1() -> u64 {
	part1_impl(input())
}


struct CubeFace<const SIZE: usize> {
	map_region: usize,
	/// Multiples of `SIZE`
	offset: usize,
	/// In [`Facing`] order (RDLU), indices of other faces, and
	/// facings on those faces when arriving there from this face.
	adjacent_faces: [(usize, Facing); 4],
}

struct Cube<'m, const SIZE: usize> {
	map: &'m Map,
	faces: [CubeFace<SIZE>; 6]
}

impl<T> std::ops::Index<Facing> for [T] {
	type Output = T;
	fn index(&self, index: Facing) -> &Self::Output {
		&self[index as usize]
	}
}

impl<T> std::ops::IndexMut<Facing> for [T] {
	fn index_mut(&mut self, index: Facing) -> &mut Self::Output {
		&mut self[index as usize]
	}
}

#[allow(dead_code)]
#[derive(Debug)]
enum CubeFromMapError {
	RegionGeometry { map_region: usize },
	NumberOfFaces { found: usize },
	DisconnectedFaces,
}

impl<'m, const SIZE: usize> TryFrom<&'m Map> for Cube<'m, SIZE> {
	type Error = CubeFromMapError; // TODO(bm-w): Better error…
	fn try_from(map: &'m Map) -> Result<Self, Self::Error> {
		use {CubeFromMapError as E, itertools::{Either, iproduct}};

		let faces = {
			let mut iter = map.regions.iter()
				.scan(0, |y, region| { let ry = *y; *y += region.dy; Some((region, ry)) })
				.enumerate()
				.flat_map(|(r, (region, y))| {
					if region.x.start % SIZE != 0
							|| region.x.len() % SIZE != 0
							|| region.dy % SIZE != 0
							|| region.x.len() != SIZE && region.dy != SIZE {
						return Either::Left(std::iter::once(
							Err(E::RegionGeometry { map_region: r })));
					}

					let (i, di) = (region.x.start / SIZE, region.x.len() / SIZE);
					let (j, dj) = (y / SIZE, region.dy / SIZE);
					Either::Right(iproduct!(i..i + di, j..j + dj)
						.enumerate()
						.map(move |(k, (i, j))| Ok(([i, j], r, k))))
				});
			let mut arr = [([usize::MAX, usize::MAX], usize::MAX, usize::MAX); 6];
			for (f, elt) in arr.iter_mut().enumerate() {
				*elt = iter.next().ok_or(E::NumberOfFaces { found: f })??
			}
			if iter.next().is_some() { return Err(E::NumberOfFaces { found: 7 + iter.count() }) }
			arr
		};

		fn checked_add_signed(pos: &[usize; 2], d: [isize; 2]) -> Option<[usize; 2]> {
			pos[0].checked_add_signed(d[0])
				.and_then(|x| pos[1].checked_add_signed(d[1]).map(|y| [x, y]))
		}

		impl Facing {
			fn dij(&self) -> [isize; 2] {
				use Facing::*;
				match self {
					Right => [1, 0],
					Down => [0, 1],
					Left => [-1, 0],
					Up => [0, -1],
				}
			}

			fn inverse(&self) -> Self {
				use Facing::*;
				match self { Right => Left, Down => Up, Left => Right, Up => Down }
			}

			fn turned(&self, turn: &Turn) -> Self {
				let mut copy = *self;
				copy.turn(turn);
				copy
			}
		}

		impl Turn {
			fn inverse(&self) -> Self {
				use Turn::*;
				match self { Left => Right, Right => Left}
			}
		}

		let mut adj = [[(usize::MAX, Facing::Right); 4]; 6];
		let mut prev_found = 0;
		loop {
			let mut found = 0;
			for f in 0..6 {
				let (ij, _, _) = &faces[f];
				for facing in [Facing::Right, Facing::Down, Facing::Left, Facing::Up] {
					if adj[f][facing].0 != usize::MAX { found += 1; continue }
					if let Some(cf) = checked_add_signed(ij, facing.dij())
							.and_then(|cij| faces.iter().position(|(ij, _, _)| *ij == cij)) {
						adj[f][facing] = (cf, facing);
						adj[cf][facing.inverse()] = (f, facing.inverse());
						found += if f > cf { 2 } else { 1 };
					} else { for turn in &[Turn::Left, Turn::Right] {
						let (vf, via_facing) = adj[f][facing.turned(turn)];
						if vf == usize::MAX { continue }
						let (cf, conn_prefacing) = adj[vf][via_facing.turned(&turn.inverse())];
						if cf == usize::MAX { continue }
						let conn_facing = conn_prefacing.turned(turn);
						adj[f][facing] = (cf, conn_facing);
						adj[cf][conn_facing.inverse()] = (f, facing.inverse());
						found += if f > cf { 2 } else { 1 };
						break
					} }
				}
			}
			if found == 6 * 4 { break }
			else if found == prev_found { return Err(E::DisconnectedFaces); }
			else { prev_found = found }
		}

		Ok(Cube { map, faces: std::array::from_fn(|f| {
			let (_, map_region, offset) = faces[f];
			CubeFace { map_region, offset, adjacent_faces: adj[f] }
		}) })
	}
}


impl<const SIZE: usize> Cube<'_, SIZE> {
	fn pos_from_face(&self, face: &CubeFace<SIZE>, [x, y]: [usize; 2]) -> usize {
		let map_region = &self.map.regions[face.map_region];
		let mrdx = map_region.x.len();
		let [x, y] = if mrdx > map_region.dy { [face.offset * SIZE + x, y] }
			else { [x, face.offset * SIZE + y] };
		self.map.regions[..face.map_region].iter()
			.map(|r| r.x.len() * r.dy)
			.sum::<usize>() + y * mrdx + x
	}

	fn r#move(&self, pos: &mut usize, facing: &mut Facing) -> bool {
		use Facing::*;

		let (mr, [mrx, _], mrpos) = self.map.pos_region(*pos);
		let (face, x, y) = {
			let [mrx, mry] = [(*pos - mrpos) % mrx.len(), (*pos - mrpos) / mrx.len()];
			let o = (mrx / SIZE).max(mry / SIZE);
			let face = self.faces.iter().find(|f| f.map_region == mr && f.offset == o).unwrap();
			(face, mrx % SIZE, mry % SIZE)
		};

		macro_rules! wrap { ( $face:expr, $facing:expr, $match_next_facing:tt ) => { {
			let (next_f, next_facing) = $face.adjacent_faces[$facing];
			let [x, y] = match next_facing $match_next_facing;
			(self.pos_from_face(&self.faces[next_f], [x, y]), next_facing)
		} } }

		let (next_pos, next_facing) = match *facing {
			Right if x < SIZE - 1 => (*pos + 1, *facing),
			Right => wrap!(face, *facing, {
				Right => [0, y],
				Down => [SIZE - y - 1, 0],
				Left => [SIZE - 1, SIZE - y - 1],
				Up => [y, SIZE - 1],
			}),
			Down if y < SIZE - 1 => (*pos + mrx.len(), *facing),
			Down => wrap!(face, *facing, {
				Right => [0, SIZE - x - 1],
				Down => [x, 0],
				Left => [SIZE - 1, x],
				Up => [SIZE - x - 1, SIZE - 1],
			}),
			Left if x > 0 => (*pos - 1, *facing),
			Left => wrap!(face, *facing, {
				Right => [0, SIZE - y - 1],
				Down => [y, 0],
				Left => [SIZE - 1, y],
				Up => [SIZE - y - 1, SIZE - 1],
			}),
			Up if y > 0 => (*pos - mrx.len(), *facing),
			Up => wrap!(face, *facing, {
				Right => [0, x],
				Down => [SIZE - x - 1, 0],
				Left => [SIZE - 1, SIZE - x - 1],
				Up => [x, SIZE - 1],
			}),
		};

		#[cfg(LOGGING)]
		println!("{pos:?} ({facing:?}) -> {next_pos:?} ({next_facing:?}){}",
			if matches!(&self.map.spaces[next_pos], Space::Wall) { " X" } else { "" });

		if matches!(&self.map.spaces[next_pos], Space::Wall) { return false }
		*pos = next_pos;
		*facing = next_facing;
		true
	}
}


fn part2_impl<const CUBE_SIZE: usize>(input: (Map, PathDescription)) -> u64 {
	let (input_map, input_path_description) = input;
	let input_cube = Cube::<CUBE_SIZE>::try_from(&input_map).unwrap();

	let mut state = (input_cube.map.start_space, Facing::Right);
	for (steps, turn) in input_path_description.iter() {
		for _ in 0..*steps { if !input_cube.r#move(&mut state.0, &mut state.1) { break } }
		if let Some(turn) = turn { state.1.turn(turn) }
	}

	let [x, y] = input_map.pos_xy(state.0);
	(y as u64 + 1) * 1000 + (x as u64 + 1) * 4 + state.1 as u64
}

pub(crate) fn part2() -> u64 {
	part2_impl::<50>(input())
}


mod parsing {
	use std::{num::ParseIntError, str::FromStr};
	use super::{Space, Region, Map, Turn, PathDescription};

	macro_rules! str_offset { ( $s0:expr, $s:expr ) => {
		// SAFETY: It is assumed that `$s0` and `$s` point into the same string slice
		unsafe { $s.as_ptr().offset_from($s0.as_ptr()) as usize }
	} }

	#[allow(dead_code)]
	#[derive(Debug)]
	pub(super) enum MapError {
		InvalidByte { line: usize, column: usize, found: u8 },
		ZeroRegionWidth { line: usize },
		EndOfString { line: usize },
		MissingSpartSpace,
		TrailingStr,
	}

	pub(super) fn try_map_from_str(s: &str) -> Result<(Map, &str), MapError> {
		use MapError as E;

		let mut spaces = vec![];
		let mut regions = vec![];

		let mut curr_region_x = None;
		let mut start_space = None;
		let mut ry0 = 0;
		let mut cx0 = 0;
		let mut l = 0;
		for (c, b) in s.bytes().enumerate() {
			match b {
				b' ' => {
					match curr_region_x {
						Some((_, None)) => return Err(
							E::InvalidByte { line: l + 1, column: c - cx0 + 1, found: b' ' }),
						Some((x_start, Some(x_end))) if c - cx0 >= x_start => {
							regions.push(Region { x: x_start..x_end, dy: l - ry0 });
							curr_region_x = None;
							ry0 = l;
						}
						_ => (),
					}
				}
				b'.'|b'#' => {
					match curr_region_x {
						None => curr_region_x = Some((c - cx0, None)),
						Some((x_start, Some(x_end))) if c - cx0 < x_start => {
							regions.push(Region { x: x_start..x_end, dy: l - ry0 });
							curr_region_x = Some((c - cx0, None));
							ry0 = l;
						}
						Some((x_start, Some(x_end))) if c - cx0 >= x_end => {
							regions.push(Region { x: x_start..x_end, dy: l - ry0 });
							curr_region_x = Some((x_start, None));
							ry0 = l;
						}
						_ => (),
					}
					if b == b'.' && start_space.is_none() { start_space = Some(spaces.len()) }
					spaces.push(if b == b'.' { Space::Open } else { Space::Wall });
				}
				b'\n' => {
					if c - cx0 == 0 { break }
					match curr_region_x.as_mut() {
						None => return Err(E::ZeroRegionWidth { line: l + 1 }),
						Some((_, x_end @ None)) => *x_end = Some(c - cx0),
						Some((ref x_start, Some(ref x_end))) => if c - cx0 < *x_end {
							regions.push(Region { x: *x_start..*x_end, dy: l - ry0 });
							curr_region_x = Some((*x_start, Some(c - cx0)));
							ry0 = l;
						}
					}
					cx0 = c + 1;
					l += 1;
				}
				found => return Err(E::InvalidByte { line: l + 1, column: c - cx0 + 1, found }),
			}
		}

		if s[cx0..].starts_with('\n') {
			let Some((x_start, Some(x_end))) = curr_region_x else { unreachable!() };
			regions.push(Region { x: x_start..x_end, dy: l - ry0 });
		} else if s.ends_with('\n') { match curr_region_x {
			None | Some((_, None)) => unreachable!(),
			Some((x_start, Some(x_end))) =>
				regions.push(Region { x: x_start..x_end, dy: l - ry0 }),
		} } else { match curr_region_x {
			None => return Err(E::EndOfString { line: l + 1 }),
			Some((x_start, None)) =>
				regions.push(Region { x: x_start..s.len() - cx0, dy: l - ry0 }),
			Some((x_start, Some(x_end))) => if s.len() - cx0 == x_end {
				regions.push(Region { x: x_start..x_end, dy: l + 1 - ry0 })
			} else {
				regions.push(Region { x: x_start..x_end, dy: l - ry0 });
				regions.push(Region { x: x_start..s.len() - cx0, dy: 1 })
			}
		} }

		let Some(start_space) = start_space else { return Err(E::MissingSpartSpace); };

		let c = regions.iter().fold(0, |acc, region| acc + (region.x.end + 1) * region.dy) - 1;
		Ok((Map { spaces, regions, start_space }, &s[c..]))
	}

	impl FromStr for Map {
		type Err = MapError;
		fn from_str(s: &str) -> Result<Self, Self::Err> {
			let (map, rest) = try_map_from_str(s)?;
			if !rest.is_empty() { return Err(MapError::TrailingStr) }
			Ok(map)
		}
	}

	#[allow(dead_code)]
	#[derive(Debug)]
	pub(super) enum PathDescriptionError {
		Turn { column: usize, found: u8 },
		Steps { column: usize, source: ParseIntError },
		EndOfString,
		TrailingStr,
	}

	pub(super) fn try_path_description_from_str(mut s: &str)
	-> Result<(PathDescription, &str), PathDescriptionError> {
		use PathDescriptionError as E;

		let s0 = s;
		macro_rules! c { ( $s:expr ) => { str_offset!(s0, $s) } }

		let mut steps_turns = vec![];
		let mut last_steps;
		loop {
			let (steps, r) = s.find(|c: char| !c.is_ascii_digit())
				.map(|p| (&s[..p], &s[p..]))
				.unwrap_or((s, &s[s.len()..]));
			last_steps = Some(steps.parse()
				.map_err(|e| E::Steps { column: c!(s) + 1, source: e })?);
			if r.is_empty() { s = r; break }
			let turn = match r.as_bytes()[0] {
				b'L' => Turn::Left,
				b'R' => Turn::Right,
				found => return Err(E::Turn { column: c!(r), found }),
			};
			steps_turns.push((last_steps.take().unwrap(), turn));
			s = &r[1..];
		}
		let Some(last_steps) = last_steps else { return Err(E::EndOfString) };

		Ok((PathDescription { steps_turns, last_steps }, s))
	}

	impl FromStr for PathDescription {
		type Err = PathDescriptionError;
		fn from_str(s: &str) -> Result<Self, Self::Err> {
			let (map, rest) = try_path_description_from_str(s)?;
			if !rest.is_empty() { return Err(PathDescriptionError::TrailingStr) }
			Ok(map)
		}
	}

	#[allow(dead_code)]
	#[derive(Debug)]
	pub(super) enum InputError {
		Format,
		Map(MapError),
		PathDescription { line: usize, source: PathDescriptionError },
	}

	pub(super) fn try_input_from_str(s: &str) -> Result<(Map, PathDescription), InputError> {
		use InputError as E;
		let (map, path_description) = s.split_once("\n\n").ok_or(E::Format)?;
		Ok((
			map.parse().map_err(E::Map)?,
			path_description.strip_suffix('\n').unwrap_or(path_description)
				.parse().map_err(|e| { E::PathDescription {
					line: s[..s.len() - path_description.len()].lines().count() + 1,
					source: e,
				} })?,
		))
	}
}


#[cfg(test)]
impl From<&Space> for char {
	fn from(space: &Space) -> Self {
		if matches!(space, Space::Open) { '.' } else { '#' }
	}
}

#[cfg(test)]
impl std::fmt::Display for Map {
	fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
		use std::fmt::Write as _;

		let mut regions = self.regions.iter();
		let mut ry_end = 0;
		let mut rx = 0..0;
		let mut pos = 0;

		for y in 0.. {
			if y == ry_end {
				let Some(region) = regions.next() else { break; };
				if y > 0 { f.write_char('\n')? }
				ry_end += region.dy;
				rx = region.x.clone();
			}
			for _ in 0..rx.start { f.write_char(' ')? }
			for pos in pos..pos + rx.len() { f.write_char((&self.spaces[pos]).into())? }
			pos += rx.len();
			if y < ry_end - 1 { f.write_char('\n')? }
		}

		Ok(())
	}
}


#[test]
fn tests() {
	const INPUT: &str = indoc::indoc! { "
		        ...#
		        .#..
		        #...
		        ....
		...#.......#
		........#...
		..#....#....
		..........#.
		        ...#....
		        .....#..
		        .#......
		        ......#.

		10R5L5R10L4R5L5
	" };
	assert_eq!(part1_impl(input_from_str(INPUT)), 6032);
	assert_eq!(part1(), 13566);
	assert_eq!(part2_impl::<4>(input_from_str(INPUT)), 5031);
	assert_eq!(part2(), 11451);
}
