// Copyright (c) 2022 Bastiaan Marinus van de Weerd


#[derive(Clone, Copy)]
enum Dir { Left, Right, Down }

#[derive(Clone, Copy)]
enum RockShape { Bar, Plus, Angle, Pole, Block }

impl RockShape {
	const ALL: [RockShape; 5] = {
		use RockShape::*;
		[Bar, Plus, Angle, Pole, Block]
	};

	/// Width & height
	fn size(&self) -> [usize; 2] {
		use RockShape::*;
		match self {
			Bar => [4, 1],
			Plus => [3, 3],
			Angle => [3, 3],
			Pole => [1, 4],
			Block => [2, 2],
		}
	}

	/// 4x4 bottom-left anchored row-major grid
	fn bits(&self) -> u16 {
		use RockShape::*;
		match self {
			Bar => 0b0000000000001111,
			Plus => 0b0000010011100100,
			Angle => 0b00000001000101110,
			Pole => 0b1000100010001000,
			Block => 0b0000000011001100,
		}
	}
}

trait Rock {
	fn shape(&self) -> RockShape;

	/// X,Y anchor position (rocks are bottom-left anchored; in the
	/// case of [`Rock::Plus`] the anchor itself is an open space).
	fn position(&self) -> [usize; 2];

	fn overlaps<Other: Rock>(&self, other: &Other) -> bool {
		let [ps, po] = [self.position(), other.position()];
		let delta: [isize; 2] = std::array::from_fn(|i| ps[i] as isize - po[i] as isize);
		if !matches!(delta, [-3..=3, -3..=3]) { return false }
		let bs = self.shape().bits();
		let m = [
			0b0001000100010001,
			0b0011001100110011,
			0b0111011101110111,
			0b1111111111111111,
			0b1110111011101110,
			0b1100110011001100,
			0b1000100010001000,
		][(delta[0] + 3) as usize];
		let bs = match delta {
			[0, 0] => bs,
			[x, y] if x >= 0 && y >= 0 => ((bs & m) >> x) << (y * 4),
			[x, y] if x >= 0 => ((bs & m) >> x) >> (-y * 4),
			[x, y] if y >= 0 => ((bs & m) << -x) << (y * 4),
			[x, y] => ((bs & m) << -x) >> (-y * 4),
		};
		let bo = other.shape().bits();
		bs & bo != 0
	}

	fn is_stacked_on<Other: Rock>(&self, other: &Other) -> bool {
		let pos = self.position();
		(self.shape(), [pos[0], pos[1] - 1]).overlaps(other)
	}
}

impl Rock for (RockShape, [usize; 2]) {
	fn shape(&self) -> RockShape { self.0 }
	fn position(&self) -> [usize; 2] { self.1 }
}

#[derive(Default)]
struct Simulation {
	/// Y-X position (relative to the bottom-left open space in the chamber), & insertion index.
	rock_positions: std::collections::BTreeSet<([usize; 2], usize)>,
	height: usize,
	current_rock_position: Option<[usize; 2]>,
}

impl Simulation {

	fn rock_shape(&self, index: usize) -> RockShape {
		RockShape::ALL[index % RockShape::ALL.len()]
	}

	fn can_current_rock_move(&self, dir: Dir) -> Option<bool> {
		use Dir::*;
		let current_pos = self.current_rock_position?;
		match dir {
			Left if current_pos[0] == 0 => return Some(false),
			Down if current_pos[1] == 0 => return Some(false),
			Down if current_pos[1] > self.height => return Some(true),
			_ => (),
		};

		let current_shape = self.rock_shape(self.rock_positions.len());
		if matches!(dir, Right if current_pos[0] + current_shape.size()[0] == 7) {
			return Some(false)
		}

		let offset_pos = match dir {
			Left => [current_pos[0] - 1, current_pos[1]],
			Right => [current_pos[0] + 1, current_pos[1]],
			Down => [current_pos[0], current_pos[1] - 1],
		};

		for &([prev_y, prev_x], prev) in self.rock_positions.iter().rev() {
			if matches!(dir, Down if prev_y + 3 < offset_pos[1]) { break }
			let prev_shape = self.rock_shape(prev);
			if (current_shape, offset_pos).overlaps(&(prev_shape, [prev_x, prev_y])) {
				return Some(false)
			}
		}

		Some(true)
	}

	fn tick(&mut self, dir: Dir) {
		let mut current_pos = *self.current_rock_position.get_or_insert([2, self.height + 3]);
		if self.can_current_rock_move(dir).unwrap() {
			current_pos[0] = match dir { Dir::Left => current_pos[0] - 1, _ => current_pos[0] + 1 };
			self.current_rock_position = Some(current_pos);
		}
		if self.can_current_rock_move(Dir::Down).unwrap() {
			current_pos[1] -= 1;
			self.current_rock_position = Some(current_pos);
			return
		}
		let size = self.rock_shape(self.rock_positions.len()).size();
		self.rock_positions.insert(([current_pos[1], current_pos[0]], self.rock_positions.len()));
		self.height = self.height.max(current_pos[1] + size[1]);
		self.current_rock_position = None;
	}
}


fn input_dirs_from_str(s: &str) -> impl AsRef<[Dir]> {
	parsing::dirs_from_str(s).unwrap()
}


fn part1_impl(input_dirs: impl AsRef<[Dir]>) -> usize {
	let mut simulation = Simulation::default();
	for (_dbg_i, dir) in input_dirs.as_ref().iter().cycle().enumerate() {
		simulation.tick(*dir);
		if simulation.rock_positions.len() == 2022 {
			return simulation.height;
		}
	}
	unreachable!()
}

pub(crate) fn part1() -> usize {
	part1_impl(input_dirs_from_str(include_str!("day17.txt")))
}


pub(crate) fn part2() -> &'static str {
	"WIP"
}


mod parsing {
	use super::Dir;

	#[allow(dead_code)]
	#[derive(Debug)]
	pub(super) struct  DirsError { column: usize, found: u8 }

	pub(super) fn dirs_from_str(s: &str) -> Result<impl AsRef<[Dir]>, DirsError> {
		s.bytes()
			.take_while(|b| *b != b'\n')
			.enumerate()
			.map(|(c, b)| match b {
				b'<' => Ok(Dir::Left),
				b'>' => Ok(Dir::Right),
				found => Err(DirsError { column: c + 1, found })
			})
			.collect::<Result<Vec<_>, _>>()
	}
}


#[cfg(test)]
impl std::fmt::Display for Simulation {
	fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
		use {std::fmt::Write, itertools::iproduct};

		let current_top = self.current_rock_position
			.map(|[_, y]| y + self.rock_shape(self.rock_positions.len()).size()[1]);
		let mut current_rock_position = self.current_rock_position;
		let mut rock_positions = self.rock_positions.iter().rev().peekable();
		let mut buffers = [0_u16; 28];
		let mut current_buffer = None;
		let h = current_top.unwrap_or(0).max(self.height);

		for y in (0..h + 3).rev() {
			if let Some(&[_, pos_y]) = current_rock_position.as_ref() {
				if pos_y == y - 3 {
					let Some([pos_x, _]) = current_rock_position.take() else { unreachable!() };
					let bi = (pos_y % 4) * 7 + pos_x;
					buffers[bi] = self.rock_shape(self.rock_positions.len()).bits();
					current_buffer = Some(bi)
				}
			}
			while let Some(&&([pos_y, _], _)) = rock_positions.peek() {
				if pos_y != y - 3 { break }
				let Some(([_, pos_x], i)) = rock_positions.next() else { unreachable!() };
				buffers[(pos_y % 4) * 7 + pos_x] = self.rock_shape(*i).bits();
			}

			if y > h { continue }

			f.write_char('|')?;
			for x in 0..7 {
				f.write_char(iproduct!(0..(y + 1).min(4), (0..(x + 1).min(4)).rev())
					.find_map(|(by, bx)| {
						let bi = ((y - by) % 4) * 7 + x - bx;
						(buffers[bi] & 1 << (4 * by + 3 - bx) != 0)
							.then_some(if current_buffer == Some(bi) { '@' } else { '#' })
					})
					.unwrap_or('.'))?;
			}
			f.write_char('|')?;
			f.write_char('\n')?;

			let buffers_clear_range = (y % 4) * 7..(y % 4) * 7 + 7;
			if current_buffer.map(|bi| buffers_clear_range.contains(&bi)).unwrap_or(false) {
				current_buffer = None;
			}
			buffers[buffers_clear_range].fill(0)
		}
		write!(f, "+-------+")
	}
}


#[test]
fn tests() {
	const INPUT: &str = ">>><<><>><<<>><>>><<<>>><<<><<<>><>><<>>";
	assert_eq!(part1_impl(input_dirs_from_str(INPUT)), 3068);
	assert_eq!(part1(), 3224);
}