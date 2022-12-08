// Copyright (c) 2022 Bastiaan Marinus van de Weerd


struct Grid {
	tree_heights: Vec<u8>,
	width: usize,
}

impl Grid {
	fn tree_height_xy(&self, x: usize, y: usize) -> u8 {
		self.tree_heights[y * self.width + x]
	}
}


fn input_grid_from_str(s: &str) -> Grid {
	s.parse().unwrap()
}

fn input_grid() -> Grid {
	input_grid_from_str(include_str!("day08.txt"))
}


fn part1_impl(input_grid: Grid) -> usize {
	use itertools::iproduct;

	let outer = (input_grid.width - 1) * 4;
	let mut inner = 0;
	let through = input_grid.width - 2;
	for (y, x) in iproduct!(1..=through, 1..=through) {
		let height = input_grid.tree_height_xy(x, y);

		macro_rules! is_clear_sightline { ( $range:expr, $arg:ident, $x:expr, $y:expr ) => {
			$range.all(|$arg| input_grid.tree_height_xy($x, $y) < height)
		} }

		if is_clear_sightline!(1..=y, dy, x, y - dy) // Above
			|| is_clear_sightline!(1..=x, dx, x - dx, y) // Left
			|| is_clear_sightline!(1..=through - x + 1, dx, x + dx, y) // Right
			|| is_clear_sightline!(1..=through - y + 1, dy, x, y + dy) { // Below
			inner += 1
		}
	}

	outer + inner
}

pub(crate) fn part1() -> usize {
	part1_impl(input_grid())
}


fn part2_impl(input_grid: Grid) -> u64 {
	use itertools::iproduct;

	let mut max = 0;
	let through = input_grid.width - 2;
	for (y, x) in iproduct!(1..=through, 1..=through) {
		let height = input_grid.tree_height_xy(x, y);

		macro_rules! count_visible_trees { ( $range:expr, $arg:ident, $x:expr, $y:expr ) => { {
			use itertools::Itertools as _;
			let mut range = $range.peekable();
			let count = range
				.peeking_take_while(|$arg| input_grid.tree_height_xy($x, $y) < height)
				.count();
			count + if range.next().is_some() { 1 } else { 0 }
		} } }

		let above = count_visible_trees!(1..=y, dy, x, y - dy);
		let left = count_visible_trees!(1..=x, dx, x - dx, y);
		let right = count_visible_trees!(1..=through - x + 1, dx, x + dx, y);
		let below = count_visible_trees!(1..=through - y + 1, dy, x, y + dy);

		let score = (above * left * right * below) as u64;
		if score > max { max = score }
	}

	max
}

pub(crate) fn part2() -> u64 {
	part2_impl(input_grid())
}


mod parsing {
	use std::str::FromStr;
	use super::Grid;

	#[allow(dead_code)]
	#[derive(Debug)]
	pub(super) enum GridError {
		Empty,
		LineLen { line: usize, len: Option<usize>, found: usize },
		InvalidByte { line: usize, column: usize, found: u8 },
	}

	impl FromStr for Grid {
		type Err = GridError;
		fn from_str(s: &str) -> Result<Self, Self::Err> {
			if s.is_empty() { return Err(GridError::Empty) }

			let mut tree_heights = vec![];
			let mut width = None;

			for (l, line) in s.lines().enumerate() {

				macro_rules! ret_line_len_err { ( $found:expr ) => {
					return Err(GridError::LineLen {
						line: l + 1, len: width, found: $found })
				}}

				for (c, b) in line.bytes().enumerate() {
					match b {
						_ if Some(c) == width => ret_line_len_err!(c + 1),
						found if !found.is_ascii_digit() =>
							return Err(GridError::InvalidByte {
								line: l + 1, column: c + 1, found }),
						height => tree_heights.push(height - b'0'),
					}
				}

				match width {
					None => {
						let len = tree_heights.len();
						if len < 2 { ret_line_len_err!(len) }
						width = Some(len)
					}
					Some(len) => {
						let len_mod = tree_heights.len() % len;
						if len_mod != 0 { ret_line_len_err!(len_mod) }
					}
				}
			}

			Ok(Grid { tree_heights, width: width.unwrap() })
		}
	}
}


#[cfg(LOGGING)]
impl std::fmt::Display for Grid {
	fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
		use std::fmt::Write;
		let height = self.heights.len() / self.width; 
		for y in 0..height {
			for x in 0..self.width {
				f.write_char((b'0' + self.heights[y * self.width + x]) as char)?;
			}
			if y < height - 1 { f.write_char('\n')? }
		}
		Ok(())
	}
}


#[test]
fn tests() {
	const INPUT: &str = indoc::indoc! { "
		30373
		25512
		65332
		33549
		35390
	" };
	assert_eq!(part1_impl(input_grid_from_str(INPUT)), 21);
	assert_eq!(part1(), 1827);
	assert_eq!(part2_impl(input_grid_from_str(INPUT)), 8);
	assert_eq!(part2(), 335580);
}
