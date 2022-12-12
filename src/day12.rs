// Copyright (c) 2022 Bastiaan Marinus van de Weerd


struct Heightmap {
	heights: Vec<u8>,
	stride: usize,
	start: usize,
	end: usize,
}

impl Heightmap {
	/// Returns an [`Iterator`] with as its [`Iterator::Item`]s pairs of position and height.
	fn adjacent_heights(&self, pos: usize) -> impl Iterator<Item = (usize, u8)> {
		let s = self.stride;
		macro_rules! item { ( $pos:expr ) => { ($pos, self.heights[$pos]) } }
		let above = (pos >= s).then(|| item!(pos - s));
		let left = ((pos % s) > 0).then(|| item!(pos - 1));
		let right = ((pos % s) < s - 1).then(|| item!(pos + 1));
		let below = (pos < self.heights.len() - s).then(|| item!(pos + s));
		[above, left, right, below].into_iter().flatten()
	}

	/// Returns an [`Iterator`] similar to `adjacent_heights`, but
	/// containing only those positions that can be reached from `pos`.
	fn reachable_adjacent_heights(&self, pos: usize) -> impl Iterator<Item = (usize, u8)> {
		let height = self.heights[pos];
		self.adjacent_heights(pos).filter(move |(_, h)| *h <= height + 1)
	}

	/// Returns an [`Iterator`] similar to `adjacent_heights`, but
	/// containing only those positions from which `pos` can be reached.
	fn reaching_adjacent_heights(&self, pos: usize) -> impl Iterator<Item = (usize, u8)> {
		let height = self.heights[pos];
		self.adjacent_heights(pos).filter(move |(_, h)| *h + 1 >= height)
	}

	fn find_steps<Next: Iterator<Item = (usize, u8)>>(
		&self,
		from: usize,
		to: impl Fn(usize) -> bool,
		next_steps: impl Fn(usize) -> Next
	) -> usize {
		use std::collections::VecDeque;

		// Breadth-first search
		let mut queue = VecDeque::new();
		let mut known_steps = vec![usize::MAX; self.heights.len()];
		queue.push_back((from, 0));

		while let Some((pos, steps)) = queue.pop_front() {

			if known_steps[pos] <= steps { continue }
			known_steps[pos] = steps;

			#[cfg(LOGGING)]
			println!("{},{} @ {steps}: {}",
				pos % self.stride,
				pos / self.stride,
				self.heights[pos]);

			if to(pos) { return steps }

			for (pos, _) in next_steps(pos) {
				queue.push_back((pos, steps + 1));
			}
		}

		panic!("Could not find path")
	}
}


fn input_heightmap_from_str(s: &str) -> Heightmap {
	s.parse().unwrap()
}

fn input_heightmap() -> Heightmap {
	input_heightmap_from_str(include_str!("day12.txt"))
}


fn part1_impl(input_heightmap: Heightmap) -> usize {
	input_heightmap.find_steps(
		input_heightmap.start,
		|pos| pos == input_heightmap.end,
		|pos| input_heightmap.reachable_adjacent_heights(pos)
	)
}

pub(crate) fn part1() -> usize {
	part1_impl(input_heightmap())
}


fn part2_impl(input_heightmap: Heightmap) -> usize {
	input_heightmap.find_steps(
		input_heightmap.end,
		|pos| input_heightmap.heights[pos] == 0,
		|pos| input_heightmap.reaching_adjacent_heights(pos)
	)
}

pub(crate) fn part2() -> usize {
	part2_impl(input_heightmap())
}


mod parsing {
	use std::str::FromStr;
	use super::Heightmap;
	
	#[allow(dead_code)]
	#[derive(Debug)]
	pub(super) enum HeightmapError {
		LineLen { line: usize, len: Option<usize>, found: usize },
		InvalidByte { line: usize, column: usize, found: u8 },
		DuplicateStart { line: usize, column: usize },
		DuplicateEnd { line: usize, column: usize },
		NoStart,
		NoEnd,
	}

	impl FromStr for Heightmap {
		type Err = HeightmapError;
		fn from_str(s: &str) -> Result<Self, Self::Err> {
			let mut heights = vec![];
			let mut stride = None;
			let mut start = None;
			let mut end = None;

			let mut l = 0;
			for (i, b) in s.bytes().enumerate() {
				macro_rules! c { () => { i - l * stride.unwrap_or(0) - l } }

				macro_rules! ret_line_len_err { ( $found:expr ) => {
					return Err(HeightmapError::LineLen { line: l + 1, len: stride, found: $found })
				} }

				if Some(i) == stride { ret_line_len_err!(i % (stride.unwrap() + 1)) }

				macro_rules! set_start_or_end {
					( $which:ident, $which_err:ident, $height:literal ) => { {
						if $which.is_some() { return Err(HeightmapError::$which_err {
							line: l + 1, column: c!() + 1 }) }
						$which = Some(i - l);
						heights.push($height);
					} }
				}

				match b {
					b'S' => set_start_or_end!(start, DuplicateStart, 0),
					b'E' => set_start_or_end!(end, DuplicateEnd, 25),
					b if b.is_ascii_lowercase() => { heights.push(b - b'a') },
					b'\n' => match stride {
						None => { stride = Some(i); l = 1 }
						Some(s) => if (i + 1) % (s + 1) == 0 { l += 1 }
							else { ret_line_len_err!(i - l * s - l) }
					}
					invalid => return Err(HeightmapError::InvalidByte {
						line: l + 1, column: c!() + 1, found: invalid })
				}
			}

			Ok(Heightmap {
				heights,
				stride: stride.ok_or(
					HeightmapError::LineLen { line: 1, len: None, found: s.len() })?,
				start: start.ok_or(HeightmapError::NoStart)?,
				end: end.ok_or(HeightmapError::NoEnd)?,
			})
		}
	}
}


#[test]
fn tests() {
	const INPUT: &str = indoc::indoc! { "
		Sabqponm
		abcryxxl
		accszExk
		acctuvwj
		abdefghi
	" };
	assert_eq!(part1_impl(input_heightmap_from_str(INPUT)), 31);
	assert_eq!(part1(), 456);
	assert_eq!(part2_impl(input_heightmap_from_str(INPUT)), 29);
	assert_eq!(part2(), 454);
}
