// Copyright (c) 2022 Bastiaan Marinus van de Weerd


const HEIGHT: usize = 200;
const WIDTH: usize = HEIGHT * 2 - 1;
const X_OFFSET: usize = 500 - WIDTH / 2;


struct Cave {
	// Benchmarks suggests a `Vec` performs much better than a `(Hash|BTree)Set`
	rocks: Vec<bool>,
}

impl Cave {
	fn pos([x, y]: [usize; 2]) -> usize {
		y * WIDTH + x - X_OFFSET
	}
}

// TODO(bm-w): Use const. enum `const FLOOR: Floor` once rust allows it
struct Simulation<const ABYSS: bool> {
	cave: Cave,
	floor: usize,
	sand: Vec<bool>,
	current: Option<[usize; 2]>,
	time: usize,
}

impl<const ABYSS: bool> From<Cave> for Simulation<ABYSS> {
	fn from(cave: Cave) -> Self {
		let floor = cave.rocks.iter().enumerate().rev()
			.find_map(|(i, rock)| rock.then_some(i / WIDTH)).unwrap_or(0) + 2;
		Self { cave, floor, sand: vec![false; WIDTH * HEIGHT], current: None, time: 0 }
	}
}

impl<const ABYSS: bool> Simulation<ABYSS> {
	// Returns whether the simulation reached its end state.
	fn tick(&mut self) -> bool {
		let from = self.current.take().unwrap_or([500, 0]);
		self.time += 1;
		if ABYSS && from[1] + 2 == self.floor { return true }

		for to in [
			[from[0], from[1] + 1],
			[from[0] - 1, from[1] + 1],
			[from[0] + 1, from[1] + 1]] {
			if !(self.sand[Cave::pos(to)]
				|| self.cave.rocks[Cave::pos(to)]
				|| !ABYSS && to[1] == self.floor) {
				self.current = Some(to);
				return false
			}
		}

		self.sand[Cave::pos(from)] = true;
		!ABYSS && from == [500, 0]
	}

	fn count_sand(&self) -> usize {
		self.sand.iter().filter(|sand| **sand).count()
	}
}


fn input_cave_from_str(s: &str) -> Cave {
	s.parse().unwrap()
}

fn input_cave() -> Cave {
	input_cave_from_str(include_str!("day14.txt"))
}


fn part1_impl(input_cave: Cave) -> usize {
	let mut simulation = Simulation::<true>::from(input_cave);
	while !simulation.tick() {}
	#[cfg(LOGGING)]
	println!("{simulation}");
	simulation.count_sand()
}

pub(crate) fn part1() -> usize {
	part1_impl(input_cave())
}


fn part2_impl(input_cave: Cave) -> usize {
	let mut simulation = Simulation::<false>::from(input_cave);
	while !simulation.tick() {}
	#[cfg(LOGGING)]
	println!("{simulation}");
	simulation.count_sand()
}

pub(crate) fn part2() -> usize {
	part2_impl(input_cave())
}


mod parsing {
	use std::{num::ParseIntError, str::FromStr};
	use super::{Cave, WIDTH, HEIGHT};

	macro_rules! str_offset { ( $s0:expr, $s:expr ) => {
		// SAFETY: It is assumed that `$s0` and `$s` point into the same string slice
		unsafe { $s.as_ptr().offset_from($s0.as_ptr()) as usize }
	} }

	#[derive(Debug)]
	pub(super) enum PosError {
		Format { column: usize },
		X(ParseIntError),
		Y(ParseIntError),
	}

	fn try_pos_from_str(s: &str) -> Result<([usize; 2], &str), PosError> {
		let s0 = s; macro_rules! c { ( $s:expr ) => { str_offset!(s0, $s) } }

		let (x, s) = s.split_once(',').ok_or(PosError::Format { column: 1 })?;
		let x = x.parse().map_err(PosError::X)?;

		let (y, s) = s.split_once(|c: char| !c.is_ascii_digit()).unwrap_or((s, &s[s.len()..]));
		let y = y.parse().map_err(PosError::Y)?;

		Ok(([x, y], &s0[c!(s) - usize::from(!s.is_empty())..]))
	}

	#[derive(Debug)]
	pub(super) enum StructuresErrorKind { Format, Pos(PosError), Unaligned([[usize; 2]; 2]) }
	#[allow(dead_code)]
	#[derive(Debug)]
	pub(super) struct StructuresError { column: usize, kind: StructuresErrorKind }

	fn try_with_structures_from_str(s: &str, mut f: impl FnMut([[usize; 2]; 2]))
	-> Result<&str, StructuresError> {
		use {StructuresErrorKind as EK, StructuresError as E};
		let s0 = s; macro_rules! c { ( $s:expr ) => { str_offset!(s0, $s) } }

		let (mut pos0, mut s) = try_pos_from_str(s).map_err(|e| E { column: 1, kind: EK::Pos(e) })?;
		loop {
			s = s.strip_prefix(" -> ").ok_or(E { column: c!(s) + 1, kind: EK::Format })?;

			let (pos1, rest) = try_pos_from_str(s).map_err(|e| match e {
				PosError::Format { column } => E { column: c!(s) + column, kind: EK::Pos(e) },
				_ => E { column: c!(s) + 1, kind: EK::Pos(e) },
			})?;
			s = rest;

			if pos0[0] != pos1[0] && pos0[1] != pos1[1] {
				return Err(E { column: c!(s) + 1, kind: EK::Unaligned([pos0, pos1]) })
			}

			f([pos0, pos1]);
			pos0 = pos1;
			if s.starts_with('\n') || s.is_empty() { break }
		}

		Ok(s)
	}

	#[allow(dead_code)]
	#[derive(Debug)]
	pub(super) struct CaveError { line: usize, source: StructuresError }

	impl FromStr for Cave {
		type Err = CaveError;
		fn from_str(mut s: &str) -> Result<Self, Self::Err> {
			use {itertools::iproduct, CaveError as E};
			let mut rocks = vec![false; WIDTH * HEIGHT];
			let mut l = 0;
			while !s.is_empty() {
				s = try_with_structures_from_str(s, |structure| {
					let [xr, yr] = match structure {
						[[x, y0], [_, y1]] if y0 < y1 => [x..=x, y0..=y1],
						[[x, y1], [_, y0]] if y0 < y1 => [x..=x, y0..=y1],
						[[x0, y], [x1, _]] if x0 < x1 => [x0..=x1, y..=y],
						[[x1, y], [x0, _]] => [x0..=x1, y..=y],
					};
					for (x, y) in iproduct!(xr, yr) { rocks[Cave::pos([x, y])] = true; }
				}).map_err(|e| E { line: l + 1, source: e })?;
				s = s.strip_prefix('\n').unwrap_or(s);
				l += 1;
			}
			Ok(Cave { rocks })
		}
	}
}


#[cfg(test)]
mod fmt {
	use std::fmt::Write;
	use super::{WIDTH, X_OFFSET, Cave, Simulation};

	impl Cave {
		fn xy(pos: usize) -> [usize; 2] {
			[X_OFFSET + pos % WIDTH, pos / WIDTH]
		}

		fn extents(&self) -> [std::ops::RangeInclusive<usize>; 2] {
			use itertools::Itertools as _;
			macro_rules! r { ( $i:literal, $incl:literal ) => { {
				let mut r = self.rocks.iter().enumerate()
					.filter_map(|(i, rock)| rock.then(|| Cave::xy(i)[$i]))
					.minmax().into_option().map(|(s, e)| s..=e).unwrap_or($incl..=$incl);
				#[allow(unused_comparisons)]
				if *r.end() < $incl { r = *r.start()..=$incl }
				if *r.start() > $incl { r = $incl..=*r.end() }
				r
			} } }
			[r!(0, 500), r!(1, 0)]
		}
	}

	fn fmt_cave(
		cave: &Cave,
		f: &mut std::fmt::Formatter<'_>,
		left_padding: Option<usize>,
		write_char: impl Fn([usize; 2]) -> Option<char>,
	) -> Result<(usize, [std::ops::RangeInclusive<usize>; 2]), std::fmt::Error> {
		let [xr, yr] = cave.extents();
		let top_padding = format!("{}", xr.end()).len();
		let left_padding = left_padding.unwrap_or_else(|| format!("{}", yr.end()).len());

		let x_ticks = [*xr.start(), 500, *xr.end()];
		let x_ticks: [_; 3] = std::array::from_fn(|i| {
			let x = x_ticks[i];
			(x, format!("{x:>p$}", p = top_padding))
		});
		for y in 0..top_padding {
			macro_rules! c { ( $tick:expr ) => { $tick.1.chars().nth(y).unwrap() } }
			for (tick, p) in x_ticks.iter()
				.zip(std::iter::once(left_padding + 2)
					.chain(x_ticks.windows(2).map(|x| x[1].0 - x[0].0))) {
				write!(f, "{:>p$}", c!(tick), p = p)?;
			}
			writeln!(f)?
		}

		for y in yr.clone() {
			write!(f, "{y:>p$} ", p = left_padding)?;
			for x in xr.clone() {
				f.write_char(if [x, y] == [500, 0] { '+' }
					else { write_char([x, y]).unwrap_or_else(||
						if cave.rocks[Cave::pos([x, y])] { '#' }
						else { '.' }) })?
			}
			if y < *yr.end() { writeln!(f)? }
		}
		Ok((left_padding, [xr, yr]))
	}

	impl std::fmt::Display for Cave {
		fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
			fmt_cave(self, f, None, |_| None).map(|_| ())
		}
	}

	impl<const ABYSS: bool> std::fmt::Display for Simulation<ABYSS> {
		fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
			writeln!(f, "t = {}", self.time)?;
			let sand_char = |xy| (Some(xy) == self.current).then_some('O')
				.or_else(|| self.sand[Cave::pos(xy)].then_some('o'));
			let left_padding = (!ABYSS).then(|| format!("{}", self.floor).len());
			let (left_padding, [xr, yr]) = fmt_cave(&self.cave, f, left_padding, sand_char)?;
			if ABYSS { return Ok(()) }

			write!(f, "\n{:>p$} ", *yr.end() + 1, p = left_padding)?;
			for x in xr.clone() { f.write_char(sand_char([x, self.floor - 1]).unwrap_or('.'))? }
			write!(f, "\n{:>p$} ", *yr.end() + 2, p = left_padding)?;
			for _ in xr { f.write_char('#')? }
			Ok(())
		}
	}
}


#[test]
fn tests() {
	const INPUT: &str = indoc::indoc! { "
		498,4 -> 498,6 -> 496,6
		503,4 -> 502,4 -> 502,9 -> 494,9
	" };
	assert_eq!(part1_impl(input_cave_from_str(INPUT)), 24);
	assert_eq!(part1(), 843);
	assert_eq!(part2_impl(input_cave_from_str(INPUT)), 93);
	assert_eq!(part2(), 27625);
}

#[cfg(BENCHING)]
mod bench {
	extern crate test;

	#[bench]
	fn part1(b: &mut test::Bencher) {
		b.iter(super::part1)
	}

	#[bench]
	fn part2(b: &mut test::Bencher) {
		b.iter(super::part2)
	}
}
