// Copyright (c) 2022 Bastiaan Marinus van de Weerd


#[cfg_attr(test, derive(Copy, Clone, Debug))]
enum Instr {
	Nop,
	AddX(i8),
}

mod cpu {
	use super::Instr;

	pub(super) fn execute(instrs: impl Iterator<Item = Instr>) -> impl Iterator<Item = i8> {
		use {std::iter::once, itertools::Either};
		instrs
			.scan(1, |x, instr| Some(match instr {
				Instr::Nop => Either::Left(once(*x)),
				Instr::AddX(v) => {
					let x0 = *x;
					*x = x0 + v;
					Either::Right([x0, x0].into_iter())
				}
			}))
			.flatten()
	}
}

struct Crt([bool; 240]);

impl std::fmt::Display for Crt {
	fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
		use std::fmt::Write;
		for y in 0..6 {
			for x in 0..40 {
				f.write_char(if self.0[y * 40 + x] { '#' } else { '.' })?
			}
			if y < 5 { f.write_char('\n')? }
		}
		Ok(())
	}
}


fn input_instrs_from_str(s: &str) -> impl Iterator<Item = Instr> + '_ {
	parsing::instrs_from_str(s).map(|r| r.unwrap())
}

fn input_instrs() -> impl Iterator<Item = Instr> {
	input_instrs_from_str(include_str!("day10.txt"))
}


fn part1_impl(input_instrs: impl Iterator<Item = Instr>) -> i64 {
	cpu::execute(input_instrs)
		.enumerate()
		.filter_map(|(i, x)| (i >= 19 && (i - 19) % 40 == 0)
			.then_some((i as i64 + 1) * x as i64))
		.sum()
}

pub(crate) fn part1() -> i64 {
	part1_impl(input_instrs())
}


fn part2_impl(input_instrs: impl Iterator<Item = Instr>) -> impl std::fmt::Display {
	let mut pixels = [false; 240];
	for (i, x) in cpu::execute(input_instrs).enumerate() {
		pixels[i] = ((i % 40) as i8).abs_diff(x) <= 1
	}
	Crt(pixels)
}

pub(crate) fn part2() -> impl std::fmt::Display {
	part2_impl(input_instrs())
}


mod parsing {
	use std::{num::ParseIntError, str::FromStr};
	use super::Instr;

	#[derive(Debug)]
	pub(super) enum InstrError {
		Empty,
		Invalid,
		AddX(ParseIntError),
	}

	impl FromStr for Instr {
		type Err = InstrError;
		fn from_str(s: &str) -> Result<Self, Self::Err> {
			if s.is_empty() { Err(InstrError::Empty) }
			else if s == "noop" { Ok(Instr::Nop) }
			else if let Some(v) = s.strip_prefix("addx ") {
				Ok(Instr::AddX(v.parse().map_err(InstrError::AddX)?)) }
			else { return Err(InstrError::Invalid) }
		}
	}

	#[allow(dead_code)]
	#[derive(Debug)]
	pub(super) struct InstrsError {
		line: usize,
		source: InstrError,
	}

	pub(super) fn instrs_from_str(s: &str)
	-> impl Iterator<Item = Result<Instr, InstrsError>> + '_ {
		s.lines()
			.enumerate()
			.map(|(l, line)| line.parse()
				.map_err(|e| InstrsError { line: l + 1, source: e }))
	}
}

#[test]
fn tests() {
	const INPUTS: [&str; 2] = [
		indoc::indoc! { "
			noop
			addx 3
			addx -5
		" },
		include_str!("day10-test.txt"),
	];
	assert_eq!(part1_impl(input_instrs_from_str(INPUTS[0])), 0);
	assert_eq!(part1_impl(input_instrs_from_str(INPUTS[1])), 13140);
	assert_eq!(part1(), 15140);
	assert_eq!(part2_impl(input_instrs_from_str(INPUTS[1])).to_string(), indoc::indoc! { "
		##..##..##..##..##..##..##..##..##..##..
		###...###...###...###...###...###...###.
		####....####....####....####....####....
		#####.....#####.....#####.....#####.....
		######......######......######......####
		#######.......#######.......#######....." });
	assert_eq!(part2().to_string(), indoc::indoc! { "
		###..###....##..##..####..##...##..###..
		#..#.#..#....#.#..#....#.#..#.#..#.#..#.
		###..#..#....#.#..#...#..#....#..#.#..#.
		#..#.###.....#.####..#...#.##.####.###..
		#..#.#....#..#.#..#.#....#..#.#..#.#....
		###..#.....##..#..#.####..###.#..#.#...." });
}
