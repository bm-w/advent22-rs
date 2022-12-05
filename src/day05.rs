// Copyright (c) 2022 Bastiaan Marinus van de Weerd


#[cfg_attr(test, derive(Debug))]
struct Crate(u8);

#[cfg_attr(test, derive(Debug))]

struct Stacks(Vec<Vec<Crate>>);

#[cfg_attr(test, derive(Debug))]
struct Step {
	num_crates: std::num::NonZeroUsize,
	from_stack: usize,
	to_stack: usize,
}


fn input_from_str(s: &str) -> (Stacks, impl Iterator<Item = Step> + '_) {
	let (stacks, steps) = parsing::try_stacks_and_steps_from_str(s).unwrap();
	(stacks, steps.map(|r| r.unwrap()))
}

fn input() -> (Stacks, impl Iterator<Item = Step> + 'static) {
	input_from_str(include_str!("day05.txt"))
}


fn part1and2_impl(
	input: (Stacks, impl Iterator<Item = Step>),
	operate: impl Fn(&mut Stacks, Step),
) -> String {
	let (mut input_stacks, input_steps) = input;

	for step in input_steps { operate(&mut input_stacks, step) }

	// SAFETY: All crates labels are valid ASCII uppercase bytes
	unsafe {
		String::from_utf8_unchecked(input_stacks.0.into_iter()
			.flat_map(|s| s.last().map(|c| c.0))
			.collect())
	}
}


fn part1_impl(input: (Stacks, impl Iterator<Item = Step>)) -> String {
	part1and2_impl(input, |stacks, step| {
		for _ in 0..step.num_crates.get() {
			let crat = stacks.0[step.from_stack].pop().unwrap();
			stacks.0[step.to_stack].push(crat);
		}
	})
}

pub(crate) fn part1() -> String {
	part1_impl(input())
}


unsafe fn index_mut_unchecked<T, const N: usize>(s: &mut [T], at: [usize; N]) -> [&mut T; N] {
	let ptr = s.as_mut_ptr();
	std::array::from_fn(|i| &mut *ptr.add(at[i]))
}

fn part2_impl(input: (Stacks, impl Iterator<Item = Step>)) -> String {
	part1and2_impl(input, |stacks, step| {
		// SAFETY: `step.(from|to)_stack` are unequal and guaranteed to “point” into `stacks.0`
		let [from, to] = unsafe {
			index_mut_unchecked(&mut stacks.0, [step.from_stack, step.to_stack]) };
		to.extend(from.drain(from.len() - step.num_crates.get()..));
	})
}

pub(crate) fn part2() -> String {
	part2_impl(input())
}


mod parsing {
	use std::{str::FromStr, num::{ParseIntError, NonZeroUsize}};
	use super::{Crate, Stacks, Step};

	impl TryFrom<u8> for Crate {
		type Error = ();
		fn try_from(value: u8) -> Result<Self, Self::Error> {
			if !value.is_ascii_uppercase() { return Err(()) }
			Ok(Crate(value))
		}
	}

	#[allow(dead_code)]
	#[derive(Debug)]
	pub(super) enum StacksError {
		ExpectedLine(usize),
		LineLen { line: usize, len: Option<usize>, found: usize },
		InvalidByte { line: usize, column: usize, found: u8 },
		InvalidCrate { line: usize, column: usize, found: u8 },
		VoidBelowCrates { line: usize, column: usize }
	}

	fn try_stacks_from_lines<'l>(
		mut l: usize,
		lines: impl Iterator<Item = &'l str>
	) -> Result<Stacks, StacksError> {
		use StacksError::*;

		let mut len = None;
		let mut rev_stacks = vec![];

		enum State { VoidOrLabel, Void, Crate, Label }
		let mut state: Option<State> = None;

		for line in lines {
			if !matches!(state, Some(State::Label)) { state = None };

			let mut c = 0;
			macro_rules! ret_line_len_err { () => {
				return Err(LineLen { line: l + 1, len, found: c + 1 })
			} }

			while c < line.len() {
				if Some(c) == len { ret_line_len_err!() }

				match (c % 4, &state, line.as_bytes()[c]) {
					(0 | 2 | 3, Some(State::Label), b' ') => (),
					(0, None, b @ (b' ' | b'[')) => {
						if rev_stacks.len() < c / 4 + 1 { rev_stacks.push(vec![]) }
						state = match b {
							b'[' => Some(State::Crate),
							_ => Some(State::VoidOrLabel),
						}
					}
					(1, Some(State::VoidOrLabel), b' ') => {
						if !rev_stacks[(c - 1) / 4].is_empty() {
							return Err(VoidBelowCrates { line: l + 1, column: c + 1 })
						}
						state = Some(State::Void);
					}
					(1, Some(State::Crate), b) => {
						let crat = b.try_into().map_err(|_|
							InvalidCrate { line: l + 1, column: c + 1, found: b })?;
						rev_stacks[(c - 1) / 4].push(crat);
					}
					(1, Some(State::VoidOrLabel | State::Label), b) => {
						if !b.is_ascii_digit() || (b - b'0' - 1) as usize != (c - 1) / 4 {
							return Err(InvalidByte { line: l + 1, column: c + 1, found: b });
						}
						state = Some(State::Label);
					}
					(2, Some(State::Void), b' ') => (),
					(2, Some(State::Crate), b']') => (),
					(3, Some(State::Void | State::Crate), b' ') => state = None,
					(_, _, found) =>
						return Err(InvalidByte { line: l + 1, column: c + 1, found }),
				}

				c += 1;
			}

			if matches!(state, Some(State::Label)) { break }

			match len {
				None if (c + 1) % 4 != 0 => ret_line_len_err!(),
				None => len = Some(c),
				Some(prev_len) => if c < prev_len { ret_line_len_err!() },
			}

			l += 1;
		}

		if !matches!(state, Some(State::Label)) { return Err(ExpectedLine(l + 1)) }

		rev_stacks.iter_mut().for_each(|s| s.reverse());
		Ok(Stacks(rev_stacks))
	}

	impl FromStr for Stacks {
		type Err = StacksError;
		fn from_str(s: &str) -> Result<Self, Self::Err> {
			try_stacks_from_lines(0, s.lines())
		}
	}

	#[allow(dead_code)]
	#[derive(Debug)]
	pub(super) enum StepError {
		Format { column: usize },
		NumCrates(ParseIntError),
		FromStack(ParseIntError),
		ToStack(ParseIntError),
		SameStack,
	}

	impl FromStr for Step {
		type Err = StepError;
		fn from_str(s: &str) -> Result<Self, Self::Err> {
			let s_start = s.as_ptr();
			macro_rules! c { ( $s:expr ) => {
				// SAFETY: `$s` and `s_start` poin tot the same string slice
				unsafe { $s.as_ptr().offset_from(s_start) as usize }
			} }

			let s = s.strip_prefix("move ").ok_or(StepError::Format { column: 1 })?;

			let num_crates = s.find(' ').map(|p| &s[..p]).unwrap_or(s);
			let s = &s[num_crates.len()..];
			let num_crates = num_crates.parse().map_err(StepError::NumCrates)?;

			let s = s.strip_prefix(" from ").ok_or(StepError::Format { column: c!(s) + 1 })?;

			let from_stack = s.find(' ').map(|p| &s[..p]).unwrap_or(s);
			let s = &s[from_stack.len()..];
			let from_stack = from_stack.parse::<NonZeroUsize>().map_err(StepError::FromStack)?;

			let s = s.strip_prefix(" to ").ok_or(StepError::Format { column: c!(s) + 1 })?;

			let to_stack = s.parse::<NonZeroUsize>().map_err(StepError::ToStack)?;

			if from_stack == to_stack { return Err(StepError::SameStack) }

			Ok(Step {
				num_crates,
				from_stack: from_stack.get() - 1,
				to_stack: to_stack.get() - 1,
			})	
		}
	}

	#[allow(dead_code)]
	#[derive(Debug)]
	pub(super) enum StacksAndStepsError {
		Stacks(StacksError),
		NoBlank,
		Step { line: usize, source: StepError },
		NoSteps,
		InvalidStepFromStack { line: usize, from_stack: usize },
		InvalidStepToStack { line: usize, to_stack: usize },
	}

	pub(super) fn try_stacks_and_steps_from_str(s: &str) -> Result<(
		Stacks,
		impl Iterator<Item = Result<Step, StacksAndStepsError>> + '_
	), StacksAndStepsError> {
		let mut lines = s.lines().enumerate();

		let stacks = try_stacks_from_lines(0, (&mut lines).map(|(_, line)| line))
			.map_err(StacksAndStepsError::Stacks)?;

		if !matches!(lines.next(), Some((_, ""))) { return Err(StacksAndStepsError::NoBlank) }

		let mut lines = lines.peekable();
		if lines.peek().is_none() { return Err(StacksAndStepsError::NoSteps) }

		let stacks_range = 0..stacks.0.len();
		Ok((stacks, lines
			.map(move |(l, line)| {
				let step = line.parse()
					.map_err(|e| StacksAndStepsError::Step { line: l + 1, source: e })?;
				let Step { from_stack, to_stack, .. } = step;
				if !stacks_range.contains(&from_stack) { return Err(
					StacksAndStepsError::InvalidStepFromStack { line: l + 1, from_stack }) }
				if !stacks_range.contains(&to_stack) { return Err(
					StacksAndStepsError::InvalidStepToStack { line: l + 1, to_stack }) }
				Ok(step)
			})))
	}
}


#[test]
fn tests() {
	const INPUT: &str = indoc::indoc! { "
		    [D]    
		[N] [C]    
		[Z] [M] [P]
		 1   2   3 
		
		move 1 from 2 to 1
		move 3 from 1 to 3
		move 2 from 2 to 1
		move 1 from 1 to 2
	" };
	assert_eq!(part1_impl(input_from_str(INPUT)), "CMZ");
	assert_eq!(part1(), "TLNGFGMFN");
	assert_eq!(part2_impl(input_from_str(INPUT)), "MCD");
	assert_eq!(part2(), "FGLQJCMBD");
}
