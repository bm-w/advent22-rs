// Copyright (c) 2022 Bastiaan Marinus van de Weerd


fn calories_per_elf(input_calories: impl Iterator<Item = Option<usize>>) -> impl Iterator<Item = usize> {
	use itertools::Itertools;
	input_calories
		.coalesce(|left, right|
			if let Some(right) = right {
				Ok(left.map(|left| left + right))
			} else {
				Err((left, Some(0)))
			})
		.flatten()
}


fn input_calories_from_str(s: &str) -> impl Iterator<Item = Option<usize>> + '_ {
	parsing::calories_from_string(s).map(|r| r.unwrap())
}

fn input_calories() -> impl Iterator<Item = Option<usize>> {
	input_calories_from_str(include_str!("day01.txt"))
}


fn part1_impl(input_calories: impl Iterator<Item = Option<usize>>) -> usize {
	calories_per_elf(input_calories).max().unwrap()
}

pub(crate) fn part1() -> usize {
	part1_impl(input_calories())
}


pub(crate) fn part2_impl(input_calories: impl Iterator<Item = Option<usize>>) -> usize {
	let mut top_three = [0; 4];
	for calories in calories_per_elf(input_calories) {
		if calories > top_three[1] {
			top_three[0] = calories;
			top_three.sort()
		}
	}
	top_three[1..].iter().sum()
}

pub(crate) fn part2() -> usize {
	part2_impl(input_calories())
}


mod parsing {
	use std::num::ParseIntError;

	#[allow(dead_code)]
	#[derive(Debug)]
	pub(super) enum CaloriesError {
		Empty,
		Invalid { line: usize, source: ParseIntError },
	}

	pub(super) fn calories_from_string(s: &str) -> impl Iterator<Item = Result<Option<usize>, CaloriesError>> + '_ {
		use {std::iter::once, itertools::Either};
		if s.is_empty() { return Either::Left(once(Err(CaloriesError::Empty))) }

		Either::Right(s.lines()
			.enumerate()
			.map(|(l, line)| (!line.is_empty())
				.then(|| line.parse()
					.map_err(|e| CaloriesError::Invalid { line: l + 1, source: e }))
				.transpose()))
	}
}


#[test]
fn tests() {
	const INPUT: &str = indoc::indoc! { "
		1000
		2000
		3000
		
		4000
		
		5000
		6000
		
		7000
		8000
		9000
		
		10000
	" };
	assert_eq!(part1_impl(input_calories_from_str(INPUT)), 24_000);
	assert_eq!(part1(), 70509);
	assert_eq!(part2_impl(input_calories_from_str(INPUT)), 45_000);
	assert_eq!(part2(), 208567);
}
