// Copyright (c) 2022 Bastiaan Marinus van de Weerd


struct Rucksack<'s>(&'s str);

impl Rucksack<'_> {
	fn compartments(&self) -> [&str; 2] {
		let half_len = self.0.len() / 2;
		[&self.0[..half_len], &self.0[half_len..]]
	}

	fn prioritize_common_items<'i>(common_item: impl Iterator<Item = &'i u8>) -> u64 {
		use itertools::Itertools as _;
		let common_item = match common_item.exactly_one() {
			Ok(&b) => b,
			Err(i) => panic!("Not exactly 1: {:?}", i.size_hint()),
		};
		let priority = if common_item >= b'a' { 1 + common_item - b'a' }
			else { 27 + common_item - b'A' } as u64;
		#[cfg(LOGGING)]
		println!("{common_item} ({}): {priority}", common_item as char);
		#[allow(clippy::let_and_return)]
		priority
	}
}


fn input_rucksacks_from_str(s: &str) -> impl Iterator<Item = Rucksack<'_>> + '_ {
	parsing::rucksacks_from_str(s).map(|r| r.unwrap())
}

fn input_rucksacks() -> impl Iterator<Item = Rucksack<'static>> {
	input_rucksacks_from_str(include_str!("day03.txt"))
}


fn part1_impl<'s>(input_rucksacks: impl Iterator<Item = Rucksack<'s>>) -> u64 {
	use std::collections::HashSet;
	input_rucksacks
		.map(|r| {
			let [c0, c1] = r.compartments();
			let s0 = HashSet::<u8>::from_iter(c0.bytes());
			let s1 = HashSet::<u8>::from_iter(c1.bytes());
			Rucksack::prioritize_common_items(s0.intersection(&s1))
		})
		.sum()
}

pub(crate) fn part1() -> u64 {
	part1_impl(input_rucksacks())
}


fn part2_impl<'s>(input_rucksacks: impl Iterator<Item = Rucksack<'s>>) -> u64 {
	use {std::collections::HashSet, itertools::Itertools};
	input_rucksacks
		.chunks(3)
		.into_iter()
		.map(|chunk| {
			let mut ss = chunk.into_iter().map(|r| HashSet::<u8>::from_iter(r.0.bytes()));
			Rucksack::prioritize_common_items(ss.next().unwrap()
				.intersection(&ss.next().unwrap())
				.copied()
				.collect::<HashSet<_>>()
				.intersection(&ss.next().unwrap()))
		})
		.sum()
}

pub(crate) fn part2() -> u64 {
	part2_impl(input_rucksacks())
}


mod parsing {
	use super::Rucksack;

	#[allow(dead_code)]
	#[derive(Debug)]
	pub(super) enum RucksackError {
		OddLen(usize),
		InvalidItem(char),
	}

	impl<'s> TryFrom<&'s str> for Rucksack<'s> {
		type Error = RucksackError;
		fn try_from(s: &'s str) -> Result<Self, Self::Error> {
			use RucksackError::*;
			if s.len() % 2 != 0 { return Err(OddLen(s.len())); }
			if let Some(c) = s.chars().find(|c| !c.is_ascii_alphabetic()) {
				return Err(InvalidItem(c))
			}
			Ok(Rucksack(s))
		}
	}

	#[allow(dead_code)]
	#[derive(Debug)]
	pub(super) enum RucksacksError {
		Empty,
		Rucksack { line: usize, source: RucksackError }
	}

	pub(super) fn rucksacks_from_str(s: &str) -> impl Iterator<Item = Result<Rucksack<'_>, RucksacksError>> + '_ {
		use {std::iter::once, itertools::Either::*};
		if s.is_empty() { return Left(once(Err(RucksacksError::Empty))) }
		Right(s.lines()
			.enumerate()
			.map(|(l, line)| line.try_into()
				.map_err(|e| RucksacksError::Rucksack { line: l + 1, source: e})))
	}
}


#[test]
fn tests() {
	const INPUT: &str = indoc::indoc! { "
		vJrwpWtwJgWrhcsFMMfFFhFp
		jqHRNqRjqzjGDLGLrsFMfFZSrLrFZsSL
		PmmdzqPrVvPwwTWBwg
		wMqvLMZHhHMvwLHjbvcjnnSBnvTQFn
		ttgJtRGJQctTZtZT
		CrZsJsPPZsGzwwsLwLmpwMDw
	" };
	assert_eq!(part1_impl(input_rucksacks_from_str(INPUT)), 157);
	assert_eq!(part1(), 7446);
	assert_eq!(part2_impl(input_rucksacks_from_str(INPUT)), 70);
	assert_eq!(part2(), 2646);
}
