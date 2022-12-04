// Copyright (c) 2022 Bastiaan Marinus van de Weerd


struct Rucksack<'s>(&'s str);

impl Rucksack<'_> {
	fn as_items(&self) -> &[u8] {
		self.0.as_bytes()
	}

	fn as_compartments_items(&self) -> [&[u8]; 2] {
		let half_len = self.0.len() / 2;
		[self.0[..half_len].as_bytes(), self.0[half_len..].as_bytes()]
	}

	fn item_priority(item: u8) -> u8 {
		if item >= b'a' { 1 + item - b'a' } else { 27 + item - b'A' }
	}
}


fn input_rucksacks_from_str(s: &str) -> impl Iterator<Item = Rucksack<'_>> + '_ {
	parsing::rucksacks_from_str(s).map(|r| r.unwrap())
}

fn input_rucksacks() -> impl Iterator<Item = Rucksack<'static>> {
	input_rucksacks_from_str(include_str!("day03.txt"))
}


fn part1_impl<'s>(input_rucksacks: impl Iterator<Item = Rucksack<'s>>) -> u64 {
	// As seen on ThePrimeagen’s stream (author unknown?):
	// https://www.twitch.tv/videos/1669214699 (starting at 1:21:41)
	input_rucksacks
		.map(|rucksack| {
			let compartments_items = rucksack.as_compartments_items();
			let mut seen = [false; 52];
			for &item in compartments_items[0] {
				seen[Rucksack::item_priority(item) as usize - 1] = true
			}
			compartments_items[1].iter().find_map(|&item| {
				let item_priority = Rucksack::item_priority(item);
				seen[item_priority as usize - 1].then_some(item_priority)
			}).unwrap() as u64
		})
		.sum()
}

pub(crate) fn part1() -> u64 {
	part1_impl(input_rucksacks())
}


fn part2_impl<'s>(input_rucksacks: impl Iterator<Item = Rucksack<'s>>) -> u64 {
	// As seen on ThePrimeagen’s stream (author unknown?):
	// https://www.twitch.tv/videos/1669214699 (starting at 1:21:41)
	use itertools::Itertools as _;
	input_rucksacks
		// TODO(bm-w): Use `array_chunks` once it’s stabilized
		.chunks(3)
		.into_iter()
		.map(|chunk| chunk.into_iter().enumerate()
			.scan([0_u8; 52], |bit_counts, (i, rucksack)| {
				for &item in rucksack.as_items() {
					let item_priority = Rucksack::item_priority(item);
					let bit_count = &mut bit_counts[item_priority as usize - 1];
					*bit_count |= 1 << i;
					if *bit_count == 0b111 { return Some(Some(item_priority)) }
				}
				Some(None)
			})
			.flatten()
			.next().unwrap() as u64)
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
