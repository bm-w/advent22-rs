// Copyright (c) 2022 Bastiaan Marinus van de Weerd


type Assignment = std::ops::RangeInclusive<usize>;
struct AssignmentsPair([Assignment; 2]);

trait RangeInclusiveExt {
	fn contains_range(&self, other: &Self) -> bool;
	fn overlaps_range(&self, other: &Self) -> bool;
}

impl<T: PartialOrd> RangeInclusiveExt for std::ops::RangeInclusive<T> {
	fn contains_range(&self, other: &Self) -> bool {
		*self.start() <= *other.start() && *self.end() >= *other.end()
	}

	fn overlaps_range(&self, other: &Self) -> bool {
		*self.start() <= *other.end() && *self.end() >= *other.start()
	}
}


fn input_assignments_pairs_from_str(s: &str) -> impl Iterator<Item = AssignmentsPair> + '_ {
	parsing::assignments_pairs_from_str(s).map(|r| r.unwrap())
}

fn input_assignments() -> impl Iterator<Item = AssignmentsPair> + 'static {
	input_assignments_pairs_from_str(include_str!("day04.txt"))
}


fn part1_impl(input_assignment_pairs: impl Iterator<Item = AssignmentsPair>) -> usize {
	input_assignment_pairs
		.filter(|AssignmentsPair([left, right])|
			left.contains_range(right) || right.contains_range(left))
		.count()
}

pub(crate) fn part1() -> usize {
	part1_impl(input_assignments())
}


fn part2_impl(input_assignment_pairs: impl Iterator<Item = AssignmentsPair>) -> usize {
	input_assignment_pairs
		.filter(|AssignmentsPair([left, right])|
			left.overlaps_range(right))
		.count()
}

pub(crate) fn part2() -> usize {
	part2_impl(input_assignments())
}


mod parsing {
	use std::{num::ParseIntError, ops::RangeInclusive, str::FromStr};
	use super::AssignmentsPair;

	#[allow(dead_code)]
	#[derive(Debug)]
	pub(super) enum AssignmentError {
		NoHyphen,
		StartError(ParseIntError),
		EndError(ParseIntError),
		Negative { start: usize, end: usize },
	}

	#[derive(Debug)]
	pub(super) enum AssignmentsPairError {
		NoComma,
		LeftAssignment(AssignmentError),
		RightAssignment(AssignmentError),
	}

	impl FromStr for AssignmentsPair {
		type Err = AssignmentsPairError;
		fn from_str(s: &str) -> Result<Self, Self::Err> {
			let (left, right) = s.split_once(',')
				.ok_or(AssignmentsPairError::NoComma)?;
			fn assignment_from_str(s: &str) -> Result<RangeInclusive<usize>, AssignmentError> {
				let (start, end) = s.split_once('-')
					.ok_or(AssignmentError::NoHyphen)?;
				let start = start.parse().map_err(AssignmentError::StartError)?;
				let end = end.parse().map_err(AssignmentError::EndError)?;
				if end < start { return Err(AssignmentError::Negative { start, end }) }
				Ok(start..=end)
			}
			let left = assignment_from_str(left)
				.map_err(AssignmentsPairError::LeftAssignment)?;
			let right = assignment_from_str(right)
				.map_err(AssignmentsPairError::RightAssignment)?;
			Ok(AssignmentsPair([left, right]))
		}
	}

	#[allow(dead_code)]
	#[derive(Debug)]
	pub(super) enum AssignmentsPairsError {
		Empty,
		Pair { line: usize, source: AssignmentsPairError }
	}

	pub(super) fn assignments_pairs_from_str(s: &str) -> impl Iterator<Item = Result<AssignmentsPair, AssignmentsPairsError>> + '_ {
		use {std::iter::once, itertools::Either::*};
		if s.is_empty() { return Left(once(Err(AssignmentsPairsError::Empty))) }
		Right(s.lines()
			.enumerate()
			.map(|(l, line)| line.parse()
				.map_err(|e| AssignmentsPairsError::Pair { line: l + 1, source: e })))
	}
}


#[test]
fn tests() {
	const INPUT: &str = indoc::indoc! { "
		2-4,6-8
		2-3,4-5
		5-7,7-9
		2-8,3-7
		6-6,4-6
		2-6,4-8
	" };
	assert_eq!(part1_impl(input_assignments_pairs_from_str(INPUT)), 2);
	assert_eq!(part1(), 477);
	assert_eq!(part2_impl(input_assignments_pairs_from_str(INPUT)), 4);
	assert_eq!(part2(), 830);
}
