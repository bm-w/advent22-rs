// Copyright (c) 2022 Bastiaan Marinus van de Weerd


fn input_numbers_from_str(s: &str) -> impl Iterator<Item = i64> + '_ {
	parsing::numbers_from_str(s).map(|r| r.unwrap())
}

fn input_numbers() -> impl Iterator<Item = i64> {
	input_numbers_from_str(include_str!("day20.txt"))
}


fn part1and2_impl<const MIXES: usize, const DECRYPTION_KEY: i64>(
	input_numbers: impl Iterator<Item = i64>
) -> i64 {

	// Doubly-linked list (using indices), but seeing other solutions it’s clearly much
	// faster to just use an array and move elements around (with the implied `memmove`s).
	struct Cell {
		number: i64,
		prev: usize,
		next: usize,
	}

	let mut cells = input_numbers
		.enumerate()
		.map(|(i, number)| Cell {
			number: number * DECRYPTION_KEY,
			prev: i.saturating_sub(1),
			next: i + 1 })
		.collect::<Vec<_>>();
	let len = cells.len();
	dbg!(len);
	cells[0].prev = len - 1;
	cells[len - 1].next = 0;

	let mut i0 = None;
	for _ in 0..MIXES {
		for i in 0..len {
			macro_rules! remove_and_insert {
				( $cells:ident, $prev:ident, $next:ident, $walk:expr, $i:ident ) => {
					$cells[$prev].next = $next;
					$cells[$next].prev = $prev;
					let (prev, next) = $walk;
					cells[prev].next = $i;
					cells[i].prev = prev;
					cells[i].next = next;
					cells[next].prev = $i;
				}
			}
			match &cells[i] {
				Cell { number: 0, .. } => i0 = Some(i),
				Cell { number, .. } if number.unsigned_abs() as usize % len == 0 => (),
				&Cell { number, mut prev, next } if number < 0 => {
					remove_and_insert!(cells, prev, next, {
						for _ in 0..number.unsigned_abs() as usize % (len - 1) {
							prev = cells[prev].prev
						}
						(prev, cells[prev].next)
					}, i);
				}
				&Cell { number, prev, mut next } => {
					remove_and_insert!(cells, prev, next, {
						for _ in 0..number as usize % (len - 1) {
							next = cells[next].next
						}
						(cells[next].prev, next)
					}, i);
				}
			}
		}
	}

	let Some(mut next) = i0 else { panic!("Did not encounter 0!") };
	for _ in 0..(1000 % len) { next = cells[next].next }
	let number1000 = cells[next].number;
	for _ in 0..(1000 % len) { next = cells[next].next }
	let number2000 = cells[next].number;
	for _ in 0..(1000 % len) { next = cells[next].next }
	number1000 + number2000 + cells[next].number
}


fn part1_impl(input_numbers: impl Iterator<Item = i64>) -> i64 {
	part1and2_impl::<1, 1>(input_numbers)
}

pub(crate) fn part1() -> i64 {
	part1_impl(input_numbers())
}


fn part2_impl(input_numbers: impl Iterator<Item = i64>) -> i64 {
	part1and2_impl::<10, 811589153>(input_numbers)
}

pub(crate) fn part2() -> i64 {
	part2_impl(input_numbers())
}


mod parsing {
	use std::num::ParseIntError;

	#[allow(dead_code)]
	#[derive(Debug)]
	pub(super) struct NumbersError { line: usize, source: ParseIntError }

	pub(super) fn numbers_from_str(s: &str)
	-> impl Iterator<Item = Result<i64, NumbersError>> + '_ {
		s.lines()
			.enumerate()
			.map(|(l, line)| line.parse()
				.map_err(|e| NumbersError { line: l, source: e }))
	}
}


#[test]
fn tests() {
	const INPUT: &str = indoc::indoc! { "
		1
		2
		-3
		3
		-2
		0
		4
	" };
	assert_eq!(part1_impl(input_numbers_from_str(INPUT)), 3);
	assert_eq!(part1(), 4151);
	assert_eq!(part2_impl(input_numbers_from_str(INPUT)), 1623178306);
	assert_eq!(part2(), 7848878698663);
}
