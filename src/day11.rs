// Copyright (c) 2022 Bastiaan Marinus van de Weerd


struct ThrowTest {
	div_by: u64,
	if_true: usize,
	if_false: usize,
}

enum Operator { Add, Mul }
enum Operand { Value(u64), Old }
/// Left operand is always [`Operand::Old`].
struct Operation(Operator, Operand);

impl Operation {
	fn execute(&self, worry_level: u64) -> u64 {
		use {Operator::*, Operand::*};
		let rhs = match self.1 { Value(v) => v, Old => worry_level };
		match self.0 { Add => worry_level + rhs, Mul => worry_level * rhs }
	}
}

struct Monkey {
	items: Vec<u64>,
	operation: Operation,
	throw_test: ThrowTest,
}


fn input_monkeys_from_str(s: &str) -> impl AsRef<[Monkey]> + AsMut<[Monkey]> {
	parsing::try_monkeys_from_str(s).unwrap()
}

fn input_monkeys() -> impl AsRef<[Monkey]> + AsMut<[Monkey]> {
	input_monkeys_from_str(include_str!("day11.txt"))
}


fn part1and2_impl<const ROUNDS: usize>(
	mut input_monkeys: impl AsMut<[Monkey]>,
	reduce: impl Fn(u64) -> u64,
) -> u64 {
	let input_monkeys = input_monkeys.as_mut();
	let n = input_monkeys.len();
	assert!(n >= 2);

	let mut inspected_count = vec![0; n];
	for i in (0..ROUNDS).flat_map(|_| 0..n) {
		let (head, tail) = input_monkeys.split_at_mut(i);
		let (monkey, tail) = tail.split_at_mut(1);
		let monkey = &mut monkey[0];

		inspected_count[i] += monkey.items.len();

		for worry_level in monkey.items.drain(..) {
			let new_worry_level = reduce(monkey.operation.execute(worry_level));

			let i_target = if new_worry_level % monkey.throw_test.div_by == 0
				{ monkey.throw_test.if_true }
				else { monkey.throw_test.if_false };
			assert_ne!(i_target, i);
			if i_target < i { &mut head[i_target] } else { &mut tail[i_target - i - 1] }
				.items.push(new_worry_level);
		}
	}

	inspected_count.sort();
	inspected_count[n - 2..].iter().product::<usize>() as u64
}


fn part1_impl(input_monkeys: impl AsMut<[Monkey]>) -> u64 {
	part1and2_impl::<20>(input_monkeys, |worry_level| worry_level / 3)
}

pub(crate) fn part1() -> u64 {
	part1_impl(input_monkeys())
}


fn part2_impl(input_monkeys: impl AsRef<[Monkey]> + AsMut<[Monkey]>) -> u64 {
	let div_by_product = input_monkeys.as_ref().iter()
		.map(|monkey| monkey.throw_test.div_by)
		.product::<u64>();
	part1and2_impl::<10_000>(input_monkeys, |worry_level| worry_level % div_by_product)
}

pub(crate) fn part2() -> u64 {
	part2_impl(input_monkeys())
}


mod parsing {
	use {std::{num::ParseIntError, str::FromStr}, itertools::Itertools as _};
	use super::{ThrowTest, Operator, Operand, Operation, Monkey};

	macro_rules! str_offset { ( $s0:expr, $s:expr ) => {
		// SAFETY: It is assumed that `$s0` and `$s` point into the same string slice
		unsafe { $s.as_ptr().offset_from($s0.as_ptr()) as usize }
	} }

	fn try_strip_prefix<'s, 'p>(s: &'s str, prefix: &'p str) -> Result<&'s str, &'s str> {
		s.strip_prefix(prefix).ok_or_else(|| {
			let p = s.bytes().zip(prefix.bytes()).position(|(s, p)| s != p).unwrap();
			&s[p..]
		})
	}

	impl TryFrom<char> for Operator {
		type Error = ();
		fn try_from(value: char) -> Result<Self, Self::Error> {
			match value {
				'+' => Ok(Operator::Add),
				'*' => Ok(Operator::Mul),
				_ => Err(())
			}
		}
	}

	impl FromStr for Operand {
		type Err = ParseIntError;
		fn from_str(s: &str) -> Result<Self, Self::Err> {
			match s {
				"old" => Ok(Operand::Old),
				value => Ok(Operand::Value(value.parse()?)),
			}
		}
	}

	#[allow(dead_code)]
	#[derive(Debug)]
	pub(super) enum OperationError {
		Format { column: usize },
		Operator(Option<char>),
		Operand(<Operand as FromStr>::Err),
	}

	fn try_operation_from_str(s: &str) -> Result<(Operation, &str), OperationError> {
		let s_start = s;
		macro_rules! c { ( $s:expr ) => { str_offset!(s_start, $s) } }

		let s = try_strip_prefix(s, "new = old ")
			.map_err(|s| OperationError::Format { column: c!(s) + 1 })?;
		let (operator, s) = s.split_once(' ')
			.ok_or(OperationError::Format { column: c!(s) + s.len() })?;
		let operator = {
			let chr = operator.chars().exactly_one()
				.map_err(|mut chars| OperationError::Operator(chars.nth(1)))?;
			chr.try_into().map_err(|_| OperationError::Operator(Some(chr)))?
		};
		let (operand, _) = s.split_once('\n').unwrap_or((s, &s[s.len()..]));
		let s = &s[operand.len()..];
		let operand = operand.parse().map_err(OperationError::Operand)?;
		Ok((Operation(operator, operand), s))
	}

	impl FromStr for Operation {
		type Err = OperationError;
		fn from_str(s: &str) -> Result<Self, Self::Err> {
			let (operation, rest) = try_operation_from_str(s)?;
			if !rest.is_empty() { return Err(
				OperationError::Format { column: str_offset!(s, rest) }) }
			Ok(operation)
		}
	}

	#[allow(dead_code)]
	#[derive(Debug)]
	pub(super) enum ThrowTestError {
		Format { column: usize },
		DivBy(ParseIntError),
		If(bool, ParseIntError),
	}

	fn try_throw_test_from_str(s: &str) -> Result<(ThrowTest, &str), ThrowTestError> {
		let s_start = s;
		macro_rules! c { ( $s:expr ) => { str_offset!(s_start, $s) } }

		let s = try_strip_prefix(s.trim_start(), "Test: divisible by ")
			.map_err(|s| ThrowTestError::Format { column: c!(s) + 1 })?;
		let (div_by, s) = s.split_once('\n')
			.ok_or(ThrowTestError::Format { column: c!(s) + s.len() })?;
		let div_by = div_by.parse().map_err(ThrowTestError::DivBy)?;
		let s = try_strip_prefix(s.trim_start(), "If true: throw to monkey ")
			.map_err(|s| ThrowTestError::Format { column: c!(s) + 1 })?;
		let (if_true, s) = s.split_once('\n')
			.ok_or(ThrowTestError::Format { column: c!(s) + s.len() })?;
		let if_true = if_true.parse().map_err(|e| ThrowTestError::If(true, e))?;
		let s = try_strip_prefix(s.trim_start(), "If false: throw to monkey ")
			.map_err(|s| ThrowTestError::Format { column: c!(s) + 1 })?;
		let (if_false, _) = s.split_once('\n').unwrap_or((s, &s[s.len()..]));
		let s = &s[if_false.len()..];
		let if_false = if_false.parse().map_err(|e| ThrowTestError::If(false, e))?;
		Ok((ThrowTest { div_by, if_true, if_false }, s))
	}

	impl FromStr for ThrowTest {
		type Err = ThrowTestError;
		fn from_str(s: &str) -> Result<Self, Self::Err> {
			let (throw_test, rest) = try_throw_test_from_str(s)?;
			if !rest.is_empty() { return Err(
				ThrowTestError::Format { column: str_offset!(s, rest) }) }
			Ok(throw_test)
		}
	}

	#[allow(dead_code)]
	#[derive(Debug)]
	pub(super) enum MonkeyError {
		Format { column: usize },
		Id(ParseIntError),
		StartingItems { offset: usize, source: ParseIntError },
		Operation(OperationError),
		ThrowTest(ThrowTestError),
	}

	fn try_monkey_from_str(s: &str) -> Result<(usize, Monkey, &str), MonkeyError> {
		let s_start = s;
		macro_rules! c { ( $s:expr ) => { str_offset!(s_start, $s) } }

		let s = try_strip_prefix(s, "Monkey ")
			.map_err(|s| MonkeyError::Format { column: c!(s) + 1 })?;
		let (id, s) = s.split_once(':')
			.ok_or(MonkeyError::Format { column: c!(s) + s.len() })?;
		let id = id.parse().map_err(MonkeyError::Id)?;
		let mut s = try_strip_prefix(s, "\n") // TODO: Pass `char` instead
			.and_then(|s| try_strip_prefix(s.trim_start(), "Starting items: "))
			.map_err(|s| MonkeyError::Format { column: c!(s) + 1 })?;
		let mut starting_items = vec![];
		loop {
			let (item, rest) = s.split_once(|c| c == ',' || c == '\n')
				.ok_or(MonkeyError::Format { column: c!(s) + s.len() })?;
			let last = s.as_bytes()[item.len()] == b'\n';
			s = rest;
			starting_items.push(item.parse().map_err(|e|
				MonkeyError::StartingItems { offset: starting_items.len(), source: e })?);
			if last { break }
			s = s.trim_start();
		};
		let s = try_strip_prefix(s.trim_start(), "Operation: ")
			.map_err(|s| MonkeyError::Format { column: c!(s) + 1 })?;
		let (operation, s) = try_operation_from_str(s).map_err(MonkeyError::Operation)?;
		let s = try_strip_prefix(s, "\n") // TODO: Pass `char` instead
			.map_err(|s| MonkeyError::Format { column: c!(s) + 1 })?;
		let (throw_test, s) = try_throw_test_from_str(s.trim_start())
			.map_err(MonkeyError::ThrowTest)?;
		Ok((id, Monkey { items: starting_items, operation, throw_test }, s))
	}

	impl FromStr for Monkey {
		type Err = MonkeyError;
		fn from_str(s: &str) -> Result<Self, Self::Err> {
			let (_, monkey, rest) = try_monkey_from_str(s)?;
			if !rest.is_empty() { return Err(
				MonkeyError::Format { column: str_offset!(s, rest) }) }
			Ok(monkey)
		}
	}

	#[derive(Debug)]
	pub(super) enum MonkeysErrorKind {
		Format,
		Monkey(MonkeyError),
		Id(usize),
	}

	#[allow(dead_code)]
	#[derive(Debug)]
	pub(super) struct MonkeysError { line: usize, kind: MonkeysErrorKind }

	pub(super) fn try_monkeys_from_str(mut s: &str)
	-> Result<impl AsRef<[Monkey]> + AsMut<[Monkey]>, MonkeysError> {
		let s_start = s;
		let mut monkeys = vec![];
		loop {
			let l = || &s_start[..s.len()].lines().count() + 1;
			let (id, monkey, rest) = try_monkey_from_str(s).map_err(|e|
				MonkeysError { line: l() + 1, kind: MonkeysErrorKind::Monkey(e) })?;
			if id != monkeys.len() { return Err(
				MonkeysError { line: l() + 1, kind: MonkeysErrorKind::Id(id) }) }
			monkeys.push(monkey);
			s = rest;
			if s.is_empty() || s == "\n" { break }
			s = s.strip_prefix("\n\n").ok_or(
				MonkeysError { line: l() + 1, kind: MonkeysErrorKind::Format })?;
		}
		Ok(monkeys)
	}
}


#[test]
fn tests() {
	const INPUT: &str = indoc::indoc! { "
		Monkey 0:
		  Starting items: 79, 98
		  Operation: new = old * 19
		  Test: divisible by 23
		    If true: throw to monkey 2
		    If false: throw to monkey 3

		Monkey 1:
		  Starting items: 54, 65, 75, 74
		  Operation: new = old + 6
		  Test: divisible by 19
		    If true: throw to monkey 2
		    If false: throw to monkey 0

		Monkey 2:
		  Starting items: 79, 60, 97
		  Operation: new = old * old
		  Test: divisible by 13
		    If true: throw to monkey 1
		    If false: throw to monkey 3

		Monkey 3:
		  Starting items: 74
		  Operation: new = old + 3
		  Test: divisible by 17
		    If true: throw to monkey 0
		    If false: throw to monkey 1
	" };
	assert_eq!(part1_impl(input_monkeys_from_str(INPUT)), 10605);
	assert_eq!(part1(), 55944);
	assert_eq!(part2_impl(input_monkeys_from_str(INPUT)), 2713310158);
	assert_eq!(part2(), 15117269860);
}
