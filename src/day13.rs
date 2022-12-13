// Copyright (c) 2022 Bastiaan Marinus van de Weerd


#[derive(PartialEq, Eq)]
enum Value {
	Int(u8),
	List(Vec<Value>),
}

impl PartialOrd for Value {
	fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
		Some(self.cmp(other))
	}
}

// TODO(bm-w): Does this require custom implementation of `PartialEq` as well?
impl Ord for Value {
	fn cmp(&self, other: &Self) -> std::cmp::Ordering {
		use Value::*;
		match (self, other) {
			(Int(left), Int(right)) => left.cmp(right),
			(List(left), List(right)) => left.cmp(right),
			(Int(left_int), right) => List(vec![Int(*left_int)]).cmp(right),
			(left, Int(right_int)) => left.cmp(&List(vec![Int(*right_int)]))
		}
	}
}

struct Packet(Vec<Value>);

impl Packet {
	fn is_divider(&self) -> bool {
		if self.0.len() != 1 { return false }
		let Value::List(values) = &self.0[0] else { return false };
		if values.len() != 1 { return false }
		matches!(&values[0], Value::Int(2 | 6))
	}
}


fn optional_input_packets_from_str(s: &str) -> impl Iterator<Item = Option<Packet>> + '_ {
	parsing::optional_packets_from_str(s).map(|r| r.unwrap())
}

fn optional_input_packets() -> impl Iterator<Item = Option<Packet>> + 'static {
	optional_input_packets_from_str(include_str!("day13.txt"))
}


fn part1_impl(mut input_values: impl Iterator<Item = Option<Packet>>) -> usize {
	use itertools::Itertools as _;
	let sum = input_values.by_ref()
		.flatten()
		.tuples()
		.enumerate()
		.filter_map(|(i, (left, right))| (left.0 < right.0)
			.then_some(i + 1))
		.sum();
	assert!(input_values.next().is_none());
	sum
}

pub(crate) fn part1() -> usize {
	part1_impl(optional_input_packets())
}


fn part2_impl(input_values: impl Iterator<Item = Option<Packet>>) -> usize {
	use {itertools::Itertools as _, Value::*};
	input_values
		.flatten()
		.chain([
			Packet(vec![List(vec![Int(2)])]),
			Packet(vec![List(vec![Int(6)])])])
		.sorted_by(|l, r| l.0.cmp(&r.0))
		.enumerate()
		.filter_map(|(i, packet)| packet.is_divider()
			.then_some(i + 1))
		.product()
}

pub(crate) fn part2() -> usize {
	part2_impl(optional_input_packets())

}


mod parsing {
	use std::{num::ParseIntError, str::FromStr};
	use super::{Value, Packet};

	#[allow(dead_code)]
	#[derive(Debug)]
	pub(super) enum ValueError {
		Int { column: usize, source: ParseIntError },
		InvalidByte { column: usize, found: u8 },
		EndOfString
	}

	impl FromStr for Value {
		type Err = ValueError;
		fn from_str(s: &str) -> Result<Self, Self::Err> {

			enum State<'s> {
				Int(&'s str),
				List(Vec<Value>),
				AfterValue,
			}

			let mut c = 0;
			let mut stack = vec![];

			macro_rules! parse_int_value { ( $int:expr ) => { {
				Value::Int($int.parse().map_err(|e|
					ValueError::Int { column: c - $int.len() + 1, source: e })?)
			} } }

			macro_rules! push_or_return { ( $value:expr ) => { {
				let value = $value;
				match stack.last_mut() {
					Some(State::List(values)) => values.push(value),
					None => return Ok(value),
					_ => unreachable!(),
				}
			} } }

			while c < s.as_bytes().len() {
				match (s.as_bytes()[c], stack.last_mut()) {
					(b'[', _) => stack.push(State::List(vec![])),
					(d, None | Some(State::List(_))) if d.is_ascii_digit() =>
						stack.push(State::Int(&s[c..=c])),
					(b, Some(State::Int(int))) if b.is_ascii_digit() =>
						*int = &s[c - int.len()..=c],
					(_, Some(State::Int(_))) => {
						let Some(State::Int(int)) = stack.pop() else { unreachable!() };
						push_or_return!(parse_int_value!(int));
						stack.push(State::AfterValue);
						continue
					}
					(b @ (b',' | b']'), Some(State::AfterValue)) => {
						_ = stack.pop();
						if b == b']' { continue }
					},
					(b']', Some(State::List(_))) => {
						let Some(State::List(values)) = stack.pop() else { unreachable!() };
						push_or_return!(Value::List(values));
						stack.push(State::AfterValue)
					}
					(b, _) => return Err(ValueError::InvalidByte { column: c + 1, found: b })
				}
				c += 1;
			}

			match (stack.len() == 1).then(|| stack.remove(0)) {
				Some(State::Int(int)) => Ok(parse_int_value!(int)),
				_ => Err(ValueError::EndOfString),
			}
		}
	}

	#[allow(dead_code)]
	#[derive(Debug)]
	pub(super) enum PacketError {
		NotAList,
		Value(ValueError)
	}

	impl FromStr for Packet {
		type Err = PacketError;
		fn from_str(s: &str) -> Result<Self, Self::Err> {
			if !s.starts_with('[') { return Err(PacketError::NotAList) }
			let Value::List(values) = s.parse()
				.map_err(PacketError::Value)? else { unreachable!() };
			Ok(Packet(values))
		}
	}

	#[allow(dead_code)]
	#[derive(Debug)]
	pub(super) struct PacketsError { line: usize, source: PacketError }

	pub(super) fn optional_packets_from_str(s: &str)
	-> impl Iterator<Item = Result<Option<Packet>, PacketsError>> + '_ {
		s.lines()
			.enumerate()
			.map(|(l, line)| (!line.is_empty())
				.then(|| line.parse()
					.map_err(|e| PacketsError { line: l + 1, source: e }))
				.transpose())
	}
}


#[test]
fn tests() {
	const INPUT: &str = indoc::indoc! { "
		[1,1,3,1,1]
		[1,1,5,1,1]

		[[1],[2,3,4]]
		[[1],4]

		[9]
		[[8,7,6]]

		[[4,4],4,4]
		[[4,4],4,4,4]

		[7,7,7,7]
		[7,7,7]

		[]
		[3]

		[[[]]]
		[[]]

		[1,[2,[3,[4,[5,6,7]]]],8,9]
		[1,[2,[3,[4,[5,6,0]]]],8,9]
	" };
	assert!("137".parse::<Value>().is_ok());
	assert_eq!(part1_impl(optional_input_packets_from_str(INPUT)), 13);
	assert_eq!(part1(), 5659);
	assert_eq!(part2_impl(optional_input_packets_from_str(INPUT)), 140);
	assert_eq!(part2(), 22110);
}
