// Copyright (c) 2022 Bastiaan Marinus van de Weerd


const ROOT: &str = "root";
const HUMAN: &str = "humn";


#[derive(Clone, Copy)]
enum Operator { Add, Sub, Mul, Div }

impl Operator {
	fn operate(&self, [left, right]: [u64; 2]) -> u64 {
		use Operator::*;
		match self {
			Add => left + right,
			Sub => left - right,
			Mul => left * right,
			Div => left / right,
		}
	}

	fn div_without_rem(lhs: u64, rhs: u64) -> u64 {
		assert_eq!(lhs % rhs, 0);
		lhs / rhs
	}

	fn unoperate_left(&self, output: u64, left: u64) -> u64 {
		use Operator::*;
		match self {
			Add => output - left,
			Sub => left - output,
			Mul => Self::div_without_rem(output, left),
			Div => Self::div_without_rem(output, left),
		}
	}

	fn unoperate_right(&self, output: u64, right: u64) -> u64 {
		use Operator::*;
		match self {
			Add | Mul => self.unoperate_left(output, right),
			Sub => output + right,
			Div => output * right,
		}
	}
}

enum Job<'a> {
	Number(u64),
	Operation(Operator, [&'a str; 2])
}

type Monkeys<'a> = std::collections::HashMap<&'a str, Job<'a>>;


fn input_monkeys_from_str(s: &str) -> Monkeys {
	parsing::try_monkeys_from_str(s).unwrap()
}

fn input_monkeys() -> Monkeys<'static> {
	input_monkeys_from_str(include_str!("day21.txt"))
}


fn resolve(monkey: &str, input_monkeys: &mut Monkeys, resolve_human: bool) -> u64 {
	let target = monkey;

	let monkeys_ptr = std::ptr::addr_of!(input_monkeys);
	let get_number = |label|
		// SAFETY: Mutably borrowed by `iter_mut` below, which only lets values be mutated
		// in place without mutating the `HashMap`’s overall structure. No concurrency.
		unsafe { &**monkeys_ptr }
			.get(label)
			.and_then(|job| match job {
				Job::Number(number) if resolve_human || label != HUMAN => Some(*number),
				_ => None,
			});

	loop {
		for (&monkey, job) in input_monkeys.iter_mut() {
			match job {
				Job::Number(ref number) => if monkey == target { return *number },
				&mut Job::Operation(operator, [left, right]) => {
					let Some(left) = get_number(left) else { continue };
					let Some(right) = get_number(right) else { continue };
					let number = operator.operate([left, right]);
					*job = Job::Number(number);
					if monkey == target { return number }
				}
			}
		}
	}
}


fn part1_impl(mut input_monkeys: Monkeys) -> u64 {
	resolve(ROOT, &mut input_monkeys, true)
}

pub(crate) fn part1() -> u64 {
	part1_impl(input_monkeys())
}


fn part2_impl(mut input_monkeys: Monkeys) -> u64 {
	use either::Either;

	let path_to_human = {
		let mut stack = vec![(None, ROOT)];
		while let Some(job) = stack.last()
			.map(|e| e.0.unwrap_or(e.1))
			.and_then(|m| input_monkeys.get(m))
		{
			match (job, stack.last_mut().unwrap()) {
				(Job::Number(_), (left @ Some(_), _)) => *left = None,
				(Job::Number(_), (None, _)) => loop {
					stack.pop();
					match stack.last_mut() {
						None => break,
						Some((left @ Some(_), _)) => { *left = None; break }
						Some((None, _)) => continue
					}
				}
				(&Job::Operation(_, [left, right]), _) => {
					stack.push((Some(left), right));
					if left == HUMAN || right == HUMAN { break }
				}
			}
		}

		stack.into_iter()
			.skip(1)
			.map(|(left, right)| left.map(Either::Left)
				.unwrap_or(Either::Right(right)))
			.collect::<Vec<_>>()
	};
	assert!(!path_to_human.is_empty());

	let mut prev = ROOT;
	let mut prev_resolved = None;
	for curr in path_to_human {
		let Some(&Job::Operation(operator, [left, right]))
			= input_monkeys.get(prev) else { unreachable!() };
		prev = curr.left_or_else(|right| right);

		let other_resolved
			= resolve(if curr.is_left() { right } else { left }, &mut input_monkeys, false);
		if let Some(prev_resolved) = prev_resolved.as_mut() {
			*prev_resolved = if curr.is_left() { Operator::unoperate_right }
				else { Operator::unoperate_left }(&operator, *prev_resolved, other_resolved);
		} else {
			prev_resolved = Some(other_resolved);
		}
	}
	prev_resolved.unwrap()
}

pub(crate) fn part2() -> u64 {
	part2_impl(input_monkeys())
}


mod parsing {
	use {std::num::ParseIntError, either::Either};
	use super::{Operator, Job, Monkeys};

	macro_rules! str_offset { ( $s0:expr, $s:expr ) => {
		// SAFETY: It is assumed that `$s0` and `$s` point into the same string slice
		unsafe { $s.as_ptr().offset_from($s0.as_ptr()) as usize }
	} }

	fn try_strip_prefix<'s>(s: &'s str, prefix: &str) -> Result<&'s str, &'s str> {
		s.strip_prefix(prefix).ok_or_else(|| {
			let p = s.bytes().zip(prefix.bytes()).position(|(s, p)| s != p).unwrap();
			&s[p..]
		})
	}

	#[derive(Debug)]
	pub(super) enum OperatorError { Empty, Invalid }

	fn try_operator_from_str(s: &str) -> Result<(Operator, &str), OperatorError> {
		let operator = match s.bytes().next() {
			Some(b'+') => Operator::Add,
			Some(b'-') => Operator::Sub,
			Some(b'*') => Operator::Mul,
			Some(b'/') => Operator::Div,
			Some(_) => return Err(OperatorError::Invalid),
			None => return Err(OperatorError::Empty),
		};
		Ok((operator, &s[1..]))
	}

	#[allow(dead_code)]
	#[derive(Debug)]
	pub(super) enum LabelError {
		Len { found: usize },
		Invalid { column: usize, found: char },
	}

	fn try_label_from_str(s: &str) -> Result<(&str, &str), LabelError> {
		use LabelError::*;
		s.bytes()
			.take(4)
			.enumerate()
			.try_for_each(|(c, b)| match b {
				b if b.is_ascii_whitespace() => Err(Len { found: c }),
				b if !b.is_ascii_lowercase() => Err(Invalid { column: c + 1, found: b as char }),
				_ => Ok(())
			})?;
		Ok((&s[..4], &s[4..]))
	}

	macro_rules! recolumn_err {
		( $err:ident $(:: $err_variant:ident )? {
			$column:ident $(, $others:ident )*
		}, $offset:expr ) => { |e| match e {
			$err $(:: $err_variant )? { $column $(, $others )* } =>
				$err $(:: $err_variant )? { $column: $column + $offset $(, $others )* },
			_ => e,
		} }
	}
	macro_rules! recolumn_label_err { ( $offset:expr ) => {
		recolumn_err!(LabelError::Invalid { column, found }, $offset)
	} }

	#[derive(Debug)]
	pub(super) enum JobError {
		Format { column: usize },
		Number(ParseIntError),
		Operator(OperatorError),
		Operand(Either<LabelError, LabelError>),
	}

	fn try_job_from_str(s: &str) -> Result<(Job, &str), JobError> {
		use JobError as E;

		let s0 = s;
		macro_rules! c { ( $s:expr ) => { str_offset!(s0, $s) } }
		macro_rules! map_recolumn { ( $s:ident, $either:ident ) => { |e|
			E::Operand(Either::$either(recolumn_label_err!(c!($s))(e))) } }

		if matches!(s.bytes().next(), Some(b) if b.is_ascii_digit()) {
			let (number, s) = s.split_once('\n').unwrap_or((s, &s[s.len()..]));
			let s = if s.is_empty() { s } else { &s0[c!(s) - 1..] };
			Ok((Job::Number(number.parse().map_err(E::Number)?), s))
		} else {
			let (lhs, s) = try_label_from_str(s).map_err(map_recolumn!(s, Left))?;
			let s = s.strip_prefix(' ').ok_or(E::Format { column: c!(s) + 1 })?;
			let (operator, s) = try_operator_from_str(s).map_err(E::Operator)?;
			let s = s.strip_prefix(' ').ok_or(E::Format { column: c!(s) + 1 })?;
			let (rhs, s) = try_label_from_str(s).map_err(map_recolumn!(s, Right))?;
			Ok((Job::Operation(operator, [lhs, rhs]), s))
		}
	}

	#[allow(dead_code)]
	#[derive(Debug)]
	pub(super) enum MonkeyError {
		Format { column: usize },
		Label(LabelError),
		Job(JobError),
	}

	fn try_monkey_from_str(s: &str) -> Result<(&str, Job, &str), MonkeyError> {
		use MonkeyError as E;

		let s0 = s;
		macro_rules! c { ( $s:expr ) => { str_offset!(s0, $s) } }

		let (label, s) = try_label_from_str(s)
			.map_err(|e| E::Label(recolumn_label_err!(c!(s))(e)))?;
		let s = try_strip_prefix(s, ": ")
			.map_err(|s| E::Format { column: c!(s) + 1 })?;
		let (job, s) = try_job_from_str(s)
			.map_err(|e| E::Job(match recolumn_err!(JobError::Format { column }, c!(s))(e) {
				JobError::Operand(Either::Left(label_err)) =>
					JobError::Operand(Either::Left(recolumn_label_err!(c!(s))(label_err))),
				JobError::Operand(Either::Right(label_err)) =>
					JobError::Operand(Either::Right(recolumn_label_err!(c!(s))(label_err))),
				e => e,
			}))?;
		Ok((label, job, s))
	}

	#[allow(dead_code)]
	#[derive(Debug)]
	pub(super) struct MonkeysError { line: usize, source: MonkeyError }

	pub(super) fn try_monkeys_from_str(s: &str) -> Result<Monkeys, MonkeysError> {
		s.lines()
			.enumerate()
			.map(|(l, line)| try_monkey_from_str(line)
				.map_err(|e| MonkeysError { line: l + 1, source: e })
				.map(|(label, job, _)| (label, job)))
			.collect::<Result<Monkeys, _>>()
	}
}


#[test]
fn tests() {
	const INPUT: &str = indoc::indoc! { "
		root: pppw + sjmn
		dbpl: 5
		cczh: sllz + lgvd
		zczc: 2
		ptdq: humn - dvpt
		dvpt: 3
		lfqf: 4
		humn: 5
		ljgn: 2
		sjmn: drzm * dbpl
		sllz: 4
		pppw: cczh / lfqf
		lgvd: ljgn * ptdq
		drzm: hmdt - zczc
		hmdt: 32
	"};
	assert_eq!(part1_impl(input_monkeys_from_str(INPUT)), 152);
	assert_eq!(part1(), 93_813_115_694_560);
	assert_eq!(part2_impl(input_monkeys_from_str(INPUT)), 301);
	assert_eq!(part2(), 3_910_938_071_092);
}
