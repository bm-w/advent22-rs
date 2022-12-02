// Copyright (c) 2022 Bastiaan Marinus van de Weerd


#[derive(Clone, Copy)]
enum Play { Rock = 1, Paper = 2, Scissors = 3 }

#[derive(Clone, Copy)]
enum End { Lose = 0, Draw = 3, Win = 6 }

struct Round<SecondColumn>(Play, SecondColumn);


fn input_rounds_from_str<'s, SecondColumn>(s: &'s str) -> impl Iterator<Item = Round<SecondColumn>> + 's
where SecondColumn: std::str::FromStr + 's, <SecondColumn as std::str::FromStr>::Err: std::fmt::Debug {
	parsing::rounds_from_str(s).map(|r| r.unwrap())
}

fn input_rounds<SecondColumn>() -> impl Iterator<Item = Round<SecondColumn>> + 'static
where SecondColumn: std::str::FromStr + 'static, <SecondColumn as std::str::FromStr>::Err: std::fmt::Debug {
	input_rounds_from_str(include_str!("day02.txt"))
}


fn part1_impl(input_rounds: impl Iterator<Item = Round<Play>>) -> u64 {
	input_rounds.map(|round| {
		use {Play::*, End::*, Round as R};
		round.1 as u64 + match round {
			R(Rock, Scissors) | R(Paper, Rock) | R(Scissors, Paper) => Lose as u64,
			R(Rock, Rock) | R(Paper, Paper) | R(Scissors, Scissors) => Draw as u64,
			R(Rock, Paper) | R(Paper, Scissors) | R(Scissors, Rock) => Win as u64,
		}
	}).sum()
}

pub(crate) fn part1() -> u64 {
	part1_impl(input_rounds())
}


fn part2_impl(input_rounds: impl Iterator<Item = Round<End>>) -> u64 {
	input_rounds.map(|round| {
		use {Play::*, End::*, Round as R};
		round.1 as u64 + match round {
			R(Paper, Lose) | R(Rock, Draw) | R(Scissors, Win) => Rock as u64,
			R(Scissors, Lose) | R(Paper, Draw) | R(Rock, Win) => Paper as u64,
			R(Rock, Lose) | R(Scissors, Draw) | R(Paper, Win) => Scissors as u64,
		}
	}).sum()
}

pub(crate) fn part2() -> u64 {
	part2_impl(input_rounds())
}


mod parsing {
	use {std::str::FromStr, itertools::{Either, Itertools as _}};
	use super::{Play, End, Round};

	// TODO(bm-w): Use `const` custom enum once Rust allows it
	struct PlayerPlay<const YOU: bool>(Play);

	impl<const YOU: bool> TryFrom<char> for PlayerPlay<YOU> {
		type Error = Option<char>;
		fn try_from(value: char) -> Result<Self, Self::Error> {
			use Play::*;
			match (YOU, value) {
				(false, 'A') => Ok(PlayerPlay(Rock)),
				(false, 'B') => Ok(PlayerPlay(Paper)),
				(false, 'C') => Ok(PlayerPlay(Scissors)),
				(false, 'X' | 'Y' | 'Z') => Err(None),
				(true, 'X') => Ok(PlayerPlay(Rock)),
				(true, 'Y') => Ok(PlayerPlay(Paper)),
				(true, 'Z') => Ok(PlayerPlay(Scissors)),
				(true, 'A' | 'B' | 'C') => Err(None),
				(_, invalid) => Err(Some(invalid)),
			}
		}
	}

	#[allow(dead_code)]
	#[derive(Debug)]
	pub(super) enum PlayError {
		Format { len: usize },
		WrongPlayer,
		Invalid { found: char },
	}

	macro_rules! exactly_one_err { ( $chars:expr, $err:ident ) => { {
		let (low, upp) = $chars.size_hint();
		Err($err { len: upp.unwrap_or(low) })
	} }}

	impl<const YOU: bool> FromStr for PlayerPlay<YOU> {
		type Err = PlayError;
		fn from_str(s: &str) -> Result<Self, Self::Err> {
			use PlayError::*;
			match s.chars().exactly_one() {
				Ok(chr) => PlayerPlay::<YOU>::try_from(chr).map_err(|e|
					e.map(|found| Invalid { found }).unwrap_or(WrongPlayer)),
				Err(chars) => exactly_one_err!(chars, Format),
			}
		}
	}

	impl FromStr for Play {
		type Err = PlayError;
		fn from_str(s: &str) -> Result<Self, Self::Err> {
			Ok(PlayerPlay::<true>::from_str(s)?.0)
		}
	}

	impl TryFrom<char> for End {
		type Error = ();
		fn try_from(value: char) -> Result<Self, Self::Error> {
			use End::*;
			match value {
				'X' => Ok(Lose),
				'Y' => Ok(Draw),
				'Z' => Ok(Win),
				_ => Err(())
			}
		}
	}

	#[allow(dead_code)]
	#[derive(Debug)]
	pub(super) enum EndError {
		Format { len: usize },
		Invalid { found: char },
	}

	impl FromStr for End {
		type Err = EndError;
		fn from_str(s: &str) -> Result<Self, Self::Err> {
			use EndError::*;
			match s.chars().exactly_one() {
				Ok(chr) => End::try_from(chr).map_err(|_| Invalid { found: chr }),
				Err(chars) => exactly_one_err!(chars, Format),
			}
		}
	}

	#[allow(dead_code)]
	#[derive(Debug)]
	pub(super) enum RoundError<SecondColumn> {
		Format,
		Play(PlayError),
		SecondColumn(SecondColumn),
	}

	impl<SecondColumn: FromStr> FromStr for Round<SecondColumn> {
		type Err = RoundError<<SecondColumn as FromStr>::Err>;
		fn from_str(s: &str) -> Result<Self, Self::Err> {
			let (other, second_column) = s.split_once(' ')
				.ok_or(RoundError::Format)?;
			Ok(Round(
				other.parse::<PlayerPlay<false>>()
					.map_err(RoundError::Play)?.0,
				second_column.parse::<SecondColumn>()
					.map_err(RoundError::SecondColumn)?,
			))
		}
	}

	#[allow(dead_code)]
	#[derive(Debug)]
	pub(super) enum RoundsError<SecondColumn> {
		Empty,
		Round { line: usize, source: RoundError<SecondColumn> },
	}

	pub(super) fn rounds_from_str<'s, SecondColumn: FromStr + 's>(s: &'s str)
	-> impl Iterator<Item = Result<Round<SecondColumn>, RoundsError<<SecondColumn as FromStr>::Err>>> + 's {
		if s.is_empty() { return Either::Left(std::iter::once(Err(RoundsError::Empty))) }
		Either::Right(s.lines()
			.enumerate()
			.map(|(l, line)| line.parse()
				.map_err(|e| RoundsError::Round { line: l + 1, source: e })))
	}
}


#[test]
fn tests() {
	const INPUT: &str = indoc::indoc! { "
		A Y
		B X
		C Z
	" };
	assert_eq!(part1_impl(input_rounds_from_str(INPUT)), 15);
	assert_eq!(part1(), 11475);
	assert_eq!(part2_impl(input_rounds_from_str(INPUT)), 12);
	assert_eq!(part2(), 16862);
}
