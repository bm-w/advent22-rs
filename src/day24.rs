// Copyright (c) 2022 Bastiaan Marinus van de Weerd


#[cfg_attr(test, derive(Debug))]
enum Dir { Backward, Forward }

#[cfg_attr(test, derive(Debug))]
struct Blizzard {
	/// Initial distance from corresponding edge (wall).
	start: usize,
	/// Northward / southward for blizzards corresponding to the north edge (wall),
	/// eastward / westward for those corresponding to the west edge (wall).
	dir: Dir,
}

#[cfg_attr(test, derive(Debug))]
struct Valley {
	/// Also implies valley size (East->West and North->South, excluding walls).
	blizzards: [Vec<Vec<Blizzard>>; 2],
}


pub(crate) fn part1() -> &'static str {
	"WIP"
}


pub(crate) fn part2() -> &'static str {
	"WIP"
}


mod parsing {
	use std::str::FromStr;
	use super::{Dir, Blizzard, Valley};

	fn try_strip_prefix<'s>(s: &'s str, prefix: &str) -> Result<&'s str, &'s str> {
		s.strip_prefix(prefix).ok_or_else(|| {
			let p = s.bytes().zip(prefix.bytes()).position(|(s, p)| s != p);
			&s[p.unwrap_or(s.len())..]
		})
	}

	macro_rules! str_offset { ( $s0:expr, $s:expr ) => {
		// SAFETY: It is assumed that `$s0` and `$s` point into the same string slice
		unsafe { $s.as_ptr().offset_from($s0.as_ptr()) as usize }
	} }

	#[allow(dead_code)]
	#[derive(Debug)]
	pub(super) enum ValleyError {
		LineLen { line: usize, len: Option<usize>, found: usize },
		InvalidByte { line: usize, column: usize, found: u8 },
		EndOfString,
	}

	impl FromStr for Valley {
		type Err = ValleyError;
		fn from_str(s: &str) -> Result<Self, Self::Err> {
			use ValleyError as E;

			let mut blizzards = (Option::<Vec<Vec<Blizzard>>>::None, vec![]);
			macro_rules! len { () => { blizzards.0.as_ref().map(|bb| bb.len()) } }

			let (mut c, mut l, mut cx0, mut south_edge) = (0, 0, 0, false);

			macro_rules! inv_byte_err { ( $c:expr, $found:expr ) => {
				E::InvalidByte { line: l + 1, column: $c + 1, found: $found }
			} }

			while c < s.len() {
				if Some(c) == len!() { return Err(
					E::LineLen { line: l + 1, len: len!(), found: c + 1 }) }
				match blizzards.0.as_mut() {
					None => {
						_ = try_strip_prefix(s, "#.#").map_err(|e| if e.is_empty() {
							E::LineLen { line: 1, len: None, found: str_offset!(s, e) }
						} else {
							inv_byte_err!(s.len() - e.len(), e.as_bytes()[0])
						})?;

						let len = s.bytes().position(|b| b == b'\n').ok_or(E::EndOfString)?;
						blizzards.0 = Some(Vec::from_iter(
							std::iter::from_fn(|| Some(vec![])).take(len - 2)));
						l = 1;
						c = len + 1;
						cx0 = c;
					}
					Some(x_blizzards) => {
						if c >= s.len() { return Err(E::EndOfString); }
						let (cx, len) = (c - cx0, x_blizzards.len() + 2);

						macro_rules! ret_line_len_err { () => {
							return Err(E::LineLen { line: l + 1, len: Some(len), found: cx + 1 })
						} }

						if !south_edge && blizzards.1.len() < l { blizzards.1.push(vec![]) }

						match s.as_bytes()[c] {
							b'\n' => {
								if cx + 1 < len { ret_line_len_err!() }
								l += 1;
								cx0 = c + 1;
							}
							_ if cx == len => ret_line_len_err!(),
							b'#' if cx == 0 || cx == len - 1 => (),
							b'#' if cx == 1 => { south_edge = true },
							b'#' if south_edge && cx < len - 2 => (),
							b'.' if cx > 0 && cx < len - 1 => (),
							b @ (b'^'|b'v') => {
								let dir = if b == b'^' { Dir::Backward } else { Dir::Forward };
								x_blizzards[cx - 1].push(Blizzard { start: l - 1, dir })
							}
							b @ (b'<'|b'>') => {
								let dir = if b == b'<' { Dir::Backward } else { Dir::Forward };
								blizzards.1.last_mut().unwrap().push(
									Blizzard { start: cx - 1, dir })
							}
							found => return Err(inv_byte_err!(cx, found))
						}

						c += 1;
					}
				}
			}

			let Some(blizzards_x) = blizzards.0 else { return Err(E::EndOfString) };
			if !south_edge || c > cx0 && c - cx0 < blizzards_x.len() + 2 {
				return Err(E::EndOfString) };

			Ok(Valley { blizzards: [blizzards_x, blizzards.1] })
		}
	}
}


#[test]
fn tests() {
	const INPUTS: [&str; 2] = [
		indoc::indoc! { "
			#.#####
			#.....#
			#>....#
			#.....#
			#...v.#
			#.....#
			#####.#
		" },
		indoc::indoc! { "
			#.######
			#>>.<^<#
			#.<..<<#
			#>v.><>#
			#<^v^^>#
			######.#
		" },
	];
	_ = dbg!(INPUTS[0].parse::<Valley>());
	_ = dbg!(INPUTS[1].parse::<Valley>());
	_ = dbg!(include_str!("day24.txt").parse::<Valley>());
}
