// Copyright (c) 2022 Bastiaan Marinus van de Weerd


fn input_snafus_from_str(s: &str) -> impl Iterator<Item = &str> + '_ {
	s.lines()
}


fn part1_impl<'s>(input_snafus: impl Iterator<Item = &'s str>) -> String {
	let total = input_snafus
		.map(|snafu| snafu.bytes().rev().fold((0, 1), |(num, pow), b| {
			let d = match b { b'=' => -2, b'-' => -1, b'0'|b'1'|b'2' => (b - b'0') as isize,
				_ => panic!("Invalid SNAFU digit {}", b as char) };
			(num + d * pow, pow * 5)
		}).0)
		.sum::<isize>();

	if total == 0 { return "0".to_owned() }

	assert!(total > 0);

	let mut scratch = itertools::unfold(total, |rem| (*rem != 0).then(|| {
		*rem += 2;
		let b = match *rem % 5 { 0 => b'=', 1 => b'-', d => b'0' + d as u8 - 2 };
		*rem /= 5;
		b
	})).collect::<Vec<_>>();
	scratch.reverse();

	// SAFETY: `scratch` only contains SNAFU digits
	unsafe { String::from_utf8_unchecked(scratch) }
}

pub(crate) fn part1() -> String {
	part1_impl(input_snafus_from_str(include_str!("day25.txt")))
}


pub(crate) fn part2() -> &'static str {
	"Merry Christmas!"
}


#[test]
fn tests() {
	const INPUT: &str = indoc::indoc! { "
		1=-0-2
		12111
		2=0=
		21
		2=01
		111
		20012
		112
		1=-1=
		1-12
		12
		1=
		122
	" };
	assert_eq!(part1_impl(input_snafus_from_str(INPUT)), "2=-1=0");
	assert_eq!(part1(), "2=12-100--1012-0=012");
}
