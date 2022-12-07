// Copyright (c) 2022 Bastiaan Marinus van de Weerd


fn input_datastream_buffer() -> &'static str {
	include_str!("day06.txt")
}


fn part1and2_impl<const N: usize>(input_datastream_buffer: &str) -> usize {
	input_datastream_buffer.as_bytes()
		.windows(N)
		.position(|w| w.iter()
			.scan(0_usize, |acc, b| {
				let prev_acc = *acc;
				*acc |= 1 << (*b - b'a');
				Some(*acc != prev_acc)
			})
			.all(std::convert::identity))
		.unwrap() + N
}

pub(crate) fn part1() -> usize {
	part1and2_impl::<4>(input_datastream_buffer())
}

pub(crate) fn part2() -> usize {
	part1and2_impl::<14>(input_datastream_buffer())
}


#[cfg(test)]
mod tests {
	use test_case::test_case;
	use super::*;

	#[test_case("mjqjpqmgbljsphdztnvjfqwrcgsmlb", 7; "a")]
	#[test_case("bvwbjplbgvbhsrlpgdmjqwftvncz", 5; "b")]
	#[test_case("nppdvjthqldpwncqszvftbrmjlhg", 6; "c")]
	#[test_case("nznrnfrfntjfmvfwmzdfjlvtqnbhcprsg", 10; "d")]
	#[test_case("zcfzfwzzqfrljwzlrfnpqdbhtmscgvjw", 11; "e")]
	fn part1_impl(input_buffer_stream: &str, offset: usize) {
		assert_eq!(part1and2_impl::<4>(input_buffer_stream), offset);
	}

	#[test]
	fn part1() {
		assert_eq!(super::part1(), 1953);
	}

	#[test_case("mjqjpqmgbljsphdztnvjfqwrcgsmlb", 19; "a")]
	#[test_case("bvwbjplbgvbhsrlpgdmjqwftvncz", 23; "b")]
	#[test_case("nppdvjthqldpwncqszvftbrmjlhg", 23; "c")]
	#[test_case("nznrnfrfntjfmvfwmzdfjlvtqnbhcprsg", 29; "d")]
	#[test_case("zcfzfwzzqfrljwzlrfnpqdbhtmscgvjw", 26; "e")]
	fn part2_impl(input_buffer_stream: &str, offset: usize) {
		assert_eq!(part1and2_impl::<14>(input_buffer_stream), offset);
	}

	#[test]
	fn part2() {
		assert_eq!(super::part2(), 2301);
	}
}
