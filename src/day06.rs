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
	use super::*;

	#[test]
	fn part1() {
		const INPUTS_ANSWERS: [(&str, usize); 5] = [
			("mjqjpqmgbljsphdztnvjfqwrcgsmlb", 7),
			("bvwbjplbgvbhsrlpgdmjqwftvncz", 5),
			("nppdvjthqldpwncqszvftbrmjlhg", 6),
			("nznrnfrfntjfmvfwmzdfjlvtqnbhcprsg", 10),
			("zcfzfwzzqfrljwzlrfnpqdbhtmscgvjw", 11),
		];
		for (input, answer) in INPUTS_ANSWERS {
			assert_eq!(part1and2_impl::<4>(input), answer);
		}
		assert_eq!(super::part1(), 1953);
	}

	#[test]
	fn part2() {
		const INPUTS_ANSWERS: [(&str, usize); 5] = [
			("mjqjpqmgbljsphdztnvjfqwrcgsmlb", 19),
			("bvwbjplbgvbhsrlpgdmjqwftvncz", 23),
			("nppdvjthqldpwncqszvftbrmjlhg", 23),
			("nznrnfrfntjfmvfwmzdfjlvtqnbhcprsg", 29),
			("zcfzfwzzqfrljwzlrfnpqdbhtmscgvjw", 26),
		];
		for (input, answer) in INPUTS_ANSWERS {
			assert_eq!(part1and2_impl::<14>(input), answer);
		}
		assert_eq!(super::part2(), 2301);
	}
}
