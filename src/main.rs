// Copyright (c) 2022 Bastiaan Marinus van de Weerd

mod util;
util::mod_days![01, 02];

fn main() {
	println!("Day X; part 1: {}, part 2: {}", day01::part1(), day01::part2());
	println!("Day X; part 1: {}, part 2: {}", day02::part1(), day02::part2());
}
