// Copyright (c) 2022 Bastiaan Marinus van de Weerd


#[cfg_attr(test, derive(Debug))]
#[derive(Clone)]
struct Sensor {
	pos: [isize; 2],
	beacon: [isize; 2],
}

use std::ops::Range;

impl Sensor {
	fn radius(&self) -> usize {
		self.beacon[0].abs_diff(self.pos[0]) + self.beacon[1].abs_diff(self.pos[1])
	}

	fn row_range(&self, row: isize, range: Range<isize>)
	-> Option<Range<isize>> {
		let sensor_radius = self.radius() as isize;
		let row_distance = self.pos[1].abs_diff(row) as isize;
		let delta = sensor_radius - row_distance;
		if delta < 0 { return None }
		let intersection_start = self.pos[0] - delta;
		if intersection_start > range.end { return None }
		let row_range = intersection_start..(intersection_start + 2 * delta + 1);
		if row_range.end < range.start { return None }
		Some(row_range.start.max(range.start)..row_range.end.min(range.end))
	}
}

trait Sensors: Iterator<Item = Sensor> {

	fn row_coverage(self, row: isize, range: Option<Range<isize>>, beacons: bool) -> usize
	where Self: Sized {
		use {std::collections::HashSet, itertools::Itertools as _};
		let range = range.unwrap_or(isize::MIN..isize::MAX);

		let mut beacons = (!beacons).then(HashSet::new);
		let count = self
			.filter_map(|sensor| {
				let Some(range) = sensor.row_range(row, range.clone()) else { return None };
				if let Some(beacons) = beacons.as_mut() {
					if sensor.beacon[1] == row && range.contains(&sensor.beacon[0]) {
						beacons.insert(sensor.beacon[0]);
					}
				}
				Some(range)
			})
			.sorted_by_key(|r| r.start)
			.fold((0, range.start), |(count, x), range| {
				if range.end <= x { return (count, x) }
				let range = if range.start < x { x..range.end } else { range };
				(count + range.len(), range.end)
			}).0;

		count - beacons.map(|b| b.len()).unwrap_or(0)
	}
}

impl<T> Sensors for T where T: Iterator<Item = Sensor> {}


fn input_sensors_from_str(s: &str) -> impl Iterator<Item = Sensor> + '_ {
	parsing::sensors_from_str(s).map(|r| r.unwrap())
}

fn input_sensors() -> impl Iterator<Item = Sensor> + 'static {
	input_sensors_from_str(include_str!("day15.txt"))
}


fn part1_impl<const ROW: isize>(input_sensors: impl Iterator<Item = Sensor>) -> usize {
	input_sensors.row_coverage(ROW, None, false)
}

pub(crate) fn part1() -> usize {
	part1_impl::<2_000_000>(input_sensors())
}


fn part2_naive<const MAX: usize>(input_sensors: impl Iterator<Item = Sensor>) -> usize {
	use {
		itertools::Itertools as _,
		rayon::prelude::{IntoParallelIterator as _, ParallelIterator as _}
	};

	let input_sensors = input_sensors.collect::<Vec<_>>();

	let Some(y) = (0..MAX as isize)
		.into_par_iter()
		.find_any(|&y| input_sensors.clone()
			.into_iter()
			.row_coverage(y, Some(0..MAX as isize), true) < MAX)
		else { panic!("Beacon row not found") };

	let Some(x) = input_sensors.into_iter()
		.filter_map(move |s| s.row_range(y, 0..MAX  as isize))
		.sorted_by_key(|r| r.start)
		.scan(Option::<Range<isize>>::None, |r0, r1| {
			if let Some(r0) = r0.as_mut() {
				if r1.start > r0.end { return Some(Some(r0.end)) }
				if r1.end >= r0.end { *r0 = r1 }
			} else {
				*r0 = Some(r1);
			}
			Some(None)
		})
		.flatten()
		.next() else { panic!("Beacon not found") };

	x as usize * 4_000_000 + y as usize
}

pub(crate) fn part2() -> usize {
	part2_naive::<4_000_000>(input_sensors())
}


mod parsing {
	use std::{num::ParseIntError, str::FromStr};
	use super::Sensor;

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
	pub(super) enum PosError {
		Format { column: usize },
		X(ParseIntError),
		Y(ParseIntError),
	}

	fn try_pos_from_str(s: &str) -> Result<([isize; 2], &str), PosError> {
		let s0 = s; 
		macro_rules! c { ( $s:expr ) => { str_offset!(s0, $s) } }

		let s = try_strip_prefix(s, "x=")
			.map_err(|s| PosError::Format { column: c!(s) + 1 })?;
		let (x, s) = s.split_once(',')
			.ok_or(PosError::Format { column: c!(s) + 1 })?;
		let x = x.parse().map_err(PosError::X)?;
		let s = try_strip_prefix(s, " y=")
			.map_err(|s| PosError::Format { column: c!(s) + 1 })?;
		let (y, s) = s.split_once(|c: char| c != '-' && !c.is_ascii_digit())
			.unwrap_or((s, &s[s.len()..]));
		let y = y.parse().map_err(PosError::Y)?;
		Ok(([x, y], if s.is_empty() { s } else { &s0[c!(s) - 1..] }))
	}

	#[allow(dead_code)]
	#[derive(Debug)]
	pub(super) enum SensorError {
		Format { column: usize },
		Pos(PosError),
		Beacon(PosError),
	}

	fn try_sensor_from_str(s: &str) -> Result<(Sensor, &str), SensorError> {
		let s0 = s; 
		macro_rules! c { ( $s:expr ) => { str_offset!(s0, $s) } }

		let offset_pos_err = |pos_err, c| match pos_err {
			PosError::Format { column } => PosError::Format { column: c + column },
			_ => pos_err,
		};

		let s = try_strip_prefix(s, "Sensor at ")
			.map_err(|s| SensorError::Format { column: c!(s) + 1 })?;
		let (pos, s) = try_pos_from_str(s)
			.map_err(|e| SensorError::Pos(offset_pos_err(e, c!(s))))?;
		let s = try_strip_prefix(s, ": closest beacon is at ")
			.map_err(|s| SensorError::Format { column: c!(s) + 1 })?;
		let (beacon, s) = try_pos_from_str(s)
			.map_err(|e| SensorError::Beacon(offset_pos_err(e, c!(s))))?;
		Ok((Sensor { pos, beacon }, s))
	}

	impl FromStr for Sensor {
		type Err = SensorError;
		fn from_str(s: &str) -> Result<Self, Self::Err> {
			let (sensor, rest) = try_sensor_from_str(s)?;
			if !rest.is_empty() { return Err(
				SensorError::Format { column: str_offset!(s, rest) + 1 }) }
			Ok(sensor)
		}
	}

	#[allow(dead_code)]
	#[derive(Debug)]
	pub(super) struct SensorsError { line: usize, source: SensorError }

	pub(super) fn sensors_from_str(s: &str)
	-> impl Iterator<Item = Result<Sensor, SensorsError>> + '_ {
		s.lines()
			.enumerate()
			.map(|(l, line)| line.parse()
				.map_err(|e| SensorsError { line: l + 1, source: e }))
	}
}


#[test]
fn tests() {
	const INPUT: &str = indoc::indoc! { "
		Sensor at x=2, y=18: closest beacon is at x=-2, y=15
		Sensor at x=9, y=16: closest beacon is at x=10, y=16
		Sensor at x=13, y=2: closest beacon is at x=15, y=3
		Sensor at x=12, y=14: closest beacon is at x=10, y=16
		Sensor at x=10, y=20: closest beacon is at x=10, y=16
		Sensor at x=14, y=17: closest beacon is at x=10, y=16
		Sensor at x=8, y=7: closest beacon is at x=2, y=10
		Sensor at x=2, y=0: closest beacon is at x=2, y=10
		Sensor at x=0, y=11: closest beacon is at x=2, y=10
		Sensor at x=20, y=14: closest beacon is at x=25, y=17
		Sensor at x=17, y=20: closest beacon is at x=21, y=22
		Sensor at x=16, y=7: closest beacon is at x=15, y=3
		Sensor at x=14, y=3: closest beacon is at x=15, y=3
		Sensor at x=20, y=1: closest beacon is at x=15, y=3
	" };
	assert_eq!(part1_impl::<10>(input_sensors_from_str(INPUT)), 26);
	assert_eq!(part1(), 4737567);
	assert_eq!(part2_naive::<20>(input_sensors_from_str(INPUT)), 56000011);
	assert_eq!(part2(), 13267474686239);
}
