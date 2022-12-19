// Copyright (c) 2022 Bastiaan Marinus van de Weerd


#[derive(PartialEq, Eq, Hash)]
struct Label(u16);

#[cfg_attr(test, derive(Debug))]
struct Valve {
	flow_rate: usize,
	tunnels: Vec<Label>,
}

type Valves = std::collections::HashMap<Label, Valve>;


fn input_valves_from_str(s: &str) -> Valves {
	parsing::valves_from_str(s).map(|r| r.unwrap()).collect()
}

fn input_valves() -> Valves {
	input_valves_from_str(include_str!("day16.txt"))
}


fn part1and2_impl<const N: usize>(input_valves: Valves) -> usize {
	use {
		std::{
			cmp::{PartialOrd, Ord, Ordering},
			collections::{BinaryHeap, HashMap, hash_map::Entry},
		},
		itertools::Itertools as _,
	};

	fn elapsed_limit<const N: usize>() -> usize { 30 - ((N - 1) * 4) }

	#[cfg_attr(test, derive(Debug))]
	#[derive(PartialEq, Eq)]
	struct State<const N: usize> {
		elapsed: usize,
		relabeled_valves: [u64; N],
		opened: u64,
		pressure_released: usize,
		flow_rate: usize,
	}

	impl<const N: usize> State<N> {
		fn estimate(&self) -> usize {
			self.pressure_released
				+ self.flow_rate * (elapsed_limit::<N>() - self.elapsed)
		}
	}

	impl<const N: usize> State<N> {
		fn is_valve_open(&self, index: usize) -> bool {
			self.opened & self.relabeled_valves[index] != 0
		}
	}

	impl<const N: usize> PartialOrd for State<N> {
		fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
			Some(self.cmp(other))
		}
	}

	impl<const N: usize> Ord for State<N> {
		fn cmp(&self, other: &Self) -> Ordering {
			Ordering::Equal
				.then_with(|| self.elapsed.cmp(&other.elapsed).reverse())
				.then_with(|| self.estimate().cmp(&other.estimate()))
				.then_with(|| self.flow_rate.cmp(&other.flow_rate))
				.then_with(|| self.pressure_released.cmp(&other.pressure_released))
				.then_with(|| self.opened.count_ones().cmp(&other.opened.count_ones()).reverse())
				.then_with(|| self.relabeled_valves.cmp(&other.relabeled_valves))
		}
	}

	let relabels = input_valves.keys()
		.sorted_by_key(|l| l.0)
		.enumerate()
		.map(|(i, label)| (label, 1u64 << i))
		.collect::<HashMap<_, _>>();
	let labels = relabels.iter()
		.sorted_by_key(|(_, relabel)| **relabel)
		.map(|(label, _)| *label)
		.collect::<Vec<_>>();
	let opened_all_nonzero = input_valves.iter()
		.filter_map(|(l, v)| (v.flow_rate > 0).then(|| relabels[&l]))
		.fold(0, |acc, rl| acc | rl);

	let mut heap = BinaryHeap::new();
	heap.push(State {
		elapsed: 0,
		relabeled_valves: [relabels[&Label(0)]; N],
		opened: 0,
		pressure_released: 0,
		flow_rate: 0,
	});

	let mut estimates = HashMap::new();
	let mut best_estimate = 0;

	while let Some(state) = heap.pop() {

		match estimates.entry((state.relabeled_valves, state.opened)) {
			Entry::Vacant(entry) => {
				entry.insert(state.estimate());
			}
			Entry::Occupied(mut entry) => {
				let state_estimate = state.estimate();
				if *entry.get() >= state_estimate {
					#[cfg(LOGGING)]
					println!("- t={} @ {} (open: {}); flow: {}, rel.: {}; est.: {} -- was here at est.: {}",
						state.elapsed,
						state.relabeled_valves.iter()
							.map(|r| labels[r.trailing_zeros() as usize].to_string())
							.join(","),
						if state.opened == 0 {
							"-".to_owned()
						} else {
							labels.iter()
								.enumerate()
								.filter_map(|(i, l)| (state.opened & 1 << i != 0)
									.then(|| l.to_string()))
								.join(",")
						},
						state.flow_rate,
						state.pressure_released,
						state.estimate(),
						*entry.get());
					continue
				}
				entry.insert(state_estimate);
			}
		};

		#[cfg(LOGGING)]
		println!("t={} @ {} (open: {}); flow: {}, rel.: {}; est.: {}",
			state.elapsed,
			state.relabeled_valves.iter()
				.map(|r| labels[r.trailing_zeros() as usize].to_string())
				.join(","),
			if state.opened == 0 {
				"-".to_owned()
			} else {
				labels.iter()
					.enumerate()
					.filter_map(|(i, l)| (state.opened & 1 << i != 0)
						.then(|| l.to_string()))
					.join(",")
			},
			state.flow_rate,
			state.pressure_released,
			state.estimate());

		if state.opened == opened_all_nonzero || state.elapsed == elapsed_limit::<N>() {
			#[cfg(LOGGING)]
			println!("  └-> FINAL!");
			best_estimate = best_estimate.max(state.estimate());
			continue
		}

		let elapsed = state.elapsed + 1;
		let pressure_released = state.pressure_released + state.flow_rate;

		#[derive(Clone, Copy)]
		enum Action {
			Move { to: u64 },
			OpenValve { flow_rate: usize },
		}

		heap.extend(state.relabeled_valves.iter()
			.enumerate()
			.map(|(i, relabel)| {
				let label = labels[relabel.trailing_zeros() as usize];
				let valve = &input_valves[label];

				let open = (!state.is_valve_open(i) && valve.flow_rate > 0)
					.then_some(Action::OpenValve { flow_rate: valve.flow_rate });
				let moves = valve.tunnels.iter()
					.map(|valve| Action::Move { to: relabels[&valve] });

				open.into_iter().chain(moves)
			})
			.multi_cartesian_product()
			.filter(|actions| !actions.iter()
				.enumerate()
				.tuple_combinations()
				.any(|((i0, a0), (i1, a1))| matches!((a0, a1),
					(Action::OpenValve { .. }, Action::OpenValve { .. })
						if state.relabeled_valves[i0] == state.relabeled_valves[i1])))
			.map(|actions| {
				let mut relabeled_valves = state.relabeled_valves;
				let mut opened = state.opened;
				let mut flow_rate = state.flow_rate;
				for (valve, action) in relabeled_valves.iter_mut().zip(&actions) {
					match action {
						Action::Move { to } =>
							*valve = *to,
						Action::OpenValve { flow_rate: add_flow_rate } => {
							opened |= *valve;
							flow_rate += add_flow_rate
						}
					}
				}
				State { elapsed, relabeled_valves, opened, pressure_released, flow_rate }
			}));
	}

	best_estimate
}

pub(crate) fn part1() -> usize {
	part1and2_impl::<1>(input_valves())
}

pub(crate) fn part2() -> usize {
	part1and2_impl::<2>(input_valves())
}


mod parsing {
	use std::num::ParseIntError;
	use super::{Label, Valve};

	#[allow(dead_code)]
	#[derive(Debug)]
	pub(super) struct LabelError { column: usize, found: Option<u8> }

	fn try_label_from_str(s: &str) -> Result<(Label, &str), LabelError> {
		let mut bytes = s.bytes();
		match (bytes.next(), bytes.next()) {
			(None, _) => Err(LabelError { column: 1, found: None }),
			(Some(b), _) if !b.is_ascii_uppercase() =>
				Err(LabelError { column: 1, found: Some(b) }),
			(_, None) => Err(LabelError { column: 2, found: None }),
			(_, Some(b)) if !b.is_ascii_uppercase() =>
				Err(LabelError { column: 2, found: Some(b) }),
			(Some(b0), Some(b1)) => Ok((
				Label((((b0 - b'A') as u16) << 8) + (b1 - b'A') as u16),
				&s[2..],
			))
		}
	}

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

	#[allow(dead_code)]
	#[derive(Debug)]
	pub(super) enum ValveError {
		Format { column: usize },
		Label(LabelError),
		FlowRate(ParseIntError),
		Tunnel { offset: usize, source: LabelError }
	}

	fn try_valve_from_str(s: &str) -> Result<(Label, Valve, &str), ValveError> {
		use ValveError as E;
		let s0 = s;
		macro_rules! c { ( $s:expr ) => { str_offset!(s0, $s) } }

		let s = try_strip_prefix(s, "Valve ")
			.map_err(|s| E::Format { column: c!(s) + 1 })?;
		let (label, s) = try_label_from_str(s).map_err(|e|
			E::Label(LabelError { column: c!(s) + e.column, ..e }))?;
		let s = try_strip_prefix(s, " has flow rate=")
			.map_err(|s| E::Format { column: c!(s) + 1 })?;
		let (flow_rate, s) = s.split_once(';')
			.ok_or(E::Format { column: c!(s) + 1 })?;
		let flow_rate = flow_rate.parse().map_err(E::FlowRate)?;
		let s = try_strip_prefix(s, " tunnel")
			.map_err(|s| E::Format { column: c!(s) + 1 })?;
		let (tunnels, s) = if s.starts_with('s') {
			let mut s = try_strip_prefix(s, "s lead to valves ")
				.map_err(|s| E::Format { column: c!(s) + 1 })?;
			let mut tunnels = vec![];
			for offset in 0.. {
				let (tunnel, rest) = try_label_from_str(s)
					.map_err(|e| E::Tunnel { offset, source: e })?;
				tunnels.push(tunnel);
				s = rest;
				if s.is_empty() || s.starts_with('\n') { break }
				s = try_strip_prefix(s, ", ")
					.map_err(|s| E::Format { column: c!(s) + 1 })?;
			}
			(tunnels, s)
		} else {
			let s = try_strip_prefix(s, " leads to valve ")
				.map_err(|s| E::Format { column: c!(s) + 1 })?;
			let (tunnel, s) = try_label_from_str(s)
				.map_err(|e| E::Tunnel { offset: 0, source: e })?;
			(vec![tunnel], s)
		};
		Ok((label, Valve { flow_rate, tunnels }, s))
	}

	#[allow(dead_code)]
	#[derive(Debug)]
	pub(super) struct ValvesError { line: usize, source: ValveError }

	pub(super) fn valves_from_str(s: &str)
	-> impl Iterator<Item = Result<(Label, Valve), ValvesError>> + '_ {
		s.lines()
			.enumerate()
			.map(|(l, line)| try_valve_from_str(line)
				.map_err(|e| ValvesError { line: l + 1, source: e })
				.map(|(label, valve, _)| (label, valve)))
	}
}

#[cfg(test)]
impl std::fmt::Display for Label {
	fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
		use std::fmt::Write as _;
		f.write_char((b'A' + ((self.0 & 0xff00) >> 8) as u8) as char)?;
		f.write_char((b'A' + (self.0 & 0x00ff) as u8) as char)?;
		Ok(())
	}
}

#[cfg(test)]
impl std::fmt::Debug for Label {
	fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
		write!(f, "\"{self}\"")
	}
}


#[test]
fn tests() {
	const INPUT: &str = indoc::indoc! { "
		Valve AA has flow rate=0; tunnels lead to valves DD, II, BB
		Valve BB has flow rate=13; tunnels lead to valves CC, AA
		Valve CC has flow rate=2; tunnels lead to valves DD, BB
		Valve DD has flow rate=20; tunnels lead to valves CC, AA, EE
		Valve EE has flow rate=3; tunnels lead to valves FF, DD
		Valve FF has flow rate=0; tunnels lead to valves EE, GG
		Valve GG has flow rate=0; tunnels lead to valves FF, HH
		Valve HH has flow rate=22; tunnel leads to valve GG
		Valve II has flow rate=0; tunnels lead to valves AA, JJ
		Valve JJ has flow rate=21; tunnel leads to valve II
	" };
	assert_eq!(part1and2_impl::<1>(input_valves_from_str(INPUT)), 1651);
	assert_eq!(part1(), 1923);
	assert_eq!(part1and2_impl::<2>(input_valves_from_str(INPUT)), 1707);
	assert_eq!(part2(), 2594);
}
