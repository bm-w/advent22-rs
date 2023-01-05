// Copyright (c) 2022 Bastiaan Marinus van de Weerd


#[derive(PartialEq, Eq, Hash)]
struct Label(u16);

impl Label {
	const START: Self = Label(0);
}

#[cfg_attr(test, derive(Debug))]
struct Valve {
	flow_rate: usize,
	tunnels: Vec<Label>,
}

type Valves = std::collections::HashMap<Label, Valve>;

struct Graph<'valves> {
	nodes: Vec<(&'valves Label, &'valves Valve)>,
	edges: Vec<Option<std::num::NonZeroU8>>,
}

impl<'valves> From<&'valves Valves> for Graph<'valves> {
	fn from(valves: &'valves Valves) -> Self {
		use {std::{collections::{HashSet, VecDeque}, num::NonZeroU8}, itertools::Itertools as _};
		let nodes = valves.iter()
			.filter(|(l, v)| **l == Label::START || v.flow_rate > 0)
			.sorted_by_key(|(l, _)| l.0)
			.collect::<Vec<_>>();
		let len = nodes.len();
		let mut edges = vec![Option::<NonZeroU8>::None; len * len];
		let mut queue = VecDeque::new();
		let mut seen = HashSet::new();
		for f in 0..len {
			if f > 0 { seen.clear(); }
			queue.push_back((nodes[f].0, 0));
			while let Some((label, cost)) = queue.pop_front() {
				if !seen.insert(label) { continue }
				if let Some(t) = nodes.iter().position(|&(l, _)| l == label) {
					edges[len * f + t] = NonZeroU8::new(cost);
				}
				for to_label in &valves[label].tunnels {
					queue.push_back((to_label, cost + 1))
				}
			}
		}
		Graph { nodes, edges }
	}
}

/// Elapsed minutes, current node, and remaining valves to be opened.
type GraphMaxReleasedCacheKey = (usize, usize, u64);
/// Estimated additional pressure released
type GraphMaxReleasedCache = std::collections::HashMap<GraphMaxReleasedCacheKey, usize>;

impl Graph<'_> {
	fn is_start_nonzero(&self) -> bool {
		self.nodes.first().map(|(_, v)| v.flow_rate > 0).unwrap_or(false)
	}

	fn all_openable(&self) -> u64 {
		assert!(!self.is_start_nonzero());
		(u64::MAX >> (64 - self.nodes.len() + 1)) << 1
	}

	fn node_edges(&self, node: usize) -> &[Option<std::num::NonZeroU8>] {
		let len = self.nodes.len();
		&self.edges[node * len..(node + 1) * len]
	}

	fn max_released<const ELAPSED: usize>(
		&self,
		openable: Option<u64>,
		cache: Option<&mut GraphMaxReleasedCache>,
	) -> usize {
		const ELAPSED_LIMIT: usize = 30;

		let openable = openable.unwrap_or_else(|| self.all_openable());

		#[allow(clippy::too_many_arguments)]
		fn inner(
			graph: &Graph, openable: u64,
			elapsed: usize, node: usize, opened: u64,
			cache: &mut Cache,
		) -> usize {
			let nop_estimate = (ELAPSED_LIMIT - elapsed) * graph.nodes[node].1.flow_rate;

			if elapsed == ELAPSED_LIMIT || opened == openable { return nop_estimate }

			let cache_key = (elapsed, node, openable & !opened);
			if let Some(add_estimate) = cache.get(&cache_key) { return nop_estimate + add_estimate }

			let is_valve_openable = openable & 1 << node != 0;
			let is_valve_open = opened & 1 << node != 0;
			assert!(!is_valve_openable || is_valve_open);
			let mut add_estimate = 0;

			for (to_node, cost) in graph.node_edges(node).iter().enumerate() {
				let &Some(cost) = cost else { continue };
				let duration = cost.get() as usize + 1;
				let elapsed = elapsed + duration;
				let is_valve_openable = openable & 1 << to_node != 0;
				let is_valve_open = opened & 1 << to_node != 0;
				if elapsed > ELAPSED_LIMIT || !is_valve_openable || is_valve_open { continue }
				add_estimate = add_estimate.max(inner(
					graph, openable,
					elapsed, to_node, opened | 1 << to_node,
					cache
				))
			}

			cache.insert(cache_key, add_estimate);
			nop_estimate + add_estimate
		}

		type Cache = GraphMaxReleasedCache;
		inner(self, openable, ELAPSED, 0, 0, cache.unwrap_or(&mut Cache::new()))
	}
}


fn input_valves_from_str(s: &str) -> Valves {
	parsing::valves_from_str(s).map(|r| r.unwrap()).collect()
}

fn input_valves() -> Valves {
	input_valves_from_str(include_str!("day16.txt"))
}


fn part1_impl(input_valves: Valves) -> usize {
	Graph::from(&input_valves).max_released::<0>(None, None)
}

pub(crate) fn part1() -> usize {
	part1_impl(input_valves())
}


fn part2_impl(input_valves: Valves) -> usize {
	use rayon::prelude::{IntoParallelIterator as _, ParallelIterator as _};

	let graph = Graph::from(&input_valves);
	assert!(!graph.is_start_nonzero());
	let zero_start_shift = 1;
	let openable_len = graph.nodes.len() - zero_start_shift;
	let all_openable = graph.all_openable();
	let low_bound = openable_len / 2; // To be tuned to input

	(0..2_u32.pow(openable_len as u32) as u64)
		.into_par_iter()
		.filter_map(|o| (low_bound..=openable_len / 2).contains(&(o.count_ones() as usize))
			.then_some(o << zero_start_shift))
		.map_init(GraphMaxReleasedCache::new, |cache, you_openable| {
			let you_released = graph.max_released::<4>(Some(you_openable), Some(cache));
			let elephant_openable = !you_openable & all_openable;
			let elephant_released = graph.max_released::<4>(Some(elephant_openable), Some(cache));
			you_released + elephant_released
		})
		.max()
		.unwrap()
}

pub(crate) fn part2() -> usize {
	part2_impl(input_valves())
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
	assert_eq!(part1_impl(input_valves_from_str(INPUT)), 1651);
	assert_eq!(part1(), 1923);
	assert_eq!(part2_impl(input_valves_from_str(INPUT)), 1707);
	assert_eq!(part2(), 2594);
}
