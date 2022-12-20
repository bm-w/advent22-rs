// Copyright (c) 2022 Bastiaan Marinus van de Weerd


macro_rules! resources { ( $( $name:ident ),+ ) => { $(
	#[cfg_attr(test, derive(Debug))]
	#[derive(PartialEq, Eq, PartialOrd, Ord, Hash, Clone, Copy)]
	struct $name(usize);
)+ } }
resources!(Ore, Clay, Obsidian, Geode);

#[cfg_attr(test, derive(Debug))]
struct Blueprint {
	id: u8,
	ore_robot: Ore,
	clay_robot: Ore,
	obsidian_robot: (Ore, Clay),
	geode_robot: (Ore, Obsidian),
}

impl Blueprint {
	// TODO(bm-w): Macro (tried but got stuck with the `self` keyword)?
	fn sufficient_ore_robots(&self) -> usize { [self.ore_robot.0, self.clay_robot.0,
		self.obsidian_robot.0.0, self.geode_robot.0.0].into_iter().max().unwrap() }
	fn sufficient_clay_robots(&self) -> usize { self.obsidian_robot.1.0 }
	fn sufficient_obsidian_robots(&self) -> usize { self.geode_robot.1.0 }
	fn sufficient_geode_robots(&self) -> usize { usize::MAX } // Can never have enough geodes
}

#[cfg_attr(test, derive(Debug))]
#[derive(Clone)]
struct Simulation<'bp> {
	blueprint: &'bp Blueprint,
	elapsed: usize,
	resources: (Ore, Clay, Obsidian, Geode),
	robots: (Ore, Clay, Obsidian, Geode),
	idled: bool,
}

impl std::cmp::PartialEq for Simulation<'_> {
	fn eq(&self, other: &Self) -> bool {
		std::ptr::eq(self.blueprint as *const _, other.blueprint as *const _)
			&& self.elapsed == other.elapsed
			&& self.resources == other.resources
			&& self.robots == other.robots
	}
}

impl std::cmp::Eq for Simulation<'_> {}

impl std::hash::Hash for Simulation<'_> {
	fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
		(self.blueprint as *const Blueprint).hash(state);
		self.elapsed.hash(state);
		self.resources.hash(state);
		self.robots.hash(state);
	}
}

impl<'bp> From<&'bp Blueprint> for Simulation<'bp> {
	fn from(blueprint: &'bp Blueprint) -> Self {
		Simulation {
			blueprint,
			elapsed: 0,
			resources: (Ore(0), Clay(0), Obsidian(0), Geode(0)),
			robots: (Ore(1), Clay(0), Obsidian(0), Geode(0)),
			idled: false,
		}
	}
}

#[cfg_attr(test, derive(Debug))]
enum BuildAction { Geode, Obsidian, Clay, Ore }

macro_rules! simulation_optimistic_resource_collection { ( $name:ident ) => { paste::paste! {
	fn [<optimistic_ $name _collection>]<const MINUTES: usize>(&self) -> usize {
		let remaining = MINUTES - self.elapsed;
		#[allow(unused_variables)]
		let ((Ore(ore_avail), Clay(clay_avail), Obsidian(obsidian_avail), Geode(geode_avail)),
			 (Ore(ore_robots), Clay(clay_robots), Obsidian(obsidian_robots), Geode(geode_robots)))
				= (self.resources, self.robots);
		[<$name _avail>] + [<$name _robots>] * remaining + remaining * (remaining - 1) / 2
	}
} } }

impl Simulation<'_> {

	// Returns which robot (if any) was built
	fn tick(&mut self, variation: usize) -> Option<BuildAction> {
		use BuildAction as BA;

		let (Ore(ore_avail), Clay(clay_avail), Obsidian(obsidian_avail), Geode(geode_avail))
			= &mut self.resources;
		let (Ore(ore_robots), Clay(clay_robots), Obsidian(obsidian_robots), Geode(geode_robots))
			= self.robots;

		// “Plan” build
		macro_rules! build_action_check { ( $robot:ident, $( $resource:ident ),+ ) => { {
			paste::paste! {
				#[allow(unused_parens)]
				let ($( $resource([<$resource:lower _cost>]) ),+)
					= self.blueprint.[<$robot:lower _robot>];
				let availability_check = $( *[<$resource:lower _avail >]
					>= [<$resource:lower _cost>] ) && +;
				let sufficiency_check = [<$robot:lower _robots>]
					< self.blueprint.[<sufficient_ $robot:lower _robots>]();
				let idled_check = !self.idled || $( *[<$resource:lower _avail >]
					< [<$resource:lower _cost>] + [<$resource:lower _robots>] ) || +;
				(availability_check && sufficiency_check && idled_check)
			}
		} } }

		let build_action = [BA::Geode, BA::Obsidian, BA::Clay, BA::Ore]
			.into_iter()
			.filter(|build_action| match build_action {
				BA::Ore => build_action_check!(Ore, Ore),
				BA::Clay => build_action_check!(Clay, Ore),
				BA::Obsidian => build_action_check!(Obsidian, Ore, Clay),
				BA::Geode => build_action_check!(Geode, Ore, Obsidian),
			})
			.nth(variation);

		// Collect
		*ore_avail += ore_robots;
		*clay_avail += clay_robots;
		*obsidian_avail += obsidian_robots;
		*geode_avail += geode_robots;

		// Execute build
		let (Ore(ore_robots), Clay(clay_robots), Obsidian(obsidian_robots), Geode(geode_robots))
			= &mut self.robots;
		match build_action {
			Some(BA::Ore) => {
				*ore_avail -= self.blueprint.ore_robot.0;
				*ore_robots += 1;
			}
			Some(BA::Clay) => {
				*ore_avail -= self.blueprint.clay_robot.0;
				*clay_robots += 1;
			}
			Some(BA::Obsidian) => {
				*ore_avail -= self.blueprint.obsidian_robot.0.0;
				*clay_avail -= self.blueprint.obsidian_robot.1.0;
				*obsidian_robots += 1;
			}
			Some(BA::Geode) => {
				*ore_avail -= self.blueprint.geode_robot.0.0;
				*obsidian_avail -= self.blueprint.geode_robot.1.0;
				*geode_robots += 1;
			}
			None => (),
		}

		self.idled = build_action.is_none();
		self.elapsed += 1;

		build_action
	}

	simulation_optimistic_resource_collection!(obsidian);
	simulation_optimistic_resource_collection!(geode);

	// Returns optimal number of geodes that can be collected
	fn optimize_geode_collection<const MINUTES: usize>(&self) -> usize {
		use std::collections::HashMap;

		fn inner<'bp, const MINUTES: usize>(
			simulation: &Simulation<'bp>,
			cache: &mut HashMap<Simulation<'bp>, usize>,
			optimal_geodes: usize,
		) -> usize {
			if simulation.elapsed + 1 == MINUTES {
				return simulation.resources.3.0 + simulation.robots.3.0
			} else if simulation.optimistic_geode_collection::<MINUTES>() < optimal_geodes {
				return optimal_geodes
			} else if simulation.optimistic_obsidian_collection::<MINUTES>()
					< simulation.blueprint.geode_robot.1.0 {
				return simulation.resources.3.0
					+ simulation.robots.3.0 * (MINUTES - simulation.elapsed)
			} else if let Some(geodes) = cache.get(simulation) {
				return *geodes
			}

			let mut optimal_geodes = optimal_geodes;
			for variation in 0.. {
				let mut clone = simulation.clone();
				let robot_built = clone.tick(variation);
				optimal_geodes = optimal_geodes.max(
					inner::<MINUTES>(&clone, cache, optimal_geodes));
				if matches!(robot_built, Some(BuildAction::Geode) | None) { break }
			}
			cache.insert(simulation.clone(), optimal_geodes);
			optimal_geodes
		}

		inner::<MINUTES>(self, &mut HashMap::new(), 0)
	}
}

impl Blueprint {
	fn optimize_geode_collection<const MINUTES: usize>(&self) -> usize {
		Simulation::from(self).optimize_geode_collection::<MINUTES>()
	}

	fn compute_quality_level<const MINUTES: usize>(&self) -> u64 {
		self.id as u64 * self.optimize_geode_collection::<MINUTES>() as u64
	}
}


fn input_blueprints_from_str(s: &str) -> impl Iterator<Item = Blueprint> + '_ {
	parsing::blueprints_from_str(s).map(|r| r.unwrap())
}
fn input_blueprints() -> impl Iterator<Item = Blueprint> + 'static {
	input_blueprints_from_str(include_str!("day19.txt"))
}


fn part1_impl(input_blueprints: impl Iterator<Item = Blueprint> + Send) -> u64 {
	use rayon::iter::{ParallelBridge as _, ParallelIterator as _};
	input_blueprints
		.par_bridge()
		.map(|bp| bp.compute_quality_level::<24>())
		.sum()
}

pub(crate) fn part1() -> u64 {
	part1_impl(input_blueprints())
}


fn part2_impl(input_blueprints: impl Iterator<Item = Blueprint> + Send) -> u64 {
	use rayon::iter::{ParallelBridge as _, ParallelIterator as _};
	input_blueprints
		.take(3)
		.par_bridge()
		.map(|bp| bp.optimize_geode_collection::<32>() as u64)
		.product()
}

pub(crate) fn part2() -> u64 {
	part2_impl(input_blueprints())
}


mod parsing {
	use {std::{num::ParseIntError, str::FromStr}, either::Either};
	use super::{Ore, Clay, Obsidian, Blueprint};


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

	macro_rules! try_resource_from_str {
		( $name:ident ) => { paste::paste! {
			#[derive(Debug)]
			pub(super) enum [<$name Error>] {
				Format { column: usize },
				Amount(ParseIntError),
			}

			fn [<try_ $name:lower _from_str>](s: &str)
			-> Result<($name, &str), [<$name Error>]> {
				use [<$name Error>] as E;
				let s0 = s;
				let (amount, s) = s.split_once(' ')
					.ok_or(E::Format { column: 1 })?;
				let amount = amount.parse().map_err(E::Amount)?;
				let s = try_strip_prefix(s, stringify!([< $name:lower >]))
					.map_err(|s| E::Format { column: str_offset!(s0, s) + 1 })?;
				Ok(($name(amount), s))
			}
		} }
	}
	try_resource_from_str!(Ore);
	try_resource_from_str!(Clay);
	try_resource_from_str!(Obsidian);

	#[allow(dead_code)]
	#[derive(Debug)]
	pub(super) enum BlueprintError {
		Format { column: usize },
		Id(ParseIntError),
		Ore(OreError),
		Clay(OreError),
		Obsidian(Either<OreError, ClayError>),
		Geode(Either<OreError, ObsidianError>),
	}

	pub(super) fn try_blueprint_from_str(s: &str) -> Result<(Blueprint, &str), BlueprintError> {
		use BlueprintError as E;

		let s0 = s;
		macro_rules! c { ( $s:expr ) => { str_offset!(s0, $s) } }

		let s = try_strip_prefix(s, "Blueprint ")
			.map_err(|s| E::Format { column: c!(s) + 1 })?;
		let (id, s) = s.split_once(':')
			.ok_or(E::Format { column: c!(s) + 1 })?;
		let id = id.parse().map_err(E::Id)?;
		let s = s.trim_start();

		macro_rules! recolumn_resource_format_err { ( $s:ident, $name:ident, $map:expr ) => {
			paste::paste! {
				#[allow(clippy::redundant_closure_call)]
				|err| ($map)(match err {
					[<$name Error>]::Format { column } =>
						[<$name Error>]::Format { column: c!($s) + column },
					_ => err
				})
			} }
		}

		macro_rules! robot {
			(@ore $s:ident, $kind:ident, $err:expr) => { {
				let s = try_strip_prefix($s.trim_start(), stringify!(Each $kind robot costs ))
					.map_err(|s| E::Format { column: c!(s) + 1 })?;
				// TODO(bm-w): Can’t `stringify!` include the trailing space somehow?
				let s = s.strip_prefix(' ').ok_or(E::Format { column: c!(s) + 1 })?;
				try_ore_from_str(s).map_err(recolumn_resource_format_err!(s, Ore, $err))?
			} };
			(@strip_period $s:ident, $ret:expr ) => { {
				($ret, $s.strip_prefix('.').ok_or(E::Format { column: c!(s) + 1 })?)
			} };
			( $s:ident, $kind:ident, $err:expr) => { {
				let (ore, s) = robot!(@ore $s, $kind, $err);
				robot!(@strip_period s, ore)
			} };
			( $s:ident, $kind:ident, $ore_err:expr, $resource:ident, $resource_err:expr ) => { {
				let (ore, s) = robot!(@ore $s, $kind, $ore_err);
				let s = try_strip_prefix(s, " and ").map_err(|s| E::Format { column: c!(s) + 1 })?;
				paste::paste! {
					let (resource, s) = [<try_ $resource:lower _from_str>](s)
						.map_err(recolumn_resource_format_err!(s, $resource, $resource_err))?;
				}
				robot!(@strip_period s, (ore, resource))
			} }
		}

		let (ore_robot, s) = robot!(s, ore, E::Ore);
		let (clay_robot, s) = robot!(s, clay, E::Clay);
		let (obsidian_robot, s) = robot!(s, obsidian, |ore| E::Obsidian(Either::Left(ore)),
			Clay, |clay| E::Obsidian(Either::Right(clay)));
		let (geode_robot, s) = robot!(s, geode, |ore| E::Geode(Either::Left(ore)),
			Obsidian, |obsidian| E::Geode(Either::Right(obsidian)));

		Ok((Blueprint { id, ore_robot, clay_robot, obsidian_robot, geode_robot }, s))
	}

	impl FromStr for Blueprint {
		type Err = BlueprintError;
		fn from_str(s: &str) -> Result<Self, Self::Err> {
			let (blueprint, rest) = try_blueprint_from_str(s)?;
			if !rest.is_empty() { return Err(
				BlueprintError::Format { column: str_offset!(s, rest) + 1 }) }
			Ok(blueprint)
		}
	}

	#[allow(dead_code)]
	#[derive(Debug)]
	pub(super) struct BlueprintsError { line: usize, source: BlueprintError }

	pub(super) fn blueprints_from_str(s: &str)
	-> impl Iterator<Item = Result<Blueprint, BlueprintsError>> + '_ {
		s.lines()
			.enumerate()
			.map(|(l, line)| line.parse()
				.map_err(|e| BlueprintsError { line: l + 1, source: e }))
	}
}


#[test]
fn tests() {
	const INPUT: &str = indoc::indoc! { "
		Blueprint 1:
		  Each ore robot costs 4 ore.
		  Each clay robot costs 2 ore.
		  Each obsidian robot costs 3 ore and 14 clay.
		  Each geode robot costs 2 ore and 7 obsidian.

		Blueprint 2:
		  Each ore robot costs 2 ore.
		  Each clay robot costs 3 ore.
		  Each obsidian robot costs 3 ore and 8 clay.
		  Each geode robot costs 3 ore and 12 obsidian.
	" };
	let input = INPUT.replace("\n  ", " ").replace("\n\n", "\n");
	assert_eq!(part1_impl(input_blueprints_from_str(&input)), 33);
	assert_eq!(part1(), 2341);
	assert_eq!(part2_impl(input_blueprints_from_str(&input)), 3472);
	assert_eq!(part2(), 3689);
}
