// Copyright (c) 2022 Bastiaan Marinus van de Weerd


#[cfg_attr(test, derive(Debug))]
struct Item<'s> {
	name: &'s str,
	kind: ItemKind<'s>,
}

impl Item<'_> {
	fn iter(&self) -> impl Iterator<Item = &Item<'_>> {
		use {std::iter::once, itertools::Either};
		match &self.kind {
			ItemKind::File { .. } => Either::Left(once(self)),
			ItemKind::Dir(items) => Either::Right(once(self)
				.chain(Box::new(items.iter().flat_map(|item| item.iter()))
					as Box<dyn Iterator<Item = _>>))
		}
	}

	fn total_size(&self) -> usize {
		self.iter()
			.filter_map(|i| match &i.kind { ItemKind::File { size } => Some(size), _ => None })
			.sum()
	}

	fn is_dir(&self) -> bool {
		self.kind.is_dir()
	}
}

#[cfg_attr(test, derive(Debug))]
enum ItemKind<'s> {
	File { size: usize },
	Dir(Vec<Item<'s>>)
}

impl ItemKind<'_> {
	fn is_dir(&self) -> bool {
		matches!(self, ItemKind::Dir(_))
	}
}


fn input_root_items_from_str(s: &str) -> Vec<Item<'_>> {
	parsing::try_root_items_from_str(s).unwrap()
}

fn input_root_items() -> Vec<Item<'static>> {
	input_root_items_from_str(include_str!("day07.txt"))
}


fn part1_impl(input_root_items: Vec<Item<'_>>) -> usize {
	// This multiple-counts files in nested directories, but apparently that’s the idea? ¯\_(ツ)_/¯
	input_root_items.iter()
		.flat_map(|item| item.iter())
		.filter_map(|item| {
			if !item.is_dir() { return None }
			let size = item.total_size();
			(size <= 100_000).then_some(size)
		})
		.sum()
}

pub(crate) fn part1() -> usize {
	part1_impl(input_root_items())
}


fn part2_impl(input_root_items: Vec<Item<'_>>) -> usize {
	let total_size: usize = input_root_items.iter().map(|item| item.total_size()).sum();
	let size_needed = total_size - 40_000_000;
	input_root_items.iter()
		.flat_map(|item| item.iter())
		.filter_map(|item| {
			if !item.is_dir() { return None }
			let size = item.total_size();
			(size >= size_needed).then_some(size)
		})
		.min().unwrap()
}

pub(crate) fn part2() -> usize {
	part2_impl(input_root_items())
}


mod parsing {
	use std::num::ParseIntError;
	use super::{Item, ItemKind};

	trait ByteAsciiExt {
		fn is_ascii_dirname(&self) -> bool;
		fn is_ascii_filename(&self) -> bool;
	}

	impl ByteAsciiExt for u8 {
		fn is_ascii_dirname(&self) -> bool {
			self.is_ascii_alphabetic()
		}

		fn is_ascii_filename(&self) -> bool {
			self.is_ascii_alphabetic() || *self == b'.'
		}
	}

	#[allow(dead_code)]
	#[derive(Debug)]
	pub(super) enum ItemError {
		NoSpace,
		InvalidDirName { column: usize },
		InvalidFilesize(ParseIntError),
		InvalidFilename { column: usize },
	}

	impl<'s> TryFrom<&'s str> for Item<'s> {
		type Error = ItemError;
		fn try_from(line: &'s str) -> Result<Self, Self::Error> {
			let (prefix, name) = line.split_once(' ').ok_or(ItemError::NoSpace)?;
			if prefix == "dir" {
				if let Some(c) = name.bytes().position(|b| !b.is_ascii_dirname()) {
					return Err(ItemError::InvalidDirName { column: c + 1 })
				}
				Ok(Item { name, kind: ItemKind::Dir(vec![]) })
			} else {
				let size = prefix.parse().map_err(ItemError::InvalidFilesize)?;
				if let Some(c) = name.bytes().position(|b| !b.is_ascii_filename()) {
					return Err(ItemError::InvalidFilename { column: c + 1 })
				}
				Ok(Item { name, kind: ItemKind::File { size } })
			}
		}
	}

	#[allow(dead_code)]
	#[derive(Debug)]
	pub(super) enum InputError<'s> {
		ExpectedCommand(&'static str),
		CannotChangeOutOfRootDir,
		ChangeIntoDirNotFound(&'s str),
		ChangeIntoNotADir(&'s str),
		InvalidCommand,
	}

	#[allow(dead_code)]
	#[derive(Debug)]
	pub(super) enum LineErrorKind<'s> {
		Input(InputError<'s>),
		Output(Option<ItemError>),
	}

	#[allow(dead_code)]
	#[derive(Debug)]
	pub(super) struct LineError<'s> { line: usize, kind: LineErrorKind<'s> }

	pub(super) fn try_root_items_from_str(s: &str) -> Result<Vec<Item<'_>>, LineError<'_>> {
		use {LineErrorKind::*, InputError::*};

		let mut root_items: Vec<Item<'_>> = vec![];
		// SAFETY: Using raw pointers here to get around borrowing limitations. Items are only ever
		// “added“ to the directory at the top of the stack, so pointers will not get invalidated
		// because of vector resizing. Regardless, using raw pointers here is probably unwise, but
		// this AoC so YOLO!
		let mut dir_items_stack = vec![std::ptr::addr_of_mut!(root_items)];
		let mut listing = true;

		for (l, line) in s.lines().enumerate() {

			macro_rules! expect_command { ( $command:literal ) => { {
				let expected_command = concat!("$ ", $command);
				if line != expected_command {
					return Err(LineError { line: l + 1,
						kind: Input(ExpectedCommand(expected_command)) })
				}
			} } }

			match (l, line.strip_prefix("$ "), dir_items_stack.last().unwrap(), listing) {
				(0, _, _, _) => expect_command!("cd /"),
				(1, _, _, _) => expect_command!("ls"),
				(_, None, &dir_items, true) => {
					// SAFETY: See comment above `dir_items_stack`
					unsafe { &mut *dir_items }.push(line.try_into().map_err(|e|
						LineError { line: l + 1, kind: LineErrorKind::Output(Some(e)) })?)
				}
				(_, Some(command), &dir_items, _) => {
					listing = false;
					match command.strip_prefix("cd ") {
						Some("/") => dir_items_stack.drain(1..).for_each(|_| ()),
						Some("..") => {
							if dir_items_stack.len() == 1 {
								return Err(LineError { line: l + 1,
									kind: Input(CannotChangeOutOfRootDir) })
							}
							_ = dir_items_stack.pop()
						}
						Some(item_name) => {
							// SAFETY: See comment above `dir_items_stack`
							let item = unsafe { &mut *dir_items }.iter_mut()
								.find(|item| item.name == item_name)
								.ok_or(LineError { line: l + 1,
									kind: Input(ChangeIntoDirNotFound(item_name)) })?;
							match &mut item.kind {
								ItemKind::Dir(dir_items) =>
									dir_items_stack.push(std::ptr::addr_of_mut!(*dir_items)),
								_ => return Err(LineError { line: l + 1,
									kind: Input(ChangeIntoDirNotFound(item_name)) })
							}
							
						},
						None if command == "ls" => {
							// SAFETY: See comment above `dir_items_stack`
							unsafe { &mut *dir_items }.clear();
							listing = true
						}
						_ => return Err(LineError { line: l + 1,
							kind: Input(InvalidCommand) }) 
					}
				}
				_ => unreachable!(),
			}
		}

		Ok(root_items)
	}
}


#[test]
fn tests() {
	const INPUT: &str = indoc::indoc! { "
		$ cd /
		$ ls
		dir a
		14848514 b.txt
		8504156 c.dat
		dir d
		$ cd a
		$ ls
		dir e
		29116 f
		2557 g
		62596 h.lst
		$ cd e
		$ ls
		584 i
		$ cd ..
		$ cd ..
		$ cd d
		$ ls
		4060174 j
		8033020 d.log
		5626152 d.ext
		7214296 k
	" };
	assert_eq!(part1_impl(input_root_items_from_str(INPUT)), 95437);
	assert_eq!(part1(), 1449447);
	assert_eq!(part2_impl(input_root_items_from_str(INPUT)), 24933642);
	assert_eq!(part2(), 8679207);
}
