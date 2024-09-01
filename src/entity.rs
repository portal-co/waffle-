//! Type-safe indices and indexed containers.

use std::default::Default;
use std::fmt::Debug;
use std::hash::Hash;
use std::marker::PhantomData;
use std::ops::{Index, IndexMut};

// use arena_traits::Arena;

pub trait EntityRef: Clone + Copy + PartialEq + Eq + PartialOrd + Ord + Hash {
    fn new(value: usize) -> Self;
    fn index(self) -> usize;
    fn invalid() -> Self;
    fn is_valid(self) -> bool {
        self != Self::invalid()
    }
    fn is_invalid(self) -> bool {
        self == Self::invalid()
    }
    fn maybe_index(self) -> Option<usize>;
}

#[macro_export]
macro_rules! declare_entity {
    ($name:tt, $prefix:tt) => {
        #[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, serde::Serialize, serde::Deserialize)]
        pub struct $name(u32);

        impl $crate::entity::EntityRef for $name {
            fn new(value: usize) -> Self {
                use std::convert::TryFrom;
                let value = u32::try_from(value).unwrap();
                debug_assert!(value != u32::MAX);
                Self(value)
            }
            fn index(self) -> usize {
                debug_assert!(self.is_valid());
                self.0 as usize
            }
            fn maybe_index(self) -> Option<usize> {
                if self.is_valid() {
                    Some(self.0 as usize)
                } else {
                    None
                }
            }
            fn invalid() -> Self {
                Self(u32::MAX)
            }
        }

        impl std::convert::From<u32> for $name {
            fn from(val: u32) -> Self {
                <Self as $crate::entity::EntityRef>::new(val as usize)
            }
        }

        impl std::default::Default for $name {
            fn default() -> Self {
                <Self as $crate::entity::EntityRef>::invalid()
            }
        }

        impl std::fmt::Debug for $name {
            fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
                write!(f, "{}{}", $prefix, self.0)
            }
        }
        impl std::fmt::Display for $name {
            fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
                write!(f, "{}{}", $prefix, self.0)
            }
        }
    };
}

#[derive(Clone, Debug, serde::Serialize, serde::Deserialize)]
pub struct EntityVec<Idx: EntityRef, T: Clone + Debug>(Vec<T>, PhantomData<Idx>);

impl<Idx: EntityRef, T: Clone + Debug> std::default::Default for EntityVec<Idx, T> {
    fn default() -> Self {
        Self(vec![], PhantomData)
    }
}

impl<Idx: EntityRef, T: Clone + Debug> From<Vec<T>> for EntityVec<Idx, T> {
    fn from(vec: Vec<T>) -> Self {
        Self(vec, PhantomData)
    }
}

impl<Idx: EntityRef, T: Clone + Debug> EntityVec<Idx, T> {
    pub fn push(&mut self, t: T) -> Idx {
        let idx = Idx::new(self.0.len());
        self.0.push(t);
        idx
    }

    pub fn len(&self) -> usize {
        self.0.len()
    }

    pub fn iter(&self) -> impl DoubleEndedIterator<Item = Idx> {
        (0..self.0.len()).map(|index| Idx::new(index))
    }

    pub fn values(&self) -> impl DoubleEndedIterator<Item = &T> {
        self.0.iter()
    }

    pub fn values_mut(&mut self) -> impl DoubleEndedIterator<Item = &mut T> {
        self.0.iter_mut()
    }

    pub fn entries(&self) -> impl DoubleEndedIterator<Item = (Idx, &T)> {
        self.0
            .iter()
            .enumerate()
            .map(|(index, t)| (Idx::new(index), t))
    }

    pub fn entries_mut(&mut self) -> impl Iterator<Item = (Idx, &mut T)> {
        self.0
            .iter_mut()
            .enumerate()
            .map(|(index, t)| (Idx::new(index), t))
    }

    pub fn get(&self, idx: Idx) -> Option<&T> {
        self.0.get(idx.index())
    }

    pub fn get_mut(&mut self, idx: Idx) -> Option<&mut T> {
        self.0.get_mut(idx.index())
    }

    pub fn into_vec(self) -> Vec<T> {
        self.0
    }
}

impl<Idx: EntityRef, T: Clone + Debug> Index<Idx> for EntityVec<Idx, T> {
    type Output = T;
    fn index(&self, idx: Idx) -> &T {
        &self.0[idx.index()]
    }
}

impl<Idx: EntityRef, T: Clone + Debug> IndexMut<Idx> for EntityVec<Idx, T> {
    fn index_mut(&mut self, idx: Idx) -> &mut T {
        &mut self.0[idx.index()]
    }
}

// impl<Idx: EntityRef, T: Clone + Debug> Arena<Idx> for EntityVec<Idx, T> {
//     fn alloc(&mut self, a: Self::Output) -> Idx {
//         self.push(a)
//     }

//     fn iter(&self) -> impl Iterator<Item = Idx> {
//         self.iter()
//     }
// }

#[derive(Clone, Debug, Default, serde::Serialize, serde::Deserialize)]
pub struct PerEntity<Idx: EntityRef, T: Clone + Debug + Default>(Vec<T>, PhantomData<Idx>, T);

impl<Idx: EntityRef, T: Clone + Debug + Default> Index<Idx> for PerEntity<Idx, T> {
    type Output = T;
    fn index(&self, idx: Idx) -> &T {
        debug_assert!(idx.is_valid());
        self.0.get(idx.index()).unwrap_or(&self.2)
    }
}

impl<Idx: EntityRef, T: Clone + Debug + Default> IndexMut<Idx> for PerEntity<Idx, T> {
    fn index_mut(&mut self, idx: Idx) -> &mut T {
        debug_assert!(idx.is_valid());
        if idx.index() >= self.0.len() {
            self.0.resize(idx.index() + 1, T::default());
        }
        &mut self.0[idx.index()]
    }
}

impl<Idx: EntityRef, T: Clone + Debug + Default + PartialEq> PartialEq for PerEntity<Idx, T> {
    fn eq(&self, other: &Self) -> bool {
        self.0 == other.0
    }
}
impl<Idx: EntityRef, T: Clone + Debug + Default + PartialEq + Eq> Eq for PerEntity<Idx, T> {}
