use alloc::borrow::Cow;

use thiserror::Error;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum CommitmentRole {
    Random,
    Trace,
    Quotient,
    Preprocessed,
    Permutation,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum MatrixRoute {
    Random { instance: usize },
    Trace { instance: usize },
    Quotient { instance: usize, chunk: usize },
    Preprocessed { instance: usize, matrix: usize },
    Permutation { instance: usize },
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct MatrixOpeningLayout {
    pub(crate) route: MatrixRoute,
    pub(crate) log_height: usize,
    pub(crate) width: usize,
    pub(crate) point_count: usize,
    pub(crate) next_step_log: Option<usize>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct InstanceLayout {
    pub(crate) challenge_width: usize,
    pub(crate) ext_log: usize,
    pub(crate) base_log: usize,
    pub(crate) trace_width: usize,
    pub(crate) trace_next: bool,
    pub(crate) pre_width: usize,
    pub(crate) pre_next: bool,
    pub(crate) quotient_log: usize,
    pub(crate) quotient_chunks: usize,
    pub(crate) permutation_width: usize,
}

#[derive(Clone, Copy, Debug, Error, PartialEq, Eq)]
pub(crate) enum LayoutError {
    #[error("STARK quotient chunk count overflows for log degree {log_degree}")]
    QuotientCountOverflow { log_degree: usize },
    #[error("STARK quotient matrix count overflows")]
    QuotientMatrixCountOverflow,
    #[error("preprocessed matrix route index {index} is out of bounds")]
    PreprocessedIndexOutOfBounds { index: usize },
    #[error("preprocessed matrix route repeats instance {index}")]
    DuplicatePreprocessedIndex { index: usize },
    #[error("preprocessed matrix route points to zero-width instance {index}")]
    PreprocessedWidthZero { index: usize },
    #[error("preprocessed metadata and matrix_to_instance map are not a complete bijection")]
    PreprocessedMetadataMismatch,
    #[error("STARK commitment ordinal {ordinal} is out of bounds")]
    InvalidCommitmentOrdinal { ordinal: usize },
}

pub(crate) fn checked_power_of_two(log_degree: usize) -> Result<usize, LayoutError> {
    let shift =
        u32::try_from(log_degree).map_err(|_| LayoutError::QuotientCountOverflow { log_degree })?;
    1usize
        .checked_shl(shift)
        .ok_or(LayoutError::QuotientCountOverflow { log_degree })
}

pub(crate) fn checked_quotient_matrix_count(
    instances: &[InstanceLayout],
) -> Result<usize, LayoutError> {
    instances.iter().try_fold(0usize, |total, instance| {
        total
            .checked_add(instance.quotient_chunks)
            .ok_or(LayoutError::QuotientMatrixCountOverflow)
    })
}

pub(crate) fn validate_preprocessed_metadata(
    metadata: &[Option<(usize, usize, usize)>],
    matrix_to_instance: &[usize],
    degree_bits: &[usize],
) -> Result<(), LayoutError> {
    if metadata.len() != degree_bits.len() || matrix_to_instance.is_empty() {
        return Err(LayoutError::PreprocessedMetadataMismatch);
    }
    for &instance in matrix_to_instance {
        if instance >= metadata.len() {
            return Err(LayoutError::PreprocessedIndexOutOfBounds { index: instance });
        }
    }
    let present = metadata.iter().filter(|entry| entry.is_some()).count();
    if present != matrix_to_instance.len() {
        return Err(LayoutError::PreprocessedMetadataMismatch);
    }
    for (instance, entry) in metadata.iter().enumerate() {
        let Some((matrix_index, width, degree)) = entry else {
            continue;
        };
        if *width == 0
            || *degree != degree_bits[instance]
            || *matrix_index >= matrix_to_instance.len()
            || matrix_to_instance[*matrix_index] != instance
        {
            return Err(LayoutError::PreprocessedMetadataMismatch);
        }
    }
    Ok(())
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct NativeStarkLayout<'a> {
    pub(crate) instances: alloc::vec::Vec<InstanceLayout>,
    pub(crate) preprocessed_order: Cow<'a, [usize]>,
    pub(crate) has_random: bool,
    pub(crate) has_preprocessed: bool,
    pub(crate) has_permutation: bool,
}

#[derive(Clone, Copy)]
pub struct FriOpeningLayout<'a> {
    inner: &'a NativeStarkLayout<'a>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct FriMatrixGeometry {
    log_height: usize,
    width: usize,
    point_count: usize,
}

impl FriMatrixGeometry {
    pub const fn log_height(self) -> usize {
        self.log_height
    }

    pub const fn width(self) -> usize {
        self.width
    }

    pub const fn point_count(self) -> usize {
        self.point_count
    }
}

impl<'a> FriOpeningLayout<'a> {
    #[allow(dead_code)]
    pub(crate) const fn new(inner: &'a NativeStarkLayout<'a>) -> Self {
        Self { inner }
    }

    pub fn commitment_count(self) -> usize {
        self.inner.commitment_count()
    }

    pub(crate) fn matrix_count(self, ordinal: usize) -> Result<usize, LayoutError> {
        self.inner.matrix_count(ordinal)
    }

    pub(crate) fn to_owned_layout(self) -> NativeStarkLayout<'static> {
        self.inner.to_owned_layout()
    }

    pub(crate) fn matches_layout(self, expected: &NativeStarkLayout<'_>) -> bool {
        self.inner == expected
    }

    pub fn matrices(self, ordinal: usize) -> impl Iterator<Item = FriMatrixGeometry> + Clone + 'a {
        let role = self.inner.commitment_role(ordinal);
        role.into_iter().flat_map(move |role| {
            self.inner.matrices(role).map(|matrix| FriMatrixGeometry {
                log_height: matrix.log_height,
                width: matrix.width,
                point_count: matrix.point_count,
            })
        })
    }
}

impl<'a> NativeStarkLayout<'a> {
    #[allow(dead_code)]
    pub(crate) const fn opening_view(&'a self) -> FriOpeningLayout<'a> {
        FriOpeningLayout::new(self)
    }

    pub(crate) fn new(
        instances: alloc::vec::Vec<InstanceLayout>,
        preprocessed_order: &'a [usize],
        has_random: bool,
        has_preprocessed: bool,
        has_permutation: bool,
    ) -> Result<Self, LayoutError> {
        for (position, &index) in preprocessed_order.iter().enumerate() {
            if index >= instances.len() {
                return Err(LayoutError::PreprocessedIndexOutOfBounds { index });
            }
            if instances[index].pre_width == 0 {
                return Err(LayoutError::PreprocessedWidthZero { index });
            }
            if preprocessed_order[..position].contains(&index) {
                return Err(LayoutError::DuplicatePreprocessedIndex { index });
            }
        }
        let positive_preprocessed: alloc::vec::Vec<usize> = instances
            .iter()
            .enumerate()
            .filter_map(|(index, instance)| (instance.pre_width != 0).then_some(index))
            .collect();
        if has_preprocessed == preprocessed_order.is_empty()
            || positive_preprocessed.len() != preprocessed_order.len()
            || positive_preprocessed
                .iter()
                .any(|index| !preprocessed_order.contains(index))
        {
            return Err(LayoutError::PreprocessedMetadataMismatch);
        }
        for instance in &instances {
            let quotient_log = instance.ext_log.checked_add(instance.quotient_log).ok_or(
                LayoutError::QuotientCountOverflow {
                    log_degree: instance.ext_log,
                },
            )?;
            checked_power_of_two(quotient_log)?;
        }
        checked_quotient_matrix_count(&instances)?;
        Ok(Self {
            instances,
            preprocessed_order: Cow::Borrowed(preprocessed_order),
            has_random,
            has_preprocessed,
            has_permutation,
        })
    }

    pub(crate) fn commitment_count(&self) -> usize {
        usize::from(self.has_random)
            + 2
            + usize::from(self.has_preprocessed)
            + usize::from(self.has_permutation)
    }

    pub(crate) fn matrix_count(&self, ordinal: usize) -> Result<usize, LayoutError> {
        let role = self
            .commitment_role(ordinal)
            .ok_or(LayoutError::InvalidCommitmentOrdinal { ordinal })?;
        match role {
            CommitmentRole::Random | CommitmentRole::Trace => Ok(self.instances.len()),
            CommitmentRole::Quotient => checked_quotient_matrix_count(&self.instances),
            CommitmentRole::Preprocessed => Ok(self.preprocessed_order.len()),
            CommitmentRole::Permutation => Ok(self
                .instances
                .iter()
                .filter(|instance| instance.permutation_width != 0)
                .count()),
        }
    }

    pub(crate) fn to_owned_layout(&self) -> NativeStarkLayout<'static> {
        NativeStarkLayout {
            instances: self.instances.clone(),
            preprocessed_order: Cow::Owned(self.preprocessed_order.to_vec()),
            has_random: self.has_random,
            has_preprocessed: self.has_preprocessed,
            has_permutation: self.has_permutation,
        }
    }

    pub(crate) const fn commitment_role(&self, ordinal: usize) -> Option<CommitmentRole> {
        let mut next = 0;
        if self.has_random {
            if ordinal == next {
                return Some(CommitmentRole::Random);
            }
            next += 1;
        }
        if ordinal == next {
            return Some(CommitmentRole::Trace);
        }
        next += 1;
        if ordinal == next {
            return Some(CommitmentRole::Quotient);
        }
        next += 1;
        if self.has_preprocessed {
            if ordinal == next {
                return Some(CommitmentRole::Preprocessed);
            }
            next += 1;
        }
        if self.has_permutation && ordinal == next {
            return Some(CommitmentRole::Permutation);
        }
        None
    }

    pub(crate) const fn matrices(&self, role: CommitmentRole) -> MatrixLayoutIter<'_> {
        MatrixLayoutIter {
            layout: self,
            role,
            instance: 0,
            chunk: 0,
            preprocessed: 0,
        }
    }
}

#[derive(Clone)]
pub(crate) struct MatrixLayoutIter<'a> {
    layout: &'a NativeStarkLayout<'a>,
    role: CommitmentRole,
    instance: usize,
    chunk: usize,
    preprocessed: usize,
}

impl Iterator for MatrixLayoutIter<'_> {
    type Item = MatrixOpeningLayout;

    fn next(&mut self) -> Option<Self::Item> {
        if (self.role == CommitmentRole::Random && !self.layout.has_random)
            || (self.role == CommitmentRole::Preprocessed && !self.layout.has_preprocessed)
            || (self.role == CommitmentRole::Permutation && !self.layout.has_permutation)
        {
            return None;
        }
        match self.role {
            CommitmentRole::Random => {
                let instance = self.instance;
                let info = self.layout.instances.get(instance)?;
                self.instance += 1;
                Some(MatrixOpeningLayout {
                    route: MatrixRoute::Random { instance },
                    log_height: info.ext_log,
                    width: info.challenge_width,
                    point_count: 1,
                    next_step_log: None,
                })
            }
            CommitmentRole::Trace => {
                let instance = self.instance;
                let info = self.layout.instances.get(instance)?;
                self.instance += 1;
                Some(MatrixOpeningLayout {
                    route: MatrixRoute::Trace { instance },
                    log_height: info.ext_log,
                    width: info.trace_width,
                    point_count: usize::from(info.trace_next) + 1,
                    next_step_log: info.trace_next.then_some(info.base_log),
                })
            }
            CommitmentRole::Quotient => loop {
                let info = self.layout.instances.get(self.instance)?;
                if self.chunk == info.quotient_chunks {
                    self.instance += 1;
                    self.chunk = 0;
                    continue;
                }
                let chunk = self.chunk;
                self.chunk += 1;
                return Some(MatrixOpeningLayout {
                    route: MatrixRoute::Quotient {
                        instance: self.instance,
                        chunk,
                    },
                    log_height: info.ext_log,
                    width: info.challenge_width,
                    point_count: 1,
                    next_step_log: None,
                });
            },
            CommitmentRole::Preprocessed => {
                let matrix = self.preprocessed;
                let &instance = self.layout.preprocessed_order.get(matrix)?;
                self.preprocessed += 1;
                let info = self.layout.instances[instance];
                Some(MatrixOpeningLayout {
                    route: MatrixRoute::Preprocessed { instance, matrix },
                    log_height: info.ext_log,
                    width: info.pre_width,
                    point_count: usize::from(info.pre_next) + 1,
                    next_step_log: info.pre_next.then_some(info.base_log),
                })
            }
            CommitmentRole::Permutation => loop {
                let info = self.layout.instances.get(self.instance)?;
                let instance = self.instance;
                self.instance += 1;
                if info.permutation_width == 0 {
                    continue;
                }
                return Some(MatrixOpeningLayout {
                    route: MatrixRoute::Permutation { instance },
                    log_height: info.ext_log,
                    width: info.permutation_width,
                    point_count: 2,
                    next_step_log: Some(info.base_log),
                });
            },
        }
    }
}
