use crate::gens::Gens;
use halo2curves::CurveAffineExt;

pub struct Commitment<C>
where
    C: CurveAffineExt,
{
    gens: Gens<C>,
}

impl<C> Commitment<C>
where
    C: CurveAffineExt,
{
    pub fn new(gens: Gens<C>) -> Self {
        Self { gens }
    }

    pub fn commit(&self, a: &[C::ScalarExt]) {}
}
