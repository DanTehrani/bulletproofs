use halo2curves::CurveAffineExt;

#[derive(Clone)]
pub struct Gens<C>
where
    C: CurveAffineExt,
{
    pub g: Vec<C>,
    pub h: Vec<C>,
    pub u: C,
}

impl<C> Gens<C>
where
    C: CurveAffineExt,
{
    pub fn new(n: usize) -> Self {
        // Unsafe!!
        let g = (0..n)
            .map(|i| (C::generator() * C::ScalarExt::from(i as u64)).into())
            .collect::<Vec<C>>();
        let h = (0..n)
            .map(|i| (C::generator() * C::ScalarExt::from((64 - n - i) as u64)).into())
            .collect::<Vec<C>>();
        let u = C::generator() * C::ScalarExt::from(64 as u64);
        Self { g, h, u: u.into() }
    }
}
