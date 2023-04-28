#![allow(non_snake_case)]
use std::sync::WaitTimeoutResult;

use halo2curves::CurveAffineExt;
mod commitment;
mod gens;
use ff::{Field, PrimeField, PrimeFieldBits};
use gens::Gens;
use multiexp::multiexp;
use poseidon_transcript::transcript::PoseidonTranscript;
use std::ops::Neg;
use zeroize::DefaultIsZeroes;

#[derive(Clone, Debug)]
pub struct BulletProof<C>
where
    C: CurveAffineExt,
{
    pub a: C::ScalarExt,
    pub b: C::ScalarExt,
    pub L_vec: Vec<C>,
    pub R_vec: Vec<C>,
}

pub struct BulletProver<C>
where
    C: CurveAffineExt,
{
    gens: Gens<C>,
    transcript: PoseidonTranscript<C>,
}

impl<C> BulletProver<C>
where
    C: CurveAffineExt,
    C::ScalarExt: PrimeFieldBits,
    C::Base: PrimeField<Repr = [u8; 32]>,
    C::ScalarExt: DefaultIsZeroes,
    C::ScalarExt: PrimeField<Repr = [u8; 32]>,
{
    pub fn new(gens: Gens<C>, transcript: PoseidonTranscript<C>) -> Self {
        Self { gens, transcript }
    }

    pub fn dot_prod(a: &[C::ScalarExt], b: &[C::ScalarExt]) -> C::ScalarExt {
        assert_eq!(a.len(), b.len());

        let mut res = C::ScalarExt::zero();

        for i in 0..a.len() {
            res += a[i] * b[i];
        }

        res
    }

    fn scale_vec(a: &[C::ScalarExt], b: C::ScalarExt) -> Vec<C::ScalarExt> {
        let mut res = Vec::with_capacity(a.len());

        for i in 0..a.len() {
            res.push(a[i] * b);
        }

        res
    }

    pub fn prove(&mut self, a: &[C::ScalarExt], b: &[C::ScalarExt], P: &C) -> BulletProof<C> {
        let mut n = a.len().next_power_of_two();

        let num_rounds = (n as f64).log2() as usize;

        let mut g = self.gens.g.clone();
        let mut h = self.gens.h.clone();
        let u = self.gens.u;

        let mut a = a.to_vec();
        let mut b = b.to_vec();

        a.resize(n, C::ScalarExt::zero());
        b.resize(n, C::ScalarExt::zero());

        // Apply the Hash function and get P
        let mut P = P.clone();

        let mut L_vec = Vec::<C>::with_capacity(num_rounds);
        let mut R_vec = Vec::<C>::with_capacity(num_rounds);

        for _ in 0..num_rounds {
            n /= 2;

            let a_L = &a[..n];
            let b_R = &b[n..];
            let c_L = Self::dot_prod(a_L, b_R);

            let a_R = &a[n..];
            let b_L = &b[..n];
            let c_R = Self::dot_prod(a_R, b_L);

            let L = multiexp(
                &g[n..]
                    .iter()
                    .zip(a_L.iter())
                    .map(|(g_i, a_i)| (*a_i, (*g_i).into()))
                    .collect::<Vec<(C::ScalarExt, C::Curve)>>(),
            ) + multiexp(
                &h[..n]
                    .iter()
                    .zip(b_R.iter())
                    .map(|(h_i, b_i)| (*b_i, (*h_i).into()))
                    .collect::<Vec<(C::ScalarExt, C::Curve)>>(),
            ) + u * c_L;

            let R = multiexp(
                &g[..n]
                    .iter()
                    .zip(a_R.iter())
                    .map(|(g_i, a_i)| (*a_i, (*g_i).into()))
                    .collect::<Vec<(C::ScalarExt, C::Curve)>>(),
            ) + multiexp(
                &h[n..]
                    .iter()
                    .zip(b_L.iter())
                    .map(|(h_i, b_i)| (*b_i, (*h_i).into()))
                    .collect::<Vec<(C::ScalarExt, C::Curve)>>(),
            ) + u * c_R;

            L_vec.push(L.into());
            R_vec.push(R.into());

            self.transcript.append_points(&[L.into(), R.into()]);

            let x = self.transcript.squeeze(1)[0];
            let x_invert = x.invert().unwrap();

            let mut g_prime: Vec<C::Curve> = vec![C::identity().into(); n];
            for (i, g_i) in g[..n].iter().enumerate() {
                g_prime[i] += *g_i * x_invert;
            }

            for (i, g_i) in g[n..].iter().enumerate() {
                g_prime[i] += *g_i * x;
            }

            let mut h_prime: Vec<C::Curve> = vec![C::identity().into(); n];
            for (i, h_i) in h[..n].iter().enumerate() {
                h_prime[i] += *h_i * x;
            }

            for (i, h_i) in h[n..].iter().enumerate() {
                h_prime[i] += *h_i * x_invert;
            }

            // Update the basis
            g = g_prime.iter().map(|x| (*x).into()).collect();
            h = h_prime.iter().map(|x| (*x).into()).collect();

            P = (L * (x * x) + R * (x_invert * x_invert) + P).into();

            a = Self::scale_vec(a_L, x)
                .iter()
                .zip(Self::scale_vec(a_R, x_invert).iter())
                .map(|(r, l)| *r + *l)
                .collect::<Vec<C::Scalar>>();

            b = Self::scale_vec(b_L, x_invert)
                .iter()
                .zip(Self::scale_vec(b_R, x).iter())
                .map(|(r, l)| *r + *l)
                .collect::<Vec<C::Scalar>>();
        }

        assert_eq!(1, a.len());
        assert_eq!(1, b.len());
        assert_eq!(1, g.len());
        assert_eq!(1, h.len());

        BulletProof {
            a: a[0],
            b: b[0],
            L_vec,
            R_vec,
        }
    }
}

pub struct BulletVerifier<C>
where
    C: CurveAffineExt,
    C::ScalarExt: PrimeField<Repr = [u8; 32]>,
{
    gens: Gens<C>,
    transcript: PoseidonTranscript<C>,
}

impl<C> BulletVerifier<C>
where
    C: CurveAffineExt,
    C::ScalarExt: PrimeField<Repr = [u8; 32]>,
    C::Base: PrimeField<Repr = [u8; 32]>,
    C::ScalarExt: DefaultIsZeroes,
    C::ScalarExt: PrimeFieldBits,
{
    fn new(gens: Gens<C>, transcript: PoseidonTranscript<C>) -> Self {
        Self { gens, transcript }
    }

    fn compute_scalar(
        challenges: &[C::ScalarExt],
        challenges_inv: &[C::ScalarExt],
    ) -> Vec<C::ScalarExt> {
        let mut scalars = vec![C::ScalarExt::one(); challenges.len().pow(2u32)];
        let num_rounds = (challenges.len() as f64).log2() as usize;

        for i in 0..scalars.len() {
            for j in 0..num_rounds {
                let b = ((i >> j as u32) & 1) as u32;
                assert!(b == 0 || b == 1);
                if b == 1 {
                    scalars[i] *= challenges[j];
                } else {
                    scalars[i] *= challenges_inv[j];
                }
            }
        }

        scalars
    }

    fn verify(&mut self, bullet_proof: &BulletProof<C>, target: C) {
        let n = self.gens.g.len();
        let num_rounds = (n as f64).log2() as usize;

        assert_eq!(bullet_proof.L_vec.len(), num_rounds);
        assert_eq!(bullet_proof.R_vec.len(), num_rounds);

        let mut challenges = Vec::with_capacity(num_rounds);
        let mut challenges_inv = Vec::with_capacity(num_rounds);

        for i in 0..num_rounds {
            self.transcript
                .append_points(&[bullet_proof.L_vec[i], bullet_proof.R_vec[i]]);

            let x = self.transcript.squeeze(1)[0];
            challenges.push(x);
            challenges_inv.push(x.invert().unwrap());
        }

        let mut g_reduced = self.gens.g.clone();
        let mut h_reduced = self.gens.h.clone();

        let mut n_reduce = n;
        for i in 0..num_rounds {
            n_reduce /= 2;
            let mut g_updated = Vec::<C>::with_capacity(n_reduce);
            let mut h_updated = Vec::<C>::with_capacity(n_reduce);

            for j in 0..n_reduce {
                g_updated.push(
                    (g_reduced[j] * challenges_inv[i] + g_reduced[j + n_reduce] * challenges[i])
                        .into(),
                );
                h_updated.push(
                    (h_reduced[j] * challenges[i] + h_reduced[j + n_reduce] * challenges_inv[i])
                        .into(),
                );
            }

            g_reduced = g_updated;
            h_reduced = h_updated;
        }

        assert_eq!(g_reduced.len(), 1);
        assert_eq!(h_reduced.len(), 1);

        // TODO: Make this work!
        /*
        let s = Self::compute_scalar(&challenges, &challenges_inv);
        assert_eq!(s.len(), n);

        let a_s = s.iter().map(|s_i| bullet_proof.a * s_i);
        let b_s = s.iter().map(|s_i| bullet_proof.b * s_i);

        let g_a_s = multiexp(
            &a_s.enumerate()
                .map(|(i, a_s_i)| (a_s_i, self.gens.g[i].into()))
                .collect::<Vec<(C::ScalarExt, C::Curve)>>(),
        );

        let h_b_s = multiexp(
            &b_s.enumerate()
                .map(|(i, b_s_i)| (b_s_i, self.gens.h[n - i - 1].into()))
                .collect::<Vec<(C::ScalarExt, C::Curve)>>(),
        );

        let lhs = g_a_s + h_b_s + u_a_b;
         */

        let c = bullet_proof.a * bullet_proof.b;
        let u_a_b = self.gens.u * c;

        let lhs = g_reduced[0] * bullet_proof.a + h_reduced[0] * bullet_proof.b + u_a_b;
        let mut rhs: C::Curve = target.into();

        for i in 0..num_rounds {
            rhs += bullet_proof.L_vec[i] * challenges[i] * challenges[i];
            rhs += bullet_proof.R_vec[i] * challenges_inv[i] * challenges_inv[i];
        }

        assert_eq!(lhs, rhs);
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use halo2curves::secq256k1::{Fq, Secq256k1, Secq256k1Affine};
    use halo2curves::{CurveAffine, FieldExt};
    use poseidon_transcript::sponge::SpongeCurve;

    #[test]
    fn test_bullet() {
        type C = Secq256k1Affine;
        type Scalar = Fq;
        type Curve = Secq256k1;

        let n: usize = 16;
        let gens = Gens::new(n.next_power_of_two());

        let prover_transcript = PoseidonTranscript::<C>::new(b"BulletProof", SpongeCurve::K256);
        let mut bullet_prover = BulletProver::new(gens.clone(), prover_transcript);

        let mut a = Vec::with_capacity(n);
        let mut b = Vec::with_capacity(n);

        for i in 0..n {
            a.push(<C as CurveAffine>::ScalarExt::from_u128((i + 20) as u128));
            b.push(<C as CurveAffine>::ScalarExt::from_u128(
                (n - i + 10) as u128,
            ));
        }

        let c = BulletProver::<C>::dot_prod(&a, &b);

        let target = multiexp(
            &a.iter()
                .zip(gens.g.iter())
                .map(|(a_i, g_i)| (*a_i, (*g_i).into()))
                .collect::<Vec<(Scalar, Curve)>>(),
        ) + multiexp(
            &b.iter()
                .zip(gens.h.iter())
                .map(|(b_i, h_i)| (*b_i, (*h_i).into()))
                .collect::<Vec<(Scalar, Curve)>>(),
        ) + gens.u * c;

        let proof = bullet_prover.prove(&a, &b, &target.into());

        let verifier_transcript = PoseidonTranscript::<C>::new(b"BulletProof", SpongeCurve::K256);
        let mut verifier = BulletVerifier::new(gens, verifier_transcript);
        verifier.verify(&proof, target.into());
    }
}
