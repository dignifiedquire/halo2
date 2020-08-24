//! This module provides an implementation of a variant of (Turbo)[PLONK][plonk]
//! that is designed specifically for the polynomial commitment scheme described
//! in the [Halo][halo] paper.
//!
//! [halo]: https://eprint.iacr.org/2019/1021
//! [plonk]: https://eprint.iacr.org/2019/953

use crate::arithmetic::CurveAffine;
use crate::polycommit::OpeningProof;
use crate::transcript::Hasher;

#[macro_use]
mod circuit;
mod domain;
mod prover;
mod srs;
mod verifier;

pub use circuit::*;
pub use prover::*;
pub use srs::*;
pub use verifier::*;

use domain::EvaluationDomain;

// TODO: remove this
const GATE_DEGREE: u32 = 3;

/// This is a structured reference string (SRS) that is (deterministically)
/// computed from a specific circuit and parameters for the polynomial
/// commitment scheme.
#[derive(Debug)]
pub struct SRS<C: CurveAffine> {
    sa: (Vec<C::Scalar>, Vec<C::Scalar>),
    sb: (Vec<C::Scalar>, Vec<C::Scalar>),
    sc: (Vec<C::Scalar>, Vec<C::Scalar>),
    sd: (Vec<C::Scalar>, Vec<C::Scalar>),
    sm: (Vec<C::Scalar>, Vec<C::Scalar>),
    sa_commitment: C,
    sb_commitment: C,
    sc_commitment: C,
    sd_commitment: C,
    sm_commitment: C,
    domain: EvaluationDomain<C::Scalar>,
}

/// This is an object which represents a (Turbo)PLONK proof.
#[derive(Debug, Clone)]
pub struct Proof<C: CurveAffine> {
    a_commitment: C,
    b_commitment: C,
    c_commitment: C,
    d_commitment: C,
    h_commitments: Vec<C>,
    a_eval_x: C::Scalar,
    b_eval_x: C::Scalar,
    c_eval_x: C::Scalar,
    d_eval_x: C::Scalar,
    sa_eval_x: C::Scalar,
    sb_eval_x: C::Scalar,
    sc_eval_x: C::Scalar,
    sd_eval_x: C::Scalar,
    sm_eval_x: C::Scalar,
    h_evals_x: Vec<C::Scalar>,
    opening: OpeningProof<C>,
}

/// This is an error that could occur during proving or circuit synthesis.
// TODO: these errors need to be cleaned up
#[derive(Debug)]
pub enum Error {
    /// This is an error that can occur during synthesis of the circuit, for
    /// example, when the witness is not present.
    SynthesisError,
    /// The structured reference string or the parameters are not compatible
    /// with the circuit being synthesized.
    IncompatibleParams,
    /// The constraint system is not satisfied.
    ConstraintSystemFailure,
}

fn hash_point<C: CurveAffine, H: Hasher<C::Base>>(
    transcript: &mut H,
    point: &C,
) -> Result<(), Error> {
    let tmp = point.get_xy();
    if bool::from(tmp.is_none()) {
        return Err(Error::SynthesisError);
    };
    let tmp = tmp.unwrap();
    transcript.absorb(tmp.0);
    transcript.absorb(tmp.1);
    Ok(())
}

#[test]
fn test_proving() {
    use crate::arithmetic::{EqAffine, Field, Fp, Fq};
    use crate::polycommit::Params;
    use crate::transcript::DummyHash;
    const K: u32 = 5;

    // Initialize the polynomial commitment parameters
    let params: Params<EqAffine> = Params::new::<DummyHash<Fq>>(K);

    struct MyCircuit<F: Field> {
        a: Option<F>,
    }

    impl<F: Field> Circuit<F> for MyCircuit<F> {
        fn synthesize(&self, cs: &mut impl ConstraintSystem<F>) -> Result<(), Error> {
            for _ in 0..10 {
                let (_, _, _, _) = cs.multiply(|| {
                    let a = self.a.ok_or(Error::SynthesisError)?;
                    let a2 = a.square();
                    Ok((a, a, a2))
                })?;
                //cs.copy(a, b);
                let (_, _, _, _) = cs.add(|| {
                    let a = self.a.ok_or(Error::SynthesisError)?;
                    let a2 = a.square();
                    let a3 = a + a2;
                    Ok((a, a2, a3))
                })?;
                //cs.copy(a, d);
                //cs.copy(c, e);
            }

            Ok(())
        }
    }

    let circuit: MyCircuit<Fp> = MyCircuit {
        a: Some((-Fp::from_u64(2) + Fp::ROOT_OF_UNITY).pow(&[100, 0, 0, 0])),
    };

    // Initialize the SRS
    let srs = SRS::generate(&params, &circuit).expect("SRS generation should not fail");

    // Create a proof
    let proof = Proof::create::<DummyHash<Fq>, DummyHash<Fp>, _>(&params, &srs, &circuit)
        .expect("proof generation should not fail");

    assert!(proof.verify::<DummyHash<Fq>, DummyHash<Fp>>(&params, &srs));
}