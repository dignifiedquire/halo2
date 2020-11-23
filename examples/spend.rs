use halo2::arithmetic::*;
use halo2::gadgets::num::*;
use halo2::gadgets::*;
use halo2::plonk::*;
use halo2::poly::commitment::Params;
use halo2::transcript::*;
use halo2::tweedle::*;
struct SpendCircuit<F> {
    x: Option<F>,
}

use std::time::Instant;

impl<F: Field> Circuit<F> for SpendCircuit<F> {
    type Config = StandardConfig;

    fn configure(meta: &mut ConstraintSystem<F>) -> StandardConfig {
        StandardConfig::new(meta)
    }

    fn synthesize(
        &self,
        cs: &mut impl Assignment<F>,
        config: StandardConfig,
    ) -> Result<(), Error> {
        let mut cs = Standard::new(cs, config);

        let mut x = AllocatedNum::alloc(&mut cs, || Ok(self.x.ok_or(Error::SynthesisError)?))?;
        for _ in 0..1000 {
            x = x.mul(&mut cs, &x)?;
            x = x.add(&mut cs, &x)?;
        }

        Ok(())
    }
}

fn main() {
    const K: u32 = 11;

    // Initialize the polynomial commitment parameters
    println!("Initializing polynomial commitment parameters");
    let params: Params<EqAffine> = Params::new::<DummyHash<Fq>>(K);

    let empty_circuit: SpendCircuit<Fp> = SpendCircuit { x: None };

    // Initialize the SRS
    println!("Keygeneration");
    let pk = keygen(&params, &empty_circuit).expect("keygen should not fail");

    // Create a proof
    {
        let circuit = SpendCircuit {
            x: Some(Fp::from_u64(2)),
        };

        println!("Creating proof");
        let start = Instant::now();
        let proof = Proof::create::<DummyHash<Fq>, DummyHash<Fp>, _>(
            &params,
            &pk,
            &circuit,
            &[],
        ).expect("proof generation should not fail");
        let elapsed = start.elapsed();
        println!("Proof created in {:?}", elapsed);


        let msm = params.empty_msm();
        
        println!("Verifying proof");
        let start = Instant::now();
        let guard = proof.verify::<DummyHash<Fq>, DummyHash<Fp>>(
            &params,
            &pk.get_vk(),
            msm,
            &[],
        ).expect("proof verifiation should not fail");
        // TODO: is this the right check?
        {
            let msm = guard.clone().use_challenges();
            assert!(msm.eval());
        }
        {
            let g = guard.compute_g();
            let (msm, _) = guard.clone().use_g(g);
            assert!(msm.eval());
        }
        let elapsed = start.elapsed();
        println!("Proof verified in {:?}", elapsed);
    }
}
