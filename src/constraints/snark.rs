use crate::constraints::{
    data_structures::{IndexVerifierKeyVar, PreparedIndexVerifierKeyVar, ProofVar},
    verifier::Marlin as MarlinVerifierGadget,
};
use crate::Error::IndexTooLarge;
use crate::{
    IndexProverKey, IndexVerifierKey, Marlin, MarlinConfig, PreparedIndexVerifierKey, Proof,
    String, ToString, UniversalSRS, Vec,
};
use ark_crypto_primitives::snark::{
    NonNativeFieldInputVar, UniversalSetupIndexError,
};
use ark_crypto_primitives::sponge::{CryptographicSponge, constraints::CryptographicSpongeVar};
use ark_ff::{PrimeField, ToConstraintField};
use ark_poly::univariate::DensePolynomial;
use ark_poly_commit::{PCCheckVar, PolynomialCommitment};
use ark_r1cs_std::{bits::boolean::Boolean, ToConstraintFieldGadget};
use ark_relations::lc;
use ark_relations::r1cs::{
    ConstraintSynthesizer, ConstraintSystemRef, LinearCombination, SynthesisError, Variable,
};
use ark_std::cmp::min;
use ark_std::fmt::{Debug, Formatter};
use ark_std::marker::PhantomData;
use ark_std::{
    boxed::Box,
    rand::{CryptoRng, RngCore},
    test_rng,
};

#[derive(Clone, PartialEq, PartialOrd)]
pub struct MarlinBound {
    pub max_degree: usize,
}

impl Default for MarlinBound {
    fn default() -> Self {
        Self { max_degree: 200000 }
    }
}

impl Debug for MarlinBound {
    fn fmt(&self, f: &mut Formatter<'_>) -> core::fmt::Result {
        write!(f, "{}", self.max_degree)
    }
}

pub struct MarlinSNARK<
    F: PrimeField,
    FSF: PrimeField,
    PC: PolynomialCommitment<F, DensePolynomial<F>, S>,
    S: CryptographicSponge + Default + RngCore,
    MC: MarlinConfig,
> {
    f_phantom: PhantomData<F>,
    fsf_phantom: PhantomData<FSF>,
    pc_phantom: PhantomData<PC>,
    s_phantom: PhantomData<S>,
    mc_phantom: PhantomData<MC>,
}

impl<F, FSF, PC, S, MC> MarlinSNARK<F, FSF, PC, S, MC>
where
    F: PrimeField,
    FSF: PrimeField,
    PC: PolynomialCommitment<F, DensePolynomial<F>, S>,
    S: CryptographicSponge + Default + RngCore,
    MC: MarlinConfig,
    PC::VerifierKey: ToConstraintField<FSF>,
    PC::Commitment: ToConstraintField<FSF>,
{
    fn circuit_specific_setup<C: ConstraintSynthesizer<F>, R: RngCore + CryptoRng>(
        circuit: C,
        rng: &mut R,
    ) -> Result<(IndexProverKey<F, PC, S>, IndexVerifierKey<F, PC, S>), Box<MarlinError>> {
        Ok(Marlin::<F, FSF, PC, S, MC>::circuit_specific_setup(circuit, rng).unwrap())
    }

    fn prove<C: ConstraintSynthesizer<F>, R: RngCore + CryptographicSponge>(
        pk: &IndexProverKey<F, PC, S>,
        circuit: C,
        rng: &mut R,
    ) -> Result<Proof<F, PC, S>, Box<MarlinError>> {
        match Marlin::<F, FSF, PC, S, MC>::prove(&pk, circuit, rng) {
            Ok(res) => Ok(res),
            Err(e) => Err(Box::new(MarlinError::from(e))),
        }
    }

    fn verify<R: RngCore>(vk: &IndexVerifierKey<F, PC, S>, x: &[F], proof: &Proof<F, PC, S>, rng: &mut R) -> Result<bool, Box<MarlinError>> {
        match Marlin::<F, FSF, PC, S, MC>::verify(vk, x, proof, rng) {
            Ok(res) => Ok(res),
            Err(e) => Err(Box::new(MarlinError::from(e))),
        }
    }

    fn process_vk(vk: &IndexVerifierKey<F, PC, S>) -> Result<PreparedIndexVerifierKey<F, PC, S>, Box<MarlinError>> {
        let prepared_vk = PreparedIndexVerifierKey::prepare(vk);
        Ok(prepared_vk)
    }

    fn verify_with_processed_vk<R: RngCore>(
        pvk: &PreparedIndexVerifierKey<F, PC, S>,
        x: &[F],
        proof: &Proof<F, PC, S>,
        rng: &mut R,
    ) -> Result<bool, Box<MarlinError>> {
        match Marlin::<F, FSF, PC, S, MC>::prepared_verify(pvk, x, proof, rng) {
            Ok(res) => Ok(res),
            Err(e) => Err(Box::new(MarlinError::from(e))),
        }
    }

    fn universal_setup<R: RngCore>(
        bound: &MarlinBound,
        rng: &mut R,
    ) -> Result<(MarlinBound, UniversalSRS<F, PC, S>), Box<MarlinError>> {
        let MarlinBound { max_degree } = bound;

        match Marlin::<F, FSF, PC, S, MC>::universal_setup(1, 1, (max_degree + 5) / 3, rng) {
            Ok(res) => Ok((bound.clone(), res)),
            Err(e) => Err(Box::new(MarlinError::from(e))),
        }
    }

    #[allow(clippy::type_complexity)]
    fn index<C: ConstraintSynthesizer<F>, R: RngCore>(
        crs: &(MarlinBound, UniversalSRS<F, PC, S>),
        circuit: C,
        _rng: &mut R,
    ) -> Result<
        (IndexProverKey<F, PC, S>, IndexVerifierKey<F, PC, S>),
        UniversalSetupIndexError<MarlinBound, Box<MarlinError>>,
    > {
        let index_res = Marlin::<F, FSF, PC, S, MC>::index(&crs.1, circuit);
        match index_res {
            Ok(res) => Ok(res),
            Err(err) => match err {
                IndexTooLarge(v) => Err(UniversalSetupIndexError::NeedLargerBound(MarlinBound {
                    max_degree: v,
                })),
                _ => Err(UniversalSetupIndexError::Other(Box::new(
                    MarlinError::from(err),
                ))),
            },
        }
    }
}

pub struct MarlinSNARKGadget<F, FSF, PC, S, MC, PCG, SV>
where
    F: PrimeField,
    FSF: PrimeField,
    PC: PolynomialCommitment<F, DensePolynomial<F>, S>,
    S: CryptographicSponge,
    MC: MarlinConfig,
    PCG: PCCheckVar<F, DensePolynomial<F>, PC, FSF, S>,
    SV: CryptographicSpongeVar<FSF, S>,
{
    pub f_phantom: PhantomData<F>,
    pub fsf_phantom: PhantomData<FSF>,
    pub pc_phantom: PhantomData<PC>,
    pub fs_phantom: PhantomData<S>,
    pub mc_phantom: PhantomData<MC>,
    pub pcg_phantom: PhantomData<PCG>,
    pub fsg_phantom: PhantomData<SV>,
}

impl<F, FSF, PC, S, MC, PCG, SV> MarlinSNARKGadget<F, FSF, PC, S, MC, PCG, SV>
where
    F: PrimeField,
    FSF: PrimeField,
    PC: PolynomialCommitment<F, DensePolynomial<F>, S>,
    S: CryptographicSponge + Default + RngCore,
    MC: MarlinConfig,
    PCG: PCCheckVar<F, DensePolynomial<F>, PC, FSF, S>,
    SV: CryptographicSpongeVar<FSF, S>,
    PC::VerifierKey: ToConstraintField<FSF>,
    PC::Commitment: ToConstraintField<FSF>,
    PCG::VerifierKeyVar: ToConstraintFieldGadget<FSF>,
    PCG::CommitmentVar: ToConstraintFieldGadget<FSF>,
{
    fn verifier_size(
        circuit_vk: &IndexVerifierKey<F, PC, S>,
    ) -> usize {
        circuit_vk.index_info.num_instance_variables
    }

    #[tracing::instrument(target = "r1cs", skip(circuit_pvk, x, proof))]
    fn verify_with_processed_vk(
        circuit_pvk: &PreparedIndexVerifierKeyVar<F, FSF, PC, PCG, S, SV>,
        x: &NonNativeFieldInputVar<F, FSF>,
        proof: &ProofVar<F, FSF, PC, PCG, S>,
    ) -> Result<Boolean<FSF>, SynthesisError> {
        Ok(
            MarlinVerifierGadget::<F, FSF, PC, PCG, S, SV>::prepared_verify(&circuit_pvk, &x.val, proof)
                .unwrap(),
        )
    }

    #[tracing::instrument(target = "r1cs", skip(circuit_vk, x, proof))]
    fn verify(
        circuit_vk: &IndexVerifierKeyVar<F, FSF, PC, PCG, S>,
        x: &NonNativeFieldInputVar<F, FSF>,
        proof: &ProofVar<F, FSF, PC, PCG, S>,
    ) -> Result<Boolean<FSF>, SynthesisError> {
        Ok(
            MarlinVerifierGadget::<F, FSF, PC, PCG, S, SV>::verify(circuit_vk, &x.val, proof)
                .unwrap(),
        )
    }
}

#[derive(Clone)]
pub struct MarlinBoundCircuit<F: PrimeField> {
    pub bound: MarlinBound,
    pub fsf_phantom: PhantomData<F>,
}

impl<F: PrimeField> From<MarlinBound> for MarlinBoundCircuit<F> {
    fn from(bound: MarlinBound) -> Self {
        Self {
            bound,
            fsf_phantom: PhantomData,
        }
    }
}

impl<F: PrimeField> ConstraintSynthesizer<F> for MarlinBoundCircuit<F> {
    #[tracing::instrument(target = "r1cs", skip(self))]
    fn generate_constraints(self, cs: ConstraintSystemRef<F>) -> Result<(), SynthesisError> {
        let MarlinBound { max_degree } = self.bound;

        let num_variables = max_degree / 3;
        let num_constraints = max_degree / 3;

        let mut vars: Vec<Variable> = vec![];
        for _ in 0..num_variables - 1 {
            let var_i = cs.new_witness_variable(|| Ok(F::zero()))?;
            vars.push(var_i);
        }

        let mut rng = test_rng();

        let mut non_zero_remaining = (max_degree + 5) / 3;
        for _ in 0..num_constraints {
            if non_zero_remaining > 0 {
                let num_for_this_constraint = min(non_zero_remaining, num_variables - 1);

                let mut lc_a = LinearCombination::zero();
                let mut lc_b = LinearCombination::zero();
                let mut lc_c = LinearCombination::zero();

                for var in vars.iter().take(num_for_this_constraint) {
                    lc_a += (F::rand(&mut rng), *var);
                    lc_b += (F::rand(&mut rng), *var);
                    lc_c += (F::rand(&mut rng), *var);
                }

                cs.enforce_constraint(lc_a, lc_b, lc_c)?;

                non_zero_remaining -= num_for_this_constraint;
            } else {
                cs.enforce_constraint(lc!(), lc!(), lc!())?;
            }
        }

        Ok(())
    }
}

impl<F, FSF, PC, S, MC, PCG, SV> MarlinSNARKGadget<F, FSF, PC, S, MC, PCG, SV>
where
    F: PrimeField,
    FSF: PrimeField,
    PC: PolynomialCommitment<F, DensePolynomial<F>, S>,
    S: CryptographicSponge + Default + RngCore,
    MC: MarlinConfig,
    PCG: PCCheckVar<F, DensePolynomial<F>, PC, FSF, S>,
    SV: CryptographicSpongeVar<FSF, S>,
    PC::VerifierKey: ToConstraintField<FSF>,
    PC::Commitment: ToConstraintField<FSF>,
    PCG::VerifierKeyVar: ToConstraintFieldGadget<FSF>,
    PCG::CommitmentVar: ToConstraintFieldGadget<FSF>,
{
    // type BoundCircuit = MarlinBoundCircuit<F>;
}

pub struct MarlinError {
    pub error_msg: String,
}

impl<E> From<crate::Error<E>> for MarlinError
where
    E: ark_std::error::Error,
{
    fn from(e: crate::Error<E>) -> Self {
        match e {
            IndexTooLarge(v) => Self {
                error_msg: format!("index too large, needed degree {}", v),
            },
            crate::Error::<E>::AHPError(err) => match err {
                crate::ahp::Error::MissingEval(str) => Self {
                    error_msg: String::from("missing eval: ") + &*str,
                },
                crate::ahp::Error::InvalidPublicInputLength => Self {
                    error_msg: String::from("invalid public input length"),
                },
                crate::ahp::Error::InstanceDoesNotMatchIndex => Self {
                    error_msg: String::from("instance does not match index"),
                },
                crate::ahp::Error::NonSquareMatrix => Self {
                    error_msg: String::from("non-sqaure matrix"),
                },
                crate::ahp::Error::ConstraintSystemError(error) => Self {
                    error_msg: error.to_string(),
                },
            },
            crate::Error::<E>::R1CSError(err) => Self {
                error_msg: err.to_string(),
            },
            crate::Error::<E>::PolynomialCommitmentError(err) => Self {
                error_msg: err.to_string(),
            },
        }
    }
}

impl Debug for MarlinError {
    fn fmt(&self, f: &mut Formatter<'_>) -> core::fmt::Result {
        write!(f, "{}", self.error_msg)
    }
}

impl core::fmt::Display for MarlinError {
    fn fmt(&self, f: &mut Formatter<'_>) -> core::fmt::Result {
        write!(f, "{}", self.error_msg)
    }
}

impl ark_std::error::Error for MarlinError {}

#[cfg(test)]
mod test {
    use crate::{MarlinConfig, SimplePoseidonRng};
    #[derive(Clone)]
    struct TestMarlinConfig;
    impl MarlinConfig for TestMarlinConfig {
        const FOR_RECURSION: bool = true;
    }

    #[derive(Copy, Clone, Debug)]
    struct Mnt64298cycle;
    impl CurveCycle for Mnt64298cycle {
        type E1 = <MNT6_298 as Pairing>::G1;
        type E2 = <MNT4_298 as Pairing>::G1;
    }
    impl PairingFriendlyCycle for Mnt64298cycle {
        type Engine1 = MNT6_298;
        type Engine2 = MNT4_298;
    }

    use crate::constraints::snark::{MarlinSNARK, MarlinSNARKGadget};
    use ark_crypto_primitives::snark::{SNARKGadget, SNARK};
    use ark_crypto_primitives::sponge::CryptographicSponge;
    use ark_crypto_primitives::sponge::constraints::CryptographicSpongeVar;
    use ark_crypto_primitives::sponge::poseidon::constraints::PoseidonSpongeVar;
    use ark_ec::{CurveCycle, pairing::Pairing, PairingFriendlyCycle};
    use ark_ff::{Field, UniformRand};
    use ark_mnt4_298::{
        constraints::PairingVar as MNT4PairingVar, Fq as MNT4Fq, Fr as MNT4Fr, MNT4_298,
    };
    use ark_mnt6_298::MNT6_298;
    use ark_poly_commit::marlin_pc::{MarlinKZG10, MarlinKZG10Gadget};
    use ark_r1cs_std::{alloc::AllocVar, bits::boolean::Boolean, eq::EqGadget};
    use ark_relations::{
        lc, ns,
        r1cs::{ConstraintSynthesizer, ConstraintSystem, ConstraintSystemRef, SynthesisError},
    };
    use core::ops::MulAssign;

    #[derive(Copy, Clone)]
    struct Circuit<F: Field> {
        a: Option<F>,
        b: Option<F>,
        num_constraints: usize,
        num_variables: usize,
    }

    impl<ConstraintF: Field> ConstraintSynthesizer<ConstraintF> for Circuit<ConstraintF> {
        fn generate_constraints(
            self,
            cs: ConstraintSystemRef<ConstraintF>,
        ) -> Result<(), SynthesisError> {
            let a = cs.new_witness_variable(|| self.a.ok_or(SynthesisError::AssignmentMissing))?;
            let b = cs.new_witness_variable(|| self.b.ok_or(SynthesisError::AssignmentMissing))?;
            let c = cs.new_input_variable(|| {
                let mut a = self.a.ok_or(SynthesisError::AssignmentMissing)?;
                let b = self.b.ok_or(SynthesisError::AssignmentMissing)?;

                a.mul_assign(&b);
                Ok(a)
            })?;

            for _ in 0..(self.num_variables - 3) {
                let _ =
                    cs.new_witness_variable(|| self.a.ok_or(SynthesisError::AssignmentMissing))?;
            }

            for _ in 0..self.num_constraints {
                cs.enforce_constraint(lc!() + a, lc!() + b, lc!() + c)
                    .unwrap();
            }
            Ok(())
        }
    }

    type TestSNARK = MarlinSNARK<
        MNT4Fr,
        MNT4Fq,
        MarlinKZG10<MNT4_298, DensePolynomial<MNT4Fr>, SimplePoseidonRng<MNT4Fq>>,
        SimplePoseidonRng<MNT4Fq>,
        TestMarlinConfig,
    >;
    type PCGadget4 = MarlinKZG10Gadget<Mnt64298cycle, DensePolynomial<MNT4Fr>, MNT4PairingVar, SimplePoseidonRng<MNT4Fq>>;
    type SV = PoseidonSpongeVar<MNT4Fq>;
    type TestSNARKGadget = MarlinSNARKGadget<
        MNT4Fr,
        MNT4Fq,
        MarlinKZG10<MNT4_298, DensePolynomial<MNT4Fr>, SimplePoseidonRng<MNT4Fq>>,
        SimplePoseidonRng<MNT4Fq>,
        TestMarlinConfig,
        PCGadget4,
        SV,
    >;

    use ark_poly::univariate::DensePolynomial;
    use ark_relations::r1cs::OptimizationGoal;

    #[test]
    fn marlin_snark_test() {
        let mut rng = ark_std::test_rng();
        let a = MNT4Fr::rand(&mut rng);
        let b = MNT4Fr::rand(&mut rng);
        let mut c = a;
        c.mul_assign(&b);

        let circ = Circuit {
            a: Some(a),
            b: Some(b),
            num_constraints: 100,
            num_variables: 25,
        };

        let (pk, vk) = TestSNARK::circuit_specific_setup(circ, &mut rng).unwrap();

        let proof = TestSNARK::prove(&pk, circ, &mut rng).unwrap();

        assert!(
            TestSNARK::verify(&vk, &[c], &proof).unwrap(),
            "The native verification check fails."
        );

        let cs_sys = ConstraintSystem::<MNT4Fq>::new();
        let cs = ConstraintSystemRef::new(cs_sys);
        cs.set_optimization_goal(OptimizationGoal::Weight);

        let input_gadget = <TestSNARKGadget as SNARKGadget<
            <MNT4_298 as Pairing>::ScalarField,
            <MNT4_298 as Pairing>::BaseField,
            TestSNARK,
        >>::InputVar::new_input(ns!(cs, "new_input"), || Ok(vec![c]))
        .unwrap();

        let proof_gadget = <TestSNARKGadget as SNARKGadget<
            <MNT4_298 as Pairing>::ScalarField,
            <MNT4_298 as Pairing>::BaseField,
            TestSNARK,
        >>::ProofVar::new_witness(ns!(cs, "alloc_proof"), || Ok(proof))
        .unwrap();
        let vk_gadget = <TestSNARKGadget as SNARKGadget<
            <MNT4_298 as Pairing>::ScalarField,
            <MNT4_298 as Pairing>::BaseField,
            TestSNARK,
        >>::VerifyingKeyVar::new_constant(ns!(cs, "alloc_vk"), vk.clone())
        .unwrap();

        assert!(
            cs.is_satisfied().unwrap(),
            "Constraints not satisfied: {}",
            cs.which_is_unsatisfied().unwrap().unwrap_or_default()
        );

        let verification_result = <TestSNARKGadget as SNARKGadget<
            <MNT4_298 as Pairing>::ScalarField,
            <MNT4_298 as Pairing>::BaseField,
            TestSNARK,
        >>::verify(&vk_gadget, &input_gadget, &proof_gadget)
        .unwrap();

        assert!(
            cs.is_satisfied().unwrap(),
            "Constraints not satisfied: {}",
            cs.which_is_unsatisfied().unwrap().unwrap_or_default()
        );

        verification_result
            .enforce_equal(&Boolean::Constant(true))
            .unwrap();

        assert!(
            cs.is_satisfied().unwrap(),
            "Constraints not satisfied: {}",
            cs.which_is_unsatisfied().unwrap().unwrap_or_default()
        );

        let pvk = TestSNARK::process_vk(&vk).unwrap();
        let pvk_gadget =
            <TestSNARKGadget as SNARKGadget<
                <MNT4_298 as Pairing>::ScalarField,
                <MNT4_298 as Pairing>::BaseField,
                TestSNARK,
            >>::ProcessedVerifyingKeyVar::new_constant(ns!(cs, "alloc_pvk"), pvk)
            .unwrap();
        TestSNARKGadget::verify_with_processed_vk(&pvk_gadget, &input_gadget, &proof_gadget)
            .unwrap()
            .enforce_equal(&Boolean::Constant(true))
            .unwrap();

        assert!(
            cs.is_satisfied().unwrap(),
            "Constraints not satisfied: {}",
            cs.which_is_unsatisfied().unwrap().unwrap_or_default()
        );
    }
}
