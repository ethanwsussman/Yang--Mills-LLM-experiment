import YangMills.Construction.Lattice.CommutatorsOfTheSystemWithAFunction
import YangMills.Construction.Lattice.DifferencesOfTheSystemAtASmallTriple
import YangMills.Construction.Lattice.InverseOfTheSystemAtLayerZero
import YangMills.Construction.Lattice.MapsOfTheDoubledSystemAndItsLocalForms
import YangMills.Construction.Lattice.PropertiesOfTheDoubledSystem
import Mathlib
set_option autoImplicit false
open scoped ENNReal
noncomputable section
namespace YangMills.Construction
open Set PeriodicLattice SeparatedSequences SeparatedRegions
namespace SequenceTriples
variable {L m : ℕ} (S : ScaleData) (Ω : ℕ → Set (FourTorus L m))
def IsDoubledMapsHypothesis (g : ℝ) (𝔸 : Set (FourTorus L m))
    (U J : FineBond L m S → Matrices.ComplexMatrix2)
    (j : LeveledBond L m S → Matrices.ComplexMatrix2) : Prop :=
  IsSmallInTrivialGauge S Ω g (smallTripleRadius L) 𝔸 U J j ∨
    j = 0 ∧ ∃ (Y : Set (FourTorus L m)) (U₀ A' : FineBond L m S → Matrices.ComplexMatrix2),
      Ω = singleRegionSequence Y ∧
        IsLayerZeroData S (baseLayerSmallness L) g Y 𝔸 U J U₀ A'
structure CouplingLocalDivergence (c β : ℝ) (W : FineBond L m S → Matrices.ComplexMatrix2) :
    Prop where
  eq : ∀ Ψ' ∈ reducedTupleSpace S Ω, couplingTerm S Ω W Ψ' =
    reducedAugmentedSourceEmbedding S Ω W (sourceFieldEmbedding S Ω W Ψ')
  seminorm_le : ∀ y ∈ layerPoints S Ω, ∀ Ψ' ∈ reducedTupleSpace S Ω,
    reducedAugmentedSourceSeminormAt S Ω y (sourceFieldEmbedding S Ω W Ψ') ≤
      ENNReal.ofReal c *
        ⨆ (y'' : FourTorus L m) (_ : IsNearbyTop S Ω y y''),
          reducedSolutionSeminormAt S Ω W y'' Ψ'
  hoelderSeminorm_le : ∀ y ∈ layerPoints S Ω, ∀ Ψ' ∈ reducedTupleSpace S Ω,
    reducedAugmentedSourceHoelderSeminormAt S Ω β W y (sourceFieldEmbedding S Ω W Ψ') ≤
      ENNReal.ofReal c *
        ⨆ (y'' : FourTorus L m) (_ : IsNearbyTop S Ω y y''),
          reducedSolutionStrongHoelderSeminormAt S Ω β W y'' Ψ'
structure CouplingCommutatorLocal (c ϑ : ℝ) (W : FineBond L m S → Matrices.ComplexMatrix2)
    (θ : FourTorus L m → ℝ) : Prop where
  eq : ∀ Ψ' ∈ reducedTupleSpace S Ω,
    couplingTerm S Ω W (reducedTupleSmul S θ Ψ') -
        reducedTupleSmul S θ (couplingTerm S Ω W Ψ') =
      reducedSourceEmbedding S Ω W (sourceCommutator S Ω W θ Ψ')
  seminorm_le : ∀ y ∈ layerPoints S Ω, ∀ Ψ' ∈ reducedTupleSpace S Ω,
    reducedSourceSeminormAt S Ω y (sourceCommutator S Ω W θ Ψ') ≤
      ENNReal.ofReal (c * ϑ⁻¹) *
        ⨆ (y'' : FourTorus L m) (_ : IsNearbyTop S Ω y y''),
          reducedSolutionSeminormAt S Ω W y'' Ψ'
  seminorm_eq_zero : ∀ y ∈ layerPoints S Ω, IsLocallyConstantAt S Ω θ y →
    ∀ Ψ' ∈ reducedTupleSpace S Ω,
      reducedSourceSeminormAt S Ω y (sourceCommutator S Ω W θ Ψ') = 0
structure WeakCouplingCommutatorLocal (c β ϑ : ℝ) (W : FineBond L m S → Matrices.ComplexMatrix2)
    (θ : FourTorus L m → ℝ) : Prop where
  eq : ∀ Ψ' ∈ reducedTupleSpace S Ω,
    couplingTerm S Ω W (reducedTupleSmul S θ Ψ') -
        reducedTupleSmul S θ (couplingTerm S Ω W Ψ') =
      reducedAugmentedSourceEmbedding S Ω W (weakSourceCommutator S Ω W θ Ψ')
  seminorm_le : ∀ y ∈ layerPoints S Ω, ∀ Ψ' ∈ reducedTupleSpace S Ω,
    reducedAugmentedSourceHoelderSeminormAt S Ω β W y (weakSourceCommutator S Ω W θ Ψ') ≤
      ENNReal.ofReal (c * ϑ⁻¹) *
        ⨆ (y'' : FourTorus L m) (_ : IsNearbyTop S Ω y y''),
          reducedSolutionWeakHoelderSeminormAt S Ω β W y'' Ψ'
  seminorm_eq_zero : ∀ y ∈ layerPoints S Ω, IsLocallyConstantAt S Ω θ y →
    ∀ Ψ' ∈ reducedTupleSpace S Ω,
      reducedAugmentedSourceHoelderSeminormAt S Ω β W y (weakSourceCommutator S Ω W θ Ψ') = 0
section Operators
variable [∀ (n : ℕ) (c : BondAtLevel L m S.levels (n + 1)),
  Fintype (PositiveBondsOf (doubleBlockSymmetricSet c))]
structure IsResidualMap (c : ℝ) (𝔸 : Set (FourTorus L m))
    (U J : FineBond L m S → Matrices.ComplexMatrix2)
    (j : LeveledBond L m S → Matrices.ComplexMatrix2)
    (T : ReducedTuple L m S × ReducedSourceTuple L m S → ReducedAugmentedSourceTuple L m S) :
    Prop where
  isLinear : IsLinearOnSets (reducedTupleSpace S Ω ×ˢ reducedSourceTupleSpace S Ω)
    (reducedAugmentedSourceTupleSpace S Ω) T
  eq : ∀ Ψ' ∈ reducedTupleSpace S Ω, ∀ g' ∈ reducedSourceTupleSpace S Ω,
    secondCopyResidual S Ω 𝔸 U J j Ψ'.2.1 g'.1.2.1 g'.1.2.2.2.1 =
      reducedAugmentedSourceEmbedding S Ω (firstMemberRestriction S Ω U) (T (Ψ', g'))
  seminorm_le : ∀ y ∈ layerPoints S Ω, ∀ Ψ' ∈ reducedTupleSpace S Ω,
    ∀ g' ∈ reducedSourceTupleSpace S Ω,
      reducedAugmentedSourceSeminormAt S Ω y (T (Ψ', g')) ≤
        ENNReal.ofReal c *
          ⨆ (y'' : FourTorus L m) (_ : IsNearbyTop S Ω y y''),
            reducedWeakSeminormAt S Ω (firstMemberRestriction S Ω U) y'' Ψ' ⊔
              reducedSourceSeminormAt S Ω y'' g'
structure DoubledMapsLocal (c β ϑ : ℝ) (𝔸 : Set (FourTorus L m))
    (U J : FineBond L m S → Matrices.ComplexMatrix2)
    (j : LeveledBond L m S → Matrices.ComplexMatrix2) (θ : FourTorus L m → ℝ) : Prop where
  coupling : CouplingLocalDivergence S Ω c β (firstMemberRestriction S Ω U)
  residual : ∃ T, IsResidualMap S Ω c 𝔸 U J j T
  commutator : CouplingCommutatorLocal S Ω c ϑ (firstMemberRestriction S Ω U) θ
  weakCommutator : WeakCouplingCommutatorLocal S Ω c β ϑ (firstMemberRestriction S Ω U) θ
end Operators
end SequenceTriples
end YangMills.Construction
end
