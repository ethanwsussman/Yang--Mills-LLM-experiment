import YangMills.Construction.Lattice.PropertiesOfTheFourLocalMaps
import Mathlib
set_option autoImplicit false
open Set
open scoped ENNReal
noncomputable section
namespace YangMills.Construction.SequenceTriples
open PeriodicLattice SeparatedSequences SeparatedRegions
def SourceCommutatorBoundedBy (L : ℕ) (c : ℝ) : Prop :=
  ∀ (m : ℕ) (S : ScaleData) (Ω : ℕ → Set (FourTorus L m)) (g : ℝ) (A : Set (FourTorus L m))
    (U J : FineBond L m S → Matrices.ComplexMatrix2) (V : LeveledBond L m S → Matrices.ComplexMatrix2)
    (h : FourTorus L m → ℝ) (θ : ℝ),
    IsDoubledMapsHypothesis S Ω g A U J V → IsCommutatorTestFunction S Ω h θ →
      ∀ y ∈ layerPoints S Ω, ∀ Ψ ∈ reducedTupleSpace S Ω,
        reducedSourceSeminormAt S Ω y
            (sourceCommutator S Ω (firstMemberRestriction S Ω U) h Ψ) ≤
          ENNReal.ofReal (c * θ⁻¹) *
            ⨆ (z : FourTorus L m) (_ : IsNearbyTop S Ω y z),
              reducedSolutionSeminormAt S Ω (firstMemberRestriction S Ω U) z Ψ
def sourceCommutatorLeastConstant (L : ℕ) : ℝ :=
  sInf {c : ℝ | 0 ≤ c ∧ SourceCommutatorBoundedBy L c}
end YangMills.Construction.SequenceTriples
end
