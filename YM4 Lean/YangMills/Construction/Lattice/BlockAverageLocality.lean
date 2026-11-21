import YangMills.Construction.Conventions.StandingParameters
import YangMills.Construction.Lattice.BlockAveraging
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.PeriodicLattice
def BlockAverageDependsOnDoubleBlock : Prop :=
  ∀ L m K k : ℕ, Conventions.IsAdmissibleBlockingFactor L → 0 < m → k < K →
    ∀ (ω : ℝ) (c : BondAtLevel L m K (k + 1)) (U U' : BondAtLevel L m K k → Matrices.ComplexMatrix2),
      (∀ b ∈ (bondsInDoubleBlock c : Set (BondAtLevel L m K k)), U b = U' b) →
        blockAverage ω U c = blockAverage ω U' c
end YangMills.Construction.PeriodicLattice
end
