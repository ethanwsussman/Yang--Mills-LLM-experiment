import YangMills.Construction.RunningCouplingSlope.TorusViewedOnATower
import Mathlib
set_option autoImplicit false
open Filter
open scoped Topology
noncomputable section
namespace YangMills.Construction.RunningCouplingSlope
open Tower
def ChainLogWeightIndependent : Prop :=
  ∀ a : ℝ, 0 < a → ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∀ k n : ℕ, 1 ≤ k → 0 < n →
    ∀ᶠ V in 𝓝 (TorusFields.trivialField (2 * L ^ n)),
      ∀ U : Edge L n k k → Matrices.ComplexMatrix2, RepresentsTorusField U V →
      ∀ X X' : ChainPoint L n k, IsMinimizerOver a U X → IsMinimizerOver a U X' →
        ∀ (Y Y' : Type) [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [FiniteDimensional ℝ Y]
          [NormedAddCommGroup Y'] [InnerProductSpace ℝ Y'] [FiniteDimensional ℝ Y']
          (l : LevelForms L n k →ₗ[ℝ] Y) (l' : LevelForms L n k →ₗ[ℝ] Y'),
          IsTransversalSlice X l → IsTransversalSlice X' l' →
            chainLogWeight a X l = chainLogWeight a X' l'
end YangMills.Construction.RunningCouplingSlope
end
