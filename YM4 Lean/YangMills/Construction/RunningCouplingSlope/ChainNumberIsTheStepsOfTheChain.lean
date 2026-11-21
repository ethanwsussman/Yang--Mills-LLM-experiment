import YangMills.Construction.RunningCouplingSlope.LeastChainOverAField
import YangMills.Construction.RunningCouplingSlope.TorusViewedOnATower
import Mathlib
set_option autoImplicit false
open Filter
open scoped Topology
noncomputable section
namespace YangMills.Construction.RunningCouplingSlope
open Tower
def ChainLogWeightEqStepLogSum : Prop :=
  ∀ a : ℝ, 0 < a → ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∀ k n : ℕ, 1 ≤ k → 0 < n →
    ∀ ρ : ℝ, 0 < ρ → ρ ≤ 1 → ∃ c : ℝ,
      ∀ᶠ V in 𝓝 (TorusFields.trivialField (2 * L ^ n)),
        ∀ U : Edge L n k k → Matrices.ComplexMatrix2, RepresentsTorusField U V →
        ∀ X : ChainPoint L n k, IsMinimizerOver a U X → RepresentsMinimizerChain a ρ V X →
          ∃ (Y : Type) (_ : NormedAddCommGroup Y) (_ : InnerProductSpace ℝ Y)
            (_ : FiniteDimensional ℝ Y) (l : LevelForms L n k →ₗ[ℝ] Y),
            IsTransversalSlice X l ∧
              chainLogWeight a X l = chainStepLogSum a ρ L k (2 * L ^ n) V + c
end YangMills.Construction.RunningCouplingSlope
end
