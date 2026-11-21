import YangMills.Construction.RunningCouplingSlope.LogarithmOfTheChain
import YangMills.Construction.RunningCouplingSlope.TorusViewedOnATower
import Mathlib
set_option autoImplicit false
open Filter
open scoped Topology
noncomputable section
namespace YangMills.Construction.RunningCouplingSlope
def ChainLogIsGaussianNumber : Prop :=
  ∀ a : ℝ, 0 < a → ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∀ k n : ℕ, 1 ≤ k → 0 < n →
    ∀ ρ : ℝ, 0 < ρ → ρ ≤ 1 →
      ∀ᶠ V in 𝓝 (TorusFields.trivialField (2 * L ^ n)),
        ∀ W : Tower.Edge L n k k → Matrices.ComplexMatrix2, RepresentsTorusField W V →
        (∃ X : ChainPoint L n k, IsMinimizerOver a W X) ∧
        ∀ X : ChainPoint L n k, IsMinimizerOver a W X →
          ∀ (Y Y₀ : Type) [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [FiniteDimensional ℝ Y]
            [NormedAddCommGroup Y₀] [InnerProductSpace ℝ Y₀] [FiniteDimensional ℝ Y₀]
            (l : LevelForms L n k →ₗ[ℝ] Y) (l₀ : LevelForms L n k →ₗ[ℝ] Y₀),
            IsTransversalSlice X l → IsTransversalSlice (unitPoint L n k) l₀ →
              SlopeCoefficient.chainLogarithm a ρ L k (2 * L ^ n) V =
                chainLogWeight a X l - chainLogWeight a (unitPoint L n k) l₀
end YangMills.Construction.RunningCouplingSlope
end
