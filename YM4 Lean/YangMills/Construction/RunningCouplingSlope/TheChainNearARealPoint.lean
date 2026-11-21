import YangMills.Construction.RunningCouplingSlope.GaussianNumbersOfTheSoftChain
import Mathlib
set_option autoImplicit false
open Filter
open scoped Topology Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction.RunningCouplingSlope
open Tower
def ExpMoveNearCompactPoint : Prop :=
  ∀ (a : ℝ) (L : ℕ), Conventions.IsAdmissibleBlockingFactor L → ∀ k n : ℕ, 1 ≤ k → 0 < n →
    ∀ X : ChainPoint L n k, IsCompactValued X →
      IsFibreHessian a X (fibreHessian a X) ∧
      ∀ ξ : LevelForms L n k,
        (∀ᶠ r in 𝓝 (0 : ℝ), IsCompactValued (expMove (r • ξ) X)) ∧
        ∀ j, j ≤ k → ∀ b : Edge L n k j, b.IsPositivelyOriented →
          HasDerivAt (fun r : ℝ => levelField (expMove (r • ξ) X) j b)
            ((Complex.I • tangentTransport X ξ j b) * levelField X j b) 0
end YangMills.Construction.RunningCouplingSlope
end
