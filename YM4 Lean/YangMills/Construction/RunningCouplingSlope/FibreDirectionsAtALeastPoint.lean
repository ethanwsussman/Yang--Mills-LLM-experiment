import YangMills.Construction.RunningCouplingSlope.GaussianNumbersOfTheSoftChain
import Mathlib
set_option autoImplicit false
open Filter
open scoped Topology
noncomputable section
namespace YangMills.Construction.RunningCouplingSlope
open Tower
def FibreHessianNonnegAtMinimizer : Prop :=
  ∀ a : ℝ, 0 < a → ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∀ k n : ℕ, 1 ≤ k → 0 < n →
    ∀ (W : Edge L n k k → Matrices.ComplexMatrix2) (X : ChainPoint L n k), IsMinimizerOver a W X →
      (∀ ξ : LevelForms L n k, 0 ≤ fibreSecondDeriv a X ξ ξ) ∧
      ∀ l ∈ topVanishingGauges L n k, ∀ ξ : LevelForms L n k,
        formValues ξ = gaugeOrbitValues X (l : Vertex L n k 0 → Matrices.ComplexMatrix2) →
          fibreSecondDeriv a X ξ ξ = 0
end YangMills.Construction.RunningCouplingSlope
end
