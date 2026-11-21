import YangMills.Construction.Towers.CovariantLinearAverages
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Tower
def ComplexIterDerivChain : Prop :=
  ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∀ n k : ℕ, 0 < n →
    ∀ U ∈ smallIterateFields L n k, ∀ B ∈ complexEdgeForms L n k 0,
      complexIterDeriv L n k 0 U B = B ∧
      (∀ j < k, complexIterDeriv L n k (j + 1) U B =
        complexSmoothingDeriv (PeriodicLattice.complexBlockFieldAtLevel j U)
          (complexIterDeriv L n k j U B)) ∧
      ∀ j ≤ k, complexIterDeriv L n k j U B ∈ complexEdgeForms L n k j
end YangMills.Construction.Tower
end
