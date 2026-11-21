import YangMills.Construction.Towers.CovariantLinearAverages
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Tower.FullSpace
def ComplexIterChain : Prop :=
  ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∀ k : ℕ, ∀ U ∈ smallIterateFields L k,
    ∀ B ∈ complexEdgeForms (meshAt L k 0),
      complexIterDeriv L k 0 U B = B ∧
      (∀ j < k, complexIterDeriv L k (j + 1) U B =
        complexSmoothingDeriv (complexIter L k j U)
          (complexIterDeriv L k j U B)) ∧
      ∀ j ≤ k, complexIterDeriv L k j U B ∈ complexEdgeForms (meshAt L k j)
end YangMills.Construction.Tower.FullSpace
end
