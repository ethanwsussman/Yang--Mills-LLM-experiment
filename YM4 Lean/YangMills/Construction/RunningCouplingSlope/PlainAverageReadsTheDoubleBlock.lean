import YangMills.Construction.RunningCouplingSlope.SoftChainOnATower
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
namespace RunningCouplingSlope
def NormalizedMeanLocal : Prop :=
  ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∀ n k j : ℕ, 0 < n → j < k →
    ∀ c : Tower.Edge L n k (j + 1), c.IsPositivelyOriented →
    ∀ W W' : Tower.Edge L n k j → Matrices.ComplexMatrix2,
      (∀ e ∈ (PeriodicLattice.bondsInDoubleBlock c : Set (Tower.Edge L n k j)), W e = W' e) →
        contourMean W c = contourMean W' c ∧ meanRadius W c = meanRadius W' c ∧
          normalizedMean W c = normalizedMean W' c
end RunningCouplingSlope
end YangMills.Construction
end
