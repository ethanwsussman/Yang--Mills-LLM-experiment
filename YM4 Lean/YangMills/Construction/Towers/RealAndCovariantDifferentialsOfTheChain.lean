import YangMills.Construction.Towers.ChainOfABlockFieldAndTheTotalNormaliser
import YangMills.Construction.Towers.CovariantLinearAverages
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Tower
open Matrices (ComplexMatrix2)
def RealDerivEqComplexAtChainBottom : Prop :=
  ∀ L n k : ℕ, Conventions.IsAdmissibleBlockingFactor L → 0 < n → 1 ≤ k →
    EventuallyNearIdentity (fieldSpace L n k k) fun W => ∀ j ≤ k, ∀ B : edgeFormSpace L n k 0,
      (smoothingIterDifferential L n k j (chainBottom W) B : Edge L n k j → ComplexMatrix2) =
        complexIterDeriv L n k j (chainBottom W) B
end YangMills.Construction.Tower
end
