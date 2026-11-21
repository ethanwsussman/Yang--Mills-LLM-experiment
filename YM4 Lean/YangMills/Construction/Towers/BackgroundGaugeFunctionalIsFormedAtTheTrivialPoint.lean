import YangMills.Construction.Towers.TheFunctionalInTheBackgroundGauge
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Tower
def BackgroundFunctionalWellDefinedAtTrivialField : Prop :=
  ∀ L n k : ℕ, Conventions.IsAdmissibleBlockingFactor L → 0 < n → 1 ≤ k →
    BackgroundFunctionalWellDefined (trivialField L n k 0) 0 0
end YangMills.Construction.Tower
end
