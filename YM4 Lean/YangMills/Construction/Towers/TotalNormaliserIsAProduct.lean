import YangMills.Construction.Towers.ChainOfABlockFieldAndTheTotalNormaliser
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Tower
def TotalNormaliserFactorises : Prop :=
  ∀ L n k : ℕ, YangMills.Construction.Conventions.IsAdmissibleBlockingFactor L → 0 < n → 1 ≤ k →
    EventuallyNearIdentity (fieldSpace L n k k) fun W =>
      TotalNormaliserWellDefined W ∧
        totalGaussianNormaliser L n k W =
          ∏ i : Fin k, gaussianNormaliser L n k i (descendingChain W i.is_lt)
end YangMills.Construction.Tower
end
