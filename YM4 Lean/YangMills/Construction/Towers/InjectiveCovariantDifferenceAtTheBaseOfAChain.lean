import YangMills.Construction.Towers.ChainOfABlockFieldAndTheTotalNormaliser
import YangMills.Construction.Towers.InjectiveCovariantDifference
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Tower
def CovDiffInjectiveAtChainBottom : Prop :=
  ∀ L m k : ℕ, Conventions.IsAdmissibleBlockingFactor L → 0 < m → 1 ≤ k →
    EventuallyNearIdentity (fieldSpace L m k k) fun A =>
      CovDiffInjective A → CovDiffInjective (chainBottom A)
end YangMills.Construction.Tower
end
