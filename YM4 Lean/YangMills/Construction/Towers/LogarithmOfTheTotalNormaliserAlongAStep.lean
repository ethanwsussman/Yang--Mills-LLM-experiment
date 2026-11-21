import YangMills.Construction.Towers.ChainOfABlockFieldAndTheTotalNormaliser
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Tower
def LogTotalNormaliserStep.Statement : Prop :=
  ∀ L n k : ℕ, Conventions.IsAdmissibleBlockingFactor L → 0 < n → ∀ hL : 0 < L,
    EventuallyNearIdentity (fieldSpace L n (k + 1) (k + 1)) fun W =>
      LogTotalNormaliserWellDefined W ∧
        LogLevelNormaliserWellDefined hL (Nat.le_succ k) (chosenProlong L n (k + 1) k W) ∧
        logTotalNormaliserRatio L n (k + 1) W =
          logNormaliserRatio L n (k + 1) k W +
            logLevelNormaliserRatio hL (Nat.le_succ k) (chosenProlong L n (k + 1) k W)
end YangMills.Construction.Tower
end
