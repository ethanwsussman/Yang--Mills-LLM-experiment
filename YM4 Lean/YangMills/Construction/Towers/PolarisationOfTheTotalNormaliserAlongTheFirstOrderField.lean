import YangMills.Construction.Towers.ChainOfABlockFieldAndTheTotalNormaliser
import YangMills.Construction.Towers.ResponseFieldOnTheTorus
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Tower.NormaliserHessianAlongLinearizedField
def Claim : Prop :=
  ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∀ k : ℕ, 1 ≤ k →
    PeriodicOperators.Tempered.EventuallyForSides L fun n =>
      ∀ B ∈ Tower.edgeFormSpace L n k k, ∀ B' ∈ Tower.edgeFormSpace L n k k,
        Tower.leftSecondDeriv (Tower.logTotalNormaliserRatio L n k) (Tower.trivialField L n k k)
            B B' =
          Tower.fieldFunctionalSecondDeriv L n k (Tower.TorusResponseField.linearizedField L n k B)
            (Tower.TorusResponseField.linearizedField L n k B')
end YangMills.Construction.Tower.NormaliserHessianAlongLinearizedField
end
