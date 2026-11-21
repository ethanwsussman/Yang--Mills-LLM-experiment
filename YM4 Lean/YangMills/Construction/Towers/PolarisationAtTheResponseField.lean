import YangMills.Construction.Towers.ResponseFieldOnTheTorus
import YangMills.Construction.Towers.TheFamiliesOfTheTotalNormaliser
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Tower.HessianAtResponseField
open PeriodicOperators.Tempered (EventuallyForSides complexHessian)
def Claim : Prop :=
  ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∀ k : ℕ, 1 ≤ k →
    EventuallyForSides L fun n =>
      ∀ B ∈ Tower.complexEdgeForms L n 0 0, ∀ B' ∈ Tower.complexEdgeForms L n 0 0,
        complexHessian (Tower.logNormaliserFamily L k) n B B' =
          Tower.complexSecondDeriv L n k (Tower.TorusResponseField.complexResponse L n k B)
            (Tower.TorusResponseField.complexResponse L n k B')
end YangMills.Construction.Tower.HessianAtResponseField
end
