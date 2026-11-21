import YangMills.Construction.PeriodicOperators.RulesOfTheCalculusOfJets
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.PeriodicOperators
def LogNumberDerivAlongFamily.Claim : Prop :=
  ∀ (δ : ℝ) (p : Fin 4 → ℂ), 0 < δ → p ∈ imStrip δ → JetCalculus.HasDerivLogNumber δ p
end YangMills.Construction.PeriodicOperators
end
