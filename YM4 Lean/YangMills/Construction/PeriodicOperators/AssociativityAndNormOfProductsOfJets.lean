import YangMills.Construction.PeriodicOperators.RulesOfTheCalculusOfJets
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.PeriodicOperators
def JetProductsAssocAndNormLe : Prop :=
  ∀ (δ : ℝ) (p : Fin 4 → ℂ), 0 < δ → p ∈ imStrip δ → JetCalculus.MulAssocNormLe δ p
end YangMills.Construction.PeriodicOperators
end
