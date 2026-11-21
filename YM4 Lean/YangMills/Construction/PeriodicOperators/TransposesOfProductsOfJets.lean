import YangMills.Construction.PeriodicOperators.RulesOfTheCalculusOfJets
import Mathlib
noncomputable section
namespace YangMills.Construction.PeriodicOperators
def JetTranspose.Claim : Prop :=
  ∀ (δ : ℝ) (p : Fin 4 → ℂ), 0 < δ → p ∈ imStrip δ → JetCalculus.TransposeMulNorm δ p
end YangMills.Construction.PeriodicOperators
end
