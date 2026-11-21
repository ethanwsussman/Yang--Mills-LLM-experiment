import YangMills.Construction.PeriodicOperators.BlockMatricesAndCopiesOfIndexSets
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.PeriodicOperators.BlockJetProducts
def Claim : Prop :=
  ∀ (δ : ℝ) (z : Fin 4 → ℂ), 0 < δ → z ∈ imStrip δ →
    ∀ J : Fin 2 → PeriodicData, (∀ b, IsPeriodic (J b)) →
      BlockJets.MulBlockJet δ z J
end YangMills.Construction.PeriodicOperators.BlockJetProducts
end
