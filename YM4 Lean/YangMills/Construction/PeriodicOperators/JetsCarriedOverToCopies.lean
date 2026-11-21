import YangMills.Construction.PeriodicOperators.BlockMatricesAndCopiesOfIndexSets
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.PeriodicOperators.CopyJets
def Claim : Prop :=
  ∀ (δ : ℝ) (p : Fin 4 → ℂ), 0 < δ → p ∈ imStrip δ →
    ∀ V : Fin 2 → PeriodicData, (∀ b, IsPeriodic (V b)) →
      BlockJets.JetsToCopies δ p V
end YangMills.Construction.PeriodicOperators.CopyJets
end
