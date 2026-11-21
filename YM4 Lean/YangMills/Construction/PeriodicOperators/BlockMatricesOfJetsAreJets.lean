import YangMills.Construction.PeriodicOperators.BlockMatricesAndCopiesOfIndexSets
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.PeriodicOperators.BlockJetsAreJets
def Claim : Prop :=
  ∀ (δ : ℝ) (q : Fin 4 → ℂ), 0 < δ → q ∈ imStrip δ →
    ∀ J : Fin 2 → PeriodicData, (∀ b, IsPeriodic (J b)) →
      BlockJets.BlockJetFacts δ q J
end YangMills.Construction.PeriodicOperators.BlockJetsAreJets
end
