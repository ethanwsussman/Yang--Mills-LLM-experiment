import YangMills.Construction.PeriodicOperators.BlockMatricesAndCopiesOfIndexSets
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.PeriodicOperators.BlockJets
def AllConditions : Prop :=
  CopiesAndSigmaPeriodic ∧
    ∀ F : PeriodicData, IsPeriodic F → ∀ (δ : ℝ) (p : Fin 4 → ℂ), 0 < δ → p ∈ imStrip δ →
      ∀ εp εm : F.UnitQuot → ℂ,
        SmulLocalOpFun F δ p εp εm ∧
        (∀ J : Fin 2 → PeriodicData, (∀ b, IsPeriodic (J b)) →
          BlockJetFacts δ p J ∧ MulBlockJet δ p J ∧
            BlockLocalOpFun F δ p εp εm J) ∧
        ∀ V : Fin 2 → PeriodicData, (∀ b, IsPeriodic (V b)) →
          ToCopies F δ p εp εm V
end YangMills.Construction.PeriodicOperators.BlockJets
end
