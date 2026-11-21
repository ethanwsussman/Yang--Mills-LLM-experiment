import YangMills.Construction.PeriodicOperators.BlockMatricesAndCopiesOfIndexSets
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.PeriodicOperators.BlockLocality
def Claim : Prop :=
  ∀ F : PeriodicData, IsPeriodic F → ∀ (δ : ℝ) (p : Fin 4 → ℂ), 0 < δ → p ∈ imStrip δ →
    ∀ εPlus εMinus : F.UnitQuot → ℂ, ∀ J : Fin 2 → PeriodicData, (∀ b, IsPeriodic (J b)) →
      BlockJets.BlockLocalOpFun F δ p εPlus εMinus J
end YangMills.Construction.PeriodicOperators.BlockLocality
end
