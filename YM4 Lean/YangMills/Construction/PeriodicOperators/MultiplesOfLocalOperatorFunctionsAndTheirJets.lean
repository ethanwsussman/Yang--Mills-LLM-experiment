import YangMills.Construction.PeriodicOperators.BlockMatricesAndCopiesOfIndexSets
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.PeriodicOperators.OpFunMultiples
def Claim : Prop :=
  ∀ F : PeriodicData, IsPeriodic F → ∀ (δ : ℝ) (p : Fin 4 → ℂ), 0 < δ → p ∈ imStrip δ →
    ∀ εPlus εMinus : F.UnitQuot → ℂ,
      BlockJets.SmulLocalOpFun F δ p εPlus εMinus
end YangMills.Construction.PeriodicOperators.OpFunMultiples
end
