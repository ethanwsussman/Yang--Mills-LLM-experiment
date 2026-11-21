import YangMills.Construction.PeriodicOperators.BlockMatricesAndCopiesOfIndexSets
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.PeriodicOperators.CopyOpFuns
def Claim : Prop :=
  ∀ F : PeriodicData, IsPeriodic F → ∀ (δ : ℝ) (p : Fin 4 → ℂ), 0 < δ → p ∈ imStrip δ →
    ∀ εPlus εMinus : F.UnitQuot → ℂ, ∀ V : Fin 2 → PeriodicData, (∀ b, IsPeriodic (V b)) →
      BlockJets.LocalOpFunToCopies F δ p εPlus εMinus V
end YangMills.Construction.PeriodicOperators.CopyOpFuns
end
