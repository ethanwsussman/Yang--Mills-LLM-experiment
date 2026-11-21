import YangMills.Construction.PeriodicOperators.Jets
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.PeriodicOperators
open JetQuad
def TransposeJet.Claim : Prop :=
  ∀ (δ : ℝ) (p : Fin 4 → ℂ), 0 < δ → p ∈ imStrip δ →
    ∀ F I₁ I₂ : PeriodicData, IsPeriodic F → IsPeriodic I₁ → IsPeriodic I₂ →
    ∀ (εPlus εMinus : F.UnitQuot → ℂ) (T : (F.Carrier → ℂ) → I₁.Carrier → I₂.Carrier → ℂ),
      IsLocalOpFun F I₂ I₁ T →
      EqAsJet δ p (jetAlong F I₁ I₂ (opFunTranspose T) p εPlus εMinus)
        (transposeAt p (jetAlong F I₂ I₁ T p εPlus εMinus))
end YangMills.Construction.PeriodicOperators
end
