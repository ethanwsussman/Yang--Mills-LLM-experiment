import YangMills.Construction.PeriodicOperators.Jets
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.PeriodicOperators.JetComp
def Claim : Prop :=
  ∀ (δ : ℝ) (p : Fin 4 → ℂ), 0 < δ → p ∈ imStrip δ →
    ∀ F I₁ I₂ I₃ : PeriodicData, IsPeriodic F → IsPeriodic I₁ →
      IsPeriodic I₂ → IsPeriodic I₃ →
      ∀ (εPlus εMinus : F.UnitQuot → ℂ) (T : (F.Carrier → ℂ) → I₁.Carrier → I₂.Carrier → ℂ)
        (S : (F.Carrier → ℂ) → I₂.Carrier → I₃.Carrier → ℂ),
        IsLocalOpFun F I₂ I₁ T → IsLocalOpFun F I₃ I₂ S →
        JetQuad.EqAsJet δ p (jetAlong F I₃ I₁ (opFunComp T S) p εPlus εMinus)
          (JetQuad.mul p (jetAlong F I₂ I₁ T p εPlus εMinus) (jetAlong F I₃ I₂ S p εPlus εMinus))
end YangMills.Construction.PeriodicOperators.JetComp
end
