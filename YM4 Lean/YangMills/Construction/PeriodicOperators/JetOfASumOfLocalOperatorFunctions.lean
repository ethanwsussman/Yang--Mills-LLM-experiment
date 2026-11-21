import YangMills.Construction.PeriodicOperators.Jets
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.PeriodicOperators.JetAdd
def Claim : Prop :=
  ∀ (δ : ℝ) (p : Fin 4 → ℂ), 0 < δ → p ∈ imStrip δ →
    ∀ F I₁ I₂ : PeriodicData, IsPeriodic F → IsPeriodic I₁ →
      IsPeriodic I₂ →
      ∀ (εPlus εMinus : F.UnitQuot → ℂ) (T T' : (F.Carrier → ℂ) → I₁.Carrier → I₂.Carrier → ℂ),
        IsLocalOpFun F I₂ I₁ T → IsLocalOpFun F I₂ I₁ T' →
        JetQuad.EqAsJet δ p (jetAlong F I₂ I₁ (opFunAdd T T') p εPlus εMinus)
          (JetQuad.add (jetAlong F I₂ I₁ T p εPlus εMinus) (jetAlong F I₂ I₁ T' p εPlus εMinus))
end YangMills.Construction.PeriodicOperators.JetAdd
end
