import YangMills.Construction.Towers.SymbolsOfTheConstantField
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Tower.ConstantFieldSymbols
def gaugeSymbolColumn (q : InfiniteLattice.AmbientSpace) : Matrix (Fin 4) (Fin 1) ℂ :=
  Matrix.of fun μ _ => Complex.exp (Complex.I * (q μ : ℂ)) - 1
def ChargedSymbolGaugeRelation : Prop :=
  ∀ (D C : ℝ) (s₁ s₂ : InfiniteLattice.AmbientSpace → Matrix (Fin 4) (Fin 4) ℂ)
    (s sRem : ℝ → InfiniteLattice.AmbientSpace → Matrix (Fin 4) (Fin 4) ℂ),
    ChargedSymbolExpansion D C s₁ s₂ s sRem → ∀ φ : ℝ, |φ| ≤ Real.pi →
      MagneticWeyl.moyalProduct φ (s φ) gaugeSymbolColumn =
        MagneticWeyl.moyalProduct φ gaugeSymbolColumn scalarMultiplier
end YangMills.Construction.Tower.ConstantFieldSymbols
end
