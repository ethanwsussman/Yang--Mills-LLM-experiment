import YangMills.Construction.Towers.GaugeRelationOfTheChargedSymbol
import Mathlib
set_option autoImplicit false
open YangMills.Construction.InfiniteLattice (AmbientSpace)
noncomputable section
namespace YangMills.Construction.Tower.ConstantFieldSymbols
def rotatedGaugeSymbolColumn (q : AmbientSpace) : Matrix (Fin 4) (Fin 1) ℂ :=
  Matrix.of fun μ _ =>
    ![((2 * Real.sin (q 1) : ℝ) : ℂ) * Complex.exp (Complex.I * (q 0 : ℂ)),
      -((2 * Real.sin (q 0) : ℝ) : ℂ) * Complex.exp (Complex.I * (q 1 : ℂ)), 0, 0] μ
def FirstCoeffOnGaugeColumn : Prop :=
  ∀ (D C : ℝ) (σ₁ σ₂ : AmbientSpace → Matrix (Fin 4) (Fin 4) ℂ)
    (σ σr : ℝ → AmbientSpace → Matrix (Fin 4) (Fin 4) ℂ),
    ChargedSymbolExpansion D C σ₁ σ₂ σ σr → ∀ q : AmbientSpace,
      σ₁ q * gaugeSymbolColumn q = rotatedGaugeSymbolColumn q
end YangMills.Construction.Tower.ConstantFieldSymbols
end
