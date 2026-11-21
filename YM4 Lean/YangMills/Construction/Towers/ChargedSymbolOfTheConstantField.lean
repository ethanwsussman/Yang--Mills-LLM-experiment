import YangMills.Construction.Towers.SymbolsOfTheConstantField
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Tower.ConstantFieldSymbols
def ChargedSymbolExpansionExists : Prop :=
  ∃ (D C : ℝ) (σ₁ σ₂ : InfiniteLattice.AmbientSpace → Matrix (Fin 4) (Fin 4) ℂ)
    (σ σr : ℝ → InfiniteLattice.AmbientSpace → Matrix (Fin 4) (Fin 4) ℂ),
    ChargedSymbolExpansion D C σ₁ σ₂ σ σr
end YangMills.Construction.Tower.ConstantFieldSymbols
end
