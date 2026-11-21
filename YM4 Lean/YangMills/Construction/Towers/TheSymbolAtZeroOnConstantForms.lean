import YangMills.Construction.Towers.ResponseFieldOnTheTorus
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Tower.SymbolAtZero
open TorusResponseField (constantFieldAmplitude)
open FullSpace (fieldPeriodicData secondVariationSymbol)
def SymmetricAndKillsConstantForms : Prop :=
  ∀ (L : ℕ) (hL : 0 < L), Conventions.IsAdmissibleBlockingFactor L → ∀ k : ℕ, 1 ≤ k →
    (∀ u v : (fieldPeriodicData L k hL).UnitQuot → ℂ,
      secondVariationSymbol L k hL 0 u v = secondVariationSymbol L k hL 0 v u) ∧
    ∀ ξ : Fin 4 → Matrices.ComplexMatrix2, (∀ ρ, ξ ρ ∈ Matrices.ComplexMatrix2.traceless) →
      ∀ ε : (fieldPeriodicData L k hL).UnitQuot → ℂ,
        secondVariationSymbol L k hL 0 (constantFieldAmplitude L k hL ξ) ε = 0 ∧
          secondVariationSymbol L k hL 0 ε (constantFieldAmplitude L k hL ξ) = 0
end YangMills.Construction.Tower.SymbolAtZero
end
