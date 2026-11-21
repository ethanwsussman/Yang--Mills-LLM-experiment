import YangMills.Construction.PeriodicOperators.TemperedFunctionals
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.PeriodicOperators.Tempered
def HessianSymbolDetermined.Claim : Prop :=
  ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∀ F : FieldFamily L, IsTemperedFunctional L F →
    (∀ (δ δ' : ℝ) (π π' : SymbolArray) (e e' : ℕ → ℝ),
      IsTemperedWitness L F δ π e → IsTemperedWitness L F δ' π' e' → δ' ≤ δ →
        ∀ μ ν, EqOn (π' μ ν) (π μ ν) (imStrip δ')) ∧
    ∃ P : SymbolArray, IsHessianSymbol L F P ∧
      ∀ P' : SymbolArray, IsHessianSymbol L F P' →
        ∀ μ ν, EqOn (P' μ ν) (P μ ν) (symbolDomain L F)
end YangMills.Construction.PeriodicOperators.Tempered
end
