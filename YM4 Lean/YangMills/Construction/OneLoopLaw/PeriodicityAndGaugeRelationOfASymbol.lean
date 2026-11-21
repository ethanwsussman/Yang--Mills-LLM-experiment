import YangMills.Construction.OneLoopLaw.KernelsAndTensorFormOfASymbol
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.OneLoopLaw.SymbolPeriodicity
open YangMills.Construction.PeriodicOperators YangMills.Construction.PeriodicOperators.Tempered
open YangMills.Construction.OneLoopLaw.TemperedStiffness
open YangMills.Construction.PeriodicOperators.RiemannSums
def PeriodicityAndWardClaim : Prop :=
  ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L →
    ∀ (F : FieldFamily L) (δ : ℝ) (π : SymbolArray) (e : ℕ → ℝ),
    IsLatticeFunctional L F → IsTemperedWitness L F δ π e →
      (∀ μ ν : Fin 4, PeriodicOnStrip δ (π μ ν)) ∧ SatisfiesWardIdentity δ π
end YangMills.Construction.OneLoopLaw.SymbolPeriodicity
end
