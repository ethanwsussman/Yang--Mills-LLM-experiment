import YangMills.Construction.OneLoopLaw.KernelsAndTensorFormOfASymbol
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.OneLoopLaw.CovariantSymbolTaylor
open YangMills.Construction.PeriodicOperators YangMills.Construction.PeriodicOperators.RiemannSums
open YangMills.Construction.PeriodicOperators.Tempered YangMills.Construction.OneLoopLaw.TemperedStiffness
open YangMills.Construction.InfiniteLattice (AmbientSpace)
def TaylorExpansionClaim : Prop :=
  ∀ (δ : ℝ) (π : SymbolArray), 0 < δ → (∀ μ ν : Fin 4, HolomorphicNearStrip δ (π μ ν)) →
    SatisfiesWardIdentity δ π → PermutationCovariant δ π → ReflectionCovariant δ π →
    (∀ (μ ν : Fin 4) (p : AmbientSpace),
      (starRingEnd ℂ) (π μ ν (toComplexVec p)) = π μ ν (toComplexVec (-p))) →
    ∃ b : ℝ, HasTransverseForm π b ∧ ∀ μ ν : Fin 4, μ ≠ ν →
      secondPartialAtZero (π μ ν) μ ν = -(b : ℂ) ∧ secondPartialAtZero (π ν ν) μ μ = 2 * (b : ℂ)
end YangMills.Construction.OneLoopLaw.CovariantSymbolTaylor
end
