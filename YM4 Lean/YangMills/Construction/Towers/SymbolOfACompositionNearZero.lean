import YangMills.Construction.OneLoopLaw.KernelsAndTensorFormOfASymbol
import YangMills.Construction.Towers.TheSymbolOfOneStepOfTheCriticalBranch
import Mathlib
set_option autoImplicit false
open Asymptotics
open scoped Topology
noncomputable section
namespace YangMills.Construction.Tower.StepSymbolNearZero
open PeriodicOperators (toComplexVec)
open PeriodicOperators.Tempered PeriodicOperators.Tempered.OneStep
def Claim : Prop :=
  ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∀ (π : SymbolArray) (b : ℝ) (i : ℕ),
    (∃ C : ℝ, ∀ (ρ σ : Fin 4) (q : InfiniteLattice.AmbientSpace),
        ‖π ρ σ (toComplexVec q)‖ ≤ C) →
      OneLoopLaw.TemperedStiffness.HasTransverseForm π b →
      ∀ μ ν : Fin 4,
        (fun p : InfiniteLattice.AmbientSpace => stepSymbolArray L i π μ ν (toComplexVec p) -
            (L : ℂ) ^ 2 * π μ ν (toComplexVec ((L : ℝ)⁻¹ • p))) =O[𝓝 0]
          fun p => TorusMetric.euclidNormVec p ^ 3
end YangMills.Construction.Tower.StepSymbolNearZero
end
