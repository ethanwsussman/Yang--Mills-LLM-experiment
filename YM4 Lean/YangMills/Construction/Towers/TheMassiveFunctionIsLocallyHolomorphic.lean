import YangMills.Construction.Towers.TheFunctionOfTheMassiveJets
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Tower.MassiveOpFunctions.LocallyHolomorphic
open Coordinates
open FullSpace.BackgroundJets
def Claim : Prop :=
  ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∀ k : ℕ, 1 ≤ k → ∀ m₀ : ℝ, 0 < m₀ →
    ∃ U : Set (ComplexCoordinates 5),
      (∃ x₀ ∈ U, x₀ 0 = (m₀ : ℂ) ∧ ∀ j : Fin 4, x₀ j.succ = 0) ∧
        ∃ F : ComplexCoordinates 5 → ℂ,
          ComplexCoordinates.LogDetSecondDeriv.IsHolomorphicScalarIn U F ∧
          ∀ x ∈ U, x ∈ ComplexCoordinates.realLocus 5 → 0 < (x 0).re →
            (∀ ν : Fin 4, ‖x ν.succ‖ < massWidth (x 0).re) →
              F x = massiveLogFn L k (fun ν => x ν.succ) 0 1 (x 0).re
end YangMills.Construction.Tower.MassiveOpFunctions.LocallyHolomorphic
end
