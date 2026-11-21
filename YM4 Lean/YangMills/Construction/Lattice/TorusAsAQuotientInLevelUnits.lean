import YangMills.Construction.Conventions.StandingParameters
import YangMills.Construction.PeriodicLattice.LevelProjectionAndLiftedCubes
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open Conventions
namespace PeriodicLattice
def TorusQuotientInLevelUnits : Prop :=
  ∀ (s : StandingParameters) (k : ℕ), k ≤ (s.K : ℕ) →
    let N : ℝ := sideInLevelUnits s.L s.m s.K k
    (s.L : ℝ) ^ levelDepth s.K k * s.side = N ∧
    toLevelUnits s.L s.K k s.side = N ∧
    Function.Surjective (levelProj s.L s.m s.K k) ∧
    (∀ (x : Fin 4 → ℝ) (μ : Fin 4), levelProj s.L s.m s.K k x μ =
      (((s.L : ℝ) ^ ((k : ℤ) - ((s.K : ℕ) : ℤ)) * x μ : ℝ) : AddCircle (torusSide s.L s.m))) ∧
    ∀ x x' : Fin 4 → ℝ, levelProj s.L s.m s.K k x = levelProj s.L s.m s.K k x' ↔
      ∃ n : Fin 4 → ℤ, ∀ μ, x μ - x' μ = N * (n μ : ℝ)
end PeriodicLattice
end YangMills.Construction
end
