import YangMills.Construction.Conventions.StandingParameters
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.LevelUnits
open PeriodicLattice
variable (s : Conventions.StandingParameters) (k : ℕ)
def coverMap : (Fin 4 → ℝ) →+ s.Torus where
  toFun u μ := ((meshSize s.L (levelDepth s.K k) * u μ : ℝ) : AddCircle (torusSide s.L s.m))
  map_zero' := by
    funext μ
    simp
  map_add' u v := by
    funext μ
    simp [mul_add]
variable {s}
theorem blockingFactor_cast_ne_zero (s : Conventions.StandingParameters) : (s.L : ℝ) ≠ 0 := by
  have h : 13 ≤ s.L := s.isAdmissible.2
  exact_mod_cast (by omega : s.L ≠ 0)
variable (s)
variable (n : ℕ)
variable {s k n}
variable (s k n)
end YangMills.Construction.LevelUnits
