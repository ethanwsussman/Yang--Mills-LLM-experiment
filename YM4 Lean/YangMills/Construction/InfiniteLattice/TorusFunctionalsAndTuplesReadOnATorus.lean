import YangMills.Construction.Continuum.SchwingerFunctions
import YangMills.Construction.InfiniteLattice.SeparatedLipschitzTuplesAndPartialFamilies
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
namespace TorusCumulants
open YangMills.Construction.PeriodicLattice
variable {n : ℕ}
def BoundedComponents {L m : ℕ} (h : Fin n → FourTorus L m → ℝ) : Prop :=
  ∀ i, TestFunctions.IsBoundedFun (h i)
def cumulantFunctional (L m K : ℕ) (β : ℝ) (h : Fin n → FourTorus L m → ℝ) : ℂ :=
  gibbsCumulant L m K β fun i U => smearedObservable (h i) U
structure FitsOnTorus (L m : ℕ) (r : ℝ) (X : Fin n → (Fin 4 → ℝ) → ℝ) : Prop where
  radius_pos : 0 < r
  mem_separated : X ∈ SeparatedFamilies.separatedLipschitzSetIn n (ENNReal.ofReal r)
  radius_le_half_side : 2 * r + 2 ≤ torusSide L m / 2
def periodizedFamily (L m : ℕ) (X : Fin n → (Fin 4 → ℝ) → ℝ) : Fin n → FourTorus L m → ℝ :=
  SchwingerFunctions.periodizeAll L m X
def cumulantOfFamily (L m K : ℕ) (β : ℝ) (X : Fin n → (Fin 4 → ℝ) → ℝ) : ℂ :=
  cumulantFunctional L m K β (periodizedFamily L m X)
end TorusCumulants
end YangMills.Construction
