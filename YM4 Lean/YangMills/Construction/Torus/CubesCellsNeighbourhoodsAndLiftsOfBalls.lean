import YangMills.Construction.Lattice.BlocksAndCorridors
import YangMills.Construction.Lattice.PlaquetteFunctionsAndTwoNotionsOfSupport
import YangMills.Construction.Torus.CellOfAPointOfTheTorus
import Mathlib
set_option autoImplicit false
namespace YangMills.Construction.CubesAndBallLifts
open Set PeriodicLattice TestFunctions TorusMeasure
noncomputable section
variable {s : Conventions.StandingParameters}
abbrev siteCube (y : Site s.L s.m ((s.K : ℕ) : ℤ)) : Set s.Torus := cubeAround y
def translatedSiteCube (y : Site s.L s.m ((s.K : ℕ) : ℤ)) (v : s.Torus) : Set s.Torus :=
  (fun x => x + v) '' siteCube y
abbrev cellAround (z : s.Torus) : Set s.Torus := torusCell (PlaquetteSupports.latticeSpacing s) z
variable (s) in
def halfOpenCubeR4 (y : Fin 4 → ℝ) : Set (Fin 4 → ℝ) :=
  (fun τ => y + τ) '' Set.pi univ fun _ : Fin 4 =>
    Ico (-(PlaquetteSupports.latticeSpacing s / 2))
      (PlaquetteSupports.latticeSpacing s / 2)
def IsBallLift (z : s.Torus) (ϱ : ℝ) (B : Set (Fin 4 → ℝ)) : Prop :=
  0 < ϱ ∧ ϱ < s.side / 4 ∧ (∃ c : Fin 4 → ℝ, B = closedBallR4 c ϱ) ∧
    proj s '' B = closedBallTorus z ϱ
def IsLiftWithin (B : Set (Fin 4 → ℝ)) (u : s.Torus) (t : Fin 4 → ℝ) : Prop :=
  t ∈ B ∧ proj s t = u
def setLiftWithin (B : Set (Fin 4 → ℝ)) (A : Set s.Torus) : Set (Fin 4 → ℝ) :=
  {t | ∃ u ∈ A, IsLiftWithin B u t}
def functionLiftTo (B : Set (Fin 4 → ℝ)) (f : s.Torus → ℝ) : (Fin 4 → ℝ) → ℝ :=
  B.indicator (f ∘ proj s)
end
end YangMills.Construction.CubesAndBallLifts
