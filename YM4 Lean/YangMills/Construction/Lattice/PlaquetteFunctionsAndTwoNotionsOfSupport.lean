import YangMills.Construction.Conventions.StandingParameters
import YangMills.Construction.Geometry.TorusMetric
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction
namespace PlaquetteSupports
variable (s : Conventions.StandingParameters)
def latticeSpacing : ℝ := PeriodicLattice.meshSize s.L ((s.K : ℕ) : ℤ)
abbrev LatticePlaquette : Type := PeriodicLattice.Plaquette s.L s.m ((s.K : ℕ) : ℤ)
def planeDiagonal (μ ν : Fin 4) : s.Torus :=
  TorusMetric.torusProj (PeriodicLattice.torusSide s.L s.m)
    ((latticeSpacing s / 2) • (Pi.single μ 1 + Pi.single ν 1 : Fin 4 → ℝ))
variable {s}
def planeOf (p : LatticePlaquette s) : Fin 4 × Fin 4 := (p.firstAxis, p.secondAxis)
variable (s)
abbrev PlaquetteFunction : Type := LatticePlaquette s → ℝ
variable {s}
def torusTSupport (f : s.Torus → ℝ) : Set s.Torus := tsupport f
def euclideanTSupport (f : (Fin 4 → ℝ) → ℝ) : Set (Fin 4 → ℝ) := tsupport f
def torusESup (f : s.Torus → ℝ) : EReal := ⨆ u, (f u : EReal)
def TorusFunNonneg (f : s.Torus → ℝ) : Prop := ∀ u, 0 ≤ f u
end PlaquetteSupports
end YangMills.Construction
