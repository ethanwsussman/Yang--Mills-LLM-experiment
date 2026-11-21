import YangMills.Construction.Conventions.StandingParameters
import YangMills.Construction.Geometry.TorusMetric
import YangMills.Construction.Lattice.LevelCoordinates
import Mathlib
set_option autoImplicit false
universe u
noncomputable section
namespace YangMills.Construction.TorusTransport
open TorusMetric Conventions
structure TransportData extends StandingParameters where
  M : ℝ
  one_le_M : 1 ≤ M
abbrev PositiveNat : Type := ℕ+
namespace TransportData
variable (D : TransportData)
def spacing : ℝ := PeriodicLattice.meshSize D.L (D.K : ℕ)
end TransportData
inductive Domain where
  | euclidean
  | torus
abbrev Domain.Point (D : TransportData) : Domain → Type
  | .euclidean => Fin 4 → ℝ
  | .torus => D.Torus
abbrev euclidNorm (x : Fin 4 → ℝ) : ℝ := euclidNormVec x
abbrev scalarProd (x y : Fin 4 → ℝ) : ℝ := x ⬝ᵥ y
abbrev maxNorm (x : Fin 4 → ℝ) : ℝ := supNormVec x
abbrev basisVec (μ : Fin 4) : Fin 4 → ℝ := PeriodicLattice.coordVec μ
section Functions
variable {X : Type u}
abbrev ComplexFun (X : Type u) : Type u := X → ℂ
abbrev RealFun (X : Type u) : Type u := X → ℝ
def RealFun.toComplex (f : RealFun X) : ComplexFun X := fun x => (f x : ℂ)
end Functions
end YangMills.Construction.TorusTransport
end
