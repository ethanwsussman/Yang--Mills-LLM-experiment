import YangMills.Construction.Conventions.StandingParameters
import YangMills.Construction.Lattice.ObservablesAndTestNorms
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Conventions.StandingParameters
variable (s : StandingParameters)
abbrev cutoffMesh : ℝ := PeriodicLattice.meshSize s.L ((s.K : ℕ) : ℤ)
abbrev cutoffLattice : AddSubgroup s.Torus := PeriodicLattice.sublattice s.L s.m ((s.K : ℕ) : ℤ)
def periodLattice : Set (Fin 4 → ℝ) :=
  Set.range (TestFunctions.latticeTranslate (PeriodicLattice.torusSide s.L s.m))
def addVector (y : s.Torus) (ζ : Fin 4 → ℝ) : s.Torus :=
  y + TorusMetric.torusProj (PeriodicLattice.torusSide s.L s.m) ζ
def subVector (y : s.Torus) (ζ : Fin 4 → ℝ) : s.Torus :=
  s.addVector y (-ζ)
def cutoffLatticeIsometries : Set (s.Torus ≃ s.Torus) :=
  {r | PeriodicLattice.IsSublatticeIsometry ((s.K : ℕ) : ℤ) r}
end YangMills.Construction.Conventions.StandingParameters
end
