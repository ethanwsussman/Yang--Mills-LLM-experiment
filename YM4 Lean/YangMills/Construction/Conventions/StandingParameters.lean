import YangMills.Construction.Lattice.PeriodicLattices
import YangMills.Construction.Matrices.SpecialUnitaryTwo
import Mathlib
set_option autoImplicit false
universe u
noncomputable section
namespace YangMills.Construction
namespace Conventions
def IsAdmissibleBlockingFactor (L : ℕ) : Prop := Odd L ∧ 13 ≤ L
structure StandingParameters where
  L : ℕ
  isAdmissible : IsAdmissibleBlockingFactor L
  K : ℕ+
  m : ℕ+
namespace StandingParameters
abbrev dimension : ℕ := 4
abbrev gaugeGroup : Submonoid Matrices.ComplexMatrix2 := Matrices.ComplexMatrix2.specialUnitary
def side (p : StandingParameters) : ℝ := PeriodicLattice.torusSide p.L p.m
abbrev Torus (p : StandingParameters) : Type := PeriodicLattice.FourTorus p.L p.m
end StandingParameters
end Conventions
end YangMills.Construction
end
