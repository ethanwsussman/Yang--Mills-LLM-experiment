import YangMills.Construction.ReflectionPositivity.AxisMirrorData
import Mathlib
set_option autoImplicit false
open Set MeasureTheory
noncomputable section
namespace YangMills.Construction.ReflectionPositivity.AxisMirror.MirrorData
variable (D : MirrorData)
abbrev LatticeBond : Type := PeriodicLattice.Bond D.L D.m (D.K : ℕ)
abbrev LatticePlaquette : Type := PeriodicLattice.Plaquette D.L D.m (D.K : ℕ)
abbrev LatticeGaugeField : Type :=
  {U : D.LatticeBond → Matrices.ComplexMatrix2 //
    PeriodicLattice.IsGaugeField PeriodicLattice.compactGaugeGroup univ U}
def linkValues (B : Set D.LatticeBond) (U : D.LatticeGaugeField) :
    B → Matrices.ComplexMatrix2.specialUnitary :=
  fun b => ⟨U.1 b.1, U.2.1 b.1 (mem_univ _)⟩
end YangMills.Construction.ReflectionPositivity.AxisMirror.MirrorData
end
