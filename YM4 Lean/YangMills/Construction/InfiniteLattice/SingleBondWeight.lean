import YangMills.Construction.Matrices.SpecialUnitaryTwo
import Mathlib
noncomputable section
namespace YangMills.Construction.InfiniteLattice
def singleBondWeight (β : ℝ) (g : Matrices.ComplexMatrix2.specialUnitary) : ℂ :=
  Complex.exp (-(β : ℂ) * (1 - (1 / 2 : ℂ) * Matrices.ComplexMatrix2.fullTrace (g : Matrices.ComplexMatrix2)))
end YangMills.Construction.InfiniteLattice
end
