import YangMills.Construction.Lattice.PeriodicLattices
import YangMills.Construction.Matrices.SpecialUnitaryTwo
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
namespace Averaging
structure LayerwiseParameters (d N L K m : ℕ) (G : Submonoid Matrices.ComplexMatrix2) (ℓ : ℝ) :
    Prop where
  dim_eq : d = 4
  size_eq : N = 2
  group_eq : G = Matrices.ComplexMatrix2.specialUnitary
  odd_factor : Odd L
  thirteen_le_factor : 13 ≤ L
  cutoff_pos : 0 < K
  exponent_pos : 0 < m
  side_eq : ℓ = PeriodicLattice.torusSide L m
namespace LayerwiseParameters
def halfFactor (L : ℕ) : ℝ := ((L : ℝ) - 1) / 2
end LayerwiseParameters
end Averaging
end YangMills.Construction
end
