import YangMills.Construction.InfiniteLattice.LatticeGeometryOfTheFrame
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction
open EuclideanFrame (Ambient)
namespace WholeSpace
def maxNorm (x : Ambient) : ℝ := Finset.univ.sup' Finset.univ_nonempty fun μ => |x μ|
end WholeSpace
end YangMills.Construction
