import YangMills.Construction.InfiniteLattice.ExpansionsMeetTheConditionsOfTheReconstruction
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
namespace LatticeConventions
open MirrorExpansions
def DiagonalPictureExpansion.Statement : Prop :=
  ∀ (a : Spacing) (μ ν : Direction) (hne : μ ≠ ν) (c : ℝ)
    (hc : ∃ q : ℤ, c = (q : ℝ) * (a : ℝ)),
    IsPictureExpansion a (diagonalPicture a μ ν hne c hc)
      (basisVector μ + basisVector ν) (2 * (a : ℝ)) 1
end LatticeConventions
end YangMills.Construction
end
