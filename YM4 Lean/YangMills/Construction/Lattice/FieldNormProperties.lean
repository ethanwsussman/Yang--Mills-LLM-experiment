import YangMills.Construction.Lattice.LocalizedDecayBounds
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.PeriodicLattice
open ScaledFun
variable {d N : ℕ}
variable (d) in
structure SiteFunNormFacts (s : Mesh N) : Prop where
  abs_le_maxNorm (f : SiteFun d s) (x : GridPoint d s) : |f x| ≤ SiteFun.maxNorm f
  maxNorm_nonneg (f : SiteFun d s) : 0 ≤ SiteFun.maxNorm f
  holderSemi_nonneg (α : ℝ) (f : SiteFun d s) : 0 ≤ SiteFun.holderSemi α f
  le_holderSemi (α : ℝ) (f : SiteFun d s) (x y : GridPoint d s)
      (hpos : 0 < taxicabDist (x : Torus d N) y) (hle : taxicabDist (x : Torus d N) y ≤ 1) :
    taxicabDist (x : Torus d N) y ^ (-α) * |f x - f y| ≤ SiteFun.holderSemi α f
end YangMills.Construction.PeriodicLattice
