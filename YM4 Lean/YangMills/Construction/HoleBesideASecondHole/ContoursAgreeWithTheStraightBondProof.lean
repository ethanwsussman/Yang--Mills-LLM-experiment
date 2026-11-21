import YangMills.Construction.HoleBesideASecondHole.BondSpreadBelowCurvatureProof
import YangMills.Construction.HoleBesideASecondHole.ContoursAgreeWithTheStraightBond
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction
open BlockAverages LumpContours BondContours SquareDescent
namespace ContourComparison
variable {F : BlockFrame}
theorem contourHolonomy_sub_straight_sq_le (j : ℕ) (hj : j < F.top) (hL : Odd F.blockSide)
    (hA : IsAdmissibleAmbient F) (W : F.GaugeField j) (c : F.Site (j + 1) × Fin 4)
    (e : (Fin 4 → ℤ) × Equiv.Perm (Fin 4)) (he : e ∈ allContours F) :
    ‖((contourHolonomy W c e : UnitQuaternion) : ℍ[ℝ]) -
        (pathHolonomy W (refineSite c.1) (List.replicate F.blockSide (c.2, true)) : UnitQuaternion)‖ ^ 2 ≤
      16 * (F.blockSide : ℝ) ^ 2 * ∑ p ∈ blockPairPlaquettes c, plaquetteDefect W p ^ 2 := by apply _root_.YangMills.Construction.BondContours.contourHolonomy_deviation_sq_le <;> assumption
end ContourComparison
theorem BondContours.contourStraightBondStatement_holds : BondContours.contourStraightBondStatement :=
  fun _ j hj hL hA W c e he => ContourComparison.contourHolonomy_sub_straight_sq_le j hj hL hA W c e he
end YangMills.Construction
end
