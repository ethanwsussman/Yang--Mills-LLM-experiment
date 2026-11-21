import YangMills.Construction.HoleBesideASecondHole.BondSpreadBelowCurvature
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction
namespace BondContours
open BlockAverages LumpContours SquareDescent
def contourStraightBondStatement : Prop :=
  ∀ (F : BlockFrame) (j : ℕ), j < F.top → Odd F.blockSide → IsAdmissibleAmbient F →
    ∀ (A : F.GaugeField j) (c : F.Site (j + 1) × Fin 4)
    (e : (Fin 4 → ℤ) × Equiv.Perm (Fin 4)), e ∈ allContours F →
    ‖((contourHolonomy A c e : UnitQuaternion) : ℍ[ℝ]) -
        (pathHolonomy A (refineSite c.1) (List.replicate F.blockSide (c.2, true)) : UnitQuaternion)‖ ^ 2 ≤
      16 * (F.blockSide : ℝ) ^ 2 * ∑ p ∈ blockPairPlaquettes c, plaquetteDefect A p ^ 2
end BondContours
end YangMills.Construction
end
