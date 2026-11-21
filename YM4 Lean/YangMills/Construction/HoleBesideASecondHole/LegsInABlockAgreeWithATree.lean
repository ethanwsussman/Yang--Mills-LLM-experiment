import YangMills.Construction.HoleBesideASecondHole.CutsLumpsBasesAndContours
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction
namespace BlockTrees
open BlockAverages LumpContours
variable {F : BlockFrame}
def blockCurvatureNorm {j : ℕ} (X : F.GaugeField j) (y : F.Site (j + 1)) : ℝ :=
  Real.sqrt (∑ p ∈ cutPlaquettes (sitesBelow j y), plaquetteDefect X p ^ 2)
def blockTreeTransport {j : ℕ} (X : F.GaugeField j) (y : F.Site (j + 1)) (o : Fin 4 → ℤ) :
    UnitQuaternion :=
  pathHolonomy X (refineSite y) (axisPath o 1)
def LegNearBlockTree : Prop :=
  ∀ (F : BlockFrame) (j : ℕ), j < F.top → Odd F.blockSide → IsAdmissibleAmbient F →
    ∀ (X : F.GaugeField j) (y : F.Site (j + 1))
    (o o' : Fin 4 → ℤ) (π : Equiv.Perm (Fin 4)), o ∈ centredCube F.blockSide → o' ∈ centredCube F.blockSide →
    ‖((pathHolonomy X (refineSite y + siteOfCoords j o) (axisPath (o' - o) π) : UnitQuaternion) : ℍ[ℝ]) -
        (((blockTreeTransport X y o)⁻¹ * blockTreeTransport X y o' : UnitQuaternion) : ℍ[ℝ])‖ ≤
      16 * (F.blockSide : ℝ) * blockCurvatureNorm X y
end BlockTrees
end YangMills.Construction
end
