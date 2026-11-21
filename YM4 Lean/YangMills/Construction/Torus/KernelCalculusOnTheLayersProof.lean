import YangMills.Construction.Torus.DistanceAveragesWholePairMatricesAndNormsProof
import YangMills.Construction.Torus.KernelCalculusOnTheLayers
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.Weighted.LayerKernels
variable {D : TorusData} (B : SeparatedChain D)
theorem siteScale_pos (y : D.Space) : 0 < B.siteScale y := by apply _root_.YangMills.Construction.Weighted.AvgMatrix.siteScale_pos <;> assumption
theorem allSites_finite : Finite ↥B.allSites := by apply _root_.YangMills.Construction.Weighted.AvgMatrix.allSites_finite <;> assumption
def invScaleOn (W : Set D.Space) : Module.End ℝ ↥(B.layerSpaceOn W) :=
  (B.mulOp fun y => (B.siteScale y)⁻¹).restrict fun w hw y hy => by
    change (B.siteScale y)⁻¹ * w y = 0
    rw [hw y hy, mul_zero]
end YangMills.Construction.Weighted.LayerKernels
