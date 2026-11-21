import YangMills.Construction.Continuum.RegularityAndSupportsOfTheUnitKernelsProof
import YangMills.Construction.EuclideanFunctionals.RoomForTheInsertion
import YangMills.Construction.RotationInvariance.MotionsOfPlatesAndQuarterRotations
import Mathlib
set_option autoImplicit false
namespace YangMills.Construction.EuclideanFunctionals
open YangMills.Construction.RealPlane
namespace InsertionRoom
theorem abs_coord_le_euclidNormVec (u : R4) (k : Fin 4) :
    |u k| ≤ YangMills.Construction.TorusMetric.euclidNormVec u := by apply _root_.YangMills.Construction.Parametrix.UnitKernelSupport.abs_apply_le_euclidNormVec <;> assumption
theorem closedBall_subset_slab {w r : ℝ} (hw : w ∈ gapWidthRange) (hr : r ∈ ballFractionRange)
    {p : R4} (hp : |p 3| ≤ w / 8) :
    YangMills.Construction.TestFunctions.closedBallR4 p (r * w) ⊆ {q | |q 3| < w / 4} := by
  intro q hq
  have hdist : YangMills.Construction.TorusMetric.euclidNormVec (q - p) ≤ r * w := hq
  have hcoord : |q 3 - p 3| ≤ r * w := (abs_coord_le_euclidNormVec (q - p) 3).trans hdist
  have hsmall : r * w < 1 / 8 * w := mul_lt_mul_of_pos_right hr.2 hw.1
  have htri := abs_sub_abs_le_abs_sub (q 3) (p 3)
  show |q 3| < w / 4
  linarith
theorem productFunction_supp_subset_slab (hmot : ProductMotions.MotionFacts) {w r : ℝ}
    (hw : w ∈ gapWidthRange) (hr : r ∈ stripFractionRange) {g : RealPlane → ℂ}
    {ψ : RealPlane → ℝ} (hg : g ∈ complexProfiles) (hψ : ψ ∈ realLabels)
    (hstrip : tsupport g ⊆ {q : RealPlane | |q 0| < r * w}) :
    supp (productFunction g ψ) ⊆ {p | |p 3| < w / 4} := by
  intro p hp
  have hplane : |planeComponent p 0| < r * w := hstrip ((hmot.2.2.1 g hg ψ hψ).2 hp).1
  have hsame : planeComponent p 0 = p 3 := by simp [planeComponent]
  rw [hsame] at hplane
  have hsmall : r * w ≤ 1 / 4 * w := mul_le_mul_of_nonneg_right hr.2 hw.1.le
  show |p 3| < w / 4
  linarith
theorem holds (hmot : ProductMotions.MotionFacts) : InsertionRoom.Holds := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro w hw r hr p hp
    exact closedBall_subset_slab hw hr hp
  · intro w hw r hr g hg ψ hψ hstrip
    exact productFunction_supp_subset_slab hmot hw hr hg hψ hstrip
  · intro w hw r hr p hp t ht hsupp G hG G' hG'
    exact ⟨by linarith [hw.1], hG, hG', ht, hsupp.trans (closedBall_subset_slab hw hr hp)⟩
  · intro w hw r hr g hg ψ hψ hstrip G hG G' hG'
    exact ⟨by linarith [hw.1], hG, hG', (hmot.2.2.1 g hg ψ hψ).1,
      productFunction_supp_subset_slab hmot hw hr hg hψ hstrip⟩
end InsertionRoom
end YangMills.Construction.EuclideanFunctionals
