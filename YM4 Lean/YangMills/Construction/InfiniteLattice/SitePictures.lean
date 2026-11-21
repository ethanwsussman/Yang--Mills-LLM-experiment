import YangMills.Construction.InfiniteLattice.ClosedSidesOfABond
import YangMills.Construction.InfiniteLattice.LinkPicturesAndReconstructionByTimeReflection
import Mathlib
set_option autoImplicit false
open MeasureTheory
noncomputable section
namespace YangMills.Construction
open OneLoopNotation
namespace LatticeConventions
namespace SiteFrame
open NormalHyperplane
open InfiniteLattice (GaugeField LatticeSymmetry LatticePoint localRegionObservables axisStep)
variable (a : Spacing) (μ : Direction)
abbrev vertexPlane : NormalHyperplane := axial μ 0
abbrev midPlane : NormalHyperplane := axial μ ((a : ℝ) / 2)
theorem sitePicture_normalStep : (sitePicture a μ).normalStep = (axisStep (a : ℝ) μ : Point) := by apply _root_.YangMills.Construction.LatticeConventions.LinkFrame.linkPicture_normalStep <;> assumption
theorem sitePicture_tangentStep (κ : {l : Direction // l ≠ μ}) :
    (sitePicture a μ).tangentStep κ = (axisStep (a : ℝ) κ.1 : Point) := by apply _root_.YangMills.Construction.LatticeConventions.LinkFrame.linkPicture_tangentStep <;> assumption
theorem vertexPlane_isLatticeMirror : (vertexPlane μ).IsLatticeMirror (a : ℝ) :=
  ⟨fun _ => ⟨0, by change (0 : ℝ) = _; simp⟩,
    fun h => absurd h (basisVector_not_isFaceDiagonalNormal μ)⟩
def siteReflectionMap (x : Point) : Point := x - (2 * x μ) • basisVector μ
theorem siteReflectionMap_eq_reflect : siteReflectionMap μ = (vertexPlane μ).reflect := by
  funext x
  have hd : euclidDot (basisVector μ) x = x μ := by
    simp [euclidDot, basisVector, Pi.single_apply]
  have hn : euclidNorm (basisVector μ) ^ 2 = 1 := by
    rw [euclidNorm_sq_eq_dotProduct]
    simp [basisVector]
  simp only [siteReflectionMap, NormalHyperplane.reflect, axial, hd, hn]
  congr 2
  ring
def siteReflection : LatticeSymmetry (a : ℝ) := reflectSymmetry (vertexPlane_isLatticeMirror a μ)
theorem siteReflection_toFun :
    (siteReflection a μ).toFun = siteReflectionMap μ :=
  (siteReflectionMap_eq_reflect μ).symm
abbrev upperSpace : Submodule ℂ (GaugeField (a : ℝ) → ℂ) :=
  upperObservables (a : ℝ) (vertexPlane μ)
theorem coe_upperSpace :
    (upperSpace a μ : Set (GaugeField (a : ℝ) → ℂ)) =
      localRegionObservables (a : ℝ) {x : Point | 0 ≤ x μ} := by
  have h : (vertexPlane μ).upperHalfSpace = {x : Point | 0 ≤ x μ} := by
    ext x
    have hd : euclidDot (basisVector μ) x = x μ := by
      simp [euclidDot, basisVector, Pi.single_apply]
    change (0 : ℝ) ≤ euclidDot (basisVector μ) x ↔ _
    rw [hd]
    rfl
  change localRegionObservables (a : ℝ) (vertexPlane μ).upperHalfSpace = _
  rw [h]
theorem upperSpace_eq_upperAlgebra
    (h : LinkHalfSpaces.HalfSpaceLocalObservablesEq a μ) :
    upperSpace a μ = LinkFrame.upperAlgebra a μ :=
  SetLike.coe_injective (by
    rw [coe_upperSpace, LinkFrame.coe_upperAlgebra]
    exact h.symm)
section Objects
variable (ν : Measure (GaugeField (a : ℝ))) [IsProbabilityMeasure ν]
variable {a μ ν}
theorem reflectionPositive_vertexPlane (h : LinkFrame.IsAdmissibleState a μ ν) :
    IsReflectionPositiveAcrossMirror (vertexPlane_isLatticeMirror a μ) ν :=
  LinkFrame.isReflectionPositiveAcrossMirror_congr a ν
    (congrArg (axial μ) (by simp)) _ _ (h.reflectionPositive_axial 0)
theorem reflectionPositive_midPlane (h : LinkFrame.IsAdmissibleState a μ ν)
    (h' : (midPlane a μ).IsLatticeMirror (a : ℝ)) : IsReflectionPositiveAcrossMirror h' ν :=
  LinkFrame.isReflectionPositiveAcrossMirror_congr a ν
    (congrArg (axial μ) (by push_cast; ring)) _ _ (h.reflectionPositive_axial 1)
variable (a μ ν)
def siteForm (F F' : upperSpace a μ) : ℂ :=
  ∫ U, conjFun ((siteReflection a μ).actOn F.1) U * F'.1 U ∂ν
abbrev SiteHilbertSpace : Type := MirrorHilbertSpace (vertexPlane_isLatticeMirror a μ) ν
def siteClass (F : upperSpace a μ) : SiteHilbertSpace a μ ν :=
  mirrorClass (vertexPlane_isLatticeMirror a μ) ν F
def transferOperator : BddOp (SiteHilbertSpace a μ ν) :=
  stepOperator (vertexPlane_isLatticeMirror a μ) ν (axisStep (a : ℝ) μ)
def transverseShift (κ : {l : Direction // l ≠ μ}) : BddOp (SiteHilbertSpace a μ ν) :=
  vectorUnitary (vertexPlane_isLatticeMirror a μ) ν (axisStep (a : ℝ) κ.1)
end Objects
end SiteFrame
end LatticeConventions
end YangMills.Construction
end
