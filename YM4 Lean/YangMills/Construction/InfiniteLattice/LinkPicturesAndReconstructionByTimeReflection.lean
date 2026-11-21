import YangMills.Construction.InfiniteLattice.ReconstructionAtALatticeMirror
import YangMills.Construction.InfiniteLattice.ThreeNamedSetsOfConditionsOnAState
import Mathlib
set_option autoImplicit false
open MeasureTheory
open YangMills.Construction.OneLoopNotation
noncomputable section
namespace YangMills.Construction.LatticeConventions
namespace LinkFrame
open NormalHyperplane
open YangMills.Construction.InfiniteLattice (GaugeField IsShiftInvariant LatticeSymmetry
  localRegionObservables axisStep)
variable (a : Spacing) (μ : Direction)
abbrev linkPlane : NormalHyperplane := axial μ (-((a : ℝ) / 2))
abbrev sitePlane : NormalHyperplane := axial μ 0
theorem linkPicture_normalStep : (linkPicture a μ).normalStep = (axisStep (a : ℝ) μ : Point) := by
  funext i
  by_cases hi : i = μ
  · subst hi
    simp [linkPicture, axisStep, basisVector]
  · simp [linkPicture, axisStep, basisVector, Pi.single_eq_of_ne hi]
theorem linkPicture_tangentStep (ρ : {k : Direction // k ≠ μ}) :
    (linkPicture a μ).tangentStep ρ = (axisStep (a : ℝ) ρ.1 : Point) :=
  linkPicture_normalStep a ρ.1
theorem linkPlane_isLatticeMirror : (linkPlane a μ).IsLatticeMirror (a : ℝ) :=
  ⟨fun _ => ⟨-1, by change -((a : ℝ) / 2) = _; push_cast; ring⟩,
    fun hd => absurd hd (basisVector_not_isFaceDiagonalNormal μ)⟩
def linkReflectionMap (x : Point) : Point := x - (2 * x μ + (a : ℝ)) • basisVector μ
theorem linkReflectionMap_eq_reflect : linkReflectionMap a μ = (linkPlane a μ).reflect := by
  funext x
  have hdot : euclidDot (basisVector μ) x = x μ := by
    simp [euclidDot, basisVector, Pi.single_apply]
  have hnorm : euclidNorm (basisVector μ) ^ 2 = 1 := by
    rw [euclidNorm_sq_eq_dotProduct]
    simp [basisVector]
  simp only [linkReflectionMap, NormalHyperplane.reflect, axial, hdot, hnorm]
  congr 2
  ring
def linkReflection : LatticeSymmetry (a : ℝ) := reflectSymmetry (linkPlane_isLatticeMirror a μ)
theorem linkReflection_toFun :
    (linkReflection a μ).toFun = linkReflectionMap a μ :=
  (linkReflectionMap_eq_reflect a μ).symm
abbrev upperAlgebra : Submodule ℂ (GaugeField (a : ℝ) → ℂ) :=
  upperObservables (a : ℝ) (linkPlane a μ)
theorem coe_upperAlgebra :
    (upperAlgebra a μ : Set (GaugeField (a : ℝ) → ℂ)) =
      localRegionObservables (a : ℝ) {x : Point | -((a : ℝ) / 2) ≤ x μ} := by
  have hside : (linkPlane a μ).upperHalfSpace = {x : Point | -((a : ℝ) / 2) ≤ x μ} := by
    ext x
    have hdot : euclidDot (basisVector μ) x = x μ := by
      simp [euclidDot, basisVector, Pi.single_apply]
    change -((a : ℝ) / 2) ≤ euclidDot (basisVector μ) x ↔ _
    rw [hdot]
    rfl
  change localRegionObservables (a : ℝ) (linkPlane a μ).upperHalfSpace = _
  rw [hside]
section Objects
variable (ν : Measure (GaugeField (a : ℝ))) [IsProbabilityMeasure ν]
structure IsAdmissibleState : Prop where
  shiftInvariant : IsShiftInvariant ν
  reflectionPositive_axial : ∀ q : ℤ,
    IsReflectionPositiveAcrossMirror (axial_isLatticeMirror (a := (a : ℝ)) μ q) ν
theorem isReflectionPositiveAcrossMirror_congr {P P' : NormalHyperplane} (e : P = P')
    (hP : P.IsLatticeMirror (a : ℝ)) (hP' : P'.IsLatticeMirror (a : ℝ))
    (hpos : IsReflectionPositiveAcrossMirror hP ν) : IsReflectionPositiveAcrossMirror hP' ν := by
  subst e
  exact hpos
variable {a μ ν}
theorem IsAdmissibleState.reflectionPositive_linkPlane (hν : IsAdmissibleState a μ ν) :
    IsReflectionPositiveAcrossMirror (linkPlane_isLatticeMirror a μ) ν :=
  isReflectionPositiveAcrossMirror_congr a ν
    (congrArg (axial μ) (by push_cast; ring)) _ _ (hν.reflectionPositive_axial (-1))
theorem IsAdmissibleState.reflectionPositive_sitePlane (hν : IsAdmissibleState a μ ν)
    (hm : (sitePlane μ).IsLatticeMirror (a : ℝ)) : IsReflectionPositiveAcrossMirror hm ν :=
  isReflectionPositiveAcrossMirror_congr a ν
    (congrArg (axial μ) (by simp)) _ _ (hν.reflectionPositive_axial 0)
variable (a μ ν)
def linkForm (f g : upperAlgebra a μ) : ℂ :=
  ∫ U, conjFun ((linkReflection a μ).actOn f.1) U * g.1 U ∂ν
abbrev LinkHilbertSpace : Type := MirrorHilbertSpace (linkPlane_isLatticeMirror a μ) ν
def linkClass (f : upperAlgebra a μ) : LinkHilbertSpace a μ ν :=
  mirrorClass (linkPlane_isLatticeMirror a μ) ν f
def transferOperator : BddOp (LinkHilbertSpace a μ ν) :=
  stepOperator (linkPlane_isLatticeMirror a μ) ν (axisStep (a : ℝ) μ)
def transverseShift (ρ : {k : Direction // k ≠ μ}) : BddOp (LinkHilbertSpace a μ ν) :=
  vectorUnitary (linkPlane_isLatticeMirror a μ) ν (axisStep (a : ℝ) ρ.1)
end Objects
end LinkFrame
end YangMills.Construction.LatticeConventions
end
