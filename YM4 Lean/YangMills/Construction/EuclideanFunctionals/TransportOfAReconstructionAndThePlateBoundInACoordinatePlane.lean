import YangMills.Construction.EuclideanFunctionals.PlateBoundOfAFunctionalWithReconstruction
import YangMills.Construction.EuclideanFunctionals.TuplesSpansAndActions
import YangMills.Construction.RotationInvariance.DiscsMotionsAndComplexPositionsOfThePlane
import Mathlib
set_option autoImplicit false
open YangMills.Construction.RealPlane
noncomputable section
namespace YangMills.Construction.EuclideanFunctionals
def timePlaneImage (w : hyperoctahedral) : Set R4 :=
  (w : EuclidMotion) '' (Submodule.span ℝ {timeVec, PeriodicLattice.coordVec 0} : Submodule ℝ R4)
def imagePlaneRotation (w : hyperoctahedral) (t : ℝ) : EuclidMotion :=
  (w : EuclidMotion) * rotateMotion t * (w : EuclidMotion)⁻¹
def mappedUpperSpan (w : hyperoctahedral) : Submodule ℂ FreeSep :=
  (finCombIn upperHalf).map (w : EuclidMotion).actFree
def mappedInsertionForm (S : ConnFamily) (w : hyperoctahedral) (B : FreeSep) (k : R4 → ℂ)
    (D : FreeSep) : ℂ :=
  centeredFnFree S ((w : EuclidMotion).actFree
    (freeMul3 (flipConj ((w : EuclidMotion)⁻¹.actFree B))
      (singleComponent ((w : EuclidMotion)⁻¹.actFn k)) ((w : EuclidMotion)⁻¹.actFree D)))
theorem one_actFree (F : FreeSep) : (1 : EuclidMotion).actFree F = F := by
  have hf : ∀ f : R4 → ℝ, (1 : EuclidMotion).actFn f = f := fun f => by
    funext x
    simp [EuclidMotion.actFn, EuclidMotion.one_apply]
  have ht : ∀ X : FnList, (1 : EuclidMotion).actList X = X := fun X => by
    simp [EuclidMotion.actList, funext hf]
  induction F using Finsupp.induction_linear with
  | zero => simp
  | add F G hF hG => rw [map_add, hF, hG]
  | single X z =>
    have h1 : Finsupp.single X z = z • toFree X.1 := by
      rw [toFree_of_mem X.2]
      simp
    rw [h1, map_smul, EuclidMotion.actFree, liftLin_toFree, ht]
theorem inv_actFree_actFree (hA : TupleRules.MotionOnFree) (w : EuclidMotion)
    (F : FreeSep) : w⁻¹.actFree (w.actFree F) = F := by
  rw [(hA w⁻¹ w F).1, inv_mul_cancel, one_actFree]
theorem inv_actFn_actFn {α : Type*} (w : EuclidMotion) (h : R4 → α) :
    w⁻¹.actFn (w.actFn h) = h := by
  funext x
  exact congrArg h (EuclidMotion.apply_inv_apply w⁻¹ x)
theorem mappedInsertionForm_image (hA : TupleRules.MotionOnFree)
    (S : ConnFamily) (w : hyperoctahedral) (F : FreeSep) (h : R4 → ℂ) (A : FreeSep) :
    mappedInsertionForm S w ((w : EuclidMotion).actFree F) ((w : EuclidMotion).actFn h)
        ((w : EuclidMotion).actFree A) =
      centeredFnFree S ((w : EuclidMotion).actFree
        (freeMul3 (flipConj F) (singleComponent h) A)) := by
  rw [mappedInsertionForm, inv_actFree_actFree hA, inv_actFree_actFree hA,
    inv_actFn_actFn]
variable {m : SharpScale} {S : ConnFamily} (σ : EuclidFunctionalWithRecon m S)
def mappedReconClass (w : hyperoctahedral) (B : FreeSep) : σ.space :=
  reconClass σ ((w : EuclidMotion)⁻¹.actFree B)
def ImagePlaneProductBoundWith (w : hyperoctahedral) {p c : ℝ} (_hp : 0 < p)
    (_hc : c ∈ productBoundFractions) (φ : RealPlane → ℝ) (C : ℝ) : Prop :=
  ∀ η ∈ gapWidthRange, ∀ α ∈ complexProfiles, tsupport α ⊆ planeStrip c η →
    ∀ F ∈ finCombIn {y | η / 4 < y 3}, ∀ A ∈ finCombIn {y | η / 4 < y 3},
      ‖mappedInsertionForm S w ((w : EuclidMotion).actFree F)
          ((w : EuclidMotion).actFn (productFunction α φ)) ((w : EuclidMotion).actFree A)‖ ≤
        C * η ^ (-p) * profileL1Norm α * heightNorm σ (η / 4) F * heightNorm σ (η / 4) A
def ImagePlaneProductBound (w : hyperoctahedral) {p c : ℝ} (hp : 0 < p)
    (hc : c ∈ productBoundFractions) : Prop :=
  ∀ φ ∈ realLabels, ∃ C : ℝ, ImagePlaneProductBoundWith σ w hp hc φ C
end YangMills.Construction.EuclideanFunctionals
