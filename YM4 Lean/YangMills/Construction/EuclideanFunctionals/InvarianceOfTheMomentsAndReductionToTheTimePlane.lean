import YangMills.Construction.EuclideanFunctionals.TransportOfAReconstructionAndThePlateBoundInACoordinatePlane
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open ReflectionPositivity.AxisMirror RealPlane
namespace EuclideanFunctionals.MomentSymmetry
def PermInvariant (S : ConnFamily) : Prop :=
  ∀ n : ℕ, 2 ≤ n → ∀ (ς : Equiv.Perm (Fin n)) (h : Fin n → R4 → ℂ), ComplexComponents h →
    centeredFnFree S (complexTuple (h ∘ ς)) =
      centeredFnFree S (complexTuple h)
def MotionInvariant (S : ConnFamily) : Prop :=
  ∀ A : FreeSep,
    (∀ v : R4, centeredFnFree S ((EuclidMotion.transl v).actFree A) =
      centeredFnFree S A) ∧
    ∀ w ∈ hyperoctahedral, centeredFnFree S (w.actFree A) = centeredFnFree S A
def ImagePlaneBoundEquiv {m : SharpScale} {S : ConnFamily}
    (σ : EuclidFunctionalWithRecon m S) (w : hyperoctahedral) {p c : ℝ} (hp : 0 < p)
    (hc : c ∈ productBoundFractions) : Prop :=
  (∀ η ∈ gapWidthRange, ∀ α ∈ RealPlane.complexProfiles, tsupport α ⊆ planeStrip c η →
    ∀ φ ∈ RealPlane.realLabels,
    ∀ F ∈ finCombIn {y | η / 4 < y 3}, ∀ A ∈ finCombIn {y | η / 4 < y 3},
      mappedInsertionForm S w ((w : EuclidMotion).actFree F)
          ((w : EuclidMotion).actFn (RealPlane.productFunction α φ)) ((w : EuclidMotion).actFree A) =
        insertion S F (RealPlane.productFunction α φ) A) ∧
  (∀ φ ∈ RealPlane.realLabels, ∀ C : ℝ,
    ImagePlaneProductBoundWith σ w hp hc φ C ↔ ProductBoundWith σ hp hc φ C) ∧
  (ImagePlaneProductBound σ w hp hc ↔ ProductBoundWithExponent σ hp hc)
def TwoPointInvariant (S : ConnFamily) (r : EuclidMotion) : Prop :=
  ∀ f₁ f₂ : R4 → ℝ, [f₁, f₂] ∈ sepN 2 →
    Ambient.evalOrZero (S.fn 2 le_rfl) [r.actFn f₁, r.actFn f₂] =
      Ambient.evalOrZero (S.fn 2 le_rfl) [f₁, f₂]
def ReductionHolds : Prop :=
  ∀ (m : SharpScale) (S : ConnFamily) (σ : EuclidFunctionalWithRecon m S),
    PermInvariant S ∧ MotionInvariant S ∧
    (∀ (w : hyperoctahedral) (p c : ℝ) (hp : 0 < p) (hc : c ∈ productBoundFractions),
      ImagePlaneBoundEquiv σ w hp hc) ∧
    ∀ (w : hyperoctahedral) (t : ℝ),
      TwoPointInvariant S (imagePlaneRotation w t) ↔
        TwoPointInvariant S (rotateMotion t)
end EuclideanFunctionals.MomentSymmetry
end YangMills.Construction
