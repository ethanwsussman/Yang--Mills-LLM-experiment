import YangMills.Construction.EuclideanFunctionals.PulledDownNormsTheInsertionValueAndClassesOfTensors
import YangMills.Construction.EuclideanFunctionals.TuplesSpansAndActions
import YangMills.Construction.Rotation.ProductFunctionsOnFourSpace
import YangMills.Construction.RotationInvariance.DiscsMotionsAndComplexPositionsOfThePlane
import Mathlib
set_option autoImplicit false
open scoped Pointwise
noncomputable section
namespace YangMills.Construction
open RealPlane
namespace EuclideanFunctionals.MotionMulRules
abbrev shiftFn (z : R4) (f : R4 → ℂ) : R4 → ℂ :=
  (EuclidMotion.transl z).actFn f
abbrev shiftFree (z : R4) : FreeSep →ₗ[ℂ] FreeSep :=
  (EuclidMotion.transl z).actFree
def EmptyAndShiftRules : Prop :=
  ∀ (z w : R4) (F : FreeSep),
    shiftFree z (shiftFree w F) = shiftFree (z + w) F ∧
    shiftFree 0 F = F ∧
    shiftFree z (toFree []) = toFree [] ∧
    flipConj (toFree []) = toFree [] ∧
    freeMul (toFree []) F = F ∧
    freeMul F (toFree []) = F
def ShiftMulRule : Prop :=
  ∀ (z : R4) (F A : FreeSep), MulDefined F A →
    MulDefined (shiftFree z F) (shiftFree z A) ∧
    shiftFree z (freeMul F A) = freeMul (shiftFree z F) (shiftFree z A)
def MulAssocRule : Prop :=
  ∀ F A B : FreeSep, MulDefined F A → MulDefined F B →
    MulDefined A B →
    MulDefined (freeMul F A) B ∧
    MulDefined F (freeMul A B) ∧
    freeMul (freeMul F A) B = freeMul F (freeMul A B) ∧
    freeMul3 F A B = freeMul F (freeMul A B)
def ComplexTupleRules : Prop :=
  ∀ (n : ℕ) (h : Fin n → R4 → ℂ) (O : Set R4), ComplexComponents h → IsOpen O →
    (∀ l, supp (h l) ⊆ O) →
    complexTuple h ∈ finCombIn O ∧
    tensorComp n (complexTuple h) = tensorOfFns h ∧
    tensorCompZero (complexTuple h) = 0 ∧
    (∀ q, 1 ≤ q → q ≠ n → tensorComp q (complexTuple h) = 0) ∧
    ∀ z : R4, shiftFree z (complexTuple h) =
      complexTuple fun l => shiftFn z (h l)
def headTimesTail {m : ℕ} (h : Fin (m + 2) → R4 → ℂ) : FreeSep :=
  freeMul (singleComponent (h 0)) (complexTuple fun l : Fin (m + 1) => h l.succ)
def HeadTailRules : Prop :=
  ∀ (m : ℕ) (h : Fin (m + 2) → R4 → ℂ) (O : Set R4), ComplexComponents h → IsOpen O →
    (∀ l, supp (h l) ⊆ O) →
    MulDefined (singleComponent (h 0))
      (complexTuple fun l : Fin (m + 1) => h l.succ) ∧
    headTimesTail h ∈ finCombIn O ∧
    SameTensors (headTimesTail h) (complexTuple h) ∧
    (O ⊆ upperHalf →
      ∀ (M : SharpScale) (S : ConnFamily) (σ : EuclidFunctionalWithRecon M S),
        reconClass σ (headTimesTail h) = reconClass σ (complexTuple h))
def SingleEntryValueZero : Prop :=
  ∀ (M : SharpScale) (S : ConnFamily), EuclidFunctionalWithRecon M S →
    ∀ (n : ℕ) (h : Fin n → R4 → ℂ) (hh : ComplexComponents h),
      centeredFnFree S (singleComponent (h ⟨0, hh.one_le⟩)) = 0
def ShiftFlipConjRule : Prop :=
  ∀ (b : R4) (F : FreeSep),
    shiftFree b (flipConj F) =
      flipConj (shiftFree (timeFlip b) F)
def MovedSupportRules : Prop :=
  ∀ (f : R4 → ℂ), Continuous f → HasCompactSupport f → ∀ z : R4,
    supp (shiftFn z f) = supp f + {z} ∧
    supp (timeFlip.actFn f) = timeFlip '' supp f
def FinCombMonotone : Prop :=
  ∀ O O' : Set R4, IsOpen O → IsOpen O' → O ⊆ O' → finCombIn O ≤ finCombIn O'
def FinCombAboveLevel : Prop :=
  ∀ (b : R4) (c : ℝ), ∀ F ∈ finCombIn {x | c < x 3},
    shiftFree b F ∈ finCombIn {x | c + b 3 < x 3} ∧
    flipConj F ∈ finCombIn {x | x 3 < -c}
def liftedInsertion (c : ℝ) (h : R4 → ℂ) (A : FreeSep) : FreeSep :=
  freeMul (singleComponent (shiftFn (c • timeVec) h)) (shiftFree ((2 * c) • timeVec) A)
def InsertionRules : Prop :=
  ∀ c : ℝ, 0 < c → ∀ h ∈ C1c ℂ, supp h ⊆ {x | |x 3| < c} →
    (∀ A ∈ finCombIn upperHalf,
      MulDefined (singleComponent (shiftFn (c • timeVec) h))
        (shiftFree ((2 * c) • timeVec) A) ∧
      liftedInsertion c h A ∈ finCombIn upperHalf) ∧
    (∀ A ∈ finCombIn upperHalf, ∀ B ∈ finCombIn upperHalf, ∀ z : ℂ,
      liftedInsertion c h (A + z • B) = liftedInsertion c h A + z • liftedInsertion c h B) ∧
    ∀ F ∈ finCombIn {x | c < x 3}, ∀ A ∈ finCombIn {x | c < x 3},
      TupleRules.MulDefined3 (flipConj F)
        (singleComponent h) A
def VacNormOne : Prop :=
  ∀ (M : SharpScale) (S : ConnFamily) (σ : EuclidFunctionalWithRecon M S),
    ‖σ.recon.vac‖ = 1
def profileRe (α : RealPlane → ℂ) : RealPlane → ℂ :=
  fun y => ((α y).re : ℂ)
def profileIm (α : RealPlane → ℂ) : RealPlane → ℂ :=
  fun y => ((α y).im : ℂ)
def ProductFunctionRules : Prop :=
  ∀ α ∈ complexProfiles, ∀ φ ∈ realLabels,
    productFunction α φ ∈ C1c ℂ ∧
    supp (productFunction α φ) ⊆
      {x | planeComponent x ∈ tsupport α ∧ orthogonalComponent x ∈ tsupport φ} ∧
    (fun x => ((productFunction α φ x).re : ℂ)) = productFunction (profileRe α) φ ∧
    (fun x => ((productFunction α φ x).im : ℂ)) = productFunction (profileIm α) φ ∧
    profileRe α ∈ complexProfiles ∧
    profileIm α ∈ complexProfiles ∧
    tsupport (profileRe α) ⊆ tsupport α ∧
    tsupport (profileIm α) ⊆ tsupport α ∧
    ∫ x : R4, ‖productFunction α φ x‖ = profileL1Norm α * ∫ y, ‖φ y‖
def ShiftedProductInStrip : Prop :=
  ∀ α ∈ complexProfiles, ∀ φ ∈ realLabels, ∀ t : ℝ, 0 < t → (∀ y' ∈ tsupport α, |y' 0| < t) →
    ∀ y : RealPlane,
      supp ((planeShift y).actFn (productFunction α φ)) ⊆ {x | |x 3 - y 0| < t}
def MotionMulTupleRules : Prop :=
  EmptyAndShiftRules ∧ ShiftMulRule ∧
    MulAssocRule ∧ ComplexTupleRules ∧ HeadTailRules ∧ SingleEntryValueZero ∧
    ShiftFlipConjRule ∧ MovedSupportRules ∧ FinCombMonotone ∧
    FinCombAboveLevel ∧ InsertionRules ∧ VacNormOne ∧ ProductFunctionRules ∧
    ShiftedProductInStrip
end EuclideanFunctionals.MotionMulRules
end YangMills.Construction
