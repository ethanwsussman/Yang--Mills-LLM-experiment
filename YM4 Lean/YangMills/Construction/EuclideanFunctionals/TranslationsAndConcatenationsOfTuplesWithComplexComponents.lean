import YangMills.Construction.EuclideanFunctionals.CentredFunctionalOnSeparatedTensors
import YangMills.Construction.EuclideanFunctionals.PulledDownNormsTheInsertionValueAndClassesOfTensors
import YangMills.Construction.Rotation.ProductFunctionsOnFourSpace
import Mathlib
set_option autoImplicit false
open YangMills.Construction.RealPlane
noncomputable section
namespace YangMills.Construction.EuclideanFunctionals.TupleConcat
theorem complexTuple_zero (h : Fin 0 → R4 → ℂ) :
    complexTuple h = toFree [] := by
  simp [complexTuple]
def consEntries {n : ℕ} (h : R4 → ℂ) (hs : Fin n → R4 → ℂ) : Fin (n + 1) → R4 → ℂ :=
  Fin.cons h hs
def singleMulTuple {n : ℕ} (h : R4 → ℂ) (hs : Fin n → R4 → ℂ) : FreeSep :=
  freeMul (singleComponent h) (complexTuple hs)
def consTuple {n : ℕ} (h : R4 → ℂ) (hs : Fin n → R4 → ℂ) : FreeSep :=
  complexTuple (consEntries h hs)
def TranslTuple (z : R4) {n : ℕ} (hs : Fin n → R4 → ℂ) : Prop :=
  (EuclidMotion.transl z).actFree (complexTuple hs) =
    complexTuple fun l => (EuclidMotion.transl z).actFn (hs l)
def SameComponents {n : ℕ} (h : R4 → ℂ) (hs : Fin n → R4 → ℂ) : Prop :=
  MulDefined (singleComponent h) (complexTuple hs) ∧
    SameTensors (singleMulTuple h hs) (consTuple h hs) ∧
    HasSoleTensorComp (n + 1) (tensorOfFns (consEntries h hs))
      (singleMulTuple h hs) ∧
    HasSoleTensorComp (n + 1) (tensorOfFns (consEntries h hs)) (consTuple h hs)
def EqualCases {n : ℕ} (h : R4 → ℂ) (hs : Fin n → R4 → ℂ) : Prop :=
  (n = 0 ∨ (∀ l, IsRealValued (consEntries h hs l)) ∨
      (¬ IsRealValued h ∧ ¬ ∀ l, IsRealValued (hs l))) →
    singleMulTuple h hs = consTuple h hs
def SameValues {n : ℕ} (h : R4 → ℂ) (hs : Fin n → R4 → ℂ) : Prop :=
  ∀ (m : SharpScale) (S : ConnFamily), EuclidFunctionalWithRecon m S →
    centeredFnFree S (singleMulTuple h hs) =
      centeredFnFree S (consTuple h hs)
def SameClasses {n : ℕ} (h : R4 → ℂ) (hs : Fin n → R4 → ℂ) : Prop :=
  (∀ l, supp (consEntries h hs l) ⊆ upperHalf) →
    singleMulTuple h hs ∈ finCombIn upperHalf ∧
    consTuple h hs ∈ finCombIn upperHalf ∧
    ∀ (m : SharpScale) (S : ConnFamily) (σ : EuclidFunctionalWithRecon m S),
      reconClass σ (singleMulTuple h hs) = reconClass σ (consTuple h hs)
def TranslOnComb (z z' : R4) : Prop :=
  (∀ F : FreeSep,
    (EuclidMotion.transl z).actFree ((EuclidMotion.transl z').actFree F) =
      (EuclidMotion.transl (z + z')).actFree F) ∧
  ∀ F F' : FreeSep, MulDefined F F' →
    MulDefined ((EuclidMotion.transl z).actFree F)
        ((EuclidMotion.transl z).actFree F') ∧
      (EuclidMotion.transl z).actFree (freeMul F F') =
        freeMul ((EuclidMotion.transl z).actFree F) ((EuclidMotion.transl z).actFree F')
def ProductFunctionsC1c : Prop :=
  ∀ α ∈ complexProfiles, ∀ φ ∈ realLabels,
    productFunction α φ ∈ C1c ℂ ∧
      ∀ x ∈ supp (productFunction α φ), planeComponent x ∈ tsupport α
def TupleFacts : Prop :=
  (∀ (n : ℕ) (h : R4 → ℂ) (hs : Fin n → R4 → ℂ) (z : R4),
    ComplexComponents (consEntries h hs) →
      TranslTuple z hs ∧ SameComponents h hs ∧
        EqualCases h hs ∧ SameValues h hs ∧ SameClasses h hs) ∧
  (∀ z z' : R4, TranslOnComb z z') ∧
  ProductFunctionsC1c
end YangMills.Construction.EuclideanFunctionals.TupleConcat
