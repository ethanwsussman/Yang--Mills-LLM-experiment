import YangMills.Construction.EuclideanFunctionals.PulledDownNormsTheInsertionValueAndClassesOfTensors
import Mathlib
set_option autoImplicit false
open scoped InnerProductSpace
noncomputable section
namespace YangMills.Construction.EuclideanFunctionals.OneInsertionOperator
variable {m : SharpScale} {S : ConnFamily}
def liftComponent (c : ℝ) (h : R4 → ℂ) : R4 → ℂ :=
  (EuclidMotion.transl (c • timeVec)).actFn h
def liftOnce (c : ℝ) (F : FreeSep) : FreeSep :=
  (EuclidMotion.transl (c • timeVec)).actFree F
def liftTwice (c : ℝ) (A : FreeSep) : FreeSep :=
  (EuclidMotion.transl ((2 * c) • timeVec)).actFree A
def prependComponent (c : ℝ) (h : R4 → ℂ) (A : FreeSep) : FreeSep :=
  freeMul (singleComponent (liftComponent c h)) (liftTwice c A)
def headTensor {q : ℕ} (g : R4 → ℂ) (a : TestSpaces.PointTuple q → ℂ) :
    TestSpaces.PointTuple (q + 1) → ℂ :=
  fun x => g (x 0) * a fun l => x l.succ
def InsertionBounded (σ : EuclidFunctionalWithRecon m S) (c : ℝ) (h : R4 → ℂ)
    (b : ℝ) : Prop :=
  ∀ F ∈ finCombIn {x | c < x 3}, ∀ A ∈ finCombIn {x | c < x 3},
    ‖insertion S F h A‖ ≤ b * heightNorm σ c F * heightNorm σ c A
structure PrependLinear (c : ℝ) (h : R4 → ℂ) : Prop where
  mem_upper : ∀ A ∈ finCombIn upperHalf,
    prependComponent c h A ∈ finCombIn upperHalf
  map_add_smul : ∀ A ∈ finCombIn upperHalf, ∀ A' ∈ finCombIn upperHalf,
    ∀ z : ℂ, prependComponent c h (A + z • A') =
      prependComponent c h A + z • prependComponent c h A'
structure PrependComponents (c : ℝ) (h : R4 → ℂ) : Prop where
  comp_zero : ∀ A ∈ finCombIn upperHalf,
    tensorCompZero (prependComponent c h A) = 0
  comp_succ : ∀ A ∈ finCombIn upperHalf, ∀ q : ℕ,
    tensorComp (q + 1) (prependComponent c h A) =
      headTensor (liftComponent c h) (translateArgs ((2 * c) • timeVec) (tensorComp q A))
  comp_succ_apply : ∀ A ∈ finCombIn upperHalf, ∀ (q : ℕ)
    (x : TestSpaces.PointTuple (q + 1)),
    tensorComp (q + 1) (prependComponent c h A) x =
      h (x 0 - c • timeVec) * tensorComp q A fun l => x l.succ - (2 * c) • timeVec
  comp_one : ∀ A ∈ finCombIn upperHalf, ∀ x : TestSpaces.PointTuple 1,
    tensorComp 1 (prependComponent c h A) x = tensorCompZero A * liftComponent c h (x 0)
def ShiftGivesInsertion (σ : EuclidFunctionalWithRecon m S) (c : ℝ)
    (h : R4 → ℂ) (b : ℝ) : Prop :=
  ∀ F ∈ finCombIn upperHalf, ∀ A ∈ finCombIn upperHalf,
    liftOnce c F ∈ finCombIn {x | c < x 3} ∧
    liftOnce c A ∈ finCombIn {x | c < x 3} ∧
    heightNorm σ c (liftOnce c F) = ‖reconClass σ F‖ ∧
    ⟪reconClass σ F, reconClass σ (prependComponent c h A)⟫_ℂ =
      insertion S (liftOnce c F) h (liftOnce c A) ∧
    ‖reconClass σ (prependComponent c h A)‖ ≤ b * ‖reconClass σ A‖
def ActsOnReconClasses (σ : EuclidFunctionalWithRecon m S) (c : ℝ) (h : R4 → ℂ)
    (B : σ.space →L[ℂ] σ.space) : Prop :=
  ∀ A ∈ finCombIn upperHalf, B (reconClass σ A) = reconClass σ (prependComponent c h A)
def insertionOp (σ : EuclidFunctionalWithRecon m S) (c : ℝ) (h : R4 → ℂ) :
    σ.space →L[ℂ] σ.space :=
  Classical.epsilon (ActsOnReconClasses σ c h)
def MatrixElementsAreInsertion (σ : EuclidFunctionalWithRecon m S) (c : ℝ)
    (h : R4 → ℂ) (B : σ.space →L[ℂ] σ.space) : Prop :=
  ∀ F ∈ finCombIn {x | c < x 3}, ∀ A ∈ finCombIn {x | c < x 3},
    ⟪reconClass σ (pullDown c F), B (reconClass σ (pullDown c A))⟫_ℂ =
      insertion S F h A
def statement : Prop :=
  ∀ (m : SharpScale) (S : ConnFamily) (σ : EuclidFunctionalWithRecon m S) (c : ℝ)
    (h : R4 → ℂ) (b : ℝ),
    0 < c → h ∈ C1c ℂ → supp h ⊆ {x | |x 3| < c} → 0 ≤ b →
    InsertionBounded σ c h b →
    PrependLinear c h ∧ PrependComponents c h ∧ ShiftGivesInsertion σ c h b ∧
      (∃! B : σ.space →L[ℂ] σ.space, ActsOnReconClasses σ c h B) ∧
      ActsOnReconClasses σ c h (insertionOp σ c h) ∧
      ‖insertionOp σ c h‖ ≤ b ∧
      MatrixElementsAreInsertion σ c h (insertionOp σ c h)
end YangMills.Construction.EuclideanFunctionals.OneInsertionOperator
