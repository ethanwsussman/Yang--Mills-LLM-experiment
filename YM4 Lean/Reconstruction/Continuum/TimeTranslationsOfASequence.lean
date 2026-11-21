import Reconstruction.Continuum.HilbertSpaceOfASequenceItsTimeTranslationsAndTheSubspaceAtOrderedPositiveTimes
import Mathlib
set_option autoImplicit false
open scoped NNReal
noncomputable section
namespace YangMills.Construction.ConfigSpace
def FlatSequence.IsTranslationInvariant (A : FlatSequence) : Prop :=
  ∀ (m : ℕ) (v : Fin 4 → ℝ) (f : schwartzFlatOffDiagonal (m + 1))
    (hv : shiftAct v f.1 ∈ schwartzFlatOffDiagonal (m + 1)),
    A.atSucc m ⟨_, hv⟩ = A.atSucc m f
def FlatSequence.timeShiftFamily (A : FlatSequence) (s : ℝ≥0) :
    OneLoopNotation.BddOp A.HilbertCompletion :=
  A.timeShiftOp s
def vacuumSeq : (q : ℕ) → FnOrScalar q
  | 0 => (1 : ℂ)
  | q + 1 => zeroOfDegree (q + 1)
def FlatSequence.smoothPositiveTimeClasses
    (A : FlatSequence) : Set A.HilbertCompletion :=
  {χ | ∃ F : AdmissibleSeq,
    (∀ q : ℕ, TestSpaces.succComponent (gradedMembers (seqValues F)) q ∈
      TestSpaces.smoothCompactSupp (TestSpaces.increasingPositiveTimes (q + 1))) ∧
    χ = A.admClass F}
structure FlatSequence.HasTimeShiftSemigroup (A : FlatSequence) : Prop where
  hermitian : SesquilinearForms.IsHermitianForm A.spanForm
  shift_symm : ∀ (F G : AdmissibleSeq) (s : ℝ), 0 ≤ s →
    A.reflectionPairing (seqValues F) (timeShift s (seqValues G)) =
      A.reflectionPairing (timeShift s (seqValues F)) (seqValues G)
  nonexpanding : A.TimeShiftNonexpanding
  shiftOp_spec : ∀ s : ℝ, 0 ≤ s →
    A.IsTimeShiftContraction s (A.timeShiftOp s)
  semigroup : SesquilinearForms.IsOpSemigroup A.timeShiftFamily
  strongCont : SesquilinearForms.StronglyContinuous A.timeShiftFamily
  symmetric : ∀ s : ℝ≥0,
    ComplexHilbert.IsSymmetricOp (A.timeShiftFamily s)
  contractive : ∀ s : ℝ≥0, SesquilinearForms.IsContractive (A.timeShiftFamily s)
  family_zero : A.timeShiftFamily 0 =
    ComplexHilbert.idOp A.HilbertCompletion
  vacuum : ∃ Ω : AdmissibleSeq, seqValues Ω = vacuumSeq ∧
    A.admClass Ω ∈ A.positiveTimeSubspace ∧ ‖A.admClass Ω‖ = 1 ∧
      ∀ s : ℝ≥0, A.timeShiftFamily s (A.admClass Ω) = A.admClass Ω
  mapsTo_positiveTimeSubspace : ∀ (s : ℝ≥0), ∀ χ ∈ A.positiveTimeSubspace,
    A.timeShiftFamily s χ ∈ A.positiveTimeSubspace
  positiveTimeSubspace_eq_closure : (A.positiveTimeSubspace : Set A.HilbertCompletion) =
    ComplexHilbert.seqClosureOf A.smoothPositiveTimeClasses
def TimeShiftSemigroupStatement : Prop :=
  ∀ A : FlatSequence, IsLinearFunctionalSeq A → IsContinuousSeq A →
    IsOSPositive A → A.IsTranslationInvariant → A.HasTimeShiftSemigroup
end YangMills.Construction.ConfigSpace
end
