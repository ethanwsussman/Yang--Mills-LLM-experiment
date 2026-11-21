import Reconstruction.Continuum.OrderedTimes
import YangMills.Construction.HilbertSpaces.CompletionsAdjointsProjectionValuedMeasuresAndWeakIntegrals
import YangMills.Construction.Continuum.TestSpacesAndNormsOfTheAxiomsOnSchwartzFunctions
import YangMills.Construction.Continuum.VectorSpaceOfAdmissibleSequences
import Mathlib
set_option autoImplicit false
open YangMills.Construction.ProjectionMeasures YangMills.Construction.OneLoopNotation
noncomputable section
namespace YangMills.Construction.ConfigSpace
def FlatSequence.spanForm (S : FlatSequence) (x y : admissibleSpan) : ℂ :=
  S.reflectionPairing x.1 y.1
def FlatSequence.seminorm (S : FlatSequence) (x : GradedSeq) : ℝ :=
  Real.sqrt (S.reflectionPairing x x).re
abbrev FlatSequence.HilbertCompletion (S : FlatSequence) : Type :=
  FormQuotientCompletion S.spanForm
def FlatSequence.spanClass (S : FlatSequence) (x : admissibleSpan) : S.HilbertCompletion :=
  quotientClass S.spanForm x
def FlatSequence.admClass (S : FlatSequence) (Φ : AdmissibleSeq) : S.HilbertCompletion :=
  S.spanClass (toAdmissibleSpan Φ)
def timeShift (t : ℝ) (x : GradedSeq) : GradedSeq :=
  fun _ => shiftActAt (t • SchwartzAxioms.timeUnitVector) (x _)
def FlatSequence.TimeShiftNonexpanding (S : FlatSequence) : Prop :=
  ∀ (Φ : AdmissibleSeq) (t : ℝ), 0 ≤ t →
    S.seminorm (timeShift t (seqValues Φ)) ≤ S.seminorm (seqValues Φ)
structure FlatSequence.IsTimeShiftContraction (S : FlatSequence) (t : ℝ)
    (A : BddOp S.HilbertCompletion) : Prop where
  contractive : SesquilinearForms.IsContractive A
  apply_admClass : ∀ (Φ : AdmissibleSeq)
    (h : timeShift t (seqValues Φ) ∈ admissibleSpan),
    A (S.admClass Φ) = S.spanClass ⟨_, h⟩
def FlatSequence.timeShiftOp (S : FlatSequence) (t : ℝ) : BddOp S.HilbertCompletion :=
  Classical.epsilon (S.IsTimeShiftContraction t)
def gradedMembers (x : GradedSeq) : (q : ℕ) → Motions.TensorVal ℂ q
  | 0 => x 0
  | q + 1 => x (q + 1)
def FlatSequence.positiveTimeClasses (S : FlatSequence) : Set S.HilbertCompletion :=
  {χ | ∃ Φ : AdmissibleSeq,
    TestSpaces.IsIncreasingPositiveTimeSeq (gradedMembers (seqValues Φ)) ∧
      χ = S.admClass Φ}
def FlatSequence.positiveTimeSubspace (S : FlatSequence) : Submodule ℂ S.HilbertCompletion :=
  (Submodule.span ℂ S.positiveTimeClasses).topologicalClosure
end YangMills.Construction.ConfigSpace
end
