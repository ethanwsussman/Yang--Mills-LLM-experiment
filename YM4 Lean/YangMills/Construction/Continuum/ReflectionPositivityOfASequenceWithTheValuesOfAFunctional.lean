import YangMills.Construction.Continuum.AxiomsOfOsterwalderAndSchrader
import YangMills.Construction.Continuum.ConditionsOnASequenceOfFunctionalsOnFlatSpaces
import YangMills.Construction.Continuum.SchwartzTestsAndMollifiers
import YangMills.Construction.ReflectionPositivity.FormOfAFunctionalOnSeparatedTuples
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ReflectionPositivityFromValues
def AgreesOnTensors (σ : TestSpaces.SepTuple → ℝ) (S : ConfigSpace.FlatSequence) : Prop :=
  ∀ (m : ℕ) (A : TestSpaces.SepTupleOfCard (m + 1)), TestSpaces.HasSmoothComponents Set.univ A.1 →
    ∀ h : TestSpaces.tensorProdComplex A.1 ∈ ConfigSpace.schwartzFlatOffDiagonal (m + 1),
      S.atSucc m ⟨_, h⟩ = (σ ⟨m + 1, A⟩ : ℂ)
def IsFormPositive (σ : TestSpaces.SepTuple → ℝ) : Prop :=
  ∀ F : ReflectionPositivity.TupleForm.PositiveSpan,
    (WightmanReconstruction.linearExtension σ
        (SeparatedTuples.formalMul (ReflectionPositivity.TupleForm.reflectConj F) F.1)).im = 0 ∧
      0 ≤ (WightmanReconstruction.linearExtension σ
        (SeparatedTuples.formalMul (ReflectionPositivity.TupleForm.reflectConj F) F.1)).re
def Statement : Prop :=
  ∀ (σ : TestSpaces.SepTuple → ℝ) (S : ConfigSpace.FlatSequence),
    TestSpaces.IsSepFunctional σ → ConfigSpace.IsLinearFunctionalSeq S →
    ConfigSpace.IsContinuousSeq S → AgreesOnTensors σ S →
    IsFormPositive σ → ConfigSpace.IsOSPositive S
end YangMills.Construction.ReflectionPositivityFromValues
end
