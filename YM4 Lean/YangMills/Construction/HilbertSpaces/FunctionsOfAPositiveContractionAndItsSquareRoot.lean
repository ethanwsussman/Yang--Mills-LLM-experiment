import YangMills.Construction.HilbertSpaces.JointSpectralMeasureOfAContractionAndAUnitary
import Mathlib
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YangMills.Construction
open OneLoopNotation ComplexHilbert SpectralMeasures
namespace ContractionUnitary
variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
def pairSpectralMeasure (A U : BddOp H) : PVM intervalCircle H :=
  jointSpectralMeasure A U
theorem isCommutingPair_idOp {A : BddOp H} (hA : IsSymmetricOp A)
    (h0 : OpGE A 0) (h1 : OpLE A (idOp H)) :
    IsCommutingPair A (idOp H) where
  symm := hA
  nonneg := h0
  le_one := h1
  unitary := ⟨fun _ => rfl, Function.surjective_id⟩
  comm := by
    ext x
    rfl
def contractionFn (g : Set.Icc (0 : ℝ) 1 → ℂ) (A : BddOp H) :
    BddOp H :=
  (pairSpectralMeasure A (idOp H)).bddIntegral (g ∘ projIcc)
def sqrtFn : Set.Icc (0 : ℝ) 1 → ℂ := fun t => ((Real.sqrt t : ℝ) : ℂ)
theorem isBddMeasurable_sqrtFn :
    IsBddMeasurable sqrtFn := by
  refine ⟨Complex.measurable_ofReal.comp
    (Real.continuous_sqrt.measurable.comp measurable_subtype_coe), 1, fun t => ?_⟩
  have hle : Real.sqrt (t : ℝ) ≤ 1 := Real.sqrt_le_one.mpr t.2.2
  simpa [sqrtFn, abs_of_nonneg (Real.sqrt_nonneg (t : ℝ))] using hle
def contractionSqrt (A : BddOp H) : BddOp H :=
  contractionFn sqrtFn A
end ContractionUnitary
end YangMills.Construction
end
