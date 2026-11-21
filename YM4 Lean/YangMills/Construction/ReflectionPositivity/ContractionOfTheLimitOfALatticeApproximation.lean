import YangMills.Construction.Conventions.ContinuumLimitsOfLatticeApproximationsDefs
import YangMills.Construction.ReflectionPositivity.BoundedLatticeApproximationsAndTheirC1Constants
import YangMills.Construction.ReflectionPositivity.FormOfAFunctionalOnSeparatedTuples
import Mathlib
noncomputable section
namespace YangMills.Construction.ReflectionPositivity.LimitContraction
def twiceTimeShift (t : ℝ) : InfiniteLattice.AmbientSpace :=
  (2 * t) • LatticeConventions.basisVector TimeAxis.timeIdx
def ContractionBound : Prop :=
  ∀ (D : AxisMirror.MirrorData) (T : LimitConventions.ApproxTriple D.L)
    (σ : SeparatedTuples.TupleFunctional),
    ApproximatingSequences.LatticeApproximation.IsBoundedForSomeM D T →
    LimitConventions.ApproxTriple.IsReflPos T →
    LimitConventions.ApproxTriple.ConvergesTo T σ.toFun →
    ∀ (Z : TupleForm.PositiveSpan) (t : ℝ), 0 ≤ t →
      (TupleForm.reflectedCorrelation σ Z (twiceTimeShift t)).im = 0 ∧
      (TupleForm.reflectionForm σ Z Z).im = 0 ∧
      0 ≤ (TupleForm.reflectedCorrelation σ Z (twiceTimeShift t)).re ∧
      (TupleForm.reflectedCorrelation σ Z (twiceTimeShift t)).re ≤ (TupleForm.reflectionForm σ Z Z).re
end YangMills.Construction.ReflectionPositivity.LimitContraction
end
