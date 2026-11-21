import YangMills.Construction.Conventions.ContinuumLimitsOfLatticeApproximationsDefs
import YangMills.Construction.ReflectionPositivity.BoundedLatticeApproximationsAndTheirC1Constants
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ReflectionPositivity.LimitSymmetries
open ReflectionPositivity.AxisMirror (MirrorData)
open LimitConventions (ApproxTriple cubicMotionGroup)
open ReflectionPositivity.ApproximatingSequences.LatticeApproximation (IsBoundedForSomeM)
open Mirrors (ReflectingHyperplane)
open SeparatedTuples (FormalSpan TupleFunctional SepTuple push pushSpan formalMul
  spanIn conjugation)
def HasSymmetriesAndMirrors (σ : TupleFunctional) : Prop :=
  (σ.IsPermInvariant ∧ σ.IsEntrywiseLinear ∧ σ.IsAdmissiblyContinuous) ∧
  ((∀ r ∈ cubicMotionGroup, σ.IsInvariant r) ∧
    ∀ H : ReflectingHyperplane, (∃ r ∈ cubicMotionGroup, ⇑r = H.reflect) ∧ σ.IsInvariant H.reflect) ∧
  ∀ H : ReflectingHyperplane,
    (∀ Z ∈ spanIn H.positiveSide,
      SeparatedTupleFunctionals.IsRealNonneg
        (σ.spanExtension
          (formalMul (pushSpan H.reflect (conjugation Z)) Z))) ∧
    σ.IsReflectionPositive H
def LimitHasSymmetries : Prop :=
  ∀ (D : MirrorData) (T : ApproxTriple D.L) (σ : SepTuple → ℝ),
    IsBoundedForSomeM D T →
    ApproxTriple.IsReflPos T →
    ApproxTriple.ConvergesTo T σ →
    ∃ hσ : σ SepTuple.nil = 1, HasSymmetriesAndMirrors ⟨σ, hσ⟩
end YangMills.Construction.ReflectionPositivity.LimitSymmetries
end
