import YangMills.Construction.Conventions.ContinuumLimitsOfLatticeApproximationsDefs
import YangMills.Construction.ReflectionPositivity.BoundedLatticeApproximationsAndTheirC1Constants
import YangMills.Construction.ReflectionPositivity.FromFivePointInequalitiesAtSmallTimesToTheCone
import YangMills.Construction.ReflectionPositivity.LatticeRepresentativesAndLatticeApproximations
import Mathlib
set_option autoImplicit false
open scoped NNReal
noncomputable section
namespace YangMills.Construction.ReflectionPositivity.FivePointLimit
open LimitConventions (ApproxTriple)
open SeparatedTuples (TupleFunctional posAdicGridPoints)
open ReflectionPositivity.SmallTimeCone (FivePointNonnegAt)
def FivePointInequalityInLimit : Prop :=
  ∀ (D : ReflectionPositivity.AxisMirror.MirrorData) (T : ApproxTriple D.L) (σ : TupleFunctional),
    ReflectionPositivity.ApproximatingSequences.LatticeApproximation.IsBoundedForSomeM D T →
    ApproxTriple.IsReflPos T →
    ApproxTriple.ConvergesTo T σ →
    ∀ (i : Fin 3) (t : ℝ≥0), (t : ℝ) ∈ posAdicGridPoints D.L → FivePointNonnegAt σ i t
end YangMills.Construction.ReflectionPositivity.FivePointLimit
