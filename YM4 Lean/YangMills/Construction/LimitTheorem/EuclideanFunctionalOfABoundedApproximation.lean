import YangMills.Construction.Conventions.ContinuumLimitsOfLatticeApproximationsDefs
import YangMills.Construction.EuclideanFunctionals.JointSpectralMeasureOfAReconstructionAndTheConeCondition
import YangMills.Construction.LimitsAlongPeriodicGibbsStates.LimitAlongPeriodicGibbsStatesIsTheLimitOfABoundedApproximation
import YangMills.Construction.LimitsAlongPeriodicGibbsStates.WhatTheCentredFunctionalOfAConnectedLimitSupplies
import YangMills.Construction.ReflectionPositivity.BoundedLatticeApproximationsAndTheirC1Constants
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.FirstPassageSeqs
open EuclideanFunctionals
def BoundedApproximationLimitIsEuclidean : Prop :=
  ∀ (D : ReflectionPositivity.AxisMirror.MirrorData) (T : LimitConventions.ApproxTriple D.L) (S : ConnFamily)
    (τ : SeparatedTuples.TupleFunctional), τ.toFun = onSepTuples (centeredFn S) →
    ReflectionPositivity.ApproximatingSequences.LatticeApproximation.IsBoundedForSomeM D T →
    LimitConventions.ApproxTriple.IsReflPos T →
    LimitConventions.ApproxTriple.ConvergesTo T (onSepTuples (centeredFn S)) →
    CenteredIsEuclidInvariant S ∧ CenteredIsReflectionPositive S ∧
      ∀ (c : SharpScale) (C : ℕ → ℝ → ℝ → ℝ), HasClusterBounds S c C →
        (∃ e : EuclidFunctionalWithRecon c S, e.clusterConst = C) ∧
          ∀ e : EuclidFunctionalWithRecon c S, e.ConeCondition
end YangMills.Construction.FirstPassageSeqs
end
