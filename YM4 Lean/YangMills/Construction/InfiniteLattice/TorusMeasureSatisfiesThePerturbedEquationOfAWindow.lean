import YangMills.Construction.InfiniteLattice.CubesDomainsAndEdgeTreesOfTheWholeLattice
import YangMills.Construction.InfiniteLattice.ObservablesOnTheClosedSideOfAMirrorAndStates
import YangMills.Construction.InfiniteLattice.ToriOfAnyShapeArraysAndPerturbedMeasures
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
namespace InfiniteLattice
def TiltedTorusMeasureWindowEquation.Statement : Prop :=
  ∀ β : ℝ, 0 < β → ∀ (A : LocalObservableArray) (t : ℝ) (W : LinkWindow 1),
    ∀ F ∈ continuousLocalFunctions 1, ∃ w : ℝ, ∀ Γ : PeriodSublattice 1, A.FitsPeriods Γ →
      (∀ γ ∈ Γ.periods, γ ≠ 0 → w < WholeSpace.maxNorm (γ : AmbientSpace)) →
      stateEval (A.tiltedLiftMeasure Γ β t) F =
        stateEval (A.tiltedLiftMeasure Γ β t) (A.tiltedKernel β t W F)
end InfiniteLattice
end YangMills.Construction
