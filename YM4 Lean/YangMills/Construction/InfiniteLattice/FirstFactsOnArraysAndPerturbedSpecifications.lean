import YangMills.Construction.InfiniteLattice.ToriOfAnyShapeArraysAndPerturbedMeasures
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
namespace InfiniteLattice
def BasicTiltedKernelFacts : Prop :=
  ∀ β : ℝ, 0 < β → ∀ (𝔸 : LocalObservableArray) (W : LinkWindow 1) (t : ℝ),
    (𝔸.labelsTouching W).Finite ∧
    (∀ F : GaugeField 1 → ℂ, IsBoundedObservable F →
      𝔸.tiltedKernel β 0 W F = W.conditionalExpectation one_pos β F) ∧
    𝔸.tiltedGibbsClass β 0 = gibbsClass one_pos β ∧
    ∀ F ∈ continuousLocalFunctions 1,
      𝔸.tiltedKernel β t W F ∈ continuousLocalFunctions 1
end InfiniteLattice
end YangMills.Construction
