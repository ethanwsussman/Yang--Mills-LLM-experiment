import YangMills.Construction.InfiniteLattice.ToriOfAnyShapeArraysAndPerturbedMeasures
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.InfiniteLattice
def TiltedKernelsUniformlyCloseNearZero : Prop :=
  ∀ β : ℝ, 0 < β → ∀ (𝔸 : LocalObservableArray) (W : LinkWindow 1),
    ∀ F ∈ continuousLocalFunctions 1, ∃ C : ℝ, 0 ≤ C ∧
      ∀ (s : ℝ) (U : GaugeField 1),
        ‖𝔸.tiltedKernel β s W F U - 𝔸.tiltedKernel β 0 W F U‖ ≤
          (⨆ V, ‖F V‖) * (Real.exp (C * |s|) - 1)
end YangMills.Construction.InfiniteLattice
