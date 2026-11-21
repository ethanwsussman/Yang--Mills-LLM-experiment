import YangMills.Construction.InfiniteLattice.PropertiesOfToriArraysAndPerturbedMeasures
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.InfiniteLattice
def TiltedKernelOfArrayIsWellDefined : Prop :=
  ∀ β : ℝ, 0 < β → ∀ (𝔸 : LocalObservableArray) (t : ℝ), 𝔸.TiltedKernelWellDefined β t
end YangMills.Construction.InfiniteLattice
