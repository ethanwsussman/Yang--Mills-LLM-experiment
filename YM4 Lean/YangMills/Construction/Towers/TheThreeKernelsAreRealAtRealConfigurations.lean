import YangMills.Construction.Towers.TheScaledPicture
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Tower.FullSpace
def KernelsRealAtGroupFields : Prop :=
  ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∀ k : ℕ, 1 ≤ k →
    ∀ U ∈ smallIterateFields L k, U ∈ fieldSpace L k 0 →
      (∀ a b, (covDiffKernel L k 0 U a b).im = 0) ∧
      (∀ a b, (iterAverageKernel L k U a b).im = 0) ∧
      (∀ a b, (iterCovariantKernel L k U a b).im = 0) ∧
      (∀ B ∈ edgeFormSpace (meshAt L k 0),
        covDiffTranspose L k U B ∈ vertexFunctionSpace (meshAt L k 0)) ∧
      ∀ f ∈ vertexFunctionSpace (meshAt L k k),
        iterAverageTranspose L k U f ∈ vertexFunctionSpace (meshAt L k 0)
end YangMills.Construction.Tower.FullSpace
end
