import YangMills.Construction.Towers.CovariantLinearAverages
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Tower.FullSpace
def StraightSmoothingOnForms : Prop :=
  ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∀ k m : ℕ, 1 ≤ k → m ≤ k →
    (∀ A ∈ complexEdgeForms (meshAt L k 0),
      crossingSmoothingIter L k m A ∈ complexEdgeForms (meshAt L k m)) ∧
    (∀ A ∈ edgeFormSpace (meshAt L k 0),
      crossingSmoothingIter L k m A ∈ edgeFormSpace (meshAt L k m)) ∧
    (∀ A ∈ complexEdgeForms (meshAt L k 0), ∀ A' ∈ complexEdgeForms (meshAt L k 0), ∀ z : ℂ,
      crossingSmoothingIter L k m (z • A + A') =
        z • crossingSmoothingIter L k m A + crossingSmoothingIter L k m A') ∧
    ∀ A ∈ complexEdgeForms (meshAt L k 0),
      iterCovariantDeriv L k (fun _ => 1) m A = crossingSmoothingIter L k m A
end YangMills.Construction.Tower.FullSpace
end
