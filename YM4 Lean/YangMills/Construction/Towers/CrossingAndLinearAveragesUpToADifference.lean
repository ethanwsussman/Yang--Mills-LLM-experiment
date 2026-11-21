import YangMills.Construction.Conventions.StandingParameters
import YangMills.Construction.Towers.LinearMapsAtTheTrivialConfiguration
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Tower
def CrossingAndLinearSmoothingDifferByCoboundary : Prop :=
  ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∀ k n : ℕ, 1 ≤ k → 0 < n →
    (∀ m ≤ k, ∀ A ∈ edgeFormSpace L n k 0, ∀ l ∈ vertexFunctionSpace L n k 0,
      ∃ l' ∈ vertexFunctionSpace L n k m,
        linearSmoothingIter L n k m (A + vertexCoboundary l) =
          crossingSmoothingIter L n k m A + vertexCoboundary l') ∧
    ∀ A ∈ edgeFormSpace L n k 0, ∃ l ∈ vertexFunctionSpace L n k 0,
      linearSmoothingIter L n k k (A + vertexCoboundary l) = crossingSmoothingIter L n k k A
end YangMills.Construction.Tower
end
