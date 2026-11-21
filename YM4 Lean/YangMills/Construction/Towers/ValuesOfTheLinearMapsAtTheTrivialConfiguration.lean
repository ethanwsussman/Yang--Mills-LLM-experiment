import YangMills.Construction.Conventions.StandingParameters
import YangMills.Construction.Towers.LinearMapsAtTheTrivialConfiguration
import Mathlib
noncomputable section
namespace YangMills.Construction.Tower.LinearMapValues
def OnFiniteTorus (L n k : ℕ) : Prop :=
  (∀ j : ℕ, j + 1 ≤ k →
    (∀ A ∈ edgeFormSpace L n k j,
      (∀ e : Edge L n k (j + 1),
        crossingSmoothing L n k j A e.opposite = -crossingSmoothing L n k j A e) ∧
      crossingSmoothing L n k j A ∈ edgeFormSpace L n k (j + 1) ∧
      linearSmoothing L n k j A ∈ edgeFormSpace L n k (j + 1) ∧
      fineOnlyContourAverage L n k j A ∈ fineOnlyFunctions L n k j) ∧
    Finite (FineOnlyVertex L n k j) ∧
    ∃ c : InnerProductSpace.Core ℝ (fineOnlyFunctions L n k j),
      ∀ f g : fineOnlyFunctions L n k j,
        ((c.inner f g : ℝ) : ℂ) =
          fineOnlyPairing (f : FineOnlyVertex L n k j → Matrices.ComplexMatrix2)
            (g : FineOnlyVertex L n k j → Matrices.ComplexMatrix2)) ∧
  ∀ m : ℕ, m ≤ k → ∀ A ∈ edgeFormSpace L n k 0,
    cubeContourAverageIter L n k m A ∈ vertexFunctionSpace L n k m
def OnInfiniteLattice (L k : ℕ) : Prop :=
  (∀ j : ℕ, j + 1 ≤ k → ∀ A ∈ FullSpace.edgeFormSpace (meshAt L k j),
    (∀ e : FullSpace.Edge L k (j + 1),
      FullSpace.crossingSmoothing L A e.opposite = -FullSpace.crossingSmoothing L A e) ∧
    FullSpace.crossingSmoothing (a := meshAt L k (j + 1)) L A ∈
      FullSpace.edgeFormSpace (meshAt L k (j + 1)) ∧
    FullSpace.linearSmoothing (a := meshAt L k (j + 1)) L A ∈
      FullSpace.edgeFormSpace (meshAt L k (j + 1)) ∧
    FullSpace.fineOnlyContourAverage (a := meshAt L k (j + 1)) L A ∈
      FullSpace.fineOnlyFunctions (meshAt L k (j + 1)) (meshAt L k j)) ∧
  ∀ m : ℕ, m ≤ k → ∀ A ∈ FullSpace.edgeFormSpace (meshAt L k 0),
    FullSpace.cubeContourAverageIter L k m A ∈ FullSpace.vertexFunctionSpace (meshAt L k m)
def Statement : Prop :=
  ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∀ k : ℕ,
    (∀ n : ℕ, 0 < n → OnFiniteTorus L n k) ∧ OnInfiniteLattice L k
end YangMills.Construction.Tower.LinearMapValues
end
