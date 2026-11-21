import YangMills.Construction.LawInAState.ReflectionKernelAtADistance
import YangMills.Construction.LawInAState.ResponsesInOneBox
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.StateLaws
open TorusFields WeightedResponses BoxResponses TorusMetric
open InfiniteLattice (AmbientSpace)
def minimalSiteDiff {N : ℕ} (y z : TorusSite N) : Fin 4 → ℤ := fun i => (y i - z i).valMinAbs
def blockMeanKernelSum (L K k : ℕ) [NeZero L] (f h : AmbientSpace → ℝ) : ℝ :=
  ∑ y : TorusSite (boxSide L K k), ∑ z : TorusSite (boxSide L K k),
    blockMean L k (boxSide L K k) y (unitTorusWeight L K k f) * blockMean L k (boxSide L K k) z (unitTorusWeight L K k h) *
      (ReflectionKernel.normSq (fun i => (minimalSiteDiff y z i : ℝ)) ^ 4)⁻¹
structure IsLocalizedLipschitzPair (c : AmbientSpace) (d Λ : ℝ) (f h : AmbientSpace → ℝ) : Prop where
  abs_f_le : ∀ x, |f x| ≤ 1
  abs_h_le : ∀ x, |h x| ≤ 1
  f_localized : ∀ x, f x ≠ 0 → ∀ i, |x i - c i| ≤ 6 * d
  h_localized : ∀ x, h x ≠ 0 → ∀ i, |x i - c i| ≤ 6 * d
  f_lipschitz : ∀ (x x' : AmbientSpace) (t : ℝ), (∀ i, |x i - x' i| ≤ t) → |f x - f x'| ≤ Λ * t
  h_lipschitz : ∀ (x x' : AmbientSpace) (t : ℝ), (∀ i, |x i - x' i| ≤ t) → |h x - h x'| ≤ Λ * t
  separated : ∀ x x', f x ≠ 0 → h x' ≠ 0 → d ≤ euclidNormVec (x - x')
def blockMeanSumApproxKernelStatement : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ (L : ℕ) [NeZero L], Odd L → ∀ (K k : ℕ), k ≤ K → ∀ (c : AmbientSpace) (d Λ : ℝ)
    (f h : AmbientSpace → ℝ),
    IsLocalizedLipschitzPair c d Λ f h → 0 < d → 0 ≤ Λ → d ≤ 1 / 100 → 64 * ((L : ℝ) ^ k / (L : ℝ) ^ K) ≤ d →
    Λ * ((L : ℝ) ^ k / (L : ℝ) ^ K) ≤ 1 →
    |blockMeanKernelSum L K k f h - TestFunctions.inverseEighthKernel f h| ≤
      C * (Λ * ((L : ℝ) ^ k / (L : ℝ) ^ K) + (L : ℝ) ^ k / (L : ℝ) ^ K / d)
end YangMills.Construction.StateLaws
end
