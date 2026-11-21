import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
namespace Calculus
def weightedNorm {N : ℕ} (w : Fin N → ℝ) (x : Fin N → ℝ) : ℝ := ∑ n, |x n| * w n
def segmentConstant (k : ℕ) (K C₁ : ℝ) : ℝ :=
  (Fintype.card (OrderedFinpartition k) : ℝ) * 2 ^ (k + 2) * K * (2 * C₁) ^ (k + 1)
def IteratedDerivAlongSegmentBound : Prop :=
  ∀ (N k : ℕ) (A : (Fin N → ℝ) → ℝ) (v : Fin N → ℝ) (P D : (Fin k → ℝ) → (Fin N → ℝ)) (w : Fin N → ℝ)
    (K C₁ ω s Γ : ℝ) (B : Finset (Fin k) → ℝ),
    (∀ n, 0 ≤ w n) → P 0 = 0 → AnalyticAt ℝ P 0 → AnalyticAt ℝ D 0 →
    (∀ θ ∈ Set.Icc (0 : ℝ) 1, AnalyticAt ℝ A (θ • D 0)) →
    (∀ θ ∈ Set.Icc (0 : ℝ) 1, ∀ (l : ℕ), 1 ≤ l → l ≤ k + 1 → ∀ r : Fin l → Fin N,
      |iteratedFDeriv ℝ l (fun σ => fderiv ℝ A σ v) (θ • D 0) (fun i => Pi.single (r i) 1)| ≤ K * ∏ i, w (r i)) →
    iteratedFDeriv ℝ k ((fun σ => fderiv ℝ A σ v) ∘ P) 0 (fun i => Pi.single i 1) = 0 →
    (∀ (p : ℕ) (e : Fin p → Fin k), 0 < p → Function.Injective e →
      weightedNorm w (iteratedFDeriv ℝ p P 0 (fun i => Pi.single (e i) 1)) ≤ C₁ * B (Finset.univ.image e)) →
    (∀ (p : ℕ) (e : Fin p → Fin k), 0 < p → Function.Injective e →
      weightedNorm w (iteratedFDeriv ℝ p D 0 (fun i => Pi.single (e i) 1)) ≤ C₁ * ω * B (Finset.univ.image e)) →
    weightedNorm w (D 0) ≤ C₁ * ω →
    (∀ I, 0 ≤ B I ∧ B I ≤ 1) → (∀ c : OrderedFinpartition k, ∏ i, B (Finset.univ.image (c.emb i)) ≤ Γ) →
    0 ≤ K → 1 ≤ C₁ → 0 ≤ ω → ω ≤ 1 → s ∈ Set.Icc (0 : ℝ) 1 →
    |iteratedFDeriv ℝ k ((fun σ => fderiv ℝ A σ v) ∘ fun τ => P τ + s • D τ) 0 (fun i => Pi.single i 1)| ≤
      segmentConstant k K C₁ * ω * Γ
end Calculus
end YangMills.Construction
end
