import YangMills.Construction.ColdStepAtMirrorFrames.SlopeAlongASegment
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Calculus
def IteratedDerivCompSegmentDiffBound : Prop :=
  ∀ (N k : ℕ) (f : (Fin N → ℝ) → ℝ) (P D : (Fin k → ℝ) → (Fin N → ℝ)) (w : Fin N → ℝ)
    (K C ω s Γ : ℝ) (B : Finset (Fin k) → ℝ),
    (∀ n, 0 ≤ w n) → P 0 = 0 → AnalyticAt ℝ P 0 → AnalyticAt ℝ D 0 →
    (∀ θ ∈ Set.Icc (0 : ℝ) 1, AnalyticAt ℝ f (θ • D 0)) →
    (∀ θ ∈ Set.Icc (0 : ℝ) 1, ∀ (l : ℕ), 1 ≤ l → l ≤ k + 1 → ∀ r : Fin l → Fin N,
      |iteratedFDeriv ℝ l f (θ • D 0) (fun i => Pi.single (r i) 1)| ≤ K * ∏ i, w (r i)) →
    (∀ (p : ℕ) (e : Fin p → Fin k), 0 < p → Function.Injective e →
      weightedNorm w (iteratedFDeriv ℝ p P 0 (fun i => Pi.single (e i) 1)) ≤ C * B (Finset.univ.image e)) →
    (∀ (p : ℕ) (e : Fin p → Fin k), 0 < p → Function.Injective e →
      weightedNorm w (iteratedFDeriv ℝ p D 0 (fun i => Pi.single (e i) 1)) ≤ C * ω * B (Finset.univ.image e)) →
    weightedNorm w (D 0) ≤ C * ω →
    (∀ I, 0 ≤ B I ∧ B I ≤ 1) → (∀ c : OrderedFinpartition k, ∏ i, B (Finset.univ.image (c.emb i)) ≤ Γ) →
    0 ≤ K → 1 ≤ C → 0 ≤ ω → ω ≤ 1 → s ∈ Set.Icc (0 : ℝ) 1 →
    |iteratedFDeriv ℝ k (f ∘ fun y => P y + s • D y) 0 (fun i => Pi.single i 1) -
      iteratedFDeriv ℝ k (f ∘ P) 0 (fun i => Pi.single i 1)| ≤ segmentConstant k K C * ω * Γ
end YangMills.Construction.Calculus
end
