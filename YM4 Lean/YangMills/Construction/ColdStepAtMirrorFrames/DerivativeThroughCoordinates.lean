import YangMills.Construction.ColdStepAtMirrorFrames.SlopeAlongASegment
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Calculus
def compositionConstant (k : ℕ) (K C : ℝ) : ℝ := (Fintype.card (OrderedFinpartition k) : ℝ) * K * C ^ k
def IteratedDerivCompBound : Prop :=
  ∀ (N k : ℕ) (f : (Fin N → ℝ) → ℝ) (Q : (Fin k → ℝ) → (Fin N → ℝ)) (w : Fin N → ℝ) (K C : ℝ),
    (∀ n, 0 ≤ w n) → AnalyticAt ℝ Q 0 → AnalyticAt ℝ f (Q 0) →
    (∀ (l : ℕ), 1 ≤ l → l ≤ k → ∀ r : Fin l → Fin N,
      |iteratedFDeriv ℝ l f (Q 0) (fun i => Pi.single (r i) 1)| ≤ K * ∏ i, w (r i)) →
    (∀ (p : ℕ) (e : Fin p → Fin k), 0 < p → Function.Injective e →
      weightedNorm w (iteratedFDeriv ℝ p Q 0 (fun i => Pi.single (e i) 1)) ≤ C) →
    1 ≤ k → 0 ≤ K → 1 ≤ C →
    |iteratedFDeriv ℝ k (f ∘ Q) 0 (fun i => Pi.single i 1)| ≤ compositionConstant k K C
end YangMills.Construction.Calculus
end
