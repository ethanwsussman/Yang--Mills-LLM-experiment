import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ColdStepAtMirrorFrames
def SymmetricSystemGreenDecay : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (d : ι → ι → ℝ) (S : Matrix ι ι ℝ) (lam κ : ℝ),
    0 < lam → 0 ≤ κ → (∀ i, d i i = 0) → (∀ i j, d i j = d j i) →
    (∀ i j k, d i k ≤ d i j + d j k) → S.IsSymm →
    (∀ x : ι → ℝ, lam * ∑ i, x i ^ 2 ≤ ∑ i, x i * S.mulVec x i) →
    (∀ i, ∑ j, |S i j| * (Real.exp (2 * κ * d i j) - 1) ≤ lam / 2) →
    ∀ (x : ι → ℝ) (b₀ : ι), S.mulVec x = Pi.single b₀ 1 →
      ∀ b, |x b| ≤ 2 / lam * Real.exp (-(2 * κ * d b b₀))
end YangMills.Construction.ColdStepAtMirrorFrames
end
