import YangMills.Construction.ClusterExpansionOfAStep.FreeClassesOfAStep
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.CoreColumns
open TorusFields TorusLumps
variable {n : ℕ} [NeZero n]
def setGap (X X' : Finset (TorusSite n)) : ℕ := sInf {d | ∃ y ∈ X, ∃ y' ∈ X', supDist y y' = d}
def coreWeight (κ : ℝ) (Y : TorusSite n) (X : Finset (TorusSite n)) : ℝ :=
  (X.card : ℝ) * Real.exp (-(κ * (setGap {Y} X : ℝ)))
def columnConstant (rt : ℝ) (Dn : ℕ) : ℝ :=
  Real.exp (rt / 2 ^ 6 * Dn) * (2 * (Dn : ℝ) + 1) ^ 4 + (2 / (1 - Real.exp (-(7 * rt / 2 ^ 8)))) ^ 4
def ColumnSumBound : Prop :=
  ∀ (n : ℕ) [NeZero n] (I : Type) [Fintype I] (core : I → Finset (TorusSite n)) (z : I → ℝ)
    (c : I → I → ℝ) (Y : TorusSite n) (rt e : ℝ) (Dn : ℕ),
    0 < rt → (∀ i, (core i).Nonempty) → (∀ i, 0 ≤ z i) →
    (∀ y, ∑ i with y ∈ core i,
      z i * ((core i).card : ℝ) ^ 4 * Real.exp (2 * rt * (siteDiameter (core i) : ℝ)) ≤ e) →
    (∀ i j, (setGap (core i) (core j) ≤ Dn ∧ c i j ≤ 4 * z i) ∨
      c i j ≤ 8 * z i * min 1 (((core i).card : ℝ) *
        Real.exp (-(rt * (setGap (core i) (core j) : ℝ) / 8)))) →
    ∀ j, ∑ i, coreWeight (rt / 2 ^ 6) Y (core i) * c i j ≤
      coreWeight (rt / 2 ^ 6) Y (core j) * (8 * e * columnConstant rt Dn)
end YangMills.Construction.CoreColumns
end
