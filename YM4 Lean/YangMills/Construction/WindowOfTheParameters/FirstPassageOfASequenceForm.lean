import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.SequencePassage
def passageThreshold (B g : ℝ) : ℝ := g ^ (-2 : ℤ) + B
def lowerWindowCoupling (B g : ℝ) : ℝ := passageThreshold B g ^ (-(1 / 2) : ℝ)
def IsFirstPassageIndex (B g : ℝ) (x : ℕ → ℝ) (K : ℕ) : Prop :=
  x K ≤ passageThreshold B g ∧ ∀ k < K, passageThreshold B g < x k
def passageWindow (B g : ℝ) (x : ℝ → ℕ → ℝ) (K : ℕ) : Set ℝ :=
  {β | passageThreshold B g ≤ β ∧ IsFirstPassageIndex B g (x β) K}
def definedPassageWindow (F : ℝ → ℕ → Prop) (B g : ℝ) (x : ℝ → ℕ → ℝ) (K : ℕ) : Set ℝ :=
  {β | F β K ∧ β ∈ passageWindow B g x K}
end YangMills.Construction.SequencePassage
end
