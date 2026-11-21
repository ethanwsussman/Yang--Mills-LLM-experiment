import Mathlib
set_option autoImplicit false
noncomputable section
open scoped ContDiff
namespace YangMills.Construction
namespace CouplingFlow
def flow (b d : ℕ → ℝ) (β : ℝ) : ℕ → ℝ
  | 0 => β
  | t + 1 => flow b d β t - b t - d t / flow b d β t
def slopeConst (L : ℕ) : ℝ := 11 / (3 * Real.pi ^ 2) * Real.log L
def stepRemainder (b d x : ℕ → ℝ) (k : ℕ) : ℝ := x (k + 1) - (x k - b k - d k / x k)
def HasAverageSlope (b : ℕ → ℝ) (s c : ℝ) : Prop :=
  ∀ i j : ℕ, i ≤ j → |∑ k ∈ Finset.Ico i j, b k - ((j : ℝ) - i) * s| ≤ 2 * c
def StaysAbove (X : ℝ) (x : ℕ → ℝ) (t : ℕ) : Prop := ∀ k ≤ t, X ≤ x k
def FollowsFlowAbove (b d : ℕ → ℝ) (R X : ℝ) (x : ℕ → ℝ) : Prop :=
  ∀ k, StaysAbove X x k → |stepRemainder b d x k| ≤ R * x k ^ (-(5 / 4) : ℝ)
structure BoundsUpTo (b d : ℕ → ℝ) (s c M R C : ℝ) (w : ℕ) (x : ℕ → ℝ) (t : ℕ) : Prop where
  drop_two_sided : ∀ i j : ℕ, i ≤ j → j ≤ t →
    3 / 4 * s * ((j : ℝ) - i) - 2 * c ≤ x i - x j ∧ x i - x j ≤ 5 / 4 * s * ((j : ℝ) - i) + 2 * c
  drop_window : ∀ i m : ℕ, w ≤ m → i + m ≤ t → s * m / 2 ≤ x i - x (i + m)
  drop_step : ∀ k ≤ t, b k - M / x k - R * x k ^ (-(5 / 4) : ℝ) ≤ x k - x (k + 1)
  sum_abs_remainder_le : ∑ k ∈ Finset.range t, |stepRemainder b d x k| ≤ C * x t ^ (-(1 / 4) : ℝ)
  sum_inv_sq_le : ∑ k ∈ Finset.range t, (x k ^ 2)⁻¹ ≤ 16 / (3 * s * x t)
  flow_pos : ∀ k ≤ t, 0 < flow b d (x 0) k
  near_flow : |x t - flow b d (x 0) t| ≤ 2 * C * x t ^ (-(1 / 4) : ℝ)
  near_flow_succ : |x (t + 1) - flow b d (x 0) (t + 1)| ≤ 1 / 2
structure FlowBounds (b d : ℕ → ℝ) (s c M R X C : ℝ) (w : ℕ) (v₀ : ℝ) (x : ℕ → ℝ) : Prop where
  boundsUpTo : ∀ t, StaysAbove X x t → BoundsUpTo b d s c M R C w x t
  staysAbove_of_flow : ∀ t, (∀ k ≤ t, X + 1 ≤ flow b d (x 0) k) → StaysAbove X x t
  near_value : ∀ (K : ℕ) (v : ℝ), v₀ ≤ v → flow b d (x 0) K = v → (∀ k ≤ K, X + 1 ≤ flow b d (x 0) k) →
    v - 1 / 2 ≤ x K ∧ |x K - v| ≤ 2 * C * x K ^ (-(1 / 4) : ℝ) ∧
      2 * C * x K ^ (-(1 / 4) : ℝ) ≤ 3 * C * v ^ (-(1 / 4) : ℝ)
  near_scale : ∀ (K : ℕ) (g : ℝ), 0 < g → StaysAbove X x K → |x K - (g ^ 2)⁻¹| ≤ 1 →
    |x K - flow b d (x 0) K| ≤ 3 * C * g ^ (1 / 2 : ℝ)
structure FlowAbove (b d : ℕ → ℝ) (X v₀ : ℝ) : Prop where
  halfLine : ∀ t : ℕ, ∃ β₀ : ℝ, {β | ∀ k ≤ t, X + 1 ≤ flow b d β k} = Set.Ici β₀ ∧
    StrictMonoOn (fun β => flow b d β t) (Set.Ici β₀) ∧
    ∀ β ∈ Set.Ici β₀, ContDiffAt ℝ ∞ (fun β => flow b d β t) β ∧
      1 / 2 ≤ deriv (fun β => flow b d β t) β ∧ deriv (fun β => flow b d β t) β ≤ 2
  existsUnique_value : ∀ (K : ℕ) (v : ℝ), v₀ ≤ v →
    ∃! β : ℝ, flow b d β K = v ∧ ∀ k ≤ K, X + 1 ≤ flow b d β k
end CouplingFlow
end YangMills.Construction
end
