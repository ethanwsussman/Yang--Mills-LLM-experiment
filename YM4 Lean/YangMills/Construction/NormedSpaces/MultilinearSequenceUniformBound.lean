import Mathlib
set_option autoImplicit false
namespace YangMills.Construction.NormedSpaces
def MultilinearSequenceUniformBound : Prop :=
  ∀ (k : ℕ+) (E : Fin k → Type) [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace ℝ (E i)]
    [∀ i, CompleteSpace (E i)] (B : ℕ+ → MultilinearMap ℝ E ℝ),
    (∀ n, ∃ c : ℝ, ∀ v : ∀ i, E i, |B n v| ≤ c * ∏ i, ‖v i‖) →
    (∀ v : ∀ i, E i, BddAbove (Set.range fun n => |B n v|)) →
    ∃ C : ℝ, ∀ (n : ℕ+) (v : ∀ i, E i), |B n v| ≤ C * ∏ i, ‖v i‖
end YangMills.Construction.NormedSpaces
