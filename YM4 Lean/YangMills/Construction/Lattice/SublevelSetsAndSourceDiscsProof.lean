import YangMills.Construction.Lattice.SublevelSetsAndSourceDiscs
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.SublevelSets
open WeightedModulusSum
theorem sublevelAndDiskStatement_holds : SublevelAndDiskStatement := by
  refine ⟨?_, ?_⟩
  · intro n a r hr
    refine ⟨?_, ?_, ?_⟩
    · have hc : Continuous a.weightedNorm := by
        unfold Weights.weightedNorm
        fun_prop
      exact isOpen_lt hc continuous_const
    · simpa [Weights.weightedNorm] using hr
    · rintro rfl
      rfl
  · intro D n f ϱ' hf hpos hϱ
    have hn : 1 ≤ n := hf.1
    let a : Weights n :=
      { one_le := hn
        c := fun i => D.sharpNorm (f i) / ϱ'
        c_pos := fun i => div_pos (hpos i) hϱ }
    have hrho : ∀ z : Fin n → ℂ, a.weightedNorm z = 1 / ϱ' * ∑ i, ‖z i‖ * D.sharpNorm (f i) := by
      intro z
      change ∑ i, D.sharpNorm (f i) / ϱ' * ‖z i‖ = _
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      ring
    refine ⟨a, fun _ => rfl, ?_, hrho, ?_⟩
    · ext z
      change ∑ i, ‖z i‖ * D.sharpNorm (f i) < ϱ' ↔ a.weightedNorm z < 1
      rw [hrho z, one_div, inv_mul_lt_iff₀ hϱ, mul_one]
    · change (n : ℝ) ^ n * ∏ i, (D.sharpNorm (f i) / ϱ') = _
      rw [Finset.prod_div_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin, div_pow]
      field_simp
end YangMills.Construction.SublevelSets
end
