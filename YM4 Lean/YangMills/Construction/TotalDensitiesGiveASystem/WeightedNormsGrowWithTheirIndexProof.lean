import YangMills.Construction.TotalDensitiesGiveASystem.WeightedNormsGrowWithTheirIndex
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.TotalDensitiesGiveASystem
theorem bracketNorm_mono : BracketNormMonotone := by
  intro n k k' f hkk'
  rcases Nat.eq_zero_or_pos k' with hzero | hpos
  · have : k = 0 := by omega
    subst this; subst hzero
    exact le_rfl
  have hfinite := f.2.2 k' hpos
  refine ENNReal.toReal_mono hfinite.ne ?_
  refine iSup_le fun x => iSup_le fun α => iSup_le fun hα => ?_
  refine le_iSup_of_le x (le_iSup_of_le α (le_iSup_of_le (hα.trans hkk') ?_))
  refine ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right ?_ (norm_nonneg _))
  refine Real.rpow_le_rpow_of_exponent_le (le_add_of_nonneg_right (sq_nonneg _)) ?_
  have : (k : ℝ) ≤ k' := by exact_mod_cast hkk'
  linarith
end YangMills.Construction.TotalDensitiesGiveASystem
end
