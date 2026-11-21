import YangMills.Construction.Towers.ExtendedFamilyKeepsTheLowerLevels
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Tower
theorem extendLevel_preserves_lower : ExtendLevelPreservesLower := by
  intro L n k i b p hb
  have hE : ∀ j, j ≤ i → (b.extendLevel i p).energy j = b.energy j := by
    intro j hj
    have hne : j ≠ i + 1 := by omega
    simp [CriticalBranchData.extendLevel, Function.update_of_ne hne]
  have hP : ∀ j, j < i → (b.extendLevel i p).prolong j = b.prolong j := by
    intro j hj
    have hne : j ≠ i := by omega
    simp [CriticalBranchData.extendLevel, Function.update_of_ne hne]
  have hC : ∀ j, j ≤ i → (b.extendLevel i p).prolongComp j = b.prolongComp j := by
    intro j
    induction j with
    | zero => intro _; rfl
    | succ j ih =>
      intro hj
      simp only [CriticalBranchData.prolongComp]
      rw [ih (by omega), hP j (by omega)]
  have hF : ∀ j, j ≤ i → (b.extendLevel i p).gaugeFixedEnergy j = b.gaugeFixedEnergy j := by
    intro j hj
    funext V
    simp only [CriticalBranchData.gaugeFixedEnergy]
    rw [hE j hj]
  have hH : ∀ j, j ≤ i → (b.extendLevel i p).hessianAtOne j = b.hessianAtOne j := by
    intro j hj
    funext B B'
    simp only [CriticalBranchData.hessianAtOne]
    rw [hE j hj]
  have hQ : ∀ j, j ≤ i → (b.extendLevel i p).stepQuadratic j = b.stepQuadratic j := by
    intro j hj
    funext ξ
    simp only [CriticalBranchData.stepQuadratic]
    rw [hH j hj]
  have hG : ∀ j, j ≤ i → (b.extendLevel i p).energyGradient j = b.energyGradient j := by
    intro j hj
    funext W
    simp only [CriticalBranchData.energyGradient]
    rw [hE j hj]
  have hM : ∀ j, j ≤ i →
      (b.extendLevel i p).SatisfiesMultiplierIdentity j = b.SatisfiesMultiplierIdentity j := by
    intro j hj
    funext W
    simp only [CriticalBranchData.SatisfiesMultiplierIdentity]
    rw [hG j hj, hC j hj]
  constructor
  · intro j hj; rw [hE j hj]; exact hb.analytic_energy j hj
  · intro j hj; rw [hE j hj]; exact hb.energy_nonneg j hj
  · rw [hE 0 (Nat.zero_le i)]; exact hb.energy_bottom
  · intro j hj; rw [hP j hj]; exact hb.analytic_prolong j hj
  · intro j hj; rw [hP j hj]; exact hb.prolong_trivial j hj
  · intro j hj
    rw [hP j hj, hE j hj.le, hE (j + 1) hj, hF j hj.le]
    exact hb.prolong_section j hj
  · intro j hj; rw [hP j hj, hF j hj.le]; exact hb.fibre_structure j hj
  · intro j hj; rw [hE j hj]; exact hb.energy_gauge_invariant j hj
  · intro j hj; rw [hP j hj]; exact hb.prolong_gauge_equivariant j hj
  · intro j hj; rw [hE j hj]; exact hb.energy_symmetry_invariant j hj
  · intro j hj; rw [hP j hj]; exact hb.prolong_symmetry_equivariant j hj
  · intro j hj; rw [hE j hj]; exact hb.energy_trivial j hj
  · intro j hj; rw [hG j hj]; exact hb.gradient_trivial j hj
  · intro j hj; rw [hH j hj]; exact hb.hessianAtOne_nonneg j hj
  · intro j hj; rw [hH j hj]; exact hb.hessianAtOne_null_iff j hj
  · rw [hH 0 (Nat.zero_le i)]; exact hb.hessianAtOne_bottom
  · intro j hj; rw [hQ j hj.le, hH (j + 1) hj]; exact hb.hessianAtOne_isLeast j hj
  · intro j hj; rw [hQ j hj.le, hH (j + 1) hj, hP j hj]; exact hb.hessianAtOne_minimizer_iff j hj
  · intro j hj; rw [hC j hj, hE j hj, hM j hj]; exact hb.prolongComp_section j hj
  · intro j hj; rw [hC (j + 1) hj, hP j hj]; exact hb.prolongComp_lift j hj
  · intro j hj; rw [hC j hj]; exact hb.prolongComp_critical j hj
end YangMills.Construction.Tower
end
