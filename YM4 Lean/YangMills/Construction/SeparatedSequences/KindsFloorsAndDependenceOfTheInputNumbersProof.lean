import YangMills.Construction.SeparatedSequences.ConditionsHoldAtChosenConstants
import YangMills.Construction.SeparatedSequences.KindsFloorsAndDependenceOfTheInputNumbers
import Mathlib
set_option autoImplicit false
namespace YangMills.Construction.SeparatedSequences.InputConstants.Properties
theorem exists_nat_pow_ge {L : ℕ} (hL : 2 ≤ L) (x : ℝ) : ∃ a : ℕ, x ≤ ((L ^ a : ℕ) : ℝ) := by
  have hone : (1 : ℝ) < (L : ℝ) := by
    have : (2 : ℝ) ≤ (L : ℝ) := by exact_mod_cast hL
    linarith
  obtain ⟨a, ha⟩ := pow_unbounded_of_one_lt x hone
  exact ⟨a, by push_cast; exact ha.le⟩
theorem blockPow_spec {L : ℕ} (hL : 2 ≤ L) :
    (∃ a : ℕ, blockPow L = L ^ a) ∧
      SeparatedSequences.CombinedConstants.blockLower L ≤ (blockPow L : ℝ) := by
  obtain ⟨a, ha⟩ := exists_nat_pow_ge hL (SeparatedSequences.CombinedConstants.blockLower L)
  have hne : {M : ℕ | (∃ a : ℕ, M = L ^ a) ∧
      SeparatedSequences.CombinedConstants.blockLower L ≤ (M : ℝ)}.Nonempty :=
    ⟨L ^ a, ⟨a, rfl⟩, ha⟩
  exact Nat.sInf_mem hne
theorem sq_le_blockLower (L : ℕ) :
    (L : ℝ) ^ 2 ≤ SeparatedSequences.CombinedConstants.blockLower L := by
  unfold SeparatedSequences.CombinedConstants.blockLower
  exact le_trans (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) (le_max_right _ _))
    (le_max_right _ _)
theorem gapMultiplier_spec {L : ℕ} (hL : 2 ≤ L) :
    (∃ a : ℕ, gapMultiplier L = L ^ a) ∧ L ≤ gapMultiplier L ∧
      max (SeparatedSequences.CombinedConstants.derivedGapLower L)
          (16 * (4 * Real.log (L : ℝ) + Real.log 2) / SeparatedSequences.minimalInputRate L) ≤
        (gapMultiplier L : ℝ) * (blockPow L : ℝ) := by
  set x : ℝ := max (SeparatedSequences.CombinedConstants.derivedGapLower L)
    (16 * (4 * Real.log (L : ℝ) + Real.log 2) / SeparatedSequences.minimalInputRate L) with hx
  obtain ⟨a, ha⟩ := exists_nat_pow_ge hL x
  have hL1 : 1 ≤ L := by omega
  have hLa : 1 ≤ L ^ a := Nat.one_le_pow _ _ (by omega)
  have hM : (1 : ℝ) ≤ (blockPow L : ℝ) := by
    have hfl := (blockPow_spec hL).2
    have hsq := sq_le_blockLower L
    have hone : (1 : ℝ) ≤ (L : ℝ) := by exact_mod_cast hL1
    nlinarith
  have hstep : L ^ a ≤ L ^ (a + 1) := Nat.pow_le_pow_right hL1 (by omega)
  have hLle : L ≤ L ^ (a + 1) := by
    rw [pow_succ]
    exact Nat.le_mul_of_pos_left L (by omega)
  have hmem : (L ^ (a + 1)) ∈ {R : ℕ | (∃ a : ℕ, R = L ^ a) ∧ L ≤ R ∧
      max (SeparatedSequences.CombinedConstants.derivedGapLower L)
          (16 * (4 * Real.log (L : ℝ) + Real.log 2) / SeparatedSequences.minimalInputRate L) ≤
        (R : ℝ) * (blockPow L : ℝ)} := by
    refine ⟨⟨a + 1, rfl⟩, hLle, ?_⟩
    have hcast : ((L ^ a : ℕ) : ℝ) ≤ ((L ^ (a + 1) : ℕ) : ℝ) := by exact_mod_cast hstep
    have hnn : (0 : ℝ) ≤ ((L ^ (a + 1) : ℕ) : ℝ) := Nat.cast_nonneg _
    calc x ≤ ((L ^ a : ℕ) : ℝ) := ha
      _ ≤ ((L ^ (a + 1) : ℕ) : ℝ) := hcast
      _ ≤ ((L ^ (a + 1) : ℕ) : ℝ) * (blockPow L : ℝ) := le_mul_of_one_le_right hnn hM
  exact Nat.sInf_mem ⟨_, hmem⟩
theorem minimalInputRate_pos {L : ℕ} (hL : 13 ≤ L)
    (h : (SeparatedClasses.operatorConstantsAt L).Pos) :
    0 < SeparatedSequences.minimalInputRate L := by
  have h13 : (13 : ℝ) ≤ (L : ℝ) := by exact_mod_cast hL
  have hsq : (1 : ℝ) < (L : ℝ) ^ 2 := by nlinarith
  have hzero : 0 < DirichletGreen.FourDimensional.decayRate L := h.zeroFormRate_pos
  have hone : 0 < Weighted.expansionDecayRate 4 L := h.avgSqRate_pos
  have hthree : 0 < SeparatedSequences.sequencePropagatorRate L := h.oneFormRate_pos
  have hfour : 0 < SeparatedSequences.propagatorInverseRate L := h.coarseRate_pos
  have hfive : 0 < (1 - ((L : ℝ) ^ 2)⁻¹) / (32 * 4 * ((L : ℝ) ^ 2 + 1)) :=
    div_pos (sub_pos.mpr (inv_lt_one_of_one_lt₀ hsq)) (by positivity)
  unfold SeparatedSequences.minimalInputRate
  exact lt_min one_pos (lt_min (by linarith) (lt_min (by linarith)
    (lt_min hthree (lt_min (by linarith) hfive))))
theorem minimalInputRate_le_quarter (L : ℕ) :
    SeparatedSequences.minimalInputRate L ≤
      1 / 4 * Dirichlet.FloorComparison.comparisonRate 4 (L : ℝ) := by
  have hlast : SeparatedSequences.minimalInputRate L ≤
      (1 - ((L : ℝ) ^ 2)⁻¹) / (32 * 4 * ((L : ℝ) ^ 2 + 1)) := by
    unfold SeparatedSequences.minimalInputRate
    exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (le_trans (min_le_right _ _)
      (le_trans (min_le_right _ _) (min_le_right _ _))))
  have heq : (1 - ((L : ℝ) ^ 2)⁻¹) / (32 * 4 * ((L : ℝ) ^ 2 + 1)) =
      1 / 4 * Dirichlet.FloorComparison.comparisonRate 4 (L : ℝ) := by
    unfold Dirichlet.FloorComparison.comparisonRate
    push_cast
    rw [show (32 * 4 * ((L : ℝ) ^ 2 + 1)) = 4 * (8 * 4 * ((L : ℝ) ^ 2 + 1)) by ring,
      div_mul_eq_div_div, one_div, ← div_eq_inv_mul, div_div, div_div]
    ring_nf
  exact heq ▸ hlast
theorem valueKinds_and_lowerBounds {L : ℕ} (hL : 13 ≤ L)
    (hpos : (SeparatedClasses.operatorConstantsAt L).Pos)
    (hcmp : Dirichlet.FloorComparison.FloorComparisonStatement) :
    ValueKinds L ∧ LowerBounds L := by
  have hL2 : 2 ≤ L := by omega
  have h13 : (13 : ℝ) ≤ (L : ℝ) := by exact_mod_cast hL
  obtain ⟨hMpow, hMlow⟩ := blockPow_spec hL2
  obtain ⟨hRpow, hRL, hgapIneq⟩ := gapMultiplier_spec hL2
  have hsqlow := sq_le_blockLower L
  have hδ := minimalInputRate_pos hL hpos
  have hδ1 : SeparatedSequences.minimalInputRate L ≤ 1 := min_le_left _ _
  have hgapcast : (gapLength L : ℝ) = (gapMultiplier L : ℝ) * (blockPow L : ℝ) := by
    unfold gapLength
    push_cast
    rfl
  have hg1 : SeparatedSequences.CombinedConstants.derivedGapLower L ≤ (gapLength L : ℝ) := by
    rw [hgapcast]
    exact le_trans (le_max_left _ _) hgapIneq
  have hg2 : 16 * (4 * Real.log (L : ℝ) + Real.log 2) ≤
      (gapLength L : ℝ) * SeparatedSequences.minimalInputRate L := by
    have h := le_trans (le_max_right _ _) hgapIneq
    rw [div_le_iff₀ hδ] at h
    rw [hgapcast]
    exact h
  have hsqnat : L ^ 2 ≤ blockPow L := by
    have h : ((L ^ 2 : ℕ) : ℝ) ≤ (blockPow L : ℝ) := by
      push_cast
      exact le_trans hsqlow hMlow
    exact_mod_cast h
  have hcube : L ^ 3 ≤ gapLength L := by
    unfold gapLength
    calc L ^ 3 = L * L ^ 2 := by ring
      _ ≤ gapMultiplier L * blockPow L := Nat.mul_le_mul hRL hsqnat
  have hlog : 0 ≤ Real.log (L : ℝ) := Real.log_nonneg (by linarith)
  have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hmain := hcmp 4 (L : ℝ) (SeparatedSequences.minimalInputRate L) (blockPow L : ℝ)
    (gapLength L : ℝ) rfl (by linarith) hδ (minimalInputRate_le_quarter L)
    (le_trans hsqlow hMlow)
    (by
      show 4 * (((4 : ℕ) : ℝ) + 2) * Real.log (L : ℝ) / SeparatedSequences.minimalInputRate L ≤
        (gapLength L : ℝ)
      rw [div_le_iff₀ hδ]
      push_cast
      nlinarith)
  have hρ : 0 ≤ 2 * Lattice.siteNearnessRadius L := by
    unfold Lattice.siteNearnessRadius
    positivity
  have hbound : 1 ≤ mainBound L := by
    unfold mainBound
    have he : 1 ≤ Real.exp (2 * Lattice.siteNearnessRadius L) := Real.one_le_exp hρ
    have he2 : 0 < Real.exp 2 := Real.exp_pos 2
    have hc : (1 : ℝ) ≤ 12 * (1 + 16 * Real.exp 2) := by linarith
    have hm : (1 : ℝ) ≤ max 1 (max ((L : ℝ) * SeparatedSequences.CombinedConstants.mainConst L)
        (GreenThreeGroups.secondDiffBound L)) := le_max_left _ _
    exact one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hc he) hm
  refine ⟨⟨hMpow, hRpow, hMlow, hsqlow, hRL, hcube, hδ, hδ1, hbound, ?_, ?_, ?_⟩,
    hg1, ?_, hg2, ?_⟩
  · intro β _ _
    unfold holderBound
    have := le_max_left (1 : ℝ) (SeparatedSequences.CombinedConstants.holderConst L β)
    linarith
  · intro ε _ _
    unfold gradBound
    have := le_max_left (1 : ℝ)
      (max (SeparatedSequences.CombinedConstants.gradConst L (cappedExp ε))
        (3 * GreenThreeGroups.pointwiseConst L ε))
    linarith
  · intro ε β _ _ _ _
    unfold gradHolderBound
    split_ifs
    · have := le_max_left (1 : ℝ)
        (max (SeparatedSequences.CombinedConstants.gradHolderConst L β ε)
          (3 * GreenThreeGroups.holderConst L ε β))
      linarith
    · have := le_max_left (1 : ℝ) (3 * GreenThreeGroups.holderConst L ε β)
      linarith
  · unfold SeparatedSequences.CombinedConstants.derivedGapLower
    exact le_max_left _ _
  · exact hmain.2.2 (blockPow L : ℝ) (gapMultiplier L : ℝ) le_rfl hgapcast.symm.ge
theorem dependencies_hold : Dependencies :=
  ⟨⟨SeparatedSequences.minimalInputRate, fun _ => rfl⟩, ⟨blockPow, fun _ => rfl⟩,
    ⟨gapMultiplier, fun _ => rfl⟩, ⟨gapLength, fun _ => rfl⟩, ⟨mainBound, fun _ => rfl⟩,
    ⟨fun p => holderBound p.1 p.2, fun _ => rfl⟩,
    ⟨fun p => gradBound p.1 p.2, fun _ => rfl⟩,
    ⟨fun p => gradHolderBound p.1 p.2.1 p.2.2, fun _ => rfl⟩⟩
theorem statement_holds (hcl : SeparatedClasses.OperatorBoundsHoldAtConstants)
    (hcmp : Dirichlet.FloorComparison.FloorComparisonStatement) : Statement :=
  ⟨fun L hodd hL => valueKinds_and_lowerBounds hL (hcl.1 L ⟨hodd, hL⟩).1 hcmp, dependencies_hold⟩
end YangMills.Construction.SeparatedSequences.InputConstants.Properties
