import YangMills.Construction.SystemOfAdmissibleConstants.TheFourBoundsAlongTheTrajectory
import YangMills.Construction.TotalDensitiesGiveASystem.GlueAtDrawnParameters
import YangMills.Construction.TotalDensitiesGiveASystem.TheBoundsAtTheData
import YangMills.Construction.TotalDensitiesGiveASystem.TheCouplingsGiveTheWindow
import YangMills.Construction.TotalDensitiesGiveASystem.TheExpansionFlowIsTheTotalFlow
import Mathlib
set_option autoImplicit false
open Filter MeasureTheory Set
open scoped Topology
noncomputable section
namespace YangMills.Construction.TotalDensities
private theorem truncatedDist_pos' {d : ℝ} (hd : 0 < d) : 0 < AdmissibleConstants.truncatedDist d :=
  lt_min hd one_pos
private theorem truncatedDist_mono' {d d' : ℝ} (h : d ≤ d') :
    AdmissibleConstants.truncatedDist d ≤ AdmissibleConstants.truncatedDist d' :=
  min_le_min_right _ h
private theorem cumulantConstant_pos' {L : ℕ} {A b : ℝ} (hL : 0 < L) :
    0 < AdmissibleConstants.cumulantConstant L A b := by
  have h : (0 : ℝ) < 24 * 2 ^ 40 * (L : ℝ) ^ 12 := by
    have : (0 : ℝ) < L := by exact_mod_cast hL
    positivity
  unfold AdmissibleConstants.cumulantConstant
  have := lt_of_lt_of_le h (le_max_right (10 * 2 ^ 53 * (L : ℝ) ^ 5 * A * Real.exp (b + b ^ ((20 : ℝ) / 19))) _)
  linarith
private theorem cumulantBound_le_torusCumulantBound {L : ℕ} {A b : ℝ} (hL : 0 < L) (n : ℕ) {d l : ℝ}
    (hd : 0 < d) (hl : 1 ≤ l) :
    AdmissibleConstants.cumulantBound L A b n d l ≤
      AdmissibleConstants.torusCumulantBound L A b n d * Real.exp (n * 4 * l ^ 4) := by
  have hC := cumulantConstant_pos' (A := A) (b := b) hL
  have hd₁ := truncatedDist_pos' hd
  have h1 : 1 + l ≤ Real.exp l := by linarith [Real.add_one_le_exp l]
  have h2 : (1 + l) ^ 4 ≤ Real.exp (4 * l ^ 4) := by
    have h3 : (1 + l) ^ 4 ≤ Real.exp l ^ 4 := pow_le_pow_left₀ (by linarith) h1 4
    have h4 : Real.exp l ^ 4 = Real.exp (4 * l) := by rw [← Real.exp_nat_mul]; norm_num
    have h5 : l ≤ l ^ 4 := le_self_pow₀ hl (by norm_num)
    rw [h4] at h3
    exact h3.trans (Real.exp_le_exp.2 (by linarith))
  have h6 : ((1 + l) ^ 4) ^ n ≤ Real.exp (n * 4 * l ^ 4) := by
    have h7 := pow_le_pow_left₀ (by positivity) h2 n
    have h8 : Real.exp (4 * l ^ 4) ^ n = Real.exp (n * 4 * l ^ 4) := by
      rw [← Real.exp_nat_mul]; ring_nf
    rwa [h8] at h7
  unfold AdmissibleConstants.cumulantBound AdmissibleConstants.torusCumulantBound
  have e : (AdmissibleConstants.cumulantConstant L A b * (1 + l) ^ 4 *
        ((n : ℝ) / AdmissibleConstants.truncatedDist d) ^ 5) ^ n =
      (AdmissibleConstants.cumulantConstant L A b * ((n : ℝ) / AdmissibleConstants.truncatedDist d) ^ 5) ^ n *
        ((1 + l) ^ 4) ^ n := by
    rw [← mul_pow]; ring_nf
  rw [e, ← mul_assoc]
  exact mul_le_mul_of_nonneg_left h6 (by positivity)
private theorem cumulantBound_le_growth {L : ℕ} {A b : ℝ} (hL : 0 < L) (n : ℕ) {d R : ℝ} (hd : 0 < d)
    (hR : 0 < R) :
    AdmissibleConstants.cumulantBound L A b n d R ≤
      AdmissibleConstants.growthPrefactor d * AdmissibleConstants.growthRate L A b R ^ n *
        (n.factorial : ℝ) ^ (7 : ℝ) := by
  have hC := cumulantConstant_pos' (A := A) (b := b) hL
  have hd₁ := truncatedDist_pos' (d := d) hd
  set C := AdmissibleConstants.cumulantConstant L A b
  set X := AdmissibleConstants.truncatedDist d ^ (-5 : ℤ) with hX
  have hXpos : 0 < X := zpow_pos hd₁ _
  have hfac : (0 : ℝ) < n.factorial := by exact_mod_cast Nat.factorial_pos n
  have hnn : (n : ℝ) ^ n ≤ Real.exp n * n.factorial := by
    have := Real.pow_div_factorial_le_exp (n : ℝ) (Nat.cast_nonneg n) n
    rwa [div_le_iff₀ hfac] at this
  have hXn : X ^ n ≤ Real.exp X * n.factorial := by
    have := Real.pow_div_factorial_le_exp X hXpos.le n
    rwa [div_le_iff₀ hfac] at this
  have hbase : ((n : ℝ) / AdmissibleConstants.truncatedDist d) ^ 5 = (n : ℝ) ^ 5 * X := by
    rw [hX, zpow_neg, div_pow, div_eq_mul_inv]
    try norm_cast
  have hpow : (C * (1 + R) ^ 4 * ((n : ℝ) / AdmissibleConstants.truncatedDist d) ^ 5) ^ n =
      (C * (1 + R) ^ 4) ^ n * ((n : ℝ) ^ n) ^ 5 * X ^ n := by
    rw [hbase, ← pow_mul, mul_comm n 5, pow_mul]
    rw [show C * (1 + R) ^ 4 * ((n : ℝ) ^ 5 * X) = C * (1 + R) ^ 4 * (n : ℝ) ^ 5 * X by ring, mul_pow, mul_pow]
  have hexp : Real.exp n ^ 5 = Real.exp 5 ^ n := by
    rw [← Real.exp_nat_mul, ← Real.exp_nat_mul]
    congr 1
    push_cast
    ring
  have hseven : (n.factorial : ℝ) ^ (7 : ℝ) = (n.factorial : ℝ) ^ 7 := by
    exact_mod_cast Real.rpow_natCast (n.factorial : ℝ) 7
  unfold AdmissibleConstants.cumulantBound AdmissibleConstants.growthPrefactor AdmissibleConstants.growthRate
  rw [hpow, hseven]
  calc (n.factorial : ℝ) * ((C * (1 + R) ^ 4) ^ n * ((n : ℝ) ^ n) ^ 5 * X ^ n)
      ≤ (n.factorial : ℝ) * ((C * (1 + R) ^ 4) ^ n * (Real.exp n * n.factorial) ^ 5 * (Real.exp X * n.factorial)) := by
        gcongr
    _ = Real.exp X * (Real.exp 5 * C * (1 + R) ^ 4) ^ n * (n.factorial : ℝ) ^ 7 := by
        have e1 : Real.exp 5 * C * (1 + R) ^ 4 = Real.exp 5 * (C * (1 + R) ^ 4) := by ring
        rw [e1, mul_pow (Real.exp 5), mul_pow (Real.exp n), hexp]
        generalize (C * (1 + R) ^ 4) ^ n = E
        ring
private def cumulantLimitConstants (L : ℕ) (A b : ℝ) : SystemsWithFiveBounds.LimitConstants where
  localBound n d R := AdmissibleConstants.cumulantBound L A b n d R
  globalPrefactor d _ := AdmissibleConstants.growthPrefactor d
  globalBase R := AdmissibleConstants.growthRate L A b R
  globalExp := 7
  schwartzOrder := 1
  schwartzPrefactor := 1
  schwartzBase := 1
  schwartzExp := 1
  clusterConst _ _ := 1
  clusterRadius _ _ := 1
private theorem cumulantLimitConstants_valid {L : ℕ} {A b : ℝ} (hL : 0 < L) :
    (cumulantLimitConstants L A b).Valid where
  globalExp_nonneg := by show (0 : ℝ) ≤ 7; norm_num
  localBound_antitone n hn R hR := fun d hd d' hd' hdd => by
    have hC := cumulantConstant_pos' (A := A) (b := b) hL
    have h0 : 0 < AdmissibleConstants.truncatedDist d := truncatedDist_pos' hd
    have hle : AdmissibleConstants.truncatedDist d ≤ AdmissibleConstants.truncatedDist d' :=
      truncatedDist_mono' hdd
    have h0' : 0 < AdmissibleConstants.truncatedDist d' := lt_of_lt_of_le h0 hle
    have h1 : 0 < 1 + R := by have : (0 : ℝ) < R := hR; linarith
    show AdmissibleConstants.cumulantBound L A b n d' R ≤ AdmissibleConstants.cumulantBound L A b n d R
    unfold AdmissibleConstants.cumulantBound
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    gcongr
  localBound_pos n hn d R hd hR := by
    have hC := cumulantConstant_pos' (A := A) (b := b) hL
    have h0 : 0 < AdmissibleConstants.truncatedDist d := truncatedDist_pos' hd
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
    show 0 < AdmissibleConstants.cumulantBound L A b n d R
    unfold AdmissibleConstants.cumulantBound
    positivity
  globalPrefactor_pos d R _ _ := Real.exp_pos _
  globalBase_pos R hR := by
    have hC := cumulantConstant_pos' (A := A) (b := b) hL
    show 0 < AdmissibleConstants.growthRate L A b R
    unfold AdmissibleConstants.growthRate
    positivity
  schwartzOrder_pos := one_pos
  schwartzPrefactor_pos := one_pos
  schwartzBase_pos := one_pos
  schwartzExp_pos := one_pos
  clusterConst_pos _ _ := one_pos
  clusterRadius_pos _ _ := one_pos
theorem cumulantBoundsExist_of_trajectory (hG : TrajectoryCouplingsGiveWindow.Statement)
    (hC : SystemOfAdmissibleConstants.FamilyBoundsAlongFlow)
    (hJ : expansionFlowEqTotalFlow) : CumulantBoundsExist := by
  refine HoldsAtAdmissibleParameters.mono (HoldsAtAdmissibleParameters.and (hG _ hC) hJ) fun T y hDr hA => ?_
  obtain ⟨h, hj⟩ := hA
  obtain ⟨y₂, f⟩ := h (2 * T.B) le_rfl
  obtain ⟨y₃, j⟩ := hj (2 * T.B) le_rfl
  refine ⟨max y₂ y₃, fun g hg hy => ?_⟩
  obtain ⟨D, hDB, A, b, -, -, hcl, -⟩ := f g hg (le_trans (le_max_left _ _) hy)
  have hjg := j g hg (le_trans (le_max_right _ _) hy)
  have hLpos : 0 < T.side := lt_of_lt_of_le (by norm_num) hDr.L_ge
  have toWindow : ∀ (K : ℕ+) (β : ℝ),
      TotalDensitySystem.IsFirstPassagePair (T.stepParameters y) (2 * T.B) g K β →
        β ∈ D.passageWindow K g := fun K β h' => by
    have h'' : β ∈ SequencePassage.definedPassageWindow
      (TotalDensityFlow.IsDefinedUpTo (T.stepParameters y)) (2 * T.B) g
      (TotalDensityFlow.coupling (T.stepParameters y)) K := h'
    rw [(hjg K).1] at h''
    show β ∈ SequencePassage.passageWindow D.shift g D.coupling K
    rw [hDB]
    exact h''
  have cl := hcl 1 le_rfl
  refine ⟨4, AdmissibleConstants.torusCumulantBound T.side A b, cumulantLimitConstants T.side A b,
    cumulantLimitConstants_valid hLpos, ?_, ?_, ?_⟩
  · intro K β hp m n hn d hd f' hf hs
    have h₁ := cl.torus K β (toWindow K β hp) m n hn d hd f' hf hs
    refine h₁.trans (mul_le_mul_of_nonneg_right (cumulantBound_le_torusCumulantBound hLpos n hd ?_) ?_)
    · have : (1 : ℝ) ≤ PeriodicLattice.torusSide T.side m := by
        have hL1 : (1 : ℝ) ≤ (T.side : ℝ) := by exact_mod_cast hLpos
        have : (1 : ℝ) ≤ (T.side : ℝ) ^ (m : ℕ) := one_le_pow₀ hL1
        unfold PeriodicLattice.torusSide
        linarith
      exact this
    · exact Finset.prod_nonneg fun i _ => le_trans (Real.iSup_nonneg fun x => norm_nonneg _) (le_max_left _ _)
  · intro K β hp m n hn R d hR hd f' hf hb hs
    have h₁ := cl.ballOnTori K β (toWindow K β hp) m n hn R d hR hd f' hf hb hs
    refine ⟨h₁, h₁.trans (mul_le_mul_of_nonneg_right (cumulantBound_le_growth hLpos n hd hR) ?_)⟩
    exact Finset.prod_nonneg fun i _ => le_trans (Real.iSup_nonneg fun x => norm_nonneg _) (le_max_left _ _)
  · intro K β hp ν hν n hn R d hR hd f' hf hb hs
    have h₁ := cl.ballInStates K β (toWindow K β hp) ν hν n hn R d hR hd f' hf hb hs
    refine ⟨h₁, h₁.trans (mul_le_mul_of_nonneg_right (cumulantBound_le_growth hLpos n hd hR) ?_)⟩
    exact Finset.prod_nonneg fun i _ => le_trans (Real.iSup_nonneg fun x => norm_nonneg _) (le_max_left _ _)
end YangMills.Construction.TotalDensities
end
