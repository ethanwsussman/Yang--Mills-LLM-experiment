import YangMills.Construction.SystemOfAdmissibleConstants.TheFourBoundsAlongTheTrajectory
import YangMills.Construction.TotalDensitiesGiveASystem.GlueAtDrawnParameters
import YangMills.Construction.TotalDensitiesGiveASystem.TheCouplingsGiveTheWindow
import YangMills.Construction.TotalDensitiesGiveASystem.TheExpansionFlowIsTheTotalFlow
import YangMills.Construction.TotalDensitiesGiveASystem.ThePowerBoundAtTheData
import Mathlib
set_option autoImplicit false
open Filter MeasureTheory Set
open scoped Topology
noncomputable section
namespace YangMills.Construction.TotalDensities
private theorem factorial_mul_pow_le (Ccum R d : ℝ) (hC : 0 < Ccum) (hR : 0 < R) (hd : 0 < d) (n : ℕ) :
    (n.factorial : ℝ) * (Ccum * (1 + R) ^ 4 * ((n : ℝ) / min d 1) ^ 5) ^ n ≤
      (Real.exp 5 * Ccum * max 1 (d ^ (-((5 : ℕ) : ℤ))) * (1 + R) ^ 4) ^ n * (n.factorial : ℝ) ^ (6 : ℝ) := by
  have hX : (1 / min d 1) ^ 5 = max 1 (d ^ (-((5 : ℕ) : ℤ))) := by
    rcases le_total d 1 with h | h
    · have h1 : (1 : ℝ) ≤ d ^ (-((5 : ℕ) : ℤ)) := by
        rw [zpow_neg, zpow_natCast]
        exact (one_le_inv₀ (by positivity)).2 (pow_le_one₀ hd.le h)
      rw [min_eq_left h, max_eq_right h1, zpow_neg, zpow_natCast, one_div, inv_pow]
    · have h1 : d ^ (-((5 : ℕ) : ℤ)) ≤ 1 := by
        rw [zpow_neg, zpow_natCast]
        exact inv_le_one_of_one_le₀ (one_le_pow₀ h)
      rw [min_eq_right h, max_eq_left h1]
      norm_num
  set X := max 1 (d ^ (-((5 : ℕ) : ℤ))) with hXdef
  have hfac : (0 : ℝ) < n.factorial := by exact_mod_cast Nat.factorial_pos n
  have hnn : ((n : ℝ) ^ n) ≤ Real.exp n * n.factorial := by
    have := Real.pow_div_factorial_le_exp (n : ℝ) (Nat.cast_nonneg n) n
    rwa [div_le_iff₀ hfac] at this
  have hbase : (n : ℝ) / min d 1 = n * (1 / min d 1) := by ring
  have hpow : (Ccum * (1 + R) ^ 4 * ((n : ℝ) / min d 1) ^ 5) ^ n =
      (Ccum * (1 + R) ^ 4 * X) ^ n * ((n : ℝ) ^ n) ^ 5 := by
    rw [hbase, mul_pow (n : ℝ), hX]
    rw [show Ccum * (1 + R) ^ 4 * ((n : ℝ) ^ 5 * X) = Ccum * (1 + R) ^ 4 * X * (n : ℝ) ^ 5 by ring, mul_pow,
      ← pow_mul, ← pow_mul, mul_comm 5 n]
  have hexp : Real.exp n ^ 5 = Real.exp 5 ^ n := by
    rw [← Real.exp_nat_mul, ← Real.exp_nat_mul]
    congr 1
    push_cast
    ring
  have hsix : (n.factorial : ℝ) ^ (6 : ℝ) = (n.factorial : ℝ) ^ 6 := by
    exact_mod_cast Real.rpow_natCast (n.factorial : ℝ) 6
  rw [hpow, hsix]
  calc (n.factorial : ℝ) * ((Ccum * (1 + R) ^ 4 * X) ^ n * ((n : ℝ) ^ n) ^ 5)
      ≤ (n.factorial : ℝ) * ((Ccum * (1 + R) ^ 4 * X) ^ n * (Real.exp n * n.factorial) ^ 5) := by
        gcongr
    _ = (Real.exp 5 * Ccum * X * (1 + R) ^ 4) ^ n * (n.factorial : ℝ) ^ 6 := by
        have e1 : Real.exp 5 * Ccum * X * (1 + R) ^ 4 = Real.exp 5 * (Ccum * (1 + R) ^ 4 * X) := by ring
        rw [e1, mul_pow (Real.exp 5), mul_pow (Real.exp n), hexp]
        generalize Ccum * (1 + R) ^ 4 * X = E
        ring
private theorem cumulantConstant_pos {L : ℕ} {A b : ℝ} (hL : 0 < L) :
    0 < AdmissibleConstants.cumulantConstant L A b := by
  have h : (0 : ℝ) < 24 * 2 ^ 40 * (L : ℝ) ^ 12 := by
    have : (0 : ℝ) < L := by exact_mod_cast hL
    positivity
  unfold AdmissibleConstants.cumulantConstant
  have := lt_of_lt_of_le h (le_max_right (10 * 2 ^ 53 * (L : ℝ) ^ 5 * A * Real.exp (b + b ^ ((20 : ℝ) / 19))) _)
  linarith
theorem powerBoundAtData_of_trajectoryBounds (hG : TrajectoryCouplingsGiveWindow.Statement)
    (hC : SystemOfAdmissibleConstants.FamilyBoundsAlongFlow)
    (hJ : expansionFlowEqTotalFlow) : PowerBoundAtData := by
  refine HoldsAtAdmissibleParameters.mono (HoldsAtAdmissibleParameters.and (hG _ hC) hJ) fun T y hDr hA => ?_
  obtain ⟨h, hj⟩ := hA
  obtain ⟨y₂, f⟩ := h (2 * T.B) le_rfl
  obtain ⟨y₃, j⟩ := hj (2 * T.B) le_rfl
  refine ⟨max y₂ y₃, fun g hg hy => ?_⟩
  obtain ⟨D, hDB, A, b, -, -, hcl, -⟩ := f g hg (le_trans (le_max_left _ _) hy)
  have hjg := j g hg (le_trans (le_max_right _ _) hy)
  have hLpos : 0 < T.side := lt_of_lt_of_le (by norm_num) hDr.L_ge
  have toWindow : ∀ (K : ℕ+) (β : ℝ), TotalDensitySystem.IsFirstPassagePair (T.stepParameters y) (2 * T.B) g K β →
      β ∈ D.passageWindow K g := fun K β h' => by
    have h'' : β ∈ SequencePassage.definedPassageWindow
      (TotalDensityFlow.IsDefinedUpTo (T.stepParameters y)) (2 * T.B) g
      (TotalDensityFlow.coupling (T.stepParameters y)) K := h'
    rw [(hjg K).1] at h''
    show β ∈ SequencePassage.passageWindow D.shift g D.coupling K
    rw [hDB]
    exact h''
  have cl := hcl 1 le_rfl
  have hbase := cumulantConstant_pos (A := A) (b := b) hLpos
  refine ⟨Real.exp 5 * AdmissibleConstants.cumulantConstant T.side A b, by positivity,
    fun K β hp m n hn R d hR hd f' hf hb hs => ?_⟩
  have h₁ := cl.ballOnTori K β (toWindow K β hp) m n hn R d hR hd f' hf hb hs
  refine h₁.trans (mul_le_mul_of_nonneg_right ?_ ?_)
  · exact factorial_mul_pow_le (AdmissibleConstants.cumulantConstant T.side A b) R d hbase hR hd n
  · exact Finset.prod_nonneg fun i _ => le_trans (Real.iSup_nonneg fun x => norm_nonneg _) (le_max_left _ _)
end YangMills.Construction.TotalDensities
end
