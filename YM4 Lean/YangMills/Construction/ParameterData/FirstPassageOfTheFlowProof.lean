import YangMills.Construction.FlowConstants.ReferenceWindow
import YangMills.Construction.ParameterData.FirstPassageOfTheFlow
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.TrajectoryData
open TorusLumps StepReturn RenormalizationStepParameters SequencePassage
private theorem couplingFlow_step_abs_le {p : StepParameters} (hr : ExpansionReturnsAt p) (β : ℝ) (t : ℕ)
    (hy : p.y₁ ≤ (couplingFlow p β t).1)
    (hexp : HasExpansion p t (couplingFlow p β t).1 (couplingFlow p β t).2) :
    |(couplingFlow p β (t + 1)).1 - (couplingFlow p β t).1| ≤ 2 * p.B := by
  obtain ⟨x', ⟨hx', hle⟩, huniq⟩ := hr t _ _ hy hexp
  have hex : ∃ x' : ℝ, HasExpansion p (t + 1) x' (kernelImage p (couplingFlow p β t).1 (couplingFlow p β t).2) :=
    ⟨x', hx'⟩
  have hnext : (couplingFlow p β (t + 1)).1 = hex.choose := dif_pos hex
  obtain ⟨_, f, hcold, _⟩ := hex.choose_spec
  rw [hnext, huniq _ f hcold]
  exact hle
abbrev _root_.YangMills.DeltaSharedProofs.p502367 := @couplingFlow_step_abs_le
abbrev _root_.YangMills.SharedProofs.p80822 := @couplingFlow_step_abs_le
private theorem zpow_neg_two_rpow_neg_half {g : ℝ} (hg : 0 < g) : (g ^ (-2 : ℤ)) ^ (-(1 / 2) : ℝ) = g := by apply _root_.YangMills.Construction.FlowConstants.zpow_neg_two_rpow_neg_half <;> assumption
theorem firstPassageExists : firstPassageExistsStatement := by
  intro T y D hD g hg hstar β hβ
  have hb := hD.errorMargin
  have hGpos : 0 < g ^ (-2 : ℤ) := zpow_pos hg _
  have hBpos : 0 < T.B := hb.admissible.B_pos
  have hBs : 2 * T.B ≤ D.shift := hD.shift_ge
  have hXi : D.threshold g = g ^ (-2 : ℤ) + D.shift := rfl
  have hX₀ : D.X₀ ≤ g ^ (-2 : ℤ) :=
    le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hstar
  have hyX : y ≤ D.X₀ := hb.floor_le
  have hc₀ : 10 < D.c₀ := hb.slope_gt
  have hx0 : D.coupling β 0 = β := rfl
  have hlam : D.lam ≤ 3 / 4 * D.c₀ := hD.lam_le
  have hlampos : 0 < D.lam := hD.lam_pos
  have hline : ∀ j : ℕ, (∀ l < j, D.X₀ ≤ D.coupling β l) →
      3 / 4 * D.c₀ * (j : ℝ) - 2 * D.cH ≤ β - D.coupling β j := by
    intro j hj
    have h : 3 / 4 * D.c₀ * ((j : ℝ) - ((0 : ℕ) : ℝ)) - 2 * D.cH ≤ D.coupling β 0 - D.coupling β j :=
      (hb.drop_two_sided β 0 j (Nat.zero_le j) hj).1
    rw [hx0, Nat.cast_zero, sub_zero] at h
    exact h
  have hcH : 0 ≤ D.cH := by
    have := hline 0 (fun l hl => absurd hl (Nat.not_lt_zero l))
    rw [hx0] at this
    simp at this
    linarith
  have hXiX : D.X₀ < D.threshold g := by
    rw [hXi]
    linarith
  have hex : ∃ k, D.coupling β k ≤ D.threshold g := by
    by_contra hno
    simp only [not_exists, not_le] at hno
    obtain ⟨n, hn⟩ := exists_nat_gt ((β - D.threshold g + 2 * D.cH) / (3 / 4 * D.c₀))
    have hl := hline n (fun l _ => (hXiX.trans (hno l)).le)
    have hpos : 0 < 3 / 4 * D.c₀ := by linarith
    rw [div_lt_iff₀ hpos] at hn
    have := hno n
    nlinarith
  classical
  let K := Nat.find hex
  have hKle : D.coupling β K ≤ D.threshold g := Nat.find_spec hex
  have hbefore : ∀ k < K, D.threshold g < D.coupling β k := fun k hk => not_le.mp (Nat.find_min hex hk)
  have hfl : ∀ k < K, D.X₀ ≤ D.coupling β k := fun k hk => (hXiX.trans (hbefore k hk)).le
  have hβX : D.X₀ ≤ β := (hXiX.trans_le hβ).le
  have hexp : ∀ k ≤ K, HasExpansion (T.stepParameters y) k (D.coupling β k)
      (couplingFlow (T.stepParameters y) β k).2 :=
    fun k hk => hb.expansion β k hβX (fun l hl => hfl l (lt_of_lt_of_le hl hk))
  have hstep : ∀ k < K, |D.coupling β (k + 1) - D.coupling β k| ≤ 2 * T.B := fun k hk =>
    couplingFlow_step_abs_le hb.returns β k (hyX.trans (hfl k hk)) (hexp k hk.le)
  have habove : ∀ k ≤ K, g ^ (-2 : ℤ) < D.coupling β k := by
    intro k hk
    rcases Nat.lt_or_ge k K with hlt | hge
    · have := hbefore k hlt
      rw [hXi] at this
      linarith
    · obtain rfl : k = K := le_antisymm hk hge
      rcases Nat.eq_zero_or_pos K with h0 | hpos
      · rw [h0, hx0]
        rw [hXi] at hβ
        linarith
      · obtain ⟨m, hm⟩ : ∃ m, K = m + 1 := ⟨K - 1, by omega⟩
        have h1 := hbefore m (by omega)
        have h2 := abs_le.mp (hstep m (by omega))
        rw [hm]
        rw [hXi] at h1
        linarith [h2.1]
  have hdrop : ∀ k ≤ K, β - D.coupling β k ≤ D.shift * (k : ℝ) := by
    intro k
    induction k with
    | zero => intro _; simp [hx0]
    | succ m ih =>
      intro hk
      have h1 := ih (by omega)
      have h2 := abs_le.mp (hstep m (by omega))
      push_cast
      linarith [h2.1]
  have hBspos : 0 < D.shift := by linarith
  have hxpos : 0 < D.coupling β K := hGpos.trans (habove K le_rfl)
  refine ⟨K, ⟨⟨hKle, hbefore⟩, hexp, habove, ?_, ?_, ?_, ?_⟩⟩
  · have h1 := hdrop K le_rfl
    have h2 : (β - g ^ (-2 : ℤ)) / D.shift ≤ (K : ℝ) + 1 := by
      rw [div_le_iff₀ hBspos]
      rw [hXi] at hKle
      linarith
    linarith
  · rcases Nat.eq_zero_or_pos K with h0 | hpos
    · rw [h0]
      have hnn : 0 ≤ (β - g ^ (-2 : ℤ) - D.shift + D.c₅) / D.lam := by
        apply div_nonneg _ hlampos.le
        have : D.c₅ = 2 * D.cH := rfl
        rw [hXi] at hβ
        linarith
      simp only [Nat.cast_zero]
      linarith
    · obtain ⟨m, hm⟩ : ∃ m, K = m + 1 := ⟨K - 1, by omega⟩
      have h1 := hbefore m (by omega)
      have h2 := hline m (fun l hl => hfl l (by omega))
      have hc : D.c₅ = 2 * D.cH := rfl
      have hm0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
      have h3 : (m : ℝ) ≤ (β - g ^ (-2 : ℤ) - D.shift + D.c₅) / D.lam := by
        rw [le_div_iff₀ hlampos]
        rw [hXi] at h1
        nlinarith
      rw [hm]
      push_cast
      linarith
  · exact Real.rpow_le_rpow_of_nonpos hxpos hKle (by norm_num)
  · have h := Real.rpow_lt_rpow_of_neg hGpos (habove K le_rfl) (by norm_num : (-(1 / 2) : ℝ) < 0)
    rw [zpow_neg_two_rpow_neg_half hg] at h
    exact h
end YangMills.Construction.TrajectoryData
end
