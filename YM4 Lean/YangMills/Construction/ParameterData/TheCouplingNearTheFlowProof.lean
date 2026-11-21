import YangMills.Construction.ParameterData.TheCouplingNearTheFlow
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.TrajectoryData
open TorusLumps CouplingFlow RenormalizationStepParameters
variable {T : ParameterAssignment} {y : ℝ} {D : TrajectoryParameters T y}
private theorem abs_step_le (hD : D.Admissible) {β : ℝ} {t : ℕ} (hl : ∀ l ≤ t, D.X₀ ≤ D.coupling β l) :
    |D.coupling β (t + 1) - D.coupling β t| ≤ 2 * T.B := by
  have hb := hD.errorMargin
  have hexp : HasExpansion (T.stepParameters y) t (couplingAt (T.stepParameters y) β t)
      (couplingFlow (T.stepParameters y) β t).2 :=
    hb.expansion β t (hl 0 (Nat.zero_le _)) fun l hlt => hl l hlt.le
  have hy : (T.stepParameters y).y₁ ≤ couplingAt (T.stepParameters y) β t := hb.floor_le.trans (hl t le_rfl)
  obtain ⟨x', ⟨hx', hstep⟩, huniq⟩ := hb.returns t _ _ hy hexp
  have hex : ∃ x' : ℝ, HasExpansion (T.stepParameters y) (t + 1) x'
      (kernelImage (T.stepParameters y) (couplingAt (T.stepParameters y) β t)
        (couplingFlow (T.stepParameters y) β t).2) := ⟨x', hx'⟩
  have hnext : expansionCoupling (T.stepParameters y) t (couplingAt (T.stepParameters y) β t)
      (couplingFlow (T.stepParameters y) β t).2 = hex.choose :=
    dif_pos hex
  obtain ⟨-, f₁, hc₁, -⟩ := hex.choose_spec
  have heq : D.coupling β (t + 1) = x' := hnext.trans (huniq _ _ hc₁)
  rw [heq]
  exact hstep
private theorem zpow_neg_two_le_coupling (hD : D.Admissible) {g β : ℝ} {K : ℕ}
    (hX : D.X₀ ≤ g ^ (-2 : ℤ)) (hβ : β ∈ D.passageWindow K g) :
    ∀ k ≤ K, g ^ (-2 : ℤ) ≤ D.coupling β k := by
  obtain ⟨hβ₀, -, hcut⟩ := hβ
  have hB : 0 < T.B := hD.errorMargin.admissible.B_pos
  have hBs : 2 * T.B ≤ D.shift := hD.shift_ge
  have hlevel : SequencePassage.passageThreshold D.shift g = g ^ (-2 : ℤ) + D.shift := rfl
  rw [hlevel] at hβ₀ hcut
  have hbefore : ∀ k < K, g ^ (-2 : ℤ) ≤ D.coupling β k := fun k hk => by
    have := hcut k hk
    linarith
  intro k hk
  rcases hk.lt_or_eq with hk | rfl
  · exact hbefore k hk
  · cases k with
    | zero =>
      have h0 : D.coupling β 0 = β := rfl
      rw [h0]
      linarith
    | succ m =>
      have hs := abs_le.mp (abs_step_le hD (β := β) (t := m) fun l hl =>
        hX.trans (hbefore l (Nat.lt_succ_of_le hl)))
      have := hcut m (Nat.lt_succ_self m)
      linarith [hs.1]
private theorem rpow_neg_quarter_le {g x : ℝ} (hg : 0 < g) (hx : g ^ (-2 : ℤ) ≤ x) :
    x ^ (-(1 / 4) : ℝ) ≤ g ^ (1 / 2 : ℝ) := by
  have h0 : 0 < g ^ (-2 : ℤ) := zpow_pos hg _
  have h1 := Real.rpow_le_rpow_of_nonpos h0 hx (z := (-(1 / 4) : ℝ)) (by norm_num)
  have h2 : (g ^ (-2 : ℤ)) ^ (-(1 / 4) : ℝ) = g ^ (1 / 2 : ℝ) := by
    rw [← Real.rpow_intCast, ← Real.rpow_mul hg.le]
    norm_num
  rwa [h2] at h1
theorem couplingNearFlow : couplingNearFlowStatement := by
  intro T y D hD g hg hgy K β hβ
  have hb := hD.errorMargin
  have hX : D.X₀ ≤ g ^ (-2 : ℤ) := ((le_max_left _ _).trans (le_max_left _ _)).trans hgy
  have habove := zpow_neg_two_le_coupling hD hX hβ
  have hnear : ∀ k ≤ K, |D.coupling β k - D.numberFlow β k| ≤ 2 * D.Cr * D.coupling β k ^ (-(1 / 4) : ℝ) :=
    fun k hk => ((hb.bounds β).boundsUpTo k fun l hl => hX.trans (habove l (hl.trans hk))).near_flow
  refine ⟨hnear, (hnear K le_rfl).trans ?_⟩
  exact mul_le_mul_of_nonneg_left (rpow_neg_quarter_le hg (habove K le_rfl)) (by linarith [hb.Cr_nonneg])
end YangMills.Construction.TrajectoryData
end
