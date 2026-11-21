import YangMills.Construction.InequalityOnMirroredCopies.CouplingAtTheLevelOfARadius
import YangMills.Construction.LawInAState.ProductsOfMarksAtOneLevelProof
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ReflectedCopies
open ChessboardTori
private theorem one_add_nat_le_two_pow (m : ℕ) : (1 : ℝ) + m ≤ 2 ^ m := by
  have h : m < 2 ^ m := Nat.lt_two_pow_self
  exact_mod_cast (by omega : 1 + m ≤ 2 ^ m)
private theorem nat_mul_log_two_le {L A ϱ : ℝ} (hL : 4 ≤ L) (hA : 0 < A) (hϱ : 0 < ϱ) {m : ℕ}
    (h : ϱ * L ^ m < A * (1 + m)) :
    (m : ℝ) * Real.log 2 ≤ Real.log A + TorusBound.logPos (1 / ϱ) := by
  have h2 : (0 : ℝ) < 2 ^ m := by positivity
  have h4 : (2 : ℝ) ^ m * 2 ^ m ≤ L ^ m := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (by norm_num) (by linarith) m
  have hlt : ϱ * 2 ^ m < A := by
    have hmul : (ϱ * 2 ^ m) * 2 ^ m < A * 2 ^ m := by
      calc (ϱ * 2 ^ m) * 2 ^ m = ϱ * (2 ^ m * 2 ^ m) := by ring
        _ ≤ ϱ * L ^ m := mul_le_mul_of_nonneg_left h4 hϱ.le
        _ < A * (1 + m) := h
        _ ≤ A * 2 ^ m := mul_le_mul_of_nonneg_left (one_add_nat_le_two_pow m) hA.le
    exact lt_of_mul_lt_mul_right hmul h2.le
  have hlog := Real.log_le_log (by positivity) hlt.le
  rw [Real.log_mul hϱ.ne' h2.ne', Real.log_pow] at hlog
  have hinv : Real.log (1 / ϱ) = - Real.log ϱ := by rw [one_div, Real.log_inv]
  have hp : Real.log (1 / ϱ) ≤ TorusBound.logPos (1 / ϱ) := le_max_left _ _
  linarith
private theorem clusterRange_le_two_mul {x : ℝ} (hx : 1 ≤ x) : (TorusLumps.clusterRange x : ℝ) ≤ 2 * x := by apply _root_.YangMills.SharedProofs.p24708 <;> assumption
private theorem couplingFlow_le_of_depth {p : TorusLumps.StepParameters} {Ξ : ℝ} {D : ChessboardSetup}
    (hD : IsAdmissibleSetup p Ξ D)
    (hmove : ∀ t : ℕ, t < (D.K : ℕ) →
      |(TorusLumps.couplingFlow p D.β (t + 1)).1 - (TorusLumps.couplingFlow p D.β t).1| ≤ 2 * p.B)
    (m t : ℕ) (hm : t + m = (D.K : ℕ)) : (TorusLumps.couplingFlow p D.β t).1 ≤ Ξ + 2 * p.B * m := by
  induction m generalizing t with
  | zero =>
    have ht : t = (D.K : ℕ) := by omega
    rw [ht]
    simpa using hD.2.2
  | succ m ih =>
    have h1 := ih (t + 1) (by omega)
    have h2 := (abs_le.1 (hmove t (by omega))).1
    push_cast
    linarith
private def uncoveredConstant (p : TorusLumps.StepParameters) (Ξ c : ℝ) : ℝ :=
  max Ξ 1 + 2 * p.B / Real.log 2 * (Real.log (2 * c * (max Ξ 1 + 2 * p.B)) + 1)
private theorem log_two_pos' : 0 < Real.log 2 := Real.log_pos (by norm_num)
private theorem one_le_logArgument {p : TorusLumps.StepParameters} {Ξ c : ℝ} (hp : p.Admissible) (hc : 1 ≤ c) :
    1 ≤ 2 * c * (max Ξ 1 + 2 * p.B) := by
  have hM : (1 : ℝ) ≤ max Ξ 1 := le_max_right _ _
  have hB := hp.B_pos
  nlinarith
private theorem max_le_uncoveredConstant {p : TorusLumps.StepParameters} {Ξ c : ℝ} (hp : p.Admissible)
    (hc : 1 ≤ c) : max Ξ 1 ≤ uncoveredConstant p Ξ c := by
  have hk : 0 ≤ 2 * p.B / Real.log 2 := div_nonneg (by linarith [hp.B_pos]) log_two_pos'.le
  have hl := Real.log_nonneg (one_le_logArgument (Ξ := Ξ) hp hc)
  unfold uncoveredConstant
  have := mul_nonneg hk (by linarith : 0 ≤ Real.log (2 * c * (max Ξ 1 + 2 * p.B)) + 1)
  linarith
private theorem couplingFlow_le_of_not_covers {p : TorusLumps.StepParameters} {Ξ c : ℝ}
    (hp : p.Admissible) (hc : 1 ≤ c)
    {D : ChessboardSetup} (hD : IsAdmissibleSetup p Ξ D)
    (hmove : ∀ t : ℕ, t < (D.K : ℕ) →
      |(TorusLumps.couplingFlow p D.β (t + 1)).1 - (TorusLumps.couplingFlow p D.β t).1| ≤ 2 * p.B)
    {ϱ : ℝ} (hϱ : 0 < ϱ) {t : ℕ} (ht : t ≤ (D.K : ℕ)) (hn : ¬ RadiusCoversScale p D c ϱ t) :
    (TorusLumps.couplingFlow p D.β t).1 ≤ uncoveredConstant p Ξ c * (1 + TorusBound.logPos (1 / ϱ)) := by
  obtain ⟨m, hm⟩ : ∃ m : ℕ, t + m = (D.K : ℕ) := ⟨(D.K : ℕ) - t, by omega⟩
  have hA1 := one_le_logArgument (Ξ := Ξ) hp hc
  have hB := hp.B_pos
  have hM1 : (1 : ℝ) ≤ max Ξ 1 := le_max_right _ _
  have hΞM : Ξ ≤ max Ξ 1 := le_max_left _ _
  unfold uncoveredConstant
  generalize max Ξ 1 = M at *
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have hx1 : 1 ≤ (TorusLumps.couplingFlow p D.β t).1 := hp.y₁_ge.trans (hD.2.1 t ht)
  have hxm : (TorusLumps.couplingFlow p D.β t).1 ≤ M + 2 * p.B * m := by
    have := couplingFlow_le_of_depth hD hmove m t hm
    linarith
  have hxm' : (TorusLumps.couplingFlow p D.β t).1 ≤ (M + 2 * p.B) * (1 + m) := by
    nlinarith [mul_nonneg (by linarith : 0 ≤ M) hm0]
  have hr : c * (TorusLumps.clusterRange (TorusLumps.couplingFlow p D.β t).1 : ℝ) ≤
      2 * c * (M + 2 * p.B) * (1 + m) := by
    have h1 := clusterRange_le_two_mul hx1
    have h2 : (TorusLumps.clusterRange (TorusLumps.couplingFlow p D.β t).1 : ℝ) ≤
        2 * ((M + 2 * p.B) * (1 + m)) := by
      linarith
    calc c * (TorusLumps.clusterRange (TorusLumps.couplingFlow p D.β t).1 : ℝ)
        ≤ c * (2 * ((M + 2 * p.B) * (1 + m))) := mul_le_mul_of_nonneg_left h2 (by linarith)
      _ = 2 * c * (M + 2 * p.B) * (1 + m) := by ring
  have hsp : ϱ / levelMesh D t = ϱ * (p.side : ℝ) ^ m := by
    unfold levelMesh
    rw [hD.1]
    have he : ((t : ℤ) - (((D.K : ℕ)) : ℤ)) = -(m : ℤ) := by omega
    rw [he, zpow_neg, zpow_natCast, div_inv_eq_mul]
  have hlt : ϱ * (p.side : ℝ) ^ m < 2 * c * (M + 2 * p.B) * (1 + m) := by
    unfold RadiusCoversScale at hn
    rw [hsp] at hn
    exact (not_le.1 hn).trans_le hr
  have hL : (4 : ℝ) ≤ (p.side : ℝ) := by
    have h := hp.L_ge
    have h' : 4 ≤ p.side := le_trans (by norm_num) h
    exact_mod_cast h'
  have hst := nat_mul_log_two_le hL (by linarith) hϱ hlt
  have hlp : 0 ≤ TorusBound.logPos (1 / ϱ) := le_max_right _ _
  have hlA := Real.log_nonneg hA1
  generalize TorusBound.logPos (1 / ϱ) = lp at *
  generalize Real.log (2 * c * (M + 2 * p.B)) = lA at *
  have hk : 0 ≤ 2 * p.B / Real.log 2 := div_nonneg (by linarith) log_two_pos'.le
  have hkm : 2 * p.B * m ≤ 2 * p.B / Real.log 2 * (lA + lp) := by
    have he : 2 * p.B * m = 2 * p.B / Real.log 2 * (m * Real.log 2) := by
      field_simp [log_two_pos'.ne']
    rw [he]
    exact mul_le_mul_of_nonneg_left hst hk
  generalize 2 * p.B / Real.log 2 = k at *
  have hprod : 0 ≤ (M + k * lA) * lp :=
    mul_nonneg (add_nonneg (by linarith) (mul_nonneg hk hlA)) hlp
  nlinarith
theorem couplingBoundAtRadiusScale_holds : CouplingBoundAtRadiusScale := by
  intro p Ξ c hp hc
  have hb : 1 ≤ uncoveredConstant p Ξ c := (le_max_right _ _).trans (max_le_uncoveredConstant hp hc)
  have hB := hp.B_pos
  refine ⟨uncoveredConstant p Ξ c + 2 * p.B, by linarith, fun D hD hmove ϱ hϱ => ⟨fun s hs => ?_, fun hnone => ?_⟩⟩
  · have hlp : 0 ≤ TorusBound.logPos (1 / ϱ) := le_max_right _ _
    rcases hs.1.eq_or_lt with hsK | hsK
    · have h1 : (TorusLumps.couplingFlow p D.β s).1 ≤ Ξ := by
        rw [hsK]
        exact hD.2.2
      have h2 : Ξ ≤ uncoveredConstant p Ξ c := (le_max_left _ _).trans (max_le_uncoveredConstant hp hc)
      nlinarith
    · have h1 := couplingFlow_le_of_not_covers hp hc hD hmove hϱ (t := s + 1) hsK
        (hs.2.2 (s + 1) (by omega) hsK)
      have h2 := (abs_le.1 (hmove s hsK)).1
      nlinarith [mul_nonneg hB.le hlp]
  · have hlp : 0 ≤ TorusBound.logPos (1 / ϱ) := le_max_right _ _
    have h1 := couplingFlow_le_of_not_covers hp hc hD hmove hϱ (t := 0) (Nat.zero_le _)
      (hnone 0 (Nat.zero_le _))
    have h2 : (TorusLumps.couplingFlow p D.β 0).1 = D.β := rfl
    rw [h2] at h1
    nlinarith
end YangMills.Construction.ReflectedCopies
end
