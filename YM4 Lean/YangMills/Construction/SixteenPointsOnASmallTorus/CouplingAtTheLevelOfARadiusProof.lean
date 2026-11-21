import YangMills.Construction.SixteenPointsOnASmallTorus.CouplingAtTheLevelOfARadius
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.SmallTorusCopies
open TorusLumps StepReturn ResponseInTheExpansion
private theorem expansionCoupling_of_returns {p : StepParameters} (hret : ExpansionReturnsAt p) {t : ℕ} {x : ℝ}
    {D : TorusFunctional} (hx : p.y₁ ≤ x) (hD : HasExpansion p t x D) :
    HasExpansion p (t + 1) (expansionCoupling p t x D) (kernelImage p x D) ∧
      |expansionCoupling p t x D - x| ≤ 2 * p.B := by
  obtain ⟨x', ⟨h1, h2⟩, h3⟩ := hret t x D hx hD
  have hex : ∃ x' : ℝ, HasExpansion p (t + 1) x' (kernelImage p x D) := ⟨x', h1⟩
  have hn : expansionCoupling p t x D = x' := by
    unfold expansionCoupling
    rw [dif_pos hex]
    obtain ⟨_, f, hf, _⟩ := hex.choose_spec
    exact h3 _ f hf
  rw [hn]
  exact ⟨h1, h2⟩
abbrev _root_.YangMills.SharedProofs.p2841 := @expansionCoupling_of_returns
private theorem hasExpansion_couplingFlow {p : StepParameters} (hret : ExpansionReturnsAt p) {β : ℝ}
    (h0 : HasExpansion p 0 β (wilsonWeight β)) :
    ∀ t : ℕ, (∀ j < t, p.y₁ ≤ (couplingFlow p β j).1) →
      HasExpansion p t (couplingFlow p β t).1 (couplingFlow p β t).2 := by
  intro t
  induction t with
  | zero => exact fun _ => h0
  | succ t ih =>
    intro hj
    exact (expansionCoupling_of_returns hret (hj t (Nat.lt_succ_self t))
      (ih fun j hjt => hj j (Nat.lt_succ_of_lt hjt))).1
abbrev _root_.YangMills.DeltaSharedProofs.p3925 := @hasExpansion_couplingFlow
abbrev _root_.YangMills.SharedProofs.p3977 := @hasExpansion_couplingFlow
private theorem couplingFlow_le_of_remaining {p : StepParameters} (hret : ExpansionReturnsAt p)
    (hw : ∀ β : ℝ, p.y₁ ≤ β → HasExpansion p 0 β (wilsonWeight β)) {Ξ β : ℝ} {K : ℕ}
    (hd : IsAdmissibleFlow p Ξ β K) :
    ∀ n t : ℕ, t + n = K → (couplingFlow p β t).1 ≤ Ξ + 2 * p.B * n := by
  have h0 : HasExpansion p 0 β (wilsonWeight β) := hw β (hd.coupling_ge 0 (Nat.zero_le K))
  intro n
  induction n with
  | zero =>
    intro t ht
    have : t = K := by omega
    subst this
    simpa using hd.coupling_le
  | succ n ih =>
    intro t ht
    have hnext := ih (t + 1) (by omega)
    have hexp := hasExpansion_couplingFlow hret h0 t fun j hj => hd.coupling_ge j (by omega)
    have hstep := (expansionCoupling_of_returns hret (hd.coupling_ge t (by omega)) hexp).2
    have hle : (couplingFlow p β t).1 - (couplingFlow p β (t + 1)).1 ≤ 2 * p.B := by
      have := (abs_le.mp hstep).1
      change -(2 * p.B) ≤ (couplingFlow p β (t + 1)).1 - (couplingFlow p β t).1 at this
      linarith
    push_cast
    linarith
private theorem coupling_le_of_not_fits {L : ℕ} (hL : 3 ≤ L) {B Ξ v ρ : ℝ} {n : ℕ} (hB : 1 ≤ B) (hΞ : 0 ≤ Ξ)
    (hv : 1 ≤ v) (hρ : 0 < ρ) (hfit : ρ * (L : ℝ) ^ n < 2 ^ 11 * (clusterRange v : ℝ))
    (hup : v ≤ Ξ + 2 * B * n) :
    v ≤ 2 * Ξ + 48 * B + B ^ 2 + 4 * B * TorusBound.logPos (1 / ρ) := by
  have hB0 : 0 < B := by linarith
  have hv0 : 0 < v := by linarith
  have hL0 : (0 : ℝ) < L := by
    have : 0 < L := by omega
    exact_mod_cast this
  have hlogL : 1 ≤ Real.log L := by
    rw [Real.le_log_iff_exp_le hL0]
    have h3 : (3 : ℝ) ≤ L := by exact_mod_cast hL
    have := Real.exp_one_lt_d9
    linarith
  set w : ℝ := v ^ ((1 : ℝ) / 100) with hw
  have hw1 : 1 ≤ w := Real.one_le_rpow hv (by norm_num)
  have hr : (clusterRange v : ℝ) ≤ 2 * w := by
    have := Nat.ceil_lt_add_one (a := w) (by linarith)
    have e : (clusterRange v : ℝ) = ((⌈w⌉₊ : ℕ) : ℝ) := rfl
    rw [e]
    linarith
  have hlogw : Real.log w = (1 / 100) * Real.log v := by
    rw [hw, Real.log_rpow hv0]
  have hlog2 : Real.log 2 ≤ 1 := by
    have := Real.log_two_lt_d9
    linarith
  have hpos : 0 < ρ * (L : ℝ) ^ n := by positivity
  have h1 : Real.log (ρ * (L : ℝ) ^ n) ≤ Real.log (2 ^ 12 * w) := by
    apply Real.log_le_log hpos
    have : (2 : ℝ) ^ 11 * (clusterRange v : ℝ) ≤ 2 ^ 12 * w := by
      have := mul_le_mul_of_nonneg_left hr (by norm_num : (0 : ℝ) ≤ 2 ^ 11)
      calc (2 : ℝ) ^ 11 * (clusterRange v : ℝ) ≤ 2 ^ 11 * (2 * w) := this
        _ = 2 ^ 12 * w := by ring
    linarith
  have h2 : Real.log (ρ * (L : ℝ) ^ n) = Real.log ρ + n * Real.log L := by
    rw [Real.log_mul hρ.ne' (by positivity), Real.log_pow]
  have h3 : Real.log (2 ^ 12 * w) = 12 * Real.log 2 + Real.log w := by
    rw [Real.log_mul (by positivity) (by positivity), Real.log_pow]
    norm_num
  have hlp : -Real.log ρ ≤ TorusBound.logPos (1 / ρ) := by
    unfold TorusBound.logPos
    rw [one_div, Real.log_inv]
    exact le_max_left _ _
  have hlogv : Real.log v ≤ v / B + B := by
    have e : Real.log (v / B) = Real.log v - Real.log B := Real.log_div hv0.ne' hB0.ne'
    have a1 : Real.log (v / B) ≤ v / B - 1 := Real.log_le_sub_one_of_pos (by positivity)
    have a2 : Real.log B ≤ B - 1 := Real.log_le_sub_one_of_pos hB0
    linarith
  have hnL : (n : ℝ) ≤ n * Real.log L := by nlinarith
  have hn : (n : ℝ) ≤ 12 + (1 / 100) * (v / B + B) + TorusBound.logPos (1 / ρ) := by
    rw [h2, h3, hlogw] at h1
    linarith
  have hBv : B * (v / B) = v := by field_simp
  have hm := mul_le_mul_of_nonneg_left hn (by linarith : (0 : ℝ) ≤ 2 * B)
  have hexp : 2 * B * (12 + (1 / 100) * (v / B + B) + TorusBound.logPos (1 / ρ)) =
      24 * B + (1 / 50) * (B * (v / B)) + (1 / 50) * B ^ 2 +
        2 * B * TorusBound.logPos (1 / ρ) := by ring
  rw [hexp, hBv] at hm
  have hlp0 : 0 ≤ TorusBound.logPos (1 / ρ) := by
    unfold TorusBound.logPos
    exact le_max_right _ _
  have hBlp : 0 ≤ B * TorusBound.logPos (1 / ρ) := mul_nonneg hB0.le hlp0
  have hB2 : 0 ≤ B ^ 2 := sq_nonneg B
  linarith
private theorem levelSpacing_mul_pow {L K t n : ℕ} (hL : (L : ℝ) ≠ 0) (h : t + n = K) :
    levelSpacing L K t * (L : ℝ) ^ n = 1 := by
  unfold levelSpacing
  rw [← zpow_natCast, ← zpow_add₀ hL]
  have : ((t : ℤ) - (K : ℤ)) + (n : ℤ) = 0 := by omega
  rw [this, zpow_zero]
private theorem lt_of_not_fitsAtLevel {p : StepParameters} {β ρ : ℝ} {K t n : ℕ} (hL : 3 ≤ p.side)
    (h : t + n = K) (hf : ¬ FitsAtLevel p β K ρ t) :
    ρ * (p.side : ℝ) ^ n < 2 ^ 11 * (clusterRange (couplingFlow p β t).1 : ℝ) := by
  have hL0 : (0 : ℝ) < p.side := by
    have : 0 < p.side := by omega
    exact_mod_cast this
  have hlt : 2 ^ 11 * rangeAtLevel p β t * levelSpacing p.side K t > ρ := not_le.mp hf
  have hp : (0 : ℝ) < (p.side : ℝ) ^ n := by positivity
  have := mul_lt_mul_of_pos_right hlt hp
  have e : 2 ^ 11 * rangeAtLevel p β t * levelSpacing p.side K t * (p.side : ℝ) ^ n =
      2 ^ 11 * (clusterRange (couplingFlow p β t).1 : ℝ) := by
    rw [mul_assoc, levelSpacing_mul_pow hL0.ne' h, mul_one]
    rfl
  rw [e] at this
  exact this
private theorem radiusLevel_eq_some {p : StepParameters} {β ρ : ℝ} {K s : ℕ}
    (h : radiusLevel p β K ρ = some s) :
    s ≤ K ∧ (s < K → ¬ FitsAtLevel p β K ρ (s + 1)) := by
  classical
  unfold radiusLevel at h
  split_ifs at h with hex
  obtain rfl := Option.some.inj h
  exact ⟨Nat.findGreatest_le K, fun hlt => Nat.findGreatest_is_greatest (Nat.lt_succ_self _) hlt⟩
private theorem radiusLevel_eq_none {p : StepParameters} {β ρ : ℝ} {K : ℕ}
    (h : radiusLevel p β K ρ = none) :
    ¬ FitsAtLevel p β K ρ 0 := by
  classical
  unfold radiusLevel at h
  split_ifs at h with hex
  exact fun hf => hex ⟨0, Nat.zero_le K, hf⟩
private theorem coupling_bound_of_params {p : StepParameters} (hL : 3 ≤ p.side) (hB : 1 ≤ p.B)
    (hy : 1 ≤ p.y₁) (hret : ExpansionReturnsAt p)
    (hw : ∀ β : ℝ, p.y₁ ≤ β → HasExpansion p 0 β (wilsonWeight β)) {Ξ : ℝ} (hΞ : 0 ≤ Ξ)
    {β : ℝ} {K : ℕ} {ρ : ℝ} (hd : IsAdmissibleFlow p Ξ β K) (hρ : 0 < ρ) :
    (∀ s : ℕ, radiusLevel p β K ρ = some s → (couplingFlow p β s).1 ≤
      (2 * Ξ + 52 * p.B + p.B ^ 2) * (1 + TorusBound.logPos (1 / ρ))) ∧
    (radiusLevel p β K ρ = none → β ≤
      (2 * Ξ + 52 * p.B + p.B ^ 2) * (1 + TorusBound.logPos (1 / ρ))) := by
  set lp := TorusBound.logPos (1 / ρ) with hlp
  have hlp0 : 0 ≤ lp := by
    rw [hlp]
    unfold TorusBound.logPos
    exact le_max_right _ _
  have hB2 : 0 ≤ p.B ^ 2 := sq_nonneg _
  have hBlp : 0 ≤ p.B * lp := mul_nonneg (by linarith) hlp0
  have hB2lp : 0 ≤ p.B ^ 2 * lp := mul_nonneg hB2 hlp0
  have hΞlp : 0 ≤ Ξ * lp := mul_nonneg hΞ hlp0
  have hrem := couplingFlow_le_of_remaining hret hw hd
  have hmis : ∀ t n : ℕ, t + n = K → ¬ FitsAtLevel p β K ρ t →
      (couplingFlow p β t).1 ≤ 2 * Ξ + 48 * p.B + p.B ^ 2 + 4 * p.B * lp := fun t n h hf =>
    coupling_le_of_not_fits hL hB hΞ (hy.trans (hd.coupling_ge t (by omega))) hρ
      (lt_of_not_fitsAtLevel hL h hf) (hrem n t h)
  refine ⟨fun s hs => ?_, fun hs => ?_⟩
  · obtain ⟨hsK, hnot⟩ := radiusLevel_eq_some hs
    rcases hsK.lt_or_eq with hlt | rfl
    · have h1 := hmis (s + 1) (K - (s + 1)) (by omega) (hnot hlt)
      have h0 : HasExpansion p 0 β (wilsonWeight β) := hw β (hd.coupling_ge 0 (Nat.zero_le K))
      have hexp := hasExpansion_couplingFlow hret h0 s fun j hj => hd.coupling_ge j (by omega)
      have hstep := (expansionCoupling_of_returns hret (hd.coupling_ge s (by omega)) hexp).2
      have hle : (couplingFlow p β s).1 - (couplingFlow p β (s + 1)).1 ≤ 2 * p.B := by
        have := (abs_le.mp hstep).1
        change -(2 * p.B) ≤ (couplingFlow p β (s + 1)).1 - (couplingFlow p β s).1 at this
        linarith
      nlinarith
    · have := hd.coupling_le
      nlinarith
  · have h1 := hmis 0 K (by omega) (radiusLevel_eq_none hs)
    have e : (couplingFlow p β 0).1 = β := rfl
    rw [e] at h1
    nlinarith
theorem couplingAtRadiusLevel : couplingAtRadiusLevelStatement := by
  unfold couplingAtRadiusLevelStatement HoldsOnParameterFamilies
  intro a _
  refine ⟨3, fun _ => 1, 0, fun _ => one_pos, ?_⟩
  intro L _ hL3 T _ hTL hT _ _ _ _
  refine ⟨1, fun y hy hret hw Ξ hΞ => ?_⟩
  have hB : 1 ≤ T.B := hT.B_ge
  have hΞ0 : 0 ≤ Ξ := by linarith
  refine ⟨2 * Ξ + 52 * T.B + T.B ^ 2, by positivity, fun β K ρ hd hρ => ?_⟩
  exact coupling_bound_of_params (p := T.stepParameters y) (by change 3 ≤ T.side; omega) hB hy hret hw hΞ0 hd hρ
end YangMills.Construction.SmallTorusCopies
end
