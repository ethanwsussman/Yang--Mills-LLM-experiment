import YangMills.Construction.LawByMomentsOfTheFlow.AStateForgetsAFieldTurnedOnABox
import YangMills.Construction.LawByMomentsOfTheFlow.GoodStateForgets
import YangMills.Construction.LawByMomentsOfTheFlow.TheCutOfAGoodState
import YangMills.Construction.LawByMomentsOfTheFlow.WindowOfTheScale
import YangMills.Construction.ResponseInTheExpansion.MassAlongTheLevelsProof
import YangMills.Construction.ResponseInTheExpansion.OneStepIsTheLawOfTheMirrorProof
import Mathlib
set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
noncomputable section
open MeasureTheory ProbabilityTheory Filter
namespace YangMills.Construction.MomentLaw
open TorusFields TorusLumps TorusBlocks TorusCounting RenormalizationStepParameters StepSettings StepFloors ResponseInTheExpansion WeightedResponses
  ColdStepAtMirrorFrames ClusterExpansionOfAStep
namespace MeanForgetting
private theorem card_blocksNearFreeCores_supBall_le {n L : ℕ} [NeZero n] [NeZero L] (hL : Odd L) (r m : ℕ) (o : TorusSite n) :
    ((blocksNearFreeCores L r (supBall o m)).card : ℝ) ≤ (2 * ((m : ℝ) + 4 * r + 1) + 1) ^ 4 := by apply _root_.YangMills.SharedProofs.p55616 <;> assumption
private theorem two_errors_le {B rt ch x c : ℝ} {m r m₀ : ℕ} {card : ℝ} (hB : 0 ≤ B) (hc1 : c ≤ 1) (hc0 : 0 < c) (hct : c ≤ rt / 16)
    (hm : 4096 * r ≤ m) (hr : 1 ≤ r) (hm₀ : m₀ ≤ r) (hcard : card ≤ (2 * ((m : ℝ) + 4 * r + 1) + 1) ^ 4)
    (hx : 33 * (m : ℝ) ≤ 7 * ch * x) :
    2 * B * Real.exp (-(rt * ((m - m₀ - 1 : ℕ) : ℝ) / 2 ^ 3)) + 2 * B * card * Real.exp (-(7 * ch * x)) ≤
      4 * B * Real.exp (-(c * (m : ℝ))) := by apply _root_.YangMills.SharedProofs.p79174 <;> assumption
private theorem gasRate_pos {T : ParameterAssignment} (hT : T.Admissible) : 0 < T.gasRate := by apply _root_.YangMills.Construction.StepFloors.gasRate_pos <;> assumption
private theorem isWellPosed_of_onParameters {T : ParameterAssignment} (hT : T.Admissible) {y : ℝ} (hy₀ : T.floorMin ≤ y) (hy₁ : 1 ≤ y)
    {R : StepSetup} (hon : R.OnParameters T y) (hmoved : |R.nextCoupling - R.coupling| ≤ 2 * T.B) (hArr : R.IsSymmetricWeight)
    (hF : T.FloorConditions (2 ^ 40 * T.side + 4 * T.n₀ + 2 ^ 17) 1 R.coupling) : R.IsWellPosed := by apply _root_.YangMills.SharedProofs.p3707 <;> assumption
private theorem isHullState_of_weight_pos (hHull : CoarseHullIsHullState) {R : StepSetup} (hS : R.IsWellPosed) {n : ℕ} [NeZero n]
    (hL : R.params.side ∣ n) (V : TorusField n) (q : CoarseState R n)
    (hpos : 0 < coarseStateWeight R (hotCoreSites R V) V q) : IsHullState R.params R.nextRange V q.1 := by
  classical
  by_contra hc
  have h0 : coarseStateMass R (hotCoreSites R V) V q = 0 := by
    unfold coarseStateMass
    refine Finset.sum_eq_zero fun bad _ => Finset.sum_eq_zero fun Yt _ => Finset.sum_eq_zero fun b _ => ?_
    have hz : ∀ (W : TorusField (n * R.params.side)) (ν : q.unlabelled Yt → R.labels.Ω),
        (if IsHullState R.params R.range (q.fieldWithStoredLinks W) Yt ∧
            coarseStateOf R (hotCoreSites R V) (q.fieldWithStoredLinks W) Yt (q.fillLabels Yt ν) bad b = q then
          ENNReal.ofReal (stepWeight R (hotCoreSites R V) V (q.fieldWithStoredLinks W) Yt (q.fillLabels Yt ν) bad b) else 0) = 0 := by
      intro W ν
      refine if_neg fun h => hc ?_
      have e : q.1 = coarseHull R.params.side R.range R.nextRange _ _ _ := (congrArg Sigma.fst h.2).symm
      rw [e]
      exact hHull R.params hS.admissible R.range R.nextRange hS.range_le hS.nextRange_ge n hL V bad Yt
    simp only [hz]
    simp
  have : coarseStateWeight R (hotCoreSites R V) V q = 0 := by
    unfold coarseStateWeight
    rw [h0]
    rfl
  linarith
private theorem eventually_window_numbers (c ch C σ Y : ℝ) (hc : 0 < c) (hch : 0 < ch) (hσ : 0 < σ) :
    ∃ X : ℝ, ∀ x, X ≤ x → 1 ≤ x ∧ C * Real.log x ≤ x / 2 ∧ (2 : ℝ) ^ 13 ≤ x ^ ((1 : ℝ) / 100) ∧
      33 * (4 * x ^ ((1 : ℝ) / 50)) ≤ 7 * ch * (x / 2) ∧ x ^ ((1 : ℝ) / 200) + 3 ≤ c * x ^ ((1 : ℝ) / 50) ∧
      32 * x ^ ((1 : ℝ) / 50) ≤ x ^ 4 ∧ 64 * x ^ (-(1 / 4) : ℝ) < σ ∧ Y ≤ x / 2 := by
  set W : ℝ := max (max (max (2 ^ 13) 32) (1 + 4 / c)) (max (1 + 132 / (7 * ch / 2)) (1 + 65 / σ)) with hW
  have hw : Tendsto (fun x : ℝ => x ^ ((1 : ℝ) / 200)) atTop atTop := tendsto_rpow_atTop (by norm_num)
  have e1 := hw.eventually_ge_atTop W
  have e2 := Real.isLittleO_log_id_atTop.bound (show (0 : ℝ) < 1 / (2 * (|C| + 1)) by positivity)
  have e3 := eventually_ge_atTop (max 1 (2 * Y))
  obtain ⟨X, hX⟩ := eventually_atTop.mp ((e1.and e2).and e3)
  refine ⟨X, fun x hx => ?_⟩
  obtain ⟨⟨h1, h2⟩, h3⟩ := hX x hx
  have hx1 : 1 ≤ x := (le_max_left _ _).trans h3
  have hY : Y ≤ x / 2 := by
    have := (le_max_right _ _).trans h3
    linarith
  have hx0 : 0 ≤ x := by linarith
  set w : ℝ := x ^ ((1 : ℝ) / 200) with hwd
  have hp : ∀ k : ℕ, w ^ k = x ^ ((k : ℝ) / 200) := fun k => by
    rw [hwd, ← Real.rpow_natCast, ← Real.rpow_mul hx0]
    congr 1
    ring
  have hW1 : (2 : ℝ) ^ 13 ≤ w := ((le_max_left _ _).trans ((le_max_left _ _).trans (le_max_left _ _))).trans h1
  have hW2 : (32 : ℝ) ≤ w := ((le_max_right _ _).trans ((le_max_left _ _).trans (le_max_left _ _))).trans h1
  have hW3 : 1 + 4 / c ≤ w := ((le_max_right _ _).trans (le_max_left _ _)).trans h1
  have hW4 : 1 + 132 / (7 * ch / 2) ≤ w := ((le_max_left _ _).trans (le_max_right _ _)).trans h1
  have hW5 : 1 + 65 / σ ≤ w := ((le_max_right _ _).trans (le_max_right _ _)).trans h1
  have hw1 : 1 ≤ w := by linarith [hW2]
  have p2 : x ^ ((1 : ℝ) / 100) = w ^ 2 := by
    rw [hp 2]
    congr 1
    norm_num
  have p4 : x ^ ((1 : ℝ) / 50) = w ^ 4 := by
    rw [hp 4]
    congr 1
    norm_num
  have p200 : x = w ^ 200 := by
    rw [hp 200]
    norm_num
  have hle : ∀ {a b : ℕ}, a ≤ b → w ^ a ≤ w ^ b := fun h => pow_le_pow_right₀ hw1 h
  refine ⟨hx1, ?_, ?_, ?_, ?_, ?_, ?_, hY⟩
  · have h4 : ‖Real.log x‖ ≤ 1 / (2 * (|C| + 1)) * ‖id x‖ := h2
    rw [Real.norm_eq_abs, id, Real.norm_eq_abs, abs_of_nonneg hx0] at h4
    have h5 : C * Real.log x ≤ |C| * |Real.log x| := by
      rw [← abs_mul]
      exact le_abs_self _
    have h6 : (|C| + 1) * |Real.log x| ≤ x / 2 := by
      have h7 := mul_le_mul_of_nonneg_left h4 (show 0 ≤ |C| + 1 by positivity)
      have e : (|C| + 1) * (1 / (2 * (|C| + 1)) * x) = x / 2 := by
        field_simp
      linarith
    nlinarith [abs_nonneg (Real.log x)]
  · rw [p2]
    have : w ≤ w ^ 2 := by nlinarith
    linarith
  · rw [p4]
    have h1' : 132 / (7 * ch / 2) ≤ w := by linarith
    have hk : 0 < 7 * ch / 2 := by positivity
    have h2' : 132 ≤ w * (7 * ch / 2) := by
      rwa [div_le_iff₀ hk] at h1'
    have h3' : w ^ 5 ≤ x := by
      rw [p200]
      exact hle (by norm_num)
    have h4' : 132 * w ^ 4 ≤ (7 * ch / 2) * w ^ 5 := by
      have : 0 ≤ w ^ 4 := by positivity
      nlinarith
    have h5' : (7 * ch / 2) * w ^ 5 ≤ (7 * ch / 2) * x := mul_le_mul_of_nonneg_left h3' hk.le
    linarith
  · rw [p4]
    have h1' : 4 / c ≤ w := by linarith
    have h2' : 4 ≤ w * c := by
      rwa [div_le_iff₀ hc] at h1'
    have h3' : w ≤ w ^ 3 := by
      have := hle (show 1 ≤ 3 by norm_num)
      simpa using this
    have h4' : 4 * w ^ 3 ≤ c * w ^ 4 := by
      have : 0 ≤ w ^ 3 := by positivity
      nlinarith
    linarith
  · rw [p4]
    have e : x ^ 4 = w ^ 800 := by
      rw [p200, ← pow_mul]
    rw [e]
    have h3' : w ^ 5 ≤ w ^ 800 := hle (by norm_num)
    have h4' : 32 * w ^ 4 ≤ w ^ 5 := by
      have : 0 ≤ w ^ 4 := by positivity
      nlinarith
    linarith
  · have e : x ^ (-(1 / 4) : ℝ) = (w ^ 50)⁻¹ := by
      rw [hp 50, ← Real.rpow_neg hx0]
      congr 1
      norm_num
    rw [e]
    have h1' : 65 / σ ≤ w := by linarith
    have h2' : 65 ≤ w * σ := by
      rwa [div_le_iff₀ hσ] at h1'
    have h3' : w ≤ w ^ 50 := by
      have := hle (show 1 ≤ 50 by norm_num)
      simpa using this
    have h4' : 0 < w ^ 50 := by positivity
    rw [← div_eq_mul_inv, div_lt_iff₀ h4']
    nlinarith
private theorem supDist_originSite_fineSite_le {Λ : MomentParameters} (S : MomentPoint Λ) (u n : ℕ) [NeZero n]
    (hL : 1 ≤ Λ.stepParams.side) :
    TorusFields.supDist (S.originSite u (n * Λ.stepParams.side)) (fineSite Λ.stepParams.side (S.originSite (u + 1) n) 0 0) ≤ Λ.stepParams.side := by
  classical
  set L := Λ.stepParams.side with hLd
  have : NeZero L := ⟨by omega⟩
  have : NeZero (n * L) := ⟨mul_ne_zero (NeZero.ne n) (NeZero.ne L)⟩
  have hLr : (1 : ℝ) ≤ L := by exact_mod_cast hL
  have hL0 : (L : ℝ) ≠ 0 := by linarith
  set ρ₀ : Fin 4 → ℤ := fun a => round (S.data.center a * (L : ℝ) ^ S.data.windowLevel / (L : ℝ) ^ u) with hρ₀
  set ρ₁ : Fin 4 → ℤ := fun a => round (S.data.center a * (L : ℝ) ^ S.data.windowLevel / (L : ℝ) ^ (u + 1)) with hρ₁
  set h : Fin 4 → ℤ := fun a => ρ₀ a - (L : ℤ) * ρ₁ a with hh
  have hb : ∀ a, (h a).natAbs ≤ L := by
    intro a
    set t₁ : ℝ := S.data.center a * (L : ℝ) ^ S.data.windowLevel / (L : ℝ) ^ (u + 1) with ht₁
    have e0 : S.data.center a * (L : ℝ) ^ S.data.windowLevel / (L : ℝ) ^ u = L * t₁ := by
      rw [ht₁, pow_succ]
      field_simp
    have b0 : |L * t₁ - (ρ₀ a : ℝ)| ≤ 1 / 2 := by
      rw [← e0]
      exact abs_sub_round _
    have b1 : |t₁ - (ρ₁ a : ℝ)| ≤ 1 / 2 := abs_sub_round _
    have b2 := abs_le.mp b0
    have b3 := abs_le.mp b1
    have hr : |((h a : ℤ) : ℝ)| ≤ L := by
      have e : ((h a : ℤ) : ℝ) = (ρ₀ a : ℝ) - L * (ρ₁ a : ℝ) := by
        simp only [hh]
        push_cast
        ring
      rw [e, abs_le]
      constructor <;> nlinarith
    have hz : |h a| ≤ (L : ℤ) := by exact_mod_cast hr
    rw [Int.abs_eq_natAbs] at hz
    exact_mod_cast hz
  have e : S.originSite u (n * L) = fineSite L (S.originSite (u + 1) n) 0 0 + siteOfInt h := by
    funext a
    have hc : ((((S.originSite (u + 1) n a).cast : ℤ)) : ZMod n) = ((ρ₁ a : ℤ) : ZMod n) := by
      rw [ZMod.intCast_zmod_cast]
      rfl
    obtain ⟨w, hw⟩ := (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).mp hc
    have e2 : (((L : ℤ) * (((S.originSite (u + 1) n a).cast : ℤ) + (0 : Fin 4 → ℤ) a) + (0 : Fin 4 → ℤ) a + h a : ℤ) : ZMod (n * L)) =
        ((ρ₀ a : ℤ) : ZMod (n * L)) := by
      refine (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).mpr ⟨w, ?_⟩
      simp only [hh, Pi.zero_apply]
      push_cast
      linear_combination (L : ℤ) * hw
    show ((ρ₀ a : ℤ) : ZMod (n * L)) = _
    rw [← e2]
    simp [fineSite, siteOfInt]
  rw [e, supDist_comm]
  exact supDist_add_siteOfInt_le _ h L hb
private theorem room_in_block {L m : ℕ} (hL : 2 ^ 40 ≤ L) (hm : 2 ^ 26 ≤ m) : 8 * m + L + 1 + L ≤ L * (m / 8) := by
  obtain ⟨a, rfl⟩ := Nat.exists_eq_add_of_le hL
  have h1 : 8 * (m / 8) ≤ m := Nat.mul_div_le m 8
  have h2 : m < 8 * (m / 8) + 8 := by omega
  obtain ⟨b, hb⟩ : ∃ b, m / 8 = 3 + b := ⟨m / 8 - 3, by omega⟩
  rw [hb] at h1 h2 ⊢
  nlinarith [Nat.zero_le (a * b)]
private theorem clusterRange_bounds {x y : ℝ} (hx : 0 ≤ x) (hy0 : 0 ≤ y) (hy : y ≤ 2 * x) (h13 : (2 : ℝ) ^ 13 ≤ x ^ ((1 : ℝ) / 100)) :
    2 ^ 13 ≤ clusterRange x ∧ clusterRange y ≤ 2 * clusterRange x ∧ x ^ ((1 : ℝ) / 50) ≤ ((clusterRange x ^ 2 : ℕ) : ℝ) ∧
      ((clusterRange x ^ 2 : ℕ) : ℝ) ≤ 4 * x ^ ((1 : ℝ) / 50) ∧ 2 ^ 12 * clusterRange y ≤ clusterRange x ^ 2 := by
  have hp : 0 ≤ x ^ ((1 : ℝ) / 100) := by positivity
  have hrge : x ^ ((1 : ℝ) / 100) ≤ (clusterRange x : ℝ) := Nat.le_ceil _
  have hrle : (clusterRange x : ℝ) ≤ x ^ ((1 : ℝ) / 100) + 1 := (Nat.ceil_lt_add_one hp).le
  have hr13 : 2 ^ 13 ≤ clusterRange x := by
    have : (2 : ℝ) ^ 13 ≤ (clusterRange x : ℝ) := h13.trans hrge
    exact_mod_cast this
  have hyr : clusterRange y ≤ 2 * clusterRange x := by
    refine Nat.ceil_le.mpr ?_
    have h1 : y ^ ((1 : ℝ) / 100) ≤ (2 * x) ^ ((1 : ℝ) / 100) := Real.rpow_le_rpow hy0 hy (by norm_num)
    have h2 : (2 * x) ^ ((1 : ℝ) / 100) = 2 ^ ((1 : ℝ) / 100) * x ^ ((1 : ℝ) / 100) := Real.mul_rpow (by norm_num) hx
    have h3 : (2 : ℝ) ^ ((1 : ℝ) / 100) ≤ 2 ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
    rw [Real.rpow_one] at h3
    push_cast
    rw [h2] at h1
    have h4 := mul_le_mul_of_nonneg_right h3 hp
    linarith
  have e : x ^ ((1 : ℝ) / 50) = (x ^ ((1 : ℝ) / 100)) ^ 2 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hx]
    norm_num
  refine ⟨hr13, hyr, ?_, ?_, ?_⟩
  · rw [e]
    push_cast
    exact pow_le_pow_left₀ hp hrge 2
  · rw [e]
    push_cast
    have h1 : (1 : ℝ) ≤ x ^ ((1 : ℝ) / 100) := by
      have : (1 : ℝ) ≤ 2 ^ 13 := by norm_num
      linarith
    have hr2 : (clusterRange x : ℝ) ≤ 2 * x ^ ((1 : ℝ) / 100) := by linarith
    have h2 := pow_le_pow_left₀ (Nat.cast_nonneg (clusterRange x)) hr2 2
    rw [mul_pow] at h2
    linarith
  · have h1 : 2 ^ 12 * clusterRange y ≤ 2 ^ 12 * (2 * clusterRange x) := Nat.mul_le_mul_left _ hyr
    have h2 : 2 ^ 13 * clusterRange x ≤ clusterRange x * clusterRange x := Nat.mul_le_mul_right _ hr13
    rw [sq]
    omega
private theorem pow_four_le_of_window {L N : ℕ} {x : ℝ} (hL : 1 ≤ L) (hx : 1 ≤ x) (hh : (L : ℝ) ^ (-(N : ℝ) / 4) ≤ x⁻¹) :
    x ^ 4 ≤ ((L ^ N : ℕ) : ℝ) := by
  have hL0 : (0 : ℝ) < L := by exact_mod_cast hL
  set p : ℝ := (L : ℝ) ^ ((N : ℝ) / 4) with hp
  have hp0 : 0 < p := Real.rpow_pos_of_pos hL0 _
  have e1 : (L : ℝ) ^ (-(N : ℝ) / 4) = p⁻¹ := by
    rw [hp, ← Real.rpow_neg hL0.le]
    congr 1
    ring
  rw [e1] at hh
  have hx0 : (0 : ℝ) < x := by linarith
  have h1 : x ≤ p := (inv_le_inv₀ hp0 hx0).mp hh
  have h2 : p ^ 4 = ((L ^ N : ℕ) : ℝ) := by
    rw [hp, ← Real.rpow_natCast, ← Real.rpow_mul hL0.le]
    push_cast
    rw [show (N : ℝ) / 4 * 4 = (N : ℝ) by ring, Real.rpow_natCast]
  rw [← h2]
  exact pow_le_pow_left₀ hx0.le h1 4
private theorem error_sum_le {M E E' card c m w : ℝ} (hM : 0 ≤ M) (hcard : 0 ≤ card)
    (he : 2 * M * E + 2 * M * card * E' ≤ 4 * M * Real.exp (-(c * m))) (hw : w + 3 ≤ c * m) (hE' : 0 ≤ E') :
    4 * M * E + 2 * M * card * E' ≤ M * Real.exp (-w) := by
  have h1 : 0 ≤ 2 * M * card * E' := by positivity
  have h2 : Real.exp (-(c * m)) ≤ Real.exp (-w) * Real.exp (-3) := by
    rw [← Real.exp_add]
    exact Real.exp_le_exp.mpr (by linarith)
  have h3 : Real.exp (-3) ≤ 1 / 8 := by
    rw [Real.exp_neg, one_div]
    refine inv_anti₀ (by norm_num) ?_
    have h4 : (2 : ℝ) ≤ Real.exp 1 := by
      have := Real.add_one_le_exp (1 : ℝ)
      linarith
    have h5 := pow_le_pow_left₀ (by norm_num) h4 3
    rw [← Real.exp_nat_mul] at h5
    norm_num at h5
    linarith
  have h6 : 0 ≤ Real.exp (-w) := (Real.exp_pos _).le
  have h7 : Real.exp (-(c * m)) ≤ Real.exp (-w) / 8 := by
    have := mul_le_mul_of_nonneg_left h3 h6
    linarith
  have h8 := mul_le_mul_of_nonneg_left h7 hM
  nlinarith
end MeanForgetting
set_option maxHeartbeats 2000000 in
open MeanForgetting in
theorem goodStateMeanForgets (hA : forgetsRotatedFieldStatement) (hCut : goodConfigCutoffStatement)
    (hWin : scaleWindowStatement) (hFl : EventuallyFloorConditions) (hHull : CoarseHullIsHullState)
    (hZ : CoarseWeightZeroOfFactorZero) : goodStateMeanForgetsStatement := by
  classical
  intro a ha
  obtain ⟨L₁, r₁, C₁, hr₁, H₁⟩ := hCut a ha
  obtain ⟨L₂, r₂, C₂, hr₂, H₂⟩ := hWin a ha
  obtain ⟨r₃, hr₃, H₃⟩ := hA
  refine ⟨max L₁ L₂, fun c => min (min (r₁ c) (r₂ c)) (r₃ c), max C₁ C₂,
    fun c => lt_min (lt_min (hr₁ c) (hr₂ c)) (hr₃ c), fun L hL hLL Tb e1 e2 hD hC hO hrt hCd Kr hKr => ?_⟩
  have t1 := hrt.trans ((min_le_left _ _).trans (min_le_left _ _))
  have t2 := hrt.trans ((min_le_left _ _).trans (min_le_right _ _))
  have t3 := hrt.trans (min_le_right _ _)
  obtain ⟨y₁, G₁⟩ := H₁ L hL ((le_max_left _ _).trans hLL) Tb e1 e2 hD hC hO t1 ((le_max_left _ _).trans hCd) Kr hKr
  obtain ⟨y₂, G₂⟩ := H₂ L hL ((le_max_right _ _).trans hLL) Tb e1 e2 hD hC hO t2 ((le_max_right _ _).trans hCd) Kr hKr
  obtain ⟨y₃, G₃⟩ := H₃ Tb hD hC hO t3
  refine ⟨max (max y₁ y₂) (max y₃ (max Tb.floorMin 1)), fun y hy => ?_⟩
  intro hret hW g hg hyg k _ hk2 hk8 Rd d hd
  have hy1 : y₁ ≤ y := ((le_max_left _ _).trans (le_max_left _ _)).trans hy
  have hy2 : y₂ ≤ y := ((le_max_right _ _).trans (le_max_left _ _)).trans hy
  have hy3 : y₃ ≤ y := ((le_max_left _ _).trans (le_max_right _ _)).trans hy
  have hy4 : Tb.floorMin ≤ y := ((le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))).trans hy
  have hy5 : 1 ≤ y := ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))).trans hy
  obtain ⟨C₁', c₁, X₁, hc₁, hX₁, Q₁⟩ := G₁ y hy1 hret hW g hg hyg k hk2 hk8 Rd d hd
  obtain ⟨C₂', c₂, X₂, hc₂, hX₂, Q₂⟩ := G₂ y hy2 hret hW g hg hyg k hk2 hk8 Rd d hd
  have hfit : (Tb.stepParameters y).Admissible := hD.fits y hy4
  obtain ⟨yF, hyF⟩ := hFl Tb hD (2 ^ 40 * Tb.side + 4 * Tb.n₀ + 2 ^ 17) 1 (by positivity) one_pos
  have hrtpos := hD.rt_pos
  have hchpos := _root_.YangMills.Construction.MomentLaw.MeanForgetting.gasRate_pos hD
  obtain ⟨X₃, hX₃⟩ := eventually_window_numbers (min (Tb.rt / 16) 1) Tb.gasRate (C₂' 0) Tb.threshold (max yF (200 * Tb.B))
    (lt_min (by positivity) one_pos) hchpos hD.σ_pos
  refine ⟨fun _ => 0, 1, max (max X₁ X₂) (max X₃ y), one_pos, (le_max_right _ _).trans (le_max_right _ _), fun S => ?_⟩
  intro hX dd n _ hdd hn V Y ω hgood hpos f M hbd hbor hgau hloc
  have hxX₁ : X₁ ≤ S.scaleCoupling := ((le_max_left _ _).trans (le_max_left _ _)).trans hX
  have hxX₂ : X₂ ≤ S.scaleCoupling := ((le_max_right _ _).trans (le_max_left _ _)).trans hX
  have hxX₃ : X₃ ≤ S.scaleCoupling := ((le_max_left _ _).trans (le_max_right _ _)).trans hX
  obtain ⟨hl1, hl2, hl3, hl4, hl5, hK, hw⟩ := Q₂ S hxX₂
  obtain ⟨hx1, hlog, hr13, h33, hexp, h32, h64, hYx⟩ := hX₃ S.scaleCoupling hxX₃
  have hu0 : S.lastSeparated + dd + 1 ≤ S.data.windowLevel := by omega
  have hstand : StageOnFlow Tb Kr y S.β (S.lastSeparated + dd)
      ⟨S.tower.stage (S.lastSeparated + dd), S.resp (S.lastSeparated + dd)⟩ := by
    have h : StageOnFlow Tb Kr y S.β (S.lastSeparated + dd)
        (flowStages Tb y S.β S.labelFacts S.initial (S.lastSeparated + dd)) := S.onFlow _ (by omega)
    have e : (⟨S.tower.stage (S.lastSeparated + dd), S.resp (S.lastSeparated + dd)⟩ : StageWithResponse (Tb.stepParameters y)) =
        flowStages Tb y S.β S.labelFacts S.initial (S.lastSeparated + dd) :=
      S.stage_eq _ (by omega)
    rw [← e] at h
    exact h
  have hon : (S.tower.stage (S.lastSeparated + dd)).toStepSetup.OnParameters Tb y := hstand.onFamily.onFamily
  have hmv : |(S.tower.stage (S.lastSeparated + dd)).toStepSetup.nextCoupling - (S.tower.stage (S.lastSeparated + dd)).toStepSetup.coupling|
      ≤ 2 * Tb.B := hstand.onFamily.abs_sub_le
  have hRx : (S.tower.stage (S.lastSeparated + dd)).toStepSetup.coupling = S.coupling (S.lastSeparated + dd) := hstand.coupling_eq
  have hwu := (hw (S.lastSeparated + dd) (by omega) (by omega)).1
  have hwu1 := (hw (S.lastSeparated + dd + 1) (by omega) (by omega)).2
  have hYF : yF ≤ S.scaleCoupling / 2 := (le_max_left _ _).trans hYx
  have hYB : 200 * Tb.B ≤ S.scaleCoupling / 2 := (le_max_right _ _).trans hYx
  have hRlo : S.scaleCoupling / 2 ≤ (S.tower.stage (S.lastSeparated + dd)).toStepSetup.coupling := by
    rw [hRx]
    have := (abs_le.mp hwu).1
    linarith
  have hRhi : (S.tower.stage (S.lastSeparated + dd)).toStepSetup.coupling ≤ 2 * S.scaleCoupling := by
    rw [hRx]
    have := (abs_le.mp hwu).2
    linarith
  have hF : (S.tower.stage (S.lastSeparated + dd)).toStepSetup.IsWellPosed :=
    isWellPosed_of_onParameters hD hy4 hy5 hon hmv hstand.isSymmetricWeight (hyF _ (hYF.trans hRlo))
  have hxx : (S.tower.stage (S.lastSeparated + dd)).toStepSetup.nextCoupling ≤ 1.01 * (S.tower.stage (S.lastSeparated + dd)).toStepSetup.coupling := by
    have := (abs_le.mp hmv).2
    have h2 : 2 * Tb.B ≤ 0.01 * (S.tower.stage (S.lastSeparated + dd)).toStepSetup.coupling := by linarith
    linarith
  have hx0 : (0 : ℝ) ≤ S.scaleCoupling := by linarith
  have hRx0 : 0 ≤ (S.tower.stage (S.lastSeparated + dd)).toStepSetup.coupling := by linarith
  have hLge : 2 ^ 40 ≤ (Tb.stepParameters y).side := hD.L_ge
  obtain ⟨hr13'', hRr', hmge', hmle', hrm'⟩ := clusterRange_bounds hx0 hRx0 hRhi hr13
  have hr13' : 2 ^ 13 ≤ S.range := hr13''
  have hRr : (S.tower.stage (S.lastSeparated + dd)).toStepSetup.range ≤ 2 * S.range := hRr'
  have hmge : S.scaleCoupling ^ ((1 : ℝ) / 50) ≤ (S.rangeSq : ℝ) := hmge'
  have hmle : (S.rangeSq : ℝ) ≤ 4 * S.scaleCoupling ^ ((1 : ℝ) / 50) := hmle'
  have hrm : 2 ^ 12 * (S.tower.stage (S.lastSeparated + dd)).toStepSetup.range ≤ S.rangeSq := hrm'
  have hm_def : S.rangeSq = S.range ^ 2 := rfl
  have hmpos : 0 < S.rangeSq := by
    rw [hm_def]
    exact pow_pos (by have : S.range = clusterRange S.scaleCoupling := rfl; omega) 2
  have : NeZero (4 * S.rangeSq) := ⟨by omega⟩
  have hLN : S.scaleCoupling ^ 4 ≤ (((Tb.stepParameters y).side ^ S.logIndex : ℕ) : ℝ) := pow_four_le_of_window (by omega) hx1 hl1
  have hnside : (Tb.stepParameters y).side ^ S.logIndex ≤ n := by
    rw [hn]
    exact hwu1
  have hmn : 8 * S.rangeSq ≤ n := by
    have h1 : (8 * (S.rangeSq : ℝ)) ≤ ((n : ℕ) : ℝ) := by
      have h2 : (((Tb.stepParameters y).side ^ S.logIndex : ℕ) : ℝ) ≤ n := by exact_mod_cast hnside
      linarith
    exact_mod_cast h1
  have hb' : IsBlockTorusSide (S.tower.stage (S.lastSeparated + dd)).toStepSetup.params n := by
    have hK1 : 1 ≤ S.data.windowLevel - (S.lastSeparated + dd + 1) := by omega
    have hnd : n = S.data.period (Tb.stepParameters y).side * (Tb.stepParameters y).side ^ (S.data.windowLevel - (S.lastSeparated + dd + 1)) := hn
    have hside : (Tb.stepParameters y).side * (Tb.stepParameters y).n₀ ≤ S.data.period (Tb.stepParameters y).side := S.side_le
    have hpos1 : 1 ≤ (Tb.stepParameters y).side ^ (S.data.windowLevel - (S.lastSeparated + dd + 1)) := Nat.one_le_pow _ _ (by omega)
    refine ⟨?_, ?_⟩
    · show (Tb.stepParameters y).side ∣ n
      rw [hnd]
      exact Dvd.dvd.mul_left (dvd_pow_self _ (by omega)) _
    · show (Tb.stepParameters y).side * (Tb.stepParameters y).n₀ ≤ n
      rw [hnd]
      exact hside.trans (Nat.le_mul_of_pos_right _ (by omega))
  have hull := isHullState_of_weight_pos hHull hF hb'.1 V ⟨Y, ω⟩ hpos
  have hΦ : ∀ X ∈ chainComponents (S.tower.stage (S.lastSeparated + dd)).toStepSetup.nextRange Y,
      coarseFactor V (⟨Y, ω⟩ : CoarseState (S.tower.stage (S.lastSeparated + dd)).toStepSetup n) X ≠ 0 := fun X hX h0 =>
    hpos.ne' (hZ (S.tower.stage (S.lastSeparated + dd)).toStepSetup hF n hb' V ⟨Y, ω⟩ hull ⟨X, hX, h0⟩)
  have hdis : Disjoint Y (supBall (S.originSite (S.lastSeparated + dd + 1) n) S.rangeSq) := by
    refine Finset.disjoint_of_subset_right (fun z hz => ?_) hgood.disjoint_lumps
    obtain ⟨h1, h2⟩ := Finset.mem_filter.mp hz
    refine Finset.mem_filter.mpr ⟨h1, h2.trans ?_⟩
    have : (0 : ℝ) ≤ S.rangeSq := Nat.cast_nonneg _
    linarith
  obtain ⟨-, -, hcold3, g₀, hg₀⟩ := Q₁ S hxX₁ (S.lastSeparated + dd + 1) (by omega) (by omega) n hn V Y hgood
  have hUc : IsCold (S.tower.stage (S.lastSeparated + dd)).toStepSetup.params.threshold
      (S.smoothedField (S.lastSeparated + dd + 1) n V) := by
    intro z μ ν h
    have h1 := hcold3 1 zero_le_one le_rfl z μ ν h
    have h2 := hgood.curvature_le
    have h3 : curvature (S.smoothedField (S.lastSeparated + dd + 1) n V) z μ ν ≤
        64 * S.localCurvature (S.lastSeparated + dd + 1) n V := h1
    show _ < Tb.threshold
    linarith
  have hA' : ∀ z ∈ supBall (S.originSite (S.lastSeparated + dd) (n * (Tb.stepParameters y).side)) (8 * S.rangeSq),
      TorusFields.supDist z (fineSite (Tb.stepParameters y).side (S.originSite (S.lastSeparated + dd + 1) n) 0 0) + 1 + (Tb.stepParameters y).side
        ≤ (Tb.stepParameters y).side * (S.rangeSq / 8) := by
    intro z hz
    have h1 : TorusFields.supDist z (S.originSite (S.lastSeparated + dd) (n * (Tb.stepParameters y).side)) ≤ 8 * S.rangeSq := by
      have := (Finset.mem_filter.mp hz).2
      exact_mod_cast this
    have h2 := supDist_originSite_fineSite_le S (S.lastSeparated + dd) n (Λ := ⟨Tb, Kr, y, g, k, Rd, d⟩) (le_trans (by norm_num) hLge)
    have h3 := supDist_triangle z (S.originSite (S.lastSeparated + dd) (n * (Tb.stepParameters y).side))
      (fineSite (Tb.stepParameters y).side (S.originSite (S.lastSeparated + dd + 1) n) 0 0)
    have h4 : 2 ^ 26 ≤ S.rangeSq := by
      rw [hm_def]
      calc 2 ^ 26 = (2 ^ 13) ^ 2 := by norm_num
        _ ≤ S.range ^ 2 := Nat.pow_le_pow_left hr13' 2
    have h5 := room_in_block hLge h4
    have h6 : TorusFields.supDist (S.originSite (S.lastSeparated + dd) (n * (Tb.stepParameters y).side))
        (fineSite (Tb.stepParameters y).side (S.originSite (S.lastSeparated + dd + 1) n) 0 0) ≤ (Tb.stepParameters y).side := h2
    omega
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hbd (trivialField _) ∅)
  have hf : ReadsGaugeInvariantly (supBall (S.originSite (S.lastSeparated + dd) (n * (Tb.stepParameters y).side)) (8 * S.rangeSq)) M f :=
    ⟨hbd, hbor, hgau, hloc⟩
  have hmain := G₃ y hy3 (S.tower.stage (S.lastSeparated + dd)).toStepSetup hon hF hxx n S.rangeSq V
    (S.smoothedField (S.lastSeparated + dd + 1) n V) ⟨Y, ω⟩ (S.originSite (S.lastSeparated + dd + 1) n) g₀ hb' hull hΦ hrm hmn
    hdis hUc hg₀ _ M f hA' hf
  refine hmain.trans ?_
  have hrL : 1 ≤ (S.tower.stage (S.lastSeparated + dd)).toStepSetup.range := by
    have h := hF.range_ge_side
    have : 1 ≤ 2 ^ 40 * (S.tower.stage (S.lastSeparated + dd)).toStepSetup.params.side :=
      Nat.mul_pos (by positivity) (Nat.pos_of_ne_zero (NeZero.ne _))
    omega
  have hm₀r : (S.tower.stage (S.lastSeparated + dd)).toStepSetup.frameReach ≤ (S.tower.stage (S.lastSeparated + dd)).toStepSetup.range :=
    Nat.div_le_self _ _
  have hm4 : 4096 * (S.tower.stage (S.lastSeparated + dd)).toStepSetup.range ≤ S.rangeSq := by
    have : (2 : ℕ) ^ 12 = 4096 := by norm_num
    omega
  have hx33 : 33 * (S.rangeSq : ℝ) ≤ 7 * Tb.gasRate * (S.tower.stage (S.lastSeparated + dd)).toStepSetup.coupling := by
    have h1 : 7 * Tb.gasRate * (S.scaleCoupling / 2) ≤ 7 * Tb.gasRate * (S.tower.stage (S.lastSeparated + dd)).toStepSetup.coupling :=
      mul_le_mul_of_nonneg_left hRlo (by positivity)
    linarith
  have he := two_errors_le (B := M) (rt := Tb.rt) (ch := Tb.gasRate) (x := (S.tower.stage (S.lastSeparated + dd)).toStepSetup.coupling)
    (c := min (Tb.rt / 16) 1) hM0 (min_le_right _ _) (lt_min (by positivity) one_pos) (min_le_left _ _) hm4 hrL hm₀r
    (card_blocksNearFreeCores_supBall_le hfit.L_odd (S.tower.stage (S.lastSeparated + dd)).toStepSetup.range S.rangeSq
      (S.originSite (S.lastSeparated + dd + 1) n)) hx33
  exact error_sum_le hM0 (Nat.cast_nonneg _) he
    (hexp.trans (mul_le_mul_of_nonneg_left hmge (lt_min (by positivity) one_pos).le)) (Real.exp_pos _).le
end YangMills.Construction.MomentLaw
end
