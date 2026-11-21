import YangMills.Construction.LawByMomentsOfTheFlow.MomentsAtTheLastFarLevelInALimitFieldProof
import YangMills.Construction.LawByMomentsOfTheFlow.MomentsNearAProductAtAFarLevel
import YangMills.Construction.LawByMomentsOfTheFlow.MomentsNearAProductAtTheFarLevel
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory
namespace YangMills.Construction.MomentLaw
private theorem linear_le_eps_mul_pow_add (L : ℝ) (hL : 1 < L) (ε A : ℝ) (hε : 0 < ε) (hA : 0 ≤ A) :
    ∃ C₂ : ℝ, 0 ≤ C₂ ∧ ∀ m : ℕ, A * m ≤ ε * L ^ m + C₂ := by apply _root_.YangMills.SharedProofs.p107442 <;> assumption
private theorem sum_half_pow_le (s t : ℕ) (h : t ≤ s) :
    ∑ u ∈ Finset.range t, (1 / 2 : ℝ) ^ (s - u) ≤ (1 / 2 : ℝ) ^ (s - t) - (1 / 2 : ℝ) ^ s := by apply _root_.YangMills.SharedProofs.p34912 <;> assumption
private theorem weighted_sum_le_exp (L c rt : ℝ) (hL : 2 ≤ L) (hc : 0 < c) (hrt : 0 < rt) :
    ∃ ε W₀ : ℝ, 0 < ε ∧ 0 ≤ W₀ ∧ ∀ w : ℝ, W₀ ≤ w → ∀ (s t : ℕ) (D : ℕ → ℝ), t ≤ s →
      (∀ u < t, c * L ^ (s - u) - 12 ≤ D u) →
      (∀ u < t, L ^ (s - u) ≤ w → 2 ^ 10 * w ≤ D u) →
      ∑ u ∈ Finset.range t, L ^ (40 * (s - u)) * Real.exp (-(rt * D u / 2 ^ 8)) ≤
        Real.exp (-(ε * w)) := by
  have hL1 : 1 < L := by linarith
  have hlog : 0 < Real.log L := Real.log_pos hL1
  obtain ⟨γ, hγd⟩ : ∃ γ : ℝ, γ = rt * c / 2 ^ 8 := ⟨_, rfl⟩
  have hγ : 0 < γ := by
    rw [hγd]
    positivity
  obtain ⟨b, hbd⟩ : ∃ b : ℝ, b = 40 * Real.log L + Real.log 2 := ⟨_, rfl⟩
  have hb : 0 ≤ b := by
    rw [hbd]
    positivity
  obtain ⟨C₃, hC₃, h3⟩ := linear_le_eps_mul_pow_add L hL1 rt b hrt hb
  obtain ⟨C₄, hC₄, h4⟩ := linear_le_eps_mul_pow_add L hL1 (γ / 4) b (by positivity) hb
  obtain ⟨ε, hεd⟩ : ∃ ε : ℝ, ε = min rt (γ / 4) := ⟨_, rfl⟩
  have hε : 0 < ε := by
    rw [hεd]
    exact lt_min hrt (by positivity)
  have hε1 : ε ≤ rt := by
    rw [hεd]
    exact min_le_left _ _
  have hε2 : ε ≤ γ / 4 := by
    rw [hεd]
    exact min_le_right _ _
  refine ⟨ε, max (C₃ / rt) ((12 * rt / 2 ^ 8 + C₄) / (γ / 2)), hε, le_max_of_le_left (by positivity), ?_⟩
  intro w hw s t D hts h1 h2
  have hw1 : C₃ / rt ≤ w := (le_max_left _ _).trans hw
  have hw2 : (12 * rt / 2 ^ 8 + C₄) / (γ / 2) ≤ w := (le_max_right _ _).trans hw
  have hw0 : 0 ≤ w := le_trans (by positivity) hw1
  have hw1' : C₃ ≤ w * rt := (div_le_iff₀ hrt).mp hw1
  have hw2' : 12 * rt / 2 ^ 8 + C₄ ≤ w * (γ / 2) := (div_le_iff₀ (by positivity)).mp hw2
  have hterm : ∀ u ∈ Finset.range t, L ^ (40 * (s - u)) * Real.exp (-(rt * D u / 2 ^ 8)) ≤
      Real.exp (-(ε * w)) * (1 / 2 : ℝ) ^ (s - u) := by
    intro u hu
    have hut := Finset.mem_range.mp hu
    have hH1 := h1 u hut
    have hH2 := h2 u hut
    obtain ⟨e, he⟩ : ∃ e : ℕ, e = s - u := ⟨_, rfl⟩
    rw [← he] at hH1 hH2 ⊢
    have key : ε * w + b * e ≤ rt * D u / 2 ^ 8 := by
      rcases le_or_gt (L ^ e) w with hle | hgt
      · have hD := hH2 hle
        have h5 := h3 e
        have h6 : rt * L ^ e ≤ rt * w := mul_le_mul_of_nonneg_left hle hrt.le
        have h7 : ε * w ≤ rt * w := mul_le_mul_of_nonneg_right hε1 hw0
        have h8 : rt * (2 ^ 10 * w) ≤ rt * D u := mul_le_mul_of_nonneg_left hD hrt.le
        have h9 : 0 ≤ rt * w := by positivity
        linarith
      · have h5 := h4 e
        have h6 : rt * (c * L ^ e - 12) ≤ rt * D u := mul_le_mul_of_nonneg_left hH1 hrt.le
        have h7 : ε * w ≤ γ / 4 * L ^ e :=
          (mul_le_mul_of_nonneg_right hε2 hw0).trans (mul_le_mul_of_nonneg_left hgt.le (by positivity))
        have h8 : w * (γ / 2) ≤ L ^ e * (γ / 2) := mul_le_mul_of_nonneg_right hgt.le (by positivity)
        have h9 : γ * L ^ e = rt * c * L ^ e / 2 ^ 8 := by
          rw [hγd]
          ring
        linarith
    have e1 : L ^ (40 * e) = Real.exp (((40 * e : ℕ) : ℝ) * Real.log L) := by
      rw [Real.exp_nat_mul, Real.exp_log (by linarith)]
    have e2 : (1 / 2 : ℝ) ^ e = Real.exp ((e : ℝ) * (-Real.log 2)) := by
      rw [Real.exp_nat_mul, Real.exp_neg, Real.exp_log (by norm_num), one_div]
    rw [e1, e2, ← Real.exp_add, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    rw [hbd] at key
    push_cast
    linarith
  calc ∑ u ∈ Finset.range t, L ^ (40 * (s - u)) * Real.exp (-(rt * D u / 2 ^ 8))
      ≤ ∑ u ∈ Finset.range t, Real.exp (-(ε * w)) * (1 / 2 : ℝ) ^ (s - u) := Finset.sum_le_sum hterm
    _ = Real.exp (-(ε * w)) * ∑ u ∈ Finset.range t, (1 / 2 : ℝ) ^ (s - u) := by rw [Finset.mul_sum]
    _ ≤ Real.exp (-(ε * w)) * 1 := by
        apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
        have h5 := sum_half_pow_le s t hts
        have h6 : (1 / 2 : ℝ) ^ (s - t) ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
        have h7 : 0 ≤ (1 / 2 : ℝ) ^ s := by positivity
        linarith
    _ = Real.exp (-(ε * w)) := mul_one _
private theorem le_rpow_inv_of_pow_le (a x : ℝ) (n : ℕ) (hn : n ≠ 0) (ha : 0 ≤ a) (h : a ^ n ≤ x) :
    a ≤ x ^ (((n : ℕ) : ℝ))⁻¹ := by
  have h1 := Real.rpow_le_rpow (by positivity) h (by positivity : (0 : ℝ) ≤ ((n : ℕ) : ℝ)⁻¹)
  rwa [Real.pow_rpow_inv_natCast ha hn] at h1
private theorem weighted_sum_le_exp_neg_root (L c rt B A : ℝ) (hL : 2 ≤ L) (hc : 0 < c) (hrt : 0 < rt)
    (hB : 0 < B) (hA : 0 ≤ A) :
    ∃ X₁ : ℝ, ∀ x : ℝ, X₁ ≤ x → ∀ (s t : ℕ) (D : ℕ → ℝ), t ≤ s →
      (∀ u < t, c * L ^ (s - u) - 12 ≤ D u) →
      (∀ u < t, 4 * B * ((s - u : ℕ) : ℝ) ≤ x → 2 ^ 10 * (x ^ ((1 : ℝ) / 100) / 2) ≤ D u) →
      A * ∑ u ∈ Finset.range t, L ^ (40 * (s - u)) * Real.exp (-(rt * D u / 2 ^ 8)) ≤
        Real.exp (-(x ^ ((1 : ℝ) / 200))) := by
  obtain ⟨ε, W₀, hε, hW₀, hT⟩ := weighted_sum_le_exp L c rt hL hc hrt
  obtain ⟨l, hld⟩ : ∃ l : ℝ, l = Real.log (A + 1) := ⟨_, rfl⟩
  have hl : 0 ≤ l := by
    rw [hld]
    exact Real.log_nonneg (by linarith)
  obtain ⟨V, hVd⟩ : ∃ V : ℝ, V = 4 / ε + 4 * l / ε + 1 := ⟨_, rfl⟩
  have hV1 : 1 ≤ V := by
    have h1 : 0 ≤ 4 / ε := by positivity
    have h2 : 0 ≤ 4 * l / ε := by positivity
    rw [hVd]
    linarith
  refine ⟨max (max (V ^ 200) ((2 * W₀) ^ 100)) (max 1 ((2 * B) ^ 2)), ?_⟩
  intro x hx s t D hts h1 h2
  have hxV : V ^ 200 ≤ x := ((le_max_left _ _).trans (le_max_left _ _)).trans hx
  have hxW : (2 * W₀) ^ 100 ≤ x := ((le_max_right _ _).trans (le_max_left _ _)).trans hx
  have hx1 : 1 ≤ x := ((le_max_left _ _).trans (le_max_right _ _)).trans hx
  have hxB : (2 * B) ^ 2 ≤ x := ((le_max_right _ _).trans (le_max_right _ _)).trans hx
  have hx0 : 0 ≤ x := by linarith
  obtain ⟨v, hvd⟩ : ∃ v : ℝ, v = x ^ ((1 : ℝ) / 200) := ⟨_, rfl⟩
  have hv : V ≤ v := by
    have h3 := le_rpow_inv_of_pow_le V x 200 (by norm_num) (by linarith) hxV
    rw [hvd]
    have h4 : (((200 : ℕ) : ℝ))⁻¹ = (1 : ℝ) / 200 := by norm_num
    rwa [h4] at h3
  have hv1 : 1 ≤ v := hV1.trans hv
  have hsq : x ^ ((1 : ℝ) / 100) = v ^ 2 := by
    rw [hvd, ← Real.rpow_natCast, ← Real.rpow_mul hx0]
    norm_num
  obtain ⟨w, hwd⟩ : ∃ w : ℝ, w = x ^ ((1 : ℝ) / 100) / 2 := ⟨_, rfl⟩
  have hwW : W₀ ≤ w := by
    have h3 := le_rpow_inv_of_pow_le (2 * W₀) x 100 (by norm_num) (by positivity) hxW
    have h4 : (((100 : ℕ) : ℝ))⁻¹ = (1 : ℝ) / 100 := by norm_num
    rw [h4] at h3
    rw [hwd]
    linarith
  have hz : 2 * B ≤ x ^ ((1 : ℝ) / 2) := by
    have h3 := le_rpow_inv_of_pow_le (2 * B) x 2 (by norm_num) (by positivity) hxB
    have h4 : (((2 : ℕ) : ℝ))⁻¹ = (1 : ℝ) / 2 := by norm_num
    rwa [h4] at h3
  have hzz : x ^ ((1 : ℝ) / 2) * x ^ ((1 : ℝ) / 2) = x := by
    rw [← Real.rpow_add (by linarith)]
    norm_num
  have hroot : x ^ ((1 : ℝ) / 100) ≤ x ^ ((1 : ℝ) / 2) :=
    Real.rpow_le_rpow_of_exponent_le hx1 (by norm_num)
  have hz0 : 0 ≤ x ^ ((1 : ℝ) / 2) := Real.rpow_nonneg hx0 _
  have hpre : ∀ u < t, L ^ (s - u) ≤ w → 2 ^ 10 * w ≤ D u := by
    intro u hut hle
    rw [hwd] at hle ⊢
    apply h2 u hut
    have h3 : ((s - u : ℕ) : ℝ) ≤ L ^ (s - u) := by
      have h4 : ((s - u : ℕ) : ℝ) ≤ 2 ^ (s - u) := by
        have h5 : s - u + 1 ≤ 2 ^ (s - u) := Nat.lt_two_pow_self
        have h6 : ((s - u + 1 : ℕ) : ℝ) ≤ ((2 ^ (s - u) : ℕ) : ℝ) := by exact_mod_cast h5
        push_cast at h6
        linarith
      exact h4.trans (pow_le_pow_left₀ (by norm_num) hL _)
    have h4 : ((s - u : ℕ) : ℝ) ≤ x ^ ((1 : ℝ) / 2) / 2 := by linarith
    have h5 : 4 * B * ((s - u : ℕ) : ℝ) ≤ 4 * B * (x ^ ((1 : ℝ) / 2) / 2) :=
      mul_le_mul_of_nonneg_left h4 (by positivity)
    have h6 : 2 * B * x ^ ((1 : ℝ) / 2) ≤ x ^ ((1 : ℝ) / 2) * x ^ ((1 : ℝ) / 2) :=
      mul_le_mul_of_nonneg_right hz hz0
    linarith
  have hsum := hT w hwW s t D hts h1 hpre
  have hAe : A ≤ Real.exp l := by
    rw [hld, Real.exp_log (by linarith)]
    linarith
  have hEv : 4 + 4 * l ≤ ε * v := by
    have h3 := mul_le_mul_of_nonneg_left hv hε.le
    have h4 : ε * V = 4 + 4 * l + ε := by
      rw [hVd]
      field_simp
    linarith
  have hexp : l + -(ε * w) ≤ -v := by
    have h3 : (4 + 4 * l) * v ≤ ε * v * v := mul_le_mul_of_nonneg_right hEv (by linarith)
    have h4 : l ≤ l * v := le_mul_of_one_le_right hl hv1
    have h5 : w = v ^ 2 / 2 := by rw [hwd, hsq]
    rw [h5]
    nlinarith
  rw [← hvd]
  calc A * ∑ u ∈ Finset.range t, L ^ (40 * (s - u)) * Real.exp (-(rt * D u / 2 ^ 8))
      ≤ A * Real.exp (-(ε * w)) := mul_le_mul_of_nonneg_left hsum hA
    _ ≤ Real.exp l * Real.exp (-(ε * w)) := mul_le_mul_of_nonneg_right hAe (Real.exp_pos _).le
    _ = Real.exp (l + -(ε * w)) := (Real.exp_add _ _).symm
    _ ≤ Real.exp (-v) := Real.exp_le_exp.mpr hexp
private theorem sq_sum_mul_prod_le {ι : Type} (B : Finset ι) (a : ι → ℝ) (A M P C₀ : ℝ) (hB : B.card ≤ 8)
    (h0 : ∀ i ∈ B, 0 ≤ a i) (ha : ∀ i ∈ B, a i ≤ A * P) (hA : 1 ≤ A) (hM : 4 * C₀ * A ≤ M)
    (hM1 : 1 ≤ M) (hP : 1 ≤ P) (hC₀ : 0 ≤ C₀) :
    (∑ i ∈ B, a i) ^ 2 * ∏ i ∈ B, (4 * (C₀ * a i)) ≤ 64 * A ^ 2 * M ^ 8 * P ^ 10 := by
  have hAP : 0 ≤ A * P := by positivity
  have hs0 : 0 ≤ ∑ i ∈ B, a i := Finset.sum_nonneg h0
  have hs : ∑ i ∈ B, a i ≤ 8 * (A * P) := by
    calc ∑ i ∈ B, a i ≤ ∑ _i ∈ B, A * P := Finset.sum_le_sum ha
      _ = (B.card : ℝ) * (A * P) := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ 8 * (A * P) := mul_le_mul_of_nonneg_right (by exact_mod_cast hB) hAP
  have hs2 : (∑ i ∈ B, a i) ^ 2 ≤ (8 * (A * P)) ^ 2 := pow_le_pow_left₀ hs0 hs 2
  have hMP : 1 ≤ M * P := one_le_mul_of_one_le_of_one_le hM1 hP
  have hnn : ∀ i ∈ B, 0 ≤ 4 * (C₀ * a i) := fun i hi =>
    mul_nonneg (by norm_num) (mul_nonneg hC₀ (h0 i hi))
  have hp : ∏ i ∈ B, (4 * (C₀ * a i)) ≤ (M * P) ^ 8 := by
    calc ∏ i ∈ B, (4 * (C₀ * a i)) ≤ ∏ _i ∈ B, (M * P) := by
          apply Finset.prod_le_prod hnn
          intro i hi
          have h1 : C₀ * a i ≤ C₀ * (A * P) := mul_le_mul_of_nonneg_left (ha i hi) hC₀
          have h2 : 4 * C₀ * A * P ≤ M * P := mul_le_mul_of_nonneg_right hM (by linarith)
          nlinarith
      _ = (M * P) ^ B.card := by rw [Finset.prod_const]
      _ ≤ (M * P) ^ 8 := pow_le_pow_right₀ hMP hB
  have hp0 : 0 ≤ ∏ i ∈ B, (4 * (C₀ * a i)) := Finset.prod_nonneg hnn
  calc (∑ i ∈ B, a i) ^ 2 * ∏ i ∈ B, (4 * (C₀ * a i))
      ≤ (8 * (A * P)) ^ 2 * (M * P) ^ 8 := mul_le_mul hs2 hp hp0 (by positivity)
    _ = 64 * A ^ 2 * M ^ 8 * P ^ 10 := by ring
private theorem norm_le_two_mul_of_abs_coord_le (x : TestFunctions.EuclideanFourSpace) (R : ℝ)
    (h : ∀ a, |x a| ≤ R) : ‖x‖ ≤ 2 * R := by apply _root_.YangMills.SharedProofs.p52306 <;> assumption
private theorem supDist_le_dist (x y : TestFunctions.EuclideanFourSpace) : supDist x y ≤ dist x y := by apply _root_.YangMills.SharedProofs.p2932 <;> assumption
private theorem admissible_of_supAdmissible {k : ℕ} {P : LevelTestFunctions.LevelData k} {L : ℕ} [NeZero L]
    {R d : ℝ} (h : P.SupAdmissible L R d) : P.Admissible L (2 * R) d where
  isTestFamily :=
    { lipschitzWith_one := fun i => LipschitzWith.of_dist_le_mul fun x y => by
        rw [NNReal.coe_one, one_mul, Real.dist_eq]
        exact (h.isSupTestFamily.lipschitz i x y).trans (supDist_le_dist x y)
      abs_le_one := h.isSupTestFamily.abs_le_one
      tsupport_subset_closedBall := fun i x hx => by
        rw [Metric.mem_closedBall, dist_zero_right]
        exact norm_le_two_mul_of_abs_coord_le x R (h.isSupTestFamily.abs_coord_le i x hx)
      le_dist_of_ne := fun i j hij x hx y hy =>
        (h.isSupTestFamily.le_supDist i j hij x hx y hy).trans (supDist_le_dist x y) }
  scaleLevel_le := h.scaleLevel_le
  support_small := h.support_small
  exists_ne_zero := h.exists_ne_zero
open Classical in
private theorem lastSeparated_le_and_separatedBelow {Λ : MomentParameters} (S : MomentPoint Λ) :
    S.lastSeparated ≤ S.data.scaleLevel ∧
      S.data.SeparatedBelow Λ.stepParams S.β S.lastSeparated := by
  unfold MomentPoint.lastSeparated
  exact ⟨Nat.findGreatest_le _,
    Nat.findGreatest_spec (m := 0) (Nat.zero_le _) fun u hu => absurd hu (Nat.not_lt_zero u)⟩
private theorem productApprox_lastSeparated_aux {Λ : MomentParameters} (hf : Λ.stepParams.Admissible)
    (hK : Λ.response.Admissible Λ.stepParams) (hrun : LevelTestFunctions.AdmissibleStep Λ.stepParams)
    (hg : 0 < Λ.g) (hy : Λ.stepParams.y₁ ≤ (Λ.g ^ 2)⁻¹) (hk2 : 2 ≤ Λ.k) (hk8 : Λ.k ≤ 8) (hd : 0 < Λ.d)
    (hG : LevelTestFunctions.separationLowerBoundStatement)
    (hW : LevelTestFunctions.CouplingFlowAboveWindow) (C₁ C₂ : ℕ → ℝ)
    (hM : ∀ S : MomentPoint Λ, ∀ t' ≤ S.data.windowLevel,
      (∀ u ≤ t', ∀ i : Fin Λ.k, WeightedResponses.weightNorm Λ.stepParams.side u
        (S.weight i (WeightedResponses.fineSide Λ.stepParams.side u (S.levelSide u))) ≤ 1) →
      S.data.SeparatedBelow Λ.stepParams S.β t' → ∀ B : Finset (Fin Λ.k),
        ∀ᵐ w ∂(S.law t' (S.levelSide t')),
        |WeightedResponses.conditionalCenteredProduct S.tower S.β S.coeff t' (S.levelSide t')
            (fun i => S.weight i _) B (fun i => S.kappa t' (S.levelSide t') i) w -
            ∏ i ∈ B, S.supportTotal t' (S.levelSide t') i (S.state t' (S.levelSide t') w)| ≤
          S.separationError (C₁ B.card) t' B *
            ∏ i ∈ B, S.meanScore t' (S.levelSide t') i (S.state t' (S.levelSide t') w))
    (hS : ∀ S : MomentPoint Λ, ∀ u ≤ S.data.scaleLevel, ∀ i : Fin Λ.k,
      WeightedResponses.weightNorm Λ.stepParams.side u
          (S.weight i (WeightedResponses.fineSide Λ.stepParams.side u (S.levelSide u))) ≤ 1 ∧
        ((S.data.supportSites Λ.stepParams.side u i).card : ℝ) ≤
          C₂ 0 * (Λ.stepParams.side : ℝ) ^ (4 * (S.data.scaleLevel - u))) :
    ∃ (C : ℕ → ℝ) (c X₀ : ℝ), 0 < c ∧ Λ.floor ≤ X₀ ∧ ∀ S : MomentPoint Λ, ∀ B : Finset (Fin Λ.k),
      (∀ᵐ w ∂(S.law S.lastSeparated (S.levelSide S.lastSeparated)),
        |WeightedResponses.conditionalCenteredProduct S.tower S.β S.coeff S.lastSeparated
            (S.levelSide S.lastSeparated) (fun i => S.weight i _) B
            (fun i => S.kappa S.lastSeparated (S.levelSide S.lastSeparated) i) w -
            ∏ i ∈ B, S.supportTotal S.lastSeparated (S.levelSide S.lastSeparated) i
              (S.state S.lastSeparated (S.levelSide S.lastSeparated) w)| ≤
          S.separationError (C B.card) S.lastSeparated B *
            ∏ i ∈ B, S.meanScore S.lastSeparated (S.levelSide S.lastSeparated) i
              (S.state S.lastSeparated (S.levelSide S.lastSeparated) w)) ∧
      S.separationError (C B.card) S.lastSeparated B ≤ C 100 * ∑ u ∈ Finset.range S.lastSeparated,
        (Λ.stepParams.side : ℝ) ^ (C 101 * ((S.data.scaleLevel : ℝ) - (u : ℝ))) *
          Real.exp (-(Λ.stepParams.rt * (S.data.separation Λ.stepParams.side u : ℝ) / 2 ^ 8)) ∧
      (X₀ ≤ S.scaleCoupling → S.separationError (C B.card) S.lastSeparated B ≤
        Real.exp (-(S.scaleCoupling ^ ((1 : ℝ) / 200)))) := by
  have hL2 : (2 : ℝ) ≤ (Λ.stepParams.side : ℝ) := by
    have h1 := hf.L_ge
    exact_mod_cast (by omega : 2 ≤ Λ.stepParams.side)
  obtain ⟨c, hc, hgap⟩ := hG Λ.stepParams.side hf.L_odd (by have h1 := hf.L_ge; omega) Λ.k hk2
    (2 * Λ.R) Λ.d hd
  have hC₀ : 0 ≤ Λ.response.C₀ := by
    rw [hK.C₀_eq]
    linarith [hf.a_ge, hK.N₀_nonneg, hK.Kc_ge]
  obtain ⟨A', hA'd⟩ : ∃ A' : ℝ, A' = max (C₂ 0) 1 := ⟨_, rfl⟩
  have hA' : 1 ≤ A' := by
    rw [hA'd]
    exact le_max_right _ _
  have hA'2 : C₂ 0 ≤ A' := by
    rw [hA'd]
    exact le_max_left _ _
  obtain ⟨M, hMd⟩ : ∃ M : ℝ, M = max (4 * Λ.response.C₀ * A') 1 := ⟨_, rfl⟩
  have hM1 : 1 ≤ M := by
    rw [hMd]
    exact le_max_right _ _
  have hM' : 4 * Λ.response.C₀ * A' ≤ M := by
    rw [hMd]
    exact le_max_left _ _
  obtain ⟨K₀, hK₀⟩ : ∃ K₀ : ℝ, K₀ = 64 * A' ^ 2 * M ^ 8 := ⟨_, rfl⟩
  have hK₀0 : 0 ≤ K₀ := by
    rw [hK₀]
    positivity
  obtain ⟨Cm, hCmd⟩ : ∃ Cm : ℝ, Cm = ∑ j ∈ Finset.range 9, |C₁ j| := ⟨_, rfl⟩
  have hCm0 : 0 ≤ Cm := by
    rw [hCmd]
    exact Finset.sum_nonneg fun _ _ => abs_nonneg _
  obtain ⟨A₀, hA₀⟩ : ∃ A₀ : ℝ, A₀ = Cm * K₀ := ⟨_, rfl⟩
  have hA₀0 : 0 ≤ A₀ := by
    rw [hA₀]
    positivity
  obtain ⟨X₁, hX₁⟩ := weighted_sum_le_exp_neg_root (Λ.stepParams.side : ℝ) c Λ.stepParams.rt
    Λ.stepParams.B A₀ hL2 hc hf.rt_pos hf.B_pos hA₀0
  obtain ⟨C, hCd⟩ : ∃ C : ℕ → ℝ, C = fun n => if n = 100 then A₀ else if n = 101 then 40 else C₁ n :=
    ⟨_, rfl⟩
  have hC100 : C 100 = A₀ := by simp [hCd]
  have hC101 : C 101 = 40 := by simp [hCd]
  refine ⟨C, 1, max Λ.floor X₁, one_pos, le_max_left _ _, fun S B => ?_⟩
  have hcard : B.card ≤ 8 := by
    have h1 := Finset.card_le_univ B
    rw [Fintype.card_fin] at h1
    omega
  have hCB : C B.card = C₁ B.card := by
    have h1 : B.card ≠ 100 := by omega
    have h2 : B.card ≠ 101 := by omega
    simp [hCd, h1, h2]
  have hCm : |C₁ B.card| ≤ Cm := by
    rw [hCmd]
    exact Finset.single_le_sum (f := fun j => |C₁ j|) (fun _ _ => abs_nonneg _)
      (Finset.mem_range.mpr (by omega))
  obtain ⟨hts, hfar⟩ := lastSeparated_le_and_separatedBelow S
  have hsK : S.data.scaleLevel ≤ S.data.windowLevel := S.supAdmissible.scaleLevel_le
  have hFit : S.data.Admissible Λ.stepParams.side (2 * Λ.R) Λ.d :=
    admissible_of_supAdmissible S.supAdmissible
  have hrunF := hW Λ.stepParams hrun Λ.g hg hy S.β S.data.windowLevel S.window_le S.passage
  have hbound : S.separationError (C₁ B.card) S.lastSeparated B ≤ A₀ * ∑ u ∈ Finset.range S.lastSeparated,
      (Λ.stepParams.side : ℝ) ^ (40 * (S.data.scaleLevel - u)) *
        Real.exp (-(Λ.stepParams.rt * (S.data.separation Λ.stepParams.side u : ℝ) / 2 ^ 8)) := by
    unfold MomentPoint.separationError
    have hT : ∀ u ∈ Finset.range S.lastSeparated,
        (∑ i ∈ B, ((S.data.supportSites Λ.stepParams.side u i).card : ℝ)) ^ 2 *
        Real.exp (-(Λ.stepParams.rt * (S.data.separation Λ.stepParams.side u : ℝ) / 2 ^ 8)) *
        ∏ i ∈ B, (4 * (Λ.response.C₀ * ((S.data.supportSites Λ.stepParams.side u i).card : ℝ))) ≤
        K₀ * ((Λ.stepParams.side : ℝ) ^ (40 * (S.data.scaleLevel - u)) *
          Real.exp (-(Λ.stepParams.rt * (S.data.separation Λ.stepParams.side u : ℝ) / 2 ^ 8))) := by
      intro u hu
      have hut := Finset.mem_range.mp hu
      have hP : (1 : ℝ) ≤ (Λ.stepParams.side : ℝ) ^ (4 * (S.data.scaleLevel - u)) :=
        one_le_pow₀ (by linarith)
      have h1 := sq_sum_mul_prod_le B (fun i => ((S.data.supportSites Λ.stepParams.side u i).card : ℝ))
        A' M _ Λ.response.C₀ hcard
        (fun i _ => Nat.cast_nonneg _)
        (fun i _ => ((hS S u (hut.le.trans hts) i).2).trans
          (mul_le_mul_of_nonneg_right hA'2 (by linarith)))
        hA' hM' hM1 hP hC₀
      beta_reduce at h1
      have h2 : ((Λ.stepParams.side : ℝ) ^ (4 * (S.data.scaleLevel - u))) ^ 10 =
          (Λ.stepParams.side : ℝ) ^ (40 * (S.data.scaleLevel - u)) := by
        rw [← pow_mul]
        congr 1
        ring
      rw [h2, ← hK₀] at h1
      have he := (Real.exp_pos
        (-(Λ.stepParams.rt * (S.data.separation Λ.stepParams.side u : ℝ) / 2 ^ 8))).le
      have h3 := mul_le_mul_of_nonneg_right h1 he
      calc _ = (∑ i ∈ B, ((S.data.supportSites Λ.stepParams.side u i).card : ℝ)) ^ 2 *
            (∏ i ∈ B, (4 * (Λ.response.C₀ * ((S.data.supportSites Λ.stepParams.side u i).card : ℝ)))) *
            Real.exp (-(Λ.stepParams.rt * (S.data.separation Λ.stepParams.side u : ℝ) / 2 ^ 8)) := by
              ring
        _ ≤ _ := h3
        _ = _ := by ring
    have hT0 : 0 ≤ ∑ u ∈ Finset.range S.lastSeparated,
        (∑ i ∈ B, ((S.data.supportSites Λ.stepParams.side u i).card : ℝ)) ^ 2 *
        Real.exp (-(Λ.stepParams.rt * (S.data.separation Λ.stepParams.side u : ℝ) / 2 ^ 8)) *
        ∏ i ∈ B, (4 * (Λ.response.C₀ * ((S.data.supportSites Λ.stepParams.side u i).card : ℝ))) :=
      Finset.sum_nonneg fun u _ => mul_nonneg (mul_nonneg (sq_nonneg _) (Real.exp_pos _).le)
        (Finset.prod_nonneg fun i _ => mul_nonneg (by norm_num) (mul_nonneg hC₀ (Nat.cast_nonneg _)))
    refine (mul_le_mul_of_nonneg_right ((le_abs_self _).trans hCm) hT0).trans ?_
    refine (mul_le_mul_of_nonneg_left (Finset.sum_le_sum hT) hCm0).trans (le_of_eq ?_)
    rw [← Finset.mul_sum, hA₀]
    ring
  rw [hCB]
  refine ⟨hM S S.lastSeparated (hts.trans hsK) (fun u hu i => (hS S u (hu.trans hts) i).1) hfar B, ?_, ?_⟩
  · refine hbound.trans (le_of_eq ?_)
    rw [hC100]
    congr 1
    refine Finset.sum_congr rfl fun u hu => ?_
    have hus := (Finset.mem_range.mp hu).le.trans hts
    have h1 : C 101 * ((S.data.scaleLevel : ℝ) - (u : ℝ)) = ((40 * (S.data.scaleLevel - u) : ℕ) : ℝ) := by
      rw [hC101, Nat.cast_mul, Nat.cast_sub hus]
      norm_num
    rw [h1, Real.rpow_natCast]
  · intro hx
    have hxX : X₁ ≤ S.scaleCoupling := (le_max_right _ _).trans hx
    have hxy : Λ.floor ≤ S.scaleCoupling := (le_max_left _ _).trans hx
    have hy1 : (1 : ℝ) ≤ Λ.floor := hf.y₁_ge
    have hx0 : 0 ≤ S.scaleCoupling := by linarith
    refine hbound.trans (hX₁ S.scaleCoupling hxX S.data.scaleLevel S.lastSeparated
      (fun u => (S.data.separation Λ.stepParams.side u : ℝ)) hts ?_ ?_)
    · intro u hut
      have h1 := hgap S.data hFit u (lt_of_lt_of_le hut (hts.trans hsK))
      have hz : (Λ.stepParams.side : ℝ) ^ ((S.data.scaleLevel : ℤ) - (u : ℤ)) =
          (Λ.stepParams.side : ℝ) ^ (S.data.scaleLevel - u) := by
        have h2 : (S.data.scaleLevel : ℤ) - (u : ℤ) = ((S.data.scaleLevel - u : ℕ) : ℤ) := by
          have h3 := hut.le.trans hts
          omega
        rw [h2, zpow_natCast]
      rw [hz] at h1
      exact h1
    · intro u hut h4
      have hus := hut.le.trans hts
      have hcast : (2 : ℝ) ^ 10 *
          (TorusLumps.clusterRange (TorusLumps.couplingFlow Λ.stepParams S.β u).1 : ℝ) ≤
          (S.data.separation Λ.stepParams.side u : ℝ) := by
        exact_mod_cast (hfar u hut).1
      have hmove := hrunF.2 u S.data.scaleLevel hus hsK
      rw [Nat.cast_sub hus] at h4
      have hxu : S.scaleCoupling / 2 ≤ (TorusLumps.couplingFlow Λ.stepParams S.β u).1 := by
        have h1 := (abs_le.mp hmove).2
        have h2 : S.scaleCoupling = (TorusLumps.couplingFlow Λ.stepParams S.β S.data.scaleLevel).1 := rfl
        rw [← h2] at h1
        linarith
      have h5 : (S.scaleCoupling / 2) ^ ((1 : ℝ) / 100) ≤
          (TorusLumps.couplingFlow Λ.stepParams S.β u).1 ^ ((1 : ℝ) / 100) :=
        Real.rpow_le_rpow (by positivity) hxu (by norm_num)
      have h6 : S.scaleCoupling ^ ((1 : ℝ) / 100) / 2 ≤ (S.scaleCoupling / 2) ^ ((1 : ℝ) / 100) := by
        rw [Real.div_rpow hx0 (by norm_num)]
        apply div_le_div_of_nonneg_left (Real.rpow_nonneg hx0 _) (Real.rpow_pos_of_pos (by norm_num) _)
        exact (Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)).trans_eq (Real.rpow_one 2)
      have h7 : (TorusLumps.couplingFlow Λ.stepParams S.β u).1 ^ ((1 : ℝ) / 100) ≤
          (TorusLumps.clusterRange (TorusLumps.couplingFlow Λ.stepParams S.β u).1 : ℝ) := Nat.le_ceil _
      show 2 ^ 10 * (S.scaleCoupling ^ ((1 : ℝ) / 100) / 2) ≤ (S.data.separation Λ.stepParams.side u : ℝ)
      linarith
theorem productApproxAtLastSeparated_holds (hM : productApproxAtSeparatedLevelStatement)
    (hS : weightsSitesBelowScaleStatement) (hG : LevelTestFunctions.separationLowerBoundStatement)
    (hW : LevelTestFunctions.CouplingFlowAboveWindow) : productApproxAtLastSeparatedStatement := by
  intro a ha
  obtain ⟨L₁, r₁, D₁, hr₁, H₁⟩ := hM a ha
  obtain ⟨L₂, r₂, D₂, hr₂, H₂⟩ := hS a ha
  refine ⟨max L₁ L₂, fun c => min (r₁ c) (r₂ c), max D₁ D₂, fun c => lt_min (hr₁ c) (hr₂ c), ?_⟩
  intro L hL hLL Tb hTa hTL hD hCS hCH hrt hC Kr hKr
  obtain ⟨y₁, H₁⟩ := H₁ L hL ((le_max_left _ _).trans hLL) Tb hTa hTL hD hCS hCH
    (hrt.trans (min_le_left _ _)) ((le_max_left _ _).trans hC) Kr hKr
  obtain ⟨y₂, H₂⟩ := H₂ L hL ((le_max_right _ _).trans hLL) Tb hTa hTL hD hCS hCH
    (hrt.trans (min_le_right _ _)) ((le_max_right _ _).trans hC) Kr hKr
  refine ⟨max (max y₁ y₂) Tb.floorMin, ?_⟩
  intro y hy hret hrow g hg hyg k _ hk2 hk8 R d hd
  have hy₁ : y₁ ≤ y := ((le_max_left _ _).trans (le_max_left _ _)).trans hy
  have hy₂ : y₂ ≤ y := ((le_max_right _ _).trans (le_max_left _ _)).trans hy
  have hf : (Tb.stepParameters y).Admissible := hD.fits y ((le_max_right _ _).trans hy)
  obtain ⟨C₁, _, _, _, _, Q₁⟩ := H₁ y hy₁ hret hrow g hg hyg k hk2 hk8 R d hd
  obtain ⟨C₂, _, _, _, _, Q₂⟩ := H₂ y hy₂ hret hrow g hg hyg k hk2 hk8 R d hd
  exact productApprox_lastSeparated_aux (Λ := ⟨Tb, Kr, y, g, k, R, d⟩) hf (hKr y) ⟨hf, hret, hrow⟩ hg hyg
    hk2 hk8 hd hG hW C₁ C₂ Q₁ Q₂
end YangMills.Construction.MomentLaw
end
