import YangMills.Construction.ColdStepAtMirrorFrames.EnergyOfTheShiftOfAChain
import Mathlib
set_option autoImplicit false
noncomputable section
open YangMills.Construction.BlockAverages
namespace YangMills.Construction.ColdStepAtMirrorFrames
variable {F : BlockFrame}
theorem chainMisfit_testForm (W : (j : ℕ) → F.Site j → ℝ) (X : FormChain F) (j : ℕ) (y : F.Site (j + 1)) (k : Fin 4) :
    chainMisfit (testForm W X) j y k = W (j + 1) y * chainMisfit X j y k := by
  simp only [chainMisfit, testForm]
  ring
theorem sq_cutoff_step_mul_le (hL : Odd F.blockSide) (hs : ∀ i, 0 < F.extent i) (h8 : 8 ≤ F.blockSide) (c : Fin 4 → ℝ) (x : F.Site 0)
    (k : Fin 4) (G : F.Site 0 → ℝ) :
    ((cutoff c 0 (x + unitStep 0 k) - cutoff c 0 x) * G (x + unitStep 0 k)) ^ 2 ≤
      1 / (4 * (cellSide F : ℝ) ^ 2) * (nearWeight c 5 0 (x + unitStep 0 k) * G (x + unitStep 0 k)) ^ 2 := by
  have hL4 : 4 ≤ F.blockSide := by omega
  have hNr : (1 : ℝ) ≤ cellSide F := by exact_mod_cast cellSide_pos hL
  have hd := abs_distFromPoint_unitStep_sub_le hL hs x k c
  by_cases hx : distFromPoint c (x + unitStep 0 k) ≤ 5
  · have e : nearWeight c 5 0 (x + unitStep 0 k) = 1 := by
      unfold nearWeight
      have := readReach_nonneg (F := F) hL4 0
      rw [if_pos ⟨Nat.zero_le _, by linarith⟩]
    rw [e, one_mul, mul_pow]
    refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
    have h1 := (abs_cutoff_sub_le c x (x + unitStep 0 k)).trans (mul_le_mul_of_nonneg_left hd (by norm_num))
    have h2 := pow_le_pow_left₀ (abs_nonneg _) h1 2
    rw [sq_abs] at h2
    refine h2.trans (le_of_eq ?_)
    field_simp
    ring
  · push Not at hx
    have h1 : (1 : ℝ) / cellSide F ≤ 1 := by
      rw [div_le_one (by linarith)]
      exact hNr
    have c1 : cutoff c 0 (x + unitStep 0 k) = 0 := cutoff_eq_zero c _ (by linarith)
    have c2 : cutoff c 0 x = 0 := cutoff_eq_zero c _ (by
      have := (abs_le.1 hd).2
      linarith)
    rw [c1, c2]
    simp only [sub_self, zero_mul, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]
    positivity
theorem sum_sq_plaquetteCurl_add_cutoff_le (hL : Odd F.blockSide) (hs : ∀ i, 0 < F.extent i) (h8 : 8 ≤ F.blockSide) (c : Fin 4 → ℝ) (i : Fin 4) (m : ℕ)
    (hm : m ≤ F.blockSide) (B₀ U₀ : LevelForm F 0)
    (hU : ∀ x k l, plaquetteCurl U₀ x k l = plaquetteCurl B₀ (x + axisOffset 0 i (shiftLength F m 0)) k l - plaquetteCurl B₀ x k l) :
    ∑ x ∈ allSites F 0, ∑ e ∈ orientedPlanes,
        plaquetteCurl (B₀ + fun x k => cutoff c 0 x * U₀ x k) x e.1 e.2 ^ 2 ≤
      (∑ x ∈ allSites F 0, ∑ e ∈ orientedPlanes, plaquetteCurl B₀ x e.1 e.2 ^ 2) +
        (m : ℝ) / (2 * F.blockSide) * weightedCurlNormSq (ballIndicator c 5 0) B₀ +
        2 * (Real.sqrt (2 * weightedCurlNormSq (nearWeight c 6 0) B₀) * Real.sqrt (6 * weightedNormSq (nearWeight c 5 0) U₀ / (cellSide F : ℝ) ^ 2)) +
        6 * weightedNormSq (nearWeight c 5 0) U₀ / (cellSide F : ℝ) ^ 2 := by
  have hNr : (0 : ℝ) < cellSide F := by exact_mod_cast cellSide_pos hL
  have hN1 : (1 : ℝ) ≤ cellSide F := by exact_mod_cast cellSide_pos hL
  have hLp : (0 : ℝ) < F.blockSide := by exact_mod_cast hL.pos
  have hm1 : (m : ℝ) / F.blockSide ≤ 1 := by
    rw [div_le_one hLp]
    exact_mod_cast hm
  have h0t : 0 ≤ F.depth := Nat.zero_le _
  set s := axisOffset 0 i (shiftLength F m 0) with hs'
  set ch := cutoff (F := F) c 0 with hch
  set Y : F.Site 0 → Fin 4 × Fin 4 → ℝ := fun x e =>
    (1 - ch x) * plaquetteCurl B₀ x e.1 e.2 + ch x * plaquetteCurl B₀ (x + s) e.1 e.2 with hY
  set R : F.Site 0 → Fin 4 × Fin 4 → ℝ := fun x e =>
    (ch (x + unitStep 0 e.1) - ch x) * U₀ (x + unitStep 0 e.1) e.2 -
      (ch (x + unitStep 0 e.2) - ch x) * U₀ (x + unitStep 0 e.2) e.1 with hR
  have hsum : ∀ x e, plaquetteCurl (B₀ + fun x k => ch x * U₀ x k) x e.1 e.2 = Y x e + R x e := by
    intro x e
    rw [plaquetteCurl_add, plaquetteCurl_mul_left ch U₀ x e.1 e.2, hU]
    simp only [hY, hR]
    ring
  set J := ballIndicator (F := F) c 5 0 with hJ
  have hJR : ∀ x e, J x * R x e = R x e := by
    intro x e
    by_cases hx : distFromPoint c x ≤ 5
    · have : J x = 1 := by
        simp only [hJ]
        unfold ballIndicator
        rw [if_pos hx]
      rw [this, one_mul]
    · push Not at hx
      have hd1 := abs_distFromPoint_unitStep_sub_le hL hs x e.1 c
      have hd2 := abs_distFromPoint_unitStep_sub_le hL hs x e.2 c
      have h1 : (1 : ℝ) / cellSide F ≤ 1 := by
        rw [div_le_one hNr]
        exact hN1
      have c0 : ch x = 0 := cutoff_eq_zero c x (by linarith)
      have c1 : ch (x + unitStep 0 e.1) = 0 := cutoff_eq_zero c _ (by
        have := (abs_le.1 hd1).1
        linarith)
      have c2 : ch (x + unitStep 0 e.2) = 0 := cutoff_eq_zero c _ (by
        have := (abs_le.1 hd2).1
        linarith)
      have : R x e = 0 := by
        simp only [hR, c0, c1, c2]
        ring
      rw [this, mul_zero]
  have hRsq : ∀ e, ∑ x ∈ allSites F 0, R x e ^ 2 ≤ weightedNormSq (nearWeight c 5 0) U₀ / (cellSide F : ℝ) ^ 2 := by
    intro e
    have t : ∀ (k l : Fin 4), ∑ x ∈ allSites F 0, ((ch (x + unitStep 0 k) - ch x) * U₀ (x + unitStep 0 k) l) ^ 2 ≤
        1 / (4 * (cellSide F : ℝ) ^ 2) * weightedNormSq (nearWeight c 5 0) U₀ := by
      intro k l
      calc _ ≤ ∑ x ∈ allSites F 0, 1 / (4 * (cellSide F : ℝ) ^ 2) *
            (nearWeight c 5 0 (x + unitStep 0 k) * U₀ (x + unitStep 0 k) l) ^ 2 :=
            Finset.sum_le_sum fun x _ => sq_cutoff_step_mul_le hL hs h8 c x k (fun y => U₀ y l)
        _ = 1 / (4 * (cellSide F : ℝ) ^ 2) * ∑ x ∈ allSites F 0, (nearWeight c 5 0 x * U₀ x l) ^ 2 := by
            rw [← Finset.mul_sum]
            congr 1
            exact sum_allSites_add_right hL hs (Nat.zero_le _) _ (fun x => (nearWeight c 5 0 x * U₀ x l) ^ 2)
        _ ≤ _ := mul_le_mul_of_nonneg_left (sum_sq_component_le_weightedNormSq _ _ l) (by positivity)
    have a1 := t e.1 e.2
    have a2 := t e.2 e.1
    calc _ ≤ ∑ x ∈ allSites F 0, (2 * ((ch (x + unitStep 0 e.1) - ch x) * U₀ (x + unitStep 0 e.1) e.2) ^ 2 +
          2 * ((ch (x + unitStep 0 e.2) - ch x) * U₀ (x + unitStep 0 e.2) e.1) ^ 2) := by
          refine Finset.sum_le_sum fun x _ => ?_
          simp only [hR]
          nlinarith [sq_nonneg ((ch (x + unitStep 0 e.1) - ch x) * U₀ (x + unitStep 0 e.1) e.2 +
            (ch (x + unitStep 0 e.2) - ch x) * U₀ (x + unitStep 0 e.2) e.1)]
      _ = 2 * ∑ x ∈ allSites F 0, ((ch (x + unitStep 0 e.1) - ch x) * U₀ (x + unitStep 0 e.1) e.2) ^ 2 +
          2 * ∑ x ∈ allSites F 0, ((ch (x + unitStep 0 e.2) - ch x) * U₀ (x + unitStep 0 e.2) e.1) ^ 2 := by
          rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
      _ ≤ _ := by
          have e2 : weightedNormSq (nearWeight c 5 0) U₀ / (cellSide F : ℝ) ^ 2 =
              2 * (1 / (4 * (cellSide F : ℝ) ^ 2) * weightedNormSq (nearWeight c 5 0) U₀) +
              2 * (1 / (4 * (cellSide F : ℝ) ^ 2) * weightedNormSq (nearWeight c 5 0) U₀) := by
            field_simp
            ring
          rw [e2]
          linarith
  set Q := ∑ e ∈ orientedPlanes, ∑ x ∈ allSites F 0, R x e ^ 2 with hQ
  have hQle : Q ≤ 6 * weightedNormSq (nearWeight c 5 0) U₀ / (cellSide F : ℝ) ^ 2 := by
    calc Q ≤ ∑ _e ∈ orientedPlanes, weightedNormSq (nearWeight c 5 0) U₀ / (cellSide F : ℝ) ^ 2 := Finset.sum_le_sum fun e _ => hRsq e
      _ = _ := by
          simp only [Finset.sum_const, nsmul_eq_mul, card_orientedPlanes]
          push_cast
          ring
  have hYJ : ∀ e, ∑ x ∈ allSites F 0, (J x * Y x e) ^ 2 ≤
      2 * ∑ x ∈ allSites F 0, (nearWeight c 6 0 x * plaquetteCurl B₀ x e.1 e.2) ^ 2 := by
    intro e
    have p1 : ∀ x, (J x * Y x e) ^ 2 ≤ (nearWeight c 6 0 x * plaquetteCurl B₀ x e.1 e.2) ^ 2 +
        (nearWeight c 6 0 (x + s) * plaquetteCurl B₀ (x + s) e.1 e.2) ^ 2 := by
      intro x
      have a0 : 0 ≤ ch x := cutoff_nonneg c x
      have a1 : ch x ≤ 1 := cutoff_le_one c x
      set f := plaquetteCurl B₀ x e.1 e.2
      set g := plaquetteCurl B₀ (x + s) e.1 e.2
      have y2 : Y x e ^ 2 ≤ f ^ 2 + g ^ 2 := by
        simp only [hY]
        nlinarith [mul_nonneg (mul_nonneg a0 (by linarith : (0 : ℝ) ≤ 1 - ch x)) (sq_nonneg (f - g)),
          sq_nonneg f, sq_nonneg g, mul_nonneg a0 (sq_nonneg g), mul_nonneg (by linarith : (0 : ℝ) ≤ 1 - ch x) (sq_nonneg f)]
      by_cases hx : distFromPoint c x ≤ 5
      · have hJ1 : J x = 1 := by
          simp only [hJ]
          unfold ballIndicator
          rw [if_pos hx]
        have r0 := readReach_nonneg (F := F) (by omega) 0
        have n1 : nearWeight c 6 0 x = 1 := by
          unfold nearWeight
          rw [if_pos ⟨Nat.zero_le _, by linarith⟩]
        have hdx := abs_distFromPoint_shiftLength_sub_le hL hs h0t x i m c
        have n2 : nearWeight c 6 0 (x + s) = 1 := by
          unfold nearWeight
          rw [if_pos ⟨Nat.zero_le _, by
            have := (abs_le.1 hdx).2
            linarith⟩]
        rw [hJ1, n1, n2, one_mul, one_mul, one_mul]
        exact y2
      · have hJ0 : J x = 0 := by
          simp only [hJ]
          unfold ballIndicator
          rw [if_neg hx]
        rw [hJ0]
        simp only [zero_mul, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]
        positivity
    calc _ ≤ ∑ x ∈ allSites F 0, ((nearWeight c 6 0 x * plaquetteCurl B₀ x e.1 e.2) ^ 2 +
          (nearWeight c 6 0 (x + s) * plaquetteCurl B₀ (x + s) e.1 e.2) ^ 2) := Finset.sum_le_sum fun x _ => p1 x
      _ = _ := by
          rw [Finset.sum_add_distrib,
            sum_allSites_add_right hL hs (Nat.zero_le _) s (fun x => (nearWeight c 6 0 x * plaquetteCurl B₀ x e.1 e.2) ^ 2)]
          ring
  set P := ∑ e ∈ orientedPlanes, ∑ x ∈ allSites F 0, (J x * Y x e) ^ 2 with hP
  have hPle : P ≤ 2 * weightedCurlNormSq (nearWeight c 6 0) B₀ := by
    rw [weightedCurlNormSq_eq_sum_orientedPlanes, Finset.mul_sum]
    exact Finset.sum_le_sum fun e _ => hYJ e
  have hcross : |∑ e ∈ orientedPlanes, ∑ x ∈ allSites F 0, Y x e * R x e| ≤ Real.sqrt P * Real.sqrt Q := by
    have c1 := sum_abs_mul_abs_le_sqrt_mul_sqrt (orientedPlanes ×ˢ allSites F 0) (fun p => J p.2 * Y p.2 p.1) (fun p => R p.2 p.1)
    rw [Finset.sum_product, Finset.sum_product, Finset.sum_product] at c1
    refine le_trans ?_ c1
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun e _ => ?_)
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun x _ => ?_)
    have : Y x e * R x e = (J x * Y x e) * R x e := by
      conv_lhs => rw [← hJR x e]
      ring
    rw [this, abs_mul]
  have hYsq : ∑ e ∈ orientedPlanes, ∑ x ∈ allSites F 0, Y x e ^ 2 ≤
      (∑ e ∈ orientedPlanes, ∑ x ∈ allSites F 0, plaquetteCurl B₀ x e.1 e.2 ^ 2) + (m : ℝ) / (2 * F.blockSide) * weightedCurlNormSq (ballIndicator c 5 0) B₀ := by
    rw [weightedCurlNormSq_eq_sum_orientedPlanes, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_le_sum fun e _ => sum_sq_cutoff_mix_le hL hs h8 h0t c i m hm (fun x => plaquetteCurl B₀ x e.1 e.2)
  have hcomm : ∑ x ∈ allSites F 0, ∑ e ∈ orientedPlanes, plaquetteCurl (B₀ + fun x k => ch x * U₀ x k) x e.1 e.2 ^ 2 =
      (∑ e ∈ orientedPlanes, ∑ x ∈ allSites F 0, Y x e ^ 2) + 2 * (∑ e ∈ orientedPlanes, ∑ x ∈ allSites F 0, Y x e * R x e) + Q := by
    rw [Finset.sum_comm, hQ, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun e _ => ?_
    rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [hsum]
    ring
  rw [hcomm, Finset.sum_comm (s := allSites F 0)]
  have sP : Real.sqrt P ≤ Real.sqrt (2 * weightedCurlNormSq (nearWeight c 6 0) B₀) := Real.sqrt_le_sqrt hPle
  have sQ : Real.sqrt Q ≤ Real.sqrt (6 * weightedNormSq (nearWeight c 5 0) U₀ / (cellSide F : ℝ) ^ 2) := Real.sqrt_le_sqrt hQle
  have hprod := mul_le_mul sP sQ (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hx := (le_abs_self _).trans hcross
  linarith
structure LocalEnergyBounds (c : Fin 4 → ℝ) (a : ℝ) (B : FormChain F) (E : ℝ) : Prop where
  nonneg : 0 ≤ E
  curl_near : weightedCurlNormSq (nearWeight c 6 0) (B 0) ≤ E ^ 2
  misfit_near : totalMisfit (nearWeight c 6) B ≤ E ^ 2
  below_ball : weightedCurlNormSq (ballIndicator c 5 0) (B 0) + a * ∑ j ∈ Finset.range F.depth, weightedNormSq (ballIndicator c 5 (j + 1)) (chainMisfit B j) ≤ E ^ 2
  top_ball : a * weightedNormSq (ballIndicator c (15 / 2) F.top) (chainMisfit B F.depth) ≤ E ^ 2
theorem ballIndicator_sq_mono (c : Fin 4 → ℝ) {r r' : ℝ} (hr : r ≤ r') {j : ℕ} (x : F.Site j) :
    ballIndicator c r j x ^ 2 ≤ ballIndicator c r' j x ^ 2 := by
  unfold ballIndicator
  by_cases h : distFromPoint c x ≤ r
  · rw [if_pos h, if_pos (h.trans hr)]
  · rw [if_neg h]
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]
    exact sq_nonneg _
theorem localEnergyBounds_sqrt (hL8 : 8 ≤ F.blockSide) (c : Fin 4 → ℝ) {a : ℝ} (ha : 1 ≤ a) (B : FormChain F) :
    LocalEnergyBounds c a B (Real.sqrt (localEnergy c a B)) := by
  have ha0 : (0 : ℝ) ≤ a := by linarith
  have hL4 : 4 ≤ F.blockSide := by omega
  have hLr : (8 : ℝ) ≤ F.blockSide := by exact_mod_cast hL8
  have hLp : (0 : ℝ) < F.blockSide := by linarith
  have hE0 := localEnergy_nonneg c ha0 B
  have hsq : Real.sqrt (localEnergy c a B) ^ 2 = localEnergy c a B := Real.sq_sqrt hE0
  have hW0 : 0 ≤ weightedCurlNormSq (ballIndicator c (15 / 2) 0) (B 0) := weightedCurlNormSq_nonneg _ _
  have hM0 : 0 ≤ totalMisfit (ballIndicator c (15 / 2)) B := totalMisfit_nonneg _ _
  have hr : ∀ j, 6 + readReach F j ≤ 15 / 2 := by
    intro j
    have h1 := readReach_le (F := F) hL4 j
    have h2 : 4 / (F.blockSide : ℝ) ≤ 1 := by
      rw [div_le_one hLp]
      linarith
    linarith
  have hnE : localEnergy c a B = weightedCurlNormSq (ballIndicator c (15 / 2) 0) (B 0) + a * totalMisfit (ballIndicator c (15 / 2)) B := rfl
  refine ⟨Real.sqrt_nonneg _, ?_, ?_, ?_, ?_⟩
  · rw [hsq, hnE]
    have := weightedCurlNormSq_mono (fun x => nearWeight_sq_le_ballIndicator_sq c (r := 6) (r' := 15 / 2) (j := 0) x (hr 0)) (B 0)
    nlinarith
  · rw [hsq, hnE]
    have : totalMisfit (nearWeight c 6) B ≤ totalMisfit (ballIndicator c (15 / 2)) B :=
      Finset.sum_le_sum fun j _ => weightedNormSq_mono (fun x => nearWeight_sq_le_ballIndicator_sq c x (hr _)) _
    nlinarith
  · rw [hsq, hnE]
    have h1 : weightedCurlNormSq (ballIndicator c 5 0) (B 0) ≤ weightedCurlNormSq (ballIndicator c (15 / 2) 0) (B 0) :=
      weightedCurlNormSq_mono (fun x => ballIndicator_sq_mono c (by norm_num) x) _
    have h2 : ∑ j ∈ Finset.range F.depth, weightedNormSq (ballIndicator c 5 (j + 1)) (chainMisfit B j) ≤
        totalMisfit (ballIndicator c (15 / 2)) B := by
      unfold totalMisfit
      calc _ ≤ ∑ j ∈ Finset.range F.depth, weightedNormSq (ballIndicator c (15 / 2) (j + 1)) (chainMisfit B j) :=
            Finset.sum_le_sum fun j _ => weightedNormSq_mono (fun x => ballIndicator_sq_mono c (by norm_num) x) _
        _ ≤ _ := by
            show _ ≤ ∑ j ∈ Finset.range (F.depth + 1), _
            rw [Finset.sum_range_succ]
            have := weightedNormSq_nonneg (ballIndicator c (15 / 2) (F.depth + 1)) (chainMisfit B F.depth)
            linarith
    nlinarith
  · rw [hsq, hnE]
    have : weightedNormSq (ballIndicator c (15 / 2) F.top) (chainMisfit B F.depth) ≤ totalMisfit (ballIndicator c (15 / 2)) B := by
      unfold totalMisfit
      exact Finset.single_le_sum (f := fun j => weightedNormSq (ballIndicator c (15 / 2) (j + 1)) (chainMisfit B j))
        (fun _ _ => weightedNormSq_nonneg _ _) (Finset.mem_range.2 (by unfold BlockFrame.top; omega))
    nlinarith
set_option maxHeartbeats 1000000 in
theorem energyBelowTop_add_testForm_le (hL : Odd F.blockSide) (hs : ∀ i, 0 < F.extent i) (h8 : 8 ≤ F.blockSide) (c : Fin 4 → ℝ) {a E : ℝ}
    (ha : 1 ≤ a) (B : FormChain F) (i : Fin 4) (m : ℕ) (hm : m ≤ F.blockSide) (hE : LocalEnergyBounds c a B E) :
    energyBelowTop a (fun j => B j + testForm (cutoff c) (shiftDifference B i m) j) ≤
      energyBelowTop a B + 49 * ((m : ℝ) / F.blockSide) * E ^ 2 := by
  have hLp : (0 : ℝ) < F.blockSide := by exact_mod_cast hL.pos
  have ha0 : (0 : ℝ) ≤ a := by linarith
  set r : ℝ := (m : ℝ) / F.blockSide with hr
  have hr0 : 0 ≤ r := by positivity
  have hr1 : r ≤ 1 := by
    rw [hr, div_le_one hLp]
    exact_mod_cast hm
  have hE0 := hE.nonneg
  set Uc := shiftDifference B i m with hUc
  set CC := testForm (cutoff c) Uc with hCC
  have hb := sum_sq_plaquetteCurl_add_cutoff_le hL hs h8 c i m hm (B 0) (Uc 0) (fun x k l => plaquetteCurl_shiftDifference B i m 0 x k l)
  set V := weightedNormSq (nearWeight c 5 0) (Uc 0) with hV
  set A := weightedCurlNormSq (nearWeight c 6 0) (B 0) with hA
  have hV0 : 0 ≤ V := weightedNormSq_nonneg _ _
  set H : ℝ := ((m * F.blockSide ^ F.depth : ℕ) : ℝ) with hH
  have hHN : H / (cellSide F : ℝ) = r := by
    rw [hH, hr]
    push_cast
    have : (F.blockSide : ℝ) ^ F.top = (F.blockSide : ℝ) ^ F.depth * F.blockSide := by
      unfold BlockFrame.top
      rw [pow_succ]
    rw [this]
    field_simp
  have hnmV : Real.sqrt V ≤ 2 * H * E := by
    have h1 := weightedNorm_shiftDifference_zero_le hL hs c B i m hm
    have h2 : Real.sqrt A ≤ E := by
      rw [show E = Real.sqrt (E ^ 2) by rw [Real.sqrt_sq hE0]]
      exact Real.sqrt_le_sqrt hE.curl_near
    exact h1.trans (mul_le_mul_of_nonneg_left h2 (by positivity))
  have hV2 : V ≤ (2 * H * E) ^ 2 := by
    have := pow_le_pow_left₀ (Real.sqrt_nonneg V) hnmV 2
    rwa [Real.sq_sqrt hV0] at this
  have hVN : 6 * V / (cellSide F : ℝ) ^ 2 ≤ 24 * r ^ 2 * E ^ 2 := by
    rw [div_le_iff₀ (by positivity), ← hHN]
    have e : 24 * (H / (cellSide F : ℝ)) ^ 2 * E ^ 2 * (cellSide F : ℝ) ^ 2 = 6 * (2 * H * E) ^ 2 := by
      field_simp
      ring
    rw [e]
    linarith
  have hs1 : Real.sqrt (2 * A) ≤ 2 * E := by
    rw [show 2 * E = Real.sqrt ((2 * E) ^ 2) by rw [Real.sqrt_sq (by positivity)]]
    refine Real.sqrt_le_sqrt ?_
    have := hE.curl_near
    nlinarith [sq_nonneg E]
  have hs2 : Real.sqrt (6 * V / (cellSide F : ℝ) ^ 2) ≤ 5 * r * E := by
    rw [show 5 * r * E = Real.sqrt ((5 * r * E) ^ 2) by rw [Real.sqrt_sq (by positivity)]]
    refine Real.sqrt_le_sqrt (hVN.trans ?_)
    nlinarith [mul_nonneg (sq_nonneg r) (sq_nonneg E)]
  have hcross : 2 * (Real.sqrt (2 * A) * Real.sqrt (6 * V / (cellSide F : ℝ) ^ 2)) ≤ 20 * r * E ^ 2 := by
    have := mul_le_mul hs1 hs2 (Real.sqrt_nonneg _) (by positivity)
    nlinarith
  have hr2 : 24 * r ^ 2 * E ^ 2 ≤ 24 * r * E ^ 2 := by
    have : r ^ 2 ≤ r := by nlinarith
    have h2 : 0 ≤ E ^ 2 := sq_nonneg E
    nlinarith
  have hmis : ∀ j ∈ Finset.range F.depth, ∑ y ∈ allSites F (j + 1), ∑ k : Fin 4,
        chainMisfit (fun j => B j + CC j) j y k ^ 2 ≤
      (∑ y ∈ allSites F (j + 1), ∑ k : Fin 4, chainMisfit B j y k ^ 2) +
        (m : ℝ) / (2 * F.blockSide) * weightedNormSq (ballIndicator c 5 (j + 1)) (chainMisfit B j) := by
    intro j hj
    have hj' : j + 1 ≤ F.depth := Finset.mem_range.1 hj
    have hform : ∀ y k, chainMisfit (fun j => B j + CC j) j y k =
        (1 - cutoff c (j + 1) y) * chainMisfit B j y k +
          cutoff c (j + 1) y * chainMisfit B j (y + axisOffset (j + 1) i (shiftLength F m (j + 1))) k := by
      intro y k
      rw [chainMisfit_add, Pi.add_apply, Pi.add_apply, chainMisfit_testForm, hUc, chainMisfit_shiftDifference B i m hj']
      simp only [shiftForm, Pi.sub_apply]
      ring
    simp only [hform]
    rw [Finset.sum_comm, Finset.sum_comm (s := allSites F (j + 1)) (t := Finset.univ)]
    unfold weightedNormSq
    rw [Finset.sum_comm (s := allSites F (j + 1)) (t := Finset.univ), Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_le_sum fun k _ => sum_sq_cutoff_mix_le hL hs h8 hj' c i m hm (fun y => chainMisfit B j y k)
  unfold energyBelowTop
  have e0 : (fun j => B j + CC j) 0 = B 0 + fun x k => cutoff c 0 x * Uc 0 x k := rfl
  simp only [e0]
  have hsum := Finset.sum_le_sum hmis
  rw [Finset.sum_add_distrib, ← Finset.mul_sum] at hsum
  have hlow := hE.below_ball
  have h5 : (m : ℝ) / (2 * F.blockSide) = r / 2 := by
    rw [hr]
    field_simp
  rw [h5] at hb hsum
  have hfin : r / 2 * weightedCurlNormSq (ballIndicator c 5 0) (B 0) +
      a * (r / 2 * ∑ j ∈ Finset.range F.depth, weightedNormSq (ballIndicator c 5 (j + 1)) (chainMisfit B j)) ≤ r / 2 * E ^ 2 := by
    have := mul_le_mul_of_nonneg_left hlow (by positivity : (0 : ℝ) ≤ r / 2)
    nlinarith
  have hmul := mul_le_mul_of_nonneg_left hsum ha0
  rw [mul_add] at hmul
  have hp := mul_nonneg hr0 (sq_nonneg E)
  linarith
theorem mul_eq_zero_of_weightedNormSq_eq_zero {j : ℕ} {u : F.Site j → ℝ} {X : LevelForm F j} (h : weightedNormSq u X = 0) (x : F.Site j)
    (hx : x ∈ allSites F j) (k : Fin 4) : u x * X x k = 0 := by
  unfold weightedNormSq at h
  have h1 := (Finset.sum_eq_zero_iff_of_nonneg (fun x _ => Finset.sum_nonneg fun _ _ => sq_nonneg _)).1 h x hx
  have h2 := (Finset.sum_eq_zero_iff_of_nonneg (fun _ _ => sq_nonneg _)).1 h1 k (Finset.mem_univ k)
  exact pow_eq_zero_iff (by norm_num) |>.1 h2
theorem belowTopWeight_depth : belowTopWeight (F := F) F.depth = fun _ => 1 := by
  funext x
  unfold belowTopWeight
  rw [if_pos le_rfl]
theorem lineAverage_testForm_eq_zero_of_far (hL : Odd F.blockSide) (hs : ∀ i, 0 < F.extent i) (h8 : 8 ≤ F.blockSide) (c : Fin 4 → ℝ) (X : FormChain F)
    (y : F.Cell) (hy : 15 / 2 < distFromPoint c y) (k : Fin 4) : lineAverage (testForm (cutoff c) X F.depth) y k = 0 := by
  have hfar := weightedNorm_farWeight_testDefect_cutoff_eq_zero hL hs h8 c X (j := F.depth) le_rfl
  have hz : weightedNormSq (farWeight c (9 / 2) F.depth) (testDefect (cutoff c) X F.depth) = 0 := by
    have := weightedNorm_sq (farWeight c (9 / 2) F.depth) (testDefect (cutoff c) X F.depth)
    rw [hfar] at this
    simpa using this.symm
  have hn : F.depth + 1 ≤ F.top := le_rfl
  have hreach0 : readReach F F.depth = 0 := by
    unfold readReach
    simp
  have hp : ∀ p : F.Site F.depth, 9 / 2 < distFromPoint c p → ∀ k, testForm (cutoff c) X F.depth p k = 0 := by
    intro p hp k
    have hmem := mem_allSites hL hs (j := F.depth) (by unfold BlockFrame.top; omega) p
    have h1 := mul_eq_zero_of_weightedNormSq_eq_zero hz p hmem k
    have h2 : farWeight c (9 / 2) F.depth p = 1 := by
      unfold farWeight
      rw [if_pos ⟨le_rfl, by rw [hreach0]; linarith⟩]
    rw [h2, one_mul] at h1
    have h3 : testDefect (cutoff c) X F.depth p k = testForm (cutoff c) X F.depth p k - cutoff c F.depth p * X F.depth p k := rfl
    rw [h3, cutoff_eq_zero c p (by linarith), zero_mul, sub_zero] at h1
    exact h1
  have e : lineAverage (testForm (cutoff c) X F.depth) y k = (1 / (F.blockSide : ℝ) ^ 4) * ∑ h ∈ centredCube F.blockSide, ∑ l ∈ Finset.range F.blockSide,
      testForm (cutoff c) X F.depth (BlockAverages.refineSite y + siteOfCoords F.depth h + axisOffset F.depth k (l : ℤ)) k := rfl
  rw [e]
  have z : ∀ h ∈ centredCube F.blockSide, ∀ l ∈ Finset.range F.blockSide,
      testForm (cutoff c) X F.depth (BlockAverages.refineSite y + siteOfCoords F.depth h + axisOffset F.depth k (l : ℤ)) k = 0 := by
    intro h hh l hl
    refine hp _ ?_ k
    have hread := abs_distFromPoint_read_sub_le hL hs hn y c k k h hh l 0 hl (Finset.mem_range.2 hL.pos)
    simp only [Nat.cast_zero, axisOffset_zero, add_zero] at hread
    have e1 : F.top - F.depth = 1 := by
      unfold BlockFrame.top
      omega
    rw [e1, pow_one] at hread
    have e2 : 3 * (F.blockSide : ℝ) / (F.blockSide : ℝ) = 3 := by
      field_simp
    rw [e2] at hread
    have := (abs_le.1 hread).1
    linarith
  rw [Finset.sum_eq_zero fun h hh => Finset.sum_eq_zero fun l hl => z h hh l hl, mul_zero]
theorem energyBelowTop_testForm_le (hL : Odd F.blockSide) (hs : ∀ i, 0 < F.extent i) (h8 : 8 ≤ F.blockSide) (c : Fin 4 → ℝ) {a E : ℝ}
    (ha : 1 ≤ a) {cc : F.Site F.top × Fin 4} {B : FormChain F} (hB : IsFlatChain a cc B) (i : Fin 4) (m : ℕ)
    (hm1 : 1 ≤ m) (hm : m ≤ F.blockSide) (hE : LocalEnergyBounds c a B E) :
    energyBelowTop a (testForm (cutoff c) (shiftDifference B i m)) ≤
      (49 + 34 * Real.sqrt a) * ((m : ℝ) / F.blockSide) * E ^ 2 := by
  have hL4 : 4 ≤ F.blockSide := by omega
  have hL1 : (1 : ℝ) ≤ F.blockSide := by exact_mod_cast hL.pos
  have ha0 : (0 : ℝ) < a := by linarith
  set r : ℝ := (m : ℝ) / F.blockSide with hr
  have hr0 : 0 ≤ r := by positivity
  have hE0 := hE.nonneg
  set Uc := shiftDifference B i m with hUc
  set CC := testForm (cutoff c) Uc with hCC
  have hmix := energyBelowTop_add_testForm_le hL hs h8 c ha B i m hm hE
  have hadd := energyBelowTop_add a B CC
  have hpol := IsFlatChain.polarBelowTop_add_eq_zero hB CC
  set T := ∑ y ∈ allSites F F.top, ∑ k : Fin 4, chainMisfit B F.depth y k * lineAverage (CC F.depth) y k with hT
  have hs1 : Real.sqrt (weightedCurlNormSq (nearWeight c 6 0) (B 0)) ≤ E := by
    rw [show E = Real.sqrt (E ^ 2) by rw [Real.sqrt_sq hE0]]
    exact Real.sqrt_le_sqrt hE.curl_near
  have hs2 : Real.sqrt (totalMisfit (nearWeight c 6) B) ≤ E := by
    rw [show E = Real.sqrt (E ^ 2) by rw [Real.sqrt_sq hE0]]
    exact Real.sqrt_le_sqrt hE.misfit_near
  set H : ℝ := ((m * F.blockSide ^ F.depth : ℕ) : ℝ) with hH
  have hX : ∀ j, j ≤ F.depth → (F.blockSide : ℝ) ^ j * weightedNorm (nearWeight c 5 j) (Uc j) ≤ 5 * H * E :=
    fun j hj => pow_mul_weightedNorm_shiftDifference_le hL hs hL4 c B i m hm1 hm E hE0 hs1 hs2 hj
  have hg := weightedNorm_testDefect_cutoff_le hL hs hL4 c Uc (5 * H * E) (by positivity) hX (j := F.depth) le_rfl
  have hHN : H / (cellSide F : ℝ) = r := by
    rw [hH, hr]
    push_cast
    have : (F.blockSide : ℝ) ^ F.top = (F.blockSide : ℝ) ^ F.depth * F.blockSide := by
      unfold BlockFrame.top
      rw [pow_succ]
    rw [this]
    field_simp
  have hg2 : weightedNorm (belowTopWeight F.depth) (testDefect (cutoff c) Uc F.depth) ≤ 12 * r * E := by
    refine hg.trans ?_
    have : 5 * H * E / (cellSide F : ℝ) = 5 * r * E := by
      rw [← hHN]
      ring
    rw [this]
    nlinarith [mul_nonneg hr0 hE0]
  have hCt : weightedNorm (belowTopWeight F.depth) (CC F.depth) ≤ 17 * (m : ℝ) * E := by
    have e : CC F.depth = weightedChain (cutoff c) Uc F.depth + testDefect (cutoff c) Uc F.depth := by
      funext x k
      simp only [testDefect, Pi.add_apply, Pi.sub_apply, add_sub_cancel]
      rfl
    rw [e]
    refine (weightedNorm_add_le _ _ _).trans ?_
    have w1 : weightedNorm (belowTopWeight F.depth) (weightedChain (cutoff c) Uc F.depth) ≤ weightedNorm (nearWeight c 5 F.depth) (Uc F.depth) := by
      refine Real.sqrt_le_sqrt ?_
      unfold weightedNormSq
      refine Finset.sum_le_sum fun x _ => Finset.sum_le_sum fun k _ => ?_
      have hl : belowTopWeight (F := F) F.depth x = 1 := by
        unfold belowTopWeight
        rw [if_pos le_rfl]
      rw [hl, one_mul]
      unfold weightedChain
      by_cases hx : distFromPoint c x ≤ 4
      · have e1 : nearWeight c 5 F.depth x = 1 := by
          unfold nearWeight
          have := readReach_nonneg (F := F) hL4 F.depth
          rw [if_pos ⟨le_rfl, by linarith⟩]
        rw [e1, one_mul, mul_pow]
        have h0 := cutoff_nonneg c x
        have h1 := cutoff_le_one c x
        have : cutoff c F.depth x ^ 2 ≤ 1 := by nlinarith
        nlinarith [sq_nonneg (Uc F.depth x k)]
      · push Not at hx
        rw [cutoff_eq_zero c x hx.le]
        simp only [zero_mul, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]
        exact sq_nonneg _
    have w2 : weightedNorm (nearWeight c 5 F.depth) (Uc F.depth) ≤ 5 * (m : ℝ) * E := by
      have := hX F.depth le_rfl
      have hp : 0 < (F.blockSide : ℝ) ^ F.depth := by positivity
      have e2 : 5 * H * E = (F.blockSide : ℝ) ^ F.depth * (5 * (m : ℝ) * E) := by
        rw [hH]
        push_cast
        ring
      rw [e2] at this
      exact le_of_mul_le_mul_left this hp
    have hrm : r ≤ m := by
      rw [hr]
      exact div_le_self (by positivity) hL1
    nlinarith [mul_nonneg hr0 hE0]
  have hQ : weightedNorm (fun _ => (1 : ℝ)) (lineAverage (CC F.depth)) ≤ (1 / (F.blockSide : ℝ)) * (17 * (m : ℝ) * E) := by
    have h1 := weightedNormSq_lineAverage_le hL hs (j := F.depth) le_rfl (fun _ => (1 : ℝ)) (belowTopWeight F.depth) 1 zero_le_one (CC F.depth)
      (fun k y h hh l hl => by
        unfold belowTopWeight
        simp)
    have h2 : weightedNorm (fun _ => (1 : ℝ)) (lineAverage (CC F.depth)) ≤ (1 / (F.blockSide : ℝ)) * weightedNorm (belowTopWeight F.depth) (CC F.depth) := by
      unfold weightedNorm
      refine (Real.sqrt_le_sqrt h1).trans (le_of_eq ?_)
      rw [Real.sqrt_mul (by positivity), show (1 / (F.blockSide : ℝ) ^ 2) = (1 / (F.blockSide : ℝ)) ^ 2 by field_simp,
        Real.sqrt_sq (by positivity)]
    exact h2.trans (mul_le_mul_of_nonneg_left hCt (by positivity))
  set Y := weightedNorm (ballIndicator c (15 / 2) F.top) (chainMisfit B F.depth) with hY
  have hY0 : 0 ≤ Y := weightedNorm_nonneg _ _
  have hTle : |T| ≤ Y * ((1 / (F.blockSide : ℝ)) * (17 * (m : ℝ) * E)) := by
    have hp := abs_weightedInner_le (ballIndicator c (15 / 2) F.top) (fun _ => (1 : ℝ)) (chainMisfit B F.depth) (lineAverage (CC F.depth))
    have e : T = ∑ x ∈ allSites F F.top, ∑ k : Fin 4, (ballIndicator c (15 / 2) F.top x * chainMisfit B F.depth x k) *
        (1 * lineAverage (CC F.depth) x k) := by
      refine Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun k _ => ?_
      by_cases hy : distFromPoint c y ≤ 15 / 2
      · have : ballIndicator c (15 / 2) F.top y = 1 := by
          unfold ballIndicator
          rw [if_pos hy]
        rw [this]
        ring
      · push Not at hy
        rw [lineAverage_testForm_eq_zero_of_far hL hs h8 c Uc y hy k]
        ring
    rw [e]
    exact hp.trans (mul_le_mul_of_nonneg_left hQ hY0)
  set Ra := Real.sqrt a with hRa
  have hRa2 : Ra ^ 2 = a := Real.sq_sqrt ha0.le
  have haY : a * Y ≤ Ra * E := by
    have h2 : (a * Y) ^ 2 ≤ (Ra * E) ^ 2 := by
      rw [mul_pow, mul_pow, hRa2, hY, weightedNorm_sq]
      have := hE.top_ball
      nlinarith
    exact abs_le_of_sq_le_sq' h2 (by positivity) |>.2
  have haT : a * |T| ≤ 17 * Ra * r * E ^ 2 := by
    calc a * |T| ≤ a * (Y * ((1 / (F.blockSide : ℝ)) * (17 * (m : ℝ) * E))) :=
          mul_le_mul_of_nonneg_left hTle ha0.le
      _ = (a * Y) * (17 * r * E) := by
          rw [hr]
          field_simp
      _ ≤ (Ra * E) * (17 * r * E) := mul_le_mul_of_nonneg_right haY (by positivity)
      _ = _ := by ring
  have hfin : energyBelowTop a CC = energyBelowTop a (fun j => B j + CC j) - energyBelowTop a B + 2 * (a * T) := by
    rw [hadd]
    linarith
  rw [hfin]
  have hTT := le_abs_self T
  have : a * T ≤ a * |T| := mul_le_mul_of_nonneg_left hTT ha0.le
  nlinarith
theorem weightedCurlNormSq_depth_le (hL : Odd F.blockSide) (hs : ∀ i, 0 < F.extent i) (h3 : 3 ≤ F.blockSide) {a : ℝ} (ha : 1 ≤ a) (C : FormChain F) :
    weightedCurlNormSq (fun _ => (1 : ℝ)) (C F.depth) ≤ 432 * energyBelowTop a C := by
  have htn : F.depth ≤ F.top := by
    unfold BlockFrame.top
    omega
  have h1 : weightedCurlNormSq (fun _ => (1 : ℝ)) (C F.depth) ≤ 2 * weightedCurlNormSq (fun _ => (1 : ℝ)) (iteratedLineAverage (C 0) F.depth) +
      2 * weightedCurlNormSq (fun _ => (1 : ℝ)) (chainDefect C F.depth) := by
    unfold weightedCurlNormSq
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun x _ => ?_
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun e _ => ?_
    have e1 : plaquetteCurl (chainDefect C F.depth) x e.1 e.2 = plaquetteCurl (iteratedLineAverage (C 0) F.depth) x e.1 e.2 - plaquetteCurl (C F.depth) x e.1 e.2 := by
      unfold chainDefect
      exact plaquetteCurl_sub _ _ _ _ _
    rw [e1]
    simp only [one_mul]
    nlinarith [sq_nonneg (plaquetteCurl (iteratedLineAverage (C 0) F.depth) x e.1 e.2 + (plaquetteCurl (iteratedLineAverage (C 0) F.depth) x e.1 e.2 -
      plaquetteCurl (C F.depth) x e.1 e.2))]
  have h2 : weightedCurlNormSq (fun _ => (1 : ℝ)) (iteratedLineAverage (C 0) F.depth) ≤
      ∑ x ∈ allSites F 0, ∑ e ∈ orientedPlanes, plaquetteCurl (C 0) x e.1 e.2 ^ 2 := by
    have := weightedCurlNormSq_iteratedLineAverage_le hL hs isReadMonotone_belowTopWeight (C 0) htn
    rw [belowTopWeight_depth] at this
    refine this.trans (le_of_eq ?_)
    unfold weightedCurlNormSq belowTopWeight
    simp
  have h3' : weightedCurlNormSq (fun _ => (1 : ℝ)) (chainDefect C F.depth) ≤ 96 * (9 / 4 * totalMisfit belowTopWeight C) := by
    refine (weightedCurlNormSq_one_le hL hs htn _).trans (mul_le_mul_of_nonneg_left ?_ (by norm_num))
    have g := weightedNorm_chainDefect_le hL hs h3 isReadMonotone_belowTopWeight C htn
    rw [belowTopWeight_depth] at g
    have g2 := pow_le_pow_left₀ (weightedNorm_nonneg _ _) g 2
    rw [weightedNorm_sq, mul_pow, Real.sq_sqrt (totalMisfit_nonneg _ _)] at g2
    refine g2.trans (le_of_eq ?_)
    norm_num
  have h4 : totalMisfit belowTopWeight C = ∑ j ∈ Finset.range F.depth, ∑ y ∈ allSites F (j + 1), ∑ i : Fin 4, chainMisfit C j y i ^ 2 := by
    unfold totalMisfit
    show ∑ j ∈ Finset.range (F.depth + 1), _ = _
    rw [Finset.sum_range_succ]
    have e1 : weightedNormSq (belowTopWeight (F.depth + 1)) (chainMisfit C F.depth) = 0 := by
      unfold weightedNormSq belowTopWeight
      simp
    rw [e1, add_zero]
    refine Finset.sum_congr rfl fun j hj => ?_
    have hj' := Finset.mem_range.1 hj
    unfold weightedNormSq belowTopWeight
    simp only [show j + 1 ≤ F.depth by omega, if_true, one_mul]
  have hb0 : 0 ≤ ∑ x ∈ allSites F 0, ∑ e ∈ orientedPlanes, plaquetteCurl (C 0) x e.1 e.2 ^ 2 :=
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hm0 : 0 ≤ ∑ j ∈ Finset.range F.depth, ∑ y ∈ allSites F (j + 1), ∑ i : Fin 4, chainMisfit C j y i ^ 2 :=
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _
  unfold energyBelowTop
  rw [h4] at h3'
  nlinarith
def shiftConstant (a : ℝ) : ℝ := 864 * (49 + 34 * Real.sqrt a) + 27648
theorem sum_sq_ballIndicator_curl_shift_sub_le (hL : Odd F.blockSide) (hs : ∀ i, 0 < F.extent i) (h8 : 8 ≤ F.blockSide) (c : Fin 4 → ℝ) {a : ℝ} (ha : 1 ≤ a)
    {cc : F.Site F.top × Fin 4} {B : FormChain F} (hB : IsFlatChain a cc B) (i : Fin 4) (m : ℕ)
    (hm1 : 1 ≤ m) (hm : m ≤ F.blockSide) :
    ∑ p ∈ allSites F F.depth, ∑ e ∈ orientedPlanes, (ballIndicator c (3 / 2) F.depth p *
        (plaquetteCurl (B F.depth) (p + axisOffset F.depth i (m : ℤ)) e.1 e.2 - plaquetteCurl (B F.depth) p e.1 e.2)) ^ 2 ≤
      shiftConstant a * ((m : ℝ) / F.blockSide) * localEnergy c a B := by
  have hL4 : 4 ≤ F.blockSide := by omega
  have h3 : 3 ≤ F.blockSide := by omega
  have hLr : (8 : ℝ) ≤ F.blockSide := by exact_mod_cast h8
  have hLp : (0 : ℝ) < F.blockSide := by linarith
  have ha0 : (0 : ℝ) ≤ a := by linarith
  have htn : F.depth ≤ F.top := by
    unfold BlockFrame.top
    omega
  have hE := localEnergyBounds_sqrt h8 c ha B
  set E := Real.sqrt (localEnergy c a B) with hEdef
  have hE0 := hE.nonneg
  have hE2 : E ^ 2 = localEnergy c a B := Real.sq_sqrt (localEnergy_nonneg c ha0 B)
  set r : ℝ := (m : ℝ) / F.blockSide with hr
  have hr0 : 0 ≤ r := by positivity
  have hr1 : r ≤ 1 := by
    rw [hr, div_le_one hLp]
    exact_mod_cast hm
  set Uc := shiftDifference B i m with hUc
  set CC := testForm (cutoff c) Uc with hCC
  set G := testDefect (cutoff c) Uc F.depth with hG
  have hen := energyBelowTop_testForm_le hL hs h8 c ha hB i m hm1 hm hE
  have hct := weightedCurlNormSq_depth_le hL hs h3 ha CC
  have hs1 : Real.sqrt (weightedCurlNormSq (nearWeight c 6 0) (B 0)) ≤ E := by
    rw [show E = Real.sqrt (E ^ 2) by rw [Real.sqrt_sq hE0]]
    exact Real.sqrt_le_sqrt hE.curl_near
  have hs2 : Real.sqrt (totalMisfit (nearWeight c 6) B) ≤ E := by
    rw [show E = Real.sqrt (E ^ 2) by rw [Real.sqrt_sq hE0]]
    exact Real.sqrt_le_sqrt hE.misfit_near
  set H : ℝ := ((m * F.blockSide ^ F.depth : ℕ) : ℝ) with hH
  have hX : ∀ j, j ≤ F.depth → (F.blockSide : ℝ) ^ j * weightedNorm (nearWeight c 5 j) (Uc j) ≤ 5 * H * E :=
    fun j hj => pow_mul_weightedNorm_shiftDifference_le hL hs hL4 c B i m hm1 hm E hE0 hs1 hs2 hj
  have hg := weightedNorm_testDefect_cutoff_le hL hs hL4 c Uc (5 * H * E) (by positivity) hX (j := F.depth) le_rfl
  have hHN : H / (cellSide F : ℝ) = r := by
    rw [hH, hr]
    push_cast
    have : (F.blockSide : ℝ) ^ F.top = (F.blockSide : ℝ) ^ F.depth * F.blockSide := by
      unfold BlockFrame.top
      rw [pow_succ]
    rw [this]
    field_simp
  have hg2 : weightedNorm (fun _ => (1 : ℝ)) G ≤ 12 * r * E := by
    have e : weightedNorm (fun _ => (1 : ℝ)) G = weightedNorm (belowTopWeight F.depth) G := by
      rw [belowTopWeight_depth]
    rw [e]
    refine hg.trans ?_
    have : 5 * H * E / (cellSide F : ℝ) = 5 * r * E := by
      rw [← hHN]
      ring
    rw [this]
    nlinarith [mul_nonneg hr0 hE0]
  have hwG : weightedCurlNormSq (fun _ => (1 : ℝ)) G ≤ 13824 * r * E ^ 2 := by
    have h1 := weightedCurlNormSq_one_le hL hs htn G
    have h2 := pow_le_pow_left₀ (weightedNorm_nonneg _ _) hg2 2
    rw [weightedNorm_sq] at h2
    have h3' : r ^ 2 ≤ r := by nlinarith
    have h4 : (12 * r * E) ^ 2 ≤ 144 * r * E ^ 2 := by
      have := mul_le_mul_of_nonneg_right h3' (sq_nonneg E)
      nlinarith
    linarith
  have hterm : ∀ (p : F.Site F.depth) (e : Fin 4 × Fin 4),
      (ballIndicator c (3 / 2) F.depth p * (plaquetteCurl (B F.depth) (p + axisOffset F.depth i (m : ℤ)) e.1 e.2 - plaquetteCurl (B F.depth) p e.1 e.2)) ^ 2 ≤
      2 * (1 * plaquetteCurl (CC F.depth) p e.1 e.2) ^ 2 + 2 * (1 * plaquetteCurl G p e.1 e.2) ^ 2 := by
    intro p e
    by_cases hp : distFromPoint c p ≤ 3 / 2
    · have hn : ballIndicator c (3 / 2) F.depth p = 1 := by
        unfold ballIndicator
        rw [if_pos hp]
      have hunit : ∀ k, cutoff c F.depth (p + unitStep F.depth k) = 1 := by
        intro k
        refine cutoff_eq_one c _ ?_
        have hM : (F.blockSide : ℝ) ^ (F.top - F.depth) = F.blockSide := by
          have : F.top - F.depth = 1 := by
            unfold BlockFrame.top
            omega
          rw [this, pow_one]
        have hd := abs_distFromPoint_axisOffset_sub_le hL hs p k 1 c (1 / 2) (by norm_num) (by
          rw [hM]
          simp only [Int.cast_one, abs_one]
          rw [div_le_iff₀ hLp]
          linarith)
        have := (abs_le.1 hd).2
        rw [axisOffset_one] at this
        linarith
      have hc0 : cutoff c F.depth p = 1 := cutoff_eq_one c p (by linarith)
      have ecurl : plaquetteCurl (CC F.depth) p e.1 e.2 = plaquetteCurl (Uc F.depth) p e.1 e.2 + plaquetteCurl G p e.1 e.2 := by
        have e1 : CC F.depth = weightedChain (cutoff c) Uc F.depth + G := by
          funext x k
          simp only [hG, testDefect, Pi.add_apply, Pi.sub_apply, add_sub_cancel]
          rfl
        rw [e1, plaquetteCurl_add]
        congr 1
        unfold plaquetteCurl weightedChain
        rw [hc0, hunit, hunit]
        ring
      have eU := plaquetteCurl_shiftDifference B i m F.depth p e.1 e.2
      have hsh : shiftLength F m F.depth = (m : ℤ) := by
        unfold shiftLength
        simp
      rw [hsh] at eU
      rw [hn, one_mul, one_mul, one_mul]
      rw [hUc] at ecurl
      have : plaquetteCurl (B F.depth) (p + axisOffset F.depth i (m : ℤ)) e.1 e.2 - plaquetteCurl (B F.depth) p e.1 e.2 =
          plaquetteCurl (CC F.depth) p e.1 e.2 - plaquetteCurl G p e.1 e.2 := by
        rw [ecurl, eU]
        ring
      rw [this]
      nlinarith [sq_nonneg (plaquetteCurl (CC F.depth) p e.1 e.2 + plaquetteCurl G p e.1 e.2)]
    · have hn : ballIndicator c (3 / 2) F.depth p = 0 := by
        unfold ballIndicator
        rw [if_neg hp]
      rw [hn]
      simp only [zero_mul, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]
      positivity
  have htot : ∑ p ∈ allSites F F.depth, ∑ e ∈ orientedPlanes, (ballIndicator c (3 / 2) F.depth p *
        (plaquetteCurl (B F.depth) (p + axisOffset F.depth i (m : ℤ)) e.1 e.2 - plaquetteCurl (B F.depth) p e.1 e.2)) ^ 2 ≤
      2 * weightedCurlNormSq (fun _ => (1 : ℝ)) (CC F.depth) + 2 * weightedCurlNormSq (fun _ => (1 : ℝ)) G := by
    unfold weightedCurlNormSq
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun p _ => ?_
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_le_sum fun e _ => hterm p e
  refine htot.trans ?_
  rw [← hE2]
  unfold shiftConstant
  nlinarith
end YangMills.Construction.ColdStepAtMirrorFrames
end
