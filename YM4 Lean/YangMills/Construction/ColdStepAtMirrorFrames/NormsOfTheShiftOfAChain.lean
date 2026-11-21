import YangMills.Construction.ColdStepAtMirrorFrames.CommutatorOfAMeanAndAWeight
import YangMills.Construction.ColdStepAtMirrorFrames.GaugeOfAFormInOneDirection
import YangMills.Construction.ColdStepAtMirrorFrames.ShiftOfAChainInOneDirection
import Mathlib
set_option autoImplicit false
noncomputable section
open YangMills.Construction.BlockAverages
namespace YangMills.Construction.ColdStepAtMirrorFrames
variable {F : BlockFrame}
theorem sum_sq_mul_le_of_le_sum_translates (hL : Odd F.blockSide) (hs : ∀ i, 0 < F.extent i) (i : Fin 4)
    (u v A G : F.Site 0 → ℝ) (K c : ℝ)
    (hK : 0 ≤ K) (hc : 0 ≤ c) {ι : Type*} (T : Finset ι) (o : ι → ℤ)
    (hw : ∀ x, ∀ m ∈ T, u x ^ 2 ≤ K * v (x + axisOffset 0 i (o m)) ^ 2)
    (hA : ∀ x, |A x| ≤ c * ∑ m ∈ T, |G (x + axisOffset 0 i (o m))|) :
    ∑ x ∈ allSites F 0, (u x * A x) ^ 2 ≤
      c ^ 2 * ((T.card : ℝ) ^ 2 * K) * ∑ x ∈ allSites F 0, (v x * G x) ^ 2 := by
  have h0 : 0 ≤ F.top := Nat.zero_le _
  have hx : ∀ x, (u x * A x) ^ 2 ≤ c ^ 2 * ((T.card : ℝ) * K) *
      ∑ m ∈ T, (v (x + axisOffset 0 i (o m)) * G (x + axisOffset 0 i (o m))) ^ 2 := by
    intro x
    have c1 := sq_sum_le_card_mul_sum_sq (s := T) (f := fun m => |G (x + axisOffset 0 i (o m))|)
    have hs2 : 0 ≤ ∑ m ∈ T, |G (x + axisOffset 0 i (o m))| := Finset.sum_nonneg fun _ _ => abs_nonneg _
    have h2 : A x ^ 2 ≤ (c * ∑ m ∈ T, |G (x + axisOffset 0 i (o m))|) ^ 2 := by
      rw [← sq_abs (A x)]
      exact pow_le_pow_left₀ (abs_nonneg _) (hA x) 2
    calc (u x * A x) ^ 2 = u x ^ 2 * A x ^ 2 := by ring
      _ ≤ u x ^ 2 * (c * ∑ m ∈ T, |G (x + axisOffset 0 i (o m))|) ^ 2 :=
          mul_le_mul_of_nonneg_left h2 (sq_nonneg _)
      _ = c ^ 2 * (u x ^ 2 * (∑ m ∈ T, |G (x + axisOffset 0 i (o m))|) ^ 2) := by ring
      _ ≤ c ^ 2 * (u x ^ 2 * ((T.card : ℝ) * ∑ m ∈ T, |G (x + axisOffset 0 i (o m))| ^ 2)) := by
          refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
          exact mul_le_mul_of_nonneg_left c1 (sq_nonneg _)
      _ = c ^ 2 * ((T.card : ℝ) * ∑ m ∈ T, u x ^ 2 * G (x + axisOffset 0 i (o m)) ^ 2) := by
          have e : u x ^ 2 * ((T.card : ℝ) * ∑ m ∈ T, |G (x + axisOffset 0 i (o m))| ^ 2) =
              (T.card : ℝ) * ∑ m ∈ T, u x ^ 2 * G (x + axisOffset 0 i (o m)) ^ 2 := by
            rw [mul_left_comm, Finset.mul_sum]
            congr 1
            refine Finset.sum_congr rfl fun m _ => ?_
            rw [sq_abs]
          rw [e]
      _ ≤ c ^ 2 * ((T.card : ℝ) * ∑ m ∈ T, K * (v (x + axisOffset 0 i (o m)) * G (x + axisOffset 0 i (o m))) ^ 2) := by
          refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
          refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun m hm => ?_) (by positivity)
          rw [mul_pow, ← mul_assoc]
          exact mul_le_mul_of_nonneg_right (hw x m hm) (sq_nonneg _)
      _ = _ := by
          rw [← Finset.mul_sum]
          ring
  calc _ ≤ ∑ x ∈ allSites F 0, c ^ 2 * ((T.card : ℝ) * K) *
        ∑ m ∈ T, (v (x + axisOffset 0 i (o m)) * G (x + axisOffset 0 i (o m))) ^ 2 :=
        Finset.sum_le_sum fun x _ => hx x
    _ = c ^ 2 * ((T.card : ℝ) * K) * ∑ m ∈ T, ∑ x ∈ allSites F 0, (v x * G x) ^ 2 := by
        rw [← Finset.mul_sum, Finset.sum_comm]
        congr 1
        refine Finset.sum_congr rfl fun m _ => ?_
        exact sum_allSites_add_right hL hs h0 _ (fun x => (v x * G x) ^ 2)
    _ = _ := by
        simp only [Finset.sum_const, nsmul_eq_mul]
        ring
theorem abs_single_div_pow_le {j : ℕ} (hL : Odd F.blockSide) (i l : Fin 4) (s : ℤ) (t : ℝ) (ht0 : 0 ≤ t)
    (hs' : |(s : ℝ)| / (F.blockSide : ℝ) ^ (F.top - j) ≤ t) :
    |(((Pi.single i s : Fin 4 → ℤ) l : ℤ) : ℝ)| / (F.blockSide : ℝ) ^ (F.top - j) ≤ t := by
  by_cases h : l = i
  · subst h
    simpa using hs'
  · simp only [Pi.single_eq_of_ne h, Int.cast_zero, abs_zero, zero_div]
    exact ht0
theorem abs_distFromPoint_axisOffset_sub_le (hL : Odd F.blockSide) (hs : ∀ i, 0 < F.extent i) {j : ℕ}
    (x : F.Site j) (i : Fin 4) (s : ℤ)
    (c : Fin 4 → ℝ) (t : ℝ) (ht0 : 0 ≤ t) (ht : |(s : ℝ)| / (F.blockSide : ℝ) ^ (F.top - j) ≤ t) :
    |distFromPoint c (x + axisOffset j i s) - distFromPoint c x| ≤ t := by
  have a1 := distFromPoint_add_le hL hs x (Pi.single i s) c t fun l =>
    abs_single_div_pow_le hL i l s t ht0 ht
  have a2 := distFromPoint_add_le hL hs (x + axisOffset j i s) (Pi.single i (-s)) c t fun l =>
    abs_single_div_pow_le hL i l (-s) t ht0 (by simpa using ht)
  have e : x + axisOffset j i s + siteOfCoords j (Pi.single i (-s)) = x := by
    have : (siteOfCoords j (Pi.single i (-s)) : F.Site j) = - axisOffset j i s := by
      unfold axisOffset
      rw [← siteOfCoords_neg, Pi.single_neg]
    rw [this, add_neg_cancel_right]
  rw [e] at a2
  have e3 : x + siteOfCoords j (Pi.single i s) = x + axisOffset j i s := rfl
  rw [e3] at a1
  rw [abs_le]
  constructor <;> linarith
theorem abs_distFromPoint_unitStep_sub_le (hL : Odd F.blockSide) (hs : ∀ i, 0 < F.extent i) (x : F.Site 0)
    (k : Fin 4) (c : Fin 4 → ℝ) :
    |distFromPoint c (x + unitStep 0 k) - distFromPoint c x| ≤ 1 / (cellSide F : ℝ) := by
  have hNr : (0 : ℝ) < (cellSide F : ℝ) := by exact_mod_cast cellSide_pos hL
  refine abs_distFromPoint_axisOffset_sub_le hL hs x k 1 c _ (by positivity) ?_
  have e0 : (F.blockSide : ℝ) ^ (F.top - 0) = (cellSide F : ℝ) := by
    push_cast
    rfl
  rw [e0]
  simp
theorem abs_shiftLength_div_pow (hL : Odd F.blockSide) {l : ℕ} (hl : l ≤ F.depth) (m : ℕ) :
    |(shiftLength F m l : ℝ)| / (F.blockSide : ℝ) ^ (F.top - l) = (m : ℝ) / F.blockSide := by
  have hLp : (0 : ℝ) < F.blockSide := by exact_mod_cast hL.pos
  have e : F.top - l = (F.depth - l) + 1 := by
    unfold BlockFrame.top
    omega
  unfold shiftLength
  push_cast
  rw [e, pow_succ, abs_of_nonneg (by positivity)]
  field_simp
theorem abs_distFromPoint_shiftLength_sub_le (hL : Odd F.blockSide) (hs : ∀ i, 0 < F.extent i) {l : ℕ}
    (hl : l ≤ F.depth) (x : F.Site l) (i : Fin 4) (m : ℕ) (c : Fin 4 → ℝ) :
    |distFromPoint c (x + axisOffset l i (shiftLength F m l)) - distFromPoint c x| ≤ (m : ℝ) / F.blockSide := by
  have hLp : (0 : ℝ) < F.blockSide := by exact_mod_cast hL.pos
  exact abs_distFromPoint_axisOffset_sub_le hL hs x i _ c _ (by positivity)
    (le_of_eq (abs_shiftLength_div_pow hL hl m))
theorem weightedNormSq_shiftForm_le (hL : Odd F.blockSide) (hs : ∀ i, 0 < F.extent i) {l : ℕ} (hl : l ≤ F.top)
    (u v : F.Site l → ℝ) (i : Fin 4) (m : ℕ) (X : LevelForm F l)
    (h : ∀ x, u x ^ 2 ≤ v (x + axisOffset l i (shiftLength F m l)) ^ 2) :
    weightedNormSq u (shiftForm i m l X) ≤ weightedNormSq v X := by
  unfold weightedNormSq shiftForm
  calc _ ≤ ∑ x ∈ allSites F l, ∑ k : Fin 4, (v (x + axisOffset l i (shiftLength F m l)) *
          X (x + axisOffset l i (shiftLength F m l)) k) ^ 2 := by
        refine Finset.sum_le_sum fun x _ => Finset.sum_le_sum fun k _ => ?_
        rw [mul_pow, mul_pow]
        exact mul_le_mul_of_nonneg_right (h x) (sq_nonneg _)
    _ = _ := sum_allSites_add_right hL hs hl _ (fun x => ∑ k : Fin 4, (v x * X x k) ^ 2)
theorem weightedNormSq_mono {j : ℕ} {u v : F.Site j → ℝ} (h : ∀ x, u x ^ 2 ≤ v x ^ 2) (X : LevelForm F j) :
    weightedNormSq u X ≤ weightedNormSq v X := by
  unfold weightedNormSq
  refine Finset.sum_le_sum fun x _ => Finset.sum_le_sum fun k _ => ?_
  rw [mul_pow, mul_pow]
  exact mul_le_mul_of_nonneg_right (h x) (sq_nonneg _)
theorem weightedCurlNormSq_mono {j : ℕ} {u v : F.Site j → ℝ} (h : ∀ x, u x ^ 2 ≤ v x ^ 2)
    (X : LevelForm F j) :
    weightedCurlNormSq u X ≤ weightedCurlNormSq v X := by
  unfold weightedCurlNormSq
  refine Finset.sum_le_sum fun x _ => Finset.sum_le_sum fun k _ => ?_
  rw [mul_pow, mul_pow]
  exact mul_le_mul_of_nonneg_right (h x) (sq_nonneg _)
theorem sq_nearWeight_le_of_le (c : Fin 4 → ℝ) {r r' : ℝ} (hr : r ≤ r') {j : ℕ} (x : F.Site j) :
    nearWeight c r j x ^ 2 ≤ nearWeight c r' j x ^ 2 := by
  unfold nearWeight
  by_cases h : j ≤ F.depth ∧ distFromPoint c x ≤ r + readReach F j
  · rw [if_pos h, if_pos ⟨h.1, by linarith [h.2]⟩]
  · rw [if_neg h]
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]
    exact sq_nonneg _
theorem sq_nearWeight_le_of_near (c : Fin 4 → ℝ) {l : ℕ} (x x' : F.Site l)
    (hx : |distFromPoint c x' - distFromPoint c x| ≤ 1) (r r' : ℝ)
    (hr : r + 1 ≤ r') : nearWeight c r l x ^ 2 ≤ nearWeight c r' l x' ^ 2 := by
  unfold nearWeight
  by_cases h : l ≤ F.depth ∧ distFromPoint c x ≤ r + readReach F l
  · rw [if_pos h, if_pos ⟨h.1, by linarith [h.2, (abs_le.1 hx).2]⟩]
  · rw [if_neg h]
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]
    exact sq_nonneg _
theorem weightedNorm_shiftDifference_zero_le (hL : Odd F.blockSide) (hs : ∀ i, 0 < F.extent i)
    (c : Fin 4 → ℝ) (B : FormChain F) (i : Fin 4) (m : ℕ) (hm : m ≤ F.blockSide) :
    weightedNorm (nearWeight c 5 0) (shiftDifference B i m 0) ≤
      2 * ((m * F.blockSide ^ F.depth : ℕ) : ℝ) * Real.sqrt (weightedCurlNormSq (nearWeight c 6 0) (B 0)) := by
  have hLp : 0 < F.blockSide := hL.pos
  set H : ℕ := m * F.blockSide ^ F.depth with hH
  have hHN : H ≤ F.blockSide ^ (F.top - 0) := by
    have : F.top - 0 = F.depth + 1 := by
      unfold BlockFrame.top
      omega
    rw [this, pow_succ, hH, mul_comm]
    exact Nat.mul_le_mul_left _ hm
  have hk : ∀ k, ∑ x ∈ allSites F 0, (nearWeight c 5 0 x * shiftDifference B i m 0 x k) ^ 2 ≤
      (H : ℝ) ^ 2 * weightedCurlNormSq (nearWeight c 6 0) (B 0) := by
    intro k
    have b := sum_sq_mul_le_of_le_sum_translates hL hs i (nearWeight c 5 0) (nearWeight c 6 0)
      (fun x => shiftDifference B i m 0 x k)
      (fun x => plaquetteCurl (B 0) x i k) 1 1 zero_le_one zero_le_one (Finset.range H) (fun l => (l : ℤ))
      (fun x l hl => by
        rw [one_mul]
        have hl' := Finset.mem_range.1 hl
        refine sq_nearWeight_le_of_near c x _ ?_ 5 6 (by norm_num)
        refine abs_distFromPoint_axisOffset_sub_le hL hs x i _ c 1 zero_le_one ?_
        have hMp : (0 : ℝ) < (F.blockSide : ℝ) ^ (F.top - 0) := by positivity
        rw [div_le_one hMp]
        have : ((l : ℕ) : ℝ) ≤ ((F.blockSide ^ (F.top - 0) : ℕ) : ℝ) := by exact_mod_cast (hl'.le.trans hHN)
        push_cast at this
        simpa using this)
      (fun x => by
        rw [shiftDifference_zero_apply, one_mul]
        exact Finset.abs_sum_le_sum_abs _ _)
    rw [Finset.card_range, one_pow, one_mul, mul_one] at b
    exact b.trans (mul_le_mul_of_nonneg_left (sum_sq_plaquetteCurl_le_weightedCurlNormSq _ _ i k) (by positivity))
  have hw : weightedNormSq (nearWeight c 5 0) (shiftDifference B i m 0) ≤
      (2 * (H : ℝ)) ^ 2 * weightedCurlNormSq (nearWeight c 6 0) (B 0) := by
    unfold weightedNormSq
    rw [Finset.sum_comm]
    calc _ ≤ ∑ _k : Fin 4, (H : ℝ) ^ 2 * weightedCurlNormSq (nearWeight c 6 0) (B 0) :=
          Finset.sum_le_sum fun k _ => hk k
      _ = _ := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          push_cast
          ring
  unfold weightedNorm
  refine (Real.sqrt_le_sqrt hw).trans (le_of_eq ?_)
  rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (by positivity)]
theorem totalMisfit_shiftDifference_le (hL : Odd F.blockSide) (hs : ∀ i, 0 < F.extent i) (c : Fin 4 → ℝ)
    (B : FormChain F) (i : Fin 4) (m : ℕ) (hm : m ≤ F.blockSide) :
    totalMisfit (nearWeight c 5) (shiftDifference B i m) ≤ 4 * totalMisfit (nearWeight c 6) B := by
  have hLr : (0 : ℝ) < F.blockSide := by exact_mod_cast hL.pos
  unfold totalMisfit
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun j hj => ?_
  have hj' := Finset.mem_range.1 hj
  by_cases hc : j + 1 ≤ F.depth
  · rw [chainMisfit_shiftDifference B i m hc]
    have a1 : weightedNormSq (nearWeight c 5 (j + 1)) (shiftForm i m (j + 1) (chainMisfit B j)) ≤
        weightedNormSq (nearWeight c 6 (j + 1)) (chainMisfit B j) := by
      refine weightedNormSq_shiftForm_le hL hs (by omega) _ _ i m _ fun x => ?_
      refine sq_nearWeight_le_of_near c x _ ?_ 5 6 (by norm_num)
      refine (abs_distFromPoint_shiftLength_sub_le hL hs hc x i m c).trans ?_
      rw [div_le_one hLr]
      exact_mod_cast hm
    have a2 : weightedNormSq (nearWeight c 5 (j + 1)) (chainMisfit B j) ≤
        weightedNormSq (nearWeight c 6 (j + 1)) (chainMisfit B j) :=
      weightedNormSq_mono (fun x => sq_nearWeight_le_of_le c (by norm_num) x) _
    have a3 : weightedNormSq (nearWeight c 5 (j + 1)) (shiftForm i m (j + 1) (chainMisfit B j) - chainMisfit B j) ≤
        2 * weightedNormSq (nearWeight c 5 (j + 1)) (shiftForm i m (j + 1) (chainMisfit B j)) +
          2 * weightedNormSq (nearWeight c 5 (j + 1)) (chainMisfit B j) := by
      unfold weightedNormSq
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_le_sum fun x _ => ?_
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_le_sum fun k _ => ?_
      simp only [Pi.sub_apply]
      nlinarith [sq_nonneg (nearWeight c 5 (j + 1) x * shiftForm i m (j + 1) (chainMisfit B j) x k +
        nearWeight c 5 (j + 1) x * chainMisfit B j x k)]
    linarith
  · have e : ∀ x : F.Site (j + 1), nearWeight c 5 (j + 1) x = 0 := by
      intro x
      unfold nearWeight
      rw [if_neg]
      exact fun h => hc h.1
    have : weightedNormSq (nearWeight c 5 (j + 1)) (chainMisfit (shiftDifference B i m) j) = 0 := by
      unfold weightedNormSq
      simp [e]
    rw [this]
    exact mul_nonneg (by norm_num) (weightedNormSq_nonneg _ _)
theorem pow_mul_weightedNorm_shiftDifference_le (hL : Odd F.blockSide) (hs : ∀ i, 0 < F.extent i)
    (hL4 : 4 ≤ F.blockSide) (c : Fin 4 → ℝ) (B : FormChain F)
    (i : Fin 4) (m : ℕ) (hm1 : 1 ≤ m) (hm : m ≤ F.blockSide) (E : ℝ) (hE : 0 ≤ E)
    (h1 : Real.sqrt (weightedCurlNormSq (nearWeight c 6 0) (B 0)) ≤ E)
    (h2 : Real.sqrt (totalMisfit (nearWeight c 6) B) ≤ E)
    {j : ℕ} (hj : j ≤ F.depth) :
    (F.blockSide : ℝ) ^ j * weightedNorm (nearWeight c 5 j) (shiftDifference B i m j) ≤
      5 * ((m * F.blockSide ^ F.depth : ℕ) : ℝ) * E := by
  have h3 : 3 ≤ F.blockSide := by omega
  have hLr : (1 : ℝ) ≤ F.blockSide := by exact_mod_cast hL.pos
  have hU := isReadMonotone_nearWeight hL hs hL4 c (5 : ℝ)
  have b := pow_mul_weightedNorm_le hL hs h3 hU (shiftDifference B i m) (j := j) (by unfold BlockFrame.top; omega)
  have b0 := weightedNorm_shiftDifference_zero_le hL hs c B i m hm
  set H : ℝ := ((m * F.blockSide ^ F.depth : ℕ) : ℝ) with hH
  have b1 : Real.sqrt (totalMisfit (nearWeight c 5) (shiftDifference B i m)) ≤ 2 * E := by
    have := Real.sqrt_le_sqrt (totalMisfit_shiftDifference_le hL hs c B i m hm)
    refine this.trans ?_
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_mul (by positivity), Real.sqrt_sq (by norm_num)]
    exact mul_le_mul_of_nonneg_left h2 (by norm_num)
  have b2 : (F.blockSide : ℝ) ^ j ≤ H := by
    have e1 : (F.blockSide : ℝ) ^ j ≤ (F.blockSide : ℝ) ^ F.depth := pow_le_pow_right₀ hLr hj
    have e2 : (F.blockSide : ℝ) ^ F.depth ≤ H := by
      rw [hH]
      push_cast
      have : (1 : ℝ) ≤ m := by exact_mod_cast hm1
      have h0 : (0 : ℝ) ≤ (F.blockSide : ℝ) ^ F.depth := by positivity
      nlinarith
    exact e1.trans e2
  have b3 : 2 * H * Real.sqrt (weightedCurlNormSq (nearWeight c 6 0) (B 0)) ≤ 2 * H * E :=
    mul_le_mul_of_nonneg_left h1 (by positivity)
  have b4 : 3 / 2 * (F.blockSide : ℝ) ^ j * Real.sqrt (totalMisfit (nearWeight c 5) (shiftDifference B i m)) ≤
      3 / 2 * H * (2 * E) := by
    refine mul_le_mul (by linarith) b1 (Real.sqrt_nonneg _) (by positivity)
  nlinarith
theorem weightedNorm_weightCommutator_cutoff_le (hL : Odd F.blockSide) (hs : ∀ i, 0 < F.extent i)
    (hL4 : 4 ≤ F.blockSide) (c : Fin 4 → ℝ) (X : FormChain F)
    {j : ℕ} (hj : j + 1 ≤ F.depth) :
    weightedNorm (belowTopWeight (j + 1)) (weightCommutator (cutoff c) X j) ≤
      3 / 2 / (F.blockSide : ℝ) ^ (F.top - j) * weightedNorm (nearWeight c 5 j) (X j) := by
  have hL4r : (4 : ℝ) ≤ F.blockSide := by exact_mod_cast hL4
  have hjn : j + 1 ≤ F.top := by
    unfold BlockFrame.top
    omega
  have hMpos : (0 : ℝ) < (F.blockSide : ℝ) ^ (F.top - j) := by positivity
  set μ : ℝ := 3 / 2 * (F.blockSide : ℝ) / (F.blockSide : ℝ) ^ (F.top - j) with hμ
  have hreach : 3 * (F.blockSide : ℝ) / (F.blockSide : ℝ) ^ (F.top - j) ≤ 1 := by
    rw [div_le_one hMpos]
    have e : F.top - j = (F.top - j - 2) + 2 := by
      unfold BlockFrame.top
      omega
    rw [e, pow_add]
    have : (1 : ℝ) ≤ (F.blockSide : ℝ) ^ (F.top - j - 2) := one_le_pow₀ (by linarith)
    nlinarith
  have hw : weightedNormSq (belowTopWeight (j + 1)) (weightCommutator (cutoff c) X j) ≤
      μ ^ 2 / (F.blockSide : ℝ) ^ 2 * weightedNormSq (nearWeight c 5 j) (X j) := by
    unfold weightedNormSq
    rw [Finset.sum_comm, Finset.sum_comm (s := allSites F j), Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    have b := sum_sq_lineKernel_le hL hs hjn i (belowTopWeight (j + 1)) (nearWeight c 5 j) (μ ^ 2) (sq_nonneg _)
      (fun x => X j x i)
      (fun y h l => cutoff c j (BlockAverages.refineSite y + siteOfCoords j h + axisOffset j i (l : ℤ)) - cutoff c (j + 1) y)
      (fun y h hh l hl => by
        have hread : |distFromPoint c (BlockAverages.refineSite y + siteOfCoords j h + axisOffset j i (l : ℤ)) -
            distFromPoint c y| ≤ 3 * (F.blockSide : ℝ) / (F.blockSide : ℝ) ^ (F.top - j) := by
          have := abs_distFromPoint_read_sub_le hL hs hjn y c i i h hh l 0 hl (Finset.mem_range.2 hL.pos)
          simpa [axisOffset_zero] using this
        set p := BlockAverages.refineSite y + siteOfCoords j h + axisOffset j i (l : ℤ)
        have e1 : belowTopWeight (F := F) (j + 1) y = 1 := by
          unfold belowTopWeight
          rw [if_pos hj]
        rw [e1, one_pow, one_mul]
        by_cases hp : distFromPoint c p ≤ 5 + readReach F j
        · have e2 : nearWeight c 5 j p = 1 := by
            unfold nearWeight
            rw [if_pos ⟨by omega, hp⟩]
          rw [e2, one_pow, mul_one]
          have h1 := abs_cutoff_sub_le c y p
          rw [← sq_abs]
          refine pow_le_pow_left₀ (abs_nonneg _) (h1.trans ?_) 2
          rw [hμ]
          have e3 : 3 / 2 * (F.blockSide : ℝ) / (F.blockSide : ℝ) ^ (F.top - j) =
              1 / 2 * (3 * (F.blockSide : ℝ) / (F.blockSide : ℝ) ^ (F.top - j)) := by
            ring
          rw [e3]
          exact mul_le_mul_of_nonneg_left hread (by norm_num)
        · push_neg at hp
          have r0 := readReach_nonneg (F := F) hL4 j
          have c1 : cutoff c j p = 0 := cutoff_eq_zero c p (by linarith)
          have c2 : cutoff c (j + 1) y = 0 := cutoff_eq_zero c y (by
            have := (abs_le.1 hread).2
            linarith)
          rw [c1, c2]
          simp only [sub_self, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]
          exact mul_nonneg (sq_nonneg _) (sq_nonneg _))
    simp only [weightCommutator_eq]
    exact b
  unfold weightedNorm
  refine (Real.sqrt_le_sqrt hw).trans (le_of_eq ?_)
  have e : μ ^ 2 / (F.blockSide : ℝ) ^ 2 = (3 / 2 / (F.blockSide : ℝ) ^ (F.top - j)) ^ 2 := by
    rw [hμ]
    field_simp
  rw [e, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (by positivity)]
theorem weightedNorm_testDefect_cutoff_le (hL : Odd F.blockSide) (hs : ∀ i, 0 < F.extent i)
    (hL4 : 4 ≤ F.blockSide) (c : Fin 4 → ℝ) (X : FormChain F)
    (M : ℝ) (hM : 0 ≤ M)
    (hX : ∀ j, j ≤ F.depth → (F.blockSide : ℝ) ^ j * weightedNorm (nearWeight c 5 j) (X j) ≤ M)
    {j : ℕ} (hj : j ≤ F.depth) :
    weightedNorm (belowTopWeight j) (testDefect (cutoff c) X j) ≤ 9 / 4 * (M / (cellSide F : ℝ)) := by
  have hNr : (0 : ℝ) < cellSide F := by exact_mod_cast cellSide_pos hL
  have hL3 : (3 : ℝ) ≤ F.blockSide := by
    have : 3 ≤ F.blockSide := by omega
    exact_mod_cast this
  induction j with
  | zero =>
    rw [testDefect_zero]
    have : weightedNorm (belowTopWeight (F := F) 0) (0 : LevelForm F 0) = 0 := by
      unfold weightedNorm weightedNormSq
      simp
    rw [this]
    positivity
  | succ j ih =>
    have ih' := ih (by omega)
    rw [testDefect_succ]
    refine (weightedNorm_add_le _ _ _).trans ?_
    have hjn : j + 1 ≤ F.top := by
      unfold BlockFrame.top
      omega
    have a1 := weightedNorm_lineAverage_le hL hs isReadMonotone_belowTopWeight hjn (testDefect (cutoff c) X j)
    have a2 := weightedNorm_weightCommutator_cutoff_le hL hs hL4 c X hj
    have hMj : (F.blockSide : ℝ) ^ (F.top - j) * (F.blockSide : ℝ) ^ j = (cellSide F : ℝ) := by
      rw [← pow_add]
      have : F.top - j + j = F.top := by omega
      rw [this]
      push_cast
      rfl
    have a3 : 3 / 2 / (F.blockSide : ℝ) ^ (F.top - j) * weightedNorm (nearWeight c 5 j) (X j) ≤
        3 / 2 * (M / (cellSide F : ℝ)) := by
      have := hX j (by omega)
      have e : 3 / 2 / (F.blockSide : ℝ) ^ (F.top - j) * weightedNorm (nearWeight c 5 j) (X j) =
          3 / 2 * (((F.blockSide : ℝ) ^ j * weightedNorm (nearWeight c 5 j) (X j)) / (cellSide F : ℝ)) := by
        rw [← hMj]
        field_simp
      rw [e]
      refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
      exact div_le_div_of_nonneg_right this hNr.le
    have a4 : (1 / (F.blockSide : ℝ)) * weightedNorm (belowTopWeight j) (testDefect (cutoff c) X j) ≤
        1 / 3 * (9 / 4 * (M / (cellSide F : ℝ))) := by
      refine mul_le_mul ?_ ih' (weightedNorm_nonneg _ _) (by norm_num)
      exact one_div_le_one_div_of_le (by norm_num) hL3
    linarith
theorem weightedNormSq_eq_zero_of_forall {j : ℕ} {u : F.Site j → ℝ} {X : LevelForm F j}
    (h : ∀ x, u x = 0 ∨ ∀ k, X x k = 0) :
    weightedNormSq u X = 0 := by
  unfold weightedNormSq
  refine Finset.sum_eq_zero fun x _ => Finset.sum_eq_zero fun k _ => ?_
  rcases h x with h | h
  · simp [h]
  · simp [h k]
theorem weightedNorm_farWeight_testDefect_cutoff_eq_zero (hL : Odd F.blockSide) (hs : ∀ i, 0 < F.extent i)
    (h8 : 8 ≤ F.blockSide) (c : Fin 4 → ℝ) (X : FormChain F)
    {j : ℕ} (hj : j ≤ F.depth) : weightedNorm (farWeight c (9 / 2) j) (testDefect (cutoff c) X j) = 0 := by
  have hL4 : 4 ≤ F.blockSide := by omega
  have hL8r : (8 : ℝ) ≤ F.blockSide := by exact_mod_cast h8
  have hLp : (0 : ℝ) < F.blockSide := by linarith
  have hU := isReadMonotone_farWeight hL hs hL4 c (9 / 2 : ℝ)
  induction j with
  | zero =>
    rw [testDefect_zero]
    unfold weightedNorm weightedNormSq
    simp
  | succ j ih =>
    have ih' := ih (by omega)
    have hjn : j + 1 ≤ F.top := by
      unfold BlockFrame.top
      omega
    have hcomm : weightedNorm (farWeight c (9 / 2) (j + 1)) (weightCommutator (cutoff c) X j) = 0 := by
      have : weightedNormSq (farWeight c (9 / 2) (j + 1)) (weightCommutator (cutoff c) X j) = 0 := by
        refine weightedNormSq_eq_zero_of_forall fun y => ?_
        by_cases hy : 9 / 2 - readReach F (j + 1) < distFromPoint c y
        · right
          intro k
          rw [weightCommutator_eq]
          have hrr := readReach_le (F := F) hL4 (j + 1)
          have hrj := readReach_le (F := F) hL4 j
          have h41 : 4 / (F.blockSide : ℝ) ≤ 1 / 2 := by
            rw [div_le_iff₀ hLp]
            linarith
          have hst := readReach_succ_add_le hL4 hj
          have c2 : cutoff c (j + 1) y = 0 := cutoff_eq_zero c y (by linarith)
          have z : ∀ h ∈ centredCube F.blockSide, ∀ l ∈ Finset.range F.blockSide,
              (cutoff c j (BlockAverages.refineSite y + siteOfCoords j h + axisOffset j k (l : ℤ)) -
              cutoff c (j + 1) y) * X j (BlockAverages.refineSite y + siteOfCoords j h + axisOffset j k (l : ℤ)) k = 0 := by
            intro h hh l hl
            have hread : |distFromPoint c (BlockAverages.refineSite y + siteOfCoords j h + axisOffset j k (l : ℤ)) -
                distFromPoint c y| ≤ 3 * (F.blockSide : ℝ) / (F.blockSide : ℝ) ^ (F.top - j) := by
              have := abs_distFromPoint_read_sub_le hL hs hjn y c k k h hh l 0 hl (Finset.mem_range.2 hL.pos)
              simpa [axisOffset_zero] using this
            have c1 : cutoff c j (BlockAverages.refineSite y + siteOfCoords j h + axisOffset j k (l : ℤ)) = 0 :=
              cutoff_eq_zero c _ (by
                have := (abs_le.1 hread).1
                linarith)
            rw [c1, c2]
            simp
          rw [Finset.sum_eq_zero fun h hh => Finset.sum_eq_zero fun l hl => z h hh l hl, mul_zero]
        · left
          unfold farWeight
          rw [if_neg]
          exact fun h => hy h.2
      unfold weightedNorm
      rw [this, Real.sqrt_zero]
    have a := weightedNorm_add_le (farWeight c (9 / 2) (j + 1)) (lineAverage (testDefect (cutoff c) X j))
      (weightCommutator (cutoff c) X j)
    have a1 := weightedNorm_lineAverage_le hL hs hU hjn (testDefect (cutoff c) X j)
    rw [ih', mul_zero] at a1
    rw [testDefect_succ]
    have h0 := weightedNorm_nonneg (farWeight c (9 / 2) (j + 1))
      (lineAverage (testDefect (cutoff c) X j) + weightCommutator (cutoff c) X j)
    rw [hcomm] at a
    linarith
end YangMills.Construction.ColdStepAtMirrorFrames
end
