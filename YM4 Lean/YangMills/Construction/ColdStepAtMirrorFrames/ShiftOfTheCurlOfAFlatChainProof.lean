import YangMills.Construction.ColdStepAtMirrorFrames.ShiftOfTheCurlInOneDirection
import YangMills.Construction.ColdStepAtMirrorFrames.ShiftOfTheCurlOfAFlatChain
import YangMills.Construction.ColdStepAtMirrorFrames.SitesCellsAndPositions
import YangMills.Construction.ColdStepAtMirrorFrames.WeightsOfPositionsAtACell
import Mathlib
set_option autoImplicit false
noncomputable section
open YangMills.Construction.BlockAverages
namespace YangMills.Construction.ColdStepAtMirrorFrames
variable {F : BlockFrame}
theorem depthSite_mem_depthBall (hL : Odd F.blockSide) (hs : ∀ i, 0 < F.extent i) (h2 : 2 ≤ F.blockSide)
    (z z' : F.Site F.depth) (hz : siteSupDist z' z ≤ F.blockSide) {j : ℕ} (hj : j ≤ F.top) (x : F.Site j)
    (h : distFromPoint (sitePosition z') x ≤ 15 / 2) :
    depthSite x ∈ depthBall z (9 * F.blockSide) := by
  have hLr : (2 : ℝ) ≤ F.blockSide := by exact_mod_cast h2
  have hLp : (0 : ℝ) < F.blockSide := by linarith
  have htn : F.depth ≤ F.top := by
    unfold BlockFrame.top
    omega
  have hM : (F.blockSide : ℝ) ^ (F.top - F.depth) = F.blockSide := by
    have : F.top - F.depth = 1 := by
      unfold BlockFrame.top
      omega
    rw [this, pow_one]
  set p := depthSite x with hp
  have hpos : distFromPoint (sitePosition z') p ≤ 15 / 2 + 1 / (F.blockSide : ℝ) := by
    by_cases hjt : j ≤ F.depth
    · have e : p = ancestorSite F.depth x := by
        rw [hp]
        unfold depthSite
        rw [if_pos hjt]
      rw [e]
      have := distFromPoint_ancestorSite_le hL hs hjt htn x (sitePosition z')
      rw [hM] at this
      linarith
    · have hjn : j = F.top := by
        unfold BlockFrame.top at hj ⊢
        omega
      subst hjn
      have e : p = refineSite F.depth F.top x := by
        rw [hp]
        unfold depthSite refineSite
        rw [if_neg hjt]
        have : F.top - F.depth = 1 := by
          unfold BlockFrame.top
          omega
        rw [this, pow_one]
      rw [e, distFromPoint_refineSite hL hs htn le_rfl]
      have : 0 ≤ 1 / (F.blockSide : ℝ) := by positivity
      linarith
  have h8 : siteSupDist p z' ≤ 8 * F.blockSide := by
    refine siteSupDist_le_of_distFromPoint hL hs htn p z' _ ?_
    rw [hM]
    push_cast
    have : (15 / 2 + 1 / (F.blockSide : ℝ)) * (F.blockSide : ℝ) = 15 / 2 * F.blockSide + 1 := by
      field_simp
    have := mul_le_mul_of_nonneg_right hpos hLp.le
    nlinarith
  have a1 := distFromPoint_le_add_siteSupDist hL hs p z' (sitePosition z)
  have a2 := distFromPoint_le_add_siteSupDist hL hs z' z (sitePosition z)
  rw [hM] at a1 a2
  have a3 : distFromPoint (sitePosition z) z = 0 := distFromPoint_sitePosition_self z
  have a4 : (siteSupDist z' z : ℝ) / F.blockSide ≤ 1 := by
    rw [div_le_one hLp]
    exact_mod_cast hz
  have a5 : (siteSupDist p z' : ℝ) / F.blockSide ≤ 8 := by
    rw [div_le_iff₀ hLp]
    exact_mod_cast h8
  show siteSupDist p z ≤ 9 * F.blockSide
  refine siteSupDist_le_of_distFromPoint hL hs htn p z _ ?_
  rw [hM]
  push_cast
  have : distFromPoint (sitePosition z) p ≤ 9 := by linarith
  exact mul_le_mul_of_nonneg_right this hLp.le
theorem localEnergy_le_chainEnergyOnSites (hL : Odd F.blockSide) (hs : ∀ i, 0 < F.extent i)
    (h2 : 2 ≤ F.blockSide) {a : ℝ} (ha : 1 ≤ a)
    (z z' : F.Site F.depth) (hz : siteSupDist z' z ≤ F.blockSide) (B : FormChain F) :
    localEnergy (sitePosition z') a B ≤ chainEnergyOnSites a B (depthBall z (9 * F.blockSide)) := by
  classical
  have ha0 : (0 : ℝ) ≤ a := by linarith
  set X := depthBall z (9 * F.blockSide) with hX
  have key : ∀ {j : ℕ} (hj : j ≤ F.top) (g : F.Site j → ℝ), (∀ x, 0 ≤ g x) →
      ∑ x ∈ allSites F j, ballIndicator (sitePosition z') (15 / 2) j x ^ 2 * g x ≤
      ∑ x ∈ (allSites F j).filter (fun x => depthSite x ∈ X), g x := by
    intro j hj g hg
    rw [Finset.sum_filter]
    refine Finset.sum_le_sum fun x _ => ?_
    by_cases h : distFromPoint (sitePosition z') x ≤ 15 / 2
    · have hm := depthSite_mem_depthBall hL hs h2 z z' hz hj x h
      rw [if_pos hm]
      have : ballIndicator (sitePosition z') (15 / 2) j x = 1 := by
        unfold ballIndicator
        rw [if_pos h]
      rw [this]
      simp
    · have : ballIndicator (sitePosition z') (15 / 2) j x = 0 := by
        unfold ballIndicator
        rw [if_neg h]
      rw [this]
      simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_mul]
      split_ifs
      · exact hg x
      · exact le_rfl
  have b0 : weightedCurlNormSq (ballIndicator (sitePosition z') (15 / 2) 0) (B 0) ≤
      ∑ x ∈ (allSites F 0).filter (fun x => depthSite x ∈ X), ∑ e ∈ orientedPlanes,
        plaquetteCurl (B 0) x e.1 e.2 ^ 2 := by
    have := key (j := 0) (Nat.zero_le _) (fun x => ∑ e ∈ orientedPlanes, plaquetteCurl (B 0) x e.1 e.2 ^ 2)
      (fun x => Finset.sum_nonneg fun _ _ => sq_nonneg _)
    refine le_trans (le_of_eq ?_) this
    unfold weightedCurlNormSq
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun e _ => ?_
    ring
  have b1 : totalMisfit (ballIndicator (sitePosition z') (15 / 2)) B ≤ ∑ j ∈ Finset.range F.top,
      ∑ y ∈ (allSites F (j + 1)).filter (fun y => depthSite y ∈ X), ∑ i : Fin 4, chainMisfit B j y i ^ 2 := by
    refine Finset.sum_le_sum fun j hj => ?_
    have hj' := Finset.mem_range.1 hj
    have := key (j := j + 1) (by omega) (fun y => ∑ i : Fin 4, chainMisfit B j y i ^ 2)
      (fun x => Finset.sum_nonneg fun _ _ => sq_nonneg _)
    refine le_trans (le_of_eq ?_) this
    unfold weightedNormSq
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun e _ => ?_
    ring
  have e : chainEnergyOnSites a B X = (∑ x ∈ (allSites F 0).filter (fun x => depthSite x ∈ X),
      ∑ e ∈ orientedPlanes, plaquetteCurl (B 0) x e.1 e.2 ^ 2) + a * ∑ j ∈ Finset.range F.top,
      ∑ y ∈ (allSites F (j + 1)).filter (fun y => depthSite y ∈ X), ∑ i : Fin 4, chainMisfit B j y i ^ 2 := rfl
  rw [e]
  unfold localEnergy
  have := mul_le_mul_of_nonneg_left b1 ha0
  linarith
theorem sum_sq_curl_shift_axis_sub_le (hL : Odd F.blockSide) (hs : ∀ i, 0 < F.extent i) (h8 : 8 ≤ F.blockSide)
    {a : ℝ} (ha : 1 ≤ a) {cc : F.Site F.top × Fin 4} {B : FormChain F} (hB : IsFlatChain a cc B)
    (z s : F.Site F.depth) (hz : siteSupDist (z + s) z ≤ F.blockSide) (i : Fin 4) (m : ℕ) (hm1 : 1 ≤ m)
    (hm : m ≤ F.blockSide) :
    ∑ p ∈ (allSites F F.depth).filter (fun p => siteSupDist p z ≤ F.blockSide), ∑ e ∈ orientedPlanes,
        (plaquetteCurl (B F.depth) (p + s + axisOffset F.depth i (m : ℤ)) e.1 e.2 -
          plaquetteCurl (B F.depth) (p + s) e.1 e.2) ^ 2 ≤
      shiftConstant a * ((m : ℝ) / F.blockSide) * chainEnergyOnSites a B (depthBall z (9 * F.blockSide)) := by
  have hLr : (8 : ℝ) ≤ F.blockSide := by exact_mod_cast h8
  have hLp : (0 : ℝ) < F.blockSide := by linarith
  have htn : F.depth ≤ F.top := by
    unfold BlockFrame.top
    omega
  have hM : (F.blockSide : ℝ) ^ (F.top - F.depth) = F.blockSide := by
    have : F.top - F.depth = 1 := by
      unfold BlockFrame.top
      omega
    rw [this, pow_one]
  set c := sitePosition (z + s) with hc
  have core := sum_sq_ballIndicator_curl_shift_sub_le hL hs h8 c ha hB i m hm1 hm
  have hen := localEnergy_le_chainEnergyOnSites hL hs (by omega) ha z (z + s) hz B
  have hC : 0 ≤ shiftConstant a * ((m : ℝ) / F.blockSide) := by
    unfold shiftConstant
    positivity
  refine le_trans ?_ (mul_le_mul_of_nonneg_left hen hC)
  refine le_trans ?_ core
  set f : F.Site F.depth → ℝ := fun q => ∑ e ∈ orientedPlanes, (ballIndicator c (3 / 2) F.depth q *
      (plaquetteCurl (B F.depth) (q + axisOffset F.depth i (m : ℤ)) e.1 e.2 -
        plaquetteCurl (B F.depth) q e.1 e.2)) ^ 2 with hf
  have hf0 : ∀ q, 0 ≤ f q := fun q => Finset.sum_nonneg fun _ _ => sq_nonneg _
  calc _ = ∑ p ∈ (allSites F F.depth).filter (fun p => siteSupDist p z ≤ F.blockSide), f (p + s) := by
        refine Finset.sum_congr rfl fun p hp => ?_
        have hp2 := (Finset.mem_filter.1 hp).2
        have hn : ballIndicator c (3 / 2) F.depth (p + s) = 1 := by
          unfold ballIndicator
          rw [if_pos]
          have a1 := distFromPoint_le_add_siteSupDist hL hs (p + s) (z + s) c
          have a2 : distFromPoint c (z + s) = 0 := distFromPoint_sitePosition_self _
          have a3 : siteSupDist (p + s) (z + s) = siteSupDist p z := by
            unfold siteSupDist
            congr 1
            funext i
            simp
          rw [a3, hM, a2] at a1
          have a4 : (siteSupDist p z : ℝ) / F.blockSide ≤ 1 := by
            rw [div_le_one hLp]
            exact_mod_cast hp2
          linarith
        simp only [hf, hn, one_mul]
    _ ≤ ∑ p ∈ allSites F F.depth, f (p + s) := by
        refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) ?_
        intro _ _ _
        exact hf0 _
    _ = _ := sum_allSites_add_right hL hs htn s f
def partialOffset (h : Fin 4 → ℤ) (k : ℕ) : Fin 4 → ℤ := fun l => if l.val < k then h l else 0
theorem partialOffset_succ (h : Fin 4 → ℤ) (i : Fin 4) :
    partialOffset h (i.val + 1) = partialOffset h i.val + Pi.single i (h i) := by
  funext l
  unfold partialOffset
  simp only [Pi.add_apply]
  by_cases hl : l = i
  · subst hl
    simp
  · have hv : l.val ≠ i.val := fun e => hl (Fin.ext e)
    simp only [Pi.single_eq_of_ne hl, add_zero]
    by_cases h1 : l.val < i.val
    · rw [if_pos h1, if_pos (by omega)]
    · rw [if_neg h1, if_neg (by omega)]
theorem abs_partialOffset_le (h : Fin 4 → ℤ) (n : ℕ) (hn : ∀ i, |h i| ≤ n) (k : ℕ) (l : Fin 4) :
    |partialOffset h k l| ≤ n := by
  unfold partialOffset
  split_ifs
  · exact hn l
  · simp
theorem siteSupDist_add_siteOfCoords_le (hL : Odd F.blockSide) (hs : ∀ i, 0 < F.extent i)
    (z : F.Site F.depth) (v : Fin 4 → ℤ) (n : ℕ)
    (hv : ∀ l, |v l| ≤ n) : siteSupDist (z + siteOfCoords F.depth v) z ≤ n := by
  refine Finset.sup_le fun i _ => ?_
  have hper : 0 < F.period F.depth i := period_pos hL.pos hs _ i
  have : NeZero (F.period F.depth i) := ⟨hper.ne'⟩
  have e : (z + siteOfCoords F.depth v : F.Site F.depth) i - z i =
      ((v i : ℤ) : ZMod (F.period F.depth i)) := by
    simp [siteOfCoords]
  show (((z + siteOfCoords F.depth v : F.Site F.depth) i - z i).valMinAbs).natAbs ≤ n
  rw [e]
  have hmin : ((((v i : ℤ) : ZMod (F.period F.depth i))).valMinAbs).natAbs ≤ (v i).natAbs := by
    refine ZMod.natAbs_min_of_le_div_two _ _ _ ?_ (ZMod.natAbs_valMinAbs_le _)
    rw [ZMod.coe_valMinAbs]
  have : (v i).natAbs ≤ n := by
    have := hv i
    rw [Int.abs_eq_natAbs] at this
    exact_mod_cast this
  exact hmin.trans this
theorem curlShiftBound_holds : CurlShiftBound := by
  intro a ha
  have hC0 : 0 < shiftConstant a := by
    unfold shiftConstant
    positivity
  refine ⟨16 * shiftConstant a, by positivity, 8, ?_⟩
  intro F c B hL hL8 hcub hB z h n hn hnmax hn1 hnL
  have hs := extent_pos_of_isLargeCubicTorus hcub
  have hLp : (0 : ℝ) < F.blockSide := by exact_mod_cast hL.pos
  set E := chainEnergyOnSites a B (depthBall z (9 * F.blockSide)) with hE
  have hE0 : 0 ≤ E := by
    have ha0 : (0 : ℝ) ≤ a := by linarith
    refine add_nonneg (Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _) ?_
    exact mul_nonneg ha0 (Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ =>
      Finset.sum_nonneg fun _ _ => sq_nonneg _)
  set Fc : F.Site F.depth → Fin 4 × Fin 4 → ℝ := fun p e => plaquetteCurl (B F.depth) p e.1 e.2 with hFc
  set S : ℕ → F.Site F.depth := fun k => siteOfCoords F.depth (partialOffset h k) with hS
  have hdist : ∀ k, siteSupDist (z + S k) z ≤ F.blockSide := fun k =>
    (siteSupDist_add_siteOfCoords_le hL hs z _ n (abs_partialOffset_le h n hn k)).trans hnL
  have hS0 : S 0 = 0 := by
    have : partialOffset h 0 = 0 := by
      funext l
      simp [partialOffset]
    simp only [hS, this, siteOfCoords_zero]
  have hS4 : S 4 = siteOfCoords F.depth h := by
    have : partialOffset h 4 = h := by
      funext l
      simp [partialOffset, l.isLt]
    simp only [hS, this]
  have hstep : ∀ i : Fin 4, S (i.val + 1) = S i.val + axisOffset F.depth i (h i) := by
    intro i
    simp only [hS]
    rw [partialOffset_succ, siteOfCoords_add]
    rfl
  have hone : ∀ i : Fin 4, ∑ p ∈ (allSites F F.depth).filter (fun p => siteSupDist p z ≤ F.blockSide),
      ∑ e ∈ orientedPlanes, (Fc (p + S (i.val + 1)) e - Fc (p + S i.val) e) ^ 2 ≤
        shiftConstant a * ((n : ℝ) / F.blockSide) * E := by
    intro i
    have hb : |h i| ≤ n := hn i
    have hr : 0 ≤ shiftConstant a * ((n : ℝ) / F.blockSide) * E := by positivity
    rcases lt_trichotomy (h i) 0 with hneg | hzero | hpos
    · obtain ⟨m, hm⟩ : ∃ m : ℕ, -(h i) = (m : ℤ) := ⟨(-(h i)).toNat, by omega⟩
      have hm1 : 1 ≤ m := by omega
      have hmn : m ≤ n := by
        rw [abs_of_neg hneg] at hb
        omega
      have core := sum_sq_curl_shift_axis_sub_le hL hs hL8 ha hB z (S (i.val + 1)) (hdist _) i m hm1
        (hmn.trans hnL)
      have e1 : ∀ p, p + S i.val = p + S (i.val + 1) + axisOffset F.depth i (m : ℤ) := by
        intro p
        rw [hstep, add_assoc, add_assoc, ← axisOffset_add, ← hm]
        simp [axisOffset_zero]
      refine le_trans (le_of_eq ?_) (core.trans ?_)
      · refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun e _ => ?_
        simp only [hFc]
        rw [e1 p]
        ring
      · refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ?_ hC0.le) hE0
        refine div_le_div_of_nonneg_right ?_ hLp.le
        exact_mod_cast hmn
    · have e1 : ∀ p, p + S (i.val + 1) = p + S i.val := by
        intro p
        rw [hstep, hzero, axisOffset_zero, add_zero]
      have : ∑ p ∈ (allSites F F.depth).filter (fun p => siteSupDist p z ≤ F.blockSide),
          ∑ e ∈ orientedPlanes, (Fc (p + S (i.val + 1)) e - Fc (p + S i.val) e) ^ 2 = 0 := by
        refine Finset.sum_eq_zero fun p _ => Finset.sum_eq_zero fun e _ => ?_
        rw [e1 p]
        simp
      rw [this]
      exact hr
    · obtain ⟨m, hm⟩ : ∃ m : ℕ, h i = (m : ℤ) := ⟨(h i).toNat, by omega⟩
      have hm1 : 1 ≤ m := by omega
      have hmn : m ≤ n := by
        rw [abs_of_pos hpos] at hb
        omega
      have core := sum_sq_curl_shift_axis_sub_le hL hs hL8 ha hB z (S i.val) (hdist _) i m hm1
        (hmn.trans hnL)
      have e1 : ∀ p, p + S (i.val + 1) = p + S i.val + axisOffset F.depth i (m : ℤ) := by
        intro p
        rw [hstep, hm, add_assoc]
      refine le_trans (le_of_eq ?_) (core.trans ?_)
      · refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun e _ => ?_
        simp only [hFc]
        rw [e1 p]
      · refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ?_ hC0.le) hE0
        refine div_le_div_of_nonneg_right ?_ hLp.le
        exact_mod_cast hmn
  have h0 := hone 0
  have h1 := hone 1
  have h2 := hone 2
  have h3 := hone 3
  simp only [Fin.val_zero, Fin.val_one, Fin.val_two] at h0 h1 h2
  have h3' : ∑ p ∈ (allSites F F.depth).filter (fun p => siteSupDist p z ≤ F.blockSide),
      ∑ e ∈ orientedPlanes, (Fc (p + S 4) e - Fc (p + S 3) e) ^ 2 ≤
        shiftConstant a * ((n : ℝ) / F.blockSide) * E := h3
  have hsum : ∑ p ∈ (sitesOfCells (finiteCells F) F.depth).filter (fun p => siteSupDist p z ≤ F.blockSide),
      ∑ e ∈ orientedPlanes, (plaquetteCurl (B F.depth) (p + siteOfCoords F.depth h) e.1 e.2 -
        plaquetteCurl (B F.depth) p e.1 e.2) ^ 2 ≤
      4 * ((∑ p ∈ (allSites F F.depth).filter (fun p => siteSupDist p z ≤ F.blockSide), ∑ e ∈ orientedPlanes,
        (Fc (p + S (0 + 1)) e - Fc (p + S 0) e) ^ 2) +
      (∑ p ∈ (allSites F F.depth).filter (fun p => siteSupDist p z ≤ F.blockSide), ∑ e ∈ orientedPlanes,
        (Fc (p + S (1 + 1)) e - Fc (p + S 1) e) ^ 2) +
      (∑ p ∈ (allSites F F.depth).filter (fun p => siteSupDist p z ≤ F.blockSide), ∑ e ∈ orientedPlanes,
        (Fc (p + S (2 + 1)) e - Fc (p + S 2) e) ^ 2) +
      (∑ p ∈ (allSites F F.depth).filter (fun p => siteSupDist p z ≤ F.blockSide), ∑ e ∈ orientedPlanes,
        (Fc (p + S 4) e - Fc (p + S 3) e) ^ 2)) := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, Finset.mul_sum]
    refine Finset.sum_le_sum fun p _ => ?_
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, Finset.mul_sum]
    refine Finset.sum_le_sum fun e _ => ?_
    have e0 : Fc (p + S 0) e = plaquetteCurl (B F.depth) p e.1 e.2 := by
      simp only [hFc, hS0, add_zero]
    have e4 : Fc (p + S 4) e = plaquetteCurl (B F.depth) (p + siteOfCoords F.depth h) e.1 e.2 := by
      simp only [hFc, hS4]
    rw [← e0, ← e4]
    set A := Fc (p + S (0 + 1)) e - Fc (p + S 0) e
    set Bd := Fc (p + S (1 + 1)) e - Fc (p + S 1) e
    set Cd := Fc (p + S (2 + 1)) e - Fc (p + S 2) e
    set D := Fc (p + S 4) e - Fc (p + S 3) e
    have tele : Fc (p + S 4) e - Fc (p + S 0) e = A + Bd + Cd + D := by
      simp only [A, Bd, Cd, D]
      ring
    rw [tele]
    nlinarith [sq_nonneg (A - Bd), sq_nonneg (A - Cd), sq_nonneg (A - D), sq_nonneg (Bd - Cd),
      sq_nonneg (Bd - D), sq_nonneg (Cd - D)]
  refine hsum.trans ?_
  have hfin : (16 * shiftConstant a) * ((n : ℝ) / F.blockSide) * E =
      4 * (shiftConstant a * ((n : ℝ) / F.blockSide) * E +
      shiftConstant a * ((n : ℝ) / F.blockSide) * E + shiftConstant a * ((n : ℝ) / F.blockSide) * E +
      shiftConstant a * ((n : ℝ) / F.blockSide) * E) := by ring
  rw [hfin]
  linarith
end YangMills.Construction.ColdStepAtMirrorFrames
end
