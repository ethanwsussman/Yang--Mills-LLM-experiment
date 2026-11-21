import YangMills.Construction.ColdChainAtEveryLevel.BoundedDifferences
import YangMills.Construction.ColdChainAtEveryLevel.PatchesAndTheGaugeMap
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction.BlockAverages
open YangMills.Construction.GaugeMap YangMills.Construction.LatticeFractionalIntegration YangMills.Construction.FiniteDifferences
variable {F : BlockFrame}
theorem siteOfCoords_add (j : ℕ) (a b : Lattice4) :
    siteOfCoords (F := F) j (a + b) = siteOfCoords j a + siteOfCoords j b := by
  funext i
  simp [siteOfCoords]
theorem siteOfCoords_zero (j : ℕ) : siteOfCoords (F := F) j (0 : Lattice4) = 0 := by
  funext i
  simp [siteOfCoords]
theorem siteOfCoords_neg (j : ℕ) (a : Lattice4) : siteOfCoords (F := F) j (-a) = - siteOfCoords j a := by
  funext i
  simp [siteOfCoords]
theorem siteOfCoords_sub (j : ℕ) (a b : Lattice4) :
    siteOfCoords (F := F) j (a - b) = siteOfCoords j a - siteOfCoords j b := by
  funext i
  simp [siteOfCoords]
theorem siteOfCoords_siteCoords {j : ℕ} (x : F.Site j) : siteOfCoords j (siteCoords x) = x := by
  funext i
  simp [siteOfCoords, siteCoords]
theorem unitStep_eq (j : ℕ) (i : Fin 4) : unitStep (F := F) j i = siteOfCoords j (basisVector i) := rfl
theorem intCast_mul_eq_of_eq {p q : ℕ} {c a b : ℤ} (hq : (q : ℤ) = p * c)
    (h : (a : ZMod p) = (b : ZMod p)) :
    ((c * a : ℤ) : ZMod q) = ((c * b : ℤ) : ZMod q) := by
  rw [ZMod.intCast_eq_intCast_iff_dvd_sub] at h ⊢
  obtain ⟨k, hk⟩ := h
  refine ⟨k, ?_⟩
  rw [hq, ← mul_sub, hk]
  ring
theorem period_zero_eq (j : ℕ) (hj : j ≤ F.top) (i : Fin 4) :
    ((F.period 0 i : ℕ) : ℤ) = (F.period j i : ℕ) * (F.blockSide : ℤ) ^ j := by
  have : F.top - 0 = (F.top - j) + j := by omega
  simp only [BlockFrame.period, this, pow_add]
  push_cast
  ring
theorem period_eq_top_mul (j : ℕ) (hj : j ≤ F.top) (i : Fin 4) :
    ((F.period j i : ℕ) : ℤ) = (F.period F.top i : ℕ) * (F.blockSide : ℤ) ^ (F.top - j) := by
  simp [BlockFrame.period]
theorem period_eq_succ_mul (j : ℕ) (hj : j + 1 ≤ F.top) (i : Fin 4) :
    ((F.period j i : ℕ) : ℤ) = (F.period (j + 1) i : ℕ) * (F.blockSide : ℤ) := by
  have : F.top - j = (F.top - (j + 1)) + 1 := by omega
  simp only [BlockFrame.period, this, pow_succ]
  push_cast
  ring
theorem siteCoords_add_cast {j : ℕ} (x : F.Site j) (a : Lattice4) (i : Fin 4) :
    ((siteCoords (x + siteOfCoords j a) i : ℤ) : ZMod (F.period j i)) =
      ((siteCoords x i + a i : ℤ) : ZMod (F.period j i)) := by
  simp [siteCoords, siteOfCoords]
theorem siteCoords_cast {j : ℕ} (a : Lattice4) (i : Fin 4) :
    ((siteCoords (siteOfCoords (F := F) j a) i : ℤ) : ZMod (F.period j i)) =
      ((a i : ℤ) : ZMod (F.period j i)) := by
  simp [siteCoords, siteOfCoords]
theorem baseSite_add (j : ℕ) (hj : j ≤ F.top) (x : F.Site j) (a : Lattice4) :
    baseSite (x + siteOfCoords j a) =
      baseSite x + siteOfCoords 0 (fun i => (F.blockSide : ℤ) ^ j * a i) := by
  funext i
  have h := intCast_mul_eq_of_eq (period_zero_eq j hj i) (siteCoords_add_cast x a i)
  simp only [baseSite, siteOfCoords, Pi.add_apply] at h ⊢
  rw [h]
  push_cast
  ring
theorem baseSite_refineSite (j : ℕ) (hj : j + 1 ≤ F.top) (y : F.Site (j + 1)) :
    baseSite (refineSite y) = baseSite y := by
  funext i
  have h := intCast_mul_eq_of_eq (period_zero_eq j (by omega) i)
    (siteCoords_cast (F := F) (j := j) (fun i => (F.blockSide : ℤ) * siteCoords y i) i)
  simp only [baseSite, refineSite, siteOfCoords] at h ⊢
  rw [h]
  push_cast
  ring
theorem refineSite_add (j : ℕ) (hj : j + 1 ≤ F.top) (y : F.Site (j + 1)) (a : Lattice4) :
    refineSite (y + siteOfCoords (j + 1) a) =
      refineSite y + siteOfCoords j (fun i => (F.blockSide : ℤ) * a i) := by
  funext i
  have h := intCast_mul_eq_of_eq (period_eq_succ_mul j hj i) (siteCoords_add_cast y a i)
  simp only [refineSite, siteOfCoords, Pi.add_apply] at h ⊢
  rw [h]
  push_cast
  ring
theorem cellCentre_add (j : ℕ) (hj : j ≤ F.top) (z : F.Cell) (a : Lattice4) :
    cellCentre j (z + siteOfCoords F.top a) =
      cellCentre j z + siteOfCoords j (fun i => (F.blockSide : ℤ) ^ (F.top - j) * a i) := by
  funext i
  have h := intCast_mul_eq_of_eq (period_eq_top_mul j hj i) (siteCoords_add_cast z a i)
  simp only [cellCentre, siteOfCoords, Pi.add_apply] at h ⊢
  rw [h]
  push_cast
  ring
theorem cellCentre_top (z : F.Cell) : cellCentre F.top z = z := by
  have : (fun i => (F.blockSide : ℤ) ^ (F.top - F.top) * siteCoords z i) = siteCoords z := by
    funext i; simp
  simp only [cellCentre, this]
  exact siteOfCoords_siteCoords z
theorem baseSite_cellCentre (j : ℕ) (hj : j ≤ F.top) (z : F.Cell) :
    baseSite (cellCentre j z) = cellCentre 0 z := by
  funext i
  have h := intCast_mul_eq_of_eq (period_zero_eq j hj i)
    (siteCoords_cast (F := F) (j := j) (fun i => (F.blockSide : ℤ) ^ (F.top - j) * siteCoords z i) i)
  simp only [baseSite, cellCentre, siteOfCoords] at h ⊢
  rw [h]
  have : (F.blockSide : ℤ) ^ j * ((F.blockSide : ℤ) ^ (F.top - j) * siteCoords z i) =
      (F.blockSide : ℤ) ^ (F.top - 0) * siteCoords z i := by
    rw [← mul_assoc, ← pow_add]
    congr 2
    omega
  rw [this]
theorem valMinAbs_intCast_of_small {p : ℕ} {A : ℤ} (h : p = 0 ∨ 2 * |A| < p) :
    ((A : ZMod p)).valMinAbs = A := by
  rcases h with h | h
  · subst h
    rfl
  · have hp : p ≠ 0 := by
      rintro rfl
      have := abs_nonneg A
      simp at h
      omega
    haveI : NeZero p := ⟨hp⟩
    rw [ZMod.valMinAbs_spec]
    refine ⟨rfl, ?_, ?_⟩ <;> have := abs_lt.1 (show |A| < (p : ℤ) from by have := abs_nonneg A; omega) <;>
      rcases abs_cases A with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> omega
section Cutoffs
theorem cutoffProfile_neg (t : ℝ) : cutoffProfile (-t) = cutoffProfile t := by
  simp [cutoffProfile, abs_neg]
theorem cutoffProfile_eq_one {t : ℝ} (h : |t| ≤ 0.6) : cutoffProfile t = 1 := by
  unfold cutoffProfile
  apply Real.smoothTransition.one_of_one_le
  rw [le_div_iff₀ (by norm_num)]
  linarith
theorem cutoffProfile_eq_zero {t : ℝ} (h : 0.9 ≤ |t|) : cutoffProfile t = 0 := by
  unfold cutoffProfile
  apply Real.smoothTransition.zero_of_nonpos
  apply div_nonpos_of_nonpos_of_nonneg <;> linarith
theorem abs_lt_of_cutoffProfile_ne_zero {t : ℝ} (h : cutoffProfile t ≠ 0) : |t| < 0.9 := by
  by_contra hc
  exact h (cutoffProfile_eq_zero (not_lt.1 hc))
theorem cutoffProfile_nonneg (t : ℝ) : 0 ≤ cutoffProfile t := Real.smoothTransition.nonneg _
theorem cutoffProfile_le_one (t : ℝ) : cutoffProfile t ≤ 1 := Real.smoothTransition.le_one _
theorem cutoffProfile_contDiff : ContDiff ℝ (⊤ : ℕ∞) cutoffProfile := by
  have hG : ContDiff ℝ (⊤ : ℕ∞) (fun t : ℝ => Real.smoothTransition ((0.9 - t) / 0.3)) :=
    Real.smoothTransition.contDiff.comp (by fun_prop)
  have hG' : ContDiff ℝ (⊤ : ℕ∞) (fun t : ℝ => Real.smoothTransition ((0.9 - -t) / 0.3)) :=
    Real.smoothTransition.contDiff.comp (by fun_prop)
  have e : cutoffProfile = fun t => Real.smoothTransition ((0.9 - t) / 0.3) *
      Real.smoothTransition ((0.9 - -t) / 0.3) := by
    funext t
    have one : ∀ x : ℝ, x ≤ 0 → Real.smoothTransition ((0.9 - x) / 0.3) = 1 := by
      intro x hx
      apply Real.smoothTransition.one_of_one_le
      rw [le_div_iff₀ (by norm_num)]
      linarith
    rcases le_total 0 t with h | h
    · have := one (-t) (by linarith)
      simp only [cutoffProfile, abs_of_nonneg h, this, mul_one]
    · have := one t h
      simp only [cutoffProfile, abs_of_nonpos h, this, one_mul]
  rw [e]
  exact hG.mul hG'
theorem cutoffProfile_hasCompactSupport : HasCompactSupport cutoffProfile := by
  refine HasCompactSupport.intro (isCompact_Icc (a := (-1 : ℝ)) (b := 1)) fun t ht => ?_
  apply cutoffProfile_eq_zero
  simp only [Set.mem_Icc, not_and_or, not_le] at ht
  rcases ht with h | h
  · rw [abs_of_neg (by linarith)]; linarith
  · rw [abs_of_pos (by linarith)]; linarith
theorem _root_.YangMills.Construction.FiniteDifferences.DerivBound.mono {k : ℕ} {M M' : ℝ} {g : ℝ → ℝ}
    (hM : M ≤ M') (h : DerivBound k M g) : DerivBound k M' g := by
  induction k generalizing g with
  | zero => exact fun t => (h t).trans hM
  | succ k ih => exact ⟨fun t => (h.1 t).trans hM, h.2.1, ih h.2.2⟩
theorem exists_derivBound (k : ℕ) {g : ℝ → ℝ} (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (hc : HasCompactSupport g) : ∃ M, DerivBound k M g := by
  obtain ⟨M0, hM0⟩ := hc.exists_bound_of_continuous hg.continuous
  induction k generalizing g M0 with
  | zero => exact ⟨M0, fun t => by simpa using hM0 t⟩
  | succ k ih =>
    have hd := (contDiff_infty_iff_deriv.1 hg)
    obtain ⟨M1, hM1⟩ := hc.deriv.exists_bound_of_continuous hd.2.continuous
    obtain ⟨M, hM⟩ := ih hd.2 hc.deriv M1 hM1
    exact ⟨max M0 M, fun t => ((by simpa using hM0 t : |g t| ≤ M0)).trans (le_max_left _ _), hd.1,
      hM.mono (le_max_right _ _)⟩
def cutoffBound : ℝ :=
  max 1 (Classical.choose (exists_derivBound 3 cutoffProfile_contDiff cutoffProfile_hasCompactSupport))
theorem one_le_cutoffBound : 1 ≤ cutoffBound := le_max_left _ _
theorem cutoffProfile_derivBound : DerivBound 3 cutoffBound cutoffProfile :=
  (Classical.choose_spec (exists_derivBound 3 cutoffProfile_contDiff cutoffProfile_hasCompactSupport)).mono
    (le_max_right _ _)
end Cutoffs
section Local
variable (S : Finset F.Cell) (z : F.Cell)
def localCell (v : Lattice4) : F.Cell := z + siteOfCoords F.top (fun i => closedOrthant S z i * v i)
def localCutoff (F : BlockFrame) (v x : Lattice4) : ℝ :=
  ∏ i, cutoffProfile (((x i - (cellSideLength F - 1) / 2 - cellSideLength F * v i : ℤ) : ℝ) /
    (F.blockSide : ℝ) ^ F.top)
theorem patchSite_sub_cellCentre (x v : Lattice4) (i : Fin 4) :
    (patchSite S z x - cellCentre 0 (localCell S z v)) i =
      ((closedOrthant S z i * (x i - (cellSideLength F - 1) / 2 - cellSideLength F * v i) : ℤ) :
        ZMod (F.period 0 i)) := by
  have h := cellCentre_add 0 (Nat.zero_le _) z (fun i => closedOrthant S z i * v i)
  simp only [localCell, patchSite, h, Pi.sub_apply, Pi.add_apply, siteOfCoords, Nat.sub_zero, cellSideLength]
  push_cast
  ring
variable {S z}
theorem period_zero_eq_zero_or (hamb : IsAdmissibleAmbient F) (hL : 0 < F.blockSide) (i : Fin 4) :
    F.period 0 i = 0 ∨ 64 * cellSideLength F ≤ (F.period 0 i : ℤ) := by
  rcases hamb with h | h
  · left
    simp [BlockFrame.period, h i]
  · right
    have hp : (0 : ℤ) < (F.blockSide : ℤ) ^ F.top := by positivity
    simp only [BlockFrame.period, cellSideLength, Nat.sub_zero]
    push_cast
    have : (64 : ℤ) ≤ F.extent i := by exact_mod_cast h i
    nlinarith
theorem cellSideLength_pos (hL : 0 < F.blockSide) : 0 < cellSideLength F := by
  unfold cellSideLength
  positivity
theorem valMinAbs_of_abs_lt (hamb : IsAdmissibleAmbient F) (hL : 0 < F.blockSide) (i : Fin 4) {A : ℤ}
    (hA : |A| < 32 * cellSideLength F) :
    ((A : ZMod (F.period 0 i))).valMinAbs = A := by
  apply valMinAbs_intCast_of_small
  rcases period_zero_eq_zero_or hamb hL i with h | h
  · exact Or.inl h
  · right
    linarith
theorem cellCutoff_eq_localCutoff (hamb : IsAdmissibleAmbient F) (hL : 0 < F.blockSide) {x v : Lattice4}
    (he : ∀ i, closedOrthant S z i = 1 ∨ closedOrthant S z i = -1)
    (hx : ∀ i, -(10 * cellSideLength F) ≤ x i ∧ x i < 21 * cellSideLength F)
    (hv : ∀ i, -11 ≤ v i ∧ v i ≤ 21)
    (hc : 0 ≤ (cellSideLength F - 1) / 2 ∧ (cellSideLength F - 1) / 2 < cellSideLength F) :
    cellCutoff (patchSite S z x) (localCell S z v) = localCutoff F v x := by
  have hN := cellSideLength_pos (F := F) hL
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [patchSite_sub_cellCentre]
  set A : ℤ := x i - (cellSideLength F - 1) / 2 - cellSideLength F * v i with hA
  have hAb : |A| < 32 * cellSideLength F := by
    have h1 := hx i
    have h2 := hv i
    have a1 : cellSideLength F * v i ≤ cellSideLength F * 21 := mul_le_mul_of_nonneg_left h2.2 hN.le
    have a2 : cellSideLength F * (-11) ≤ cellSideLength F * v i := mul_le_mul_of_nonneg_left h2.1 hN.le
    rw [abs_lt]
    constructor <;> omega
  have hAb' : |closedOrthant S z i * A| < 32 * cellSideLength F := by
    rcases he i with h | h <;> rw [h] <;> simpa using hAb
  rw [valMinAbs_of_abs_lt hamb hL i hAb']
  rcases he i with h | h
  · rw [h]; simp
  · rw [h]
    have : (((-1 * A : ℤ) : ℝ)) / (F.blockSide : ℝ) ^ F.top = - ((A : ℝ) / (F.blockSide : ℝ) ^ F.top) := by
      push_cast; ring
    rw [this, cutoffProfile_neg]
theorem mem_sitesOfCells {S : Finset F.Cell} {j : ℕ} {x : F.Site j} :
    x ∈ sitesOfCells S j ↔
      ∃ y ∈ S, ∃ h ∈ centredCube (F.blockSide ^ (F.top - j)), x = cellCentre j y + siteOfCoords j h := by
  simp only [sitesOfCells, Finset.mem_biUnion, Finset.mem_image]
  constructor
  · rintro ⟨y, hy, h, hh, rfl⟩
    exact ⟨y, hy, h, hh, rfl⟩
  · rintro ⟨y, hy, h, hh, rfl⟩
    exact ⟨y, hy, h, hh, rfl⟩
end Local
section Index
variable {S : Finset F.Cell} {z : F.Cell}
theorem cellSideLength_half (hodd : Odd F.blockSide) :
    0 ≤ (cellSideLength F - 1) / 2 ∧ 2 * ((cellSideLength F - 1) / 2) + 1 = cellSideLength F := by
  have h1 : Odd (cellSideLength F) := by
    unfold cellSideLength
    have : Odd (F.blockSide : ℤ) := by exact_mod_cast hodd
    exact this.pow
  obtain ⟨k, hk⟩ := h1
  have hL : 0 < F.blockSide := hodd.pos
  have hp := cellSideLength_pos (F := F) hL
  constructor <;> omega
theorem exists_localCell_of_cellCutoff_ne_zero (hamb : IsAdmissibleAmbient F) (hodd : Odd F.blockSide)
    {x : Lattice4} (he : ∀ i, closedOrthant S z i = 1 ∨ closedOrthant S z i = -1)
    (hx : ∀ i, -(10 * cellSideLength F) ≤ x i ∧ x i < 21 * cellSideLength F) {y : F.Cell}
    (hb : cellCutoff (patchSite S z x) y ≠ 0) :
    ∃ v : Lattice4, (∀ i, -11 ≤ v i ∧ v i ≤ 21) ∧ y = localCell S z v := by
  have hL : 0 < F.blockSide := hodd.pos
  have hN := cellSideLength_pos (F := F) hL
  have hNr : (0 : ℝ) < (F.blockSide : ℝ) ^ F.top := by
    have : (0 : ℝ) < F.blockSide := by exact_mod_cast hL
    positivity
  obtain ⟨hc0, hc1⟩ := cellSideLength_half (F := F) hodd
  set o : Lattice4 := fun i => ((y - z) i).valMinAbs with ho
  set v : Lattice4 := fun i => closedOrthant S z i * o i with hv
  have hee : ∀ i, closedOrthant S z i * closedOrthant S z i = 1 := by
    intro i
    rcases he i with h | h <;> rw [h] <;> norm_num
  have habs : ∀ {i}, |closedOrthant S z i| = 1 := by
    intro i
    rcases he i with h | h <;> rw [h] <;> norm_num
  have hyv : y = localCell S z v := by
    have h1 : (fun i => closedOrthant S z i * v i) = o := by
      funext i
      simp only [hv]
      rw [← mul_assoc, hee i, one_mul]
    have h2 : siteOfCoords F.top o = y - z := by
      funext i
      simp [siteOfCoords, ho, ZMod.coe_valMinAbs]
    unfold localCell
    rw [h1, h2]
    abel
  refine ⟨v, fun i => ?_, hyv⟩
  have hf : cutoffProfile ((((patchSite S z x - cellCentre 0 y) i).valMinAbs : ℝ) /
      (F.blockSide : ℝ) ^ F.top) ≠ 0 :=
    fun h0 => hb (Finset.prod_eq_zero (Finset.mem_univ i) h0)
  have hlt := abs_lt_of_cutoffProfile_ne_zero hf
  have hcast := patchSite_sub_cellCentre S z x v i
  rw [← hyv] at hcast
  rw [hcast] at hlt
  set A : ℤ := closedOrthant S z i * (x i - (cellSideLength F - 1) / 2 - cellSideLength F * v i) with hA
  set t : ℤ := ((A : ZMod (F.period 0 i))).valMinAbs with ht
  have htN : |t| < cellSideLength F := by
    rw [abs_div, abs_of_pos hNr] at hlt
    rw [div_lt_iff₀ hNr] at hlt
    have h1 : |(t : ℝ)| < (cellSideLength F : ℝ) := by
      have h2 : (cellSideLength F : ℝ) = (F.blockSide : ℝ) ^ F.top := by simp [cellSideLength]
      rw [h2]
      nlinarith
    exact_mod_cast h1
  have hAt : A = t := by
    rcases period_zero_eq_zero_or hamb hL i with h0 | h0
    · rw [ht]
      exact (valMinAbs_intCast_of_small (Or.inl h0)).symm
    · have hdvd : ((F.period 0 i : ℕ) : ℤ) ∣ t - A := by
        rw [← ZMod.intCast_eq_intCast_iff_dvd_sub]
        exact (ZMod.coe_valMinAbs _).symm
      have hside : 64 ≤ F.extent i := by
        rcases hamb with h | h
        · have h1 : F.period 0 i = 0 := by simp [BlockFrame.period, h i]
          rw [h1] at h0
          simp at h0
          omega
        · exact h i
      haveI : NeZero (F.period F.top i) := ⟨by simp [BlockFrame.period]; omega⟩
      have ho2 := ZMod.valMinAbs_mem_Ioc ((y - z) i)
      have hpern : ((F.period F.top i : ℕ) : ℤ) = F.extent i := by simp [BlockFrame.period]
      have hper0 : ((F.period 0 i : ℕ) : ℤ) = F.extent i * cellSideLength F := by
        simp [BlockFrame.period, cellSideLength]
      rw [hpern] at ho2
      have hoi : o i * 2 ∈ Set.Ioc (-(F.extent i : ℤ)) (F.extent i : ℤ) := ho2
      have hAo : A = closedOrthant S z i * (x i - (cellSideLength F - 1) / 2) - cellSideLength F * o i := by
        have : closedOrthant S z i * v i = o i := by
          simp only [hv]
          rw [← mul_assoc, hee i, one_mul]
        rw [hA]
        calc _ = closedOrthant S z i * (x i - (cellSideLength F - 1) / 2) -
              cellSideLength F * (closedOrthant S z i * v i) := by ring
          _ = _ := by rw [this]
      have hx1 : |closedOrthant S z i * (x i - (cellSideLength F - 1) / 2)| ≤ 22 * cellSideLength F := by
        have h1 := hx i
        have h2 : |x i - (cellSideLength F - 1) / 2| ≤ 22 * cellSideLength F := by
          rw [abs_le]
          constructor <;> omega
        rw [abs_mul, habs, one_mul]
        exact h2
      have hoN : 2 * |cellSideLength F * o i| ≤ F.extent i * cellSideLength F := by
        rw [abs_mul, abs_of_pos hN]
        have h2 : 2 * |o i| ≤ F.extent i := by
          have a1 := hoi.1
          have a2 := hoi.2
          rcases abs_cases (o i) with ⟨h, _⟩ | ⟨h, _⟩ <;> rw [h] <;> linarith
        nlinarith
      have hAb : |A| ≤ 22 * cellSideLength F + |cellSideLength F * o i| := by
        rw [hAo]
        exact (abs_sub _ _).trans (add_le_add hx1 le_rfl)
      have hlt2 : |t - A| < ((F.period 0 i : ℕ) : ℤ) := by
        rw [hper0]
        have h3 := abs_sub t A
        omega
      have := Int.eq_zero_of_abs_lt_dvd hdvd hlt2
      omega
  have hAabs : |x i - (cellSideLength F - 1) / 2 - cellSideLength F * v i| < cellSideLength F := by
    have h1 : |A| < cellSideLength F := by rw [hAt]; exact htN
    rw [hA, abs_mul, habs, one_mul] at h1
    exact h1
  have hx2 := hx i
  obtain ⟨b1, b2⟩ := abs_lt.1 hAabs
  constructor
  · by_contra hcon
    have h1 : v i ≤ -12 := by omega
    have h2 := mul_le_mul_of_nonneg_left h1 hN.le
    omega
  · by_contra hcon
    have h1 : 22 ≤ v i := by omega
    have h2 := mul_le_mul_of_nonneg_left h1 hN.le
    omega
theorem cellCutoff_self (hamb : IsAdmissibleAmbient F) (hodd : Odd F.blockSide) (y : F.Cell) {h : Lattice4}
    (hh : h ∈ centredCube (F.blockSide ^ F.top)) : cellCutoff (cellCentre 0 y + siteOfCoords 0 h) y = 1 := by
  have hL : 0 < F.blockSide := hodd.pos
  have hNr : (0 : ℝ) < (F.blockSide : ℝ) ^ F.top := by
    have : (0 : ℝ) < F.blockSide := by exact_mod_cast hL
    positivity
  obtain ⟨hc0, hc1⟩ := cellSideLength_half (F := F) hodd
  refine Finset.prod_eq_one fun i _ => ?_
  have hm : -((((F.blockSide ^ F.top : ℕ) : ℤ) - 1) / 2) ≤ h i ∧
      h i ≤ (((F.blockSide ^ F.top : ℕ) : ℤ) - 1) / 2 := by
    have := (Fintype.mem_piFinset.1 hh) i
    simpa using this
  have hcs : ((F.blockSide ^ F.top : ℕ) : ℤ) = cellSideLength F := by simp [cellSideLength]
  rw [hcs] at hm
  have e1 : (cellCentre 0 y + siteOfCoords 0 h - cellCentre 0 y : F.Site 0) i =
      ((h i : ℤ) : ZMod (F.period 0 i)) := by
    simp [siteOfCoords]
  rw [e1, valMinAbs_of_abs_lt hamb hL i (by rw [abs_lt]; constructor <;> omega)]
  apply cutoffProfile_eq_one
  rw [abs_div, abs_of_pos hNr]
  rw [div_le_iff₀ hNr]
  have h2 : |(h i : ℝ)| ≤ ((cellSideLength F - 1) / 2 : ℤ) := by
    have : |h i| ≤ (cellSideLength F - 1) / 2 := by rw [abs_le]; exact hm
    exact_mod_cast this
  have h3 : (2 : ℝ) * ((cellSideLength F - 1) / 2 : ℤ) + 1 = (F.blockSide : ℝ) ^ F.top := by
    have : (2 : ℤ) * ((cellSideLength F - 1) / 2) + 1 = cellSideLength F := hc1
    have h4 : ((2 * ((cellSideLength F - 1) / 2) + 1 : ℤ) : ℝ) = (cellSideLength F : ℝ) := by rw [this]
    push_cast at h4
    rw [h4]
    simp [cellSideLength]
  norm_num
  nlinarith
open Classical in
def localCellIndex (S : Finset F.Cell) (z : F.Cell) : Finset Lattice4 :=
  (Fintype.piFinset fun _ : Fin 4 => Finset.Icc (-11 : ℤ) 21).filter fun v => localCell S z v ∈ S
theorem mem_localCellIndex {v : Lattice4} :
    v ∈ localCellIndex S z ↔ (∀ i, -11 ≤ v i ∧ v i ≤ 21) ∧ localCell S z v ∈ S := by
  simp [localCellIndex, Fintype.mem_piFinset]
theorem card_localCellIndex_le : (localCellIndex S z).card ≤ 33 ^ 4 := by
  classical
  refine (Finset.card_filter_le _ _).trans ?_
  simp [Fintype.card_piFinset]
theorem localCell_injective (hamb : IsAdmissibleAmbient F)
    (he : ∀ i, closedOrthant S z i = 1 ∨ closedOrthant S z i = -1) {v v' : Lattice4}
    (hv : ∀ i, -11 ≤ v i ∧ v i ≤ 21) (hv' : ∀ i, -11 ≤ v' i ∧ v' i ≤ 21)
    (h : localCell S z v = localCell S z v') : v = v' := by
  funext i
  have h1 := congrFun (add_left_cancel h) i
  simp only [siteOfCoords] at h1
  rw [ZMod.intCast_eq_intCast_iff_dvd_sub] at h1
  have hb1 := hv i
  have hb2 := hv' i
  rcases hamb with h0 | h0
  · have : ((F.period F.top i : ℕ) : ℤ) = 0 := by simp [BlockFrame.period, h0 i]
    rw [this] at h1
    have h2 := zero_dvd_iff.1 h1
    have h3 : closedOrthant S z i * (v' i - v i) = 0 := by linarith
    rcases he i with h | h <;> rw [h] at h3 <;> omega
  · have hs : (64 : ℤ) ≤ ((F.period F.top i : ℕ) : ℤ) := by
      have : (F.period F.top i) = F.extent i := by simp [BlockFrame.period]
      rw [this]
      exact_mod_cast h0 i
    have h2 : |closedOrthant S z i * v' i - closedOrthant S z i * v i| < ((F.period F.top i : ℕ) : ℤ) := by
      have : |closedOrthant S z i * v' i - closedOrthant S z i * v i| ≤ 32 := by
        rcases he i with h | h <;> rw [h] <;> rw [abs_le] <;> constructor <;> omega
      omega
    have h3 := Int.eq_zero_of_abs_lt_dvd h1 h2
    rcases he i with h | h <;> rw [h] at h3 <;> omega
theorem sum_eq_sum_localCellIndex {M : Type} [AddCommMonoid M] (hamb : IsAdmissibleAmbient F)
    (hodd : Odd F.blockSide) {x : Lattice4}
    (he : ∀ i, closedOrthant S z i = 1 ∨ closedOrthant S z i = -1)
    (hx : ∀ i, -(10 * cellSideLength F) ≤ x i ∧ x i < 21 * cellSideLength F) (G : F.Cell → M)
    (hG : ∀ y ∈ S, cellCutoff (patchSite S z x) y = 0 → G y = 0) :
    ∑ y ∈ S, G y = ∑ v ∈ localCellIndex S z, G (localCell S z v) := by
  classical
  have hsub : (localCellIndex S z).image (localCell S z) ⊆ S := by
    intro y hy
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 hy
    exact (mem_localCellIndex.1 hv).2
  rw [← Finset.sum_subset hsub, Finset.sum_image]
  · intro a ha b hb hab
    exact localCell_injective hamb he (mem_localCellIndex.1 ha).1 (mem_localCellIndex.1 hb).1 hab
  · intro y hy hny
    refine hG y hy ?_
    by_contra hb
    obtain ⟨v, hv, rfl⟩ := exists_localCell_of_cellCutoff_ne_zero hamb hodd he hx hb
    exact hny (Finset.mem_image.2 ⟨v, mem_localCellIndex.2 ⟨hv, hy⟩, rfl⟩)
end Index
section Signs
variable {S : Finset F.Cell} {z : F.Cell}
theorem signVectors_entries {e : Fin 4 → ℤ} (he : e ∈ signVectors) (i : Fin 4) : e i = 1 ∨ e i = -1 := by
  simp only [signVectors, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    fin_cases i <;> simp
theorem mem_signVectors {e : Fin 4 → ℤ} (he : ∀ i, e i = 1 ∨ e i = -1) : e ∈ signVectors := by
  have h0 : e = ![e 0, e 1, e 2, e 3] := by
    funext i
    fin_cases i <;> rfl
  rw [h0]
  rcases he 0 with a | a <;> rcases he 1 with b | b <;> rcases he 2 with c | c <;> rcases he 3 with d | d <;>
    rw [a, b, c, d] <;> simp [signVectors]
theorem closedOrthant_spec {m : ℕ} (hreg : IsOrthantRegular S m) (hm : 32 ≤ m) (z : F.Cell) :
    (∀ i, closedOrthant S z i = 1 ∨ closedOrthant S z i = -1) ∧
      IsOrthantClosedNear S z (closedOrthant S z) := by
  classical
  obtain ⟨eps, he, hc⟩ := hreg z
  have hcl : IsOrthantClosedNear S z eps := fun q hq hd h hh hb =>
    hc q hq (hd.trans hm) h hh (fun i => (hb i).trans (by exact_mod_cast hm))
  have hsome : (signVectors.find? fun e => decide (IsOrthantClosedNear S z e)).isSome := by
    rw [List.find?_isSome]
    exact ⟨eps, mem_signVectors he, by simpa using hcl⟩
  obtain ⟨r, hr⟩ := Option.isSome_iff_exists.1 hsome
  have hmem := List.mem_of_find?_eq_some hr
  have hp := List.find?_some hr
  have hsign : closedOrthant S z = r := by simp [closedOrthant, hr]
  rw [hsign]
  exact ⟨signVectors_entries hmem, by simpa using hp⟩
theorem closedOrthant_mul_self (he : ∀ i, closedOrthant S z i = 1 ∨ closedOrthant S z i = -1) (i : Fin 4) :
    closedOrthant S z i * closedOrthant S z i = 1 := by
  rcases he i with h | h <;> rw [h] <;> norm_num
theorem abs_closedOrthant (he : ∀ i, closedOrthant S z i = 1 ∨ closedOrthant S z i = -1) (i : Fin 4) :
    |closedOrthant S z i| = 1 := by
  rcases he i with h | h <;> rw [h] <;> norm_num
theorem mem_sitesOfCells_top {y : F.Cell} : y ∈ sitesOfCells S F.top ↔ y ∈ S := by
  rw [mem_sitesOfCells]
  constructor
  · rintro ⟨y', hy', h, hh, rfl⟩
    have h0 : h = 0 := by
      funext i
      have := (Fintype.mem_piFinset.1 hh) i
      simpa using this
    rw [h0, siteOfCoords_zero, add_zero, cellCentre_top]
    exact hy'
  · intro hy
    refine ⟨y, hy, 0, ?_, ?_⟩
    · simp [centredCube, Fintype.mem_piFinset]
      rfl
    · rw [siteOfCoords_zero, add_zero, cellCentre_top]
theorem valMinAbs_cell_of_small (hamb : IsAdmissibleAmbient F) (i : Fin 4) {A : ℤ} (hA : |A| < 32) :
    ((A : ZMod (F.period F.top i))).valMinAbs = A := by
  apply valMinAbs_intCast_of_small
  rcases hamb with h | h
  · left
    simp [BlockFrame.period, h i]
  · right
    have h1 : F.period F.top i = F.extent i := by simp [BlockFrame.period]
    rw [h1]
    have : (64 : ℤ) ≤ F.extent i := by exact_mod_cast h i
    omega
theorem cellDisplacement_add_siteOfCoords (hamb : IsAdmissibleAmbient F) (y : F.Cell) {a : Lattice4}
    (ha : ∀ i, |a i| < 32) : cellDisplacement y (y + siteOfCoords F.top a) = a := by
  funext i
  have : (y + siteOfCoords F.top a - y : F.Cell) i = ((a i : ℤ) : ZMod (F.period F.top i)) := by
    simp [siteOfCoords]
  simp only [cellDisplacement, this]
  exact valMinAbs_cell_of_small hamb i (ha i)
theorem cellSupDist_add_le (hamb : IsAdmissibleAmbient F) (y : F.Cell) {a : Lattice4} {r : ℕ} (hr : r < 32)
    (ha : ∀ i, |a i| ≤ r) : cellSupDist (y + siteOfCoords F.top a) y ≤ r := by
  refine Finset.sup_le fun i _ => ?_
  have h1 : (y + siteOfCoords F.top a : F.Cell) i - y i = ((a i : ℤ) : ZMod (F.period F.top i)) := by
    simp [siteOfCoords]
  have h2 : |a i| < 32 := lt_of_le_of_lt (ha i) (by exact_mod_cast hr)
  rw [h1, valMinAbs_cell_of_small hamb i h2]
  have := ha i
  rw [Int.abs_eq_natAbs] at this
  exact_mod_cast this
theorem localCell_add (v : Lattice4) (a : Lattice4) :
    localCell S z (v + a) = localCell S z v + siteOfCoords F.top (fun i => closedOrthant S z i * a i) := by
  unfold localCell
  rw [add_assoc, ← siteOfCoords_add]
  congr 2
  funext i
  simp [mul_add]
theorem cellCentre_injective (hamb : IsAdmissibleAmbient F) (hL : 0 < F.blockSide) {y y' : F.Cell}
    (h : cellCentre 0 y = cellCentre 0 y') : y = y' := by
  funext i
  have h1 := congrFun h i
  simp only [cellCentre, siteOfCoords] at h1
  rw [ZMod.intCast_eq_intCast_iff_dvd_sub] at h1
  have hN : (F.blockSide : ℤ) ^ F.top ≠ 0 := by positivity
  have hp : ((F.period 0 i : ℕ) : ℤ) = (F.extent i : ℤ) * (F.blockSide : ℤ) ^ F.top := by
    simp [BlockFrame.period]
  rw [hp] at h1
  simp only [Nat.sub_zero] at h1
  rw [← mul_sub, mul_comm ((F.extent i : ℤ))] at h1
  have h2 : (F.extent i : ℤ) ∣ siteCoords y' i - siteCoords y i := (mul_dvd_mul_iff_left hN).1 h1
  have hpn : ((F.period F.top i : ℕ) : ℤ) = F.extent i := by simp [BlockFrame.period]
  rw [← hpn, ← ZMod.intCast_eq_intCast_iff_dvd_sub] at h2
  simpa [siteCoords] using h2
end Signs
end YangMills.Construction.BlockAverages
end
