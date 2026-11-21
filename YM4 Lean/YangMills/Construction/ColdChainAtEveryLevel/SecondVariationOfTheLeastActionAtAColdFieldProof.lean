import YangMills.Construction.ColdChainAtEveryLevel.AnalyticSharesOfAColdTop
import YangMills.Construction.ColdChainAtEveryLevel.SecondVariationOfTheLeastActionAtAColdField
import YangMills.Construction.ColdChainAtEveryLevel.SecondVariationOfTheLeastActionAtAColdTop
import YangMills.Construction.ColdChainAtEveryLevel.SecondVariationOfTheWilsonAction
import YangMills.Construction.ColdChainAtEveryLevel.WeightsUpTheLevels
import YangMills.Construction.HoleBesideASecondHole.CutActionIsTheLeastActionProof
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion Topology
namespace YangMills.Construction.BlockAverages.ColdFieldSecondVariation
abbrev frameAbove (L t : ℕ) (side : Fin 4 → ℕ) : BlockFrame := ⟨L, t + 1, side⟩
abbrev frameBelow (L t : ℕ) (side : Fin 4 → ℕ) : BlockFrame := ⟨L, t, fun i => L * side i⟩
variable {L t : ℕ} {side : Fin 4 → ℕ}
theorem period_frameAbove_eq {j : ℕ} (hj : j ≤ t + 1) (i : Fin 4) :
    (frameAbove L t side).period j i = (frameBelow L t side).period j i := by
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hj
  have e1 : t + 1 + 1 - j = k + 1 := by omega
  have e2 : t + 1 - j = k := by omega
  simp only [BlockFrame.period, BlockFrame.top, e1, e2, pow_succ]
  ring
def siteEquivBelow {j : ℕ} (hj : j ≤ t + 1) : (frameAbove L t side).Site j ≃+ (frameBelow L t side).Site j :=
  AddEquiv.piCongrRight fun i => (ZMod.ringEquivCongr (period_frameAbove_eq hj i)).toAddEquiv
theorem siteEquivBelow_apply {j : ℕ} (hj : j ≤ t + 1) (x : (frameAbove L t side).Site j) (i : Fin 4) :
    siteEquivBelow hj x i = ZMod.ringEquivCongr (period_frameAbove_eq hj i) (x i) := rfl
theorem siteEquivBelow_siteOfCoords {j : ℕ} (hj : j ≤ t + 1) (z : Fin 4 → ℤ) :
    siteEquivBelow hj (siteOfCoords (F := frameAbove L t side) j z) = siteOfCoords (F := frameBelow L t side) j z := by
  funext i
  rw [siteEquivBelow_apply]
  simp only [siteOfCoords, map_intCast]
theorem zmodCast_ringEquivCongr {m n : ℕ} (h : m = n) (a : ZMod m) :
    (ZMod.cast (ZMod.ringEquivCongr h a) : ℤ) = ZMod.cast a := by
  subst h
  simp [ZMod.ringEquivCongr_refl]
theorem siteCoords_siteEquivBelow {j : ℕ} (hj : j ≤ t + 1) (x : (frameAbove L t side).Site j) :
    siteCoords (siteEquivBelow hj x) = siteCoords x := by
  funext i
  simp only [siteCoords, siteEquivBelow_apply, zmodCast_ringEquivCongr]
theorem siteEquivBelow_unitStep {j : ℕ} (hj : j ≤ t + 1) (i : Fin 4) :
    siteEquivBelow hj (unitStep (F := frameAbove L t side) j i) = unitStep (F := frameBelow L t side) j i :=
  siteEquivBelow_siteOfCoords hj _
theorem siteEquivBelow_stepDisplacement {j : ℕ} (hj : j ≤ t + 1) (st : PathStep) :
    siteEquivBelow hj (stepDisplacement (F := frameAbove L t side) j st) =
      stepDisplacement (F := frameBelow L t side) j st := by
  unfold stepDisplacement
  split_ifs
  · exact siteEquivBelow_unitStep hj _
  · rw [map_neg, siteEquivBelow_unitStep]
theorem siteEquivBelow_refineSite {j : ℕ} (hj : j + 1 ≤ t + 1) (y : (frameAbove L t side).Site (j + 1)) :
    siteEquivBelow (Nat.le_of_succ_le hj) (refineSite y) = refineSite (siteEquivBelow hj y) := by
  unfold refineSite
  rw [siteEquivBelow_siteOfCoords, siteCoords_siteEquivBelow]
def fieldBelow {j : ℕ} (hj : j ≤ t + 1) (W : (frameAbove L t side).GaugeField j) :
    (frameBelow L t side).GaugeField j :=
  fun x i => W ((siteEquivBelow hj).symm x) i
theorem fieldBelow_apply {j : ℕ} (hj : j ≤ t + 1) (W : (frameAbove L t side).GaugeField j)
    (x : (frameAbove L t side).Site j) (i : Fin 4) : fieldBelow hj W (siteEquivBelow hj x) i = W x i := by
  simp [fieldBelow]
def fieldEquivBelow {j : ℕ} (hj : j ≤ t + 1) :
    (frameAbove L t side).GaugeField j ≃ (frameBelow L t side).GaugeField j where
  toFun := fieldBelow hj
  invFun := fun W x i => W (siteEquivBelow hj x) i
  left_inv := fun W => by
    funext x i
    simp [fieldBelow]
  right_inv := fun W => by
    funext x i
    simp [fieldBelow]
theorem linkValue_fieldBelow {j : ℕ} (hj : j ≤ t + 1) (W : (frameAbove L t side).GaugeField j)
    (x : (frameAbove L t side).Site j) (st : PathStep) :
    linkValue (fieldBelow hj W) (siteEquivBelow hj x) st = linkValue W x st := by
  unfold linkValue
  split_ifs
  · exact fieldBelow_apply hj W x _
  · rw [← siteEquivBelow_unitStep hj, ← map_sub, fieldBelow_apply]
theorem pathHolonomy_fieldBelow {j : ℕ} (hj : j ≤ t + 1) (W : (frameAbove L t side).GaugeField j)
    (l : List PathStep) :
    ∀ x, pathHolonomy (fieldBelow hj W) (siteEquivBelow hj x) l = pathHolonomy W x l := by
  induction l with
  | nil => intro x; rfl
  | cons st r ih =>
    intro x
    simp only [pathHolonomy]
    rw [linkValue_fieldBelow, ← siteEquivBelow_stepDisplacement hj, ← map_add, ih]
theorem plaquetteHolonomy_fieldBelow {j : ℕ} (hj : j ≤ t + 1) (W : (frameAbove L t side).GaugeField j)
    (p : (frameAbove L t side).Site j × Fin 4 × Fin 4) :
    plaquetteHolonomy (fieldBelow hj W) (siteEquivBelow hj p.1, p.2) = plaquetteHolonomy W p :=
  pathHolonomy_fieldBelow hj W _ p.1
theorem contourAverage_fieldBelow {j : ℕ} (hj : j + 1 ≤ t + 1) (W : (frameAbove L t side).GaugeField j)
    (c : (frameAbove L t side).Site (j + 1) × Fin 4) :
    _root_.YangMills.Construction.BlockAverages.contourAverage (fieldBelow (Nat.le_of_succ_le hj) W) (siteEquivBelow hj c.1, c.2) = _root_.YangMills.Construction.BlockAverages.contourAverage W c := by
  unfold _root_.YangMills.Construction.BlockAverages.contourAverage
  simp only [← siteEquivBelow_refineSite hj, pathHolonomy_fieldBelow]
theorem blockFit_fieldBelow {j : ℕ} (hj : j + 1 ≤ t + 1) (W : (frameAbove L t side).GaugeField j)
    (V : (frameAbove L t side).GaugeField (j + 1)) (c : (frameAbove L t side).Site (j + 1) × Fin 4) :
    blockFit (fieldBelow (Nat.le_of_succ_le hj) W) (fieldBelow hj V) (siteEquivBelow hj c.1, c.2) =
      blockFit W V c := by
  unfold blockFit
  simp only [contourAverage_fieldBelow hj W c]
  rw [fieldBelow_apply]
theorem balanced_digits_iff (l m a : ℤ) (hl : 0 ≤ l) (hm : 0 ≤ m) :
    (-(2 * m * l + m + l) ≤ a ∧ a ≤ 2 * m * l + m + l) ↔
      ∃ g r, -l ≤ g ∧ g ≤ l ∧ -m ≤ r ∧ r ≤ m ∧ a = (2 * m + 1) * g + r := by
  constructor
  · rintro ⟨h1, h2⟩
    have hM : (0 : ℤ) < 2 * m + 1 := by linarith
    set g := (a + m) / (2 * m + 1) with hg
    have e := Int.mul_ediv_add_emod (a + m) (2 * m + 1)
    have e0 := Int.emod_nonneg (a + m) hM.ne'
    have e1 := Int.emod_lt_of_pos (a + m) hM
    set e' := (a + m) % (2 * m + 1) with he'
    rw [← hg] at e
    refine ⟨g, e' - m, ?_, ?_, by linarith, by linarith, by linarith⟩
    · by_contra hc
      have : g + 1 ≤ -l := by
        have : g < -l := not_le.1 hc
        linarith
      nlinarith
    · by_contra hc
      have : l + 1 ≤ g := by
        have : l < g := not_le.1 hc
        linarith
      nlinarith
  · rintro ⟨g, r, h1, h2, h3, h4, rfl⟩
    constructor <;> nlinarith
theorem exists_eq_two_mul_add_one_of_odd {M : ℕ} (hM : Odd M) :
    ∃ m : ℤ, 0 ≤ m ∧ (M : ℤ) = 2 * m + 1 ∧ ((M : ℤ) - 1) / 2 = m := by
  obtain ⟨m, rfl⟩ := hM
  refine ⟨m, by positivity, by push_cast; ring, ?_⟩
  push_cast
  have : (2 * (m : ℤ) + 1 - 1) = 2 * m := by ring
  rw [this]
  simp
theorem mem_centredCube_iff (M : ℕ) (h : Fin 4 → ℤ) :
    h ∈ centredCube M ↔ ∀ i, -(((M : ℤ) - 1) / 2) ≤ h i ∧ h i ≤ ((M : ℤ) - 1) / 2 := by apply _root_.YangMills.Construction.LumpContours.CutAction.mem_centredCube <;> assumption
theorem mem_centredCube_pow_succ_iff (hodd : Odd L) (k : ℕ) (h : Fin 4 → ℤ) :
    h ∈ centredCube (L ^ (k + 1)) ↔
      ∃ g ∈ centredCube L, ∃ r ∈ centredCube (L ^ k), h = (fun i => (L : ℤ) ^ k * g i) + r := by
  obtain ⟨l, hl0, hl, hl2⟩ := exists_eq_two_mul_add_one_of_odd hodd
  obtain ⟨m, hm0, hm, hm2⟩ := exists_eq_two_mul_add_one_of_odd (hodd.pow (n := k))
  have hLk : ((L ^ (k + 1) : ℕ) : ℤ) = (2 * m + 1) * (2 * l + 1) := by
    rw [pow_succ]
    push_cast
    push_cast at hm
    rw [hm, hl]
  have e2 : (((L ^ (k + 1) : ℕ) : ℤ) - 1) / 2 = 2 * m * l + m + l := by
    rw [hLk]
    have : (2 * m + 1) * (2 * l + 1) - 1 = 2 * (2 * m * l + m + l) := by ring
    rw [this]
    simp
  have hkm : ((L : ℤ) ^ k) = 2 * m + 1 := by
    push_cast at hm
    exact hm
  constructor
  · intro hh
    rw [_root_.YangMills.Construction.BlockAverages.ColdFieldSecondVariation.mem_centredCube_iff, e2] at hh
    have := fun i => (balanced_digits_iff l m (h i) hl0 hm0).1 (hh i)
    choose g r h1 h2 h3 h4 h5 using this
    refine ⟨g, ?_, r, ?_, ?_⟩
    · rw [_root_.YangMills.Construction.BlockAverages.ColdFieldSecondVariation.mem_centredCube_iff, hl2]
      exact fun i => ⟨h1 i, h2 i⟩
    · rw [_root_.YangMills.Construction.BlockAverages.ColdFieldSecondVariation.mem_centredCube_iff, hm2]
      exact fun i => ⟨h3 i, h4 i⟩
    · funext i
      simp only [Pi.add_apply, hkm]
      exact h5 i
  · rintro ⟨g, hg, r, hr, rfl⟩
    rw [_root_.YangMills.Construction.BlockAverages.ColdFieldSecondVariation.mem_centredCube_iff, hl2] at hg
    rw [_root_.YangMills.Construction.BlockAverages.ColdFieldSecondVariation.mem_centredCube_iff, hm2] at hr
    rw [_root_.YangMills.Construction.BlockAverages.ColdFieldSecondVariation.mem_centredCube_iff, e2]
    intro i
    refine (balanced_digits_iff l m _ hl0 hm0).2 ⟨g i, r i, (hg i).1, (hg i).2, (hr i).1, (hr i).2, ?_⟩
    simp only [Pi.add_apply, hkm]
def cellsBelow (S : Finset (frameAbove L t side).Cell) : Finset (frameBelow L t side).Cell := by
  classical exact (sitesOfCells S (t + 1)).image (siteEquivBelow le_rfl)
theorem mem_sitesOfCells_iff {F : BlockFrame} (S : Finset F.Cell) (j : ℕ) (x : F.Site j) :
    x ∈ sitesOfCells S j ↔
      ∃ z ∈ S, ∃ h ∈ centredCube (F.blockSide ^ (F.top - j)), cellCentre j z + siteOfCoords j h = x := by
  simp [sitesOfCells]
theorem siteEquivBelow_cellCentre_add {j k : ℕ} (hj : j ≤ t + 1) (hk : t + 1 - j = k)
    (z : (frameAbove L t side).Cell) (g r : Fin 4 → ℤ) :
    siteEquivBelow hj (cellCentre j z + siteOfCoords j ((fun i => (L : ℤ) ^ k * g i) + r)) =
      cellCentre j (siteEquivBelow (le_refl (t + 1)) (cellCentre (t + 1) z + siteOfCoords (t + 1) g) :
        (frameBelow L t side).Cell) + siteOfCoords j r := by
  have e1 : (frameAbove L t side).top - j = k + 1 := by
    show t + 1 + 1 - j = k + 1
    omega
  have e2 : (frameBelow L t side).top - j = k := hk
  have e3 : (frameAbove L t side).top - (t + 1) = 1 := by
    show t + 1 + 1 - (t + 1) = 1
    omega
  have hy : cellCentre (F := frameAbove L t side) (t + 1) z + siteOfCoords (t + 1) g =
      siteOfCoords (F := frameAbove L t side) (t + 1) ((fun i => (L : ℤ) * siteCoords z i) + g) := by
    unfold cellCentre
    rw [e3, pow_one, ← siteOfCoords_add]
  set w : Fin 4 → ℤ := (fun i => (L : ℤ) * siteCoords z i) + g with hw
  have hc : siteOfCoords (F := frameAbove L t side) j
        (fun i => (L : ℤ) ^ k * siteCoords (siteOfCoords (F := frameAbove L t side) (t + 1) w) i) =
      siteOfCoords j (fun i => (L : ℤ) ^ k * w i) := by
    funext i
    refine intCast_mul_eq_of_eq ?_ (siteCoords_cast (F := frameAbove L t side) (j := t + 1) w i)
    have e4 : t + 1 + 1 - j = k + 1 := by omega
    have e5 : t + 1 + 1 - (t + 1) = 1 := by omega
    simp only [BlockFrame.period, BlockFrame.top, e4, e5]
    push_cast
    ring
  have hR : cellCentre (F := frameBelow L t side) j
        (siteEquivBelow (le_refl (t + 1)) (siteOfCoords (F := frameAbove L t side) (t + 1) w) :
          (frameBelow L t side).Cell) =
      siteEquivBelow hj (siteOfCoords (F := frameAbove L t side) j (fun i => (L : ℤ) ^ k * w i)) := by
    unfold cellCentre
    rw [siteCoords_siteEquivBelow, e2, ← hc, siteEquivBelow_siteOfCoords]
  rw [hy, hR, ← siteEquivBelow_siteOfCoords hj r, ← map_add, ← siteOfCoords_add]
  congr 1
  unfold cellCentre
  rw [e1, ← siteOfCoords_add]
  congr 1
  funext i
  simp only [hw, Pi.add_apply, pow_succ]
  show (L : ℤ) ^ k * (L : ℤ) * siteCoords z i + ((L : ℤ) ^ k * g i + r i) = _
  ring
theorem mem_sitesOfCells_below_iff (hodd : Odd L) {j : ℕ} (hj : j ≤ t + 1)
    (S : Finset (frameAbove L t side).Cell) (x : (frameAbove L t side).Site j) :
    x ∈ sitesOfCells S j ↔ siteEquivBelow hj x ∈ sitesOfCells (cellsBelow S) j := by
  classical
  obtain ⟨k, hk⟩ : ∃ k, t + 1 - j = k := ⟨_, rfl⟩
  have e1 : (frameAbove L t side).top - j = k + 1 := by
    show t + 1 + 1 - j = k + 1
    omega
  have e2 : (frameBelow L t side).top - j = k := hk
  have e3 : (frameAbove L t side).top - (t + 1) = 1 := by
    show t + 1 + 1 - (t + 1) = 1
    omega
  rw [mem_sitesOfCells_iff, mem_sitesOfCells_iff, e1, e2]
  constructor
  · rintro ⟨z, hz, h, hh, rfl⟩
    obtain ⟨g, hg, r, hr, rfl⟩ := (mem_centredCube_pow_succ_iff hodd k h).1 hh
    refine ⟨siteEquivBelow (le_refl (t + 1)) (cellCentre (t + 1) z + siteOfCoords (t + 1) g), ?_, r, hr, ?_⟩
    · refine Finset.mem_image_of_mem _ ?_
      rw [mem_sitesOfCells_iff, e3, pow_one]
      exact ⟨z, hz, g, hg, rfl⟩
    · rw [siteEquivBelow_cellCentre_add hj hk]
  · rintro ⟨y', hy', r, hr, hx⟩
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 hy'
    rw [mem_sitesOfCells_iff, e3, pow_one] at hy
    obtain ⟨z, hz, g, hg, rfl⟩ := hy
    refine ⟨z, hz, (fun i => (L : ℤ) ^ k * g i) + r,
      (mem_centredCube_pow_succ_iff hodd k _).2 ⟨g, hg, r, hr, rfl⟩, ?_⟩
    apply (siteEquivBelow hj).injective
    rw [siteEquivBelow_cellCentre_add hj hk]
    exact hx
theorem plaquetteCorners_subset_iff {F : BlockFrame} {j : ℕ} (p : F.Site j × Fin 4 × Fin 4)
    (A : Finset (F.Site j)) :
    plaquetteCorners p ⊆ A ↔ p.1 ∈ A ∧ p.1 + unitStep j p.2.1 ∈ A ∧ p.1 + unitStep j p.2.2 ∈ A ∧
      p.1 + unitStep j p.2.1 + unitStep j p.2.2 ∈ A := by
  simp [plaquetteCorners, Finset.insert_subset_iff]
theorem mem_innerBonds_below_iff (hodd : Odd L) {j : ℕ} (hj : j ≤ t + 1)
    (S : Finset (frameAbove L t side).Cell) (b : (frameAbove L t side).Site j × Fin 4) :
    b ∈ innerBonds S j ↔ (siteEquivBelow hj b.1, b.2) ∈ innerBonds (cellsBelow S) j := by
  simp only [innerBonds, Finset.mem_filter, Finset.mem_product, Finset.mem_univ, and_true]
  rw [mem_sitesOfCells_below_iff hodd hj S, mem_sitesOfCells_below_iff hodd hj S, map_add,
    siteEquivBelow_unitStep]
theorem mem_innerPlaquettes_below_iff (hodd : Odd L) {j : ℕ} (hj : j ≤ t + 1)
    (S : Finset (frameAbove L t side).Cell) (p : (frameAbove L t side).Site j × Fin 4 × Fin 4) :
    p ∈ innerPlaquettes S j ↔ (siteEquivBelow hj p.1, p.2) ∈ innerPlaquettes (cellsBelow S) j := by
  simp only [innerPlaquettes, Finset.mem_filter, Finset.mem_product, Finset.mem_univ, and_true,
    plaquetteCorners_subset_iff]
  rw [mem_sitesOfCells_below_iff hodd hj S p.1, mem_sitesOfCells_below_iff hodd hj S (p.1 + _),
    mem_sitesOfCells_below_iff hodd hj S (p.1 + _), mem_sitesOfCells_below_iff hodd hj S (p.1 + _ + _)]
  simp only [map_add, siteEquivBelow_unitStep]
def bondEquivBelow {j : ℕ} (hj : j ≤ t + 1) :
    (frameAbove L t side).Site j × Fin 4 ≃ (frameBelow L t side).Site j × Fin 4 :=
  Equiv.prodCongr (siteEquivBelow hj).toEquiv (Equiv.refl _)
def plaquetteEquivBelow {j : ℕ} (hj : j ≤ t + 1) :
    (frameAbove L t side).Site j × Fin 4 × Fin 4 ≃ (frameBelow L t side).Site j × Fin 4 × Fin 4 :=
  Equiv.prodCongr (siteEquivBelow hj).toEquiv (Equiv.refl _)
theorem minimalAction_fieldBelow (hodd : Odd L) (a : ℝ) (S : Finset (frameAbove L t side).Cell) :
    ∀ (j : ℕ) (hj : j ≤ t + 1) (W : (frameAbove L t side).GaugeField j),
      minimalAction a S j W = minimalAction a (cellsBelow S) j (fieldBelow hj W) := by
  intro j
  induction j with
  | zero =>
    intro hj W
    show wilsonAction S W = wilsonAction (cellsBelow S) (fieldBelow hj W)
    unfold wilsonAction
    refine Finset.sum_equiv (plaquetteEquivBelow hj)
      (fun p => mem_innerPlaquettes_below_iff hodd hj S p) fun p _ => ?_
    show _ = 1 - ((plaquetteHolonomy (fieldBelow hj W) (siteEquivBelow hj p.1, p.2) : UnitQuaternion) : ℍ[ℝ]).re
    rw [plaquetteHolonomy_fieldBelow]
  | succ j ih =>
    intro hj V
    have hj' : j ≤ t + 1 := Nat.le_of_succ_le hj
    simp only [minimalAction]
    rw [← (fieldEquivBelow hj').iInf_comp]
    refine iInf_congr fun W => ?_
    show minimalAction a S j W + a * ∑ c ∈ innerBonds S (j + 1), blockFit W V c =
      minimalAction a (cellsBelow S) j (fieldBelow hj' W) +
        a * ∑ c ∈ innerBonds (cellsBelow S) (j + 1), blockFit (fieldBelow hj' W) (fieldBelow hj V) c
    rw [← ih hj' W]
    congr 2
    refine Finset.sum_equiv (bondEquivBelow hj) (fun b => mem_innerBonds_below_iff hodd hj S b) fun c _ => ?_
    exact (blockFit_fieldBelow hj W V c).symm
theorem isAdmissibleAmbient_below (hL : 0 < L) (h : IsAdmissibleAmbient (frameAbove L t side)) :
    IsAdmissibleAmbient (frameBelow L t side) := by
  rcases h with h | h
  · left
    intro i
    show L * side i = 0
    rw [show side i = 0 from h i, mul_zero]
  · right
    intro i
    show 64 ≤ L * side i
    exact (show 64 ≤ side i from h i).trans (Nat.le_mul_of_pos_left _ hL)
theorem natAbs_valMinAbs_intCast_le (n : ℕ) (d : ℤ) : ((d : ZMod n).valMinAbs).natAbs ≤ d.natAbs := by apply _root_.YangMills.Construction.BlockWeights.natAbs_valMinAbs_intCast_le <;> assumption
theorem exists_nearest_multiple (l a : ℤ) (hl : 0 ≤ l) :
    ∃ g r, a = (2 * l + 1) * g + r ∧ -l ≤ r ∧ r ≤ l ∧ g = (a + l) / (2 * l + 1) := by
  have hM : (0 : ℤ) < 2 * l + 1 := by linarith
  have e := Int.mul_ediv_add_emod (a + l) (2 * l + 1)
  have e0 := Int.emod_nonneg (a + l) hM.ne'
  have e1 := Int.emod_lt_of_pos (a + l) hM
  exact ⟨(a + l) / (2 * l + 1), (a + l) % (2 * l + 1) - l, by linarith, by linarith, by linarith, rfl⟩
theorem abs_le_of_odd_mul_eq (l e b m : ℤ) (hl : 0 ≤ l) (hm : 1 ≤ m) (h : (2 * l + 1) * e = b)
    (hb : |b| ≤ m + 2 * l) : |e| ≤ m := by
  rw [abs_le] at hb ⊢
  constructor
  · by_contra hc
    have : e + 1 ≤ -m := by
      have : e < -m := not_le.1 hc
      linarith
    nlinarith
  · by_contra hc
    have : m + 1 ≤ e := by
      have : m < e := not_le.1 hc
      linarith
    nlinarith
theorem natAbs_valMinAbs_cell_le (l c w g r : ℤ) (s : ℤ) (P Q : ℕ) (m : ℤ) (hl : 0 ≤ l) (hm : 1 ≤ m)
    (hP : (P : ℤ) = (2 * l + 1) * s) (hQ : (Q : ℤ) = s) (hg : |g| ≤ l) (hr : |r| ≤ l)
    (hd : (((((2 * l + 1) * c + g : ℤ) : ZMod P) - (((2 * l + 1) * w + r : ℤ) : ZMod P)).valMinAbs).natAbs ≤ m) :
    ((((c : ℤ) : ZMod Q) - ((w : ℤ) : ZMod Q)).valMinAbs).natAbs ≤ m := by
  set d := ((((2 * l + 1) * c + g : ℤ) : ZMod P) - (((2 * l + 1) * w + r : ℤ) : ZMod P)).valMinAbs with hdd
  have h1 : ((d : ℤ) : ZMod P) = (((2 * l + 1) * c + g - ((2 * l + 1) * w + r) : ℤ) : ZMod P) := by
    rw [hdd, ZMod.coe_valMinAbs]
    push_cast
    ring
  rw [ZMod.intCast_eq_intCast_iff_dvd_sub] at h1
  obtain ⟨K, hK⟩ := h1
  rw [hP] at hK
  set ee := c - w + s * (-K) with hee
  have h2 : (2 * l + 1) * ee = d - g + r := by
    rw [hee]
    linear_combination hK
  have hdabs : |d| ≤ m := by
    have : (d.natAbs : ℤ) ≤ m := hd
    rwa [Int.natCast_natAbs] at this
  have h3 : |ee| ≤ m := by
    refine abs_le_of_odd_mul_eq l ee _ m hl hm h2 ?_
    have e1 := abs_add_le (d - g) r
    have e2 := abs_sub d g
    linarith
  have h4 : (((c : ℤ) : ZMod Q) - ((w : ℤ) : ZMod Q)) = ((ee : ℤ) : ZMod Q) := by
    rw [← Int.cast_sub, ZMod.intCast_eq_intCast_iff_dvd_sub, hQ]
    exact ⟨-K, by rw [hee]; ring⟩
  rw [h4]
  have h5 := _root_.YangMills.Construction.BlockAverages.ColdFieldSecondVariation.natAbs_valMinAbs_intCast_le Q ee
  have h6 : (ee.natAbs : ℤ) ≤ m := by rwa [Int.natCast_natAbs]
  have h7 : ((((ee : ℤ) : ZMod Q).valMinAbs).natAbs : ℤ) ≤ ee.natAbs := by exact_mod_cast h5
  linarith
theorem isOrthantRegular_below (hodd : Odd L) {m : ℕ} (hm : 1 ≤ m) (S : Finset (frameAbove L t side).Cell)
    (hS : IsOrthantRegular S m) : IsOrthantRegular (cellsBelow S) m := by
  classical
  obtain ⟨l, hl0, hl, hl2⟩ := exists_eq_two_mul_add_one_of_odd hodd
  have hm' : (1 : ℤ) ≤ m := by exact_mod_cast hm
  intro z'
  have hw := fun i => exists_nearest_multiple l (siteCoords z' i) hl0
  choose w r₁ hwr hr1 hr2 _ using hw
  obtain ⟨eps, heps, hreg⟩ := hS (siteOfCoords (frameAbove L t side).top w)
  refine ⟨eps, heps, ?_⟩
  intro q hq hd h hsign hh
  obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 hq
  have e3 : (frameAbove L t side).top - (t + 1) = 1 := by
    show t + 1 + 1 - (t + 1) = 1
    omega
  rw [mem_sitesOfCells_iff, e3, pow_one] at hy
  obtain ⟨z₀, hz₀, g₀, hg₀, rfl⟩ := hy
  rw [_root_.YangMills.Construction.BlockAverages.ColdFieldSecondVariation.mem_centredCube_iff, hl2] at hg₀
  have hy : cellCentre (F := frameAbove L t side) (t + 1) z₀ + siteOfCoords (t + 1) g₀ =
      siteOfCoords (F := frameAbove L t side) (t + 1) ((fun i => (L : ℤ) * siteCoords z₀ i) + g₀) := by
    unfold cellCentre
    rw [e3, pow_one, ← siteOfCoords_add]
  have hdist : cellSupDist z₀ (siteOfCoords (frameAbove L t side).top w) ≤ m := by
    refine Finset.sup_le fun i _ => ?_
    have hdi : ((siteEquivBelow (le_refl (t + 1)) (cellCentre (t + 1) z₀ + siteOfCoords (t + 1) g₀) i -
        z' i).valMinAbs).natAbs ≤ m :=
      (Finset.le_sup (f := fun i => ((siteEquivBelow (le_refl (t + 1))
        (cellCentre (t + 1) z₀ + siteOfCoords (t + 1) g₀) i - z' i).valMinAbs).natAbs)
        (Finset.mem_univ i)).trans hd
    have hq : siteEquivBelow (le_refl (t + 1)) (cellCentre (t + 1) z₀ + siteOfCoords (t + 1) g₀) i =
        ((((2 * l + 1) * siteCoords z₀ i + g₀ i : ℤ)) : ZMod ((frameBelow L t side).period (t + 1) i)) := by
      rw [hy, siteEquivBelow_siteOfCoords]
      show ((((L : ℤ) * siteCoords z₀ i + g₀ i : ℤ)) : ZMod ((frameBelow L t side).period (t + 1) i)) = _
      rw [hl]
    have hzi : z' i = ((((2 * l + 1) * w i + r₁ i : ℤ)) : ZMod ((frameBelow L t side).period (t + 1) i)) := by
      rw [← hwr i]
      exact (congrFun (_root_.YangMills.Construction.BlockAverages.siteOfCoords_siteCoords z') i).symm
    rw [hq, hzi] at hdi
    have hP : (((frameBelow L t side).period (t + 1) i : ℕ) : ℤ) = (2 * l + 1) * (side i : ℤ) := by
      simp only [BlockFrame.period, BlockFrame.top, Nat.sub_self, pow_zero, mul_one]
      push_cast
      rw [hl]
    have hQ : (((frameAbove L t side).period (frameAbove L t side).top i : ℕ) : ℤ) = (side i : ℤ) := by
      simp only [BlockFrame.period, Nat.sub_self, pow_zero, mul_one]
    have hres := natAbs_valMinAbs_cell_le l (siteCoords z₀ i) (w i) (g₀ i) (r₁ i) (side i) _ _ (m : ℤ)
      hl0 hm' hP hQ (abs_le.2 ⟨(hg₀ i).1, (hg₀ i).2⟩) (abs_le.2 ⟨hr1 i, hr2 i⟩) (by exact_mod_cast hdi)
    have e : z₀ i = ((siteCoords z₀ i : ℤ) : ZMod ((frameAbove L t side).period (frameAbove L t side).top i)) :=
      (congrFun (_root_.YangMills.Construction.BlockAverages.siteOfCoords_siteCoords z₀) i).symm
    have hres' : (((z₀ i - siteOfCoords (F := frameAbove L t side) (frameAbove L t side).top w i).valMinAbs).natAbs
        : ℤ) ≤ m := by
      rw [e]
      exact hres
    exact_mod_cast hres'
  have hgr := fun i => exists_nearest_multiple l (g₀ i + h i) hl0
  choose g r₂ hgr1 hr3 hr4 hg using hgr
  have hsg : ∀ i, 0 ≤ eps i * g i := by
    intro i
    have hM : (0 : ℤ) < 2 * l + 1 := by linarith
    have hgi := hgr1 i
    rcases heps i with he | he
    · have hh0 : 0 ≤ h i := by
        have := hsign i
        rwa [he, one_mul] at this
      rw [he, one_mul, hg i]
      have := (hg₀ i).1
      exact Int.ediv_nonneg (by linarith) hM.le
    · have hh0 : h i ≤ 0 := by
        have := hsign i
        rw [he] at this
        linarith
      rw [he]
      have h1 := (hg₀ i).2
      have hr := hr3 i
      by_contra hc
      have : 1 ≤ g i := by
        have : 0 < g i := by
          have := not_le.1 hc
          linarith
        linarith
      nlinarith
  have hgb : ∀ i, |g i| ≤ (m : ℤ) := by
    intro i
    have hM : (0 : ℤ) < 2 * l + 1 := by linarith
    have hgi := hgr1 i
    have hh' := abs_le.1 (hh i)
    have h1 := hg₀ i
    rw [abs_le]
    constructor
    · by_contra hc
      have : g i + 1 ≤ -(m : ℤ) := by
        have : g i < -(m : ℤ) := not_le.1 hc
        linarith
      have hr := hr4 i
      nlinarith
    · by_contra hc
      have : (m : ℤ) + 1 ≤ g i := by
        have : (m : ℤ) < g i := not_le.1 hc
        linarith
      have hr := hr3 i
      nlinarith
  have hnew := hreg z₀ hz₀ hdist g hsg hgb
  refine Finset.mem_image.2
    ⟨cellCentre (t + 1) (z₀ + siteOfCoords (frameAbove L t side).top g) + siteOfCoords (t + 1) r₂, ?_, ?_⟩
  · rw [mem_sitesOfCells_iff, e3, pow_one]
    refine ⟨_, hnew, r₂, ?_, rfl⟩
    rw [_root_.YangMills.Construction.BlockAverages.ColdFieldSecondVariation.mem_centredCube_iff, hl2]
    exact fun i => ⟨hr3 i, hr4 i⟩
  · rw [cellCentre_add (t + 1) (Nat.le_succ _) z₀ g, e3, pow_one]
    have e5 : (fun i => (L : ℤ) * g i) + r₂ = g₀ + h := by
      funext i
      simp only [Pi.add_apply]
      rw [hgr1 i, hl]
    rw [← siteEquivBelow_siteOfCoords (le_refl (t + 1)) h, ← map_add, add_assoc, add_assoc,
      ← siteOfCoords_add, ← siteOfCoords_add, e5]
theorem isCold_below (hodd : Odd L) (S : Finset (frameAbove L t side).Cell) {σ : ℝ}
    {W : (frameAbove L t side).GaugeField (t + 1)} (h : IsCold S (t + 1) σ W) :
    IsCold (cellsBelow S) (frameBelow L t side).top σ (fieldBelow (le_refl (t + 1)) W) := by
  intro p hp
  obtain ⟨p', rfl⟩ := (plaquetteEquivBelow (L := L) (side := side) (le_refl (t + 1))).surjective p
  have hp' := (mem_innerPlaquettes_below_iff hodd (le_refl (t + 1)) S p').2 hp
  have := h p' hp'
  unfold plaquetteDefect at this ⊢
  show ‖((plaquetteHolonomy (fieldBelow (le_refl (t + 1)) W) (siteEquivBelow (le_refl (t + 1)) p'.1, p'.2) :
    UnitQuaternion) : ℍ[ℝ]) - 1‖ < σ
  rw [plaquetteHolonomy_fieldBelow]
  exact this
def variationBelow {j : ℕ} (hj : j ≤ t + 1) (v : (frameAbove L t side).Site j → Fin 4 → imaginaryQuaternions) :
    (frameBelow L t side).Site j → Fin 4 → imaginaryQuaternions :=
  fun x i => v ((siteEquivBelow hj).symm x) i
theorem variationBelow_apply {j : ℕ} (hj : j ≤ t + 1)
    (v : (frameAbove L t side).Site j → Fin 4 → imaginaryQuaternions)
    (x : (frameAbove L t side).Site j) (i : Fin 4) : variationBelow hj v (siteEquivBelow hj x) i = v x i := by
  simp [variationBelow]
theorem linkValueVariation_below {j : ℕ} (hj : j ≤ t + 1) (W : (frameAbove L t side).GaugeField j)
    (v : (frameAbove L t side).Site j → Fin 4 → imaginaryQuaternions) (x : (frameAbove L t side).Site j)
    (st : PathStep) :
    linkValueVariation (fieldBelow hj W) (variationBelow hj v) (siteEquivBelow hj x) st =
      linkValueVariation W v x st := by
  unfold linkValueVariation
  split_ifs
  · rw [variationBelow_apply]
  · rw [← siteEquivBelow_unitStep hj, ← map_sub, variationBelow_apply, fieldBelow_apply]
theorem pathHolonomyVariation_below {j : ℕ} (hj : j ≤ t + 1) (W : (frameAbove L t side).GaugeField j)
    (v : (frameAbove L t side).Site j → Fin 4 → imaginaryQuaternions) (l : List PathStep) :
    ∀ x, pathHolonomyVariation (fieldBelow hj W) (variationBelow hj v) (siteEquivBelow hj x) l =
      pathHolonomyVariation W v x l := by
  induction l with
  | nil => intro x; rfl
  | cons st r ih =>
    intro x
    simp only [pathHolonomyVariation]
    rw [linkValueVariation_below, linkValue_fieldBelow, ← siteEquivBelow_stepDisplacement hj, ← map_add, ih]
theorem variationCurl_below {j : ℕ} (hj : j ≤ t + 1) (W : (frameAbove L t side).GaugeField j)
    (v : (frameAbove L t side).Site j → Fin 4 → imaginaryQuaternions)
    (p : (frameAbove L t side).Site j × Fin 4 × Fin 4) :
    variationCurl (fieldBelow hj W) (variationBelow hj v) (siteEquivBelow hj p.1, p.2) = variationCurl W v p :=
  pathHolonomyVariation_below hj W v _ p.1
theorem expRotatedField_below {j : ℕ} (hj : j ≤ t + 1) (W : (frameAbove L t side).GaugeField j)
    (v : (frameAbove L t side).Site j → Fin 4 → imaginaryQuaternions) :
    fieldBelow hj (expRotatedField v W) = expRotatedField (variationBelow hj v) (fieldBelow hj W) := rfl
theorem sum_variationCurl_below (hodd : Odd L) {j : ℕ} (hj : j ≤ t + 1) (S : Finset (frameAbove L t side).Cell)
    (W : (frameAbove L t side).GaugeField j) (v : (frameAbove L t side).Site j → Fin 4 → imaginaryQuaternions) :
    ∑ p ∈ innerPlaquettes (cellsBelow S) j, ‖variationCurl (fieldBelow hj W) (variationBelow hj v) p‖ ^ 2 =
      ∑ p ∈ innerPlaquettes S j, ‖variationCurl W v p‖ ^ 2 := by
  symm
  refine Finset.sum_equiv (plaquetteEquivBelow hj) (fun p => mem_innerPlaquettes_below_iff hodd hj S p)
    fun p _ => ?_
  show _ = ‖variationCurl (fieldBelow hj W) (variationBelow hj v) (siteEquivBelow hj p.1, p.2)‖ ^ 2
  rw [variationCurl_below]
theorem sum_innerBonds_below {E : Type} [AddCommMonoid E] (hodd : Odd L) {j : ℕ} (hj : j ≤ t + 1)
    (S : Finset (frameAbove L t side).Cell) (v : (frameAbove L t side).Site j → Fin 4 → imaginaryQuaternions)
    (f : imaginaryQuaternions → E) :
    ∑ b ∈ innerBonds (cellsBelow S) j, f (variationBelow hj v b.1 b.2) = ∑ b ∈ innerBonds S j, f (v b.1 b.2) := by
  symm
  refine Finset.sum_equiv (bondEquivBelow hj) (fun b => mem_innerBonds_below_iff hodd hj S b) fun b _ => ?_
  show _ = f (variationBelow hj v (siteEquivBelow hj b.1) b.2)
  rw [variationBelow_apply]
def imaginaryUnit : Fin 3 → imaginaryQuaternions :=
  ![⟨⟨0, 1, 0, 0⟩, rfl⟩, ⟨⟨0, 0, 1, 0⟩, rfl⟩, ⟨⟨0, 0, 0, 1⟩, rfl⟩]
def imaginaryComponent (e : Fin 3) : imaginaryQuaternions →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun w => ![(w : ℍ[ℝ]).imI, (w : ℍ[ℝ]).imJ, (w : ℍ[ℝ]).imK] e
      map_add' := fun a b => by fin_cases e <;> rfl
      map_smul' := fun r a => by fin_cases e <;> rfl }
theorem sum_imaginaryComponent_smul (w : imaginaryQuaternions) :
    ∑ e, imaginaryComponent e w • imaginaryUnit e = w := by
  have hw : (w : ℍ[ℝ]).re = 0 := w.2
  apply Subtype.ext
  rw [Fin.sum_univ_three]
  have e0 : imaginaryComponent 0 w = (w : ℍ[ℝ]).imI := rfl
  have e1 : imaginaryComponent 1 w = (w : ℍ[ℝ]).imJ := rfl
  have e2 : imaginaryComponent 2 w = (w : ℍ[ℝ]).imK := rfl
  rw [e0, e1, e2]
  ext
  · show (w : ℍ[ℝ]).imI * 0 + (w : ℍ[ℝ]).imJ * 0 + (w : ℍ[ℝ]).imK * 0 = (w : ℍ[ℝ]).re
    rw [hw]
    ring
  · show (w : ℍ[ℝ]).imI * 1 + (w : ℍ[ℝ]).imJ * 0 + (w : ℍ[ℝ]).imK * 0 = (w : ℍ[ℝ]).imI
    ring
  · show (w : ℍ[ℝ]).imI * 0 + (w : ℍ[ℝ]).imJ * 1 + (w : ℍ[ℝ]).imK * 0 = (w : ℍ[ℝ]).imJ
    ring
  · show (w : ℍ[ℝ]).imI * 0 + (w : ℍ[ℝ]).imJ * 0 + (w : ℍ[ℝ]).imK * 1 = (w : ℍ[ℝ]).imK
    ring
theorem analyticAt_expRotatedField_bondListSpread {F : BlockFrame} (G : F.GaugeField F.top → ℝ)
    (V : F.GaugeField F.top) (h : IsBondAnalyticAt G V) (k : ℕ) (c : Fin k → F.Site F.top × Fin 4) :
    AnalyticAt ℝ (fun ζ : Fin k → imaginaryQuaternions => G (expRotatedField (bondListSpread c ζ) V)) 0 := by
  classical
  let q : Fin (k * 3) ≃ Fin k × Fin 3 := finProdFinEquiv.symm
  let cc : Fin (k * 3) → F.Site F.top × Fin 4 := fun n => c (q n).1
  let X : Fin (k * 3) → imaginaryQuaternions := fun n => imaginaryUnit (q n).2
  let Λ : (Fin k → imaginaryQuaternions) →L[ℝ] (Fin (k * 3) → ℝ) :=
    ContinuousLinearMap.pi fun n => (imaginaryComponent (q n).2).comp (ContinuousLinearMap.proj (q n).1)
  have hs : ∀ ζ : Fin k → imaginaryQuaternions, bondSpread cc X (Λ ζ) = bondListSpread c ζ := by
    intro ζ
    funext y i
    simp only [bondSpread, bondListSpread]
    rw [← Equiv.sum_comp q.symm, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun l _ => ?_
    by_cases hc : c l = (y, i)
    · simp only [cc, X, Λ, Equiv.apply_symm_apply, hc, if_true, ContinuousLinearMap.pi_apply,
        ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply]
      exact sum_imaginaryComponent_smul (ζ l)
    · simp [cc, hc]
  have h1 := h (k * 3) cc X
  have h2 : AnalyticAt ℝ (fun σ : Fin (k * 3) → ℝ => G (rotatedField (bondSpread cc X σ) V)) (Λ 0) := by
    rw [map_zero]
    exact h1
  have h3 := h2.comp (Λ.analyticAt 0)
  have e : (fun ζ : Fin k → imaginaryQuaternions => G (expRotatedField (bondListSpread c ζ) V)) =
      (fun σ : Fin (k * 3) → ℝ => G (rotatedField (bondSpread cc X σ) V)) ∘ Λ := by
    funext ζ
    simp only [Function.comp, hs]
    rfl
  rw [e]
  exact h3
theorem variationBelow_bondListSpread {k : ℕ} {j : ℕ} (hj : j ≤ t + 1)
    (c : Fin k → (frameAbove L t side).Site j × Fin 4) (ζ : Fin k → imaginaryQuaternions) :
    variationBelow hj (bondListSpread c ζ) =
      bondListSpread (fun l => (siteEquivBelow hj (c l).1, (c l).2)) ζ := by
  funext y i
  simp only [variationBelow, bondListSpread]
  refine Finset.sum_congr rfl fun l _ => ?_
  have : c l = ((siteEquivBelow hj).symm y, i) ↔ (siteEquivBelow hj (c l).1, (c l).2) = (y, i) := by
    constructor
    · intro h
      rw [h]
      simp
    · intro h
      have h1 := congrArg Prod.fst h
      have h2 := congrArg Prod.snd h
      simp only at h1 h2
      refine Prod.ext ?_ h2
      simp [← h1]
  simp only [this]
theorem secondVariation_succ (a ca C σ : ℝ) (hodd : Odd L) {m : ℕ} (hm : 1024 ≤ m)
    (S : Finset (frameAbove L t side).Cell) (hamb : IsAdmissibleAmbient (frameAbove L t side))
    (hreg : IsOrthantRegular S m) (W : (frameAbove L t side).GaugeField (t + 1))
    (hcold : IsCold S (t + 1) σ W)
    (hAn : IsAdmissibleAmbient (frameBelow L t side) → IsOrthantRegular (cellsBelow S) m →
      IsCold (cellsBelow S) (frameBelow L t side).top σ (fieldBelow (le_refl (t + 1)) W) →
      IsBondAnalyticAt (minimalAction a (cellsBelow S) (frameBelow L t side).top)
        (fieldBelow (le_refl (t + 1)) W))
    (hFl : IsAdmissibleAmbient (frameBelow L t side) → IsOrthantRegular (cellsBelow S) m →
      IsCold (cellsBelow S) (frameBelow L t side).top σ (fieldBelow (le_refl (t + 1)) W) →
      ∀ v : (frameBelow L t side).Site (frameBelow L t side).top → Fin 4 → imaginaryQuaternions,
        (∀ b, b ∉ innerBonds (cellsBelow S) (frameBelow L t side).top → v b.1 b.2 = 0) →
        ca * ∑ p ∈ innerPlaquettes (cellsBelow S) (frameBelow L t side).top,
              ‖variationCurl (fieldBelow (le_refl (t + 1)) W) v p‖ ^ 2 -
            C * σ * ∑ b ∈ innerBonds (cellsBelow S) (frameBelow L t side).top, ‖v b.1 b.2‖ ^ 2 ≤
          deriv (deriv fun τ : ℝ => minimalAction a (cellsBelow S) (frameBelow L t side).top
            (expRotatedField (fun x i => τ • v x i) (fieldBelow (le_refl (t + 1)) W))) 0 ∧
        |deriv (fun τ : ℝ => minimalAction a (cellsBelow S) (frameBelow L t side).top
            (expRotatedField (fun x i => τ • v x i) (fieldBelow (le_refl (t + 1)) W))) 0| ≤
          C * σ * ∑ b ∈ innerBonds (cellsBelow S) (frameBelow L t side).top, ‖v b.1 b.2‖) :
    (∀ (k : ℕ) (c : Fin k → (frameAbove L t side).Site (t + 1) × Fin 4),
      AnalyticAt ℝ (fun ζ : Fin k → imaginaryQuaternions =>
        minimalAction a S (t + 1) (expRotatedField (bondListSpread c ζ) W)) 0) ∧
    ∀ v : (frameAbove L t side).Site (t + 1) → Fin 4 → imaginaryQuaternions,
      (∀ b, b ∉ innerBonds S (t + 1) → v b.1 b.2 = 0) →
      ca * ∑ p ∈ innerPlaquettes S (t + 1), ‖variationCurl W v p‖ ^ 2 -
            C * σ * ∑ b ∈ innerBonds S (t + 1), ‖v b.1 b.2‖ ^ 2 ≤
          deriv (deriv fun τ : ℝ =>
            minimalAction a S (t + 1) (expRotatedField (fun x i => τ • v x i) W)) 0 ∧
        |deriv (fun τ : ℝ => minimalAction a S (t + 1) (expRotatedField (fun x i => τ • v x i) W)) 0| ≤
          C * σ * ∑ b ∈ innerBonds S (t + 1), ‖v b.1 b.2‖ := by
  have hL : 0 < L := hodd.pos
  have hamb' := isAdmissibleAmbient_below hL hamb
  have hreg' := isOrthantRegular_below hodd (by omega) S hreg
  have hcold' := isCold_below hodd S hcold
  refine ⟨fun k c => ?_, fun v hv => ?_⟩
  · have h1 := analyticAt_expRotatedField_bondListSpread _ _ (hAn hamb' hreg' hcold') k
      (fun l => (siteEquivBelow (le_refl (t + 1)) (c l).1, (c l).2))
    have e : (fun ζ : Fin k → imaginaryQuaternions =>
          minimalAction a S (t + 1) (expRotatedField (bondListSpread c ζ) W)) =
        fun ζ : Fin k → imaginaryQuaternions => minimalAction a (cellsBelow S) (frameBelow L t side).top
          (expRotatedField (bondListSpread (fun l => (siteEquivBelow (le_refl (t + 1)) (c l).1, (c l).2)) ζ)
            (fieldBelow (le_refl (t + 1)) W)) := by
      funext ζ
      rw [minimalAction_fieldBelow hodd a S (t + 1) le_rfl, expRotatedField_below, variationBelow_bondListSpread]
    rw [e]
    exact h1
  · have hvd : ∀ b, b ∉ innerBonds (cellsBelow S) (frameBelow L t side).top →
        variationBelow (le_refl (t + 1)) v b.1 b.2 = 0 := by
      intro b hb
      refine hv ((siteEquivBelow le_rfl).symm b.1, b.2) fun h => hb ?_
      have := (mem_innerBonds_below_iff hodd le_rfl S _).1 h
      simpa using this
    obtain ⟨b1, b2⟩ := hFl hamb' hreg' hcold' (variationBelow le_rfl v) hvd
    have e : (fun τ : ℝ => minimalAction a S (t + 1) (expRotatedField (fun x i => τ • v x i) W)) =
        fun τ : ℝ => minimalAction a (cellsBelow S) (frameBelow L t side).top
          (expRotatedField (fun x i => τ • variationBelow le_rfl v x i) (fieldBelow (le_refl (t + 1)) W)) := by
      funext τ
      rw [minimalAction_fieldBelow hodd a S (t + 1) le_rfl, expRotatedField_below]
      rfl
    rw [e]
    have e2 := sum_variationCurl_below hodd (le_refl (t + 1)) S W v
    have e3 : ∑ b ∈ innerBonds (cellsBelow S) (t + 1), ‖variationBelow (le_refl (t + 1)) v b.1 b.2‖ ^ 2 =
        ∑ b ∈ innerBonds S (t + 1), ‖v b.1 b.2‖ ^ 2 :=
      sum_innerBonds_below hodd (le_refl (t + 1)) S v (fun w => ‖w‖ ^ 2)
    have e4 : ∑ b ∈ innerBonds (cellsBelow S) (t + 1), ‖variationBelow (le_refl (t + 1)) v b.1 b.2‖ =
        ∑ b ∈ innerBonds S (t + 1), ‖v b.1 b.2‖ :=
      sum_innerBonds_below hodd (le_refl (t + 1)) S v (fun w => ‖w‖)
    rw [← e2, ← e3, ← e4]
    exact ⟨b1, b2⟩
theorem sub_le_of_weaker_constants {ca ca' C C' σ A B D : ℝ} (h1 : ca' ≤ ca) (h2 : C ≤ C') (hσ : 0 ≤ σ)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (h : ca * A - C * σ * B ≤ D) : ca' * A - C' * σ * B ≤ D := by
  have e1 : ca' * A ≤ ca * A := by gcongr
  have e2 : C * σ * B ≤ C' * σ * B := by gcongr
  linarith
theorem coldFieldSecondVariation (hW : wilsonActionSecondVariationStatement)
    (hB : coldTopSecondVariationStatement) (hS : analyticCellSharesStatement) :
    coldFieldSecondVariationStatement := by
  intro a ha
  obtain ⟨ca, hca, L₁, hB'⟩ := hB a ha
  obtain ⟨δ₀, hδ₀, hS'⟩ := hS a ha
  obtain ⟨L₂, hS''⟩ := hS' δ₀ hδ₀ le_rfl
  refine ⟨min ca 1, lt_min hca one_pos, max L₁ L₂, fun L hodd hL => ?_⟩
  obtain ⟨C₁, σ₁, hC₁, hσ₁, hBL⟩ := hB' L hodd (le_of_max_le_left hL)
  obtain ⟨σ₂, N, hσ₂, hN, hSL⟩ := hS'' L hodd (le_of_max_le_right hL)
  refine ⟨max C₁ 64, min σ₁ σ₂, lt_max_of_lt_left hC₁, lt_min hσ₁ hσ₂, ?_⟩
  intro F m S hFL hamb hm hreg σ W hσ hσ₀ hcold
  have hs1 : σ ≤ σ₁ := hσ₀.trans (min_le_left _ _)
  have hs2 : σ ≤ σ₂ := hσ₀.trans (min_le_right _ _)
  obtain ⟨L', t, side⟩ := F
  obtain rfl : L' = L := hFL
  cases t with
  | zero =>
    obtain ⟨h1, h2⟩ := hW _ S σ W hσ hcold
    refine ⟨fun k c => h1 k c, fun v _ => ?_⟩
    obtain ⟨e1, e2⟩ := h2 v
    exact ⟨sub_le_of_weaker_constants (ca := 1) (C := 64) (min_le_right _ _) (le_max_right _ _) hσ.le
        (Finset.sum_nonneg fun p _ => by positivity) (Finset.sum_nonneg fun b _ => by positivity)
        (by rw [one_mul]; exact e1),
      e2.trans (by
        have h0 : 0 ≤ ∑ b ∈ innerBonds S 0, ‖v b.1 b.2‖ := Finset.sum_nonneg fun b _ => norm_nonneg _
        have h1 : (16 : ℝ) ≤ max C₁ 64 := le_trans (by norm_num) (le_max_right _ _)
        show 16 * σ * ∑ b ∈ innerBonds S 0, ‖v b.1 b.2‖ ≤ max C₁ 64 * σ * ∑ b ∈ innerBonds S 0, ‖v b.1 b.2‖
        gcongr)⟩
  | succ t =>
    refine secondVariation_succ a (min ca 1) (max C₁ 64) σ hodd hm S hamb hreg W hcold
      (fun h1 h2 h3 => ((hSL (frameBelow L' t side) m (cellsBelow S) rfl h1 hm h2 σ _ hσ hs2 h3).1).1)
      (fun h1 h2 h3 v hv => ?_)
    obtain ⟨b1, b2⟩ := hBL (frameBelow L' t side) m (cellsBelow S) rfl h1 hm h2 σ _ hσ hs1 h3 v hv
    refine ⟨sub_le_of_weaker_constants (min_le_left _ _) (le_max_left _ _) hσ.le
      (Finset.sum_nonneg fun p _ => by positivity) (Finset.sum_nonneg fun b _ => by positivity) b1,
      b2.trans ?_⟩
    have h0 : 0 ≤ ∑ b ∈ innerBonds (cellsBelow S) (frameBelow L' t side).top, ‖v b.1 b.2‖ :=
      Finset.sum_nonneg fun b _ => norm_nonneg _
    have h1' : C₁ ≤ max C₁ 64 := le_max_left _ _
    gcongr
end YangMills.Construction.BlockAverages.ColdFieldSecondVariation
end
