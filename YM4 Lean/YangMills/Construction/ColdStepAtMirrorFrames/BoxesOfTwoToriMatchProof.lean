import YangMills.Construction.ColdChainAtEveryLevel.PathsOnTheLattice
import YangMills.Construction.ColdStepAtMirrorFrames.BlockEnergyOnTwoToriProof
import YangMills.Construction.ColdStepAtMirrorFrames.BoxesOfTwoToriMatch
import YangMills.Construction.HoleBesideASecondHole.WhatAHoleSavesAtParametersProof
import YangMills.Construction.RunningCouplingSlope.ValueOfTheDensityOfTheStepOnTwoToriAtParametersProof
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open BlockAverages
namespace ColdStepAtMirrorFrames
namespace OffsetCorrespondence
variable {F : BlockFrame}
private lemma period_top (F : BlockFrame) (i : Fin 4) : F.period F.top i = F.extent i := by apply _root_.YangMills.Construction.GaugeFixing.period_top <;> assumption
private lemma period_depth (F : BlockFrame) (i : Fin 4) :
    F.period F.depth i = F.extent i * F.blockSide := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.MinimizingChart.period_depth <;> assumption
private lemma top_sub_depth (F : BlockFrame) : F.top - F.depth = 1 := by simp [BlockFrame.top]
private def halfSide (L : ℕ) : ℤ := ((L : ℤ) - 1) / 2
private lemma cast_eq_two_mul_halfSide_add_one {L : ℕ} (h : Odd L) : (L : ℤ) = 2 * halfSide L + 1 := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.TwoTori.cast_eq_two_mul_halfSide_add_one <;> assumption
private lemma halfSide_nonneg {L : ℕ} (h : Odd L) : 0 ≤ halfSide L := by
  obtain ⟨k, rfl⟩ := h
  simp only [halfSide]
  push_cast
  omega
private lemma mem_centredCube_iff {L : ℕ} {o : Fin 4 → ℤ} :
    o ∈ centredCube L ↔ ∀ i, -halfSide L ≤ o i ∧ o i ≤ halfSide L := by apply _root_.YangMills.Construction.LatticePaths.mem_centredCube_iff <;> assumption
private lemma siteOfCoords_eq_iff {j : ℕ} {z w : Fin 4 → ℤ} :
    (siteOfCoords j z : F.Site j) = siteOfCoords j w ↔ ∀ i, (F.period j i : ℤ) ∣ z i - w i := by
  constructor
  · intro h i
    exact (ZMod.intCast_eq_intCast_iff_dvd_sub (w i) (z i) _).1 (congrFun h i).symm
  · intro h
    funext i
    exact ((ZMod.intCast_eq_intCast_iff_dvd_sub (w i) (z i) _).2 (h i)).symm
private lemma siteOfCoords_add {j : ℕ} (z w : Fin 4 → ℤ) :
    (siteOfCoords j (z + w) : F.Site j) = siteOfCoords j z + siteOfCoords j w := by apply _root_.YangMills.Construction.GaugeFixing.siteOfCoords_add <;> assumption
private lemma siteOfCoords_siteCoords {j : ℕ} (x : F.Site j) : siteOfCoords j (siteCoords x) = x := by apply _root_.YangMills.Construction.BlockAverages.siteOfCoords_siteCoords <;> assumption
private lemma siteCoords_siteOfCoords {j : ℕ} (z : Fin 4 → ℤ) (i : Fin 4) :
    siteCoords (siteOfCoords j z : F.Site j) i = z i % (F.period j i : ℤ) := by apply _root_.YangMills.Construction.BlockLines.siteCoords_siteOfCoords <;> assumption
private lemma enclosingCell_siteOfCoords (hodd : Odd F.blockSide) (c o : Fin 4 → ℤ)
    (ho : o ∈ centredCube F.blockSide) :
    enclosingCell (siteOfCoords F.depth (fun i => (F.blockSide : ℤ) * c i + o i) : F.Site F.depth) =
      (siteOfCoords F.top c : F.Cell) := by
  unfold enclosingCell
  rw [siteOfCoords_eq_iff]
  intro i
  have hlo := (mem_centredCube_iff.1 ho i).1
  have hhi := (mem_centredCube_iff.1 ho i).2
  have hL := cast_eq_two_mul_halfSide_add_one hodd
  have hhh : ((F.blockSide : ℤ) - 1) / 2 = halfSide F.blockSide := rfl
  rw [top_sub_depth, pow_one, period_top, siteCoords_siteOfCoords, period_depth, hhh]
  push_cast
  have hL0 : (F.blockSide : ℤ) ≠ 0 := by omega
  set q := ((F.blockSide : ℤ) * c i + o i) / ((F.extent i : ℤ) * F.blockSide) with hq
  have e1 : ((F.blockSide : ℤ) * c i + o i) % ((F.extent i : ℤ) * F.blockSide) + halfSide F.blockSide =
      (o i + halfSide F.blockSide) + (F.blockSide : ℤ) * (c i - F.extent i * q) := by
    rw [Int.emod_def]
    ring
  rw [e1, Int.add_mul_ediv_left _ _ hL0, Int.ediv_eq_zero_of_lt (by omega) (by omega)]
  exact ⟨-q, by ring⟩
private lemma cellCentre_siteOfCoords (c : Fin 4 → ℤ) :
    cellCentre F.depth (siteOfCoords F.top c : F.Cell) =
      (siteOfCoords F.depth (fun i => (F.blockSide : ℤ) * c i) : F.Site F.depth) := by apply _root_.YangMills.Construction.HoleBounds.FromThresholds.cellCentre_siteOfCoords <;> assumption
private lemma exists_cell_offset_decomp (hodd : Odd F.blockSide) (x : F.Site F.depth) :
    ∃ c o : Fin 4 → ℤ, o ∈ centredCube F.blockSide ∧
      x = siteOfCoords F.depth (fun i => (F.blockSide : ℤ) * c i + o i) := by
  have hL := cast_eq_two_mul_halfSide_add_one hodd
  have hpos : (0 : ℤ) < F.blockSide := by omega
  refine ⟨fun i => (siteCoords x i + halfSide F.blockSide) / F.blockSide,
    fun i => (siteCoords x i + halfSide F.blockSide) % F.blockSide - halfSide F.blockSide,
    mem_centredCube_iff.2 fun i => ?_, ?_⟩
  · have h1 := Int.emod_nonneg (siteCoords x i + halfSide F.blockSide) hpos.ne'
    have h2 := Int.emod_lt_of_pos (siteCoords x i + halfSide F.blockSide) hpos
    constructor <;> omega
  · conv_lhs => rw [← siteOfCoords_siteCoords x]
    congr 1
    funext i
    have := Int.mul_ediv_add_emod (siteCoords x i + halfSide F.blockSide) F.blockSide
    linarith
private lemma fineBondAt_fst (Y : F.Cell) (h o : Fin 4 → ℤ) (i : Fin 4) :
    (fineBondAt Y h o i).1 =
      siteOfCoords F.depth (fun k => (F.blockSide : ℤ) * (siteCoords Y + h) k + o k) := by
  have e : Y + siteOfCoords F.top h = siteOfCoords F.top (siteCoords Y + h) := by
    rw [siteOfCoords_add, siteOfCoords_siteCoords]
  simp only [fineBondAt]
  rw [e, cellCentre_siteOfCoords, ← siteOfCoords_add]
  rfl
private lemma enclosingCell_fineBondAt (hodd : Odd F.blockSide) (Y : F.Cell) (h o : Fin 4 → ℤ)
    (i : Fin 4) (ho : o ∈ centredCube F.blockSide) :
    enclosingCell (fineBondAt Y h o i).1 = Y + siteOfCoords F.top h := by
  rw [fineBondAt_fst, enclosingCell_siteOfCoords hodd _ _ ho, siteOfCoords_add, siteOfCoords_siteCoords]
private lemma isCrossingBond_iff (hodd : Odd F.blockSide) (hs : ∀ i, 2 ≤ F.extent i) (c o : Fin 4 → ℤ)
    (ho : o ∈ centredCube F.blockSide) (i : Fin 4) :
    IsCrossingBond ((siteOfCoords F.depth (fun k => (F.blockSide : ℤ) * c k + o k) : F.Site F.depth), i) ↔
      o i = halfSide F.blockSide := by
  have hL := cast_eq_two_mul_halfSide_add_one hodd
  have hu : ∀ w : Fin 4 → ℤ, (siteOfCoords F.depth w : F.Site F.depth) + unitStep F.depth i =
      siteOfCoords F.depth (w + Pi.single i 1) := fun w => by
    rw [siteOfCoords_add]
    rfl
  unfold IsCrossingBond
  simp only
  rw [hu, enclosingCell_siteOfCoords hodd c o ho]
  by_cases hi : o i = halfSide F.blockSide
  · simp only [hi, iff_true]
    have e : (fun k => (F.blockSide : ℤ) * c k + o k) + Pi.single i 1 =
        fun k => (F.blockSide : ℤ) * (c + Pi.single i 1 : Fin 4 → ℤ) k +
          (o + Pi.single i (1 - (F.blockSide : ℤ)) : Fin 4 → ℤ) k := by
      funext k
      by_cases hk : k = i
      · subst hk
        simp only [Pi.add_apply, Pi.single_eq_same]
        ring
      · simp [hk]
    have ho' : o + Pi.single i (1 - (F.blockSide : ℤ)) ∈ centredCube F.blockSide := by
      refine mem_centredCube_iff.2 fun k => ?_
      by_cases hk : k = i
      · subst hk
        simp only [Pi.add_apply, Pi.single_eq_same]
        omega
      · simpa [Pi.single_apply, hk] using mem_centredCube_iff.1 ho k
    rw [e, enclosingCell_siteOfCoords hodd _ _ ho']
    intro hE
    have h1 := siteOfCoords_eq_iff.1 hE i
    rw [period_top] at h1
    have h2 : (c + Pi.single i 1 : Fin 4 → ℤ) i - c i = 1 := by simp
    rw [h2] at h1
    have h3 := Int.le_of_dvd one_pos h1
    have h4 := hs i
    omega
  · simp only [hi, iff_false, not_not]
    have hlt : o i < halfSide F.blockSide := lt_of_le_of_ne (mem_centredCube_iff.1 ho i).2 hi
    have e : (fun k => (F.blockSide : ℤ) * c k + o k) + Pi.single i 1 =
        fun k => (F.blockSide : ℤ) * c k + (o + Pi.single i 1 : Fin 4 → ℤ) k := by
      funext k
      simp only [Pi.add_apply]
      ring
    have ho' : o + Pi.single i 1 ∈ centredCube F.blockSide := by
      refine mem_centredCube_iff.2 fun k => ?_
      by_cases hk : k = i
      · subst hk
        have := (mem_centredCube_iff.1 ho k).1
        simp only [Pi.add_apply, Pi.single_eq_same]
        omega
      · simpa [Pi.single_apply, hk] using mem_centredCube_iff.1 ho k
    rw [e, enclosingCell_siteOfCoords hodd _ _ ho']
private lemma cellOffset_siteOfCoords (hodd : Odd F.blockSide) (hs : ∀ i, 2 ≤ F.extent i) (c o : Fin 4 → ℤ)
    (ho : o ∈ centredCube F.blockSide) (k : Fin 4) :
    cellOffset (siteOfCoords F.depth (fun k => (F.blockSide : ℤ) * c k + o k) : F.Site F.depth) k = o k := by
  have hL := cast_eq_two_mul_halfSide_add_one hodd
  have hm := halfSide_nonneg hodd
  unfold cellOffset
  rw [enclosingCell_siteOfCoords hodd c o ho, cellCentre_siteOfCoords]
  have e : ((siteOfCoords F.depth (fun k => (F.blockSide : ℤ) * c k + o k) -
      siteOfCoords F.depth (fun i => (F.blockSide : ℤ) * c i) : F.Site F.depth)) k =
        ((o k : ℤ) : ZMod (F.period F.depth k)) := by
    simp [siteOfCoords]
  rw [e]
  have hp : (F.period F.depth k : ℤ) = (F.extent k : ℤ) * F.blockSide := by
    rw [period_depth]; push_cast; rfl
  have hs2 : (2 : ℤ) ≤ F.extent k := by exact_mod_cast hs k
  have hge : (F.blockSide : ℤ) ≤ (F.period F.depth k : ℤ) := by rw [hp]; nlinarith
  have : NeZero (F.period F.depth k) := ⟨by
    intro h0
    rw [h0] at hge
    push_cast at hge
    omega⟩
  have hlo := (mem_centredCube_iff.1 ho k).1
  have hhi := (mem_centredCube_iff.1 ho k).2
  refine (ZMod.valMinAbs_spec _ _).2 ⟨rfl, ?_, ?_⟩ <;> omega
private def IsTreeOffset (L : ℕ) (o : Fin 4 → ℤ) (i : Fin 4) : Prop :=
  o i ≠ halfSide L ∧ ∀ l, i < l → o l = 0
private lemma isAxialTreeBond_fineBondAt_iff (hodd : Odd F.blockSide) (hs : ∀ i, 2 ≤ F.extent i)
    (Y : F.Cell) (h o : Fin 4 → ℤ) (i : Fin 4) (ho : o ∈ centredCube F.blockSide) :
    IsAxialTreeBond (fineBondAt Y h o i) ↔ IsTreeOffset F.blockSide o i := by
  have e : fineBondAt Y h o i =
      ((siteOfCoords F.depth (fun k => (F.blockSide : ℤ) * (siteCoords Y + h) k + o k) :
        F.Site F.depth), i) :=
    Prod.ext (fineBondAt_fst Y h o i) rfl
  rw [e]
  unfold IsAxialTreeBond IsTreeOffset
  rw [isCrossingBond_iff hodd hs _ _ ho]
  simp only [cellOffset_siteOfCoords hodd hs _ _ ho]
private lemma mem_finiteCells (hs : ∀ i, 2 ≤ F.extent i) (z : F.Cell) : z ∈ finiteCells F := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.CellShares.mem_finiteCells <;> assumption
private lemma mem_sitesOfCells (hodd : Odd F.blockSide) (hs : ∀ i, 2 ≤ F.extent i) (x : F.Site F.depth) :
    x ∈ sitesOfCells (finiteCells F) F.depth := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.TwoTori.mem_sitesOfCells_finiteCells <;> assumption
private lemma mem_chordBonds_iff (hodd : Odd F.blockSide) (hs : ∀ i, 2 ≤ F.extent i)
    (b : F.Site F.depth × Fin 4) :
    b ∈ chordBonds (finiteCells F) ↔ ¬ IsAxialTreeBond b := by
  unfold chordBonds innerBonds
  simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_univ, and_true,
    mem_sitesOfCells hodd hs, true_and]
abbrev _root_.YangMills.SharedProofs.p118456 := @mem_chordBonds_iff
private lemma eq_of_add_siteOfCoords_eq {Y : F.Cell} {h h' : Fin 4 → ℤ}
    (hb : ∀ i, 2 * |h i - h' i| < F.extent i)
    (e : Y + siteOfCoords F.top h = Y + siteOfCoords F.top h') : h = h' := by
  have e' := add_left_cancel e
  funext i
  have h1 := siteOfCoords_eq_iff.1 e' i
  rw [period_top] at h1
  have h2 := hb i
  have h3 := abs_nonneg (h i - h' i)
  exact sub_eq_zero.1 (Int.eq_zero_of_abs_lt_dvd h1 (by omega))
private lemma add_siteOfCoords_zero (Y : F.Cell) : Y + siteOfCoords F.top (0 : Fin 4 → ℤ) = Y := by apply _root_.YangMills.SharedProofs.p55653 <;> assumption
private lemma cellSupDist_add_add (Y : F.Cell) (h h' : Fin 4 → ℤ) (hb : ∀ i, 2 * |h i - h' i| < F.extent i) :
    cellSupDist (Y + siteOfCoords F.top h) (Y + siteOfCoords F.top h') =
      Finset.univ.sup fun i => (h i - h' i).natAbs := by
  unfold cellSupDist
  refine Finset.sup_congr rfl fun i _ => ?_
  have hb' := hb i
  have h3 := abs_nonneg (h i - h' i)
  have hp : (F.period F.top i : ℤ) = F.extent i := by rw [period_top]
  have : NeZero (F.period F.top i) := ⟨by
    intro h0
    rw [h0] at hp
    push_cast at hp
    omega⟩
  have e : (Y + siteOfCoords F.top h : F.Cell) i - (Y + siteOfCoords F.top h' : F.Cell) i =
      ((h i - h' i : ℤ) : ZMod (F.period F.top i)) := by
    simp [siteOfCoords]
  rw [e]
  have hv : (((h i - h' i : ℤ) : ZMod (F.period F.top i))).valMinAbs = h i - h' i := by
    refine (ZMod.valMinAbs_spec _ _).2 ⟨rfl, ?_, ?_⟩ <;>
      rcases abs_cases (h i - h' i) with ⟨h4, _⟩ | ⟨h4, _⟩ <;> omega
  rw [hv]
private lemma exists_cellSupDist_eq_natAbs (Y : F.Cell) (h : Fin 4 → ℤ) (hb : ∀ i, 2 * |h i| < F.extent i) :
    ∃ k, cellSupDist (Y + siteOfCoords F.top h) Y = (h k).natAbs := by
  have e := cellSupDist_add_add Y h 0 (by simpa using hb)
  rw [add_siteOfCoords_zero] at e
  obtain ⟨k, _, hk⟩ := Finset.exists_mem_eq_sup Finset.univ Finset.univ_nonempty
    (fun i => (h i - (0 : Fin 4 → ℤ) i).natAbs)
  exact ⟨k, by rw [e, hk]; simp⟩
private lemma exists_offset_rep (z Y : F.Cell) :
    ∃ h : Fin 4 → ℤ, z = Y + siteOfCoords F.top h ∧ ∀ i, |h i| ≤ (cellSupDist z Y : ℤ) := by
  refine ⟨fun i => (z i - Y i).valMinAbs, ?_, fun i => ?_⟩
  · funext i
    simp [siteOfCoords, ZMod.coe_valMinAbs]
  · have h1 : ((z i - Y i).valMinAbs).natAbs ≤ cellSupDist z Y :=
      Finset.le_sup (f := fun i => ((z i - Y i).valMinAbs).natAbs) (Finset.mem_univ i)
    rw [Int.abs_eq_natAbs]
    exact_mod_cast h1
private lemma two_mul_abs_sub_lt {a b : ℤ} {r s : ℤ} (ha : 2 * |a| ≤ r) (hb : 2 * |b| ≤ r) (hs : 2 * r < s) :
    2 * |a - b| < s := by
  rcases abs_cases a with ⟨h1, _⟩ | ⟨h1, _⟩ <;> rcases abs_cases b with ⟨h2, _⟩ | ⟨h2, _⟩ <;>
    rcases abs_cases (a - b) with ⟨h3, _⟩ | ⟨h3, _⟩ <;> omega
private lemma exists_bond_rep (hodd : Odd F.blockSide) {Y : F.Cell} {r : ℕ} (b : ↥(bondsNearCell F Y r)) :
    ∃ (h o : Fin 4 → ℤ) (i : Fin 4), o ∈ centredCube F.blockSide ∧ (∀ k, 2 * |h k| ≤ (r : ℤ)) ∧
      b.1.1 = fineBondAt Y h o i := by
  have hb := b.2
  simp only [bondsNearCell, Finset.mem_filter, Finset.mem_univ, true_and] at hb
  obtain ⟨c, o, ho, hx⟩ := exists_cell_offset_decomp hodd b.1.1.1
  have hc : enclosingCell b.1.1.1 = siteOfCoords F.top c := by
    rw [hx, enclosingCell_siteOfCoords hodd c o ho]
  obtain ⟨h, hh, hd⟩ := exists_offset_rep (enclosingCell b.1.1.1) Y
  refine ⟨h, o, b.1.1.2, ho, fun k => ?_, ?_⟩
  · have h1 := hd k
    linarith
  · refine Prod.ext ?_ rfl
    simp only [fineBondAt]
    rw [← hh, hc, cellCentre_siteOfCoords, ← siteOfCoords_add]
    exact hx
private lemma exists_bond_of_offset (hodd : Odd F.blockSide) (hs : ∀ i, 2 ≤ F.extent i) {Y : F.Cell}
    {r : ℕ} {h o : Fin 4 → ℤ} {i : Fin 4} (ho : o ∈ centredCube F.blockSide)
    (hh : ∀ k, 2 * |h k| ≤ (r : ℤ)) (hr : ∀ k, 2 * (r : ℤ) < F.extent k)
    (ht : ¬ IsTreeOffset F.blockSide o i) :
    ∃ b : ↥(bondsNearCell F Y r), b.1.1 = fineBondAt Y h o i := by
  have hc : fineBondAt Y h o i ∈ chordBonds (finiteCells F) :=
    (mem_chordBonds_iff hodd hs _).2 fun hT => ht ((isAxialTreeBond_fineBondAt_iff hodd hs Y h o i ho).1 hT)
  refine ⟨⟨⟨_, hc⟩, ?_⟩, rfl⟩
  simp only [bondsNearCell, Finset.mem_filter, Finset.mem_univ, true_and]
  rw [enclosingCell_fineBondAt hodd Y h o i ho]
  obtain ⟨k, hk⟩ := exists_cellSupDist_eq_natAbs Y h fun i => by
    have h1 := hh i
    have h2 := hr i
    omega
  rw [hk]
  have h1 := hh k
  rw [Int.abs_eq_natAbs] at h1
  exact_mod_cast h1
private lemma offsets_eq_of_fineBondAt_eq (hodd : Odd F.blockSide) (hs : ∀ i, 2 ≤ F.extent i) {Y : F.Cell}
    {h h' o o' : Fin 4 → ℤ} {i i' : Fin 4} (ho : o ∈ centredCube F.blockSide)
    (ho' : o' ∈ centredCube F.blockSide)
    (hb : ∀ k, 2 * |h k - h' k| < F.extent k) (e : fineBondAt Y h o i = fineBondAt Y h' o' i') :
    h = h' ∧ o = o' ∧ i = i' := by
  have h1 := congrArg Prod.fst e
  have h2 : i = i' := congrArg Prod.snd e
  have hc : Y + siteOfCoords F.top h = Y + siteOfCoords F.top h' := by
    rw [← enclosingCell_fineBondAt hodd Y h o i ho, ← enclosingCell_fineBondAt hodd Y h' o' i' ho', e]
  have hh := eq_of_add_siteOfCoords_eq hb hc
  subst hh
  refine ⟨rfl, ?_, h2⟩
  simp only [fineBondAt] at h1
  have e' := add_left_cancel h1
  have hL := cast_eq_two_mul_halfSide_add_one hodd
  funext k
  have h3 := siteOfCoords_eq_iff.1 e' k
  have hp : (F.period F.depth k : ℤ) = (F.extent k : ℤ) * F.blockSide := by
    rw [period_depth]; push_cast; rfl
  have hs2 : (2 : ℤ) ≤ F.extent k := by exact_mod_cast hs k
  have hge : (F.blockSide : ℤ) ≤ (F.period F.depth k : ℤ) := by
    rw [hp]
    nlinarith [halfSide_nonneg hodd]
  have a1 := mem_centredCube_iff.1 ho k
  have a2 := mem_centredCube_iff.1 ho' k
  refine sub_eq_zero.1 (Int.eq_zero_of_abs_lt_dvd h3 ?_)
  rw [abs_lt]
  constructor <;> omega
private lemma exists_near_offset {Y : F.Cell} {r : ℕ} (z : {z // z ∈ cellsNearCell F Y r}) :
    ∃ h : Fin 4 → ℤ, (∀ k, 8 * |h k| < (r : ℤ)) ∧ z.1 = Y + siteOfCoords F.top h := by
  have hz := z.2
  simp only [cellsNearCell, Finset.mem_filter] at hz
  obtain ⟨h, hh, hd⟩ := exists_offset_rep z.1 Y
  refine ⟨h, fun k => ?_, hh⟩
  have h1 := hd k
  linarith
private lemma exists_near_cell (hs : ∀ i, 2 ≤ F.extent i) {Y : F.Cell} {r : ℕ} {h : Fin 4 → ℤ}
    (hh : ∀ k, 8 * |h k| < (r : ℤ)) (hr : ∀ k, 2 * (r : ℤ) < F.extent k) :
    ∃ z : {z // z ∈ cellsNearCell F Y r}, z.1 = Y + siteOfCoords F.top h := by
  refine ⟨⟨Y + siteOfCoords F.top h, ?_⟩, rfl⟩
  simp only [cellsNearCell, Finset.mem_filter]
  refine ⟨mem_finiteCells hs _, ?_⟩
  obtain ⟨k, hk⟩ := exists_cellSupDist_eq_natAbs Y h fun i => by
    have h1 := hh i
    have h2 := hr i
    omega
  rw [hk]
  have h1 := hh k
  rw [Int.abs_eq_natAbs] at h1
  exact_mod_cast h1
private lemma exists_equiv_of_bijective_rel {A B : Type*} (R : A → B → Prop) (t1 : ∀ a, ∃ b, R a b)
    (t2 : ∀ b, ∃ a, R a b) (u1 : ∀ a b b', R a b → R a b' → b = b')
    (u2 : ∀ a a' b, R a b → R a' b → a = a') : ∃ e : A ≃ B, ∀ a, R a (e a) := by
  choose f hf using t1
  refine ⟨Equiv.ofBijective f ⟨fun a a' h => u2 a a' (f a) (hf a) (by rw [h]; exact hf a'),
    fun b => ?_⟩, hf⟩
  obtain ⟨a, ha⟩ := t2 b
  exact ⟨a, u1 a _ _ (hf a) ha⟩
private lemma blockOfBond_eq (hodd : Odd F.blockSide) {Y : F.Cell} {h o : Fin 4 → ℤ} {i : Fin 4}
    (ho : o ∈ centredCube F.blockSide) (b : ↥(chordBonds (finiteCells F))) (e : b.1 = fineBondAt Y h o i) :
    blockOfBond F b = Y + siteOfCoords F.top h := by
  simp only [blockOfBond]
  rw [e, enclosingCell_fineBondAt hodd Y h o i ho]
private lemma exists_matching_bond {F' : BlockFrame} {r : ℕ} (hL : F.blockSide = F'.blockSide)
    (hodd : Odd F.blockSide) (g : ∀ i, 2 ≤ F.extent i)
    (g' : ∀ i, 2 ≤ F'.extent i) (hr' : ∀ k, 2 * (r : ℤ) < F'.extent k) {Y : F.Cell} (Y' : F'.Cell)
    (b : ↥(bondsNearCell F Y r)) :
    ∃ (h o : Fin 4 → ℤ) (i : Fin 4) (b' : ↥(bondsNearCell F' Y' r)), o ∈ centredCube F.blockSide ∧
      (∀ k, 2 * |h k| ≤ (r : ℤ)) ∧ b.1.1 = fineBondAt Y h o i ∧ b'.1.1 = fineBondAt Y' h o i := by
  obtain ⟨h, o, i, ho, hb, e⟩ := exists_bond_rep hodd b
  have hnt : ¬ IsTreeOffset F.blockSide o i := fun hT =>
    (mem_chordBonds_iff hodd g _).1 b.1.2 (by rw [e]; exact (isAxialTreeBond_fineBondAt_iff hodd g Y h o i ho).2 hT)
  obtain ⟨b', hb'⟩ := exists_bond_of_offset (Y := Y') (h := h) (o := o) (i := i) (hL ▸ hodd) g'
    (hL ▸ ho) hb hr' (hL ▸ hnt)
  exact ⟨h, o, i, b', ho, hb, e, hb'⟩
end OffsetCorrespondence
open OffsetCorrespondence in
theorem nearBlocksCorrespondByOffset_holds : NearBlocksCorrespondByOffset := by
  intro F F' Y Y' r hL ht hodd hs hs'
  have hodd' : Odd F'.blockSide := hL ▸ hodd
  have g : ∀ i, 2 ≤ F.extent i := fun i => by
    have := hs i
    omega
  have g' : ∀ i, 2 ≤ F'.extent i := fun i => by
    have := hs' i
    omega
  have hr : ∀ k, 2 * (r : ℤ) < F.extent k := fun k => by
    have := hs k
    omega
  have hr' : ∀ k, 2 * (r : ℤ) < F'.extent k := fun k => by
    have := hs' k
    omega
  have hcu : ∀ {o : Fin 4 → ℤ}, o ∈ centredCube F.blockSide → o ∈ centredCube F'.blockSide :=
    fun ho => hL ▸ ho
  obtain ⟨e, he⟩ := exists_equiv_of_bijective_rel
    (fun (b : ↥(bondsNearCell F Y r)) (b' : ↥(bondsNearCell F' Y' r)) =>
      ∃ (h o : Fin 4 → ℤ) (i : Fin 4), o ∈ centredCube F.blockSide ∧ (∀ k, 2 * |h k| ≤ (r : ℤ)) ∧
        b.1.1 = fineBondAt Y h o i ∧ b'.1.1 = fineBondAt Y' h o i)
    (fun b => by
      obtain ⟨h, o, i, b', ho, hb, x, y⟩ := exists_matching_bond hL hodd g g' hr' Y' b
      exact ⟨b', h, o, i, ho, hb, x, y⟩)
    (fun b' => by
      obtain ⟨h, o, i, b, ho, hb, x, y⟩ := exists_matching_bond hL.symm hodd' g' g hr Y b'
      exact ⟨b, h, o, i, hL ▸ ho, hb, y, x⟩)
    (fun b b₁ b₂ => by
      rintro ⟨h₁, o₁, i₁, ho₁, hb₁, x₁, y₁⟩ ⟨h₂, o₂, i₂, ho₂, hb₂, x₂, y₂⟩
      obtain ⟨rfl, rfl, rfl⟩ := offsets_eq_of_fineBondAt_eq hodd g ho₁ ho₂
        (fun k => two_mul_abs_sub_lt (hb₁ k) (hb₂ k) (hr k)) (x₁.symm.trans x₂)
      exact Subtype.ext (Subtype.ext (y₁.trans y₂.symm)))
    (fun b₁ b₂ b => by
      rintro ⟨h₁, o₁, i₁, ho₁, hb₁, x₁, y₁⟩ ⟨h₂, o₂, i₂, ho₂, hb₂, x₂, y₂⟩
      obtain ⟨rfl, rfl, rfl⟩ := offsets_eq_of_fineBondAt_eq hodd' g' (hcu ho₁) (hcu ho₂)
        (fun k => two_mul_abs_sub_lt (hb₁ k) (hb₂ k) (hr' k)) (y₁.symm.trans y₂)
      exact Subtype.ext (Subtype.ext (x₁.trans x₂.symm)))
  have near : ∀ {a : ℤ}, 8 * |a| < (r : ℤ) → 2 * |a| ≤ (r : ℤ) := fun {a} h => by
    have := abs_nonneg a
    omega
  obtain ⟨φ, hφ⟩ := exists_equiv_of_bijective_rel
    (fun (z : {z // z ∈ cellsNearCell F Y r}) (z' : {z // z ∈ cellsNearCell F' Y' r}) =>
      ∃ h : Fin 4 → ℤ, (∀ k, 8 * |h k| < (r : ℤ)) ∧ z.1 = Y + siteOfCoords F.top h ∧
        z'.1 = Y' + siteOfCoords F'.top h)
    (fun z => by
      obtain ⟨h, hb, x⟩ := exists_near_offset z
      obtain ⟨z', y⟩ := exists_near_cell (Y := Y') g' hb hr'
      exact ⟨z', h, hb, x, y⟩)
    (fun z' => by
      obtain ⟨h, hb, y⟩ := exists_near_offset z'
      obtain ⟨z, x⟩ := exists_near_cell (Y := Y) g hb hr
      exact ⟨z, h, hb, x, y⟩)
    (fun z z₁ z₂ => by
      rintro ⟨h₁, hb₁, x₁, y₁⟩ ⟨h₂, hb₂, x₂, y₂⟩
      have hh : h₁ = h₂ := eq_of_add_siteOfCoords_eq
        (fun k => two_mul_abs_sub_lt (near (hb₁ k)) (near (hb₂ k)) (hr k)) (x₁.symm.trans x₂)
      subst hh
      exact Subtype.ext (y₁.trans y₂.symm))
    (fun z₁ z₂ z => by
      rintro ⟨h₁, hb₁, x₁, y₁⟩ ⟨h₂, hb₂, x₂, y₂⟩
      have hh : h₁ = h₂ := eq_of_add_siteOfCoords_eq
        (fun k => two_mul_abs_sub_lt (near (hb₁ k)) (near (hb₂ k)) (hr' k)) (y₁.symm.trans y₂)
      subst hh
      exact Subtype.ext (x₁.trans x₂.symm))
  refine ⟨e, φ, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro b
    obtain ⟨h, o, i, ho, hb, x, y⟩ := he b
    refine ⟨h, o, i, ho, fun k => ?_, x, y⟩
    have h1 := hb k
    have h2 := abs_nonneg (h k)
    omega
  · intro z
    obtain ⟨h, hb, x, y⟩ := hφ z
    exact ⟨h, fun k => (hb k).le, x, y⟩
  · intro k k'
    obtain ⟨h₁, o₁, i₁, ho₁, hb₁, x₁, y₁⟩ := he k
    obtain ⟨h₂, o₂, i₂, ho₂, hb₂, x₂, y₂⟩ := he k'
    rw [blockOfBond_eq hodd ho₁ _ x₁, blockOfBond_eq hodd ho₂ _ x₂, blockOfBond_eq hodd' (hcu ho₁) _ y₁,
      blockOfBond_eq hodd' (hcu ho₂) _ y₂,
      cellSupDist_add_add Y h₁ h₂ fun k => two_mul_abs_sub_lt (hb₁ k) (hb₂ k) (hr k),
      cellSupDist_add_add Y' h₁ h₂ fun k => two_mul_abs_sub_lt (hb₁ k) (hb₂ k) (hr' k)]
  · intro k
    obtain ⟨h, o, i, ho, hb, x, y⟩ := he k
    have z0 : ∀ j, 2 * |(0 : Fin 4 → ℤ) j| ≤ (r : ℤ) := fun j => by simp
    rw [blockOfBond_eq hodd ho _ x, blockOfBond_eq hodd' (hcu ho) _ y]
    have a1 := cellSupDist_add_add Y h 0 fun k => two_mul_abs_sub_lt (hb k) (z0 k) (hr k)
    have a2 := cellSupDist_add_add Y' h 0 fun k => two_mul_abs_sub_lt (hb k) (z0 k) (hr' k)
    rw [add_siteOfCoords_zero] at a1 a2
    rw [a1, a2]
  · intro k z
    obtain ⟨h, o, i, ho, hb, x, y⟩ := he k
    obtain ⟨h₂, hb₂, x₂, y₂⟩ := hφ z
    rw [blockOfBond_eq hodd ho _ x, blockOfBond_eq hodd' (hcu ho) _ y, x₂, y₂]
    constructor
    · intro E
      have hh : h = h₂ := eq_of_add_siteOfCoords_eq
        (fun k => two_mul_abs_sub_lt (hb k) (near (hb₂ k)) (hr k)) E
      rw [hh]
    · intro E
      have hh : h = h₂ := eq_of_add_siteOfCoords_eq
        (fun k => two_mul_abs_sub_lt (hb k) (near (hb₂ k)) (hr' k)) E
      rw [hh]
  · intro z E
    obtain ⟨h, hb, x, y⟩ := hφ z
    have z0 : ∀ j, 2 * |(0 : Fin 4 → ℤ) j| ≤ (r : ℤ) := fun j => by simp
    have hh : h = 0 := eq_of_add_siteOfCoords_eq (Y := Y)
      (fun k => two_mul_abs_sub_lt (near (hb k)) (z0 k) (hr k))
      (by rw [add_siteOfCoords_zero]; exact x.symm.trans E)
    rw [y, hh, add_siteOfCoords_zero]
end ColdStepAtMirrorFrames
end YangMills.Construction
end
