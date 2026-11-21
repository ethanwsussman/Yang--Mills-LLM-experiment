import YangMills.Construction.ClusterExpansionOfAStep.DistancesAndClasses
import YangMills.Construction.HoleBesideASecondHole.ComponentsOfLumpsProof
import YangMills.Construction.HoleBesideASecondHole.DistancesBlocksAndLumps
import YangMills.Construction.HoleBesideASecondHole.TopHotPlaquettesPayProof
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
namespace LumpContours
open BlockAverages
variable {F : BlockFrame}
theorem period_pos (hL : 0 < F.blockSide) (hs : ∀ i, 0 < F.extent i) (j : ℕ) (i : Fin 4) :
    0 < F.period j i :=
  Nat.mul_pos (hs i) (pow_pos hL _)
theorem supDist_le_iff {j : ℕ} (x y : F.Site j) (m : ℕ) :
    supDist x y ≤ m ↔ ∀ i, ((x i - y i).valMinAbs).natAbs ≤ m := by
  unfold supDist
  exact Finset.sup_le_iff.trans (by simp)
theorem supDist_comm {j : ℕ} (x y : F.Site j) : supDist x y = supDist y x := by apply _root_.YangMills.Construction.Holes.LinkComponentFacts.supDist_comm <;> assumption
theorem natAbs_valMinAbs_sub_le_supDist {j : ℕ} (x y : F.Site j) (i : Fin 4) :
    ((x i - y i).valMinAbs).natAbs ≤ supDist x y :=
  (supDist_le_iff x y _).1 le_rfl i
theorem supDist_triangle {j : ℕ} (x y z : F.Site j) :
    supDist x z ≤ supDist x y + supDist y z := by
  rw [supDist_le_iff]
  intro i
  have e : x i - z i = (x i - y i) + (y i - z i) := by ring
  rw [e]
  exact (ZMod.natAbs_valMinAbs_add_le _ _).trans ((Int.natAbs_add_le _ _).trans
    (Nat.add_le_add (natAbs_valMinAbs_sub_le_supDist x y i)
      (natAbs_valMinAbs_sub_le_supDist y z i)))
theorem natAbs_valMinAbs_one_le {n : ℕ} [NeZero n] : ((1 : ZMod n).valMinAbs).natAbs ≤ 1 := by
  rw [ZMod.valMinAbs_natAbs_eq_min]
  refine (min_le_left _ _).trans ?_
  rw [ZMod.val_one_eq_one_mod]
  exact Nat.mod_le _ _
theorem natAbs_valMinAbs_natCast_le {n : ℕ} [NeZero n] (k : ℕ) :
    (((k : ℕ) : ZMod n).valMinAbs).natAbs ≤ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Nat.cast_succ]
    exact (ZMod.natAbs_valMinAbs_add_le _ _).trans
      ((Int.natAbs_add_le _ _).trans (Nat.add_le_add ih natAbs_valMinAbs_one_le))
theorem natAbs_valMinAbs_intCast_le {n : ℕ} [NeZero n] (c : ℤ) :
    (((c : ℤ) : ZMod n).valMinAbs).natAbs ≤ c.natAbs := by apply _root_.YangMills.Construction.TorusFields.natAbs_valMinAbs_intCast_le <;> assumption
theorem siteCoords_cast {j : ℕ} (x : F.Site j) (i : Fin 4) :
    ((siteCoords x i : ℤ) : ZMod (F.period j i)) = x i := by apply _root_.YangMills.Construction.LumpContours.BlockLevels.siteCoords_cast <;> assumption
theorem siteOfCoords_siteCoords {j : ℕ} (x : F.Site j) : siteOfCoords j (siteCoords x) = x := by apply _root_.YangMills.Construction.BlockAverages.siteOfCoords_siteCoords <;> assumption
theorem mem_centredCube_iff {M : ℕ} {o : Fin 4 → ℤ} :
    o ∈ centredCube M ↔ ∀ m, |o m| ≤ ((M : ℤ) - 1) / 2 := by apply _root_.YangMills.Construction.LumpContours.BlockLevels.mem_centredCube_iff <;> assumption
theorem mem_thicken_iff (hL : 0 < F.blockSide) (hs : ∀ i, 0 < F.extent i) {j : ℕ} (m : ℕ)
    (X : Finset (F.Site j)) (x : F.Site j) : x ∈ thicken m X ↔ ∃ y ∈ X, supDist y x ≤ m := by
  unfold thicken
  simp only [Finset.mem_biUnion, Finset.mem_image]
  constructor
  · rintro ⟨y, hy, h, hh, rfl⟩
    refine ⟨y, hy, ?_⟩
    rw [supDist_le_iff]
    intro i
    haveI : NeZero (F.period j i) := ⟨(period_pos hL hs j i).ne'⟩
    have e : y i - (y + siteOfCoords j h : F.Site j) i = -((h i : ℤ) : ZMod (F.period j i)) := by
      simp [siteOfCoords]
    rw [e, ZMod.natAbs_valMinAbs_neg]
    refine (natAbs_valMinAbs_intCast_le _).trans ?_
    have := mem_centredCube_iff.1 hh i
    have h2 : (((2 * m + 1 : ℕ) : ℤ) - 1) / 2 = m := by
      push_cast
      omega
    rw [h2, abs_le] at this
    omega
  · rintro ⟨y, hy, hd⟩
    refine ⟨y, hy, fun i => (x i - y i).valMinAbs, ?_, ?_⟩
    · rw [mem_centredCube_iff]
      intro i
      have h2 : (((2 * m + 1 : ℕ) : ℤ) - 1) / 2 = m := by
        push_cast
        omega
      rw [h2]
      have := (supDist_le_iff y x m).1 hd i
      rw [← neg_sub, ZMod.natAbs_valMinAbs_neg] at this
      rw [Int.abs_eq_natAbs]
      exact_mod_cast this
    · funext i
      simp [siteOfCoords, ZMod.coe_valMinAbs]
theorem two_mul_half_pred_add_one_of_odd {L : ℕ} (hL : Odd L) :
    2 * (((L : ℤ) - 1) / 2) + 1 = L := by
  obtain ⟨k, rfl⟩ := hL
  push_cast
  omega
theorem top_sub_depth : F.top - F.depth = 1 := by apply _root_.YangMills.Construction.GaugeFixing.top_sub_depth <;> assumption
theorem enclosingCell_siteOfCoords (hL : 0 < F.blockSide) (z : Fin 4 → ℤ) :
    enclosingCell (siteOfCoords F.depth z : F.Site F.depth) =
      (siteOfCoords F.top fun i => (z i + ((F.blockSide : ℤ) - 1) / 2) / (F.blockSide : ℤ) :
        F.Cell) := by
  funext i
  simp only [enclosingCell, siteOfCoords, top_sub_depth, pow_one]
  rw [ZMod.intCast_eq_intCast_iff_dvd_sub]
  have hper : F.period F.depth i = F.extent i * F.blockSide := by
    simp [BlockFrame.period, top_sub_depth]
  have hd : ((F.period F.depth i : ℕ) : ℤ) ∣
      z i - siteCoords (siteOfCoords F.depth z : F.Site F.depth) i := by
    rw [← ZMod.intCast_eq_intCast_iff_dvd_sub]
    exact siteCoords_cast (siteOfCoords F.depth z : F.Site F.depth) i
  obtain ⟨q, hq⟩ := hd
  rw [hper] at hq
  have hLz : (F.blockSide : ℤ) ≠ 0 := by exact_mod_cast hL.ne'
  have e : z i + ((F.blockSide : ℤ) - 1) / 2 =
      siteCoords (siteOfCoords F.depth z : F.Site F.depth) i + ((F.blockSide : ℤ) - 1) / 2 +
        (F.extent i * q) * F.blockSide := by
    push_cast at hq
    linarith [mul_comm ((F.extent i : ℤ) * F.blockSide) q,
      mul_assoc (F.extent i : ℤ) (F.blockSide : ℤ) q,
      mul_assoc (F.extent i : ℤ) q (F.blockSide : ℤ), mul_comm (F.blockSide : ℤ) q]
  have hper' : F.period F.top i = F.extent i := by simp [BlockFrame.period]
  rw [e, Int.add_mul_ediv_right _ _ hLz]
  refine ⟨q, ?_⟩
  rw [hper']
  ring
theorem ediv_blockSide_of_offset (hL : Odd F.blockSide) (m : ℤ) {o : ℤ}
    (ho : |o| ≤ ((F.blockSide : ℤ) - 1) / 2) :
    ((F.blockSide : ℤ) * m + o + ((F.blockSide : ℤ) - 1) / 2) / (F.blockSide : ℤ) = m := by
  have h2 := two_mul_half_pred_add_one_of_odd hL
  have hLp : (0 : ℤ) < F.blockSide := by
    have := hL.pos
    exact_mod_cast this
  rw [abs_le] at ho
  rw [add_assoc, Int.mul_comm, Int.add_ediv_of_dvd_left (Dvd.intro_left _ rfl),
    Int.mul_ediv_cancel _ hLp.ne', Int.ediv_eq_zero_of_lt (by omega) (by omega)]
  simp
theorem mem_sitesBelow_iff (hL : Odd F.blockSide) (x : F.Site F.depth) (y : F.Cell) :
    x ∈ sitesBelow F.depth y ↔ enclosingCell x = y := by
  have hLp : 0 < F.blockSide := hL.pos
  unfold sitesBelow
  simp only [Finset.mem_image, top_sub_depth, pow_one]
  constructor
  · rintro ⟨h, hh, rfl⟩
    rw [enclosingCell_siteOfCoords hLp]
    have := mem_centredCube_iff.1 hh
    funext i
    simp only [siteOfCoords]
    rw [ediv_blockSide_of_offset hL _ (this i)]
    exact siteCoords_cast y i
  · rintro rfl
    set H : ℤ := ((F.blockSide : ℤ) - 1) / 2 with hH
    have h2 := two_mul_half_pred_add_one_of_odd hL
    have hLz : (0 : ℤ) < F.blockSide := by exact_mod_cast hLp
    refine ⟨fun i => siteCoords x i - (F.blockSide : ℤ) * ((siteCoords x i + H) / (F.blockSide : ℤ)),
      ?_, ?_⟩
    · rw [mem_centredCube_iff]
      intro i
      have a1 := Int.emod_add_mul_ediv (siteCoords x i + H) (F.blockSide : ℤ)
      have a2 := Int.emod_nonneg (siteCoords x i + H) hLz.ne'
      have a3 := Int.emod_lt_of_pos (siteCoords x i + H) hLz
      rw [abs_le]
      constructor <;> omega
    · funext i
      simp only [siteOfCoords]
      have e : (((F.blockSide : ℤ) * siteCoords (enclosingCell x) i +
          (siteCoords x i - (F.blockSide : ℤ) * ((siteCoords x i + H) / (F.blockSide : ℤ))) : ℤ) :
            ZMod (F.period F.depth i)) =
          ((siteCoords x i : ℤ) : ZMod (F.period F.depth i)) := by
        rw [ZMod.intCast_eq_intCast_iff_dvd_sub]
        have hper : F.period F.depth i = F.extent i * F.blockSide := by
          simp [BlockFrame.period, top_sub_depth]
        have hper' : F.period F.top i = F.extent i := by simp [BlockFrame.period]
        have hd : ((F.period F.top i : ℕ) : ℤ) ∣
            (siteCoords x i + H) / (F.blockSide : ℤ) - siteCoords (enclosingCell x) i := by
          rw [← ZMod.intCast_eq_intCast_iff_dvd_sub]
          have := siteCoords_cast (enclosingCell x) i
          rw [this]
          simp only [enclosingCell, siteOfCoords, top_sub_depth, pow_one]
          rw [← hH]
        obtain ⟨q, hq⟩ := hd
        rw [hper'] at hq
        refine ⟨q, ?_⟩
        rw [hper]
        push_cast
        have : siteCoords (enclosingCell x) i =
            (siteCoords x i + H) / (F.blockSide : ℤ) - (F.extent i : ℤ) * q := by linarith
        rw [this]
        ring
      rw [e]
      exact siteCoords_cast x i
theorem cellSupDist_enclosingCell_le (hL : Odd F.blockSide) (hs : ∀ i, 0 < F.extent i) (m : ℕ)
    (x x' : F.Site F.depth) (hd : supDist x x' ≤ m * F.blockSide) :
    cellSupDist (enclosingCell x) (enclosingCell x') ≤ m := by
  have hLp : 0 < F.blockSide := hL.pos
  have hLz : (0 : ℤ) < F.blockSide := by exact_mod_cast hLp
  have : cellSupDist (enclosingCell x) (enclosingCell x') =
      supDist (enclosingCell x) (enclosingCell x') := rfl
  rw [this, supDist_le_iff]
  intro i
  haveI : NeZero (F.period F.top i) := ⟨(period_pos hLp hs _ i).ne'⟩
  set v : Fin 4 → ℤ := fun k => (x' k - x k).valMinAbs with hv
  have hx' : x' = siteOfCoords F.depth (siteCoords x + v) := by
    funext k
    simp only [siteOfCoords, Pi.add_apply, Int.cast_add, siteCoords_cast, hv, ZMod.coe_valMinAbs]
    ring
  have hvi : |v i| ≤ (m : ℤ) * F.blockSide := by
    have h1 := natAbs_valMinAbs_sub_le_supDist x' x i
    rw [supDist_comm x' x] at h1
    have h2 : ((x' i - x i).valMinAbs).natAbs ≤ m * F.blockSide := h1.trans hd
    have : |v i| = (((x' i - x i).valMinAbs).natAbs : ℤ) := by
      simp [hv, Int.natCast_natAbs]
    rw [this]
    exact_mod_cast h2
  have c1 : enclosingCell x = (siteOfCoords F.top fun k =>
      (siteCoords x k + ((F.blockSide : ℤ) - 1) / 2) / (F.blockSide : ℤ) : F.Cell) := by
    conv_lhs => rw [← siteOfCoords_siteCoords x]
    exact enclosingCell_siteOfCoords hLp _
  rw [hx', enclosingCell_siteOfCoords hLp, c1]
  simp only [siteOfCoords, Pi.add_apply]
  rw [← Int.cast_sub]
  refine (natAbs_valMinAbs_intCast_le _).trans ?_
  set H : ℤ := ((F.blockSide : ℤ) - 1) / 2
  set A := siteCoords x i + H
  have e2 : siteCoords x i + v i + H = A + v i := by simp only [A]; ring
  rw [e2]
  set f := A / (F.blockSide : ℤ)
  set e := (A + v i) / (F.blockSide : ℤ)
  have b1 := Int.emod_add_mul_ediv A (F.blockSide : ℤ)
  have b2 := Int.emod_nonneg A hLz.ne'
  have b3 := Int.emod_lt_of_pos A hLz
  have b4 := Int.emod_add_mul_ediv (A + v i) (F.blockSide : ℤ)
  have b5 := Int.emod_nonneg (A + v i) hLz.ne'
  have b6 := Int.emod_lt_of_pos (A + v i) hLz
  rw [abs_le] at hvi
  have k1 : (F.blockSide : ℤ) * (f - e) < (F.blockSide : ℤ) * (m + 1) := by
    simp only [f, e]
    nlinarith
  have k2 : (F.blockSide : ℤ) * (e - f) < (F.blockSide : ℤ) * (m + 1) := by
    simp only [f, e]
    nlinarith
  have k3 := lt_of_mul_lt_mul_left k1 hLz.le
  have k4 := lt_of_mul_lt_mul_left k2 hLz.le
  omega
theorem abs_offsetFromCentre_le {L : ℕ} (hL : Odd L) (c : ℤ) :
    |offsetFromCentre L c| ≤ ((L : ℤ) - 1) / 2 := by apply _root_.YangMills.Construction.HoleSavings.TopHotPlaquetteCost.abs_offsetFromCentre_le <;> assumption
theorem sub_offsetFromCentre {L : ℕ} (hL : Odd L) (c : ℤ) :
    c - offsetFromCentre L c = (L : ℤ) * ((c + ((L : ℤ) - 1) / 2) / (L : ℤ)) := by
  have a1 := Int.emod_add_mul_ediv (c + ((L : ℤ) - 1) / 2) (L : ℤ)
  unfold offsetFromCentre
  linarith
theorem siteOfCoords_mem_boxSites (j : ℕ) {lo hi z : Fin 4 → ℤ}
    (h : ∀ i, lo i ≤ z i ∧ z i ≤ hi i) :
    (siteOfCoords j z : F.Site j) ∈ boxSites j lo hi := by
  unfold boxSites
  refine Finset.mem_image.2 ⟨z, ?_, rfl⟩
  simp only [Fintype.mem_piFinset, Finset.mem_Icc]
  exact h
theorem lumpOf_facts (hL : Odd F.blockSide) (hs : ∀ i, 0 < F.extent i) (g : LumpGrid F.blockSide)
    (x : F.Site F.depth) :
    x ∈ lumpOf g x ∧ lumpOf g x ⊆ sitesBelow F.depth (enclosingCell x) ∧
      ∀ u ∈ lumpOf g x, ∀ v ∈ lumpOf g x, supDist u v < 2 ^ 15 := by
  have hLp : 0 < F.blockSide := hL.pos
  have hb := fun i => abs_offsetFromCentre_le hL (siteCoords x i)
  have hg := fun i => g.mem_interval _ (hb i)
  have hside := fun i => g.interval_length _ (hb i)
  refine ⟨?_, ?_, ?_⟩
  · have key : (siteOfCoords F.depth (siteCoords x) : F.Site F.depth) ∈ lumpOf g x := by
      refine siteOfCoords_mem_boxSites _ fun i => ?_
      have := hg i
      constructor <;> linarith [this.2.1, this.2.2.1]
    rwa [siteOfCoords_siteCoords] at key
  · intro u hu
    unfold lumpOf boxSites at hu
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.1 hu
    simp only [Fintype.mem_piFinset, Finset.mem_Icc] at hz
    rw [mem_sitesBelow_iff hL, enclosingCell_siteOfCoords hLp]
    have c1 : enclosingCell x = (siteOfCoords F.top fun k =>
        (siteCoords x k + ((F.blockSide : ℤ) - 1) / 2) / (F.blockSide : ℤ) : F.Cell) := by
      conv_lhs => rw [← siteOfCoords_siteCoords x]
      exact enclosingCell_siteOfCoords hLp _
    rw [c1]
    funext i
    simp only [siteOfCoords]
    congr 1
    have e := sub_offsetFromCentre hL (siteCoords x i)
    have hzi := hz i
    have hgi := hg i
    set o := z i - (siteCoords x i - offsetFromCentre F.blockSide (siteCoords x i)) with ho
    have hzo : z i = (F.blockSide : ℤ) *
        ((siteCoords x i + ((F.blockSide : ℤ) - 1) / 2) / (F.blockSide : ℤ)) + o := by
      rw [ho, e]; ring
    rw [hzo]
    refine ediv_blockSide_of_offset hL _ ?_
    rw [abs_le]
    constructor <;> linarith [hzi.1, hzi.2, hgi.1, hgi.2.2.2]
  · intro u hu v hv
    unfold lumpOf boxSites at hu hv
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.1 hu
    obtain ⟨z', hz', rfl⟩ := Finset.mem_image.1 hv
    simp only [Fintype.mem_piFinset, Finset.mem_Icc] at hz hz'
    have : supDist (siteOfCoords F.depth z : F.Site F.depth) (siteOfCoords F.depth z') ≤
        2 ^ 15 - 1 := by
      rw [supDist_le_iff]
      intro i
      haveI : NeZero (F.period F.depth i) := ⟨(period_pos hLp hs _ i).ne'⟩
      simp only [siteOfCoords]
      rw [← Int.cast_sub]
      refine (natAbs_valMinAbs_intCast_le _).trans ?_
      have a := hz i
      have b := hz' i
      have c := (hside i).2
      omega
    omega
theorem mem_cellBall_iff (hL : 0 < F.blockSide) (hs : ∀ i, 0 < F.extent i) (x : F.Cell) (r : ℕ)
    (y : F.Cell) : y ∈ cellBall x r ↔ cellSupDist x y ≤ r := by
  have := mem_thicken_iff hL hs r ({x} : Finset F.Cell) y
  simp only [thicken, Finset.singleton_biUnion, Finset.mem_singleton, exists_eq_left] at this
  exact this
theorem torusDistanceBlockLumpFacts_holds : TorusDistanceBlockLumpFacts := by
  intro F hL hs
  refine ⟨fun j x y => supDist_comm x y, fun j x y z => supDist_triangle x y z,
    fun j m X x => mem_thicken_iff hL hs m X x, fun h x y => mem_sitesBelow_iff h x y,
    fun h m x x' hd => cellSupDist_enclosingCell_le h hs m x x' hd,
    fun x y z => supDist_triangle x y z,
    fun x y => supDist_comm x y, fun x r y => mem_cellBall_iff hL hs x r y,
    fun h g x => lumpOf_facts h hs g x⟩
end LumpContours
end YangMills.Construction
end
