import YangMills.Construction.ColdChainAtEveryLevel.BoundsOfTheReferenceProof
import YangMills.Construction.ColdChainAtEveryLevel.BumpsOfTheCellsProof
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction
namespace PatchPoints
open YangMills.Construction.BlockAverages YangMills.Construction.GaugeMap YangMills.Construction.LatticeFractionalIntegration
variable {F : BlockFrame} {S : Finset F.Cell} {z : F.Cell}
open Classical in
def patchSiteSet (S : Finset F.Cell) (z : F.Cell) : Finset (F.Site 0) := (patchDomain S z).image (patchSite S z)
theorem patchDomain_coord_bounds {x : Lattice4} (hx : x ∈ patchDomain S z) (i : Fin 4) :
    -(10 * cellSideLength F) ≤ x i ∧ x i < 21 * cellSideLength F := by apply _root_.YangMills.Construction.ReferenceBounds.patchDomain_coord_bounds <;> assumption
theorem cellSupDist_symm (y y' : F.Cell) : cellSupDist y y' = cellSupDist y' y := by apply _root_.YangMills.Construction.BlockLines.cellSupDist_comm <;> assumption
theorem natAbs_valMinAbs_le_cellSupDist (y y' : F.Cell) (i : Fin 4) :
    ((y i - y' i).valMinAbs).natAbs ≤ cellSupDist y y' :=
  Finset.le_sup (f := fun i => ((y i - y' i).valMinAbs).natAbs) (Finset.mem_univ i)
theorem eq_add_siteOfCoords_cellDisplacement (y y' : F.Cell) :
    y' = y + siteOfCoords F.top (cellDisplacement y y') := by
  funext i
  simp only [siteOfCoords, cellDisplacement, Pi.add_apply, Pi.sub_apply, ZMod.coe_valMinAbs]
  ring
theorem patchChart_patchSite (hamb : IsAdmissibleAmbient F) (hodd : Odd F.blockSide)
    (he : ∀ i, closedOrthant S z i = 1 ∨ closedOrthant S z i = -1)
    {a : Lattice4} (ha : ∀ i, -(10 * cellSideLength F) ≤ a i ∧ a i < 21 * cellSideLength F) :
    patchChart S z (patchSite S z a) = a := by
  have hL := hodd.pos
  obtain ⟨h0, h1⟩ := cellSideLength_half (F := F) hodd
  funext i
  have e : (patchSite S z a - cellCentre 0 z) i =
      ((closedOrthant S z i * (a i - (cellSideLength F - 1) / 2) : ℤ) : ZMod (F.period 0 i)) := by
    simp [patchSite, siteOfCoords]
  have hb : |closedOrthant S z i * (a i - (cellSideLength F - 1) / 2)| < 32 * cellSideLength F := by
    rw [abs_mul, abs_closedOrthant he, one_mul, abs_lt]
    have := ha i
    constructor <;> omega
  simp only [patchChart]
  rw [e, valMinAbs_of_abs_lt hamb hL i hb, ← mul_assoc, closedOrthant_mul_self he, one_mul]
  ring
theorem patchSite_patchChart (he : ∀ i, closedOrthant S z i = 1 ∨ closedOrthant S z i = -1) (s : F.Site 0) :
    patchSite S z (patchChart S z s) = s := by
  funext i
  simp only [patchSite, patchChart, siteOfCoords, Pi.add_apply]
  have e : closedOrthant S z i * (closedOrthant S z i * ((s - cellCentre 0 z) i).valMinAbs +
      (cellSideLength F - 1) / 2 - (cellSideLength F - 1) / 2) = ((s - cellCentre 0 z) i).valMinAbs := by
    have := closedOrthant_mul_self he i
    calc _ = (closedOrthant S z i * closedOrthant S z i) * ((s - cellCentre 0 z) i).valMinAbs := by ring
      _ = _ := by rw [this, one_mul]
  rw [e, ZMod.coe_valMinAbs]
  simp
theorem patchSite_injOn (hamb : IsAdmissibleAmbient F) (hodd : Odd F.blockSide)
    (he : ∀ i, closedOrthant S z i = 1 ∨ closedOrthant S z i = -1) :
    Set.InjOn (patchSite S z) (patchDomain S z : Set Lattice4) := by
  intro a ha b hb h
  rw [← patchChart_patchSite hamb hodd he (patchDomain_coord_bounds ha), h,
    patchChart_patchSite hamb hodd he (patchDomain_coord_bounds hb)]
theorem enclosingCell_cellCentre_add {j : ℕ} (hodd : Odd F.blockSide) (y : F.Cell) (h : Fin 4 → ℤ)
    (hh : h ∈ centredCube (F.blockSide ^ (F.top - j))) :
    enclosingCell (cellCentre j y + siteOfCoords j h) = y := by apply _root_.YangMills.Construction.CellBumps.enclosingCell_cellCentre_add <;> assumption
theorem mem_centredCube_iff (h : Lattice4) :
    h ∈ centredCube (F.blockSide ^ F.top) ↔
      ∀ i, -((cellSideLength F - 1) / 2) ≤ h i ∧ h i ≤ (cellSideLength F - 1) / 2 := by
  have e : (((F.blockSide ^ F.top : ℕ) : ℤ)) = cellSideLength F := by simp [cellSideLength]
  simp [centredCube, Fintype.mem_piFinset, e]
theorem patchChart_mem_patchDomain (hamb : IsAdmissibleAmbient F) (hodd : Odd F.blockSide)
    (he : ∀ i, closedOrthant S z i = 1 ∨ closedOrthant S z i = -1)
    {y : F.Cell} (hy : y ∈ S) (hd : cellSupDist z y ≤ 10) {h : Lattice4}
    (hh : h ∈ centredCube (F.blockSide ^ F.top)) :
    patchChart S z (cellCentre 0 y + siteOfCoords 0 h) ∈ patchDomain S z := by
  classical
  have hL := hodd.pos
  have hN := cellSideLength_pos (F := F) hL
  obtain ⟨h0, h1⟩ := cellSideLength_half (F := F) hodd
  set o : Lattice4 := cellDisplacement z y with ho
  have hob : ∀ i, |o i| ≤ 10 := by
    intro i
    have h2 := natAbs_valMinAbs_le_cellSupDist y z i
    rw [cellSupDist_symm] at h2
    have h3 : (o i).natAbs ≤ 10 := h2.trans hd
    rw [Int.abs_eq_natAbs]
    exact_mod_cast h3
  have hyz : y = z + siteOfCoords F.top o := eq_add_siteOfCoords_cellDisplacement z y
  have hc := cellCentre_add 0 (Nat.zero_le _) z o
  rw [← hyz] at hc
  have hcs : (F.blockSide : ℤ) ^ (F.top - 0) = cellSideLength F := by simp [cellSideLength]
  rw [hcs] at hc
  have hhb := (mem_centredCube_iff h).1 hh
  have hcoord : ∀ i, patchChart S z (cellCentre 0 y + siteOfCoords 0 h) i =
      closedOrthant S z i * (cellSideLength F * o i + h i) + (cellSideLength F - 1) / 2 := by
    intro i
    have e : (cellCentre 0 y + siteOfCoords 0 h - cellCentre 0 z : F.Site 0) i =
        ((cellSideLength F * o i + h i : ℤ) : ZMod (F.period 0 i)) := by
      rw [hc]
      simp [siteOfCoords]
      ring
    have hb : |cellSideLength F * o i + h i| < 32 * cellSideLength F := by
      have h2 : |cellSideLength F * o i| ≤ cellSideLength F * 10 := by
        rw [abs_mul, abs_of_pos hN]
        exact mul_le_mul_of_nonneg_left (hob i) hN.le
      have h3 := hhb i
      have h4 := abs_le.1 h2
      rw [abs_lt]
      constructor <;> omega
    simp only [patchChart]
    rw [e, valMinAbs_of_abs_lt hamb hL i hb]
  have hbnd : ∀ i, closedOrthant S z i * o i * cellSideLength F ≤
        patchChart S z (cellCentre 0 y + siteOfCoords 0 h) i ∧
      patchChart S z (cellCentre 0 y + siteOfCoords 0 h) i ≤
        closedOrthant S z i * o i * cellSideLength F + (cellSideLength F - 1) := by
    intro i
    rw [hcoord i]
    have h3 := hhb i
    have e : closedOrthant S z i * (cellSideLength F * o i + h i) + (cellSideLength F - 1) / 2 =
        closedOrthant S z i * o i * cellSideLength F +
          (closedOrthant S z i * h i + (cellSideLength F - 1) / 2) := by ring
    rw [e]
    rcases he i with hs | hs <;> rw [hs] <;> constructor <;> omega
  refine Finset.mem_filter.2 ⟨Fintype.mem_piFinset.2 fun i => ?_, ?_⟩
  · rw [Finset.mem_Icc]
    have h2 := hbnd i
    have h3 : |closedOrthant S z i * o i| ≤ 10 := by
      rw [abs_mul, abs_closedOrthant he, one_mul]
      exact hob i
    obtain ⟨h4, h5⟩ := abs_le.1 h3
    have h6 : (-10) * cellSideLength F ≤ closedOrthant S z i * o i * cellSideLength F :=
      mul_le_mul_of_nonneg_right h4 hN.le
    have h7 : closedOrthant S z i * o i * cellSideLength F ≤ 10 * cellSideLength F :=
      mul_le_mul_of_nonneg_right h5 hN.le
    constructor <;> omega
  · refine ⟨fun i => closedOrthant S z i * cellDisplacement z y i * cellSideLength F, ?_, fun i => (hbnd i).1⟩
    exact Finset.mem_image.2 ⟨y, Finset.mem_filter.2 ⟨hy, hd⟩, rfl⟩
theorem exists_cell_of_mem_patchDomain (hamb : IsAdmissibleAmbient F) (hodd : Odd F.blockSide) {m : ℕ}
    (hreg : IsOrthantRegular S m) (hm : 32 ≤ m) {a : Lattice4} (ha : a ∈ patchDomain S z) :
    ∃ (y : F.Cell) (h : Lattice4), y ∈ S ∧ cellSupDist y z ≤ 20 ∧ h ∈ centredCube (F.blockSide ^ F.top) ∧
      patchSite S z a = cellCentre 0 y + siteOfCoords 0 h := by
  classical
  obtain ⟨he, hcl⟩ := closedOrthant_spec (S := S) hreg hm z
  have hL := hodd.pos
  have hN := cellSideLength_pos (F := F) hL
  obtain ⟨h0, h1⟩ := cellSideLength_half (F := F) hodd
  obtain ⟨-, c, hc, hac⟩ := Finset.mem_filter.1 ha
  obtain ⟨y0, hy0, rfl⟩ := Finset.mem_image.1 hc
  obtain ⟨hy0S, hy0d⟩ := Finset.mem_filter.1 hy0
  set o : Lattice4 := fun i => closedOrthant S z i * cellDisplacement z y0 i with ho
  set v : Lattice4 := fun i => a i / cellSideLength F with hv
  have hob : ∀ i, |o i| ≤ 10 := by
    intro i
    have h2 := natAbs_valMinAbs_le_cellSupDist y0 z i
    rw [cellSupDist_symm] at h2
    have h3 : (cellDisplacement z y0 i).natAbs ≤ 10 := h2.trans hy0d
    rw [abs_mul, abs_closedOrthant he, one_mul, Int.abs_eq_natAbs]
    exact_mod_cast h3
  have hvr : ∀ i, cellSideLength F * v i ≤ a i ∧ a i < cellSideLength F * v i + cellSideLength F := by
    intro i
    have h2 : cellSideLength F * (a i / cellSideLength F) + a i % cellSideLength F = a i := by
      rw [Int.emod_def]; ring
    have h3 := Int.emod_nonneg (a i) hN.ne'
    have h4 := Int.emod_lt_of_pos (a i) hN
    simp only [hv]
    constructor <;> omega
  have hvo : ∀ i, o i ≤ v i := by
    intro i
    have h2 : o i * cellSideLength F ≤ a i := hac i
    exact (Int.le_ediv_iff_mul_le hN).2 h2
  have hv20 : ∀ i, v i ≤ 20 := by
    intro i
    have h2 := (patchDomain_coord_bounds ha i).2
    have h3 := (hvr i).1
    by_contra hc2
    have h4 : 21 ≤ v i := by omega
    have h5 : cellSideLength F * 21 ≤ cellSideLength F * v i := mul_le_mul_of_nonneg_left h4 hN.le
    omega
  have hvm : ∀ i, -10 ≤ v i := fun i => le_trans (abs_le.1 (hob i)).1 (hvo i)
  refine ⟨localCell S z v,
    fun i => closedOrthant S z i * (a i - (cellSideLength F - 1) / 2 - cellSideLength F * v i), ?_, ?_, ?_, ?_⟩
  · have hy0e : y0 = z + siteOfCoords F.top (cellDisplacement z y0) := eq_add_siteOfCoords_cellDisplacement z y0
    have hd32 : cellSupDist y0 z ≤ 32 := by
      rw [cellSupDist_symm]
      exact hy0d.trans (by norm_num)
    have hstep := hcl y0 hy0S hd32 (fun i => closedOrthant S z i * (v i - o i)) (fun i => ?_) (fun i => ?_)
    · have e : y0 + siteOfCoords F.top (fun i => closedOrthant S z i * (v i - o i)) = localCell S z v := by
        rw [hy0e, add_assoc, ← siteOfCoords_add]
        unfold localCell
        congr 2
        funext i
        have := closedOrthant_mul_self he i
        simp only [Pi.add_apply, ho]
        calc cellDisplacement z y0 i + closedOrthant S z i * (v i - closedOrthant S z i * cellDisplacement z y0 i)
            = (1 - closedOrthant S z i * closedOrthant S z i) * cellDisplacement z y0 i +
                closedOrthant S z i * v i := by ring
          _ = _ := by rw [this]; ring
      rwa [e] at hstep
    · have := closedOrthant_mul_self he i
      have h2 := hvo i
      calc 0 ≤ v i - o i := by omega
        _ = closedOrthant S z i * (closedOrthant S z i * (v i - o i)) := by rw [← mul_assoc, this, one_mul]
    · rw [abs_mul, abs_closedOrthant he, one_mul, abs_le]
      have h2 := hvo i
      have h3 := hv20 i
      have h4 := abs_le.1 (hob i)
      constructor <;> omega
  · refine cellSupDist_add_le hamb z (r := 20) (by norm_num) (fun i => ?_)
    rw [abs_mul, abs_closedOrthant he, one_mul, abs_le]
    have h3 := hv20 i
    have h4 := hvm i
    constructor <;> omega
  · rw [mem_centredCube_iff]
    intro i
    have h2 := hvr i
    rcases he i with hs | hs <;> rw [hs] <;> constructor <;> omega
  · have e : patchSite S z a - cellCentre 0 (localCell S z v) =
        siteOfCoords 0 fun i => closedOrthant S z i * (a i - (cellSideLength F - 1) / 2 - cellSideLength F * v i) := by
      funext i
      rw [patchSite_sub_cellCentre]
      simp [siteOfCoords]
    rw [← e]
    abel
theorem patchSite_mem_sitesOfCells (hamb : IsAdmissibleAmbient F) (hodd : Odd F.blockSide) {m : ℕ}
    (hreg : IsOrthantRegular S m) (hm : 32 ≤ m) {a : Lattice4} (ha : a ∈ patchDomain S z) :
    patchSite S z a ∈ sitesOfCells S 0 := by
  obtain ⟨y, h, hy, -, hh, e⟩ := exists_cell_of_mem_patchDomain hamb hodd hreg hm ha
  rw [e]
  exact mem_sitesOfCells.2 ⟨y, hy, h, by simpa using hh, rfl⟩
theorem enclosingCell_patchSite (hamb : IsAdmissibleAmbient F) (hodd : Odd F.blockSide) {m : ℕ}
    (hreg : IsOrthantRegular S m) (hm : 32 ≤ m) {a : Lattice4} (ha : a ∈ patchDomain S z) :
    enclosingCell (patchSite S z a) ∈ S ∧ cellSupDist (enclosingCell (patchSite S z a)) z ≤ 20 := by
  obtain ⟨y, h, hy, hd, hh, e⟩ := exists_cell_of_mem_patchDomain hamb hodd hreg hm ha
  rw [e, enclosingCell_cellCentre_add hodd y h (by simpa using hh)]
  exact ⟨hy, hd⟩
theorem natAbs_valMinAbs_intCast_le (n : ℕ) (d : ℤ) : ((d : ZMod n).valMinAbs).natAbs ≤ d.natAbs := by apply _root_.YangMills.Construction.BlockWeights.natAbs_valMinAbs_intCast_le <;> assumption
theorem natAbs_valMinAbs_add_le_add (n : ℕ) (a b : ZMod n) :
    (a + b).valMinAbs.natAbs ≤ a.valMinAbs.natAbs + b.valMinAbs.natAbs := by apply _root_.YangMills.Construction.BlockWeights.natAbs_valMinAbs_add_le_add <;> assumption
theorem cellSupDist_enclosingCell_le (hodd : Odd F.blockSide) (x : F.Site 0) (y : F.Cell) (B : ℕ)
    (h : ∀ i, (((x - cellCentre 0 y) i).valMinAbs).natAbs ≤ B * F.blockSide ^ F.top) :
    cellSupDist (enclosingCell x) y ≤ B := by
  simp only [cellSupDist]
  apply Finset.sup_le
  intro i _
  obtain ⟨K, hK⟩ := Odd.pow (n := F.top) hodd
  set M : ℤ := 2 * (K : ℤ) + 1 with hM
  have hMpos : 0 < M := by omega
  have hN : (F.blockSide : ℤ) ^ F.top = M := by
    have h0 : ((F.blockSide ^ F.top : ℕ) : ℤ) = M := by rw [hK, hM]; push_cast; ring
    exact_mod_cast h0
  set d : ℤ := ((x - cellCentre 0 y) i).valMinAbs with hd
  have hdb : d.natAbs ≤ B * F.blockSide ^ F.top := h i
  set a : ℤ := siteCoords x i with ha
  set b : ℤ := siteCoords y i with hb
  set sd : ℤ := (F.extent i : ℤ) with hsd
  have hxb : x i = ((a : ℤ) : ZMod (F.period 0 i)) := (ZMod.intCast_zmod_cast (x i)).symm
  have hyb : (cellCentre 0 y : F.Site 0) i = ((M * b : ℤ) : ZMod (F.period 0 i)) := by
    simp only [cellCentre, siteOfCoords, Nat.sub_zero, hN]
    rfl
  have hcd : ((d : ℤ) : ZMod (F.period 0 i)) = ((a - M * b : ℤ) : ZMod (F.period 0 i)) := by
    rw [hd, ZMod.coe_valMinAbs, Pi.sub_apply, hxb, hyb, Int.cast_sub]
  obtain ⟨q, hq⟩ := (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).1 hcd
  have hper : (F.period 0 i : ℤ) = sd * M := by
    rw [← hN]
    simp [BlockFrame.period, hsd]
  rw [hper] at hq
  have hdabs : |d| ≤ B * M := by
    have h2 : ((d.natAbs : ℕ) : ℤ) ≤ ((B * F.blockSide ^ F.top : ℕ) : ℤ) := by exact_mod_cast hdb
    rw [Int.natCast_natAbs] at h2
    push_cast at h2
    rw [hN] at h2
    exact h2
  obtain ⟨h4, h5⟩ := abs_le.1 hdabs
  set T : ℤ := (d + K) / M with hT
  have hTb : -(B : ℤ) ≤ T ∧ T ≤ B := by
    constructor
    · have : -(B : ℤ) ≤ (d + K) / M := by
        rw [Int.le_ediv_iff_mul_le hMpos]
        nlinarith
      exact this
    · have : (d + K) / M < (B : ℤ) + 1 := Int.ediv_lt_of_lt_mul hMpos (by nlinarith)
      omega
  have hcell : (enclosingCell x - y : F.Cell) i = ((T : ℤ) : ZMod (F.period F.top i)) := by
    have e1 : a + K = (d + K) + M * (b + sd * q) := by
      have : a - M * b - d = sd * M * q := by linarith
      linear_combination this
    have e2 : (a + ((F.blockSide : ℤ) ^ (F.top - 0) - 1) / 2) / (F.blockSide : ℤ) ^ (F.top - 0) =
        b + sd * q + T := by
      rw [Nat.sub_zero, hN]
      have h2 : (2 * (K : ℤ) + 1 - 1) / 2 = K := by omega
      have h3 : (M - 1) / 2 = K := by rw [hM]; exact h2
      rw [h3, e1, Int.add_mul_ediv_left _ _ hMpos.ne', hT]
      ring
    have hyc : ((b : ℤ) : ZMod (F.period F.top i)) = y i := ZMod.intCast_zmod_cast (y i)
    have hz0 : ((sd * q : ℤ) : ZMod (F.period F.top i)) = 0 := by
      refine (CharP.intCast_eq_zero_iff (ZMod (F.period F.top i)) (F.period F.top i) _).2 ?_
      have hpn : (F.period F.top i : ℤ) = sd := by simp [BlockFrame.period, hsd]
      rw [hpn]
      exact Dvd.intro _ rfl
    have e3 : (enclosingCell x : F.Cell) i = ((b + sd * q + T : ℤ) : ZMod (F.period F.top i)) := by
      rw [← e2]
      rfl
    rw [Pi.sub_apply, e3, Int.cast_add, Int.cast_add, hz0, hyc]
    ring
  rw [Pi.sub_apply] at hcell
  rw [hcell]
  refine le_trans (natAbs_valMinAbs_intCast_le _ _) ?_
  omega
theorem natAbs_valMinAbs_stepDisplacement_le (st : PathStep) (i : Fin 4) :
    (((stepDisplacement (F := F) 0 st) i).valMinAbs).natAbs ≤ 1 := by
  have e : (stepDisplacement (F := F) 0 st) i =
      (((if st.2 then 1 else -1) * (Pi.single st.1 1 : Fin 4 → ℤ) i : ℤ) : ZMod (F.period 0 i)) := by
    simp only [stepDisplacement, unitStep]
    split_ifs <;> simp [siteOfCoords]
  rw [e]
  refine le_trans (natAbs_valMinAbs_intCast_le _ _) ?_
  by_cases hi : i = st.1
  · subst hi
    split_ifs <;> simp
  · simp [hi]
theorem cellSupDist_enclosingCell_step (hodd : Odd F.blockSide) {y : F.Cell} {h : Lattice4}
    (hh : h ∈ centredCube (F.blockSide ^ F.top)) (st : PathStep) :
    cellSupDist (enclosingCell (cellCentre 0 y + siteOfCoords 0 h + stepDisplacement 0 st)) y ≤ 1 := by
  refine cellSupDist_enclosingCell_le hodd _ y 1 fun i => ?_
  have hL := hodd.pos
  have hb := (mem_centredCube_iff h).1 hh i
  obtain ⟨h0, h1⟩ := cellSideLength_half (F := F) hodd
  have e : (cellCentre 0 y + siteOfCoords 0 h + stepDisplacement 0 st - cellCentre 0 y : F.Site 0) i =
      ((h i : ℤ) : ZMod (F.period 0 i)) + (stepDisplacement (F := F) 0 st) i := by
    simp only [Pi.sub_apply, Pi.add_apply, siteOfCoords]
    ring
  rw [e]
  refine (natAbs_valMinAbs_add_le_add _ _ _).trans ?_
  have h2 := natAbs_valMinAbs_intCast_le (F.period 0 i) (h i)
  have h3 := natAbs_valMinAbs_stepDisplacement_le (F := F) st i
  have h4 : (h i).natAbs + 1 ≤ F.blockSide ^ F.top := by
    have hN := cellSideLength_pos (F := F) hL
    have e5 : ((F.blockSide ^ F.top : ℕ) : ℤ) = cellSideLength F := by simp [cellSideLength]
    have : (((h i).natAbs : ℕ) : ℤ) + 1 ≤ ((F.blockSide ^ F.top : ℕ) : ℤ) := by
      rw [e5, Int.natCast_natAbs]
      have := abs_le.2 hb
      have h6 : 3 ≤ cellSideLength F ∨ cellSideLength F = 1 := by omega
      rcases h6 with h6 | h6
      · omega
      · have h7 : (cellSideLength F - 1) / 2 = 0 := by omega
        rw [h7] at this
        have h8 : |h i| = 0 := le_antisymm this (abs_nonneg _)
        omega
    exact_mod_cast this
  omega
end PatchPoints
end YangMills.Construction
end
