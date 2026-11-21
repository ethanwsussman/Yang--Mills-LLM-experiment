import YangMills.Construction.HoleBesideASecondHole.ComplementOfEnlargedLumpsIsRegular
import YangMills.Construction.HoleBesideASecondHole.CostOnWholeCellsIsTheLeastAction
import YangMills.Construction.HoleBesideASecondHole.TopHotPlaquettesPayProof
import YangMills.Construction.HoleBesideASecondHole.WhatAHoleSavesAtParameters
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction
open BlockAverages LumpContours HoleBounds LatticeFractionalIntegration
namespace HoleBounds.FromThresholds
variable {F : BlockFrame}
theorem cellSupDist_triangle (a b c : F.Cell) :
    cellSupDist a c ≤ cellSupDist a b + cellSupDist b c := by apply _root_.YangMills.Construction.BlockAverages.PatchLocality.cellSupDist_triangle <;> assumption
theorem top_sub_depth : F.top - F.depth = 1 := by apply _root_.YangMills.Construction.GaugeFixing.top_sub_depth <;> assumption
theorem enclosingCell_cellCentre_add (hL : Odd F.blockSide) {j : ℕ} (z : F.Cell) (h : Fin 4 → ℤ)
    (hh : h ∈ centredCube (F.blockSide ^ (F.top - j))) :
    enclosingCell (cellCentre j z + siteOfCoords j h : F.Site j) = z := by apply _root_.YangMills.Construction.BlockLines.enclosingCell_cellCentre_add <;> assumption
theorem mem_sitesBelow_iff {x : F.Site F.depth} {y : F.Cell} :
    x ∈ sitesBelow F.depth y ↔
      ∃ h ∈ centredCube (F.blockSide ^ (F.top - F.depth)), x = cellCentre F.depth y + siteOfCoords F.depth h := by
  simp only [sitesBelow, Finset.mem_image]
  constructor
  · rintro ⟨h, hh, rfl⟩
    refine ⟨h, hh, ?_⟩
    rw [cellCentre, ← siteOfCoords_add]
    rfl
  · rintro ⟨h, hh, rfl⟩
    refine ⟨h, hh, ?_⟩
    rw [cellCentre, ← siteOfCoords_add]
    rfl
theorem enclosingCell_of_mem_sitesBelow (hL : Odd F.blockSide) {x : F.Site F.depth} {y : F.Cell}
    (hx : x ∈ sitesBelow F.depth y) : enclosingCell x = y := by
  obtain ⟨h, hh, rfl⟩ := mem_sitesBelow_iff.1 hx
  exact enclosingCell_cellCentre_add hL y h hh
theorem mem_centredCube_iff {M : ℕ} {h : Fin 4 → ℤ} :
    h ∈ centredCube M ↔ ∀ i, |h i| ≤ ((M : ℤ) - 1) / 2 := by apply _root_.YangMills.Construction.LumpContours.BlockLevels.mem_centredCube_iff <;> assumption
theorem cellCentre_siteOfCoords (c : Fin 4 → ℤ) :
    cellCentre F.depth (siteOfCoords F.top c : F.Cell) =
      siteOfCoords F.depth (fun i => (F.blockSide : ℤ) * c i) := by
  have h := cellCentre_add (F := F) F.depth (Nat.le_succ _) 0 c
  rw [zero_add] at h
  rw [h, top_sub_depth]
  have h0 : cellCentre F.depth (0 : F.Cell) = 0 := by
    funext i
    simp [cellCentre, siteOfCoords, siteCoords]
  rw [h0, zero_add]
  simp
theorem exists_cellCentre_add (hL : Odd F.blockSide) (x : F.Site F.depth) :
    ∃ (z : F.Cell) (h : Fin 4 → ℤ), h ∈ centredCube (F.blockSide ^ (F.top - F.depth)) ∧
      x = cellCentre F.depth z + siteOfCoords F.depth h := by
  have hLz : (0 : ℤ) < F.blockSide := by exact_mod_cast hL.pos
  obtain ⟨m, hm⟩ := hL
  have hmz : (F.blockSide : ℤ) = 2 * m + 1 := by exact_mod_cast hm
  refine ⟨siteOfCoords F.top (fun i => (siteCoords x i + m) / (F.blockSide : ℤ)),
    fun i => (siteCoords x i + m) % (F.blockSide : ℤ) - m, ?_, ?_⟩
  · rw [mem_centredCube_iff, top_sub_depth]
    intro i
    have h1 := Int.emod_nonneg (siteCoords x i + m) hLz.ne'
    have h2 := Int.emod_lt_of_pos (siteCoords x i + m) hLz
    have e : (((F.blockSide ^ 1 : ℕ) : ℤ) - 1) / 2 = m := by
      push_cast
      rw [pow_one, hmz]
      omega
    rw [e, abs_le]
    constructor <;> omega
  · rw [cellCentre_siteOfCoords, ← siteOfCoords_add]
    have e : ((fun i => (F.blockSide : ℤ) * ((siteCoords x i + m) / (F.blockSide : ℤ))) +
        fun i => (siteCoords x i + m) % (F.blockSide : ℤ) - m) = siteCoords x := by
      funext i
      have := Int.mul_ediv_add_emod (siteCoords x i + m) (F.blockSide : ℤ)
      simp only [Pi.add_apply]
      linarith
    rw [e, siteOfCoords_siteCoords]
theorem cellSupDist_enclosingCell_add_le_one (hL : Odd F.blockSide) (hamb : IsAdmissibleAmbient F)
    (x : F.Site F.depth) (h : Fin 4 → ℤ) (hh : ∀ i, |h i| ≤ 1) :
    cellSupDist (enclosingCell (x + siteOfCoords F.depth h)) (enclosingCell x) ≤ 1 := by
  obtain ⟨z, h₀, hh₀, rfl⟩ := exists_cellCentre_add hL x
  have hLz : (0 : ℤ) < F.blockSide := by exact_mod_cast hL.pos
  obtain ⟨m, hm⟩ := id hL
  have hmz : (F.blockSide : ℤ) = 2 * m + 1 := by exact_mod_cast hm
  have e0 : (((F.blockSide ^ 1 : ℕ) : ℤ) - 1) / 2 = m := by
    push_cast
    rw [pow_one, hmz]
    omega
  have hb₀ : ∀ i, |h₀ i| ≤ m := by
    intro i
    have := mem_centredCube_iff.1 hh₀ i
    rwa [top_sub_depth, e0] at this
  rw [enclosingCell_cellCentre_add hL z h₀ hh₀]
  set d : Fin 4 → ℤ := fun i => (h₀ i + h i + m) / (F.blockSide : ℤ) with hd
  set h' : Fin 4 → ℤ := fun i => (h₀ i + h i + m) % (F.blockSide : ℤ) - m with hh'
  have hsplit : ∀ i, h₀ i + h i = (F.blockSide : ℤ) * d i + h' i := by
    intro i
    have := Int.mul_ediv_add_emod (h₀ i + h i + m) (F.blockSide : ℤ)
    simp only [hd, hh']
    linarith
  have hh'c : h' ∈ centredCube (F.blockSide ^ (F.top - F.depth)) := by
    rw [mem_centredCube_iff, top_sub_depth, e0]
    intro i
    have h1 := Int.emod_nonneg (h₀ i + h i + m) hLz.ne'
    have h2 := Int.emod_lt_of_pos (h₀ i + h i + m) hLz
    simp only [hh']
    rw [abs_le]
    constructor <;> omega
  have hdb : ∀ i, |d i| ≤ 1 := by
    intro i
    have a1 := abs_le.1 (hb₀ i)
    have a2 := abs_le.1 (hh i)
    rw [abs_le]
    constructor
    · apply Int.le_ediv_of_mul_le hLz
      linarith
    · have : (h₀ i + h i + m) / (F.blockSide : ℤ) < 2 := by
        apply Int.ediv_lt_of_lt_mul hLz
        linarith
      simp only [hd]
      omega
  have hx : (cellCentre F.depth z + siteOfCoords F.depth h₀ + siteOfCoords F.depth h : F.Site F.depth) =
      cellCentre F.depth (z + siteOfCoords F.top d) + siteOfCoords F.depth h' := by
    have h1 := cellCentre_add (F := F) F.depth (Nat.le_succ _) z d
    rw [h1, top_sub_depth, add_assoc, add_assoc, ← siteOfCoords_add, ← siteOfCoords_add]
    congr 2
    funext i
    simp only [Pi.add_apply, pow_one]
    exact hsplit i
  rw [hx, enclosingCell_cellCentre_add hL _ h' hh'c]
  exact cellSupDist_add_le hamb z (by norm_num) (by simpa using hdb)
theorem mem_lumpOf {L : ℕ} (hL : Odd L) (g : LumpGrid L) {j : ℕ} (x : F.Site j) : x ∈ lumpOf g x := by
  have hLz : (0 : ℤ) < L := by exact_mod_cast hL.pos
  obtain ⟨m, hm⟩ := hL
  have e : ((L : ℤ) - 1) / 2 = m := by omega
  unfold lumpOf boxSites
  refine Finset.mem_image.2 ⟨siteCoords x, Fintype.mem_piFinset.2 fun i => ?_, siteOfCoords_siteCoords x⟩
  have h1 := Int.emod_nonneg (siteCoords x i + m) hLz.ne'
  have h2 := Int.emod_lt_of_pos (siteCoords x i + m) hLz
  have hb : |offsetFromCentre L (siteCoords x i)| ≤ ((L : ℤ) - 1) / 2 := by
    unfold offsetFromCentre
    rw [e, abs_le]
    constructor <;> omega
  obtain ⟨-, b2, b3, -⟩ := g.mem_interval _ hb
  rw [Finset.mem_Icc]
  constructor <;> linarith
theorem mem_thicken {j : ℕ} (m : ℕ) {X : Finset (F.Site j)} {x : F.Site j} (hx : x ∈ X) :
    x ∈ thicken m X := by apply _root_.YangMills.Construction.HoleSavings.TopHotPlaquetteCost.mem_thicken <;> assumption
theorem mem_lumpsNeighbourhood {j : ℕ} {H : Finset (Finset (F.Site j))} {l : Finset (F.Site j)}
    {x : F.Site j} (hl : l ∈ H) (hx : x ∈ l) : x ∈ lumpsNeighbourhood H :=
  Finset.mem_biUnion.2 ⟨l, hl, mem_thicken _ hx⟩
theorem exists_offset_of_mem_plaquetteCorners {j : ℕ} (p : F.Site j × Fin 4 × Fin 4) (hp : p.2.1 < p.2.2)
    {c : F.Site j} (hc : c ∈ plaquetteCorners p) :
    ∃ δ : Fin 4 → ℤ, (∀ i, 0 ≤ δ i ∧ δ i ≤ 1) ∧ c = p.1 + siteOfCoords j δ := by
  have hne : p.2.1 ≠ p.2.2 := hp.ne
  have hs : ∀ (k i : Fin 4), (0 : ℤ) ≤ basisVector k i ∧ basisVector k i ≤ 1 := by
    intro k i
    by_cases h : i = k
    · subst h
      simp [basisVector]
    · simp [basisVector, h]
  simp only [plaquetteCorners, Finset.mem_insert, Finset.mem_singleton] at hc
  rcases hc with rfl | rfl | rfl | rfl
  · exact ⟨0, fun i => by simp, by rw [siteOfCoords_zero, add_zero]⟩
  · exact ⟨basisVector p.2.1, hs _, rfl⟩
  · exact ⟨basisVector p.2.2, hs _, rfl⟩
  · refine ⟨basisVector p.2.1 + basisVector p.2.2, fun i => ?_, ?_⟩
    · by_cases h1 : i = p.2.1
      · have h2 : i ≠ p.2.2 := fun e => hne (h1.symm.trans e)
        simp [basisVector, h1, hne]
      · by_cases h2 : i = p.2.2
        · simp [basisVector, h2, hne.symm]
        · simp [basisVector, h1, h2]
    · rw [siteOfCoords_add, ← add_assoc]
      rfl
theorem cellSupDist_plaquetteCorners_le_one (hL : Odd F.blockSide) (hamb : IsAdmissibleAmbient F)
    (p : F.Site F.depth × Fin 4 × Fin 4) (hp : p.2.1 < p.2.2) {c c' : F.Site F.depth}
    (hc : c ∈ plaquetteCorners p) (hc' : c' ∈ plaquetteCorners p) :
    cellSupDist (enclosingCell c') (enclosingCell c) ≤ 1 := by
  obtain ⟨δ, hδ, rfl⟩ := exists_offset_of_mem_plaquetteCorners p hp hc
  obtain ⟨δ', hδ', rfl⟩ := exists_offset_of_mem_plaquetteCorners p hp hc'
  have e : (p.1 + siteOfCoords F.depth δ' : F.Site F.depth) =
      p.1 + siteOfCoords F.depth δ + siteOfCoords F.depth (δ' - δ) := by
    rw [siteOfCoords_sub]
    abel
  rw [e]
  apply cellSupDist_enclosingCell_add_le_one hL hamb
  intro i
  have a1 := hδ i
  have a2 := hδ' i
  simp only [Pi.sub_apply]
  rw [abs_le]
  constructor <;> linarith [a1.1, a1.2, a2.1, a2.2]
theorem plaquetteHolonomy_eq_links {j : ℕ} (X : F.GaugeField j) (p : F.Site j × Fin 4 × Fin 4) :
    plaquetteHolonomy X p = X p.1 p.2.1 * (X (p.1 + unitStep j p.2.1) p.2.2 *
      ((X (p.1 + unitStep j p.2.2) p.2.1)⁻¹ * (X p.1 p.2.2)⁻¹)) := by
  have e1 : p.1 + unitStep j p.2.1 + unitStep j p.2.2 - unitStep j p.2.1 = p.1 + unitStep j p.2.2 := by abel
  have e2 : p.1 + unitStep j p.2.1 + unitStep j p.2.2 + - unitStep j p.2.1 = p.1 + unitStep j p.2.2 := by
    abel
  have e3 : p.1 + unitStep j p.2.2 - unitStep j p.2.2 = p.1 := by abel
  simp only [plaquetteHolonomy, pathHolonomy, linkValue, stepDisplacement, if_true, Bool.false_eq_true,
    if_false, mul_one, e1, e2, e3]
theorem plaquetteDefect_congr {j : ℕ} {Y : Finset (F.Site j)} {X X' : F.GaugeField j}
    {p : F.Site j × Fin 4 × Fin 4} (hp : plaquetteCorners p ⊆ Y)
    (h : ∀ b ∈ cutBonds Y, b.1 ∈ plaquetteCorners p → X b.1 b.2 = X' b.1 b.2) :
    plaquetteDefect X p = plaquetteDefect X' p := by
  have c1 : p.1 ∈ plaquetteCorners p := by simp [plaquetteCorners]
  have c2 : p.1 + unitStep j p.2.1 ∈ plaquetteCorners p := by simp [plaquetteCorners]
  have c3 : p.1 + unitStep j p.2.2 ∈ plaquetteCorners p := by simp [plaquetteCorners]
  have c4 : p.1 + unitStep j p.2.1 + unitStep j p.2.2 ∈ plaquetteCorners p := by simp [plaquetteCorners]
  have mem : ∀ (x : F.Site j) (i : Fin 4), x ∈ plaquetteCorners p → x + unitStep j i ∈ plaquetteCorners p →
      X x i = X' x i := by
    intro x i hx hx'
    refine h (x, i) ?_ hx
    simp only [cutBonds, Finset.mem_filter, Finset.mem_product, Finset.mem_univ, and_true]
    exact ⟨hp hx, hp hx'⟩
  have c5 : p.1 + unitStep j p.2.2 + unitStep j p.2.1 ∈ plaquetteCorners p := by
    rw [add_right_comm]
    exact c4
  unfold plaquetteDefect
  rw [plaquetteHolonomy_eq_links X, plaquetteHolonomy_eq_links X', mem _ _ c1 c2, mem _ _ c2 c4,
    mem _ _ c3 c5, mem _ _ c1 c3]
theorem plaquetteDefect_gaugeTransform {j : ℕ} (γ : F.Site j → UnitQuaternion) (X : F.GaugeField j)
    (p : F.Site j × Fin 4 × Fin 4) : plaquetteDefect (gaugeTransform γ X) p = plaquetteDefect X p := by apply _root_.YangMills.Construction.GaugeFixing.plaquetteDefect_gaugeTransform <;> assumption
theorem lt_and_subset_of_mem_cutPlaquettes {j : ℕ} {X : Finset (F.Site j)} {p : F.Site j × Fin 4 × Fin 4}
    (hp : p ∈ cutPlaquettes X) : p.2.1 < p.2.2 ∧ plaquetteCorners p ⊆ X := by apply _root_.YangMills.Construction.HoleSavings.TopHotPlaquetteCost.plaquetteCorners_subset <;> assumption
theorem isCold_off_hotLumps {L : ℕ} (hL : Odd L) (g : LumpGrid L) {s : ℝ} (S₀ : Finset F.Cell)
    (V : F.GaugeField F.top) :
    IsCold (S₀ \ lumpsNeighbourhood (hotLumps g s S₀ V)) F.top s V := by
  classical
  intro p hp
  by_contra hc
  rw [not_lt] at hc
  simp only [innerPlaquettes, Finset.mem_filter, Finset.mem_product, Finset.mem_univ, and_true] at hp
  obtain ⟨h1, h2, h3⟩ := hp
  have hmem : ∀ x, x ∈ plaquetteCorners p → x ∈ S₀ \ lumpsNeighbourhood (hotLumps g s S₀ V) := fun x hx =>
    mem_sitesOfCells_top.1 (h3 hx)
  have hp1 : p.1 ∈ plaquetteCorners p := by simp [plaquetteCorners]
  have hpc : p ∈ cutPlaquettes S₀ := by
    simp only [cutPlaquettes, Finset.mem_filter, Finset.mem_product, Finset.mem_univ, and_true]
    exact ⟨(Finset.mem_sdiff.1 (hmem _ hp1)).1, h2, fun x hx => (Finset.mem_sdiff.1 (hmem x hx)).1⟩
  have hl : lumpOf g p.1 ∈ hotLumps g s S₀ V := by
    unfold hotLumps
    refine Finset.mem_biUnion.2 ⟨p, Finset.mem_filter.2 ⟨hpc, hc⟩, Finset.mem_image.2 ⟨p.1, hp1, rfl⟩⟩
  exact (Finset.mem_sdiff.1 (hmem _ hp1)).2 (mem_lumpsNeighbourhood hl (mem_lumpOf hL g p.1))
theorem cellsOffLumps_sdiff (H H' : Finset (Finset (F.Site F.top))) :
    cellsOffLumps F H \ lumpsNeighbourhood H' = cellsOffLumps F (H ∪ H') := by
  classical
  ext x
  simp only [cellsOffLumps, lumpsNeighbourhood, Finset.mem_sdiff, Finset.union_biUnion, Finset.mem_union]
  tauto
theorem hasLumpWall_of_isCold {L : ℕ} (hL : Odd L) (hFL : F.blockSide = L) (hamb : IsAdmissibleAmbient F)
    (g : LumpGrid L) {s : ℝ} (hs : 0 < s) (H : Finset (Finset (F.Site F.top))) (V : F.GaugeField F.top)
    (W Wl : F.GaugeField F.depth)
    (hcold : IsCold (cellsOffLumps F H \ lumpsNeighbourhood (hotLumps g s (cellsOffLumps F H) V))
      F.depth (s / 8) Wl)
    (hap : CellsSeparated (2 * wallMargin) (lumpsNeighbourhood (hotLumps g s (cellsOffLumps F H) V))
      (lumpsNeighbourhood H))
    (hag : AgreesWithMinimizerNear (lumpsNeighbourhood H)
      (cellsOffLumps F H \ lumpsNeighbourhood (hotLumps g s (cellsOffLumps F H) V)) W Wl) :
    HasLumpWall (cellsOffLumps F H) (hotLumps g s (cutBelow F.depth (cellsOffLumps F H)) W) := by
  classical
  have hLF : Odd F.blockSide := hFL ▸ hL
  set S₀ := cellsOffLumps F H with hS₀
  set S := S₀ \ lumpsNeighbourhood (hotLumps g s S₀ V) with hS
  intro l hl y hy hly z hz
  by_contra hd
  have hzN : z ∈ lumpsNeighbourhood H := by
    have := Finset.mem_sdiff.1 hz
    by_contra hn
    exact this.2 (Finset.mem_sdiff.2 ⟨this.1, hn⟩)
  unfold hotLumps at hl
  obtain ⟨p, hpf, hlp⟩ := Finset.mem_biUnion.1 hl
  obtain ⟨hpc, hcurv⟩ := Finset.mem_filter.1 hpf
  obtain ⟨c, hc, rfl⟩ := Finset.mem_image.1 hlp
  obtain ⟨hlt, hcor⟩ := lt_and_subset_of_mem_cutPlaquettes hpc
  have hcy : enclosingCell c = y := enclosingCell_of_mem_sitesBelow hLF (hly (mem_lumpOf hL g c))
  have hnear : ∀ c' ∈ plaquetteCorners p, cellSupDist (enclosingCell c') z ≤ 3 := by
    intro c' hc'
    have h1 := cellSupDist_plaquetteCorners_le_one hLF hamb p hlt hc hc'
    rw [hcy] at h1
    have := cellSupDist_triangle (enclosingCell c') y z
    omega
  have hinS : ∀ c' ∈ plaquetteCorners p, c' ∈ cutBelow F.depth S := by
    intro c' hc'
    obtain ⟨y', hy', hu⟩ := Finset.mem_biUnion.1 (hcor hc')
    have hcy' : enclosingCell c' = y' := enclosingCell_of_mem_sitesBelow hLF hu
    refine Finset.mem_biUnion.2 ⟨y', Finset.mem_sdiff.2 ⟨hy', fun hin => ?_⟩, hu⟩
    have h10 := hap y' hin z hzN
    have h3 := hnear c' hc'
    rw [hcy'] at h3
    simp only [wallMargin] at h10
    omega
  have hsame : plaquetteDefect W p = plaquetteDefect Wl p := by
    refine plaquetteDefect_congr (Y := cutBelow F.depth S) hinS fun b hb hbc => ?_
    refine hag b hb z hzN ((hnear _ hbc).trans ?_)
    simp only [wallMargin]
    omega
  have hpS : p ∈ innerPlaquettes S F.depth := by
    have hsit : cutBelow F.depth S = sitesOfCells S F.depth := by
      unfold cutBelow sitesOfCells
      refine Finset.biUnion_congr rfl fun z' _ => ?_
      unfold sitesBelow
      refine Finset.image_congr fun h _ => ?_
      rw [cellCentre, ← siteOfCoords_add]
      rfl
    have hp1 : p.1 ∈ plaquetteCorners p := by simp [plaquetteCorners]
    simp only [innerPlaquettes, Finset.mem_filter, Finset.mem_product, Finset.mem_univ, and_true]
    rw [← hsit]
    exact ⟨hinS _ hp1, hlt, fun x hx => hinS x hx⟩
  have h8 := hcold p hpS
  rw [hsame] at hcurv
  linarith
theorem holeSavingWorkingForm_of_inequality {L : ℕ} (g : LumpGrid L) {a κ s c c₁ : ℝ} {J₀ : ℕ}
    {S₀ S : Finset F.Cell} {hV : Finset (Finset (F.Site F.top))} {V : F.GaugeField F.top}
    {W : F.GaugeField F.depth} {b : F.Cell → F.Site F.depth} {Wl : F.GaugeField F.depth}
    (hκ : 0 < κ) (hc : 0 ≤ c) (hcc : c ≤ c₁)
    (h : HoleSavingInequality g a κ s c₁ J₀ S₀ S hV V W b Wl) :
    HoleSavingWorkingForm g a κ s c J₀ S₀ S hV V W b Wl := by
  classical
  have hsub : chartDeviantCells (s / 128) S V W Wl ⊆ badCells (s / 128) S V W Wl := by
    intro y hy
    simp only [chartDeviantCells, badCells, Finset.mem_filter] at hy ⊢
    obtain ⟨hyS, b', hb', hcy, hr⟩ := hy
    exact ⟨hyS, 1, b', hb', Or.inl hcy, hr⟩
  have hcard : ((chartDeviantCells (s / 128) S V W Wl).card : ℝ) ≤ (badCells (s / 128) S V W Wl).card := by
    exact_mod_cast Finset.card_le_card hsub
  unfold HoleSavingInequality at h
  unfold HoleSavingWorkingForm
  have h1 : 0 ≤ κ * s ^ 2 * (hV.card : ℝ) := by positivity
  have h2 : 0 ≤ κ * s ^ 2 * ((hotLumps g s (cutBelow F.depth S₀) W).card : ℝ) := by positivity
  have h3 : c * ((chartDeviantCells (s / 128) S V W Wl).card : ℝ) ≤
      c₁ * (badCells (s / 128) S V W Wl).card :=
    mul_le_mul hcc hcard (by positivity) (hc.trans hcc)
  nlinarith
theorem workingBoundsFromThresholds_holds (hR : LumpContours.ComplementOfThickenedLumpsRegular)
    (hC : LumpContours.WholeCellCostEqualsMinimalAction) :
    HoleBounds.WorkingBoundsFromThresholds := by
  intro L g a κ s cE c₁ c₂ J₀ hodd ha hκ hs hcE hc₁ hc₂ hchain h₁ h₂
  refine ⟨?_, ?_⟩
  · intro F hFL hcub hdvd H hH V W b Wl hap hleast hag hbases
    have hLF : Odd F.blockSide := hFL ▸ hodd
    have hside : ∀ i, 4096 ≤ F.extent i := fun i => by
      rw [hcub.1 i]
      exact hcub.2
    have hamb : IsAdmissibleAmbient F := Or.inr fun i => (by norm_num : 64 ≤ 4096).trans (hside i)
    have hlumps : ∀ l ∈ H ∪ hotLumps g s (cellsOffLumps F H) V, IsLump g l := by
      intro l hl
      rcases Finset.mem_union.1 hl with hl | hl
      · exact hH l hl
      · unfold hotLumps at hl
        obtain ⟨p, -, hlp⟩ := Finset.mem_biUnion.1 hl
        obtain ⟨c, -, rfl⟩ := Finset.mem_image.1 hlp
        exact ⟨c, rfl⟩
    have hreg : IsOrthantRegular
        (cellsOffLumps F H \ lumpsNeighbourhood (hotLumps g s (cellsOffLumps F H) V)) 2047 := by
      rw [cellsOffLumps_sdiff]
      refine hR.2 L g F _ hodd (fun i => (by norm_num : 0 < 4096).trans_le (hside i)) (fun i => ?_) hlumps
      rw [hcub.1 i]
      exact hdvd
    obtain ⟨ρ, N₀, w, -, hwcold, huniq⟩ := hchain F _ V hFL hamb hreg (isCold_off_hotLumps hodd g _ V)
    have hmin : ∀ W'', blockEnergy a (cellsOffLumps F H \ lumpsNeighbourhood (hotLumps g s (cellsOffLumps F H) V))
        F.depth Wl V ≤
        blockEnergy a (cellsOffLumps F H \ lumpsNeighbourhood (hotLumps g s (cellsOffLumps F H) V))
          F.depth W'' V := by
      intro W''
      have hE := (hC F a (cellsOffLumps F H \ lumpsNeighbourhood (hotLumps g s (cellsOffLumps F H) V))
        hLF ha).2.2
      rw [← hE, ← hE]
      exact hleast W''
    obtain ⟨γ, -, hsame⟩ := huniq Wl hmin
    have hcold : IsCold (cellsOffLumps F H \ lumpsNeighbourhood (hotLumps g s (cellsOffLumps F H) V))
        F.depth (s / 8) Wl := by
      intro p hp
      have hp' := hp
      simp only [innerPlaquettes, Finset.mem_filter] at hp'
      have e : plaquetteDefect Wl p = plaquetteDefect (gaugeTransform γ (chartedField w V)) p :=
        plaquetteDefect_congr hp'.2.2 fun b hb _ => hsame b hb
      rw [e, plaquetteDefect_gaugeTransform]
      exact hwcold p hp
    have hwall := hasLumpWall_of_isCold hodd hFL hamb g hs H V W Wl hcold hap hag
    have hB₁ := (h₁ F hFL hcub).1 hdvd H hH V W b Wl
    simp only [one_mul] at hB₁
    exact holeSavingWorkingForm_of_inequality g hκ hcE hc₁ (hB₁ hwall hbases hleast)
  · intro F hFL hcub V W b Wl hcold hleast hbases
    exact holeSavingWorkingForm_of_inequality g hκ hcE hc₂ ((h₂ F hFL hcub).2 V W b Wl hcold hbases hleast)
end HoleBounds.FromThresholds
end YangMills.Construction
end
