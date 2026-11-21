import YangMills.Construction.ColdChainAtEveryLevel.SharesAcrossABond
import YangMills.Construction.ColdChainAtEveryLevel.AnalyticSharesOfAColdTopProof
import YangMills.Construction.ColdChainAtEveryLevel.ChartsAtTheSameOffsets
import YangMills.Construction.ColdChainAtEveryLevel.ShareAtTheReference
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction.BlockAverages.SameOffsetShares
open YangMills.Construction.BlockAverages.SameOffsets YangMills.Construction.BlockAverages.SameOffsetCharts YangMills.Construction.LowerShare YangMills.Construction.ReferenceShare
variable {F : BlockFrame} {sd : Fin 4 → ℕ}
structure NeighbourhoodsAgree (S : Finset F.Cell) (S' : Finset (sameShapeFrame F sd).Cell) (Y : F.Cell)
    (Y' : (sameShapeFrame F sd).Cell) : Prop where
  ambient : IsAdmissibleAmbient F
  ambient' : IsAdmissibleAmbient (sameShapeFrame F sd)
  odd_blockSide : Odd F.blockSide
  mem_iff : ∀ a : LatticeFractionalIntegration.Lattice4, (∀ i, |a i| ≤ 4) →
    (Y + siteOfCoords F.top a ∈ S ↔ Y' + siteOfCoords (sameShapeFrame F sd).top a ∈ S')
  extent_large : ∀ i, F.extent i = 0 ∨ 8 < F.extent i
  extent_large' : ∀ i, sd i = 0 ∨ 8 < sd i
theorem NeighbourhoodsAgree.symm {S : Finset F.Cell} {S' : Finset (sameShapeFrame F sd).Cell} {Y : F.Cell}
    {Y' : (sameShapeFrame F sd).Cell} (T : NeighbourhoodsAgree S S' Y Y') :
    NeighbourhoodsAgree (F := sameShapeFrame F sd) (sd := F.extent) S' S Y' Y :=
  ⟨T.ambient', T.ambient, T.odd_blockSide, fun a ha => (T.mem_iff a ha).symm, T.extent_large', T.extent_large⟩
section Cells
variable {G : BlockFrame}
theorem eq_add_siteOfCoords_valMinAbs (Z y : G.Cell) : y = Z + siteOfCoords G.top fun i => ((y - Z) i).valMinAbs := by apply _root_.YangMills.Construction.BlockAverages.AnalyticCellShares.eq_add_siteOfCoords_offset <;> assumption
theorem abs_valMinAbs_sub_le {Z y : G.Cell} {ρ : ℕ} (hb : cellSupDist Z y ≤ ρ) (i : Fin 4) :
    |((y - Z) i).valMinAbs| ≤ ρ := by
  have h1 : (((Z i - y i).valMinAbs).natAbs) ≤ cellSupDist Z y :=
    Finset.le_sup (f := fun i => ((Z i - y i).valMinAbs).natAbs) (Finset.mem_univ i)
  have e : (y - Z) i = -(Z i - y i) := by simp
  rw [e, Int.abs_eq_natAbs, ZMod.natAbs_valMinAbs_neg]
  exact_mod_cast h1.trans hb
theorem period_top (i : Fin 4) : G.period G.top i = G.extent i := by apply _root_.YangMills.Construction.GaugeFixing.period_top <;> assumption
theorem valMinAbs_intCast_eq (hs : ∀ i, G.extent i = 0 ∨ 8 < G.extent i) (i : Fin 4) {A : ℤ} (hA : |A| ≤ 4) :
    ((A : ZMod (G.period G.top i))).valMinAbs = A := by
  apply valMinAbs_intCast_of_small
  rw [period_top]
  rcases hs i with h | h
  · exact Or.inl h
  · right
    have : (8 : ℤ) < (G.extent i : ℤ) := by exact_mod_cast h
    omega
theorem valMinAbs_add_siteOfCoords_sub (hs : ∀ i, G.extent i = 0 ∨ 8 < G.extent i) (Z : G.Cell)
    {a : LatticeFractionalIntegration.Lattice4} (ha : ∀ i, |a i| ≤ 4) (i : Fin 4) :
    ((Z + siteOfCoords G.top a - Z : G.Cell) i).valMinAbs = a i := by
  rw [add_sub_cancel_left]
  exact valMinAbs_intCast_eq hs i (ha i)
end Cells
variable {S : Finset F.Cell} {S' : Finset (sameShapeFrame F sd).Cell} {Y : F.Cell} {Y' : (sameShapeFrame F sd).Cell}
theorem exists_offset_of_mem (T : NeighbourhoodsAgree S S' Y Y') {j : ℕ} (hj : j ≤ F.top) {x : F.Site j}
    (hx : x ∈ sitesOfCells (cellBall S Y 4) j) :
    ∃ (a g : LatticeFractionalIntegration.Lattice4), (∀ i, |a i| ≤ 4) ∧ Y + siteOfCoords F.top a ∈ cellBall S Y 4 ∧
      g ∈ centredCube (F.blockSide ^ (F.top - j)) ∧
      x = cellCentre j (Y + siteOfCoords F.top a) + siteOfCoords j g ∧
      x = siteAtOffset Y j ((fun i => (F.blockSide : ℤ) ^ (F.top - j) * a i) + g) ∧
      IsSmallOffset F j ((fun i => (F.blockSide : ℤ) ^ (F.top - j) * a i) + g) := by
  classical
  obtain ⟨y, hy, g, hg, e⟩ := mem_sitesOfCells.1 hx
  obtain ⟨hyS, hyd⟩ := Finset.mem_filter.1 hy
  set a : LatticeFractionalIntegration.Lattice4 := fun i => ((y - Y) i).valMinAbs with ha
  have hya : y = Y + siteOfCoords F.top a := eq_add_siteOfCoords_valMinAbs Y y
  have hab : ∀ i, |a i| ≤ 4 := fun i => by exact_mod_cast abs_valMinAbs_sub_le hyd i
  refine ⟨a, g, hab, hya ▸ hy, hg, hya ▸ e, ?_, fun i => ?_⟩
  · rw [e, hya, cellCentre_add j hj, siteAtOffset_add]
    rfl
  · set K : ℤ := (F.blockSide : ℤ) ^ (F.top - j) with hK
    have hK1 : 1 ≤ K := one_le_pow₀ (by exact_mod_cast T.odd_blockSide.pos)
    have hgc := (LatticePaths.mem_centredCube_iff _ _).1 hg i
    have hcast : (((F.blockSide ^ (F.top - j) : ℕ) : ℤ)) = K := by
      rw [hK]
      push_cast
      rfl
    rw [hcast] at hgc
    have hgb : |g i| ≤ K := by
      rw [abs_le]
      constructor <;> omega
    have h1 := hab i
    simp only [Pi.add_apply]
    refine (abs_add_le _ _).trans_lt ?_
    rw [abs_mul, abs_of_pos (by omega : (0 : ℤ) < K)]
    nlinarith
theorem siteAtSameOffset_mem (T : NeighbourhoodsAgree S S' Y Y') {j : ℕ} (hj : j ≤ F.top) {x : F.Site j}
    (hx : x ∈ sitesOfCells (cellBall S Y 4) j) :
    siteAtSameOffset Y Y' x ∈ sitesOfCells (cellBall S' Y' 4) j ∧
      enclosingCell (siteAtSameOffset Y Y' x) = cellAtSameOffset Y Y' (enclosingCell x) ∧
      siteAtSameOffset Y' Y (siteAtSameOffset Y Y' x) = x := by
  classical
  obtain ⟨a, g, ha, hy, hg, e, e', hsm⟩ := exists_offset_of_mem T hj hx
  have hoddG : Odd (sameShapeFrame F sd).blockSide := T.odd_blockSide
  have ha4 : ∀ i, |a i| ≤ 4 := ha
  obtain ⟨hyS, hyd⟩ := Finset.mem_filter.1 hy
  have hcellx : enclosingCell x = Y + siteOfCoords F.top a := by
    rw [e]
    exact BlockLines.enclosingCell_cellCentre_add T.odd_blockSide _ g hg
  have e2 : siteAtSameOffset Y Y' x = cellCentre j (Y' + siteOfCoords (sameShapeFrame F sd).top a) + siteOfCoords j g := by
    have hc := cellCentre_add (F := sameShapeFrame F sd) j hj Y' a
    rw [e', siteAtSameOffset_siteAtOffset T.ambient T.odd_blockSide.pos Y Y' hsm, hc, siteAtOffset_add]
    rfl
  have hdist : cellSupDist Y' (Y' + siteOfCoords (sameShapeFrame F sd).top a) ≤ 4 := by
    have h1 := cellSupDist_add_le T.ambient' (Y' + siteOfCoords (sameShapeFrame F sd).top a) (a := - a) (r := 4) (by norm_num)
      (fun i => by simpa using ha i)
    rw [siteOfCoords_neg, add_neg_cancel_right] at h1
    exact h1
  have hmem : Y' + siteOfCoords (sameShapeFrame F sd).top a ∈ cellBall S' Y' 4 :=
    Finset.mem_filter.2 ⟨(T.mem_iff a ha).1 hyS, hdist⟩
  refine ⟨mem_sitesOfCells.2 ⟨_, hmem, g, hg, e2⟩, ?_, ?_⟩
  · rw [e2, BlockLines.enclosingCell_cellCentre_add hoddG _ g hg, hcellx]
    unfold cellAtSameOffset
    congr 2
    funext i
    exact (valMinAbs_add_siteOfCoords_sub T.extent_large Y ha4 i).symm
  · have hsm' : IsSmallOffset (sameShapeFrame F sd) j ((fun i => (F.blockSide : ℤ) ^ (F.top - j) * a i) + g) := hsm
    have e3 : siteAtSameOffset Y Y' x = siteAtOffset Y' j ((fun i => (F.blockSide : ℤ) ^ (F.top - j) * a i) + g) := by
      rw [e', siteAtSameOffset_siteAtOffset T.ambient T.odd_blockSide.pos Y Y' hsm]
    rw [e3, siteAtSameOffset_siteAtOffset T.ambient' T.odd_blockSide.pos Y' Y hsm', ← e']
theorem siteAtSameOffset_add_unitStep (T : NeighbourhoodsAgree S S' Y Y') {j : ℕ} (hj : j ≤ F.top) {x : F.Site j}
    (hx : x ∈ sitesOfCells (cellBall S Y 4) j) (i : Fin 4) :
    siteAtSameOffset Y Y' (x + unitStep j i) = siteAtSameOffset Y Y' x + unitStep j i := by
  obtain ⟨a, g, ha, -, hg, -, e', hsm⟩ := exists_offset_of_mem T hj hx
  set p : LatticeFractionalIntegration.Lattice4 := (fun i => (F.blockSide : ℤ) ^ (F.top - j) * a i) + g with hp
  have hs : IsSmallOffset F j (p + LatticeFractionalIntegration.basisVector i) := fun μ => by
    set K : ℤ := (F.blockSide : ℤ) ^ (F.top - j) with hK
    have hK1 : 1 ≤ K := one_le_pow₀ (by exact_mod_cast T.odd_blockSide.pos)
    have hgc := (LatticePaths.mem_centredCube_iff _ _).1 hg μ
    have hcast : (((F.blockSide ^ (F.top - j) : ℕ) : ℤ)) = K := by
      rw [hK]
      push_cast
      rfl
    rw [hcast] at hgc
    have hgb : |g μ| ≤ K := by
      rw [abs_le]
      constructor <;> omega
    have h1 := ha μ
    have h3 : |LatticeFractionalIntegration.basisVector i μ| ≤ 1 := by
      by_cases hμ : μ = i
      · subst hμ
        simp [LatticeFractionalIntegration.basisVector]
      · simp [LatticeFractionalIntegration.basisVector, hμ]
    have h4 : |p μ| ≤ 5 * K := by
      simp only [hp, Pi.add_apply]
      refine (abs_add_le _ _).trans ?_
      rw [abs_mul, abs_of_pos (by omega : (0 : ℤ) < K)]
      nlinarith
    simp only [Pi.add_apply]
    refine (abs_add_le _ _).trans_lt ?_
    omega
  rw [e', siteAtOffset_add_unitStep, siteAtSameOffset_siteAtOffset T.ambient T.odd_blockSide.pos Y Y' hs,
    siteAtSameOffset_siteAtOffset T.ambient T.odd_blockSide.pos Y Y' hsm, siteAtOffset_add_unitStep]
theorem cellAtSameOffset_eq_iff (T : NeighbourhoodsAgree S S' Y Y') {z : F.Cell} (hz : z ∈ cellBall S Y 4) :
    cellAtSameOffset Y Y' z = Y' ↔ z = Y := by
  classical
  obtain ⟨-, hd⟩ := Finset.mem_filter.1 hz
  set a : LatticeFractionalIntegration.Lattice4 := fun i => ((z - Y) i).valMinAbs with ha
  have hza : z = Y + siteOfCoords F.top a := eq_add_siteOfCoords_valMinAbs Y z
  have hab : ∀ i, |a i| ≤ 4 := fun i => by exact_mod_cast abs_valMinAbs_sub_le hd i
  constructor
  · intro h
    have h1 : siteOfCoords (F := sameShapeFrame F sd) (sameShapeFrame F sd).top a = (0 : (sameShapeFrame F sd).Cell) := by
      have : Y' + siteOfCoords (F := sameShapeFrame F sd) (sameShapeFrame F sd).top a = Y' + 0 := by
        rw [add_zero]
        exact h
      exact add_left_cancel this
    have h2 : a = 0 := by
      funext i
      have h3 := congrFun h1 i
      have h4 := congrArg ZMod.valMinAbs h3
      simp only [siteOfCoords] at h4
      rw [valMinAbs_intCast_eq (G := sameShapeFrame F sd) T.extent_large' i (hab i)] at h4
      simpa using h4
    rw [hza, h2, siteOfCoords_zero, add_zero]
  · rintro rfl
    unfold cellAtSameOffset
    have : (fun i => ((z - z) i).valMinAbs) = (0 : LatticeFractionalIntegration.Lattice4) := by
      funext i
      simp
    rw [this, siteOfCoords_zero, add_zero]
theorem cellSupDist_cellAtSameOffset_le (T : NeighbourhoodsAgree S S' Y Y') {z : F.Cell} {ρ : ℕ} (hρ : ρ ≤ 4)
    (hz : cellSupDist Y z ≤ ρ) : cellSupDist Y' (cellAtSameOffset Y Y' z) ≤ ρ := by
  have h1 := cellSupDist_add_le T.ambient' (cellAtSameOffset Y Y' z) (a := - fun i => ((z - Y) i).valMinAbs) (r := ρ)
    (by omega) (fun i => by simpa using abs_valMinAbs_sub_le hz i)
  unfold cellAtSameOffset at h1 ⊢
  rw [siteOfCoords_neg, add_neg_cancel_right] at h1
  exact h1
theorem cellAtSameOffset_mem_cellBall (T : NeighbourhoodsAgree S S' Y Y') {z : F.Cell} {ρ : ℕ} (hρ : ρ ≤ 4)
    (hz : z ∈ cellBall S Y ρ) : cellAtSameOffset Y Y' z ∈ cellBall S' Y' ρ := by
  classical
  obtain ⟨hzS, hd⟩ := Finset.mem_filter.1 hz
  refine Finset.mem_filter.2 ⟨?_, cellSupDist_cellAtSameOffset_le T hρ hd⟩
  have hza : z = Y + siteOfCoords F.top (fun i => ((z - Y) i).valMinAbs) := eq_add_siteOfCoords_valMinAbs Y z
  refine (T.mem_iff _ fun i => ?_).1 (hza ▸ hzS)
  have := abs_valMinAbs_sub_le hd i
  have h2 : (ρ : ℤ) ≤ 4 := by exact_mod_cast hρ
  exact this.trans h2
theorem siteAtSameOffset_mem_sitesOfCells (T : NeighbourhoodsAgree S S' Y Y') {j : ℕ} (hj : j ≤ F.top) {ρ : ℕ}
    (hρ : ρ ≤ 4) {x : F.Site j} (hx : x ∈ sitesOfCells (cellBall S Y ρ) j) :
    siteAtSameOffset Y Y' x ∈ sitesOfCells (cellBall S' Y' ρ) j := by
  classical
  have h3 : x ∈ sitesOfCells (cellBall S Y 4) j := BlockLines.sitesOfCells_mono (BlockLines.cellBall_mono S Y hρ) j hx
  obtain ⟨m1, m2, -⟩ := siteAtSameOffset_mem T hj h3
  have hc := BlockLines.enclosingCell_mem T.odd_blockSide hx
  have hoddG : Odd (sameShapeFrame F sd).blockSide := T.odd_blockSide
  refine BlockLines.mem_sitesOfCells_of_enclosingCell_mem hoddG
    (BlockLines.sitesOfCells_mono (BlockLines.cellBall_subset S' Y' 4) j m1) ?_
  rw [m2]
  exact cellAtSameOffset_mem_cellBall T hρ hc
theorem bondWeight_siteAtSameOffset (T : NeighbourhoodsAgree S S' Y Y') {k : ℕ} (hk : k ≤ F.top) {c : F.Site k × Fin 4}
    (hc : c ∈ innerBonds (cellBall S Y 4) k) :
    bondWeight Y' ((siteAtSameOffset Y Y' c.1, c.2) : (sameShapeFrame F sd).Site k × Fin 4) = bondWeight Y c := by
  classical
  obtain ⟨h1, h2⟩ := ChartCoordinates.innerBonds_ends hc
  obtain ⟨-, m1, -⟩ := siteAtSameOffset_mem T hk h1
  obtain ⟨-, m2, -⟩ := siteAtSameOffset_mem T hk h2
  rw [siteAtSameOffset_add_unitStep T hk h1] at m2
  unfold bondWeight
  simp only
  rw [m1, m2]
  have e1 := cellAtSameOffset_eq_iff T (BlockLines.enclosingCell_mem T.odd_blockSide h1)
  have e2 := cellAtSameOffset_eq_iff T (BlockLines.enclosingCell_mem T.odd_blockSide h2)
  simp only [e1, e2]
theorem bond_siteAtSameOffset (T : NeighbourhoodsAgree S S' Y Y') {k : ℕ} (hk : k ≤ F.top) {c : F.Site k × Fin 4}
    (hc : c ∈ innerBonds S k) (hn : bondWeight Y c ≠ 0) :
    ((siteAtSameOffset Y Y' c.1, c.2) : (sameShapeFrame F sd).Site k × Fin 4) ∈ innerBonds S' k ∧
      bondWeight Y' ((siteAtSameOffset Y Y' c.1, c.2) : (sameShapeFrame F sd).Site k × Fin 4) = bondWeight Y c ∧
      siteAtSameOffset Y' Y (siteAtSameOffset Y Y' c.1) = c.1 := by
  classical
  have hbox := mem_innerBonds_cellBall_of_bondWeight_ne_zero T.ambient T.odd_blockSide hk hc hn
  have hb3 : c ∈ innerBonds (cellBall S Y 4) k := BlockLines.innerBonds_mono (BlockLines.cellBall_mono S Y (by norm_num)) k hbox
  obtain ⟨h1, h2⟩ := ChartCoordinates.innerBonds_ends hbox
  have m1 := siteAtSameOffset_mem_sitesOfCells T hk (by norm_num : 1 ≤ 4) h1
  have m2 := siteAtSameOffset_mem_sitesOfCells T hk (by norm_num : 1 ≤ 4) h2
  rw [siteAtSameOffset_add_unitStep T hk (ChartCoordinates.innerBonds_ends hb3).1] at m2
  refine ⟨ChartCoordinates.mem_innerBonds (BlockLines.sitesOfCells_mono (BlockLines.cellBall_subset S' Y' 1) k m1)
    (BlockLines.sitesOfCells_mono (BlockLines.cellBall_subset S' Y' 1) k m2), bondWeight_siteAtSameOffset T hk hb3,
    (siteAtSameOffset_mem T hk (ChartCoordinates.innerBonds_ends hb3).1).2.2⟩
theorem plaquetteCorners_subset (T : NeighbourhoodsAgree S S' Y Y') {p : F.Site 0 × Fin 4 × Fin 4}
    (hp : p ∈ innerPlaquettes S 0) (hn : plaquetteWeight Y p ≠ 0) :
    plaquetteCorners p ⊆ sitesOfCells (cellBall S Y 1) 0 := by
  classical
  obtain ⟨-, hlt, hsub⟩ := Finset.mem_filter.1 hp
  obtain ⟨x₀, hx₀, hxY⟩ : ∃ x ∈ plaquetteCorners p, enclosingCell x = Y := by
    by_contra hcon
    push Not at hcon
    apply hn
    unfold plaquetteWeight
    exact Finset.sum_eq_zero fun x hx => if_neg (hcon x hx)
  set μ := p.2.1 with hμ
  set ν := p.2.2 with hν
  have hne : μ ≠ ν := ne_of_lt hlt
  have hform : ∀ x ∈ plaquetteCorners p, ∃ α β : ℤ, (α = 0 ∨ α = 1) ∧ (β = 0 ∨ β = 1) ∧
      x = p.1 + siteOfCoords 0 (α • LatticeFractionalIntegration.basisVector μ +
        β • LatticeFractionalIntegration.basisVector ν) := by
    intro x hx
    simp only [plaquetteCorners, Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · exact ⟨0, 0, Or.inl rfl, Or.inl rfl, by simp [siteOfCoords_zero]⟩
    · exact ⟨1, 0, Or.inr rfl, Or.inl rfl, by simp [unitStep_eq]; rfl⟩
    · exact ⟨0, 1, Or.inl rfl, Or.inr rfl, by simp [unitStep_eq]; rfl⟩
    · exact ⟨1, 1, Or.inr rfl, Or.inr rfl, by simp [unitStep_eq, _root_.YangMills.Construction.BlockAverages.siteOfCoords_add, add_assoc]; rfl⟩
  have hx₀S := hsub hx₀
  obtain ⟨y, hy, h, hh, e⟩ := mem_sitesOfCells.1 hx₀S
  have hyY : y = Y := by
    rw [← hxY, e]
    exact (BlockLines.enclosingCell_cellCentre_add T.odd_blockSide y h hh).symm
  subst hyY
  obtain ⟨α₀, β₀, ha₀, hb₀, e₀⟩ := hform x₀ hx₀
  intro x hx
  obtain ⟨α, β, ha, hb, e₁⟩ := hform x hx
  have hxS := hsub hx
  set g : LatticeFractionalIntegration.Lattice4 := (α - α₀) • LatticeFractionalIntegration.basisVector μ +
    (β - β₀) • LatticeFractionalIntegration.basisVector ν with hg
  have hgb : ∀ i, |g i| ≤ 1 := by
    intro i
    simp only [hg, Pi.add_apply, Pi.smul_apply, smul_eq_mul, LatticeFractionalIntegration.basisVector]
    by_cases h1 : i = μ
    · subst h1
      have : Pi.single (M := fun _ => ℤ) ν (1 : ℤ) μ = 0 := Pi.single_eq_of_ne hne _
      rw [this, Pi.single_eq_same]
      rcases ha with rfl | rfl <;> rcases ha₀ with rfl | rfl <;> simp
    · by_cases h2 : i = ν
      · subst h2
        rw [Pi.single_eq_of_ne h1, Pi.single_eq_same]
        rcases hb with rfl | rfl <;> rcases hb₀ with rfl | rfl <;> simp
      · rw [Pi.single_eq_of_ne h1, Pi.single_eq_of_ne h2]
        simp
  have hxe : x = cellCentre 0 y + siteOfCoords 0 h + siteOfCoords 0 g := by
    rw [← e, e₁, e₀, add_assoc, ← _root_.YangMills.Construction.BlockAverages.siteOfCoords_add]
    congr 2
    rw [hg]
    funext i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have hcell := PlaquettesNearCell.enclosingCell_shift_mem_cellBall T.ambient T.odd_blockSide (S := S) (z := y) (j := 0)
    (Nat.zero_le _) hh hgb (hxe ▸ hxS)
  rw [← hxe] at hcell
  exact BlockLines.mem_sitesOfCells_of_enclosingCell_mem T.odd_blockSide hxS hcell
theorem plaquette_siteAtSameOffset (T : NeighbourhoodsAgree S S' Y Y') {p : F.Site 0 × Fin 4 × Fin 4}
    (hp : p ∈ innerPlaquettes S 0) (hn : plaquetteWeight Y p ≠ 0) :
    ((siteAtSameOffset Y Y' p.1, p.2) : (sameShapeFrame F sd).Site 0 × Fin 4 × Fin 4) ∈ innerPlaquettes S' 0 ∧
      plaquetteWeight Y' ((siteAtSameOffset Y Y' p.1, p.2) : (sameShapeFrame F sd).Site 0 × Fin 4 × Fin 4) =
        plaquetteWeight Y p ∧
      siteAtSameOffset Y' Y (siteAtSameOffset Y Y' p.1) = p.1 := by
  classical
  have hcs := plaquetteCorners_subset T hp hn
  have h3 : ∀ x ∈ plaquetteCorners p, x ∈ sitesOfCells (cellBall S Y 4) 0 := fun x hx =>
    BlockLines.sitesOfCells_mono (BlockLines.cellBall_mono S Y (by norm_num)) 0 (hcs hx)
  have hz : (0 : ℕ) ≤ F.top := Nat.zero_le _
  have c0 := h3 p.1 (by simp [plaquetteCorners])
  have c1 := h3 (p.1 + unitStep 0 p.2.1) (by simp [plaquetteCorners])
  have s1 := siteAtSameOffset_add_unitStep T hz c0 p.2.1
  have s2 := siteAtSameOffset_add_unitStep T hz c0 p.2.2
  have s3 := siteAtSameOffset_add_unitStep T hz c1 p.2.2
  have ecorn : plaquetteCorners ((siteAtSameOffset Y Y' p.1, p.2) : (sameShapeFrame F sd).Site 0 × Fin 4 × Fin 4) =
      (plaquetteCorners p).image (siteAtSameOffset Y Y') := by
    simp only [plaquetteCorners, Finset.image_insert, Finset.image_singleton, s3, s1, s2]
  have hinj : Set.InjOn (siteAtSameOffset Y Y' : F.Site 0 → (sameShapeFrame F sd).Site 0)
      (plaquetteCorners p : Finset _) := by
    intro x hx x' hx' e
    have e1 := (siteAtSameOffset_mem T hz (h3 x hx)).2.2
    have e2 := (siteAtSameOffset_mem T hz (h3 x' hx')).2.2
    rw [← e1, ← e2, e]
  refine ⟨?_, ?_, (siteAtSameOffset_mem T hz c0).2.2⟩
  · obtain ⟨-, hlt, -⟩ := Finset.mem_filter.1 hp
    have hsub : plaquetteCorners ((siteAtSameOffset Y Y' p.1, p.2) : (sameShapeFrame F sd).Site 0 × Fin 4 × Fin 4) ⊆
        sitesOfCells S' 0 := by
      rw [ecorn]
      intro x' hx'
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hx'
      exact BlockLines.sitesOfCells_mono (BlockLines.cellBall_subset S' Y' 4) 0 (siteAtSameOffset_mem T hz (h3 x hx)).1
    refine Finset.mem_filter.2 ⟨?_, hlt, hsub⟩
    exact Finset.mem_product.2 ⟨hsub (by simp [plaquetteCorners]), by simp⟩
  · unfold plaquetteWeight
    rw [ecorn, Finset.sum_image hinj]
    refine Finset.sum_congr rfl fun x hx => ?_
    obtain ⟨-, m, -⟩ := siteAtSameOffset_mem T hz (h3 x hx)
    have e1 := cellAtSameOffset_eq_iff T (BlockLines.enclosingCell_mem T.odd_blockSide (h3 x hx))
    simp only [m, e1]
section Values
theorem isNearCells_cellBall (S : Finset F.Cell) (Y : F.Cell) : IsNearCells Y (cellBall S Y 1) := by
  classical
  intro y hy
  obtain ⟨-, hd⟩ := Finset.mem_filter.1 hy
  exact ⟨_, fun i => by exact_mod_cast abs_valMinAbs_sub_le hd i, eq_add_siteOfCoords_valMinAbs Y y⟩
theorem exists_regionOffset (T : NeighbourhoodsAgree S S' Y Y') {j : ℕ} (hj : j ≤ F.top) {x : F.Site j}
    (hx : x ∈ sitesOfCells (cellBall S Y 1) j) :
    ∃ q : LatticeFractionalIntegration.Lattice4, x = siteAtOffset Y j q ∧ IsRegionOffset Y (cellBall S Y 1) j q ∧
      siteAtSameOffset Y Y' x = siteAtOffset Y' j q := by
  obtain ⟨a, g, -, -, -, e, hreg⟩ := exists_regionOffset_of_mem T.ambient T.odd_blockSide hj (isNearCells_cellBall S Y) hx
  refine ⟨_, e, hreg, ?_⟩
  rw [e]
  exact siteAtSameOffset_siteAtOffset T.ambient T.odd_blockSide.pos Y Y' hreg.2
theorem isSmallOffset_add (T : NeighbourhoodsAgree S S' Y Y') {j : ℕ} (hj : j ≤ F.top)
    {q : LatticeFractionalIntegration.Lattice4} (hq : IsRegionOffset Y (cellBall S Y 1) j q)
    {w : LatticeFractionalIntegration.Lattice4} (hw : ∀ i, |w i| ≤ 4) : IsSmallOffset F j (q + w) := fun i => by
  have h1 := abs_offset_le_of_region T.ambient T.odd_blockSide hj (isNearCells_cellBall S Y) hq i
  have hK : (1 : ℤ) ≤ (F.blockSide : ℤ) ^ (F.top - j) := one_le_pow₀ (by exact_mod_cast T.odd_blockSide.pos)
  have h2 := hw i
  simp only [Pi.add_apply]
  refine (abs_add_le _ _).trans_lt ?_
  omega
theorem abs_stepDisplacement_le (st : PathStep) (i : Fin 4) : |FlatPairing.stepDisplacement st i| ≤ 1 := by apply _root_.YangMills.Construction.BondShares.abs_stepOffset_le <;> assumption
variable {X : F.GaugeField 0} {X' : (sameShapeFrame F sd).GaugeField 0}
theorem plaquetteHolonomy_eq (T : NeighbourhoodsAgree S S' Y Y') (hX : AgreeOnRegion Y Y' (cellBall S Y 1) 0 X X')
    {p : F.Site 0 × Fin 4 × Fin 4} (hc : plaquetteCorners p ⊆ sitesOfCells (cellBall S Y 1) 0) :
    plaquetteHolonomy X p =
      plaquetteHolonomy X' ((siteAtSameOffset Y Y' p.1, p.2) : (sameShapeFrame F sd).Site 0 × Fin 4 × Fin 4) := by
  have hz : (0 : ℕ) ≤ F.top := Nat.zero_le _
  obtain ⟨q, e, hq, e'⟩ := exists_regionOffset T (Y' := Y') hz (hc (by simp [plaquetteCorners] : p.1 ∈ plaquetteCorners p))
  unfold plaquetteHolonomy
  simp only
  rw [e']
  nth_rewrite 1 [e]
  refine pathHolonomy_eq_of_agree (P := IsRegionOffset Y (cellBall S Y 1) 0) (fun r i h1 h2 => hX r i h1 h2) _ q ?_
  have hw1 : ∀ st : PathStep, ∀ i, |FlatPairing.stepDisplacement st i| ≤ 4 :=
    fun st i => (abs_stepDisplacement_le st i).trans (by norm_num)
  have hw2 : ∀ st st' : PathStep, ∀ i,
      |(FlatPairing.stepDisplacement st + FlatPairing.stepDisplacement st') i| ≤ 4 := fun st st' i => by
    have h1 := abs_stepDisplacement_le st i
    have h2 := abs_stepDisplacement_le st' i
    simp only [Pi.add_apply]
    refine (abs_add_le _ _).trans ?_
    omega
  have hw3 : ∀ st st' st'' : PathStep, ∀ i, |(FlatPairing.stepDisplacement st + FlatPairing.stepDisplacement st' +
      FlatPairing.stepDisplacement st'') i| ≤ 4 := fun st st' st'' i => by
    have h1 := abs_stepDisplacement_le st i
    have h2 := abs_stepDisplacement_le st' i
    have h3 := abs_stepDisplacement_le st'' i
    simp only [Pi.add_apply]
    refine (abs_add_le _ _).trans ((add_le_add (abs_add_le _ _) le_rfl).trans ?_)
    omega
  have hw4 : ∀ st st' st'' st''' : PathStep, ∀ i, |(FlatPairing.stepDisplacement st + FlatPairing.stepDisplacement st' +
      FlatPairing.stepDisplacement st'' + FlatPairing.stepDisplacement st''') i| ≤ 4 :=
    fun st st' st'' st''' i => by
    have h1 := abs_stepDisplacement_le st i
    have h2 := abs_stepDisplacement_le st' i
    have h3 := abs_stepDisplacement_le st'' i
    have h4 := abs_stepDisplacement_le st''' i
    simp only [Pi.add_apply]
    refine (abs_add_le _ _).trans
      ((add_le_add ((abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)) le_rfl).trans ?_)
    omega
  have d1 : siteAtOffset Y 0 (q + FlatPairing.stepDisplacement (p.2.1, true)) = p.1 + unitStep 0 p.2.1 := by
    rw [← siteAtOffset_add_stepDisplacement, ← e]
    rfl
  have d2 : siteAtOffset Y 0 (q + FlatPairing.stepDisplacement (p.2.1, true) + FlatPairing.stepDisplacement (p.2.2, true)) =
      p.1 + unitStep 0 p.2.1 + unitStep 0 p.2.2 := by
    rw [← siteAtOffset_add_stepDisplacement, d1]
    rfl
  have d3 : siteAtOffset Y 0 (q + FlatPairing.stepDisplacement (p.2.1, true) + FlatPairing.stepDisplacement (p.2.2, true) +
      FlatPairing.stepDisplacement (p.2.1, false)) = p.1 + unitStep 0 p.2.2 := by
    rw [← siteAtOffset_add_stepDisplacement, d2]
    simp only [BlockAverages.stepDisplacement, Bool.false_eq_true, if_false]
    abel
  have d4 : siteAtOffset Y 0 (q + FlatPairing.stepDisplacement (p.2.1, true) + FlatPairing.stepDisplacement (p.2.2, true) +
      FlatPairing.stepDisplacement (p.2.1, false) + FlatPairing.stepDisplacement (p.2.2, false)) = p.1 := by
    rw [← siteAtOffset_add_stepDisplacement, d3]
    simp only [BlockAverages.stepDisplacement, Bool.false_eq_true, if_false]
    abel
  refine ⟨hq, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · rw [d1]
    exact hc (by simp [plaquetteCorners])
  · exact isSmallOffset_add T hz hq (hw1 _)
  · rw [d2]
    exact hc (by simp [plaquetteCorners])
  · rw [add_assoc]
    exact isSmallOffset_add T hz hq (hw2 _ _)
  · rw [d3]
    exact hc (by simp [plaquetteCorners])
  · rw [add_assoc, add_assoc, ← add_assoc (FlatPairing.stepDisplacement _)]
    exact isSmallOffset_add T hz hq (hw3 _ _ _)
  · rw [d4]
    exact hc (by simp [plaquetteCorners])
  · rw [add_assoc, add_assoc, add_assoc, ← add_assoc (FlatPairing.stepDisplacement _) (FlatPairing.stepDisplacement _)
      (FlatPairing.stepDisplacement _ + FlatPairing.stepDisplacement _),
      ← add_assoc _ (FlatPairing.stepDisplacement _) (FlatPairing.stepDisplacement _)]
    exact isSmallOffset_add T hz hq (hw4 _ _ _ _)
end Values
section Terms
variable {R : F.FieldChain} {R' : (sameShapeFrame F sd).FieldChain}
theorem gaugedBlockFit_eq (T : NeighbourhoodsAgree S S' Y Y') {j : ℕ} (hj : j + 1 ≤ F.top) {X : F.GaugeField j}
    {X' : (sameShapeFrame F sd).GaugeField j} (hX : AgreeOnRegion Y Y' (cellBall S Y 1) j X X')
    {k : F.Site (j + 1) → UnitQuaternion} {k' : (sameShapeFrame F sd).Site (j + 1) → UnitQuaternion}
    {Xn : F.GaugeField (j + 1)} {Xn' : (sameShapeFrame F sd).GaugeField (j + 1)} {c : F.Site (j + 1) × Fin 4}
    (hc : c ∈ innerBonds (cellBall S Y 1) (j + 1)) (hk : k c.1 = k' (siteAtSameOffset Y Y' c.1))
    (hk2 : k (c.1 + unitStep (j + 1) c.2) = k' (siteAtSameOffset Y Y' c.1 + unitStep (j + 1) c.2))
    (hn : Xn c.1 c.2 = Xn' (siteAtSameOffset Y Y' c.1) c.2) :
    gaugedBlockFit X k Xn c =
      gaugedBlockFit X' k' Xn' ((siteAtSameOffset Y Y' c.1, c.2) : (sameShapeFrame F sd).Site (j + 1) × Fin 4) := by
  obtain ⟨x, i⟩ := c
  obtain ⟨h1, h2⟩ := ChartCoordinates.innerBonds_ends hc
  simp only at h1 h2 hk hk2 hn ⊢
  obtain ⟨q, e, hq, e'⟩ := exists_regionOffset T (Y' := Y') hj h1
  have hq' : IsRegionOffset Y (cellBall S Y 1) (j + 1) (q + LatticeFractionalIntegration.basisVector i) := by
    refine ⟨?_, isSmallOffset_add T hj hq fun μ => ?_⟩
    · rw [← siteAtOffset_add_unitStep, ← e]
      exact h2
    · have h3 : |LatticeFractionalIntegration.basisVector i μ| ≤ 1 := by
        by_cases hμ : μ = i
        · subst hμ
          simp [LatticeFractionalIntegration.basisVector]
        · simp [LatticeFractionalIntegration.basisVector, hμ]
      exact h3.trans (by norm_num)
  have hm := contourAverage_eq_of_agree (Y := Y) (Y' := Y') T.ambient T.odd_blockSide (F' := sameShapeFrame F sd) rfl hj hj
    (isNearCells_cellBall S Y) hX hq hq'
  rw [← e, ← e'] at hm
  have hfm : gaugedContourAverage X k (x, i) = gaugedContourAverage X' k' (siteAtSameOffset Y Y' x, i) := by
    unfold gaugedContourAverage
    simp only
    rw [hm, hk, hk2]
  unfold gaugedBlockFit
  simp only
  rw [hfm, hn]
variable (hR : ∀ j, j < F.top → AgreeOnRegion Y Y' (cellBall S Y 1) j (R j) (R' j))
include hR
theorem chartGauge_eq (T : NeighbourhoodsAgree S S' Y Y') (U' : ChainChart (sameShapeFrame F sd)) {j : ℕ}
    (hj : j < F.top) {x : F.Site (j + 1)} (hx : x ∈ sitesOfCells (cellBall S Y 1) (j + 1)) :
    chartGauge R (chartAtSameOffsets Y Y' U') (j + 1) x = chartGauge R' U' (j + 1) (siteAtSameOffset Y Y' x) := by
  obtain ⟨q, e, hq, e'⟩ := exists_regionOffset T (Y' := Y') (by omega : j + 1 ≤ F.top) hx
  rw [e', e]
  exact chartGauge_eq_of_agree (F' := sameShapeFrame F sd) T.ambient T.odd_blockSide rfl rfl (isNearCells_cellBall S Y)
    R R' U' hR hj hq
set_option maxHeartbeats 2000000 in
theorem lowerEvaluation_eq (T : NeighbourhoodsAgree S S' Y Y') (a : ℝ) (U' : ChainChart (sameShapeFrame F sd)) :
    lowerEvaluation a S R Y (chartAtSameOffsets Y Y' U') = lowerEvaluation a S' R' Y' U' := by
  classical
  have hF := chartField_agree (F' := sameShapeFrame F sd) T.ambient T.odd_blockSide rfl rfl (isNearCells_cellBall S Y)
    R R' U' hR
  have h0 : 0 < F.top := Nat.succ_pos _
  have hpl : ∑ p ∈ innerPlaquettes S 0, plaquetteWeight Y p *
      (1 - ((plaquetteHolonomy (chartField R (chartAtSameOffsets Y Y' U') 0) p : UnitQuaternion) : ℍ[ℝ]).re) =
      ∑ p ∈ innerPlaquettes S' 0, plaquetteWeight Y' p *
        (1 - ((plaquetteHolonomy (chartField R' U' 0) p : UnitQuaternion) : ℍ[ℝ]).re) := by
    rw [← Finset.sum_filter_of_ne (s := innerPlaquettes S 0) (p := fun p => plaquetteWeight Y p ≠ 0)
        (fun p _ hn h0 => hn (by rw [h0, zero_mul])),
      ← Finset.sum_filter_of_ne (s := innerPlaquettes S' 0) (p := fun p => plaquetteWeight Y' p ≠ 0)
        (fun p _ hn h0 => hn (by rw [h0, zero_mul]))]
    refine Finset.sum_nbij' (fun p => ((siteAtSameOffset Y Y' p.1, p.2) : (sameShapeFrame F sd).Site 0 × Fin 4 × Fin 4))
      (fun p => ((siteAtSameOffset Y' Y p.1, p.2) : F.Site 0 × Fin 4 × Fin 4)) ?_ ?_ ?_ ?_ ?_
    · intro p hp
      obtain ⟨hpS, hn⟩ := Finset.mem_filter.1 hp
      obtain ⟨m1, m2, -⟩ := plaquette_siteAtSameOffset T hpS hn
      exact Finset.mem_filter.2 ⟨m1, by rw [m2]; exact hn⟩
    · intro p hp
      obtain ⟨hpS, hn⟩ := Finset.mem_filter.1 hp
      obtain ⟨m1, m2, -⟩ := plaquette_siteAtSameOffset T.symm hpS hn
      exact Finset.mem_filter.2 ⟨m1, by
        have := m2
        intro h0
        exact hn (this.symm.trans h0)⟩
    · intro p hp
      obtain ⟨hpS, hn⟩ := Finset.mem_filter.1 hp
      obtain ⟨-, -, m3⟩ := plaquette_siteAtSameOffset T hpS hn
      exact Prod.ext m3 rfl
    · intro p hp
      obtain ⟨hpS, hn⟩ := Finset.mem_filter.1 hp
      obtain ⟨-, -, m3⟩ := plaquette_siteAtSameOffset T.symm hpS hn
      exact Prod.ext m3 rfl
    · intro p hp
      obtain ⟨hpS, hn⟩ := Finset.mem_filter.1 hp
      obtain ⟨-, m2, -⟩ := plaquette_siteAtSameOffset T hpS hn
      rw [m2, plaquetteHolonomy_eq T (hF 0 h0) (plaquetteCorners_subset T hpS hn)]
  have hbd : ∀ j, j + 1 < F.top → ∑ c ∈ innerBonds S (j + 1), bondWeight Y c *
      gaugedBlockFit (chartField R (chartAtSameOffsets Y Y' U') j) (chartGauge R (chartAtSameOffsets Y Y' U') (j + 1))
        (chartField R (chartAtSameOffsets Y Y' U') (j + 1)) c =
      ∑ c ∈ innerBonds S' (j + 1), bondWeight Y' c *
        gaugedBlockFit (chartField R' U' j) (chartGauge R' U' (j + 1)) (chartField R' U' (j + 1)) c := by
    intro j hj
    have hk : j + 1 ≤ F.top := hj.le
    rw [← Finset.sum_filter_of_ne (s := innerBonds S (j + 1)) (p := fun c => bondWeight Y c ≠ 0)
        (fun c _ hn h0 => hn (by rw [h0, zero_mul])),
      ← Finset.sum_filter_of_ne (s := innerBonds S' (j + 1)) (p := fun c => bondWeight Y' c ≠ 0)
        (fun c _ hn h0 => hn (by rw [h0, zero_mul]))]
    refine Finset.sum_nbij' (fun c => ((siteAtSameOffset Y Y' c.1, c.2) : (sameShapeFrame F sd).Site (j + 1) × Fin 4))
      (fun c => ((siteAtSameOffset Y' Y c.1, c.2) : F.Site (j + 1) × Fin 4)) ?_ ?_ ?_ ?_ ?_
    · intro c hc
      obtain ⟨hcS, hn⟩ := Finset.mem_filter.1 hc
      obtain ⟨m1, m2, -⟩ := bond_siteAtSameOffset T hk hcS hn
      exact Finset.mem_filter.2 ⟨m1, by rw [m2]; exact hn⟩
    · intro c hc
      obtain ⟨hcS, hn⟩ := Finset.mem_filter.1 hc
      obtain ⟨m1, m2, -⟩ := bond_siteAtSameOffset T.symm hk hcS hn
      exact Finset.mem_filter.2 ⟨m1, by
        have := m2
        intro h0
        exact hn (this.symm.trans h0)⟩
    · intro c hc
      obtain ⟨hcS, hn⟩ := Finset.mem_filter.1 hc
      obtain ⟨-, -, m3⟩ := bond_siteAtSameOffset T hk hcS hn
      exact Prod.ext m3 rfl
    · intro c hc
      obtain ⟨hcS, hn⟩ := Finset.mem_filter.1 hc
      obtain ⟨-, -, m3⟩ := bond_siteAtSameOffset T.symm hk hcS hn
      exact Prod.ext m3 rfl
    · intro c hc
      obtain ⟨hcS, hn⟩ := Finset.mem_filter.1 hc
      obtain ⟨-, m2, -⟩ := bond_siteAtSameOffset T hk hcS hn
      have hbox := mem_innerBonds_cellBall_of_bondWeight_ne_zero T.ambient T.odd_blockSide hk hcS hn
      obtain ⟨e1, e2⟩ := ChartCoordinates.innerBonds_ends hbox
      have h3 : c.1 ∈ sitesOfCells (cellBall S Y 4) (j + 1) :=
        BlockLines.sitesOfCells_mono (BlockLines.cellBall_mono S Y (by norm_num)) _ e1
      obtain ⟨q, e, hq, e'⟩ := exists_regionOffset T (Y' := Y') hk e1
      have hlast : chartField R (chartAtSameOffsets Y Y' U') (j + 1) c.1 c.2 =
          chartField R' U' (j + 1) (siteAtSameOffset Y Y' c.1) c.2 := by
        have hq' : IsRegionOffset Y (cellBall S Y 1) (j + 1) (q + LatticeFractionalIntegration.basisVector c.2) := by
          refine ⟨?_, isSmallOffset_add T hk hq fun μ => ?_⟩
          · rw [← siteAtOffset_add_unitStep, ← e]
            exact e2
          · have h4 : |LatticeFractionalIntegration.basisVector c.2 μ| ≤ 1 := by
              by_cases hμ : μ = c.2
              · subst hμ
                simp [LatticeFractionalIntegration.basisVector]
              · simp [LatticeFractionalIntegration.basisVector, hμ]
            exact h4.trans (by norm_num)
        have := hF (j + 1) hj q c.2 hq hq'
        rw [← e, ← e'] at this
        exact this
      rw [m2, gaugedBlockFit_eq T hk (hF j (by omega)) hbox (chartGauge_eq hR T U' (by omega) e1) (by
        rw [chartGauge_eq hR T U' (by omega) e2, siteAtSameOffset_add_unitStep T hk h3]) hlast]
  unfold lowerEvaluation
  rw [hpl]
  congr 1
  congr 1
  exact Finset.sum_congr rfl fun j hj => hbd j (by
    have := Finset.mem_range.1 hj
    simp only [BlockFrame.top] at this ⊢
    omega)
set_option maxHeartbeats 2000000 in
theorem topRestriction_eq (T : NeighbourhoodsAgree S S' Y Y') (a : ℝ) (V : F.GaugeField F.top)
    (V' : (sameShapeFrame F sd).GaugeField (sameShapeFrame F sd).top) (U' : ChainChart (sameShapeFrame F sd))
    (v : F.Site F.top → Fin 4 → imaginaryQuaternions)
    (v' : (sameShapeFrame F sd).Site (sameShapeFrame F sd).top → Fin 4 → imaginaryQuaternions)
    (hT : ∀ b ∈ innerBonds S (F.depth + 1), bondWeight Y b ≠ 0 →
      rotatedField v V b.1 b.2 = rotatedField v' V' (siteAtSameOffset Y Y' b.1) b.2) :
    topRestriction a S R V Y (chartAtSameOffsets Y Y' U') v = topRestriction a S' R' V' Y' U' v' := by
  classical
  have hF := chartField_agree (F' := sameShapeFrame F sd) T.ambient T.odd_blockSide rfl rfl (isNearCells_cellBall S Y)
    R R' U' hR
  have hk : F.depth + 1 ≤ F.top := le_rfl
  have hjt : F.depth < F.top := Nat.lt_succ_self _
  unfold topRestriction
  congr 1
  rw [← Finset.sum_filter_of_ne (s := innerBonds S (F.depth + 1)) (p := fun c => bondWeight Y c ≠ 0)
      (fun c _ hn h0 => hn (by rw [h0, zero_mul])),
    ← Finset.sum_filter_of_ne (s := innerBonds S' (F.depth + 1)) (p := fun c => bondWeight Y' c ≠ 0)
      (fun c _ hn h0 => hn (by rw [h0, zero_mul]))]
  refine Finset.sum_nbij' (fun c => ((siteAtSameOffset Y Y' c.1, c.2) : (sameShapeFrame F sd).Site (F.depth + 1) × Fin 4))
    (fun c => ((siteAtSameOffset Y' Y c.1, c.2) : F.Site (F.depth + 1) × Fin 4)) ?_ ?_ ?_ ?_ ?_
  · intro c hc
    obtain ⟨hcS, hn⟩ := Finset.mem_filter.1 hc
    obtain ⟨m1, m2, -⟩ := bond_siteAtSameOffset T hk hcS hn
    exact Finset.mem_filter.2 ⟨m1, by rw [m2]; exact hn⟩
  · intro c hc
    obtain ⟨hcS, hn⟩ := Finset.mem_filter.1 hc
    obtain ⟨m1, m2, -⟩ := bond_siteAtSameOffset T.symm hk hcS hn
    exact Finset.mem_filter.2 ⟨m1, by
      have := m2
      intro h0
      exact hn (this.symm.trans h0)⟩
  · intro c hc
    obtain ⟨hcS, hn⟩ := Finset.mem_filter.1 hc
    obtain ⟨-, -, m3⟩ := bond_siteAtSameOffset T hk hcS hn
    exact Prod.ext m3 rfl
  · intro c hc
    obtain ⟨hcS, hn⟩ := Finset.mem_filter.1 hc
    obtain ⟨-, -, m3⟩ := bond_siteAtSameOffset T.symm hk hcS hn
    exact Prod.ext m3 rfl
  · intro c hc
    obtain ⟨hcS, hn⟩ := Finset.mem_filter.1 hc
    obtain ⟨-, m2, -⟩ := bond_siteAtSameOffset T hk hcS hn
    have hbox := mem_innerBonds_cellBall_of_bondWeight_ne_zero T.ambient T.odd_blockSide hk hcS hn
    obtain ⟨e1, e2⟩ := ChartCoordinates.innerBonds_ends hbox
    have h3 : c.1 ∈ sitesOfCells (cellBall S Y 4) (F.depth + 1) :=
      BlockLines.sitesOfCells_mono (BlockLines.cellBall_mono S Y (by norm_num)) _ e1
    rw [m2, gaugedBlockFit_eq T hk (hF F.depth hjt) hbox (chartGauge_eq hR T U' hjt e1) (by
      rw [chartGauge_eq hR T U' hjt e2, siteAtSameOffset_add_unitStep T hk h3]) (hT c hcS hn)]
theorem localCellShare_eq (T : NeighbourhoodsAgree S S' Y Y') (a : ℝ) (V : F.GaugeField F.top)
    (V' : (sameShapeFrame F sd).GaugeField (sameShapeFrame F sd).top) (U' : ChainChart (sameShapeFrame F sd))
    (v : F.Site F.top → Fin 4 → imaginaryQuaternions)
    (v' : (sameShapeFrame F sd).Site (sameShapeFrame F sd).top → Fin 4 → imaginaryQuaternions)
    (hT : ∀ b ∈ innerBonds S (F.depth + 1), bondWeight Y b ≠ 0 →
      rotatedField v V b.1 b.2 = rotatedField v' V' (siteAtSameOffset Y Y' b.1) b.2) :
    localCellShare a S R V Y (chartAtSameOffsets Y Y' U') v = localCellShare a S' R' V' Y' U' v' := by
  rw [cellShareInChart_eq_lowerShareInChart_add_topShareInChart, cellShareInChart_eq_lowerShareInChart_add_topShareInChart,
    lowerEvaluation_eq hR T a U', topRestriction_eq hR T a V V' U' v v' hT]
end Terms
section Norms
variable {R : F.FieldChain} {R' : (sameShapeFrame F sd).FieldChain}
theorem mem_innerBonds_of_mem_bondsOver (T : NeighbourhoodsAgree S S' Y Y') {k : ℕ} (hk : k ≤ F.top)
    {b : F.Site k × Fin 4} (hb : b ∈ bondsOver S (cellBall S Y 3) k) : b ∈ innerBonds (cellBall S Y 4) k := by
  classical
  obtain ⟨hbS, hc⟩ := Finset.mem_filter.1 hb
  obtain ⟨h1, h2⟩ := ChartCoordinates.innerBonds_ends hbS
  set z := enclosingCell b.1 with hz
  have hq : b ∈ bondsOver S {z} k := Finset.mem_filter.2 ⟨hbS, Finset.mem_singleton.2 rfl⟩
  have hb1 := BlockLines.mem_innerBonds_cellBall_of_mem_bondsOver T.ambient T.odd_blockSide S z hk hq
  obtain ⟨e1, e2⟩ := ChartCoordinates.innerBonds_ends hb1
  have hmono : ∀ {w : F.Cell}, w ∈ cellBall S z 1 → w ∈ cellBall S Y 4 := fun {w} hw => by
    obtain ⟨hwS, hd⟩ := Finset.mem_filter.1 hw
    obtain ⟨-, hd2⟩ := Finset.mem_filter.1 hc
    refine Finset.mem_filter.2 ⟨hwS, ?_⟩
    have := PatchLocality.cellSupDist_triangle Y z w
    omega
  exact ChartCoordinates.mem_innerBonds
    (BlockLines.mem_sitesOfCells_of_enclosingCell_mem T.odd_blockSide h1 (hmono (BlockLines.enclosingCell_mem T.odd_blockSide e1)))
    (BlockLines.mem_sitesOfCells_of_enclosingCell_mem T.odd_blockSide h2 (hmono (BlockLines.enclosingCell_mem T.odd_blockSide e2)))
theorem bond_mem_bondsOver (T : NeighbourhoodsAgree S S' Y Y') {k : ℕ} (hk : k ≤ F.top) {b : F.Site k × Fin 4}
    (hb : b ∈ bondsOver S (cellBall S Y 3) k) :
    ((siteAtSameOffset Y Y' b.1, b.2) : (sameShapeFrame F sd).Site k × Fin 4) ∈ bondsOver S' (cellBall S' Y' 3) k := by
  classical
  have h4 := mem_innerBonds_of_mem_bondsOver T hk hb
  obtain ⟨h1, h2⟩ := ChartCoordinates.innerBonds_ends h4
  obtain ⟨m1, m2, -⟩ := siteAtSameOffset_mem T hk h1
  obtain ⟨m3, -, -⟩ := siteAtSameOffset_mem T hk h2
  rw [siteAtSameOffset_add_unitStep T hk h1] at m3
  refine Finset.mem_filter.2 ⟨ChartCoordinates.mem_innerBonds
    (BlockLines.sitesOfCells_mono (BlockLines.cellBall_subset S' Y' 4) k m1)
    (BlockLines.sitesOfCells_mono (BlockLines.cellBall_subset S' Y' 4) k m3), ?_⟩
  simp only
  rw [m2]
  exact cellAtSameOffset_mem_cellBall T (by norm_num) (Finset.mem_filter.1 hb).2
theorem sum_comp_le_of_injOn {β γ : Type} [DecidableEq γ] {T₁ : Finset β} {T₂ : Finset γ} (ψ : β → γ) (f : γ → ℝ)
    (hf : ∀ x, 0 ≤ f x) (hinj : Set.InjOn ψ T₁) (hmap : ∀ b ∈ T₁, ψ b ∈ T₂) :
    ∑ b ∈ T₁, f (ψ b) ≤ ∑ b ∈ T₂, f b := by
  rw [← Finset.sum_image (f := f) hinj]
  refine Finset.sum_le_sum_of_subset_of_nonneg (fun x hx => ?_) fun x _ _ => hf x
  obtain ⟨b, hb, rfl⟩ := Finset.mem_image.1 hx
  exact hmap b hb
theorem injOn_bond (T : NeighbourhoodsAgree S S' Y Y') {k : ℕ} (hk : k ≤ F.top) :
    Set.InjOn (fun b : F.Site k × Fin 4 => ((siteAtSameOffset Y Y' b.1, b.2) : (sameShapeFrame F sd).Site k × Fin 4))
      (bondsOver S (cellBall S Y 3) k : Finset _) := by
  intro b hb b' hb' e
  have h1 := (ChartCoordinates.innerBonds_ends (mem_innerBonds_of_mem_bondsOver T hk hb)).1
  have h2 := (ChartCoordinates.innerBonds_ends (mem_innerBonds_of_mem_bondsOver T hk hb')).1
  have e1 := (siteAtSameOffset_mem T hk h1).2.2
  have e2 := (siteAtSameOffset_mem T hk h2).2.2
  have e3 := congrArg Prod.fst e
  have e4 := congrArg Prod.snd e
  simp only at e3 e4
  exact Prod.ext (by rw [← e1, ← e2, e3]) e4
theorem plaquetteCorners_subset_cellBall (T : NeighbourhoodsAgree S S' Y Y') {p : F.Site 0 × Fin 4 × Fin 4}
    (hp : p ∈ plaquettesOver S (cellBall S Y 3) 0) : plaquetteCorners p ⊆ sitesOfCells (cellBall S Y 4) 0 := by
  classical
  obtain ⟨hpS, hc⟩ := Finset.mem_filter.1 hp
  set z := enclosingCell p.1 with hz
  have hq : p ∈ plaquettesOver S {z} 0 := Finset.mem_filter.2 ⟨hpS, Finset.mem_singleton.2 rfl⟩
  obtain ⟨b1, b2, b3, b4⟩ := PlaquettesNearCell.plaquette_bonds_mem_innerBonds T.ambient T.odd_blockSide hq
  obtain ⟨-, -, hsub⟩ := Finset.mem_filter.1 hpS
  have hmono : ∀ {w : F.Cell}, w ∈ cellBall S z 1 → w ∈ cellBall S Y 4 := fun {w} hw => by
    obtain ⟨hwS, hd⟩ := Finset.mem_filter.1 hw
    obtain ⟨-, hd2⟩ := Finset.mem_filter.1 hc
    refine Finset.mem_filter.2 ⟨hwS, ?_⟩
    have := PatchLocality.cellSupDist_triangle Y z w
    omega
  have hend : ∀ {b : F.Site 0 × Fin 4}, b ∈ innerBonds (cellBall S z 1) 0 → b.1 ∈ sitesOfCells (cellBall S z 1) 0 ∧
      b.1 + unitStep 0 b.2 ∈ sitesOfCells (cellBall S z 1) 0 := fun hb => ChartCoordinates.innerBonds_ends hb
  intro x hx
  refine BlockLines.mem_sitesOfCells_of_enclosingCell_mem T.odd_blockSide (hsub hx)
    (hmono (BlockLines.enclosingCell_mem T.odd_blockSide (?_ : x ∈ sitesOfCells (cellBall S z 1) 0)))
  simp only [plaquetteCorners, Finset.mem_insert, Finset.mem_singleton] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact (hend b1).1
  · exact (hend b1).2
  · exact (hend b4).2
  · exact (hend b2).2
theorem plaquette_mem_plaquettesOver (T : NeighbourhoodsAgree S S' Y Y') {p : F.Site 0 × Fin 4 × Fin 4}
    (hp : p ∈ plaquettesOver S (cellBall S Y 3) 0) :
    ((siteAtSameOffset Y Y' p.1, p.2) : (sameShapeFrame F sd).Site 0 × Fin 4 × Fin 4) ∈
      plaquettesOver S' (cellBall S' Y' 3) 0 := by
  classical
  have hcs := plaquetteCorners_subset_cellBall T hp
  have hz : (0 : ℕ) ≤ F.top := Nat.zero_le _
  have c0 := hcs (by simp [plaquetteCorners] : p.1 ∈ plaquetteCorners p)
  have c1 := hcs (by simp [plaquetteCorners] : p.1 + unitStep 0 p.2.1 ∈ plaquetteCorners p)
  have s1 := siteAtSameOffset_add_unitStep T hz c0 p.2.1
  have s2 := siteAtSameOffset_add_unitStep T hz c0 p.2.2
  have s3 := siteAtSameOffset_add_unitStep T hz c1 p.2.2
  obtain ⟨hpS, hc⟩ := Finset.mem_filter.1 hp
  obtain ⟨-, hlt, -⟩ := Finset.mem_filter.1 hpS
  have ecorn : plaquetteCorners ((siteAtSameOffset Y Y' p.1, p.2) : (sameShapeFrame F sd).Site 0 × Fin 4 × Fin 4) =
      (plaquetteCorners p).image (siteAtSameOffset Y Y') := by
    simp only [plaquetteCorners, Finset.image_insert, Finset.image_singleton, s3, s1, s2]
  have hsub : plaquetteCorners ((siteAtSameOffset Y Y' p.1, p.2) : (sameShapeFrame F sd).Site 0 × Fin 4 × Fin 4) ⊆
      sitesOfCells S' 0 := by
    rw [ecorn]
    intro x' hx'
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hx'
    exact BlockLines.sitesOfCells_mono (BlockLines.cellBall_subset S' Y' 4) 0 (siteAtSameOffset_mem T hz (hcs hx)).1
  refine Finset.mem_filter.2 ⟨Finset.mem_filter.2 ⟨Finset.mem_product.2 ⟨hsub (by simp [plaquetteCorners]), by simp⟩,
    hlt, hsub⟩, ?_⟩
  simp only
  rw [(siteAtSameOffset_mem T hz c0).2.1]
  exact cellAtSameOffset_mem_cellBall T (by norm_num) hc
theorem linearizedCurl_eq (T : NeighbourhoodsAgree S S' Y Y') (U' : ChainChart (sameShapeFrame F sd))
    (hR0 : ∀ x i, x ∈ sitesOfCells (cellBall S Y 4) 0 → x + unitStep 0 i ∈ sitesOfCells (cellBall S Y 4) 0 →
      R 0 x i = R' 0 (siteAtSameOffset Y Y' x) i) {p : F.Site 0 × Fin 4 × Fin 4}
    (hp : p ∈ plaquettesOver S (cellBall S Y 3) 0) :
    linearizedCurl (R 0) (chartAtSameOffsets Y Y' U').fine p =
      linearizedCurl (R' 0) U'.fine ((siteAtSameOffset Y Y' p.1, p.2) : (sameShapeFrame F sd).Site 0 × Fin 4 × Fin 4) := by
  have hcs := plaquetteCorners_subset_cellBall T hp
  have hz : (0 : ℕ) ≤ F.top := Nat.zero_le _
  have c0 := hcs (by simp [plaquetteCorners] : p.1 ∈ plaquetteCorners p)
  have c1 := hcs (by simp [plaquetteCorners] : p.1 + unitStep 0 p.2.1 ∈ plaquetteCorners p)
  have c2 := hcs (by simp [plaquetteCorners] : p.1 + unitStep 0 p.2.2 ∈ plaquetteCorners p)
  have c3 := hcs (by simp [plaquetteCorners] : p.1 + unitStep 0 p.2.1 + unitStep 0 p.2.2 ∈ plaquetteCorners p)
  have s1 := siteAtSameOffset_add_unitStep T hz c0 p.2.1
  have s2 := siteAtSameOffset_add_unitStep T hz c0 p.2.2
  have e3 : p.1 + unitStep 0 p.2.2 + unitStep 0 p.2.1 = p.1 + unitStep 0 p.2.1 + unitStep 0 p.2.2 := by abel
  unfold linearizedCurl
  simp only [chartAtSameOffsets]
  rw [hR0 p.1 p.2.1 c0 c1, hR0 (p.1 + unitStep 0 p.2.1) p.2.2 c1 c3,
    hR0 (p.1 + unitStep 0 p.2.2) p.2.1 c2 (by rw [e3]; exact c3), hR0 p.1 p.2.2 c0 c2, s1, s2]
theorem localNorm_chartAtSameOffsets_le (T : NeighbourhoodsAgree S S' Y Y') (U' : ChainChart (sameShapeFrame F sd))
    (hR0 : ∀ x i, x ∈ sitesOfCells (cellBall S Y 4) 0 → x + unitStep 0 i ∈ sitesOfCells (cellBall S Y 4) 0 →
      R 0 x i = R' 0 (siteAtSameOffset Y Y' x) i) :
    localNorm S R (chartAtSameOffsets Y Y' U') (oneSiteWeights F) Y ≤
      localNorm S' R' U' (oneSiteWeights (sameShapeFrame F sd)) Y' := by
  classical
  have hz : (0 : ℕ) ≤ F.top := Nat.zero_le _
  unfold localNorm localNormSq
  refine Real.sqrt_le_sqrt (add_le_add (add_le_add (Real.sqrt_le_sqrt ?_) ?_) ?_)
  · simp only [oneSiteWeights, one_mul]
    exact sum_comp_le_of_injOn
      (fun b : F.Site 0 × Fin 4 => ((siteAtSameOffset Y Y' b.1, b.2) : (sameShapeFrame F sd).Site 0 × Fin 4))
      (fun b => ‖U'.fine b.1 b.2‖ ^ 4) (fun _ => by positivity) (injOn_bond T hz) fun b hb => bond_mem_bondsOver T hz hb
  · simp only [oneSiteWeights, one_mul]
    have e : ∀ p ∈ plaquettesOver S (cellBall S Y 3) 0,
        ‖linearizedCurl (R 0) (chartAtSameOffsets Y Y' U').fine p‖ ^ 2 =
        ‖linearizedCurl (R' 0) U'.fine
          ((siteAtSameOffset Y Y' p.1, p.2) : (sameShapeFrame F sd).Site 0 × Fin 4 × Fin 4)‖ ^ 2 :=
      fun p hp => by rw [linearizedCurl_eq T U' hR0 hp]
    rw [Finset.sum_congr rfl e]
    refine sum_comp_le_of_injOn
      (fun p : F.Site 0 × Fin 4 × Fin 4 =>
        ((siteAtSameOffset Y Y' p.1, p.2) : (sameShapeFrame F sd).Site 0 × Fin 4 × Fin 4))
      (fun p => ‖linearizedCurl (R' 0) U'.fine p‖ ^ 2) (fun _ => by positivity) ?_
      fun p hp => plaquette_mem_plaquettesOver T hp
    intro p hp p' hp' e
    have h1 := plaquetteCorners_subset_cellBall T hp (by simp [plaquetteCorners] : p.1 ∈ plaquetteCorners p)
    have h2 := plaquetteCorners_subset_cellBall T hp' (by simp [plaquetteCorners] : p'.1 ∈ plaquetteCorners p')
    have e1 := (siteAtSameOffset_mem T hz h1).2.2
    have e2 := (siteAtSameOffset_mem T hz h2).2.2
    have e3 := congrArg Prod.fst e
    have e4 := congrArg Prod.snd e
    simp only at e3 e4
    exact Prod.ext (by rw [← e1, ← e2, e3]) e4
  · refine Finset.sum_le_sum fun j hj => ?_
    simp only [oneSiteWeights, one_mul]
    have hjk : j + 1 ≤ F.top := by
      have := Finset.mem_range.1 hj
      simp only [BlockFrame.top] at this ⊢
      omega
    exact sum_comp_le_of_injOn
      (fun b : F.Site (j + 1) × Fin 4 =>
        ((siteAtSameOffset Y Y' b.1, b.2) : (sameShapeFrame F sd).Site (j + 1) × Fin 4))
      (fun b => ‖U'.coarse j b.1 b.2‖ ^ 2) (fun _ => by positivity) (injOn_bond T hjk) fun b hb => bond_mem_bondsOver T hjk hb
end Norms
end YangMills.Construction.BlockAverages.SameOffsetShares
end
