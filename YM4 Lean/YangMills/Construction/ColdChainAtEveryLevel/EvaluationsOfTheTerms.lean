import YangMills.Construction.ColdChainAtEveryLevel.RatesOfTheTerms
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction.BlockAverages.VariationRates
open PatchLocality ChartCoordinates LatticePaths LatticeFractionalIntegration GaugeMap
variable {F : BlockFrame} {S : Finset F.Cell} {j : ℕ}
def SupClose (r : ℤ) (x x' : F.Site 0) : Prop :=
  ∃ δ : Lattice4, (∀ i, |δ i| ≤ r) ∧ x' = x + siteOfCoords 0 δ
def slotStart : VariationSlot F → F.Site 0
  | Sum.inl b => baseSite b.2.1
  | Sum.inr c => baseSite c.2
def slotEnd : VariationSlot F → F.Site 0
  | Sum.inl b => baseSite (b.2.1 + unitStep b.1 b.2.2)
  | Sum.inr c => baseSite c.2
def actionTermLevel : F.ActionTerm → ℕ
  | Sum.inl _ => 0
  | Sum.inr c => c.1
theorem baseSite_of_level_zero (x : F.Site 0) : baseSite x = x := by apply _root_.YangMills.Construction.CellBumps.baseSite_zero <;> assumption
theorem SupClose.mono {r r' : ℤ} (h : r ≤ r') {x x' : F.Site 0} (hw : SupClose r x x') :
    SupClose r' x x' := by
  obtain ⟨δ, hδ, e⟩ := hw
  exact ⟨δ, fun i => (hδ i).trans h, e⟩
theorem SupClose.refl {r : ℤ} (hr : 0 ≤ r) (x : F.Site 0) : SupClose r x x :=
  ⟨0, fun i => by simpa using hr, by rw [siteOfCoords_zero, add_zero]⟩
theorem SupClose.symm {r : ℤ} {x x' : F.Site 0} (hw : SupClose r x x') : SupClose r x' x := by
  obtain ⟨δ, hδ, e⟩ := hw
  refine ⟨-δ, fun i => by simpa using hδ i, ?_⟩
  rw [e, siteOfCoords_neg, add_neg_cancel_right]
theorem exists_offset_of_liesOnPath {p : Lattice4 → Prop} (x0 : F.Site j) {l : List PathStep}
    {u : Lattice4} (h : AllAlong p u l)
    {b : F.Site j × Fin 4} (hb : LiesOnPath b (x0 + siteOfCoords j u) l) :
    ∃ v, p v ∧ p (v + basisVector b.2) ∧ b.1 = x0 + siteOfCoords j v := by
  induction l generalizing u with
  | nil => exact hb.elim
  | cons st r ih =>
    have hnext : x0 + siteOfCoords j u + BlockAverages.stepDisplacement j st =
        x0 + siteOfCoords j (u + FlatPairing.stepDisplacement st) := by
      rw [stepDisplacement_eq_siteOfCoords, add_assoc, ← siteOfCoords_add]
    rcases hb with hb | hb
    · rcases st with ⟨i, s⟩
      cases s
      · simp only [Bool.false_eq_true, if_false] at hb
        subst hb
        refine ⟨u + FlatPairing.stepDisplacement (i, false), allAlong_head h.2, ?_, ?_⟩
        · have e : u + FlatPairing.stepDisplacement (i, false) + basisVector i = u := by
            simp [FlatPairing.stepDisplacement]
          simpa [e] using h.1
        · simp [FlatPairing.stepDisplacement, unitStep_eq, siteOfCoords_add, siteOfCoords_neg,
            sub_eq_add_neg, add_assoc]
      · simp only [if_true] at hb
        subst hb
        refine ⟨u, h.1, ?_, rfl⟩
        have e : FlatPairing.stepDisplacement (i, true) = basisVector i := by
          simp [FlatPairing.stepDisplacement]
        have := allAlong_head h.2
        rwa [e] at this
    · rw [hnext] at hb
      exact ih h.2 hb
theorem baseSite_eq_cellCentre_add (hodd : Odd F.blockSide) {x : F.Site j} (hj : j ≤ F.top)
    (hx : x ∈ sitesOfCells S j) :
    enclosingCell x ∈ S ∧ ∃ h ∈ centredCube (F.blockSide ^ F.top),
      baseSite x = cellCentre 0 (enclosingCell x) + siteOfCoords 0 h := by
  classical
  obtain ⟨y, hy, h, hh, e⟩ := mem_sitesOfCells.1 hx
  have hc : enclosingCell x = y := by
    rw [e]; exact LocalPartition.enclosingCell_cellCentre_add hodd y h hh
  have hx' : x ∈ sitesOfCells {y} j := mem_sitesOfCells.2 ⟨y, by simp, h, hh, e⟩
  have h0 : (0 : Lattice4) ∈ centredCube (F.blockSide ^ j) := by
    refine Fintype.mem_piFinset.2 fun i => ?_
    have : 0 < F.blockSide ^ j := by have := hodd.pos; positivity
    simp only [Pi.zero_apply, Finset.mem_Icc]
    omega
  obtain ⟨y', hy', h', hh', e'⟩ := exists_cell_of_mem_sitesOfCells hodd hj hx' h0
  obtain rfl : y' = y := by simpa using hy'
  rw [siteOfCoords_zero, add_zero] at e'
  rw [hc]
  exact ⟨hy, h', hh', e'⟩
theorem baseSite_mem_sitesOfCells (hodd : Odd F.blockSide) {x : F.Site j} (hj : j ≤ F.top)
    (hx : x ∈ sitesOfCells S j) : baseSite x ∈ sitesOfCells S 0 := by
  obtain ⟨hy, h, hh, e⟩ := baseSite_eq_cellCentre_add hodd hj hx
  rw [e]
  exact mem_sitesOfCells.2 ⟨_, hy, h, by simpa using hh, rfl⟩
theorem cellSupDist_le_four (hamb : IsAdmissibleAmbient F) (hodd : Odd F.blockSide) {j' : ℕ}
    {x : F.Site j} {x' : F.Site j'} (hj : j ≤ F.top)
    (hj' : j' ≤ F.top) (hx : x ∈ sitesOfCells S j) (hx' : x' ∈ sitesOfCells S j')
    (hw : SupClose (2 * cellSideLength F) (baseSite x) (baseSite x')) :
    cellSupDist (enclosingCell x') (enclosingCell x) ≤ 4 := by
  obtain ⟨-, h, hh, e⟩ := baseSite_eq_cellCentre_add hodd hj hx
  obtain ⟨-, h', hh', e'⟩ := baseSite_eq_cellCentre_add hodd hj' hx'
  obtain ⟨δ, hδ, e2⟩ := hw
  have hN := cellSideLength_pos (F := F) hodd.pos
  have hb : ∀ i, |h i| ≤ cellSideLength F := by
    intro i
    have h1 := (mem_centredCube_iff _ _).1 hh i
    have hcs : ((F.blockSide ^ F.top : ℕ) : ℤ) = cellSideLength F := by simp [cellSideLength]
    rw [hcs] at h1
    rw [abs_le]
    constructor <;> omega
  refine cellSupDist_le_of_offsets hamb hodd (A := h + δ) (R := 3) (by norm_num) (fun i => ?_) hh' ?_
  · have := abs_add_le (h i) (δ i)
    have h1 := hb i
    have h2 := hδ i
    simp only [Pi.add_apply]
    push_cast
    linarith
  · rw [siteOfCoords_add, ← add_assoc, ← e, ← e2, e']
theorem abs_le_of_mem_twoBlockHull {L : ℕ} (hL : 1 ≤ L) {i : Fin 4} {v : Lattice4}
    (hv : v ∈ FlatPairing.twoBlockHull L i) (μ : Fin 4) : |v μ| ≤ 2 * (L : ℤ) := by
  have h := hv μ
  rw [abs_le]
  constructor
  · omega
  · split_ifs at h <;> omega
theorem mul_pow_le_cellSideLength (hodd : Odd F.blockSide) {j : ℕ} (hj : j < F.top) :
    (F.blockSide : ℤ) * (F.blockSide : ℤ) ^ j ≤ cellSideLength F := by
  have := pow_le_cellSideLength (F := F) hodd.pos (j := j + 1) hj
  rwa [pow_succ', ] at this
theorem mem_innerBonds_of_liesOnPath_bondContour (hodd : Odd F.blockSide) {j : ℕ} (hj : j < F.top)
    {c : F.Site (j + 1) × Fin 4} (hc : c ∈ innerBonds S (j + 1))
    {a : Lattice4} (ha : a ∈ centredCube F.blockSide) (π : Equiv.Perm (Fin 4)) {b : F.Site j × Fin 4}
    (hb : LiesOnPath b (refineSite c.1) (bondContour F.blockSide a π c.2)) :
    b ∈ innerBonds S j ∧
      SupClose (2 * (F.blockSide : ℤ) * (F.blockSide : ℤ) ^ j) (baseSite c.1) (baseSite b.1) ∧
      SupClose (2 * (F.blockSide : ℤ) * (F.blockSide : ℤ) ^ j) (baseSite c.1)
        (baseSite (b.1 + unitStep j b.2)) := by
  have hL : 1 ≤ F.blockSide := hodd.pos
  have hj1 : j + 1 ≤ F.top := hj
  have hp := (bondContour_spec π c.2 hL ha).1
  have hb' : LiesOnPath b (refineSite c.1 + siteOfCoords j (0 : Lattice4))
      (bondContour F.blockSide a π c.2) := by
    rwa [add_siteOfCoords_zero]
  obtain ⟨v, hv, hv', e⟩ := exists_offset_of_liesOnPath (refineSite c.1) hp hb'
  have m1 := refineSite_add_mem_of_mem_twoBlockHull hodd hj1 hc hv
  have m2 := refineSite_add_mem_of_mem_twoBlockHull hodd hj1 hc hv'
  have e2 : b.1 + unitStep j b.2 = refineSite c.1 + siteOfCoords j (v + basisVector b.2) := by
    rw [e, unitStep_eq, siteOfCoords_add, add_assoc]
  have hpow : (0 : ℤ) ≤ (F.blockSide : ℤ) ^ j := by positivity
  have key : ∀ w : Lattice4, w ∈ FlatPairing.twoBlockHull F.blockSide c.2 →
      SupClose (2 * (F.blockSide : ℤ) * (F.blockSide : ℤ) ^ j) (baseSite c.1)
        (baseSite (refineSite c.1 + siteOfCoords j w)) := by
    intro w hw
    refine ⟨fun i => (F.blockSide : ℤ) ^ j * w i, fun i => ?_, ?_⟩
    · rw [abs_mul, abs_of_nonneg hpow, mul_comm]
      exact mul_le_mul_of_nonneg_right (abs_le_of_mem_twoBlockHull hL hw i) hpow
    · rw [baseSite_add j (by omega), baseSite_refineSite j hj1]
  refine ⟨?_, ?_, ?_⟩
  · refine mem_innerBonds ?_ ?_
    · rw [e]; exact m1
    · rw [e2]; exact m2
  · rw [e]; exact key v hv
  · rw [e2]; exact key _ hv'
theorem mem_plaquetteCorners_of_liesOnPath {p : F.Site 0 × Fin 4 × Fin 4} {b : F.Site 0 × Fin 4}
    (hb : LiesOnPath b p.1 (plaquetteBoundary p)) :
    b.1 ∈ plaquetteCorners p ∧ b.1 + unitStep 0 b.2 ∈ plaquetteCorners p := by
  simp only [plaquetteBoundary, LiesOnPath, if_true, Bool.false_eq_true, if_false,
    BlockAverages.stepDisplacement, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl
  · simp [plaquetteCorners]
  · simp [plaquetteCorners]
  · have e : p.1 + unitStep 0 p.2.1 + unitStep 0 p.2.2 - unitStep 0 p.2.1 = p.1 + unitStep 0 p.2.2 := by
      abel
    have e2 : p.1 + unitStep 0 p.2.2 + unitStep 0 p.2.1 = p.1 + unitStep 0 p.2.1 + unitStep 0 p.2.2 := by
      abel
    simp only [e, e2]
    simp [plaquetteCorners]
  · have e : p.1 + unitStep 0 p.2.1 + unitStep 0 p.2.2 + - unitStep 0 p.2.1 - unitStep 0 p.2.2 = p.1 := by
      abel
    simp only [e]
    simp [plaquetteCorners]
theorem supClose_baseSite_add_unitStep {j : ℕ} (hj : j < F.top) (y : F.Site (j + 1)) (i : Fin 4) :
    SupClose (2 * (F.blockSide : ℤ) * (F.blockSide : ℤ) ^ j) (baseSite y)
      (baseSite (y + unitStep (j + 1) i)) := by
  have hpow : (0 : ℤ) ≤ (F.blockSide : ℤ) ^ (j + 1) := by positivity
  refine ⟨fun μ => (F.blockSide : ℤ) ^ (j + 1) * basisVector i μ, fun μ => ?_, ?_⟩
  · rw [abs_mul, abs_of_nonneg hpow]
    have h1 := abs_basisVector_le i μ
    have h2 : (F.blockSide : ℤ) ^ (j + 1) * |basisVector i μ| ≤ (F.blockSide : ℤ) ^ (j + 1) * 1 :=
      mul_le_mul_of_nonneg_left h1 hpow
    have h3 : (F.blockSide : ℤ) ^ (j + 1) = (F.blockSide : ℤ) * (F.blockSide : ℤ) ^ j := pow_succ' _ _
    nlinarith
  · rw [unitStep_eq, baseSite_add (j + 1) hj]
theorem supClose_of_readsSlot (hodd : Odd F.blockSide) {t : F.ActionTerm} (ht : t ∈ actionTerms S)
    {u : VariationSlot F} (hu : ReadsSlot t u) :
    SupClose (2 * (F.blockSide : ℤ) * (F.blockSide : ℤ) ^ actionTermLevel t) (actionTermSite t) (slotStart u) ∧
      SupClose (2 * (F.blockSide : ℤ) * (F.blockSide : ℤ) ^ actionTermLevel t) (actionTermSite t) (slotEnd u) ∧
      slotStart u ∈ sitesOfCells S 0 ∧ slotEnd u ∈ sitesOfCells S 0 := by
  have hL : (1 : ℤ) ≤ F.blockSide := by exact_mod_cast hodd.pos
  rcases t with p | ⟨j, c⟩
  · obtain ⟨b, rfl, hb⟩ := hu
    have hp : p ∈ innerPlaquettes S 0 := Finset.inl_mem_disjSum.1 ht
    have hcs := (Finset.mem_filter.1 hp).2.2
    obtain ⟨h1, h2⟩ := mem_plaquetteCorners_of_liesOnPath hb
    obtain ⟨δ, hδ, e⟩ := exists_offset_of_mem_plaquetteCorners p h1
    obtain ⟨δ', hδ', e'⟩ := exists_offset_of_mem_plaquetteCorners p h2
    have hr : (2 : ℤ) ≤ 2 * (F.blockSide : ℤ) * (F.blockSide : ℤ) ^ 0 := by
      simp only [pow_zero, mul_one]
      omega
    refine ⟨⟨δ, fun i => (hδ i).trans hr, ?_⟩, ⟨δ', fun i => (hδ' i).trans hr, ?_⟩, ?_, ?_⟩
    · show baseSite b.1 = _
      rw [baseSite_of_level_zero, e]
      rfl
    · show baseSite (b.1 + unitStep 0 b.2) = _
      rw [baseSite_of_level_zero, e']
      rfl
    · show baseSite b.1 ∈ _
      rw [baseSite_of_level_zero]
      exact hcs h1
    · show baseSite (b.1 + unitStep 0 b.2) ∈ _
      rw [baseSite_of_level_zero]
      exact hcs h2
  · have hc := Finset.inr_mem_disjSum.1 ht
    have hj : j < F.top := Finset.mem_range.1 (Finset.mem_sigma.1 hc).1
    have hcb : c ∈ innerBonds S (j + 1) := (Finset.mem_sigma.1 hc).2
    obtain ⟨m1, m2⟩ := innerBonds_ends hcb
    have hr0 : (0 : ℤ) ≤ 2 * (F.blockSide : ℤ) * (F.blockSide : ℤ) ^ j := by positivity
    have b1 := baseSite_mem_sitesOfCells hodd (j := j + 1) hj m1
    have b2 := baseSite_mem_sitesOfCells hodd (j := j + 1) hj m2
    rcases hu with rfl | rfl | ⟨hlt, rfl⟩ | ⟨a, ha, π, b, rfl, hb⟩
    · exact ⟨SupClose.refl hr0 _, SupClose.refl hr0 _, b1, b1⟩
    · exact ⟨supClose_baseSite_add_unitStep hj _ _, supClose_baseSite_add_unitStep hj _ _, b2, b2⟩
    · exact ⟨SupClose.refl hr0 _, supClose_baseSite_add_unitStep hj _ _, b1, b2⟩
    · obtain ⟨h1, h2, h3⟩ := mem_innerBonds_of_liesOnPath_bondContour hodd hj hcb ha π hb
      obtain ⟨n1, n2⟩ := innerBonds_ends h1
      exact ⟨h2, h3, baseSite_mem_sitesOfCells hodd hj.le n1, baseSite_mem_sitesOfCells hodd hj.le n2⟩
end YangMills.Construction.BlockAverages.VariationRates
end
