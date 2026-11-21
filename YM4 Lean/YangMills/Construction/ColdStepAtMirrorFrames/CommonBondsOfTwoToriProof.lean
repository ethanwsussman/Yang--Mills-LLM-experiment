import YangMills.Construction.LawInAState.DecayOverATorusProof
import YangMills.Construction.SummableBoundsOfTheFlow.SlopeBetweenComparesOnTwoToriProof
import YangMills.Construction.ColdStepAtMirrorFrames.CommonBondsOfTwoTori
import YangMills.Construction.ColdStepAtMirrorFrames.SitesOfABlock
import YangMills.Construction.HoleBesideASecondHole.CellsLeftOffTheSpotsProof
import Mathlib
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.deprecated false
noncomputable section
open YangMills.Construction.BlockAverages
namespace YangMills.Construction.ColdStepAtMirrorFrames
namespace TorusBonds
variable {F : BlockFrame}
theorem period_top_eq_extent (i : Fin 4) : F.period F.top i = F.extent i := by apply _root_.YangMills.Construction.GaugeFixing.period_top <;> assumption
theorem mem_centredCube_odd_iff (R : ℕ) (h : Fin 4 → ℤ) :
    h ∈ centredCube (2 * R + 1) ↔ ∀ i, |h i| ≤ (R : ℤ) := by apply _root_.YangMills.Construction.HoleSavings.mem_centredCube_odd <;> assumption
theorem neZero_period_top {n : ℕ} (hn : 0 < n) (hs : ∀ i, F.extent i = n) (i : Fin 4) :
    NeZero (F.period F.top i) :=
  ⟨by rw [period_top_eq_extent, hs]; omega⟩
theorem valMinAbs_intCast_of_small {n : ℕ} (hn : 0 < n) (hs : ∀ i, F.extent i = n) (i : Fin 4) {z : ℤ}
    (hz : 2 * |z| < n) : ((z : ZMod (F.period F.top i))).valMinAbs = z := by
  haveI := neZero_period_top hn hs i
  rw [ZMod.valMinAbs_spec]
  refine ⟨rfl, ?_⟩
  rw [period_top_eq_extent, hs]
  have := abs_le.mp (le_refl |z|)
  constructor <;> omega
theorem add_sites_sub_apply (Y : F.Cell) (c c' : Fin 4 → ℤ) (i : Fin 4) :
    ((Y + siteOfCoords F.top c : F.Cell) - (Y + siteOfCoords F.top c' : F.Cell)) i =
      ((c i - c' i : ℤ) : ZMod (F.period F.top i)) := by
  simp [siteOfCoords]
theorem supDist_add_sites {n : ℕ} (hn : 0 < n) (hs : ∀ i, F.extent i = n) (Y : F.Cell) (c c' : Fin 4 → ℤ)
    (h : ∀ i, 2 * |c i - c' i| < n) :
    cellSupDist (Y + siteOfCoords F.top c) (Y + siteOfCoords F.top c') =
      Finset.univ.sup fun i => (c i - c' i).natAbs := by
  unfold cellSupDist
  congr 1
  funext i
  have := add_sites_sub_apply Y c c' i
  simp only [Pi.add_apply, Pi.sub_apply] at this ⊢
  rw [this, valMinAbs_intCast_of_small hn hs i (h i)]
theorem add_siteOfCoords_zero (Y : F.Cell) : Y + siteOfCoords F.top (fun _ => (0 : ℤ)) = Y := by
  funext i
  simp [siteOfCoords]
theorem siteOfCoords_add_injective {n : ℕ} (hn : 0 < n) (hs : ∀ i, F.extent i = n) {Y : F.Cell}
    {c c' : Fin 4 → ℤ} (h : ∀ i, 2 * |c i - c' i| < n)
    (he : Y + siteOfCoords F.top c = Y + siteOfCoords F.top c') : c = c' := by
  funext i
  have h1 := congrFun (add_left_cancel he) i
  simp only [siteOfCoords] at h1
  rw [ZMod.intCast_eq_intCast_iff_dvd_sub, period_top_eq_extent, hs] at h1
  have h2 : c' i - c i = 0 := by
    apply Int.eq_zero_of_abs_lt_dvd h1
    have := h i
    rw [abs_sub_comm] at this
    have := abs_nonneg (c' i - c i)
    omega
  omega
theorem supDist_self (y : F.Cell) : cellSupDist y y = 0 := by apply _root_.YangMills.Construction.BlockLines.cellSupDist_self <;> assumption
theorem supDist_comm (y z : F.Cell) : cellSupDist y z = cellSupDist z y := by apply _root_.YangMills.Construction.BlockLines.cellSupDist_comm <;> assumption
theorem natAbs_coord_le_supDist (y z : F.Cell) (i : Fin 4) :
    ((y i - z i).valMinAbs).natAbs ≤ cellSupDist y z := by apply _root_.YangMills.Construction.PatchPoints.natAbs_valMinAbs_le_cellSupDist <;> assumption
theorem supDist_triangle (y z w : F.Cell) : cellSupDist y w ≤ cellSupDist y z + cellSupDist z w := by apply _root_.YangMills.Construction.BlockAverages.PatchLocality.cellSupDist_triangle <;> assumption
theorem add_siteOfCoords_diff {n : ℕ} (hn : 0 < n) (hs : ∀ i, F.extent i = n) (Y Z : F.Cell) :
    Y + siteOfCoords F.top (fun i => ((Z - Y) i).valMinAbs) = Z := by
  funext i
  haveI := neZero_period_top hn hs i
  simp only [Pi.add_apply, siteOfCoords, ZMod.coe_valMinAbs, Pi.sub_apply]
  ring
theorem abs_diff_coord_le (Y Z : F.Cell) (i : Fin 4) :
    |((Z - Y) i).valMinAbs| ≤ (cellSupDist Y Z : ℤ) := by apply _root_.YangMills.DeltaSharedProofs.p501586 <;> assumption
theorem mem_chordBonds_iff (hS : SiteDecomposition) (hC : BlocksCoverLowerLevel) (hL : Odd F.blockSide)
    (hs : ∀ i, 2 ≤ F.extent i) (x : F.Site F.depth) (i : Fin 4) :
    (x, i) ∈ chordBonds (finiteCells F) ↔
      cellOffset x i = ((F.blockSide : ℤ) - 1) / 2 ∨ ∃ l, i < l ∧ cellOffset x l ≠ 0 := by
  classical
  obtain ⟨_, _, s3, _⟩ := hS F hL hs
  have hpos : ∀ i, 0 < F.extent i := fun i => by have := hs i; omega
  have hcov := hC F hL hpos
  have hb : (x, i) ∈ innerBonds (finiteCells F) F.depth :=
    Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hcov x, Finset.mem_univ _⟩, hcov _⟩
  unfold chordBonds
  constructor
  · intro h
    have hnt := (Finset.mem_filter.mp h).2
    by_cases hc : IsCrossingBond (x, i)
    · exact Or.inl ((s3 x i).mp hc)
    · right
      by_contra hno
      apply hnt
      refine ⟨hc, fun l hl => ?_⟩
      by_contra hne
      exact hno ⟨l, hl, hne⟩
  · intro h
    refine Finset.mem_filter.mpr ⟨hb, fun ht => ?_⟩
    rcases h with h | ⟨l, hl, hne⟩
    · exact ht.1 ((s3 x i).mpr h)
    · exact hne (ht.2 l hl)
theorem fineBondAt_cell_offset (hS : SiteDecomposition) (hL : Odd F.blockSide) (hs : ∀ i, 2 ≤ F.extent i)
    (Y : F.Cell) {h o : Fin 4 → ℤ} (i : Fin 4) (ho : o ∈ centredCube F.blockSide) :
    enclosingCell (fineBondAt Y h o i).1 = Y + siteOfCoords F.top h ∧
      cellOffset (fineBondAt Y h o i).1 = o :=
  (hS F hL hs).1 _ _ ho
theorem exists_fineBondAt_eq (hS : SiteDecomposition) (hL : Odd F.blockSide) (hs : ∀ i, 2 ≤ F.extent i)
    {n : ℕ} (hn : 0 < n) (hsn : ∀ i, F.extent i = n) (Y : F.Cell) (R : ℕ)
    (b : ↥(chordBonds (finiteCells F))) (hd : cellSupDist Y (chordBondCell F b) ≤ R) :
    ∃ h ∈ centredCube (2 * R + 1), ∃ o ∈ centredCube F.blockSide, fineBondAt Y h o b.1.2 = b.1 := by
  obtain ⟨_, s2, _, _⟩ := hS F hL hs
  refine ⟨fun i => ((chordBondCell F b - Y) i).valMinAbs, ?_, cellOffset b.1.1, (s2 b.1.1).2, ?_⟩
  · rw [mem_centredCube_odd_iff]
    intro i
    have := abs_diff_coord_le Y (chordBondCell F b) i
    have h2 : (cellSupDist Y (chordBondCell F b) : ℤ) ≤ R := by exact_mod_cast hd
    exact this.trans h2
  · unfold fineBondAt
    rw [add_siteOfCoords_diff hn hsn]
    exact Prod.ext (s2 b.1.1).1 rfl
theorem fineBondAt_mem_chordBonds_transfer {F₂ : BlockFrame} (hS : SiteDecomposition)
    (hC : BlocksCoverLowerLevel) (hL : Odd F.blockSide) (hL₂ : Odd F₂.blockSide)
    (hLL : F.blockSide = F₂.blockSide)
    (hs : ∀ i, 2 ≤ F.extent i) (hs₂ : ∀ i, 2 ≤ F₂.extent i) (Y : F.Cell) (Y₂ : F₂.Cell)
    {h o : Fin 4 → ℤ} {i : Fin 4} (ho : o ∈ centredCube F.blockSide)
    (hb : fineBondAt Y h o i ∈ chordBonds (finiteCells F)) :
    fineBondAt Y₂ h o i ∈ chordBonds (finiteCells F₂) := by
  have ho₂ : o ∈ centredCube F₂.blockSide := hLL ▸ ho
  have h1 : (fineBondAt Y h o i) = ((fineBondAt Y h o i).1, i) := rfl
  have h2 : (fineBondAt Y₂ h o i) = ((fineBondAt Y₂ h o i).1, i) := rfl
  rw [h1, mem_chordBonds_iff hS hC hL hs, (fineBondAt_cell_offset hS hL hs Y i ho).2] at hb
  rw [h2, mem_chordBonds_iff hS hC hL₂ hs₂, (fineBondAt_cell_offset hS hL₂ hs₂ Y₂ i ho₂).2, ← hLL]
  exact hb
section TwoFrames
variable {F' : BlockFrame} {L : ℕ} {Y : F.Cell} {Y' : F'.Cell} {r n n' : ℕ}
theorem mem_commonBondOffsets {R : ℕ} {q : (Fin 4 → ℤ) × (Fin 4 → ℤ) × Fin 4}
    (hq : q ∈ commonBondOffsets Y Y' R) :
    q.1 ∈ centredCube (2 * R + 1) ∧ q.2.1 ∈ centredCube F.blockSide := by
  have := (Finset.mem_filter.mp hq).1
  simp only [Finset.mem_product, Finset.mem_univ, and_true] at this
  exact this
theorem two_abs_sub_lt {R : ℕ} {c c' : Fin 4 → ℤ} (hc : c ∈ centredCube (2 * R + 1))
    (hc' : c' ∈ centredCube (2 * R + 1)) (h : 4 * R < n) (i : Fin 4) : 2 * |c i - c' i| < n := by
  have h1 := (mem_centredCube_odd_iff R c).mp hc i
  have h2 := (mem_centredCube_odd_iff R c').mp hc' i
  have h3 := abs_sub (c i) (c' i)
  omega
theorem two_abs_zero_sub_lt {R : ℕ} {c : Fin 4 → ℤ} (hc : c ∈ centredCube (2 * R + 1)) (h : 4 * R < n)
    (i : Fin 4) : 2 * |(0 : ℤ) - c i| < n := by
  have h1 := (mem_centredCube_odd_iff R c).mp hc i
  rw [zero_sub, abs_neg]
  omega
end TwoFrames
open TorusBonds in
theorem hasCommonBonds_of_large (hS : SiteDecomposition) (hC : BlocksCoverLowerLevel) {L : ℕ} (hL : Odd L)
    {F' : BlockFrame} (Y : F.Cell) (Y' : F'.Cell) {r n n' : ℕ} (hF : F.blockSide = L)
    (hF' : F'.blockSide = L)
    (hs : ∀ i, F.extent i = n) (hs' : ∀ i, F'.extent i = n') (hr : 2 * r + 2 < n) (hr' : 2 * r + 2 < n') :
    HasCommonBonds Y Y' r := by
  have hn : 0 < n := by omega
  have hn' : 0 < n' := by omega
  have hO : Odd F.blockSide := hF ▸ hL
  have hO' : Odd F'.blockSide := hF' ▸ hL
  have h2 : ∀ i, 2 ≤ F.extent i := fun i => by rw [hs]; omega
  have h2' : ∀ i, 2 ≤ F'.extent i := fun i => by rw [hs']; omega
  have hLL : F.blockSide = F'.blockSide := hF.trans hF'.symm
  have h4R : 4 * (r / 2) < n := by omega
  have h4R' : 4 * (r / 2) < n' := by omega
  have h4Q : 4 * (r / 8) < n := by omega
  have h4Q' : 4 * (r / 8) < n' := by omega
  have place_left : ∀ q, chordBondCell F (commonBondLeft Y Y' (r / 2) q) = Y + siteOfCoords F.top q.1.1 :=
    fun q => (fineBondAt_cell_offset hS hO h2 Y q.1.2.2 (mem_commonBondOffsets q.2).2).1
  have place_right : ∀ q, chordBondCell F' (commonBondRight Y Y' (r / 2) q) =
      Y' + siteOfCoords F'.top q.1.1 := fun q =>
    (fineBondAt_cell_offset hS hO' h2' Y' q.1.2.2 (hLL ▸ (mem_commonBondOffsets q.2).2)).1
  have inj : ∀ {F₂ : BlockFrame} {Y₂ : F₂.Cell} {n₂ : ℕ}, Odd F₂.blockSide → (∀ i, 2 ≤ F₂.extent i) →
      0 < n₂ → (∀ i, F₂.extent i = n₂) → 4 * (r / 2) < n₂ →
      ∀ q q' : ↥(commonBondOffsets Y Y' (r / 2)), q.1.2.1 ∈ centredCube F₂.blockSide →
      q'.1.2.1 ∈ centredCube F₂.blockSide →
      fineBondAt Y₂ q.1.1 q.1.2.1 q.1.2.2 = fineBondAt Y₂ q'.1.1 q'.1.2.1 q'.1.2.2 →
      q = q' := by
    intro F₂ Y₂ n₂ hO₂ h2₂ hn₂ hs₂ h4 q q' ho ho' he
    have e1 := fineBondAt_cell_offset hS hO₂ h2₂ Y₂ (h := q.1.1) q.1.2.2 ho
    have e2 := fineBondAt_cell_offset hS hO₂ h2₂ Y₂ (h := q'.1.1) q'.1.2.2 ho'
    have hi : q.1.2.2 = q'.1.2.2 := (Prod.ext_iff.mp he).2
    have hcell : Y₂ + siteOfCoords F₂.top q.1.1 = Y₂ + siteOfCoords F₂.top q'.1.1 := by
      rw [← e1.1, ← e2.1, he]
    have hoff : q.1.2.1 = q'.1.2.1 := by
      rw [← e1.2, ← e2.2, he]
    have hh : q.1.1 = q'.1.1 := siteOfCoords_add_injective (n := n₂) hn₂ hs₂
      (two_abs_sub_lt (n := n₂) (mem_commonBondOffsets q.2).1 (mem_commonBondOffsets q'.2).1 h4) hcell
    exact Subtype.ext (Prod.ext hh (Prod.ext hoff hi))
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro q q' he
    exact inj hO h2 hn hs h4R q q' (mem_commonBondOffsets q.2).2 (mem_commonBondOffsets q'.2).2
      (congrArg Subtype.val he)
  · intro q q' he
    exact inj hO' h2' hn' hs' h4R' q q' (hLL ▸ (mem_commonBondOffsets q.2).2)
      (hLL ▸ (mem_commonBondOffsets q'.2).2) (congrArg Subtype.val he)
  · intro c c' he
    exact Subtype.ext (siteOfCoords_add_injective hn hs (two_abs_sub_lt c.2 c'.2 h4Q) he)
  · intro c c' he
    exact Subtype.ext (siteOfCoords_add_injective hn' hs' (two_abs_sub_lt c.2 c'.2 h4Q') he)
  · intro q q'
    simp only [cellDistReal, place_left, place_right]
    rw [supDist_add_sites hn hs _ _ _
        (two_abs_sub_lt (mem_commonBondOffsets q.2).1 (mem_commonBondOffsets q'.2).1 h4R),
      supDist_add_sites hn' hs' _ _ _
        (two_abs_sub_lt (mem_commonBondOffsets q.2).1 (mem_commonBondOffsets q'.2).1 h4R')]
  · intro q
    simp only [cellDistReal, place_left, place_right]
    have e1 := supDist_add_sites hn hs Y (fun _ => 0) q.1.1
      (two_abs_zero_sub_lt (mem_commonBondOffsets q.2).1 h4R)
    have e2 := supDist_add_sites hn' hs' Y' (fun _ => 0) q.1.1
      (two_abs_zero_sub_lt (mem_commonBondOffsets q.2).1 h4R')
    rw [add_siteOfCoords_zero] at e1 e2
    rw [e1, e2]
  · intro b hb
    by_contra hlt
    have hlt' : ((cellSupDist Y (chordBondCell F b) : ℕ) : ℝ) < (r : ℝ) / 2 := not_le.mp hlt
    have hd : cellSupDist Y (chordBondCell F b) ≤ r / 2 := by
      have : (2 * cellSupDist Y (chordBondCell F b) : ℝ) < r := by linarith
      have : 2 * cellSupDist Y (chordBondCell F b) < r := by exact_mod_cast this
      omega
    obtain ⟨h, hh, o, ho, he⟩ := exists_fineBondAt_eq hS hO h2 hn hs Y (r / 2) b hd
    have hmem : fineBondAt Y h o b.1.2 ∈ chordBonds (finiteCells F) := by
      rw [he]
      exact b.2
    apply hb
    refine ⟨⟨(h, o, b.1.2), ?_⟩, Subtype.ext he⟩
    refine Finset.mem_filter.mpr
      ⟨?_, hmem, fineBondAt_mem_chordBonds_transfer hS hC hO hO' hLL h2 h2' Y Y' ho hmem⟩
    simp only [Finset.mem_product, Finset.mem_univ, and_true]
    exact ⟨hh, ho⟩
  · intro b hb
    by_contra hlt
    have hlt' : ((cellSupDist Y' (chordBondCell F' b) : ℕ) : ℝ) < (r : ℝ) / 2 := not_le.mp hlt
    have hd : cellSupDist Y' (chordBondCell F' b) ≤ r / 2 := by
      have : (2 * cellSupDist Y' (chordBondCell F' b) : ℝ) < r := by linarith
      have : 2 * cellSupDist Y' (chordBondCell F' b) < r := by exact_mod_cast this
      omega
    obtain ⟨h, hh, o, ho, he⟩ := exists_fineBondAt_eq hS hO' h2' hn' hs' Y' (r / 2) b hd
    have hmem : fineBondAt Y' h o b.1.2 ∈ chordBonds (finiteCells F') := by
      rw [he]
      exact b.2
    apply hb
    refine ⟨⟨(h, o, b.1.2), ?_⟩, Subtype.ext he⟩
    refine Finset.mem_filter.mpr
      ⟨?_, fineBondAt_mem_chordBonds_transfer hS hC hO' hO hLL.symm h2' h2 Y' Y ho hmem, hmem⟩
    simp only [Finset.mem_product, Finset.mem_univ, and_true]
    exact ⟨hh, hLL ▸ ho⟩
  · intro c
    have e1 := supDist_add_sites hn hs Y (fun _ => 0) c.1 (two_abs_zero_sub_lt c.2 h4Q)
    rw [add_siteOfCoords_zero] at e1
    have h1 : cellSupDist Y (offsetCell Y (r / 8) c) ≤ r / 8 := by
      change cellSupDist Y (Y + siteOfCoords F.top c.1) ≤ r / 8
      rw [e1]
      apply Finset.sup_le
      intro i _
      have h3 := (mem_centredCube_odd_iff _ _).mp c.2 i
      simp only [zero_sub, Int.natAbs_neg]
      have h4 := Int.abs_eq_natAbs (c.1 i)
      omega
    have h2 : ((r / 8 : ℕ) : ℝ) ≤ (r : ℝ) / 8 := by
      rw [le_div_iff₀ (by norm_num)]
      have : r / 8 * 8 ≤ r := Nat.div_mul_le_self r 8
      exact_mod_cast this
    simp only [cellDistReal]
    have h3 : ((cellSupDist Y (offsetCell Y (r / 8) c) : ℕ) : ℝ) ≤ ((r / 8 : ℕ) : ℝ) := by
      exact_mod_cast h1
    linarith
  · intro Z hZ
    by_contra hlt
    have hlt' : ((cellSupDist Y Z : ℕ) : ℝ) < (r : ℝ) / 8 := not_le.mp hlt
    have hd : cellSupDist Y Z ≤ r / 8 := by
      have : (8 * cellSupDist Y Z : ℝ) < r := by linarith
      have : 8 * cellSupDist Y Z < r := by exact_mod_cast this
      omega
    apply hZ
    refine ⟨⟨fun i => ((Z - Y) i).valMinAbs, ?_⟩, add_siteOfCoords_diff hn hs Y Z⟩
    rw [mem_centredCube_odd_iff]
    intro i
    have h1 := abs_diff_coord_le Y Z i
    have h3 : (cellSupDist Y Z : ℤ) ≤ r / 8 := by exact_mod_cast hd
    exact h1.trans h3
  · intro Z hZ
    by_contra hlt
    have hlt' : ((cellSupDist Y' Z : ℕ) : ℝ) < (r : ℝ) / 8 := not_le.mp hlt
    have hd : cellSupDist Y' Z ≤ r / 8 := by
      have : (8 * cellSupDist Y' Z : ℝ) < r := by linarith
      have : 8 * cellSupDist Y' Z < r := by exact_mod_cast this
      omega
    apply hZ
    refine ⟨⟨fun i => ((Z - Y') i).valMinAbs, ?_⟩, add_siteOfCoords_diff hn' hs' Y' Z⟩
    rw [mem_centredCube_odd_iff]
    intro i
    have h1 := abs_diff_coord_le Y' Z i
    have h3 : (cellSupDist Y' Z : ℤ) ≤ r / 8 := by exact_mod_cast hd
    exact h1.trans h3
def expWeight (μ : ℝ) (k : ℤ) : ℝ := Real.exp (-(μ * |(k : ℝ)|))
theorem summable_expWeight {μ : ℝ} (hμ : 0 < μ) : Summable (expWeight μ) := by apply _root_.YangMills.DeltaSharedProofs.p3646 <;> assumption
theorem expWeight_nonneg (μ : ℝ) (k : ℤ) : 0 ≤ expWeight μ k := (Real.exp_pos _).le
theorem sum_expWeight_zmod_le {μ : ℝ} (hμ : 0 < μ) (m : ℕ) [NeZero m] (a : ZMod m) :
    ∑ z : ZMod m, expWeight μ ((a - z).valMinAbs) ≤ ∑' k : ℤ, expWeight μ k := by
  classical
  have h1 : ∑ z : ZMod m, expWeight μ ((a - z).valMinAbs) = ∑ z : ZMod m, expWeight μ z.valMinAbs :=
    Fintype.sum_equiv (Equiv.subLeft a) _ _ fun z => rfl
  have hinj : Function.Injective (ZMod.valMinAbs (n := m)) := fun p q h => by
    have := congrArg (fun k : ℤ => (k : ZMod m)) h
    simpa [ZMod.coe_valMinAbs] using this
  rw [h1, ← Finset.sum_image (s := Finset.univ) (g := ZMod.valMinAbs) (f := expWeight μ)
    (fun p _ q _ h => hinj h)]
  exact (summable_expWeight hμ).sum_le_tsum _ fun k _ => expWeight_nonneg μ k
theorem sum_exp_cellDistReal_le {κ : ℝ} (hκ : 0 < κ) {n : ℕ} (hn : 0 < n) (hs : ∀ i, F.extent i = n)
    [Fintype F.Cell] (Z : F.Cell) : ∑ Z' : F.Cell, Real.exp (-(κ / 2 * cellDistReal F Z Z')) ≤
      (∑' k : ℤ, expWeight (κ / 8) k) ^ 4 := by
  classical
  haveI := fun i => neZero_period_top (F := F) hn hs i
  set G := ∑' k : ℤ, expWeight (κ / 8) k with hG
  have hμ : 0 < κ / 8 := by positivity
  have huniv : (Finset.univ : Finset F.Cell) = Fintype.piFinset fun i => Finset.univ := by
    ext z
    simp
  have hterm : ∀ Z' : F.Cell, Real.exp (-(κ / 2 * cellDistReal F Z Z')) ≤
      ∏ i, expWeight (κ / 8) ((Z i - Z' i).valMinAbs) := fun Z' => by
    unfold expWeight
    rw [← Real.exp_sum]
    apply Real.exp_le_exp.mpr
    have h1 : ∀ i, |(((Z i - Z' i).valMinAbs : ℤ) : ℝ)| ≤ cellDistReal F Z Z' := fun i => by
      have := natAbs_coord_le_supDist Z Z' i
      have h2 : (((Z i - Z' i).valMinAbs).natAbs : ℝ) ≤ cellSupDist Z Z' := by exact_mod_cast this
      simpa [cellDistReal, Nat.cast_natAbs] using h2
    have h3 : ∑ i, (κ / 8 * |(((Z i - Z' i).valMinAbs : ℤ) : ℝ)|) ≤
        ∑ _i : Fin 4, κ / 8 * cellDistReal F Z Z' :=
      Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (h1 i) hμ.le
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_ofNat] at h3
    simp only [Finset.sum_neg_distrib]
    nlinarith
  calc _ ≤ ∑ Z' : F.Cell, ∏ i, expWeight (κ / 8) ((Z i - Z' i).valMinAbs) :=
        Finset.sum_le_sum fun Z' _ => hterm Z'
    _ = ∏ i, ∑ z : ZMod (F.period F.top i), expWeight (κ / 8) ((Z i - z).valMinAbs) := by
        rw [huniv, Finset.prod_univ_sum]
    _ ≤ ∏ _i : Fin 4, G := Finset.prod_le_prod
        (fun i _ => Finset.sum_nonneg fun _ _ => expWeight_nonneg _ _)
        (fun i _ => sum_expWeight_zmod_le hμ _ (Z i))
    _ = G ^ 4 := by simp
theorem card_chordBondCell_fibre_le (hS : SiteDecomposition) (hL : Odd F.blockSide)
    (hs : ∀ i, 2 ≤ F.extent i) (Z : F.Cell) :
    (Finset.univ.filter fun b : ↥(chordBonds (finiteCells F)) => chordBondCell F b = Z).card ≤
      (centredCube F.blockSide ×ˢ (Finset.univ : Finset (Fin 4))).card := by
  classical
  obtain ⟨_, s2, _, _⟩ := hS F hL hs
  apply Finset.card_le_card_of_injOn (fun b => (cellOffset b.1.1, b.1.2))
  · intro b _
    simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe, Finset.mem_univ, and_true]
    exact (s2 b.1.1).2
  · intro b hb b' hb' he
    have h1 : chordBondCell F b = Z := (Finset.mem_filter.mp (Finset.mem_coe.mp hb)).2
    have h2 : chordBondCell F b' = Z := (Finset.mem_filter.mp (Finset.mem_coe.mp hb')).2
    have e1 := (s2 b.1.1).1
    have e2 := (s2 b'.1.1).1
    simp only [Prod.mk.injEq] at he
    have hc : enclosingCell b.1.1 = enclosingCell b'.1.1 := h1.trans h2.symm
    apply Subtype.ext
    refine Prod.ext ?_ he.2
    rw [← e1, ← e2, hc, he.1]
theorem exists_decayingPlacement (hS : SiteDecomposition) {L : ℕ} (hL : Odd L) {κ : ℝ} (hκ : 0 < κ) :
    ∃ S : ℝ, ∀ (F : BlockFrame) (n : ℕ) [Fintype F.Cell], F.blockSide = L → 2 ≤ n →
      (∀ i, F.extent i = n) → IsDecayingPlacement κ S (chordBondCell F) (cellDistReal F) := by
  classical
  refine ⟨(((centredCube L ×ˢ (Finset.univ : Finset (Fin 4))).card : ℝ) + 1) *
    (∑' k : ℤ, expWeight (κ / 8) k) ^ 4, ?_⟩
  intro F n _ hF hn hs
  set G4 := (∑' k : ℤ, expWeight (κ / 8) k) ^ 4 with hG4
  have hG0 : 0 ≤ G4 := pow_nonneg (tsum_nonneg (expWeight_nonneg _)) 4
  set Nb : ℝ := ((centredCube L ×ˢ (Finset.univ : Finset (Fin 4))).card : ℝ) with hNb
  have hNb0 : 0 ≤ Nb := by positivity
  have hn0 : 0 < n := by omega
  have hO : Odd F.blockSide := hF ▸ hL
  have h2 : ∀ i, 2 ≤ F.extent i := fun i => by rw [hs]; exact hn
  have hcells := fun Z => sum_exp_cellDistReal_le hκ hn0 hs Z
  refine ⟨fun Z => by simp [cellDistReal, supDist_self],
    fun Z Z' => by simp [cellDistReal, supDist_comm Z Z'],
    fun Z Z' Z'' => ?_, fun Z => ?_, fun Z => ?_⟩
  · simp only [cellDistReal]
    exact_mod_cast supDist_triangle Z Z' Z''
  · have hfib : ∑ b, Real.exp (-(κ / 2 * cellDistReal F Z (chordBondCell F b))) =
        ∑ Z', ∑ b ∈ Finset.univ.filter fun b => chordBondCell F b = Z',
          Real.exp (-(κ / 2 * cellDistReal F Z (chordBondCell F b))) :=
      (Finset.sum_fiberwise Finset.univ (chordBondCell F) _).symm
    rw [hfib]
    calc _ ≤ ∑ Z', Nb * Real.exp (-(κ / 2 * cellDistReal F Z Z')) := by
          refine Finset.sum_le_sum fun Z' _ => ?_
          have e1 : ∑ b ∈ Finset.univ.filter (fun b => chordBondCell F b = Z'),
              Real.exp (-(κ / 2 * cellDistReal F Z (chordBondCell F b))) =
              ∑ b ∈ Finset.univ.filter (fun b => chordBondCell F b = Z'),
                Real.exp (-(κ / 2 * cellDistReal F Z Z')) :=
            Finset.sum_congr rfl fun b hb => by rw [(Finset.mem_filter.mp hb).2]
          rw [e1, Finset.sum_const, nsmul_eq_mul]
          apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
          have := card_chordBondCell_fibre_le hS hO h2 Z'
          rw [hF] at this
          rw [hNb]
          exact_mod_cast this
      _ = Nb * ∑ Z', Real.exp (-(κ / 2 * cellDistReal F Z Z')) := by rw [Finset.mul_sum]
      _ ≤ Nb * G4 := mul_le_mul_of_nonneg_left (hcells Z) hNb0
      _ ≤ _ := by nlinarith
  · exact (hcells Z).trans (by nlinarith)
end TorusBonds
open TorusBonds in
theorem commonBondsOfTwoTori_holds (hS : SiteDecomposition)
    (hC : BlocksCoverLowerLevel) : commonBondsOfTwoTori := by
  intro L hL
  refine ⟨fun κ hκ => exists_decayingPlacement hS hL hκ, fun F F' Y Y' r n n' hF hF' hs hs' hr hr' => ?_⟩
  exact hasCommonBonds_of_large hS hC hL Y Y' hF hF' hs hs' hr hr'
end YangMills.Construction.ColdStepAtMirrorFrames
end
