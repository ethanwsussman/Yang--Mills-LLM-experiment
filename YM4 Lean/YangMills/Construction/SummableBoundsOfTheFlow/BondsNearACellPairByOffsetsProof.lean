import YangMills.Construction.ClusterExpansionOfAStep.SitesOfTheTopOfAStep
import YangMills.Construction.ColdStepAtMirrorFrames.OffsetsInABlock
import YangMills.Construction.SummableBoundsOfTheFlow.BondsNearACellPairByOffsets
import YangMills.Construction.SummableBoundsOfTheFlow.SitesOfACellAreFewProofForm
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open BlockAverages ColdStepAtMirrorFrames
namespace TorusComparison
namespace BondsNearCells
variable {F : BlockFrame}
theorem top_sub_depth : F.top - F.depth = 1 := by simp [BlockFrame.top]
theorem period_top (i : Fin 4) : F.period F.top i = F.extent i := by simp [BlockFrame.period]
theorem period_depth (i : Fin 4) : F.period F.depth i = F.extent i * F.blockSide := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.MinimizingChart.period_depth <;> assumption
theorem siteOfCoords_add {j : ℕ} (a b : Fin 4 → ℤ) :
    (siteOfCoords j (a + b) : F.Site j) = siteOfCoords j a + siteOfCoords j b := by apply _root_.YangMills.Construction.GaugeFixing.siteOfCoords_add <;> assumption
theorem valMinAbs_intCast_of_bounds {n : ℕ} [NeZero n] (a : ℤ) (h1 : -(n : ℤ) < a * 2) (h2 : a * 2 ≤ n) :
    ((a : ZMod n)).valMinAbs = a :=
  (ZMod.valMinAbs_spec _ _).2 ⟨rfl, h1, h2⟩
theorem enclosingCell_cellCentre_add (hL : Odd F.blockSide) (z : F.Cell) (h : Fin 4 → ℤ)
    (hh : h ∈ centredCube F.blockSide) :
    enclosingCell (cellCentre F.depth z + siteOfCoords F.depth h : F.Site F.depth) = z := by apply _root_.YangMills.Construction.CellCounting.enclosingCell_cellCentre_add <;> assumption
theorem cellOffset_cellCentre_add (hL : Odd F.blockSide) (hs : ∀ i, 2 ≤ F.extent i) (z : F.Cell)
    (h : Fin 4 → ℤ) (hh : h ∈ centredCube F.blockSide) :
    cellOffset (cellCentre F.depth z + siteOfCoords F.depth h : F.Site F.depth) = h := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.BlockOffsets.cellOffset_offset <;> assumption
theorem cellCentre_add_siteOfCoords (hs : ∀ i, 0 < F.extent i) (hLpos : 0 < F.blockSide) (z : F.Cell)
    (g : Fin 4 → ℤ) :
    (cellCentre F.depth (z + siteOfCoords F.top g) : F.Site F.depth) =
      cellCentre F.depth z + siteOfCoords F.depth (fun i => (F.blockSide : ℤ) * g i) := by
  funext i
  have hne1 : NeZero (F.period F.top i) := ⟨by rw [period_top]; exact (hs i).ne'⟩
  simp only [cellCentre, siteOfCoords, Pi.add_apply, top_sub_depth, pow_one]
  rw [← Int.cast_add, ZMod.intCast_eq_intCast_iff_dvd_sub]
  have hz : (((siteCoords (z + siteOfCoords F.top g) i : ℤ)) : ZMod (F.period F.top i)) =
      ((siteCoords z i + g i : ℤ) : ZMod (F.period F.top i)) := by
    have e1 : (((siteCoords (z + siteOfCoords F.top g) i : ℤ)) : ZMod (F.period F.top i)) =
        (z + siteOfCoords F.top g : F.Cell) i := by
      unfold siteCoords
      exact ZMod.intCast_zmod_cast _
    have e2 : ((siteCoords z i : ℤ) : ZMod (F.period F.top i)) = z i := by
      unfold siteCoords
      exact ZMod.intCast_zmod_cast _
    rw [e1, Int.cast_add, e2]
    simp [siteOfCoords]
  obtain ⟨e, he⟩ := (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).1 hz
  have hper : ((F.period F.depth i : ℕ) : ℤ) = (F.extent i : ℤ) * (F.blockSide : ℤ) := by
    rw [period_depth]; push_cast; ring
  have hper2 : ((F.period F.top i : ℕ) : ℤ) = (F.extent i : ℤ) := by rw [period_top]
  rw [hper2] at he
  rw [hper]
  refine ⟨e, ?_⟩
  linear_combination (F.blockSide : ℤ) * he
theorem isCrossingBond_iff (hL : Odd F.blockSide) (hs : ∀ i, 2 ≤ F.extent i) (z : F.Cell) (o : Fin 4 → ℤ)
    (ho : o ∈ centredCube F.blockSide) (k : Fin 4) :
    IsCrossingBond (cellCentre F.depth z + siteOfCoords F.depth o, k) ↔
      o k = ((F.blockSide : ℤ) - 1) / 2 := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.BlockOffsets.isCrossingBond_iff <;> assumption
theorem isAxialTreeBond_iff (hL : Odd F.blockSide) (hs : ∀ i, 2 ≤ F.extent i) (z : F.Cell)
    (o : Fin 4 → ℤ) (ho : o ∈ centredCube F.blockSide) (k : Fin 4) :
    IsAxialTreeBond (cellCentre F.depth z + siteOfCoords F.depth o, k) ↔
      o k ≠ ((F.blockSide : ℤ) - 1) / 2 ∧ ∀ l, k < l → o l = 0 := by apply _root_.YangMills.Construction.TopLevelSites.isAxialTreeBond_iff <;> assumption
theorem two_mul_cellSupDist_le (hs : ∀ i, 2 ≤ F.extent i) (Y : F.Cell) (h : Fin 4 → ℤ) (q : ℕ)
    (hq : ∀ i, 2 * q + 2 < F.extent i) (hh : ∀ l, 2 * |h l| ≤ q) :
    2 * cellSupDist (Y + siteOfCoords F.top h) Y ≤ q := by
  have key : cellSupDist (Y + siteOfCoords F.top h) Y ≤ q / 2 := by
    unfold cellSupDist
    refine Finset.sup_le fun i _ => ?_
    have hn : (F.period F.top i) ≠ 0 := by rw [period_top]; have := hs i; omega
    haveI : NeZero (F.period F.top i) := ⟨hn⟩
    have e : (Y + siteOfCoords F.top h : F.Cell) i - Y i = ((h i : ℤ) : ZMod (F.period F.top i)) := by
      simp [siteOfCoords]
    rw [e]
    have hper2 : ((F.period F.top i : ℕ) : ℤ) = (F.extent i : ℤ) := by rw [period_top]
    have hb : ((2 * q + 2 : ℕ) : ℤ) < (F.extent i : ℤ) := by exact_mod_cast hq i
    have hhi := hh i
    have h1 := abs_le.1 (le_refl |h i|)
    rw [valMinAbs_intCast_of_bounds _ (by rw [hper2]; push_cast at hb; linarith [h1.1])
      (by rw [hper2]; push_cast at hb; linarith [h1.2])]
    omega
  omega
theorem mem_chordBonds (hB : BlocksCoverLowerLevel) (hL : Odd F.blockSide) (hs : ∀ i, 0 < F.extent i)
    {b : F.Site F.depth × Fin 4} (hnt : ¬ IsAxialTreeBond b) : b ∈ chordBonds (finiteCells F) := by
  unfold chordBonds innerBonds
  simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_univ, and_true]
  exact ⟨⟨hB F hL hs _, hB F hL hs _⟩, hnt⟩
open Classical in
def bondOffsets (L q : ℕ) : Finset ((Fin 4 → ℤ) × (Fin 4 → ℤ) × Fin 4) :=
  ((Fintype.piFinset fun _ => Finset.Icc (-(q : ℤ)) q) ×ˢ centredCube L ×ˢ Finset.univ).filter fun i =>
    (∀ l, 2 * |i.1 l| ≤ q) ∧ ¬ (i.2.1 i.2.2 ≠ ((L : ℤ) - 1) / 2 ∧ ∀ l, i.2.2 < l → i.2.1 l = 0)
theorem mem_bondOffsets {L q : ℕ} {i : (Fin 4 → ℤ) × (Fin 4 → ℤ) × Fin 4} (hi : i ∈ bondOffsets L q) :
    (∀ l, 2 * |i.1 l| ≤ q) ∧ i.2.1 ∈ centredCube L ∧
      ¬ (i.2.1 i.2.2 ≠ ((L : ℤ) - 1) / 2 ∧ ∀ l, i.2.2 < l → i.2.1 l = 0) := by
  unfold bondOffsets at hi
  rw [Finset.mem_filter, Finset.mem_product, Finset.mem_product] at hi
  exact ⟨hi.2.1, hi.1.2.1, hi.2.2⟩
theorem mk_mem_bondOffsets {L q : ℕ} {h o : Fin 4 → ℤ} {k : Fin 4} (h1 : ∀ l, 2 * |h l| ≤ q)
    (h2 : o ∈ centredCube L) (h3 : ¬ (o k ≠ ((L : ℤ) - 1) / 2 ∧ ∀ l, k < l → o l = 0)) :
    (h, o, k) ∈ bondOffsets L q := by
  unfold bondOffsets
  rw [Finset.mem_filter, Finset.mem_product, Finset.mem_product]
  refine ⟨⟨?_, h2, Finset.mem_univ _⟩, h1, h3⟩
  refine Fintype.mem_piFinset.2 fun l => ?_
  have := h1 l
  have h4 := abs_le.1 (le_refl |h l|)
  rw [Finset.mem_Icc]
  constructor <;> linarith [abs_nonneg (h l)]
def chordBondAtOffsets (hB : BlocksCoverLowerLevel) (hL : Odd F.blockSide) (hs : ∀ i, 2 ≤ F.extent i)
    (Y : F.Cell) (q : ℕ) (i : ↥(bondOffsets F.blockSide q)) : ↥(chordBonds (finiteCells F)) :=
  ⟨fineBondAt Y i.1.1 i.1.2.1 i.1.2.2, mem_chordBonds hB hL (fun l => by have := hs l; omega) (by
    have hi := mem_bondOffsets i.2
    unfold fineBondAt
    rw [isAxialTreeBond_iff hL hs _ _ hi.2.1]
    exact hi.2.2)⟩
theorem chordBondAtOffsets_injective (hB : BlocksCoverLowerLevel) (hL : Odd F.blockSide)
    (hs : ∀ i, 2 ≤ F.extent i) (Y : F.Cell) (q : ℕ) (hq : ∀ i, 2 * q + 2 < F.extent i) :
    Function.Injective (chordBondAtOffsets hB hL hs Y q) := by
  rintro ⟨⟨h, o, k⟩, hi⟩ ⟨⟨h', o', k'⟩, hi'⟩ heq
  have h1 := mem_bondOffsets hi
  have h2 := mem_bondOffsets hi'
  simp only at h1 h2
  have e0 : fineBondAt Y h o k = fineBondAt Y h' o' k' := congrArg Subtype.val heq
  have ek : k = k' := congrArg Prod.snd e0
  have es : (cellCentre F.depth (Y + siteOfCoords F.top h) + siteOfCoords F.depth o : F.Site F.depth) =
      cellCentre F.depth (Y + siteOfCoords F.top h') + siteOfCoords F.depth o' := congrArg Prod.fst e0
  have ec := congrArg enclosingCell es
  rw [enclosingCell_cellCentre_add hL _ _ h1.2.1, enclosingCell_cellCentre_add hL _ _ h2.2.1] at ec
  have eo := congrArg cellOffset es
  rw [cellOffset_cellCentre_add hL hs _ _ h1.2.1, cellOffset_cellCentre_add hL hs _ _ h2.2.1] at eo
  have eh : h = h' := by
    funext l
    have e1 : ((h l : ℤ) : ZMod (F.period F.top l)) = ((h' l : ℤ) : ZMod (F.period F.top l)) := by
      have := congrFun (add_left_cancel ec) l
      simpa [siteOfCoords] using this
    obtain ⟨e, he⟩ := (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).1 e1
    have hper2 : ((F.period F.top l : ℕ) : ℤ) = (F.extent l : ℤ) := by rw [period_top]
    rw [hper2] at he
    have hb : (2 * (q : ℤ) + 2) < (F.extent l : ℤ) := by exact_mod_cast hq l
    have b1 := h1.1 l
    have b2 := h2.1 l
    have a1 := abs_le.1 (le_refl |h l|)
    have a2 := abs_le.1 (le_refl |h' l|)
    have hd : |h' l - h l| ≤ (q : ℤ) := by
      rw [abs_le]
      constructor <;> linarith
    by_contra hne
    have he0 : e ≠ 0 := by
      rintro rfl
      apply hne
      linarith
    have : (F.extent l : ℤ) ≤ |h' l - h l| := by
      rw [he, abs_mul, abs_of_nonneg (by positivity : (0 : ℤ) ≤ (F.extent l : ℤ))]
      have : (1 : ℤ) ≤ |e| := Int.one_le_abs he0
      nlinarith [(by positivity : (0 : ℤ) ≤ (F.extent l : ℤ))]
    linarith
  subst ek
  subst eh
  subst eo
  rfl
theorem chordBondAtOffsets_mem_bondsNearCell (hB : BlocksCoverLowerLevel) (hL : Odd F.blockSide)
    (hs : ∀ i, 2 ≤ F.extent i) (Y : F.Cell) (q : ℕ) (hq : ∀ i, 2 * q + 2 < F.extent i)
    (i : ↥(bondOffsets F.blockSide q)) :
    chordBondAtOffsets hB hL hs Y q i ∈ bondsNearCell Y q := by
  have hi := mem_bondOffsets i.2
  unfold bondsNearCell
  rw [Finset.mem_filter]
  refine ⟨Finset.mem_univ _, ?_⟩
  show 2 * cellSupDist (enclosingCell (fineBondAt Y i.1.1 i.1.2.1 i.1.2.2).1) Y ≤ q
  unfold fineBondAt
  simp only
  rw [enclosingCell_cellCentre_add hL _ _ hi.2.1]
  exact two_mul_cellSupDist_le hs Y _ q hq hi.1
theorem exists_chordBondAtOffsets_eq (hB : BlocksCoverLowerLevel) (hL : Odd F.blockSide)
    (hs : ∀ i, 2 ≤ F.extent i) (Y : F.Cell) (q : ℕ) (hq : ∀ i, 2 * q + 2 < F.extent i)
    (b : ↥(chordBonds (finiteCells F))) (hb : b ∈ bondsNearCell Y q) :
    ∃ i, chordBondAtOffsets hB hL hs Y q i = b := by
  have hs0 : ∀ i, 0 < F.extent i := fun l => by have := hs l; omega
  have hx := hB F hL hs0 b.1.1
  obtain ⟨z, -, hxz⟩ := Finset.mem_biUnion.1 hx
  obtain ⟨o, ho, hzo⟩ := Finset.mem_image.1 hxz
  rw [top_sub_depth, pow_one] at ho
  have hcell : enclosingCell b.1.1 = z := by
    rw [← hzo]
    have : (siteOfCoords F.depth o : F.Site F.depth) = siteOfCoords F.depth o := rfl
    exact enclosingCell_cellCentre_add hL z o ho
  have hnear : 2 * cellSupDist z Y ≤ q := by
    have := (Finset.mem_filter.1 hb).2
    rwa [hcell] at this
  set h : Fin 4 → ℤ := fun l => ((z - Y : F.Cell) l).valMinAbs with hh
  have hzh : Y + siteOfCoords F.top h = z := by
    funext l
    have hn : (F.period F.top l) ≠ 0 := by rw [period_top]; exact (hs0 l).ne'
    haveI : NeZero (F.period F.top l) := ⟨hn⟩
    simp [siteOfCoords, hh]
  have hbd : ∀ l, 2 * |h l| ≤ q := by
    intro l
    have e1 : ((z - Y : F.Cell) l).valMinAbs.natAbs ≤ cellSupDist z Y := by
      unfold cellSupDist
      exact Finset.le_sup (f := fun i => ((z i - Y i).valMinAbs).natAbs) (Finset.mem_univ l)
    have e2 : |h l| = (((z - Y : F.Cell) l).valMinAbs.natAbs : ℤ) := by
      simp only [hh]
      exact Int.abs_eq_natAbs _
    rw [e2]
    have : 2 * ((z - Y : F.Cell) l).valMinAbs.natAbs ≤ q := by omega
    exact_mod_cast this
  have hnt : ¬ IsAxialTreeBond b.1 := by
    have := b.2
    simp only [chordBonds, Finset.mem_filter] at this
    exact this.2
  have hbe : b.1 = (cellCentre F.depth z + siteOfCoords F.depth o, b.1.2) := by
    rw [hzo]
  have ht : ¬ (o b.1.2 ≠ ((F.blockSide : ℤ) - 1) / 2 ∧ ∀ l, b.1.2 < l → o l = 0) := by
    rw [← isAxialTreeBond_iff hL hs z o ho b.1.2, ← hbe]
    exact hnt
  refine ⟨⟨(h, o, b.1.2), mk_mem_bondOffsets hbd ho ht⟩, Subtype.ext ?_⟩
  show fineBondAt Y h o b.1.2 = b.1
  unfold fineBondAt
  rw [hzh, hbe]
end BondsNearCells
open BondsNearCells in
theorem bondsNearCellsPairStatement_of_blocksCover (hB : BlocksCoverLowerLevel) :
    bondsNearCellsPairStatement := by
  intro F F' Y Y' q hL hL' hq hq'
  have hs : ∀ i, 2 ≤ F.extent i := fun i => by have := hq i; omega
  have hs' : ∀ i, 2 ≤ F'.extent i := fun i => by have := hq' i; omega
  have hLo : Odd F'.blockSide := by rw [hL']; exact hL
  have e : ∀ i : ↥(bondOffsets F.blockSide q), i.1 ∈ bondOffsets F'.blockSide q := fun i => by
    rw [hL']; exact i.2
  let j := chordBondAtOffsets hB hL hs Y q
  let j' : ↥(bondOffsets F.blockSide q) → ↥(chordBonds (finiteCells F')) :=
    fun i => chordBondAtOffsets hB hLo hs' Y' q ⟨i.1, e i⟩
  refine ⟨↥(bondOffsets F.blockSide q), inferInstance, inferInstance, j, j', ⟨?_, ?_⟩⟩
  swap
  · intro i
    exact ⟨i.1.1, i.1.2.1, i.1.2.2, (mem_bondOffsets i.2).1, (mem_bondOffsets i.2).2.1, rfl, rfl⟩
  refine ⟨chordBondAtOffsets_injective hB hL hs Y q hq, ?_, ?_, ?_, ?_⟩
  · intro a b hab
    have := chordBondAtOffsets_injective hB hLo hs' Y' q hq' hab
    exact Subtype.ext (congrArg (fun c : ↥(bondOffsets F'.blockSide q) => c.1) this)
  · intro b
    constructor
    · exact exists_chordBondAtOffsets_eq hB hL hs Y q hq b
    · rintro ⟨i, rfl⟩
      exact chordBondAtOffsets_mem_bondsNearCell hB hL hs Y q hq i
  · intro b
    constructor
    · intro hb
      obtain ⟨i, hi⟩ := exists_chordBondAtOffsets_eq hB hLo hs' Y' q hq' b hb
      exact ⟨⟨i.1, by rw [← hL']; exact i.2⟩, hi⟩
    · rintro ⟨i, rfl⟩
      exact chordBondAtOffsets_mem_bondsNearCell hB hLo hs' Y' q hq' _
  · intro i
    exact ⟨i.1.1, i.1.2.1, i.1.2.2, (mem_bondOffsets i.2).2.1, rfl, rfl⟩
end TorusComparison
end YangMills.Construction
end
