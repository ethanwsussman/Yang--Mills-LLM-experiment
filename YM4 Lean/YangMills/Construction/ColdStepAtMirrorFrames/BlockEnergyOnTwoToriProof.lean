import YangMills.Construction.ColdChainAtEveryLevel.EvaluationsOfAChain
import YangMills.Construction.ColdStepAtMirrorFrames.BlockEnergyOnTwoTori
import YangMills.Construction.ColdStepAtMirrorFrames.ColdChainOneLevelBelow
import YangMills.Construction.ColdStepAtMirrorFrames.OffsetsInABlock
import YangMills.Construction.ColdStepAtMirrorFrames.SitesOfABlock
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open BlockAverages
namespace ColdStepAtMirrorFrames
namespace TwoTori
open BlockOffsets
variable {F F' : BlockFrame}
abbrev LatticeOffset : Type := Fin 4 → ℤ
def siteAtOffset (Y : F.Cell) (p : LatticeOffset) : F.Site F.depth :=
  cellCentre F.depth Y + siteOfCoords F.depth p
def NearBox (L r : ℕ) (p : LatticeOffset) : Prop := ∀ i, |p i| ≤ (L : ℤ) * r + halfSide L
theorem cast_eq_two_mul_halfSide_add_one {L : ℕ} (hL : Odd L) : (L : ℤ) = 2 * halfSide L + 1 := by
  obtain ⟨k, hk⟩ := hL
  unfold halfSide
  subst hk
  push_cast
  omega
theorem exists_block_decomposition {L : ℕ} (hL : Odd L) (p : LatticeOffset) :
    ∃ g q : LatticeOffset, q ∈ centredCube L ∧ ∀ i, p i = (L : ℤ) * g i + q i := by
  have hL0 : (0 : ℤ) < L := by exact_mod_cast hL.pos
  have e := cast_eq_two_mul_halfSide_add_one hL
  refine ⟨fun i => (p i + halfSide L) / L, fun i => (p i + halfSide L) % L - halfSide L, ?_, ?_⟩
  · rw [mem_centredCube_iff]
    intro i
    have h1 := Int.emod_nonneg (p i + halfSide L) hL0.ne'
    have h2 := Int.emod_lt_of_pos (p i + halfSide L) hL0
    constructor <;> linarith
  · intro i
    have := Int.mul_ediv_add_emod (p i + halfSide L) L
    simp only
    linarith
theorem abs_quotient_le_of_nearBox {L : ℕ} (hL : Odd L) {r : ℕ} {x g q : ℤ} (hx : x = L * g + q)
    (hq1 : -halfSide L ≤ q) (hq2 : q ≤ halfSide L) (hn : |x| ≤ (L : ℤ) * r + halfSide L) : |g| ≤ (r : ℤ) := by
  have e := cast_eq_two_mul_halfSide_add_one hL
  have hL0 : (0 : ℤ) < L := by exact_mod_cast hL.pos
  obtain ⟨h1, h2⟩ := abs_le.1 hn
  rw [abs_le]
  constructor
  · by_contra hc
    have h3 : g ≤ -(r : ℤ) - 1 := by omega
    have h4 := mul_le_mul_of_nonneg_left h3 hL0.le
    nlinarith
  · by_contra hc
    have h3 : (r : ℤ) + 1 ≤ g := by omega
    have h4 := mul_le_mul_of_nonneg_left h3 hL0.le
    nlinarith
theorem siteAtOffset_blockSplit (Y : F.Cell) (g q : LatticeOffset) :
    siteAtOffset Y (fun i => (F.blockSide : ℤ) * g i + q i) =
      cellCentre F.depth (Y + siteOfCoords F.top g) + siteOfCoords F.depth q := by
  unfold siteAtOffset
  rw [cellCentre_add F.depth (by simp [BlockFrame.top]), top_sub_depth, add_assoc, ← siteOfCoords_add]
  congr 2
  funext i
  simp
theorem mem_sitesOfCells_finiteCells (hL : Odd F.blockSide) (hs : ∀ i, 2 ≤ F.extent i) (x : F.Site F.depth) :
    x ∈ sitesOfCells (finiteCells F) F.depth := by
  obtain ⟨g, q, hq, hp⟩ := exists_block_decomposition hL (siteCoords x)
  refine mem_sitesOfCells.2 ⟨0 + siteOfCoords F.top g, mem_finiteCells hs _, q, ?_, ?_⟩
  · rw [top_sub_depth, pow_one]
    exact hq
  · rw [← siteAtOffset_blockSplit]
    have hc : (cellCentre F.depth (0 : F.Cell) : F.Site F.depth) = 0 := by
      funext i
      simp [cellCentre, siteCoords, siteOfCoords]
    unfold siteAtOffset
    rw [hc, zero_add, ← funext hp]
    funext i
    simp [siteOfCoords, siteCoords]
theorem fineBondAt_mem_chordBonds (hL : Odd F.blockSide) (hs : ∀ i, 2 ≤ F.extent i) (Y : F.Cell)
    (g q : LatticeOffset) (j : Fin 4)
    (ht : ¬ IsAxialTreeBond (fineBondAt Y g q j)) : fineBondAt Y g q j ∈ chordBonds (finiteCells F) := by
  simp only [chordBonds, innerBonds, Finset.mem_filter, Finset.mem_product, Finset.mem_univ, and_true]
  exact ⟨⟨mem_sitesOfCells_finiteCells hL hs _, mem_sitesOfCells_finiteCells hL hs _⟩, ht⟩
theorem withinRadius_add_single {L r : ℕ} (hL : Odd L) {p g q : LatticeOffset} {j : Fin 4}
    (hp : ∀ i, p i = (L : ℤ) * g i + q i)
    (hq : q ∈ centredCube L) (hg : WithinRadius r g) (hp' : NearBox L r (p + Pi.single j 1))
    (hqj : q j = halfSide L) :
    WithinRadius r (g + Pi.single j 1) := by
  have e := cast_eq_two_mul_halfSide_add_one hL
  intro i
  by_cases hij : i = j
  · subst hij
    have h1 := hp' i
    simp only [Pi.add_apply, Pi.single_eq_same] at h1 ⊢
    refine abs_quotient_le_of_nearBox hL (q := - halfSide L) ?_ le_rfl ?_ h1
    · rw [hp i, hqj]
      linarith
    · have := (mem_centredCube_iff q).1 hq i
      omega
  · have h1 := hg i
    simpa [Pi.single_eq_of_ne hij] using h1
theorem chartedField_eq {L r : ℕ} (hF : F.blockSide = L) (hF' : F'.blockSide = L) (hL : Odd L)
    (hs : ∀ i, 2 ≤ F.extent i) (hs' : ∀ i, 2 ≤ F'.extent i)
    {w : F.Site F.depth → Fin 4 → imaginaryQuaternions} {w' : F'.Site F'.depth → Fin 4 → imaginaryQuaternions}
    {V : F.GaugeField F.top} {V' : F'.GaugeField F'.top} {Y : F.Cell} {Y' : F'.Cell}
    (hV : ∀ b, BondWithinRadius r b → V (Y + siteOfCoords F.top b.1) b.2 = V' (Y' + siteOfCoords F'.top b.1) b.2)
    (hw : ∀ (g q : LatticeOffset) (j : Fin 4), WithinRadius r g → q ∈ centredCube L →
      fineBondAt Y g q j ∈ chordBonds (finiteCells F) →
        w (fineBondAt Y g q j).1 j = w' (fineBondAt Y' g q j).1 j)
    (p : LatticeOffset) (j : Fin 4) (hp : NearBox L r p) (hp' : NearBox L r (p + Pi.single j 1)) :
    chartedField w V (siteAtOffset Y p) j = chartedField w' V' (siteAtOffset Y' p) j := by
  obtain ⟨g, q, hq, hpq⟩ := exists_block_decomposition hL p
  have hg : WithinRadius r g := by
    intro i
    have := (mem_centredCube_iff q).1 hq i
    exact abs_quotient_le_of_nearBox hL (hpq i) this.1 this.2 (hp i)
  have hpe : p = fun i => (L : ℤ) * g i + q i := funext hpq
  have hx : siteAtOffset Y p = cellCentre F.depth (Y + siteOfCoords F.top g) + siteOfCoords F.depth q := by
    rw [hpe, ← hF]
    exact siteAtOffset_blockSplit Y g q
  have hx' : siteAtOffset Y' p = cellCentre F'.depth (Y' + siteOfCoords F'.top g) + siteOfCoords F'.depth q := by
    rw [hpe, ← hF']
    exact siteAtOffset_blockSplit Y' g q
  have hqF : q ∈ centredCube F.blockSide := by rw [hF]; exact hq
  have hqF' : q ∈ centredCube F'.blockSide := by rw [hF']; exact hq
  have hLF : Odd F.blockSide := by rw [hF]; exact hL
  have hLF' : Odd F'.blockSide := by rw [hF']; exact hL
  rw [hx, hx']
  have c1 := isCrossingBond_iff hLF hs (Y + siteOfCoords F.top g) q hqF j
  have c2 := isCrossingBond_iff hLF' hs' (Y' + siteOfCoords F'.top g) q hqF' j
  rw [hF] at c1
  rw [hF'] at c2
  have o1 := cellOffset_offset hLF hs (Y + siteOfCoords F.top g) q hqF
  have o2 := cellOffset_offset hLF' hs' (Y' + siteOfCoords F'.top g) q hqF'
  have e1 := enclosingCell_offset hLF hs (Y + siteOfCoords F.top g) q hqF
  have e2 := enclosingCell_offset hLF' hs' (Y' + siteOfCoords F'.top g) q hqF'
  have hwq : ¬ IsAxialTreeBond (fineBondAt Y g q j) →
      w (fineBondAt Y g q j).1 j = w' (fineBondAt Y' g q j).1 j :=
    fun ht => hw g q j hg hq (fineBondAt_mem_chordBonds hLF hs Y g q j ht)
  simp only [fineBondAt] at hwq
  unfold chartedField
  by_cases hc : q j = halfSide L
  · rw [if_pos (c1.2 hc), if_pos (c2.2 hc), e1, e2, hwq (fun ht => ht.1 (c1.2 hc))]
    have := hV (g, j) ⟨hg, withinRadius_add_single hL hpq hq hg hp' hc⟩
    simp only at this
    rw [this]
  · have n1 : ¬ IsCrossingBond ((cellCentre F.depth (Y + siteOfCoords F.top g) + siteOfCoords F.depth q :
        F.Site F.depth), j) :=
      fun h => hc (c1.1 h)
    have n2 : ¬ IsCrossingBond ((cellCentre F'.depth (Y' + siteOfCoords F'.top g) + siteOfCoords F'.depth q :
        F'.Site F'.depth), j) :=
      fun h => hc (c2.1 h)
    rw [if_neg n1, if_neg n2]
    by_cases ht : ∀ l, j < l → q l = 0
    · have t1 : IsAxialTreeBond ((cellCentre F.depth (Y + siteOfCoords F.top g) + siteOfCoords F.depth q :
          F.Site F.depth), j) :=
        ⟨n1, fun l hl => by simp only; rw [o1]; exact ht l hl⟩
      have t2 : IsAxialTreeBond ((cellCentre F'.depth (Y' + siteOfCoords F'.top g) + siteOfCoords F'.depth q :
          F'.Site F'.depth), j) :=
        ⟨n2, fun l hl => by simp only; rw [o2]; exact ht l hl⟩
      rw [if_pos t1, if_pos t2]
    · have t1 : ¬ IsAxialTreeBond ((cellCentre F.depth (Y + siteOfCoords F.top g) + siteOfCoords F.depth q :
          F.Site F.depth), j) := by
        intro h
        apply ht
        intro l hl
        have := h.2 l hl
        simp only at this
        rwa [o1] at this
      have t2 : ¬ IsAxialTreeBond ((cellCentre F'.depth (Y' + siteOfCoords F'.top g) + siteOfCoords F'.depth q :
          F'.Site F'.depth), j) := by
        intro h
        apply ht
        intro l hl
        have := h.2 l hl
        simp only at this
        rwa [o2] at this
      rw [if_neg t1, if_neg t2, hwq t1]
theorem pathHolonomy_eq_of_agree {Y : F.Cell} {Y' : F'.Cell} {X : F.GaugeField F.depth}
    {X' : F'.GaugeField F'.depth} {P : LatticeOffset → Prop}
    (h : ∀ v k, P v → P (v + LatticeFractionalIntegration.basisVector k) →
      X (siteAtOffset Y v) k = X' (siteAtOffset Y' v) k) :
    ∀ (l : List PathStep) (v : LatticeOffset), LatticePaths.AllAlong P v l →
      pathHolonomy X (siteAtOffset Y v) l = pathHolonomy X' (siteAtOffset Y' v) l := by
  intro l
  induction l with
  | nil => intro v _; rfl
  | cons st rest ih =>
    intro v hp
    have hn : ∀ {H : BlockFrame} (Z : H.Cell),
        siteAtOffset Z v + stepDisplacement H.depth st =
          siteAtOffset Z (v + FlatPairing.stepDisplacement st) := by
      intro H Z
      unfold siteAtOffset
      rw [ChartCoordinates.stepDisplacement_eq_siteOfCoords, add_assoc, ← siteOfCoords_add]
    simp only [pathHolonomy]
    rw [hn, hn, ih _ hp.2]
    congr 1
    have h1 : P v := hp.1
    have h2 : P (v + FlatPairing.stepDisplacement st) := LatticePaths.allAlong_head hp.2
    rcases st with ⟨i, b⟩
    cases b
    · simp only [linkValue, Bool.false_eq_true, if_false]
      have e : ∀ {H : BlockFrame} (Z : H.Cell),
          siteAtOffset Z v - unitStep H.depth i = siteAtOffset Z (v + FlatPairing.stepDisplacement (i, false)) := by
        intro H Z
        rw [← hn Z]
        simp [stepDisplacement, sub_eq_add_neg]
      rw [e, e]
      have h3 : FlatPairing.stepDisplacement (i, false) + LatticeFractionalIntegration.basisVector i = 0 := by
        simp [FlatPairing.stepDisplacement]
      rw [h _ i h2 (by rw [add_assoc, h3, add_zero]; exact h1)]
    · simp only [linkValue, if_true]
      have e : FlatPairing.stepDisplacement (i, true) = LatticeFractionalIntegration.basisVector i := by
        simp [FlatPairing.stepDisplacement]
      rw [e] at h2
      rw [h _ i h1 h2]
theorem refineSite_eq_cellCentre (Y : F.Cell) : refineSite Y = cellCentre F.depth Y := by apply _root_.YangMills.Construction.GaugeFixing.refineSite_eq_cellCentre <;> assumption
theorem refineSite_add_eq_siteAtOffset (Y : F.Cell) (g : LatticeOffset) :
    refineSite (Y + siteOfCoords F.top g) =
      siteAtOffset Y ((0 : LatticeOffset) + fun i => (F.blockSide : ℤ) * g i) := by
  rw [zero_add]
  exact (refineSite_add (F := F) F.depth le_rfl Y g).trans (by rw [refineSite_eq_cellCentre Y]; rfl)
theorem contourAverage_eq_of_agree {L : ℕ} (hF : F.blockSide = L) (hF' : F'.blockSide = L) (hL : Odd L)
    {Y : F.Cell} {Y' : F'.Cell} {X : F.GaugeField F.depth} {X' : F'.GaugeField F'.depth}
    (g : LatticeOffset) (d : Fin 4)
    (h : ∀ v k, (v - fun i => (L : ℤ) * g i) ∈ FlatPairing.twoBlockHull L d →
      (v + LatticeFractionalIntegration.basisVector k - fun i => (L : ℤ) * g i) ∈ FlatPairing.twoBlockHull L d →
      X (siteAtOffset Y v) k = X' (siteAtOffset Y' v) k) :
    contourAverage X ((Y + siteOfCoords F.top g, d) : F.Site (F.depth + 1) × Fin 4) =
      contourAverage X' ((Y' + siteOfCoords F'.top g, d) : F'.Site (F'.depth + 1) × Fin 4) := by
  unfold contourAverage
  simp only [hF, hF']
  congr 1
  refine Finset.sum_congr rfl fun a ha => Finset.sum_congr rfl fun π _ => ?_
  have hp := LatticePaths.allAlong_add (w := fun i => (L : ℤ) * g i)
    (LatticePaths.bondContour_spec π d hL.pos ha).1
  have := pathHolonomy_eq_of_agree (Y := Y) (Y' := Y') (X := X) (X' := X') h _ _ hp
  rw [refineSite_add_eq_siteAtOffset, refineSite_add_eq_siteAtOffset, hF, hF', this]
theorem nearBox_of_mem_twoBlockHull {L r : ℕ} (hL : Odd L) {g v : LatticeOffset} {d : Fin 4}
    (hg : WithinRadius r g) (hg' : WithinRadius r (g + Pi.single d 1))
    (hv : (v - fun i => (L : ℤ) * g i) ∈ FlatPairing.twoBlockHull L d) :
    NearBox L r v := by
  intro i
  have hL0 : (0 : ℤ) < L := by exact_mod_cast hL.pos
  have h1 := hv i
  have eh : ((L : ℤ) - 1) / 2 = halfSide L := rfl
  simp only [Pi.sub_apply] at h1
  rw [eh] at h1
  have b1 := abs_le.1 (hg i)
  rw [abs_le]
  by_cases hi : i = d
  · subst hi
    have b2 := abs_le.1 (hg' i)
    simp only [Pi.add_apply, Pi.single_eq_same] at b2
    simp only [if_true] at h1
    have m1 := mul_le_mul_of_nonneg_left b1.1 hL0.le
    have m2 := mul_le_mul_of_nonneg_left b2.2 hL0.le
    constructor <;> nlinarith
  · simp only [hi, if_false, add_zero] at h1
    have m1 := mul_le_mul_of_nonneg_left b1.1 hL0.le
    have m2 := mul_le_mul_of_nonneg_left b1.2 hL0.le
    constructor <;> nlinarith
theorem blockFit_eq_of_agree {L r : ℕ} (hF : F.blockSide = L) (hF' : F'.blockSide = L) (hL : Odd L)
    (hs : ∀ i, 2 ≤ F.extent i) (hs' : ∀ i, 2 ≤ F'.extent i)
    {w : F.Site F.depth → Fin 4 → imaginaryQuaternions} {w' : F'.Site F'.depth → Fin 4 → imaginaryQuaternions}
    {V : F.GaugeField F.top} {V' : F'.GaugeField F'.top} {Y : F.Cell} {Y' : F'.Cell}
    (hV : ∀ b, BondWithinRadius r b → V (Y + siteOfCoords F.top b.1) b.2 = V' (Y' + siteOfCoords F'.top b.1) b.2)
    (hw : ∀ (g q : LatticeOffset) (j : Fin 4), WithinRadius r g → q ∈ centredCube L →
      fineBondAt Y g q j ∈ chordBonds (finiteCells F) →
        w (fineBondAt Y g q j).1 j = w' (fineBondAt Y' g q j).1 j)
    (g : LatticeOffset) (d : Fin 4) (hg : WithinRadius r g) (hg' : WithinRadius r (g + Pi.single d 1)) :
    blockFit (chartedField w V) V ((Y + siteOfCoords F.top g, d) : F.Site (F.depth + 1) × Fin 4) =
      blockFit (chartedField w' V') V' ((Y' + siteOfCoords F'.top g, d) : F'.Site (F'.depth + 1) × Fin 4) := by
  have hm := contourAverage_eq_of_agree hF hF' hL (Y := Y) (Y' := Y') (X := chartedField w V)
    (X' := chartedField w' V') g d
    (fun v k h1 h2 => chartedField_eq hF hF' hL hs hs' hV hw v k (nearBox_of_mem_twoBlockHull hL hg hg' h1)
      (nearBox_of_mem_twoBlockHull hL hg hg' h2))
  have hv := hV (g, d) ⟨hg, hg'⟩
  simp only at hv
  unfold blockFit
  simp only
  rw [hm, hv]
theorem sum_innerBonds_eq_of_support (hs : ∀ i, 2 ≤ F.extent i) (D : F.Site (F.depth + 1) × Fin 4 → ℝ)
    (Cx : F.Cell)
    (hD : ∀ c : F.Site (F.depth + 1) × Fin 4, Cx ≠ c.1 → Cx ≠ c.1 + unitStep F.top c.2 → D c = 0) :
    ∑ c ∈ innerBonds (finiteCells F) (F.depth + 1), D c =
      ∑ d : Fin 4, (D (Cx, d) + D (Cx - unitStep F.top d, d)) := by
  have hB : innerBonds (finiteCells F) (F.depth + 1) = finiteCells F ×ˢ Finset.univ := by
    ext c
    simp only [innerBonds, Finset.mem_filter, Finset.mem_product, Finset.mem_univ, and_true]
    constructor
    · rintro ⟨h, _⟩
      exact mem_sitesOfCells_top.1 h
    · intro h
      exact ⟨mem_sitesOfCells_top.2 h, mem_sitesOfCells_top.2 (mem_finiteCells hs _)⟩
  rw [hB, Finset.sum_product_right]
  refine Finset.sum_congr rfl fun d _ => ?_
  refine Finset.sum_eq_add Cx (Cx - unitStep F.top d) ?_ ?_ ?_ ?_
  · intro h
    apply unitStep_top_ne_zero hs d
    have h2 : Cx - unitStep F.top d = Cx := h.symm
    exact sub_eq_self.1 h2
  · intro z _ hz
    apply hD (z, d)
    · exact fun h => hz.1 h.symm
    · intro h
      apply hz.2
      simp only at h
      rw [h]
      simp
  · intro h
    exact (h (mem_finiteCells hs _)).elim
  · intro h
    exact (h (mem_finiteCells hs _)).elim
theorem bondDeriv_zero_order {G : F.GaugeField F.depth → ℝ} (W : F.GaugeField F.depth)
    (c : Fin 0 → F.Site F.depth × Fin 4) (X : Fin 0 → imaginaryQuaternions) :
    bondDeriv G W c X = G W := by
  unfold bondDeriv
  rw [iteratedFDeriv_zero_apply]
  congr 1
  funext y i
  have h0 : expUnit 0 = 1 := by
    apply Subtype.ext
    simp [expUnit]
  simp [leftTranslate, bondSpread, h0]
theorem sum_cell_sites (hS : SiteDecomposition) (hL : Odd F.blockSide) (hs : ∀ i, 2 ≤ F.extent i) (Y : F.Cell)
    (f : F.Site F.depth → ℝ) [DecidablePred fun y : F.Site F.depth => enclosingCell y = Y] :
    ∑ y ∈ (sitesOfCells (finiteCells F) F.depth).filter (fun y => enclosingCell y = Y), f y =
      ∑ o ∈ centredCube F.blockSide, f (siteAtOffset Y o) := by
  obtain ⟨h1, h2, -, -⟩ := hS F hL hs
  refine Finset.sum_bij' (fun y _ => cellOffset y) (fun o _ => siteAtOffset Y o) ?_ ?_ ?_ ?_ ?_
  · intro y _
    exact (h2 y).2
  · intro o ho
    exact Finset.mem_filter.mpr ⟨mem_sitesOfCells_finiteCells hL hs _, (h1 Y o ho).1⟩
  · intro y hy
    have e := (Finset.mem_filter.mp hy).2
    unfold siteAtOffset
    rw [← e]
    exact (h2 y).1
  · intro o ho
    exact (h1 Y o ho).2
  · intro y hy
    have e := (Finset.mem_filter.mp hy).2
    unfold siteAtOffset
    rw [← e, (h2 y).1]
theorem sum_bonds_at_cell (hs : ∀ i, 2 ≤ F.extent i) (Y : F.Cell) (D : F.Site (F.depth + 1) × Fin 4 → ℝ)
    [DecidablePred fun c : F.Site (F.depth + 1) × Fin 4 => c.1 = Y ∨ c.1 + unitStep F.top c.2 = Y] :
    ∑ c ∈ (innerBonds (finiteCells F) (F.depth + 1)).filter
        (fun c => c.1 = Y ∨ c.1 + unitStep F.top c.2 = Y), D c =
      ∑ d : Fin 4, (D (Y, d) + D (Y - unitStep F.top d, d)) := by
  rw [Finset.sum_filter, sum_innerBonds_eq_of_support hs _ Y (fun c h1 h2 => by
    rw [if_neg]
    rintro (h | h)
    · exact h1 h.symm
    · exact h2 h.symm)]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [if_pos (Or.inl rfl), if_pos (Or.inr (by simp))]
end TwoTori
open TwoTori BlockOffsets in
theorem cellEnergyShareLocal_holds (hch : ColdEstimatesAtEveryDepth) (hS : SiteDecomposition) :
    CellEnergyShareLocal := by
  classical
  intro a L c ha hodd hL40 hc
  obtain ⟨N, hN0, hNc⟩ := hch a L c ha hodd hL40 hc
  have hσA : 0 < c.σA := hc.positivity.2.2.2.1
  obtain ⟨D, hD⟩ : ∃ D, D = c.σA ^ 2 * N 0 := ⟨_, rfl⟩
  have hD0 : 0 < D := by
    have := hN0 0
    rw [hD]
    positivity
  refine ⟨((centredCube L).card : ℝ) * D + 1, by positivity, ?_⟩
  intro F F' w w' V V' Y Y' r hr hT hT' ht hsm hsm' hag hww
  have hT0 := hT
  have hT0' := hT'
  obtain ⟨hF, n, hn, hside⟩ := hT
  obtain ⟨hF', n', hn', hside'⟩ := hT'
  have hs : ∀ i, 2 ≤ F.extent i := fun i => by rw [hside]; omega
  have hs' : ∀ i, 2 ≤ F'.extent i := fun i => by rw [hside']; omega
  obtain ⟨sd0, sd0', -, hV⟩ := hag
  have sd : ∀ i, 2 * r + 2 < F.extent i := fun i => by
    rcases sd0 i with h0 | h0
    · have := hs i
      omega
    · exact h0
  have sd' : ∀ i, 2 * r + 2 < F'.extent i := fun i => by
    rcases sd0' i with h0 | h0
    · have := hs' i
      omega
    · exact h0
  have hLF : Odd F.blockSide := by rw [hF]; exact hodd
  have hLF' : Odd F'.blockSide := by rw [hF']; exact hodd
  have hLpos : 0 < L := hodd.pos
  have hper : ∀ {G : BlockFrame}, G.blockSide = L → (∀ i, 2 * r + 2 < G.extent i) →
      ∀ i, 2 * r + 2 < G.period G.depth i := by
    intro G hG hg i
    rw [period_depth, hG]
    have := hg i
    nlinarith
  have hnear : ∀ (o : LatticeOffset) (u : LatticeOffset), o ∈ centredCube L → WithinRadius r u →
      NearBox L r (o + u) := by
    intro o u ho hu i
    have h1 := (mem_centredCube_iff o).1 ho i
    have h2 := abs_le.1 (hu i)
    have h3 : (r : ℤ) ≤ (L : ℤ) * r := by
      have : (1 : ℤ) ≤ L := by exact_mod_cast hLpos
      nlinarith
    simp only [Pi.add_apply]
    rw [abs_le]
    constructor <;> omega
  have hsh : ∀ o ∈ centredCube L,
      |minimalSiteShare a (siteAtOffset Y o) (chartedField w V) -
          minimalSiteShare a (siteAtOffset Y' o) (chartedField w' V')| ≤
        D * Real.exp (-c.δ₁ * r) := by
    intro o ho
    have hag2 : AgreeOnBox (chartedField w V) (chartedField w' V') (siteAtOffset Y o) (siteAtOffset Y' o) r := by
      refine ⟨hper hF sd, hper hF' sd', fun b hb => ?_⟩
      have hsite : ∀ {G : BlockFrame} (Z : G.Cell),
          siteAtOffset Z o + siteOfCoords G.depth b.1 = siteAtOffset Z (o + b.1) := by
        intro G Z
        unfold siteAtOffset
        rw [add_assoc, ← siteOfCoords_add]
      rw [hsite, hsite]
      refine chartedField_eq hF hF' hodd hs hs' hV hww (o + b.1) b.2 (hnear o b.1 ho hb.1) ?_
      rw [add_assoc]
      exact hnear o _ ho hb.2
    have hcmp := hNc.2 F F' c.σA _ _ _ _ r hT0 hT0' ht hσA le_rfl hsm.small_curvature hsm'.small_curvature hag2
    have h1 := hcmp.siteShare_deriv_close 0 Fin.elim0 Fin.elim0 (fun l => l.elim0) (fun l => l.elim0)
    rw [bondDeriv_zero_order, bondDeriv_zero_order] at h1
    refine h1.trans (le_of_eq ?_)
    rw [hD]
    simp [derivativeScale]
  have hfits : ∑ cb ∈ (innerBonds (finiteCells F) F.top).filter
        (fun cb => cb.1 = Y ∨ cb.1 + unitStep F.top cb.2 = Y),
      blockFit (chartedField w V) V cb =
      ∑ cb ∈ (innerBonds (finiteCells F') F'.top).filter
        (fun cb => cb.1 = Y' ∨ cb.1 + unitStep F'.top cb.2 = Y'),
        blockFit (chartedField w' V') V' cb := by
    rw [sum_bonds_at_cell hs Y, sum_bonds_at_cell hs' Y']
    refine Finset.sum_congr rfl fun d _ => ?_
    have hz : WithinRadius r (0 : LatticeOffset) := fun i => by simp
    have he : WithinRadius r (Pi.single d 1 : LatticeOffset) := fun i => by
      by_cases hi : i = d
      · subst hi
        simpa using (by exact_mod_cast hr : (1 : ℤ) ≤ r)
      · simp [Pi.single_eq_of_ne hi]
    have hne : WithinRadius r (-(Pi.single d 1) : LatticeOffset) := fun i => by
      have := he i
      simpa using this
    have h0 := blockFit_eq_of_agree hF hF' hodd hs hs' hV hww 0 d hz (by simpa using he)
    have h1 := blockFit_eq_of_agree hF hF' hodd hs hs' hV hww (-(Pi.single d 1)) d hne (by simpa using hz)
    have t0 : ∀ {G : BlockFrame} (Z : G.Cell), Z + siteOfCoords G.top (0 : LatticeOffset) = Z := by
      intro G Z
      funext i
      simp [siteOfCoords]
    have t1 : ∀ {G : BlockFrame} (Z : G.Cell),
        Z + siteOfCoords G.top (-(Pi.single d 1) : LatticeOffset) = Z - unitStep G.top d := by
      intro G Z
      funext i
      simp [siteOfCoords, unitStep, sub_eq_add_neg]
    rw [t0, t0] at h0
    rw [t1, t1] at h1
    rw [h0, h1]
  unfold cellEnergyShare
  rw [hfits, sum_cell_sites hS hLF hs, sum_cell_sites hS hLF' hs', hF, hF', add_sub_add_right_eq_sub,
    ← Finset.sum_sub_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have hexp : Real.exp (-c.δ₁ * r) = Real.exp (-(c.δ₁ * r)) := by
    congr 1
    ring
  calc ∑ o ∈ centredCube L, |minimalSiteShare a (siteAtOffset Y o) (chartedField w V) -
          minimalSiteShare a (siteAtOffset Y' o) (chartedField w' V')|
      ≤ ∑ _o ∈ centredCube L, D * Real.exp (-c.δ₁ * r) := Finset.sum_le_sum hsh
    _ = ((centredCube L).card : ℝ) * D * Real.exp (-(c.δ₁ * r)) := by
        rw [hexp]
        simp
        ring
    _ ≤ (((centredCube L).card : ℝ) * D + 1) * Real.exp (-(c.δ₁ * r)) := by
        have := Real.exp_pos (-(c.δ₁ * r))
        nlinarith
end ColdStepAtMirrorFrames
end YangMills.Construction
end
