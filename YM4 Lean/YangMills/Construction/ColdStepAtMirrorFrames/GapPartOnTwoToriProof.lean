import YangMills.Construction.ClusterExpansionOfAStep.SitesOfTheTopOfAStep
import YangMills.Construction.ColdStepAtMirrorFrames.SlopeOfTheChartOnTwoToriProof
import YangMills.Construction.ColdChainAtEveryLevel.CompositeMeanOfTheGeneratorsProof
import YangMills.Construction.ColdStepAtMirrorFrames.BlockEnergyOnTwoToriProof
import YangMills.Construction.ColdStepAtMirrorFrames.ContourOfAChartField
import YangMills.Construction.ColdStepAtMirrorFrames.CouplingFloorOfTheFrames
import YangMills.Construction.ColdStepAtMirrorFrames.DerivativesOfTheGroupGap
import YangMills.Construction.ColdStepAtMirrorFrames.ExponentialOfTheLieAlgebra
import YangMills.Construction.ColdStepAtMirrorFrames.FramesAreLocal
import YangMills.Construction.ColdStepAtMirrorFrames.FramesAreSmall
import YangMills.Construction.ColdStepAtMirrorFrames.GapPartOnTwoTori
import YangMills.Construction.ColdStepAtMirrorFrames.GapTermsOfTheExponentProof
import YangMills.Construction.ColdStepAtMirrorFrames.GroupGapIsSmooth
import YangMills.Construction.SummableBoundsOfTheFlow.ExponentBetweenBoundsProof
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction.ColdStepAtMirrorFrames
open YangMills.Construction.BlockAverages
namespace GapComponentsOnTwoTori
open YangMills.Construction.ColdStepAtMirrorFrames.BlockOffsets
variable {F F' : BlockFrame}
private abbrev LatticeOffset : Type := Fin 4 → ℤ
private def siteAtOffset (Y : F.Cell) (p : LatticeOffset) : F.Site F.depth :=
  cellCentre F.depth Y + siteOfCoords F.depth p
private def OffsetNear (L r : ℕ) (p : LatticeOffset) : Prop := ∀ i, |p i| ≤ (L : ℤ) * r + halfSide L
private theorem cast_eq_two_mul_halfSide_add_one {L : ℕ} (hL : Odd L) : (L : ℤ) = 2 * halfSide L + 1 := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.TwoTori.cast_eq_two_mul_halfSide_add_one <;> assumption
private theorem exists_block_decomposition {L : ℕ} (hL : Odd L) (p : LatticeOffset) :
    ∃ g q : LatticeOffset, q ∈ centredCube L ∧ ∀ i, p i = (L : ℤ) * g i + q i := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.TwoTori.exists_block_decomposition <;> assumption
private theorem abs_blockIndex_le {L : ℕ} (hL : Odd L) {r : ℕ} {x g q : ℤ} (hx : x = L * g + q)
    (hq1 : -halfSide L ≤ q) (hq2 : q ≤ halfSide L) (hn : |x| ≤ (L : ℤ) * r + halfSide L) : |g| ≤ (r : ℤ) := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.TwoTori.abs_quotient_le_of_nearBox <;> assumption
private theorem siteAtOffset_block (Y : F.Cell) (g q : LatticeOffset) :
    siteAtOffset Y (fun i => (F.blockSide : ℤ) * g i + q i) =
      cellCentre F.depth (Y + siteOfCoords F.top g) + siteOfCoords F.depth q := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.TwoTori.siteAtOffset_blockSplit <;> assumption
private theorem mem_sitesOfCells_finiteCells (hL : Odd F.blockSide) (hs : ∀ i, 2 ≤ F.extent i) (x : F.Site F.depth) :
    x ∈ sitesOfCells (finiteCells F) F.depth := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.TwoTori.mem_sitesOfCells_finiteCells <;> assumption
private theorem fineBondAt_mem_chordBonds (hL : Odd F.blockSide) (hs : ∀ i, 2 ≤ F.extent i) (Y : F.Cell)
    (g q : LatticeOffset) (j : Fin 4) (ht : ¬ IsAxialTreeBond (fineBondAt Y g q j)) :
    fineBondAt Y g q j ∈ chordBonds (finiteCells F) := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.TwoTori.fineBondAt_mem_chordBonds <;> assumption
private theorem withinRadius_add_single {L r : ℕ} (hL : Odd L) {p g q : LatticeOffset} {j : Fin 4}
    (hp : ∀ i, p i = (L : ℤ) * g i + q i) (hq : q ∈ centredCube L) (hg : WithinRadius r g)
    (hp' : OffsetNear L r (p + Pi.single j 1)) (hqj : q j = halfSide L) :
    WithinRadius r (g + Pi.single j 1) := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.TwoTori.withinRadius_add_single <;> assumption
private theorem isAxialTreeBond_iff (hL : Odd F.blockSide) (hs : ∀ i, 2 ≤ F.extent i) (z : F.Cell) (q : LatticeOffset)
    (hq : q ∈ centredCube F.blockSide) (j : Fin 4) :
    IsAxialTreeBond ((cellCentre F.depth z + siteOfCoords F.depth q : F.Site F.depth), j) ↔
      q j ≠ halfSide F.blockSide ∧ ∀ l, j < l → q l = 0 := by apply _root_.YangMills.Construction.TopLevelSites.isAxialTreeBond_iff <;> assumption
private theorem norm_coe_inv_sub_coe_inv (g g' : UnitQuaternion) :
    ‖((g⁻¹ : UnitQuaternion) : ℍ[ℝ]) - ((g'⁻¹ : UnitQuaternion) : ℍ[ℝ])‖ = ‖(g : ℍ[ℝ]) - (g' : ℍ[ℝ])‖ := by apply _root_.YangMills.Construction.LumpContours.BlockLevels.norm_sub_inv_inv <;> assumption
private theorem norm_coe_mul_sub_le (g g' h h' : UnitQuaternion) :
    ‖((g * h : UnitQuaternion) : ℍ[ℝ]) - ((g' * h' : UnitQuaternion) : ℍ[ℝ])‖ ≤
      ‖(g : ℍ[ℝ]) - (g' : ℍ[ℝ])‖ + ‖(h : ℍ[ℝ]) - (h' : ℍ[ℝ])‖ := by apply _root_.YangMills.Construction.BlockAverages.ChartOverTop.coe_mul_sub_mul_le <;> assumption
private theorem chartedField_close (hexp : QuaternionExp.ExpUnitLipschitzInjective) {L r : ℕ}
    (hF : F.blockSide = L) (hF' : F'.blockSide = L) (hL : Odd L)
    (hs : ∀ i, 2 ≤ F.extent i) (hs' : ∀ i, 2 ≤ F'.extent i) {w : F.Site F.depth → Fin 4 → imaginaryQuaternions}
    {w' : F'.Site F'.depth → Fin 4 → imaginaryQuaternions} {V : F.GaugeField F.top} {V' : F'.GaugeField F'.top}
    {Y : F.Cell} {Y' : F'.Cell} {ε : ℝ}
    (hε : 0 ≤ ε)
    (hV : ∀ b, BondWithinRadius r b → V (Y + siteOfCoords F.top b.1) b.2 = V' (Y' + siteOfCoords F'.top b.1) b.2)
    (hw : ∀ (g q : LatticeOffset) (j : Fin 4), WithinRadius r g → q ∈ centredCube L →
      fineBondAt Y g q j ∈ chordBonds (finiteCells F) →
      ‖((w (fineBondAt Y g q j).1 j : imaginaryQuaternions) : ℍ[ℝ]) -
        ((w' (fineBondAt Y' g q j).1 j : imaginaryQuaternions) : ℍ[ℝ])‖ ≤ ε)
    (p : LatticeOffset) (j : Fin 4) (hp : OffsetNear L r p) (hp' : OffsetNear L r (p + Pi.single j 1)) :
    ‖((chartedField w V (siteAtOffset Y p) j : UnitQuaternion) : ℍ[ℝ]) -
      ((chartedField w' V' (siteAtOffset Y' p) j : UnitQuaternion) : ℍ[ℝ])‖ ≤ ε := by
  obtain ⟨g, q, hq, hpq⟩ := exists_block_decomposition hL p
  have hg : WithinRadius r g := by
    intro i
    have := (BlockOffsets.mem_centredCube_iff q).1 hq i
    exact abs_blockIndex_le hL (hpq i) this.1 this.2 (hp i)
  have hpe : p = fun i => (L : ℤ) * g i + q i := funext hpq
  have hx : siteAtOffset Y p = cellCentre F.depth (Y + siteOfCoords F.top g) + siteOfCoords F.depth q := by
    rw [hpe, ← hF]
    exact siteAtOffset_block Y g q
  have hx' : siteAtOffset Y' p = cellCentre F'.depth (Y' + siteOfCoords F'.top g) + siteOfCoords F'.depth q := by
    rw [hpe, ← hF']
    exact siteAtOffset_block Y' g q
  have hqF : q ∈ centredCube F.blockSide := by rw [hF]; exact hq
  have hqF' : q ∈ centredCube F'.blockSide := by rw [hF']; exact hq
  have hLF : Odd F.blockSide := by rw [hF]; exact hL
  have hLF' : Odd F'.blockSide := by rw [hF']; exact hL
  rw [hx, hx']
  have c1 := isCrossingBond_iff hLF hs (Y + siteOfCoords F.top g) q hqF j
  have c2 := isCrossingBond_iff hLF' hs' (Y' + siteOfCoords F'.top g) q hqF' j
  rw [hF] at c1
  rw [hF'] at c2
  have t1 := isAxialTreeBond_iff hLF hs (Y + siteOfCoords F.top g) q hqF j
  have t2 := isAxialTreeBond_iff hLF' hs' (Y' + siteOfCoords F'.top g) q hqF' j
  rw [hF] at t1
  rw [hF'] at t2
  have e1 := enclosingCell_offset hLF hs (Y + siteOfCoords F.top g) q hqF
  have e2 := enclosingCell_offset hLF' hs' (Y' + siteOfCoords F'.top g) q hqF'
  have hwq : ¬ IsAxialTreeBond (fineBondAt Y g q j) →
      ‖((w (fineBondAt Y g q j).1 j : imaginaryQuaternions) : ℍ[ℝ]) -
        ((w' (fineBondAt Y' g q j).1 j : imaginaryQuaternions) : ℍ[ℝ])‖ ≤ ε :=
    fun ht => hw g q j hg hq (fineBondAt_mem_chordBonds hLF hs Y g q j ht)
  simp only [fineBondAt] at hwq
  have hE : ∀ v v' : imaginaryQuaternions, ‖(v : ℍ[ℝ]) - (v' : ℍ[ℝ])‖ ≤ ε →
      ‖((expUnit v : UnitQuaternion) : ℍ[ℝ]) - ((expUnit v' : UnitQuaternion) : ℍ[ℝ])‖ ≤ ε :=
    fun v v' h => (hexp.1 v v').trans h
  unfold chartedField
  by_cases hc : q j = halfSide L
  · have ht : ¬ IsAxialTreeBond ((cellCentre F.depth (Y + siteOfCoords F.top g) + siteOfCoords F.depth q :
        F.Site F.depth), j) :=
      fun h => h.1 (c1.2 hc)
    rw [if_pos (c1.2 hc), if_pos (c2.2 hc), e1, e2]
    have hvv := hV (g, j) ⟨hg, withinRadius_add_single hL hpq hq hg hp' hc⟩
    simp only at hvv
    rw [hvv]
    refine (norm_coe_mul_sub_le _ _ _ _).trans ?_
    simp only [sub_self, norm_zero, add_zero]
    exact hE _ _ (hwq ht)
  · have n1 : ¬ IsCrossingBond ((cellCentre F.depth (Y + siteOfCoords F.top g) + siteOfCoords F.depth q :
        F.Site F.depth), j) :=
      fun h => hc (c1.1 h)
    have n2 : ¬ IsCrossingBond ((cellCentre F'.depth (Y' + siteOfCoords F'.top g) + siteOfCoords F'.depth q :
        F'.Site F'.depth), j) :=
      fun h => hc (c2.1 h)
    rw [if_neg n1, if_neg n2]
    by_cases ht : ∀ l, j < l → q l = 0
    · rw [if_pos (t1.2 ⟨hc, ht⟩), if_pos (t2.2 ⟨hc, ht⟩)]
      simpa using hε
    · have u1 : ¬ IsAxialTreeBond ((cellCentre F.depth (Y + siteOfCoords F.top g) + siteOfCoords F.depth q :
          F.Site F.depth), j) :=
        fun h => ht (t1.1 h).2
      have u2 : ¬ IsAxialTreeBond ((cellCentre F'.depth (Y' + siteOfCoords F'.top g) + siteOfCoords F'.depth q :
          F'.Site F'.depth), j) :=
        fun h => ht (t2.1 h).2
      rw [if_neg u1, if_neg u2]
      exact hE _ _ (hwq u1)
private theorem pathHolonomy_close {Y : F.Cell} {Y' : F'.Cell} {X : F.GaugeField F.depth} {X' : F'.GaugeField F'.depth}
    {P : LatticeOffset → Prop} {ε : ℝ}
    (h : ∀ v k, P v → P (v + LatticeFractionalIntegration.basisVector k) →
      ‖((X (siteAtOffset Y v) k : UnitQuaternion) : ℍ[ℝ]) - ((X' (siteAtOffset Y' v) k : UnitQuaternion) : ℍ[ℝ])‖ ≤ ε) :
    ∀ (l : List PathStep) (v : LatticeOffset), LatticePaths.AllAlong P v l →
      ‖((pathHolonomy X (siteAtOffset Y v) l : UnitQuaternion) : ℍ[ℝ]) -
        ((pathHolonomy X' (siteAtOffset Y' v) l : UnitQuaternion) : ℍ[ℝ])‖ ≤ l.length * ε := by
  intro l
  induction l with
  | nil => intro v _; simp [pathHolonomy]
  | cons st r ih =>
    intro v hp
    have hn : ∀ {H : BlockFrame} (Z : H.Cell),
        siteAtOffset Z v + stepDisplacement H.depth st = siteAtOffset Z (v + FlatPairing.stepDisplacement st) := by
      intro H Z
      unfold siteAtOffset
      rw [ChartCoordinates.stepDisplacement_eq_siteOfCoords, add_assoc, ← _root_.YangMills.Construction.BlockAverages.siteOfCoords_add]
    simp only [pathHolonomy]
    rw [hn, hn]
    have h1 : P v := hp.1
    have h2 : P (v + FlatPairing.stepDisplacement st) := LatticePaths.allAlong_head hp.2
    have hstep : ‖((linkValue X (siteAtOffset Y v) st : UnitQuaternion) : ℍ[ℝ]) -
        ((linkValue X' (siteAtOffset Y' v) st : UnitQuaternion) : ℍ[ℝ])‖ ≤ ε := by
      rcases st with ⟨i, b⟩
      cases b
      · simp only [linkValue, Bool.false_eq_true, if_false]
        have e : ∀ {H : BlockFrame} (Z : H.Cell),
            siteAtOffset Z v - unitStep H.depth i = siteAtOffset Z (v + FlatPairing.stepDisplacement (i, false)) := by
          intro H Z
          rw [← hn Z]
          simp [stepDisplacement, sub_eq_add_neg]
        rw [e, e, norm_coe_inv_sub_coe_inv]
        have h3 : FlatPairing.stepDisplacement (i, false) + LatticeFractionalIntegration.basisVector i = 0 := by
          simp [FlatPairing.stepDisplacement]
        exact h _ i h2 (by rw [add_assoc, h3, add_zero]; exact h1)
      · simp only [linkValue, if_true]
        have e : FlatPairing.stepDisplacement (i, true) = LatticeFractionalIntegration.basisVector i := by
          simp [FlatPairing.stepDisplacement]
        rw [e] at h2
        exact h _ i h1 h2
    refine (norm_coe_mul_sub_le _ _ _ _).trans ?_
    have := ih _ hp.2
    simp only [List.length_cons]
    push_cast
    linarith
private theorem refineSite_eq_cellCentre (Y : F.Cell) : _root_.YangMills.Construction.BlockAverages.refineSite Y = cellCentre F.depth Y := by apply _root_.YangMills.Construction.GaugeFixing.refineSite_eq_cellCentre <;> assumption
private theorem refineSite_add_eq_siteAtOffset (Y : F.Cell) (g : LatticeOffset) :
    _root_.YangMills.Construction.BlockAverages.refineSite (Y + siteOfCoords F.top g) =
      siteAtOffset Y ((0 : LatticeOffset) + fun i => (F.blockSide : ℤ) * g i) := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.TwoTori.refineSite_add_eq_siteAtOffset <;> assumption
private def blockMean (L : ℕ) (z : LatticeOffset → Equiv.Perm (Fin 4) → ℍ[ℝ]) : ℍ[ℝ] :=
  (1 / (24 * (L : ℝ) ^ 4)) • ∑ h ∈ centredCube L, ∑ π : Equiv.Perm (Fin 4), z h π
private theorem card_centredCube_real (M : ℕ) (hM : Odd M) : ((centredCube M).card : ℝ) = (M : ℝ) ^ 4 := by apply _root_.YangMills.Construction.BlockAverages.GeneratorMeans.card_centredCube_real <;> assumption
private theorem sum_one_centredCube_perm {L : ℕ} (hL : Odd L) :
    ∑ _h ∈ centredCube L, ∑ _π : Equiv.Perm (Fin 4), (1 : ℝ) = 24 * (L : ℝ) ^ 4 := by
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one, Finset.card_univ, Fintype.card_perm, Fintype.card_fin]
  rw [card_centredCube_real _ hL]
  norm_num
  ring
private theorem norm_blockMean_sub_le {L : ℕ} (hL : Odd L) {z z' : LatticeOffset → Equiv.Perm (Fin 4) → ℍ[ℝ]} {B : ℝ}
    (h : ∀ a ∈ centredCube L, ∀ π, ‖z a π - z' a π‖ ≤ B) : ‖blockMean L z - blockMean L z'‖ ≤ B := by
  have hLpos : (0 : ℝ) < L := by exact_mod_cast hL.pos
  have e : blockMean L z - blockMean L z' =
      (1 / (24 * (L : ℝ) ^ 4)) • ∑ a ∈ centredCube L, ∑ π : Equiv.Perm (Fin 4), (z a π - z' a π) := by
    simp only [blockMean, Finset.sum_sub_distrib, smul_sub]
  rw [e, norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity)]
  have h2 : ‖∑ a ∈ centredCube L, ∑ π : Equiv.Perm (Fin 4), (z a π - z' a π)‖ ≤
      ∑ _a ∈ centredCube L, ∑ _π : Equiv.Perm (Fin 4), B :=
    (norm_sum_le _ _).trans (Finset.sum_le_sum fun a ha =>
      (norm_sum_le _ _).trans (Finset.sum_le_sum fun π _ => h a ha π))
  have h3 : ∑ _a ∈ centredCube L, ∑ _π : Equiv.Perm (Fin 4), B = 24 * (L : ℝ) ^ 4 * B := by
    rw [← sum_one_centredCube_perm hL, Finset.sum_mul]
    refine Finset.sum_congr rfl fun _ _ => ?_
    rw [Finset.sum_mul]
    simp
  rw [h3] at h2
  calc 1 / (24 * (L : ℝ) ^ 4) * _ ≤ 1 / (24 * (L : ℝ) ^ 4) * (24 * (L : ℝ) ^ 4 * B) :=
        mul_le_mul_of_nonneg_left h2 (by positivity)
    _ = B := by field_simp
private theorem contourAverage_norm_bounds (hL : Odd F.blockSide) (W : F.GaugeField F.depth) (V : F.GaugeField F.top)
    (c : F.Site F.top × Fin 4)
    (h : ∀ (h : Fin 4 → ℤ) (π : Equiv.Perm (Fin 4)), h ∈ centredCube F.blockSide →
      ‖contourHolonomyDefect W V c h π - 1‖ ≤ 1 / 2) :
    1 / 2 ≤ ‖_root_.YangMills.Construction.BlockAverages.contourAverage W c‖ ∧ ‖_root_.YangMills.Construction.BlockAverages.contourAverage W c‖ ≤ 1 := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.GapTerms.norm_contourAverage_mem_shell <;> assumption
private theorem contourAverage_close {L : ℕ} (hF : F.blockSide = L) (hF' : F'.blockSide = L) (hL : Odd L)
    {Y : F.Cell} {Y' : F'.Cell}
    {X : F.GaugeField F.depth} {X' : F'.GaugeField F'.depth} (g : LatticeOffset) (d : Fin 4) {ε : ℝ} (hε : 0 ≤ ε)
    (h : ∀ v k, (v - fun i => (L : ℤ) * g i) ∈ FlatPairing.twoBlockHull L d →
      (v + LatticeFractionalIntegration.basisVector k - fun i => (L : ℤ) * g i) ∈ FlatPairing.twoBlockHull L d →
      ‖((X (siteAtOffset Y v) k : UnitQuaternion) : ℍ[ℝ]) - ((X' (siteAtOffset Y' v) k : UnitQuaternion) : ℍ[ℝ])‖ ≤ ε) :
    ‖_root_.YangMills.Construction.BlockAverages.contourAverage X ((Y + siteOfCoords F.top g, d) : F.Site (F.depth + 1) × Fin 4) -
      _root_.YangMills.Construction.BlockAverages.contourAverage X' ((Y' + siteOfCoords F'.top g, d) : F'.Site (F'.depth + 1) × Fin 4)‖ ≤ 5 * (L : ℝ) * ε := by
  have e1 : _root_.YangMills.Construction.BlockAverages.contourAverage X ((Y + siteOfCoords F.top g, d) : F.Site (F.depth + 1) × Fin 4) =
      blockMean L (fun a π => ((pathHolonomy X (_root_.YangMills.Construction.BlockAverages.refineSite (Y + siteOfCoords F.top g)) (bondContour L a π d) :
        UnitQuaternion) : ℍ[ℝ])) := by
    unfold contourAverage blockMean
    simp only [hF]
  have e2 : _root_.YangMills.Construction.BlockAverages.contourAverage X' ((Y' + siteOfCoords F'.top g, d) : F'.Site (F'.depth + 1) × Fin 4) =
      blockMean L (fun a π => ((pathHolonomy X' (_root_.YangMills.Construction.BlockAverages.refineSite (Y' + siteOfCoords F'.top g)) (bondContour L a π d) :
        UnitQuaternion) : ℍ[ℝ])) := by
    unfold contourAverage blockMean
    simp only [hF']
  rw [e1, e2]
  refine norm_blockMean_sub_le hL fun a ha π => ?_
  have hp := LatticePaths.allAlong_add (w := fun i => (L : ℤ) * g i)
    (LatticePaths.bondContour_spec π d hL.pos ha).1
  have h5 := pathHolonomy_close (Y := Y) (Y' := Y') (X := X) (X' := X') h _ _ hp
  rw [refineSite_add_eq_siteAtOffset, refineSite_add_eq_siteAtOffset, hF, hF']
  refine h5.trans ?_
  have hlen := LatticePaths.length_bondContour_le π d hL.pos ha
  have h6 : ((bondContour L a π d).length : ℝ) ≤ 5 * (L : ℝ) := by exact_mod_cast hlen
  exact mul_le_mul_of_nonneg_right h6 hε
private theorem offsetNear_of_mem_twoBlockHull {L r : ℕ} (hL : Odd L) {g v : LatticeOffset} {d : Fin 4}
    (hg : WithinRadius r g) (hg' : WithinRadius r (g + Pi.single d 1))
    (hv : (v - fun i => (L : ℤ) * g i) ∈ FlatPairing.twoBlockHull L d) :
    OffsetNear L r v := by exact _root_.YangMills.Construction.ColdStepAtMirrorFrames.TwoTori.nearBox_of_mem_twoBlockHull (L := L) (r := r) (g := g) (v := v) (d := d) hL hg hg' hv
private theorem enclosingCell_of_mem_twoBlockHull (hL : Odd F.blockSide) (hs : ∀ i, 2 ≤ F.extent i) (z : F.Cell)
    (d : Fin 4) {v : LatticeOffset}
    (hv : v ∈ FlatPairing.twoBlockHull F.blockSide d) :
    enclosingCell (cellCentre F.depth z + siteOfCoords F.depth v : F.Site F.depth) = z ∨
      enclosingCell (cellCentre F.depth z + siteOfCoords F.depth v : F.Site F.depth) = z + unitStep F.top d := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.ChartSlopeOnTwoTori.enclosingCell_of_mem_twoBlockHull <;> assumption
private theorem cellSupDist_offset_le {R : ℕ} (Y : F.Cell) {g : LatticeOffset} (hg : WithinRadius R g)
    (hs : ∀ i, 2 * R < F.extent i) :
    cellSupDist Y (Y + siteOfCoords F.top g) ≤ R := by
  unfold cellSupDist
  refine Finset.sup_le fun i _ => ?_
  have hne : NeZero (F.period F.top i) := ⟨by
    rw [period_top]
    have := hs i
    omega⟩
  have hb := abs_le.1 (hg i)
  have hsi : (2 * (R : ℤ)) < F.extent i := by exact_mod_cast hs i
  have hv : ((Y i - (Y + siteOfCoords F.top g : F.Cell) i)).valMinAbs = -(g i) := by
    rw [ZMod.valMinAbs_spec]
    refine ⟨by simp [siteOfCoords], ?_⟩
    rw [period_top]
    simp only [Set.mem_Ioc]
    constructor <;> linarith [hb.1, hb.2]
  rw [hv]
  omega
private theorem haarGap_lipschitz_scaled {C₁ A u u' : ℝ} (hd : Differentiable ℝ haarGap)
    (hC : ∀ s : ℝ, 1 ≤ s → |s * deriv haarGap s| ≤ C₁) (hA : 2 ≤ A) (hu : 1 / 2 ≤ u) (hu1 : u ≤ 1)
    (hu' : 1 / 2 ≤ u') (hu1' : u' ≤ 1) :
    |haarGap (A * u) - haarGap (A * u')| ≤ 2 * C₁ * |u - u'| := by
  have hA0 : 0 < A := by linarith
  have hb : ∀ s ∈ Set.Icc (A / 2) A, ‖deriv haarGap s‖ ≤ 2 * C₁ / A := by
    intro s hs
    have hs1 : 1 ≤ s := by linarith [hs.1]
    have h1 := hC s hs1
    rw [abs_mul, abs_of_pos (by linarith : (0 : ℝ) < s)] at h1
    rw [Real.norm_eq_abs, le_div_iff₀ hA0]
    have h2 : A / 2 * |deriv haarGap s| ≤ s * |deriv haarGap s| :=
      mul_le_mul_of_nonneg_right hs.1 (abs_nonneg _)
    linarith
  have hm : A * u ∈ Set.Icc (A / 2) A := ⟨by nlinarith, by nlinarith⟩
  have hm' : A * u' ∈ Set.Icc (A / 2) A := ⟨by nlinarith, by nlinarith⟩
  have h3 := (convex_Icc (A / 2) A).norm_image_sub_le_of_norm_deriv_le (fun s _ => hd s) hb hm' hm
  rw [Real.norm_eq_abs, Real.norm_eq_abs] at h3
  have e : |A * u - A * u'| = A * |u - u'| := by
    rw [← mul_sub, abs_mul, abs_of_pos hA0]
  rw [e] at h3
  have e2 : 2 * C₁ / A * (A * |u - u'|) = 2 * C₁ * |u - u'| := by field_simp
  linarith
private theorem haarGapExcess_close {C₁ a x : ℝ} (hd : Differentiable ℝ haarGap)
    (hC : ∀ s : ℝ, 1 ≤ s → |s * deriv haarGap s| ≤ C₁) (ha : 1 ≤ a) (hx : 2 ≤ x)
    {W : F.GaugeField F.depth} {W' : F'.GaugeField F'.depth} (c : F.Site F.top × Fin 4) (c' : F'.Site F'.top × Fin 4)
    (h1 : 1 / 2 ≤ ‖_root_.YangMills.Construction.BlockAverages.contourAverage W c‖) (h2 : ‖_root_.YangMills.Construction.BlockAverages.contourAverage W c‖ ≤ 1)
    (h1' : 1 / 2 ≤ ‖_root_.YangMills.Construction.BlockAverages.contourAverage W' c'‖) (h2' : ‖_root_.YangMills.Construction.BlockAverages.contourAverage W' c'‖ ≤ 1) :
    |haarGapExcess a x W c - haarGapExcess a x W' c'| ≤
      2 * C₁ * ‖_root_.YangMills.Construction.BlockAverages.contourAverage W c - _root_.YangMills.Construction.BlockAverages.contourAverage W' c'‖ := by
  have hC0 : 0 ≤ C₁ := (abs_nonneg _).trans (hC 1 le_rfl)
  unfold haarGapExcess
  rw [sub_sub_sub_cancel_right]
  refine (haarGap_lipschitz_scaled hd hC (by nlinarith) h1 h2 h1' h2').trans ?_
  exact mul_le_mul_of_nonneg_left (abs_norm_sub_norm_le _ _) (by positivity)
private theorem kernelGapComponent_eq_sum (hs : ∀ i, 2 ≤ F.extent i) (star : Bool) (a ρA x : ℝ) (m : ℕ) (Z : F.Cell)
    (V : F.GaugeField F.top) (η : StepVariable (finiteCells F)) :
    kernelGapComponent star a ρA x m Z V η =
      ∑ d : Fin 4, haarGapExcess a x (fieldAboveFrame star a ρA m V η) (Z, d) := by
  classical
  have hB : innerBonds (finiteCells F) F.top = finiteCells F ×ˢ Finset.univ := by
    ext c
    simp only [innerBonds, Finset.mem_filter, Finset.mem_product, Finset.mem_univ, and_true]
    constructor
    · rintro ⟨h, _⟩
      exact mem_sitesOfCells_top.1 h
    · intro h
      exact ⟨mem_sitesOfCells_top.2 h, mem_sitesOfCells_top.2 (_root_.YangMills.Construction.ColdStepAtMirrorFrames.BlockOffsets.mem_finiteCells hs _)⟩
  unfold kernelGapComponent
  rw [hB, Finset.sum_filter, Finset.sum_product_right]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [Finset.sum_eq_single Z]
  · simp
  · intro z _ hz
    simp [hz]
  · intro h
    exact (h (_root_.YangMills.Construction.ColdStepAtMirrorFrames.BlockOffsets.mem_finiteCells hs _)).elim
private theorem sum_haarGapExcess_close (hexp : QuaternionExp.ExpUnitLipschitzInjective) {L R : ℕ}
    (hF : F.blockSide = L) (hF' : F'.blockSide = L) (hL : Odd L)
    (hs : ∀ i, 2 ≤ F.extent i) (hs' : ∀ i, 2 ≤ F'.extent i) {w : F.Site F.depth → Fin 4 → imaginaryQuaternions}
    {w' : F'.Site F'.depth → Fin 4 → imaginaryQuaternions} {V : F.GaugeField F.top} {V' : F'.GaugeField F'.top}
    {Y : F.Cell} {Y' : F'.Cell} {ε : ℝ}
    (hε : 0 ≤ ε)
    (hV : ∀ b, BondWithinRadius R b → V (Y + siteOfCoords F.top b.1) b.2 = V' (Y' + siteOfCoords F'.top b.1) b.2)
    (hw : ∀ (g q : LatticeOffset) (j : Fin 4), WithinRadius R g → q ∈ centredCube L →
      fineBondAt Y g q j ∈ chordBonds (finiteCells F) →
      ‖((w (fineBondAt Y g q j).1 j : imaginaryQuaternions) : ℍ[ℝ]) -
        ((w' (fineBondAt Y' g q j).1 j : imaginaryQuaternions) : ℍ[ℝ])‖ ≤ ε)
    (g : LatticeOffset) (hg : WithinRadius R g) (hgd : ∀ d, WithinRadius R (g + Pi.single d 1)) {C₁ a x : ℝ}
    (hd : Differentiable ℝ haarGap) (hC : ∀ s : ℝ, 1 ≤ s → |s * deriv haarGap s| ≤ C₁) (ha : 1 ≤ a) (hx : 2 ≤ x)
    (hc : ∀ (c : F.Site F.top × Fin 4) (h : Fin 4 → ℤ) (π : Equiv.Perm (Fin 4)), h ∈ centredCube F.blockSide →
      ‖contourHolonomyDefect (chartedField w V) V c h π - 1‖ ≤ 1 / 2)
    (hc' : ∀ (c : F'.Site F'.top × Fin 4) (h : Fin 4 → ℤ) (π : Equiv.Perm (Fin 4)), h ∈ centredCube F'.blockSide →
      ‖contourHolonomyDefect (chartedField w' V') V' c h π - 1‖ ≤ 1 / 2) :
    |∑ d : Fin 4, haarGapExcess a x (chartedField w V) (Y + siteOfCoords F.top g, d) -
      ∑ d : Fin 4, haarGapExcess a x (chartedField w' V') (Y' + siteOfCoords F'.top g, d)| ≤
      4 * (2 * C₁ * (5 * (L : ℝ) * ε)) := by
  have hLF : Odd F.blockSide := by rw [hF]; exact hL
  have hLF' : Odd F'.blockSide := by rw [hF']; exact hL
  have hC0 : 0 ≤ C₁ := (abs_nonneg _).trans (hC 1 le_rfl)
  rw [← Finset.sum_sub_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have hone : ∀ d : Fin 4, |haarGapExcess a x (chartedField w V) (Y + siteOfCoords F.top g, d) -
      haarGapExcess a x (chartedField w' V') (Y' + siteOfCoords F'.top g, d)| ≤ 2 * C₁ * (5 * (L : ℝ) * ε) := by
    intro d
    obtain ⟨b1, b2⟩ := contourAverage_norm_bounds hLF (chartedField w V) V (Y + siteOfCoords F.top g, d) (hc _)
    obtain ⟨b1', b2'⟩ := contourAverage_norm_bounds hLF' (chartedField w' V') V' (Y' + siteOfCoords F'.top g, d) (hc' _)
    refine (haarGapExcess_close hd hC ha hx _ _ b1 b2 b1' b2').trans ?_
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    exact contourAverage_close hF hF' hL g d hε (fun v k h1 h2 =>
      chartedField_close hexp hF hF' hL hs hs' hε hV hw v k (offsetNear_of_mem_twoBlockHull hL hg (hgd d) h1)
        (offsetNear_of_mem_twoBlockHull hL hg (hgd d) h2))
  refine (Finset.sum_le_sum fun d _ => hone d).trans (le_of_eq ?_)
  simp
private theorem zeroExtensionL_apply {Λ ι : Type} [Fintype Λ] [Fintype ι] [DecidableEq ι] (e : Λ → ι)
    (he : Function.Injective e) (ζ : BondField Λ) (l : Λ) : zeroExtensionL e ζ (e l) = ζ l := by
  have h : ∃ l', e l' = e l := ⟨l, rfl⟩
  simp only [zeroExtensionL, ContinuousLinearMap.coe_pi', dif_pos h, ContinuousLinearMap.proj_apply]
  rw [he h.choose_spec]
abbrev _root_.YangMills.SharedProofs.p32108 := @zeroExtensionL_apply
private theorem zeroExtensionL_apply_of_eq {Λ ι : Type} [Fintype Λ] [Fintype ι] [DecidableEq ι] (e : Λ → ι)
    (he : Function.Injective e) (ζ : BondField Λ) (l : Λ) (b : ι) (hb : e l = b) : zeroExtensionL e ζ b = ζ l := by
  subst hb
  exact zeroExtensionL_apply e he ζ l
private theorem norm_zeroExtensionL_lt {Λ ι : Type} [Fintype Λ] [Fintype ι] [DecidableEq ι] (e : Λ → ι) {ρ : ℝ}
    (hρ : 0 < ρ) {ζ : BondField Λ} (hζ : ζ ∈ openPolyball Λ ρ) (b : ι) : ‖zeroExtensionL e ζ b‖ < ρ := by
  by_cases h : ∃ l, e l = b
  · simp only [zeroExtensionL, ContinuousLinearMap.coe_pi', dif_pos h, ContinuousLinearMap.proj_apply]
    exact hζ _
  · simp only [zeroExtensionL, ContinuousLinearMap.coe_pi', dif_neg h]
    simpa using hρ
private theorem norm_toImaginary (v : EuclideanSpace ℝ (Fin 3)) : ‖(toImaginary v : imaginaryQuaternions)‖ = ‖v‖ := by apply _root_.YangMills.Construction.Interpolation.ExponentBoundSteps.norm_toImaginary <;> assumption
private theorem stepCoordinates_of_mem {S : Finset F.Cell} (η : StepVariable S) (b : F.Site F.depth × Fin 4)
    (hb : b ∈ chordBonds S) :
    stepCoordinates η b.1 b.2 = toImaginary (η ⟨b, hb⟩) := by
  unfold stepCoordinates
  exact dif_pos hb
private theorem enclosingCell_fineBond_near {R : ℕ} (hLF : Odd F.blockSide) (hs : ∀ i, 2 ≤ F.extent i)
    (hsR1 : ∀ i, 2 * (R + 1) < F.extent i) (Y : F.Cell)
    (g q : Fin 4 → ℤ) (j : Fin 4) (hg : WithinRadius R g) (hqF : q ∈ centredCube F.blockSide) :
    cellSupDist Y (enclosingCell (fineBondAt Y g q j).1) ≤ R ∧
      cellSupDist Y (enclosingCell ((fineBondAt Y g q j).1 + unitStep F.depth j)) ≤ R + 1 := by
  have hsR : ∀ i, 2 * R < F.extent i := fun i => by have := hsR1 i; omega
  have hd1 : cellSupDist Y (enclosingCell (fineBondAt Y g q j).1) ≤ R := by
    have e : enclosingCell (fineBondAt Y g q j).1 = Y + siteOfCoords F.top g :=
      enclosingCell_offset hLF hs (Y + siteOfCoords F.top g) q hqF
    rw [e]
    exact cellSupDist_offset_le Y hg hsR
  have hd2 : cellSupDist Y (enclosingCell ((fineBondAt Y g q j).1 + unitStep F.depth j)) ≤ R + 1 := by
    have hhull : q + Pi.single j 1 ∈ FlatPairing.twoBlockHull F.blockSide j := by
      intro μ
      have h1 := (BlockOffsets.mem_centredCube_iff q).1 hqF μ
      have eh : ((F.blockSide : ℤ) - 1) / 2 = halfSide F.blockSide := rfl
      have hpos : (0 : ℤ) < F.blockSide := by exact_mod_cast hLF.pos
      rw [eh]
      by_cases hμ : μ = j
      · subst hμ
        simp only [Pi.add_apply, Pi.single_eq_same, if_true]
        constructor <;> linarith [h1.1, h1.2]
      · simp only [Pi.add_apply, Pi.single_eq_of_ne hμ, hμ, if_false, add_zero]
        exact h1
    have e0 : (fineBondAt Y g q j).1 + unitStep F.depth j =
        cellCentre F.depth (Y + siteOfCoords F.top g) + siteOfCoords F.depth (q + Pi.single j 1) :=
      offset_add_unitStep _ _ _
    rw [e0]
    have hbig : WithinRadius (R + 1) g := fun i => (hg i).trans (by push_cast; omega)
    rcases enclosingCell_of_mem_twoBlockHull hLF hs (Y + siteOfCoords F.top g) j hhull with e | e
    · rw [e]
      exact cellSupDist_offset_le Y hbig hsR1
    · rw [e, add_assoc]
      have e2 : siteOfCoords F.top g + unitStep F.top j = (siteOfCoords F.top (g + Pi.single j 1) : F.Cell) := by
        rw [_root_.YangMills.Construction.BlockAverages.siteOfCoords_add]
        rfl
      rw [e2]
      refine cellSupDist_offset_le Y (fun i => ?_) hsR1
      have h3 := abs_le.1 (hg i)
      by_cases hi : i = j
      · subst hi
        simp only [Pi.add_apply, Pi.single_eq_same]
        rw [abs_le]
        push_cast
        constructor <;> linarith [h3.1, h3.2]
      · simp only [Pi.add_apply, Pi.single_eq_of_ne hi, add_zero]
        exact (hg i).trans (by push_cast; omega)
  exact ⟨hd1, hd2⟩
private theorem matched_mem_chordBonds {L : ℕ} (hFL : F.blockSide = L) (hFL' : F'.blockSide = L) (hodd : Odd L)
    (hs : ∀ i, 2 ≤ F.extent i)
    (hs' : ∀ i, 2 ≤ F'.extent i) (Y : F.Cell) (Y' : F'.Cell) (g q : Fin 4 → ℤ) (j : Fin 4) (hq : q ∈ centredCube L)
    (hb : fineBondAt Y g q j ∈ chordBonds (finiteCells F)) : fineBondAt Y' g q j ∈ chordBonds (finiteCells F') := by
  have hLF : Odd F.blockSide := by rw [hFL]; exact hodd
  have hLF' : Odd F'.blockSide := by rw [hFL']; exact hodd
  have hqF : q ∈ centredCube F.blockSide := by rw [hFL]; exact hq
  have hqF' : q ∈ centredCube F'.blockSide := by rw [hFL']; exact hq
  refine fineBondAt_mem_chordBonds hLF' hs' Y' g q j fun ht => ?_
  have ht1 := (isAxialTreeBond_iff hLF' hs' (Y' + siteOfCoords F'.top g) q hqF' j).1 ht
  rw [hFL'] at ht1
  have hnt : ¬ IsAxialTreeBond (fineBondAt Y g q j) := by
    classical
    simp only [chordBonds, Finset.mem_filter] at hb
    exact hb.2
  apply hnt
  refine (isAxialTreeBond_iff hLF hs (Y + siteOfCoords F.top g) q hqF j).2 ?_
  rw [hFL]
  exact ht1
private theorem stepCoordinates_common {L r R : ℕ} (hFL : F.blockSide = L) {Y : F.Cell} {Y' : F'.Cell}
    (hRr : R ≤ r / 2)
    (hcom : HasCommonBonds Y Y' r) {ζ : BondField ↥(commonBondOffsets Y Y' (r / 2))}
    {η : StepVariable (finiteCells F)}
    {η' : StepVariable (finiteCells F')} (hη : η = zeroExtensionL (commonBondLeft Y Y' (r / 2)) ζ)
    (hη' : η' = zeroExtensionL (commonBondRight Y Y' (r / 2)) ζ) (g q : Fin 4 → ℤ) (j : Fin 4)
    (hg : WithinRadius R g) (hq : q ∈ centredCube L)
    (hb : fineBondAt Y g q j ∈ chordBonds (finiteCells F)) (hb' : fineBondAt Y' g q j ∈ chordBonds (finiteCells F')) :
    stepCoordinates η (fineBondAt Y g q j).1 j = stepCoordinates η' (fineBondAt Y' g q j).1 j := by
  have hqF : q ∈ centredCube F.blockSide := by rw [hFL]; exact hq
  have hgc : g ∈ centredCube (2 * (r / 2) + 1) := by
    rw [BlockOffsets.mem_centredCube_iff]
    intro i
    have h3 := abs_le.1 (hg i)
    have e : halfSide (2 * (r / 2) + 1) = ((r / 2 : ℕ) : ℤ) := by
      unfold halfSide
      generalize r / 2 = k
      push_cast
      omega
    rw [e]
    have h4 : (R : ℤ) ≤ ((r / 2 : ℕ) : ℤ) := by exact_mod_cast hRr
    constructor <;> linarith [h3.1, h3.2]
  have hmem : (g, q, j) ∈ commonBondOffsets Y Y' (r / 2) := by
    simp only [commonBondOffsets, Finset.mem_filter, Finset.mem_product, Finset.mem_univ, and_true]
    exact ⟨⟨hgc, hqF⟩, hb, hb'⟩
  have f1 := stepCoordinates_of_mem η (fineBondAt Y g q j) hb
  have f2 := stepCoordinates_of_mem η' (fineBondAt Y' g q j) hb'
  have g1 : η ⟨fineBondAt Y g q j, hb⟩ = ζ ⟨_, hmem⟩ := by
    rw [hη]
    exact zeroExtensionL_apply_of_eq _ hcom.injective_left ζ ⟨_, hmem⟩ _ (Subtype.ext rfl)
  have g2 : η' ⟨fineBondAt Y' g q j, hb'⟩ = ζ ⟨_, hmem⟩ := by
    rw [hη']
    exact zeroExtensionL_apply_of_eq _ hcom.injective_right ζ ⟨_, hmem⟩ _ (Subtype.ext rfl)
  rw [g1] at f1
  rw [g2] at f2
  exact f1.trans f2.symm
private theorem coordsAboveFrame_close {L r R m : ℕ} {star : Bool} {a ρA δ₂ C σ : ℝ} (hFL : F.blockSide = L)
    (hFL' : F'.blockSide = L) (hodd : Odd L)
    (hs : ∀ i, 2 ≤ F.extent i) (hs' : ∀ i, 2 ≤ F'.extent i) (h2r : ∀ i, 2 * r + 2 < F.extent i) (hr : 64 ≤ r)
    (hR : R = r / 8 + 1) {V : F.GaugeField F.top} {V' : F'.GaugeField F'.top} {Y : F.Cell} {Y' : F'.Cell}
    (hfr : FrameLocality star a ρA δ₂ C σ m V V' Y Y' r) (hcom : HasCommonBonds Y Y' r) (hC : 0 ≤ C) (hσ : 0 < σ)
    (hδ : 0 < δ₂) {ζ : BondField ↥(commonBondOffsets Y Y' (r / 2))} {η : StepVariable (finiteCells F)}
    {η' : StepVariable (finiteCells F')} (hη : η = zeroExtensionL (commonBondLeft Y Y' (r / 2)) ζ)
    (hη' : η' = zeroExtensionL (commonBondRight Y Y' (r / 2)) ζ) (g q : Fin 4 → ℤ) (j : Fin 4)
    (hg : WithinRadius R g) (hq : q ∈ centredCube L)
    (hb : fineBondAt Y g q j ∈ chordBonds (finiteCells F)) :
    ‖((coordsAboveFrame star a ρA m V η (fineBondAt Y g q j).1 j : imaginaryQuaternions) : ℍ[ℝ]) -
      ((coordsAboveFrame star a ρA m V' η' (fineBondAt Y' g q j).1 j : imaginaryQuaternions) : ℍ[ℝ])‖ ≤
      C * σ * Real.exp (-(δ₂ / 4 * ((r : ℝ) / 2))) := by
  have hLF : Odd F.blockSide := by rw [hFL]; exact hodd
  have hLF' : Odd F'.blockSide := by rw [hFL']; exact hodd
  have hR2 : 2 * R ≤ r := by omega
  have hRr : R ≤ r / 2 := by omega
  have hb' := matched_mem_chordBonds hFL hFL' hodd hs hs' Y Y' g q j hq hb
  have hqF : q ∈ centredCube F.blockSide := by rw [hFL]; exact hq
  obtain ⟨hd1, hd2⟩ := enclosingCell_fineBond_near hLF hs (fun i => by have := h2r i; omega) Y g q j hg hqF
  have hlb : IsFineBondWithinRadius Y r g q j :=
    ⟨hqF, hb, fun i => (hg i).trans (by exact_mod_cast (by omega : R ≤ r)), hd1.trans (by omega),
      hd2.trans (by omega)⟩
  have hv := hfr.value g q j hlb
  have hcoord := stepCoordinates_common hFL hRr hcom hη hη' g q j hg hq hb hb'
  have hsplit : ((coordsAboveFrame star a ρA m V η (fineBondAt Y g q j).1 j : imaginaryQuaternions) : ℍ[ℝ]) -
      ((coordsAboveFrame star a ρA m V' η' (fineBondAt Y' g q j).1 j : imaginaryQuaternions) : ℍ[ℝ]) =
      (stepFrame star a ρA m (fineBondAt Y g q j) V : ℍ[ℝ]) -
        stepFrame star a ρA m (fineBondAt Y' g q j) V' := by
    have u1 : coordsAboveFrame star a ρA m V η (fineBondAt Y g q j).1 j =
        stepFrame star a ρA m (fineBondAt Y g q j) V +
          stepCoordinates η (fineBondAt Y g q j).1 j := rfl
    have u2 : coordsAboveFrame star a ρA m V' η' (fineBondAt Y' g q j).1 j =
        stepFrame star a ρA m (fineBondAt Y' g q j) V' +
          stepCoordinates η' (fineBondAt Y' g q j).1 j := rfl
    rw [u1, u2, hcoord, Submodule.coe_add, Submodule.coe_add, add_sub_add_right_eq_sub]
  rw [hsplit]
  refine hv.trans ?_
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  refine Real.exp_le_exp.2 ?_
  have h5 : (cellSupDist Y (enclosingCell (fineBondAt Y g q j).1) : ℝ) ≤ (r : ℝ) / 2 := by
    have h6 : 2 * cellSupDist Y (enclosingCell (fineBondAt Y g q j).1) ≤ r := by omega
    have h7 : (2 : ℝ) * (cellSupDist Y (enclosingCell (fineBondAt Y g q j).1) : ℝ) ≤ r := by exact_mod_cast h6
    linarith
  have h8 : (0 : ℝ) < δ₂ / 4 := by positivity
  have h9 : (r : ℝ) / 2 ≤ (r : ℝ) - cellSupDist Y (enclosingCell (fineBondAt Y g q j).1) := by linarith
  have := mul_le_mul_of_nonneg_left h9 h8.le
  linarith
private theorem contourHolonomyDefect_small (hcont : ChartedFieldContourBound) {L m : ℕ} {star : Bool}
    {a ρA σ Cm : ℝ} (hodd : Odd L)
    (hσ : 0 < σ) (hCm : 1 ≤ Cm) (hσ4 : σ ≤ 1 / (10 * L * (Cm + 1))) {G : BlockFrame} (hG : G.blockSide = L)
    (hsG : ∀ i, 2 ≤ G.extent i)
    (U : G.GaugeField G.top) (ξ : StepVariable (finiteCells G)) (hξ : ∀ b, ‖ξ b‖ < σ / 64)
    (hfrm : ∀ b ∈ chordBonds (finiteCells G), ‖stepFrame star a ρA m b U‖ ≤ Cm * σ)
    (c' : G.Site G.top × Fin 4) (h' : Fin 4 → ℤ) (π : Equiv.Perm (Fin 4)) (hh : h' ∈ centredCube G.blockSide) :
    ‖contourHolonomyDefect (chartedField (coordsAboveFrame star a ρA m U ξ) U) U c' h' π - 1‖ ≤ 1 / 2 := by
  have hLpos : (0 : ℝ) < L := by exact_mod_cast hodd.pos
  have hLG : Odd G.blockSide := by rw [hG]; exact hodd
  have hbound : ∀ b ∈ chordBonds (finiteCells G),
      ‖coordsAboveFrame star a ρA m U ξ b.1 b.2‖ ≤ Cm * σ + σ / 64 := by
    intro b hb
    have e : coordsAboveFrame star a ρA m U ξ b.1 b.2 =
        stepFrame star a ρA m b U + stepCoordinates ξ b.1 b.2 := rfl
    rw [e, stepCoordinates_of_mem ξ b hb]
    refine (norm_add_le _ _).trans ?_
    have h1 := hfrm b hb
    have h2 : ‖(toImaginary (ξ ⟨b, hb⟩) : imaginaryQuaternions)‖ = ‖ξ ⟨b, hb⟩‖ := norm_toImaginary _
    rw [h2]
    linarith [(hξ ⟨b, hb⟩).le]
  have h3 := hcont G _ U (Cm * σ + σ / 64) hLG (fun i => hsG i) (by positivity) hbound c' h' π hh
  refine le_trans h3 ?_
  rw [hG]
  have h4 : σ * (10 * L * (Cm + 1)) ≤ 1 := by
    have := mul_le_mul_of_nonneg_right hσ4 (by positivity : (0 : ℝ) ≤ 10 * L * (Cm + 1))
    rwa [one_div, inv_mul_cancel₀ (by positivity)] at this
  have h5 : 5 * (L : ℝ) * (Cm * σ + σ / 64) ≤ 5 * (L : ℝ) * ((Cm + 1) * σ) := by
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    nlinarith
  nlinarith
private theorem withinRadius_of_mem_centredCube {r R : ℕ} (hR : R = r / 8 + 1)
    (c0 : ↥(centredCube (2 * (r / 8) + 1))) :
    WithinRadius R c0.1 ∧ ∀ d, WithinRadius R (c0.1 + Pi.single d 1) := by
  have e : halfSide (2 * (r / 8) + 1) = ((r / 8 : ℕ) : ℤ) := by
    unfold halfSide
    generalize r / 8 = k
    push_cast
    omega
  have hRz : (R : ℤ) = ((r / 8 : ℕ) : ℤ) + 1 := by rw [hR]; push_cast; rfl
  constructor
  · intro i
    have h3 := (BlockOffsets.mem_centredCube_iff c0.1).1 c0.2 i
    rw [e] at h3
    rw [abs_le, hRz]
    constructor <;> linarith [h3.1, h3.2]
  · intro d i
    have h3 := (BlockOffsets.mem_centredCube_iff c0.1).1 c0.2 i
    rw [e] at h3
    rw [abs_le, hRz]
    by_cases hi : i = d
    · subst hi
      simp only [Pi.add_apply, Pi.single_eq_same]
      constructor <;> linarith [h3.1, h3.2]
    · simp only [Pi.add_apply, Pi.single_eq_of_ne hi, add_zero]
      constructor <;> have : (0 : ℤ) ≤ ((r / 8 : ℕ) : ℤ) := by positivity
      all_goals linarith [h3.1, h3.2]
private theorem final_estimate {C₁ Ct Cl σ δ₂ κ x S : ℝ} {L r : ℕ} (hC0 : 0 ≤ C₁) (hCl : 0 ≤ Cl) (hσ : 0 < σ)
    (hσ1 : σ ≤ 1) (hδ : 0 < δ₂)
    (hκ' : κ ≤ δ₂ / 2 ^ 14) (hCt : 160 * C₁ * L * Cl ≤ Ct) (hS : 0 ≤ x * S) :
    4 * (2 * C₁ * (5 * (L : ℝ) * (Cl * σ * Real.exp (-(δ₂ / 4 * ((r : ℝ) / 2)))))) ≤
      (Ct / 4 * Real.exp (-(2 * κ * r))) * (x * S + 1) := by
  have hexpo : Real.exp (-(δ₂ / 4 * ((r : ℝ) / 2))) ≤ Real.exp (-(2 * κ * r)) := by
    refine Real.exp_le_exp.2 ?_
    have hr0 : (0 : ℝ) ≤ r := by positivity
    have h1 : 2 * κ ≤ δ₂ / 8 := by
      have : δ₂ / 2 ^ 14 ≤ δ₂ / 16 := div_le_div_of_nonneg_left hδ.le (by norm_num) (by norm_num)
      linarith
    have := mul_le_mul_of_nonneg_right h1 hr0
    linarith
  have hCtn : 0 ≤ 160 * C₁ * L * Cl := by positivity
  have hCt0 : 0 ≤ Ct := hCtn.trans hCt
  have hnum : 40 * C₁ * L * Cl * σ ≤ Ct / 4 := by
    have : 40 * C₁ * L * Cl * σ ≤ 40 * C₁ * L * Cl * 1 :=
      mul_le_mul_of_nonneg_left hσ1 (by positivity)
    linarith
  have e4 : 4 * (2 * C₁ * (5 * (L : ℝ) * (Cl * σ * Real.exp (-(δ₂ / 4 * ((r : ℝ) / 2)))))) =
      (40 * C₁ * L * Cl * σ) * Real.exp (-(δ₂ / 4 * ((r : ℝ) / 2))) := by ring
  rw [e4]
  calc (40 * C₁ * L * Cl * σ) * Real.exp (-(δ₂ / 4 * ((r : ℝ) / 2)))
      ≤ (Ct / 4) * Real.exp (-(2 * κ * r)) :=
        mul_le_mul hnum hexpo (Real.exp_pos _).le (by positivity)
    _ ≤ (Ct / 4 * Real.exp (-(2 * κ * r))) * (x * S + 1) := by
      have : 0 ≤ Ct / 4 * Real.exp (-(2 * κ * r)) := by positivity
      nlinarith
private theorem kernelGapComponent_close (hexp : QuaternionExp.ExpUnitLipschitzInjective)
    (hcont : ChartedFieldContourBound)
    {a ρA δ₂ Cl Cm C₁ Ct σ κ x : ℝ} {L r m : ℕ} {star : Bool} (ha : 1 ≤ a) (hodd : Odd L) (hCl : 1 ≤ Cl)
    (hCm : 1 ≤ Cm)
    (hd : Differentiable ℝ haarGap) (hC : ∀ u : ℝ, 1 ≤ u → |u * deriv haarGap u| ≤ C₁) (hδ : 0 < δ₂)
    (hσ : 0 < σ) (hσ1 : σ ≤ 1) (hσ4 : σ ≤ 1 / (10 * L * (Cm + 1))) (hκ' : κ ≤ δ₂ / 2 ^ 14)
    (hCt : 160 * C₁ * L * Cl ≤ Ct) (hx2 : 2 ≤ x) (hFL : F.blockSide = L) (hFL' : F'.blockSide = L)
    (hs : ∀ i, 2 ≤ F.extent i)
    (hs' : ∀ i, 2 ≤ F'.extent i) (h2r : ∀ i, 2 * r + 2 < F.extent i) (hr : 64 ≤ r) {V : F.GaugeField F.top}
    {V' : F'.GaugeField F'.top} {Y : F.Cell} {Y' : F'.Cell}
    (hag : ∀ b, BondWithinRadius r b → V (Y + siteOfCoords F.top b.1) b.2 = V' (Y' + siteOfCoords F'.top b.1) b.2)
    (hfr : FrameLocality star a ρA δ₂ Cl σ m V V' Y Y' r) (hcom : HasCommonBonds Y Y' r)
    (hsz : ∀ b ∈ chordBonds (finiteCells F), ‖stepFrame star a ρA m b V‖ ≤ Cm * σ)
    (hsz' : ∀ b ∈ chordBonds (finiteCells F'), ‖stepFrame star a ρA m b V'‖ ≤ Cm * σ)
    (c0 : ↥(centredCube (2 * (r / 8) + 1))) (ζ : BondField ↥(commonBondOffsets Y Y' (r / 2)))
    (hζ : ζ ∈ openPolyball ↥(commonBondOffsets Y Y' (r / 2)) (σ / 64)) :
    |kernelGapComponent star a ρA x m (offsetCell Y (r / 8) c0) V (zeroExtensionL (commonBondLeft Y Y' (r / 2)) ζ) -
      kernelGapComponent star a ρA x m (offsetCell Y' (r / 8) c0) V'
        (zeroExtensionL (commonBondRight Y Y' (r / 2)) ζ)| ≤
      (Ct / 4 * Real.exp (-(2 * κ * r))) * (x * weightedSqNormAt κ (chordBondCell F) (cellDistReal F)
        (offsetCell Y (r / 8) c0) (zeroExtensionL (commonBondLeft Y Y' (r / 2)) ζ) + 1) := by
  have hC0 : 0 ≤ C₁ := (abs_nonneg _).trans (hC 1 le_rfl)
  have hρ : 0 < σ / 64 := by positivity
  have hCl0 : 0 ≤ Cl := by linarith
  obtain ⟨R, hR⟩ : ∃ R, R = r / 8 + 1 := ⟨_, rfl⟩
  have hw := fun g q j hg hq hb => coordsAboveFrame_close (star := star) (a := a) (ρA := ρA) (m := m) hFL hFL' hodd
    hs hs' h2r hr hR hfr hcom hCl0 hσ hδ (ζ := ζ) rfl rfl g q j hg hq hb
  have hηb : ∀ b, ‖(zeroExtensionL (commonBondLeft Y Y' (r / 2)) ζ) b‖ < σ / 64 :=
    norm_zeroExtensionL_lt _ hρ hζ
  have hηb' : ∀ b, ‖(zeroExtensionL (commonBondRight Y Y' (r / 2)) ζ) b‖ < σ / 64 :=
    norm_zeroExtensionL_lt _ hρ hζ
  obtain ⟨hc0, hc0d⟩ := withinRadius_of_mem_centredCube hR c0
  have hV : ∀ b, BondWithinRadius R b → V (Y + siteOfCoords F.top b.1) b.2 =
      V' (Y' + siteOfCoords F'.top b.1) b.2 := by
    have hle : (R : ℤ) ≤ r := by exact_mod_cast (by omega : R ≤ r)
    exact fun b hb => hag b ⟨fun i => (hb.1 i).trans hle, fun i => (hb.2 i).trans hle⟩
  have hε : 0 ≤ Cl * σ * Real.exp (-(δ₂ / 4 * ((r : ℝ) / 2))) := by positivity
  have hmain := sum_haarGapExcess_close hexp hFL hFL' hodd hs hs' hε hV hw c0.1 hc0 hc0d hd hC ha hx2
    (contourHolonomyDefect_small hcont hodd hσ hCm hσ4 hFL hs V _ hηb hsz)
    (contourHolonomyDefect_small hcont hodd hσ hCm hσ4 hFL' hs' V' _ hηb' hsz')
  rw [kernelGapComponent_eq_sum hs, kernelGapComponent_eq_sum hs']
  refine le_trans hmain ?_
  refine final_estimate hC0 hCl0 hσ hσ1 hδ hκ' hCt ?_
  refine mul_nonneg (by linarith) ?_
  unfold weightedSqNormAt
  exact Finset.sum_nonneg fun b _ => by positivity
end GapComponentsOnTwoTori
open GapComponentsOnTwoTori YangMills.Construction.ColdStepAtMirrorFrames.BlockOffsets in
theorem gapComponentsCloseOnTwoTori_holds (hloc : framesLocalStatement) (hsm : framesSmallStatement)
    (hfl : CouplingThreshold) (hcont : ChartedFieldContourBound)
    (hcb : commonBondsOfTwoTori) (hder : HaarGapDerivBound)
    (hsmooth : HaarGapContDiff) (hexp : QuaternionExp.ExpUnitLipschitzInjective) :
    gapComponentsCloseOnTwoTori := by
  intro a ha
  refine ⟨0, fun L hodd _ c hc => ?_⟩
  obtain ⟨Cl, hCl1, hloc'⟩ := hloc a L c ha hodd hc
  obtain ⟨Cm, σ₁, hCm1, hσ₁, hsm'⟩ := hsm a L c ha hodd hc
  obtain ⟨C₁, hC₁⟩ := hder 1 le_rfl
  have hd : Differentiable ℝ haarGap := hsmooth.differentiable (by simp)
  have hC : ∀ u : ℝ, 1 ≤ u → |u * deriv haarGap u| ≤ C₁ := by
    intro u hu
    have := hC₁ u hu
    simpa [iteratedDeriv_one] using this
  have hδ : 0 < c.δ₂ := hc.classical.1.2.2.2.1
  have hs0 : 0 < c.s₀ := hc.classical.1.2.2.1
  have hLpos : (0 : ℝ) < L := by exact_mod_cast hodd.pos
  refine ⟨160 * C₁ * L * Cl, fun Ct hCt => ⟨c.δ₂ / 2 ^ 14, by positivity, fun κ hκ hκ' =>
    ⟨1, one_pos, fun η₃ _ _ _ => ⟨64, fun nss hnss => ?_⟩⟩⟩⟩
  have hσ₀ : 0 < min (min 1 σ₁) (min (4 / 5 * c.s₀) (1 / (10 * L * (Cm + 1)))) := by
    refine lt_min (lt_min one_pos hσ₁) (lt_min (by positivity) ?_)
    have : 0 < Cm + 1 := by linarith
    positivity
  refine ⟨_, hσ₀, fun σ hσ hσ' p _ => ?_⟩
  have hσ1 : σ ≤ 1 := hσ'.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hσ2 : σ ≤ σ₁ := hσ'.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hσ3 : σ ≤ 4 / 5 * c.s₀ := hσ'.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hσ4 : σ ≤ 1 / (10 * L * (Cm + 1)) := hσ'.trans ((min_le_right _ _).trans (min_le_right _ _))
  obtain ⟨y₂, hy₂⟩ := hfl (frameBoundConstant c) 1 c.δ₂ κ σ 0 hδ hκ hκ' hσ
  refine ⟨0, fun Cs _ E _ => ⟨64, fun n₀ hn₀ => ⟨0, fun CE _ => ⟨max y₂ 2, fun y₁ hy₁ => ?_⟩⟩⟩⟩
  intro t x F F' V V' Y Y' r star h c0 ζ hζ
  have hxy : y₁ ≤ x := h.coupling_le
  have hx2 : 2 ≤ x := ((le_max_right _ _).trans hy₁).trans hxy
  obtain ⟨-, hm16, hmgap, -, -, -⟩ := hy₂ x (((le_max_left _ _).trans hy₁).trans hxy)
  obtain ⟨hFL, hFt, n, hn, hnn⟩ := h.top
  obtain ⟨hFL', hFt', n', hn', hnn'⟩ := h.top'
  have hnn64 : 64 ≤ n := hn₀.trans hnn
  have hnn64' : 64 ≤ n' := hn₀.trans hnn'
  have hch : IsBlockTorus L F := ⟨hFL, n, hnn64, hn⟩
  have hch' : IsBlockTorus L F' := ⟨hFL', n', hnn64', hn'⟩
  have hs : ∀ i, 2 ≤ F.extent i := fun i => by rw [hn i]; omega
  have hs' : ∀ i, 2 ≤ F'.extent i := fun i => by rw [hn' i]; omega
  have hag : AgreeOnBall (finiteCells F) V (finiteCells F') V' Y Y' r := h.agree
  have hr : 64 ≤ r := hnss.trans h.radius_le
  have h2r : ∀ i, 2 * r + 2 < F.extent i := fun i => (hag.1 i).resolve_left (by have := hs i; omega)
  have h2r' : ∀ i, 2 * r + 2 < F'.extent i := fun i => (hag.2.1 i).resolve_left (by have := hs' i; omega)
  have hcold : IsSmallCurvature (5 / 4 * σ) V := h.small
  have hcold' : IsSmallCurvature (5 / 4 * σ) V' := h.small'
  have hfr := hloc' σ (frameRadius x) F F' V V' Y Y' r hσ (by linarith) hm16 hch hch' (by rw [hFt, hFt'])
    hcold hcold' hag star
  have hsz := (hsm' σ (frameRadius x) F V hσ hσ2 hm16 hmgap hch hcold).1 star
  have hsz' := (hsm' σ (frameRadius x) F' V' hσ hσ2 hm16 hmgap hch' hcold').1 star
  have hcom := (hcb L hodd).2 F F' Y Y' r n n' hFL hFL' hn hn'
    (by have := h2r 0; rw [hn 0] at this; exact this) (by have := h2r' 0; rw [hn' 0] at this; exact this)
  exact kernelGapComponent_close hexp hcont ha hodd hCl1 hCm1 hd hC hδ hσ hσ1 hσ4 hκ' hCt hx2 hFL hFL' hs hs' h2r hr
    hag.2.2.2 hfr hcom hsz.norm_le hsz'.norm_le c0 ζ hζ
end YangMills.Construction.ColdStepAtMirrorFrames
end
