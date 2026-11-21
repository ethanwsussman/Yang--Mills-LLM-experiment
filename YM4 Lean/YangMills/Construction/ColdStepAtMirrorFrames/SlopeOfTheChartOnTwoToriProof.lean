import YangMills.Construction.ClusterExpansionOfAStep.PlaquettesUnderGaugesAndMoves
import YangMills.Construction.ColdStepAtMirrorFrames.BlockEnergyOnTwoToriProof
import YangMills.Construction.ColdStepAtMirrorFrames.LogarithmOfAMovedExponential
import YangMills.Construction.ColdStepAtMirrorFrames.SlopeOfTheChartOnTwoTori
import YangMills.Construction.ColdStepAtMirrorFrames.SlopeOfTheLeastActionBelow
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open BlockAverages
namespace ColdStepAtMirrorFrames
namespace ChartSlopeOnTwoTori
open BlockOffsets
variable {F F' : BlockFrame}
abbrev LatticeOffset : Type := Fin 4 → ℤ
def siteAtOffset (Y : F.Cell) (p : LatticeOffset) : F.Site F.depth :=
  cellCentre F.depth Y + siteOfCoords F.depth p
def NearBlocks (L r : ℕ) (p : LatticeOffset) : Prop := ∀ i, |p i| ≤ (L : ℤ) * r + halfSide L
theorem cast_eq_two_mul_halfSide_add_one {L : ℕ} (hL : Odd L) : (L : ℤ) = 2 * halfSide L + 1 := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.TwoTori.cast_eq_two_mul_halfSide_add_one <;> assumption
theorem exists_block_decomposition {L : ℕ} (hL : Odd L) (p : LatticeOffset) :
    ∃ g q : LatticeOffset, q ∈ centredCube L ∧ ∀ i, p i = (L : ℤ) * g i + q i := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.TwoTori.exists_block_decomposition <;> assumption
theorem siteAtOffset_block (Y : F.Cell) (g q : LatticeOffset) :
    siteAtOffset Y (fun i => (F.blockSide : ℤ) * g i + q i) =
      cellCentre F.depth (Y + siteOfCoords F.top g) + siteOfCoords F.depth q := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.TwoTori.siteAtOffset_blockSplit <;> assumption
theorem mem_sitesOfCells_finiteCells (hL : Odd F.blockSide) (hs : ∀ i, 2 ≤ F.extent i) (x : F.Site F.depth) :
    x ∈ sitesOfCells (finiteCells F) F.depth := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.TwoTori.mem_sitesOfCells_finiteCells <;> assumption
theorem fineBondAt_mem_chordBonds (hL : Odd F.blockSide) (hs : ∀ i, 2 ≤ F.extent i) (Y : F.Cell)
    (g q : LatticeOffset) (j : Fin 4) (ht : ¬ IsAxialTreeBond (fineBondAt Y g q j)) :
    fineBondAt Y g q j ∈ chordBonds (finiteCells F) := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.TwoTori.fineBondAt_mem_chordBonds <;> assumption
theorem withinRadius_add_single {L r : ℕ} (hL : Odd L) {p g q : LatticeOffset} {j : Fin 4}
    (hp : ∀ i, p i = (L : ℤ) * g i + q i) (hq : q ∈ centredCube L) (hg : WithinRadius r g)
    (hp' : NearBlocks L r (p + Pi.single j 1)) (hqj : q j = halfSide L) :
    WithinRadius r (g + Pi.single j 1) := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.TwoTori.withinRadius_add_single <;> assumption
theorem chartedField_eq_of_agree {L r : ℕ} (hF : F.blockSide = L) (hF' : F'.blockSide = L) (hL : Odd L)
    (hs : ∀ i, 2 ≤ F.extent i) (hs' : ∀ i, 2 ≤ F'.extent i)
    {w : F.Site F.depth → Fin 4 → imaginaryQuaternions} {w' : F'.Site F'.depth → Fin 4 → imaginaryQuaternions}
    {V : F.GaugeField F.top} {V' : F'.GaugeField F'.top} {Y : F.Cell} {Y' : F'.Cell}
    (hV : ∀ b, BondWithinRadius r b →
      V (Y + siteOfCoords F.top b.1) b.2 = V' (Y' + siteOfCoords F'.top b.1) b.2)
    (hw : ∀ (g q : LatticeOffset) (j : Fin 4), WithinRadius r g → q ∈ centredCube L →
      fineBondAt Y g q j ∈ chordBonds (finiteCells F) →
        w (fineBondAt Y g q j).1 j = w' (fineBondAt Y' g q j).1 j)
    (p : LatticeOffset) (j : Fin 4) (hp : NearBlocks L r p) (hp' : NearBlocks L r (p + Pi.single j 1)) :
    chartedField w V (siteAtOffset Y p) j = chartedField w' V' (siteAtOffset Y' p) j := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.TwoTori.chartedField_eq <;> assumption
theorem pathHolonomy_eq_of_agree {Y : F.Cell} {Y' : F'.Cell} {X : F.GaugeField F.depth}
    {X' : F'.GaugeField F'.depth} {P : LatticeOffset → Prop}
    (h : ∀ v k, P v → P (v + LatticeFractionalIntegration.basisVector k) →
      X (siteAtOffset Y v) k = X' (siteAtOffset Y' v) k) :
    ∀ (l : List PathStep) (v : LatticeOffset), LatticePaths.AllAlong P v l →
      pathHolonomy X (siteAtOffset Y v) l = pathHolonomy X' (siteAtOffset Y' v) l := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.TwoTori.pathHolonomy_eq_of_agree <;> assumption
theorem refineSite_eq_cellCentre (Y : F.Cell) : refineSite Y = cellCentre F.depth Y := by apply _root_.YangMills.Construction.GaugeFixing.refineSite_eq_cellCentre <;> assumption
theorem refineSite_add_eq_siteAtOffset (Y : F.Cell) (g : LatticeOffset) :
    refineSite (Y + siteOfCoords F.top g) =
      siteAtOffset Y ((0 : LatticeOffset) + fun i => (F.blockSide : ℤ) * g i) := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.TwoTori.refineSite_add_eq_siteAtOffset <;> assumption
theorem contourAverage_eq_of_agree {L : ℕ} (hF : F.blockSide = L) (hF' : F'.blockSide = L) (hL : Odd L)
    {Y : F.Cell} {Y' : F'.Cell} {X : F.GaugeField F.depth} {X' : F'.GaugeField F'.depth}
    (g : LatticeOffset) (d : Fin 4)
    (h : ∀ v k, (v - fun i => (L : ℤ) * g i) ∈ FlatPairing.twoBlockHull L d →
      (v + LatticeFractionalIntegration.basisVector k - fun i => (L : ℤ) * g i) ∈ FlatPairing.twoBlockHull L d →
      X (siteAtOffset Y v) k = X' (siteAtOffset Y' v) k) :
    contourAverage X ((Y + siteOfCoords F.top g, d) : F.Site (F.depth + 1) × Fin 4) =
      contourAverage X' ((Y' + siteOfCoords F'.top g, d) : F'.Site (F'.depth + 1) × Fin 4) := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.TwoTori.contourAverage_eq_of_agree <;> assumption
theorem blockFit_eq_of_agree {L r : ℕ} (hF : F.blockSide = L) (hF' : F'.blockSide = L) (hL : Odd L)
    (hs : ∀ i, 2 ≤ F.extent i) (hs' : ∀ i, 2 ≤ F'.extent i)
    {w : F.Site F.depth → Fin 4 → imaginaryQuaternions} {w' : F'.Site F'.depth → Fin 4 → imaginaryQuaternions}
    {V : F.GaugeField F.top} {V' : F'.GaugeField F'.top} {Y : F.Cell} {Y' : F'.Cell}
    (hV : ∀ b, BondWithinRadius r b →
      V (Y + siteOfCoords F.top b.1) b.2 = V' (Y' + siteOfCoords F'.top b.1) b.2)
    (hw : ∀ (g q : LatticeOffset) (j : Fin 4), WithinRadius r g → q ∈ centredCube L →
      fineBondAt Y g q j ∈ chordBonds (finiteCells F) →
        w (fineBondAt Y g q j).1 j = w' (fineBondAt Y' g q j).1 j)
    (g : LatticeOffset) (d : Fin 4) (hg : WithinRadius r g) (hg' : WithinRadius r (g + Pi.single d 1)) :
    blockFit (chartedField w V) V ((Y + siteOfCoords F.top g, d) : F.Site (F.depth + 1) × Fin 4) =
      blockFit (chartedField w' V') V' ((Y' + siteOfCoords F'.top g, d) : F'.Site (F'.depth + 1) × Fin 4) := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.TwoTori.blockFit_eq_of_agree <;> assumption
theorem enclosingCell_of_mem_twoBlockHull (hL : Odd F.blockSide) (hs : ∀ i, 2 ≤ F.extent i) (z : F.Cell)
    (d : Fin 4) {v : LatticeOffset} (hv : v ∈ FlatPairing.twoBlockHull F.blockSide d) :
    enclosingCell (cellCentre F.depth z + siteOfCoords F.depth v : F.Site F.depth) = z ∨
      enclosingCell (cellCentre F.depth z + siteOfCoords F.depth v : F.Site F.depth) = z + unitStep F.top d := by
  have e := cast_eq_two_mul_halfSide_add_one hL
  have eh : ((F.blockSide : ℤ) - 1) / 2 = halfSide F.blockSide := rfl
  by_cases hc : v d ≤ halfSide F.blockSide
  · left
    apply enclosingCell_offset hL hs
    rw [mem_centredCube_iff]
    intro i
    have h1 := hv i
    rw [eh] at h1
    by_cases hi : i = d
    · subst hi
      exact ⟨h1.1, hc⟩
    · simpa [hi] using h1
  · right
    have e1 : (cellCentre F.depth z + siteOfCoords F.depth v : F.Site F.depth) =
        cellCentre F.depth (z + unitStep F.top d) +
          siteOfCoords F.depth (v - Pi.single d (F.blockSide : ℤ)) := by
      rw [cellCentre_add_unitStep hs, add_assoc, ← siteOfCoords_add]
      congr 2
      simp
    rw [e1]
    apply enclosingCell_offset hL hs
    rw [mem_centredCube_iff]
    intro i
    have h1 := hv i
    rw [eh] at h1
    by_cases hi : i = d
    · subst hi
      simp only [if_true] at h1
      simp only [Pi.sub_apply, Pi.single_eq_same]
      constructor <;> omega
    · simpa [hi, Pi.single_eq_of_ne hi] using h1
theorem contourAverage_eq_of_ne (hL : Odd F.blockSide) (hs : ∀ i, 2 ≤ F.extent i)
    {X X' : F.GaugeField F.depth} (c : F.Site (F.depth + 1) × Fin 4) (x : F.Site F.depth)
    (hag : ∀ y k, y ≠ x → X y k = X' y k) (h1 : enclosingCell x ≠ c.1)
    (h2 : enclosingCell x ≠ c.1 + unitStep F.top c.2) : contourAverage X c = contourAverage X' c := by
  unfold contourAverage
  congr 1
  refine Finset.sum_congr rfl fun a ha => Finset.sum_congr rfl fun π _ => ?_
  have hp : LatticePaths.AllAlong
      (fun v => refineSite c.1 + siteOfCoords F.depth v ∈ ({y | y ≠ x} : Set (F.Site F.depth))) 0
      (bondContour F.blockSide a π c.2) := by
    refine LatticePaths.allAlong_mono (fun v hv => ?_) (LatticePaths.bondContour_spec π c.2 hL.pos ha).1
    intro he
    rw [refineSite_eq_cellCentre] at he
    rcases enclosingCell_of_mem_twoBlockHull hL hs c.1 c.2 hv with h | h
    · exact h1 (he ▸ h)
    · exact h2 (he ▸ h)
  have := ChartCoordinates.pathHolonomy_congr (D := {y | y ≠ x}) (fun y i hy _ => hag y i hy)
    (refineSite c.1) _ 0 hp
  rw [ChartCoordinates.add_siteOfCoords_zero] at this
  rw [this]
theorem sum_innerBonds_eq_of_local (hs : ∀ i, 2 ≤ F.extent i) (D : F.Site (F.depth + 1) × Fin 4 → ℝ)
    (Cx : F.Cell) (hD : ∀ c : F.Site (F.depth + 1) × Fin 4, Cx ≠ c.1 → Cx ≠ c.1 + unitStep F.top c.2 → D c = 0) :
    ∑ c ∈ innerBonds (finiteCells F) (F.depth + 1), D c =
      ∑ d : Fin 4, (D (Cx, d) + D (Cx - unitStep F.top d, d)) := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.TwoTori.sum_innerBonds_eq_of_support <;> assumption
theorem fineSite_eq_iff {r : ℕ} (hL : Odd F.blockSide) (hs : ∀ i, 2 ≤ F.extent i)
    (sd : ∀ i, 2 * r + 2 < F.extent i) {Y : F.Cell} {g h q o : LatticeOffset} (hg : WithinRadius r g)
    (hh : WithinRadius r h) (hq : q ∈ centredCube F.blockSide) (ho : o ∈ centredCube F.blockSide) :
    (cellCentre F.depth (Y + siteOfCoords F.top g) + siteOfCoords F.depth q : F.Site F.depth) =
      cellCentre F.depth (Y + siteOfCoords F.top h) + siteOfCoords F.depth o ↔ g = h ∧ q = o := by
  constructor
  · intro e
    have c1 := enclosingCell_offset hL hs (Y + siteOfCoords F.top g) q hq
    have c2 := enclosingCell_offset hL hs (Y + siteOfCoords F.top h) o ho
    have o1 := cellOffset_offset hL hs (Y + siteOfCoords F.top g) q hq
    have o2 := cellOffset_offset hL hs (Y + siteOfCoords F.top h) o ho
    rw [e] at c1 o1
    refine ⟨?_, o1.symm.trans o2⟩
    have e2 : (siteOfCoords F.top g : F.Cell) = siteOfCoords F.top h := add_left_cancel (c1.symm.trans c2)
    funext i
    have e3 := congrFun e2 i
    have e4 : ((F.period F.top i : ℕ) : ℤ) ∣ h i - g i := (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).1 e3
    rw [period_top] at e4
    have b1 := abs_le.1 (hg i)
    have b2 := abs_le.1 (hh i)
    have b3 : |h i - g i| < (F.extent i : ℤ) := by
      have := sd i
      rw [abs_lt]
      constructor <;> omega
    have := Int.eq_zero_of_abs_lt_dvd e4 b3
    omega
  · rintro ⟨rfl, rfl⟩
    rfl
theorem update_update_apply {A B : Type} [DecidableEq A] [DecidableEq B] {E : Type} (w : A → B → E) (x : A)
    (i : B) (v : E) (y : A) (j : B) :
    Function.update w x (Function.update (w x) i v) y j = if y = x ∧ j = i then v else w y j := by
  by_cases hy : y = x
  · subst hy
    by_cases hj : j = i
    · subst hj
      simp
    · simp [hj]
  · simp [hy]
def singleBond {j : ℕ} (x : F.Site j) (i : Fin 4) (ξ : imaginaryQuaternions) :
    F.Site j → Fin 4 → imaginaryQuaternions :=
  fun y k => if (x, i) = (y, k) then ξ else 0
theorem bondSpread_const {j n : ℕ} (x : F.Site j) (i : Fin 4) (X : Fin n → imaginaryQuaternions)
    (τ : Fin n → ℝ) :
    bondSpread (fun _ => (x, i)) X τ = singleBond x i (∑ l, τ l • X l) := by
  funext y k
  unfold bondSpread singleBond
  by_cases h : (x, i) = (y, k)
  · simp [h]
  · simp [h]
theorem bondSpread_single {j : ℕ} (x : F.Site j) (i : Fin 4) (X : imaginaryQuaternions) (τ : Fin 1 → ℝ) :
    bondSpread ![(x, i)] ![X] τ = singleBond x i (τ 0 • X) := by
  funext y k
  unfold bondSpread singleBond
  by_cases h : (x, i) = (y, k)
  · simp [h]
  · simp [h]
theorem exists_hasFDerivAt_singleBond {j : ℕ} (A : F.GaugeField j → ℝ) (W : F.GaugeField j) (x : F.Site j)
    (i : Fin 4)
    (han : ∀ (n : ℕ) (X : Fin n → imaginaryQuaternions),
      AnalyticAt ℝ (fun τ : Fin n → ℝ => A (leftTranslate (bondSpread (fun _ => (x, i)) X τ) W)) 0) :
    ∃ D : imaginaryQuaternions →L[ℝ] ℝ,
      HasFDerivAt (fun ξ : imaginaryQuaternions => A (leftTranslate (singleBond x i ξ) W)) D 0 := by
  have bs := Module.finBasis ℝ imaginaryQuaternions
  let κ : imaginaryQuaternions →L[ℝ] (Fin (Module.finrank ℝ imaginaryQuaternions) → ℝ) :=
    LinearMap.toContinuousLinearMap bs.equivFun.toLinearMap
  have hd := (han _ fun l => bs l).differentiableAt.hasFDerivAt
  have hκ0 : κ 0 = 0 := map_zero κ
  rw [← hκ0] at hd
  have h4 := hd.comp (0 : imaginaryQuaternions) κ.hasFDerivAt
  refine ⟨_, h4.congr_of_eventuallyEq (Filter.Eventually.of_forall fun ξ => ?_)⟩
  simp only [Function.comp_apply]
  rw [bondSpread_const]
  have : ∑ l, κ ξ l • bs l = ξ := bs.sum_equivFun ξ
  rw [this]
theorem bondDeriv_single_eq {j : ℕ} {A : F.GaugeField j → ℝ} {W : F.GaugeField j} {x : F.Site j} {i : Fin 4}
    {D : imaginaryQuaternions →L[ℝ] ℝ}
    (hD : HasFDerivAt (fun ξ : imaginaryQuaternions => A (leftTranslate (singleBond x i ξ) W)) D 0)
    (X : imaginaryQuaternions) :
    bondDeriv A W ![(x, i)] ![X] = D X := by
  unfold bondDeriv
  rw [iteratedFDeriv_one_apply]
  let ι : (Fin 1 → ℝ) →L[ℝ] imaginaryQuaternions := (ContinuousLinearMap.proj (0 : Fin 1)).smulRight X
  have hι0 : ι 0 = 0 := map_zero ι
  have h1 : HasFDerivAt (fun ξ : imaginaryQuaternions => A (leftTranslate (singleBond x i ξ) W)) D (ι 0) := by
    rw [hι0]; exact hD
  have h2 := h1.comp (0 : Fin 1 → ℝ) ι.hasFDerivAt
  have h3 : (fun τ : Fin 1 → ℝ => A (leftTranslate (bondSpread ![(x, i)] ![X] τ) W)) =
      (fun ξ : imaginaryQuaternions => A (leftTranslate (singleBond x i ξ) W)) ∘ ι := by
    funext τ
    simp only [Function.comp_apply]
    rw [bondSpread_single]
    rfl
  rw [h3, h2.fderiv]
  simp [ι]
theorem expUnit_zero : expUnit (0 : imaginaryQuaternions) = 1 := by apply _root_.YangMills.Construction.TorusFields.expUnit_zero <;> assumption
theorem chartedField_update_eq_leftTranslate (w : F.Site F.depth → Fin 4 → imaginaryQuaternions)
    (V : F.GaugeField F.top) (x : F.Site F.depth) (i : Fin 4) (hx : ¬ IsAxialTreeBond (x, i))
    (v ξ : imaginaryQuaternions) (he : expUnit ξ * expUnit (w x i) = expUnit v) :
    chartedField (Function.update w x (Function.update (w x) i v)) V =
      leftTranslate (singleBond x i ξ) (chartedField w V) := by
  funext y k
  unfold leftTranslate singleBond chartedField
  by_cases h : (x, i) = (y, k)
  · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
    simp only [if_true, update_update_apply, and_self]
    by_cases hc : IsCrossingBond (x, i)
    · simp only [if_pos hc]
      rw [← mul_assoc, he]
    · simp only [if_neg hc, if_neg hx]
      exact he.symm
  · have h2 : ¬ (y = x ∧ k = i) := fun hh => h (by rw [hh.1, hh.2])
    simp only [if_neg h, expUnit_zero, one_mul, update_update_apply, if_neg h2]
theorem hasDerivAt_minimalAction_line (A : F.GaugeField F.depth → ℝ)
    (w : F.Site F.depth → Fin 4 → imaginaryQuaternions) (V : F.GaugeField F.top) (x : F.Site F.depth)
    (i : Fin 4) (hx : ¬ IsAxialTreeBond (x, i)) (e : imaginaryQuaternions) {D : imaginaryQuaternions →L[ℝ] ℝ}
    (hD : HasFDerivAt (fun ξ : imaginaryQuaternions => A (leftTranslate (singleBond x i ξ) (chartedField w V))) D 0)
    {Θ : imaginaryQuaternions × imaginaryQuaternions × imaginaryQuaternions → imaginaryQuaternions}
    {U : Set (imaginaryQuaternions × imaginaryQuaternions × imaginaryQuaternions)} (hU : IsOpen U)
    (hdiag : ∀ r, diagonalTriple r ∈ U) (hcd : ContDiffOn ℝ 3 Θ U)
    (hexp : ∀ z ∈ U, expUnit (Θ z) = expUnit z.1 * expUnit z.2.1 * (expUnit z.2.2)⁻¹)
    (hzero : ∀ r, Θ (diagonalTriple r) = 0) :
    HasDerivAt
      (fun u : ℝ => A (chartedField (Function.update w x (Function.update (w x) i (w x i + u • e))) V))
      (D (fderiv ℝ Θ (diagonalTriple (w x i)) (e, 0, 0))) 0 := by
  set w₀ := w x i with hw₀
  let pt : ℝ → imaginaryQuaternions × imaginaryQuaternions × imaginaryQuaternions :=
    fun u => (w₀ + u • e, 0, w₀)
  have hp0 : pt 0 = diagonalTriple w₀ := by simp [pt, diagonalTriple]
  have hp : HasDerivAt pt (e, (0 : imaginaryQuaternions), (0 : imaginaryQuaternions)) 0 := by
    have h1 : HasDerivAt (fun u : ℝ => w₀ + u • e) e 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).smul_const e).const_add w₀
    exact h1.prodMk ((hasDerivAt_const (0 : ℝ) (0 : imaginaryQuaternions)).prodMk
      (hasDerivAt_const (0 : ℝ) w₀))
  have hΘ : DifferentiableAt ℝ Θ (pt 0) := by
    rw [hp0]
    exact (hcd.contDiffAt (hU.mem_nhds (hdiag w₀))).differentiableAt (by norm_num)
  have hθ := hΘ.hasFDerivAt.comp_hasDerivAt (0 : ℝ) hp
  rw [hp0] at hθ
  have hθ0 : (Θ ∘ pt) 0 = 0 := by
    simp only [Function.comp_apply]
    rw [hp0, hzero]
  rw [← hθ0] at hD
  have hfin := hD.comp_hasDerivAt (0 : ℝ) hθ
  refine hfin.congr_of_eventuallyEq ?_
  have hcont : ContinuousAt pt 0 := hp.continuousAt
  have hUn : U ∈ nhds (pt 0) := by
    rw [hp0]
    exact hU.mem_nhds (hdiag w₀)
  filter_upwards [hcont hUn] with u hu
  simp only [Function.comp_apply]
  rw [chartedField_update_eq_leftTranslate w V x i hx (w₀ + u • e) (Θ (pt u))]
  have := hexp (pt u) hu
  simp only [pt] at this ⊢
  rw [this, expUnit_zero, mul_one, inv_mul_cancel_right]
theorem abs_deriv_sub_le_of_hasDerivAt {E E' A A' : ℝ → ℝ} {dA dA' κ B : ℝ} (hB : 0 ≤ B)
    (hA : HasDerivAt A dA 0) (hA' : HasDerivAt A' dA' 0) (hE : ∀ u, E u - E' u = A u - A' u + κ)
    (hd : |dA - dA'| ≤ B) :
    |deriv E 0 - deriv E' 0| ≤ B := by
  have hR : HasDerivAt (fun u => A u - A' u + κ) (dA - dA') 0 := (hA.sub hA').add_const κ
  have e1 : E' = fun u => E u - (A u - A' u + κ) := by
    funext u
    linarith [hE u]
  have e2 : E = fun u => E' u + (A u - A' u + κ) := by
    funext u
    linarith [hE u]
  by_cases h : DifferentiableAt ℝ E 0
  · have h2 : HasDerivAt E' (deriv E 0 - (dA - dA')) 0 := by
      rw [e1]
      exact h.hasDerivAt.sub hR
    rw [h2.deriv]
    simpa using hd
  · have h2 : ¬ DifferentiableAt ℝ E' 0 := by
      intro h3
      apply h
      rw [e2]
      exact h3.add hR.differentiableAt
    rw [deriv_zero_of_not_differentiableAt h, deriv_zero_of_not_differentiableAt h2]
    simpa using hB
theorem chartedEnergy_eq (a : ℝ) (w : F.Site F.depth → Fin 4 → imaginaryQuaternions) (V : F.GaugeField F.top) :
    chartedEnergy a w V = minimalAction a (finiteCells F) F.depth (chartedField w V) +
      a * ∑ c ∈ innerBonds (finiteCells F) (F.depth + 1), blockFit (chartedField w V) V c := rfl
theorem sum_blockFit_sub_eq {L r : ℕ} (hF : F.blockSide = L) (hF' : F'.blockSide = L) (hL : Odd L)
    (hs : ∀ i, 2 ≤ F.extent i) (hs' : ∀ i, 2 ≤ F'.extent i)
    {w u : F.Site F.depth → Fin 4 → imaginaryQuaternions} {w' u' : F'.Site F'.depth → Fin 4 → imaginaryQuaternions}
    {V : F.GaugeField F.top} {V' : F'.GaugeField F'.top} {Y : F.Cell} {Y' : F'.Cell}
    (hV : ∀ b, BondWithinRadius r b →
      V (Y + siteOfCoords F.top b.1) b.2 = V' (Y' + siteOfCoords F'.top b.1) b.2)
    (hw : ∀ (g q : LatticeOffset) (j : Fin 4), WithinRadius r g → q ∈ centredCube L →
      fineBondAt Y g q j ∈ chordBonds (finiteCells F) →
        w (fineBondAt Y g q j).1 j = w' (fineBondAt Y' g q j).1 j)
    (hu : ∀ (g q : LatticeOffset) (j : Fin 4), WithinRadius r g → q ∈ centredCube L →
      fineBondAt Y g q j ∈ chordBonds (finiteCells F) →
        u (fineBondAt Y g q j).1 j = u' (fineBondAt Y' g q j).1 j)
    {h o : LatticeOffset} (ho : o ∈ centredCube L)
    (hh : ∀ d, WithinRadius r h ∧ WithinRadius r (h + Pi.single d 1) ∧ WithinRadius r (h - Pi.single d 1))
    (hoff : ∀ y k, y ≠ (fineBondAt Y h o 0).1 → u y k = w y k)
    (hoff' : ∀ y k, y ≠ (fineBondAt Y' h o 0).1 → u' y k = w' y k) :
    ∑ c ∈ innerBonds (finiteCells F) (F.depth + 1),
        (blockFit (chartedField u V) V c - blockFit (chartedField w V) V c) =
      ∑ c ∈ innerBonds (finiteCells F') (F'.depth + 1),
        (blockFit (chartedField u' V') V' c - blockFit (chartedField w' V') V' c) := by
  have hLF : Odd F.blockSide := by rw [hF]; exact hL
  have hLF' : Odd F'.blockSide := by rw [hF']; exact hL
  have hoF : o ∈ centredCube F.blockSide := by rw [hF]; exact ho
  have hoF' : o ∈ centredCube F'.blockSide := by rw [hF']; exact ho
  have key : ∀ {H : BlockFrame} (hLH : Odd H.blockSide) (hsH : ∀ i, 2 ≤ H.extent i)
      (v v₀ : H.Site H.depth → Fin 4 → imaginaryQuaternions)
      (U : H.GaugeField H.top) (Z : H.Cell) (hoH : o ∈ centredCube H.blockSide)
      (hv : ∀ y k, y ≠ (fineBondAt Z h o 0).1 → v y k = v₀ y k),
      ∑ c ∈ innerBonds (finiteCells H) (H.depth + 1),
          (blockFit (chartedField v U) U c - blockFit (chartedField v₀ U) U c) =
        ∑ d : Fin 4, ((blockFit (chartedField v U) U (Z + siteOfCoords H.top h, d) -
            blockFit (chartedField v₀ U) U (Z + siteOfCoords H.top h, d)) +
          (blockFit (chartedField v U) U (Z + siteOfCoords H.top h - unitStep H.top d, d) -
            blockFit (chartedField v₀ U) U (Z + siteOfCoords H.top h - unitStep H.top d, d))) := by
    intro H hLH hsH v v₀ U Z hoH hv
    refine sum_innerBonds_eq_of_local hsH
      (fun c => blockFit (chartedField v U) U c - blockFit (chartedField v₀ U) U c) _ ?_
    intro c h1 h2
    have hcell : enclosingCell (fineBondAt Z h o 0).1 = Z + siteOfCoords H.top h :=
      enclosingCell_offset hLH hsH _ o hoH
    have hag : ∀ y k, y ≠ (fineBondAt Z h o 0).1 → chartedField v U y k = chartedField v₀ U y k := by
      intro y k hy
      unfold chartedField
      rw [hv y k hy]
    have hm := contourAverage_eq_of_ne hLH hsH c (fineBondAt Z h o 0).1 hag (by rw [hcell]; exact h1)
      (by rw [hcell]; exact h2)
    simp only [blockFit]
    rw [hm]
    ring
  rw [key hLF hs u w V Y hoF hoff, key hLF' hs' u' w' V' Y' hoF' hoff']
  refine Finset.sum_congr rfl fun d _ => ?_
  have e1 : ∀ {H : BlockFrame} (Z : H.Cell),
      Z + siteOfCoords H.top h - unitStep H.top d = Z + siteOfCoords H.top (h - Pi.single d 1) := by
    intro H Z
    have : (siteOfCoords H.top (h - Pi.single d 1) : H.Cell) = siteOfCoords H.top h - unitStep H.top d := by
      funext l
      simp [siteOfCoords, unitStep]
    rw [this, add_sub_assoc]
  rw [e1 Y, e1 Y']
  obtain ⟨b0, b1, b2⟩ := hh d
  have b3 : WithinRadius r (h - Pi.single d 1 + Pi.single d 1) := by simpa using b0
  rw [blockFit_eq_of_agree hF hF' hL hs hs' hV hu h d b0 b1, blockFit_eq_of_agree hF hF' hL hs hs' hV hw h d b0 b1,
    blockFit_eq_of_agree hF hF' hL hs hs' hV hu _ d b2 b3, blockFit_eq_of_agree hF hF' hL hs hs' hV hw _ d b2 b3]
set_option maxHeartbeats 2000000 in
theorem chartedSlope_close {a : ℝ} {L : ℕ} {c : ColdChainParameters} (hodd : Odd L) (hL40 : 2 ^ 40 ≤ L)
    (hδ : 0 < c.δ₂) {Cc : ℝ} (hCc : 0 < Cc)
    (han : ∀ (F : BlockFrame) (W : F.GaugeField F.depth), IsBlockTorus L F → IsSmallCurvature c.s₀ W →
      ∀ (k : ℕ) (b : Fin k → F.Site F.depth × Fin 4) (X : Fin k → imaginaryQuaternions),
        AnalyticAt ℝ (fun τ : Fin k → ℝ =>
          minimalAction a (finiteCells F) F.depth (leftTranslate (bondSpread b X τ) W)) 0)
    (hcmp : ∀ (F F' : BlockFrame) (W : F.GaugeField F.depth) (W' : F'.GaugeField F'.depth) (y : F.Site F.depth)
      (y' : F'.Site F'.depth) (R : ℕ),
      IsBlockTorus L F → IsBlockTorus L F' → F'.depth = F.depth → IsSmallCurvature c.s₀ W →
      IsSmallCurvature c.s₀ W' → AgreeOnBox W W' y y' R → 2 ≤ R →
      ∀ (i : Fin 4) (X : imaginaryQuaternions), ‖X‖ = 1 →
        |bondDeriv (minimalAction a (finiteCells F) F.depth) W ![(y, i)] ![X] -
          bondDeriv (minimalAction a (finiteCells F') F'.depth) W' ![(y', i)] ![X]| ≤
          Cc * Real.exp (-(c.δ₂ * R)))
    {Θ : imaginaryQuaternions × imaginaryQuaternions × imaginaryQuaternions → imaginaryQuaternions}
    {U : Set (imaginaryQuaternions × imaginaryQuaternions × imaginaryQuaternions)} {CΘ : ℝ}
    (hU : IsOpen U) (hC0 : 0 ≤ CΘ)
    (hdiag : ∀ r, diagonalTriple r ∈ U) (hcd : ContDiffOn ℝ 3 Θ U)
    (hexp : ∀ z ∈ U, expUnit (Θ z) = expUnit z.1 * expUnit z.2.1 * (expUnit z.2.2)⁻¹)
    (hzero : ∀ r, Θ (diagonalTriple r) = 0)
    (hbd : ∀ (r : imaginaryQuaternions) (j : ℕ), ‖r‖ ≤ 1 → j ≤ 3 →
      ‖iteratedFDeriv ℝ j Θ (diagonalTriple r)‖ ≤ CΘ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (F F' : BlockFrame) (w : F.Site F.depth → Fin 4 → imaginaryQuaternions)
        (w' : F'.Site F'.depth → Fin 4 → imaginaryQuaternions) (V : F.GaugeField F.top)
        (V' : F'.GaugeField F'.top) (Y : F.Cell) (Y' : F'.Cell) (r : ℕ), 1 ≤ r → IsBlockTorus L F →
        IsBlockTorus L F' → F'.depth = F.depth → IsAdmissibleChartPoint L c.s₀ w V →
        IsAdmissibleChartPoint L c.s₀ w' V' →
        AgreeOnBall (finiteCells F) V (finiteCells F') V' Y Y' r →
        (∀ (h o : Fin 4 → ℤ) (i : Fin 4), WithinRadius r h → o ∈ centredCube L →
          fineBondAt Y h o i ∈ chordBonds (finiteCells F) →
          w (fineBondAt Y h o i).1 i = w' (fineBondAt Y' h o i).1 i) →
        ∀ (h o : Fin 4 → ℤ) (i : Fin 4) (e : imaginaryQuaternions), IsFineBondWithinRadius Y (r / 2) h o i →
          ‖e‖ = 1 →
          |chartedSlope a w V (fineBondAt Y h o i) e - chartedSlope a w' V' (fineBondAt Y' h o i) e| ≤
            C * Real.exp (-(c.δ₂ * ((L : ℝ) * ((r : ℝ) / 2) - 2 * L - 1))) := by
  refine ⟨Cc * (CΘ + 1), by positivity, ?_⟩
  intro F F' w w' V V' Y Y' r hr hT hT' ht hsm hsm' hag hww h o i e hin he
  have hT0 := hT
  have hT0' := hT'
  obtain ⟨hF, n, hn, hside⟩ := hT
  obtain ⟨hF', n', hn', hside'⟩ := hT'
  have hs : ∀ i, 2 ≤ F.extent i := fun i => by rw [hside]; omega
  have hs' : ∀ i, 2 ≤ F'.extent i := fun i => by rw [hside']; omega
  obtain ⟨sd0, sd0', -, hV⟩ := hag
  have sd : ∀ i, 2 * r + 2 < F.extent i := fun i => by
    rcases sd0 i with h0 | h0
    · have := hside i
      omega
    · exact h0
  have sd' : ∀ i, 2 * r + 2 < F'.extent i := fun i => by
    rcases sd0' i with h0 | h0
    · have := hside' i
      omega
    · exact h0
  obtain ⟨ho, hch, hbox, -, -⟩ := hin
  have hoL : o ∈ centredCube L := by rw [← hF]; exact ho
  have hoF' : o ∈ centredCube F'.blockSide := by rw [hF']; exact hoL
  have hLF : Odd F.blockSide := by rw [hF]; exact hodd
  have hLF' : Odd F'.blockSide := by rw [hF']; exact hodd
  obtain ⟨m, hm⟩ : ∃ m, m = r / 2 := ⟨_, rfl⟩
  obtain ⟨m', hm'⟩ : ∃ m', m' = r - r / 2 := ⟨_, rfl⟩
  rw [← hm] at hbox
  have hrm : r = m + m' := by omega
  have hm1 : m + 1 ≤ r := by omega
  have hm1' : 1 ≤ m' := by omega
  have hmr' : m' ≤ r := by omega
  have hhr : WithinRadius r h := fun l => (hbox l).trans (by exact_mod_cast (by omega : m ≤ r))
  have hh : ∀ d, WithinRadius r h ∧ WithinRadius r (h + Pi.single d 1) ∧
      WithinRadius r (h - Pi.single d 1) := by
    intro d
    refine ⟨hhr, fun l => ?_, fun l => ?_⟩
    · have b := abs_le.1 (hbox l)
      have hc : (m : ℤ) + 1 ≤ r := by exact_mod_cast hm1
      rw [abs_le]
      by_cases hl : l = d
      · subst hl
        simp only [Pi.add_apply, Pi.single_eq_same]
        constructor <;> omega
      · simp only [Pi.add_apply, Pi.single_eq_of_ne hl, add_zero]
        constructor <;> omega
    · have b := abs_le.1 (hbox l)
      have hc : (m : ℤ) + 1 ≤ r := by exact_mod_cast hm1
      rw [abs_le]
      by_cases hl : l = d
      · subst hl
        simp only [Pi.sub_apply, Pi.single_eq_same]
        constructor <;> omega
      · simp only [Pi.sub_apply, Pi.single_eq_of_ne hl, sub_zero]
        constructor <;> omega
  obtain ⟨x, hxdef⟩ : ∃ x, x = (fineBondAt Y h o i).1 := ⟨_, rfl⟩
  obtain ⟨x', hxdef'⟩ : ∃ x', x' = (fineBondAt Y' h o i).1 := ⟨_, rfl⟩
  have hw₀ : w x i = w' x' i := by
    rw [hxdef, hxdef']
    exact hww h o i hhr hoL hch
  let wu : ℝ → F.Site F.depth → Fin 4 → imaginaryQuaternions :=
    fun u => Function.update w x (Function.update (w x) i (w x i + u • e))
  let wu' : ℝ → F'.Site F'.depth → Fin 4 → imaginaryQuaternions :=
    fun u => Function.update w' x' (Function.update (w' x') i (w' x' i + u • e))
  have hu : ∀ (u : ℝ) (g q : LatticeOffset) (j : Fin 4), WithinRadius r g → q ∈ centredCube L →
      fineBondAt Y g q j ∈ chordBonds (finiteCells F) →
        wu u (fineBondAt Y g q j).1 j = wu' u (fineBondAt Y' g q j).1 j := by
    intro u g q j hg hq hmem
    have hqF : q ∈ centredCube F.blockSide := by rw [hF]; exact hq
    have hqF' : q ∈ centredCube F'.blockSide := by rw [hF']; exact hq
    have i1 : (fineBondAt Y g q j).1 = x ↔ g = h ∧ q = o := by
      rw [hxdef]
      exact fineSite_eq_iff hLF hs sd hg hhr hqF ho
    have i2 : (fineBondAt Y' g q j).1 = x' ↔ g = h ∧ q = o := by
      rw [hxdef']
      exact fineSite_eq_iff hLF' hs' sd' hg hhr hqF' hoF'
    have e3 : ((fineBondAt Y g q j).1 = x ∧ j = i) ↔ ((fineBondAt Y' g q j).1 = x' ∧ j = i) := by
      rw [i1, i2]
    simp only [wu, wu', update_update_apply]
    by_cases c1 : (fineBondAt Y g q j).1 = x ∧ j = i
    · rw [if_pos c1, if_pos (e3.1 c1), hw₀]
    · rw [if_neg c1, if_neg (fun hc => c1 (e3.2 hc))]
      exact hww g q j hg hq hmem
  have hoff : ∀ (u : ℝ) (y : F.Site F.depth) (k : Fin 4), y ≠ (fineBondAt Y h o 0).1 → wu u y k = w y k := by
    intro u y k hy
    simp only [wu, update_update_apply]
    exact if_neg fun hc => hy (hc.1.trans hxdef)
  have hoff' : ∀ (u : ℝ) (y : F'.Site F'.depth) (k : Fin 4), y ≠ (fineBondAt Y' h o 0).1 →
      wu' u y k = w' y k := by
    intro u y k hy
    simp only [wu', update_update_apply]
    exact if_neg fun hc => hy (hc.1.trans hxdef')
  have hfit := fun u : ℝ =>
    sum_blockFit_sub_eq hF hF' hodd hs hs' hV hww (hu u) hoL hh (hoff u) (hoff' u)
  obtain ⟨D, hD⟩ := exists_hasFDerivAt_singleBond (minimalAction a (finiteCells F) F.depth)
    (chartedField w V) x i (fun k X => han F _ hT0 hsm.small_curvature k _ X)
  obtain ⟨D', hD'⟩ := exists_hasFDerivAt_singleBond (minimalAction a (finiteCells F') F'.depth)
    (chartedField w' V') x' i (fun k X => han F' _ hT0' hsm'.small_curvature k _ X)
  have hnt : ¬ IsAxialTreeBond (x, i) := by
    have h1 := hch
    simp only [chordBonds, Finset.mem_filter] at h1
    rw [hxdef]
    exact h1.2
  have hnt' : ¬ IsAxialTreeBond (x', i) := by
    rw [hxdef']
    intro htree
    apply hnt
    rw [hxdef]
    have c1 := isCrossingBond_iff hLF hs (Y + siteOfCoords F.top h) o ho i
    have c2 := isCrossingBond_iff hLF' hs' (Y' + siteOfCoords F'.top h) o hoF' i
    have o1 := cellOffset_offset hLF hs (Y + siteOfCoords F.top h) o ho
    have o2 := cellOffset_offset hLF' hs' (Y' + siteOfCoords F'.top h) o hoF'
    rw [hF] at c1
    rw [hF'] at c2
    refine ⟨fun hc => htree.1 (c2.2 (c1.1 hc)), fun l hl => ?_⟩
    have := htree.2 l hl
    simp only [fineBondAt] at this ⊢
    rw [o2] at this
    rw [o1]
    exact this
  have hA := hasDerivAt_minimalAction_line (minimalAction a (finiteCells F) F.depth) w V x i hnt e hD hU hdiag
    hcd hexp hzero
  have hA' := hasDerivAt_minimalAction_line (minimalAction a (finiteCells F') F'.depth) w' V' x' i hnt' e hD'
    hU hdiag hcd hexp hzero
  have hsmall : ‖w x i‖ ≤ 1 := by
    have h1 := hsm.coord_small (x, i) (by rw [hxdef]; exact hch)
    have hLpos : (1 : ℝ) ≤ L := by exact_mod_cast hodd.pos
    have h2 : 1 / (64 * (L : ℝ)) ≤ 1 := by
      rw [div_le_one (by positivity)]
      linarith
    exact h1.trans h2
  obtain ⟨Z, hZdef⟩ : ∃ Z, Z = fderiv ℝ Θ (diagonalTriple (w x i))
      (e, (0 : imaginaryQuaternions), (0 : imaginaryQuaternions)) := ⟨_, rfl⟩
  have hZ' : fderiv ℝ Θ (diagonalTriple (w' x' i)) (e, (0 : imaginaryQuaternions), (0 : imaginaryQuaternions)) = Z := by
    rw [← hw₀, hZdef]
  rw [← hZdef] at hA
  rw [hZ'] at hA'
  have hZ : ‖Z‖ ≤ CΘ := by
    have h1 := hbd (w x i) 1 hsmall (by norm_num)
    rw [norm_iteratedFDeriv_one] at h1
    have h2 : ‖((e, (0 : imaginaryQuaternions), (0 : imaginaryQuaternions)) :
        imaginaryQuaternions × imaginaryQuaternions × imaginaryQuaternions)‖ = 1 := by
      simp [Prod.norm_def, he]
    rw [hZdef]
    calc _ ≤ ‖fderiv ℝ Θ (diagonalTriple (w x i))‖ *
          ‖((e, (0 : imaginaryQuaternions), (0 : imaginaryQuaternions)) :
            imaginaryQuaternions × imaginaryQuaternions × imaginaryQuaternions)‖ :=
          ContinuousLinearMap.le_opNorm _ _
      _ ≤ CΘ := by rw [h2, mul_one]; exact h1
  have hLpos : 0 < L := hodd.pos
  have hLbig : 4 ≤ L := le_trans (by norm_num) hL40
  obtain ⟨R, hR⟩ : ∃ R, R + 1 = L * m' := ⟨L * m' - 1, by
    have : 1 ≤ L * m' := Nat.mul_pos hLpos hm1'
    omega⟩
  have hR2 : 2 ≤ R := by
    have : L * 1 ≤ L * m' := Nat.mul_le_mul_left _ hm1'
    omega
  have hL0 : (0 : ℤ) < L := by exact_mod_cast hLpos
  have hRz : (R : ℤ) = (L : ℤ) * m' - 1 := by
    have : ((R + 1 : ℕ) : ℤ) = ((L * m' : ℕ) : ℤ) := by rw [hR]
    push_cast at this
    linarith
  have hLr : (L : ℤ) * r = (L : ℤ) * m + (L : ℤ) * m' := by
    rw [← mul_add, hrm]
    push_cast
    ring
  let p₀ : LatticeOffset := fun l => (L : ℤ) * h l + o l
  have hx : x = siteAtOffset Y p₀ := by
    have := siteAtOffset_block Y h o
    simp only [hF] at this
    rw [hxdef]
    exact this.symm
  have hx' : x' = siteAtOffset Y' p₀ := by
    have := siteAtOffset_block Y' h o
    simp only [hF'] at this
    rw [hxdef']
    exact this.symm
  have nearA : ∀ z : LatticeOffset, WithinRadius R z → NearBlocks L r (p₀ + z) := by
    intro z hz l
    have b1 := abs_le.1 (hbox l)
    have b2 := (mem_centredCube_iff o).1 hoL l
    have b3 := abs_le.1 (hz l)
    have m1 := mul_le_mul_of_nonneg_left b1.2 hL0.le
    have m2 := mul_le_mul_of_nonneg_left b1.1 hL0.le
    simp only [p₀, Pi.add_apply]
    rw [abs_le]
    constructor <;> linarith
  have hagree : AgreeOnBox (chartedField w V) (chartedField w' V') x x' R := by
    refine ⟨fun l => ?_, fun l => ?_, fun b hb => ?_⟩
    · rw [period_depth]
      have h1 := sd l
      have h2 : 2 * m' < F.extent l := by omega
      have h3 : 2 * R + 2 = 2 * (L * m') := by omega
      rw [h3, hF]
      nlinarith
    · rw [period_depth]
      have h1 := sd' l
      have h2 : 2 * m' < F'.extent l := by omega
      have h3 : 2 * R + 2 = 2 * (L * m') := by omega
      rw [h3, hF']
      nlinarith
    · have hadd : ∀ {H : BlockFrame} (Z : H.Cell) (p z : LatticeOffset),
          siteAtOffset Z p + siteOfCoords H.depth z = siteAtOffset Z (p + z) := by
        intro H Z p z
        unfold siteAtOffset
        rw [add_assoc, ← siteOfCoords_add]
      rw [hx, hx', hadd, hadd]
      refine chartedField_eq_of_agree hF hF' hodd hs hs' hV hww (p₀ + b.1) b.2 (nearA _ hb.1) ?_
      have := nearA _ hb.2
      rwa [← add_assoc] at this
  have hbound : |D Z - D' Z| ≤ Cc * (CΘ + 1) * Real.exp (-(c.δ₂ * ((L : ℝ) * ((r : ℝ) / 2) - 2 * L - 1))) := by
    have hexpos := Real.exp_pos (-(c.δ₂ * ((L : ℝ) * ((r : ℝ) / 2) - 2 * L - 1)))
    by_cases hZ0 : Z = 0
    · rw [hZ0]
      simp only [map_zero, sub_zero, abs_zero]
      positivity
    have hnZ : ‖Z‖ ≠ 0 := norm_ne_zero_iff.2 hZ0
    obtain ⟨X₀, hX₀⟩ : ∃ X₀ : imaginaryQuaternions, X₀ = ‖Z‖⁻¹ • Z := ⟨_, rfl⟩
    have hunit : ‖X₀‖ = 1 := by
      rw [hX₀, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hnZ]
    have hc1 := hcmp F F' _ _ x x' R hT0 hT0' ht hsm.small_curvature hsm'.small_curvature hagree hR2 i _ hunit
    rw [bondDeriv_single_eq hD, bondDeriv_single_eq hD'] at hc1
    have hZs : ‖Z‖ • X₀ = Z := by
      rw [hX₀, smul_smul, mul_inv_cancel₀ hnZ, one_smul]
    have e1 : D Z - D' Z = ‖Z‖ * (D X₀ - D' X₀) := by
      have h1 : D Z = ‖Z‖ * D X₀ := by
        rw [← smul_eq_mul, ← map_smul, hZs]
      have h2 : D' Z = ‖Z‖ * D' X₀ := by
        rw [← smul_eq_mul, ← map_smul, hZs]
      rw [h1, h2]
      ring
    rw [e1, abs_mul, abs_norm]
    have hRr : (L : ℝ) * ((r : ℝ) / 2) - 2 * L - 1 ≤ R := by
      have h1 : ((R : ℝ) + 1) = (L : ℝ) * m' := by exact_mod_cast hR
      have h2 : (r : ℝ) ≤ 2 * m' := by exact_mod_cast (by omega : r ≤ 2 * m')
      have hLr0 : (0 : ℝ) ≤ L := by positivity
      nlinarith
    have hle : Real.exp (-(c.δ₂ * R)) ≤ Real.exp (-(c.δ₂ * ((L : ℝ) * ((r : ℝ) / 2) - 2 * L - 1))) := by
      apply Real.exp_le_exp.2
      have := mul_le_mul_of_nonneg_left hRr hδ.le
      linarith
    calc ‖Z‖ * |D X₀ - D' X₀|
        ≤ CΘ * (Cc * Real.exp (-(c.δ₂ * ((L : ℝ) * ((r : ℝ) / 2) - 2 * L - 1)))) := by
          refine mul_le_mul hZ (hc1.trans ?_) (abs_nonneg _) hC0
          exact mul_le_mul_of_nonneg_left hle hCc.le
      _ ≤ Cc * (CΘ + 1) * Real.exp (-(c.δ₂ * ((L : ℝ) * ((r : ℝ) / 2) - 2 * L - 1))) := by
          have : 0 ≤ Cc * Real.exp (-(c.δ₂ * ((L : ℝ) * ((r : ℝ) / 2) - 2 * L - 1))) := by positivity
          nlinarith
  have hE : ∀ u : ℝ, chartedEnergy a (wu u) V - chartedEnergy a (wu' u) V' =
      (minimalAction a (finiteCells F) F.depth (chartedField (wu u) V) -
        minimalAction a (finiteCells F') F'.depth (chartedField (wu' u) V')) +
      (a * ∑ c ∈ innerBonds (finiteCells F) (F.depth + 1), blockFit (chartedField w V) V c -
        a * ∑ c ∈ innerBonds (finiteCells F') (F'.depth + 1), blockFit (chartedField w' V') V' c) := by
    intro u
    have h1 := hfit u
    rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib] at h1
    rw [chartedEnergy_eq, chartedEnergy_eq]
    linear_combination a * h1
  have hfin := abs_deriv_sub_le_of_hasDerivAt (E := fun u => chartedEnergy a (wu u) V)
    (E' := fun u => chartedEnergy a (wu' u) V') (by positivity) hA hA' hE hbound
  subst hxdef
  subst hxdef'
  exact hfin
end ChartSlopeOnTwoTori
theorem chartedSlopeComparison_holds (hlog : ConjugatedExpLogSmooth)
    (hchain : ColdEstimatesAtEveryDepth) (hbelow : MinimalActionDerivComparison) :
    ChartedSlopeComparison := by
  intro a L c ha hodd hL hc
  obtain ⟨Θ, U, CΘ, hU, hC0, hdiag, hcd, hexp, hzero, hbd, -, -⟩ := hlog
  obtain ⟨N, -, hold, -⟩ := hchain a L c ha hodd hL hc
  obtain ⟨Cc, hCc, hcmp⟩ := hbelow a L c ha hodd hL hc
  obtain ⟨⟨-, -, hs0, hδ, -⟩, -⟩ := hc.classical
  have hsσ : c.s₀ ≤ c.σA := by
    have := hc.inequalities.2.2.1
    linarith
  exact ChartSlopeOnTwoTori.chartedSlope_close hodd hL hδ hCc
    (fun F W hT hcold k b X => (hold F c.s₀ W hT hs0 hsσ hcold).minimalAction_analytic k b X) hcmp hU hC0
    hdiag hcd hexp hzero hbd
end ColdStepAtMirrorFrames
end YangMills.Construction
end
