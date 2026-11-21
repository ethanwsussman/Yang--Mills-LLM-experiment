import YangMills.Construction.ResponseInTheExpansion.ScoreAtTheFrameProof
import YangMills.Construction.ColdStepAtMirrorFrames.BlockEnergyOnTwoTori
import YangMills.Construction.ColdStepAtMirrorFrames.DerivativesOfTheGroupGap
import YangMills.Construction.ColdStepAtMirrorFrames.GroupGapIsSmooth
import YangMills.Construction.ColdStepAtMirrorFrames.TermsBetweenCompareOnTwoTori
import YangMills.Construction.ResponseInTheExpansion.ChartBetweenTwoTori
import YangMills.Construction.RunningCouplingSlope.ValueOfTheDensityOfTheStepOnTwoToriAtParametersProof
import YangMills.Construction.SummableBoundsOfTheFlow.KernelsAtTheFramesBetween
import YangMills.Construction.SummableBoundsOfTheFlow.TheFramesBetween
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction.WeightedResponses
open YangMills.Construction.BlockAverages YangMills.Construction.ColdStepAtMirrorFrames YangMills.Construction.Interpolation YangMills.Construction.TorusComparison YangMills.Construction.ChartTransfer YangMills.Construction.SecondOrderMoves
variable {F F' : BlockFrame}
section Values
variable {ι : Type} [Fintype ι] [DecidableEq ι] {T : _root_.YangMills.Construction.ColdStepAtMirrorFrames.StepParameters} {x : ℝ} {V : F.GaugeField F.top}
  {V' : F'.GaugeField F'.top} {Y : F.Cell} {Y' : F'.Cell} {q : ℕ} {j : ι → ↥(chordBonds (finiteCells F))}
  {j' : ι → ↥(chordBonds (finiteCells F'))}
private def cellEnergyConstant (T : _root_.YangMills.Construction.ColdStepAtMirrorFrames.StepParameters) (C : ℝ) (Ck : ℕ → ℝ) : ℝ :=
  bondMoveConstant (valueConstant T C (Ck 1)) (2 * Ck 2) T.ballRadius
private theorem abs_cellIncrement_sub_le (hD : Estimates.cellOffsetStatement) (hS : SiteDecomposition)
    (hM : ChartLipschitz.ChartedFieldLipschitz) (hc : Calculus.CompositeDerivativesAtPoint)
    (P : TorusPairData T x V V' Y Y' q j j') {C : ℝ} {Ck : ℕ → ℝ} (hC : 0 ≤ C) (hCk : ∀ k, 0 < Ck k)
    (hB : CellEnergyComparison T C) (hK : CellEnergyKernels T Ck) (f : LocalFamily) {ζ : BondField ι}
    (hζ : ∀ i, ‖ζ i‖ < T.ballRadius) :
    |(coldHalfLawAt T x f).blockIncrement Y (toTorus j ζ) V -
        (coldHalfLawAt T x f).blockIncrement Y' (toTorus j' ζ) V'| ≤
      Real.exp (-(4 * T.κ * q)) * (cellEnergyConstant T C Ck * weightedBondNorm T.κ Y j ζ) := by
  have h := abs_move_sub_le P (E := fun u => cellEnergyShare T.a Y u V) (E' := fun u => cellEnergyShare T.a Y' u V')
    (valueConstant_pos P hC (hCk 1).le) (K := valueConstant T C (Ck 1)) (A := Ck 2) (hCk 2).le
    (fun ζ hζ => abs_cellEnergyShare_sub_le hD hS hM hc P hC hCk hB hK hζ)
    (fun u hu b X hX => by
      obtain ⟨h1, -, h2⟩ := cellEnergyShare_line_bounds hc (fun k l => hK F u V P.torus hu Y k l) b hX
      refine ⟨h1, h2.trans ?_⟩
      have := exp_neg_δ₁_le_one P (cellSupDist Y (enclosingCell b.1))
      have := hCk 2
      nlinarith)
    (fun u hu b X hX => by
      obtain ⟨h1, -, h2⟩ := cellEnergyShare_line_bounds hc (fun k l => hK F' u V' P.torus' hu Y' k l) b hX
      refine ⟨h1, h2.trans ?_⟩
      have := exp_neg_δ₁_le_one P (cellSupDist Y' (enclosingCell b.1))
      have := hCk 2
      nlinarith) hζ
  have e : (coldHalfLawAt T x f).blockIncrement Y (toTorus j ζ) V -
      (coldHalfLawAt T x f).blockIncrement Y' (toTorus j' ζ) V' =
      (cellEnergyShare T.a Y (chartPoint T x V j ζ) V - cellEnergyShare T.a Y' (chartPoint T x V' j' ζ) V') -
      (cellEnergyShare T.a Y (chartPoint T x V j 0) V - cellEnergyShare T.a Y' (chartPoint T x V' j' 0) V') := by
    rw [chartPoint_zero, chartPoint_zero]
    simp only [ColdHalfLaw.blockIncrement, ColdHalfLaw.blockCost, chartPoint, coldHalfLawAt]
    ring
  rw [e]
  exact h
private def shareConstant (T : _root_.YangMills.Construction.ColdStepAtMirrorFrames.StepParameters) (C : ℝ) (Ck : ℕ → ℝ) : ℝ :=
  ((centredCube T.L).card : ℝ) * bondMoveConstant (valueConstant T C (Ck 1)) (2 * Ck 2) T.ballRadius
private theorem abs_shareIncrement_sub_le (hD : Estimates.cellOffsetStatement) (hS : SiteDecomposition)
    (hM : ChartLipschitz.ChartedFieldLipschitz) (hc : Calculus.CompositeDerivativesAtPoint)
    (P : TorusPairData T x V V' Y Y' q j j') {C : ℝ} {Ck : ℕ → ℝ} (hC : 0 ≤ C) (hCk : ∀ k, 0 < Ck k)
    (hB : ChartComparison T C) (hK : SiteShareKernels T Ck) {o : Fin 4 → ℤ} (ho : o ∈ centredCube T.L)
    {ζ : BondField ι} (hζ : ∀ i, ‖ζ i‖ < T.ballRadius) :
    |(minimalSiteShare T.a (cellCentre F.depth Y + siteOfCoords F.depth o) (chartedField (chartPoint T x V j ζ) V) -
        minimalSiteShare T.a (cellCentre F'.depth Y' + siteOfCoords F'.depth o)
          (chartedField (chartPoint T x V' j' ζ) V')) -
      (minimalSiteShare T.a (cellCentre F.depth Y + siteOfCoords F.depth o) (chartedField (chartPoint T x V j 0) V) -
        minimalSiteShare T.a (cellCentre F'.depth Y' + siteOfCoords F'.depth o)
          (chartedField (chartPoint T x V' j' 0) V'))| ≤
      Real.exp (-(4 * T.κ * q)) *
        (bondMoveConstant (valueConstant T C (Ck 1)) (2 * Ck 2) T.ballRadius * weightedBondNorm T.κ Y j ζ) := by
  exact abs_move_sub_le P
    (E := fun u => minimalSiteShare T.a (cellCentre F.depth Y + siteOfCoords F.depth o) (chartedField u V))
    (E' := fun u => minimalSiteShare T.a (cellCentre F'.depth Y' + siteOfCoords F'.depth o) (chartedField u V'))
    (valueConstant_pos P hC (hCk 1).le) (K := valueConstant T C (Ck 1)) (A := Ck 2) (hCk 2).le
    (fun ζ hζ => abs_minimalSiteShare_sub_le hD hS hM hc P hC hCk hB hK hζ ho)
    (fun u hu b X hX => by
      obtain ⟨h1, -, h2⟩ := minimalSiteShare_line_bounds hc (fun k l => hK F u V P.torus hu _ k l) b hX
      refine ⟨h1, h2.trans ?_⟩
      have := exp_neg_δ₁_le_one P
        (cellSupDist (enclosingCell (cellCentre F.depth Y + siteOfCoords F.depth o)) (enclosingCell b.1))
      have := hCk 2
      nlinarith)
    (fun u hu b X hX => by
      obtain ⟨h1, -, h2⟩ := minimalSiteShare_line_bounds hc (fun k l => hK F' u V' P.torus' hu _ k l) b hX
      refine ⟨h1, h2.trans ?_⟩
      have := exp_neg_δ₁_le_one P
        (cellSupDist (enclosingCell (cellCentre F'.depth Y' + siteOfCoords F'.depth o)) (enclosingCell b.1))
      have := hCk 2
      nlinarith) hζ
end Values
section OneTorus
variable {ι : Type} [Fintype ι] [DecidableEq ι] {T : _root_.YangMills.Construction.ColdStepAtMirrorFrames.StepParameters} {x : ℝ} {V V' : F.GaugeField F.top}
  {Y : F.Cell} {q : ℕ} {j j' : ι → ↥(chordBonds (finiteCells F))}
private theorem abs_weightedIncrement_sub_le (hD : Estimates.cellOffsetStatement) (hS : SiteDecomposition)
    (hM : ChartLipschitz.ChartedFieldLipschitz) (hc : Calculus.CompositeDerivativesAtPoint)
    (P : TorusPairData T x V V' Y Y q j j') {C : ℝ} {Ck : ℕ → ℝ} (hC : 0 ≤ C) (hCk : ∀ k, 0 < Ck k)
    (hB : ChartComparison T C) (hK : SiteShareKernels T Ck) (f : LocalFamily) {ζ : BondField ι}
    (hζ : ∀ i, ‖ζ i‖ < T.ballRadius) {w : F.Site F.depth → ℝ} {B : ℝ} (hB0 : 0 < B) (hw : ∀ y, |w y| ≤ B) :
    |(coldHalfLawAt T x f).weightedShareIncrement w Y (toTorus j ζ) V -
        (coldHalfLawAt T x f).weightedShareIncrement w Y (toTorus j' ζ) V'| ≤
      Real.exp (-(4 * T.κ * q)) * (shareConstant T C Ck * B * weightedBondNorm T.κ Y j ζ) := by
  classical
  set M := Real.exp (-(4 * T.κ * q)) *
    (bondMoveConstant (valueConstant T C (Ck 1)) (2 * Ck 2) T.ballRadius * weightedBondNorm T.κ Y j ζ) with hMdef
  have hs2 := P.two_le_extent
  obtain ⟨b1, b2, -, -⟩ := hS F P.odd_blockSide hs2
  set A := (sitesOfCells (finiteCells F) F.depth).filter (fun y => enclosingCell y = Y) with hA
  have hcard : (A.card : ℝ) ≤ ((centredCube T.L).card : ℝ) := by
    have : A.card ≤ (centredCube T.L).card := by
      refine Finset.card_le_card_of_injOn cellOffset (fun y _ => ?_) (fun y hy y' hy' e => ?_)
      · rw [← P.torus.1]
        exact (b2 y).2
      · have h1 := (b2 y).1
        have h2 := (b2 y').1
        rw [Finset.mem_coe, hA, Finset.mem_filter] at hy hy'
        rw [hy.2] at h1
        rw [hy'.2, ← e] at h2
        rw [← h1, h2]
    exact_mod_cast this
  have hterm : ∀ y ∈ A, |w y * ((minimalSiteShare T.a y (chartedField (chartPoint T x V j ζ) V) -
      minimalSiteShare T.a y (chartedField (chartPoint T x V j 0) V)) -
      (minimalSiteShare T.a y (chartedField (chartPoint T x V' j' ζ) V') -
        minimalSiteShare T.a y (chartedField (chartPoint T x V' j' 0) V')))| ≤ B * M := by
    intro y hy
    have hyY := (Finset.mem_filter.1 hy).2
    have ho : cellOffset y ∈ centredCube T.L := by
      rw [← P.torus.1]
      exact (b2 y).2
    have hm := abs_shareIncrement_sub_le hD hS hM hc P hC hCk hB hK ho hζ
    have e : cellCentre F.depth Y + siteOfCoords F.depth (cellOffset y) = y := by
      rw [← hyY]
      exact (b2 y).1
    rw [e] at hm
    rw [abs_mul]
    refine mul_le_mul (hw y) ?_ (abs_nonneg _) hB0.le
    have e2 : (minimalSiteShare T.a y (chartedField (chartPoint T x V j ζ) V) -
          minimalSiteShare T.a y (chartedField (chartPoint T x V j 0) V)) -
        (minimalSiteShare T.a y (chartedField (chartPoint T x V' j' ζ) V') -
          minimalSiteShare T.a y (chartedField (chartPoint T x V' j' 0) V')) =
        (minimalSiteShare T.a y (chartedField (chartPoint T x V j ζ) V) -
          minimalSiteShare T.a y (chartedField (chartPoint T x V' j' ζ) V')) -
        (minimalSiteShare T.a y (chartedField (chartPoint T x V j 0) V) -
          minimalSiteShare T.a y (chartedField (chartPoint T x V' j' 0) V')) := by ring
    rw [e2]
    exact hm
  have e : (coldHalfLawAt T x f).weightedShareIncrement w Y (toTorus j ζ) V -
      (coldHalfLawAt T x f).weightedShareIncrement w Y (toTorus j' ζ) V' =
      ∑ y ∈ A, w y * ((minimalSiteShare T.a y (chartedField (chartPoint T x V j ζ) V) -
        minimalSiteShare T.a y (chartedField (chartPoint T x V j 0) V)) -
        (minimalSiteShare T.a y (chartedField (chartPoint T x V' j' ζ) V') -
          minimalSiteShare T.a y (chartedField (chartPoint T x V' j' 0) V'))) := by
    rw [chartPoint_zero, chartPoint_zero]
    simp only [ColdHalfLaw.weightedShareIncrement, chartPoint, coldHalfLawAt, interpolatedField]
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr (by rw [hA]) fun y _ => ?_
    ring
  rw [e]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ((Finset.sum_le_sum hterm).trans ?_)
  have hM0 : 0 ≤ M := by
    have hρ : 0 < T.ballRadius := by
      have := P.σ_pos
      unfold StepParameters.ballRadius
      positivity
    have h1 : 0 ≤ bondMoveConstant (valueConstant T C (Ck 1)) (2 * Ck 2) T.ballRadius :=
      bondMoveConstant_nonneg (valueConstant_pos P hC (hCk 1).le).le (by have := hCk 2; positivity) hρ
    have h2 : 0 ≤ weightedBondNorm T.κ Y j ζ := Finset.sum_nonneg fun _ _ => by positivity
    rw [hMdef]
    positivity
  rw [Finset.sum_const, nsmul_eq_mul]
  have h3 : (A.card : ℝ) * (B * M) ≤ ((centredCube T.L).card : ℝ) * (B * M) :=
    mul_le_mul_of_nonneg_right hcard (by positivity)
  refine h3.trans (le_of_eq ?_)
  rw [hMdef]
  unfold shareConstant
  ring
end OneTorus
section Scores
variable {ι : Type} [Fintype ι] [DecidableEq ι] {T : _root_.YangMills.Construction.ColdStepAtMirrorFrames.StepParameters} {x : ℝ} {V : F.GaugeField F.top}
  {V' : F'.GaugeField F'.top} {Y : F.Cell} {Y' : F'.Cell} {q : ℕ} {j : ι → ↥(chordBonds (finiteCells F))}
  {j' : ι → ↥(chordBonds (finiteCells F'))}
private def contourSize (T : _root_.YangMills.Construction.ColdStepAtMirrorFrames.StepParameters) (x : ℝ) {G : BlockFrame} (W : G.GaugeField G.top) {ι : Type}
    [Fintype ι] [DecidableEq ι] (l : ι → ↥(chordBonds (finiteCells G))) (ζ : BondField ι)
    (c : G.Site G.top × Fin 4) : ℝ :=
  ‖_root_.YangMills.Construction.BlockAverages.contourAverage (chartedField (chartPoint T x W l ζ) W) c‖
private theorem expUnit_zero : expUnit (0 : imaginaryQuaternions) = 1 := by apply _root_.YangMills.Construction.TorusFields.expUnit_zero <;> assumption
private theorem contourSize_mem_Icc (hM : ChartLipschitz.ChartedFieldLipschitz) {G : BlockFrame} {T : _root_.YangMills.Construction.ColdStepAtMirrorFrames.StepParameters}
    {x : ℝ} {W : G.GaugeField G.top} {l : ι → ↥(chordBonds (finiteCells G))} (hl : Function.Injective l)
    (hG : Odd G.blockSide) (hGL : G.blockSide = T.L)
    (hs : InterpolatedFrameSmall 1 T.a T.chainParams.ρA T.chainParams.δ₂ T.Ct T.σ (frameRadius x) W)
    (hσ : 0 < T.σ) (hC : 0 < T.Ct) (hr : (T.Ct + 1) * T.σ ≤ 1 / (64 * (T.L : ℝ))) {ζ : BondField ι}
    (hζ : ∀ i, ‖ζ i‖ ≤ T.ballRadius) (c : G.Site G.top × Fin 4) :
    1 / 2 ≤ contourSize T x W l ζ c ∧ contourSize T x W l ζ c ≤ 1 := by
  have hρ : 0 ≤ T.ballRadius := by
    unfold StepParameters.ballRadius
    positivity
  refine norm_contourAverage_bounds hG _ W c fun h π hh => ?_
  set fr : G.Site G.depth → Fin 4 → imaginaryQuaternions :=
    fun z i => interpolatedFrame 1 T.a T.chainParams.ρA (frameRadius x) (z, i) W with hfr
  have hw : ∀ z i, ‖chartPoint T x W l ζ z i - fr z i‖ ≤ T.ballRadius := by
    intro z i
    rw [hfr]
    simp only
    rw [chartPoint_sub_interpolatedFrame]
    exact norm_stepCoordinates_le _ hρ (norm_toTorus_le hl hρ hζ) z i
  have h1 := (hM.2 G (chartPoint T x W l ζ) fr W T.ballRadius hw hρ).1 (_root_.YangMills.Construction.BlockAverages.refineSite c.1)
    (bondContour G.blockSide h π c.2)
  have h2 := LatticePaths.length_bondContour_le (L := G.blockSide) π c.2 hG.pos hh
  have h3 : ((bondContour G.blockSide h π c.2).length : ℝ) ≤ 5 * (G.blockSide : ℝ) := by exact_mod_cast h2
  have h4 := hs.contour_near_one c h π hh
  have e : contourHolonomyDefect (chartedField (chartPoint T x W l ζ) W) W c h π - 1 =
      (((pathHolonomy (chartedField (chartPoint T x W l ζ) W) (_root_.YangMills.Construction.BlockAverages.refineSite c.1) (bondContour G.blockSide h π c.2) :
            UnitQuaternion) : ℍ[ℝ]) -
        ((pathHolonomy (chartedField fr W) (refineSite c.1) (bondContour G.blockSide h π c.2) : UnitQuaternion) :
          ℍ[ℝ])) * (((W c.1 c.2)⁻¹ : UnitQuaternion) : ℍ[ℝ]) +
      (contourHolonomyDefect (chartedField fr W) W c h π - 1) := by
    have co : ∀ g h : UnitQuaternion, ((g * h : UnitQuaternion) : ℍ[ℝ]) = (g : ℍ[ℝ]) * (h : ℍ[ℝ]) :=
      fun _ _ => rfl
    unfold contourHolonomyDefect
    simp only [co]
    noncomm_ring
  rw [e]
  refine (norm_add_le _ _).trans ?_
  rw [norm_mul, norm_unitQuaternion, mul_one]
  have hLp : (0 : ℝ) < T.L := by
    rw [← hGL]
    have := hG.pos
    exact_mod_cast this
  have h5 : ‖((pathHolonomy (chartedField (chartPoint T x W l ζ) W) (_root_.YangMills.Construction.BlockAverages.refineSite c.1)
          (bondContour G.blockSide h π c.2) : UnitQuaternion) : ℍ[ℝ]) -
        ((pathHolonomy (chartedField fr W) (refineSite c.1) (bondContour G.blockSide h π c.2) : UnitQuaternion) :
          ℍ[ℝ])‖ ≤ 5 * (T.L : ℝ) * T.ballRadius := by
    rw [← hGL]
    exact h1.trans (mul_le_mul_of_nonneg_right h3 hρ)
  have h6 : T.L * ((T.Ct + 1) * T.σ) ≤ 1 / 64 := by
    have := mul_le_mul_of_nonneg_left hr hLp.le
    have e2 : (T.L : ℝ) * (1 / (64 * (T.L : ℝ))) = 1 / 64 := by field_simp
    linarith
  have hL1 : (1 : ℝ) ≤ T.L := by
    rw [← hGL]
    exact_mod_cast hG.pos
  have h7 : T.Ct * T.σ ≤ 1 / 64 := by
    have : 0 < T.Ct * T.σ := by positivity
    nlinarith
  have h8 : 5 * (T.L : ℝ) * T.ballRadius ≤ 1 / 64 := by
    unfold StepParameters.ballRadius
    have : 0 < T.Ct * T.σ := by positivity
    nlinarith
  linarith
private theorem abs_contourSize_sub_le (hM : ChartLipschitz.ChartedFieldLipschitz) {G : BlockFrame}
    {T : _root_.YangMills.Construction.ColdStepAtMirrorFrames.StepParameters} {x : ℝ} {W : G.GaugeField G.top} {l : ι → ↥(chordBonds (finiteCells G))}
    (hl : Function.Injective l) (hG : Odd G.blockSide) (hGL : G.blockSide = T.L) (ζ : BondField ι)
    (c : G.Site G.top × Fin 4) :
    |contourSize T x W l ζ c - contourSize T x W l 0 c| ≤ 5 * (T.L : ℝ) * ∑ i, ‖ζ i‖ := by
  have hS0 : 0 ≤ ∑ i, ‖ζ i‖ := Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hw : ∀ z i, ‖chartPoint T x W l ζ z i - chartPoint T x W l 0 z i‖ ≤ ∑ i, ‖ζ i‖ := by
    intro z i
    have e : chartPoint T x W l ζ z i - chartPoint T x W l 0 z i = stepCoordinates (toTorus l ζ) z i := by
      have h0 : stepCoordinates (toTorus l (0 : BondField ι)) z i = 0 := by
        rw [toTorus_zero]
        unfold stepCoordinates
        split_ifs
        · simp [toImaginary]
          rfl
        · rfl
      simp only [chartPoint, interpolatedCoords]
      rw [h0]
      simp
    rw [e]
    refine norm_stepCoordinates_le _ hS0 (fun b => ?_) z i
    by_cases hb : ∃ k, l k = b
    · obtain ⟨k, rfl⟩ := hb
      rw [toTorus_apply_self hl]
      exact Finset.single_le_sum (f := fun i => ‖ζ i‖) (fun _ _ => norm_nonneg _) (Finset.mem_univ k)
    · push Not at hb
      rw [toTorus_apply_of_forall_ne ζ hb]
      simpa using hS0
  have h := norm_contourAverage_sub_le hM hG _ _ W hS0 hw c
  rw [hGL] at h
  exact (abs_norm_sub_norm_le _ _).trans h
private theorem cellBond_eq (Y : F.Cell) (i : Fin 4) (back : Bool) :
    cellBond Y i back = (Y + siteOfCoords F.top (if back then -(Pi.single i 1) else 0), i) := by apply _root_.YangMills.DeltaSharedProofs.p501180 <;> assumption
private theorem abs_contourSize_pair_sub_le (hD : Estimates.cellOffsetStatement) (hS : SiteDecomposition)
    (hM : ChartLipschitz.ChartedFieldLipschitz) (P : TorusPairData T x V V' Y Y' q j j') {C : ℝ}
    (hB : ChartComparison T C) {ζ : BondField ι} (hζ : ∀ i, ‖ζ i‖ ≤ T.ballRadius) (i : Fin 4) (back : Bool) :
    |contourSize T x V j ζ (cellBond Y i back) - contourSize T x V' j' ζ (cellBond Y' i back)| ≤
      5 * (T.L : ℝ) * frameGap T q := by
  have hw := (hB F F' (chartPoint T x V j ζ) (transferredChart T x V V' j j' ζ) V V' Y Y' (q / 2) P.one_le_half
    P.torus P.torus' P.depth_eq
    (chartPoint_admissible P.short.isBoxPairing.injective_left P.small P.σ_pos hζ P.room_le P.σ_le)
    (admissible_of_between hD hS hM P hζ _ fun z i => ⟨1, zero_le_one, le_rfl, by simp⟩) P.agreeOnBall_half
    (fun h o i hh ho hb =>
      chartPoint_eq_transferredChart hD hS P ζ h o i hh (by rw [P.torus.1]; exact ho) hb)).2
  have h1 := P.one_le_half
  have h2 : (1 : ℤ) ≤ ((q / 2 : ℕ) : ℤ) := by exact_mod_cast h1
  have hone : WithinRadius (q / 2) (Pi.single i 1 : Fin 4 → ℤ) := fun l => by
    by_cases hl : l = i
    · subst hl
      simpa using h2
    · simp only [Pi.single_eq_of_ne hl, abs_zero]
      omega
  have hzero : WithinRadius (q / 2) (0 : Fin 4 → ℤ) := fun l => by
    simp only [Pi.zero_apply, abs_zero]
    omega
  have hneg : WithinRadius (q / 2) (-(Pi.single i 1) : Fin 4 → ℤ) := fun l => by
    have := hone l
    simpa using this
  have hbox : WithinRadius (q / 2) (if back then -(Pi.single i 1) else (0 : Fin 4 → ℤ)) ∧
      WithinRadius (q / 2) ((if back then -(Pi.single i 1) else (0 : Fin 4 → ℤ)) + Pi.single i 1) := by
    cases back
    · simpa using ⟨hzero, hone⟩
    · simpa using ⟨hneg, hzero⟩
  have he := hw _ i hbox.1 hbox.2
  unfold contourSize
  rw [cellBond_eq Y, cellBond_eq Y']
  have hgap : ∀ z k, ‖transferredChart T x V V' j j' ζ z k - chartPoint T x V' j' ζ z k‖ ≤ frameGap T q :=
    norm_transferredChart_sub_le hD hS P ζ
  have h3 := norm_contourAverage_sub_le hM P.odd_blockSide' _ _ V' (frameGap_nonneg P) hgap
    ((Y' + siteOfCoords F'.top (if back then -(Pi.single i 1) else 0), i) : F'.Site F'.top × Fin 4)
  rw [P.torus'.1] at h3
  refine le_trans ?_ h3
  refine (abs_norm_sub_norm_le _ _).trans (le_of_eq ?_)
  exact congrArg (fun z => ‖z - _root_.YangMills.Construction.BlockAverages.contourAverage (chartedField (chartPoint T x V' j' ζ) V')
    ((Y' + siteOfCoords F'.top (if back then -(Pi.single i 1) else 0), i) : F'.Site F'.top × Fin 4)‖) he
private theorem logContourNorm_line {G : BlockFrame} {s a ρA κ κ₂ rE x : ℝ} {m : ℕ} {K : ℕ → ℝ}
    {D : ℕ → ℕ → ℝ} {W : G.GaugeField G.top} {η : StepVariable (finiteCells G)}
    (H : HasInterpolationKernels s a ρA κ κ₂ rE x m K D W η) (hκ : 0 ≤ κ) (hD : 0 ≤ D 2 0)
    (c₀ : G.Site G.top × Fin 4) (b : ↥(chordBonds (finiteCells G))) {e : BondVector} (he : ‖e‖ = 1) :
    ContDiffAt ℝ 2 (fun τ : ℝ => logContourNorm s a ρA m c₀ (η + Pi.single b (τ • e)) W) 0 ∧
      |deriv (deriv fun τ : ℝ => logContourNorm s a ρA m c₀ (η + Pi.single b (τ • e)) W) 0| ≤ D 2 0 := by
  set φ : ℝ → ℝ := fun τ => logContourNorm s a ρA m c₀ (η + Pi.single b (τ • e)) W with hφ
  have hk := H.logContour c₀ 2 0 ![b, b] ![e, e] Fin.elim0 Fin.elim0 (by norm_num)
    (fun i => by fin_cases i <;> simpa using he) (fun l => l.elim0)
  have e1 : jointDisplacement (logContourNorm s a ρA m c₀) η W ![b, b] ![e, e]
      (Fin.elim0 : Fin 0 → G.Site G.top × Fin 4) (Fin.elim0 : Fin 0 → imaginaryQuaternions) =
      fun σ : Fin 2 → ℝ => φ (σ 0 + σ 1) := by
    funext σ
    have e2 : leftTranslate (ColdStepAtMirrorFrames.bondSpread (Fin.elim0 : Fin 0 → G.Site G.top × Fin 4)
        (Fin.elim0 : Fin 0 → imaginaryQuaternions) fun i => σ (Fin.natAdd 2 i)) W = W := by
      funext y i
      simp [leftTranslate, ColdStepAtMirrorFrames.bondSpread, expUnit_zero]
    have e3 : displacedPoint η ![b, b] ![e, e] (fun i => σ (Fin.castAdd 0 i)) =
        η + Pi.single b ((σ 0 + σ 1) • e) := by
      unfold displacedPoint
      rw [Fin.sum_univ_two, add_smul, Pi.single_add]
      rfl
    simp only [jointDisplacement, hφ]
    rw [e2, e3]
  obtain ⟨h1, h2⟩ := hk
  have h1' : ContDiffAt ℝ 2 (fun σ : Fin 2 → ℝ => φ (σ 0 + σ 1)) 0 := by
    have := h1
    rw [e1] at this
    exact this
  obtain ⟨h3, h4⟩ := contDiffAt_and_iteratedFDeriv_comp_add h1'
  refine ⟨h3, ?_⟩
  rw [← h4]
  have h5 := h2
  unfold jointMixedDeriv at h5
  rw [e1] at h5
  refine h5.trans ?_
  have : Real.exp (-(2 ^ 8 * κ * (cellSetDiameter ({c₀.1} ∪ chordBondCells ![b, b] ∪
      topBondCells (Fin.elim0 : Fin 0 → G.Site G.top × Fin 4)) : ℕ))) ≤ 1 := by
    apply Real.exp_le_one_iff.2
    have : 0 ≤ 2 ^ 8 * κ * (cellSetDiameter ({c₀.1} ∪ chordBondCells ![b, b] ∪
      topBondCells (Fin.elim0 : Fin 0 → G.Site G.top × Fin 4)) : ℕ) := by positivity
    linarith
  nlinarith
private def logContourSize (T : _root_.YangMills.Construction.ColdStepAtMirrorFrames.StepParameters) (x : ℝ) {G : BlockFrame} (W : G.GaugeField G.top) {ι : Type}
    [Fintype ι] [DecidableEq ι] (l : ι → ↥(chordBonds (finiteCells G))) (ζ : BondField ι)
    (c : G.Site G.top × Fin 4) : ℝ :=
  Real.log (contourSize T x W l ζ c)
private theorem logContourSize_line {G : BlockFrame} {W : G.GaugeField G.top}
    {l : ι → ↥(chordBonds (finiteCells G))} {Kf : ℕ → ℝ} {Df : ℕ → ℕ → ℝ} {ζ : BondField ι}
    (H : HasInterpolationKernels 1 T.a T.chainParams.ρA T.κ T.chainParams.κ₂ T.chainParams.δ₂ x (frameRadius x)
      Kf Df W (toTorus l ζ))
    (hκ : 0 ≤ T.κ) (hD : 0 ≤ Df 2 0) (c : G.Site G.top × Fin 4) (i : ι) {e : BondVector} (he : ‖e‖ = 1) :
    ContDiffAt ℝ 2 (fun τ : ℝ => logContourSize T x W l (ζ + Pi.single i (τ • e)) c) 0 ∧
      |deriv (deriv fun τ : ℝ => logContourSize T x W l (ζ + Pi.single i (τ • e)) c) 0| ≤ Df 2 0 := by
  have e1 : (fun τ : ℝ => logContourSize T x W l (ζ + Pi.single i (τ • e)) c) =
      fun τ : ℝ => logContourNorm 1 T.a T.chainParams.ρA (frameRadius x) c
        (toTorus l ζ + Pi.single (l i) (τ • e)) W := by
    funext τ
    have : toTorus l (ζ + Pi.single i (τ • e)) = toTorus l ζ + Pi.single (l i) (τ • e) :=
      extendByZero_add_single l Finset.univ (Finset.mem_univ i) ζ (τ • e)
    simp only [logContourSize, contourSize, chartPoint, logContourNorm, interpolatedField]
    rw [this]
  rw [e1]
  exact logContourNorm_line H hκ hD c (l i) he
private theorem frameGap_le_rate (P : TorusPairData T x V V' Y Y' q j j') :
    frameGap T q ≤ T.Ct * T.σ * Real.exp (-(valueRate T * q)) := by
  have hδ := P.δ₂_pos
  have hσ := P.σ_pos
  have hC := P.Ct_pos
  unfold ChartTransfer.frameGap valueRate
  have : Real.exp (-(T.chainParams.δ₂ / 8 * q)) ≤ Real.exp (-(T.chainParams.δ₂ / 16 * q)) := by
    apply Real.exp_le_exp.2
    nlinarith
  gcongr
private def sizeConstant (T : _root_.YangMills.Construction.ColdStepAtMirrorFrames.StepParameters) : ℝ := 5 * (T.L : ℝ) * (T.Ct * T.σ)
private def logConstant (T : _root_.YangMills.Construction.ColdStepAtMirrorFrames.StepParameters) : ℝ := 2 * sizeConstant T + 1
private theorem logContourSize_increment (hD : Estimates.cellOffsetStatement) (hS : SiteDecomposition)
    (hM : ChartLipschitz.ChartedFieldLipschitz) (P : TorusPairData T x V V' Y Y' q j j') {C : ℝ}
    (hB : ChartComparison T C) {Kf : ℕ → ℝ} {Df : ℕ → ℕ → ℝ} (hDf : 0 ≤ Df 2 0)
    (hH : ∀ ζ : BondField ι, (∀ i, ‖ζ i‖ ≤ T.ballRadius) →
      HasInterpolationKernels 1 T.a T.chainParams.ρA T.κ T.chainParams.κ₂ T.chainParams.δ₂ x (frameRadius x)
        Kf Df V (toTorus j ζ))
    (hH' : ∀ ζ : BondField ι, (∀ i, ‖ζ i‖ ≤ T.ballRadius) →
      HasInterpolationKernels 1 T.a T.chainParams.ρA T.κ T.chainParams.κ₂ T.chainParams.δ₂ x (frameRadius x)
        Kf Df V' (toTorus j' ζ))
    (i : Fin 4) (back : Bool) {ζ : BondField ι} (hζ : ∀ i, ‖ζ i‖ < T.ballRadius) :
    (∀ ζ : BondField ι, (∀ i, ‖ζ i‖ ≤ T.ballRadius) →
      |logContourSize T x V j ζ (cellBond Y i back) - logContourSize T x V' j' ζ (cellBond Y' i back)| ≤
        logConstant T * Real.exp (-(valueRate T * q))) ∧
    |(logContourSize T x V j ζ (cellBond Y i back) - logContourSize T x V' j' ζ (cellBond Y' i back)) -
      (logContourSize T x V j 0 (cellBond Y i back) - logContourSize T x V' j' 0 (cellBond Y' i back))| ≤
      bondMoveConstant (logConstant T) (2 * Df 2 0) T.ballRadius * Real.exp (-(valueRate T / 2 * q)) *
        ∑ k, ‖ζ k‖ := by
  have hρ : 0 < T.ballRadius := by
    have := P.σ_pos
    unfold StepParameters.ballRadius
    positivity
  have hL : (0 : ℝ) < T.L := by
    have := P.odd_side.pos
    exact_mod_cast this
  have hsc : 0 ≤ sizeConstant T := by
    have := P.σ_pos
    have := P.Ct_pos
    unfold sizeConstant
    positivity
  have hlc : 0 < logConstant T := by
    unfold logConstant
    positivity
  have hr : 0 ≤ valueRate T := by
    have := P.δ₂_pos
    unfold valueRate
    positivity
  have hv : ∀ ζ : BondField ι, (∀ i, ‖ζ i‖ ≤ T.ballRadius) →
      |logContourSize T x V j ζ (cellBond Y i back) - logContourSize T x V' j' ζ (cellBond Y' i back)| ≤
        logConstant T * Real.exp (-(valueRate T * q)) := by
    intro ζ hζ
    have h1 := abs_contourSize_pair_sub_le hD hS hM P hB hζ i back
    have h2 := contourSize_mem_Icc hM P.short.isBoxPairing.injective_left P.odd_blockSide P.torus.1 P.small P.σ_pos
      P.Ct_pos P.room_le hζ (cellBond Y i back)
    have h3 := contourSize_mem_Icc hM P.short.isBoxPairing.injective_right P.odd_blockSide' P.torus'.1 P.small' P.σ_pos
      P.Ct_pos P.room_le hζ (cellBond Y' i back)
    have h4 := abs_log_sub_log_le h2.1 h3.1
    have h5 := frameGap_le_rate P
    have he := Real.exp_pos (-(valueRate T * q))
    unfold logContourSize
    refine h4.trans ?_
    have h6 : 5 * (T.L : ℝ) * frameGap T q ≤ sizeConstant T * Real.exp (-(valueRate T * q)) := by
      unfold sizeConstant
      have := mul_le_mul_of_nonneg_left h5 (by positivity : (0 : ℝ) ≤ 5 * (T.L : ℝ))
      linarith
    unfold logConstant
    nlinarith
  refine ⟨hv, ?_⟩
  refine abs_sub_zero_le_of_exp_small
    (g := fun ζ => logContourSize T x V j ζ (cellBond Y i back) - logContourSize T x V' j' ζ (cellBond Y' i back))
    (q := q) hρ hlc (by positivity : 0 ≤ 2 * Df 2 0) hr (fun ζ hζ => hv ζ fun i => (hζ i).le)
    (fun ζ hζ k e he => ?_) hζ
  obtain ⟨a1, b1⟩ := logContourSize_line (hH ζ (fun i => (hζ i).le)) P.κ_pos.le hDf (cellBond Y i back) k he
  obtain ⟨a2, b2⟩ := logContourSize_line (hH' ζ (fun i => (hζ i).le)) P.κ_pos.le hDf (cellBond Y' i back) k he
  refine ⟨a1.sub a2, ?_⟩
  rw [deriv_deriv_sub a1 a2]
  exact (abs_sub _ _).trans (by linarith)
private theorem abs_exp_sub_sub_le {a₀ a₁ b₀ b₁ : ℝ} (ha₀ : a₀ ∈ Set.Icc (-1 : ℝ) 0)
    (ha₁ : a₁ ∈ Set.Icc (-1 : ℝ) 0) (hb₀ : b₀ ∈ Set.Icc (-1 : ℝ) 0) (hb₁ : b₁ ∈ Set.Icc (-1 : ℝ) 0) :
    |(Real.exp a₁ - Real.exp a₀) - (Real.exp b₁ - Real.exp b₀)| ≤ 1 * |(a₁ - a₀) - (b₁ - b₀)| +
      1 * (|a₀ - b₀| + |(a₁ - a₀) - (b₁ - b₀)|) * |b₁ - b₀| := by
  have hb : ∀ u ∈ Set.Icc (-1 : ℝ) 0, |Real.exp u| ≤ 1 := fun u hu => by
    rw [abs_of_pos (Real.exp_pos u)]
    exact Real.exp_le_one_iff.2 hu.2
  refine abs_sub_sub_le_of_lipschitz_deriv (f := Real.exp) (f₁ := Real.exp) zero_le_one
    (fun u _ => (Real.hasDerivAt_exp u).hasDerivWithinAt) hb (fun u hu v hv => ?_) ha₀ ha₁ hb₀ hb₁
  have := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (f := Real.exp) (f' := Real.exp)
    (s := Set.Icc (-1 : ℝ) 0) (C := 1) (fun y _ => (Real.hasDerivAt_exp y).hasDerivWithinAt)
    (fun y hy => hb y hy) (convex_Icc _ _) hv hu
  simpa using this
private structure RemainderDerivBounds (Q : ColdHalfLaw) (M₁ M₂ : ℝ) : Prop where
  nonneg : 0 ≤ M₂
  deriv : ∀ u ∈ Set.Icc (1 / 2 : ℝ) 1,
    HasDerivWithinAt Q.scoreRemainder (derivWithin Q.scoreRemainder (Set.Icc (1 / 2) 1) u) (Set.Icc (1 / 2) 1) u
  bound : ∀ u ∈ Set.Icc (1 / 2 : ℝ) 1, |derivWithin Q.scoreRemainder (Set.Icc (1 / 2) 1) u| ≤ M₁
  lipschitz : ∀ u ∈ Set.Icc (1 / 2 : ℝ) 1, ∀ v ∈ Set.Icc (1 / 2 : ℝ) 1,
    |derivWithin Q.scoreRemainder (Set.Icc (1 / 2) 1) u - derivWithin Q.scoreRemainder (Set.Icc (1 / 2) 1) v| ≤
      M₂ * |u - v|
private theorem exists_remainderDerivBounds (hT : ScoreRemainderExpansion) {a : ℝ} (ha : 1 ≤ a) :
    ∃ M₁ M₂ : ℝ, ∀ Q : ColdHalfLaw, Q.a = a → 2 / a ≤ Q.coupling → RemainderDerivBounds Q M₁ M₂ := by
  obtain ⟨C₁, h₁⟩ := hT.2 a ha 1
  obtain ⟨C₂, h₂⟩ := hT.2 a ha 2
  refine ⟨C₁, |C₂|, fun Q hQ hx => ?_⟩
  obtain ⟨s₁, b₁⟩ := h₁ Q hQ hx
  obtain ⟨s₂, b₂⟩ := h₂ Q hQ hx
  have hu : UniqueDiffOn ℝ (Set.Icc (1 / 2 : ℝ) 1) := uniqueDiffOn_Icc (by norm_num)
  have s₂' : ContDiffOn ℝ 2 Q.scoreRemainder (Set.Icc (1 / 2) 1) := by exact_mod_cast s₂
  have hd : DifferentiableOn ℝ Q.scoreRemainder (Set.Icc (1 / 2) 1) := s₂'.differentiableOn (by norm_num)
  have hd2 : DifferentiableOn ℝ (derivWithin Q.scoreRemainder (Set.Icc (1 / 2) 1)) (Set.Icc (1 / 2) 1) :=
    (s₂'.derivWithin hu (m := 1) (by norm_num)).differentiableOn (by norm_num)
  refine ⟨abs_nonneg _, fun u h => (hd u h).hasDerivWithinAt, fun u h => ?_, fun u h v h' => ?_⟩
  · have := b₁ u h
    rwa [iteratedDerivWithin_one] at this
  · have hb : ∀ y ∈ Set.Icc (1 / 2 : ℝ) 1,
        ‖derivWithin (derivWithin Q.scoreRemainder (Set.Icc (1 / 2) 1)) (Set.Icc (1 / 2) 1) y‖ ≤ |C₂| := by
      intro y hy
      have := b₂ y hy
      rw [iteratedDerivWithin_succ, iteratedDerivWithin_one] at this
      exact (this.trans (le_abs_self _))
    have := Convex.norm_image_sub_le_of_norm_derivWithin_le hd2 hb (convex_Icc _ _) h' h
    simpa using this
private def scoreConstant (T : _root_.YangMills.Construction.ColdStepAtMirrorFrames.StepParameters) (D₂ M₁ M₂ : ℝ) : ℝ :=
  M₁ * (2 * bondMoveConstant (logConstant T) (2 * D₂) T.ballRadius + 2 * logConstant T * (5 * (T.L : ℝ))) +
    M₂ * (sizeConstant T * (5 * (T.L : ℝ))) +
    M₂ * (2 * bondMoveConstant (logConstant T) (2 * D₂) T.ballRadius + 2 * logConstant T * (5 * (T.L : ℝ)))
private theorem abs_scoreIncrement_sub_le (hD : Estimates.cellOffsetStatement) (hS : SiteDecomposition)
    (hM : ChartLipschitz.ChartedFieldLipschitz) (P : TorusPairData T x V V' Y Y' q j j') {C : ℝ}
    (hB : ChartComparison T C) {Kf : ℕ → ℝ} {Df : ℕ → ℕ → ℝ} (hDf : 0 ≤ Df 2 0)
    (hH : ∀ ζ : BondField ι, (∀ i, ‖ζ i‖ ≤ T.ballRadius) →
      HasInterpolationKernels 1 T.a T.chainParams.ρA T.κ T.chainParams.κ₂ T.chainParams.δ₂ x (frameRadius x)
        Kf Df V (toTorus j ζ))
    (hH' : ∀ ζ : BondField ι, (∀ i, ‖ζ i‖ ≤ T.ballRadius) →
      HasInterpolationKernels 1 T.a T.chainParams.ρA T.κ T.chainParams.κ₂ T.chainParams.δ₂ x (frameRadius x)
        Kf Df V' (toTorus j' ζ))
    (f : LocalFamily) {M₁ M₂ : ℝ} (hTl : RemainderDerivBounds (coldHalfLawAt T x f) M₁ M₂) (i : Fin 4)
    (back : Bool) {ζ : BondField ι} (hζ : ∀ i, ‖ζ i‖ < T.ballRadius) :
    |(coldHalfLawAt T x f).scoreRemainderIncrement (cellBond Y i back) (toTorus j ζ) V -
        (coldHalfLawAt T x f).scoreRemainderIncrement (cellBond Y' i back) (toTorus j' ζ) V'| ≤
      Real.exp (-(4 * T.κ * q)) * (scoreConstant T (Df 2 0) M₁ M₂ * weightedBondNorm T.κ Y j ζ) := by
  set c := cellBond Y i back with hc
  set c' := cellBond Y' i back with hc'
  have hρ : 0 < T.ballRadius := by
    have := P.σ_pos
    unfold StepParameters.ballRadius
    positivity
  have hL : (0 : ℝ) < T.L := by
    have := P.odd_side.pos
    exact_mod_cast this
  have hz : ∀ i, ‖(0 : BondField ι) i‖ ≤ T.ballRadius := fun i => by simpa using hρ.le
  have hc1 : ∀ i, ‖ζ i‖ ≤ T.ballRadius := fun i => (hζ i).le
  obtain ⟨hval, hmv⟩ := logContourSize_increment hD hS hM P hB hDf hH hH' i back hζ
  set M := bondMoveConstant (logConstant T) (2 * Df 2 0) T.ballRadius with hMdef
  have hM0 : 0 ≤ M := bondMoveConstant_nonneg (by
    have : 0 ≤ sizeConstant T := by
      have := P.σ_pos
      have := P.Ct_pos
      unfold sizeConstant
      positivity
    unfold logConstant
    positivity) (by positivity) hρ
  set r₁ := contourSize T x V j ζ c with hr₁
  set r₀ := contourSize T x V j 0 c with hr₀
  set s₁ := contourSize T x V' j' ζ c' with hs₁
  set s₀ := contourSize T x V' j' 0 c' with hs₀
  have br₁ := contourSize_mem_Icc hM P.short.isBoxPairing.injective_left P.odd_blockSide P.torus.1 P.small P.σ_pos
    P.Ct_pos P.room_le hc1 c
  have br₀ := contourSize_mem_Icc hM P.short.isBoxPairing.injective_left P.odd_blockSide P.torus.1 P.small P.σ_pos
    P.Ct_pos P.room_le hz c
  have bs₁ := contourSize_mem_Icc hM P.short.isBoxPairing.injective_right P.odd_blockSide' P.torus'.1 P.small' P.σ_pos
    P.Ct_pos P.room_le hc1 c'
  have bs₀ := contourSize_mem_Icc hM P.short.isBoxPairing.injective_right P.odd_blockSide' P.torus'.1 P.small' P.σ_pos
    P.Ct_pos P.room_le hz c'
  have mem : ∀ r : ℝ, 1 / 2 ≤ r ∧ r ≤ 1 → Real.log r ∈ Set.Icc (-1 : ℝ) 0 := by
    intro r hr
    have hr0 : 0 < r := by linarith [hr.1]
    refine ⟨?_, Real.log_nonpos hr0.le hr.2⟩
    have h1 : Real.log (1 / 2) ≤ Real.log r := Real.log_le_log (by norm_num) hr.1
    have h2 : Real.log (1 / 2) = - Real.log 2 := by
      rw [one_div, Real.log_inv]
    have h3 : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
    linarith
  set S := ∑ k, ‖ζ k‖ with hSdef
  set θ := Real.exp (-(valueRate T / 2 * q)) with hθ
  set E₁ := Real.exp (-(valueRate T * q)) with hE₁
  have hEθ : E₁ ≤ θ := by
    apply Real.exp_le_exp.2
    have := P.δ₂_pos
    have : 0 ≤ valueRate T * q := by
      unfold valueRate
      positivity
    linarith
  set Lp : ℝ := 5 * (T.L : ℝ) with hLp
  have ms : |s₁ - s₀| ≤ Lp * S :=
    abs_contourSize_sub_le hM P.short.isBoxPairing.injective_right P.odd_blockSide' P.torus'.1 ζ c'
  have ms1 : |s₁ - s₀| ≤ 1 := by
    rw [abs_le]
    constructor <;> linarith [bs₁.1, bs₁.2, bs₀.1, bs₀.2]
  set a₁ := Real.log r₁ with ha₁
  set a₀ := Real.log r₀ with ha₀
  set b₁ := Real.log s₁ with hb₁
  set b₀ := Real.log s₀ with hb₀
  have hΔ : |(a₁ - a₀) - (b₁ - b₀)| ≤ M * θ * S := by
    have e : (a₁ - a₀) - (b₁ - b₀) = (a₁ - b₁) - (a₀ - b₀) := by ring
    rw [e]
    exact hmv
  have h₀ : |a₀ - b₀| ≤ logConstant T * E₁ := hval 0 hz
  have hb1 : |b₁ - b₀| ≤ 2 * (Lp * S) := (abs_log_sub_log_le bs₁.1 bs₀.1).trans (by linarith)
  have hb2 : |b₁ - b₀| ≤ 1 := by
    have m1 := mem s₁ bs₁
    have m0 := mem s₀ bs₀
    rw [abs_le]
    constructor <;> linarith [m1.1, m1.2, m0.1, m0.2]
  have e₁ : Real.exp a₁ = r₁ := Real.exp_log (by linarith [br₁.1])
  have e₀ : Real.exp a₀ = r₀ := Real.exp_log (by linarith [br₀.1])
  have f₁ : Real.exp b₁ = s₁ := Real.exp_log (by linarith [bs₁.1])
  have f₀ : Real.exp b₀ = s₀ := Real.exp_log (by linarith [bs₀.1])
  set Δ := |(a₁ - a₀) - (b₁ - b₀)| with hΔdef
  have hΔ0 : 0 ≤ Δ := abs_nonneg _
  have step1 := abs_exp_sub_sub_le (mem r₀ br₀) (mem r₁ br₁) (mem s₀ bs₀) (mem s₁ bs₁)
  rw [← ha₁, ← ha₀, ← hb₁, ← hb₀, e₁, e₀, f₁, f₀, ← hΔdef] at step1
  set A₁ := 2 * M + 2 * logConstant T * Lp with hA₁
  have hlc : 0 ≤ logConstant T := by
    have : 0 ≤ sizeConstant T := by
      have := P.σ_pos
      have := P.Ct_pos
      unfold sizeConstant
      positivity
    unfold logConstant
    positivity
  have hR : |(r₁ - r₀) - (s₁ - s₀)| ≤ A₁ * θ * S := by
    have t1 : |a₀ - b₀| * |b₁ - b₀| ≤ (logConstant T * E₁) * (2 * (Lp * S)) :=
      mul_le_mul h₀ hb1 (abs_nonneg _) (by positivity)
    have t2 : Δ * |b₁ - b₀| ≤ Δ * 1 := mul_le_mul_of_nonneg_left hb2 hΔ0
    have t3 : (logConstant T * E₁) * (2 * (Lp * S)) ≤ (logConstant T * θ) * (2 * (Lp * S)) := by
      gcongr
    have t4 : 1 * (|a₀ - b₀| + Δ) * |b₁ - b₀| = |a₀ - b₀| * |b₁ - b₀| + Δ * |b₁ - b₀| := by ring
    rw [t4] at step1
    rw [hA₁]
    nlinarith
  obtain ⟨-, d₁, d₂, d₃⟩ := (⟨hTl.nonneg, hTl.deriv, hTl.bound, hTl.lipschitz⟩ :
    0 ≤ M₂ ∧ _ ∧ _ ∧ _)
  have step2 := abs_sub_sub_le_of_lipschitz_deriv hTl.nonneg d₁ d₂ d₃ (a₀ := r₀) (a₁ := r₁) (b₀ := s₀) (b₁ := s₁)
    br₀ br₁ bs₀ bs₁
  have hM₁ : 0 ≤ M₁ := (abs_nonneg _).trans (d₂ r₀ br₀)
  have hM₂ := hTl.nonneg
  have hr0 : |r₀ - s₀| ≤ sizeConstant T * E₁ := by
    have h1 := abs_contourSize_pair_sub_le hD hS hM P hB hz i back
    have h2 := frameGap_le_rate P
    refine h1.trans ?_
    unfold sizeConstant
    have := mul_le_mul_of_nonneg_left h2 (by positivity : (0 : ℝ) ≤ 5 * (T.L : ℝ))
    linarith
  set Rr := |(r₁ - r₀) - (s₁ - s₀)| with hRr
  have hRr0 : 0 ≤ Rr := abs_nonneg _
  have e : (coldHalfLawAt T x f).scoreRemainderIncrement (cellBond Y i back) (toTorus j ζ) V -
      (coldHalfLawAt T x f).scoreRemainderIncrement (cellBond Y' i back) (toTorus j' ζ) V' =
      ((coldHalfLawAt T x f).scoreRemainder r₁ - (coldHalfLawAt T x f).scoreRemainder r₀) -
      ((coldHalfLawAt T x f).scoreRemainder s₁ - (coldHalfLawAt T x f).scoreRemainder s₀) := by
    have z1 : r₀ = (coldHalfLawAt T x f).contourAverageSize c 0 V := by
      simp only [hr₀, contourSize, chartPoint, ColdHalfLaw.contourAverageSize, interpolatedField, toTorus_zero,
        coldHalfLawAt]
    have z2 : s₀ = (coldHalfLawAt T x f).contourAverageSize c' 0 V' := by
      simp only [hs₀, contourSize, chartPoint, ColdHalfLaw.contourAverageSize, interpolatedField, toTorus_zero,
        coldHalfLawAt]
    rw [z1, z2]
    rfl
  rw [e]
  refine step2.trans ?_
  have t1 : M₂ * (|r₀ - s₀| + Rr) * |s₁ - s₀| = M₂ * (|r₀ - s₀| * |s₁ - s₀|) + M₂ * (Rr * |s₁ - s₀|) := by ring
  rw [t1]
  have t2 : |r₀ - s₀| * |s₁ - s₀| ≤ (sizeConstant T * E₁) * (Lp * S) := mul_le_mul hr0 ms (abs_nonneg _) (by
    have : 0 ≤ sizeConstant T := by
      have := P.σ_pos
      have := P.Ct_pos
      unfold sizeConstant
      positivity
    positivity)
  have t3 : Rr * |s₁ - s₀| ≤ Rr * 1 := mul_le_mul_of_nonneg_left ms1 hRr0
  have t4 : (sizeConstant T * E₁) * (Lp * S) ≤ (sizeConstant T * θ) * (Lp * S) := by
    have : 0 ≤ sizeConstant T := by
      have := P.σ_pos
      have := P.Ct_pos
      unfold sizeConstant
      positivity
    gcongr
  have hfin : M₁ * Rr + (M₂ * (|r₀ - s₀| * |s₁ - s₀|) + M₂ * (Rr * |s₁ - s₀|)) ≤
      scoreConstant T (Df 2 0) M₁ M₂ * (θ * S) := by
    have u1 : M₁ * Rr ≤ M₁ * (A₁ * θ * S) := mul_le_mul_of_nonneg_left hR hM₁
    have u2 : M₂ * (|r₀ - s₀| * |s₁ - s₀|) ≤ M₂ * ((sizeConstant T * θ) * (Lp * S)) :=
      mul_le_mul_of_nonneg_left (t2.trans t4) hM₂
    have u3 : M₂ * (Rr * |s₁ - s₀|) ≤ M₂ * (A₁ * θ * S) :=
      mul_le_mul_of_nonneg_left (t3.trans (by linarith)) hM₂
    have e3 : scoreConstant T (Df 2 0) M₁ M₂ * (θ * S) =
        M₁ * (A₁ * θ * S) + (M₂ * ((sizeConstant T * θ) * (Lp * S)) + M₂ * (A₁ * θ * S)) := by
      unfold scoreConstant
      rw [← hMdef, hA₁, hLp]
      ring
    rw [e3]
    linarith
  refine hfin.trans ?_
  have hw := exp_mul_sum_norm_le_weight P ζ
  have hC0 : 0 ≤ scoreConstant T (Df 2 0) M₁ M₂ := by
    have : 0 ≤ sizeConstant T := by
      have := P.σ_pos
      have := P.Ct_pos
      unfold sizeConstant
      positivity
    unfold scoreConstant
    rw [← hMdef]
    positivity
  have := mul_le_mul_of_nonneg_left hw hC0
  calc _ ≤ _ := this
    _ = _ := by ring
end Scores
section Slopes
variable {ι : Type} [Fintype ι] [DecidableEq ι] {T : _root_.YangMills.Construction.ColdStepAtMirrorFrames.StepParameters} {x : ℝ} {V : F.GaugeField F.top}
  {V' : F'.GaugeField F'.top} {Y : F.Cell} {Y' : F'.Cell} {q : ℕ} {j : ι → ↥(chordBonds (finiteCells F))}
  {j' : ι → ↥(chordBonds (finiteCells F'))}
private theorem haarLogRatio_lipschitz (hH : HaarLogRatioNearZero) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ v w : imaginaryQuaternions, ‖v‖ ≤ 1 → ‖w‖ ≤ 1 →
      |haarLogRatio v - haarLogRatio w| ≤ C * ‖v - w‖ := by apply _root_.YangMills.SharedProofs.p83653 <;> assumption
private theorem haarGap_lipschitz (hG : HaarGapDerivBound) (hs : HaarGapContDiff) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s r r' : ℝ, 2 ≤ s → 1 / 2 ≤ r → r ≤ 1 → 1 / 2 ≤ r' → r' ≤ 1 →
      |haarGap (s * r) - haarGap (s * r')| ≤ C * |r - r'| := by
  obtain ⟨C₁, h⟩ := hG 1 le_rfl
  refine ⟨2 * |C₁|, by positivity, fun s r r' h2 a1 a2 b1 b2 => ?_⟩
  have hs0 : 0 < s := by linarith
  have hd : ∀ u ∈ Set.Icc (s / 2) s, DifferentiableAt ℝ haarGap u := fun u _ =>
    (hs.differentiable (by norm_num)) u
  have hb : ∀ u ∈ Set.Icc (s / 2) s, ‖deriv haarGap u‖ ≤ 2 * |C₁| / s := by
    intro u hu
    have hu1 : 1 ≤ u := by linarith [hu.1]
    have hu0 : 0 < u := by linarith
    have := (h u hu1).trans (le_abs_self C₁)
    rw [pow_one, iteratedDeriv_one, abs_mul, abs_of_pos hu0] at this
    rw [Real.norm_eq_abs, le_div_iff₀ hs0]
    have h3 := abs_nonneg (deriv haarGap u)
    have h4 : s ≤ 2 * u := by linarith [hu.1]
    nlinarith
  have hm : ∀ r₀ : ℝ, 1 / 2 ≤ r₀ → r₀ ≤ 1 → s * r₀ ∈ Set.Icc (s / 2) s :=
    fun r₀ c1 c2 => ⟨by nlinarith, by nlinarith⟩
  have := Convex.norm_image_sub_le_of_norm_deriv_le hd hb (convex_Icc _ _) (hm r' b1 b2) (hm r a1 a2)
  rw [Real.norm_eq_abs, Real.norm_eq_abs, ← mul_sub, abs_mul, abs_of_pos hs0] at this
  refine this.trans (le_of_eq ?_)
  field_simp
private theorem sum_innerBonds_at_cell {G : BlockFrame} (hs : ∀ i, 2 ≤ G.extent i) (Z : G.Cell)
    (D : G.Site G.top × Fin 4 → ℝ) [DecidablePred fun c : G.Site G.top × Fin 4 => c.1 = Z] :
    ∑ c ∈ (innerBonds (finiteCells G) G.top).filter (fun c => c.1 = Z), D c = ∑ d : Fin 4, D (Z, d) := by
  classical
  have hB : innerBonds (finiteCells G) G.top = finiteCells G ×ˢ Finset.univ := by
    ext c
    simp only [innerBonds, Finset.mem_filter, Finset.mem_product, Finset.mem_univ, and_true]
    constructor
    · rintro ⟨h, _⟩
      exact mem_sitesOfCells_top.1 h
    · intro h
      exact ⟨mem_sitesOfCells_top.2 h, mem_sitesOfCells_top.2 (BlockOffsets.mem_finiteCells hs _)⟩
  rw [Finset.sum_filter, hB, Finset.sum_product_right]
  refine Finset.sum_congr rfl fun d _ => ?_
  have hm := BlockOffsets.mem_finiteCells hs Z
  rw [Finset.sum_eq_single Z]
  · simp
  · intro z _ hz
    simp [hz]
  · intro h
    exact absurd hm h
private theorem add_siteOfCoords_eq_self_iff (hD : Estimates.cellOffsetStatement) {G : BlockFrame}
    (hG : Odd G.blockSide) {q : ℕ} (hs : ∀ i, 2 * q + 2 < G.extent i) (Z : G.Cell) {h : Fin 4 → ℤ}
    (hh : ∀ l, 2 * |h l| ≤ q) :
    Z + siteOfCoords G.top h = Z ↔ h = 0 := by
  have hs2 : ∀ i, 2 ≤ G.extent i := fun i => by
    have := hs i
    omega
  obtain ⟨-, -, -, hd⟩ := hD G hG hs2
  have h0 : ∀ l, 2 * |(0 : Fin 4 → ℤ) l| ≤ (q : ℤ) := fun l => by simp
  have z0 : Z + siteOfCoords G.top (0 : Fin 4 → ℤ) = Z := by
    funext i
    simp [siteOfCoords]
  constructor
  · intro e
    have a1 := (hd q hs Z h 0 hh h0).1
    have a2 := (hd q hs Z 0 h h0 hh).1
    rw [e] at a1
    rw [z0] at a2
    rw [← a1, a2]
  · rintro rfl
    exact z0
private theorem enclosingCell_pair_iff (hD : Estimates.cellOffsetStatement) (P : TorusPairData T x V V' Y Y' q j j')
    (i : ι) :
    enclosingCell (j i).1.1 = Y ↔ enclosingCell (j' i).1.1 = Y' := by
  obtain ⟨h, o, k, hh, ho, e₁, e₂⟩ := P.short.short_offsets i
  have c1 : enclosingCell (j i).1.1 = Y + siteOfCoords F.top h := by
    rw [e₁]
    exact (hD F P.odd_blockSide P.two_le_extent).1 Y h o k ho
  have c2 : enclosingCell (j' i).1.1 = Y' + siteOfCoords F'.top h := by
    rw [e₂]
    exact (hD F' P.odd_blockSide' P.two_le_extent').1 Y' h o k (by rw [P.torus'.1, ← P.torus.1]; exact ho)
  rw [c1, c2, add_siteOfCoords_eq_self_iff hD P.odd_blockSide P.extent_gt Y hh,
    add_siteOfCoords_eq_self_iff hD P.odd_blockSide' P.extent_gt' Y' hh]
omit [DecidableEq ι] in
private theorem sum_chordBonds_at_cell {H : BlockFrame} {Z : H.Cell} {l : ι → ↥(chordBonds (finiteCells H))}
    (hl : Function.Injective l) (hr : ∀ b, b ∈ bondsNearCell Z q ↔ ∃ i, l i = b)
    (G : ↥(chordBonds (finiteCells H)) → ℝ)
    [DecidablePred fun b : ↥(chordBonds (finiteCells H)) => enclosingCell b.1.1 = Z] :
    ∑ b : ↥(chordBonds (finiteCells H)), (if enclosingCell b.1.1 = Z then G b else 0) =
      ∑ i, if enclosingCell (l i).1.1 = Z then G (l i) else 0 := by
  classical
  rw [← Finset.sum_image (s := Finset.univ) (g := l)
    (f := fun b => if enclosingCell b.1.1 = Z then G b else 0) hl.injOn]
  symm
  refine Finset.sum_subset (Finset.subset_univ _) fun b _ hb => ?_
  rw [if_neg]
  intro hc
  apply hb
  have hn : b ∈ bondsNearCell Z q := by
    simp only [bondsNearCell, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [hc, PatchLocality.cellSupDist_self]
    omega
  obtain ⟨i, hi⟩ := (hr b).1 hn
  exact Finset.mem_image.2 ⟨i, Finset.mem_univ _, hi⟩
private theorem card_pairs_at_cell_le (hD : Estimates.cellOffsetStatement) (P : TorusPairData T x V V' Y Y' q j j')
    [DecidablePred fun i => enclosingCell (j i).1.1 = Y] :
    (((Finset.univ.filter fun i => enclosingCell (j i).1.1 = Y).card : ℕ) : ℝ) ≤
      4 * ((centredCube T.L).card : ℝ) := by
  classical
  have hs := fun i => P.short.short_offsets i
  choose h o k hh ho e₁ e₂ using hs
  have hc : ∀ i, enclosingCell (j i).1.1 = Y → h i = 0 := by
    intro i hi
    have c1 : enclosingCell (j i).1.1 = Y + siteOfCoords F.top (h i) := by
      rw [e₁]
      exact (hD F P.odd_blockSide P.two_le_extent).1 Y (h i) (o i) (k i) (ho i)
    rw [c1] at hi
    exact (add_siteOfCoords_eq_self_iff hD P.odd_blockSide P.extent_gt Y (hh i)).1 hi
  have hcard : (Finset.univ.filter fun i => enclosingCell (j i).1.1 = Y).card ≤
      (centredCube T.L ×ˢ (Finset.univ : Finset (Fin 4))).card := by
    refine Finset.card_le_card_of_injOn (fun i => (o i, k i)) (fun i _ => ?_) (fun i hi i' hi' e => ?_)
    · simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe, Finset.coe_univ, Set.mem_univ, and_true]
      rw [← P.torus.1]
      exact ho i
    · rw [Finset.mem_coe, Finset.mem_filter] at hi hi'
      simp only [Prod.mk.injEq] at e
      apply P.short.isBoxPairing.injective_left
      apply Subtype.ext
      rw [e₁, e₁, hc i hi.2, hc i' hi'.2, e.1, e.2]
  rw [Finset.card_product, Finset.card_univ, Fintype.card_fin] at hcard
  have : (((Finset.univ.filter fun i => enclosingCell (j i).1.1 = Y).card : ℕ) : ℝ) ≤
      ((centredCube T.L).card : ℝ) * 4 := by exact_mod_cast hcard
  linarith
private def slopeConstant (T : _root_.YangMills.Construction.ColdStepAtMirrorFrames.StepParameters) (Cg Ch : ℝ) : ℝ :=
  T.Ct + (4 * (Cg * (5 * (T.L : ℝ))) + 4 * ((centredCube T.L).card : ℝ) * Ch) * (T.Ct * T.σ)
private theorem abs_linearPart_sub_le (hD : Estimates.cellOffsetStatement) (hS : SiteDecomposition)
    (hM : ChartLipschitz.ChartedFieldLipschitz) (P : TorusPairData T x V V' Y Y' q j j') {C : ℝ}
    (hB : ChartComparison T C) (f : LocalFamily) {Cg Ch : ℝ} (hCg0 : 0 ≤ Cg) (hCh0 : 0 ≤ Ch)
    (hCg : ∀ s r r' : ℝ, 2 ≤ s → 1 / 2 ≤ r → r ≤ 1 → 1 / 2 ≤ r' → r' ≤ 1 →
      |haarGap (s * r) - haarGap (s * r')| ≤ Cg * |r - r'|)
    (hCh : ∀ v w : imaginaryQuaternions, ‖v‖ ≤ 1 → ‖w‖ ≤ 1 → |haarLogRatio v - haarLogRatio w| ≤ Ch * ‖v - w‖)
    (hx : 2 ≤ T.a * x) {ζ : BondField ι} (hζ : ∀ i, ‖ζ i‖ < T.ballRadius)
    (hterm : |interpolatedBlockExponent 1 T.a T.chainParams.ρA x (frameRadius x) Y' V' (toTorus j' ζ) -
      interpolatedBlockExponent 1 T.a T.chainParams.ρA x (frameRadius x) Y V (toTorus j ζ)| ≤
      T.Ct * Real.exp (-(4 * T.κ * q)) * (x * weightedBondNormSq T.κ Y j ζ + 1)) :
    |(coldHalfLawAt T x f).linearBlockPart Y (toTorus j ζ) V -
        (coldHalfLawAt T x f).linearBlockPart Y' (toTorus j' ζ) V'| ≤
      Real.exp (-(4 * T.κ * q)) * (slopeConstant T Cg Ch * weightedBondNorm T.κ Y j ζ +
        slopeConstant T Cg Ch * (x * weightedBondNormSq T.κ Y j ζ + 1)) := by
  classical
  have hc1 : ∀ i, ‖ζ i‖ ≤ T.ballRadius := fun i => (hζ i).le
  have hj := P.short.isBoxPairing.injective_left
  have hj' := P.short.isBoxPairing.injective_right
  set eq4 := Real.exp (-(4 * T.κ * q)) with heq4
  have hσ := P.σ_pos
  have hCt := P.Ct_pos
  have hδ := P.δ₂_pos
  have hκ' := P.κ_le
  have hgap : frameGap T q ≤ T.Ct * T.σ * eq4 := by
    unfold ChartTransfer.frameGap
    have : Real.exp (-(T.chainParams.δ₂ / 8 * q)) ≤ eq4 := by
      apply Real.exp_le_exp.2
      nlinarith
    gcongr
  have hg0 := frameGap_nonneg P
  have hL : (0 : ℝ) < T.L := by
    have := P.odd_side.pos
    exact_mod_cast this
  have ha : 0 < T.a := by linarith [P.one_le_a]
  have hgaps : ∀ d : Fin 4, |haarGapExcess T.a x (chartedField (chartPoint T x V j ζ) V) (Y, d) -
      haarGapExcess T.a x (chartedField (chartPoint T x V' j' ζ) V') (Y', d)| ≤
      Cg * (5 * (T.L : ℝ) * frameGap T q) := by
    intro d
    have h1 := abs_contourSize_pair_sub_le hD hS hM P hB hc1 d false
    have b1 := contourSize_mem_Icc hM hj P.odd_blockSide P.torus.1 P.small hσ hCt P.room_le hc1 (cellBond Y d false)
    have b2 := contourSize_mem_Icc hM hj' P.odd_blockSide' P.torus'.1 P.small' hσ hCt P.room_le hc1
      (cellBond Y' d false)
    have h2 := hCg (T.a * x) _ _ hx b1.1 b1.2 b2.1 b2.2
    have e : haarGapExcess T.a x (chartedField (chartPoint T x V j ζ) V) (Y, d) -
        haarGapExcess T.a x (chartedField (chartPoint T x V' j' ζ) V') (Y', d) =
        haarGap (T.a * x * contourSize T x V j ζ (cellBond Y d false)) -
          haarGap (T.a * x * contourSize T x V' j' ζ (cellBond Y' d false)) := by
      simp only [haarGapExcess, contourSize, cellBond, Bool.false_eq_true, if_false]
      ring
    rw [e]
    exact h2.trans (mul_le_mul_of_nonneg_left h1 hCg0)
  have hhaar : ∀ i, |haarLogRatio (chartPoint T x V j ζ (j i).1.1 (j i).1.2) -
      haarLogRatio (chartPoint T x V' j' ζ (j' i).1.1 (j' i).1.2)| ≤ Ch * frameGap T q := by
    intro i
    have s1 := chartPoint_admissible hj P.small hσ hc1 P.room_le P.σ_le
    have s2 := chartPoint_admissible hj' P.small' hσ hc1 P.room_le P.σ_le
    have hLinv : 1 / (64 * (T.L : ℝ)) ≤ 1 := by
      rw [div_le_one (by positivity)]
      have : (1 : ℝ) ≤ T.L := by exact_mod_cast P.odd_side.pos
      linarith
    have n1 := (s1.coord_small _ (j i).2).trans hLinv
    have n2 := (s2.coord_small _ (j' i).2).trans hLinv
    have h3 := norm_transferredChart_sub_le hD hS P ζ (j' i).1.1 (j' i).1.2
    rw [transferredChart_apply_pair hj'] at h3
    exact (hCh _ _ n1 n2).trans (mul_le_mul_of_nonneg_left h3 hCh0)
  set N : ℝ := (((Finset.univ.filter fun i => enclosingCell (j i).1.1 = Y).card : ℕ) : ℝ) with hN
  have hNle : N ≤ 4 * ((centredCube T.L).card : ℝ) := card_pairs_at_cell_le hD P
  have hsplit : ∀ {G : BlockFrame} {Z : G.Cell} {W : G.GaugeField G.top} {ζ' : StepVariable (finiteCells G)},
      (coldHalfLawAt T x f).linearBlockPart Z ζ' W =
        interpolatedBlockExponent 1 T.a T.chainParams.ρA x (frameRadius x) Z W ζ' +
        (∑ c ∈ (innerBonds (finiteCells G) G.top).filter (fun c => c.1 = Z),
          haarGapExcess T.a x (interpolatedField 1 T.a T.chainParams.ρA (frameRadius x) W ζ') c) +
        (∑ b : ↥(chordBonds (finiteCells G)), if enclosingCell b.1.1 = Z then
          haarLogRatio (interpolatedCoords 1 T.a T.chainParams.ρA (frameRadius x) W ζ' b.1.1 b.1.2) else 0) := by
    intro G Z W ζ'
    simp only [ColdHalfLaw.linearBlockPart, interpolatedBlockExponent, coldHalfLawAt]
    ring
  rw [hsplit, hsplit, sum_innerBonds_at_cell P.two_le_extent, sum_innerBonds_at_cell P.two_le_extent',
    sum_chordBonds_at_cell hj P.short.isBoxPairing.mem_left_iff, sum_chordBonds_at_cell hj' P.short.isBoxPairing.mem_right_iff]
  set ψ := interpolatedBlockExponent 1 T.a T.chainParams.ρA x (frameRadius x) Y V (toTorus j ζ) with hψ
  set ψ' := interpolatedBlockExponent 1 T.a T.chainParams.ρA x (frameRadius x) Y' V' (toTorus j' ζ) with hψ'
  set g₁ := ∑ d, haarGapExcess T.a x
    (interpolatedField 1 T.a T.chainParams.ρA (frameRadius x) V (toTorus j ζ)) (Y, d) with hg₁
  set g₂ := ∑ d, haarGapExcess T.a x
    (interpolatedField 1 T.a T.chainParams.ρA (frameRadius x) V' (toTorus j' ζ)) (Y', d) with hg₂
  set h₁ := ∑ i, if enclosingCell (j i).1.1 = Y then
    haarLogRatio (interpolatedCoords 1 T.a T.chainParams.ρA (frameRadius x) V (toTorus j ζ) (j i).1.1 (j i).1.2)
    else 0 with hh₁
  set h₂ := ∑ i, if enclosingCell (j' i).1.1 = Y' then
    haarLogRatio (interpolatedCoords 1 T.a T.chainParams.ρA (frameRadius x) V' (toTorus j' ζ) (j' i).1.1 (j' i).1.2)
    else 0 with hh₂
  have hA : |g₁ - g₂| ≤ 4 * (Cg * (5 * (T.L : ℝ) * frameGap T q)) := by
    rw [hg₁, hg₂, ← Finset.sum_sub_distrib]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ((Finset.sum_le_sum fun d _ => hgaps d).trans (le_of_eq ?_))
    simp
  have hBd : |h₁ - h₂| ≤ N * (Ch * frameGap T q) := by
    rw [hh₁, hh₂, ← Finset.sum_sub_distrib]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    have hterm' : ∀ i, |(if enclosingCell (j i).1.1 = Y then
        haarLogRatio (interpolatedCoords 1 T.a T.chainParams.ρA (frameRadius x) V (toTorus j ζ) (j i).1.1 (j i).1.2)
        else 0) -
        (if enclosingCell (j' i).1.1 = Y' then
          haarLogRatio
            (interpolatedCoords 1 T.a T.chainParams.ρA (frameRadius x) V' (toTorus j' ζ) (j' i).1.1 (j' i).1.2)
          else 0)| ≤
        if enclosingCell (j i).1.1 = Y then Ch * frameGap T q else 0 := by
      intro i
      by_cases hc : enclosingCell (j i).1.1 = Y
      · rw [if_pos hc, if_pos ((enclosingCell_pair_iff hD P i).1 hc), if_pos hc]
        exact hhaar i
      · have hc' : ¬ enclosingCell (j' i).1.1 = Y' := fun h => hc ((enclosingCell_pair_iff hD P i).2 h)
        rw [if_neg hc, if_neg hc', if_neg hc]
        simp
    refine (Finset.sum_le_sum fun i _ => hterm' i).trans (le_of_eq ?_)
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
  have hsum : |(ψ + g₁ + h₁) - (ψ' + g₂ + h₂)| ≤ |ψ' - ψ| + |g₁ - g₂| + |h₁ - h₂| := by
    have e : (ψ + g₁ + h₁) - (ψ' + g₂ + h₂) = -(ψ' - ψ) + (g₁ - g₂) + (h₁ - h₂) := by ring
    rw [e]
    refine (abs_add_le _ _).trans
      (add_le_add ((abs_add_le _ _).trans (add_le_add (le_of_eq (abs_neg _)) le_rfl)) le_rfl)
  refine hsum.trans ?_
  have hW : 0 ≤ weightedBondNorm T.κ Y j ζ := Finset.sum_nonneg fun _ _ => by positivity
  have hx0 : 0 ≤ x := by
    by_contra hn
    push Not at hn
    nlinarith
  have hQ : 0 ≤ weightedBondNormSq T.κ Y j ζ := Finset.sum_nonneg fun _ _ => by positivity
  set Sq := x * weightedBondNormSq T.κ Y j ζ + 1 with hSq
  have hSq1 : 1 ≤ Sq := by
    have : 0 ≤ x * weightedBondNormSq T.κ Y j ζ := by positivity
    linarith
  set A := 4 * (Cg * (5 * (T.L : ℝ))) + 4 * ((centredCube T.L).card : ℝ) * Ch with hAdef
  have hA0 : 0 ≤ A := by positivity
  have hrest : |g₁ - g₂| + |h₁ - h₂| ≤ A * (T.Ct * T.σ * eq4) := by
    have t1 : N * (Ch * frameGap T q) ≤ (4 * ((centredCube T.L).card : ℝ)) * (Ch * frameGap T q) :=
      mul_le_mul_of_nonneg_right hNle (by positivity)
    have t2 : A * frameGap T q ≤ A * (T.Ct * T.σ * eq4) := mul_le_mul_of_nonneg_left hgap hA0
    have e : A * frameGap T q = 4 * (Cg * (5 * (T.L : ℝ) * frameGap T q)) +
        (4 * ((centredCube T.L).card : ℝ)) * (Ch * frameGap T q) := by
      rw [hAdef]
      ring
    linarith
  have hslope : slopeConstant T Cg Ch = T.Ct + A * (T.Ct * T.σ) := rfl
  have hCs : 0 ≤ slopeConstant T Cg Ch := by
    rw [hslope]
    positivity
  have h1 : A * (T.Ct * T.σ * eq4) ≤ eq4 * (A * (T.Ct * T.σ) * Sq) := by
    have : 0 ≤ A * (T.Ct * T.σ) * eq4 := by positivity
    nlinarith
  have h2 : eq4 * (slopeConstant T Cg Ch * Sq) = T.Ct * eq4 * Sq + eq4 * (A * (T.Ct * T.σ) * Sq) := by
    rw [hslope]
    ring
  have h3 : 0 ≤ eq4 * (slopeConstant T Cg Ch * weightedBondNorm T.κ Y j ζ) := by positivity
  have e : eq4 * (slopeConstant T Cg Ch * weightedBondNorm T.κ Y j ζ + slopeConstant T Cg Ch * Sq) =
      eq4 * (slopeConstant T Cg Ch * weightedBondNorm T.κ Y j ζ) + eq4 * (slopeConstant T Cg Ch * Sq) := by ring
  rw [e, h2]
  linarith
end Slopes
private structure ThresholdConditions (T : _root_.YangMills.Construction.ColdStepAtMirrorFrames.StepParameters) : Prop where
  side_ge : 2 ^ 40 ≤ T.L
  Ct_pos : 0 < T.Ct
  δ₂_pos : 0 < T.chainParams.δ₂
  κ_le : T.κ ≤ T.chainParams.δ₂ / 2 ^ 8
  two_le : 2 ≤ T.blockIndex
  gap_le : 16 * T.Ct * Real.exp (-(T.chainParams.δ₂ / 8 * T.blockIndex)) ≤ 1
  room_le : (T.Ct + 1) * T.σ ≤ 1 / (64 * (T.L : ℝ))
  σ_le : T.σ ≤ T.chainParams.σA
  n₀_ge : 64 ≤ T.n₀
  coupling_ge : 2 / T.a ≤ T.coupling
private theorem eventually_thresholdConditions : EventuallyInParameters ThresholdConditions := by
  intro a ha
  refine ⟨2 ^ 40, fun L hL hL0 c hc => ⟨1, fun Ct hCt => ?_⟩⟩
  have hδ : 0 < c.δ₂ := hc.classical.1.2.2.2.1
  refine ⟨c.δ₂ / 2 ^ 8, by positivity, fun κ hκ hκ' => ⟨1, one_pos, fun η₃ _ _ _ => ?_⟩⟩
  have hCt0 : 0 < Ct := by linarith
  obtain ⟨N₀, hN₀⟩ : ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n → 2 ≤ n ∧ 16 * Ct * Real.exp (-(c.δ₂ / 8 * n)) ≤ 1 := by
    obtain ⟨M, hM⟩ := exists_nat_ge ((8 / c.δ₂) * Real.log (16 * Ct))
    refine ⟨max 2 M, fun n hn => ⟨le_trans (le_max_left _ _) hn, ?_⟩⟩
    have hnM : (M : ℝ) ≤ n := by exact_mod_cast le_trans (le_max_right _ _) hn
    have h1 : Real.log (16 * Ct) ≤ c.δ₂ / 8 * n := by
      have h2 : (8 / c.δ₂) * Real.log (16 * Ct) ≤ n := hM.trans hnM
      have h3 := mul_le_mul_of_nonneg_left h2 (by positivity : 0 ≤ c.δ₂ / 8)
      have e : c.δ₂ / 8 * ((8 / c.δ₂) * Real.log (16 * Ct)) = Real.log (16 * Ct) := by
        field_simp
      linarith
    have h4 : 16 * Ct = Real.exp (Real.log (16 * Ct)) := (Real.exp_log (by positivity)).symm
    rw [h4, ← Real.exp_add]
    apply Real.exp_le_one_iff.2
    linarith
  refine ⟨N₀, fun nss hn => ?_⟩
  have hσA : 0 < c.σA := hc.positivity.2.2.2.1
  have hLp : (0 : ℝ) < L := by
    have := hL.pos
    exact_mod_cast this
  refine ⟨min c.σA (1 / (64 * (L : ℝ) * (Ct + 1))), lt_min hσA (by positivity), fun σ hσ hσ' p hp =>
    ⟨0, fun Cs _ E hE => ⟨64, fun n₀ hn₀ => ⟨0, fun CE _ => ⟨2 / a, fun y₁ hy => ?_⟩⟩⟩⟩⟩
  obtain ⟨g1, g2⟩ := hN₀ nss hn
  have h2 : σ ≤ 1 / (64 * (L : ℝ) * (Ct + 1)) := hσ'.trans (min_le_right _ _)
  refine ⟨hL0, hCt0, hδ, hκ', g1, g2, ?_, hσ'.trans (min_le_left _ _), hn₀, hy⟩
  have hC1 : 0 < Ct + 1 := by linarith
  have e : 1 / (64 * (L : ℝ)) = (Ct + 1) * (1 / (64 * (L : ℝ) * (Ct + 1))) := by
    field_simp
  show (Ct + 1) * σ ≤ 1 / (64 * (L : ℝ))
  rw [e]
  exact mul_le_mul_of_nonneg_left h2 hC1.le
section Table
variable {ι : Type} [Fintype ι] [DecidableEq ι] {T : _root_.YangMills.Construction.ColdStepAtMirrorFrames.StepParameters} {x : ℝ} {V : F.GaugeField F.top}
  {V' : F'.GaugeField F'.top} {Y : F.Cell} {Y' : F'.Cell} {q : ℕ} {j : ι → ↥(chordBonds (finiteCells F))}
  {j' : ι → ↥(chordBonds (finiteCells F'))}
private theorem torusPairData_of_admissible {t : ℕ} {f : LocalFamily} {Cq Cz : ℕ → ℝ} {Cr : ℕ → ℕ → ℕ → ℝ}
    (hT : T.IsOrdered) (hF : ThresholdConditions T) (fr : InterpolatedFrameBoundsAt T Cq Cz Cr t x)
    (hs : IsAdmissibleAt T t x f F V) (hs' : IsAdmissibleAt T t x f F' V')
    (hag : AgreeOnBall (finiteCells F) V (finiteCells F') V' Y Y' q) (hn : IsShortPairing Y Y' q j j')
    (hq : T.blockIndex ≤ q) :
    TorusPairData T x V V' Y Y' q j j' := by
  obtain ⟨hL, ht, n, hn₁, hn₂⟩ := hs.torus
  obtain ⟨hL', ht', n', hn₁', hn₂'⟩ := hs'.torus
  have h64 := hF.n₀_ge
  have s1 : ∀ i, 2 * q + 2 < F.extent i := fun i => by
    rcases hag.1 i with h | h
    · have := hn₁ i
      omega
    · exact h
  have s2 : ∀ i, 2 * q + 2 < F'.extent i := fun i => by
    rcases hag.2.1 i with h | h
    · have := hn₁' i
      omega
    · exact h
  have hqr : (T.blockIndex : ℝ) ≤ q := by exact_mod_cast hq
  have hδ := hF.δ₂_pos
  have hC := hF.Ct_pos
  have e1 : Real.exp (-(T.chainParams.δ₂ / 8 * q)) ≤ Real.exp (-(T.chainParams.δ₂ / 8 * T.blockIndex)) := by
    apply Real.exp_le_exp.2
    nlinarith
  have hσ := hT.σ_pos
  exact
    { odd_side := hT.odd_L
      torus := ⟨hL, n, by omega, hn₁⟩
      torus' := ⟨hL', n', by omega, hn₁'⟩
      depth_eq := ht'.trans ht.symm
      two_le := hF.two_le.trans hq
      extent_gt := s1
      extent_gt' := s2
      agree := hag
      short := hn
      small := (fr.one_torus F V 1 hs.torus hs.small_curvature zero_le_one le_rfl).small
      small' := (fr.one_torus F' V' 1 hs'.torus hs'.small_curvature zero_le_one le_rfl).small
      locality := (fr.two_tori F F' V V' Y Y' q 1 hs.torus hs'.torus hs.small_curvature hs'.small_curvature hag
        zero_le_one le_rfl).1
      σ_pos := hσ
      Ct_pos := hC
      δ₂_pos := hδ
      gap_le := le_trans (mul_le_mul_of_nonneg_left e1 (by positivity)) hF.gap_le
      room_le := hF.room_le
      σ_le := hF.σ_le
      one_le_a := hT.one_le_a
      side_ge := hF.side_ge
      admissible := hT.chain_admissible
      κ_pos := hT.κ_pos
      κ_le := hF.κ_le }
end Table
theorem smoothIncrementsOnTwoTori_holds (hFr : interpolatedFramesStatement) (hBE : CellEnergyShareLocal)
    (hCh : ChartResponse.SharesAndContoursAgreeOnTwoTori) (hKB : CellEnergyKernelBound) (hKS : SiteShareKernelBound)
    (hKF : interpolationKernelBoundsStatement) (hTC : InterpolatedTermsCloseOnTwoTori)
    (hM : ChartLipschitz.ChartedFieldLipschitz) (hD : Estimates.cellOffsetStatement) (hS : SiteDecomposition)
    (hc : Calculus.CompositeDerivativesAtPoint) (hTS : ScoreRemainderExpansion) (hGD : HaarGapDerivBound)
    (hGS : HaarGapContDiff) (hHE : HaarLogRatioNearZero) (hTJ : EventuallyInParametersCombines) :
    SmoothIncrementsOnTwoTori := by
  obtain ⟨Cq, Cz, Cr, hFr⟩ := hFr
  obtain ⟨Kf, Df, -, hDf0, hKF⟩ := hKF
  choose! Cb hCb using hBE
  choose! Cc hCc using hCh
  choose! Kb hKb using hKB
  choose! Ks hKs using hKS
  have tails := fun (a : ℝ) (ha : 1 ≤ a) => exists_remainderDerivBounds hTS ha
  choose! M₁ M₂ hTl using tails
  obtain ⟨Cg, hCg0, hCg⟩ := haarGap_lipschitz hGD hGS
  obtain ⟨Ch, hCh0, hChl⟩ := haarLogRatio_lipschitz hHE
  let Cv : _root_.YangMills.Construction.ColdStepAtMirrorFrames.StepParameters → ℝ := fun T =>
    |cellEnergyConstant T (Cb T.a T.L T.chainParams) (Kb T.a T.L T.chainParams)| +
    |shareConstant T (Cc T.a T.L T.chainParams) (Ks T.a T.L T.chainParams)| +
    |scoreConstant T (Df (rateParameters T) 2 0) (M₁ T.a) (M₂ T.a)| + |slopeConstant T Cg Ch|
  refine ⟨Cv, fun T => by positivity, ?_⟩
  refine hTJ.2 _ _ (fun T hT h => ?_)
    (hTJ.1 _ _ hFr (hTJ.1 _ _ hKF (hTJ.1 _ _ hTC eventually_thresholdConditions)))
  obtain ⟨frames, kern, terms, fl⟩ := h
  have hCv : Cv (parametersBeforeSide T) = Cv T := rfl
  rw [hCv]
  obtain ⟨cb0, cb⟩ := hCb T.a T.L T.chainParams hT.one_le_a hT.odd_L fl.side_ge hT.chain_admissible
  obtain ⟨cc0, cc⟩ := hCc T.a T.L T.chainParams hT.one_le_a hT.odd_L fl.side_ge hT.chain_admissible
  obtain ⟨kb0, kb⟩ := hKb T.a T.L T.chainParams hT.one_le_a hT.odd_L fl.side_ge hT.chain_admissible
  obtain ⟨ks0, ks⟩ := hKs T.a T.L T.chainParams hT.one_le_a hT.odd_L fl.side_ge hT.chain_admissible
  have hρ : 0 ≤ T.ballRadius := by
    have := hT.σ_pos
    unfold StepParameters.ballRadius
    positivity
  have hCb1 : cellEnergyConstant T (Cb T.a T.L T.chainParams) (Kb T.a T.L T.chainParams) ≤ Cv T := by
    have := le_abs_self (cellEnergyConstant T (Cb T.a T.L T.chainParams) (Kb T.a T.L T.chainParams))
    have p1 := abs_nonneg (shareConstant T (Cc T.a T.L T.chainParams) (Ks T.a T.L T.chainParams))
    have p2 := abs_nonneg (scoreConstant T (Df (rateParameters T) 2 0) (M₁ T.a) (M₂ T.a))
    have p3 := abs_nonneg (slopeConstant T Cg Ch)
    show _ ≤ _ + _ + _ + _
    linarith
  have hCs1 : shareConstant T (Cc T.a T.L T.chainParams) (Ks T.a T.L T.chainParams) ≤ Cv T := by
    have := le_abs_self (shareConstant T (Cc T.a T.L T.chainParams) (Ks T.a T.L T.chainParams))
    have p1 := abs_nonneg (cellEnergyConstant T (Cb T.a T.L T.chainParams) (Kb T.a T.L T.chainParams))
    have p2 := abs_nonneg (scoreConstant T (Df (rateParameters T) 2 0) (M₁ T.a) (M₂ T.a))
    have p3 := abs_nonneg (slopeConstant T Cg Ch)
    show _ ≤ _ + _ + _ + _
    linarith
  have hCt1 : scoreConstant T (Df (rateParameters T) 2 0) (M₁ T.a) (M₂ T.a) ≤ Cv T := by
    have := le_abs_self (scoreConstant T (Df (rateParameters T) 2 0) (M₁ T.a) (M₂ T.a))
    have p1 := abs_nonneg (cellEnergyConstant T (Cb T.a T.L T.chainParams) (Kb T.a T.L T.chainParams))
    have p2 := abs_nonneg (shareConstant T (Cc T.a T.L T.chainParams) (Ks T.a T.L T.chainParams))
    have p3 := abs_nonneg (slopeConstant T Cg Ch)
    show _ ≤ _ + _ + _ + _
    linarith
  have hCl1 : slopeConstant T Cg Ch ≤ Cv T := by
    have := le_abs_self (slopeConstant T Cg Ch)
    have p1 := abs_nonneg (cellEnergyConstant T (Cb T.a T.L T.chainParams) (Kb T.a T.L T.chainParams))
    have p2 := abs_nonneg (shareConstant T (Cc T.a T.L T.chainParams) (Ks T.a T.L T.chainParams))
    have p3 := abs_nonneg (scoreConstant T (Df (rateParameters T) 2 0) (M₁ T.a) (M₂ T.a))
    show _ ≤ _ + _ + _ + _
    linarith
  constructor
  · intro t x f F F' V V' Y Y' q ι _ _ j j' ζ hs hs' _ hag hn hq hζ
    have P : TorusPairData T x V V' Y Y' q j j' :=
      torusPairData_of_admissible hT fl (frames t x hs.coupling_le) hs hs' hag hn hq
    have hW : 0 ≤ weightedBondNorm T.κ Y j ζ := Finset.sum_nonneg fun _ _ => by positivity
    have hQ : 0 ≤ weightedBondNormSq T.κ Y j ζ := Finset.sum_nonneg fun _ _ => by positivity
    have he : 0 < Real.exp (-(4 * T.κ * q)) := Real.exp_pos _
    have hx : 2 / T.a ≤ x := fl.coupling_ge.trans hs.coupling_le
    have ha : 0 < T.a := by linarith [hT.one_le_a]
    have hax : 2 ≤ T.a * x := by
      rw [div_le_iff₀ ha] at hx
      linarith
    have hx0 : 0 ≤ x := by
      have : 0 ≤ 2 / T.a := by positivity
      linarith
    have hH := fun (ζ : BondField ι) (hz : ∀ i, ‖ζ i‖ ≤ T.ballRadius) =>
      kern x t F V 1 (toTorus j ζ) hs.coupling_le hs.torus hs.small_curvature zero_le_one le_rfl
        (norm_toTorus_le P.short.isBoxPairing.injective_left hρ hz)
    have hH' := fun (ζ : BondField ι) (hz : ∀ i, ‖ζ i‖ ≤ T.ballRadius) =>
      kern x t F' V' 1 (toTorus j' ζ) hs'.coupling_le hs'.torus hs'.small_curvature zero_le_one le_rfl
        (norm_toTorus_le P.short.isBoxPairing.injective_right hρ hz)
    have hTail := hTl T.a hT.one_le_a (coldHalfLawAt T x f) rfl hx
    refine ⟨?_, ?_, fun i back => ?_⟩
    · refine (abs_cellIncrement_sub_le hD hS hM hc P cb0.le kb0 cb kb f hζ).trans ?_
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hCb1 hW) he.le
    · have tc := terms t x 1 f F F' V V' Y Y' q ι j j' 0 ⟨hs.coupling_le, ⟨zero_le_one, le_rfl⟩, hs.family_bounded,
        hs.torus, hs'.torus, hs.small_curvature, hs'.small_curvature, hag, hq, hn.isBoxPairing.injective_left,
        hn.isBoxPairing.injective_right, fun i => by
          obtain ⟨h, o, k, hh, ho, e₁, e₂⟩ := hn.short_offsets i
          refine ⟨h, o, k, ho, fun l => ?_, e₁, e₂⟩
          have := hh l
          have := abs_nonneg (h l)
          omega, fun i => by simp⟩
      have z0 : Y + siteOfCoords F.top (0 : Fin 4 → ℤ) = Y := by
        funext i
        simp [siteOfCoords]
      have z1 : Y' + siteOfCoords F'.top (0 : Fin 4 → ℤ) = Y' := by
        funext i
        simp [siteOfCoords]
      rw [z0, z1] at tc
      have hterm := (tc.1 ζ hζ).1
      refine (abs_linearPart_sub_le hD hS hM P cc f hCg0 hCh0 hCg hChl hax hζ hterm).trans ?_
      have hSq : 0 ≤ x * weightedBondNormSq T.κ Y j ζ + 1 := by positivity
      refine mul_le_mul_of_nonneg_left (add_le_add ?_ ?_) he.le
      · exact mul_le_mul_of_nonneg_right hCl1 hW
      · exact mul_le_mul_of_nonneg_right hCl1 hSq
    · refine (abs_scoreIncrement_sub_le hD hS hM P cc (hDf0 _ 2 0).le hH hH' f hTail i back hζ).trans ?_
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hCt1 hW) he.le
  · intro t x f F V V' Y q ι _ _ j j' ζ w B hs hs' _ hag hn hq hζ hB0 hw
    have P : TorusPairData T x V V' Y Y q j j' :=
      torusPairData_of_admissible hT fl (frames t x hs.coupling_le) hs hs' hag hn hq
    have hW : 0 ≤ weightedBondNorm T.κ Y j ζ := Finset.sum_nonneg fun _ _ => by positivity
    have he : 0 < Real.exp (-(4 * T.κ * q)) := Real.exp_pos _
    refine (abs_weightedIncrement_sub_le hD hS hM hc P cc0.le ks0 cc ks f hζ hB0 hw).trans ?_
    exact mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCs1 hB0.le) hW) he.le
end YangMills.Construction.WeightedResponses
end
