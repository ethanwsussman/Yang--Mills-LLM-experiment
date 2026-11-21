import YangMills.Construction.ReflectionPositivity.ApproximationWithALimitOnEveryTupleIsBoundedProof
import YangMills.Construction.InequalityOnMirroredCopies.SizeAtASmallRadius
import YangMills.Construction.LawInAState.FromSixteenCopiesToOneBoxProof
import YangMills.Construction.ParameterData.FirstPassagesAreData
import YangMills.Construction.SixteenPointsOnASmallTorus.TheInequalityAtEveryDatum
import YangMills.Construction.SystemOfAdmissibleConstants.CentredCellValueOnTheWindow
import YangMills.Construction.SystemOfAdmissibleConstants.MeansAndValuesOfACellFunction
import Mathlib
set_option autoImplicit false
open MeasureTheory Filter
noncomputable section
namespace YangMills.Construction.SystemOfAdmissibleConstants
open YangMills.Construction.ChessboardTori YangMills.Construction.ReflectedCopies
open YangMills.Construction.TrajectoryData
open YangMills.Construction.InfiniteLattice (AmbientSpace periodicGibbsSet smearedEnergy)
private theorem abs_apply_le_euclidNormVec (v : AmbientSpace) (μ : Fin 4) :
    |v μ| ≤ TorusMetric.euclidNormVec v := by apply _root_.YangMills.SharedProofs.p10398 <;> assumption
private theorem cellSide_pos {S : ChessboardSetup} (c : GridCell S) : 0 < c.grid.cellSide := by
  have hL := S.one_lt_factor
  exact zpow_pos (by linarith) _
private theorem coords_of_mem_quarterBall {S : ChessboardSetup} (c : GridCell S) {x : AmbientSpace}
    (hx : x ∈ TestFunctions.closedBallR4 c.centre (c.side / 4)) (μ : Fin 4) :
    c.grid.cellSide / 4 ≤ x μ - (c.grid.origin μ + c.grid.cellSide * c.index μ) ∧
      x μ - (c.grid.origin μ + c.grid.cellSide * c.index μ) ≤ 3 * c.grid.cellSide / 4 := by
  have h : TorusMetric.euclidNormVec (x - c.centre) ≤ c.grid.cellSide / 4 := hx
  have h1 : |x μ - c.centre μ| ≤ c.grid.cellSide / 4 :=
    (abs_apply_le_euclidNormVec (x - c.centre) μ).trans h
  have h2 : c.centre μ = c.grid.origin μ + c.grid.cellSide * c.index μ + c.grid.cellSide / 2 := rfl
  rw [h2] at h1
  have h3 := abs_le.1 h1
  constructor <;> linarith [h3.1, h3.2]
private theorem supportedInCell_quarter {S : ChessboardSetup} (c : GridCell S) {f : AmbientSpace → ℝ}
    (hf : TestFunctions.IsLipschitzFor TestFunctions.euclidDistR4 f)
    (hs : tsupport f ⊆ TestFunctions.closedBallR4 c.centre (c.side / 4)) :
    SupportedInCell c (c.side / 4) f := by
  have hpos := cellSide_pos c
  have hball : ∀ x, f x ≠ 0 → x ∈ TestFunctions.closedBallR4 c.centre (c.side / 4) :=
    fun x hx => hs (subset_tsupport f (Function.mem_support.2 hx))
  refine ⟨div_pos hpos (by norm_num), le_rfl, hf, ⟨c.centre, hball⟩, ?_, ?_⟩
  · intro x hx μ
    obtain ⟨h1, h2⟩ := coords_of_mem_quarterBall c (hball x hx) μ
    exact ⟨by linarith, by linarith⟩
  · intro x hx z hz
    simp only [ReflectionGrid.walls, Set.mem_iUnion] at hz
    obtain ⟨μ, k, hk⟩ := hz
    have hk' : z μ = c.grid.origin μ + k * c.grid.cellSide := hk
    obtain ⟨h1, h2⟩ := coords_of_mem_quarterBall c (hball x hx) μ
    have hv := abs_apply_le_euclidNormVec (x - z) μ
    have hsub : (x - z) μ = x μ - (c.grid.origin μ + k * c.grid.cellSide) := by
      rw [← hk']; rfl
    rw [hsub] at hv
    exact show c.grid.cellSide / 4 ≤ TorusMetric.euclidNormVec (x - z) from by
      rcases le_or_gt k (c.index μ) with hle | hgt
      · have hr : (k : ℝ) ≤ c.index μ := by exact_mod_cast hle
        have h3 : (k : ℝ) * c.grid.cellSide ≤ c.index μ * c.grid.cellSide :=
          mul_le_mul_of_nonneg_right hr hpos.le
        have h4 := le_abs_self (x μ - (c.grid.origin μ + k * c.grid.cellSide))
        linarith
      · have hr : (c.index μ : ℝ) + 1 ≤ k := by exact_mod_cast hgt
        have h3 : ((c.index μ : ℝ) + 1) * c.grid.cellSide ≤ k * c.grid.cellSide :=
          mul_le_mul_of_nonneg_right hr hpos.le
        have h4 := neg_abs_le (x μ - (c.grid.origin μ + k * c.grid.cellSide))
        linarith
private theorem two_le_K_of_side_le_one {S : ChessboardSetup} (c : GridCell S) (hc : c.side ≤ 1) :
    2 ≤ (S.K : ℕ) := by
  by_contra hK
  have hK1 : (S.K : ℕ) = 1 := by
    have := S.K.pos
    omega
  have hL := S.one_lt_factor
  have ha : S.mesh = (S.L : ℝ)⁻¹ := by
    simp [ChessboardSetup.mesh, PeriodicLattice.meshSize, hK1]
  have hs : S.mesh ≤ c.grid.cellSide / (S.L : ℝ) ^ 2 := c.hasAdmissibleSide.2
  have hc' : c.grid.cellSide ≤ 1 := hc
  rw [ha, le_div_iff₀ (by positivity)] at hs
  have h1 : (S.L : ℝ)⁻¹ * (S.L : ℝ) ^ 2 = S.L := by
    field_simp
  linarith
private theorem lipConstR4_nonneg (f : AmbientSpace → ℝ) : 0 ≤ TestFunctions.lipConstR4 f := by apply _root_.YangMills.Construction.ReflectionPositivity.ApproximatingSequences.BoundedOfLimits.lipConstR4_nonneg <;> assumption
private theorem two_mul_copyBound_le {A b A' M l : ℝ} (hA' : 0 ≤ A') (hM : 1 ≤ M) (hl : 0 < l)
    (hsize : copySize A b l (l / 4) ≤ A' / (l / 4)) (f : AmbientSpace → ℝ) :
    2 * copyBound A b l (l / 4) f ≤ 8 * A' * l⁻¹ * TestFunctions.sharpNormR4 M f := by
  have hlip := lipConstR4_nonneg f
  have hρ : 0 < l / 4 := by positivity
  have hnorm0 : 0 ≤ radiusNorm (l / 4) f :=
    le_max_of_le_right (mul_nonneg (le_min zero_le_one hρ.le) hlip)
  have hnorm : radiusNorm (l / 4) f ≤ TestFunctions.sharpNormR4 M f := by
    refine max_le_max le_rfl (mul_le_mul_of_nonneg_right ?_ hlip)
    exact (min_le_left _ _).trans (by linarith)
  have hq : copyBound A b l (l / 4) f ≤ A' / (l / 4) * TestFunctions.sharpNormR4 M f :=
    mul_le_mul hsize hnorm hnorm0 (by positivity)
  calc 2 * copyBound A b l (l / 4) f
      ≤ 2 * (A' / (l / 4) * TestFunctions.sharpNormR4 M f) := by linarith
    _ = 8 * A' * l⁻¹ * TestFunctions.sharpNormR4 M f := by
      field_simp
      ring
private theorem chessboardBound_of_cell (hMV : AdmissibleConstants.CellFunctionMeanBounds)
    {A b A' M : ℝ} (hA : 0 ≤ A) (hb : 0 ≤ b) (hA' : 0 ≤ A')
    (hsize : ∀ l ρ : ℝ, 0 < l → l ≤ 1 → 0 < ρ → ρ ≤ 1 → copySize A b l ρ ≤ A' / ρ) (hM : 1 ≤ M)
    {S : ChessboardSetup} (hI : CopyInequality S A b) (c : GridCell S) (hc : c.side ≤ 1)
    {f : AmbientSpace → ℝ}
    (hf : TestFunctions.IsLipschitzFor TestFunctions.euclidDistR4 f)
    (hs : tsupport f ⊆ TestFunctions.closedBallR4 c.centre (c.side / 4))
    {ν : Measure S.GaugeField} (hν : ν ∈ periodicGibbsSet S.L S.K S.β) :
    centredSmeared S f (∫ U, smearedEnergy f U ∂ν) ∈ ReflectionGrid.cellObservables (D := S) c.cell ∧
      ∀ (m : ℕ+ → ℕ+) (hm : c.IsAdmissibleSideSequence m)
        (hF : centredSmeared S f (∫ U, smearedEnergy f U ∂ν) ∈
          ReflectionGrid.cellObservables (D := S) c.cell),
        c.limsupChessboardNorm m hm _ hF ≤ 8 * A' * c.side⁻¹ * TestFunctions.sharpNormR4 M f := by
  obtain ⟨κ, hmean, -, hval⟩ := hMV S A b hA hb hI c (c.side / 4) f (supportedInCell_quarter c hf hs)
  have he := hval _ (hmean ν hν)
  refine ⟨he.1, fun m hm hF => ?_⟩
  have hl : 0 < c.side := cellSide_pos c
  have hq := two_mul_copyBound_le hA' hM hl
    (hsize c.side (c.side / 4) hl hc (by positivity) (by linarith)) f
  have hle : ∀ r, c.chessboardNormAt m (centredSmeared S f (∫ U, smearedEnergy f U ∂ν)) r ≤
      2 * copyBound A b c.side (c.side / 4) f := fun r => he.2 (m r) (hm.1 r)
  have h0 : ∀ r, 0 ≤ c.chessboardNormAt m (centredSmeared S f (∫ U, smearedEnergy f U ∂ν)) r := by
    intro r
    unfold GridCell.chessboardNormAt ReflectionGrid.chessboardNormOfCell
      ReflectionGrid.cellChessboardSeminorm
    positivity
  refine le_trans ?_ hq
  unfold GridCell.limsupChessboardNorm
  exact limsup_le_of_le (isBoundedUnder_of ⟨0, h0⟩).isCoboundedUnder_le (Eventually.of_forall hle)
theorem centredCellChessboardBound_holds
    (hP : SmallTorusCopies.copyInequalityForAdmissibleFlows)
    (hD : windowMembersAreDataStatement)
    (hMV : AdmissibleConstants.CellFunctionMeanBounds)
    (hS : CopySizeSmallRadius.Statement) : CentredCellChessboardBound := by
  intro a ha
  obtain ⟨L₀, r₀, C₀, hr₀, hT⟩ := hP a ha
  refine ⟨L₀, r₀, C₀, hr₀, ?_⟩
  intro L hodd hL₀ T hTa hTL hdr hcs hon hr hC
  obtain ⟨y₀, hy₀⟩ := hT L hodd hL₀ T hTa hTL hdr hcs hon hr hC
  refine ⟨y₀, ?_⟩
  intro y hy hrow hW D hDh g hg hfl
  have hup := hy₀ y hy hrow hW
  have hstar : D.floorStar ≤ g ^ (-2 : ℤ) := le_trans (le_max_left _ _) hfl
  by_cases hroom : y + 2 * T.B ≤ D.threshold g
  · obtain ⟨A, b, hA, hb, hI⟩ := hup _ hroom
    have hA0 : 0 ≤ A := by linarith
    have hb0 : 0 ≤ b := by linarith
    obtain ⟨A', hA', hsz⟩ := hS A b hA0 hb0
    refine ⟨8 * A', by positivity, ?_⟩
    intro M hM S hSL hw c hc f hf hs ν hν
    have hdat := hD T y D hDh g hg hstar _ _ (two_le_K_of_side_le_one c hc) hw
    have hI' := hI S hSL ⟨hdat.two_le, hdat.floor, hdat.le_threshold⟩
    exact chessboardBound_of_cell hMV hA0 hb0 hA' hsz hM hI' c hc hf hs hν
  · refine ⟨0, le_rfl, ?_⟩
    intro M hM S hSL hw c hc
    have hdat := hD T y D hDh g hg hstar _ _ (two_le_K_of_side_le_one c hc) hw
    exact absurd hdat.room hroom
end YangMills.Construction.SystemOfAdmissibleConstants
end
