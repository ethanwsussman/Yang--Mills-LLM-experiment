import YangMills.Construction.ColdStepAtMirrorFrames.BlocksCoverTheLevelBelow
import YangMills.Construction.ColdStepAtMirrorFrames.CompatibleLocalFamiliesGlue
import YangMills.Construction.ColdStepAtMirrorFrames.MovingTheChartCoordinates
import YangMills.Construction.ColdStepAtMirrorFrames.SitesOfABlock
import YangMills.Construction.SummableBoundsOfTheFlow.ExponentBetweenAtATop
import YangMills.Construction.SummableBoundsOfTheFlow.ExponentBetweenBounds
import YangMills.Construction.SummableBoundsOfTheFlow.FloorsOfTheFrames
import YangMills.Construction.SummableBoundsOfTheFlow.FramesBetweenStayNear
import YangMills.Construction.SummableBoundsOfTheFlow.GapTermIsBounded
import YangMills.Construction.SummableBoundsOfTheFlow.HaarTermIsBounded
import YangMills.Construction.SummableBoundsOfTheFlow.SlopeOfTheFramesBetween
import YangMills.Construction.SummableBoundsOfTheFlow.SumOfTheWeightsAboutACell
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction
open BlockAverages ColdStepAtMirrorFrames
namespace Interpolation
namespace ExponentBoundSteps
variable {F : BlockFrame}
theorem card_cellChordBonds_le (hB : SiteDecomposition) (hL : Odd F.blockSide) (hs : ∀ i, 2 ≤ F.extent i)
    (z : F.Cell) : (cellChordBonds z).card ≤ (centredCube F.blockSide).card * 4 := by
  classical
  have := Finset.card_le_card_of_injOn (s := cellChordBonds z)
    (t := centredCube F.blockSide ×ˢ (Finset.univ : Finset (Fin 4)))
    (fun b => (cellOffset b.1.1, b.1.2)) ?_ ?_
  · simpa [Finset.card_product] using this
  · intro b _
    simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe, Finset.mem_univ, and_true]
    exact ((hB F hL hs).2.1 b.1.1).2
  · intro b hb b' hb' hEq
    have hcell : enclosingCell b.1.1 = z := by simpa [cellChordBonds] using hb
    have hcell' : enclosingCell b'.1.1 = z := by simpa [cellChordBonds] using hb'
    simp only [Prod.mk.injEq] at hEq
    have hsite := ((hB F hL hs).2.1 b.1.1).1
    have hsite' := ((hB F hL hs).2.1 b'.1.1).1
    rw [hcell, hEq.1] at hsite
    rw [hcell'] at hsite'
    exact Subtype.ext (Prod.ext (hsite.symm.trans hsite') hEq.2)
theorem nonempty_chordBonds (hB : SiteDecomposition) (hC : BlocksCoverLowerLevel) (hL : Odd F.blockSide)
    (hs : ∀ i, 2 ≤ F.extent i) : Nonempty ↥(chordBonds (finiteCells F)) := by
  classical
  have hpos : ∀ i, 0 < F.extent i := fun i => by have := hs i; omega
  have hmid : (fun _ : Fin 4 => ((F.blockSide : ℤ) - 1) / 2) ∈ centredCube F.blockSide := by
    simp [centredCube, Fintype.mem_piFinset]
    have := hL.pos
    omega
  set x : F.Site F.depth := cellCentre F.depth (0 : F.Cell) +
    siteOfCoords F.depth (fun _ => ((F.blockSide : ℤ) - 1) / 2) with hx
  have hoff := ((hB F hL hs).1 0 _ hmid).2
  have hcross : IsCrossingBond (x, (0 : Fin 4)) := ((hB F hL hs).2.2.1 x 0).2 (by rw [hoff])
  have hnot : ¬ IsAxialTreeBond (x, (0 : Fin 4)) := fun h => h.1 hcross
  refine ⟨⟨(x, 0), ?_⟩⟩
  unfold chordBonds innerBonds
  simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_univ, and_true]
  exact ⟨⟨hC F hL hpos x, hC F hL hpos _⟩, hnot⟩
def derivBoundSum (D : ℕ → ℕ → ℝ) : ℝ := ∑ l ∈ Finset.range 4, ∑ j ∈ Finset.range 4, D l j
theorem derivBoundSum_nonneg {D : ℕ → ℕ → ℝ} (h : ∀ l j, 0 < D l j) : 0 ≤ derivBoundSum D :=
  Finset.sum_nonneg fun l _ => Finset.sum_nonneg fun j _ => (h l j).le
theorem le_derivBoundSum {D : ℕ → ℕ → ℝ} (h : ∀ l j, 0 < D l j) (l j : ℕ) (hl : l ≤ 3) (hj : j ≤ 3) :
    D l j ≤ derivBoundSum D := by
  have hrow : D l j ≤ ∑ j ∈ Finset.range 4, D l j :=
    Finset.single_le_sum (f := fun j => D l j) (fun j _ => (h l j).le) (Finset.mem_range.2 (by omega))
  have hall : ∑ j ∈ Finset.range 4, D l j ≤ derivBoundSum D :=
    Finset.single_le_sum (f := fun l => ∑ j ∈ Finset.range 4, D l j)
      (fun l _ => Finset.sum_nonneg fun j _ => (h l j).le) (Finset.mem_range.2 (by omega))
  exact hrow.trans hall
structure ExponentBoundConstants (D : StepParameters → ℕ → ℕ → ℝ) (Cg : ℝ) (T : StepParameters) : Prop where
  two_le_n₀ : 2 ≤ T.n₀
  rate_le : 2 ^ 10 * T.κ ≤ T.chainParams.δ₂
  one_le_Ct : 1 ≤ T.Ct
  small_field : T.Ct * T.σ + 5 * (T.L : ℝ) * T.ballRadius ≤ 1 / 2
  gap_le : ∀ x, T.coupling ≤ x → 2 ≤ x ∧ x * (T.Ct * frameGapBound T (frameRadius x)) ≤ 1
  weight_sums : ∃ Wt : ℝ, (∀ F : BlockFrame, F.blockSide = T.L → (∀ i, 2 ≤ F.extent i) → ∀ z : F.Cell,
      ∑ b : ↥(chordBonds (finiteCells F)),
        Real.exp (-(T.chainParams.δ₂ / 2 * (cellSupDist (enclosingCell b.1.1) z : ℝ))) ≤ Wt) ∧
    ((((centredCube T.L).card * 4 : ℕ) : ℝ) * T.ballRadius +
      (Wt + (((centredCube T.L).card * 4 : ℕ) : ℝ)) / 2 * derivBoundSum (D (rateParameters T)) +
      4 * (Cg + derivBoundSum (D (rateParameters T))) +
      (((centredCube T.L).card * 4 : ℕ) : ℝ) * (1 + derivBoundSum (D (rateParameters T))) ≤ T.Cs) ∧
    (derivBoundSum (D (rateParameters T)) * ((((centredCube T.L).card * 4 : ℕ) : ℝ) + 1) + 1 +
      derivBoundSum (D (rateParameters T)) * (Wt + 1) + 4 * derivBoundSum (D (rateParameters T)) +
      (((centredCube T.L).card * 4 : ℕ) : ℝ) * derivBoundSum (D (rateParameters T)) ≤ T.Cs) ∧
    ((((centredCube T.L).card * 4 : ℕ) : ℝ) * T.ballRadius * derivBoundSum (D (rateParameters T)) +
      2 * derivBoundSum (D (rateParameters T)) + 4 * derivBoundSum (D (rateParameters T)) +
      (((centredCube T.L).card * 4 : ℕ) : ℝ) * derivBoundSum (D (rateParameters T)) ≤ T.Cs)
theorem eventually_exponentBoundConstants (hF : Estimates.frameRadiusGrowthStatement)
    (hS : CellCounting.ExpDecaySumBounded) (hB : SiteDecomposition) (D : StepParameters → ℕ → ℕ → ℝ) (Cg : ℝ) :
    EventuallyInParameters (ExponentBoundConstants D Cg) := by
  intro a _
  refine ⟨0, fun L hL _ c hc => ?_⟩
  have hδ : 0 < c.δ₂ := hc.classical.1.2.2.2.1
  refine ⟨1, fun Ct hCt => ?_⟩
  refine ⟨c.δ₂ / 2 ^ 10, by positivity, fun κ hκ hκle => ?_⟩
  refine ⟨1, one_pos, fun η₃ _ _ _ => ?_⟩
  refine ⟨0, fun nss _ => ?_⟩
  have hL0 : (0 : ℝ) ≤ L := Nat.cast_nonneg _
  have hCL : 0 < Ct + L := by linarith
  refine ⟨1 / (2 * (Ct + L)), by positivity, fun σ hσ hσle p _ => ?_⟩
  obtain ⟨W₀, hW0, hW⟩ := hS ((centredCube L).card * 4) (c.δ₂ / 2) (by positivity)
  set Dm := derivBoundSum (D ⟨a, L, c, Ct, κ, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩) with hDm
  set Nb : ℝ := (((centredCube L).card * 4 : ℕ) : ℝ) with hNb
  set r : ℝ := σ / 64 with hr
  refine ⟨max (max (Nb * r + (W₀ + Nb) / 2 * Dm + 4 * (Cg + Dm) + Nb * (1 + Dm))
      (Dm * (Nb + 1) + 1 + Dm * (W₀ + 1) + 4 * Dm + Nb * Dm))
      (Nb * r * Dm + 2 * Dm + 4 * Dm + Nb * Dm), fun Cs hCs E _ => ?_⟩
  refine ⟨2, fun n₀ hn₀ => ?_⟩
  refine ⟨0, fun CE _ => ?_⟩
  obtain ⟨y, hy1, hy⟩ := hF (Ct ^ 2 + 1) (c.δ₂ / 4) (by positivity) (by positivity)
  refine ⟨max y 2, fun y₁ hy₁ => ?_⟩
  refine ⟨hn₀, ?_, hCt, ?_, ?_, ?_⟩
  · change 2 ^ 10 * κ ≤ c.δ₂
    have := mul_le_mul_of_nonneg_left hκle (by positivity : (0 : ℝ) ≤ 2 ^ 10)
    have e : (2 : ℝ) ^ 10 * (c.δ₂ / 2 ^ 10) = c.δ₂ := by ring
    linarith
  · change Ct * σ + 5 * (L : ℝ) * (σ / 64) ≤ 1 / 2
    have h1 : (Ct + L) * σ ≤ 1 / 2 := by
      have := mul_le_mul_of_nonneg_left hσle hCL.le
      have e : (Ct + L) * (1 / (2 * (Ct + L))) = 1 / 2 := by field_simp
      linarith
    have h2 : 5 * (L : ℝ) * (σ / 64) ≤ L * σ := by nlinarith [mul_nonneg hL0 hσ.le]
    nlinarith
  · intro x hx
    have hx' : y₁ ≤ x := hx
    have hxy : y ≤ x := ((le_max_left _ _).trans hy₁).trans hx'
    have hx2 : 2 ≤ x := ((le_max_right _ _).trans hy₁).trans hx'
    refine ⟨hx2, ?_⟩
    have h1 := (hy x hxy).1
    change x * (Ct * (Ct * Real.exp (-(c.δ₂ / 4 * (frameRadius x : ℝ))))) ≤ 1
    have he := Real.exp_pos (-(c.δ₂ / 4 * (frameRadius x : ℝ)))
    have h2 : x * (Ct * (Ct * Real.exp (-(c.δ₂ / 4 * (frameRadius x : ℝ))))) ≤
        (Ct ^ 2 + 1) * x ^ 2 * Real.exp (-(c.δ₂ / 4 * (frameRadius x : ℝ))) := by
      have hxx : x ≤ x ^ 2 := by nlinarith
      have h3 : x * Ct ^ 2 ≤ (Ct ^ 2 + 1) * x ^ 2 := by
        calc x * Ct ^ 2 = Ct ^ 2 * x := by ring
          _ ≤ Ct ^ 2 * x ^ 2 := mul_le_mul_of_nonneg_left hxx (sq_nonneg _)
          _ ≤ (Ct ^ 2 + 1) * x ^ 2 := by nlinarith [sq_nonneg x]
      have := mul_le_mul_of_nonneg_right h3 he.le
      nlinarith
    exact h2.trans h1
  · refine ⟨W₀, ?_, ?_, ?_, ?_⟩
    · intro F hFL hs z
      change ∑ b : ↥(chordBonds (finiteCells F)),
        Real.exp (-(c.δ₂ / 2 * (cellSupDist (enclosingCell b.1.1) z : ℝ))) ≤ W₀
      have hLF : Odd F.blockSide := hFL ▸ hL
      refine hW F ↥(chordBonds (finiteCells F)) (fun b => enclosingCell b.1.1) (fun z' => ?_) z
      have := card_cellChordBonds_le hB hLF hs z'
      rw [hFL] at this
      exact this
    · exact ((le_max_left _ _).trans (le_max_left _ _)).trans hCs
    · exact ((le_max_right _ _).trans (le_max_left _ _)).trans hCs
    · exact (le_max_right _ _).trans hCs
theorem norm_toImaginary (v : EuclideanSpace ℝ (Fin 3)) : ‖toImaginary v‖ = ‖v‖ := by
  have h1 : ‖toImaginary v‖ ^ 2 = ‖v‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq, Fin.sum_univ_three, Submodule.coe_norm, sq,
      ← Quaternion.normSq_eq_norm_mul_self, Quaternion.normSq_def']
    simp only [toImaginary]
    simp [sq_abs]
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp h1
theorem stepCoordinates_of_chordBond (η : StepVariable (finiteCells F)) (b : ↥(chordBonds (finiteCells F))) :
    stepCoordinates η b.1.1 b.1.2 = toImaginary (η b) := by
  unfold stepCoordinates
  rw [dif_pos b.2]
end ExponentBoundSteps
open ExponentBoundSteps in
theorem interpolatedExponentBounds_holds (hKern : interpolationKernelBoundsStatement)
    (hSlope : interpolatedSlopeSmallOnTorus) (hNear : interpolatedFramesControlled)
    (hFloors : Estimates.frameRadiusGrowthStatement) (hSum : CellCounting.ExpDecaySumBounded)
    (hTop : interpolatedExponentBoundsAtTopStatement) (hJoin : EventuallyInParametersCombines)
    (hGap : ScaledVariables.HaarGapExcessBounded) (hHaar : Estimates.haarLogRatioBoundStatement)
    (hMove : ChartShiftLipschitz) (hB : SiteDecomposition)
    (hC : BlocksCoverLowerLevel) : interpolatedExponentBoundsStatement := by
  obtain ⟨K, Dk, -, hDpos, hKT⟩ := hKern
  obtain ⟨Cg, hCg0, hCg⟩ := hGap
  have hP := hJoin.1 _ _ (hJoin.1 _ _ (hJoin.1 _ _ hKT hSlope) hNear)
    (eventually_exponentBoundConstants hFloors hSum hB Dk Cg)
  refine hJoin.2 _ _ ?_ hP
  rintro T hT ⟨⟨⟨hk, hs⟩, hn⟩, hnum⟩ t x hx F V s ht hcold hs0 hs1
  obtain ⟨hFL, -, n, hside, hn₀⟩ := id ht
  have hn2 : 2 ≤ n := hnum.two_le_n₀.trans hn₀
  have hs2 : ∀ i, 2 ≤ F.extent i := fun i => by rw [hside i]; exact hn2
  have hLodd : Odd F.blockSide := hFL ▸ hT.odd_L
  have hr : 0 < T.ballRadius := by
    have := hT.σ_pos
    unfold StepParameters.ballRadius
    positivity
  obtain ⟨hx2, hωx⟩ := hnum.gap_le x hx
  have hne := nonempty_chordBonds hB hC hLodd hs2
  obtain ⟨Wt, hW, hC1, hC2, hC3⟩ := hnum.weight_sums
  obtain ⟨-, hsmall⟩ := (hn t x hx).single F V s ht hcold hs0 hs1
  have hρA : T.chainParams.ρA ≤ 1 := hT.chain_admissible.classical.1.2.1
  have hCt := hnum.one_le_Ct
  have hω0 : 0 ≤ T.Ct * frameGapBound T (frameRadius x) := by
    unfold frameGapBound
    have := Real.exp_pos (-(T.chainParams.δ₂ / 4 * (frameRadius x : ℝ)))
    have : 0 ≤ T.Ct := by linarith
    positivity
  refine hTop F s T.a T.chainParams.ρA T.ballRadius x T.κ T.chainParams.κ₂ T.chainParams.δ₂ T.Ct
    (frameGapBound T (frameRadius x)) T.Cs Cg 1 Wt
    (derivBoundSum (Dk (rateParameters T))) (frameRadius x) ((centredCube T.L).card * 4) (K (rateParameters T))
    (Dk (rateParameters T)) V hne hr hT.κ_pos hnum.rate_le (by linarith) hω0 hωx hCg0 zero_le_one
    (derivBoundSum_nonneg (hDpos _)) (le_derivBoundSum (hDpos _)) (fun z => ?_) (hW F hFL hs2)
    (fun η hη => hk x t F V s η hx ht hcold hs0 hs1 hη) (hs t x hx F V s ht hcold hs0 hs1)
    (fun η c₀ hη _ => ?_) (fun η b hη => ?_) hC1 hC2 hC3
  · have := card_cellChordBonds_le hB hLodd hs2 z
    rwa [hFL] at this
  · refine hCg F T.a x _ V c₀ hLodd hT.one_le_a hx2 fun h π hh => ?_
    have hm := (hMove F V (fun z i => interpolatedFrame s T.a T.chainParams.ρA (frameRadius x) (z, i) V) η
      T.ballRadius hLodd (fun b => (hη b).le) hr.le).2.2 c₀ h π hh
    have hc := hsmall.contour_near_one c₀ h π hh
    have hcd := hnum.small_field
    rw [hFL] at hm
    have e : interpolatedField s T.a T.chainParams.ρA (frameRadius x) V η = chartedField (fun z i =>
        interpolatedFrame s T.a T.chainParams.ρA (frameRadius x) (z, i) V + stepCoordinates η z i) V := rfl
    rw [e]
    linarith
  · refine hHaar _ ?_
    have e : interpolatedCoords s T.a T.chainParams.ρA (frameRadius x) V η b.1.1 b.1.2 =
        interpolatedFrame s T.a T.chainParams.ρA (frameRadius x) b.1 V + toImaginary (η b) := by
      simp only [interpolatedCoords, stepCoordinates_of_chordBond]
    rw [e]
    have h1 := hsmall.norm_add_le b.1 b.2
    have h2 := hη b
    have h3 : ‖toImaginary (η b)‖ = ‖η b‖ := norm_toImaginary _
    have h4 := norm_add_le (interpolatedFrame s T.a T.chainParams.ρA (frameRadius x) b.1 V) (toImaginary (η b))
    have h5 : T.ballRadius = T.σ / 64 := rfl
    linarith
end Interpolation
end YangMills.Construction
end
