import YangMills.Construction.ClusterExpansionOfAStep.BondInCoordinates
import YangMills.Construction.SummableBoundsOfTheFlow.LogAlongATiltProof
import Mathlib
set_option autoImplicit false
noncomputable section
open YangMills.Construction.BlockAverages MeasureTheory
namespace YangMills.Construction.ColdStepAtMirrorFrames
variable {F : BlockFrame}
namespace StepDecomposition
theorem measurable_indicator_openBallProduct {ρ : ℝ} {g : StepVariable (finiteCells F) → ℝ}
    (hg : ContinuousOn g (openBallProduct F ρ)) : Measurable ((openBallProduct F ρ).indicator g) := by apply _root_.YangMills.SharedProofs.p50454 <;> assumption
theorem abs_indicator_openBallProduct_le {ρ M : ℝ} {g : StepVariable (finiteCells F) → ℝ} (hM : 0 ≤ M)
    (hg : ∀ η ∈ openBallProduct F ρ, |g η| ≤ M) (η : StepVariable (finiteCells F)) :
    |(openBallProduct F ρ).indicator g η| ≤ M := by apply _root_.YangMills.SharedProofs.p22511 <;> assumption
theorem mem_finiteCells (hs : ∀ i, 2 ≤ F.extent i) (z : F.Cell) : z ∈ finiteCells F := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.CellShares.mem_finiteCells <;> assumption
theorem stepExponent_eq_sub_mul_sum (a ρA x : ℝ) (m : ℕ) (f : LocalFamily) (ν : ℝ)
    (V : F.GaugeField F.top) (η : StepVariable (finiteCells F)) :
    stepExponent false a ρA x m f ν V η = stepExponent false a ρA x m f 0 V η -
      ν * ∑ y ∈ sitesOfCells (finiteCells F) F.depth, centredExpansion false a ρA m f y η V := by
  unfold stepExponent
  ring
theorem toImaginary_zero : toImaginary 0 = 0 := by apply _root_.YangMills.Construction.BondCoordinates.toImaginary_zero <;> assumption
theorem coordsAboveFrame_zero (a ρA : ℝ) (m : ℕ) (V : F.GaugeField F.top) :
    coordsAboveFrame false a ρA m V 0 = fun z i => stepFrame false a ρA m (z, i) V := by
  funext z i
  unfold coordsAboveFrame stepCoordinates
  by_cases h : (z, i) ∈ chordBonds (finiteCells F)
  · simp [h, toImaginary_zero]
  · simp [h]
end StepDecomposition
open StepDecomposition in
theorem logStepIntegralDecomposition_of (hfix : stepIntegralInFixedVariables)
    (hshare : sumCellSharesEqAction) (hbirth : LogPartitionTwoSegmentsLocalDecomposition) :
    logStepIntegralDecomposition := by
  classical
  intro F a ρA ρ lam x M m p f V ha hodd hs hframe hreg
  have hpos : ∀ i, 0 < F.extent i := fun i => by
    have := hs i
    omega
  have hmem := mem_finiteCells (F := F) hs
  set O := openBallProduct F ρ with hO
  set μ : Measure (StepVariable (finiteCells F)) :=
    volume.withDensity fun η => ENNReal.ofReal (cutoffWeight ρ p η) with hμd
  have hfinite : IsFiniteMeasure μ :=
    isFiniteMeasure_withDensity_ofReal hreg.integrable_cutoffWeight.hasFiniteIntegral
  have hint : ∀ g : StepVariable (finiteCells F) → ℝ, ∫ η, g η ∂μ = ∫ η, cutoffWeight ρ p η * g η := by
    intro g
    rw [hμd, integral_withDensity_eq_integral_toReal_smul hreg.measurable_cutoffWeight.ennreal_ofReal
      (ae_of_all _ fun η => ENNReal.ofReal_lt_top)]
    apply integral_congr_ae
    refine Filter.Eventually.of_forall fun η => ?_
    dsimp only
    rw [ENNReal.toReal_ofReal (hreg.cutoffWeight_nonneg η), smul_eq_mul]
  have hμ : μ ≠ 0 := by
    intro h
    have h1 := hint fun _ => 1
    rw [h] at h1
    simp only [integral_zero_measure, mul_one] at h1
    have := hreg.integral_cutoffWeight_pos
    linarith
  set ψ : ↥(finiteCells F) → StepVariable (finiteCells F) → ℝ := fun Y =>
    O.indicator (cellExponent false a ρA x m Y.1 V) with hψ
  set q : ↥(finiteCells F) → StepVariable (finiteCells F) → ℝ := fun Y =>
    O.indicator (cellQuadratic lam x Y.1) with hq
  set G : ↥(finiteCells F) → StepVariable (finiteCells F) → ℝ := fun Y =>
    O.indicator (fun η => cellCentredExpansion false a ρA m f Y.1 η V) with hG
  have hb := hbirth _ μ ↥(finiteCells F) ψ q G M hμ
    (fun Y => measurable_indicator_openBallProduct (hreg.continuousOn_cellExponent Y.1))
    (fun Y => measurable_indicator_openBallProduct (hreg.continuousOn_cellQuadratic Y.1))
    (fun Y => measurable_indicator_openBallProduct (hreg.continuousOn_cellCentredExpansion Y.1))
    (fun Y => abs_indicator_openBallProduct_le hreg.bound_nonneg (hreg.abs_cellExponent_le Y.1))
    (fun Y => abs_indicator_openBallProduct_le hreg.bound_nonneg (hreg.abs_cellQuadratic_le Y.1))
    (fun Y => abs_indicator_openBallProduct_le hreg.bound_nonneg (hreg.abs_cellCentredExpansion_le Y.1))
  have hψO : ∀ η ∈ O, ∀ Y, ψ Y η = cellExponent false a ρA x m Y.1 V η := fun η h Y => by
    simp only [hψ, Set.indicator_of_mem h]
  have hqO : ∀ η ∈ O, ∀ Y, q Y η = cellQuadratic lam x Y.1 η := fun η h Y => by
    simp only [hq, Set.indicator_of_mem h]
  have hGO : ∀ η ∈ O, ∀ Y, G Y η = cellCentredExpansion false a ρA m f Y.1 η V := fun η h Y => by
    simp only [hG, Set.indicator_of_mem h]
  have hS1 : ∀ η ∈ O, ∑ Y, ψ Y η = stepExponent false a ρA x m f 0 V η := by
    intro η h
    simp only [hψO η h]
    rw [Finset.sum_coe_sort (finiteCells F) fun Y => cellExponent false a ρA x m Y V η]
    exact (hreg.stepExponent_eq_sum η h).symm
  have hS2 : ∀ η ∈ O, ∑ Y, q Y η = totalQuadratic lam x η := by
    intro η h
    simp only [hqO η h]
    rw [Finset.sum_coe_sort (finiteCells F) fun Y => cellQuadratic lam x Y η]
    unfold cellQuadratic totalQuadratic
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro b _
    rw [Finset.sum_eq_single (enclosingCell b.1.1)]
    · simp
    · intro Y _ hY
      simp [Ne.symm hY]
    · intro h
      exact absurd (hmem _) h
  have hS3 : ∀ η ∈ O, ∑ Y, G Y η =
      ∑ y ∈ sitesOfCells (finiteCells F) F.depth, centredExpansion false a ρA m f y η V := by
    intro η h
    simp only [hGO η h]
    rw [Finset.sum_coe_sort (finiteCells F) fun Y => cellCentredExpansion false a ρA m f Y η V]
    unfold cellCentredExpansion
    exact Finset.sum_fiberwise_of_maps_to (fun y _ => hmem _) _
  have hoff : ∀ η, η ∉ O → cutoffWeight ρ p η = 0 := hreg.cutoffWeight_eq_zero_of_not_mem
  have hI1 : ∫ η, Real.exp (-(∑ Y, ψ Y η - ∑ Y, G Y η)) ∂μ =
      ∫ η, cutoffWeight ρ p η * Real.exp (- stepExponent false a ρA x m f 1 V η) := by
    rw [hint]
    apply integral_congr_ae
    refine Filter.Eventually.of_forall fun η => ?_
    dsimp only
    by_cases h : η ∈ O
    · rw [hS1 η h, hS3 η h, stepExponent_eq_sub_mul_sum a ρA x m f 1 V η, one_mul]
    · rw [hoff η h]
      simp
  have hI2 : ∫ η, Real.exp (-(∑ Y, q Y η)) ∂μ = gaussianMass ρ lam x p F := by
    rw [hint]
    unfold gaussianMass
    apply integral_congr_ae
    refine Filter.Eventually.of_forall fun η => ?_
    dsimp only
    by_cases h : η ∈ O
    · rw [hS2 η h]
    · rw [hoff η h]
      simp
  have hU : ∀ Y : ↥(finiteCells F), (- ∫ τ in (0 : ℝ)..1, gibbsMean μ
      (fun ω => τ * ∑ Z, ψ Z ω + (1 - τ) * ∑ Z, q Z ω) (fun ω => ψ Y ω - q Y ω)) =
      interactionDensity false a ρA ρ lam x m p f Y.1 V := by
    intro Y
    unfold interactionDensity
    congr 1
    apply intervalIntegral.integral_congr
    intro τ _
    simp only [gibbsMean, cutoffMean]
    rw [hint, hint]
    congr 1
    · apply integral_congr_ae
      refine Filter.Eventually.of_forall fun η => ?_
      dsimp only
      by_cases h : η ∈ O
      · rw [hS1 η h, hS2 η h, hψO η h Y, hqO η h Y]
        ring
      · rw [hoff η h]
        simp
    · apply integral_congr_ae
      refine Filter.Eventually.of_forall fun η => ?_
      dsimp only
      by_cases h : η ∈ O
      · rw [hS1 η h, hS2 η h]
      · rw [hoff η h]
        simp
  have hSd : ∀ Y : ↥(finiteCells F), (∫ ν in (0 : ℝ)..1, gibbsMean μ
      (fun ω => ∑ Z, ψ Z ω - ν * ∑ Z, G Z ω) (G Y)) =
      expansionDensity false a ρA ρ x m p f Y.1 V := by
    intro Y
    unfold expansionDensity
    apply intervalIntegral.integral_congr
    intro ν _
    simp only [gibbsMean, cutoffMean]
    rw [hint, hint]
    congr 1
    · apply integral_congr_ae
      refine Filter.Eventually.of_forall fun η => ?_
      dsimp only
      by_cases h : η ∈ O
      · rw [hS1 η h, hS3 η h, hGO η h Y, stepExponent_eq_sub_mul_sum a ρA x m f ν V η]
        ring
      · rw [hoff η h]
        simp
    · apply integral_congr_ae
      refine Filter.Eventually.of_forall fun η => ?_
      dsimp only
      by_cases h : η ∈ O
      · rw [hS1 η h, hS3 η h, stepExponent_eq_sub_mul_sum a ρA x m f ν V η]
      · rw [hoff η h]
        simp
  rw [hI1, hI2] at hb
  simp only [hU, hSd] at hb
  rw [Finset.sum_coe_sort (finiteCells F) fun Y => interactionDensity false a ρA ρ lam x m p f Y V +
    expansionDensity false a ρA ρ x m p f Y V] at hb
  have hpos1 : 0 < ∫ η, cutoffWeight ρ p η * Real.exp (- stepExponent false a ρA x m f 1 V η) := by
    rw [← hI1]
    have : NeZero μ := ⟨hμ⟩
    apply integral_exp_pos
    have hm : Measurable fun η => Real.exp (-(∑ Y, ψ Y η - ∑ Y, G Y η)) := by
      have h1 : Measurable fun η => ∑ Y, ψ Y η :=
        Finset.measurable_fun_sum _ fun Y _ =>
          measurable_indicator_openBallProduct (hreg.continuousOn_cellExponent Y.1)
      have h2 : Measurable fun η => ∑ Y, G Y η :=
        Finset.measurable_fun_sum _ fun Y _ =>
          measurable_indicator_openBallProduct (hreg.continuousOn_cellCentredExpansion Y.1)
      exact (h1.sub h2).neg.exp
    refine Integrable.of_bound hm.aestronglyMeasurable
      (Real.exp (2 * ((finiteCells F).card : ℝ) * M)) (Filter.Eventually.of_forall fun η => ?_)
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    apply Real.exp_le_exp.mpr
    have hsum : ∀ g : ↥(finiteCells F) → StepVariable (finiteCells F) → ℝ, (∀ Y η, |g Y η| ≤ M) →
        |∑ Y, g Y η| ≤ ((finiteCells F).card : ℝ) * M := by
      intro g hg
      calc |∑ Y, g Y η| ≤ ∑ Y, |g Y η| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _Y : ↥(finiteCells F), M := Finset.sum_le_sum fun Y _ => hg Y η
        _ = _ := by simp
    have h1 := hsum ψ
      (fun Y => abs_indicator_openBallProduct_le hreg.bound_nonneg (hreg.abs_cellExponent_le Y.1))
    have h2 := hsum G
      (fun Y => abs_indicator_openBallProduct_le hreg.bound_nonneg (hreg.abs_cellCentredExpansion_le Y.1))
    have h3 := abs_le.mp h1
    have h4 := abs_le.mp h2
    linarith [h3.1, h3.2, h4.1, h4.2]
  have hJ : 0 < ∏ _b : ↥(chordBonds (finiteCells F)), haarRadialDensity 0 := by
    apply Finset.prod_pos
    intro b _
    unfold haarRadialDensity
    rw [if_pos Real.pi_pos]
    simp only [Real.sinc_zero]
    have := Real.pi_pos
    positivity
  have hfx := hfix F a ρA ρ x m p f V hodd hpos hframe
  rw [hfx, Real.log_mul (by positivity) hpos1.ne', Real.log_mul (by positivity) (Real.exp_pos _).ne',
    Real.log_mul (Real.exp_pos _).ne' hJ.ne', Real.log_exp, Real.log_exp,
    Real.log_prod (fun b _ => by
      unfold haarRadialDensity
      rw [if_pos Real.pi_pos]
      simp only [Real.sinc_zero]
      have := Real.pi_pos
      positivity)]
  obtain ⟨hA, hB⟩ := hshare F a (fun z i => stepFrame false a ρA m (z, i) V) V ha hodd hs
  have hT : ∑ Y ∈ finiteCells F, frameDensity false a ρA x m Y V =
      - x * (chartedEnergy a (coordsAboveFrame false a ρA m V 0) V -
        minimalAction a (finiteCells F) F.top V) := by
    unfold frameDensity
    rw [← Finset.mul_sum, Finset.sum_sub_distrib, hA, hB, coordsAboveFrame_zero]
  rw [Finset.sum_add_distrib, hT]
  linarith
end YangMills.Construction.ColdStepAtMirrorFrames
end
