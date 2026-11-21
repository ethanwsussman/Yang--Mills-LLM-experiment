import YangMills.Construction.SummableBoundsOfTheFlow.ObservablesInTheLawsBetweenProof
import YangMills.Construction.ColdStepAtMirrorFrames.BirthsAlongTwoSegments
import YangMills.Construction.ColdStepAtMirrorFrames.StepInFixedVariables
import YangMills.Construction.ColdStepAtMirrorFrames.SumOfTheSharesProof
import YangMills.Construction.SummableBoundsOfTheFlow.LogAlongATilt
import Mathlib
set_option autoImplicit false
noncomputable section
open YangMills.Construction.BlockAverages YangMills.Construction.ColdStepAtMirrorFrames YangMills.Construction.Estimates MeasureTheory
namespace YangMills.Construction.Interpolation
variable {F : BlockFrame}
private theorem stepFrame_small_eq {m₁ : ℕ} (hm : ¬ ∀ i, 4 * m₁ + 5 < F.extent i) (a ρA : ℝ) (m : ℕ)
    (b : F.Site F.depth × Fin 4) (V : F.GaugeField F.top) :
    stepFrame false a ρA m₁ b V = stepFrame true a ρA m b V := by
  simp [stepFrame, bondFrameCoord, hm]
private theorem coordsAboveFrame_small_eq {m₁ : ℕ} (hm : ¬ ∀ i, 4 * m₁ + 5 < F.extent i) (a ρA : ℝ) (m : ℕ)
    (V : F.GaugeField F.top) (η : StepVariable (finiteCells F)) :
    coordsAboveFrame false a ρA m₁ V η = coordsAboveFrame true a ρA m V η := by
  funext z i
  simp only [coordsAboveFrame, stepFrame_small_eq hm a ρA m (z, i) V]
private theorem fieldAboveFrame_small_eq {m₁ : ℕ} (hm : ¬ ∀ i, 4 * m₁ + 5 < F.extent i) (a ρA : ℝ) (m : ℕ)
    (V : F.GaugeField F.top) (η : StepVariable (finiteCells F)) :
    fieldAboveFrame false a ρA m₁ V η = fieldAboveFrame true a ρA m V η := by
  simp only [fieldAboveFrame, coordsAboveFrame_small_eq hm a ρA m V η]
private theorem centredExpansion_small_eq {m₁ : ℕ} (hm : ¬ ∀ i, 4 * m₁ + 5 < F.extent i) (a ρA : ℝ) (m : ℕ)
    (f : LocalFamily) (y : F.Site F.depth) (V : F.GaugeField F.top) (η : StepVariable (finiteCells F)) :
    centredExpansion false a ρA m₁ f y η V = centredExpansion true a ρA m f y η V := by
  simp only [centredExpansion, fieldAboveFrame_small_eq hm a ρA m V η]
private theorem stepExponent_small_eq {m₁ : ℕ} (hm : ¬ ∀ i, 4 * m₁ + 5 < F.extent i) (a ρA x : ℝ) (m : ℕ)
    (f : LocalFamily) (ν : ℝ) (V : F.GaugeField F.top) (η : StepVariable (finiteCells F)) :
    stepExponent false a ρA x m₁ f ν V η = stepExponent true a ρA x m f ν V η := by
  simp only [stepExponent, coordsAboveFrame_small_eq hm a ρA m V, fieldAboveFrame_small_eq hm a ρA m V η,
    centredExpansion_small_eq hm a ρA m f _ V η]
private theorem interpolatedStepIntegral_zero_eq {m₁ : ℕ} (hm : ¬ ∀ i, 4 * m₁ + 5 < F.extent i)
    (a ρA ρ x : ℝ) (m : ℕ) (p : ℝ → ℝ) (f : LocalFamily) (V : F.GaugeField F.top) :
    interpolatedStepIntegral 0 a ρA ρ x m p f V = stepIntegral a ρA ρ x m₁ p f (finiteCells F) V := by
  have hb : ∀ b : F.Site F.depth × Fin 4,
      interpolatedFrame 0 a ρA m b V = bondFrameCoord a ρA m₁ b V := by
    intro b
    have h := stepFrame_small_eq hm a ρA m b V
    simp only [stepFrame, Bool.false_eq_true, if_false, if_true] at h
    simp only [interpolatedFrame, stepFrame, Bool.false_eq_true, if_false, if_true, sub_zero, one_smul,
      zero_smul, add_zero]
    exact h.symm
  unfold interpolatedStepIntegral stepIntegral
  congr 1
  funext w
  simp only [interpolatedStepIntegrand, stepIntegrand, hb]
abbrev _root_.YangMills.SharedProofs.p39075 := @interpolatedStepIntegral_zero_eq
private theorem isOpen_openBallProduct (ρ : ℝ) : IsOpen (openBallProduct F ρ) := by apply _root_.YangMills.Construction.Interpolation.ObservableSizes.isOpen_bondBall <;> assumption
private theorem measurable_indicator_openBallProduct {ρ : ℝ} {g : StepVariable (finiteCells F) → ℝ}
    (hg : ContinuousOn g (openBallProduct F ρ)) : Measurable ((openBallProduct F ρ).indicator g) := by
  classical
  have h := hg.measurable_piecewise (continuousOn_const (c := (0 : ℝ)) (s := (openBallProduct F ρ)ᶜ))
    (isOpen_openBallProduct ρ).measurableSet
  have e : (openBallProduct F ρ).indicator g = (openBallProduct F ρ).piecewise g fun _ => 0 := by
    funext η
    by_cases hη : η ∈ openBallProduct F ρ
    · rw [Set.indicator_of_mem hη, Set.piecewise_eq_of_mem _ _ _ hη]
    · rw [Set.indicator_of_notMem hη, Set.piecewise_eq_of_notMem _ _ _ hη]
  rw [e]
  exact h
abbrev _root_.YangMills.SharedProofs.p50454 := @measurable_indicator_openBallProduct
private theorem abs_indicator_openBallProduct_le {ρ M : ℝ} {g : StepVariable (finiteCells F) → ℝ}
    (hM : 0 ≤ M) (hg : ∀ η ∈ openBallProduct F ρ, |g η| ≤ M) (η : StepVariable (finiteCells F)) :
    |(openBallProduct F ρ).indicator g η| ≤ M := by
  by_cases h : η ∈ openBallProduct F ρ
  · rw [Set.indicator_of_mem h]
    exact hg η h
  · rw [Set.indicator_of_notMem h]
    simpa using hM
abbrev _root_.YangMills.SharedProofs.p22511 := @abs_indicator_openBallProduct_le
private theorem mem_finiteCells (hs : ∀ i, 2 ≤ F.extent i) (z : F.Cell) : z ∈ finiteCells F := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.CellShares.mem_finiteCells <;> assumption
private theorem centredExpansion_add_smul (a ρA : ℝ) (m : ℕ) (φ h : LocalFamily) (θ : ℝ) (y : F.Site F.depth)
    (η : StepVariable (finiteCells F)) (V : F.GaugeField F.top) :
    centredExpansion true a ρA m (φ + θ • h) y η V =
      centredExpansion true a ρA m φ y η V + θ * centredExpansion true a ρA m h y η V := by
  simp only [centredExpansion, subtractTrivial, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring
private theorem stepExponent_add_smul (a ρA x : ℝ) (m : ℕ) (φ h : LocalFamily) (θ : ℝ)
    (V : F.GaugeField F.top) (η : StepVariable (finiteCells F)) :
    stepExponent true a ρA x m (φ + θ • h) 1 V η = stepExponent true a ρA x m φ 1 V η -
      θ * ∑ y ∈ sitesOfCells (finiteCells F) F.depth, centredExpansion true a ρA m h y η V := by
  unfold stepExponent
  simp only [centredExpansion_add_smul, Finset.sum_add_distrib, ← Finset.mul_sum]
  ring
theorem logIntegralAlongSegment (hfix : stepIntegralInFixedVariables)
    (hbirth : LogPartitionTwoSegmentsLocalDecomposition) : logIntegralAlongSegmentStatement := by
  classical
  intro F a ρA ρ x M m m₁ p φ h V hodd hs hm hframe hreg
  have hpos : ∀ i, 0 < F.extent i := fun i => by
    have := hs i
    omega
  have hmem := mem_finiteCells (F := F) hs
  have hframe' : ∀ b ∈ chordBonds (finiteCells F), ‖stepFrame false a ρA m₁ b V‖ + ρ < Real.pi :=
    fun b hb => by rw [stepFrame_small_eq hm a ρA m b V]; exact hframe b hb
  set O := openBallProduct F ρ with hO
  set μ : Measure (StepVariable (finiteCells F)) :=
    volume.withDensity fun η => ENNReal.ofReal (cutoffWeight ρ p η) with hμd
  have hfinite : IsFiniteMeasure μ :=
    isFiniteMeasure_withDensity_ofReal hreg.integrable_cutoffWeight.hasFiniteIntegral
  have hint : ∀ g : StepVariable (finiteCells F) → ℝ,
      ∫ η, g η ∂μ = ∫ η, cutoffWeight ρ p η * g η := by
    intro g
    rw [hμd, integral_withDensity_eq_integral_toReal_smul hreg.measurable_cutoffWeight.ennreal_ofReal
      (ae_of_all _ fun η => ENNReal.ofReal_lt_top)]
    apply integral_congr_ae
    refine Filter.Eventually.of_forall fun η => ?_
    dsimp only
    rw [ENNReal.toReal_ofReal (hreg.cutoffWeight_nonneg η), smul_eq_mul]
  have hμ : μ ≠ 0 := by
    intro h0
    have h1 := hint fun _ => 1
    rw [h0] at h1
    simp only [integral_zero_measure, mul_one] at h1
    have := hreg.integral_cutoffWeight_pos
    linarith
  have hoff : ∀ η, η ∉ O → cutoffWeight ρ p η = 0 := hreg.cutoffWeight_eq_zero_of_not_mem
  set A : StepVariable (finiteCells F) → ℝ := O.indicator (stepExponent true a ρA x m φ 1 V) with hAd
  have hAm : Measurable A := measurable_indicator_openBallProduct hreg.continuousOn_stepExponent
  have hAb : ∀ η, |A η| ≤ M := abs_indicator_openBallProduct_le hreg.bound_nonneg hreg.abs_stepExponent_le
  set N : ℝ := ((finiteCells F).card : ℝ) with hN
  have hcard : 0 < N := by
    rw [hN]
    exact_mod_cast Finset.card_pos.mpr ⟨0, hmem 0⟩
  set ψ : ↥(finiteCells F) → StepVariable (finiteCells F) → ℝ := fun _ η => N⁻¹ * A η with hψ
  set G : ↥(finiteCells F) → StepVariable (finiteCells F) → ℝ := fun Y =>
    O.indicator (fun η => cellCentredExpansion true a ρA m h Y.1 η V) with hG
  have hSψ : ∀ η, ∑ Y, ψ Y η = A η := by
    intro η
    simp only [hψ, Finset.sum_const, Finset.card_univ, Fintype.card_coe, nsmul_eq_mul]
    rw [← hN]
    field_simp
  have hGO : ∀ η ∈ O, ∀ Y, G Y η = cellCentredExpansion true a ρA m h Y.1 η V := fun η hη Y => by
    simp only [hG, Set.indicator_of_mem hη]
  have hS3 : ∀ η ∈ O, ∑ Y, G Y η =
      ∑ y ∈ sitesOfCells (finiteCells F) F.depth, centredExpansion true a ρA m h y η V := by
    intro η hη
    simp only [hGO η hη]
    rw [Finset.sum_coe_sort (finiteCells F) fun Y => cellCentredExpansion true a ρA m h Y η V]
    unfold cellCentredExpansion
    exact Finset.sum_fiberwise_of_maps_to (fun y _ => hmem _) _
  have hψb : ∀ Y η, |ψ Y η| ≤ max M (N⁻¹ * M) := by
    intro Y η
    simp only [hψ, abs_mul, abs_of_pos (inv_pos.mpr hcard)]
    exact le_trans (mul_le_mul_of_nonneg_left (hAb η) (inv_pos.mpr hcard).le) (le_max_right _ _)
  have hGb : ∀ Y η, |G Y η| ≤ max M (N⁻¹ * M) := fun Y η =>
    le_trans (abs_indicator_openBallProduct_le hreg.bound_nonneg (hreg.abs_cellCentredExpansion_le Y.1) η)
      (le_max_left _ _)
  have hb := hbirth _ μ ↥(finiteCells F) ψ ψ G _ hμ (fun Y => hAm.const_mul _) (fun Y => hAm.const_mul _)
    (fun Y => measurable_indicator_openBallProduct (hreg.continuousOn_cellCentredExpansion Y.1)) hψb hψb hGb
  have hexpo : ∀ θ : ℝ, ∀ η ∈ O,
      A η - θ * ∑ Y, G Y η = stepExponent true a ρA x m (φ + θ • h) 1 V η := by
    intro θ η hη
    rw [stepExponent_add_smul, hS3 η hη, hAd, Set.indicator_of_mem hη]
  have hI : ∀ θ : ℝ, ∫ η, Real.exp (-(A η - θ * ∑ Y, G Y η)) ∂μ =
      ∫ η, cutoffWeight ρ p η * Real.exp (- stepExponent true a ρA x m (φ + θ • h) 1 V η) := by
    intro θ
    rw [hint]
    apply integral_congr_ae
    refine Filter.Eventually.of_forall fun η => ?_
    dsimp only
    by_cases hη : η ∈ O
    · rw [hexpo θ η hη]
    · rw [hoff η hη]
      simp
  have hmeanY : ∀ (θ : ℝ) (Y : ↥(finiteCells F)),
      gibbsMean μ (fun ω => ∑ Z, ψ Z ω - θ * ∑ Z, G Z ω) (G Y) =
        conditionalExpansionMean true a ρA ρ x m p (φ + θ • h) h F Y.1 V := by
    intro θ Y
    simp only [gibbsMean, conditionalExpansionMean, cutoffMean, hSψ]
    rw [hI θ, hint]
    congr 1
    apply integral_congr_ae
    refine Filter.Eventually.of_forall fun η => ?_
    dsimp only
    by_cases hη : η ∈ O
    · rw [hGO η hη Y, hexpo θ η hη]
      ring
    · rw [hoff η hη]
      simp
  have hzero : ∀ Y : ↥(finiteCells F), (∫ τ in (0 : ℝ)..1, gibbsMean μ
      (fun ω => τ * ∑ Z, ψ Z ω + (1 - τ) * ∑ Z, ψ Z ω) (fun ω => ψ Y ω - ψ Y ω)) = 0 := by
    intro Y
    simp [gibbsMean]
  simp only [hzero, neg_zero, zero_add, hmeanY] at hb
  rw [Finset.sum_coe_sort (finiteCells F) fun Y =>
    ∫ θ in (0 : ℝ)..1, conditionalExpansionMean true a ρA ρ x m p (φ + θ • h) h F Y V] at hb
  simp only [hSψ] at hb
  have e1 : ∫ η, Real.exp (-(A η - ∑ Z, G Z η)) ∂μ =
      ∫ η, cutoffWeight ρ p η * Real.exp (- stepExponent true a ρA x m (φ + (1 : ℝ) • h) 1 V η) := by
    have := hI 1
    simpa only [one_mul] using this
  have e2 : ∫ η, Real.exp (- A η) ∂μ =
      ∫ η, cutoffWeight ρ p η * Real.exp (- stepExponent true a ρA x m φ 1 V η) := by
    rw [hint]
    apply integral_congr_ae
    refine Filter.Eventually.of_forall fun η => ?_
    dsimp only
    by_cases hη : η ∈ O
    · rw [hAd, Set.indicator_of_mem hη]
    · rw [hoff η hη]
      simp
  rw [e1, e2] at hb
  have hneZ : NeZero μ := ⟨hμ⟩
  have hexpint : ∀ B : StepVariable (finiteCells F) → ℝ, Measurable B →
      (∀ η, |B η| ≤ (N + 1) * max M (N⁻¹ * M) + M) → 0 < ∫ η, Real.exp (- B η) ∂μ := by
    intro B hB hBb
    apply integral_exp_pos
    refine Integrable.of_bound hB.neg.exp.aestronglyMeasurable
      (Real.exp ((N + 1) * max M (N⁻¹ * M) + M)) (Filter.Eventually.of_forall fun η => ?_)
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    apply Real.exp_le_exp.mpr
    have := abs_le.mp (hBb η)
    linarith [this.1]
  have hmax0 : 0 ≤ max M (N⁻¹ * M) := le_trans hreg.bound_nonneg (le_max_left _ _)
  have hp0 : 0 < ∫ η, cutoffWeight ρ p η * Real.exp (- stepExponent true a ρA x m φ 1 V η) := by
    rw [← e2]
    refine hexpint A hAm fun η => (hAb η).trans ?_
    have : 0 ≤ (N + 1) * max M (N⁻¹ * M) := by positivity
    linarith
  have hGsum : ∀ η, |∑ Z, G Z η| ≤ N * max M (N⁻¹ * M) := by
    intro η
    calc |∑ Z, G Z η| ≤ ∑ Z, |G Z η| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _Z : ↥(finiteCells F), max M (N⁻¹ * M) := Finset.sum_le_sum fun Z _ => hGb Z η
      _ = _ := by simp [hN]
  have hp1 : 0 < ∫ η, cutoffWeight ρ p η *
      Real.exp (- stepExponent true a ρA x m (φ + (1 : ℝ) • h) 1 V η) := by
    rw [← e1]
    have hm' : Measurable fun η => A η - ∑ Z, G Z η :=
      hAm.sub (Finset.measurable_fun_sum _ fun Y _ =>
        measurable_indicator_openBallProduct (hreg.continuousOn_cellCentredExpansion Y.1))
    have := hexpint (fun η => A η - ∑ Z, G Z η) hm' (fun η => by
      have a1 := abs_le.mp (hAb η)
      have a2 := abs_le.mp (hGsum η)
      refine abs_le.mpr ⟨?_, ?_⟩ <;> nlinarith [a1.1, a1.2, a2.1, a2.2])
    exact this
  have hK : ∀ f : LocalFamily, interpolatedStepIntegral 0 a ρA ρ x m p f V =
      (Real.exp (∑ _c ∈ innerBonds (finiteCells F) F.top, haarGap (a * x)) *
        (∏ _b : ↥(chordBonds (finiteCells F)), haarRadialDensity 0) *
        Real.exp (- x * chartedEnergy a (coordsAboveFrame false a ρA m₁ V 0) V)) *
      ∫ η, cutoffWeight ρ p η * Real.exp (- stepExponent true a ρA x m f 1 V η) := by
    intro f
    rw [interpolatedStepIntegral_zero_eq hm, hfix F a ρA ρ x m₁ p f V hodd hpos hframe']
    simp only [stepExponent_small_eq hm a ρA x m f 1 V]
  have hJ : 0 < ∏ _b : ↥(chordBonds (finiteCells F)), haarRadialDensity 0 := by
    apply Finset.prod_pos
    intro b _
    unfold haarRadialDensity
    rw [if_pos Real.pi_pos]
    simp only [Real.sinc_zero]
    have := Real.pi_pos
    positivity
  have e3 : φ + h = φ + (1 : ℝ) • h := by rw [one_smul]
  rw [e3, hK, hK, Real.log_mul (by positivity) hp1.ne', Real.log_mul (by positivity) hp0.ne']
  linarith
end YangMills.Construction.Interpolation
end
