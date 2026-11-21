import YangMills.Construction.ColdStepAtMirrorFrames.TermsInFixedVariables
import YangMills.Construction.ResponseInTheExpansion.GapLessCostIsASlopeProof
import YangMills.Construction.ResponseInTheExpansion.TotalOfThePartsProof
import YangMills.Construction.SummableBoundsOfTheFlow.MeanAlongAFieldInALaw
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped RealInnerProductSpace Quaternion
open MeasureTheory
namespace YangMills.Construction
open BlockAverages ColdStepAtMirrorFrames Interpolation BondIntegration ConvexObservables Estimates
namespace WeightedResponses
section Law
variable {ι : Type} [Fintype ι] [DecidableEq ι]
omit [DecidableEq ι] in
private theorem integrable_of_continuousAt_closedBalls {ρ : ℝ} {μ : Measure (BondField ι)} [IsFiniteMeasure μ]
    (hμ : ∀ᵐ η ∂μ, ∀ b, ‖η b‖ < ρ) {G : BondField ι → ℝ}
    (hG : ∀ η : BondField ι, (∀ b, ‖η b‖ ≤ ρ) → ContinuousAt G η) : Integrable G μ := by
  set CB : Set (BondField ι) := Set.pi Set.univ fun _ => Metric.closedBall 0 ρ with hCB
  have hmem : ∀ η, η ∈ CB ↔ ∀ b, ‖η b‖ ≤ ρ := fun η => by simp [hCB, Set.mem_pi]
  have hcomp : IsCompact CB := isCompact_univ_pi fun _ => isCompact_closedBall 0 ρ
  have hcont : ContinuousOn G CB := fun η h => (hG η ((hmem η).1 h)).continuousWithinAt
  have hon : IntegrableOn G CB μ := hcont.integrableOn_compact hcomp
  have hr : μ.restrict CB = μ := by
    apply Measure.restrict_eq_self_of_ae_mem
    filter_upwards [hμ] with η hη
    exact (hmem η).2 fun b => (hη b).le
  rwa [IntegrableOn, hr] at hon
private theorem continuousAt_bondPartialDeriv_diag {G : BondField ι → ℝ} {η : BondField ι} (hG : ContDiffAt ℝ 1 G η) (b : ι) :
    ContinuousAt (fun ζ : BondField ι => bondPartialDeriv G b ζ (ζ b)) η := by
  have h1 : ContinuousAt (fderiv ℝ G) η := (hG.fderiv_right (m := 0) (by simp)).continuousAt
  have h2 : Continuous fun ζ : BondField ι => bondVariation b (ζ b) :=
    (ContinuousLinearMap.single ℝ (fun _ : ι => BondVector) b).continuous.comp (continuous_apply b)
  exact h1.clm_apply h2.continuousAt
private theorem exists_truncated_identity_field {ρ : ℝ} (hρ : 0 < ρ) : ∃ (z : BondVector → BondVector) (C : ℝ), ContDiff ℝ 1 z ∧
    (∀ v, ‖z v‖ ≤ C) ∧ (∀ v, ‖fderiv ℝ z v‖ ≤ C) ∧ (∀ v, ‖v‖ < ρ → z v = v) ∧
    (∀ v, ‖v‖ < ρ → bondDivergence z v = 3) := by
  let c : ContDiffBump (0 : BondVector) := ⟨ρ, 2 * ρ, hρ, by linarith⟩
  let z : BondVector → BondVector := fun v => c v • v
  have hz : ContDiff ℝ 1 z := (c.contDiff (n := 1)).smul contDiff_id
  have hsupp : HasCompactSupport z := c.hasCompactSupport.smul_right
  have hfd : Continuous (fderiv ℝ z) := hz.continuous_fderiv (by simp)
  obtain ⟨C₁, hC₁⟩ := hfd.bounded_above_of_compact_support (hsupp.fderiv (𝕜 := ℝ))
  have hid : ∀ v : BondVector, ‖v‖ < ρ → z v = v := fun v hv => by
    have : c v = 1 := c.one_of_mem_closedBall (by simpa using hv.le)
    simp [z, this]
  refine ⟨z, max (2 * ρ) C₁, hz, fun v => ?_, fun v => (hC₁ v).trans (le_max_right _ _), hid, fun v hv => ?_⟩
  · refine le_trans ?_ (le_max_left _ _)
    by_cases h : ‖v‖ < 2 * ρ
    · have h1 : |c v| ≤ 1 := by rw [abs_of_nonneg c.nonneg]; exact c.le_one
      calc ‖z v‖ = |c v| * ‖v‖ := by simp [z, norm_smul]
        _ ≤ 1 * ‖v‖ := by gcongr
        _ ≤ 2 * ρ := by linarith
    · have h0 : c v = 0 := c.zero_of_le_dist (by simpa [dist_eq_norm] using not_lt.1 h)
      simp [z, h0]; positivity
  · have hev : z =ᶠ[nhds v] id := by
      filter_upwards [(isOpen_lt continuous_norm continuous_const).mem_nhds hv] with w hw using hid w hw
    have hf : fderiv ℝ z v = ContinuousLinearMap.id ℝ BondVector := by
      rw [hev.fderiv_eq]; exact fderiv_id
    unfold bondDivergence
    simp [hf]
private theorem cutoffTerm_integrable (hP : cutoffDerivBoundsStatement) (hL : normalizedBallLawIsProbabilityStatement) {ρ : ℝ}
    {p : ℝ → ℝ} {Ψ : BondField ι → ℝ} (hρ : 0 < ρ) (hp : IsCutoff ρ p) (hΨ : Continuous Ψ) (b : ι) :
    Integrable (fun η : BondField ι => ‖η b‖ * deriv p ‖η b‖) (normalizedBallLaw (cutoffFactor ρ p) Ψ) := by
  obtain ⟨-, -, hiff, -, hmeas, hnn, -, -, -, hnz, hanti⟩ := hL ι ρ p Ψ hρ hp hΨ
  rw [hiff]
  obtain ⟨hd0, -, hpow, -⟩ := hP ρ p hρ hp
  obtain ⟨C, hC0, hC⟩ := hpow 1
  set CB : Set (BondField ι) := Set.pi Set.univ fun _ => Metric.closedBall 0 ρ with hCB
  have hmem : ∀ η, η ∈ CB ↔ ∀ b, ‖η b‖ ≤ ρ := fun η => by simp [hCB, Set.mem_pi]
  have hcomp : IsCompact CB := isCompact_univ_pi fun _ => isCompact_closedBall 0 ρ
  have hexp : Continuous fun η => Real.exp (- Ψ η) := (hΨ.neg).rexp
  obtain ⟨M, hM⟩ := hcomp.exists_bound_of_continuousOn hexp.continuousOn
  have hM0 : 0 ≤ M := by
    have h0 : (0 : BondField ι) ∈ CB := (hmem 0).2 fun b => by simpa using hρ.le
    exact (norm_nonneg _).trans (hM 0 h0)
  have hcut1 : ∀ u : ℝ, 0 ≤ u → cutoffFactor ρ p u ≤ 1 := fun u hu => by
    have h1 := hanti 0 u le_rfl hu
    have h2 : cutoffFactor ρ p 0 = 1 := by
      unfold cutoffFactor
      rw [if_pos hρ, hp.vanish_small 0 le_rfl (by positivity)]
      simp
    linarith
  have hcut0 : ∀ u : ℝ, 0 ≤ cutoffFactor ρ p u := fun u => by
    unfold cutoffFactor
    split_ifs
    · exact (Real.exp_pos _).le
    · exact le_rfl
  have hdom : IntegrableOn (fun _ : BondField ι => ρ * C * M) CB :=
    integrableOn_const hcomp.measure_lt_top.ne
  have hCBm : MeasurableSet CB := hcomp.isClosed.measurableSet
  refine (hdom.integrable_indicator hCBm).mono' ?_ (Filter.Eventually.of_forall fun η => ?_)
  · refine Measurable.aestronglyMeasurable ?_
    have h1 : Measurable fun η : BondField ι => ‖η b‖ := (measurable_pi_apply b).norm
    exact (h1.mul ((measurable_deriv p).comp h1)).mul hmeas
  · by_cases hin : ∀ b, ‖η b‖ < ρ
    · have hmemη : η ∈ CB := (hmem η).2 fun b => (hin b).le
      rw [Set.indicator_of_mem hmemη]
      set u := ‖η b‖ with hu
      have hu0 : 0 ≤ u := norm_nonneg _
      have hD : ballDensity (cutoffFactor ρ p) Ψ η =
          cutoffFactor ρ p u * ((∏ b' ∈ Finset.univ.erase b, cutoffFactor ρ p ‖η b'‖) * Real.exp (- Ψ η)) := by
        unfold ballDensity radialWeightProd
        rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ b)]
        ring
      have hR0 : 0 ≤ ∏ b' ∈ Finset.univ.erase b, cutoffFactor ρ p ‖η b'‖ := Finset.prod_nonneg fun _ _ => hcut0 _
      have hR1 : ∏ b' ∈ Finset.univ.erase b, cutoffFactor ρ p ‖η b'‖ ≤ 1 :=
        Finset.prod_le_one (fun _ _ => hcut0 _) fun _ _ => hcut1 _ (norm_nonneg _)
      have hE : Real.exp (- Ψ η) ≤ M := by
        have := hM η hmemη
        rwa [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] at this
      rcases hu0.eq_or_lt with h0 | h0
      · rw [← h0]
        simp
        positivity
      · have hp1 : 0 ≤ deriv p u := hd0 u h0 (hin b)
        have hcf : cutoffFactor ρ p u = Real.exp (- p u) := by
          unfold cutoffFactor; rw [if_pos (hin b)]
        have hb1 : deriv p u * cutoffFactor ρ p u ≤ C := by
          have h3 := hC u h0 (hin b)
          rw [pow_one] at h3
          rw [hcf]
          nlinarith [Real.exp_pos (- p u)]
        have hb0 : 0 ≤ deriv p u * cutoffFactor ρ p u := mul_nonneg hp1 (hcut0 _)
        have hRE : (∏ b' ∈ Finset.univ.erase b, cutoffFactor ρ p ‖η b'‖) * Real.exp (- Ψ η) ≤ M := by
          calc _ ≤ 1 * Real.exp (- Ψ η) := by gcongr
            _ ≤ M := by simpa using hE
        have hRE0 : 0 ≤ (∏ b' ∈ Finset.univ.erase b, cutoffFactor ρ p ‖η b'‖) * Real.exp (- Ψ η) :=
          mul_nonneg hR0 (Real.exp_pos _).le
        rw [hD]
        have heq : u * deriv p u * (cutoffFactor ρ p u * ((∏ b' ∈ Finset.univ.erase b, cutoffFactor ρ p ‖η b'‖) * Real.exp (- Ψ η))) =
            u * (deriv p u * cutoffFactor ρ p u) * ((∏ b' ∈ Finset.univ.erase b, cutoffFactor ρ p ‖η b'‖) * Real.exp (- Ψ η)) := by ring
        have hub : u ≤ ρ := (hin b).le
        have hfin : u * (deriv p u * cutoffFactor ρ p u) * ((∏ b' ∈ Finset.univ.erase b, cutoffFactor ρ p ‖η b'‖) * Real.exp (- Ψ η)) ≤
            ρ * C * M :=
          mul_le_mul (mul_le_mul hub hb1 hb0 hρ.le) hRE hRE0 (mul_nonneg hρ.le hC0)
        rw [heq, Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (mul_nonneg hu0 hb0) hRE0)]
        exact hfin
    · have hz : ballDensity (cutoffFactor ρ p) Ψ η = 0 := by
        by_contra hne
        exact hin ((hnz η).1 hne)
      rw [hz]
      simp only [mul_zero, norm_zero]
      apply Set.indicator_nonneg
      intro _ _
      have h0 : (0 : BondField ι) ∈ CB := (hmem 0).2 fun b => by simpa using hρ.le
      positivity
private theorem integral_dilation_score_eq_zero (hM : integrationByPartsAlongFieldStatement) (hP : cutoffDerivBoundsStatement)
    (hL : normalizedBallLawIsProbabilityStatement) {ρ : ℝ} {p : ℝ → ℝ} {Ψ : BondField ι → ℝ} (hρ : 0 < ρ) (hp : IsCutoff ρ p)
    (hΨ : ContDiff ℝ 1 Ψ) (b : ι) :
    Integrable (fun η : BondField ι => bondPartialDeriv Ψ b η (η b) + ‖η b‖ * deriv p ‖η b‖ - 3)
        (normalizedBallLaw (cutoffFactor ρ p) Ψ) ∧
      ∫ η, (bondPartialDeriv Ψ b η (η b) + ‖η b‖ * deriv p ‖η b‖ - 3) ∂(normalizedBallLaw (cutoffFactor ρ p) Ψ) = 0 := by
  have hc := hΨ.continuous
  obtain ⟨hprob, hmean, hiff, hae, -, -, -, -, -, hnz, -⟩ := hL ι ρ p Ψ hρ hp hc
  have hI1 : Integrable (fun η : BondField ι => bondPartialDeriv Ψ b η (η b)) (normalizedBallLaw (cutoffFactor ρ p) Ψ) :=
    integrable_of_continuousAt_closedBalls hae fun η _ => continuousAt_bondPartialDeriv_diag hΨ.contDiffAt b
  have hI2 := cutoffTerm_integrable hP hL hρ hp hc b
  have hI : Integrable (fun η : BondField ι => bondPartialDeriv Ψ b η (η b) + ‖η b‖ * deriv p ‖η b‖ - 3)
      (normalizedBallLaw (cutoffFactor ρ p) Ψ) := (hI1.add hI2).sub (integrable_const _)
  refine ⟨hI, ?_⟩
  obtain ⟨z, C, hz, hzb, hzd, hzid, hzdiv⟩ := exists_truncated_identity_field hρ
  have hrim : ∀ v : BondVector, ‖v‖ < ρ → radialCutoffSlope p v (z v) = ‖v‖ * deriv p ‖v‖ := fun v hv => by
    unfold radialCutoffSlope
    rw [hzid v hv, real_inner_self_eq_norm_sq]
    by_cases h0 : ‖v‖ = 0
    · simp [h0]
    · field_simp
  have hoff : ∀ η : BondField ι, ¬ (∀ b, ‖η b‖ < ρ) → ballDensity (cutoffFactor ρ p) Ψ η = 0 := fun η h => by
    by_contra hne
    exact h ((hnz η).1 hne)
  have hsc : ∀ η : BondField ι, (1 : ℝ) * fieldScore p Ψ b z η * ballDensity (cutoffFactor ρ p) Ψ η =
      (bondPartialDeriv Ψ b η (η b) + ‖η b‖ * deriv p ‖η b‖ - 3) * ballDensity (cutoffFactor ρ p) Ψ η := fun η => by
    by_cases hin : ∀ b, ‖η b‖ < ρ
    · unfold fieldScore
      rw [hzdiv _ (hin b), hrim _ (hin b), hzid _ (hin b)]
      ring
    · rw [hoff η hin]; simp
  have hrs : ∀ η : BondField ι, (1 : ℝ) * radialCutoffSlope p (η b) (z (η b)) * ballDensity (cutoffFactor ρ p) Ψ η =
      ‖η b‖ * deriv p ‖η b‖ * ballDensity (cutoffFactor ρ p) Ψ η := fun η => by
    by_cases hin : ∀ b, ‖η b‖ < ρ
    · rw [hrim _ (hin b)]; ring
    · rw [hoff η hin]; simp
  have hal : ∀ η : BondField ι, fieldDerivative b z (fun _ => (1 : ℝ)) η * ballDensity (cutoffFactor ρ p) Ψ η = 0 := fun η => by
    simp [fieldDerivative, bondPartialDeriv]
  have hmain := hM ι ρ p Ψ (fun _ => 1) b z C hρ hp hΨ contDiffOn_const hz hzb hzd
    (by simp only [hal]; exact integrable_zero _ _ _)
    (by simp only [hsc]; exact (hiff _).1 hI)
    (by simp only [hrs]; exact (hiff _).1 hI2)
  simp only [hal, hsc, integral_zero] at hmain
  rw [hmean]
  unfold ballExpectation
  rw [← hmain, zero_div]
end Law
section Field
variable {F : BlockFrame}
private theorem mem_finiteCells_of_site {j : ℕ} {y : F.Site j} (h : y ∈ sitesOfCells (finiteCells F) j) (Y : F.Cell) :
    Y ∈ finiteCells F := by apply _root_.YangMills.Construction.ResponseInTheExpansion.SumOfTerms.mem_finiteCells_of_mem_sites <;> assumption
private theorem mem_finiteCells_of_bond {j : ℕ} {b : F.Site j × Fin 4} (h : b ∈ innerBonds (finiteCells F) j) (Y : F.Cell) :
    Y ∈ finiteCells F := mem_finiteCells_of_site (Finset.mem_product.1 (Finset.filter_subset _ _ h)).1 Y
private theorem mem_finiteCells_of_chord {b : F.Site F.depth × Fin 4} (h : b ∈ chordBonds (finiteCells F)) (Y : F.Cell) :
    Y ∈ finiteCells F := by apply _root_.YangMills.Construction.ResponseInTheExpansion.SumOfTerms.mem_finiteCells_of_mem_chord <;> assumption
private theorem sum_sumOverBlock (u : ↥(chordBonds (finiteCells F)) → ℝ) :
    ∑ Y ∈ finiteCells F, ColdHalfLaw.sumOverBlock Y u = ∑ b, u b := by
  classical
  unfold ColdHalfLaw.sumOverBlock
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Finset.sum_ite_eq, if_pos (mem_finiteCells_of_chord b.2 _)]
private theorem contDiffAt_of_jointDisplacement (G : StepVariable (finiteCells F) → F.GaugeField F.top → ℝ) (V : F.GaugeField F.top)
    (η : StepVariable (finiteCells F))
    (h : ∀ (l : ℕ) (b : Fin l → ↥(chordBonds (finiteCells F))) (u : Fin l → EuclideanSpace ℝ (Fin 3)), 2 ≤ l →
      (∀ i, ‖u i‖ = 1) → ContDiffAt ℝ ((l + 0 : ℕ)) (jointDisplacement (j := 0) G η V b u Fin.elim0 Fin.elim0) 0) :
    ContDiffAt ℝ 1 (fun ζ => G ζ V) η := by apply _root_.YangMills.SharedProofs.p65438 <;> assumption
end Field
section Slope
variable {F : BlockFrame}
private theorem bondPartialDeriv_eq_chartedSlope (Q : ColdHalfLaw) (V : F.GaugeField F.top) (η : StepVariable (finiteCells F))
    (hS : DifferentiableAt ℝ (fun ζ => Q.totalCost ζ V) η) (b : ↥(chordBonds (finiteCells F)))
    (e : EuclideanSpace ℝ (Fin 3)) :
    bondPartialDeriv (fun ζ => Q.totalCost ζ V) b η e =
      chartedSlope Q.a (interpolatedCoords 1 Q.a Q.chartRadius Q.mirrorRadius V η) V b.1 (toImaginary e) := by apply _root_.YangMills.SharedProofs.p18260 <;> assumption
private theorem linearBlockPart_eq (Q : ColdHalfLaw) (Y : F.Cell) (ζ : StepVariable (finiteCells F)) (V : F.GaugeField F.top) :
    Q.linearBlockPart Y ζ V = interpolatedBlockExponent 1 Q.a Q.chartRadius Q.coupling Q.mirrorRadius Y V ζ +
      (∑ c ∈ (innerBonds (finiteCells F) F.top).filter (fun c => c.1 = Y),
        haarGapExcess Q.a Q.coupling (interpolatedField 1 Q.a Q.chartRadius Q.mirrorRadius V ζ) c) +
      ColdHalfLaw.sumOverBlock Y (fun b => haarLogRatio (interpolatedCoords 1 Q.a Q.chartRadius Q.mirrorRadius V ζ b.1.1 b.1.2)) := by
  unfold ColdHalfLaw.linearBlockPart interpolatedBlockExponent ColdHalfLaw.sumOverBlock
  ring
private theorem slopeTerm_eq (Q : ColdHalfLaw) (Y : F.Cell) (η : StepVariable (finiteCells F)) (V : F.GaugeField F.top) :
    Q.slopeTerm Y η V = Q.coupling * ColdHalfLaw.sumOverBlock Y (fun b =>
        chartedSlope Q.a (interpolatedCoords 1 Q.a Q.chartRadius Q.mirrorRadius V η) V b.1 (toImaginary (η b))) -
      2 * Q.linearBlockPart Y η V := by apply _root_.YangMills.SharedProofs.p90711 <;> assumption
end Slope
section Identity
variable {F : BlockFrame}
private def slopeAlong (Q : ColdHalfLaw) (V : F.GaugeField F.top) (b : ↥(chordBonds (finiteCells F)))
    (η : StepVariable (finiteCells F)) : ℝ :=
  chartedSlope Q.a (interpolatedCoords 1 Q.a Q.chartRadius Q.mirrorRadius V η) V b.1 (toImaginary (η b))
private theorem exponent_eq_sub (Q : ColdHalfLaw) (V : F.GaugeField F.top) (η : StepVariable (finiteCells F)) :
    Q.exponent V η = Q.coupling * (Q.totalCost η V - Q.totalCost 0 V) - Q.gapHaarExcess η V -
      ∑ y ∈ sitesOfCells (finiteCells F) F.depth, interpolatedExpansion 1 Q.a Q.chartRadius Q.mirrorRadius Q.family y η V := by
  simp only [ColdHalfLaw.exponent, familyLawExponent, interpolatedExponent, ColdHalfLaw.totalCost, ColdHalfLaw.gapHaarExcess]
  ring
private theorem isOpen_forall_norm_lt (ρ : ℝ) : IsOpen {η : StepVariable (finiteCells F) | ∀ b, ‖η b‖ < ρ} := by apply _root_.YangMills.Construction.Interpolation.ObservableSizes.isOpen_bondBall <;> assumption
private theorem bondPartialDeriv_exponent (Q : ColdHalfLaw) (V : F.GaugeField F.top) (Ψ' : StepVariable (finiteCells F) → ℝ)
    (hagree : ∀ η : StepVariable (finiteCells F), (∀ b, ‖η b‖ < Q.ballRadius) → Ψ' η = Q.exponent V η)
    (η : StepVariable (finiteCells F)) (hη : ∀ b, ‖η b‖ < Q.ballRadius)
    (hS : DifferentiableAt ℝ (fun ζ => Q.totalCost ζ V) η) (hJ : DifferentiableAt ℝ (fun ζ => Q.gapHaarExcess ζ V) η)
    (hR : ∀ y, DifferentiableAt ℝ (fun ζ => interpolatedExpansion 1 Q.a Q.chartRadius Q.mirrorRadius Q.family y ζ V) η)
    (b : ↥(chordBonds (finiteCells F))) :
    bondPartialDeriv Ψ' b η (η b) = Q.coupling * slopeAlong Q V b η - bondPartialDeriv (fun ζ => Q.gapHaarExcess ζ V) b η (η b) -
      ∑ y ∈ sitesOfCells (finiteCells F) F.depth,
        bondPartialDeriv (fun ζ => interpolatedExpansion 1 Q.a Q.chartRadius Q.mirrorRadius Q.family y ζ V) b η (η b) := by
  have hev : Ψ' =ᶠ[nhds η] fun ζ => Q.coupling * (Q.totalCost ζ V - Q.totalCost 0 V) - Q.gapHaarExcess ζ V -
      ∑ y ∈ sitesOfCells (finiteCells F) F.depth, interpolatedExpansion 1 Q.a Q.chartRadius Q.mirrorRadius Q.family y ζ V := by
    filter_upwards [(isOpen_forall_norm_lt Q.ballRadius).mem_nhds hη] with ζ hζ
    rw [hagree ζ hζ, exponent_eq_sub]
  have hd := (((hS.hasFDerivAt.sub_const (Q.totalCost 0 V)).const_mul Q.coupling).sub hJ.hasFDerivAt).sub
    (HasFDerivAt.fun_sum (u := sitesOfCells (finiteCells F) F.depth) fun y _ => (hR y).hasFDerivAt)
  have hd' : HasFDerivAt (fun ζ => Q.coupling * (Q.totalCost ζ V - Q.totalCost 0 V) - Q.gapHaarExcess ζ V -
      ∑ y ∈ sitesOfCells (finiteCells F) F.depth, interpolatedExpansion 1 Q.a Q.chartRadius Q.mirrorRadius Q.family y ζ V) _ η := hd
  have hs := bondPartialDeriv_eq_chartedSlope Q V η hS b (η b)
  unfold bondPartialDeriv at *
  rw [hev.fderiv_eq, hd'.fderiv]
  simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply, ContinuousLinearMap.sum_apply, hs, smul_eq_mul,
    slopeAlong]
private theorem dilationIdentity_of_smooth (hM : integrationByPartsAlongFieldStatement) (hP : cutoffDerivBoundsStatement)
    (hL : normalizedBallLawIsProbabilityStatement) (Q : ColdHalfLaw) (V : F.GaugeField F.top) (hx : 0 < Q.coupling)
    (hρ : 0 < Q.ballRadius) (hcut : IsCutoff Q.ballRadius Q.cutoff)
    (hS : ∀ η : StepVariable (finiteCells F), (∀ b, ‖η b‖ ≤ Q.ballRadius) → ContDiffAt ℝ 1 (fun ζ => Q.totalCost ζ V) η)
    (hgap : ∀ (c : F.Site F.top × Fin 4) (η : StepVariable (finiteCells F)), (∀ b, ‖η b‖ ≤ Q.ballRadius) →
      ContDiffAt ℝ 1 (fun ζ => haarGapExcess Q.a Q.coupling (interpolatedField 1 Q.a Q.chartRadius Q.mirrorRadius V ζ) c) η)
    (hhaar : ∀ (b₀ : ↥(chordBonds (finiteCells F))) (η : StepVariable (finiteCells F)), (∀ b, ‖η b‖ ≤ Q.ballRadius) →
      ContDiffAt ℝ 1 (fun ζ => haarLogRatio (interpolatedCoords 1 Q.a Q.chartRadius Q.mirrorRadius V ζ b₀.1.1 b₀.1.2)) η)
    (hR : ∀ (y : F.Site F.depth) (η : StepVariable (finiteCells F)), (∀ b, ‖η b‖ ≤ Q.ballRadius) →
      ContDiffAt ℝ 1 (fun ζ => interpolatedExpansion 1 Q.a Q.chartRadius Q.mirrorRadius Q.family y ζ V) η)
    (hblock : ∀ (Y : F.Cell) (η : StepVariable (finiteCells F)), (∀ b, ‖η b‖ ≤ Q.ballRadius) →
      ContinuousAt (fun ζ => interpolatedBlockExponent 1 Q.a Q.chartRadius Q.coupling Q.mirrorRadius Y V ζ) η)
    (hsum0 : ∀ η : StepVariable (finiteCells F), (∀ b, ‖η b‖ < Q.ballRadius) →
      interpolatedExponent 1 Q.a Q.chartRadius Q.coupling Q.mirrorRadius V η =
        ∑ Y ∈ finiteCells F, interpolatedBlockExponent 1 Q.a Q.chartRadius Q.coupling Q.mirrorRadius Y V η)
    (Ψ' : StepVariable (finiteCells F) → ℝ) (hΨ' : ContDiff ℝ 1 Ψ')
    (hagree : ∀ η : StepVariable (finiteCells F), (∀ b, ‖η b‖ < Q.ballRadius) → Ψ' η = Q.exponent V η) :
    Q.coupling * Q.expectation V (fun η => Q.totalCost η V - Q.totalCost 0 V) =
      3 / 2 * ((chordBonds (finiteCells F)).card : ℝ) + Q.coupling * ∑ Y ∈ finiteCells F, Q.dilationRemainder Y V := by
  have hJ : ∀ η : StepVariable (finiteCells F), (∀ b, ‖η b‖ ≤ Q.ballRadius) →
      ContDiffAt ℝ 1 (fun ζ => Q.gapHaarExcess ζ V) η :=
    fun η hη => (ContDiffAt.sum fun c _ => hgap c η hη).add (ContDiffAt.sum fun b _ => hhaar b η hη)
  have hover : ∀ (Y : F.Cell) (u : ↥(chordBonds (finiteCells F)) → StepVariable (finiteCells F) → ℝ)
      (η : StepVariable (finiteCells F)), (∀ b, ContinuousAt (u b) η) →
      ContinuousAt (fun ζ => ColdHalfLaw.sumOverBlock Y fun b => u b ζ) η := fun Y u η hu => by
    unfold ColdHalfLaw.sumOverBlock
    refine tendsto_finsetSum _ fun b _ => ?_
    by_cases h : enclosingCell b.1.1 = Y
    · simp only [if_pos h]
      exact hu b
    · simp only [if_neg h]
      exact tendsto_const_nhds
  have hB : ∀ (Y : F.Cell) (η : StepVariable (finiteCells F)), (∀ b, ‖η b‖ ≤ Q.ballRadius) →
      ContinuousAt (fun ζ => Q.linearBlockPart Y ζ V) η := fun Y η hη => by
    have h2 : ContinuousAt (fun ζ => ∑ c ∈ (innerBonds (finiteCells F) F.top).filter (fun c => c.1 = Y),
        haarGapExcess Q.a Q.coupling (interpolatedField 1 Q.a Q.chartRadius Q.mirrorRadius V ζ) c) η :=
      (ContDiffAt.sum fun c _ => hgap c η hη).continuousAt
    have h3 := hover Y (fun b ζ => haarLogRatio (interpolatedCoords 1 Q.a Q.chartRadius Q.mirrorRadius V ζ b.1.1 b.1.2)) η
      fun b => (hhaar b η hη).continuousAt
    have he : (fun ζ => Q.linearBlockPart Y ζ V) = fun ζ =>
        interpolatedBlockExponent 1 Q.a Q.chartRadius Q.coupling Q.mirrorRadius Y V ζ +
        (∑ c ∈ (innerBonds (finiteCells F) F.top).filter (fun c => c.1 = Y),
          haarGapExcess Q.a Q.coupling (interpolatedField 1 Q.a Q.chartRadius Q.mirrorRadius V ζ) c) +
        ColdHalfLaw.sumOverBlock Y (fun b => haarLogRatio (interpolatedCoords 1 Q.a Q.chartRadius Q.mirrorRadius V ζ b.1.1 b.1.2)) :=
      funext fun ζ => linearBlockPart_eq Q Y ζ V
    rw [he]
    exact ((hblock Y η hη).add h2).add h3
  have hsum : ∀ η : StepVariable (finiteCells F), (∀ b, ‖η b‖ < Q.ballRadius) →
      ∑ Y ∈ finiteCells F, Q.linearBlockPart Y η V = Q.coupling * (Q.totalCost η V - Q.totalCost 0 V) := fun η hη => by
    classical
    simp only [linearBlockPart_eq, Finset.sum_add_distrib]
    rw [← hsum0 η hη, sum_sumOverBlock, Finset.sum_fiberwise_of_maps_to (fun c hc => mem_finiteCells_of_bond hc _)]
    simp only [interpolatedExponent, ColdHalfLaw.totalCost]
    ring
  have hc := hΨ'.continuous
  obtain ⟨hprob, hmean, -, hae, -, -, -, -, -, -, -⟩ := hL _ Q.ballRadius Q.cutoff Ψ' hρ hcut hc
  have hdens : ballDensity Q.radialWeight (Q.exponent V) = ballDensity (cutoffFactor Q.ballRadius Q.cutoff) Ψ' := by
    funext η
    by_cases hin : ∀ b, ‖η b‖ < Q.ballRadius
    · unfold ballDensity
      rw [hagree η hin]
      rfl
    · push Not at hin
      obtain ⟨b, hb⟩ := hin
      have h0 : ∏ b', cutoffFactor Q.ballRadius Q.cutoff ‖η b'‖ = 0 :=
        Finset.prod_eq_zero (Finset.mem_univ b) (by unfold cutoffFactor; rw [if_neg (not_lt.2 hb)])
      show (∏ b', cutoffFactor Q.ballRadius Q.cutoff ‖η b'‖) * _ = (∏ b', cutoffFactor Q.ballRadius Q.cutoff ‖η b'‖) * _
      rw [h0, zero_mul, zero_mul]
  have hQm : ∀ H : StepVariable (finiteCells F) → ℝ,
      Q.expectation V H = ∫ η, H η ∂normalizedBallLaw (cutoffFactor Q.ballRadius Q.cutoff) Ψ' := fun H => by
    rw [hmean]
    show ballExpectation Q.radialWeight (Q.exponent V) H = _
    unfold ballExpectation
    rw [hdens]
  have ipart : ∀ (G : StepVariable (finiteCells F) → ℝ), (∀ η : StepVariable (finiteCells F), (∀ b, ‖η b‖ ≤ Q.ballRadius) →
      ContDiffAt ℝ 1 G η) → ∀ b, Integrable (fun η : StepVariable (finiteCells F) => bondPartialDeriv G b η (η b))
        (normalizedBallLaw (cutoffFactor Q.ballRadius Q.cutoff) Ψ') := fun G hG b =>
    integrable_of_continuousAt_closedBalls hae fun η h => continuousAt_bondPartialDeriv_diag (hG η h) b
  have iover : ∀ (Y : F.Cell) (u : ↥(chordBonds (finiteCells F)) → StepVariable (finiteCells F) → ℝ),
      (∀ b, Integrable (u b) (normalizedBallLaw (cutoffFactor Q.ballRadius Q.cutoff) Ψ')) →
      Integrable (fun η => ColdHalfLaw.sumOverBlock Y fun b => u b η)
        (normalizedBallLaw (cutoffFactor Q.ballRadius Q.cutoff) Ψ') := fun Y u hu => by
    unfold ColdHalfLaw.sumOverBlock
    refine integrable_finsetSum _ fun b _ => ?_
    by_cases h : enclosingCell b.1.1 = Y
    · simpa [h] using hu b
    · simpa [h] using integrable_zero _ _ _
  have hslope : ∀ η : StepVariable (finiteCells F), (∀ b, ‖η b‖ ≤ Q.ballRadius) → ∀ b,
      bondPartialDeriv (fun ζ => Q.totalCost ζ V) b η (η b) = slopeAlong Q V b η := fun η hη b =>
    bondPartialDeriv_eq_chartedSlope Q V η ((hS η hη).differentiableAt (by simp)) b (η b)
  have islope : ∀ b, Integrable (slopeAlong Q V b) (normalizedBallLaw (cutoffFactor Q.ballRadius Q.cutoff) Ψ') := fun b => by
    refine (ipart _ hS b).congr ?_
    filter_upwards [hae] with η hη
    exact hslope η (fun b => (hη b).le) b
  have ig : ∀ Y : F.Cell, Integrable (fun η => - Q.cutoffTerm Y η V + Q.gapTerm Y η V + Q.familyTerm Y η V - Q.slopeTerm Y η V)
      (normalizedBallLaw (cutoffFactor Q.ballRadius Q.cutoff) Ψ') := fun Y => by
    have i1 : Integrable (fun η => Q.cutoffTerm Y η V) (normalizedBallLaw (cutoffFactor Q.ballRadius Q.cutoff) Ψ') :=
      iover Y (fun b η => ‖η b‖ * deriv Q.cutoff ‖η b‖) fun b => cutoffTerm_integrable hP hL hρ hcut hc b
    have i2 : Integrable (fun η => Q.gapTerm Y η V) (normalizedBallLaw (cutoffFactor Q.ballRadius Q.cutoff) Ψ') :=
      iover Y (fun b η => bondPartialDeriv (fun ζ => Q.gapHaarExcess ζ V) b η (η b)) fun b => ipart _ hJ b
    have i3 : Integrable (fun η => Q.familyTerm Y η V) (normalizedBallLaw (cutoffFactor Q.ballRadius Q.cutoff) Ψ') := by
      unfold ColdHalfLaw.familyTerm
      exact integrable_finsetSum _ fun y _ => integrable_finsetSum _ fun b _ => ipart _ (hR y) b
    have i4 : Integrable (fun η => Q.slopeTerm Y η V) (normalizedBallLaw (cutoffFactor Q.ballRadius Q.cutoff) Ψ') := by
      have h5 := ((iover Y (fun b η => slopeAlong Q V b η) islope).const_mul Q.coupling).sub
        ((integrable_of_continuousAt_closedBalls hae (hB Y)).const_mul 2)
      refine h5.congr (Filter.Eventually.of_forall fun η => ?_)
      exact (slopeTerm_eq Q Y η V).symm
    exact ((i1.neg.add i2).add i3).sub i4
  have hsc := fun b => integral_dilation_score_eq_zero hM hP hL hρ hcut hΨ' b
  have hpt : ∀ᵐ η ∂normalizedBallLaw (cutoffFactor Q.ballRadius Q.cutoff) Ψ',
      ∑ Y ∈ finiteCells F, (- Q.cutoffTerm Y η V + Q.gapTerm Y η V + Q.familyTerm Y η V - Q.slopeTerm Y η V) =
        2 * Q.coupling * (Q.totalCost η V - Q.totalCost 0 V) - 3 * ((chordBonds (finiteCells F)).card : ℝ) -
          ∑ b, (bondPartialDeriv Ψ' b η (η b) + ‖η b‖ * deriv Q.cutoff ‖η b‖ - 3) := by
    filter_upwards [hae] with η hη
    have hcl : ∀ b, ‖η b‖ ≤ Q.ballRadius := fun b => (hη b).le
    have e1 : ∑ Y ∈ finiteCells F, Q.cutoffTerm Y η V = ∑ b, ‖η b‖ * deriv Q.cutoff ‖η b‖ :=
      sum_sumOverBlock fun b => ‖η b‖ * deriv Q.cutoff ‖η b‖
    have e2 : ∑ Y ∈ finiteCells F, Q.gapTerm Y η V = ∑ b, bondPartialDeriv (fun ζ => Q.gapHaarExcess ζ V) b η (η b) :=
      sum_sumOverBlock fun b => bondPartialDeriv (fun ζ => Q.gapHaarExcess ζ V) b η (η b)
    have e3 : ∑ Y ∈ finiteCells F, Q.familyTerm Y η V = ∑ y ∈ sitesOfCells (finiteCells F) F.depth, ∑ b,
        bondPartialDeriv (fun ζ => interpolatedExpansion 1 Q.a Q.chartRadius Q.mirrorRadius Q.family y ζ V) b η (η b) := by
      classical
      unfold ColdHalfLaw.familyTerm
      exact Finset.sum_fiberwise_of_maps_to (fun y hy => mem_finiteCells_of_site hy _) _
    have e4 : ∑ Y ∈ finiteCells F, Q.slopeTerm Y η V =
        Q.coupling * ∑ b, slopeAlong Q V b η - 2 * (Q.coupling * (Q.totalCost η V - Q.totalCost 0 V)) := by
      simp only [slopeTerm_eq, Finset.sum_sub_distrib, ← Finset.mul_sum]
      rw [hsum η hη]
      congr 2
      exact sum_sumOverBlock fun b => slopeAlong Q V b η
    have e5 : ∑ b, (bondPartialDeriv Ψ' b η (η b) + ‖η b‖ * deriv Q.cutoff ‖η b‖ - 3) =
        Q.coupling * ∑ b, slopeAlong Q V b η - ∑ b, bondPartialDeriv (fun ζ => Q.gapHaarExcess ζ V) b η (η b) -
          (∑ y ∈ sitesOfCells (finiteCells F) F.depth, ∑ b,
            bondPartialDeriv (fun ζ => interpolatedExpansion 1 Q.a Q.chartRadius Q.mirrorRadius Q.family y ζ V) b η (η b)) +
          ∑ b, ‖η b‖ * deriv Q.cutoff ‖η b‖ - 3 * ((chordBonds (finiteCells F)).card : ℝ) := by
      have hp : ∀ b, bondPartialDeriv Ψ' b η (η b) = _ := fun b => bondPartialDeriv_exponent Q V Ψ' hagree η hη
        ((hS η hcl).differentiableAt (by simp)) ((hJ η hcl).differentiableAt (by simp))
        (fun y => (hR y η hcl).differentiableAt (by simp)) b
      simp only [hp, Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]
      rw [Finset.sum_comm (s := Finset.univ) (t := sitesOfCells (finiteCells F) F.depth)]
      simp
      ring
    rw [e5, Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_neg_distrib, e1, e2, e3, e4]
    ring
  have icost : Integrable (fun η => Q.totalCost η V - Q.totalCost 0 V) (normalizedBallLaw (cutoffFactor Q.ballRadius Q.cutoff) Ψ') :=
    integrable_of_continuousAt_closedBalls hae fun η h => (hS η h).continuousAt.sub continuousAt_const
  have hg : ∑ Y ∈ finiteCells F,
      Q.expectation V (fun η => - Q.cutoffTerm Y η V + Q.gapTerm Y η V + Q.familyTerm Y η V - Q.slopeTerm Y η V) =
      2 * Q.coupling * Q.expectation V (fun η => Q.totalCost η V - Q.totalCost 0 V) -
        3 * ((chordBonds (finiteCells F)).card : ℝ) := by
    simp only [hQm]
    have h3 : Integrable (fun η => 2 * Q.coupling * (Q.totalCost η V - Q.totalCost 0 V))
        (normalizedBallLaw (cutoffFactor Q.ballRadius Q.cutoff) Ψ') :=
      icost.const_mul _
    have h1 : Integrable (fun η => 2 * Q.coupling * (Q.totalCost η V - Q.totalCost 0 V) -
        3 * ((chordBonds (finiteCells F)).card : ℝ)) (normalizedBallLaw (cutoffFactor Q.ballRadius Q.cutoff) Ψ') :=
      h3.sub (integrable_const _)
    have h2 : Integrable (fun η : StepVariable (finiteCells F) =>
        ∑ b, (bondPartialDeriv Ψ' b η (η b) + ‖η b‖ * deriv Q.cutoff ‖η b‖ - 3))
        (normalizedBallLaw (cutoffFactor Q.ballRadius Q.cutoff) Ψ') := integrable_finsetSum _ fun b _ => (hsc b).1
    rw [← integral_finsetSum _ fun Y _ => ig Y, integral_congr_ae hpt, integral_sub h1 h2,
      integral_sub h3 (integrable_const _), integral_const_mul, integral_const,
      integral_finsetSum _ fun b _ => (hsc b).1]
    simp [fun b => (hsc b).2]
  have hx0 : Q.coupling ≠ 0 := hx.ne'
  have hd : ∀ Y, Q.dilationRemainder Y V = 1 / (2 * Q.coupling) *
      Q.expectation V (fun η => - Q.cutoffTerm Y η V + Q.gapTerm Y η V + Q.familyTerm Y η V - Q.slopeTerm Y η V) :=
    fun Y => rfl
  simp only [hd]
  rw [← Finset.mul_sum, hg]
  field_simp
  ring
end Identity
section Table
variable {F : BlockFrame}
private theorem contDiffAt_of_leftTranslate_elim0 {k : WithTop ℕ∞} (G : StepVariable (finiteCells F) → F.GaugeField F.top → ℝ)
    (V : F.GaugeField F.top) (η : StepVariable (finiteCells F))
    (h : ContDiffAt ℝ k (fun q : (Fin 0 → ℝ) × StepVariable (finiteCells F) =>
      G q.2 (leftTranslate (ColdStepAtMirrorFrames.bondSpread (Fin.elim0 : Fin 0 → F.Site F.top × Fin 4)
        (Fin.elim0 : Fin 0 → imaginaryQuaternions) q.1) V)) (0, η)) :
    ContDiffAt ℝ k (fun ζ => G ζ V) η := by apply _root_.YangMills.SharedProofs.p43393 <;> assumption
private theorem dilationIdentity_at_parameters (hM : integrationByPartsAlongFieldStatement) (hP : cutoffDerivBoundsStatement)
    (hL : normalizedBallLawIsProbabilityStatement) (hE : interpolationAtEndpoints) (T : _root_.YangMills.Construction.ColdStepAtMirrorFrames.StepParameters)
    (hDr : T.IsOrdered) (hy : 1 ≤ T.coupling) {K : ℕ → ℝ} {D : ℕ → ℕ → ℝ} (hX : CellExponentsBoundedAt T)
    (hRw : CentredExpansionsBoundedAt T) (hCv : ExponentsConvexAt T)
    (hKt : interpolationKernelBoundsAt T K D) : dilationIdentityAt T := by
  intro t x f F V hst hrow
  have hfl : T.coupling ≤ x := hst.coupling_le
  have hx : 0 < x := by linarith
  have hρ : 0 < T.ballRadius := by
    have := hDr.σ_pos
    show 0 < T.σ / 64
    positivity
  have hEB := (hX t x F V false hfl hst.torus hst.small_curvature).1
  have hRB := hRw t x f F V false hfl hrow hst.torus hst.small_curvature
  obtain ⟨Ψ', K', hag, hconv, -⟩ := hCv t x f F V false 1 hfl hrow hst.torus hst.small_curvature zero_le_one le_rfl
  have hends := hE F false T.a T.chainParams.ρA T.chainParams.lam x 0 (frameRadius x) V
  have e1 : segmentEnd false = 1 := by simp [segmentEnd]
  rw [e1] at hends
  obtain ⟨-, -, -, hf4, hf5, hf6, -⟩ := hends
  have hK' : ∀ η : StepVariable (finiteCells F), (∀ b, ‖η b‖ ≤ T.ballRadius) →
      HasInterpolationKernels 1 T.a T.chainParams.ρA T.κ T.chainParams.κ₂ T.chainParams.δ₂ x (frameRadius x) K D V η :=
    fun η hη => hKt x t F V 1 η hfl hst.torus hst.small_curvature zero_le_one le_rfl hη
  have hu : AreUnitVectors (Fin.elim0 : Fin 0 → imaginaryQuaternions) := fun i => i.elim0
  refine dilationIdentity_of_smooth hM hP hL (coldHalfLawAt T x f) V hx hρ hDr.cutoff ?_ ?_ ?_ ?_ ?_ ?_ Ψ'
    (hconv.smooth.of_le (by norm_num)) ?_
  · intro η hη
    exact contDiffAt_of_jointDisplacement (interpolatedEnergy 1 T.a T.chainParams.ρA (frameRadius x)) V η
      fun l b u hl hu' => ((hK' η hη).energy l 0 b u Fin.elim0 Fin.elim0 hl hu' hu).1
  · intro c η hη
    exact (contDiffAt_of_jointDisplacement (contourHaarGap 1 T.a T.chainParams.ρA x (frameRadius x) c) V η
      fun l b u hl hu' => ((hK' η hη).gap c l 0 b u Fin.elim0 Fin.elim0 (by omega) hu' hu).1).sub contDiffAt_const
  · intro b₀ η hη
    exact contDiffAt_of_jointDisplacement (interpolatedHaarLogRatio 1 T.a T.chainParams.ρA (frameRadius x) b₀) V η
      fun l b u hl hu' => ((hK' η hη).haar b₀ l 0 b u Fin.elim0 Fin.elim0 (by omega) hu' hu).1
  · intro y η hη
    have h := contDiffAt_of_leftTranslate_elim0
      (fun ζ V' => centredExpansion false T.a T.chainParams.ρA (frameRadius x) f y ζ V') V η
      (hRB.smooth y η 0 Fin.elim0 Fin.elim0 hη)
    exact (h.of_le (by norm_num)).congr_of_eventuallyEq (Filter.Eventually.of_forall fun ζ => hf4 f y ζ)
  · intro Y η hη
    have h := contDiffAt_of_leftTranslate_elim0
      (fun ζ V' => cellExponent false T.a T.chainParams.ρA x (frameRadius x) Y V' ζ) V η
      (hEB.smooth Y η 0 Fin.elim0 Fin.elim0 hη)
    exact h.continuousAt.congr (Filter.Eventually.of_forall fun ζ => (hf5 Y ζ).symm)
  · intro η hη
    show interpolatedExponent 1 T.a T.chainParams.ρA x (frameRadius x) V η =
      ∑ Y ∈ finiteCells F, interpolatedBlockExponent 1 T.a T.chainParams.ρA x (frameRadius x) Y V η
    have hz := hEB.sum_eq η hη
    have h6 := hf6 (fun _ _ _ => 0) η
    have hz1 : stepExponent false T.a T.chainParams.ρA x (frameRadius x) (fun _ _ _ => 0) 0 V η =
        stepExponent false T.a T.chainParams.ρA x (frameRadius x) (fun _ _ _ => 0) 1 V η := by
      simp [stepExponent, centredExpansion, subtractTrivial]
    have hz2 : familyLawExponent 1 T.a T.chainParams.ρA x (frameRadius x) (fun _ _ _ => 0) V η =
        interpolatedExponent 1 T.a T.chainParams.ρA x (frameRadius x) V η := by
      simp [familyLawExponent, interpolatedExpansion, subtractTrivial]
    rw [Finset.sum_congr rfl fun Y _ => hf5 Y η, ← hz, hz1, ← h6, hz2]
  · intro η hη
    rw [hag η hη]
    exact (hf6 f η).symm
end Table
theorem dilationIdentity_holds (hM : integrationByPartsAlongFieldStatement) (hP : cutoffDerivBoundsStatement)
    (hL : normalizedBallLawIsProbabilityStatement) (hE : interpolationAtEndpoints)
    (hB : CellExponentsBounded) (hRw : CentredExpansionsBounded)
    (hC : exponentConvexityStatement) (hK : interpolationKernelBoundsStatement)
    (hJ : EventuallyInParametersCombines) : dilationIdentity := by
  obtain ⟨join, weaken⟩ := hJ
  obtain ⟨Kf, Df, -, -, hKt⟩ := hK
  have h1 : EventuallyInParameters fun T => 1 ≤ T.coupling := fun _ _ => ⟨0, fun _ _ _ _ _ => ⟨0, fun _ _ =>
    ⟨1, one_pos, fun _ _ _ => ⟨1, one_pos, fun _ _ _ _ => ⟨0, fun _ _ => ⟨1, one_pos,
      fun _ _ _ _ _ => ⟨0, fun _ _ _ _ => ⟨0, fun _ _ => ⟨0, fun _ _ => ⟨1, fun _ hy => hy⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
  refine weaken _ _ ?_ (join _ _ hB (join _ _ hRw (join _ _ hC (join _ _ hKt h1))))
  rintro T hDr ⟨hX, hR, hCv, hKT, hy⟩
  exact dilationIdentity_at_parameters hM hP hL hE T hDr hy hX hR hCv hKT
end WeightedResponses
end YangMills.Construction
end
