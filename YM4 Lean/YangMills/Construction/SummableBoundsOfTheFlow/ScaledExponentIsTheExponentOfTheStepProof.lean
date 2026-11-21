import YangMills.Construction.SummableBoundsOfTheFlow.BlockExpansionIsAdmittedProof
import YangMills.Construction.SummableBoundsOfTheFlow.GroupGapHasItsTail
import YangMills.Construction.SummableBoundsOfTheFlow.ScaledExponentIsTheExponentOfTheStep
import YangMills.Construction.SummableBoundsOfTheFlow.TheTraceOfTheHessianHasKernelsProof
import Mathlib
set_option autoImplicit false
noncomputable section
open YangMills.Construction.BlockAverages YangMills.Construction.ColdStepAtMirrorFrames YangMills.Construction.ReferenceDensity MeasureTheory Set
namespace YangMills.Construction.ScaledVariables
variable {F : BlockFrame}
private theorem secondDerivAlong_eq_fderiv_fderiv {X : Type} [Fintype X] [DecidableEq X]
    (E : BondField X → ℝ) (z u w : BondField X) (hz : DifferentiableAt ℝ (fderiv ℝ E) z) :
    secondDerivAlong E z u w = fderiv ℝ (fderiv ℝ E) z w u := by apply _root_.YangMills.SharedProofs.p7378 <;> assumption
private theorem isOpen_setOf_forall_norm_lt {X : Type} [Fintype X] (r : ℝ) :
    IsOpen {η : BondField X | ∀ b, ‖η b‖ < r} := by apply _root_.YangMills.SharedProofs.p3058 <;> assumption
private theorem smul_norm_lt_of_mem_Icc {X : Type} [Fintype X] {r : ℝ} {η : BondField X}
    (hη : ∀ b, ‖η b‖ < r) {v : ℝ} (hv : v ∈ Icc (0 : ℝ) 1) : ∀ b, ‖(v • η) b‖ < r := by
  intro b
  have h1 : ‖(v • η) b‖ = |v| * ‖η b‖ := by
    rw [Pi.smul_apply, norm_smul, Real.norm_eq_abs]
  rw [h1, abs_of_nonneg hv.1]
  have := hη b
  have h0 := norm_nonneg (η b)
  nlinarith [hv.1, hv.2]
private theorem integral_fderiv_segment_eq_integral_second {X : Type} [Fintype X] [DecidableEq X]
    (E : BondField X → ℝ) (r : ℝ)
    (hE : ContDiffOn ℝ 2 E {η | ∀ b, ‖η b‖ < r}) (η d : BondField X)
    (hη : ∀ b, ‖η b‖ < r) (h0 : fderiv ℝ E 0 = 0) :
    ∫ v in (0 : ℝ)..1, fderiv ℝ E (v • η) d =
      ∫ v in (0 : ℝ)..1, (1 - v) * secondDerivAlong E (v • η) d η := by
  set B : Set (BondField X) := {η | ∀ b, ‖η b‖ < r} with hB
  have hBo : IsOpen B := isOpen_setOf_forall_norm_lt r
  have hE1 : ContDiffOn ℝ 1 (fderiv ℝ E) B := hE.fderiv_of_isOpen hBo (by norm_num)
  set G : BondField X → ℝ := fun ζ => fderiv ℝ E ζ d with hG
  have hG1 : ContDiffOn ℝ 1 G B := hE1.clm_apply contDiffOn_const
  have hG2 : ContinuousOn (fun z => fderiv ℝ G z η) B :=
    (hG1.continuousOn_fderiv_of_isOpen hBo le_rfl).clm_apply continuousOn_const
  have hseg : ∀ v ∈ Icc (0 : ℝ) 1, v • η ∈ B := fun v hv => smul_norm_lt_of_mem_Icc hη hv
  have hγ : ContinuousOn (fun v : ℝ => v • η) (Icc 0 1) := by fun_prop
  have hH : ContinuousOn (fun v : ℝ => G (v • η)) (Icc 0 1) :=
    hG1.continuousOn.comp hγ hseg
  have hH' : ContinuousOn (fun v : ℝ => fderiv ℝ G (v • η) η) (Icc 0 1) :=
    hG2.comp hγ hseg
  have hder : ∀ v ∈ Icc (0 : ℝ) 1,
      HasDerivAt (fun v : ℝ => G (v • η)) (fderiv ℝ G (v • η) η) v := by
    intro v hv
    have hdiff : DifferentiableAt ℝ G (v • η) :=
      (hG1.differentiableOn (by norm_num)).differentiableAt (hBo.mem_nhds (hseg v hv))
    have h1 : HasDerivAt (fun v : ℝ => v • η) ((1 : ℝ) • η) v := (hasDerivAt_id v).smul_const η
    have h3 := hdiff.hasFDerivAt.comp_hasDerivAt v h1
    rw [one_smul] at h3
    exact h3
  have hP : ∀ v ∈ uIcc (0 : ℝ) 1, HasDerivAt (fun v : ℝ => (v - 1) * G (v • η))
      (G (v • η) + (v - 1) * fderiv ℝ G (v • η) η) v := by
    intro v hv
    rw [uIcc_of_le zero_le_one] at hv
    have h1 : HasDerivAt (fun v : ℝ => v - 1) 1 v := (hasDerivAt_id v).sub_const 1
    exact (h1.mul (hder v hv)).congr_deriv (by ring)
  have hint1 : IntervalIntegrable (fun v : ℝ => G (v • η)) volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    rwa [uIcc_of_le zero_le_one]
  have hint2 : IntervalIntegrable (fun v : ℝ => (v - 1) * fderiv ℝ G (v • η) η) volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le zero_le_one]
    exact (by fun_prop : ContinuousOn (fun v : ℝ => v - 1) (Icc 0 1)).mul hH'
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hP (hint1.add hint2)
  rw [intervalIntegral.integral_add hint1 hint2] at hftc
  have hz : G ((0 : ℝ) • η) = 0 := by
    simp [hG, h0]
  have hneg : ∫ v in (0 : ℝ)..1, (1 - v) * secondDerivAlong E (v • η) d η =
      -∫ v in (0 : ℝ)..1, (v - 1) * fderiv ℝ G (v • η) η := by
    rw [← intervalIntegral.integral_neg]
    congr 1
    funext v
    simp only [secondDerivAlong, hG]
    ring
  rw [hneg]
  show (∫ v in (0 : ℝ)..1, G (v • η)) = _
  linarith
private theorem sub_eq_integral_fderiv_segment {X : Type} [Fintype X] [DecidableEq X]
    (E : BondField X → ℝ) (r : ℝ)
    (hE : ContDiffOn ℝ 2 E {η | ∀ b, ‖η b‖ < r}) (η : BondField X)
    (hη : ∀ b, ‖η b‖ < r) :
    E η - E 0 = ∫ v in (0 : ℝ)..1, fderiv ℝ E (v • η) η := by
  set B : Set (BondField X) := {η | ∀ b, ‖η b‖ < r} with hB
  have hBo : IsOpen B := isOpen_setOf_forall_norm_lt r
  have hseg : ∀ v ∈ Icc (0 : ℝ) 1, v • η ∈ B := fun v hv => smul_norm_lt_of_mem_Icc hη hv
  have hγ : ContinuousOn (fun v : ℝ => v • η) (Icc 0 1) := by fun_prop
  have hder : ∀ v ∈ uIcc (0 : ℝ) 1,
      HasDerivAt (fun v : ℝ => E (v • η)) (fderiv ℝ E (v • η) η) v := by
    intro v hv
    rw [uIcc_of_le zero_le_one] at hv
    have hdiff : DifferentiableAt ℝ E (v • η) :=
      (hE.differentiableOn (by norm_num)).differentiableAt (hBo.mem_nhds (hseg v hv))
    have h1 : HasDerivAt (fun v : ℝ => v • η) ((1 : ℝ) • η) v := (hasDerivAt_id v).smul_const η
    have h3 := hdiff.hasFDerivAt.comp_hasDerivAt v h1
    rw [one_smul] at h3
    exact h3
  have hc : ContinuousOn (fun v : ℝ => fderiv ℝ E (v • η) η) (Icc 0 1) :=
    ((hE.continuousOn_fderiv_of_isOpen hBo (by norm_num)).comp hγ hseg).clm_apply
      continuousOn_const
  have hint : IntervalIntegrable (fun v : ℝ => fderiv ℝ E (v • η) η) volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    rwa [uIcc_of_le zero_le_one]
  have := intervalIntegral.integral_eq_sub_of_hasDerivAt hder hint
  rw [this]
  simp
private theorem toImaginary_add_apply (v w : EuclideanSpace ℝ (Fin 3)) :
    toImaginary (v + w) = toImaginary v + toImaginary w := by apply _root_.YangMills.Construction.Interpolation.TopVariation.toImaginary_add <;> assumption
private theorem toImaginary_smul_apply (c : ℝ) (v : EuclideanSpace ℝ (Fin 3)) :
    toImaginary (c • v) = c • toImaginary v := by apply _root_.YangMills.Construction.Interpolation.TopVariation.toImaginary_smul <;> assumption
private theorem update_coordsAboveFrame (a r : ℝ) (V : F.GaugeField F.top)
    (η : StepVariable (finiteCells F)) (b : ↥(chordBonds (finiteCells F))) (e : BondVector) (u : ℝ) :
    Function.update (coordsAboveFrame true a r 0 V η) b.1.1
      (Function.update (coordsAboveFrame true a r 0 V η b.1.1) b.1.2
        (coordsAboveFrame true a r 0 V η b.1.1 b.1.2 + u • toImaginary e)) =
      coordsAboveFrame true a r 0 V (η + u • bondVariation b e) := by
  funext x i
  by_cases h : (x, i) = b.1
  · have hx : x = b.1.1 := congrArg Prod.fst h
    have hi : i = b.1.2 := congrArg Prod.snd h
    subst hx hi
    have hm : (b.1.1, b.1.2) ∈ chordBonds (finiteCells F) := b.2
    simp only [Function.update_self, coordsAboveFrame, stepCoordinates, dif_pos hm]
    have hb : (⟨(b.1.1, b.1.2), hm⟩ : ↥(chordBonds (finiteCells F))) = b := rfl
    rw [hb]
    simp only [Pi.add_apply, Pi.smul_apply, bondVariation, Pi.single_eq_same,
      toImaginary_add_apply, toImaginary_smul_apply]
    abel
  · have hne : ∀ hm : (x, i) ∈ chordBonds (finiteCells F),
        (bondVariation b e : StepVariable (finiteCells F)) ⟨(x, i), hm⟩ = 0 := by
      intro hm
      apply Pi.single_eq_of_ne
      intro h'
      exact h (congrArg Subtype.val h')
    have hc : stepCoordinates (η + u • bondVariation b e) x i = stepCoordinates η x i := by
      unfold stepCoordinates
      by_cases hm : (x, i) ∈ chordBonds (finiteCells F)
      · simp only [dif_pos hm, Pi.add_apply, Pi.smul_apply, hne hm, smul_zero, add_zero]
      · simp only [dif_neg hm]
    have hr : coordsAboveFrame true a r 0 V (η + u • bondVariation b e) x i =
        coordsAboveFrame true a r 0 V η x i := by
      simp only [coordsAboveFrame, hc]
    rw [hr]
    by_cases hx : x = b.1.1
    · subst hx
      have hi : i ≠ b.1.2 := fun h' => h (Prod.ext rfl h')
      simp only [Function.update_self]
      rw [Function.update_of_ne hi]
    · rw [Function.update_of_ne hx]
private theorem chartedSlope_eq_fderiv (a r : ℝ) (V : F.GaugeField F.top)
    (z : StepVariable (finiteCells F))
    (hd : DifferentiableAt ℝ (chartedEnergyAtMinimizer a r V) z)
    (b : ↥(chordBonds (finiteCells F))) (e : BondVector) :
    chartedSlope a (coordsAboveFrame true a r 0 V z) V b.1 (toImaginary e) =
      fderiv ℝ (chartedEnergyAtMinimizer a r V) z (bondVariation b e) := by
  unfold chartedSlope
  have h1 : (fun u : ℝ => chartedEnergy a (Function.update (coordsAboveFrame true a r 0 V z) b.1.1
      (Function.update (coordsAboveFrame true a r 0 V z b.1.1) b.1.2
        (coordsAboveFrame true a r 0 V z b.1.1 b.1.2 + u • toImaginary e))) V) =
      fun u : ℝ => chartedEnergyAtMinimizer a r V (z + u • bondVariation b e) := by
    funext u
    rw [update_coordsAboveFrame]
    rfl
  rw [h1]
  have h2 : HasDerivAt (fun u : ℝ => z + u • (bondVariation b e : StepVariable (finiteCells F)))
      (bondVariation b e) 0 := by
    have h3 := ((hasDerivAt_id (0 : ℝ)).smul_const
      (bondVariation b e : StepVariable (finiteCells F))).const_add z
    simpa using h3
  have h4 : HasFDerivAt (chartedEnergyAtMinimizer a r V)
      (fderiv ℝ (chartedEnergyAtMinimizer a r V) z)
      (z + (0 : ℝ) • (bondVariation b e : StepVariable (finiteCells F))) := by
    simpa using hd.hasFDerivAt
  exact (h4.comp_hasDerivAt (0 : ℝ) h2).deriv
private theorem bondVariation_smul_apply {X : Type} [Fintype X] [DecidableEq X] (b : X) (c : ℝ)
    (e : BondVector) :
    bondVariation b (c • e) = c • bondVariation b e := by
  unfold bondVariation
  funext i
  by_cases h : i = b
  · subst h
    simp
  · simp [Pi.single_eq_of_ne h]
abbrev _root_.YangMills.SharedProofs.p169 := @bondVariation_smul_apply
private theorem mem_finiteCells_of_extent_ne_zero (hF : ∀ i, F.extent i ≠ 0) (Y : F.Cell) :
    Y ∈ finiteCells F := by
  have hfin : Finite F.Cell := by
    have h : ∀ i, NeZero (F.period F.top i) := fun i => ⟨by simp [BlockFrame.period, hF i]⟩
    exact Pi.finite
  unfold finiteCells
  rw [dif_pos hfin]
  exact @Finset.mem_univ _ (Fintype.ofFinite _) Y
abbrev _root_.YangMills.SharedProofs.p16107 := @mem_finiteCells_of_extent_ne_zero
private theorem integral_quadratic_term_rescaled (E : StepVariable (finiteCells F) → ℝ)
    (r l : ℝ) (hl : 0 < l)
    (hE : ContDiffOn ℝ 2 E {η | ∀ b, ‖η b‖ < r}) (h0 : fderiv ℝ E 0 = 0)
    (ζ : StepVariable (finiteCells F)) (hη : ∀ b, ‖(l • ζ) b‖ < r)
    (b : ↥(chordBonds (finiteCells F))) :
    l⁻¹ ^ 2 * ∫ v in (0 : ℝ)..1, fderiv ℝ E (v • (l • ζ)) (bondVariation b ((l • ζ) b)) =
      ∫ v in (0 : ℝ)..1, (1 - v) * secondDerivAlong E ((v * l) • ζ) (bondVariation b (ζ b)) ζ := by
  have hBo : IsOpen {η : StepVariable (finiteCells F) | ∀ b, ‖η b‖ < r} :=
    isOpen_setOf_forall_norm_lt r
  have hE1 : ContDiffOn ℝ 1 (fderiv ℝ E) {η | ∀ b, ‖η b‖ < r} :=
    hE.fderiv_of_isOpen hBo (by norm_num)
  rw [integral_fderiv_segment_eq_integral_second E r hE (l • ζ) _ hη h0,
    ← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro v hv
  rw [uIcc_of_le zero_le_one] at hv
  have hz : v • (l • ζ) ∈ {η : StepVariable (finiteCells F) | ∀ b, ‖η b‖ < r} :=
    smul_norm_lt_of_mem_Icc hη hv
  have hdz : DifferentiableAt ℝ (fderiv ℝ E) (v • (l • ζ)) :=
    (hE1.differentiableOn (by norm_num)).differentiableAt (hBo.mem_nhds hz)
  have hvl : v • (l • ζ) = (v * l) • ζ := smul_smul v l ζ
  have hd2 : DifferentiableAt ℝ (fderiv ℝ E) ((v * l) • ζ) := hvl ▸ hdz
  simp only []
  rw [secondDerivAlong_eq_fderiv_fderiv E _ _ _ hdz, hvl,
    secondDerivAlong_eq_fderiv_fderiv E _ _ _ hd2]
  have key : fderiv ℝ (fderiv ℝ E) ((v * l) • ζ) (l • ζ) (bondVariation b ((l • ζ) b)) =
      l * (l * fderiv ℝ (fderiv ℝ E) ((v * l) • ζ) ζ (bondVariation b (ζ b))) := by
    rw [Pi.smul_apply, bondVariation_smul_apply, map_smul]
    simp only [ContinuousLinearMap.smul_apply, map_smul, smul_eq_mul]
  rw [key]
  generalize fderiv ℝ (fderiv ℝ E) ((v * l) • ζ) ζ (bondVariation b (ζ b)) = A
  field_simp
private theorem sub_eq_sum_integral_bondVariation (E : StepVariable (finiteCells F) → ℝ) (r : ℝ)
    (hE : ContDiffOn ℝ 2 E {η | ∀ b, ‖η b‖ < r}) (η : StepVariable (finiteCells F))
    (hη : ∀ b, ‖η b‖ < r) :
    E η - E 0 = ∑ b : ↥(chordBonds (finiteCells F)),
      ∫ v in (0 : ℝ)..1, fderiv ℝ E (v • η) (bondVariation b (η b)) := by
  have hBo : IsOpen {η : StepVariable (finiteCells F) | ∀ b, ‖η b‖ < r} :=
    isOpen_setOf_forall_norm_lt r
  have hseg : ∀ v ∈ Icc (0 : ℝ) 1,
      v • η ∈ {η : StepVariable (finiteCells F) | ∀ b, ‖η b‖ < r} :=
    fun v hv => smul_norm_lt_of_mem_Icc hη hv
  have hγ : ContinuousOn (fun v : ℝ => v • η) (Icc 0 1) := by fun_prop
  have hint : ∀ d : StepVariable (finiteCells F),
      IntervalIntegrable (fun v : ℝ => fderiv ℝ E (v • η) d) volume 0 1 := by
    intro d
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le zero_le_one]
    exact ((hE.continuousOn_fderiv_of_isOpen hBo (by norm_num)).comp hγ hseg).clm_apply
      continuousOn_const
  rw [sub_eq_integral_fderiv_segment E r hE η hη,
    ← intervalIntegral.integral_finsetSum (fun b _ => hint _)]
  apply intervalIntegral.integral_congr
  intro v _
  simp only []
  rw [← map_sum]
  congr 1
  exact (Finset.univ_sum_single η).symm
private theorem haarGap_sub_eq_haarGapShift
    (tail : ∀ s : ℝ, 0 < s → haarGap s = 3 / 2 * Real.log s + haarGapTail (1 / s))
    (a l r : ℝ) (ha : 0 < a) (hl : 0 < l) (hr : 0 < r) :
    haarGap (a * l⁻¹ ^ 2 * r) - haarGap (a * l⁻¹ ^ 2) = haarGapShift a l r := by
  have hx : 0 < a * l⁻¹ ^ 2 := by positivity
  rw [tail _ (by positivity), tail _ hx, Real.log_mul hx.ne' hr.ne']
  unfold haarGapShift
  have h1 : 1 / (a * l⁻¹ ^ 2 * r) = l ^ 2 / (a * r) := by field_simp
  have h2 : 1 / (a * l⁻¹ ^ 2) = l ^ 2 / a := by field_simp
  rw [h1, h2]
  ring
theorem rescaledExponentAgrees_of_regular_of_logTail
    (hreg : chartedEnergyAtMinimizerRegular) (htail : HaarGapLogTail) :
    RescaledExponentAgrees := by
  refine EventuallyOrdered.mono hreg ?_
  intro T hT hn hE
  refine ⟨1, one_pos, ?_⟩
  intro t F V f ν l Y ζ hF hV hl _ hζ
  obtain ⟨hC, hcrit, hr, -⟩ := hE t F V hF hV
  have ha : 0 < T.a := by linarith [hT.one_le_a]
  have hη : ∀ b, ‖(l • ζ) b‖ < T.ballRadius := by
    intro b
    rw [Pi.smul_apply, norm_smul, Real.norm_eq_abs, abs_of_pos hl]
    exact hζ b
  have hext : ∀ i, F.extent i ≠ 0 := by
    obtain ⟨_, _, n, hn, hn₀⟩ := hF
    intro i
    rw [hn i]
    omega
  have hBo : IsOpen {η : StepVariable (finiteCells F) | ∀ b, ‖η b‖ < T.ballRadius} :=
    isOpen_setOf_forall_norm_lt T.ballRadius
  have hdiff : ∀ v ∈ Icc (0 : ℝ) 1,
      DifferentiableAt ℝ (chartedEnergyAtMinimizer T.a T.ρA V) (v • (l • ζ)) := by
    intro v hv
    exact (hC.differentiableOn (by norm_num)).differentiableAt
      (hBo.mem_nhds (smul_norm_lt_of_mem_Icc hη hv))
  have hgap : ∀ c ∈ innerBonds (finiteCells F) F.top,
      haarGapExcess T.a (l⁻¹ ^ 2) (fieldAboveFrame true T.a T.ρA 0 V (l • ζ)) c =
        haarGapShift T.a l ‖contourAverage (fieldAboveFrame true T.a T.ρA 0 V (l • ζ)) c‖ := by
    intro c hc
    unfold haarGapExcess
    exact haarGap_sub_eq_haarGapShift htail T.a l _ ha hl (hr _ hη c hc)
  have hquad : ∀ b : ↥(chordBonds (finiteCells F)),
      l⁻¹ ^ 2 * ∫ v in (0 : ℝ)..1,
          chartedSlope T.a (coordsAboveFrame true T.a T.ρA 0 V (v • (l • ζ))) V b.1
            (toImaginary ((l • ζ) b)) =
        ∫ v in (0 : ℝ)..1, (1 - v) *
          secondDerivAlong (chartedEnergyAtMinimizer T.a T.ρA V) ((v * l) • ζ)
            (bondVariation b (ζ b)) ζ := by
    intro b
    rw [← integral_quadratic_term_rescaled _ T.ballRadius l hl hC hcrit ζ hη b]
    congr 1
    apply intervalIntegral.integral_congr
    intro v hv
    rw [uIcc_of_le zero_le_one] at hv
    exact chartedSlope_eq_fderiv T.a T.ρA V _ (hdiff v hv) b _
  have hcell : ∀ Y : F.Cell, cellExponent true T.a T.ρA (l⁻¹ ^ 2) 0 Y V (l • ζ) =
      rescaledCellTerm T.a T.ρA l Y V ζ := by
    intro Y
    unfold cellExponent rescaledCellTerm
    congr 1
    · congr 1
      · rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro b _
        split_ifs
        · exact hquad b
        · simp
      · apply Finset.sum_congr rfl
        intro c hc
        exact hgap c (Finset.mem_filter.mp hc).1
  refine ⟨?_, hcell Y, ?_⟩
  · have hsum1 : ∀ g : ↥(chordBonds (finiteCells F)) → ℝ,
        ∑ Y' ∈ finiteCells F,
            (∑ b : ↥(chordBonds (finiteCells F)), if enclosingCell b.1.1 = Y' then g b else 0) =
          ∑ b, g b := by
      intro g
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro b _
      rw [Finset.sum_ite_eq, if_pos (mem_finiteCells_of_extent_ne_zero hext _)]
    have hsum2 : ∀ g : F.Site F.top × Fin 4 → ℝ,
        ∑ Y' ∈ finiteCells F,
            (∑ c ∈ (innerBonds (finiteCells F) F.top).filter (fun c => c.1 = Y'), g c) =
          ∑ c ∈ innerBonds (finiteCells F) F.top, g c :=
      fun g => Finset.sum_fiberwise_of_maps_to
        (fun c _ => mem_finiteCells_of_extent_ne_zero hext c.1) g
    unfold stepExponent rescaledExponent rescaledCellTerm
    simp only [Finset.sum_sub_distrib, hsum1, hsum2]
    have henergy : l⁻¹ ^ 2 * (chartedEnergy T.a (coordsAboveFrame true T.a T.ρA 0 V (l • ζ)) V -
        chartedEnergy T.a (coordsAboveFrame true T.a T.ρA 0 V 0) V) =
        ∑ b : ↥(chordBonds (finiteCells F)), ∫ v in (0 : ℝ)..1,
          (1 - v) * secondDerivAlong (chartedEnergyAtMinimizer T.a T.ρA V) ((v * l) • ζ)
            (bondVariation b (ζ b)) ζ := by
      have := sub_eq_sum_integral_bondVariation (chartedEnergyAtMinimizer T.a T.ρA V)
        T.ballRadius hC (l • ζ) hη
      unfold chartedEnergyAtMinimizer at this ⊢
      rw [this, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro b _
      exact integral_quadratic_term_rescaled _ T.ballRadius l hl hC hcrit ζ hη b
    rw [henergy, Finset.sum_congr rfl hgap]
  · unfold cellQuadratic
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro b _
    split_ifs
    · rw [Pi.smul_apply, norm_smul, Real.norm_eq_abs, abs_of_pos hl]
      field_simp
    · simp
end YangMills.Construction.ScaledVariables
end
