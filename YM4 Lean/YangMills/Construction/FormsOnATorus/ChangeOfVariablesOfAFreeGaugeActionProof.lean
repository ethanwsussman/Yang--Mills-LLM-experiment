import YangMills.Construction.ColdChainAtEveryLevel.GaugeMotionsOfAChain
import YangMills.Construction.FormsOnATorus.ChangeOfVariablesOfAFreeGaugeAction
import YangMills.Construction.FormsOnATorus.FactsOfTheHalfChart
import YangMills.Construction.FormsOnATorus.HaarOfFieldsInTheChart
import YangMills.Construction.FormsOnATorus.InvariantMeasureOnFreeOrbits
import YangMills.Construction.ResponseInTheExpansion.ElementsOfABond
import Mathlib
set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.deprecated false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false
noncomputable section
open MeasureTheory Set Metric
open scoped Quaternion ENNReal
namespace YangMills.Construction
open BlockAverages TorusFields
namespace GaugeCharts
namespace OrbitChart
private instance : StarModule ℝ ℍ[ℝ] := ⟨fun r a => by ext <;> simp⟩
variable {ι κ S : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
  [NormedAddCommGroup S] [NormedSpace ℝ S] [FiniteDimensional ℝ S]
def endpointQuaternion (χ : ι → imaginaryQuaternions) : Option ι → ℍ[ℝ]
  | none => 1
  | some z => hemispherePoint (χ z)
def bondQuaternion (tl hd : κ → Option ι) (V : κ → UnitQuaternion) (e : S →ₗ[ℝ] (κ → imaginaryQuaternions))
    (p : (ι → imaginaryQuaternions) × S) (b : κ) : ℍ[ℝ] :=
  endpointQuaternion p.1 (tl b) * hemispherePoint (e p.2 b) * (V b : ℍ[ℝ]) * star (endpointQuaternion p.1 (hd b)) *
    star (V b : ℍ[ℝ])
def bondCoordinates (tl hd : κ → Option ι) (V : κ → UnitQuaternion) (e : S →ₗ[ℝ] (κ → imaginaryQuaternions))
    (p : (ι → imaginaryQuaternions) × S) : κ → imaginaryQuaternions :=
  fun b => imaginaryPart (bondQuaternion tl hd V e p b)
def chartDomain (e : S →ₗ[ℝ] (κ → imaginaryQuaternions)) : Set ((ι → imaginaryQuaternions) × S) :=
  {p | (∀ z, ‖p.1 z‖ < 1) ∧ ∀ b, ‖e p.2 b‖ < 1}
def gaugeOfForm (χ : ι → imaginaryQuaternions) : ι → UnitQuaternion := fun z => hemisphereUnit (χ z)
def transformedChartField (tl hd : κ → Option ι) (V : κ → UnitQuaternion) (e : S →ₗ[ℝ] (κ → imaginaryQuaternions))
    (p : (ι → imaginaryQuaternions) × S) : κ → UnitQuaternion :=
  gaugeTransform tl hd (gaugeOfForm p.1) (hemisphereChartField V (e p.2))
def imaginaryPartCLM : ℍ[ℝ] →L[ℝ] imaginaryQuaternions := LinearMap.toContinuousLinearMap imaginaryPart
omit [DecidableEq ι] [DecidableEq κ] in
theorem isOpen_chartDomain (e : S →ₗ[ℝ] (κ → imaginaryQuaternions)) : IsOpen (chartDomain (ι := ι) e) := by
  have hc : Continuous e := e.continuous_of_finiteDimensional
  have h1 : IsOpen {p : (ι → imaginaryQuaternions) × S | ∀ z, ‖p.1 z‖ < 1} := by
    simp only [setOf_forall]
    exact isOpen_iInter_of_finite fun z => isOpen_lt (by fun_prop) continuous_const
  have h2 : IsOpen {p : (ι → imaginaryQuaternions) × S | ∀ b, ‖e p.2 b‖ < 1} := by
    simp only [setOf_forall]
    refine isOpen_iInter_of_finite fun b => isOpen_lt ?_ continuous_const
    exact ((continuous_apply b).comp (hc.comp continuous_snd)).norm
  exact h1.inter h2
theorem coe_gaugeAtEnd_gaugeOfForm {χ : ι → imaginaryQuaternions} (hχ : ∀ z, ‖χ z‖ < 1) (o : Option ι) :
    ((gaugeAtEnd (gaugeOfForm χ) o : UnitQuaternion) : ℍ[ℝ]) = endpointQuaternion χ o := by
  cases o with
  | none => rfl
  | some z => exact coe_hemisphereUnit (hχ z).le
theorem coe_transformedChartField_mul_inv (tl hd : κ → Option ι) (V : κ → UnitQuaternion)
    (e : S →ₗ[ℝ] (κ → imaginaryQuaternions)) {p : (ι → imaginaryQuaternions) × S} (hp : p ∈ chartDomain e) (b : κ) :
    ((transformedChartField tl hd V e p b * (V b)⁻¹ : UnitQuaternion) : ℍ[ℝ]) = bondQuaternion tl hd V e p b := by
  have h1 := coe_gaugeAtEnd_gaugeOfForm hp.1 (tl b)
  have h2 := coe_gaugeAtEnd_gaugeOfForm hp.1 (hd b)
  have h3 : ((hemisphereUnit (e p.2 b) : UnitQuaternion) : ℍ[ℝ]) = hemispherePoint (e p.2 b) :=
    coe_hemisphereUnit (hp.2 b).le
  simp only [transformedChartField, gaugeTransform, hemisphereChartField, bondQuaternion]
  rw [← h1, ← h2, ← h3]
  simp only [Submonoid.coe_mul, coe_inv_unitQuaternion, mul_assoc]
theorem norm_bondQuaternion (tl hd : κ → Option ι) (V : κ → UnitQuaternion) (e : S →ₗ[ℝ] (κ → imaginaryQuaternions))
    {p : (ι → imaginaryQuaternions) × S} (hp : p ∈ chartDomain e) (b : κ) :
    ‖bondQuaternion tl hd V e p b‖ = 1 := by
  rw [← coe_transformedChartField_mul_inv tl hd V e hp b]
  exact norm_unitQuaternion _
theorem endpointQuaternion_zero (o : Option ι) : endpointQuaternion (0 : ι → imaginaryQuaternions) o = 1 := by
  cases o with
  | none => rfl
  | some z => exact hemispherePoint_zero
theorem bondQuaternion_zero_form (tl hd : κ → Option ι) (V : κ → UnitQuaternion)
    (e : S →ₗ[ℝ] (κ → imaginaryQuaternions)) (ζ : S) (b : κ) :
    bondQuaternion tl hd V e (0, ζ) b = hemispherePoint (e ζ b) := by
  simp only [bondQuaternion, endpointQuaternion_zero, one_mul, star_one, mul_one]
  rw [mul_assoc, mul_star_self_unitQuaternion, mul_one]
theorem bondCoordinates_zero_form (tl hd : κ → Option ι) (V : κ → UnitQuaternion)
    (e : S →ₗ[ℝ] (κ → imaginaryQuaternions)) (ζ : S) :
    bondCoordinates tl hd V e (0, ζ) = e ζ := by
  funext b
  rw [bondCoordinates, bondQuaternion_zero_form, imaginaryPart_hemispherePoint]
omit [DecidableEq ι] [DecidableEq κ] in
theorem contDiffOn_endpointQuaternion (e : S →ₗ[ℝ] (κ → imaginaryQuaternions)) (o : Option ι) :
    ContDiffOn ℝ 1 (fun p : (ι → imaginaryQuaternions) × S => endpointQuaternion p.1 o) (chartDomain e) := by
  cases o with
  | none => exact contDiffOn_const
  | some z =>
    have h : ContDiff ℝ 1 fun p : (ι → imaginaryQuaternions) × S => p.1 z :=
      (contDiff_apply ℝ imaginaryQuaternions z).comp contDiff_fst
    exact contDiffOn_hemispherePoint.comp h.contDiffOn fun p hp => hp.1 z
omit [DecidableEq ι] [DecidableEq κ] in
theorem contDiffOn_bondQuaternion (tl hd : κ → Option ι) (V : κ → UnitQuaternion)
    (e : S →ₗ[ℝ] (κ → imaginaryQuaternions)) (b : κ) :
    ContDiffOn ℝ 1 (fun p : (ι → imaginaryQuaternions) × S => bondQuaternion tl hd V e p b) (chartDomain e) := by
  have hB : ContDiffOn ℝ 1 (fun p : (ι → imaginaryQuaternions) × S => hemispherePoint (e p.2 b)) (chartDomain e) := by
    have h : ContDiff ℝ 1 fun p : (ι → imaginaryQuaternions) × S => e p.2 b :=
      (contDiff_apply ℝ imaginaryQuaternions b).comp ((e.toContinuousLinearMap).contDiff.comp contDiff_snd)
    exact contDiffOn_hemispherePoint.comp h.contDiffOn fun p hp => hp.2 b
  have hS : ContDiffOn ℝ 1 (fun p : (ι → imaginaryQuaternions) × S => star (endpointQuaternion p.1 (hd b)))
      (chartDomain e) :=
    (starL' ℝ : ℍ[ℝ] ≃L[ℝ] ℍ[ℝ]).contDiff.comp_contDiffOn (contDiffOn_endpointQuaternion e (hd b))
  exact (((contDiffOn_endpointQuaternion e (tl b)).mul hB).mul contDiffOn_const |>.mul hS).mul contDiffOn_const
omit [DecidableEq ι] [DecidableEq κ] in
theorem contDiffOn_bondCoordinates (tl hd : κ → Option ι) (V : κ → UnitQuaternion)
    (e : S →ₗ[ℝ] (κ → imaginaryQuaternions)) :
    ContDiffOn ℝ 1 (bondCoordinates (ι := ι) tl hd V e) (chartDomain e) :=
  contDiffOn_pi.mpr fun b => imaginaryPartCLM.contDiff.comp_contDiffOn (contDiffOn_bondQuaternion tl hd V e b)
theorem hasDerivAt_endpointQuaternion (χ : ι → imaginaryQuaternions) (o : Option ι) :
    HasDerivAt (fun t : ℝ => endpointQuaternion (t • χ) o) ((formAtEnd χ o : imaginaryQuaternions) : ℍ[ℝ]) 0 := by
  cases o with
  | none => simpa [endpointQuaternion, formAtEnd] using hasDerivAt_const (0 : ℝ) (1 : ℍ[ℝ])
  | some z =>
    have hl : HasDerivAt (fun t : ℝ => t • χ z) (χ z) 0 := by
      simpa using (hasDerivAt_id (0 : ℝ)).smul_const (χ z)
    exact hasFDerivAt_hemispherePoint_zero.comp_hasDerivAt_of_eq 0 hl (by simp)
theorem star_coe_imaginary (w : imaginaryQuaternions) : star (w : ℍ[ℝ]) = -(w : ℍ[ℝ]) := by apply _root_.YangMills.Construction.GaugeMotions.star_coe_imaginary <;> assumption
theorem hasDerivAt_bondCoordinates_gaugeDirection (tl hd : κ → Option ι) (V : κ → UnitQuaternion)
    (e : S →ₗ[ℝ] (κ → imaginaryQuaternions)) (χ : ι → imaginaryQuaternions) (ζ : S) :
    HasDerivAt (fun t : ℝ => bondCoordinates tl hd V e (t • χ, ζ)) (gaugeLinearization tl hd V (e ζ) χ) 0 := by
  refine hasDerivAt_pi.mpr fun b => ?_
  have h1 := hasDerivAt_endpointQuaternion χ (tl b)
  have h2 := (hasDerivAt_endpointQuaternion χ (hd b)).star
  have hq := (((h1.mul_const (hemispherePoint (e ζ b))).mul_const (V b : ℍ[ℝ])).mul h2).mul_const
    (star (V b : ℍ[ℝ]))
  have hi := imaginaryPartCLM.hasFDerivAt.comp_hasDerivAt (0 : ℝ) hq
  have hv := mul_star_self_unitQuaternion (V b)
  set f₁ : ℍ[ℝ] := ((formAtEnd χ (tl b) : imaginaryQuaternions) : ℍ[ℝ]) with hf₁
  set f₂ : ℍ[ℝ] := ((formAtEnd χ (hd b) : imaginaryQuaternions) : ℍ[ℝ]) with hf₂
  set M : ℍ[ℝ] := hemispherePoint (e ζ b) with hM
  have hs₂ : star f₂ = -f₂ := star_coe_imaginary _
  have hderiv : (gaugeLinearization tl hd V (e ζ)) χ b =
      imaginaryPartCLM ((f₁ * M * (V b : ℍ[ℝ]) * star (endpointQuaternion ((0 : ℝ) • χ) (hd b)) +
      endpointQuaternion ((0 : ℝ) • χ) (tl b) * M * (V b : ℍ[ℝ]) * star f₂) * star (V b : ℍ[ℝ])) := by
    rw [zero_smul, endpointQuaternion_zero, endpointQuaternion_zero, star_one, mul_one, one_mul, hs₂]
    have e1 : (f₁ * M * (V b : ℍ[ℝ]) + M * (V b : ℍ[ℝ]) * -f₂) * star (V b : ℍ[ℝ]) =
        f₁ * M - M * ((V b : ℍ[ℝ]) * f₂ * star (V b : ℍ[ℝ])) := by
      calc _ = f₁ * M * ((V b : ℍ[ℝ]) * star (V b : ℍ[ℝ])) - M * ((V b : ℍ[ℝ]) * f₂ * star (V b : ℍ[ℝ])) := by
            noncomm_ring
        _ = _ := by rw [hv, mul_one]
    rw [e1]
    show imaginaryPart (f₁ * M) - imaginaryPart (M * ((V b : ℍ[ℝ]) * f₂ * star (V b : ℍ[ℝ]))) = imaginaryPart _
    rw [map_sub]
  rw [hderiv]
  exact hi
theorem hasFDerivAt_bondCoordinates_zero_form (tl hd : κ → Option ι) (V : κ → UnitQuaternion)
    (e : S →ₗ[ℝ] (κ → imaginaryQuaternions)) {ζ : S} (hζ : ∀ b, ‖e ζ b‖ < 1) :
    HasFDerivAt (bondCoordinates (ι := ι) tl hd V e) (chartLinearization tl hd V e (e ζ)).toContinuousLinearMap
      (0, ζ) := by
  have hp : ((0 : ι → imaginaryQuaternions), ζ) ∈ chartDomain e := ⟨fun z => by simp, hζ⟩
  have hd' : DifferentiableAt ℝ (bondCoordinates (ι := ι) tl hd V e) (0, ζ) :=
    ((contDiffOn_bondCoordinates tl hd V e).contDiffAt ((isOpen_chartDomain e).mem_nhds hp)).differentiableAt
      one_ne_zero
  have hF := hd'.hasFDerivAt
  suffices h : fderiv ℝ (bondCoordinates (ι := ι) tl hd V e) (0, ζ) =
      (chartLinearization tl hd V e (e ζ)).toContinuousLinearMap by
    rwa [h] at hF
  refine ContinuousLinearMap.ext fun v => ?_
  obtain ⟨χ, η⟩ := v
  have hsplit : ((χ, η) : (ι → imaginaryQuaternions) × S) = (χ, 0) + (0, η) := by simp
  rw [hsplit, map_add, map_add]
  congr 1
  · have hl : HasDerivAt (fun t : ℝ => ((t • χ, ζ) : (ι → imaginaryQuaternions) × S)) (χ, 0) 0 :=
      ((by simpa using (hasDerivAt_id (0 : ℝ)).smul_const χ : HasDerivAt (fun t : ℝ => t • χ) χ 0)).prodMk
        (hasDerivAt_const (0 : ℝ) ζ)
    have h1 := HasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hF hl (by simp)
    have h2 := hasDerivAt_bondCoordinates_gaugeDirection tl hd V e χ ζ
    have := h1.unique h2
    simpa [chartLinearization] using this
  · have hl : HasDerivAt (fun t : ℝ => (((0 : ι → imaginaryQuaternions), ζ + t • η) : (ι → imaginaryQuaternions) × S))
        (0, η) 0 :=
      (hasDerivAt_const (0 : ℝ) (0 : ι → imaginaryQuaternions)).prodMk
        (by simpa using ((hasDerivAt_id (0 : ℝ)).smul_const η).const_add ζ)
    have h1 := HasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hF hl (by simp)
    have h2 : HasDerivAt (fun t : ℝ => bondCoordinates (ι := ι) tl hd V e (0, ζ + t • η)) (e η) 0 := by
      have : (fun t : ℝ => bondCoordinates (ι := ι) tl hd V e (0, ζ + t • η)) = fun t : ℝ => e ζ + t • e η := by
        funext t
        rw [bondCoordinates_zero_form, map_add, map_smul]
      rw [this]
      simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (e η)).const_add (e ζ)
    have := h1.unique h2
    simpa [chartLinearization] using this
def positiveDomain (tl hd : κ → Option ι) (V : κ → UnitQuaternion) (e : S →ₗ[ℝ] (κ → imaginaryQuaternions)) :
    Set ((ι → imaginaryQuaternions) × S) :=
  {p | p ∈ chartDomain e ∧ ∀ b, 0 < (bondQuaternion tl hd V e p b).re}
omit [DecidableEq ι] [DecidableEq κ] in
theorem isOpen_positiveDomain (tl hd : κ → Option ι) (V : κ → UnitQuaternion)
    (e : S →ₗ[ℝ] (κ → imaginaryQuaternions)) : IsOpen (positiveDomain (ι := ι) tl hd V e) := by
  have hc : ∀ b, ContinuousOn (fun p : (ι → imaginaryQuaternions) × S => (bondQuaternion tl hd V e p b).re)
      (chartDomain e) := fun b =>
    Quaternion.continuous_re.comp_continuousOn (contDiffOn_bondQuaternion tl hd V e b).continuousOn
  have h : positiveDomain (ι := ι) tl hd V e =
      chartDomain e ∩ ⋂ b, (chartDomain e ∩ (fun p => (bondQuaternion tl hd V e p b).re) ⁻¹' Ioi 0) := by
    ext p
    simp only [positiveDomain, mem_setOf_eq, mem_inter_iff, mem_iInter, mem_preimage, mem_Ioi]
    exact ⟨fun h => ⟨h.1, fun b => ⟨h.1, h.2 b⟩⟩, fun h => ⟨h.1, fun b => (h.2 b).2⟩⟩
  rw [h]
  exact (isOpen_chartDomain e).inter
    (isOpen_iInter_of_finite fun b => (hc b).isOpen_inter_preimage (isOpen_chartDomain e) isOpen_Ioi)
theorem exists_uniform_tube {O : Set ((ι → imaginaryQuaternions) × S)} (hO : IsOpen O) {Z : Set S} (hZ : IsCompact Z)
    (h0 : ∀ ζ ∈ Z, ((0 : ι → imaginaryQuaternions), ζ) ∈ O) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ χ ζ, (∀ z, ‖χ z‖ < ε) → ζ ∈ Z → (χ, ζ) ∈ O := by
  obtain ⟨u, v, hu, hv, hsu, htv, huv⟩ :=
    generalized_tube_lemma (isCompact_singleton (x := (0 : ι → imaginaryQuaternions))) hZ hO
    (by
      rintro ⟨χ, ζ⟩ ⟨hχ, hζ⟩
      have : χ = 0 := hχ
      subst this
      exact h0 ζ hζ)
  obtain ⟨ε, hε, hb⟩ := Metric.isOpen_iff.mp hu 0 (hsu rfl)
  refine ⟨ε, hε, fun χ ζ hχ hζ => huv ⟨hb ?_, htv hζ⟩⟩
  rw [mem_ball_zero_iff, pi_norm_lt_iff hε]
  exact hχ
theorem bondCoordinates_of_mem_positiveDomain (tl hd : κ → Option ι) (V : κ → UnitQuaternion)
    (e : S →ₗ[ℝ] (κ → imaginaryQuaternions)) {p : (ι → imaginaryQuaternions) × S}
    (hp : p ∈ positiveDomain tl hd V e) :
    (∀ b, ‖bondCoordinates tl hd V e p b‖ < 1) ∧
      transformedChartField tl hd V e p = hemisphereChartField V (bondCoordinates tl hd V e p) := by
  have h := fun b => hemispherePoint_imaginaryPart (norm_bondQuaternion tl hd V e hp.1 b) (hp.2 b)
  refine ⟨fun b => (h b).1, ?_⟩
  funext b
  have h1 : ((transformedChartField tl hd V e p b * (V b)⁻¹ : UnitQuaternion) : ℍ[ℝ]) =
      ((hemisphereUnit (bondCoordinates tl hd V e p b) : UnitQuaternion) : ℍ[ℝ]) := by
    rw [coe_transformedChartField_mul_inv tl hd V e hp.1 b]
    show _ = ((hemisphereUnit (imaginaryPart (bondQuaternion tl hd V e p b)) : UnitQuaternion) : ℍ[ℝ])
    rw [coe_hemisphereUnit (h b).1.le]
    exact (h b).2.symm
  have h2 : transformedChartField tl hd V e p b * (V b)⁻¹ = hemisphereUnit (bondCoordinates tl hd V e p b) :=
    Subtype.ext h1
  rw [hemisphereChartField, ← h2, inv_mul_cancel_right]
theorem hemisphereChartField_mem_image_iff (tl hd : κ → Option ι) (V : κ → UnitQuaternion)
    (e : S →ₗ[ℝ] (κ → imaginaryQuaternions)) {A : Set ((ι → imaginaryQuaternions) × S)}
    (hA : A ⊆ positiveDomain tl hd V e) {y : κ → imaginaryQuaternions} (hy : ∀ b, ‖y b‖ < 1) :
    hemisphereChartField V y ∈ transformedChartField tl hd V e '' A ↔ y ∈ bondCoordinates tl hd V e '' A := by
  constructor
  · rintro ⟨p, hp, hpy⟩
    refine ⟨p, hp, ?_⟩
    funext b
    have h1 : bondQuaternion tl hd V e p b = hemispherePoint (y b) := by
      rw [← coe_transformedChartField_mul_inv tl hd V e (hA hp).1 b, hpy]
      simp only [hemisphereChartField, mul_inv_cancel_right]
      exact coe_hemisphereUnit (hy b).le
    rw [bondCoordinates, h1, imaginaryPart_hemispherePoint]
  · rintro ⟨p, hp, rfl⟩
    exact ⟨p, hp, (bondCoordinates_of_mem_positiveDomain tl hd V e (hA hp)).2⟩
theorem le_of_forall_pos_le_add_mul {a c D : ℝ≥0∞} (hD : D ≠ ⊤)
    (h : ∀ η : ℝ, 0 < η → a ≤ c + D * ENNReal.ofReal η) : a ≤ c := by
  refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
  set d := D.toReal with hd
  have hd0 : 0 ≤ d := ENNReal.toReal_nonneg
  have hη : 0 < (ε : ℝ) / (d + 1) := div_pos (by exact_mod_cast hε) (by linarith)
  refine (h _ hη).trans ?_
  gcongr
  have hDd : D = ENNReal.ofReal d := (ENNReal.ofReal_toReal hD).symm
  rw [hDd, ← ENNReal.ofReal_mul hd0]
  have h1 : d * ((ε : ℝ) / (d + 1)) ≤ ε := by
    rw [mul_div_assoc', div_le_iff₀ (by linarith)]
    nlinarith
  calc ENNReal.ofReal (d * ((ε : ℝ) / (d + 1))) ≤ ENNReal.ofReal ε := ENNReal.ofReal_le_ofReal h1
    _ = ε := ENNReal.ofReal_coe_nnreal
variable [MeasurableSpace S] [BorelSpace S]
section AreaFormula
variable {E W : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E]
  [BorelSpace E] [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W] [MeasurableSpace W] [BorelSpace W]
theorem exists_areaFormula_constant (lamE : Measure E) [lamE.IsAddHaarMeasure] (lamV : Measure W)
    [lamV.IsAddHaarMeasure] (L : E ≃L[ℝ] W) :
    ∃ a : ℝ≥0∞, a ≠ 0 ∧ a ≠ ⊤ ∧ ∀ (T : W → W) (A : Set E), MeasurableSet A →
      (∀ p ∈ A, DifferentiableAt ℝ T (L p)) → InjOn (fun p => T (L p)) A → ∀ ρ : W → ℝ≥0∞,
        ∫⁻ y in (fun p => T (L p)) '' A, ρ y ∂lamV =
          a * ∫⁻ p in A, ENNReal.ofReal |(fderiv ℝ T (L p)).det| * ρ (T (L p)) ∂lamE := by
  have hH : (lamE.map L).IsAddHaarMeasure := L.isAddHaarMeasure_map lamE
  have hs := Measure.isAddLeftInvariant_eq_smul (lamE.map L) lamV
  set a' := Measure.addHaarScalarFactor (lamE.map L) lamV with ha'
  have ha0 : a' ≠ 0 := (Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure _ _).ne'
  refine ⟨(a' : ℝ≥0∞)⁻¹, ENNReal.inv_ne_zero.mpr ENNReal.coe_ne_top, ENNReal.inv_ne_top.mpr (by exact_mod_cast ha0),
    fun T A hA hT hinj ρ => ?_⟩
  have hemb : MeasurableEmbedding L := L.toHomeomorph.measurableEmbedding
  set LA : Set W := L '' A with hLA
  have hLAm : MeasurableSet LA := hemb.measurableSet_image.mpr hA
  have himg : (fun p => T (L p)) '' A = T '' LA := by
    rw [hLA, image_image]
  have hinj' : InjOn T LA := by
    rintro _ ⟨p, hp, rfl⟩ _ ⟨q, hq, rfl⟩ h
    rw [hinj hp hq h]
  have hder : ∀ x ∈ LA, HasFDerivWithinAt T (fderiv ℝ T x) LA x := by
    rintro _ ⟨p, hp, rfl⟩
    exact (hT p hp).hasFDerivAt.hasFDerivWithinAt
  rw [himg, lintegral_image_eq_lintegral_abs_det_fderiv_mul lamV hLAm hder hinj' ρ]
  set F : W → ℝ≥0∞ := fun x => ENNReal.ofReal |(fderiv ℝ T x).det| * ρ (T x) with hF
  have h1 : ∫⁻ p in A, F (L p) ∂lamE = (a' : ℝ≥0∞) * ∫⁻ x in LA, F x ∂lamV := by
    have hpre : L ⁻¹' LA = A := by
      rw [hLA]
      exact L.injective.preimage_image A
    have h2 : ∫⁻ x in LA, F x ∂(lamE.map L) = ∫⁻ p in L ⁻¹' LA, F (L p) ∂lamE := by
      rw [hemb.restrict_map, hemb.lintegral_map]
    rw [hpre] at h2
    rw [← h2]
    conv_lhs => rw [hs]
    rw [Measure.restrict_smul, lintegral_smul_measure]
    rfl
  show _ = _ * ∫⁻ p in A, F (L p) ∂lamE
  rw [h1, ← mul_assoc, ENNReal.inv_mul_cancel (by exact_mod_cast ha0) ENNReal.coe_ne_top, one_mul]
end AreaFormula
private instance : SecondCountableTopology UnitQuaternion := TopologicalSpace.Subtype.secondCountableTopology _
private theorem haarUnit_eq_of_isMulLeftInvariant (μ : Measure UnitQuaternion) [IsProbabilityMeasure μ]
    [μ.IsMulLeftInvariant] : μ = haarUnit := by apply _root_.YangMills.Construction.WeightedResponses.eq_haarUnit_of_isMulLeftInvariant <;> assumption
private instance : haarUnit.IsMulRightInvariant := by
  constructor
  intro g
  have : (Measure.map (· * g) haarUnit).IsMulLeftInvariant := isMulLeftInvariant_map_mul_right g
  have : IsProbabilityMeasure (Measure.map (· * g) haarUnit) :=
    Measure.isProbabilityMeasure_map (measurable_mul_const g).aemeasurable
  exact haarUnit_eq_of_isMulLeftInvariant _
omit [DecidableEq ι] [DecidableEq κ] in
theorem measurePreserving_gaugeTransform (tl hd : κ → Option ι) (g : ι → UnitQuaternion) :
    MeasurePreserving (gaugeTransform tl hd g) (Measure.pi fun _ : κ => haarUnit)
      (Measure.pi fun _ : κ => haarUnit) :=
  measurePreserving_pi _ _ fun b =>
    (measurePreserving_mul_right haarUnit (gaugeAtEnd g (hd b))⁻¹).comp
      (measurePreserving_mul_left haarUnit (gaugeAtEnd g (tl b)))
omit [DecidableEq ι] [DecidableEq κ] in
theorem continuous_gaugeTransform_chart (tl hd : κ → Option ι) (V : κ → UnitQuaternion)
    (e : S →ₗ[ℝ] (κ → imaginaryQuaternions)) {Z : Set S} (hZ1 : ∀ ζ ∈ Z, ∀ b, ‖e ζ b‖ < 1) :
    Continuous fun p : (ι → UnitQuaternion) × Z => gaugeTransform tl hd p.1 (hemisphereChartField V (e p.2)) := by
  have hce : Continuous e := e.continuous_of_finiteDimensional
  refine continuous_pi fun b => ?_
  have h1 : Continuous fun p : (ι → UnitQuaternion) × Z => gaugeAtEnd p.1 (tl b) :=
    (continuous_gaugeAtEnd _).comp continuous_fst
  have h2 : Continuous fun p : (ι → UnitQuaternion) × Z => gaugeAtEnd p.1 (hd b) :=
    (continuous_gaugeAtEnd _).comp continuous_fst
  have h3 : Continuous fun p : (ι → UnitQuaternion) × Z => hemisphereUnit (e p.2.1 b) := by
    refine continuousOn_hemisphereUnit.comp_continuous ?_ fun p => (hZ1 p.2.1 p.2.2 b).le
    exact (continuous_apply b).comp (hce.comp (continuous_subtype_val.comp continuous_snd))
  exact (h1.mul (h3.mul continuous_const)).mul h2.inv
theorem orbit_measure_decomposition (hD : GroupActions.FreeOrbitMeasureIsProduct) (tl hd : κ → Option ι)
    (V : κ → UnitQuaternion) (e : S →ₗ[ℝ] (κ → imaginaryQuaternions))
    {Z : Set S} (hZ : IsCompact Z) (hZ1 : ∀ ζ ∈ Z, ∀ b, ‖e ζ b‖ < 1)
    (hinj : InjOn (fun p : (ι → UnitQuaternion) × S => gaugeTransform tl hd p.1 (hemisphereChartField V (e p.2)))
      (univ ×ˢ Z)) :
    MeasurableEmbedding (fun p : (ι → UnitQuaternion) × Z => gaugeTransform tl hd p.1 (hemisphereChartField V (e p.2))) ∧
    ∃ ν : Measure Z, IsFiniteMeasure ν ∧ ∀ f : (κ → UnitQuaternion) → ℝ≥0∞, Measurable f →
      ∫⁻ w in range (fun p : (ι → UnitQuaternion) × Z => gaugeTransform tl hd p.1 (hemisphereChartField V (e p.2))),
          f w ∂(Measure.pi fun _ : κ => haarUnit) =
        ∫⁻ g, ∫⁻ z : Z, f (gaugeTransform tl hd g (hemisphereChartField V (e z))) ∂ν
          ∂(Measure.pi fun _ : ι => haarUnit) := by
  have hcs : CompactSpace Z := isCompact_iff_compactSpace.mp hZ
  have hemb : MeasurableEmbedding
      (fun p : (ι → UnitQuaternion) × Z => gaugeTransform tl hd p.1 (hemisphereChartField V (e p.2))) := by
    refine ((_root_.YangMills.Construction.GaugeCharts.OrbitChart.continuous_gaugeTransform_chart tl hd V e hZ1).isClosedEmbedding ?_).measurableEmbedding
    rintro ⟨g, z⟩ ⟨g', z'⟩ h
    have h' : gaugeTransform tl hd g (hemisphereChartField V (e z.1)) =
        gaugeTransform tl hd g' (hemisphereChartField V (e z'.1)) := h
    have := hinj (show (g, z.1) ∈ (univ : Set (ι → UnitQuaternion)) ×ˢ Z from ⟨mem_univ _, z.2⟩)
      (show (g', z'.1) ∈ (univ : Set (ι → UnitQuaternion)) ×ˢ Z from ⟨mem_univ _, z'.2⟩) h'
    have h1 : g = g' := congrArg Prod.fst this
    have h2 : z.1 = z'.1 := congrArg Prod.snd this
    exact Prod.ext h1 (Subtype.ext h2)
  refine ⟨hemb, ?_⟩
  have i1 : (Measure.pi fun _ : ι => haarUnit).IsHaarMeasure := inferInstance
  have i2 : IsProbabilityMeasure (Measure.pi fun _ : ι => haarUnit) := inferInstance
  have i3 : IsFiniteMeasure (Measure.pi fun _ : κ => haarUnit) := inferInstance
  have hh := hD (ι → UnitQuaternion) (κ → UnitQuaternion) Z (Measure.pi fun _ : ι => haarUnit)
    (Measure.pi fun _ : κ => haarUnit) (gaugeTransform tl hd)
    (fun z => hemisphereChartField V (e z)) (fun k l x => _root_.YangMills.Construction.GaugeCharts.gaugeTransform_gaugeTransform tl hd k l x)
    (fun k => _root_.YangMills.Construction.GaugeCharts.OrbitChart.measurePreserving_gaugeTransform tl hd k) hemb
  exact hh
def smallGaugeForms (ι : Type) (ε : ℝ) : Set (ι → imaginaryQuaternions) := {χ | ∀ z, ‖χ z‖ < ε}
theorem gaugeOfForm_injective_of_norm_lt_one {χ χ' : ι → imaginaryQuaternions} (hχ : ∀ z, ‖χ z‖ < 1)
    (hχ' : ∀ z, ‖χ' z‖ < 1) (h : gaugeOfForm χ = gaugeOfForm χ') : χ = χ' := by
  funext z
  have h1 : hemispherePoint (χ z) = hemispherePoint (χ' z) := by
    rw [← coe_hemisphereUnit (hχ z).le, ← coe_hemisphereUnit (hχ' z).le]
    exact congrArg (fun g : ι → UnitQuaternion => ((g z : UnitQuaternion) : ℍ[ℝ])) h
  have := congrArg imaginaryPart h1
  rwa [imaginaryPart_hemispherePoint, imaginaryPart_hemispherePoint] at this
theorem image_gaugeOfForm_smallGaugeForms {ε : ℝ} (hε : ε ≤ 1) :
    gaugeOfForm '' smallGaugeForms ι ε = {g : ι → UnitQuaternion | ∀ z, 0 < ((g z : UnitQuaternion) : ℍ[ℝ]).re ∧
      ‖imaginaryPart ((g z : UnitQuaternion) : ℍ[ℝ])‖ < ε} := by
  ext g
  constructor
  · rintro ⟨χ, hχ, rfl⟩ z
    have h1 : ‖χ z‖ < 1 := (hχ z).trans_le hε
    simp only [gaugeOfForm]
    rw [coe_hemisphereUnit h1.le, re_hemispherePoint, imaginaryPart_hemispherePoint]
    exact ⟨Real.sqrt_pos.mpr (by nlinarith [norm_nonneg (χ z)]), hχ z⟩
  · intro hg
    refine ⟨fun z => imaginaryPart ((g z : UnitQuaternion) : ℍ[ℝ]), fun z => (hg z).2, ?_⟩
    funext z
    have h := hemispherePoint_imaginaryPart (norm_unitQuaternion (g z)) (hg z).1
    apply Subtype.ext
    simp only [gaugeOfForm]
    rw [coe_hemisphereUnit h.1.le, h.2]
theorem measurableSet_image_gaugeOfForm {ε : ℝ} (hε : ε ≤ 1) :
    MeasurableSet (gaugeOfForm '' smallGaugeForms ι ε) := by
  rw [image_gaugeOfForm_smallGaugeForms hε]
  refine IsOpen.measurableSet ?_
  simp only [setOf_forall]
  refine isOpen_iInter_of_finite fun z => ?_
  have hc : Continuous fun g : ι → UnitQuaternion => ((g z : UnitQuaternion) : ℍ[ℝ]) :=
    continuous_subtype_val.comp (continuous_apply z)
  have hi : Continuous fun q : ℍ[ℝ] => imaginaryPart q := imaginaryPartCLM.continuous
  exact (isOpen_lt continuous_const (Quaternion.continuous_re.comp hc)).inter
    (isOpen_lt (hi.comp hc).norm continuous_const)
variable [MeasurableSpace imaginaryQuaternions] [BorelSpace imaginaryQuaternions]
theorem measurableSet_smallGaugeForms (ε : ℝ) : MeasurableSet (smallGaugeForms ι ε) := by
  have : IsOpen (smallGaugeForms ι ε) := by
    simp only [smallGaugeForms, setOf_forall]
    exact isOpen_iInter_of_finite fun z => isOpen_lt (by fun_prop) continuous_const
  exact this.measurableSet
theorem haar_image_gaugeOfForm {c : ℝ} (μ₃ : Measure imaginaryQuaternions)
    (hc : ∀ (V : ι → UnitQuaternion) (Φ : (ι → UnitQuaternion) → ℝ≥0∞), Measurable Φ →
      ∫⁻ w in {w : ι → UnitQuaternion | ∀ b, 0 < ((w b * (V b)⁻¹ : UnitQuaternion) : ℍ[ℝ]).re}, Φ w
          ∂(Measure.pi fun _ : ι => haarUnit) =
        ENNReal.ofReal c * ∫⁻ y in {y : ι → imaginaryQuaternions | ∀ b, ‖y b‖ < 1},
          Φ (hemisphereChartField V y) * ENNReal.ofReal (∏ b, hemisphereDensity (y b)) ∂(Measure.pi fun _ : ι => μ₃))
    {ε : ℝ} (hε : ε ≤ 1) :
    (Measure.pi fun _ : ι => haarUnit) (gaugeOfForm '' smallGaugeForms ι ε) =
      ENNReal.ofReal c * ∫⁻ χ in smallGaugeForms ι ε, ENNReal.ofReal (∏ z, hemisphereDensity (χ z))
        ∂(Measure.pi fun _ : ι => μ₃) := by
  have hW := measurableSet_image_gaugeOfForm (ι := ι) hε
  have h := hc 1 _ (measurable_one.indicator hW)
  have hBm : MeasurableSet {y : ι → imaginaryQuaternions | ∀ b, ‖y b‖ < 1} := by
    have : IsOpen {y : ι → imaginaryQuaternions | ∀ b, ‖y b‖ < 1} := by
      simp only [setOf_forall]
      exact isOpen_iInter_of_finite fun z => isOpen_lt (by fun_prop) continuous_const
    exact this.measurableSet
  have hsub : gaugeOfForm '' smallGaugeForms ι ε ⊆
      {w : ι → UnitQuaternion | ∀ b, 0 < ((w b * ((1 : ι → UnitQuaternion) b)⁻¹ : UnitQuaternion) : ℍ[ℝ]).re} := by
    intro g hg z
    rw [image_gaugeOfForm_smallGaugeForms hε] at hg
    simpa using (hg z).1
  have hl : ∫⁻ w in {w : ι → UnitQuaternion | ∀ b, 0 < ((w b * ((1 : ι → UnitQuaternion) b)⁻¹ : UnitQuaternion) :
        ℍ[ℝ]).re}, (gaugeOfForm '' smallGaugeForms ι ε).indicator 1 w ∂(Measure.pi fun _ : ι => haarUnit) =
      (Measure.pi fun _ : ι => haarUnit) (gaugeOfForm '' smallGaugeForms ι ε) := by
    rw [lintegral_indicator_one hW, Measure.restrict_apply hW, inter_eq_left.mpr hsub]
  rw [← hl, h]
  congr 1
  rw [← lintegral_indicator hBm, ← lintegral_indicator (measurableSet_smallGaugeForms ε)]
  refine lintegral_congr fun y => ?_
  have hcf : hemisphereChartField (1 : ι → UnitQuaternion) y = gaugeOfForm y := by
    funext z
    simp [hemisphereChartField, gaugeOfForm]
  by_cases hy : y ∈ smallGaugeForms ι ε
  · have hy1 : y ∈ {y : ι → imaginaryQuaternions | ∀ b, ‖y b‖ < 1} := fun b => (hy b).trans_le hε
    rw [indicator_of_mem hy1, indicator_of_mem hy, hcf, indicator_of_mem (mem_image_of_mem _ hy)]
    simp
  · rw [indicator_of_notMem hy]
    by_cases hy1 : y ∈ {y : ι → imaginaryQuaternions | ∀ b, ‖y b‖ < 1}
    · rw [indicator_of_mem hy1, hcf]
      have : gaugeOfForm y ∉ gaugeOfForm '' smallGaugeForms ι ε := by
        rintro ⟨χ, hχ, h⟩
        exact hy (gaugeOfForm_injective_of_norm_lt_one (fun z => (hχ z).trans_le hε) hy1 h ▸ hχ)
      rw [indicator_of_notMem this]
      simp
    · rw [indicator_of_notMem hy1]
theorem haar_image_transformedChartField {c : ℝ} (tl hd : κ → Option ι) (V : κ → UnitQuaternion)
    (e : S →ₗ[ℝ] (κ → imaginaryQuaternions)) (μ₃ : Measure imaginaryQuaternions)
    (hc : ∀ (Φ : (κ → UnitQuaternion) → ℝ≥0∞), Measurable Φ →
      ∫⁻ w in {w : κ → UnitQuaternion | ∀ b, 0 < ((w b * (V b)⁻¹ : UnitQuaternion) : ℍ[ℝ]).re}, Φ w
          ∂(Measure.pi fun _ : κ => haarUnit) =
        ENNReal.ofReal c * ∫⁻ y in {y : κ → imaginaryQuaternions | ∀ b, ‖y b‖ < 1},
          Φ (hemisphereChartField V y) * ENNReal.ofReal (∏ b, hemisphereDensity (y b)) ∂(Measure.pi fun _ : κ => μ₃))
    {A : Set ((ι → imaginaryQuaternions) × S)} (hA : A ⊆ positiveDomain tl hd V e)
    (hY : MeasurableSet (transformedChartField tl hd V e '' A)) :
    (Measure.pi fun _ : κ => haarUnit) (transformedChartField tl hd V e '' A) =
      ENNReal.ofReal c * ∫⁻ y in bondCoordinates tl hd V e '' A, ENNReal.ofReal (∏ b, hemisphereDensity (y b))
        ∂(Measure.pi fun _ : κ => μ₃) := by
  have h := hc _ (measurable_one.indicator hY)
  have hBopen : IsOpen {y : κ → imaginaryQuaternions | ∀ b, ‖y b‖ < 1} := by
    simp only [setOf_forall]
    exact isOpen_iInter_of_finite fun z => isOpen_lt (by fun_prop) continuous_const
  have hBm : MeasurableSet {y : κ → imaginaryQuaternions | ∀ b, ‖y b‖ < 1} := hBopen.measurableSet
  have hsub : transformedChartField tl hd V e '' A ⊆
      {w : κ → UnitQuaternion | ∀ b, 0 < ((w b * (V b)⁻¹ : UnitQuaternion) : ℍ[ℝ]).re} := by
    rintro _ ⟨p, hp, rfl⟩ b
    show 0 < ((transformedChartField tl hd V e p b * (V b)⁻¹ : UnitQuaternion) : ℍ[ℝ]).re
    rw [coe_transformedChartField_mul_inv tl hd V e (hA hp).1 b]
    exact (hA hp).2 b
  have hl : ∫⁻ w in {w : κ → UnitQuaternion | ∀ b, 0 < ((w b * (V b)⁻¹ : UnitQuaternion) : ℍ[ℝ]).re},
      (transformedChartField tl hd V e '' A).indicator 1 w ∂(Measure.pi fun _ : κ => haarUnit) =
      (Measure.pi fun _ : κ => haarUnit) (transformedChartField tl hd V e '' A) := by
    rw [lintegral_indicator_one hY, Measure.restrict_apply hY, inter_eq_left.mpr hsub]
  have hCm : Measurable (hemisphereChartField (κ := κ) V) :=
    measurable_pi_lambda _ fun b => (measurable_hemisphereUnit.comp (measurable_pi_apply b)).mul_const _
  have hset : bondCoordinates tl hd V e '' A = {y : κ → imaginaryQuaternions | ∀ b, ‖y b‖ < 1} ∩
      hemisphereChartField V ⁻¹' (transformedChartField tl hd V e '' A) := by
    ext y
    constructor
    · rintro ⟨p, hp, rfl⟩
      have hg := bondCoordinates_of_mem_positiveDomain tl hd V e (hA hp)
      exact ⟨hg.1, (hemisphereChartField_mem_image_iff tl hd V e hA hg.1).mpr ⟨p, hp, rfl⟩⟩
    · rintro ⟨h1, h2⟩
      exact (hemisphereChartField_mem_image_iff tl hd V e hA h1).mp h2
  rw [← hl, h]
  congr 1
  rw [hset, ← lintegral_indicator hBm, ← lintegral_indicator (hBm.inter (hCm hY))]
  refine lintegral_congr fun y => ?_
  by_cases hy1 : y ∈ {y : κ → imaginaryQuaternions | ∀ b, ‖y b‖ < 1}
  · rw [indicator_of_mem hy1]
    by_cases hy2 : hemisphereChartField V y ∈ transformedChartField tl hd V e '' A
    · have hy3 : y ∈ {y : κ → imaginaryQuaternions | ∀ b, ‖y b‖ < 1} ∩
          hemisphereChartField V ⁻¹' (transformedChartField tl hd V e '' A) := ⟨hy1, hy2⟩
      rw [indicator_of_mem hy2, indicator_of_mem hy3]
      simp
    · rw [indicator_of_notMem hy2, indicator_of_notMem (fun h => hy2 h.2)]
      simp
  · rw [indicator_of_notMem hy1, indicator_of_notMem (fun h => hy1 h.1)]
theorem isOpen_image_gaugeOfForm {ε : ℝ} (hε : ε ≤ 1) : IsOpen (gaugeOfForm '' smallGaugeForms ι ε) := by
  rw [image_gaugeOfForm_smallGaugeForms hε]
  simp only [setOf_forall]
  refine isOpen_iInter_of_finite fun z => ?_
  have hc : Continuous fun g : ι → UnitQuaternion => ((g z : UnitQuaternion) : ℍ[ℝ]) :=
    continuous_subtype_val.comp (continuous_apply z)
  have hi : Continuous fun q : ℍ[ℝ] => imaginaryPart q := imaginaryPartCLM.continuous
  exact (isOpen_lt continuous_const (Quaternion.continuous_re.comp hc)).inter
    (isOpen_lt (hi.comp hc).norm continuous_const)
theorem measurable_hemisphereDensity : Measurable hemisphereDensity := by
  have : Continuous fun y : imaginaryQuaternions => 1 - ‖y‖ ^ 2 := by fun_prop
  exact (this.measurable.sqrt).inv
def densityProduct {ι : Type} [Fintype ι] (χ : ι → imaginaryQuaternions) : ℝ := ∏ z, hemisphereDensity (χ z)
omit [DecidableEq ι] in
theorem measurable_densityProduct : Measurable (densityProduct (ι := ι)) :=
  Finset.measurable_prod _ fun z _ => measurable_hemisphereDensity.comp (measurable_pi_apply z)
theorem le_of_mul_le_mul_left_of_ne {I x y : ℝ≥0∞} (h0 : I ≠ 0) (ht : I ≠ ⊤) (h : I * x ≤ I * y) : x ≤ y := by
  calc x = I⁻¹ * (I * x) := by rw [← mul_assoc, ENNReal.inv_mul_cancel h0 ht, one_mul]
    _ ≤ I⁻¹ * (I * y) := by gcongr
    _ = y := by rw [← mul_assoc, ENNReal.inv_mul_cancel h0 ht, one_mul]
theorem two_sided_bounds_of_product {I X R₀ v C₁ C₂ Y₀ o : ℝ≥0∞} (hI0 : I ≠ 0) (hIt : I ≠ ⊤)
    (hmain : I * (C₁ * X) = C₂ * Y₀) (hup : Y₀ ≤ I * (R₀ + v * o)) (hlo : I * R₀ ≤ Y₀ + I * (v * o)) :
    C₁ * X ≤ C₂ * R₀ + C₂ * v * o ∧ C₂ * R₀ ≤ C₁ * X + C₂ * v * o := by
  constructor
  · refine le_of_mul_le_mul_left_of_ne hI0 hIt ?_
    rw [hmain]
    calc C₂ * Y₀ ≤ C₂ * (I * (R₀ + v * o)) := by gcongr
      _ = I * (C₂ * R₀ + C₂ * v * o) := by ring
  · refine le_of_mul_le_mul_left_of_ne hI0 hIt ?_
    calc I * (C₂ * R₀) = C₂ * (I * R₀) := by ring
      _ ≤ C₂ * (Y₀ + I * (v * o)) := by gcongr
      _ = C₂ * Y₀ + I * (C₂ * v * o) := by ring
      _ = I * (C₁ * X + C₂ * v * o) := by rw [← hmain]; ring
theorem product_integral_bounds {P : Type} [MeasurableSpace P] (lamI : Measure P) [SFinite lamI] (μ : Measure S)
    [SFinite μ] {Wc : Set P} {B : Set S} (hW : MeasurableSet Wc) (hB : MeasurableSet B) (r : P → ℝ)
    (hr : Measurable r) (j : P × S → ℝ) (Jf : S → ℝ)
    (hJB : AEMeasurable (fun ζ => ENNReal.ofReal (Jf ζ)) (μ.restrict B))
    {η : ℝ} (hnear : ∀ p ∈ Wc ×ˢ B, |j p - Jf p.2| < η) :
    ∫⁻ p in Wc ×ˢ B, ENNReal.ofReal (j p) * ENNReal.ofReal (r p.1) ∂(lamI.prod μ) ≤
        (∫⁻ χ in Wc, ENNReal.ofReal (r χ) ∂lamI) * ((∫⁻ ζ in B, ENNReal.ofReal (Jf ζ) ∂μ) + μ B * ENNReal.ofReal η) ∧
      (∫⁻ χ in Wc, ENNReal.ofReal (r χ) ∂lamI) * (∫⁻ ζ in B, ENNReal.ofReal (Jf ζ) ∂μ) ≤
        (∫⁻ p in Wc ×ˢ B, ENNReal.ofReal (j p) * ENNReal.ofReal (r p.1) ∂(lamI.prod μ)) +
          (∫⁻ χ in Wc, ENNReal.ofReal (r χ) ∂lamI) * (μ B * ENNReal.ofReal η) := by
  have hAm : MeasurableSet (Wc ×ˢ B) := hW.prod hB
  have hrm : Measurable fun χ => ENNReal.ofReal (r χ) := ENNReal.measurable_ofReal.comp hr
  have hfac : ∀ F : S → ℝ≥0∞, AEMeasurable F (μ.restrict B) →
      ∫⁻ p in Wc ×ˢ B, ENNReal.ofReal (r p.1) * F p.2 ∂(lamI.prod μ) =
        (∫⁻ χ in Wc, ENNReal.ofReal (r χ) ∂lamI) * ∫⁻ ζ in B, F ζ ∂μ := by
    intro F hFm
    rw [← Measure.prod_restrict]
    exact lintegral_prod_mul (f := fun χ => ENNReal.ofReal (r χ)) hrm.aemeasurable hFm
  have hconst : ∫⁻ p in Wc ×ˢ B, ENNReal.ofReal (r p.1) * ENNReal.ofReal η ∂(lamI.prod μ) =
      (∫⁻ χ in Wc, ENNReal.ofReal (r χ) ∂lamI) * (μ B * ENNReal.ofReal η) := by
    rw [hfac (fun _ => ENNReal.ofReal η) aemeasurable_const, setLIntegral_const, mul_comm (ENNReal.ofReal η)]
  constructor
  · have h1 : ∫⁻ p in Wc ×ˢ B, ENNReal.ofReal (j p) * ENNReal.ofReal (r p.1) ∂(lamI.prod μ) ≤
        ∫⁻ p in Wc ×ˢ B, ENNReal.ofReal (r p.1) * (ENNReal.ofReal (Jf p.2) + ENNReal.ofReal η) ∂(lamI.prod μ) := by
      refine setLIntegral_mono' hAm fun p hp => ?_
      rw [mul_comm]
      have h2 := (abs_lt.mp (hnear p hp)).2
      have h3 : ENNReal.ofReal (j p) ≤ ENNReal.ofReal (Jf p.2) + ENNReal.ofReal η :=
        (ENNReal.ofReal_le_ofReal (by linarith : j p ≤ Jf p.2 + η)).trans ENNReal.ofReal_add_le
      gcongr
    refine h1.trans (le_of_eq ?_)
    have hadd : AEMeasurable (fun ζ => ENNReal.ofReal (Jf ζ) + ENNReal.ofReal η) (μ.restrict B) :=
      hJB.add aemeasurable_const
    rw [hfac (fun ζ => ENNReal.ofReal (Jf ζ) + ENNReal.ofReal η) hadd, lintegral_add_right _ measurable_const,
      setLIntegral_const, mul_comm (ENNReal.ofReal η)]
  · have hmeas : Measurable fun p : P × S => ENNReal.ofReal (r p.1) * ENNReal.ofReal η :=
      (hrm.comp measurable_fst).mul_const _
    have h1 : (∫⁻ χ in Wc, ENNReal.ofReal (r χ) ∂lamI) * (∫⁻ ζ in B, ENNReal.ofReal (Jf ζ) ∂μ) ≤
        ∫⁻ p in Wc ×ˢ B, (ENNReal.ofReal (j p) * ENNReal.ofReal (r p.1) +
          ENNReal.ofReal (r p.1) * ENNReal.ofReal η) ∂(lamI.prod μ) := by
      rw [← hfac _ hJB]
      refine setLIntegral_mono' hAm fun p hp => ?_
      have h2 := (abs_lt.mp (hnear p hp)).1
      have h3 : ENNReal.ofReal (Jf p.2) ≤ ENNReal.ofReal (j p) + ENNReal.ofReal η :=
        (ENNReal.ofReal_le_ofReal (by linarith : Jf p.2 ≤ j p + η)).trans ENNReal.ofReal_add_le
      calc ENNReal.ofReal (r p.1) * ENNReal.ofReal (Jf p.2)
          ≤ ENNReal.ofReal (r p.1) * (ENNReal.ofReal (j p) + ENNReal.ofReal η) := by gcongr
        _ = _ := by ring
    refine h1.trans (le_of_eq ?_)
    rw [lintegral_add_right _ hmeas, hconst]
abbrev orbitMap (tl hd : κ → Option ι) (V : κ → UnitQuaternion) (e : S →ₗ[ℝ] (κ → imaginaryQuaternions))
    (Z : Set S) : (ι → UnitQuaternion) × Z → (κ → UnitQuaternion) :=
  fun p => gaugeTransform tl hd p.1 (hemisphereChartField V (e p.2))
theorem haar_image_orbitMap_prod (tl hd : κ → Option ι) (V : κ → UnitQuaternion)
    (e : S →ₗ[ℝ] (κ → imaginaryQuaternions)) {Z : Set S}
    (hemb : MeasurableEmbedding (orbitMap tl hd V e Z)) (ν : Measure Z)
    (hν : ∀ f : (κ → UnitQuaternion) → ℝ≥0∞, Measurable f →
      ∫⁻ w in range (orbitMap tl hd V e Z), f w ∂(Measure.pi fun _ : κ => haarUnit) =
        ∫⁻ g, ∫⁻ z : Z, f (gaugeTransform tl hd g (hemisphereChartField V (e z))) ∂ν
          ∂(Measure.pi fun _ : ι => haarUnit))
    {W' : Set (ι → UnitQuaternion)} (hW'm : MeasurableSet W') {Bt : Set Z} (hBtm : MeasurableSet Bt) :
    (Measure.pi fun _ : κ => haarUnit) (orbitMap tl hd V e Z '' (W' ×ˢ Bt)) =
      (Measure.pi fun _ : ι => haarUnit) W' * ν Bt := by
  have hYm : MeasurableSet (orbitMap tl hd V e Z '' (W' ×ˢ Bt)) := hemb.measurableSet_image.mpr (hW'm.prod hBtm)
  have h1 := hν ((orbitMap tl hd V e Z '' (W' ×ˢ Bt)).indicator 1) (measurable_one.indicator hYm)
  rw [lintegral_indicator_one hYm, Measure.restrict_apply hYm,
    inter_eq_left.mpr (image_subset_range _ _)] at h1
  rw [h1]
  have hin : ∀ g, ∫⁻ z : Z, (orbitMap tl hd V e Z '' (W' ×ˢ Bt)).indicator 1
      (gaugeTransform tl hd g (hemisphereChartField V (e z))) ∂ν = W'.indicator (fun _ => ν Bt) g := by
    intro g
    by_cases hg : g ∈ W'
    · rw [indicator_of_mem hg, ← lintegral_indicator_one hBtm]
      refine lintegral_congr fun z => ?_
      by_cases hz : z ∈ Bt
      · have hmem : gaugeTransform tl hd g (hemisphereChartField V (e z)) ∈ orbitMap tl hd V e Z '' (W' ×ˢ Bt) :=
          ⟨(g, z), ⟨hg, hz⟩, rfl⟩
        rw [indicator_of_mem hmem, indicator_of_mem hz]
        rfl
      · have hmem : gaugeTransform tl hd g (hemisphereChartField V (e z)) ∉ orbitMap tl hd V e Z '' (W' ×ˢ Bt) := by
          rintro ⟨q, hq, hqe⟩
          have : q = (g, z) := hemb.injective hqe
          rw [this] at hq
          exact hz hq.2
        rw [indicator_of_notMem hmem, indicator_of_notMem hz]
    · rw [indicator_of_notMem hg]
      have hz0 : ∀ z : Z, (orbitMap tl hd V e Z '' (W' ×ˢ Bt)).indicator (1 : (κ → UnitQuaternion) → ℝ≥0∞)
          (gaugeTransform tl hd g (hemisphereChartField V (e z))) = 0 := by
        intro z
        refine indicator_of_notMem ?_ _
        rintro ⟨q, hq, hqe⟩
        have : q = (g, z) := hemb.injective hqe
        rw [this] at hq
        exact hg hq.1
      simp only [hz0, lintegral_zero]
  simp only [hin]
  rw [lintegral_indicator hW'm, setLIntegral_const, mul_comm]
theorem image_transformedChartField_eq_orbitMap (tl hd : κ → Option ι) (V : κ → UnitQuaternion)
    (e : S →ₗ[ℝ] (κ → imaginaryQuaternions)) {Z B : Set S} (hBZ : B ⊆ Z) (Wc : Set (ι → imaginaryQuaternions)) :
    transformedChartField tl hd V e '' (Wc ×ˢ B) =
      orbitMap tl hd V e Z '' ((gaugeOfForm '' Wc) ×ˢ (Subtype.val ⁻¹' B)) := by
  ext w
  constructor
  · rintro ⟨⟨χ, ζ⟩, ⟨hχ, hζ⟩, rfl⟩
    exact ⟨(gaugeOfForm χ, ⟨ζ, hBZ hζ⟩), ⟨mem_image_of_mem _ hχ, hζ⟩, rfl⟩
  · rintro ⟨⟨g, z⟩, ⟨⟨χ, hχ, rfl⟩, hz⟩, rfl⟩
    exact ⟨(χ, z.1), ⟨hχ, hz⟩, rfl⟩
theorem injOn_bondCoordinates (tl hd : κ → Option ι) (V : κ → UnitQuaternion)
    (e : S →ₗ[ℝ] (κ → imaginaryQuaternions)) {Z : Set S}
    (hinj : InjOn (fun p : (ι → UnitQuaternion) × S => gaugeTransform tl hd p.1 (hemisphereChartField V (e p.2)))
      (univ ×ˢ Z))
    {A : Set ((ι → imaginaryQuaternions) × S)} (hAG : A ⊆ positiveDomain tl hd V e) (hAZ : ∀ p ∈ A, p.2 ∈ Z) :
    InjOn (bondCoordinates tl hd V e) A := by
  rintro ⟨χ, ζ⟩ hp ⟨χ', ζ'⟩ hp' h
  have g1 := (bondCoordinates_of_mem_positiveDomain tl hd V e (hAG hp)).2
  have g2 := (bondCoordinates_of_mem_positiveDomain tl hd V e (hAG hp')).2
  have hw : transformedChartField tl hd V e (χ, ζ) = transformedChartField tl hd V e (χ', ζ') := by rw [g1, g2, h]
  have := hinj (show (gaugeOfForm χ, ζ) ∈ (univ : Set (ι → UnitQuaternion)) ×ˢ Z from ⟨mem_univ _, hAZ _ hp⟩)
    (show (gaugeOfForm χ', ζ') ∈ (univ : Set (ι → UnitQuaternion)) ×ˢ Z from ⟨mem_univ _, hAZ _ hp'⟩) hw
  have h1 : gaugeOfForm χ = gaugeOfForm χ' := congrArg Prod.fst this
  have h2 : ζ = ζ' := congrArg Prod.snd this
  have h3 : χ = χ' := gaugeOfForm_injective_of_norm_lt_one (hAG hp).1.1 (hAG hp').1.1 h1
  rw [h3, h2]
theorem orbit_measure_bounds (tl hd : κ → Option ι) (V : κ → UnitQuaternion) (e : S →ₗ[ℝ] (κ → imaginaryQuaternions))
    {Z : Set S} (hZ : IsCompact Z) (hZ1 : ∀ ζ ∈ Z, ∀ b, ‖e ζ b‖ < 1)
    (hinj : InjOn (fun p : (ι → UnitQuaternion) × S => gaugeTransform tl hd p.1 (hemisphereChartField V (e p.2)))
      (univ ×ˢ Z))
    (μ₃ : Measure imaginaryQuaternions) (μ : Measure S) [SigmaFinite μ₃] [SFinite μ]
    {cκ cι : ℝ} (hcι : 0 < cι) (hF₁ : (Measure.pi fun _ : ι => haarUnit).IsHaarMeasure)
    (hFκ : ∀ (Φ : (κ → UnitQuaternion) → ℝ≥0∞), Measurable Φ →
      ∫⁻ w in {w : κ → UnitQuaternion | ∀ b, 0 < ((w b * (V b)⁻¹ : UnitQuaternion) : ℍ[ℝ]).re}, Φ w
          ∂(Measure.pi fun _ : κ => haarUnit) =
        ENNReal.ofReal cκ * ∫⁻ y in {y : κ → imaginaryQuaternions | ∀ b, ‖y b‖ < 1},
          Φ (hemisphereChartField V y) * ENNReal.ofReal (∏ b, hemisphereDensity (y b)) ∂(Measure.pi fun _ : κ => μ₃))
    (hFι : ∀ (V : ι → UnitQuaternion) (Φ : (ι → UnitQuaternion) → ℝ≥0∞), Measurable Φ →
      ∫⁻ w in {w : ι → UnitQuaternion | ∀ b, 0 < ((w b * (V b)⁻¹ : UnitQuaternion) : ℍ[ℝ]).re}, Φ w
          ∂(Measure.pi fun _ : ι => haarUnit) =
        ENNReal.ofReal cι * ∫⁻ y in {y : ι → imaginaryQuaternions | ∀ b, ‖y b‖ < 1},
          Φ (hemisphereChartField V y) * ENNReal.ofReal (∏ b, hemisphereDensity (y b)) ∂(Measure.pi fun _ : ι => μ₃))
    (hemb : MeasurableEmbedding (orbitMap tl hd V e Z)) (ν : Measure Z)
    (hν : ∀ f : (κ → UnitQuaternion) → ℝ≥0∞, Measurable f →
      ∫⁻ w in range (orbitMap tl hd V e Z), f w ∂(Measure.pi fun _ : κ => haarUnit) =
        ∫⁻ g, ∫⁻ z : Z, f (gaugeTransform tl hd g (hemisphereChartField V (e z))) ∂ν
          ∂(Measure.pi fun _ : ι => haarUnit))
    (a : ℝ≥0∞) (j₀ : (ι → imaginaryQuaternions) × S → ℝ)
    (harea : ∀ A : Set ((ι → imaginaryQuaternions) × S), MeasurableSet A → A ⊆ positiveDomain tl hd V e →
      InjOn (bondCoordinates tl hd V e) A →
      ∫⁻ y in bondCoordinates tl hd V e '' A, ENNReal.ofReal (densityProduct y) ∂(Measure.pi fun _ : κ => μ₃) =
        a * ∫⁻ p in A, ENNReal.ofReal (j₀ p) * ENNReal.ofReal (densityProduct p.1)
          ∂((Measure.pi fun _ : ι => μ₃).prod μ))
    (Jf : S → ℝ) (hJc : ContinuousOn Jf Z) (hOo : ∀ η : ℝ, 0 < η → ∃ ε : ℝ, 0 < ε ∧ ε ≤ 1 ∧
      ∀ χ ζ, (∀ z, ‖χ z‖ < ε) → ζ ∈ Z → (χ, ζ) ∈ positiveDomain tl hd V e ∧ |j₀ (χ, ζ) - Jf ζ| < η)
    {B : Set S} (hBm : MeasurableSet B) (hBZ : B ⊆ Z) {η : ℝ} (hη : 0 < η) :
    ENNReal.ofReal cι * ν (Subtype.val ⁻¹' B) ≤ ENNReal.ofReal cκ * a * (∫⁻ ζ in B, ENNReal.ofReal (Jf ζ) ∂μ) +
        ENNReal.ofReal cκ * a * μ B * ENNReal.ofReal η ∧
      ENNReal.ofReal cκ * a * (∫⁻ ζ in B, ENNReal.ofReal (Jf ζ) ∂μ) ≤ ENNReal.ofReal cι * ν (Subtype.val ⁻¹' B) +
        ENNReal.ofReal cκ * a * μ B * ENNReal.ofReal η := by
  obtain ⟨ε, hε, hε1, hO⟩ := hOo η hη
  have hAO : ∀ p ∈ smallGaugeForms ι ε ×ˢ B, p ∈ positiveDomain tl hd V e ∧ |j₀ p - Jf p.2| < η := by
    rintro ⟨χ, ζ⟩ ⟨hχ, hζ⟩
    exact hO χ ζ hχ (hBZ hζ)
  have hAG : smallGaugeForms ι ε ×ˢ B ⊆ positiveDomain tl hd V e := fun p hp => (hAO p hp).1
  have hAm : MeasurableSet (smallGaugeForms ι ε ×ˢ B) := (measurableSet_smallGaugeForms ε).prod hBm
  have hBtm : MeasurableSet ((Subtype.val ⁻¹' B) : Set Z) := measurable_subtype_coe hBm
  have hW'm : MeasurableSet (gaugeOfForm '' smallGaugeForms ι ε) := measurableSet_image_gaugeOfForm hε1
  have hYeq := image_transformedChartField_eq_orbitMap tl hd V e (Z := Z) hBZ (smallGaugeForms ι ε)
  have hYm : MeasurableSet (transformedChartField tl hd V e '' (smallGaugeForms ι ε ×ˢ B)) := by
    rw [hYeq]
    exact hemb.measurableSet_image.mpr (hW'm.prod hBtm)
  have hY1 := haar_image_orbitMap_prod tl hd V e hemb ν hν hW'm hBtm
  rw [← hYeq] at hY1
  have hinjA := injOn_bondCoordinates tl hd V e hinj hAG (fun p hp => hBZ hp.2)
  have hY2 := haar_image_transformedChartField tl hd V e μ₃ hFκ hAG hYm
  have hrho : ∀ y : κ → imaginaryQuaternions, ENNReal.ofReal (∏ b, hemisphereDensity (y b)) =
      ENNReal.ofReal (densityProduct y) := fun y => rfl
  simp only [hrho] at hY2
  rw [harea _ hAm hAG hinjA] at hY2
  have hμW := haar_image_gaugeOfForm μ₃ hFι (ι := ι) hε1
  have hW'pos : (Measure.pi fun _ : ι => haarUnit) (gaugeOfForm '' smallGaugeForms ι ε) ≠ 0 := by
    have hne : (gaugeOfForm '' smallGaugeForms ι ε).Nonempty := ⟨gaugeOfForm 0, mem_image_of_mem _ fun z => by
      show ‖(0 : ι → imaginaryQuaternions) z‖ < ε
      rw [Pi.zero_apply, norm_zero]
      exact hε⟩
    exact ((isOpen_image_gaugeOfForm hε1).measure_pos _ hne).ne'
  have hC₁0 : ENNReal.ofReal cι ≠ 0 := (ENNReal.ofReal_pos.mpr hcι).ne'
  set I : ℝ≥0∞ := ∫⁻ χ in smallGaugeForms ι ε, ENNReal.ofReal (∏ z, hemisphereDensity (χ z))
    ∂(Measure.pi fun _ : ι => μ₃) with hI
  have hI0 : I ≠ 0 := fun h => hW'pos (by rw [hμW, h, mul_zero])
  have hIt : I ≠ ⊤ := by
    intro h
    have : (Measure.pi fun _ : ι => haarUnit) (gaugeOfForm '' smallGaugeForms ι ε) = ⊤ := by
      rw [hμW, h, ENNReal.mul_top hC₁0]
    exact measure_ne_top _ _ this
  have hJB : AEMeasurable (fun ζ => ENNReal.ofReal (Jf ζ)) (μ.restrict B) :=
    ENNReal.measurable_ofReal.comp_aemeasurable ((hJc.mono hBZ).aemeasurable hBm)
  obtain ⟨hup, hlo⟩ := product_integral_bounds (Measure.pi fun _ : ι => μ₃) μ (measurableSet_smallGaugeForms ε) hBm
    densityProduct measurable_densityProduct j₀ Jf hJB (fun p hp => (hAO p hp).2)
  have hmain : I * (ENNReal.ofReal cι * ν (Subtype.val ⁻¹' B)) =
      ENNReal.ofReal cκ * a * ∫⁻ p in smallGaugeForms ι ε ×ˢ B, ENNReal.ofReal (j₀ p) *
        ENNReal.ofReal (densityProduct p.1) ∂((Measure.pi fun _ : ι => μ₃).prod μ) := by
    rw [mul_assoc (ENNReal.ofReal cκ), ← hY2, hY1, hμW]
    ring
  exact two_sided_bounds_of_product hI0 hIt hmain hup hlo
def linearCoordinates (tl hd : κ → Option ι) (V : κ → UnitQuaternion) (e : S →ₗ[ℝ] (κ → imaginaryQuaternions))
    (Q : (κ → imaginaryQuaternions) →ₗ[ℝ] ((ι → imaginaryQuaternions) × S)) (v : κ → imaginaryQuaternions) :
    κ → imaginaryQuaternions :=
  bondCoordinates tl hd V e (Q v)
def chartDensity (tl hd : κ → Option ι) (V : κ → UnitQuaternion) (e : S →ₗ[ℝ] (κ → imaginaryQuaternions))
    (Q : (κ → imaginaryQuaternions) →ₗ[ℝ] ((ι → imaginaryQuaternions) × S)) (p : (ι → imaginaryQuaternions) × S) : ℝ :=
  |(fderiv ℝ (linearCoordinates tl hd V e Q) (chartLinearization tl hd V e 0 p)).det| *
    densityProduct (bondCoordinates tl hd V e p) / densityProduct p.1
section ChartDensity
variable (tl hd : κ → Option ι) (V : κ → UnitQuaternion) (e : S →ₗ[ℝ] (κ → imaginaryQuaternions))
  (Q : (κ → imaginaryQuaternions) →ₗ[ℝ] ((ι → imaginaryQuaternions) × S))
theorem linearCoordinates_chartLinearization (hQ : ∀ p, Q (chartLinearization tl hd V e 0 p) = p)
    (p : (ι → imaginaryQuaternions) × S) :
    linearCoordinates tl hd V e Q (chartLinearization tl hd V e 0 p) = bondCoordinates tl hd V e p := by
  rw [linearCoordinates, hQ]
theorem contDiffOn_linearCoordinates : ContDiffOn ℝ 1 (linearCoordinates tl hd V e Q) (Q ⁻¹' chartDomain e) :=
  (contDiffOn_bondCoordinates tl hd V e).comp Q.toContinuousLinearMap.contDiff.contDiffOn fun v hv => hv
theorem isOpen_preimage_chartDomain : IsOpen (Q ⁻¹' chartDomain (ι := ι) e) :=
  (isOpen_chartDomain e).preimage Q.continuous_of_finiteDimensional
theorem differentiableAt_linearCoordinates (hQ : ∀ p, Q (chartLinearization tl hd V e 0 p) = p)
    {p : (ι → imaginaryQuaternions) × S} (hp : p ∈ chartDomain e) :
    DifferentiableAt ℝ (linearCoordinates tl hd V e Q) (chartLinearization tl hd V e 0 p) := by
  have hm : chartLinearization tl hd V e 0 p ∈ Q ⁻¹' chartDomain e := by
    show Q (chartLinearization tl hd V e 0 p) ∈ chartDomain e
    rwa [hQ]
  exact ((contDiffOn_linearCoordinates tl hd V e Q).contDiffAt
    ((isOpen_preimage_chartDomain e Q).mem_nhds hm)).differentiableAt one_ne_zero
theorem densityProduct_pos {ι : Type} [Fintype ι] {χ : ι → imaginaryQuaternions} (h : ∀ z, ‖χ z‖ < 1) :
    0 < densityProduct χ :=
  Finset.prod_pos fun z _ => hemisphereDensity_pos (h z)
theorem continuousOn_chartDensity (hQ : ∀ p, Q (chartLinearization tl hd V e 0 p) = p) :
    ContinuousOn (chartDensity tl hd V e Q) (positiveDomain tl hd V e) := by
  have hGd : positiveDomain (ι := ι) tl hd V e ⊆ chartDomain e := fun p hp => hp.1
  have hLc : Continuous (chartLinearization tl hd V e 0) :=
    (chartLinearization tl hd V e 0).continuous_of_finiteDimensional
  have hfc : ContinuousOn (fun p => fderiv ℝ (linearCoordinates tl hd V e Q) (chartLinearization tl hd V e 0 p))
      (chartDomain e) :=
    ((contDiffOn_linearCoordinates tl hd V e Q).continuousOn_fderiv_of_isOpen (isOpen_preimage_chartDomain e Q)
      le_rfl).comp hLc.continuousOn
      fun p hp => by
        show Q (chartLinearization tl hd V e 0 p) ∈ chartDomain e
        rwa [hQ]
  have hPc : ContinuousOn (bondCoordinates (ι := ι) tl hd V e) (chartDomain e) :=
    (contDiffOn_bondCoordinates tl hd V e).continuousOn
  have hrV : ContinuousOn (fun p => densityProduct (bondCoordinates (ι := ι) tl hd V e p))
      (positiveDomain tl hd V e) := by
    refine continuousOn_finset_prod _ fun b _ => continuousOn_hemisphereDensity.comp ?_
      fun p hp => (bondCoordinates_of_mem_positiveDomain tl hd V e hp).1 b
    exact ((continuous_apply b).comp_continuousOn hPc).mono hGd
  have hrI : ContinuousOn (fun p : (ι → imaginaryQuaternions) × S => densityProduct p.1)
      (positiveDomain tl hd V e) := by
    refine continuousOn_finset_prod _ fun z _ => continuousOn_hemisphereDensity.comp ?_ fun p hp => hp.1.1 z
    exact ((continuous_apply z).comp continuous_fst).continuousOn
  exact ((ContinuousLinearMap.continuous_det.comp_continuousOn (hfc.mono hGd)).abs.mul hrV).div hrI
    fun p hp => (densityProduct_pos hp.1.1).ne'
theorem chartDensity_zero_form (hQ : ∀ p, Q (chartLinearization tl hd V e 0 p) = p) {ζ : S}
    (hζ : ∀ b, ‖e ζ b‖ < 1) :
    chartDensity tl hd V e Q ((0 : ι → imaginaryQuaternions), ζ) = chartJacobian tl hd V e Q (e ζ) := by
  have h1 := hasFDerivAt_bondCoordinates_zero_form (ι := ι) tl hd V e hζ
  have h2 : HasFDerivAt (bondCoordinates (ι := ι) tl hd V e) (chartLinearization tl hd V e (e ζ)).toContinuousLinearMap
      (Q.toContinuousLinearMap (chartLinearization tl hd V e 0 ((0 : ι → imaginaryQuaternions), ζ))) := by
    have : Q.toContinuousLinearMap (chartLinearization tl hd V e 0 ((0 : ι → imaginaryQuaternions), ζ)) = (0, ζ) :=
      hQ _
    rw [this]
    exact h1
  have h3 : HasFDerivAt (linearCoordinates tl hd V e Q)
      ((chartLinearization tl hd V e (e ζ)).toContinuousLinearMap.comp Q.toContinuousLinearMap)
      (chartLinearization tl hd V e 0 ((0 : ι → imaginaryQuaternions), ζ)) :=
    h2.comp _ Q.toContinuousLinearMap.hasFDerivAt
  have hr1 : densityProduct (0 : ι → imaginaryQuaternions) = 1 :=
    Finset.prod_eq_one fun z _ => hemisphereDensity_zero
  rw [chartDensity, h3.fderiv, bondCoordinates_zero_form, hr1, div_one]
  rfl
theorem chartDensity_mul {p : (ι → imaginaryQuaternions) × S} (hp : p ∈ positiveDomain tl hd V e) :
    ENNReal.ofReal |(fderiv ℝ (linearCoordinates tl hd V e Q) (chartLinearization tl hd V e 0 p)).det| *
        ENNReal.ofReal (densityProduct (bondCoordinates tl hd V e p)) =
      ENNReal.ofReal (chartDensity tl hd V e Q p) * ENNReal.ofReal (densityProduct p.1) := by
  have hr := densityProduct_pos hp.1.1
  have hrv := densityProduct_pos (bondCoordinates_of_mem_positiveDomain tl hd V e hp).1
  have hjn : 0 ≤ chartDensity tl hd V e Q p := div_nonneg (mul_nonneg (abs_nonneg _) hrv.le) hr.le
  have hmul : chartDensity tl hd V e Q p * densityProduct p.1 =
      |(fderiv ℝ (linearCoordinates tl hd V e Q) (chartLinearization tl hd V e 0 p)).det| *
        densityProduct (bondCoordinates tl hd V e p) := div_mul_cancel₀ _ hr.ne'
  rw [← ENNReal.ofReal_mul (abs_nonneg _), ← ENNReal.ofReal_mul hjn, hmul]
theorem zero_form_mem_positiveDomain {ζ : S} (h : ∀ b, ‖e ζ b‖ < 1) :
    ((0 : ι → imaginaryQuaternions), ζ) ∈ positiveDomain tl hd V e :=
  ⟨⟨fun z => by simp, h⟩, fun b => by
    rw [bondQuaternion_zero_form, re_hemispherePoint]
    exact Real.sqrt_pos.mpr (by nlinarith [norm_nonneg (e ζ b), h b])⟩
theorem exists_small_forms_near_chartDensity (hQ : ∀ p, Q (chartLinearization tl hd V e 0 p) = p) {Z : Set S}
    (hZ : IsCompact Z) (hZ1 : ∀ ζ ∈ Z, ∀ b, ‖e ζ b‖ < 1) {η : ℝ} (hη : 0 < η) :
    ∃ ε : ℝ, 0 < ε ∧ ε ≤ 1 ∧ ∀ (χ : ι → imaginaryQuaternions) ζ, (∀ z, ‖χ z‖ < ε) → ζ ∈ Z →
      (χ, ζ) ∈ positiveDomain tl hd V e ∧
        |chartDensity tl hd V e Q (χ, ζ) - chartJacobian tl hd V e Q (e ζ)| < η := by
  have hjc := continuousOn_chartDensity tl hd V e Q hQ
  have hdc : ContinuousOn (fun p : (ι → imaginaryQuaternions) × S =>
      chartDensity tl hd V e Q p - chartDensity tl hd V e Q (0, p.2)) (positiveDomain tl hd V e) :=
    hjc.sub (hjc.comp (by fun_prop : Continuous fun p : (ι → imaginaryQuaternions) × S =>
      (((0 : ι → imaginaryQuaternions), p.2) : (ι → imaginaryQuaternions) × S)).continuousOn
      fun p hp => zero_form_mem_positiveDomain tl hd V e hp.1.2)
  have hOo := hdc.isOpen_inter_preimage (isOpen_positiveDomain tl hd V e) (isOpen_Ioo (a := -η) (b := η))
  obtain ⟨ε₁, hε₁, hO⟩ := exists_uniform_tube hOo hZ (fun ζ hζ =>
    ⟨zero_form_mem_positiveDomain tl hd V e (hZ1 ζ hζ), by simp [hη]⟩)
  refine ⟨min ε₁ 1, lt_min hε₁ one_pos, min_le_right _ _, fun χ ζ hχ hζ => ?_⟩
  have h := hO χ ζ (fun z => (hχ z).trans_le (min_le_left _ _)) hζ
  refine ⟨h.1, ?_⟩
  have h2 : chartDensity tl hd V e Q (χ, ζ) - chartDensity tl hd V e Q (0, ζ) ∈ Ioo (-η) η := h.2
  rw [chartDensity_zero_form tl hd V e Q hQ (hZ1 ζ hζ)] at h2
  exact abs_lt.mpr h2
end ChartDensity
theorem base_measure_eq_withDensity {Z : Set S} (hZm : MeasurableSet Z) (μ : Measure S) (Jf : S → ℝ)
    (hJm : Measurable fun z : Z => ENNReal.ofReal (Jf z)) {c' : ℝ≥0∞}
    (ν : Measure Z) (hkey : ∀ B : Set S, MeasurableSet B → B ⊆ Z →
      ν (Subtype.val ⁻¹' B) = c' * ∫⁻ ζ in B, ENNReal.ofReal (Jf ζ) ∂μ) :
    ν = c' • (μ.comap (Subtype.val : Z → S)).withDensity fun z => ENNReal.ofReal (Jf z) := by
  refine Measure.ext fun Bt hBt => ?_
  have hBm : MeasurableSet (Subtype.val '' Bt) := MeasurableSet.subtype_image hZm hBt
  have hpre : Subtype.val ⁻¹' (Subtype.val '' Bt) = Bt := Subtype.val_injective.preimage_image Bt
  have hsub : Subtype.val '' Bt ⊆ Z := by
    rintro _ ⟨z, _, rfl⟩
    exact z.2
  have h := hkey _ hBm hsub
  rw [hpre] at h
  have h2 := setLIntegral_subtype (μ := μ) hZm Bt fun ζ => ENNReal.ofReal (Jf ζ)
  rw [h, Measure.smul_apply, withDensity_apply _ hBt, smul_eq_mul, h2]
theorem lintegral_base_measure {Z : Set S} (hZm : MeasurableSet Z) (μ : Measure S) (Jf : S → ℝ)
    (hJm : Measurable fun z : Z => ENNReal.ofReal (Jf z)) (c' : ℝ≥0∞) (F : S → ℝ≥0∞)
    (hFm : Measurable fun z : Z => F z) :
    ∫⁻ z : Z, F z ∂(c' • (μ.comap (Subtype.val : Z → S)).withDensity fun z => ENNReal.ofReal (Jf z)) =
      c' * ∫⁻ ζ in Z, F ζ * ENNReal.ofReal (Jf ζ) ∂μ := by
  rw [lintegral_smul_measure, smul_eq_mul]
  congr 1
  have h1 := lintegral_withDensity_eq_lintegral_mul (μ.comap (Subtype.val : Z → S)) hJm hFm
  have h3 := lintegral_subtype_comap hZm (μ := μ) fun ζ => ENNReal.ofReal (Jf ζ) * F ζ
  refine h1.trans (Eq.trans ?_ (h3.trans ?_))
  · rfl
  · refine lintegral_congr fun ζ => ?_
    rw [mul_comm]
theorem lintegral_orbit_base (tl hd : κ → Option ι) (V : κ → UnitQuaternion) (e : S →ₗ[ℝ] (κ → imaginaryQuaternions))
    {Z : Set S} (hZ : IsCompact Z) (hZ1 : ∀ ζ ∈ Z, ∀ b, ‖e ζ b‖ < 1) (μ : Measure S) (Jf : S → ℝ)
    (hJc : ContinuousOn Jf Z) {c' : ℝ≥0∞}
    (ν : Measure Z) (hkey : ∀ B : Set S, MeasurableSet B → B ⊆ Z →
      ν (Subtype.val ⁻¹' B) = c' * ∫⁻ ζ in B, ENNReal.ofReal (Jf ζ) ∂μ)
    (Φ : (κ → UnitQuaternion) → ℝ≥0∞) (hΦ : Measurable Φ) (g : ι → UnitQuaternion) :
    ∫⁻ z : Z, Φ (gaugeTransform tl hd g (hemisphereChartField V (e z))) ∂ν =
      c' * ∫⁻ ζ in Z, Φ (gaugeTransform tl hd g (hemisphereChartField V (e ζ))) * ENNReal.ofReal (Jf ζ) ∂μ := by
  have hZm : MeasurableSet Z := hZ.isClosed.measurableSet
  have hJm : Measurable fun z : Z => ENNReal.ofReal (Jf z) :=
    ENNReal.measurable_ofReal.comp (continuousOn_iff_continuous_domRestrict.mp hJc).measurable
  have hνeq := base_measure_eq_withDensity hZm μ Jf hJm ν hkey
  have hcont : Continuous fun z : Z => gaugeTransform tl hd g (hemisphereChartField V (e z)) := by
    have hce : Continuous e := e.continuous_of_finiteDimensional
    refine continuous_pi fun b => ?_
    have h3 : Continuous fun z : Z => hemisphereUnit (e z b) := by
      refine continuousOn_hemisphereUnit.comp_continuous ?_ fun z => (hZ1 z.1 z.2 b).le
      exact (continuous_apply b).comp (hce.comp continuous_subtype_val)
    exact (continuous_const.mul (h3.mul continuous_const)).mul continuous_const
  have hFm : Measurable fun z : Z => Φ (gaugeTransform tl hd g (hemisphereChartField V (e z))) :=
    hΦ.comp hcont.measurable
  have h := lintegral_base_measure hZm μ Jf hJm c'
    (fun ζ => Φ (gaugeTransform tl hd g (hemisphereChartField V (e ζ)))) hFm
  rw [← hνeq] at h
  exact h
end OrbitChart
open OrbitChart in
theorem freeGaugeActionChangeOfVariables_holds (hD : GroupActions.FreeOrbitMeasureIsProduct)
    (hF : HaarOnFieldsInHemisphereChart) : FreeGaugeActionChangeOfVariables := by
  intro _ _ ι κ S _ _ _ _ _ _ _ _ _ tl hd V e Q Z μ _ hZ hZ1 hQ1 hQ2 hinj
  obtain ⟨cκ, hcκ, hFκ⟩ := hF (Measure.addHaar : Measure imaginaryQuaternions) κ
  obtain ⟨cι, hcι, hFι⟩ := hF (Measure.addHaar : Measure imaginaryQuaternions) ι
  obtain ⟨hemb, ν, hνf, hν⟩ := orbit_measure_decomposition hD tl hd V e hZ hZ1 hinj
  have hQ : ∀ p, Q (chartLinearization tl hd V e 0 p) = p := fun p => LinearMap.congr_fun hQ2 p
  let L : ((ι → imaginaryQuaternions) × S) ≃L[ℝ] (κ → imaginaryQuaternions) :=
    (LinearEquiv.ofLinear (chartLinearization tl hd V e 0) Q hQ1 hQ2).toContinuousLinearEquiv
  have hLe : ∀ p, L p = chartLinearization tl hd V e 0 p := fun p => rfl
  obtain ⟨a, ha0, hat, harea⟩ := exists_areaFormula_constant
    ((Measure.pi fun _ : ι => (Measure.addHaar : Measure imaginaryQuaternions)).prod μ)
    (Measure.pi fun _ : κ => (Measure.addHaar : Measure imaginaryQuaternions)) L
  have harea' : ∀ A : Set ((ι → imaginaryQuaternions) × S), MeasurableSet A → A ⊆ positiveDomain tl hd V e →
      InjOn (bondCoordinates tl hd V e) A →
      ∫⁻ y in bondCoordinates tl hd V e '' A, ENNReal.ofReal (densityProduct y)
          ∂(Measure.pi fun _ : κ => (Measure.addHaar : Measure imaginaryQuaternions)) =
        a * ∫⁻ p in A, ENNReal.ofReal (chartDensity tl hd V e Q p) * ENNReal.ofReal (densityProduct p.1)
          ∂((Measure.pi fun _ : ι => (Measure.addHaar : Measure imaginaryQuaternions)).prod μ) := by
    intro A hAm hAG hinjA
    have hcomp : (fun p => linearCoordinates tl hd V e Q (L p)) = bondCoordinates tl hd V e :=
      funext fun p => linearCoordinates_chartLinearization tl hd V e Q hQ p
    have h1 := harea (linearCoordinates tl hd V e Q) A hAm
      (fun p hp => differentiableAt_linearCoordinates tl hd V e Q hQ (hAG hp).1)
      (by rw [hcomp]; exact hinjA) (fun y => ENNReal.ofReal (densityProduct y))
    rw [hcomp] at h1
    rw [h1]
    congr 1
    refine setLIntegral_congr_fun hAm fun p hp => ?_
    have h2 := chartDensity_mul tl hd V e Q (hAG hp)
    simp only [hLe, linearCoordinates_chartLinearization tl hd V e Q hQ p]
    exact h2
  have hJc : ContinuousOn (fun ζ => chartJacobian tl hd V e Q (e ζ)) Z := by
    have h1 : ContinuousOn (fun ζ : S => chartDensity tl hd V e Q ((0 : ι → imaginaryQuaternions), ζ)) Z :=
      (continuousOn_chartDensity tl hd V e Q hQ).comp
        (by fun_prop : Continuous fun ζ : S =>
          (((0 : ι → imaginaryQuaternions), ζ) : (ι → imaginaryQuaternions) × S)).continuousOn
        fun ζ hζ => zero_form_mem_positiveDomain tl hd V e (hZ1 ζ hζ)
    exact h1.congr fun ζ hζ => (chartDensity_zero_form tl hd V e Q hQ (hZ1 ζ hζ)).symm
  set C₂ : ℝ≥0∞ := ENNReal.ofReal cκ * a with hC₂
  have hC₂t : C₂ ≠ ⊤ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top hat
  have hC₁0 : ENNReal.ofReal cι ≠ 0 := (ENNReal.ofReal_pos.mpr hcι).ne'
  have hC₁t : ENNReal.ofReal cι ≠ ⊤ := ENNReal.ofReal_ne_top
  have hC₂0 : C₂ ≠ 0 := mul_ne_zero (ENNReal.ofReal_pos.mpr hcκ).ne' ha0
  have hkey : ∀ B : Set S, MeasurableSet B → B ⊆ Z →
      ν (Subtype.val ⁻¹' B) = C₂ / ENNReal.ofReal cι *
        ∫⁻ ζ in B, ENNReal.ofReal (chartJacobian tl hd V e Q (e ζ)) ∂μ := by
    intro B hBm hBZ
    have hvt : μ B ≠ ⊤ := (lt_of_le_of_lt (measure_mono hBZ) hZ.measure_lt_top).ne
    have hDt : C₂ * μ B ≠ ⊤ := ENNReal.mul_ne_top hC₂t hvt
    have step := fun (η : ℝ) (hη : 0 < η) => orbit_measure_bounds tl hd V e hZ hZ1 hinj
      (Measure.addHaar : Measure imaginaryQuaternions) μ hcι inferInstance
      (hFκ V) hFι hemb ν hν a (chartDensity tl hd V e Q) harea' (fun ζ => chartJacobian tl hd V e Q (e ζ)) hJc
      (fun η hη => exists_small_forms_near_chartDensity tl hd V e Q hQ hZ hZ1 hη) hBm hBZ hη
    have h := le_antisymm (le_of_forall_pos_le_add_mul hDt fun η hη => (step η hη).1)
      (le_of_forall_pos_le_add_mul hDt fun η hη => (step η hη).2)
    calc ν (Subtype.val ⁻¹' B) = (ENNReal.ofReal cι)⁻¹ * (ENNReal.ofReal cι * ν (Subtype.val ⁻¹' B)) := by
          rw [← mul_assoc, ENNReal.inv_mul_cancel hC₁0 hC₁t, one_mul]
      _ = _ := by
          rw [h, div_eq_mul_inv]
          ring
  have himage : (fun p : (ι → UnitQuaternion) × S => gaugeTransform tl hd p.1 (hemisphereChartField V (e p.2))) ''
      (univ ×ˢ Z) =
      range fun p : (ι → UnitQuaternion) × Z => gaugeTransform tl hd p.1 (hemisphereChartField V (e p.2)) := by
    ext w
    constructor
    · rintro ⟨⟨g, ζ⟩, ⟨_, hζ⟩, rfl⟩
      exact ⟨(g, ⟨ζ, hζ⟩), rfl⟩
    · rintro ⟨⟨g, z⟩, rfl⟩
      exact ⟨(g, z.1), ⟨mem_univ _, z.2⟩, rfl⟩
  have hc't : C₂ / ENNReal.ofReal cι ≠ ⊤ := ENNReal.div_ne_top hC₂t hC₁0
  have hc'0 : C₂ / ENNReal.ofReal cι ≠ 0 := ENNReal.div_ne_zero.mpr ⟨hC₂0, hC₁t⟩
  refine ⟨(C₂ / ENNReal.ofReal cι).toReal, ENNReal.toReal_pos hc'0 hc't, fun Φ hΦ => ?_⟩
  rw [ENNReal.ofReal_toReal hc't, himage, hν Φ hΦ, ← lintegral_const_mul' _ _ hc't]
  exact lintegral_congr fun g => lintegral_orbit_base tl hd V e hZ hZ1 μ _ hJc ν hkey Φ hΦ g
end GaugeCharts
end YangMills.Construction
end
