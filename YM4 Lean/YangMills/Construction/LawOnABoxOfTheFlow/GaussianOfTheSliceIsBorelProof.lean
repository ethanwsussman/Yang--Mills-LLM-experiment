import YangMills.Construction.ColdStepAtMirrorFrames.ExpansionUnderAGaugeOfTheTopProof
import YangMills.Construction.LawOnABoxOfTheFlow.GaussianOfTheSliceIsBorel
import YangMills.Construction.LawOnABoxOfTheFlow.ToolsOfAChart
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped Quaternion ENNReal
namespace YangMills.Construction.BoxGaussian
open TorusFields BlockAverages
set_option synthInstance.maxSize 1024
set_option linter.unusedSectionVars false
set_option linter.deprecated false
set_option linter.unusedVariables false
section Projections
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
private theorem exists_measurable_orthogonalProjection [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X]
    {α J : Type*} [MeasurableSpace α] (B : X →ₗ[ℝ] X →ₗ[ℝ] ℝ) (hdef : ∀ u, B u u = 0 → u = 0)
    (hB : Measurable fun p : X × X => B p.1 p.2) (f : J → α → X) (hf : ∀ j, Measurable (f j)) (l : List J) :
    ∃ P : α → X → X, Measurable (fun p : α × X => P p.1 p.2) ∧ ∀ a,
      (∀ v, ∀ j ∈ l, B (f j a) (P a v) = 0) ∧
      ∀ v s, (∀ j ∈ l, B (f j a) s = 0) → B (v - P a v) s = 0 := by
  induction l with
  | nil => exact ⟨fun _ v => v, measurable_snd, fun a => ⟨by simp, by simp⟩⟩
  | cons j l ih =>
    obtain ⟨P, hP, hprop⟩ := ih
    let w : α → X := fun a => P a (f j a)
    have hw : Measurable w := hP.comp (measurable_id.prodMk (hf j))
    let P' : α → X → X := fun a v => P a v - (B (w a) (P a v) / B (w a) (w a)) • w a
    refine ⟨P', ?_, fun a => ?_⟩
    · have h1 : Measurable fun p : α × X => B (w p.1) (P p.1 p.2) :=
        hB.comp ((hw.comp measurable_fst).prodMk hP)
      have h2 : Measurable fun p : α × X => B (w p.1) (w p.1) :=
        hB.comp ((hw.comp measurable_fst).prodMk (hw.comp measurable_fst))
      exact hP.sub ((h1.div h2).smul (hw.comp measurable_fst))
    · obtain ⟨h1, h2⟩ := hprop a
      have hwS : ∀ i ∈ l, B (f i a) (w a) = 0 := fun i hi => h1 _ i hi
      have hkey : ∀ s, (∀ i ∈ l, B (f i a) s = 0) → B (f j a) s = B (w a) s := by
        intro s hs'
        have := h2 (f j a) s hs'
        rw [map_sub, LinearMap.sub_apply, sub_eq_zero] at this
        exact this
      have hS' : ∀ v, ∀ i ∈ l, B (f i a) (P' a v) = 0 := by
        intro v i hi
        simp only [P', map_sub, map_smul, h1 v i hi, hwS i hi, smul_eq_mul, mul_zero, sub_zero]
      refine ⟨fun v i hi => ?_, fun v s hs' => ?_⟩
      · rcases List.mem_cons.1 hi with rfl | hi
        · rw [hkey _ (hS' v)]
          simp only [P', map_sub, map_smul, smul_eq_mul]
          by_cases h0 : B (w a) (w a) = 0
          · have hz := hdef _ h0
            rw [hz]
            simp
          · rw [div_mul_cancel₀ _ h0, sub_self]
        · exact hS' v i hi
      · have hs1 : ∀ i ∈ l, B (f i a) s = 0 := fun i hi => hs' i (List.mem_cons_of_mem _ hi)
        have hs0 : B (w a) s = 0 := by
          rw [← hkey s hs1]
          exact hs' j List.mem_cons_self
        have e : v - P' a v = (v - P a v) + (B (w a) (P a v) / B (w a) (w a)) • w a := by
          simp only [P']
          abel
        rw [e, map_add, LinearMap.add_apply, h2 v s hs1, map_smul, LinearMap.smul_apply, hs0]
        simp
private theorem exists_linearMap_of_orthogonal (B : X →ₗ[ℝ] X →ₗ[ℝ] ℝ) (hdef : ∀ u, B u u = 0 → u = 0)
    (S : Submodule ℝ X) (P : X → X) (hP : ∀ v, P v ∈ S) (hQ : ∀ v, ∀ s ∈ S, B (v - P v) s = 0) :
    ∃ T : X →ₗ[ℝ] X, (∀ v, T v = P v) ∧ ∀ s ∈ S, T s = s := by
  have huniq : ∀ d ∈ S, (∀ s ∈ S, B d s = 0) → d = 0 := fun d hd' h => hdef d (h d hd')
  have hadd : ∀ u v, P (u + v) = P u + P v := by
    intro u v
    have h : P (u + v) - (P u + P v) = 0 := by
      refine huniq _ (S.sub_mem (hP _) (S.add_mem (hP _) (hP _))) fun s hs => ?_
      have e : P (u + v) - (P u + P v) = (u - P u) + (v - P v) - (u + v - P (u + v)) := by abel
      rw [e, map_sub, map_add, LinearMap.sub_apply, LinearMap.add_apply, hQ u s hs, hQ v s hs, hQ _ s hs]
      simp
    exact sub_eq_zero.1 h
  have hsmul : ∀ (c : ℝ) v, P (c • v) = c • P v := by
    intro c v
    have h : P (c • v) - c • P v = 0 := by
      refine huniq _ (S.sub_mem (hP _) (S.smul_mem _ (hP _))) fun s hs => ?_
      have e : P (c • v) - c • P v = c • (v - P v) - (c • v - P (c • v)) := by
        rw [smul_sub]
        abel
      rw [e, map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, hQ v s hs, hQ _ s hs]
      simp
    exact sub_eq_zero.1 h
  refine ⟨⟨⟨P, hadd⟩, hsmul⟩, fun _ => rfl, fun s hs => ?_⟩
  have h : s - P s = 0 := huniq _ (S.sub_mem hs (hP s)) fun t ht => hQ s t ht
  exact (sub_eq_zero.1 h).symm
private theorem exists_lintegral_addHaar_projection [FiniteDimensional ℝ X] [MeasurableSpace X] [BorelSpace X]
    [SecondCountableTopology X]
    (μ : Measure X) [μ.IsAddHaarMeasure] (S : Submodule ℝ X) (T : X →ₗ[ℝ] X) (hT : ∀ v, T v ∈ S)
    (hTs : ∀ s ∈ S, T s = s) :
    ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ∞ ∧ ∀ h : X → ℝ≥0∞, Measurable h →
      ∫⁻ v, h (T v) * (Metric.closedBall (0 : X) 1).indicator 1 (v - T v) ∂μ =
        c * ∫⁻ s, h s ∂((Measure.addHaar : Measure S).map Subtype.val) := by
  classical
  let K : Submodule ℝ X := LinearMap.ker T
  have hK : ∀ v, (LinearMap.id - T : X →ₗ[ℝ] X) v ∈ K := fun v => by
    simp [K, LinearMap.mem_ker, hTs _ (hT v)]
  let e : (S × K) ≃ₗ[ℝ] X := LinearEquiv.ofLinear (S.subtype.coprod K.subtype)
    ((T.codRestrict S hT).prod ((LinearMap.id - T).codRestrict K hK))
    (by
      ext v <;> simp)
    (by
      apply LinearMap.ext
      rintro ⟨⟨s, hs⟩, ⟨t, ht⟩⟩
      have ht' : T t = 0 := ht
      ext <;> simp [hTs s hs, ht'])
  let Φ : (S × K) ≃L[ℝ] X := e.toContinuousLinearEquiv
  let ν : Measure (S × K) := (Measure.addHaar : Measure S).prod (Measure.addHaar : Measure K)
  have : (ν.map Φ).IsAddHaarMeasure := Φ.isAddHaarMeasure_map ν
  have hμ := Measure.isAddLeftInvariant_eq_smul μ (ν.map Φ)
  set c₁ := Measure.addHaarScalarFactor μ (ν.map Φ) with hc₁
  have hc₁0 : 0 < c₁ := Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure _ _
  let m : ℝ≥0∞ := (Measure.addHaar : Measure K) (Metric.closedBall (0 : K) 1)
  have hm0 : m ≠ 0 :=
    (Measure.measure_pos_of_mem_nhds _ (Metric.closedBall_mem_nhds _ one_pos)).ne'
  have hm1 : m ≠ ∞ := (isCompact_closedBall (0 : K) 1).measure_lt_top.ne
  refine ⟨(c₁ : ℝ≥0∞) * m, mul_ne_zero (by exact_mod_cast hc₁0.ne') hm0,
    ENNReal.mul_ne_top ENNReal.coe_ne_top hm1, fun h hh => ?_⟩
  have hind : Measurable ((Metric.closedBall (0 : X) 1).indicator (1 : X → ℝ≥0∞)) :=
    measurable_one.indicator Metric.isClosed_closedBall.measurableSet
  have hH : Measurable fun v => h (T v) * (Metric.closedBall (0 : X) 1).indicator (1 : X → ℝ≥0∞) (v - T v) :=
    (hh.comp (T.continuous_of_finiteDimensional.measurable)).mul
      (hind.comp (measurable_id.sub T.continuous_of_finiteDimensional.measurable))
  have hΦ : ∀ (s : S) (t : K), T (Φ (s, t)) = s ∧ Φ (s, t) - T (Φ (s, t)) = t := by
    rintro ⟨s, hs⟩ ⟨t, ht⟩
    have ht' : T t = 0 := ht
    have e1 : Φ (⟨s, hs⟩, ⟨t, ht⟩) = s + t := by simp [Φ, e]
    rw [e1]
    simp [hTs s hs, ht']
  calc ∫⁻ v, h (T v) * (Metric.closedBall (0 : X) 1).indicator 1 (v - T v) ∂μ
      = (c₁ : ℝ≥0∞) * ∫⁻ v, h (T v) * (Metric.closedBall (0 : X) 1).indicator 1 (v - T v) ∂(ν.map Φ) := by
        conv_lhs => rw [hμ]
        rw [lintegral_smul_measure]
        rfl
    _ = (c₁ : ℝ≥0∞) * ∫⁻ p, h (p.1 : X) * (Metric.closedBall (0 : K) 1).indicator 1 p.2 ∂ν := by
        rw [lintegral_map hH Φ.continuous.measurable]
        congr 1
        refine lintegral_congr fun p => ?_
        obtain ⟨e1, e2⟩ := hΦ p.1 p.2
        have hp : Φ p = Φ (p.1, p.2) := rfl
        rw [hp, e2, e1]
        congr 1
    _ = (c₁ : ℝ≥0∞) * ∫⁻ s : S, h (s : X) * m ∂(Measure.addHaar : Measure S) := by
        congr 1
        have hm' : Measurable fun p : S × K => h (p.1 : X) * (Metric.closedBall (0 : K) 1).indicator (1 : K → ℝ≥0∞) p.2 :=
          (hh.comp (measurable_subtype_coe.comp measurable_fst)).mul
            ((measurable_one.indicator Metric.isClosed_closedBall.measurableSet).comp measurable_snd)
        rw [lintegral_prod _ hm'.aemeasurable]
        refine lintegral_congr fun s => ?_
        show ∫⁻ y : K, h (s : X) * (Metric.closedBall (0 : K) 1).indicator (1 : K → ℝ≥0∞) y ∂(Measure.addHaar : Measure K) = _
        rw [lintegral_const_mul _ (measurable_one.indicator Metric.isClosed_closedBall.measurableSet),
          lintegral_indicator_one Metric.isClosed_closedBall.measurableSet]
    _ = (c₁ : ℝ≥0∞) * m * ∫⁻ s, h s ∂((Measure.addHaar : Measure S).map Subtype.val) := by
        have hs : Measurable fun s : S => h (s : X) := hh.comp measurable_subtype_coe
        rw [lintegral_map hh measurable_subtype_coe, lintegral_mul_const _ hs]
        ring
end Projections
variable {n : ℕ} [NeZero n]
private def bondPairing : (TorusBond n → imaginaryQuaternions) →ₗ[ℝ] (TorusBond n → imaginaryQuaternions) →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ (fun u v => ∑ b : TorusBond n, inner ℝ (u b) (v b))
    (fun u u' v => by simp only [Pi.add_apply, inner_add_left, Finset.sum_add_distrib])
    (fun c u v => by simp [inner_smul_left, Finset.mul_sum])
    (fun u v v' => by simp only [Pi.add_apply, inner_add_right, Finset.sum_add_distrib])
    (fun c u v => by simp [inner_smul_right, Finset.mul_sum])
private theorem bondPairing_apply (u v : TorusBond n → imaginaryQuaternions) :
    bondPairing u v = ∑ b : TorusBond n, inner ℝ (u b) (v b) := rfl
private theorem bondPairing_self_eq_zero (u : TorusBond n → imaginaryQuaternions) (h : bondPairing u u = 0) : u = 0 := by
  rw [bondPairing_apply] at h
  funext b
  have h0 := (Finset.sum_eq_zero_iff_of_nonneg (fun b _ => real_inner_self_nonneg)).1 h b (Finset.mem_univ b)
  exact inner_self_eq_zero.1 h0
private theorem continuous_bondPairing :
    Continuous fun p : (TorusBond n → imaginaryQuaternions) × (TorusBond n → imaginaryQuaternions) =>
      bondPairing p.1 p.2 := by
  simp only [bondPairing_apply]
  exact continuous_finset_sum _ fun b _ => Continuous.inner
    ((continuous_apply b).comp continuous_fst) ((continuous_apply b).comp continuous_snd)
private theorem adjointAction_add (g : UnitQuaternion) (u v : imaginaryQuaternions) :
    ColdStepAtMirrorFrames.adjointAction g (u + v) =
      ColdStepAtMirrorFrames.adjointAction g u + ColdStepAtMirrorFrames.adjointAction g v := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.GaugeCovariance.adjointAction_add <;> assumption
private theorem adjointAction_smul (g : UnitQuaternion) (c : ℝ) (u : imaginaryQuaternions) :
    ColdStepAtMirrorFrames.adjointAction g (c • u) = c • ColdStepAtMirrorFrames.adjointAction g u := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.GaugeCovariance.adjointAction_smul <;> assumption
private def covariantGradLinear (A : TorusBond n → imaginaryQuaternions) :
    (TorusSite n → imaginaryQuaternions) →ₗ[ℝ] (TorusBond n → imaginaryQuaternions) where
  toFun χ := covariantGrad A χ
  map_add' u v := by
    funext b
    simp only [covariantGrad, Pi.add_apply, adjointAction_add]
    abel
  map_smul' c u := by
    funext b
    simp only [covariantGrad, Pi.smul_apply, adjointAction_smul, RingHom.id_apply, smul_sub]
private abbrev SliceConstraintIndex (n : ℕ) : Type :=
  (TorusBond n × Fin (Module.finrank ℝ imaginaryQuaternions)) ⊕
    (TorusSite n × Fin (Module.finrank ℝ imaginaryQuaternions))
open Classical in
private def sliceConstraint (o : TorusSite n) (R : ℕ) :
    SliceConstraintIndex n → (TorusBond n → imaginaryQuaternions) → (TorusBond n → imaginaryQuaternions)
  | Sum.inl (b, c), _ =>
      if b ∈ bondsTouching o R then 0 else Pi.single b (Module.finBasis ℝ imaginaryQuaternions c)
  | Sum.inr (z, c), A =>
      if z ∈ ResponseInTheExpansion.supBall o R then
        covariantGrad A (Pi.single z (Module.finBasis ℝ imaginaryQuaternions c)) else 0
private theorem continuous_sliceConstraint (o : TorusSite n) (R : ℕ) (j : SliceConstraintIndex n) :
    Continuous (sliceConstraint o R j) := by
  classical
  rcases j with ⟨b, c⟩ | ⟨z, c⟩
  · exact continuous_const
  · by_cases h : z ∈ ResponseInTheExpansion.supBall o R
    · have e : sliceConstraint o R (Sum.inr (z, c)) =
          fun A => covariantGrad A (Pi.single z (Module.finBasis ℝ imaginaryQuaternions c)) := by
        funext A
        simp only [sliceConstraint, if_pos h]
      rw [e]
      exact continuous_pi fun b => continuous_covariantGrad _ b
    · have e : sliceConstraint o R (Sum.inr (z, c)) = fun _ => 0 := by
        funext A
        simp only [sliceConstraint, if_neg h]
      rw [e]
      exact continuous_const
private theorem mem_gaugeSlice_iff (o : TorusSite n) (R : ℕ) (A ζ : TorusBond n → imaginaryQuaternions) :
    ζ ∈ gaugeSlice o R A ↔ ∀ j, bondPairing (sliceConstraint o R j A) ζ = 0 := by
  classical
  have hsingle : ∀ (b : TorusBond n) (e : imaginaryQuaternions),
      bondPairing (Pi.single b e) ζ = inner ℝ e (ζ b) := by
    intro b e
    rw [bondPairing_apply, Finset.sum_eq_single b]
    · rw [Pi.single_eq_same]
    · intro b' _ hb
      rw [Pi.single_eq_of_ne hb, inner_zero_left]
    · intro h
      exact absurd (Finset.mem_univ b) h
  constructor
  · rintro ⟨h1, h2⟩ (⟨b, c⟩ | ⟨z, c⟩)
    · by_cases h : b ∈ bondsTouching o R
      · simp [sliceConstraint, h]
      · simp only [sliceConstraint, if_neg h]
        rw [hsingle, h1 b h]
        simp
    · by_cases h : z ∈ ResponseInTheExpansion.supBall o R
      · simp only [sliceConstraint, if_pos h]
        rw [bondPairing_apply]
        have := h2 (Pi.single z (Module.finBasis ℝ imaginaryQuaternions c)) (fun y hy => by
          have hne : y ≠ z := fun e => hy (e ▸ h)
          simp [Pi.single_eq_of_ne hne])
        rw [← this]
        exact Finset.sum_congr rfl fun b _ => real_inner_comm _ _
      · simp [sliceConstraint, h]
  · intro h
    refine ⟨fun b hb => ?_, fun χ hχ => ?_⟩
    · have h0 : (innerₗ imaginaryQuaternions).flip (ζ b) = 0 := by
        refine (Module.finBasis ℝ imaginaryQuaternions).ext fun c => ?_
        have := h (Sum.inl (b, c))
        simp only [sliceConstraint, if_neg hb] at this
        rw [hsingle, real_inner_comm] at this
        simpa using this
      exact inner_self_eq_zero.1 (LinearMap.congr_fun h0 (ζ b))
    · let G : (TorusSite n → imaginaryQuaternions) →ₗ[ℝ] ℝ := (bondPairing ζ).comp (covariantGradLinear A)
      have hG : ∀ χ', ∑ b : TorusBond n, inner ℝ (ζ b) (covariantGrad A χ' b) = G χ' := fun _ => rfl
      rw [hG, ← Finset.univ_sum_single χ, map_sum]
      refine Finset.sum_eq_zero fun z _ => ?_
      by_cases hz : z ∈ ResponseInTheExpansion.supBall o R
      · have hz0 : G.comp (LinearMap.single ℝ (fun _ : TorusSite n => imaginaryQuaternions) z) = 0 := by
          refine (Module.finBasis ℝ imaginaryQuaternions).ext fun c => ?_
          have := h (Sum.inr (z, c))
          simp only [sliceConstraint, if_pos hz] at this
          rw [bondPairing_apply] at this
          show ∑ b : TorusBond n, inner ℝ (ζ b)
            (covariantGrad A (Pi.single z (Module.finBasis ℝ imaginaryQuaternions c)) b) = 0
          rw [← this]
          exact Finset.sum_congr rfl fun b _ => real_inner_comm _ _
        exact LinearMap.congr_fun hz0 (χ z)
      · rw [hχ z hz]
        simp
private theorem measurable_sliceGaussian_section (a : ℝ) (L k : ℕ) (o : TorusSite n) (R : ℕ) (x : ℝ)
    (hq : Continuous fun v : TorusBond n → imaginaryQuaternions =>
      hessianForm a L k (ResponseInTheExpansion.supBall o (2 * R)) v v)
    {E : Set ((TorusBond n → imaginaryQuaternions) × (TorusBond n → imaginaryQuaternions))} (hE : MeasurableSet E) :
    Measurable fun A : TorusBond n → imaginaryQuaternions => sliceGaussian a L k o R x A {ζ | (A, ζ) ∈ E} := by
  classical
  let μ : Measure (TorusBond n → imaginaryQuaternions) := Measure.addHaar
  obtain ⟨P, hP, hprop⟩ := exists_measurable_orthogonalProjection (bondPairing (n := n)) bondPairing_self_eq_zero
    continuous_bondPairing.measurable (sliceConstraint o R)
    (fun j => (continuous_sliceConstraint o R j).measurable) (Finset.univ.toList)
  let w : (TorusBond n → imaginaryQuaternions) × (TorusBond n → imaginaryQuaternions) → ℝ≥0∞ := fun p => ENNReal.ofReal
    (Real.exp (-(x / 2) * hessianForm a L k (ResponseInTheExpansion.supBall o (2 * R)) (p.1 + p.2) (p.1 + p.2)))
  have hw : Measurable w := by
    have : Continuous fun p : (TorusBond n → imaginaryQuaternions) × (TorusBond n → imaginaryQuaternions) =>
        Real.exp (-(x / 2) * hessianForm a L k (ResponseInTheExpansion.supBall o (2 * R)) (p.1 + p.2) (p.1 + p.2)) :=
      Real.continuous_exp.comp (continuous_const.mul (hq.comp (continuous_fst.add continuous_snd)))
    exact ENNReal.measurable_ofReal.comp this.measurable
  let ind : (TorusBond n → imaginaryQuaternions) → ℝ≥0∞ :=
    (Metric.closedBall (0 : TorusBond n → imaginaryQuaternions) 1).indicator 1
  have hind : Measurable ind := measurable_one.indicator Metric.isClosed_closedBall.measurableSet
  have hPv : Measurable fun p : (TorusBond n → imaginaryQuaternions) × (TorusBond n → imaginaryQuaternions) =>
      (p.1, P p.1 p.2) :=
    measurable_fst.prodMk hP
  have hrem : Measurable fun p : (TorusBond n → imaginaryQuaternions) × (TorusBond n → imaginaryQuaternions) =>
      ind (p.2 - P p.1 p.2) :=
    hind.comp (measurable_snd.sub hP)
  have hEi : Measurable
      (E.indicator (1 : (TorusBond n → imaginaryQuaternions) × (TorusBond n → imaginaryQuaternions) → ℝ≥0∞)) :=
    measurable_one.indicator hE
  let F : (TorusBond n → imaginaryQuaternions) → ℝ≥0∞ := fun A =>
    ∫⁻ v, (E.indicator 1 (A, P A v) * w (A, P A v)) * ind (v - P A v) ∂μ
  let M : (TorusBond n → imaginaryQuaternions) → ℝ≥0∞ := fun A => ∫⁻ v, w (A, P A v) * ind (v - P A v) ∂μ
  have hF : Measurable F :=
    Measurable.lintegral_prod_right'
      (f := fun p : (TorusBond n → imaginaryQuaternions) × (TorusBond n → imaginaryQuaternions) =>
        (E.indicator 1 (p.1, P p.1 p.2) * w (p.1, P p.1 p.2)) * ind (p.2 - P p.1 p.2))
      (((hEi.comp hPv).mul (hw.comp hPv)).mul hrem)
  have hM : Measurable M :=
    Measurable.lintegral_prod_right'
      (f := fun p : (TorusBond n → imaginaryQuaternions) × (TorusBond n → imaginaryQuaternions) =>
        w (p.1, P p.1 p.2) * ind (p.2 - P p.1 p.2)) ((hw.comp hPv).mul hrem)
  have hform : (fun A : TorusBond n → imaginaryQuaternions => sliceGaussian a L k o R x A {ζ | (A, ζ) ∈ E}) =
      fun A => (M A)⁻¹ * F A := by
    funext A
    obtain ⟨h1, h2⟩ := hprop A
    have hin : ∀ v, P A v ∈ gaugeSlice o R A := fun v => (mem_gaugeSlice_iff o R A _).2 fun j =>
      h1 v j (Finset.mem_toList.2 (Finset.mem_univ j))
    have hout : ∀ v, ∀ s ∈ gaugeSlice o R A, bondPairing (v - P A v) s = 0 := fun v s hs =>
      h2 v s fun j _ => (mem_gaugeSlice_iff o R A s).1 hs j
    obtain ⟨T, hTP, hTs⟩ :=
      exists_linearMap_of_orthogonal bondPairing bondPairing_self_eq_zero (gaugeSlice o R A) (P A) hin hout
    obtain ⟨c, hc0, hc1, hc⟩ := exists_lintegral_addHaar_projection μ (gaugeSlice o R A) T
      (fun v => hTP v ▸ hin v) hTs
    have hsec : MeasurableSet {ζ | (A, ζ) ∈ E} := measurable_prodMk_left hE
    have hwA : Measurable fun ζ => w (A, ζ) := hw.comp measurable_prodMk_left
    have hMA : M A = c * ∫⁻ s, w (A, s) ∂(subspaceVolume (gaugeSlice o R A)) := by
      have := hc (fun s => w (A, s)) hwA
      simp only [hTP] at this
      exact this
    have hFA : F A = c * ∫⁻ s, {ζ | (A, ζ) ∈ E}.indicator (fun ζ => w (A, ζ)) s
        ∂(subspaceVolume (gaugeSlice o R A)) := by
      have := hc (fun s => {ζ | (A, ζ) ∈ E}.indicator (fun ζ => w (A, ζ)) s) (hwA.indicator hsec)
      simp only [hTP] at this
      refine Eq.trans ?_ this
      refine lintegral_congr fun v => ?_
      congr 1
      by_cases hv : (A, P A v) ∈ E
      · simp [Set.indicator, hv]
      · simp [Set.indicator, hv]
    rw [hMA, hFA]
    show (BoxGaussian.normalize _) _ = _
    unfold BoxGaussian.normalize
    rw [Measure.smul_apply, smul_eq_mul, withDensity_apply _ MeasurableSet.univ, withDensity_apply _ hsec,
      Measure.restrict_univ, ← lintegral_indicator hsec]
    rw [ENNReal.mul_inv (Or.inl hc0) (Or.inl hc1)]
    have hcc : c⁻¹ * c = 1 := ENNReal.inv_mul_cancel hc0 hc1
    calc _ = (c⁻¹ * c) * (((∫⁻ s, w (A, s) ∂(subspaceVolume (gaugeSlice o R A)))⁻¹) *
          ∫⁻ s, {ζ | (A, ζ) ∈ E}.indicator (fun ζ => w (A, ζ)) s ∂(subspaceVolume (gaugeSlice o R A))) := by
          rw [hcc, one_mul]
      _ = _ := by ring
  rw [hform]
  exact hM.inv.mul hF
theorem sliceGaussianMeasurable_of_cubeHessian (hF : cubeHessianStatement) : sliceGaussianMeasurableStatement := by
  intro Tb hTb κ₀ h1 h2
  obtain ⟨CQ, R₀, -, hf⟩ := hF Tb hTb
  refine ⟨((R₀ : ℝ) + 1) ^ 27, ?_⟩
  intro x R k n _ o hx hR hn E hE
  have hRR : R₀ ≤ R := by
    rw [hR]
    exact le_boxRadius κ₀ x h1 R₀ hx
  obtain ⟨-, -, -, -, -, -, hform⟩ := hf k n o R hRR hn
  exact (measurable_sliceGaussian_section _ _ k o R x (continuous_hessianForm_diag hform) hE).comp
    measurable_subtype_coe
end YangMills.Construction.BoxGaussian
end
