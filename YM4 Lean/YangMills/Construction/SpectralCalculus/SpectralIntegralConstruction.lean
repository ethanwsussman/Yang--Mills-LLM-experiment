import YangMills.Construction.ReflectionPositiveLimits.ReconstructionFromAContractionAtADenseSetOfTimesProof
import YangMills.Construction.HilbertSpaces.JointSpectralMeasureOfACommutingPairProof
import YangMills.Construction.SpectralCalculus.SpectralIntegralGenerators
import YangMills.Construction.SpectralTheory.UnboundedBorelCalculusFromTruncations
import Mathlib
set_option autoImplicit false
open MeasureTheory Set Filter Topology
open scoped ComplexConjugate ComplexOrder NNReal ENNReal
noncomputable section
namespace YangMills.Construction.SpectralCalculus.SpectralIntegralConstruction
section Functions
variable {F G : SpectralPlane → ℂ}
theorem isBoundedMeasurable_add (hF : IsBoundedMeasurable F) (hG : IsBoundedMeasurable G) :
    IsBoundedMeasurable fun p => F p + G p := by
  obtain ⟨hm, C, hC⟩ := hF
  obtain ⟨hm', D, hD⟩ := hG
  exact ⟨hm.add hm', C + D, fun p => (norm_add_le _ _).trans (add_le_add (hC p) (hD p))⟩
theorem isBoundedMeasurable_mul (hF : IsBoundedMeasurable F) (hG : IsBoundedMeasurable G) :
    IsBoundedMeasurable fun p => F p * G p := by
  obtain ⟨hm, C, hC⟩ := hF
  obtain ⟨hm', D, hD⟩ := hG
  refine ⟨hm.mul hm', C * D, fun p => ?_⟩
  rw [norm_mul]
  exact mul_le_mul (hC p) (hD p) (norm_nonneg _) ((norm_nonneg _).trans (hC p))
theorem isBoundedMeasurable_const (c : ℂ) : IsBoundedMeasurable fun _ : SpectralPlane => c :=
  ⟨measurable_const, ‖c‖, fun _ => le_rfl⟩
theorem isBoundedMeasurable_indicator (hF : IsBoundedMeasurable F) {s : Set SpectralPlane}
    (hs : MeasurableSet s) : IsBoundedMeasurable (s.indicator F) := by
  obtain ⟨hm, C, hC⟩ := hF
  refine ⟨hm.indicator hs, C, fun p => ?_⟩
  by_cases hp : p ∈ s
  · simpa [hp] using hC p
  · simpa [hp] using (norm_nonneg _).trans (hC p)
theorem isBoundedMeasurable_conj (hF : IsBoundedMeasurable F) :
    IsBoundedMeasurable fun p => conj (F p) := by
  obtain ⟨hm, C, hC⟩ := hF
  exact ⟨Complex.continuous_conj.measurable.comp hm, C, fun p => by simpa using hC p⟩
theorem boundedMeasurable_induction {Q : (SpectralPlane → ℂ) → Prop}
    (hind : ∀ (c : ℂ) (s : Set SpectralPlane), MeasurableSet s → Q (s.indicator fun _ => c))
    (hadd : ∀ F G, IsBoundedMeasurable F → IsBoundedMeasurable G → Q F → Q G →
      Q fun p => F p + G p)
    (hlim : ∀ (F : ℕ → SpectralPlane → ℂ) (G : SpectralPlane → ℂ) (C : ℝ),
      (∀ n, IsBoundedMeasurable (F n)) → IsBoundedMeasurable G → (∀ n p, ‖F n p‖ ≤ C) →
      (∀ p, Tendsto (fun n => F n p) atTop (𝓝 (G p))) → (∀ n, Q (F n)) → Q G)
    (hF : IsBoundedMeasurable F) : Q F := by
  have hb : ∀ f : SimpleFunc SpectralPlane ℂ, IsBoundedMeasurable f := fun f =>
    ⟨f.measurable, f.exists_forall_norm_le⟩
  have hsimple : ∀ f : SimpleFunc SpectralPlane ℂ, Q f := by
    intro f
    refine SimpleFunc.induction (motive := fun f => Q f) ?_ ?_ f
    · intro c s hs
      have : (SimpleFunc.piecewise s hs (SimpleFunc.const _ c) (SimpleFunc.const _ 0) :
          SpectralPlane → ℂ) = s.indicator fun _ => c := by
        funext p
        by_cases hp : p ∈ s <;> simp [hp]
      rw [this]
      exact hind c s hs
    · intro f g _ hf hg
      exact hadd f g (hb f) (hb g) hf hg
  obtain ⟨hm, C, hC⟩ := hF
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC (0, 0))
  have hs := hm.stronglyMeasurable
  exact hlim (fun n => hs.approxBounded C n) F C (fun n => hb _) ⟨hm, C, hC⟩
    (fun n p => hs.norm_approxBounded_le hC0 n p)
    (fun p => hs.tendsto_approxBounded_of_norm_le (hC p)) fun n => hsimple _
end Functions
section Calculus
variable {F G : SpectralPlane → ℂ}
theorem integrable_of_isBoundedMeasurable (μ : ComplexMeasure SpectralPlane)
    (hF : IsBoundedMeasurable F) : μ.Integrable F := by
  obtain ⟨hm, C, hC⟩ := hF
  exact Integrable.of_bound hm.aestronglyMeasurable C (Eventually.of_forall hC)
theorem complexIntegral_add (μ : ComplexMeasure SpectralPlane) (hF : IsBoundedMeasurable F)
    (hG : IsBoundedMeasurable G) :
    complexIntegral μ (fun p => F p + G p) = complexIntegral μ F + complexIntegral μ G :=
  VectorMeasure.integral_fun_add (integrable_of_isBoundedMeasurable μ hF)
    (integrable_of_isBoundedMeasurable μ hG)
theorem complexIntegral_indicator_const (μ : ComplexMeasure SpectralPlane) (c : ℂ)
    {s : Set SpectralPlane} (hs : MeasurableSet s) :
    complexIntegral μ (s.indicator fun _ => c) = c * μ s :=
  VectorMeasure.integral_indicator_const c hs
theorem tendsto_complexIntegral (μ : ComplexMeasure SpectralPlane) {F : ℕ → SpectralPlane → ℂ}
    {G : SpectralPlane → ℂ} {C : ℝ} (hF : ∀ n, IsBoundedMeasurable (F n))
    (hC : ∀ n p, ‖F n p‖ ≤ C) (hl : ∀ p, Tendsto (fun n => F n p) atTop (𝓝 (G p))) :
    Tendsto (fun n => complexIntegral μ (F n)) atTop (𝓝 (complexIntegral μ G)) :=
  VectorMeasure.tendsto_integral_of_dominated_convergence (fun _ => C)
    (fun n => (hF n).1.aestronglyMeasurable) (integrable_const C)
    (fun n => Eventually.of_forall (hC n)) (Eventually.of_forall hl)
theorem complexIntegral_eq_of_apply {μ ν₁ ν₂ : ComplexMeasure SpectralPlane} {a : ℂ}
    (h : ∀ s, MeasurableSet s → μ s = a * ν₁ s + ν₂ s) (hF : IsBoundedMeasurable F) :
    complexIntegral μ F = a * complexIntegral ν₁ F + complexIntegral ν₂ F := by
  refine boundedMeasurable_induction
    (Q := fun F => complexIntegral μ F = a * complexIntegral ν₁ F + complexIntegral ν₂ F)
    ?_ ?_ ?_ hF
  · intro c s hs
    simp only [complexIntegral_indicator_const _ _ hs, h s hs]
    ring
  · intro F G hF hG h₁ h₂
    rw [complexIntegral_add μ hF hG, complexIntegral_add ν₁ hF hG, complexIntegral_add ν₂ hF hG,
      h₁, h₂]
    ring
  · intro F G C hF _ hC hl hQ
    refine tendsto_nhds_unique (tendsto_complexIntegral μ hF hC hl) ?_
    simp only [hQ]
    exact ((tendsto_complexIntegral ν₁ hF hC hl).const_mul a).add
      (tendsto_complexIntegral ν₂ hF hC hl)
theorem complexIntegral_eq_mul_of_apply {μ ν : ComplexMeasure SpectralPlane} {a : ℂ}
    (h : ∀ s, MeasurableSet s → μ s = a * ν s) (hF : IsBoundedMeasurable F) :
    complexIntegral μ F = a * complexIntegral ν F := by
  have := complexIntegral_eq_of_apply (μ := μ) (ν₁ := ν) (ν₂ := 0) (a := a)
    (fun s hs => by simp [h s hs]) hF
  rw [this]
  simp [complexIntegral, VectorMeasure.integral_zero_vectorMeasure]
theorem complexIntegral_const_mul (μ : ComplexMeasure SpectralPlane) (a : ℂ)
    (hF : IsBoundedMeasurable F) :
    complexIntegral μ (fun p => a * F p) = a * complexIntegral μ F := by
  refine boundedMeasurable_induction
    (Q := fun F => complexIntegral μ (fun p => a * F p) = a * complexIntegral μ F) ?_ ?_ ?_ hF
  · intro c s hs
    have : (fun p => a * s.indicator (fun _ => c) p) = s.indicator fun _ => a * c := by
      funext p
      by_cases hp : p ∈ s <;> simp [hp]
    rw [this, complexIntegral_indicator_const _ _ hs, complexIntegral_indicator_const _ _ hs]
    ring
  · intro F G hF hG h₁ h₂
    have hc : ∀ {F : SpectralPlane → ℂ}, IsBoundedMeasurable F →
        IsBoundedMeasurable fun p => a * F p := fun hF =>
      isBoundedMeasurable_mul (isBoundedMeasurable_const a) hF
    have : (fun p => a * (F p + G p)) = fun p => a * F p + a * G p := by
      funext p
      ring
    rw [this, complexIntegral_add μ (hc hF) (hc hG), complexIntegral_add μ hF hG, h₁, h₂]
    ring
  · intro F G C hF _ hC hl hQ
    refine tendsto_nhds_unique
      (tendsto_complexIntegral μ (F := fun n p => a * F n p) (G := fun p => a * G p)
        (C := ‖a‖ * C)
        (fun n => isBoundedMeasurable_mul (isBoundedMeasurable_const a) (hF n))
        (fun n p => ?_) (fun p => (hl p).const_mul a)) ?_
    · rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (hC n p) (norm_nonneg _)
    · simp only [hQ]
      exact (tendsto_complexIntegral μ hF hC hl).const_mul a
theorem complexIntegral_conj_of_apply {μ ν : ComplexMeasure SpectralPlane}
    (h : ∀ s, MeasurableSet s → μ s = conj (ν s)) (hF : IsBoundedMeasurable F) :
    complexIntegral μ (fun p => conj (F p)) = conj (complexIntegral ν F) := by
  refine boundedMeasurable_induction
    (Q := fun F => complexIntegral μ (fun p => conj (F p)) = conj (complexIntegral ν F))
    ?_ ?_ ?_ hF
  · intro c s hs
    have : (fun p => conj (s.indicator (fun _ => c) p)) = s.indicator fun _ => conj c := by
      funext p
      by_cases hp : p ∈ s <;> simp [hp]
    rw [this, complexIntegral_indicator_const _ _ hs, complexIntegral_indicator_const _ _ hs,
      h s hs, map_mul]
  · intro F G hF hG h₁ h₂
    have : (fun p => conj (F p + G p)) = fun p => conj (F p) + conj (G p) := by
      funext p
      simp
    rw [this, complexIntegral_add μ (isBoundedMeasurable_conj hF) (isBoundedMeasurable_conj hG),
      complexIntegral_add ν hF hG, h₁, h₂, map_add]
  · intro F G C hF _ hC hl hQ
    refine tendsto_nhds_unique
      (tendsto_complexIntegral μ (F := fun n p => conj (F n p)) (G := fun p => conj (G p))
        (C := C) (fun n => isBoundedMeasurable_conj (hF n)) (fun n p => by simpa using hC n p)
        (fun p => (Complex.continuous_conj.tendsto _).comp (hl p))) ?_
    simp only [hQ]
    exact (Complex.continuous_conj.tendsto _).comp (tendsto_complexIntegral ν hF hC hl)
theorem norm_complexIntegral_le (μ : ComplexMeasure SpectralPlane) {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ p, ‖F p‖ ≤ C) : ‖complexIntegral μ F‖ ≤ C * μ.variation.real univ := by
  have h := VectorMeasure.norm_integral_le_of_norm_le_const (μ := μ) (f := F)
    (B := mulPairing) (C := C) (ae_of_all _ hC)
  have hB : ‖mulPairing‖ ≤ 1 := ContinuousLinearMap.opNorm_mul_le ℝ ℂ
  calc ‖complexIntegral μ F‖ ≤ C * ‖mulPairing‖ * μ.variation.real univ := h
    _ ≤ C * 1 * μ.variation.real univ := by gcongr
    _ = C * μ.variation.real univ := by ring
end Calculus
section Coefficients
variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (P : ProjValuedMeasure H)
theorem matrixCoeff_apply_set (u v : H) {s : Set SpectralPlane} (hs : MeasurableSet s) :
    P.matrixCoeff u v s = inner ℂ u (P ⟨s, hs⟩ v) :=
  P.matrixCoeff_apply u v ⟨s, hs⟩
theorem apply_idem (B : MeasurableSubtype SpectralPlane) (v : H) : P B (P B v) = P B v :=
  DFunLike.congr_fun (P.isOrthogonalProjection B).2 v
theorem inner_apply_left_eq (B : MeasurableSubtype SpectralPlane) (u v : H) :
    inner ℂ (P B u) v = inner ℂ u (P B v) :=
  (P.isOrthogonalProjection B).1 u v
theorem apply_univ_eq (v : H) : P ⟨univ, MeasurableSet.univ⟩ v = v :=
  DFunLike.congr_fun P.map_univ v
theorem matrixCoeff_self (v : H) {s : Set SpectralPlane} (hs : MeasurableSet s) :
    P.matrixCoeff v v s = ((‖P ⟨s, hs⟩ v‖ ^ 2 : ℝ) : ℂ) := by
  have h : inner ℂ v (P ⟨s, hs⟩ v) = inner ℂ (P ⟨s, hs⟩ v) (P ⟨s, hs⟩ v) := by
    rw [inner_apply_left_eq, apply_idem]
  rw [matrixCoeff_apply_set P v v hs, h, inner_self_eq_norm_sq_to_K]
  push_cast
  rfl
theorem enorm_matrixCoeff_self (v : H) {s : Set SpectralPlane} (hs : MeasurableSet s) :
    ‖P.matrixCoeff v v s‖ₑ = ENNReal.ofReal (‖P ⟨s, hs⟩ v‖ ^ 2) := by
  rw [matrixCoeff_self P v hs, ← ofReal_norm, Complex.norm_real,
    Real.norm_of_nonneg (by positivity)]
def diagMeasure (v : H) : Measure SpectralPlane :=
  Measure.ofMeasurable (fun s hs => ENNReal.ofReal (‖P ⟨s, hs⟩ v‖ ^ 2))
    (by
      rw [← enorm_matrixCoeff_self P v MeasurableSet.empty]
      simp)
    (by
      intro f hf hd
      have hsum := (P.matrixCoeff v v).hasSum_of_disjoint_iUnion hf hd
      simp only [matrixCoeff_self P v (hf _), matrixCoeff_self P v (MeasurableSet.iUnion hf)]
        at hsum
      have hsum' := Complex.hasSum_ofReal.mp hsum
      rw [← hsum'.tsum_eq]
      exact ENNReal.ofReal_tsum_of_nonneg (fun _ => by positivity) hsum'.summable)
theorem diagMeasure_apply (v : H) {s : Set SpectralPlane} (hs : MeasurableSet s) :
    diagMeasure P v s = ENNReal.ofReal (‖P ⟨s, hs⟩ v‖ ^ 2) :=
  Measure.ofMeasurable_apply s hs
theorem variation_matrixCoeff_self (v : H) {s : Set SpectralPlane} (hs : MeasurableSet s) :
    (P.matrixCoeff v v).variation s = ENNReal.ofReal (‖P ⟨s, hs⟩ v‖ ^ 2) := by
  apply le_antisymm
  · have hle : (P.matrixCoeff v v).variation ≤ diagMeasure P v :=
      VectorMeasure.variation_le_of_forall_enorm_le fun E hE => by
        rw [enorm_matrixCoeff_self P v hE, diagMeasure_apply P v hE]
    simpa only [diagMeasure_apply P v hs] using hle s
  · rw [← enorm_matrixCoeff_self P v hs]
    exact VectorMeasure.enorm_measure_le_variation _ _
theorem variation_matrixCoeff_self_real (v : H) {s : Set SpectralPlane}
    (hs : MeasurableSet s) :
    (P.matrixCoeff v v).variation.real s = ‖P ⟨s, hs⟩ v‖ ^ 2 := by
  rw [Measure.real, variation_matrixCoeff_self P v hs, ENNReal.toReal_ofReal (by positivity)]
theorem variation_matrixCoeff_self_univ (v : H) :
    (P.matrixCoeff v v).variation univ = ENNReal.ofReal (‖v‖ ^ 2) := by
  rw [variation_matrixCoeff_self P v MeasurableSet.univ, apply_univ_eq]
theorem matrixCoeff_zero_left (v : H) : P.matrixCoeff 0 v = 0 :=
  VectorMeasure.ext fun s hs => by simp [matrixCoeff_apply_set P 0 v hs]
theorem matrixCoeff_zero_right (u : H) : P.matrixCoeff u 0 = 0 :=
  VectorMeasure.ext fun s hs => by simp [matrixCoeff_apply_set P u 0 hs]
theorem variation_matrixCoeff_le (u v : H) :
    (P.matrixCoeff u v).variation.real univ ≤ ‖u‖ * ‖v‖ := by
  by_cases hu : u = 0
  · simp [hu, matrixCoeff_zero_left]
  by_cases hv : v = 0
  · simp [hv, matrixCoeff_zero_right]
  set a : ℝ := ‖v‖ / (2 * ‖u‖) with ha
  set b : ℝ := ‖u‖ / (2 * ‖v‖) with hb
  have ha0 : 0 ≤ a := by positivity
  have hb0 : 0 ≤ b := by positivity
  have hle : (P.matrixCoeff u v).variation ≤
      ENNReal.ofReal a • (P.matrixCoeff u u).variation +
        ENNReal.ofReal b • (P.matrixCoeff v v).variation := by
    refine VectorMeasure.variation_le_of_forall_enorm_le fun E hE => ?_
    have h₁ : ‖P.matrixCoeff u v E‖ ≤ a * ‖P ⟨E, hE⟩ u‖ ^ 2 + b * ‖P ⟨E, hE⟩ v‖ ^ 2 := by
      have hi : inner ℂ u (P ⟨E, hE⟩ v) = inner ℂ (P ⟨E, hE⟩ u) (P ⟨E, hE⟩ v) := by
        rw [inner_apply_left_eq, apply_idem]
      rw [matrixCoeff_apply_set P u v hE, hi]
      refine (norm_inner_le_norm _ _).trans ?_
      set x := ‖P ⟨E, hE⟩ u‖
      set y := ‖P ⟨E, hE⟩ v‖
      have hab' : a * b = 1 / 4 := by
        rw [ha, hb]
        field_simp
        norm_num
      have hapos : 0 < a := by positivity
      have : x * y ≤ a * x ^ 2 + b * y ^ 2 := by
        have hb' : b = 1 / (4 * a) := by
          field_simp
          linarith
        rw [hb']
        have : a * x ^ 2 + 1 / (4 * a) * y ^ 2 - x * y = (2 * a * x - y) ^ 2 / (4 * a) := by
          field_simp
          ring
        have h0 : 0 ≤ (2 * a * x - y) ^ 2 / (4 * a) := by positivity
        linarith
      exact this
    have hpos : 0 ≤ a * ‖P ⟨E, hE⟩ u‖ ^ 2 := by positivity
    have hpos' : 0 ≤ b * ‖P ⟨E, hE⟩ v‖ ^ 2 := by positivity
    calc ‖P.matrixCoeff u v E‖ₑ = ENNReal.ofReal ‖P.matrixCoeff u v E‖ :=
          (ofReal_norm _).symm
      _ ≤ ENNReal.ofReal (a * ‖P ⟨E, hE⟩ u‖ ^ 2 + b * ‖P ⟨E, hE⟩ v‖ ^ 2) :=
          ENNReal.ofReal_le_ofReal h₁
      _ = _ := by
          rw [ENNReal.ofReal_add hpos hpos', ENNReal.ofReal_mul ha0, ENNReal.ofReal_mul hb0]
          simp only [Measure.add_apply, Measure.smul_apply, smul_eq_mul,
            variation_matrixCoeff_self P u hE, variation_matrixCoeff_self P v hE]
  have hu2 : a * ‖u‖ ^ 2 + b * ‖v‖ ^ 2 = ‖u‖ * ‖v‖ := by
    rw [ha, hb]
    field_simp
    ring
  have hfin : (P.matrixCoeff u v).variation univ ≤ ENNReal.ofReal (‖u‖ * ‖v‖) := by
    refine (hle univ).trans ?_
    simp only [Measure.add_apply, Measure.smul_apply, smul_eq_mul,
      variation_matrixCoeff_self_univ]
    rw [← ENNReal.ofReal_mul ha0, ← ENNReal.ofReal_mul hb0,
      ← ENNReal.ofReal_add (by positivity) (by positivity), hu2]
  exact ENNReal.toReal_le_of_le_ofReal (by positivity) hfin
end Coefficients
section Bounded
variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (P : ProjValuedMeasure H) (hr : HilbertSpace.BoundedSesqRep.Claim)
variable {F F' G : SpectralPlane → ℂ}
theorem isSesqMap_complexIntegral (hF : IsBoundedMeasurable F) :
    HilbertSpace.BoundedSesqRep.IsSesqMap
      fun u v : H => complexIntegral (P.matrixCoeff u v) F where
  add_left u₁ u₂ v := by
    have := complexIntegral_eq_of_apply (μ := P.matrixCoeff (u₁ + u₂) v)
      (ν₁ := P.matrixCoeff u₁ v) (ν₂ := P.matrixCoeff u₂ v) (a := 1) (fun s hs => by
        simp only [matrixCoeff_apply_set P _ _ hs, inner_add_left, one_mul]) hF
    simpa using this
  smul_left a u v := complexIntegral_eq_mul_of_apply (fun s hs => by
    simp only [matrixCoeff_apply_set P _ _ hs, inner_smul_left]) hF
  add_right u v₁ v₂ := by
    have := complexIntegral_eq_of_apply (μ := P.matrixCoeff u (v₁ + v₂))
      (ν₁ := P.matrixCoeff u v₁) (ν₂ := P.matrixCoeff u v₂) (a := 1) (fun s hs => by
        simp only [matrixCoeff_apply_set P _ _ hs, map_add, inner_add_right, one_mul]) hF
    simpa using this
  smul_right a u v := complexIntegral_eq_mul_of_apply (fun s hs => by
    simp only [matrixCoeff_apply_set P _ _ hs, map_smul, inner_smul_right]) hF
theorem norm_complexIntegral_matrixCoeff_le {C : ℝ} (hC0 : 0 ≤ C) (hC : ∀ p, ‖F p‖ ≤ C)
    (u v : H) : ‖complexIntegral (P.matrixCoeff u v) F‖ ≤ C * ‖u‖ * ‖v‖ := by
  refine (norm_complexIntegral_le _ hC0 hC).trans ?_
  rw [mul_assoc]
  exact mul_le_mul_of_nonneg_left (variation_matrixCoeff_le P u v) hC0
include hr
theorem exists_isBoundedSpectralIntegral (hF : IsBoundedMeasurable F) {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ p, ‖F p‖ ≤ C) : ∃ B : H →L[ℂ] H, P.IsBoundedSpectralIntegral F B ∧ ‖B‖ ≤ C := by
  obtain ⟨B, hB, -, hn, -⟩ := hr H C (fun u v => complexIntegral (P.matrixCoeff u v) F) hC0
    (isSesqMap_complexIntegral P hF) (norm_complexIntegral_matrixCoeff_le P hC0 hC)
  exact ⟨B, hB, hn⟩
theorem isBoundedSpectralIntegral_self (hF : IsBoundedMeasurable F) :
    P.IsBoundedSpectralIntegral F (P.boundedSpectralIntegral F) := by
  obtain ⟨hm, C, hC⟩ := id hF
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC (0, 0))
  obtain ⟨B, hB, -⟩ := exists_isBoundedSpectralIntegral P hr hF hC0 hC
  exact Classical.epsilon_spec (p := P.IsBoundedSpectralIntegral F) ⟨B, hB⟩
theorem eq_boundedSpectralIntegral_of (hF : IsBoundedMeasurable F) {B : H →L[ℂ] H}
    (h : P.IsBoundedSpectralIntegral F B) : B = P.boundedSpectralIntegral F :=
  ContinuousLinearMap.ext fun v => ext_inner_left ℂ fun u => by
    rw [h u v, isBoundedSpectralIntegral_self P hr hF u v]
theorem norm_boundedSpectralIntegral_le_of_bound (hF : IsBoundedMeasurable F) {C : ℝ}
    (hC0 : 0 ≤ C) (hC : ∀ p, ‖F p‖ ≤ C) : ‖P.boundedSpectralIntegral F‖ ≤ C := by
  obtain ⟨B, hB, hn⟩ := exists_isBoundedSpectralIntegral P hr hF hC0 hC
  rwa [← eq_boundedSpectralIntegral_of P hr hF hB]
theorem boundedSpectralIntegral_add_fun (hF : IsBoundedMeasurable F)
    (hG : IsBoundedMeasurable G) :
    P.boundedSpectralIntegral (fun p => F p + G p) =
      P.boundedSpectralIntegral F + P.boundedSpectralIntegral G := by
  refine (eq_boundedSpectralIntegral_of P hr (isBoundedMeasurable_add hF hG)
    fun u v => ?_).symm
  rw [add_apply, inner_add_right,
    isBoundedSpectralIntegral_self P hr hF u v, isBoundedSpectralIntegral_self P hr hG u v,
    complexIntegral_add _ hF hG]
theorem boundedSpectralIntegral_const_mul (a : ℂ) (hF : IsBoundedMeasurable F) :
    P.boundedSpectralIntegral (fun p => a * F p) = a • P.boundedSpectralIntegral F := by
  refine (eq_boundedSpectralIntegral_of P hr
    (isBoundedMeasurable_mul (isBoundedMeasurable_const a) hF) fun u v => ?_).symm
  rw [smul_apply, inner_smul_right,
    isBoundedSpectralIntegral_self P hr hF u v, complexIntegral_const_mul _ a hF]
theorem boundedSpectralIntegral_indicator_const (c : ℂ) (B : MeasurableSubtype SpectralPlane) :
    P.boundedSpectralIntegral (B.1.indicator fun _ => c) = c • P B := by
  refine (eq_boundedSpectralIntegral_of P hr
    (isBoundedMeasurable_indicator (isBoundedMeasurable_const c) B.2) fun u v => ?_).symm
  rw [smul_apply, inner_smul_right, complexIntegral_indicator_const _ c B.2,
    P.matrixCoeff_apply u v B]
theorem boundedSpectralIntegral_indicator_one (B : MeasurableSubtype SpectralPlane) :
    P.boundedSpectralIntegral (B.1.indicator fun _ => 1) = P B := by
  rw [boundedSpectralIntegral_indicator_const P hr, one_smul]
theorem boundedSpectralIntegral_one : P.boundedSpectralIntegral (fun _ => 1) = 1 := by
  have h := boundedSpectralIntegral_indicator_one P hr ⟨univ, MeasurableSet.univ⟩
  rw [P.map_univ] at h
  simpa using h
theorem inner_boundedSpectralIntegral_left (hF : IsBoundedMeasurable F) (u v : H) :
    inner ℂ (P.boundedSpectralIntegral F u) v =
      inner ℂ u (P.boundedSpectralIntegral (fun p => conj (F p)) v) := by
  rw [isBoundedSpectralIntegral_self P hr (isBoundedMeasurable_conj hF) u v,
    complexIntegral_conj_of_apply (ν := P.matrixCoeff v u) (fun s hs => ?_) hF,
    ← isBoundedSpectralIntegral_self P hr hF v u, inner_conj_symm]
  rw [matrixCoeff_apply_set P _ _ hs, matrixCoeff_apply_set P _ _ hs, inner_conj_symm,
    inner_apply_left_eq]
theorem tendsto_inner_boundedSpectralIntegral {F : ℕ → SpectralPlane → ℂ}
    {G : SpectralPlane → ℂ} {C : ℝ} (hF : ∀ n, IsBoundedMeasurable (F n))
    (hG : IsBoundedMeasurable G) (hC : ∀ n p, ‖F n p‖ ≤ C)
    (hl : ∀ p, Tendsto (fun n => F n p) atTop (𝓝 (G p))) (u v : H) :
    Tendsto (fun n => inner ℂ u (P.boundedSpectralIntegral (F n) v)) atTop
      (𝓝 (inner ℂ u (P.boundedSpectralIntegral G v))) := by
  simp only [fun n => isBoundedSpectralIntegral_self P hr (hF n) u v,
    isBoundedSpectralIntegral_self P hr hG u v]
  exact tendsto_complexIntegral _ hF hC hl
theorem apply_mul_boundedSpectralIntegral (B : MeasurableSubtype SpectralPlane)
    (hF : IsBoundedMeasurable F) :
    P B * P.boundedSpectralIntegral F = P.boundedSpectralIntegral (B.1.indicator F) := by
  refine boundedMeasurable_induction
    (Q := fun F => P B * P.boundedSpectralIntegral F =
      P.boundedSpectralIntegral (B.1.indicator F)) ?_ ?_ ?_ hF
  · intro c s hs
    have h : B.1.indicator (s.indicator fun _ => c) = (B.1 ∩ s).indicator fun _ => c := by
      rw [Set.indicator_indicator]
    rw [h, boundedSpectralIntegral_indicator_const P hr c ⟨s, hs⟩,
      boundedSpectralIntegral_indicator_const P hr c ⟨B.1 ∩ s, B.2.inter hs⟩, mul_smul_comm,
      P.map_inter]
  · intro F G hF hG h₁ h₂
    have h : B.1.indicator (fun p => F p + G p) =
        fun p => B.1.indicator F p + B.1.indicator G p := by
      funext p
      by_cases hp : p ∈ B.1 <;> simp [hp]
    rw [h, boundedSpectralIntegral_add_fun P hr hF hG,
      boundedSpectralIntegral_add_fun P hr (isBoundedMeasurable_indicator hF B.2)
        (isBoundedMeasurable_indicator hG B.2), mul_add, h₁, h₂]
  · intro F G C hF hG hC hl hQ
    have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 0 (0, 0))
    refine ContinuousLinearMap.ext fun v => ext_inner_left ℂ fun u => ?_
    have h₁ := tendsto_inner_boundedSpectralIntegral P hr hF hG hC hl (P B u) v
    have h₂ := tendsto_inner_boundedSpectralIntegral P hr (F := fun n => B.1.indicator (F n))
      (G := B.1.indicator G) (C := C) (fun n => isBoundedMeasurable_indicator (hF n) B.2)
      (isBoundedMeasurable_indicator hG B.2) (fun n p => by
        by_cases hp : p ∈ B.1
        · simpa [hp] using hC n p
        · simp [hp, hC0])
      (fun p => by
        by_cases hp : p ∈ B.1
        · simpa [hp] using hl p
        · simp [hp]) u v
    have h₃ : ∀ n, inner ℂ (P B u) (P.boundedSpectralIntegral (F n) v) =
        inner ℂ u (P.boundedSpectralIntegral (B.1.indicator (F n)) v) := fun n => by
      rw [inner_apply_left_eq, ← hQ n]
      rfl
    simp only [h₃] at h₁
    have := tendsto_nhds_unique h₁ h₂
    rw [inner_apply_left_eq] at this
    exact this
theorem boundedSpectralIntegral_mul_fun (hF : IsBoundedMeasurable F)
    (hF' : IsBoundedMeasurable F') :
    P.boundedSpectralIntegral F * P.boundedSpectralIntegral F' =
      P.boundedSpectralIntegral fun p => F p * F' p := by
  refine boundedMeasurable_induction
    (Q := fun F => P.boundedSpectralIntegral F * P.boundedSpectralIntegral F' =
      P.boundedSpectralIntegral fun p => F p * F' p) ?_ ?_ ?_ hF
  · intro c s hs
    have h : (fun p => s.indicator (fun _ => c) p * F' p) =
        fun p => c * s.indicator F' p := by
      funext p
      by_cases hp : p ∈ s <;> simp [hp]
    rw [h, boundedSpectralIntegral_indicator_const P hr c ⟨s, hs⟩,
      boundedSpectralIntegral_const_mul P hr c (isBoundedMeasurable_indicator hF' hs),
      smul_mul_assoc, apply_mul_boundedSpectralIntegral P hr ⟨s, hs⟩ hF']
  · intro F G hF hG h₁ h₂
    have h : (fun p => (F p + G p) * F' p) = fun p => F p * F' p + G p * F' p := by
      funext p
      ring
    rw [h, boundedSpectralIntegral_add_fun P hr hF hG,
      boundedSpectralIntegral_add_fun P hr (isBoundedMeasurable_mul hF hF')
        (isBoundedMeasurable_mul hG hF'),
      add_mul, h₁, h₂]
  · intro F G C hF hG hC hl hQ
    obtain ⟨hm', D, hD⟩ := id hF'
    have hD0 : 0 ≤ D := (norm_nonneg _).trans (hD (0, 0))
    have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 0 (0, 0))
    refine ContinuousLinearMap.ext fun v => ext_inner_left ℂ fun u => ?_
    have h₁ := tendsto_inner_boundedSpectralIntegral P hr hF hG hC hl u
      (P.boundedSpectralIntegral F' v)
    have h₂ := tendsto_inner_boundedSpectralIntegral P hr (F := fun n p => F n p * F' p)
      (G := fun p => G p * F' p) (C := C * D) (fun n => isBoundedMeasurable_mul (hF n) hF')
      (isBoundedMeasurable_mul hG hF') (fun n p => by
        rw [norm_mul]
        exact mul_le_mul (hC n p) (hD p) (norm_nonneg _) hC0)
      (fun p => (hl p).mul_const _) u v
    have h₃ : ∀ n, inner ℂ u (P.boundedSpectralIntegral (F n) (P.boundedSpectralIntegral F' v)) =
        inner ℂ u (P.boundedSpectralIntegral (fun p => F n p * F' p) v) := fun n => by
      rw [← hQ n]
      rfl
    simp only [h₃] at h₁
    exact tendsto_nhds_unique h₁ h₂
theorem norm_sq_boundedSpectralIntegral_eq (hF : IsBoundedMeasurable F) (v : H) :
    ((‖P.boundedSpectralIntegral F v‖ ^ 2 : ℝ) : ℂ) =
      complexIntegral (P.matrixCoeff v v) fun p => ((‖F p‖ ^ 2 : ℝ) : ℂ) := by
  have h₁ : (fun p => ((‖F p‖ ^ 2 : ℝ) : ℂ)) = fun p => conj (F p) * F p := by
    funext p
    rw [Complex.conj_mul']
    push_cast
    rfl
  rw [h₁, ← isBoundedSpectralIntegral_self P hr
    (isBoundedMeasurable_mul (isBoundedMeasurable_conj hF) hF) v v,
    ← boundedSpectralIntegral_mul_fun P hr (isBoundedMeasurable_conj hF) hF]
  change _ = inner ℂ v (P.boundedSpectralIntegral (fun p => conj (F p))
    (P.boundedSpectralIntegral F v))
  rw [← inner_boundedSpectralIntegral_left P hr hF, inner_self_eq_norm_sq_to_K]
  push_cast
  rfl
end Bounded
section Helpers
theorem enorm_sq_eq_ofReal {E : Type*} [NormedAddCommGroup E] (z : E) :
    ‖z‖ₑ ^ 2 = ENNReal.ofReal (‖z‖ ^ 2) := by
  rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]
theorem norm_add_sq_le_two_mul {E : Type*} [NormedAddCommGroup E] (x y : E) :
    ‖x + y‖ ^ 2 ≤ 2 * ‖x‖ ^ 2 + 2 * ‖y‖ ^ 2 := by apply _root_.YangMills.Construction.BorelCalculus.Unbounded.norm_add_sq_le_two_mul <;> assumption
theorem enorm_add_sq_le_two_mul {E : Type*} [NormedAddCommGroup E] (x y : E) :
    ‖x + y‖ₑ ^ 2 ≤ 2 * ‖x‖ₑ ^ 2 + 2 * ‖y‖ₑ ^ 2 := by
  have h2 : (2 : ℝ≥0∞) = ENNReal.ofReal 2 := by simp
  rw [enorm_sq_eq_ofReal, enorm_sq_eq_ofReal, enorm_sq_eq_ofReal, h2,
    ← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_mul (by norm_num),
    ← ENNReal.ofReal_add (by positivity) (by positivity)]
  exact ENNReal.ofReal_le_ofReal (norm_add_sq_le_two_mul x y)
theorem enorm_sub_sq_le_two_mul {E : Type*} [NormedAddCommGroup E] (x y : E) :
    ‖x - y‖ₑ ^ 2 ≤ 2 * ‖x‖ₑ ^ 2 + 2 * ‖y‖ₑ ^ 2 := by
  have := enorm_add_sq_le_two_mul x (-y)
  rwa [← sub_eq_add_neg, enorm_neg] at this
theorem tendsto_zero_of_enorm_sq_tendsto_zero {E ι : Type*} [NormedAddCommGroup E]
    {l : Filter ι} {f : ι → E}
    (h : Tendsto (fun i => ‖f i‖ₑ ^ 2) l (𝓝 0)) : Tendsto f l (𝓝 0) := by
  have h₂ : ∀ i, (‖f i‖ₑ ^ 2).toReal = ‖f i‖ ^ 2 := fun i => by
    simp [ENNReal.toReal_pow]
  have h₁ : Tendsto (fun i => ‖f i‖ ^ 2) l (𝓝 0) := by
    have h₀ := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp h
    simp only [ENNReal.toReal_zero] at h₀
    exact h₀.congr h₂
  have h₃ := (Real.continuous_sqrt.tendsto 0).comp h₁
  simp only [Function.comp_def, Real.sqrt_sq (norm_nonneg _), Real.sqrt_zero] at h₃
  exact tendsto_zero_iff_norm_tendsto_zero.mpr h₃
theorem lintegral_enorm_sq_le_of_tendsto {μ : Measure SpectralPlane} {F : SpectralPlane → ℂ}
    {G : ℕ → SpectralPlane → ℂ} {C : ℝ≥0∞} (hG : ∀ n, Measurable (G n))
    (hl : ∀ p, Tendsto (fun n => G n p) atTop (𝓝 (F p)))
    (hC : ∀ n, ∫⁻ p, ‖G n p‖ₑ ^ 2 ∂μ ≤ C) : ∫⁻ p, ‖F p‖ₑ ^ 2 ∂μ ≤ C := by
  calc ∫⁻ p, ‖F p‖ₑ ^ 2 ∂μ = ∫⁻ p, liminf (fun n => ‖G n p‖ₑ ^ 2) atTop ∂μ :=
        lintegral_congr fun p => (ENNReal.Tendsto.pow (hl p).enorm).liminf_eq.symm
    _ ≤ liminf (fun n => ∫⁻ p, ‖G n p‖ₑ ^ 2 ∂μ) atTop :=
        lintegral_liminf_le fun n => (hG n).enorm.pow_const 2
    _ ≤ C := by
        refine Filter.liminf_le_of_le (by isBoundedDefault) fun b hb => ?_
        obtain ⟨n, hn⟩ := hb.exists
        exact hn.trans (hC n)
end Helpers
section Unbounded
variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (P : ProjValuedMeasure H)
variable {F F' G : SpectralPlane → ℂ}
abbrev spectralMeasureOf (v : H) : Measure SpectralPlane := (P.matrixCoeff v v).variation
theorem complexIntegral_matrixCoeff_self (hF : IsBoundedMeasurable F) (v : H) :
    complexIntegral (P.matrixCoeff v v) F = ∫ p, F p ∂spectralMeasureOf P v := by
  refine boundedMeasurable_induction
    (Q := fun F => complexIntegral (P.matrixCoeff v v) F = ∫ p, F p ∂spectralMeasureOf P v)
    ?_ ?_ ?_ hF
  · intro c s hs
    rw [complexIntegral_indicator_const _ _ hs, MeasureTheory.integral_indicator_const c hs,
      variation_matrixCoeff_self_real P v hs, matrixCoeff_self P v hs, Complex.real_smul]
    ring
  · intro F G hF hG h₁ h₂
    rw [complexIntegral_add _ hF hG, h₁, h₂, MeasureTheory.integral_add
      (integrable_of_isBoundedMeasurable _ hF) (integrable_of_isBoundedMeasurable _ hG)]
  · intro F G C hF _ hC hl hQ
    refine tendsto_nhds_unique (tendsto_complexIntegral _ hF hC hl) ?_
    simp only [hQ]
    exact tendsto_integral_of_dominated_convergence (fun _ => C)
      (fun n => (hF n).1.aestronglyMeasurable) (integrable_const C)
      (fun n => Eventually.of_forall (hC n)) (Eventually.of_forall hl)
theorem spectralMeasureOf_add_le (u v : H) :
    spectralMeasureOf P (u + v) ≤
      (2 : ℝ≥0∞) • spectralMeasureOf P u + (2 : ℝ≥0∞) • spectralMeasureOf P v := by
  refine Measure.le_iff.mpr fun s hs => ?_
  have h2 : (2 : ℝ≥0∞) = ENNReal.ofReal 2 := by simp
  simp only [Measure.add_apply, Measure.smul_apply, smul_eq_mul,
    variation_matrixCoeff_self P _ hs, map_add]
  rw [h2, ← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_mul (by norm_num),
    ← ENNReal.ofReal_add (by positivity) (by positivity)]
  exact ENNReal.ofReal_le_ofReal (norm_add_sq_le_two_mul _ _)
theorem spectralMeasureOf_smul_le (a : ℂ) (v : H) :
    spectralMeasureOf P (a • v) ≤ ENNReal.ofReal (‖a‖ ^ 2) • spectralMeasureOf P v := by
  refine Measure.le_iff.mpr fun s hs => ?_
  simp only [Measure.smul_apply, smul_eq_mul, variation_matrixCoeff_self P _ hs, map_smul]
  rw [← ENNReal.ofReal_mul (by positivity), norm_smul, mul_pow]
def spectralDomainSubmodule (F : SpectralPlane → ℂ) : Submodule ℂ H where
  carrier := P.spectralDomain F
  add_mem' := by
    intro u v hu hv
    have h : ∫⁻ p, ‖F p‖ₑ ^ 2 ∂spectralMeasureOf P (u + v) ≤
        ∫⁻ p, ‖F p‖ₑ ^ 2 ∂((2 : ℝ≥0∞) • spectralMeasureOf P u +
          (2 : ℝ≥0∞) • spectralMeasureOf P v) :=
      lintegral_mono' (spectralMeasureOf_add_le P u v) le_rfl
    rw [lintegral_add_measure, lintegral_smul_measure, lintegral_smul_measure] at h
    refine lt_of_le_of_lt h (ENNReal.add_lt_top.mpr ⟨?_, ?_⟩)
    · exact ENNReal.mul_lt_top (by simp) hu
    · exact ENNReal.mul_lt_top (by simp) hv
  zero_mem' := by
    change ∫⁻ p, ‖F p‖ₑ ^ 2 ∂(P.matrixCoeff 0 0).variation < ∞
    rw [matrixCoeff_zero_left]
    simp
  smul_mem' := by
    intro a v hv
    have h : ∫⁻ p, ‖F p‖ₑ ^ 2 ∂spectralMeasureOf P (a • v) ≤
        ∫⁻ p, ‖F p‖ₑ ^ 2 ∂(ENNReal.ofReal (‖a‖ ^ 2) • spectralMeasureOf P v) :=
      lintegral_mono' (spectralMeasureOf_smul_le P a v) le_rfl
    rw [lintegral_smul_measure] at h
    exact lt_of_le_of_lt h (ENNReal.mul_lt_top (by simp) hv)
theorem tendsto_lintegral_indicator_sub_self {v : H} (hF : Measurable F)
    {B : ℕ → MeasurableSubtype SpectralPlane} (hmono : Monotone fun n => (B n).1)
    (hU : ⋃ n, (B n).1 = univ) (hv : v ∈ P.spectralDomain F) :
    Tendsto (fun n => ∫⁻ p, ‖(B n).1.indicator F p - F p‖ₑ ^ 2 ∂spectralMeasureOf P v) atTop
      (𝓝 0) := by
  have h := tendsto_lintegral_filter_of_dominated_convergence (μ := spectralMeasureOf P v)
    (l := atTop) (F := fun n p => ‖(B n).1.indicator F p - F p‖ₑ ^ 2) (f := fun _ => 0)
    (fun p => ‖F p‖ₑ ^ 2)
    (Eventually.of_forall fun n => ((hF.indicator (B n).2).sub hF).enorm.pow_const 2)
    (Eventually.of_forall fun n => ae_of_all _ fun p => by
      by_cases hp : p ∈ (B n).1 <;> simp [hp])
    hv.ne
    (ae_of_all _ fun p => by
      have hp : p ∈ ⋃ n, (B n).1 := by
        rw [hU]
        exact mem_univ p
      obtain ⟨N, hN⟩ := mem_iUnion.mp hp
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [eventually_ge_atTop N] with n hn
      have : p ∈ (B n).1 := hmono hn hN
      simp [this])
  simpa using h
def normSublevel (hF : Measurable F) (n : ℕ) : MeasurableSubtype SpectralPlane :=
  ⟨{p | ‖F p‖ ≤ n}, measurableSet_le hF.norm measurable_const⟩
theorem monotone_normSublevel (hF : Measurable F) : Monotone fun n => (normSublevel hF n).1 := by
  intro a b h p hp
  change ‖F p‖ ≤ (b : ℝ)
  exact le_trans hp (Nat.cast_le.mpr h)
theorem iUnion_normSublevel (hF : Measurable F) : ⋃ n, (normSublevel hF n).1 = univ :=
  eq_univ_of_forall fun p => by
    obtain ⟨n, hn⟩ := exists_nat_ge ‖F p‖
    exact mem_iUnion.mpr ⟨n, hn⟩
theorem isBoundedMeasurable_truncate (hF : Measurable F) (n : ℕ) :
    IsBoundedMeasurable (ProjValuedMeasure.truncate F n) := by
  refine ⟨hF.indicator (normSublevel hF n).2, n, fun p => ?_⟩
  by_cases hp : ‖F p‖ ≤ n
  · simp [ProjValuedMeasure.truncate, hp]
  · simp [ProjValuedMeasure.truncate, hp]
theorem tendsto_truncate (F : SpectralPlane → ℂ) (p : SpectralPlane) :
    Tendsto (fun n => ProjValuedMeasure.truncate F n p) atTop (𝓝 (F p)) := by
  obtain ⟨N, hN⟩ := exists_nat_ge ‖F p‖
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [eventually_ge_atTop N] with n hn
  have : ‖F p‖ ≤ n := hN.trans (Nat.cast_le.mpr hn)
  simp [ProjValuedMeasure.truncate, this]
theorem enorm_truncate_le (F : SpectralPlane → ℂ) (n : ℕ) (p : SpectralPlane) :
    ‖ProjValuedMeasure.truncate F n p‖ₑ ≤ ‖F p‖ₑ := by
  by_cases hp : ‖F p‖ ≤ n <;> simp [ProjValuedMeasure.truncate, hp]
variable (hr : HilbertSpace.BoundedSesqRep.Claim)
include hr
theorem norm_sq_boundedSpectralIntegral_eq_integral (hF : IsBoundedMeasurable F) (v : H) :
    ‖P.boundedSpectralIntegral F v‖ ^ 2 = ∫ p, ‖F p‖ ^ 2 ∂spectralMeasureOf P v := by
  have hb : IsBoundedMeasurable fun p => ((‖F p‖ ^ 2 : ℝ) : ℂ) := by
    obtain ⟨hm, C, hC⟩ := hF
    refine ⟨Complex.measurable_ofReal.comp (hm.norm.pow_const 2), C ^ 2, fun p => ?_⟩
    rw [Complex.norm_real, Real.norm_of_nonneg (by positivity)]
    exact pow_le_pow_left₀ (norm_nonneg _) (hC p) 2
  have h := norm_sq_boundedSpectralIntegral_eq P hr hF v
  rw [complexIntegral_matrixCoeff_self P hb v, integral_complex_ofReal] at h
  exact_mod_cast h
theorem enorm_sq_boundedSpectralIntegral (hF : IsBoundedMeasurable F) (v : H) :
    ‖P.boundedSpectralIntegral F v‖ₑ ^ 2 = ∫⁻ p, ‖F p‖ₑ ^ 2 ∂spectralMeasureOf P v := by
  have hint : Integrable (fun p => ‖F p‖ ^ 2) (spectralMeasureOf P v) := by
    obtain ⟨hm, C, hC⟩ := hF
    refine Integrable.of_bound (hm.norm.pow_const 2).aestronglyMeasurable (C ^ 2)
      (ae_of_all _ fun p => ?_)
    rw [Real.norm_of_nonneg (by positivity)]
    exact pow_le_pow_left₀ (norm_nonneg _) (hC p) 2
  rw [enorm_sq_eq_ofReal, norm_sq_boundedSpectralIntegral_eq_integral P hr hF v,
    ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ fun p => by positivity)]
  simp only [enorm_sq_eq_ofReal]
theorem boundedSpectralIntegral_sub (hF : IsBoundedMeasurable F) (hG : IsBoundedMeasurable G) :
    P.boundedSpectralIntegral (fun p => F p - G p) =
      P.boundedSpectralIntegral F - P.boundedSpectralIntegral G := by
  have h : (fun p => F p - G p) = fun p => F p + (-1) * G p := by
    funext p
    ring
  rw [h, boundedSpectralIntegral_add_fun P hr hF
      (isBoundedMeasurable_mul (isBoundedMeasurable_const _) hG),
    boundedSpectralIntegral_const_mul P hr _ hG]
  simp [sub_eq_add_neg]
theorem enorm_sub_boundedSpectralIntegral_sq (hF : IsBoundedMeasurable F)
    (hG : IsBoundedMeasurable G) (v : H) :
    ‖P.boundedSpectralIntegral F v - P.boundedSpectralIntegral G v‖ₑ ^ 2 =
      ∫⁻ p, ‖F p - G p‖ₑ ^ 2 ∂spectralMeasureOf P v := by
  have hb : IsBoundedMeasurable fun p => F p - G p := by
    have h : (fun p => F p - G p) = fun p => F p + (-1) * G p := by
      funext p
      ring
    rw [h]
    exact isBoundedMeasurable_add hF (isBoundedMeasurable_mul (isBoundedMeasurable_const _) hG)
  rw [← enorm_sq_boundedSpectralIntegral P hr hb v, boundedSpectralIntegral_sub P hr hF hG]
  rfl
theorem spectralMeasureOf_boundedSpectralIntegral (hG : IsBoundedMeasurable G) (v : H) :
    spectralMeasureOf P (P.boundedSpectralIntegral G v) =
      (spectralMeasureOf P v).withDensity fun p => ‖G p‖ₑ ^ 2 := by
  refine Measure.ext fun s hs => ?_
  have h₁ : P ⟨s, hs⟩ (P.boundedSpectralIntegral G v) =
      P.boundedSpectralIntegral (s.indicator G) v :=
    DFunLike.congr_fun (apply_mul_boundedSpectralIntegral P hr ⟨s, hs⟩ hG) v
  rw [variation_matrixCoeff_self P _ hs, h₁, ← enorm_sq_eq_ofReal,
    enorm_sq_boundedSpectralIntegral P hr (isBoundedMeasurable_indicator hG hs) v,
    withDensity_apply _ hs, ← lintegral_indicator hs]
  refine lintegral_congr fun p => ?_
  by_cases hp : p ∈ s <;> simp [hp]
theorem lintegral_spectralMeasureOf_boundedSpectralIntegral (hG : IsBoundedMeasurable G)
    {f : SpectralPlane → ℝ≥0∞} (hf : Measurable f) (v : H) :
    ∫⁻ p, f p ∂spectralMeasureOf P (P.boundedSpectralIntegral G v) =
      ∫⁻ p, ‖G p‖ₑ ^ 2 * f p ∂spectralMeasureOf P v := by
  rw [spectralMeasureOf_boundedSpectralIntegral P hr hG v,
    lintegral_withDensity_eq_lintegral_mul _ (hG.1.enorm.pow_const 2) hf]
  rfl
theorem cauchySeq_truncate (hF : Measurable F) {v : H} (hv : v ∈ P.spectralDomain F) :
    CauchySeq fun n => P.boundedSpectralIntegral (ProjValuedMeasure.truncate F n) v := by
  have ha := tendsto_lintegral_indicator_sub_self P hF (monotone_normSublevel hF)
    (iUnion_normSublevel hF) hv
  set a : ℕ → ℝ≥0∞ := fun n =>
    ∫⁻ p, ‖(normSublevel hF n).1.indicator F p - F p‖ₑ ^ 2 ∂spectralMeasureOf P v with hadef
  have hsum : Tendsto (fun q : ℕ × ℕ => 2 * a q.1 + 2 * a q.2) atTop (𝓝 0) := by
    have h₁ : Tendsto (fun n => 2 * a n) atTop (𝓝 0) := by
      simpa using ENNReal.Tendsto.const_mul ha (Or.inr (by simp : (2 : ℝ≥0∞) ≠ ∞))
    rw [← prod_atTop_atTop_eq]
    simpa using (h₁.comp tendsto_fst).add (h₁.comp tendsto_snd)
  have hle : ∀ q : ℕ × ℕ,
      ‖P.boundedSpectralIntegral (ProjValuedMeasure.truncate F q.1) v -
        P.boundedSpectralIntegral (ProjValuedMeasure.truncate F q.2) v‖ₑ ^ 2 ≤
      2 * a q.1 + 2 * a q.2 := by
    intro q
    rw [enorm_sub_boundedSpectralIntegral_sq P hr (isBoundedMeasurable_truncate hF _)
      (isBoundedMeasurable_truncate hF _) v]
    have hpt : ∀ p, ‖ProjValuedMeasure.truncate F q.1 p -
        ProjValuedMeasure.truncate F q.2 p‖ₑ ^ 2 ≤
        2 * ‖(normSublevel hF q.1).1.indicator F p - F p‖ₑ ^ 2 +
          2 * ‖(normSublevel hF q.2).1.indicator F p - F p‖ₑ ^ 2 := fun p => by
      have := enorm_sub_sq_le_two_mul ((normSublevel hF q.1).1.indicator F p - F p)
        ((normSublevel hF q.2).1.indicator F p - F p)
      rwa [sub_sub_sub_cancel_right] at this
    have hm : ∀ n, Measurable fun p =>
        ‖(normSublevel hF n).1.indicator F p - F p‖ₑ ^ 2 := fun n =>
      ((hF.indicator (normSublevel hF n).2).sub hF).enorm.pow_const 2
    calc _ ≤ ∫⁻ p, 2 * ‖(normSublevel hF q.1).1.indicator F p - F p‖ₑ ^ 2 +
            2 * ‖(normSublevel hF q.2).1.indicator F p - F p‖ₑ ^ 2 ∂spectralMeasureOf P v :=
          lintegral_mono hpt
      _ = 2 * a q.1 + 2 * a q.2 := by
          rw [lintegral_add_left ((hm _).const_mul _), lintegral_const_mul _ (hm _),
            lintegral_const_mul _ (hm _)]
  have hz : Tendsto (fun q : ℕ × ℕ =>
      P.boundedSpectralIntegral (ProjValuedMeasure.truncate F q.1) v -
        P.boundedSpectralIntegral (ProjValuedMeasure.truncate F q.2) v) atTop (𝓝 0) :=
    tendsto_zero_of_enorm_sq_tendsto_zero (tendsto_of_tendsto_of_tendsto_of_le_of_le
      tendsto_const_nhds hsum (fun _ => zero_le) hle)
  refine cauchySeq_iff_tendsto_dist_atTop_0.mpr ?_
  simpa only [dist_eq_norm] using tendsto_zero_iff_norm_tendsto_zero.mp hz
theorem exists_isSpectralIntegral (hF : Measurable F) : ∃ A, P.IsSpectralIntegral F A := by
  have hlim : ∀ v : spectralDomainSubmodule P F, Tendsto
      (fun n => P.boundedSpectralIntegral (ProjValuedMeasure.truncate F n) (v : H)) atTop
      (𝓝 (limUnder atTop
        fun n => P.boundedSpectralIntegral (ProjValuedMeasure.truncate F n) (v : H))) :=
    fun v => (cauchySeq_truncate P hr hF v.2).tendsto_limUnder
  let L : spectralDomainSubmodule P F →ₗ[ℂ] H :=
    { toFun := fun v => limUnder atTop
        fun n => P.boundedSpectralIntegral (ProjValuedMeasure.truncate F n) (v : H)
      map_add' := fun u v => tendsto_nhds_unique (hlim (u + v)) (by
        simpa using (hlim u).add (hlim v))
      map_smul' := fun a v => tendsto_nhds_unique (hlim (a • v)) (by
        simpa using (hlim v).const_smul a) }
  exact ⟨⟨spectralDomainSubmodule P F, L⟩, rfl, hlim⟩
theorem isSpectralIntegral_spectralIntegral (hF : Measurable F) :
    P.IsSpectralIntegral F (P.spectralIntegral F) := by
  obtain ⟨A, hA⟩ := exists_isSpectralIntegral P hr hF
  exact Classical.epsilon_spec (p := P.IsSpectralIntegral F) ⟨A, hA⟩
theorem mem_spectralIntegral_domain_iff (hF : Measurable F) (v : H) :
    v ∈ (P.spectralIntegral F).domain ↔ v ∈ P.spectralDomain F := by
  rw [← (isSpectralIntegral_spectralIntegral P hr hF).1]
  rfl
theorem tendsto_spectralIntegral (hF : Measurable F) (v : (P.spectralIntegral F).domain) :
    Tendsto (fun n => P.boundedSpectralIntegral (ProjValuedMeasure.truncate F n) (v : H)) atTop
      (𝓝 (P.spectralIntegral F v)) :=
  (isSpectralIntegral_spectralIntegral P hr hF).2 v
theorem lintegral_enorm_sq_ne_top_of_bounded (hG : IsBoundedMeasurable G) (v : H) :
    ∫⁻ p, ‖G p‖ₑ ^ 2 ∂spectralMeasureOf P v ≠ ∞ := by
  rw [← enorm_sq_boundedSpectralIntegral P hr hG v]
  exact (ENNReal.pow_lt_top enorm_lt_top).ne
theorem enorm_sub_spectralIntegral_sq (hF : Measurable F) (hG : IsBoundedMeasurable G)
    (v : (P.spectralIntegral F).domain) :
    ‖P.boundedSpectralIntegral G (v : H) - P.spectralIntegral F v‖ₑ ^ 2 =
      ∫⁻ p, ‖G p - F p‖ₑ ^ 2 ∂spectralMeasureOf P (v : H) := by
  have hv : (v : H) ∈ P.spectralDomain F := (mem_spectralIntegral_domain_iff P hr hF _).mp v.2
  have h₂ : Tendsto (fun n => ‖P.boundedSpectralIntegral G (v : H) -
      P.boundedSpectralIntegral (ProjValuedMeasure.truncate F n) (v : H)‖ₑ ^ 2) atTop
      (𝓝 (‖P.boundedSpectralIntegral G (v : H) - P.spectralIntegral F v‖ₑ ^ 2)) :=
    ENNReal.Tendsto.pow (tendsto_const_nhds.sub (tendsto_spectralIntegral P hr hF v)).enorm
  simp only [enorm_sub_boundedSpectralIntegral_sq P hr hG (isBoundedMeasurable_truncate hF _)]
    at h₂
  have hmG : Measurable fun p => ‖G p‖ₑ ^ 2 := hG.1.enorm.pow_const 2
  have hmF : Measurable fun p => ‖F p‖ₑ ^ 2 := hF.enorm.pow_const 2
  have h₃ : Tendsto (fun n => ∫⁻ p, ‖G p - ProjValuedMeasure.truncate F n p‖ₑ ^ 2
      ∂spectralMeasureOf P (v : H)) atTop
      (𝓝 (∫⁻ p, ‖G p - F p‖ₑ ^ 2 ∂spectralMeasureOf P (v : H))) := by
    refine tendsto_lintegral_of_dominated_convergence
      (fun p => 2 * ‖G p‖ₑ ^ 2 + 2 * ‖F p‖ₑ ^ 2)
      (fun n => (hG.1.sub (isBoundedMeasurable_truncate hF n).1).enorm.pow_const 2)
      (fun n => ae_of_all _ fun p => ?_) ?_ (ae_of_all _ fun p => ?_)
    · refine (enorm_sub_sq_le_two_mul _ _).trans ?_
      change 2 * ‖G p‖ₑ ^ 2 + 2 * ‖ProjValuedMeasure.truncate F n p‖ₑ ^ 2 ≤
        2 * ‖G p‖ₑ ^ 2 + 2 * ‖F p‖ₑ ^ 2
      gcongr
      exact enorm_truncate_le F n p
    · rw [lintegral_add_left (hmG.const_mul _), lintegral_const_mul _ hmG,
        lintegral_const_mul _ hmF]
      exact ENNReal.add_ne_top.mpr
        ⟨ENNReal.mul_ne_top (by simp) (lintegral_enorm_sq_ne_top_of_bounded P hr hG _),
          ENNReal.mul_ne_top (by simp) hv.ne⟩
    · exact ENNReal.Tendsto.pow (tendsto_const_nhds.sub (tendsto_truncate F p)).enorm
  exact tendsto_nhds_unique h₂ h₃
theorem tendsto_boundedSpectralIntegral_of_lintegral {ι : Type*} {l : Filter ι}
    {G : ι → SpectralPlane → ℂ} (hF : Measurable F) (hG : ∀ i, IsBoundedMeasurable (G i))
    (v : (P.spectralIntegral F).domain)
    (h : Tendsto (fun i => ∫⁻ p, ‖G i p - F p‖ₑ ^ 2 ∂spectralMeasureOf P (v : H)) l (𝓝 0)) :
    Tendsto (fun i => P.boundedSpectralIntegral (G i) (v : H)) l
      (𝓝 (P.spectralIntegral F v)) := by
  have hz : Tendsto (fun i => P.boundedSpectralIntegral (G i) (v : H) - P.spectralIntegral F v)
      l (𝓝 0) :=
    tendsto_zero_of_enorm_sq_tendsto_zero (by
      simpa only [enorm_sub_spectralIntegral_sq P hr hF (hG _)] using h)
  simpa using hz.add_const (P.spectralIntegral F v)
theorem boundedSpectralIntegral_zero : P.boundedSpectralIntegral (fun _ => 0) = 0 := by
  have h := boundedSpectralIntegral_const_mul P hr 0 (isBoundedMeasurable_const 0)
  simpa using h
theorem enorm_sq_spectralIntegral_eq (hF : Measurable F) (v : (P.spectralIntegral F).domain) :
    ‖P.spectralIntegral F v‖ₑ ^ 2 = ∫⁻ p, ‖F p‖ₑ ^ 2 ∂spectralMeasureOf P (v : H) := by
  have h := enorm_sub_spectralIntegral_sq P hr hF (isBoundedMeasurable_const 0) v
  simpa [boundedSpectralIntegral_zero P hr] using h
theorem eq_spectralIntegral_of (hF : Measurable F) {A : PartialOperator H}
    (hA : P.IsSpectralIntegral F A) : A = P.spectralIntegral F := by
  have hd : A.domain = (P.spectralIntegral F).domain :=
    SetLike.coe_injective (hA.1.trans (isSpectralIntegral_spectralIntegral P hr hF).1.symm)
  refine LinearPMap.ext hd fun x hx hy => ?_
  exact tendsto_nhds_unique (hA.2 ⟨x, hx⟩) (tendsto_spectralIntegral P hr hF ⟨x, hy⟩)
theorem spectralIntegral_of_isBoundedMeasurable_eq (hF : IsBoundedMeasurable F) :
    (P.spectralIntegral F).domain = ⊤ ∧
      ∀ v : (P.spectralIntegral F).domain,
        P.spectralIntegral F v = P.boundedSpectralIntegral F (v : H) := by
  constructor
  · refine (Submodule.eq_top_iff').mpr fun v =>
      (mem_spectralIntegral_domain_iff P hr hF.1 v).mpr ?_
    exact (lintegral_enorm_sq_ne_top_of_bounded P hr hF v).lt_top
  · intro v
    have h := enorm_sub_spectralIntegral_sq P hr hF.1 hF v
    simp only [sub_self, enorm_zero] at h
    have h₀ : ‖P.boundedSpectralIntegral F (v : H) - P.spectralIntegral F v‖ₑ ^ 2 = 0 := by
      rw [h]
      simp
    have h₁ : ‖P.boundedSpectralIntegral F (v : H) - P.spectralIntegral F v‖ₑ = 0 := by
      simpa using h₀
    exact (sub_eq_zero.mp (enorm_eq_zero.mp h₁)).symm
theorem tendsto_boundedSpectralIntegral_indicator_of (hF : Measurable F)
    {B : ℕ → MeasurableSubtype SpectralPlane} (hmono : Monotone fun n => (B n).1)
    (hU : ⋃ n, (B n).1 = univ) (hb : ∀ n, IsBoundedMeasurable ((B n).1.indicator F))
    (v : (P.spectralIntegral F).domain) :
    Tendsto (fun n => P.boundedSpectralIntegral ((B n).1.indicator F) (v : H)) atTop
      (𝓝 (P.spectralIntegral F v)) :=
  tendsto_boundedSpectralIntegral_of_lintegral P hr hF hb v
    (tendsto_lintegral_indicator_sub_self P hF hmono hU
      ((mem_spectralIntegral_domain_iff P hr hF _).mp v.2))
omit hr in
theorem isBoundedMeasurable_of_isBoundedExhaustion (hF : Measurable F)
    {B : ℕ → MeasurableSubtype SpectralPlane} (hB : IsBoundedExhaustion F B) (n : ℕ) :
    IsBoundedMeasurable ((B n).1.indicator F) := by
  obtain ⟨C, hC⟩ := hB.isBounded n
  refine ⟨hF.indicator (B n).2, max C 0, fun p => ?_⟩
  by_cases hp : p ∈ (B n).1
  · simpa [hp] using Or.inl (hC p hp)
  · simp [hp]
theorem apply_normSublevel_eq (hF : Measurable F) (n : ℕ) (v : H) :
    P (normSublevel hF n) v =
      P.boundedSpectralIntegral ((normSublevel hF n).1.indicator fun _ => 1) v := by
  rw [boundedSpectralIntegral_indicator_one P hr]
theorem apply_normSublevel_mem (hF : Measurable F) (n : ℕ) (v : H) :
    P (normSublevel hF n) v ∈ P.spectralDomain F := by
  change ∫⁻ p, ‖F p‖ₑ ^ 2 ∂spectralMeasureOf P (P (normSublevel hF n) v) < ∞
  rw [apply_normSublevel_eq P hr hF n v, lintegral_spectralMeasureOf_boundedSpectralIntegral P hr
    (isBoundedMeasurable_indicator (isBoundedMeasurable_const 1) (normSublevel hF n).2)
    (hF.enorm.pow_const 2) v]
  have h : ∀ p, ‖(normSublevel hF n).1.indicator (fun _ => (1 : ℂ)) p‖ₑ ^ 2 * ‖F p‖ₑ ^ 2 =
      ‖ProjValuedMeasure.truncate F n p‖ₑ ^ 2 := fun p => by
    by_cases hp : ‖F p‖ ≤ n
    · have hp' : p ∈ (normSublevel hF n).1 := hp
      simp [ProjValuedMeasure.truncate, hp, hp']
    · have hp' : p ∉ (normSublevel hF n).1 := hp
      simp [ProjValuedMeasure.truncate, hp, hp']
  simp only [h]
  exact (lintegral_enorm_sq_ne_top_of_bounded P hr (isBoundedMeasurable_truncate hF n) v).lt_top
theorem isSeqDense_spectralDomain_of (hF : Measurable F) :
    IsSeqDense (P.spectralDomain F) := by
  intro v
  refine ⟨fun n => P (normSublevel hF n) v, fun n => apply_normSublevel_mem P hr hF n v, ?_⟩
  have hone : Measurable fun _ : SpectralPlane => (1 : ℂ) := measurable_const
  have hmem : v ∈ P.spectralDomain fun _ => (1 : ℂ) :=
    (lintegral_enorm_sq_ne_top_of_bounded P hr (isBoundedMeasurable_const 1) v).lt_top
  have h := tendsto_lintegral_indicator_sub_self P hone (monotone_normSublevel hF)
    (iUnion_normSublevel hF) hmem
  simp only [← enorm_sub_boundedSpectralIntegral_sq P hr
    (isBoundedMeasurable_indicator (isBoundedMeasurable_const 1) (normSublevel hF _).2)
    (isBoundedMeasurable_const 1) v, boundedSpectralIntegral_one P hr,
    boundedSpectralIntegral_indicator_one P hr] at h
  have hz := tendsto_zero_of_enorm_sq_tendsto_zero h
  simpa using hz.add_const v
theorem spectralIntegral_add_of (hF : Measurable F) (hF' : Measurable F') (v : H)
    (hv : v ∈ (P.spectralIntegral F).domain) (hv' : v ∈ (P.spectralIntegral F').domain) :
    ∃ hs : v ∈ (P.spectralIntegral fun p => F p + F' p).domain,
      (P.spectralIntegral fun p => F p + F' p) ⟨v, hs⟩ =
        P.spectralIntegral F ⟨v, hv⟩ + P.spectralIntegral F' ⟨v, hv'⟩ := by
  have hm : Measurable fun p => F p + F' p := hF.add hF'
  have hd : v ∈ P.spectralDomain F := (mem_spectralIntegral_domain_iff P hr hF v).mp hv
  have hd' : v ∈ P.spectralDomain F' := (mem_spectralIntegral_domain_iff P hr hF' v).mp hv'
  have hs : v ∈ (P.spectralIntegral fun p => F p + F' p).domain := by
    refine (mem_spectralIntegral_domain_iff P hr hm v).mpr ?_
    change ∫⁻ p, ‖F p + F' p‖ₑ ^ 2 ∂spectralMeasureOf P v < ∞
    have hmF : Measurable fun p => ‖F p‖ₑ ^ 2 := hF.enorm.pow_const 2
    have hmF' : Measurable fun p => ‖F' p‖ₑ ^ 2 := hF'.enorm.pow_const 2
    refine lt_of_le_of_lt (lintegral_mono fun p => enorm_add_sq_le_two_mul (F p) (F' p)) ?_
    rw [lintegral_add_left (hmF.const_mul _), lintegral_const_mul _ hmF,
      lintegral_const_mul _ hmF']
    exact ENNReal.add_lt_top.mpr
      ⟨ENNReal.mul_lt_top (by simp) hd, ENNReal.mul_lt_top (by simp) hd'⟩
  refine ⟨hs, ?_⟩
  let B : ℕ → MeasurableSubtype SpectralPlane := fun n =>
    ⟨(normSublevel hF n).1 ∩ (normSublevel hF' n).1,
      (normSublevel hF n).2.inter (normSublevel hF' n).2⟩
  have hmono : Monotone fun n => (B n).1 := fun a b h =>
    inter_subset_inter (monotone_normSublevel hF h) (monotone_normSublevel hF' h)
  have hU : ⋃ n, (B n).1 = univ := eq_univ_of_forall fun p => by
    obtain ⟨n, hn⟩ := exists_nat_ge (max ‖F p‖ ‖F' p‖)
    exact mem_iUnion.mpr ⟨n, (le_max_left _ _).trans hn, (le_max_right _ _).trans hn⟩
  have hb : ∀ n, IsBoundedMeasurable ((B n).1.indicator F) := fun n => by
    refine ⟨hF.indicator (B n).2, n, fun p => ?_⟩
    by_cases hp : p ∈ (B n).1
    · simpa [hp] using (show ‖F p‖ ≤ (n : ℝ) from hp.1)
    · simp [hp]
  have hb' : ∀ n, IsBoundedMeasurable ((B n).1.indicator F') := fun n => by
    refine ⟨hF'.indicator (B n).2, n, fun p => ?_⟩
    by_cases hp : p ∈ (B n).1
    · simpa [hp] using (show ‖F' p‖ ≤ (n : ℝ) from hp.2)
    · simp [hp]
  have hsum : ∀ n, (B n).1.indicator (fun p => F p + F' p) =
      fun p => (B n).1.indicator F p + (B n).1.indicator F' p := fun n => by
    funext p
    by_cases hp : p ∈ (B n).1 <;> simp [hp]
  have hb'' : ∀ n, IsBoundedMeasurable ((B n).1.indicator fun p => F p + F' p) := fun n => by
    rw [hsum]
    exact isBoundedMeasurable_add (hb n) (hb' n)
  have h₁ := tendsto_boundedSpectralIntegral_indicator_of P hr hF hmono hU hb ⟨v, hv⟩
  have h₂ := tendsto_boundedSpectralIntegral_indicator_of P hr hF' hmono hU hb' ⟨v, hv'⟩
  have h₃ := tendsto_boundedSpectralIntegral_indicator_of P hr hm hmono hU hb'' ⟨v, hs⟩
  simp only [hsum, boundedSpectralIntegral_add_fun P hr (hb _) (hb' _)] at h₃
  exact tendsto_nhds_unique h₃ (h₁.add h₂)
omit hr in
theorem conj_truncate (hre : ∀ p, (F p).im = 0) (n : ℕ) :
    (fun p => conj (ProjValuedMeasure.truncate F n p)) = ProjValuedMeasure.truncate F n := by
  funext p
  refine Complex.conj_eq_iff_im.mpr ?_
  by_cases hp : ‖F p‖ ≤ n
  · simp [ProjValuedMeasure.truncate, hp, hre p]
  · simp [ProjValuedMeasure.truncate, hp]
theorem spectralIntegral_apply_normSublevel (hF : Measurable F) (n : ℕ) (v : H)
    (x : (P.spectralIntegral F).domain) (hx : (x : H) = P (normSublevel hF n) v) :
    P.spectralIntegral F x = P.boundedSpectralIntegral (ProjValuedMeasure.truncate F n) v := by
  refine tendsto_nhds_unique (tendsto_spectralIntegral P hr hF x)
    (tendsto_const_nhds.congr' ?_)
  filter_upwards [eventually_ge_atTop n] with k hk
  have hb := isBoundedMeasurable_indicator (isBoundedMeasurable_const (1 : ℂ))
    (normSublevel hF n).2
  have h₁ : P.boundedSpectralIntegral (ProjValuedMeasure.truncate F k) (x : H) =
      P.boundedSpectralIntegral (fun p => ProjValuedMeasure.truncate F k p *
        (normSublevel hF n).1.indicator (fun _ => 1) p) v := by
    rw [← boundedSpectralIntegral_mul_fun P hr (isBoundedMeasurable_truncate hF k) hb, hx,
      apply_normSublevel_eq P hr hF n v]
    rfl
  have h₂ : (fun p => ProjValuedMeasure.truncate F k p *
      (normSublevel hF n).1.indicator (fun _ => 1) p) =
      ProjValuedMeasure.truncate F n := by
    funext p
    by_cases hp : ‖F p‖ ≤ n
    · have hp' : p ∈ (normSublevel hF n).1 := hp
      have hk' : ‖F p‖ ≤ k := hp.trans (Nat.cast_le.mpr hk)
      simp [ProjValuedMeasure.truncate, hp, hp', hk']
    · have hp' : p ∉ (normSublevel hF n).1 := hp
      simp [ProjValuedMeasure.truncate, hp, hp']
  rw [h₁, h₂]
theorem norm_apply_le_norm (B : MeasurableSubtype SpectralPlane) (w : H) : ‖P B w‖ ≤ ‖w‖ := by
  rw [← boundedSpectralIntegral_indicator_one P hr B]
  refine ((P.boundedSpectralIntegral _).le_opNorm w).trans ?_
  have h := norm_boundedSpectralIntegral_le_of_bound P hr
    (isBoundedMeasurable_indicator (isBoundedMeasurable_const (1 : ℂ)) B.2) zero_le_one
    (fun p => by by_cases hp : p ∈ B.1 <;> simp [hp])
  calc _ ≤ 1 * ‖w‖ := mul_le_mul_of_nonneg_right h (norm_nonneg _)
    _ = ‖w‖ := one_mul _
theorem isSelfAdjoint_spectralIntegral_of (hF : Measurable F) (hre : ∀ p, (F p).im = 0) :
    IsSelfAdjointPartial (P.spectralIntegral F) where
  dense_domain := by
    have h := isSeqDense_spectralDomain_of P hr hF
    rwa [← (isSpectralIntegral_spectralIntegral P hr hF).1] at h
  symmetric u v := by
    have h₁ := (tendsto_spectralIntegral P hr hF u).inner (𝕜 := ℂ)
      (tendsto_const_nhds (x := (v : H)))
    have h₂ := (tendsto_const_nhds (x := (u : H))).inner (𝕜 := ℂ)
      (tendsto_spectralIntegral P hr hF v)
    refine tendsto_nhds_unique h₁ (h₂.congr fun n => ?_)
    rw [inner_boundedSpectralIntegral_left P hr (isBoundedMeasurable_truncate hF n),
      conj_truncate hre]
  mem_domain u hu := by
    obtain ⟨w, hw⟩ := hu
    have key : ∀ n, P.boundedSpectralIntegral (ProjValuedMeasure.truncate F n) u =
        P (normSublevel hF n) w := by
      intro n
      refine ext_inner_right ℂ fun v' => ?_
      have hx : P (normSublevel hF n) v' ∈ (P.spectralIntegral F).domain :=
        (mem_spectralIntegral_domain_iff P hr hF _).mpr (apply_normSublevel_mem P hr hF n v')
      have h₁ := hw ⟨_, hx⟩
      rw [spectralIntegral_apply_normSublevel P hr hF n v' ⟨_, hx⟩ rfl] at h₁
      calc inner ℂ (P.boundedSpectralIntegral (ProjValuedMeasure.truncate F n) u) v'
          = inner ℂ u (P.boundedSpectralIntegral (fun p =>
              conj (ProjValuedMeasure.truncate F n p)) v') :=
            inner_boundedSpectralIntegral_left P hr (isBoundedMeasurable_truncate hF n) u v'
        _ = inner ℂ u (P.boundedSpectralIntegral (ProjValuedMeasure.truncate F n) v') := by
            rw [conj_truncate hre]
        _ = inner ℂ w (P (normSublevel hF n) v') := h₁
        _ = inner ℂ (P (normSublevel hF n) w) v' := (inner_apply_left_eq P _ w v').symm
    refine (mem_spectralIntegral_domain_iff P hr hF u).mpr ?_
    have hle : ∫⁻ p, ‖F p‖ₑ ^ 2 ∂spectralMeasureOf P u ≤ ‖w‖ₑ ^ 2 := by
      refine lintegral_enorm_sq_le_of_tendsto (fun n => (isBoundedMeasurable_truncate hF n).1)
        (tendsto_truncate F) fun n => ?_
      rw [← enorm_sq_boundedSpectralIntegral P hr (isBoundedMeasurable_truncate hF n) u, key n]
      have := norm_apply_le_norm P hr (normSublevel hF n) w
      rw [enorm_sq_eq_ofReal, enorm_sq_eq_ofReal]
      exact ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (norm_nonneg _) this 2)
    exact lt_of_le_of_lt hle (ENNReal.pow_lt_top enorm_lt_top)
theorem isPositive_spectralIntegral_of (hF : Measurable F) (hnn : ∀ p, 0 ≤ F p) :
    IsPositivePartial (P.spectralIntegral F) := by
  have hre : ∀ p, (F p).im = 0 := fun p => ((Complex.le_def.mp (hnn p)).2).symm
  refine ⟨isSelfAdjoint_spectralIntegral_of P hr hF hre, fun v => ?_⟩
  have h := (tendsto_const_nhds (x := (v : H))).inner (𝕜 := ℂ)
    (tendsto_spectralIntegral P hr hF v)
  refine ge_of_tendsto' h fun n => ?_
  have hb := isBoundedMeasurable_truncate hF n
  rw [isBoundedSpectralIntegral_self P hr hb, complexIntegral_matrixCoeff_self P hb]
  have hval : ∀ p, ProjValuedMeasure.truncate F n p =
      (((ProjValuedMeasure.truncate F n p).re : ℝ) : ℂ) := fun p => by
    by_cases hp : ‖F p‖ ≤ n
    · apply Complex.ext <;> simp [ProjValuedMeasure.truncate, hp, hre p]
    · simp [ProjValuedMeasure.truncate, hp]
  have hpos : ∀ p, 0 ≤ (ProjValuedMeasure.truncate F n p).re := fun p => by
    by_cases hp : ‖F p‖ ≤ n
    · simpa [ProjValuedMeasure.truncate, hp] using (Complex.le_def.mp (hnn p)).1
    · simp [ProjValuedMeasure.truncate, hp]
  have hint : ∫ p, ProjValuedMeasure.truncate F n p ∂spectralMeasureOf P (v : H) =
      ((∫ p, (ProjValuedMeasure.truncate F n p).re ∂spectralMeasureOf P (v : H) : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal]
    exact integral_congr_ae (ae_of_all _ hval)
  rw [hint]
  exact Complex.zero_le_real.mpr (integral_nonneg hpos)
theorem tendsto_boundedSpectralIntegral_of_dominated {ι : Type*} {l : Filter ι}
    [l.IsCountablyGenerated] {G : ι → SpectralPlane → ℂ} (hF : Measurable F)
    (hG : ∀ i, IsBoundedMeasurable (G i)) (hb : ∀ i p, ‖G i p‖ ≤ ‖F p‖)
    (hl : ∀ p, Tendsto (fun i => G i p) l (𝓝 (F p))) (v : (P.spectralIntegral F).domain) :
    Tendsto (fun i => P.boundedSpectralIntegral (G i) (v : H)) l
      (𝓝 (P.spectralIntegral F v)) := by
  refine tendsto_boundedSpectralIntegral_of_lintegral P hr hF hG v ?_
  have hv : (v : H) ∈ P.spectralDomain F := (mem_spectralIntegral_domain_iff P hr hF _).mp v.2
  have hmF : Measurable fun p => ‖F p‖ₑ ^ 2 := hF.enorm.pow_const 2
  have h := tendsto_lintegral_filter_of_dominated_convergence
    (μ := spectralMeasureOf P (v : H))
    (l := l) (F := fun i p => ‖G i p - F p‖ₑ ^ 2) (f := fun _ => 0)
    (fun p => 2 * ‖F p‖ₑ ^ 2 + 2 * ‖F p‖ₑ ^ 2)
    (Eventually.of_forall fun i => ((hG i).1.sub hF).enorm.pow_const 2)
    (Eventually.of_forall fun i => ae_of_all _ fun p => by
      refine (enorm_sub_sq_le_two_mul _ _).trans ?_
      have : ‖G i p‖ₑ ≤ ‖F p‖ₑ := enorm_le_iff_norm_le.mpr (hb i p)
      gcongr)
    (by
      rw [lintegral_add_left (hmF.const_mul _), lintegral_const_mul _ hmF]
      exact ENNReal.add_ne_top.mpr
        ⟨ENNReal.mul_ne_top (by simp) hv.ne, ENNReal.mul_ne_top (by simp) hv.ne⟩)
    (ae_of_all _ fun p => by
      have h₀ := ENNReal.Tendsto.pow (n := 2)
        ((hl p).sub (tendsto_const_nhds (x := F p))).enorm
      simpa using h₀)
  simpa using h
theorem mem_spectralIntegral_domain_of_tendsto {ι : Type*} {l : Filter ι}
    [l.IsCountablyGenerated] [l.NeBot] {G : ι → SpectralPlane → ℂ} (hF : Measurable F)
    (hG : ∀ i, IsBoundedMeasurable (G i)) (hl : ∀ p, Tendsto (fun i => G i p) l (𝓝 (F p)))
    {v w : H} (h : Tendsto (fun i => P.boundedSpectralIntegral (G i) v) l (𝓝 w)) :
    v ∈ (P.spectralIntegral F).domain := by
  obtain ⟨x, hx⟩ := exists_seq_tendsto l
  obtain ⟨M, hM⟩ := (h.comp hx).norm.bddAbove_range
  have hM' : ∀ n, ‖P.boundedSpectralIntegral (G (x n)) v‖ ≤ M := fun n => hM ⟨n, rfl⟩
  refine (mem_spectralIntegral_domain_iff P hr hF v).mpr ?_
  have hle : ∫⁻ p, ‖F p‖ₑ ^ 2 ∂spectralMeasureOf P v ≤ ENNReal.ofReal (M ^ 2) := by
    refine lintegral_enorm_sq_le_of_tendsto (G := fun n => G (x n)) (fun n => (hG _).1)
      (fun p => (hl p).comp hx) fun n => ?_
    rw [← enorm_sq_boundedSpectralIntegral P hr (hG _) v, enorm_sq_eq_ofReal]
    exact ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (norm_nonneg _) (hM' n) 2)
  exact lt_of_le_of_lt hle ENNReal.ofReal_lt_top
end Unbounded
section Exponentials
theorem norm_spectralCharacter_le (t : ℝ≥0) (s : ℝ) (p : SpectralPlane) :
    ‖spectralCharacter t s p‖ ≤ 1 := by
  have h : 0 ≤ (t : ℝ) * (p.1 : ℝ) := mul_nonneg t.2 p.1.2
  simp only [spectralCharacter, Complex.norm_exp, Complex.add_re, Complex.ofReal_re,
    Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_im, zero_mul, one_mul, sub_zero,
    add_zero, neg_mul, Real.exp_le_one_iff]
  linarith
theorem isBoundedMeasurable_spectralCharacter (t : ℝ≥0) (s : ℝ) :
    IsBoundedMeasurable (spectralCharacter t s) := by apply _root_.YangMills.Construction.SpectralCalculus.JointSpectralProof.isBoundedMeasurable_spectralCharacter <;> assumption
theorem measurable_coordFst : Measurable coordFst := by apply _root_.YangMills.Construction.ReflectionPositivity.DenseTimeReconstruction.measurable_lineEnergyCoord <;> assumption
theorem measurable_coordSnd : Measurable coordSnd := by apply _root_.YangMills.Construction.ReflectionPositivity.DenseTimeReconstruction.measurable_lineMomentumCoord <;> assumption
def fstDiffQuot (t : ℝ≥0) (p : SpectralPlane) : ℂ :=
  (((t : ℝ)⁻¹ : ℝ) : ℂ) * (1 - spectralCharacter t 0 p)
def sndDiffQuot (s : ℝ) (p : SpectralPlane) : ℂ :=
  (Complex.I * (s : ℂ))⁻¹ * (spectralCharacter 0 s p - 1)
theorem spectralCharacter_zero_right (t : ℝ≥0) (p : SpectralPlane) :
    spectralCharacter t 0 p = ((Real.exp (-(t : ℝ) * (p.1 : ℝ)) : ℝ) : ℂ) := by
  simp [spectralCharacter]
theorem spectralCharacter_zero_left (s : ℝ) (p : SpectralPlane) :
    spectralCharacter 0 s p = Complex.exp (Complex.I * ((s * p.2 : ℝ) : ℂ)) := by
  simp [spectralCharacter]
theorem isBoundedMeasurable_fstDiffQuot (t : ℝ≥0) : IsBoundedMeasurable (fstDiffQuot t) := by
  have h : IsBoundedMeasurable fun p => (1 : ℂ) + (-1) * spectralCharacter t 0 p :=
    isBoundedMeasurable_add (isBoundedMeasurable_const 1)
      (isBoundedMeasurable_mul (isBoundedMeasurable_const _)
        (isBoundedMeasurable_spectralCharacter t 0))
  have h₂ := isBoundedMeasurable_mul (isBoundedMeasurable_const (((t : ℝ)⁻¹ : ℝ) : ℂ)) h
  convert h₂ using 2 with p
  simp only [fstDiffQuot]
  ring
theorem isBoundedMeasurable_sndDiffQuot (s : ℝ) : IsBoundedMeasurable (sndDiffQuot s) := by
  have h : IsBoundedMeasurable fun p => spectralCharacter 0 s p + (-1) * (1 : ℂ) :=
    isBoundedMeasurable_add (isBoundedMeasurable_spectralCharacter 0 s)
      (isBoundedMeasurable_const _ |> fun h => isBoundedMeasurable_mul h
        (isBoundedMeasurable_const _))
  have h₂ := isBoundedMeasurable_mul (isBoundedMeasurable_const (Complex.I * (s : ℂ))⁻¹) h
  convert h₂ using 2 with p
  simp only [sndDiffQuot]
  ring
theorem norm_fstDiffQuot_le (t : ℝ≥0) (p : SpectralPlane) :
    ‖fstDiffQuot t p‖ ≤ ‖coordFst p‖ := by
  have hE : 0 ≤ (p.1 : ℝ) := p.1.2
  have ht : 0 ≤ (t : ℝ) := t.2
  have hnorm : ‖coordFst p‖ = (p.1 : ℝ) := by
    simp [coordFst]
  rw [hnorm]
  by_cases h0 : (t : ℝ) = 0
  · simp [fstDiffQuot, h0, hE]
  have htp : 0 < (t : ℝ) := lt_of_le_of_ne ht (Ne.symm h0)
  have hval : fstDiffQuot t p =
      (((t : ℝ)⁻¹ * (1 - Real.exp (-(t : ℝ) * (p.1 : ℝ))) : ℝ) : ℂ) := by
    simp only [fstDiffQuot, spectralCharacter_zero_right]
    push_cast
    ring
  rw [hval, Complex.norm_real]
  have h₁ : Real.exp (-(t : ℝ) * (p.1 : ℝ)) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    nlinarith
  have h₂ : 1 - (t : ℝ) * (p.1 : ℝ) ≤ Real.exp (-(t : ℝ) * (p.1 : ℝ)) := by
    have := Real.add_one_le_exp (-(t : ℝ) * (p.1 : ℝ))
    linarith
  rw [Real.norm_of_nonneg (mul_nonneg (inv_nonneg.mpr ht) (by linarith)),
    inv_mul_le_iff₀ htp]
  linarith
theorem norm_sndDiffQuot_le (s : ℝ) (p : SpectralPlane) :
    ‖sndDiffQuot s p‖ ≤ ‖coordSnd p‖ := by
  have hnorm : ‖coordSnd p‖ = |p.2| := by
    simp [coordSnd]
  rw [hnorm]
  by_cases h0 : s = 0
  · simp [sndDiffQuot, h0]
  have hs : 0 < |s| := abs_pos.mpr h0
  have h₁ : ‖Complex.exp (Complex.I * ((s * p.2 : ℝ) : ℂ)) - 1‖ ≤ |s * p.2| := by
    simpa using Real.norm_exp_I_mul_ofReal_sub_one_le (x := s * p.2)
  rw [sndDiffQuot, spectralCharacter_zero_left, norm_mul, norm_inv, norm_mul,
    Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs, inv_mul_le_iff₀ hs, ← abs_mul]
  exact h₁
theorem tendsto_fstDiffQuot (p : SpectralPlane) :
    Tendsto (fun t => fstDiffQuot t p) (𝓝[>] 0) (𝓝 (coordFst p)) := by
  have h₁ : HasDerivAt (fun t : ℝ => -t * (p.1 : ℝ)) (-(p.1 : ℝ)) 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).neg.mul_const (p.1 : ℝ)
  have h₂ : HasDerivAt (fun t : ℝ => Real.exp (-t * (p.1 : ℝ))) (-(p.1 : ℝ)) 0 := by
    simpa using h₁.exp
  have h₃ := hasDerivAt_iff_tendsto_slope.mp h₂
  have hcoe : Tendsto (fun t : ℝ≥0 => (t : ℝ)) (𝓝[>] 0) (𝓝[≠] (0 : ℝ)) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · exact (NNReal.continuous_coe.tendsto' 0 0 rfl).mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with t ht
      have : (0 : ℝ) < t := ht
      exact this.ne'
  have h₄ := (h₃.comp hcoe).neg
  have h₅ := (Complex.continuous_ofReal.tendsto _).comp h₄
  simp only [neg_neg] at h₅
  refine h₅.congr fun t => ?_
  simp only [Function.comp, slope, fstDiffQuot, spectralCharacter_zero_right]
  simp only [sub_zero, neg_zero, zero_mul, Real.exp_zero, vsub_eq_sub, smul_eq_mul]
  push_cast
  ring
theorem tendsto_sndDiffQuot (p : SpectralPlane) :
    Tendsto (fun s => sndDiffQuot s p) (𝓝[≠] 0) (𝓝 (coordSnd p)) := by
  have h₁ : HasDerivAt (fun s : ℝ => Complex.I * ((s * p.2 : ℝ) : ℂ))
      (Complex.I * (p.2 : ℂ)) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).mul_const p.2).ofReal_comp.const_mul Complex.I
  have h₂ : HasDerivAt (fun s : ℝ => Complex.exp (Complex.I * ((s * p.2 : ℝ) : ℂ)))
      (Complex.I * (p.2 : ℂ)) 0 := by
    simpa using h₁.cexp
  have h₃ := (hasDerivAt_iff_tendsto_slope.mp h₂).const_mul (Complex.I⁻¹)
  have h₄ : Complex.I⁻¹ * (Complex.I * (p.2 : ℂ)) = coordSnd p := by
    rw [← mul_assoc, inv_mul_cancel₀ Complex.I_ne_zero, one_mul]
    rfl
  rw [h₄] at h₃
  refine h₃.congr fun s => ?_
  simp only [slope, sndDiffQuot, spectralCharacter_zero_left, sub_zero, vsub_eq_sub]
  simp only [Complex.real_smul, zero_mul, Complex.ofReal_zero, mul_zero, Complex.exp_zero]
  rw [mul_inv]
  push_cast
  ring
end Exponentials
section Generators
variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (hr : HilbertSpace.BoundedSesqRep.Claim)
  {T : ℝ≥0 → H →L[ℂ] H} {U : ℝ → H →L[ℂ] H} {P : ProjValuedMeasure H}
include hr
theorem semigroup_eq_boundedSpectralIntegral (hp : IsCommutingSemigroupGroup T U)
    (hP : IsJointSpectralPVM T U P) (t : ℝ≥0) :
    T t = P.boundedSpectralIntegral (spectralCharacter t 0) := by
  have h := hP t 0
  rw [hp.group.map_zero, mul_one] at h
  exact eq_boundedSpectralIntegral_of P hr (isBoundedMeasurable_spectralCharacter t 0) h
theorem group_eq_boundedSpectralIntegral (hp : IsCommutingSemigroupGroup T U)
    (hP : IsJointSpectralPVM T U P) (s : ℝ) :
    U s = P.boundedSpectralIntegral (spectralCharacter 0 s) := by
  have h := hP 0 s
  rw [hp.semigroup.map_zero, one_mul] at h
  exact eq_boundedSpectralIntegral_of P hr (isBoundedMeasurable_spectralCharacter 0 s) h
theorem semigroupDiffQuot_eq (hp : IsCommutingSemigroupGroup T U)
    (hP : IsJointSpectralPVM T U P) (v : H) (t : ℝ≥0) :
    semigroupDiffQuot T v t = P.boundedSpectralIntegral (fstDiffQuot t) v := by
  have hb := isBoundedMeasurable_spectralCharacter t 0
  have hsub : IsBoundedMeasurable fun p => (1 : ℂ) - spectralCharacter t 0 p := by
    have h := isBoundedMeasurable_add (isBoundedMeasurable_const (1 : ℂ))
      (isBoundedMeasurable_mul (isBoundedMeasurable_const (-1 : ℂ)) hb)
    convert h using 2 with p
    ring
  have h₁ : P.boundedSpectralIntegral (fstDiffQuot t) =
      (((t : ℝ)⁻¹ : ℝ) : ℂ) • (1 - T t) := by
    change P.boundedSpectralIntegral (fun p => (((t : ℝ)⁻¹ : ℝ) : ℂ) *
      (1 - spectralCharacter t 0 p)) = _
    rw [boundedSpectralIntegral_const_mul P hr _ hsub,
      boundedSpectralIntegral_sub P hr (isBoundedMeasurable_const 1) hb,
      boundedSpectralIntegral_one P hr, semigroup_eq_boundedSpectralIntegral hr hp hP t]
  rw [h₁]
  simp [semigroupDiffQuot]
theorem groupDiffQuot_eq (hp : IsCommutingSemigroupGroup T U)
    (hP : IsJointSpectralPVM T U P) (v : H) (s : ℝ) :
    groupDiffQuot U v s = P.boundedSpectralIntegral (sndDiffQuot s) v := by
  have hb := isBoundedMeasurable_spectralCharacter 0 s
  have hsub : IsBoundedMeasurable fun p => spectralCharacter 0 s p - (1 : ℂ) := by
    have h := isBoundedMeasurable_add hb
      (isBoundedMeasurable_mul (isBoundedMeasurable_const (-1 : ℂ))
        (isBoundedMeasurable_const (1 : ℂ)))
    convert h using 2 with p
    ring
  have h₁ : P.boundedSpectralIntegral (sndDiffQuot s) =
      (Complex.I * (s : ℂ))⁻¹ • (U s - 1) := by
    change P.boundedSpectralIntegral (fun p => (Complex.I * (s : ℂ))⁻¹ *
      (spectralCharacter 0 s p - 1)) = _
    rw [boundedSpectralIntegral_const_mul P hr _ hsub,
      boundedSpectralIntegral_sub P hr hb (isBoundedMeasurable_const 1),
      boundedSpectralIntegral_one P hr, group_eq_boundedSpectralIntegral hr hp hP s]
  rw [h₁]
  simp [groupDiffQuot]
theorem generatorProperties (hp : IsCommutingSemigroupGroup T U)
    (hP : IsJointSpectralPVM T U P) : GeneratorProperties T U P := by
  have hre : ∀ p, (coordFst p).im = 0 := fun p => by simp [coordFst]
  have hrq : ∀ p, (coordSnd p).im = 0 := fun p => by simp [coordSnd]
  have hnn : ∀ p, 0 ≤ coordFst p := fun p => Complex.zero_le_real.mpr p.1.2
  have hq : ∀ v, semigroupDiffQuot T v = fun t => P.boundedSpectralIntegral (fstDiffQuot t) v :=
    fun v => funext (semigroupDiffQuot_eq hr hp hP v)
  have hg : ∀ v, groupDiffQuot U v = fun s => P.boundedSpectralIntegral (sndDiffQuot s) v :=
    fun v => funext (groupDiffQuot_eq hr hp hP v)
  refine
    { isSelfAdjoint_energy := isSelfAdjoint_spectralIntegral_of P hr measurable_coordFst hre
      isSelfAdjoint_momentum := isSelfAdjoint_spectralIntegral_of P hr measurable_coordSnd hrq
      isPositive_energy := isPositive_spectralIntegral_of P hr measurable_coordFst hnn
      mem_domain_energy_iff := fun v =>
        ⟨fun hv => ⟨P.spectralIntegral coordFst ⟨v, hv⟩, ?_⟩, fun ⟨w, hw⟩ => ?_⟩
      tendsto_energy := fun v => ?_
      mem_domain_momentum_iff := fun v =>
        ⟨fun hv => ⟨P.spectralIntegral coordSnd ⟨v, hv⟩, ?_⟩, fun ⟨w, hw⟩ => ?_⟩
      tendsto_momentum := fun v => ?_
      commute_strips := fun B B' => ?_ }
  · rw [hq]
    exact tendsto_boundedSpectralIntegral_of_dominated P hr measurable_coordFst
      isBoundedMeasurable_fstDiffQuot norm_fstDiffQuot_le tendsto_fstDiffQuot ⟨v, hv⟩
  · rw [hq] at hw
    exact mem_spectralIntegral_domain_of_tendsto P hr measurable_coordFst
      isBoundedMeasurable_fstDiffQuot tendsto_fstDiffQuot hw
  · rw [hq]
    exact tendsto_boundedSpectralIntegral_of_dominated P hr measurable_coordFst
      isBoundedMeasurable_fstDiffQuot norm_fstDiffQuot_le tendsto_fstDiffQuot v
  · rw [hg]
    exact tendsto_boundedSpectralIntegral_of_dominated P hr measurable_coordSnd
      isBoundedMeasurable_sndDiffQuot norm_sndDiffQuot_le tendsto_sndDiffQuot ⟨v, hv⟩
  · rw [hg] at hw
    exact mem_spectralIntegral_domain_of_tendsto P hr measurable_coordSnd
      isBoundedMeasurable_sndDiffQuot tendsto_sndDiffQuot hw
  · rw [hg]
    exact tendsto_boundedSpectralIntegral_of_dominated P hr measurable_coordSnd
      isBoundedMeasurable_sndDiffQuot norm_sndDiffQuot_le tendsto_sndDiffQuot v
  · change P (fstStrip B) * P (cylinderSet B') = P (cylinderSet B') * P (fstStrip B)
    rw [P.map_inter, P.map_inter]
    exact congrArg P.toFun (Subtype.ext (inter_comm _ _))
end Generators
theorem spectralIntegralProperties {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (hr : HilbertSpace.BoundedSesqRep.Claim)
    (P : ProjValuedMeasure H) : SpectralIntegralProperties P where
  nonneg v B := by
    rw [show P.matrixCoeff v v B.1 = _ from matrixCoeff_self P v B.2]
    exact Complex.zero_le_real.mpr (by positivity)
  variation_eq v B := by
    rw [variation_matrixCoeff_self_real P v B.2, matrixCoeff_self P v B.2, Complex.ofReal_re]
  mass v := by
    rw [matrixCoeff_self P v MeasurableSet.univ, apply_univ_eq]
  conj_symm u v := VectorMeasure.ext fun s hs => by
    rw [conjMeasure_apply, matrixCoeff_apply_set P _ _ hs, matrixCoeff_apply_set P _ _ hs,
      inner_conj_symm, inner_apply_left_eq]
  variation_le := variation_matrixCoeff_le P
  isBoundedSpectralIntegral _ hF := isBoundedSpectralIntegral_self P hr hF
  eq_boundedSpectralIntegral _ _ hF h := eq_boundedSpectralIntegral_of P hr hF h
  boundedSpectralIntegral_add _ _ hF hF' := boundedSpectralIntegral_add_fun P hr hF hF'
  boundedSpectralIntegral_smul a _ hF := boundedSpectralIntegral_const_mul P hr a hF
  norm_boundedSpectralIntegral_le F hF := by
    obtain ⟨_, C, hC⟩ := id hF
    have hbdd : BddAbove (range fun p => ‖F p‖) := ⟨C, by
      rintro _ ⟨p, rfl⟩
      exact hC p⟩
    exact norm_boundedSpectralIntegral_le_of_bound P hr hF
      (Real.iSup_nonneg fun _ => norm_nonneg _) (fun p => le_ciSup hbdd p)
  inner_boundedSpectralIntegral _ hF := inner_boundedSpectralIntegral_left P hr hF
  boundedSpectralIntegral_mul _ _ hF hF' := boundedSpectralIntegral_mul_fun P hr hF hF'
  norm_sq_boundedSpectralIntegral _ hF := norm_sq_boundedSpectralIntegral_eq P hr hF
  boundedSpectralIntegral_indicator := boundedSpectralIntegral_indicator_one P hr
  exists_submodule F _ := ⟨spectralDomainSubmodule P F, rfl⟩
  isSeqDense_spectralDomain _ hF := isSeqDense_spectralDomain_of P hr hF
  isSpectralIntegral _ hF := isSpectralIntegral_spectralIntegral P hr hF
  eq_spectralIntegral _ _ hF h := eq_spectralIntegral_of P hr hF h
  tendsto_boundedSpectralIntegral_indicator _ _ hF hB v :=
    tendsto_boundedSpectralIntegral_indicator_of P hr hF hB.monotone hB.iUnion_eq
      (isBoundedMeasurable_of_isBoundedExhaustion hF hB) v
  enorm_sq_spectralIntegral _ hF v := enorm_sq_spectralIntegral_eq P hr hF v
  spectralIntegral_of_isBoundedMeasurable _ hF := spectralIntegral_of_isBoundedMeasurable_eq P hr hF
  spectralIntegral_add _ _ hF hF' v hv hv' := spectralIntegral_add_of P hr hF hF' v hv hv'
  isSelfAdjoint_spectralIntegral _ hF hre := isSelfAdjoint_spectralIntegral_of P hr hF hre
  isPositive_spectralIntegral _ hF hnn := isPositive_spectralIntegral_of P hr hF hnn
theorem spectralIntegralTheorem_of_boundedSesqRep (hr : HilbertSpace.BoundedSesqRep.Claim) :
    SpectralIntegralTheorem := by
  intro H _ _ _
  exact ⟨spectralIntegralProperties hr, fun _ _ _ hp hP => generatorProperties hr hp hP⟩
end YangMills.Construction.SpectralCalculus.SpectralIntegralConstruction
