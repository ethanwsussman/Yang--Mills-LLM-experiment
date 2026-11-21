import YangMills.Construction.SpectralTheory.GeneratorsOfUnitaryGroupsAndSemigroups
import YangMills.Construction.SpectralTheory.SpectralIntegralLaws
import YangMills.Construction.SpectralTheory.SpectralMeasureConcentratedOnSupport
import Mathlib
set_option autoImplicit false
open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal InnerProductSpace ComplexConjugate ComplexOrder
noncomputable section
namespace YangMills.Construction.GeneratorsAndFlows
open YangMills.Construction.SpectralTheory
open YangMills.Construction.SpectralTheory.ProjectionMeasure
open YangMills.Construction.HilbertSpaceBasics (ofBounded)
section EvaluationMaps
variable {ℋ : Type} [NormedAddCommGroup ℋ] [InnerProductSpace ℂ ℋ] [CompleteSpace ℋ]
theorem apply_of_eq_toUnboundedOperator {A : UnboundedOperator ℋ} {B : ℋ →L[ℂ] ℋ}
    (h : A = toUnboundedOperator B) (ψ : A.domain) : A ψ = B ψ := by
  subst h
  rfl
theorem mem_domain_of_eq_toUnboundedOperator {A : UnboundedOperator ℋ} {B : ℋ →L[ℂ] ℋ}
    (h : A = toUnboundedOperator B) (ψ : ℋ) : ψ ∈ A.domain := by
  subst h
  exact Submodule.mem_top
theorem toUnboundedOperator_injective {B B' : ℋ →L[ℂ] ℋ}
    (h : toUnboundedOperator B = toUnboundedOperator B') : B = B' := by
  ext ψ
  exact apply_of_eq_toUnboundedOperator h ⟨ψ, Submodule.mem_top⟩
theorem toBounded_eq_of_eq {T : UnboundedOperator ℋ} {B : ℋ →L[ℂ] ℋ}
    (h : T = toUnboundedOperator B) : toBounded T = B := by
  have hs : T = ofBounded (toBounded T) :=
    Classical.epsilon_spec (p := fun B => T = ofBounded B) ⟨B, h⟩
  exact toUnboundedOperator_injective (hs.symm.trans h)
end EvaluationMaps
section Basics
set_option linter.unusedSectionVars false
variable {n : ℕ} [NeZero n] {ℋ : Type} [NormedAddCommGroup ℋ] [InnerProductSpace ℂ ℋ]
  [CompleteSpace ℋ]
structure SpectralToolkit (E : ProjectionMeasure n ℋ) : Prop where
  laws : E.CalculusLaws
  supportProps : E.SupportLaws
  simpleLaws : E.SimpleIntegralRules
  limitVectors : ∀ f : (Fin n → ℝ) → ℂ, Measurable f → E.ApproximantLimitsExist f
variable {E : ProjectionMeasure n ℋ}
theorem SpectralToolkit.isFinite (T : SpectralToolkit E) (ψ : ℋ) :
    IsFiniteMeasure (E.spectralValueMeasure ψ) :=
  T.supportProps.isFiniteMeasure ψ
theorem SpectralToolkit.spectralIntegral_eq (T : SpectralToolkit E) {f : (Fin n → ℝ) → ℂ}
    (hf : Measurable f) (hb : IsBoundedComplexFn f) :
    E.functionalCalculus f = toUnboundedOperator (E.boundedCalculus f) :=
  T.laws.isBoundedCalculusOf f hf hb
theorem SpectralToolkit.mem_dom_iff (T : SpectralToolkit E) {f : (Fin n → ℝ) → ℂ}
    (hf : Measurable f) (ψ : ℋ) :
    ψ ∈ (E.functionalCalculus f).domain ↔ ∫⁻ x, ‖f x‖ₑ ^ 2 ∂(E.spectralValueMeasure ψ) < ∞ := by
  have h := (T.laws.isOperator f hf).1
  rw [← SetLike.mem_coe, h]
  rfl
theorem SpectralToolkit.mem_dom_of_bounded (T : SpectralToolkit E) {f : (Fin n → ℝ) → ℂ}
    (hf : Measurable f) (hb : IsBoundedComplexFn f) (ψ : ℋ) :
    ψ ∈ (E.functionalCalculus f).domain :=
  mem_domain_of_eq_toUnboundedOperator (T.spectralIntegral_eq hf hb) ψ
theorem SpectralToolkit.integrable_norm_sq (T : SpectralToolkit E) {f : (Fin n → ℝ) → ℂ}
    (hf : Measurable f) {ψ : ℋ} (hψ : ψ ∈ (E.functionalCalculus f).domain) :
    Integrable (fun x => ‖f x‖ ^ 2) (E.spectralValueMeasure ψ) := by
  refine ⟨(hf.norm.pow_const 2).aestronglyMeasurable, ?_⟩
  have h := (T.mem_dom_iff hf ψ).1 hψ
  simpa [HasFiniteIntegral, enorm_pow] using h
theorem SpectralToolkit.integrable_of_isBounded (T : SpectralToolkit E) {f : (Fin n → ℝ) → ℂ}
    (hf : Measurable f) (hb : IsBoundedComplexFn f) (ψ : ℋ) :
    Integrable f (E.spectralValueMeasure ψ) := by
  have := T.isFinite ψ
  obtain ⟨C, hC⟩ := hb
  exact Integrable.of_bound hf.aestronglyMeasurable C (ae_of_all _ hC)
theorem isBoundedComplexFn_linComb {p q : (Fin n → ℝ) → ℂ} (hpb : IsBoundedComplexFn p)
    (hqb : IsBoundedComplexFn q) (a b : ℂ) :
    IsBoundedComplexFn fun x => a * p x + b * q x := by
  obtain ⟨C, hC⟩ := hpb
  obtain ⟨D, hD⟩ := hqb
  refine ⟨‖a‖ * C + ‖b‖ * D, fun x => ?_⟩
  calc ‖a * p x + b * q x‖ ≤ ‖a * p x‖ + ‖b * q x‖ := norm_add_le _ _
    _ = ‖a‖ * ‖p x‖ + ‖b‖ * ‖q x‖ := by rw [norm_mul, norm_mul]
    _ ≤ ‖a‖ * C + ‖b‖ * D := by gcongr <;> simp [hC, hD]
theorem isBoundedComplexFn_const_one : IsBoundedComplexFn (fun _ : Fin n → ℝ => (1 : ℂ)) :=
  ⟨1, fun _ => by simp⟩
theorem SpectralToolkit.boundedIntegralOp_linComb (T : SpectralToolkit E) {p q : (Fin n → ℝ) → ℂ}
    (hp : Measurable p) (hq : Measurable q) (hpb : IsBoundedComplexFn p)
    (hqb : IsBoundedComplexFn q) (a b : ℂ) :
    E.boundedCalculus (fun x => a * p x + b * q x) =
      a • E.boundedCalculus p + b • E.boundedCalculus q := by
  symm
  have hm : Measurable fun x => a * p x + b * q x := (hp.const_mul a).add (hq.const_mul b)
  refine (T.laws.eq_boundedCalculus_iff _ hm (isBoundedComplexFn_linComb hpb hqb a b) _).1
    fun φ ψ => ?_
  have key : ∀ χ : ℋ, ∫ x, (a * p x + b * q x) ∂(E.spectralValueMeasure χ) =
      a * ∫ x, p x ∂(E.spectralValueMeasure χ) + b * ∫ x, q x ∂(E.spectralValueMeasure χ) :=
    fun χ => by
      rw [integral_add ((T.integrable_of_isBounded hp hpb χ).const_mul a)
        ((T.integrable_of_isBounded hq hqb χ).const_mul b), integral_const_mul,
        integral_const_mul]
  simp only [_root_.add_apply, _root_.smul_apply, inner_add_right,
    inner_smul_right, T.laws.inner_boundedCalculus p hp hpb,
    T.laws.inner_boundedCalculus q hq hqb]
  simp only [polarizedIntegral, key, Finset.sum_range_succ, Finset.sum_range_zero]
  ring
theorem SpectralToolkit.boundedIntegralOp_indicator (T : SpectralToolkit E) (A : BorelSets n) :
    E.boundedCalculus (A.1.indicator fun _ => (1 : ℂ)) = E A := by
  have hs := IsSimpleBorel.indicator_one A
  have h₁ := T.laws.calculus_simple _ hs
  have h₂ := T.simpleLaws.indicator A
  rw [h₂] at h₁
  have hb : IsBoundedComplexFn (A.1.indicator fun _ => (1 : ℂ)) := by
    refine ⟨1, fun x => ?_⟩
    by_cases hx : x ∈ A.1 <;> simp [hx]
  exact toUnboundedOperator_injective ((T.spectralIntegral_eq hs.1 hb).symm.trans h₁)
theorem SpectralToolkit.boundedIntegralOp_const_one (T : SpectralToolkit E) :
    E.boundedCalculus (fun _ => (1 : ℂ)) = 1 := by
  have h := T.boundedIntegralOp_indicator ⟨univ, MeasurableSet.univ⟩
  rw [E.map_univ] at h
  simpa using h
theorem SpectralToolkit.boundedIntegralOp_congr (T : SpectralToolkit E) {f g : (Fin n → ℝ) → ℂ}
    (hf : Measurable f) (hg : Measurable g) (hfb : IsBoundedComplexFn f)
    (hgb : IsBoundedComplexFn g)
    (h : E ⟨{x | f x ≠ g x}, (measurableSet_eq_fun hf hg).compl⟩ = 0) :
    E.boundedCalculus f = E.boundedCalculus g :=
  toUnboundedOperator_injective
    (((T.spectralIntegral_eq hf hfb).symm.trans (T.laws.calculus_congr f g hf hg h)).trans
      (T.spectralIntegral_eq hg hgb))
theorem SpectralToolkit.proj_add_proj_compl (T : SpectralToolkit E) (A : BorelSets n) :
    E A + E ⟨A.1ᶜ, A.2.compl⟩ = 1 := by
  have hb : ∀ B : BorelSets n, IsBoundedComplexFn (B.1.indicator fun _ => (1 : ℂ)) := fun B => by
    refine ⟨1, fun x => ?_⟩
    by_cases hx : x ∈ B.1 <;> simp [hx]
  have hm : ∀ B : BorelSets n, Measurable (B.1.indicator fun _ => (1 : ℂ)) := fun B =>
    measurable_const.indicator B.2
  have h := T.boundedIntegralOp_linComb (hm A) (hm ⟨A.1ᶜ, A.2.compl⟩) (hb A) (hb _) 1 1
  rw [T.boundedIntegralOp_indicator, T.boundedIntegralOp_indicator] at h
  have hf : (fun x => (1 : ℂ) * (A.1.indicator (fun _ => (1 : ℂ)) x) +
      1 * ((A.1ᶜ).indicator (fun _ => (1 : ℂ)) x)) = fun _ => 1 := by
    funext x
    by_cases hx : x ∈ A.1 <;> simp [hx]
  rw [hf, T.boundedIntegralOp_const_one] at h
  simpa using h.symm
theorem diagonalMeasure_eq_zero_iff (A : BorelSets n) (ψ : ℋ) :
    E.spectralValueMeasure ψ A.1 = 0 ↔ E A ψ = 0 := by
  rw [spectralValueMeasure_apply, ENNReal.ofReal_eq_zero]
  constructor
  · intro h
    have h₂ : ‖E A ψ‖ ^ 2 = 0 := le_antisymm h (by positivity)
    simpa using h₂
  · intro h
    simp [h]
theorem ae_not_mem_of_proj_eq_zero {A : BorelSets n} (h : E A = 0) (ψ : ℋ) :
    ∀ᵐ x ∂(E.spectralValueMeasure ψ), x ∉ A.1 := by
  refine measure_eq_zero_iff_ae_notMem.1 ?_
  rw [diagonalMeasure_eq_zero_iff, h]
  rfl
theorem SpectralToolkit.norm_sub_sq (T : SpectralToolkit E) {p f : (Fin n → ℝ) → ℂ}
    (hp : Measurable p) (hpb : IsBoundedComplexFn p) (hf : Measurable f) {ψ : ℋ}
    (hψ : ψ ∈ (E.functionalCalculus f).domain) :
    ‖E.boundedCalculus p ψ - E.functionalCalculus f ⟨ψ, hψ⟩‖ ^ 2 =
      ∫ x, ‖p x - f x‖ ^ 2 ∂(E.spectralValueMeasure ψ) := by
  obtain ⟨h, e⟩ := T.laws.add_const_mul p f hp hf (-1) ψ (T.mem_dom_of_bounded hp hpb ψ) hψ
  have hm : Measurable fun x => p x + (-1) * f x := hp.add (hf.const_mul _)
  have h₂ := T.laws.norm_sq _ hm ⟨ψ, h⟩
  rw [e, apply_of_eq_toUnboundedOperator (T.spectralIntegral_eq hp hpb)] at h₂
  simp only [neg_smul, one_smul, neg_mul, one_mul, ← sub_eq_add_neg] at h₂
  exact h₂
theorem SpectralToolkit.norm_boundedIntegralOp_sq (T : SpectralToolkit E) {p : (Fin n → ℝ) → ℂ}
    (hp : Measurable p) (hpb : IsBoundedComplexFn p) (ψ : ℋ) :
    ‖E.boundedCalculus p ψ‖ ^ 2 = ∫ x, ‖p x‖ ^ 2 ∂(E.spectralValueMeasure ψ) := by
  have h := T.laws.norm_sq p hp ⟨ψ, T.mem_dom_of_bounded hp hpb ψ⟩
  rwa [apply_of_eq_toUnboundedOperator (T.spectralIntegral_eq hp hpb)] at h
theorem SpectralToolkit.tendsto_of_dominated_sq (T : SpectralToolkit E) {ι : Type*}
    {l : Filter ι} [l.IsCountablyGenerated] {p : ι → (Fin n → ℝ) → ℂ} {f : (Fin n → ℝ) → ℂ}
    (hp : ∀ s, Measurable (p s)) (hpb : ∀ s, IsBoundedComplexFn (p s)) (hf : Measurable f)
    {ψ : ℋ} (hψ : ψ ∈ (E.functionalCalculus f).domain) {G : (Fin n → ℝ) → ℝ}
    (hG : Integrable G (E.spectralValueMeasure ψ))
    (hbound : ∀ᶠ s in l, ∀ᵐ x ∂(E.spectralValueMeasure ψ), ‖p s x - f x‖ ^ 2 ≤ G x)
    (hlim : ∀ᵐ x ∂(E.spectralValueMeasure ψ), Tendsto (fun s => p s x) l (𝓝 (f x))) :
    Tendsto (fun s => E.boundedCalculus (p s) ψ) l (𝓝 (E.functionalCalculus f ⟨ψ, hψ⟩)) := by
  have h₁ : Tendsto (fun s => ∫ x, ‖p s x - f x‖ ^ 2 ∂(E.spectralValueMeasure ψ)) l
      (𝓝 (∫ _, (0 : ℝ) ∂(E.spectralValueMeasure ψ))) := by
    refine tendsto_integral_filter_of_dominated_convergence G
      (Eventually.of_forall fun s => (((hp s).sub hf).norm.pow_const 2).aestronglyMeasurable)
      ?_ hG ?_
    · filter_upwards [hbound] with s hs
      filter_upwards [hs] with x hx
      rwa [Real.norm_of_nonneg (by positivity)]
    · filter_upwards [hlim] with x hx
      have h₂ := ((hx.sub_const (f x)).norm).pow 2
      simpa using h₂
  rw [integral_zero] at h₁
  simp only [← T.norm_sub_sq (hp _) (hpb _) hf hψ] at h₁
  have h₃ := (Real.continuous_sqrt.tendsto 0).comp h₁
  simp only [Real.sqrt_zero] at h₃
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine h₃.congr fun s => ?_
  simp [Real.sqrt_sq (norm_nonneg _)]
theorem SpectralToolkit.boundedIntegralOp_diffQuot_apply (T : SpectralToolkit E)
    {p : (Fin n → ℝ) → ℂ} (hp : Measurable p) (hpb : IsBoundedComplexFn p) (a : ℂ) (ψ : ℋ) :
    E.boundedCalculus (fun x => a * (p x - 1)) ψ = a • (E.boundedCalculus p ψ - ψ) := by
  have h := T.boundedIntegralOp_linComb hp measurable_const hpb isBoundedComplexFn_const_one a (-a)
  have hf : (fun x => a * p x + -a * 1) = fun x => a * (p x - 1) := by
    funext x
    ring
  rw [hf, T.boundedIntegralOp_const_one] at h
  rw [h]
  simp [sub_eq_add_neg]
theorem measurable_diffQuot {p : (Fin n → ℝ) → ℂ} (hp : Measurable p) (a : ℂ) :
    Measurable fun x => a * (p x - 1) :=
  (hp.sub_const 1).const_mul a
theorem isBoundedComplexFn_diffQuot {p : (Fin n → ℝ) → ℂ} (hpb : IsBoundedComplexFn p) (a : ℂ) :
    IsBoundedComplexFn fun x => a * (p x - 1) := by
  have h := isBoundedComplexFn_linComb hpb (isBoundedComplexFn_const_one (n := n)) a (-a)
  obtain ⟨C, hC⟩ := h
  refine ⟨C, fun x => ?_⟩
  have h₂ : ‖a * p x + -a * 1‖ ≤ C := hC x
  rw [show a * p x + -a * 1 = a * (p x - 1) by ring] at h₂
  exact h₂
theorem SpectralToolkit.tendsto_diffQuot_apply (T : SpectralToolkit E) {ι : Type*}
    {l : Filter ι} [l.IsCountablyGenerated] {a : ι → ℂ} {p : ι → (Fin n → ℝ) → ℂ}
    {f : (Fin n → ℝ) → ℂ} (hp : ∀ s, Measurable (p s)) (hpb : ∀ s, IsBoundedComplexFn (p s))
    (hf : Measurable f) {ψ : ℋ} (hψ : ψ ∈ (E.functionalCalculus f).domain)
    (hbound : ∀ᶠ s in l, ∀ᵐ x ∂(E.spectralValueMeasure ψ), ‖a s * (p s x - 1)‖ ≤ ‖f x‖)
    (hlim : ∀ᵐ x ∂(E.spectralValueMeasure ψ),
      Tendsto (fun s => a s * (p s x - 1)) l (𝓝 (f x))) :
    Tendsto (fun s => a s • (E.boundedCalculus (p s) ψ - ψ)) l
      (𝓝 (E.functionalCalculus f ⟨ψ, hψ⟩)) := by
  have h := T.tendsto_of_dominated_sq (p := fun s x => a s * (p s x - 1))
    (fun s => measurable_diffQuot (hp s) _) (fun s => isBoundedComplexFn_diffQuot (hpb s) _) hf hψ
    (G := fun x => 4 * ‖f x‖ ^ 2) ((T.integrable_norm_sq hf hψ).const_mul 4) ?_ hlim
  · exact h.congr fun s => T.boundedIntegralOp_diffQuot_apply (hp s) (hpb s) _ _
  · filter_upwards [hbound] with s hs
    filter_upwards [hs] with x hx
    have h₁ : ‖a s * (p s x - 1) - f x‖ ≤ 2 * ‖f x‖ := by
      calc _ ≤ ‖a s * (p s x - 1)‖ + ‖f x‖ := norm_sub_le _ _
        _ ≤ 2 * ‖f x‖ := by linarith
    calc _ ≤ (2 * ‖f x‖) ^ 2 := by gcongr
      _ = 4 * ‖f x‖ ^ 2 := by ring
theorem SpectralToolkit.norm_le_of_dominated (T : SpectralToolkit E) {g f : (Fin n → ℝ) → ℂ}
    (hg : Measurable g) (hgb : IsBoundedComplexFn g) (hf : Measurable f) {ψ : ℋ}
    (hψ : ψ ∈ (E.functionalCalculus f).domain)
    (hbound : ∀ᵐ x ∂(E.spectralValueMeasure ψ), ‖g x‖ ≤ ‖f x‖) :
    ‖E.boundedCalculus g ψ‖ ≤ ‖E.functionalCalculus f ⟨ψ, hψ⟩‖ := by
  have := T.isFinite ψ
  have hi : Integrable (fun x => ‖g x‖ ^ 2) (E.spectralValueMeasure ψ) :=
    T.integrable_norm_sq hg (T.mem_dom_of_bounded hg hgb ψ)
  have h₁ : ∫ x, ‖g x‖ ^ 2 ∂(E.spectralValueMeasure ψ) ≤
      ∫ x, ‖f x‖ ^ 2 ∂(E.spectralValueMeasure ψ) := by
    refine integral_mono_ae hi (T.integrable_norm_sq hf hψ) ?_
    filter_upwards [hbound] with x hx
    gcongr
  rw [← T.norm_boundedIntegralOp_sq hg hgb, ← T.laws.norm_sq f hf ⟨ψ, hψ⟩] at h₁
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).1 h₁
theorem SpectralToolkit.mem_dom_of_bounded_approx (T : SpectralToolkit E)
    {g : ℕ → (Fin n → ℝ) → ℂ} {f : (Fin n → ℝ) → ℂ} (hg : ∀ r, Measurable (g r))
    (hgb : ∀ r, IsBoundedComplexFn (g r)) (hf : Measurable f) {ψ : ℋ} {c : ℝ}
    (hc : ∀ r, ‖E.boundedCalculus (g r) ψ‖ ≤ c)
    (hlim : ∀ᵐ x ∂(E.spectralValueMeasure ψ), Tendsto (fun r => g r x) atTop (𝓝 (f x))) :
    ψ ∈ (E.functionalCalculus f).domain := by
  rw [T.mem_dom_iff hf]
  have h₁ : ∀ r, ∫⁻ x, ‖g r x‖ₑ ^ 2 ∂(E.spectralValueMeasure ψ) ≤ ENNReal.ofReal (c ^ 2) :=
    fun r => by
      have hi : Integrable (fun x => ‖g r x‖ ^ 2) (E.spectralValueMeasure ψ) :=
        T.integrable_norm_sq (hg r) (T.mem_dom_of_bounded (hg r) (hgb r) ψ)
      have h₂ : ∫⁻ x, ‖g r x‖ₑ ^ 2 ∂(E.spectralValueMeasure ψ) =
          ENNReal.ofReal (∫ x, ‖g r x‖ ^ 2 ∂(E.spectralValueMeasure ψ)) := by
        rw [ofReal_integral_eq_lintegral_ofReal hi (ae_of_all _ fun x => by positivity)]
        refine lintegral_congr fun x => ?_
        rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]
      rw [h₂, ← T.norm_boundedIntegralOp_sq (hg r) (hgb r)]
      refine ENNReal.ofReal_le_ofReal ?_
      gcongr
      exact hc r
  have h₃ : ∫⁻ x, ‖f x‖ₑ ^ 2 ∂(E.spectralValueMeasure ψ) =
      ∫⁻ x, liminf (fun r => ‖g r x‖ₑ ^ 2) atTop ∂(E.spectralValueMeasure ψ) := by
    refine lintegral_congr_ae ?_
    filter_upwards [hlim] with x hx
    have h₄ : Tendsto (fun r => ‖g r x‖ₑ ^ 2) atTop (𝓝 (‖f x‖ₑ ^ 2)) :=
      (ENNReal.continuous_pow 2).continuousAt.tendsto.comp hx.enorm
    exact h₄.liminf_eq.symm
  rw [h₃]
  refine lt_of_le_of_lt (lintegral_liminf_le fun r => (hg r).enorm.pow_const 2) ?_
  refine lt_of_le_of_lt (liminf_le_of_frequently_le' (Frequently.of_forall h₁))
    ENNReal.ofReal_lt_top
end Basics
section Group
set_option linter.unusedSectionVars false
variable {ℋ : Type} [NormedAddCommGroup ℋ] [InnerProductSpace ℂ ℋ] [CompleteSpace ℋ]
  {F : ProjectionMeasure 1 ℋ}
def phaseFn (u : ℝ) (x : Fin 1 → ℝ) : ℂ :=
  Complex.exp (Complex.I * u * x 0)
theorem measurable_phaseFn (u : ℝ) : Measurable (phaseFn u) :=
  Complex.measurable_exp.comp
    ((Complex.measurable_ofReal.comp (measurable_pi_apply 0)).const_mul (Complex.I * u))
theorem phaseFn_eq (u : ℝ) (x : Fin 1 → ℝ) :
    phaseFn u x = Complex.exp (Complex.I * ((u * x 0 : ℝ) : ℂ)) := by
  simp only [phaseFn]
  push_cast
  ring_nf
theorem norm_phaseFn (u : ℝ) (x : Fin 1 → ℝ) : ‖phaseFn u x‖ = 1 := by
  rw [phaseFn_eq, mul_comm, Complex.norm_exp_ofReal_mul_I]
theorem isBoundedComplexFn_phaseFn (u : ℝ) : IsBoundedComplexFn (phaseFn u) :=
  ⟨1, fun x => (norm_phaseFn u x).le⟩
theorem unitaryGroupOp_eq_boundedIntegralOp (T : SpectralToolkit F) (u : ℝ) :
    F.unitaryFlow u = F.boundedCalculus (phaseFn u) :=
  toBounded_eq_of_eq (T.spectralIntegral_eq (measurable_phaseFn u) (isBoundedComplexFn_phaseFn u))
theorem unitaryGroup_eq_ofBounded (T : SpectralToolkit F) (u : ℝ) :
    F.expIMulOp u = ofBounded (F.unitaryFlow u) := by
  rw [unitaryGroupOp_eq_boundedIntegralOp T]
  exact T.spectralIntegral_eq (measurable_phaseFn u) (isBoundedComplexFn_phaseFn u)
theorem unitaryGroupOp_zero (T : SpectralToolkit F) : F.unitaryFlow 0 = 1 := by
  have h : phaseFn 0 = fun _ => (1 : ℂ) := by
    funext x
    simp [phaseFn]
  rw [unitaryGroupOp_eq_boundedIntegralOp T, h, T.boundedIntegralOp_const_one]
theorem unitaryGroupOp_mul (T : SpectralToolkit F) (u u' : ℝ) :
    F.unitaryFlow u * F.unitaryFlow u' = F.unitaryFlow (u + u') := by
  have h : (fun x => phaseFn u x * phaseFn u' x) = phaseFn (u + u') := by
    funext x
    simp only [phaseFn, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [unitaryGroupOp_eq_boundedIntegralOp T, unitaryGroupOp_eq_boundedIntegralOp T,
    unitaryGroupOp_eq_boundedIntegralOp T,
    T.laws.boundedCalculus_mul _ _ (measurable_phaseFn u) (measurable_phaseFn u')
      (isBoundedComplexFn_phaseFn u) (isBoundedComplexFn_phaseFn u'), h]
theorem unitaryGroupOp_star (T : SpectralToolkit F) (u : ℝ) :
    star (F.unitaryFlow u) = F.unitaryFlow (-u) := by
  have h : (fun x => conj (phaseFn u x)) = phaseFn (-u) := by
    funext x
    simp only [phaseFn, ← Complex.exp_conj, map_mul, Complex.conj_I, Complex.conj_ofReal]
    congr 1
    push_cast
    ring
  rw [unitaryGroupOp_eq_boundedIntegralOp T, unitaryGroupOp_eq_boundedIntegralOp T,
    T.laws.star_boundedCalculus _ (measurable_phaseFn u) (isBoundedComplexFn_phaseFn u), h]
theorem exists_linearIsometryEquiv_of_star {W : ℋ →L[ℂ] ℋ} (h₁ : star W * W = 1)
    (h₂ : W * star W = 1) : ∃ V : ℋ ≃ₗᵢ[ℂ] ℋ, ∀ ψ, W ψ = V ψ := by
  have hW : W ∈ unitary (ℋ →L[ℂ] ℋ) := Unitary.mem_iff.2 ⟨h₁, h₂⟩
  refine ⟨Unitary.linearIsometryEquiv ⟨W, hW⟩, fun ψ => ?_⟩
  exact (DFunLike.congr_fun (Unitary.coe_linearIsometryEquiv_apply (⟨W, hW⟩ : unitary _)) ψ).symm
theorem unitaryGroupOp_isUnitary (T : SpectralToolkit F) (u : ℝ) :
    ∃ V : ℋ ≃ₗᵢ[ℂ] ℋ, ∀ ψ, F.unitaryFlow u ψ = V ψ := by
  refine exists_linearIsometryEquiv_of_star ?_ ?_
  · rw [unitaryGroupOp_star T, unitaryGroupOp_mul T, neg_add_cancel, unitaryGroupOp_zero T]
  · rw [unitaryGroupOp_star T, unitaryGroupOp_mul T, add_neg_cancel, unitaryGroupOp_zero T]
theorem norm_unitaryGroupOp_apply (T : SpectralToolkit F) (u : ℝ) (ψ : ℋ) :
    ‖F.unitaryFlow u ψ‖ = ‖ψ‖ := by
  obtain ⟨V, hV⟩ := unitaryGroupOp_isUnitary T u
  rw [hV, V.norm_map]
theorem unitaryGroupOp_stronglyContinuous (T : SpectralToolkit F) :
    StronglyContinuous F.unitaryFlow := by
  intro ψ
  refine continuous_iff_continuousAt.2 fun u₀ => ?_
  have := T.isFinite ψ
  have hψ := T.mem_dom_of_bounded (measurable_phaseFn u₀) (isBoundedComplexFn_phaseFn u₀) ψ
  have h := T.tendsto_of_dominated_sq (l := 𝓝 u₀) (p := phaseFn) (f := phaseFn u₀)
    measurable_phaseFn isBoundedComplexFn_phaseFn (measurable_phaseFn u₀) hψ
    (G := fun _ => 4) (integrable_const _) (Eventually.of_forall fun u => ae_of_all _ fun x => ?_)
    (ae_of_all _ fun x => ?_)
  · rw [apply_of_eq_toUnboundedOperator
      (T.spectralIntegral_eq (measurable_phaseFn u₀) (isBoundedComplexFn_phaseFn u₀))] at h
    simp only [unitaryGroupOp_eq_boundedIntegralOp T]
    exact h
  · have h₁ : ‖phaseFn u x - phaseFn u₀ x‖ ≤ 2 := by
      calc _ ≤ ‖phaseFn u x‖ + ‖phaseFn u₀ x‖ := norm_sub_le _ _
        _ = 2 := by rw [norm_phaseFn, norm_phaseFn]; norm_num
    calc _ ≤ (2 : ℝ) ^ 2 := by gcongr
      _ = 4 := by norm_num
  · have hc : Continuous fun u => phaseFn u x := by
      unfold phaseFn
      fun_prop
    exact hc.tendsto u₀
theorem norm_phaseDiffQuot_le (u : ℝ) (x : Fin 1 → ℝ) :
    ‖(Complex.I * (u : ℂ))⁻¹ * (phaseFn u x - 1)‖ ≤ ‖coordFun 0 x‖ := by
  rcases eq_or_ne u 0 with rfl | hu
  · simp
  have h₁ : ‖phaseFn u x - 1‖ ≤ ‖u * x 0‖ := by
    rw [phaseFn_eq]
    exact Real.norm_exp_I_mul_ofReal_sub_one_le
  have h₂ : ‖coordFun 0 x‖ = |x 0| := by simp [coordFun]
  have hpos : 0 < |u| := abs_pos.2 hu
  rw [norm_mul, norm_inv, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs,
    h₂, inv_mul_le_iff₀ hpos]
  simpa [abs_mul] using h₁
theorem tendsto_phaseDiffQuot (x : Fin 1 → ℝ) :
    Tendsto (fun u : ℝ => (Complex.I * (u : ℂ))⁻¹ * (phaseFn u x - 1)) (𝓝[≠] 0)
      (𝓝 (coordFun 0 x)) := by
  have h₁ : HasDerivAt (fun u : ℝ => (Complex.I * (x 0 : ℂ)) * (u : ℂ))
      (Complex.I * (x 0 : ℂ)) 0 := by
    simpa using (Complex.ofRealCLM.hasDerivAt (x := (0 : ℝ))).const_mul (Complex.I * (x 0 : ℂ))
  have h₂ := h₁.cexp.tendsto_slope_zero
  have h₃ := h₂.const_mul (Complex.I⁻¹)
  have h₄ : Complex.I⁻¹ * (Complex.exp ((Complex.I * (x 0 : ℂ)) * ((0 : ℝ) : ℂ)) *
      (Complex.I * (x 0 : ℂ))) = coordFun 0 x := by
    simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero, one_mul, coordFun]
    rw [← mul_assoc, inv_mul_cancel₀ Complex.I_ne_zero, one_mul]
  rw [h₄] at h₃
  refine h₃.congr fun u => ?_
  simp only [zero_add, Complex.ofReal_zero, mul_zero, Complex.exp_zero, phaseFn,
    Complex.real_smul, mul_inv, Complex.ofReal_inv]
  rw [show Complex.I * (u : ℂ) * x 0 = Complex.I * (x 0 : ℂ) * (u : ℂ) by ring]
  ring
theorem unitaryGroupOp_tendsto_generator (T : SpectralToolkit F) (ψ : (F.coordinateOp 0).domain) :
    Tendsto (fun u : ℝ => (Complex.I * (u : ℂ))⁻¹ • (F.unitaryFlow u ψ - ψ)) (𝓝[≠] 0)
      (𝓝 (F.coordinateOp 0 ψ)) := by
  simp only [unitaryGroupOp_eq_boundedIntegralOp T]
  exact T.tendsto_diffQuot_apply measurable_phaseFn isBoundedComplexFn_phaseFn
    (measurable_coordFun 0) ψ.2
    (Eventually.of_forall fun u => ae_of_all _ fun x => norm_phaseDiffQuot_le u x)
    (ae_of_all _ tendsto_phaseDiffQuot)
theorem norm_unitaryGroupOp_diffQuot (u : ℝ) (ψ : ℋ) :
    ‖(Complex.I * (u : ℂ))⁻¹ • (F.unitaryFlow u ψ - ψ)‖ =
      |u|⁻¹ * ‖F.unitaryFlow u ψ - ψ‖ := by
  rw [norm_smul, norm_inv, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]
theorem mem_coordOp_dom_iff_unitary (T : SpectralToolkit F) (ψ : ℋ) :
    ψ ∈ (F.coordinateOp 0).domain ↔
      BddAbove ((fun u : ℝ => |u|⁻¹ * ‖F.unitaryFlow u ψ - ψ‖) '' {u | 0 < |u| ∧ |u| ≤ 1}) := by
  have hq : ∀ u : ℝ, (Complex.I * (u : ℂ))⁻¹ • (F.unitaryFlow u ψ - ψ) =
      F.boundedCalculus (fun x => (Complex.I * (u : ℂ))⁻¹ * (phaseFn u x - 1)) ψ := fun u => by
    rw [T.boundedIntegralOp_diffQuot_apply (measurable_phaseFn u) (isBoundedComplexFn_phaseFn u),
      unitaryGroupOp_eq_boundedIntegralOp T]
  constructor
  · intro hψ
    refine ⟨‖F.coordinateOp 0 ⟨ψ, hψ⟩‖, ?_⟩
    rintro _ ⟨u, -, rfl⟩
    simp only
    rw [← norm_unitaryGroupOp_diffQuot, hq]
    exact T.norm_le_of_dominated (measurable_diffQuot (measurable_phaseFn u) _)
      (isBoundedComplexFn_diffQuot (isBoundedComplexFn_phaseFn u) _) (measurable_coordFun 0) hψ
      (ae_of_all _ fun x => norm_phaseDiffQuot_le u x)
  · rintro ⟨c, hc⟩
    have hu : ∀ r : ℕ, (0 : ℝ) < 1 / ((r : ℝ) + 1) := fun r => by positivity
    have hc' : ∀ r : ℕ, ‖F.boundedCalculus (fun x =>
        (Complex.I * (((1 / ((r : ℝ) + 1) : ℝ)) : ℂ))⁻¹ *
        (phaseFn (1 / ((r : ℝ) + 1)) x - 1)) ψ‖ ≤ c := fun r => by
      rw [← hq, norm_unitaryGroupOp_diffQuot]
      refine hc ⟨1 / ((r : ℝ) + 1), ⟨abs_pos.2 (hu r).ne', ?_⟩, rfl⟩
      rw [abs_of_pos (hu r), div_le_one (by positivity)]
      have : (0 : ℝ) ≤ r := Nat.cast_nonneg r
      linarith
    refine T.mem_dom_of_bounded_approx
      (fun r => measurable_diffQuot (measurable_phaseFn _) _)
      (fun r => isBoundedComplexFn_diffQuot (isBoundedComplexFn_phaseFn _) _)
      (measurable_coordFun 0) hc' (ae_of_all _ fun x => ?_)
    refine (tendsto_phaseDiffQuot x).comp ?_
    exact tendsto_nhdsWithin_iff.2 ⟨tendsto_one_div_add_atTop_nhds_zero_nat,
      Eventually.of_forall fun r => (hu r).ne'⟩
theorem unitaryGroupOp_preserves_dom (T : SpectralToolkit F) (u : ℝ)
    (ψ : (F.coordinateOp 0).domain) :
    ∃ h : F.unitaryFlow u ψ ∈ (F.coordinateOp 0).domain,
      F.coordinateOp 0 ⟨F.unitaryFlow u ψ, h⟩ =
        F.unitaryFlow u (F.coordinateOp 0 ψ) := by
  obtain ⟨hχ, hfg, e₁, e₂⟩ := T.laws.calculus_boundedCalculus (coordFun 0) (phaseFn u)
    (measurable_coordFun 0) (measurable_phaseFn u) (isBoundedComplexFn_phaseFn u) ψ ψ.2
  rw [unitaryGroupOp_eq_boundedIntegralOp T]
  exact ⟨hχ, e₁.trans e₂⟩
end Group
section Sign
set_option linter.unusedSectionVars false
variable {ℋ : Type} [NormedAddCommGroup ℋ] [InnerProductSpace ℂ ℋ] [CompleteSpace ℋ]
  {F : ProjectionMeasure 1 ℋ}
theorem SpectralToolkit.integrable_of_mem_dom {n : ℕ} [NeZero n] {E : ProjectionMeasure n ℋ}
    (T : SpectralToolkit E) {f : (Fin n → ℝ) → ℂ} (hf : Measurable f) {ψ : ℋ}
    (hψ : ψ ∈ (E.functionalCalculus f).domain) : Integrable f (E.spectralValueMeasure ψ) := by
  have := T.isFinite ψ
  have h : MemLp f 2 (E.spectralValueMeasure ψ) :=
    (memLp_two_iff_integrable_sq_norm hf.aestronglyMeasurable).2 (T.integrable_norm_sq hf hψ)
  exact h.integrable one_le_two
theorem inner_coordOp_eq_integral (T : SpectralToolkit F) (ψ : (F.coordinateOp 0).domain) :
    ⟪(ψ : ℋ), F.coordinateOp 0 ψ⟫_ℂ = ((∫ x, x 0 ∂(F.spectralValueMeasure ψ) : ℝ) : ℂ) := by
  refine (T.laws.inner_self (coordFun 0) (measurable_coordFun 0) ψ).trans ?_
  exact integral_complex_ofReal (f := fun x : Fin 1 → ℝ => x 0)
theorem integrable_coord (T : SpectralToolkit F) (ψ : (F.coordinateOp 0).domain) :
    Integrable (fun x : Fin 1 → ℝ => x 0) (F.spectralValueMeasure ψ) := by
  have h := T.integrable_of_mem_dom (measurable_coordFun 0) ψ.2
  exact h.re
theorem inner_coordOp_nonneg_of_concentrated (T : SpectralToolkit F)
    (hc : F.IsConcentratedOn nonnegReals) (ψ : (F.coordinateOp 0).domain) :
    0 ≤ ⟪(ψ : ℋ), F.coordinateOp 0 ψ⟫_ℂ := by
  rw [inner_coordOp_eq_integral T]
  refine Complex.zero_le_real.2 (integral_nonneg_of_ae ?_)
  filter_upwards [ae_not_mem_of_proj_eq_zero hc ψ] with x hx
  simpa [nonnegReals] using hx
theorem diagonalMeasure_proj_apply {n : ℕ} [NeZero n] (E : ProjectionMeasure n ℋ)
    (D : BorelSets n) (ψ : ℋ) :
    E.spectralValueMeasure (E D ψ) = (E.spectralValueMeasure ψ).restrict D.1 := by
  refine Measure.ext fun A hA => ?_
  rw [Measure.restrict_apply hA, spectralValueMeasure_apply E (E D ψ) ⟨A, hA⟩,
    spectralValueMeasure_apply E ψ ⟨A ∩ D.1, hA.inter D.2⟩]
  have h := E.map_inter ⟨A, hA⟩ D
  simp only at h
  rw [h]
  rfl
theorem proj_eq_zero_of_inner_nonneg (T : SpectralToolkit F)
    (hpos : ∀ ψ : (F.coordinateOp 0).domain, 0 ≤ ⟪(ψ : ℋ), F.coordinateOp 0 ψ⟫_ℂ)
    (D : BorelSets 1) (c d : ℝ) (hc : 0 < c) (hD : ∀ x ∈ D.1, -d ≤ x 0 ∧ x 0 ≤ -c) :
    F D = 0 := by
  ext ψ
  set χ := F D ψ with hχ
  have hm := diagonalMeasure_proj_apply F D ψ
  rw [← hχ] at hm
  have := T.isFinite χ
  have := T.isFinite ψ
  have hae : ∀ᵐ x ∂(F.spectralValueMeasure χ), x ∈ D.1 := by
    rw [hm]
    exact ae_restrict_mem D.2
  have hdom : χ ∈ (F.coordinateOp 0).domain := by
    refine (T.mem_dom_iff (measurable_coordFun 0) χ).2 ?_
    have hb : ∀ x ∈ D.1, ‖coordFun 0 x‖ₑ ^ 2 ≤ ENNReal.ofReal (max c d) ^ 2 := fun x hx => by
      have h₁ : ‖coordFun 0 x‖ ≤ max c d := by
        have h₂ : ‖coordFun 0 x‖ = |x 0| := by simp [coordFun]
        rw [h₂, abs_le]
        have := hD x hx
        constructor
        · have : -max c d ≤ -d := neg_le_neg (le_max_right _ _)
          linarith
        · have : c ≤ max c d := le_max_left _ _
          linarith
      gcongr
      rw [← ofReal_norm]
      exact ENNReal.ofReal_le_ofReal h₁
    have h₃ : ∫⁻ x, ‖coordFun 0 x‖ₑ ^ 2 ∂(F.spectralValueMeasure χ) ≤
        ∫⁻ _, ENNReal.ofReal (max c d) ^ 2 ∂(F.spectralValueMeasure χ) := by
      refine lintegral_mono_ae ?_
      filter_upwards [hae] with x hx using hb x hx
    refine lt_of_le_of_lt h₃ ?_
    rw [lintegral_const]
    exact ENNReal.mul_lt_top (by simp) (measure_lt_top _ _)
  have h₁ := hpos ⟨χ, hdom⟩
  rw [inner_coordOp_eq_integral T] at h₁
  have h₂ : 0 ≤ ∫ x, x 0 ∂(F.spectralValueMeasure χ) := Complex.zero_le_real.1 h₁
  have h₃ : ∫ x : Fin 1 → ℝ, x 0 ∂(F.spectralValueMeasure χ) ≤
      ∫ _ : Fin 1 → ℝ, -c ∂(F.spectralValueMeasure χ) := by
    refine integral_mono_ae (integrable_coord T ⟨χ, hdom⟩) (integrable_const _) ?_
    filter_upwards [hae] with x hx using (hD x hx).2
  rw [integral_const, smul_eq_mul, measureReal_def, T.supportProps.spectralValueMeasure_univ χ,
    ENNReal.toReal_ofReal (by positivity)] at h₃
  have h₄ : ‖χ‖ ^ 2 ≤ 0 := by nlinarith
  have h₅ : ‖χ‖ ^ 2 = 0 := le_antisymm h₄ (by positivity)
  simpa using h₅
theorem isConcentratedOn_nonnegReals_iff (T : SpectralToolkit F) :
    F.IsConcentratedOn nonnegReals ↔
      ∀ ψ : (F.coordinateOp 0).domain, 0 ≤ ⟪(ψ : ℋ), F.coordinateOp 0 ψ⟫_ℂ := by
  refine ⟨inner_coordOp_nonneg_of_concentrated T, fun hpos => ?_⟩
  let Δ : ℕ → BorelSets 1 := fun r =>
    ⟨{x | -((r : ℝ) + 1) ≤ x 0 ∧ x 0 ≤ -(1 / ((r : ℝ) + 1))},
      (measurableSet_le measurable_const (measurable_pi_apply 0)).inter
        (measurableSet_le (measurable_pi_apply 0) measurable_const)⟩
  have hΔ : ∀ r, F.VanishesOn (Δ r) := fun r =>
    proj_eq_zero_of_inner_nonneg T hpos (Δ r) (1 / ((r : ℝ) + 1)) ((r : ℝ) + 1) (by positivity)
      fun x hx => hx
  have h := T.supportProps.vanishesOn_iUnion ℕ Δ hΔ
  have hs : (⟨⋃ r, (Δ r).1, MeasurableSet.iUnion fun r => (Δ r).2⟩ : BorelSets 1) =
      ⟨nonnegReals.1ᶜ, nonnegReals.2.compl⟩ := by
    refine Subtype.ext (Set.ext fun x => ?_)
    simp only [mem_iUnion, nonnegReals, mem_compl_iff, Set.mem_ofPred_eq, not_le, Δ]
    constructor
    · rintro ⟨r, -, h₂⟩
      have : 0 < 1 / ((r : ℝ) + 1) := by positivity
      linarith
    · intro hx
      obtain ⟨r, hr⟩ := exists_nat_gt (max (-x 0) (-x 0)⁻¹)
      have h₁ : -x 0 < r := lt_of_le_of_lt (le_max_left _ _) hr
      have h₂ : (-x 0)⁻¹ < r := lt_of_le_of_lt (le_max_right _ _) hr
      have hpx : 0 < -x 0 := by linarith
      refine ⟨r, by linarith, ?_⟩
      have hr1 : (0 : ℝ) < (r : ℝ) + 1 := by linarith
      have h₃ : 1 / ((r : ℝ) + 1) ≤ -x 0 := by
        rw [div_le_iff₀ hr1]
        have h₄ : (-x 0)⁻¹ ≤ (r : ℝ) + 1 := by linarith
        have h₅ := mul_le_mul_of_nonneg_left h₄ hpx.le
        rwa [mul_inv_cancel₀ hpx.ne'] at h₅
      linarith
  rw [hs] at h
  exact h
end Sign
section Kernel
set_option linter.unusedSectionVars false
variable {ℋ : Type} [NormedAddCommGroup ℋ] [InnerProductSpace ℂ ℋ] [CompleteSpace ℋ]
  {F : ProjectionMeasure 1 ℋ}
def puncturedLine : BorelSets 1 :=
  ⟨zeroPoint.1ᶜ, zeroPoint.2.compl⟩
theorem mem_puncturedLine_iff (x : Fin 1 → ℝ) : x ∈ puncturedLine.1 ↔ x 0 ≠ 0 := by
  have h : x = 0 ↔ x 0 = 0 := by
    constructor
    · rintro rfl
      rfl
    · intro hx
      funext i
      rw [Subsingleton.elim i 0, hx]
      rfl
  change ¬ x = 0 ↔ _
  rw [h]
theorem mem_opKernel_coordOp_iff (T : SpectralToolkit F) (ψ : ℋ) :
    ψ ∈ opKernel (F.coordinateOp 0) ↔ F puncturedLine ψ = 0 := by
  have := T.isFinite ψ
  constructor
  · rintro ⟨h, e⟩
    have h₁ := T.laws.norm_sq (coordFun 0) (measurable_coordFun 0) ⟨ψ, h⟩
    have e' : F.functionalCalculus (coordFun 0) ⟨ψ, h⟩ = 0 := e
    rw [e', norm_zero] at h₁
    have h₂ : ∫ x, ‖coordFun 0 x‖ ^ 2 ∂(F.spectralValueMeasure ψ) = 0 := by
      rw [← h₁]
      norm_num
    have h₃ := (integral_eq_zero_iff_of_nonneg (fun x => by positivity)
      (T.integrable_norm_sq (measurable_coordFun 0) h)).1 h₂
    rw [← diagonalMeasure_eq_zero_iff]
    refine measure_mono_null ?_ (ae_iff.1 h₃)
    intro x hx
    have hx' := (mem_puncturedLine_iff x).1 hx
    simpa [coordFun] using hx'
  · intro h
    have h₀ : F.spectralValueMeasure ψ puncturedLine.1 = 0 :=
      (diagonalMeasure_eq_zero_iff _ _).2 h
    have h₁ : ∀ᵐ x ∂(F.spectralValueMeasure ψ), coordFun 0 x = 0 := by
      filter_upwards [measure_eq_zero_iff_ae_notMem.1 h₀] with x hx
      have h₂ : ¬ x 0 ≠ 0 := fun h₂ => hx ((mem_puncturedLine_iff x).2 h₂)
      simpa [coordFun] using h₂
    have h₂ : ψ ∈ (F.coordinateOp 0).domain := by
      refine (T.mem_dom_iff (measurable_coordFun 0) ψ).2 ?_
      have h₃ : ∫⁻ x, ‖coordFun 0 x‖ₑ ^ 2 ∂(F.spectralValueMeasure ψ) = 0 := by
        rw [lintegral_eq_zero_iff ((measurable_coordFun 0).enorm.pow_const 2)]
        filter_upwards [h₁] with x hx
        simp [hx]
      rw [h₃]
      exact ENNReal.zero_lt_top
    refine ⟨h₂, ?_⟩
    have h₃ := T.laws.norm_sq (coordFun 0) (measurable_coordFun 0) ⟨ψ, h₂⟩
    have h₄ : ∫ x, ‖coordFun 0 x‖ ^ 2 ∂(F.spectralValueMeasure ψ) = 0 := by
      rw [integral_eq_zero_of_ae]
      filter_upwards [h₁] with x hx
      simp [hx]
    rw [h₄] at h₃
    exact show F.functionalCalculus (coordFun 0) ⟨ψ, h₂⟩ = 0 from by
      simpa using h₃
theorem mem_range_proj_zeroPoint_iff (T : SpectralToolkit F) (ψ : ℋ) :
    ψ ∈ Set.range (F zeroPoint) ↔ F puncturedLine ψ = 0 := by
  have hadd := T.proj_add_proj_compl zeroPoint
  constructor
  · rintro ⟨φ, rfl⟩
    have h := F.map_inter puncturedLine zeroPoint
    have hs : (⟨puncturedLine.1 ∩ zeroPoint.1,
        puncturedLine.2.inter zeroPoint.2⟩ : BorelSets 1) = ⟨∅, MeasurableSet.empty⟩ :=
      Subtype.ext (compl_inter_self _)
    rw [hs, F.map_empty] at h
    have h₂ := DFunLike.congr_fun h φ
    simpa using h₂.symm
  · intro h
    refine ⟨ψ, ?_⟩
    have h₂ := DFunLike.congr_fun hadd ψ
    have h₃ : F ⟨zeroPoint.1ᶜ, zeroPoint.2.compl⟩ ψ = 0 := h
    simpa [h₃] using h₂
theorem opKernel_coordOp_eq_range (T : SpectralToolkit F) :
    opKernel (F.coordinateOp 0) = Set.range (F zeroPoint) :=
  Set.ext fun ψ => (mem_opKernel_coordOp_iff T ψ).trans (mem_range_proj_zeroPoint_iff T ψ).symm
end Kernel
section Semigroup
set_option linter.unusedSectionVars false
variable {ℋ : Type} [NormedAddCommGroup ℋ] [InnerProductSpace ℂ ℋ] [CompleteSpace ℋ]
  {F : ProjectionMeasure 1 ℋ}
def decayFn (t : ℝ≥0) : (Fin 1 → ℝ) → ℂ :=
  extendByZero nonnegReals fun x => Complex.exp (-(t : ℂ) * (x.1 0 : ℝ))
theorem decayFn_of_nonneg (t : ℝ≥0) {x : Fin 1 → ℝ} (hx : 0 ≤ x 0) :
    decayFn t x = ((Real.exp (-(t : ℝ) * x 0) : ℝ) : ℂ) := by
  have h := extendByZero_apply_of_mem nonnegReals
    (fun x => Complex.exp (-(t : ℂ) * (x.1 0 : ℝ))) ⟨x, hx⟩
  refine h.trans ?_
  push_cast
  rfl
theorem decayFn_of_neg (t : ℝ≥0) {x : Fin 1 → ℝ} (hx : x 0 < 0) : decayFn t x = 0 :=
  extendByZero_apply_of_not_mem nonnegReals _ (not_le.2 hx)
theorem measurable_decayFn (t : ℝ≥0) : Measurable (decayFn t) :=
  measurable_extendByZero _ (Complex.measurable_exp.comp
    ((Complex.measurable_ofReal.comp
      ((measurable_pi_apply 0).comp measurable_subtype_coe)).const_mul _))
theorem decayFn_mem_unitInterval (t : ℝ≥0) (x : Fin 1 → ℝ) :
    ∃ r : ℝ, 0 ≤ r ∧ r ≤ 1 ∧ decayFn t x = r := by
  rcases lt_or_ge (x 0) 0 with hx | hx
  · exact ⟨0, le_rfl, zero_le_one, by simp [decayFn_of_neg t hx]⟩
  · refine ⟨Real.exp (-(t : ℝ) * x 0), (Real.exp_pos _).le, ?_, decayFn_of_nonneg t hx⟩
    refine Real.exp_le_one_iff.2 ?_
    have : 0 ≤ (t : ℝ) * x 0 := mul_nonneg t.2 hx
    linarith
theorem norm_decayFn_le (t : ℝ≥0) (x : Fin 1 → ℝ) : ‖decayFn t x‖ ≤ 1 := by
  obtain ⟨r, h₀, h₁, h⟩ := decayFn_mem_unitInterval t x
  rw [h, Complex.norm_real, Real.norm_of_nonneg h₀]
  exact h₁
theorem isBoundedComplexFn_decayFn (t : ℝ≥0) : IsBoundedComplexFn (decayFn t) :=
  ⟨1, norm_decayFn_le t⟩
theorem heatSemigroupOp_eq_boundedIntegralOp (T : SpectralToolkit F) (t : ℝ≥0) :
    F.contractionFlow t = F.boundedCalculus (decayFn t) :=
  toBounded_eq_of_eq
    (T.spectralIntegral_eq (measurable_decayFn t) (isBoundedComplexFn_decayFn t))
theorem heatSemigroup_eq_ofBounded (T : SpectralToolkit F) (t : ℝ≥0) :
    F.expNegMulOp t = ofBounded (F.contractionFlow t) := by
  rw [heatSemigroupOp_eq_boundedIntegralOp T]
  exact T.spectralIntegral_eq (measurable_decayFn t) (isBoundedComplexFn_decayFn t)
theorem heatSemigroupOp_isSelfAdjoint (T : SpectralToolkit F) (t : ℝ≥0) :
    IsSelfAdjoint (F.contractionFlow t) := by
  have h : (fun x => conj (decayFn t x)) = decayFn t := by
    funext x
    obtain ⟨r, -, -, h⟩ := decayFn_mem_unitInterval t x
    rw [h, Complex.conj_ofReal]
  change star (F.contractionFlow t) = F.contractionFlow t
  rw [heatSemigroupOp_eq_boundedIntegralOp T,
    T.laws.star_boundedCalculus _ (measurable_decayFn t) (isBoundedComplexFn_decayFn t), h]
theorem loewnerGe_zero_of_nonneg (T : SpectralToolkit F) {f : (Fin 1 → ℝ) → ℂ}
    (hf : Measurable f) (hb : IsBoundedComplexFn f) (him : ∀ x, (f x).im = 0)
    (hre : ∀ x, 0 ≤ (f x).re) : LoewnerGe (F.boundedCalculus f) 0 := by
  refine (T.laws.loewnerGe_zero_iff f hf him hb).2 ?_
  have hs : (⟨{x | (f x).re < 0}, measurableSet_lt (Complex.measurable_re.comp hf)
      measurable_const⟩ : BorelSets 1) = ⟨∅, MeasurableSet.empty⟩ :=
    Subtype.ext (Set.eq_empty_of_forall_notMem fun x hx => absurd hx (not_lt.2 (hre x)))
  rw [hs, F.map_empty]
theorem heatSemigroupOp_nonneg (T : SpectralToolkit F) (t : ℝ≥0) :
    LoewnerGe (F.contractionFlow t) 0 := by
  rw [heatSemigroupOp_eq_boundedIntegralOp T]
  refine loewnerGe_zero_of_nonneg T (measurable_decayFn t)
    (isBoundedComplexFn_decayFn t) (fun x => ?_) (fun x => ?_)
  · obtain ⟨r, -, -, h⟩ := decayFn_mem_unitInterval t x
    simp [h]
  · obtain ⟨r, h₀, -, h⟩ := decayFn_mem_unitInterval t x
    simpa [h] using h₀
theorem heatSemigroupOp_le_one (T : SpectralToolkit F) (t : ℝ≥0) :
    LoewnerGe 1 (F.contractionFlow t) := by
  have hf := measurable_decayFn t
  have hb := isBoundedComplexFn_decayFn t
  have h := T.boundedIntegralOp_linComb measurable_const hf isBoundedComplexFn_const_one hb 1 (-1)
  rw [T.boundedIntegralOp_const_one] at h
  have h₂ := loewnerGe_zero_of_nonneg T (f := fun x => 1 * 1 + -1 * decayFn t x)
    (measurable_const.add (hf.const_mul _))
    (isBoundedComplexFn_linComb isBoundedComplexFn_const_one hb 1 (-1))
    (fun x => ?_) (fun x => ?_)
  · rw [h] at h₂
    intro ψ
    have h₃ := h₂ ψ
    rw [heatSemigroupOp_eq_boundedIntegralOp T]
    simpa [sub_eq_add_neg] using h₃
  · obtain ⟨r, -, -, h⟩ := decayFn_mem_unitInterval t x
    simp [h]
  · obtain ⟨r, -, h₁, h⟩ := decayFn_mem_unitInterval t x
    simpa [h] using h₁
theorem heatSemigroupOp_zero (T : SpectralToolkit F) (hc : F.IsConcentratedOn nonnegReals) :
    F.contractionFlow 0 = 1 := by
  have hm : Measurable fun _ : Fin 1 → ℝ => (1 : ℂ) := measurable_const
  have h := T.boundedIntegralOp_congr (measurable_decayFn 0) hm
    (isBoundedComplexFn_decayFn 0) isBoundedComplexFn_const_one
    (T.supportProps.vanishesOn_of_subset ⟨nonnegReals.1ᶜ, nonnegReals.2.compl⟩ _ ?_ hc)
  · rw [heatSemigroupOp_eq_boundedIntegralOp T, h, T.boundedIntegralOp_const_one]
  · intro x hx hx₀
    apply hx
    have hx₁ : 0 ≤ x 0 := hx₀
    rw [decayFn_of_nonneg 0 hx₁]
    simp
theorem heatSemigroupOp_mul (T : SpectralToolkit F) (t t' : ℝ≥0) :
    F.contractionFlow t * F.contractionFlow t' = F.contractionFlow (t + t') := by
  have h : (fun x => decayFn t x * decayFn t' x) = decayFn (t + t') := by
    funext x
    rcases lt_or_ge (x 0) 0 with hx | hx
    · simp [decayFn_of_neg _ hx]
    · rw [decayFn_of_nonneg _ hx, decayFn_of_nonneg _ hx,
        decayFn_of_nonneg _ hx, ← Complex.ofReal_mul, ← Real.exp_add]
      congr 2
      push_cast
      ring
  rw [heatSemigroupOp_eq_boundedIntegralOp T, heatSemigroupOp_eq_boundedIntegralOp T,
    heatSemigroupOp_eq_boundedIntegralOp T,
    T.laws.boundedCalculus_mul _ _ (measurable_decayFn t) (measurable_decayFn t')
      (isBoundedComplexFn_decayFn t) (isBoundedComplexFn_decayFn t'), h]
def decayScale (t : ℝ≥0) : ℂ :=
  -(((t : ℝ) : ℂ)⁻¹)
theorem decayDiffQuot_eq_real (t : ℝ≥0) {x : Fin 1 → ℝ} (hx : 0 ≤ x 0) :
    decayScale t * (decayFn t x - 1) =
      (((t : ℝ)⁻¹ * (1 - Real.exp (-(t : ℝ) * x 0)) : ℝ) : ℂ) := by
  rw [decayFn_of_nonneg t hx, decayScale]
  push_cast
  ring
theorem norm_decayDiffQuot_le (t : ℝ≥0) {x : Fin 1 → ℝ} (hx : 0 ≤ x 0) :
    ‖decayScale t * (decayFn t x - 1)‖ ≤ ‖coordFun 0 x‖ := by
  rcases eq_or_ne t 0 with rfl | ht
  · simp [decayScale]
  have ht' : (0 : ℝ) < t := by
    have := pos_iff_ne_zero.2 ht
    exact_mod_cast this
  have hy : 0 ≤ (t : ℝ) * x 0 := mul_nonneg ht'.le hx
  have h₁ : 0 ≤ 1 - Real.exp (-(t : ℝ) * x 0) := by
    have : Real.exp (-(t : ℝ) * x 0) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
    linarith
  have h₂ : 1 - Real.exp (-(t : ℝ) * x 0) ≤ t * x 0 := by
    have := Real.add_one_le_exp (-(t : ℝ) * x 0)
    linarith
  have h₃ : ‖coordFun 0 x‖ = x 0 := by
    simp [coordFun, abs_of_nonneg hx]
  rw [decayDiffQuot_eq_real t hx, Complex.norm_real, Real.norm_of_nonneg (by positivity), h₃,
    inv_mul_le_iff₀ ht']
  exact h₂
theorem tendsto_nnreal_coe_nhdsNE :
    Tendsto (fun t : ℝ≥0 => (t : ℝ)) (𝓝[>] 0) (𝓝[≠] 0) := by
  refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
  · exact (NNReal.continuous_coe.tendsto' 0 0 rfl).mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with t ht
    have h : (0 : ℝ≥0) < t := ht
    exact show (t : ℝ) ≠ 0 from by exact_mod_cast h.ne'
theorem tendsto_decayDiffQuot {x : Fin 1 → ℝ} (hx : 0 ≤ x 0) :
    Tendsto (fun t : ℝ≥0 => decayScale t * (decayFn t x - 1)) (𝓝[>] 0)
      (𝓝 (coordFun 0 x)) := by
  have h₁ : HasDerivAt (fun s : ℝ => (-(x 0 : ℂ)) * (s : ℂ)) (-(x 0 : ℂ)) 0 := by
    simpa using (Complex.ofRealCLM.hasDerivAt (x := (0 : ℝ))).const_mul (-(x 0 : ℂ))
  have h₂ := (h₁.cexp.tendsto_slope_zero.neg).comp tendsto_nnreal_coe_nhdsNE
  have h₄ : -(Complex.exp ((-(x 0 : ℂ)) * ((0 : ℝ) : ℂ)) * (-(x 0 : ℂ))) = coordFun 0 x := by
    simp [coordFun]
  rw [h₄] at h₂
  refine h₂.congr fun t => ?_
  rw [decayFn_of_nonneg t hx, decayScale]
  simp only [Function.comp_apply, zero_add, Complex.ofReal_zero, mul_zero, Complex.exp_zero,
    Complex.real_smul, Complex.ofReal_inv, Complex.ofReal_exp, Complex.ofReal_mul,
    Complex.ofReal_neg]
  rw [show -(x 0 : ℂ) * ((t : ℝ) : ℂ) = -((t : ℝ) : ℂ) * (x 0 : ℂ) by ring]
  ring
theorem ae_coord_nonneg_of_concentrated (hc : F.IsConcentratedOn nonnegReals) (ψ : ℋ) :
    ∀ᵐ x ∂(F.spectralValueMeasure ψ), 0 ≤ x 0 := by
  filter_upwards [ae_not_mem_of_proj_eq_zero hc ψ] with x hx
  simpa [nonnegReals] using hx
theorem heatSemigroupOp_diffQuot_eq (T : SpectralToolkit F) (t : ℝ≥0) (ψ : ℋ) :
    ((t : ℝ) : ℂ)⁻¹ • (ψ - F.contractionFlow t ψ) =
      F.boundedCalculus (fun x => decayScale t * (decayFn t x - 1)) ψ := by
  rw [T.boundedIntegralOp_diffQuot_apply (measurable_decayFn t) (isBoundedComplexFn_decayFn t),
    heatSemigroupOp_eq_boundedIntegralOp T, decayScale, neg_smul, ← smul_neg, neg_sub]
theorem heatSemigroupOp_tendsto_generator (T : SpectralToolkit F)
    (hc : F.IsConcentratedOn nonnegReals) (ψ : (F.coordinateOp 0).domain) :
    Tendsto (fun t : ℝ≥0 => ((t : ℝ) : ℂ)⁻¹ • ((ψ : ℋ) - F.contractionFlow t ψ)) (𝓝[>] 0)
      (𝓝 (F.coordinateOp 0 ψ)) := by
  have h := T.tendsto_diffQuot_apply (a := decayScale) (p := decayFn)
    measurable_decayFn isBoundedComplexFn_decayFn (measurable_coordFun 0) ψ.2
    (l := 𝓝[>] 0) (Eventually.of_forall fun t => ?_) ?_
  · refine h.congr fun t => ?_
    rw [heatSemigroupOp_eq_boundedIntegralOp T, decayScale, neg_smul, ← smul_neg, neg_sub]
  · filter_upwards [ae_coord_nonneg_of_concentrated hc ψ] with x hx
      using norm_decayDiffQuot_le t hx
  · filter_upwards [ae_coord_nonneg_of_concentrated hc ψ] with x hx
      using tendsto_decayDiffQuot hx
theorem norm_heatSemigroupOp_diffQuot (t : ℝ≥0) (ψ : ℋ) :
    ‖((t : ℝ) : ℂ)⁻¹ • (ψ - F.contractionFlow t ψ)‖ =
      (t : ℝ)⁻¹ * ‖ψ - F.contractionFlow t ψ‖ := by
  rw [norm_smul, norm_inv, Complex.norm_real, Real.norm_of_nonneg (NNReal.coe_nonneg t)]
def reciprocalTime (r : ℕ) : ℝ≥0 :=
  ⟨1 / ((r : ℝ) + 1), by positivity⟩
theorem reciprocalTime_pos (r : ℕ) : 0 < reciprocalTime r := by
  change (0 : ℝ) < 1 / ((r : ℝ) + 1)
  positivity
theorem reciprocalTime_le_one (r : ℕ) : reciprocalTime r ≤ 1 := by
  change 1 / ((r : ℝ) + 1) ≤ 1
  rw [div_le_one (by positivity)]
  have : (0 : ℝ) ≤ r := Nat.cast_nonneg r
  linarith
theorem tendsto_reciprocalTime : Tendsto reciprocalTime atTop (𝓝[>] 0) := by
  refine tendsto_nhdsWithin_iff.2 ⟨?_, Eventually.of_forall reciprocalTime_pos⟩
  rw [← NNReal.tendsto_coe]
  exact tendsto_one_div_add_atTop_nhds_zero_nat
theorem mem_coordOp_dom_iff_heat (T : SpectralToolkit F) (hc : F.IsConcentratedOn nonnegReals)
    (ψ : ℋ) :
    ψ ∈ (F.coordinateOp 0).domain ↔
      BddAbove ((fun t : ℝ≥0 => (t : ℝ)⁻¹ * ‖ψ - F.contractionFlow t ψ‖) ''
        {t | 0 < t ∧ t ≤ 1}) := by
  constructor
  · intro hψ
    refine ⟨‖F.coordinateOp 0 ⟨ψ, hψ⟩‖, ?_⟩
    rintro _ ⟨t, -, rfl⟩
    simp only
    rw [← norm_heatSemigroupOp_diffQuot, heatSemigroupOp_diffQuot_eq T]
    refine T.norm_le_of_dominated (measurable_diffQuot (measurable_decayFn t) _)
      (isBoundedComplexFn_diffQuot (isBoundedComplexFn_decayFn t) _) (measurable_coordFun 0) hψ ?_
    filter_upwards [ae_coord_nonneg_of_concentrated hc ψ] with x hx
      using norm_decayDiffQuot_le t hx
  · rintro ⟨c, hc'⟩
    have hb : ∀ r : ℕ, ‖F.boundedCalculus (fun x => decayScale (reciprocalTime r) *
        (decayFn (reciprocalTime r) x - 1)) ψ‖ ≤ c := fun r => by
      rw [← heatSemigroupOp_diffQuot_eq T, norm_heatSemigroupOp_diffQuot]
      exact hc' ⟨reciprocalTime r, ⟨reciprocalTime_pos r, reciprocalTime_le_one r⟩, rfl⟩
    refine T.mem_dom_of_bounded_approx
      (fun r => measurable_diffQuot (measurable_decayFn _) _)
      (fun r => isBoundedComplexFn_diffQuot (isBoundedComplexFn_decayFn _) _)
      (measurable_coordFun 0) hb ?_
    filter_upwards [ae_coord_nonneg_of_concentrated hc ψ] with x hx
    exact (tendsto_decayDiffQuot hx).comp tendsto_reciprocalTime
theorem heatSemigroupOp_mul_proj_zeroPoint (T : SpectralToolkit F) (t : ℝ≥0) :
    F.contractionFlow t * F zeroPoint = F zeroPoint := by
  have hm : Measurable (zeroPoint.1.indicator fun _ => (1 : ℂ)) :=
    measurable_const.indicator zeroPoint.2
  have hb : IsBoundedComplexFn (zeroPoint.1.indicator fun _ => (1 : ℂ)) := by
    refine ⟨1, fun x => ?_⟩
    by_cases hx : x ∈ zeroPoint.1 <;> simp [hx]
  have h : (fun x => decayFn t x * zeroPoint.1.indicator (fun _ => (1 : ℂ)) x) =
      zeroPoint.1.indicator fun _ => (1 : ℂ) := by
    funext x
    by_cases hx : x ∈ zeroPoint.1
    · have hx₀ : x = 0 := hx
      subst hx₀
      rw [Set.indicator_of_mem hx, decayFn_of_nonneg t le_rfl]
      simp
    · simp [hx]
  rw [heatSemigroupOp_eq_boundedIntegralOp T, ← T.boundedIntegralOp_indicator zeroPoint,
    T.laws.boundedCalculus_mul _ _ (measurable_decayFn t) hm (isBoundedComplexFn_decayFn t) hb,
    h]
theorem heatSemigroupOp_tendstoStrongly (T : SpectralToolkit F)
    (hc : F.IsConcentratedOn nonnegReals) :
    TendstoStrongly atTop F.contractionFlow (F zeroPoint) := by
  intro ψ
  have := T.isFinite ψ
  have hm : Measurable (zeroPoint.1.indicator fun _ => (1 : ℂ)) :=
    measurable_const.indicator zeroPoint.2
  have hb : IsBoundedComplexFn (zeroPoint.1.indicator fun _ => (1 : ℂ)) := by
    refine ⟨1, fun x => ?_⟩
    by_cases hx : x ∈ zeroPoint.1 <;> simp [hx]
  have hψ := T.mem_dom_of_bounded hm hb ψ
  have h := T.tendsto_of_dominated_sq (l := atTop) (p := decayFn)
    measurable_decayFn isBoundedComplexFn_decayFn hm hψ
    (G := fun _ => 4) (integrable_const _)
    (Eventually.of_forall fun t => ae_of_all _ fun x => ?_) ?_
  · rw [apply_of_eq_toUnboundedOperator (T.spectralIntegral_eq hm hb),
      T.boundedIntegralOp_indicator zeroPoint] at h
    simp only [heatSemigroupOp_eq_boundedIntegralOp T]
    exact h
  · have h₁ : ‖decayFn t x - zeroPoint.1.indicator (fun _ => (1 : ℂ)) x‖ ≤ 2 := by
      calc _ ≤ ‖decayFn t x‖ + ‖zeroPoint.1.indicator (fun _ => (1 : ℂ)) x‖ :=
            norm_sub_le _ _
        _ ≤ 1 + 1 := by
            refine add_le_add (norm_decayFn_le t x) ?_
            by_cases hx : x ∈ zeroPoint.1 <;> simp [hx]
        _ = 2 := by norm_num
    calc _ ≤ (2 : ℝ) ^ 2 := by gcongr
      _ = 4 := by norm_num
  · filter_upwards [ae_coord_nonneg_of_concentrated hc ψ] with x hx
    by_cases hx₀ : x ∈ zeroPoint.1
    · have hx₁ : x = 0 := hx₀
      subst hx₁
      rw [Set.indicator_of_mem hx₀]
      refine tendsto_const_nhds.congr fun t => ?_
      rw [decayFn_of_nonneg t le_rfl]
      simp
    · have hpos : 0 < x 0 := lt_of_le_of_ne hx fun h₀ =>
        (mem_puncturedLine_iff x).1 hx₀ h₀.symm
      rw [Set.indicator_of_notMem hx₀]
      have h₁ : Tendsto (fun t : ℝ≥0 => -(t : ℝ) * x 0) atTop atBot := by
        have h₂ : Tendsto (fun t : ℝ≥0 => (t : ℝ)) atTop atTop :=
          NNReal.tendsto_coe_atTop.2 tendsto_id
        exact (tendsto_neg_atTop_atBot.comp (h₂.atTop_mul_const hpos)).congr fun t => by simp
      have h₃ := (Complex.continuous_ofReal.tendsto 0).comp (Real.tendsto_exp_atBot.comp h₁)
      simp only [Complex.ofReal_zero] at h₃
      refine h₃.congr fun t => ?_
      rw [decayFn_of_nonneg t hx]
      rfl
theorem opKernel_coordOp_eq_fixedPoints (T : SpectralToolkit F)
    (hc : F.IsConcentratedOn nonnegReals) :
    opKernel (F.coordinateOp 0) = {ψ | ∀ t, F.contractionFlow t ψ = ψ} := by
  rw [opKernel_coordOp_eq_range T]
  refine Set.ext fun ψ => ⟨?_, fun h => ?_⟩
  · rintro ⟨φ, rfl⟩ t
    exact DFunLike.congr_fun (heatSemigroupOp_mul_proj_zeroPoint T t) φ
  · refine ⟨ψ, ?_⟩
    have h₁ := heatSemigroupOp_tendstoStrongly T hc ψ
    have h₂ : Tendsto (fun t => F.contractionFlow t ψ) atTop (𝓝 ψ) :=
      tendsto_const_nhds.congr fun t => (h t).symm
    exact tendsto_nhds_unique h₁ h₂
theorem heatSemigroupProps_of_toolkit (T : SpectralToolkit F)
    (hc : F.IsConcentratedOn nonnegReals) : F.ContractionFlowFacts where
  expNegMulOp_eq := heatSemigroup_eq_ofBounded T
  flow_selfAdjoint := heatSemigroupOp_isSelfAdjoint T
  flow_nonneg := heatSemigroupOp_nonneg T
  flow_le_one := heatSemigroupOp_le_one T
  flow_zero := heatSemigroupOp_zero T hc
  flow_add := heatSemigroupOp_mul T
  mem_domain_iff_bdd := mem_coordOp_dom_iff_heat T hc
  tendsto_derivQuot := heatSemigroupOp_tendsto_generator T hc
  inner_generator_nonneg := inner_coordOp_nonneg_of_concentrated T hc
  kernel_eq_range_atom := opKernel_coordOp_eq_range T
  kernel_eq_fixedPoints := opKernel_coordOp_eq_fixedPoints T hc
  tendsto_atom := heatSemigroupOp_tendstoStrongly T hc
theorem unitaryGroupProps_of_toolkit (T : SpectralToolkit F) : F.UnitaryFlowFacts where
  expIMulOp_eq := unitaryGroup_eq_ofBounded T
  flow_zero := unitaryGroupOp_zero T
  flow_add := unitaryGroupOp_mul T
  star_flow := unitaryGroupOp_star T
  flow_isometry := unitaryGroupOp_isUnitary T
  flow_continuous := unitaryGroupOp_stronglyContinuous T
  mem_domain_iff_bdd := mem_coordOp_dom_iff_unitary T
  tendsto_derivQuot := unitaryGroupOp_tendsto_generator T
  flow_preserves_domain := unitaryGroupOp_preserves_dom T
  concentrated_nonneg_iff := isConcentratedOn_nonnegReals_iff T
end Semigroup
section Determination
set_option linter.unusedSectionVars false
variable {ℋ : Type} [NormedAddCommGroup ℋ] [InnerProductSpace ℂ ℋ] [CompleteSpace ℋ]
  {F F' : ProjectionMeasure 1 ℋ}
theorem eq_of_unitaryGroup_eq (T : SpectralToolkit F) (h : ∀ u, F'.expIMulOp u = F.expIMulOp u) :
    F' = F := by
  refine T.laws.ext_of_fourier_or_boxes F' (Or.inl fun x => ?_)
  have hf : (fun ξ : Fin 1 → ℝ => Complex.exp (Complex.I * ((∑ i, x i * ξ i : ℝ) : ℂ))) =
      fun ξ => Complex.exp (Complex.I * (x 0 : ℂ) * ξ 0) := by
    funext ξ
    simp only [Fin.sum_univ_one]
    push_cast
    rw [mul_assoc]
  rw [hf]
  exact h (x 0)
theorem unitaryGroupOp_add_apply (T : SpectralToolkit F) (a b : ℝ) (v : ℋ) :
    F.unitaryFlow (a + b) v = F.unitaryFlow a (F.unitaryFlow b v) := by
  rw [← unitaryGroupOp_mul T]
  rfl
theorem unitaryGroupOp_slope (T : SpectralToolkit F) {A : UnboundedOperator ℋ}
    (hA : A = F.coordinateOp 0) (χ : A.domain) :
    Tendsto (fun t : ℝ => ((t : ℂ))⁻¹ • (F.unitaryFlow t χ - χ)) (𝓝[≠] 0)
      (𝓝 (Complex.I • A χ)) := by
  subst hA
  refine ((unitaryGroupOp_tendsto_generator T χ).const_smul Complex.I).congr fun t => ?_
  rw [smul_smul, mul_inv, ← mul_assoc, mul_inv_cancel₀ Complex.I_ne_zero, one_mul]
theorem unitaryGroupOp_tendsto_of_tendsto (T : SpectralToolkit F) {ι : Type*} {l : Filter ι}
    {a : ι → ℝ} {a₀ : ℝ} {ξ : ι → ℋ} {ξ₀ : ℋ} (ha : Tendsto a l (𝓝 a₀))
    (hξ : Tendsto ξ l (𝓝 ξ₀)) :
    Tendsto (fun s => F.unitaryFlow (a s) (ξ s)) l (𝓝 (F.unitaryFlow a₀ ξ₀)) := by
  have h₁ : Tendsto (fun s => F.unitaryFlow (a s) ξ₀) l (𝓝 (F.unitaryFlow a₀ ξ₀)) :=
    ((unitaryGroupOp_stronglyContinuous T ξ₀).tendsto a₀).comp ha
  have h₂ : Tendsto (fun s => F.unitaryFlow (a s) (ξ s - ξ₀)) l (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    simp only [norm_unitaryGroupOp_apply T]
    exact tendsto_iff_norm_sub_tendsto_zero.1 hξ
  have h₃ := h₂.add h₁
  rw [zero_add] at h₃
  refine h₃.congr fun s => ?_
  rw [← map_add, sub_add_cancel]
theorem hasDerivAt_conj_unitaryGroupOp (T : SpectralToolkit F) (T' : SpectralToolkit F')
    (hA : F.coordinateOp 0 = F'.coordinateOp 0)
    (ψ : (F.coordinateOp 0).domain) (u : ℝ) :
    HasDerivAt (fun v : ℝ => F'.unitaryFlow (-v) (F.unitaryFlow v ψ)) 0 u := by
  obtain ⟨hχ, -⟩ := unitaryGroupOp_preserves_dom T u ψ
  set χ : (F.coordinateOp 0).domain := ⟨F.unitaryFlow u ψ, hχ⟩ with hχdef
  have hχv : (χ : ℋ) = F.unitaryFlow u ψ := rfl
  have e : ∀ t : ℝ, t⁻¹ • (F'.unitaryFlow (-(u + t)) (F.unitaryFlow (u + t) ψ) -
      F'.unitaryFlow (-u) (F.unitaryFlow u ψ)) =
      F'.unitaryFlow (-(u + t)) (((t : ℂ))⁻¹ • (F.unitaryFlow t χ - χ)) +
        F'.unitaryFlow (-u) (((t : ℂ))⁻¹ • (F'.unitaryFlow (-t) χ - χ)) := fun t => by
    rw [← Complex.coe_smul, Complex.ofReal_inv, map_smul, map_smul, ← smul_add]
    congr 1
    rw [map_sub, map_sub, ← unitaryGroupOp_add_apply T' (-u) (-t), hχv,
      ← unitaryGroupOp_add_apply T t u, add_comm t u, neg_add]
    abel
  have h₁ := unitaryGroupOp_slope T rfl χ
  have h₂ : Tendsto (fun t : ℝ => ((t : ℂ))⁻¹ • (F'.unitaryFlow (-t) χ - χ)) (𝓝[≠] 0)
      (𝓝 (-(Complex.I • F.coordinateOp 0 χ))) := by
    have hneg : Tendsto (fun t : ℝ => -t) (𝓝[≠] 0) (𝓝[≠] 0) := by
      refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
      · have h₃ : Tendsto (fun t : ℝ => -t) (𝓝 0) (𝓝 (-0)) := continuous_neg.tendsto 0
        rw [neg_zero] at h₃
        exact h₃.mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with t ht
        exact neg_ne_zero.2 ht
    have h₃ := (unitaryGroupOp_slope T' hA χ).comp hneg
    refine h₃.neg.congr fun t => ?_
    simp only [Function.comp_apply, Complex.ofReal_neg, inv_neg, neg_smul, neg_neg]
  have hlim₀ : Tendsto (fun t : ℝ => -(u + t)) (𝓝[≠] 0) (𝓝 (-u)) := by
    have h₃ : Tendsto (fun t : ℝ => -(u + t)) (𝓝 0) (𝓝 (-(u + 0))) :=
      (by fun_prop : Continuous fun t : ℝ => -(u + t)).tendsto 0
    rw [add_zero] at h₃
    exact h₃.mono_left nhdsWithin_le_nhds
  have h₃ := unitaryGroupOp_tendsto_of_tendsto T' hlim₀ h₁
  have h₄ := ((F'.unitaryFlow (-u)).continuous.tendsto _).comp h₂
  have h₅ := h₃.add h₄
  rw [map_neg, add_neg_cancel] at h₅
  refine hasDerivAt_iff_tendsto_slope_zero.2 (h₅.congr fun t => ?_)
  exact (e t).symm
theorem unitaryGroupOp_eq_of_coordOp_eq (T : SpectralToolkit F) (T' : SpectralToolkit F')
    (hA : F.coordinateOp 0 = F'.coordinateOp 0) (u : ℝ) :
    F'.unitaryFlow u = F.unitaryFlow u := by
  have hdom : ∀ ψ : (F.coordinateOp 0).domain,
      F.unitaryFlow u ψ = F'.unitaryFlow u ψ := fun ψ => by
    have hd := fun v => hasDerivAt_conj_unitaryGroupOp T T' hA ψ v
    have hc := is_const_of_deriv_eq_zero (𝕜 := ℝ)
      (f := fun v : ℝ => F'.unitaryFlow (-v) (F.unitaryFlow v ψ))
      (fun v => (hd v).differentiableAt) (fun v => (hd v).deriv) u 0
    simp only [neg_zero, unitaryGroupOp_zero T, unitaryGroupOp_zero T'] at hc
    have h₂ := congrArg (F'.unitaryFlow u) hc
    rw [← unitaryGroupOp_add_apply T', add_neg_cancel, unitaryGroupOp_zero T'] at h₂
    simpa using h₂
  have hdense : Dense ((F.coordinateOp 0).domain : Set ℋ) := by
    have h₁ := (T.laws.isOperator (coordFun 0) (measurable_coordFun 0)).1
    have h₂ := (T.limitVectors (coordFun 0) (measurable_coordFun 0)).dense
    rw [← h₁] at h₂
    exact h₂
  have h₃ := Continuous.ext_on hdense (F'.unitaryFlow u).continuous (F.unitaryFlow u).continuous
    (fun ψ hψ => (hdom ⟨ψ, hψ⟩).symm)
  exact DFunLike.coe_injective h₃
theorem eq_of_coordOp_eq (T : SpectralToolkit F) (T' : SpectralToolkit F')
    (hA : F'.coordinateOp 0 = F.coordinateOp 0) : F' = F := by
  refine eq_of_unitaryGroup_eq T fun u => ?_
  rw [unitaryGroup_eq_ofBounded T, unitaryGroup_eq_ofBounded T',
    unitaryGroupOp_eq_of_coordOp_eq T T' hA.symm]
theorem eq_of_heatSemigroup_eq (T : SpectralToolkit F) (T' : SpectralToolkit F')
    (hc : F.IsConcentratedOn nonnegReals) (hc' : F'.IsConcentratedOn nonnegReals)
    (h : ∀ t : ℝ≥0, 0 < t → t ≤ 1 → F'.expNegMulOp t = F.expNegMulOp t) : F' = F := by
  have hS : ∀ t : ℝ≥0, 0 < t → t ≤ 1 → F'.contractionFlow t = F.contractionFlow t :=
    fun t h₀ h₁ => congrArg toBounded (h t h₀ h₁)
  refine eq_of_coordOp_eq T T' ((unboundedOperator_eq_iff _ _).2 ⟨?_, fun x y hxy => ?_⟩)
  · ext ψ
    rw [mem_coordOp_dom_iff_heat T' hc', mem_coordOp_dom_iff_heat T hc]
    have hs : (fun t : ℝ≥0 => (t : ℝ)⁻¹ * ‖ψ - F'.contractionFlow t ψ‖) ''
        {t | 0 < t ∧ t ≤ 1} =
        (fun t : ℝ≥0 => (t : ℝ)⁻¹ * ‖ψ - F.contractionFlow t ψ‖) '' {t | 0 < t ∧ t ≤ 1} :=
      Set.image_congr fun t ht => by
        rw [hS t ht.1 ht.2]
    rw [hs]
  · have h₁ := heatSemigroupOp_tendsto_generator T' hc' x
    have h₂ := heatSemigroupOp_tendsto_generator T hc y
    refine tendsto_nhds_unique_of_eventuallyEq h₁ h₂ ?_
    filter_upwards [Ioc_mem_nhdsGT (zero_lt_one' ℝ≥0)] with t ht
    rw [hS t ht.1 ht.2, hxy]
theorem uniquenessProps_of_toolkit (T : SpectralToolkit F)
    (hT : ∀ F' : ProjectionMeasure 1 ℋ, SpectralToolkit F') : F.DeterminedBy where
  eq_of_expIMulOp _ h := eq_of_unitaryGroup_eq T h
  eq_of_generator F' h := eq_of_coordOp_eq T (hT F') h
  eq_of_expNegMulOp F' hc hc' h := eq_of_heatSemigroup_eq T (hT F') hc hc' h
end Determination
section Commutation
set_option linter.unusedSectionVars false
variable {ℋ : Type} [NormedAddCommGroup ℋ] [InnerProductSpace ℂ ℋ] [CompleteSpace ℋ]
  {F : ProjectionMeasure 1 ℋ}
theorem commute_apply_apply {B W : ℋ →L[ℂ] ℋ} (h : Commute B W) (v : ℋ) :
    B (W v) = W (B v) :=
  DFunLike.congr_fun h.eq v
theorem coordOp_commutes_of_unitaryGroupOp (T : SpectralToolkit F) {B : ℋ →L[ℂ] ℋ}
    (hB : ∀ u, Commute B (F.unitaryFlow u)) (ψ : (F.coordinateOp 0).domain) :
    ∃ h : B ψ ∈ (F.coordinateOp 0).domain,
      F.coordinateOp 0 ⟨B ψ, h⟩ = B (F.coordinateOp 0 ψ) := by
  have h₁ : ∀ u : ℝ, (Complex.I * (u : ℂ))⁻¹ • (F.unitaryFlow u (B ψ) - B ψ) =
      B ((Complex.I * (u : ℂ))⁻¹ • (F.unitaryFlow u ψ - ψ)) := fun u => by
    rw [map_smul, map_sub, commute_apply_apply (hB u)]
  obtain ⟨c, hc⟩ := (mem_coordOp_dom_iff_unitary T ψ).1 ψ.2
  have hdom : B ψ ∈ (F.coordinateOp 0).domain := by
    refine (mem_coordOp_dom_iff_unitary T _).2 ⟨‖B‖ * c, ?_⟩
    rintro _ ⟨u, hu, rfl⟩
    simp only
    rw [← norm_unitaryGroupOp_diffQuot, h₁]
    refine (B.le_opNorm _).trans (mul_le_mul_of_nonneg_left ?_ (norm_nonneg _))
    rw [norm_unitaryGroupOp_diffQuot]
    exact hc ⟨u, hu, rfl⟩
  refine ⟨hdom, ?_⟩
  have h₂ := unitaryGroupOp_tendsto_generator T ⟨B ψ, hdom⟩
  have h₃ := (B.continuous.tendsto _).comp (unitaryGroupOp_tendsto_generator T ψ)
  exact tendsto_nhds_unique h₂ (h₃.congr fun u => (h₁ u).symm)
theorem coordOp_commutes_of_heatSemigroupOp (T : SpectralToolkit F)
    (hcar : F.IsConcentratedOn nonnegReals) {B : ℋ →L[ℂ] ℋ}
    (hB : ∀ t : ℝ≥0, 0 < t → t ≤ 1 → Commute B (F.contractionFlow t))
    (ψ : (F.coordinateOp 0).domain) :
    ∃ h : B ψ ∈ (F.coordinateOp 0).domain,
      F.coordinateOp 0 ⟨B ψ, h⟩ = B (F.coordinateOp 0 ψ) := by
  have h₁ : ∀ t : ℝ≥0, 0 < t → t ≤ 1 → ((t : ℝ) : ℂ)⁻¹ • (B ψ - F.contractionFlow t (B ψ)) =
      B (((t : ℝ) : ℂ)⁻¹ • ((ψ : ℋ) - F.contractionFlow t ψ)) := fun t h₀ h₂ => by
    rw [map_smul, map_sub, commute_apply_apply (hB t h₀ h₂)]
  obtain ⟨c, hc⟩ := (mem_coordOp_dom_iff_heat T hcar ψ).1 ψ.2
  have hdom : B ψ ∈ (F.coordinateOp 0).domain := by
    refine (mem_coordOp_dom_iff_heat T hcar _).2 ⟨‖B‖ * c, ?_⟩
    rintro _ ⟨t, ht, rfl⟩
    simp only
    rw [← norm_heatSemigroupOp_diffQuot, h₁ t ht.1 ht.2]
    refine (B.le_opNorm _).trans (mul_le_mul_of_nonneg_left ?_ (norm_nonneg _))
    rw [norm_heatSemigroupOp_diffQuot]
    exact hc ⟨t, ht, rfl⟩
  refine ⟨hdom, ?_⟩
  have h₂ := heatSemigroupOp_tendsto_generator T hcar ⟨B ψ, hdom⟩
  have h₃ := (B.continuous.tendsto _).comp (heatSemigroupOp_tendsto_generator T hcar ψ)
  refine tendsto_nhds_unique_of_eventuallyEq h₂ h₃ ?_
  filter_upwards [Ioc_mem_nhdsGT (zero_lt_one' ℝ≥0)] with t ht
  exact h₁ t ht.1 ht.2
theorem coordOp_commutes_of_commutesWithFlow (T : SpectralToolkit F) {B : ℋ →L[ℂ] ℋ}
    (hB : F.CommutesWithFlows B) (ψ : (F.coordinateOp 0).domain) :
    ∃ h : B ψ ∈ (F.coordinateOp 0).domain,
      F.coordinateOp 0 ⟨B ψ, h⟩ = B (F.coordinateOp 0 ψ) := by
  rcases hB with hB | ⟨hc, hB⟩
  · exact coordOp_commutes_of_unitaryGroupOp T hB ψ
  · exact coordOp_commutes_of_heatSemigroupOp T hc hB ψ
theorem commute_symm_of_linearIsometryEquiv {B W : ℋ →L[ℂ] ℋ} {V : ℋ ≃ₗᵢ[ℂ] ℋ}
    (hV : ∀ ψ, B ψ = V ψ) (h : Commute B W) :
    Commute (V.symm.toContinuousLinearEquiv : ℋ →L[ℂ] ℋ) W := by
  refine ContinuousLinearMap.ext fun v => ?_
  apply V.injective
  change V (V.symm (W v)) = V (W (V.symm v))
  rw [← hV (W (V.symm v)), commute_apply_apply h, hV, V.apply_symm_apply, V.apply_symm_apply]
theorem commutantProps_of_toolkit (T : SpectralToolkit F) : F.GeneratorCommutant := by
  intro B hB
  refine ⟨coordOp_commutes_of_commutesWithFlow T hB, fun V hV => ?_⟩
  have hB' : F.CommutesWithFlows (V.symm.toContinuousLinearEquiv : ℋ →L[ℂ] ℋ) := by
    rcases hB with hB | ⟨hc, hB⟩
    · exact Or.inl fun u => commute_symm_of_linearIsometryEquiv hV (hB u)
    · exact Or.inr ⟨hc, fun t h₀ h₁ => commute_symm_of_linearIsometryEquiv hV (hB t h₀ h₁)⟩
  refine (unboundedOperator_eq_iff _ _).2 ⟨?_, fun x y hxy => ?_⟩
  · ext x
    constructor
    · rintro ⟨ψ, hψ, rfl⟩
      have h₁ := (coordOp_commutes_of_commutesWithFlow T hB ⟨ψ, hψ⟩).1
      simp only [hV] at h₁
      exact h₁
    · intro hx
      exact ⟨V.symm x, (coordOp_commutes_of_commutesWithFlow T hB' ⟨x, hx⟩).1,
        V.apply_symm_apply x⟩
  · have hψ : V.symm y ∈ (F.coordinateOp 0).domain :=
      (coordOp_commutes_of_commutesWithFlow T hB' y).1
    have hVψ : V (V.symm y) = y := V.apply_symm_apply _
    have hx : V (⟨V.symm y, hψ⟩ : (F.coordinateOp 0).domain) ∈
        (unitaryConj V (F.coordinateOp 0)).domain := by
      have h₁ : (x : ℋ) = V (V.symm y) := by rw [hVψ, hxy]
      have h₂ := x.2
      rw [h₁] at h₂
      exact h₂
    have hxe : x = ⟨V (⟨V.symm y, hψ⟩ : (F.coordinateOp 0).domain), hx⟩ :=
      Subtype.ext (by simp [hxy])
    rw [hxe, unitaryConj_apply]
    obtain ⟨h₁, h₂⟩ := coordOp_commutes_of_commutesWithFlow T hB ⟨V.symm y, hψ⟩
    have hye : (⟨_, h₁⟩ : (F.coordinateOp 0).domain) = y := Subtype.ext (by simp [hV])
    rw [hye] at h₂
    rw [h₂, hV]
end Commutation
section Coordinates
set_option linter.unusedSectionVars false
variable {ℋ : Type} [NormedAddCommGroup ℋ] [InnerProductSpace ℂ ℋ] [CompleteSpace ℋ]
  {n : ℕ} [NeZero n] {E : ProjectionMeasure n ℋ}
theorem commute_proj (E : ProjectionMeasure n ℋ) (A B : BorelSets n) :
    Commute (E A) (E B) := by
  change E A * E B = E B * E A
  rw [← E.map_inter, ← E.map_inter]
  exact congrArg E (Subtype.ext (inter_comm _ _))
theorem coordOp_pushforward_coordProj (T : SpectralToolkit E) (r : Fin n) :
    (E.imageMeasure (coordProj r) (measurable_coordProj r)).coordinateOp 0 =
      E.coordinateOp r :=
  T.laws.calculus_imageMeasure 1 _ _ (coordFun 0) (measurable_coordFun 0)
def boxCylinder (Δ : Fin n → Set ℝ) (hΔ : ∀ r, MeasurableSet (Δ r)) (s : Finset (Fin n)) :
    BorelSets n :=
  ⟨{x | ∀ r ∈ s, x r ∈ Δ r}, by
    have h : {x : Fin n → ℝ | ∀ r ∈ s, x r ∈ Δ r} = ⋂ r ∈ s, (fun x => x r) ⁻¹' Δ r := by
      ext x
      simp
    rw [h]
    exact Finset.measurableSet_biInter _ fun r _ => measurable_pi_apply r (hΔ r)⟩
theorem coordMapProps_of_toolkit
    (hT : ∀ (m : ℕ) [NeZero m] (G : ProjectionMeasure m ℋ), SpectralToolkit G)
    (E : ProjectionMeasure n ℋ) : E.MarginalFacts := by
  have T := hT n E
  refine ⟨fun r => ?_, fun r s Δ Δ' => commute_proj E _ _, fun E' hE' => ?_⟩
  · exact ⟨E.imageMeasure _ (measurable_coordProj r),
      fun Δ => T.laws.imageMeasure_apply 1 _ _ Δ, (coordOp_pushforward_coordProj T r).symm⟩
  · have T' := hT n E'
    have himage : ∀ r : Fin n,
        E'.imageMeasure (coordProj r) (measurable_coordProj r) =
          E.imageMeasure (coordProj r) (measurable_coordProj r) := fun r =>
      eq_of_coordOp_eq (hT 1 _) (hT 1 _)
        ((coordOp_pushforward_coordProj T' r).trans
          ((hE' r).trans (coordOp_pushforward_coordProj T r).symm))
    refine T.laws.ext_of_fourier_or_boxes E' (Or.inr fun Δ hΔ => ?_)
    have key : ∀ s : Finset (Fin n), E' (boxCylinder Δ hΔ s) = E (boxCylinder Δ hΔ s) := by
      intro s
      induction s using Finset.induction_on with
      | empty =>
        have hs : boxCylinder Δ hΔ ∅ = ⟨univ, MeasurableSet.univ⟩ :=
          Subtype.ext (by simp [boxCylinder])
        rw [hs, E'.map_univ, E.map_univ]
      | insert a s _ ih =>
        let D : BorelSets 1 := ⟨{y | y 0 ∈ Δ a}, measurable_pi_apply 0 (hΔ a)⟩
        have hpre : ∀ G : ProjectionMeasure n ℋ,
            G.pushforward (coordProj a) (measurable_coordProj a) D =
              G ⟨{x | x a ∈ Δ a}, measurable_pi_apply a (hΔ a)⟩ := fun G => rfl
        have hv : E' ⟨{x | x a ∈ Δ a}, measurable_pi_apply a (hΔ a)⟩ =
            E ⟨{x | x a ∈ Δ a}, measurable_pi_apply a (hΔ a)⟩ := by
          rw [← hpre, ← hpre, ← T'.laws.imageMeasure_apply 1 _ _ D,
            ← T.laws.imageMeasure_apply 1 _ _ D, himage a]
        have hs : boxCylinder Δ hΔ (insert a s) =
            ⟨{x | x a ∈ Δ a} ∩ (boxCylinder Δ hΔ s).1,
              (measurable_pi_apply a (hΔ a)).inter (boxCylinder Δ hΔ s).2⟩ :=
          Subtype.ext (by
            ext x
            simp [boxCylinder])
        rw [hs, E'.map_inter ⟨{x | x a ∈ Δ a}, measurable_pi_apply a (hΔ a)⟩ (boxCylinder Δ hΔ s),
          E.map_inter ⟨{x | x a ∈ Δ a}, measurable_pi_apply a (hΔ a)⟩ (boxCylinder Δ hΔ s),
          hv, ih]
    have hs : (⟨Set.pi univ Δ, MeasurableSet.univ_pi hΔ⟩ : BorelSets n) =
        boxCylinder Δ hΔ Finset.univ :=
      Subtype.ext (by
        ext x
        simp [boxCylinder, Set.mem_pi])
    rw [hs]
    exact key _
end Coordinates
theorem generatorFlowTheorem_holds
    (hRules : YangMills.Construction.SpectralTheory.SpectralIntegralLawsHold)
    (hSupport : YangMills.Construction.SpectralSupport.ConcentratedOnSupportTheorem)
    (hConstruction :
      YangMills.Construction.SpectralTheory.IntegralConstruction.IntegralConstructionHolds) :
    GeneratorFlowTheorem := by
  intro ℋ _ _ _
  have hT : ∀ (m : ℕ) [NeZero m] (G : ProjectionMeasure m ℋ), SpectralToolkit G :=
    fun m _ G => ⟨hRules m ℋ G, hSupport m ℋ G, (hConstruction m ℋ G).2.1,
      (hConstruction m ℋ G).2.2⟩
  refine ⟨fun F => ⟨unitaryGroupProps_of_toolkit (hT 1 F), heatSemigroupProps_of_toolkit (hT 1 F),
    uniquenessProps_of_toolkit (hT 1 F) (hT 1), commutantProps_of_toolkit (hT 1 F)⟩,
    fun n _ E => coordMapProps_of_toolkit hT E⟩
end YangMills.Construction.GeneratorsAndFlows
