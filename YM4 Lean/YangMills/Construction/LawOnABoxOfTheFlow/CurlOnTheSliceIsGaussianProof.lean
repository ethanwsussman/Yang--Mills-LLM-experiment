import YangMills.Construction.ColdStepAtMirrorFrames.ExpansionUnderAGaugeOfTheTopProof
import YangMills.Construction.FormsOnATorus.KernelOfTheCurlOnABoxProof
import YangMills.Construction.LawOnABoxOfTheFlow.CurlOnTheSliceIsGaussian
import Mathlib
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
noncomputable section
open MeasureTheory ProbabilityTheory Complex
open scoped ENNReal Real Quaternion
namespace YangMills.Construction.BoxGaussian
open TorusFields ResponseInTheExpansion ColdStepAtMirrorFrames
open BlockAverages hiding unitStep adjointAction
namespace SliceCurlGaussian
private theorem map_inner_gaussianDensity {m : ℕ} (x c₀ : ℝ) (hx : 0 < x) (g : EuclideanSpace ℝ (Fin m)) :
    (normalize ((volume : Measure (EuclideanSpace ℝ (Fin m))).withDensity fun s =>
        ENNReal.ofReal (Real.exp (-(x / 2) * (c₀ + ‖s‖ ^ 2))))).map (fun s => inner ℝ g s) =
      gaussianReal 0 (x⁻¹ * ‖g‖ ^ 2).toNNReal := by
  set b : ℝ := x / 2 with hbdef
  have hb : 0 < b := by positivity
  have hbc : 0 < ((b : ℂ)).re := by simpa using hb
  set f : EuclideanSpace ℝ (Fin m) → ℝ := fun s => Real.exp (-b * (c₀ + ‖s‖ ^ 2)) with hf
  have hfc : Continuous f := by fun_prop
  have hfm : Measurable fun s => ENNReal.ofReal (f s) := hfc.measurable.ennreal_ofReal
  have key : ∀ t : ℝ, ∫ s, (f s : ℂ) * cexp (t * (inner ℝ g s : ℝ) * I) =
      (Real.exp (-b * c₀) : ℂ) * (((π : ℂ) / (b : ℂ)) ^ ((Module.finrank ℝ (EuclideanSpace ℝ (Fin m)) : ℂ) / 2) *
        cexp (((t : ℂ) * I) ^ 2 * (‖g‖ : ℂ) ^ 2 / (4 * (b : ℂ)))) := by
    intro t
    rw [← GaussianFourier.integral_cexp_neg_mul_sq_norm_add hbc ((t : ℂ) * I) g, ← integral_const_mul]
    congr 1
    funext s
    simp only [hf]
    rw [Complex.ofReal_exp, Complex.ofReal_exp, ← Complex.exp_add, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  have hint : Integrable f := by
    have h1 := GaussianFourier.integrable_cexp_neg_mul_sq_norm_add hbc (0 : ℂ) g
    have h2 : Integrable fun s : EuclideanSpace ℝ (Fin m) => Real.exp (-b * ‖s‖ ^ 2) := by
      have := h1.re
      refine this.congr (Filter.Eventually.of_forall fun s => ?_)
      simp only [zero_mul, add_zero, RCLike.re_to_complex]
      have : -(b : ℂ) * (‖s‖ : ℂ) ^ 2 = ((-b * ‖s‖ ^ 2 : ℝ) : ℂ) := by push_cast; ring
      rw [this, ← Complex.ofReal_exp, Complex.ofReal_re]
    refine (h2.const_mul (Real.exp (-b * c₀))).congr (Filter.Eventually.of_forall fun s => ?_)
    simp only [hf]
    rw [← Real.exp_add]
    congr 1
    ring
  set Zr : ℝ := ∫ s, f s with hZ
  have hZpos : 0 < Zr := integral_exp_pos hint
  have hZc : (Zr : ℂ) = (Real.exp (-b * c₀) : ℂ) *
      ((π : ℂ) / (b : ℂ)) ^ ((Module.finrank ℝ (EuclideanSpace ℝ (Fin m)) : ℂ) / 2) := by
    have h0 := key 0
    simp only [Complex.ofReal_zero, zero_mul, Complex.exp_zero, mul_one, ne_eq, OfNat.ofNat_ne_zero,
      not_false_eq_true, zero_pow, zero_div] at h0
    rw [← h0, hZ]
    exact (integral_ofReal).symm
  set μ : Measure (EuclideanSpace ℝ (Fin m)) := volume.withDensity fun s => ENNReal.ofReal (f s) with hμ
  have hmass : μ Set.univ = ENNReal.ofReal Zr := by
    rw [hμ, withDensity_apply _ MeasurableSet.univ, setLIntegral_univ, hZ,
      ofReal_integral_eq_lintegral_ofReal hint (Filter.Eventually.of_forall fun s => (Real.exp_pos _).le)]
  have hZ0 : ENNReal.ofReal Zr ≠ 0 := by simpa using hZpos
  have hZt : ENNReal.ofReal Zr ≠ ⊤ := ENNReal.ofReal_ne_top
  set ν : Measure (EuclideanSpace ℝ (Fin m)) := normalize μ with hν
  have hνp : IsProbabilityMeasure ν := by
    constructor
    rw [hν, normalize, Measure.smul_apply, smul_eq_mul, hmass]
    exact ENNReal.inv_mul_cancel hZ0 hZt
  have hℓ : Continuous fun s : EuclideanSpace ℝ (Fin m) => (inner ℝ g s : ℝ) := by fun_prop
  have : IsProbabilityMeasure (ν.map fun s => (inner ℝ g s : ℝ)) :=
    Measure.isProbabilityMeasure_map hℓ.aemeasurable
  refine Measure.ext_of_charFun (funext fun t => ?_)
  rw [charFun_apply_real, integral_map hℓ.aemeasurable (by fun_prop), charFun_gaussianReal, hν, normalize,
    integral_smul_measure, hmass, hμ,
    integral_withDensity_eq_integral_toReal_smul₀ hfm.aemeasurable
      (Filter.Eventually.of_forall fun s => ENNReal.ofReal_lt_top)]
  have h3 : ∀ s, (ENNReal.ofReal (f s)).toReal • cexp (t * (inner ℝ g s : ℝ) * I) =
      (f s : ℂ) * cexp (t * (inner ℝ g s : ℝ) * I) := by
    intro s
    rw [ENNReal.toReal_ofReal (Real.exp_pos _).le, Complex.real_smul]
  simp_rw [h3]
  rw [key t, ENNReal.toReal_inv, ENNReal.toReal_ofReal hZpos.le, Complex.real_smul]
  have hZne : (Zr : ℂ) ≠ 0 := by exact_mod_cast hZpos.ne'
  have h4 : ((Zr⁻¹ : ℝ) : ℂ) * ((Real.exp (-b * c₀) : ℂ) *
      (((π : ℂ) / (b : ℂ)) ^ ((Module.finrank ℝ (EuclideanSpace ℝ (Fin m)) : ℂ) / 2) *
        cexp (((t : ℂ) * I) ^ 2 * (‖g‖ : ℂ) ^ 2 / (4 * (b : ℂ))))) =
      cexp (((t : ℂ) * I) ^ 2 * (‖g‖ : ℂ) ^ 2 / (4 * (b : ℂ))) := by
    rw [← mul_assoc (Real.exp (-b * c₀) : ℂ), ← hZc, Complex.ofReal_inv, ← mul_assoc,
      inv_mul_cancel₀ hZne, one_mul]
  rw [h4]
  congr 1
  have hv : (((x⁻¹ * ‖g‖ ^ 2).toNNReal : ℝ) : ℂ) = ((x⁻¹ * ‖g‖ ^ 2 : ℝ) : ℂ) := by
    rw [Real.coe_toNNReal _ (by positivity)]
  have hxc : (x : ℂ) ≠ 0 := by exact_mod_cast hx.ne'
  rw [show ((t : ℂ) * I) ^ 2 = -(t : ℂ) ^ 2 by rw [mul_pow, I_sq]; ring]
  simp only [hbdef]
  push_cast at hv ⊢
  rw [hv]
  field_simp
  ring
private theorem exists_isometry_of_posDef {E : Type*} [AddCommGroup E] [Module ℝ E] [FiniteDimensional ℝ E]
    (Q : LinearMap.BilinForm ℝ E) (hs : ∀ u v, Q u v = Q v u) (hp : ∀ z, z ≠ 0 → 0 < Q z z) :
    ∃ θ : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) ≃ₗ[ℝ] E, ∀ s t, Q (θ s) (θ t) = inner ℝ s t := by
  have hs' : LinearMap.IsSymm Q := ⟨fun a b => by simpa using hs a b⟩
  obtain ⟨v, hv⟩ := LinearMap.BilinForm.exists_orthogonal_basis hs'
  have hq : ∀ i, 0 < Q (v i) (v i) := fun i => hp _ (v.ne_zero i)
  let c : Fin (Module.finrank ℝ E) → ℝ := fun i => (Real.sqrt (Q (v i) (v i)))⁻¹
  have hc : ∀ i, IsUnit (c i) := fun i => by
    have : c i ≠ 0 := inv_ne_zero (Real.sqrt_pos.2 (hq i)).ne'
    exact this.isUnit
  let w : Module.Basis (Fin (Module.finrank ℝ E)) ℝ E := v.isUnitSMul hc
  have hw : ∀ i j, Q (w i) (w j) = if i = j then 1 else 0 := by
    intro i j
    simp only [w, Module.Basis.isUnitSMul_apply, map_smul, LinearMap.smul_apply, smul_eq_mul]
    by_cases hij : i = j
    · subst hij
      have h1 : Real.sqrt (Q (v i) (v i)) * Real.sqrt (Q (v i) (v i)) = Q (v i) (v i) :=
        Real.mul_self_sqrt (hq i).le
      have h2 : Real.sqrt (Q (v i) (v i)) ≠ 0 := (Real.sqrt_pos.2 (hq i)).ne'
      simp only [c, if_true]
      field_simp
      nlinarith [h1]
    · have : Q (v i) (v j) = 0 := hv hij
      simp [this, hij]
  refine ⟨(WithLp.linearEquiv 2 ℝ (Fin (Module.finrank ℝ E) → ℝ)).trans w.equivFun.symm, fun s t => ?_⟩
  simp only [LinearEquiv.trans_apply, Module.Basis.equivFun_symm_apply, WithLp.linearEquiv_apply]
  simp only [map_sum, LinearMap.sum_apply, map_smul, LinearMap.smul_apply, smul_eq_mul, hw]
  rw [PiLp.inner_apply]
  simp [mul_comm]
private theorem addHaar_eq_smul_map {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] {m : ℕ} (θ : EuclideanSpace ℝ (Fin m) ≃ₗ[ℝ] E)
    (μ : Measure E) [μ.IsAddHaarMeasure] :
    ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ⊤ ∧ ∀ z : E, μ = c • (volume : Measure (EuclideanSpace ℝ (Fin m))).map fun s => θ s + z := by
  let L := θ.toContinuousLinearEquiv
  have : ((volume : Measure (EuclideanSpace ℝ (Fin m))).map L).IsAddHaarMeasure := L.isAddHaarMeasure_map _
  set ν := (volume : Measure (EuclideanSpace ℝ (Fin m))).map L with hν
  have h1 : μ = Measure.addHaarScalarFactor μ ν • ν := Measure.isAddLeftInvariant_eq_smul μ ν
  have hpos : Measure.addHaarScalarFactor μ ν ≠ 0 :=
    (Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure μ ν).ne'
  refine ⟨(Measure.addHaarScalarFactor μ ν : ℝ≥0∞), by simpa using hpos, ENNReal.coe_ne_top, fun z => ?_⟩
  have h2 : μ.map (fun y => y + z) = μ := map_add_right_eq_self μ z
  have hLm : Measurable L := L.continuous.measurable
  have h3 : (volume : Measure (EuclideanSpace ℝ (Fin m))).map (fun s => θ s + z) = ν.map (fun y => y + z) := by
    rw [hν, Measure.map_map (measurable_add_const z) hLm]
    rfl
  rw [h3]
  conv_lhs => rw [← h2]
  conv_lhs => rw [h1]
  rw [Measure.map_smul]
  rfl
private theorem normalize_smul {X : Type} [MeasurableSpace X] (μ : Measure X) (c : ℝ≥0∞) (h0 : c ≠ 0)
    (ht : c ≠ ⊤) : normalize (c • μ) = normalize μ := by
  unfold normalize
  rw [Measure.smul_apply, smul_smul, smul_eq_mul, ENNReal.mul_inv (Or.inl h0) (Or.inl ht),
    mul_comm c⁻¹, mul_assoc, ENNReal.inv_mul_cancel h0 ht, mul_one]
private theorem normalize_map {X Y : Type} [MeasurableSpace X] [MeasurableSpace Y] (μ : Measure X)
    {Ψ : X → Y} (hΨ : Measurable Ψ) : normalize (μ.map Ψ) = (normalize μ).map Ψ := by
  unfold normalize
  rw [Measure.map_apply hΨ MeasurableSet.univ, Set.preimage_univ, Measure.map_smul]
private theorem map_withDensity_comp {X Y : Type} [MeasurableSpace X] [MeasurableSpace Y] (μ : Measure X)
    {Ψ : X → Y} (hΨ : Measurable Ψ) {f : Y → ℝ≥0∞} (hf : Measurable f) :
    (μ.map Ψ).withDensity f = (μ.withDensity (f ∘ Ψ)).map Ψ := by
  ext s hs
  rw [withDensity_apply f hs, Measure.map_apply hΨ hs, withDensity_apply _ (hΨ hs),
    setLIntegral_map hs hf hΨ]
  rfl
private theorem map_sliceGaussian {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    [MeasurableSpace V] [BorelSpace V] (𝒮 : Submodule ℝ V) (Q : V →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (hs : ∀ u v, Q u v = Q v u) (hp : ∀ ζ ∈ 𝒮, ζ ≠ 0 → 0 < Q ζ ζ) (x : ℝ) (hx : 0 < x) (A B h : V)
    (hB : ∀ η ∈ 𝒮, Q B η = 0) (hBA : B - A ∈ 𝒮) (hh : h ∈ 𝒮) (F : V → ℝ) (hF : Measurable F)
    (hFe : ∀ ζ ∈ 𝒮, F ζ = Q h (ζ - (B - A))) :
    (normalize (((Measure.addHaar : Measure 𝒮).map Subtype.val).withDensity fun ζ =>
        ENNReal.ofReal (Real.exp (-(x / 2) * Q (A + ζ) (A + ζ))))).map F =
      gaussianReal 0 (x⁻¹ * Q h h).toNNReal := by
  let Qs : LinearMap.BilinForm ℝ 𝒮 := Q.domRestrict₁₂ 𝒮 𝒮
  have hQs : ∀ a b : 𝒮, Qs a b = Q a b := fun _ _ => rfl
  obtain ⟨θ, hθ⟩ := exists_isometry_of_posDef Qs (fun a b => hs _ _) (fun z hz => hp _ z.2 (by simpa using hz))
  obtain ⟨c, c0, ct, hc⟩ := addHaar_eq_smul_map θ (Measure.addHaar : Measure 𝒮)
  let z : 𝒮 := ⟨B - A, hBA⟩
  let Ψ : EuclideanSpace ℝ (Fin (Module.finrank ℝ 𝒮)) → V := fun s => ((θ s + z : 𝒮) : V)
  have hθc : Continuous θ := θ.toLinearMap.continuous_of_finiteDimensional
  have hΨ : Measurable Ψ := by
    have : Continuous Ψ := continuous_subtype_val.comp (hθc.add continuous_const)
    exact this.measurable
  have hm1 : Measurable fun s : EuclideanSpace ℝ (Fin (Module.finrank ℝ 𝒮)) => θ s + z :=
    (hθc.add continuous_const).measurable
  have e1 : (Measure.addHaar : Measure 𝒮).map Subtype.val =
      c • (volume : Measure (EuclideanSpace ℝ (Fin (Module.finrank ℝ 𝒮)))).map Ψ := by
    conv_lhs => rw [hc z]
    rw [Measure.map_smul, Measure.map_map measurable_subtype_coe hm1]
    rfl
  let Qc : V →L[ℝ] V →L[ℝ] ℝ :=
    LinearMap.toContinuousLinearMap ((LinearMap.toContinuousLinearMap : (V →ₗ[ℝ] ℝ) ≃ₗ[ℝ] (V →L[ℝ] ℝ)).toLinearMap ∘ₗ Q)
  have hQc : ∀ u v, Qc u v = Q u v := fun _ _ => rfl
  have hcont : Continuous fun ζ : V => Q (A + ζ) (A + ζ) := by
    have : Continuous fun ζ : V => Qc (A + ζ) (A + ζ) := by fun_prop
    exact this
  have hfm : Measurable fun ζ : V => ENNReal.ofReal (Real.exp (-(x / 2) * Q (A + ζ) (A + ζ))) :=
    (Real.continuous_exp.comp (continuous_const.mul hcont)).measurable.ennreal_ofReal
  rw [e1, withDensity_smul_measure, normalize_smul _ c c0 ct, map_withDensity_comp _ hΨ hfm,
    normalize_map _ hΨ, Measure.map_map hF hΨ]
  have hΨv : ∀ s, Ψ s = (θ s : V) + (B - A) := fun s => rfl
  let g := θ.symm ⟨h, hh⟩
  have e3 : ((fun ζ : V => ENNReal.ofReal (Real.exp (-(x / 2) * Q (A + ζ) (A + ζ)))) ∘ Ψ) =
      fun s => ENNReal.ofReal (Real.exp (-(x / 2) * (Q B B + ‖s‖ ^ 2))) := by
    funext s
    simp only [Function.comp]
    have h1 : A + Ψ s = B + (θ s : V) := by rw [hΨv]; abel
    have h2 : Q (θ s : V) (θ s : V) = ‖s‖ ^ 2 := by
      rw [← hQs, hθ, real_inner_self_eq_norm_sq]
    have h3 : Q B (θ s : V) = 0 := hB _ (θ s).2
    rw [h1]
    simp only [map_add, LinearMap.add_apply]
    rw [h2, h3, hs (θ s : V) B, h3]
    congr 3
    ring
  have e4 : F ∘ Ψ = fun s => inner ℝ g s := by
    funext s
    have h1 : Ψ s - (B - A) = (θ s : V) := by rw [hΨv]; abel
    have h2 : (θ g : 𝒮) = ⟨h, hh⟩ := θ.apply_symm_apply _
    have h3 : Qs (θ g) (θ s) = Q h (θ s : V) := by rw [h2]; rfl
    have hmem : Ψ s ∈ 𝒮 := (θ s + z).2
    simp only [Function.comp]
    rw [hFe _ hmem, h1, ← h3, hθ]
  rw [e3, e4, map_inner_gaussianDensity x _ hx g]
  congr 3
  have h2 : (θ g : 𝒮) = ⟨h, hh⟩ := θ.apply_symm_apply _
  have h3 := hθ g g
  rw [h2, real_inner_self_eq_norm_sq] at h3
  rw [← h3]
  rfl
private theorem surjective_of_ker_trivial {E : Type*} [AddCommGroup E] [Module ℝ E] [FiniteDimensional ℝ E]
    (T : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (h : ∀ z, T z = 0 → z = 0) : Function.Surjective T := by
  have hf : Module.finrank ℝ E = Module.finrank ℝ (E →ₗ[ℝ] ℝ) := Subspace.dual_finrank_eq.symm
  have hinj : Function.Injective T := (injective_iff_map_eq_zero T).2 h
  exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hf).1 hinj
private theorem exists_representative {E : Type*} [AddCommGroup E] [Module ℝ E] [FiniteDimensional ℝ E]
    (Q : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (hp : ∀ z, z ≠ 0 → 0 < Q z z) (ℓ : E →ₗ[ℝ] ℝ) :
    ∃ h, ∀ η, Q h η = ℓ η := by
  obtain ⟨h, hh⟩ := surjective_of_ker_trivial Q (fun z hz => by
    by_contra h0
    have := hp z h0
    rw [hz] at this
    simp at this) ℓ
  exact ⟨h, fun η => by rw [hh]⟩
private theorem quadratic_sum_expand {α β : Type*} [Fintype β] (P : Finset α) (x : α → ℝ) (c : α → β → ℝ)
    (N : β → β → ℝ) :
    ∑ p ∈ P, ∑ p' ∈ P, x p * (∑ b, ∑ b', c p b * N b b' * c p' b') * x p' =
      ∑ b, (∑ p ∈ P, x p * c p b) * ∑ b', N b b' * ∑ p' ∈ P, x p' * c p' b' := by
  have h1 : ∀ b, (∑ p ∈ P, x p * c p b) * ∑ b', N b b' * ∑ p' ∈ P, x p' * c p' b' =
      ∑ p ∈ P, ∑ p' ∈ P, ∑ b', x p * (c p b * N b b' * c p' b') * x p' := by
    intro b
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [Finset.mul_sum]
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun p' _ => Finset.sum_congr rfl fun b' _ => ?_
    ring
  calc ∑ p ∈ P, ∑ p' ∈ P, x p * (∑ b, ∑ b', c p b * N b b' * c p' b') * x p'
      = ∑ p ∈ P, ∑ p' ∈ P, ∑ b, ∑ b', x p * (c p b * N b b' * c p' b') * x p' := by
        refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun p' _ => ?_
        rw [Finset.mul_sum, Finset.sum_mul]
        refine Finset.sum_congr rfl fun b _ => ?_
        rw [Finset.mul_sum, Finset.sum_mul]
    _ = ∑ b, ∑ p ∈ P, ∑ p' ∈ P, ∑ b', x p * (c p b * N b b' * c p' b') * x p' :=
        (Finset.sum_congr rfl fun p _ => Finset.sum_comm).trans Finset.sum_comm
    _ = _ := Finset.sum_congr rfl fun b _ => (h1 b).symm
variable {n : ℕ} [NeZero n]
private theorem imaginaryComponent_add (e : Fin 3) (a b : imaginaryQuaternions) :
    imaginaryComponent e (a + b) = imaginaryComponent e a + imaginaryComponent e b := by
  fin_cases e <;> simp [imaginaryComponent]
private theorem imaginaryComponent_sub (e : Fin 3) (a b : imaginaryQuaternions) :
    imaginaryComponent e (a - b) = imaginaryComponent e a - imaginaryComponent e b := by
  fin_cases e <;> simp [imaginaryComponent]
private theorem imaginaryComponent_smul (e : Fin 3) (c : ℝ) (a : imaginaryQuaternions) :
    imaginaryComponent e (c • a) = c * imaginaryComponent e a := by
  fin_cases e <;> simp [imaginaryComponent]
private theorem imaginaryComponent_zero (e : Fin 3) : imaginaryComponent e (0 : imaginaryQuaternions) = 0 := by
  fin_cases e <;> simp [imaginaryComponent]
private theorem imaginaryComponent_smul_unitI (e : Fin 3) (c : ℝ) :
    imaginaryComponent e (c • imaginaryUnitI) = if e = 0 then c else 0 := by
  fin_cases e <;> simp [imaginaryComponent, imaginaryUnitI] <;> first | exact mul_one c | exact mul_zero c
private theorem adjointAction_add (g : UnitQuaternion) (a b : imaginaryQuaternions) :
    adjointAction g (a + b) = adjointAction g a + adjointAction g b := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.GaugeCovariance.adjointAction_add <;> assumption
private theorem adjointAction_smul (g : UnitQuaternion) (c : ℝ) (a : imaginaryQuaternions) :
    adjointAction g (c • a) = c • adjointAction g a := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.GaugeCovariance.adjointAction_smul <;> assumption
private theorem lieFormCurl_add (u v : TorusBond n → imaginaryQuaternions) (p : TorusPlaquette n) :
    lieFormCurl (u + v) p = lieFormCurl u p + lieFormCurl v p := by
  simp only [lieFormCurl, Pi.add_apply]
  abel
private theorem lieFormCurl_smul (c : ℝ) (u : TorusBond n → imaginaryQuaternions) (p : TorusPlaquette n) :
    lieFormCurl (c • u) p = c • lieFormCurl u p := by
  simp only [lieFormCurl, Pi.smul_apply, smul_add, smul_sub]
private theorem lieFormCurl_sub (u v : TorusBond n → imaginaryQuaternions) (p : TorusPlaquette n) :
    lieFormCurl (u - v) p = lieFormCurl u p - lieFormCurl v p := by
  simp only [lieFormCurl, Pi.sub_apply]
  abel
private theorem lieFormCurl_latticeGrad (φ : TorusSite n → imaginaryQuaternions) (p : TorusPlaquette n) :
    lieFormCurl (latticeGrad φ) p = 0 := by
  have h : p.1 + unitStep n p.2.1 + unitStep n p.2.2 = p.1 + unitStep n p.2.2 + unitStep n p.2.1 := by abel
  simp only [lieFormCurl, latticeGrad, h]
  abel
private def boxSupported (o : TorusSite n) (R : ℕ) : Submodule ℝ (TorusSite n → imaginaryQuaternions) where
  carrier := {φ | ∀ z, z ∉ supBall o R → φ z = 0}
  add_mem' := by
    intro a b ha hb z hz
    simp [ha z hz, hb z hz]
  zero_mem' := fun _ _ => rfl
  smul_mem' := by
    intro c a ha z hz
    simp [ha z hz]
private def latticeGradLinear : (TorusSite n → imaginaryQuaternions) →ₗ[ℝ] (TorusBond n → imaginaryQuaternions) where
  toFun := latticeGrad
  map_add' a b := by
    funext x
    simp only [latticeGrad, Pi.add_apply]
    abel
  map_smul' c a := by
    funext x
    simp [latticeGrad, smul_sub]
private theorem covariantGrad_add (A : TorusBond n → imaginaryQuaternions) (χ χ' : TorusSite n → imaginaryQuaternions)
    (b : TorusBond n) :
    covariantGrad A (χ + χ') b = covariantGrad A χ b + covariantGrad A χ' b := by
  simp only [covariantGrad, Pi.add_apply, adjointAction_add]
  abel
private theorem covariantGrad_smul (A : TorusBond n → imaginaryQuaternions) (c : ℝ)
    (χ : TorusSite n → imaginaryQuaternions) (b : TorusBond n) :
    covariantGrad A (c • χ) b = c • covariantGrad A χ b := by
  simp only [covariantGrad, Pi.smul_apply, adjointAction_smul, smul_sub]
private def covariantPairing (A : TorusBond n → imaginaryQuaternions) (o : TorusSite n) (R : ℕ) :
    (TorusBond n → imaginaryQuaternions) →ₗ[ℝ] (boxSupported o R) →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ (fun ζ χ => ∑ b : TorusBond n, inner ℝ (ζ b) (covariantGrad A χ.1 b))
    (by
      intro a b c
      simp [inner_add_left, Finset.sum_add_distrib])
    (by
      intro c a b
      simp [inner_smul_left, Finset.mul_sum])
    (by
      intro a b c
      simp [covariantGrad_add, inner_add_right, Finset.sum_add_distrib])
    (by
      intro c a b
      simp [covariantGrad_smul, inner_smul_right, Finset.mul_sum])
private theorem latticeGrad_eq_zero_off {o : TorusSite n} {R : ℕ} {φ : TorusSite n → imaginaryQuaternions}
    (hφ : ∀ z, z ∉ supBall o R → φ z = 0)
    {b : TorusBond n} (hb : b ∉ bondsTouching o R) : latticeGrad φ b = 0 := by
  have h : b.1 ∉ supBall o R ∧ b.1 + unitStep n b.2 ∉ supBall o R := by
    simpa [bondsTouching, not_or] using hb
  simp [latticeGrad, hφ _ h.1, hφ _ h.2]
private theorem eq_zero_of_latticeGrad_eq_zero {o : TorusSite n} {R : ℕ} (hR : 1 ≤ R) (h16 : 16 * R < n)
    {φ : TorusSite n → imaginaryQuaternions}
    (hφ : ∀ z, z ∉ supBall o R → φ z = 0) (h0 : ∀ b, latticeGrad φ b = 0) : φ = 0 := by
  funext z
  have hstep : ∀ y : TorusSite n, φ y = φ (y + unitStep n 0) := fun y => sub_eq_zero.1 (h0 (y, 0))
  have hj : ∀ j : ℕ, φ z = φ (z + j • unitStep n 0) := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      rw [ih, hstep, succ_nsmul, add_assoc]
  set j : ℕ := (o 0 + ((R + 1 : ℕ) : ZMod n) - z 0).val with hjdef
  have hc : ((j : ℕ) : ZMod n) = o 0 + ((R + 1 : ℕ) : ZMod n) - z 0 := ZMod.natCast_zmod_val _
  have hy : z + j • unitStep n 0 ∉ supBall o R := by
    intro hm
    have h1 : (supDist (z + j • unitStep n 0) o : ℝ) ≤ R := (Finset.mem_filter.1 hm).2
    have h2 : supDist (z + j • unitStep n 0) o ≤ R := by exact_mod_cast h1
    have h3 : (((z + j • unitStep n 0) 0 - o 0).valMinAbs).natAbs ≤ supDist (z + j • unitStep n 0) o :=
      Finset.le_sup (f := fun i => (((z + j • unitStep n 0) i - o i).valMinAbs).natAbs) (Finset.mem_univ 0)
    have h4 : (z + j • unitStep n 0) 0 - o 0 = ((R + 1 : ℕ) : ZMod n) := by
      have h5 : (z + j • unitStep n 0) 0 = z 0 + (j : ZMod n) := by
        show z 0 + j • (unitStep n 0 0) = _
        rw [show unitStep n 0 0 = (1 : ZMod n) from Pi.single_eq_same _ _, nsmul_eq_mul, mul_one]
      rw [h5, hc]
      ring
    rw [h4, ZMod.valMinAbs_natCast_of_le_half (by omega)] at h3
    simp only [Int.natAbs_natCast] at h3
    omega
  rw [hj j, hφ _ hy]
  rfl
private theorem exists_slice_add_grad {o : TorusSite n} {R : ℕ} (hR : 1 ≤ R) (h16 : 16 * R < n)
    (A : TorusBond n → imaginaryQuaternions)
    (hz : ∀ ζ ∈ gaugeSlice o R A, ∀ φ, ζ = latticeGrad φ → ζ = 0) (η : TorusBond n → imaginaryQuaternions)
    (hη : ∀ b, b ∉ bondsTouching o R → η b = 0) :
    ∃ ζ ∈ gaugeSlice o R A, ∃ φ, η = ζ + latticeGrad φ := by
  let T : boxSupported o R →ₗ[ℝ] boxSupported o R →ₗ[ℝ] ℝ :=
    (covariantPairing A o R) ∘ₗ latticeGradLinear ∘ₗ (boxSupported o R).subtype
  have hinj : ∀ φ, T φ = 0 → φ = 0 := by
    intro φ hφ
    have hmem : latticeGrad φ.1 ∈ gaugeSlice o R A :=
      ⟨fun b hb => latticeGrad_eq_zero_off φ.2 hb, fun χ hχ => LinearMap.congr_fun hφ ⟨χ, hχ⟩⟩
    have h0 := hz _ hmem φ.1 rfl
    exact Subtype.ext (eq_zero_of_latticeGrad_eq_zero hR h16 φ.2 (fun b => congrFun h0 b))
  obtain ⟨φ, hφ⟩ := surjective_of_ker_trivial (E := boxSupported o R) T hinj (covariantPairing A o R η)
  refine ⟨η - latticeGrad φ.1, ⟨fun b hb => ?_, fun χ hχ => ?_⟩, φ.1, by simp⟩
  · simp [hη b hb, latticeGrad_eq_zero_off φ.2 hb]
  · have h1 := LinearMap.congr_fun hφ ⟨χ, hχ⟩
    have h2 : ∑ b : TorusBond n, inner ℝ (latticeGrad φ.1 b) (covariantGrad A χ b) =
        ∑ b : TorusBond n, inner ℝ (η b) (covariantGrad A χ b) := h1
    simp only [Pi.sub_apply, inner_sub_left, Finset.sum_sub_distrib, h2, sub_self]
private theorem sum_touchingBond {o : TorusSite n} {R : ℕ} (f : TorusBond n → ℝ)
    (hf : ∀ b, b ∉ bondsTouching o R → f b = 0) :
    ∑ b : TouchingBond o R, f b.1 = ∑ b, f b := by
  rw [Finset.sum_coe_sort (bondsTouching o R) f]
  exact Finset.sum_subset (Finset.subset_univ _) (fun b _ hb => hf b hb)
private theorem imaginaryComponent_lieFormCurl (e : Fin 3) (v : TorusBond n → imaginaryQuaternions)
    (p : TorusPlaquette n) :
    imaginaryComponent e (lieFormCurl v p) = ∑ b, curlCoeff p b * imaginaryComponent e (v b) := by
  classical
  simp only [curlCoeff, lieFormCurl, imaginaryComponent_add, imaginaryComponent_sub, add_mul, sub_mul, ite_mul,
    one_mul, zero_mul, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  simp
private theorem sum_gradCoeff_mul (ψ : TorusSite n → ℝ) (b : TorusBond n) :
    ∑ z, gradCoeff z b * ψ z = ψ b.1 - ψ (b.1 + unitStep n b.2) := by apply _root_.YangMills.SharedProofs.p55520 <;> assumption
private def ofComponents (f : Fin 3 → TorusBond n → ℝ) (b : TorusBond n) : imaginaryQuaternions :=
  ⟨⟨0, f 0 b, f 1 b, f 2 b⟩, rfl⟩
private theorem imaginaryComponent_ofComponents (e : Fin 3) (f : Fin 3 → TorusBond n → ℝ) (b : TorusBond n) :
    imaginaryComponent e (ofComponents f b) = f e b := by
  fin_cases e <;> rfl
private theorem exists_curl_potential {o : TorusSite n} {R : ℕ} (S : Finset (TorusSite n))
    (Q : (TorusBond n → imaginaryQuaternions) → (TorusBond n → imaginaryQuaternions) → ℝ)
    (M : TorusBond n → TorusBond n → ℝ) (G : Matrix (TouchingBond o R) (TouchingBond o R) ℝ)
    (hcol : ∀ u v : TorusBond n → imaginaryQuaternions, Q u v =
        ∑ e : Fin 3, ∑ b : TorusBond n, ∑ b' : TorusBond n,
          M b b' * imaginaryComponent e (u b) * imaginaryComponent e (v b'))
    (hblind : ∀ (φ : TorusSite n → imaginaryQuaternions) (v : TorusBond n → imaginaryQuaternions),
      Q (latticeGrad φ) v = 0)
    (hG : ∀ b b' : TouchingBond o R, G b b' = M b.1 b'.1 +
      ∑ z ∈ supBall o R, gradCoeff z b.1 * gradCoeff z b'.1)
    (hdet : IsUnit G.det) (u : TorusPlaquette n → Fin 3 → ℝ) :
    ∃ w : TorusBond n → imaginaryQuaternions, (∀ b, b ∉ bondsTouching o R → w b = 0) ∧
      (∀ η : TorusBond n → imaginaryQuaternions, (∀ b, b ∉ bondsTouching o R → η b = 0) →
        Q η w = colourPairing S u (lieFormCurl η)) ∧
      colourPairing S u (lieFormCurl w) = ∑ e : Fin 3, ∑ p ∈ plaquettesIn S, ∑ p' ∈ plaquettesIn S,
        u p e * (∑ b : TouchingBond o R, ∑ b' : TouchingBond o R,
          curlCoeff p b.1 * G⁻¹ b b' * curlCoeff p' b'.1) * u p' e := by
  classical
  let ℓ : Fin 3 → TouchingBond o R → ℝ := fun e b => ∑ p ∈ plaquettesIn S, u p e * curlCoeff p b.1
  let we : Fin 3 → TouchingBond o R → ℝ := fun e => G⁻¹.mulVec (ℓ e)
  have hGw : ∀ e, G.mulVec (we e) = ℓ e := fun e => by
    simp only [we]
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv G hdet, Matrix.one_mulVec]
  let Ws : Fin 3 → TorusBond n → ℝ := fun e b => if h : b ∈ bondsTouching o R then we e ⟨b, h⟩ else 0
  have hWoff : ∀ e b, b ∉ bondsTouching o R → Ws e b = 0 := fun e b hb => dif_neg hb
  have hWon : ∀ e (b : TouchingBond o R), Ws e b.1 = we e b := fun e b => by
    simp only [Ws]
    rw [dif_pos b.2]
  have hF1 : ∀ η : TorusBond n → imaginaryQuaternions, (∀ b, b ∉ bondsTouching o R → η b = 0) →
      colourPairing S u (lieFormCurl η) =
        ∑ e, ∑ b : TouchingBond o R, ℓ e b * imaginaryComponent e (η b.1) := by
    intro η hη
    unfold colourPairing
    refine Finset.sum_congr rfl fun e _ => ?_
    have h1 : ∀ p, imaginaryComponent e (lieFormCurl η p) =
        ∑ b : TouchingBond o R, curlCoeff p b.1 * imaginaryComponent e (η b.1) := fun p => by
      rw [imaginaryComponent_lieFormCurl, ← sum_touchingBond (o := o) (R := R) _
        (fun b hb => by rw [hη b hb, imaginaryComponent_zero, mul_zero])]
    simp only [h1, ℓ, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun p _ => ?_
    ring
  have hkey : ∀ e (b : TouchingBond o R), ∑ b' : TouchingBond o R, M b.1 b'.1 * we e b' = ℓ e b := by
    intro e
    let ψ : TorusSite n → ℝ := fun z =>
      if z ∈ supBall o R then ∑ b' : TouchingBond o R, gradCoeff z b'.1 * we e b' else 0
    let gs : TorusBond n → ℝ := fun b => ψ b.1 - ψ (b.1 + unitStep n b.2)
    have hψoff : ∀ z, z ∉ supBall o R → ψ z = 0 := fun z hz => if_neg hz
    have hgsoff : ∀ b, b ∉ bondsTouching o R → gs b = 0 := by
      intro b hb
      have h : b.1 ∉ supBall o R ∧ b.1 + unitStep n b.2 ∉ supBall o R := by
        simpa [bondsTouching, not_or] using hb
      simp only [gs, hψoff _ h.1, hψoff _ h.2, sub_self]
    have hrow : ∀ b : TouchingBond o R,
        ℓ e b = ∑ b' : TouchingBond o R, M b.1 b'.1 * we e b' + gs b.1 := by
      intro b
      have h1 : (G.mulVec (we e)) b = ℓ e b := congrFun (hGw e) b
      rw [← h1]
      simp only [Matrix.mulVec, dotProduct, hG, add_mul, Finset.sum_add_distrib]
      congr 1
      simp only [Finset.sum_mul]
      rw [Finset.sum_comm]
      have hz : ∀ z ∈ supBall o R, ∑ b' : TouchingBond o R,
          gradCoeff z b.1 * gradCoeff z b'.1 * we e b' = gradCoeff z b.1 * ψ z := by
        intro z hz
        simp only [ψ, if_pos hz, Finset.mul_sum, mul_assoc]
      rw [Finset.sum_congr rfl hz,
        Finset.sum_subset (Finset.subset_univ _) (fun z _ hz => by rw [hψoff z hz, mul_zero])]
      exact sum_gradCoeff_mul ψ b.1
    let φ : TorusSite n → imaginaryQuaternions := fun z => ψ z • imaginaryUnitI
    have hφ : ∀ b, latticeGrad φ b = gs b • imaginaryUnitI := fun b => by
      simp only [latticeGrad, φ, gs]
      exact (sub_smul _ _ _).symm
    let Wf : TorusBond n → imaginaryQuaternions := fun b => Ws e b • imaginaryUnitI
    have hQ : Q (latticeGrad φ) Wf =
        ∑ b : TouchingBond o R, gs b.1 * ∑ b' : TouchingBond o R, M b.1 b'.1 * we e b' := by
      rw [hcol]
      simp only [hφ, Wf, imaginaryComponent_smul_unitI]
      have h1 : ∑ e' : Fin 3, ∑ b, ∑ b',
          M b b' * (if e' = 0 then gs b else 0) * (if e' = 0 then Ws e b' else 0) =
          ∑ b, ∑ b', M b b' * gs b * Ws e b' := by
        rw [Fin.sum_univ_three]
        simp
      rw [h1, ← sum_touchingBond (o := o) (R := R) _ (fun b hb => by simp [hgsoff b hb])]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [← sum_touchingBond (o := o) (R := R) _ (fun b' hb' => by simp [hWoff e b' hb']), Finset.mul_sum]
      refine Finset.sum_congr rfl fun b' _ => ?_
      rw [hWon]
      ring
    have h0 : ∑ b : TouchingBond o R, gs b.1 * ∑ b' : TouchingBond o R, M b.1 b'.1 * we e b' = 0 := by
      rw [← hQ]
      exact hblind _ _
    have hcurl : ∑ b : TouchingBond o R, gs b.1 * ℓ e b = 0 := by
      have h1 : ∀ p : TorusPlaquette n, ∑ b : TouchingBond o R, curlCoeff p b.1 * gs b.1 = 0 := fun p => by
        refine (sum_touchingBond (o := o) (R := R) (fun b => curlCoeff p b * gs b)
          (fun b hb => by rw [hgsoff b hb, mul_zero])).trans ?_
        have h2 := imaginaryComponent_lieFormCurl 0 (latticeGrad φ) p
        rw [lieFormCurl_latticeGrad, imaginaryComponent_zero] at h2
        simp only [hφ, imaginaryComponent_smul_unitI, if_true] at h2
        exact h2.symm
      simp only [ℓ, Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_eq_zero fun p _ => ?_
      have h2 := h1 p
      calc ∑ b : TouchingBond o R, gs b.1 * (u p e * curlCoeff p b.1)
          = u p e * ∑ b : TouchingBond o R, curlCoeff p b.1 * gs b.1 := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun b _ => ?_
            ring
        _ = 0 := by rw [h2, mul_zero]
    have hsq : ∑ b : TouchingBond o R, gs b.1 ^ 2 = 0 := by
      have h1 : ∑ b : TouchingBond o R, gs b.1 * ℓ e b =
          ∑ b : TouchingBond o R, gs b.1 * ∑ b' : TouchingBond o R, M b.1 b'.1 * we e b' +
            ∑ b : TouchingBond o R, gs b.1 ^ 2 := by
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun b _ => ?_
        rw [hrow b]
        ring
      rw [hcurl, h0, zero_add] at h1
      exact h1.symm
    have hzero : ∀ b : TouchingBond o R, gs b.1 = 0 := fun b => by
      have := (Finset.sum_eq_zero_iff_of_nonneg (fun b _ => sq_nonneg (gs (b : TouchingBond o R).1))).1 hsq b
        (Finset.mem_univ b)
      exact pow_eq_zero_iff (two_ne_zero) |>.1 this
    intro b
    rw [hrow b, hzero b, add_zero]
  refine ⟨ofComponents Ws, fun b hb => ?_, fun η hη => ?_, ?_⟩
  · apply Subtype.ext
    apply Quaternion.ext <;> simp [ofComponents, hWoff _ b hb]
  · rw [hcol, hF1 η hη]
    refine Finset.sum_congr rfl fun e _ => ?_
    simp only [imaginaryComponent_ofComponents]
    rw [← sum_touchingBond (o := o) (R := R) _ (fun b hb => by simp [hη b hb, imaginaryComponent_zero])]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [← sum_touchingBond (o := o) (R := R) _ (fun b' hb' => by simp [hWoff e b' hb']), ← hkey e b,
      Finset.sum_mul]
    refine Finset.sum_congr rfl fun b' _ => ?_
    rw [hWon]
    ring
  · rw [hF1 _ (fun b hb => by
      apply Subtype.ext
      apply Quaternion.ext <;> simp [ofComponents, hWoff _ b hb])]
    refine Finset.sum_congr rfl fun e _ => ?_
    refine Eq.trans ?_ (quadratic_sum_expand (plaquettesIn S) (fun p => u p e)
      (fun p (b : TouchingBond o R) => curlCoeff p b.1) (fun b b' => G⁻¹ b b')).symm
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [imaginaryComponent_ofComponents, hWon]
    rfl
private theorem mem_bondsWithin_of_touching {o : TorusSite n} {R : ℕ} (hR : 1 ≤ R) {b : TorusBond n}
    (hb : b ∈ bondsTouching o R) :
    b ∈ bondsWithin (supBall o (2 * R)) := by apply _root_.YangMills.SharedProofs.p15112 <;> assumption
private def curlPairingLinear (S : Finset (TorusSite n)) (u : TorusPlaquette n → Fin 3 → ℝ) :
    (TorusBond n → imaginaryQuaternions) →ₗ[ℝ] ℝ where
  toFun v := colourPairing S u (lieFormCurl v)
  map_add' a b := by
    simp only [colourPairing, lieFormCurl_add, imaginaryComponent_add, mul_add, Finset.sum_add_distrib]
  map_smul' c a := by
    simp only [colourPairing, lieFormCurl_smul, imaginaryComponent_smul, Finset.mul_sum, RingHom.id_apply,
      smul_eq_mul]
    refine Finset.sum_congr rfl fun e _ => Finset.sum_congr rfl fun p _ => ?_
    ring
private theorem sliceGaussian_core {o : TorusSite n} {R : ℕ}
    (Q : (TorusBond n → imaginaryQuaternions) → (TorusBond n → imaginaryQuaternions) → ℝ)
    (M : TorusBond n → TorusBond n → ℝ) (G : Matrix (TouchingBond o R) (TouchingBond o R) ℝ)
    (var : (TorusPlaquette n → Fin 3 → ℝ) → ℝ) (x δ cK CQ : ℝ) (hx : 0 < x) (hδ : 0 ≤ δ) (hcK : 0 < cK)
    (hCQ : 1 ≤ CQ)
    (hR : 1 ≤ R) (h16 : 16 * R < n) (A : TorusBond n → imaginaryQuaternions) (hA : IsAxialSmall o R δ A)
    (hsym : ∀ u v, Q u v = Q v u)
    (hlin : ∀ (c : ℝ) (u u' v : TorusBond n → imaginaryQuaternions), Q (c • u + u') v = c * Q u v + Q u' v)
    (hbd : ∀ v, 2 * cK * curlNormSq (supBall o (2 * R)) v ≤ Q v v ∧
      Q v v ≤ CQ * curlNormSq (supBall o (2 * R)) v)
    (hblind : ∀ (φ : TorusSite n → imaginaryQuaternions) (v : TorusBond n → imaginaryQuaternions),
      Q (latticeGrad φ) v = 0)
    (hcol : ∀ u v : TorusBond n → imaginaryQuaternions, Q u v =
        ∑ e : Fin 3, ∑ b : TorusBond n, ∑ b' : TorusBond n,
          M b b' * imaginaryComponent e (u b) * imaginaryComponent e (v b'))
    (hG : ∀ b b' : TouchingBond o R, G b b' = M b.1 b'.1 +
      ∑ z ∈ supBall o R, gradCoeff z b.1 * gradCoeff z b'.1)
    (hdet : IsUnit G.det)
    (hvar : ∀ u, var u = ∑ e : Fin 3, ∑ p ∈ plaquettesIn (supBall o (2 * R)),
        ∑ p' ∈ plaquettesIn (supBall o (2 * R)),
        u p e * (∑ b : TouchingBond o R, ∑ b' : TouchingBond o R,
          curlCoeff p b.1 * G⁻¹ b b' * curlCoeff p' b'.1) * u p' e)
    (hlow : ∀ ζ ∈ gaugeSlice o R A,
      2 * cK * ((R : ℝ) ^ 2)⁻¹ * bondNormSq (supBall o (2 * R)) ζ ≤ Q ζ ζ) :
    ∃ B : TorusBond n → imaginaryQuaternions, B - A ∈ gaugeSlice o R A ∧
      (∀ η : TorusBond n → imaginaryQuaternions, (∀ b, b ∉ bondsTouching o R → η b = 0) → Q B η = 0) ∧
      curlNormSq (supBall o (2 * R)) B ≤ (CQ * 2 ^ 13 / (2 * cK)) * ((R : ℝ) ^ 4 * δ ^ 2) ∧
      (∀ b ∈ bondsWithin (supBall o (2 * R)),
        ‖B b‖ ≤ (7 + Real.sqrt (CQ * 2 ^ 12 / cK)) * ((R : ℝ) ^ 3 * δ)) ∧
      Q B B ≤ Q A A ∧
      ∀ u : TorusPlaquette n → Fin 3 → ℝ,
        (normalize ((subspaceVolume (gaugeSlice o R A)).withDensity fun ζ => ENNReal.ofReal
            (Real.exp (-(x / 2) * Q (A + ζ) (A + ζ))))).map
          (fun ζ => colourPairing (supBall o (2 * R)) u fun p => lieFormCurl (A + ζ) p - lieFormCurl B p) =
          gaussianReal 0 (x⁻¹ * var u).toNNReal := by
  have hR1 : (1 : ℝ) ≤ R := by exact_mod_cast hR
  have hzero : ∀ v, Q 0 v = 0 := by
    intro v
    have := hlin 1 0 0 v
    simp only [smul_zero, add_zero, one_mul] at this
    linarith
  let Qb : (TorusBond n → imaginaryQuaternions) →ₗ[ℝ] (TorusBond n → imaginaryQuaternions) →ₗ[ℝ] ℝ :=
    LinearMap.mk₂ ℝ Q
    (fun a b c => by simpa using hlin 1 a b c)
    (fun c a b => by simpa [hzero] using hlin c a 0 b)
    (fun a b c => by
      rw [hsym a (b + c), hsym a b, hsym a c]
      simpa using hlin 1 b c a)
    (fun c a b => by
      rw [hsym a (c • b), hsym a b]
      simpa [hzero] using hlin c b 0 a)
  have hQb : ∀ u v, Qb u v = Q u v := fun _ _ => rfl
  have hoff : ∀ ζ ∈ gaugeSlice o R A, ∀ b, b ∉ bondsTouching o R → ζ b = 0 := fun ζ h => h.1
  have hp : ∀ ζ ∈ gaugeSlice o R A, ζ ≠ 0 → 0 < Q ζ ζ := by
    intro ζ hζ h0
    obtain ⟨b, hb⟩ := Function.ne_iff.1 h0
    have hbi : b ∈ bondsTouching o R := by
      by_contra hn
      exact hb (hoff ζ hζ b hn)
    have hbS := mem_bondsWithin_of_touching hR hbi
    have h1 : ‖ζ b‖ ^ 2 ≤ bondNormSq (supBall o (2 * R)) ζ :=
      Finset.single_le_sum (f := fun b => ‖ζ b‖ ^ 2) (fun _ _ => by positivity) hbS
    have h2 : 0 < ‖ζ b‖ ^ 2 := by
      have : 0 < ‖ζ b‖ := norm_pos_iff.2 hb
      positivity
    have h3 : 0 < bondNormSq (supBall o (2 * R)) ζ := lt_of_lt_of_le h2 h1
    have h4 : 0 < 2 * cK * ((R : ℝ) ^ 2)⁻¹ * bondNormSq (supBall o (2 * R)) ζ := by positivity
    exact lt_of_lt_of_le h4 (hlow ζ hζ)
  have hz : ∀ ζ ∈ gaugeSlice o R A, ∀ φ, ζ = latticeGrad φ → ζ = 0 := by
    intro ζ hζ φ he
    by_contra h0
    have h1 := hp ζ hζ h0
    have h2 : Q ζ ζ = 0 := by
      conv_lhs => rw [he]
      rw [← he]
      have := hblind φ ζ
      rwa [← he] at this
    linarith
  obtain ⟨ζB, hζB⟩ := exists_representative (E := gaugeSlice o R A)
    (Qb.domRestrict₁₂ (gaugeSlice o R A) (gaugeSlice o R A))
    (fun z h0 => hp z.1 z.2 (by simpa using h0)) (-(Qb A).domRestrict (gaugeSlice o R A))
  have hζB' : ∀ η ∈ gaugeSlice o R A, Q ζB.1 η = -Q A η := fun η hη => hζB ⟨η, hη⟩
  set B : TorusBond n → imaginaryQuaternions := A + ζB.1 with hBdef
  have hBA : B - A = ζB.1 := by simp [hBdef]
  have hBs : ∀ η ∈ gaugeSlice o R A, Q B η = 0 := by
    intro η hη
    have h1 : Qb B η = Qb A η + Qb ζB.1 η := by simp [hBdef]
    rw [hQb, hQb, hQb, hζB' η hη] at h1
    linarith
  have hcrit : ∀ η : TorusBond n → imaginaryQuaternions, (∀ b, b ∉ bondsTouching o R → η b = 0) →
      Q B η = 0 := by
    intro η hη
    obtain ⟨ζ, hζ, φ, rfl⟩ := exists_slice_add_grad hR h16 A hz η hη
    have h1 : Qb B (ζ + latticeGrad φ) = Qb B ζ + Qb B (latticeGrad φ) := by simp
    rw [hQb, hQb, hQb, hBs ζ hζ, hsym B (latticeGrad φ), hblind] at h1
    linarith
  have hcs : ∀ v, 0 ≤ curlNormSq (supBall o (2 * R)) v := fun v =>
    Finset.sum_nonneg fun _ _ => by positivity
  have hexp : Q A A = Q B B + Q ζB.1 ζB.1 := by
    have h1 : Qb B B = Qb A A + Qb A ζB.1 + (Qb ζB.1 A + Qb ζB.1 ζB.1) := by
      simp only [hBdef, map_add, LinearMap.add_apply]
      ring
    have h2 := hζB' A
    simp only [hQb] at h1
    have h3 := hBs ζB.1 ζB.2
    have h4 : Qb B ζB.1 = Qb A ζB.1 + Qb ζB.1 ζB.1 := by simp [hBdef]
    simp only [hQb] at h4
    have h5 := hsym ζB.1 A
    linarith
  have hBpos : 0 ≤ Q B B := by
    have := (hbd B).1
    have h2 := hcs B
    have h3 : 0 ≤ 2 * cK * curlNormSq (supBall o (2 * R)) B := by positivity
    linarith
  have hζpos : 0 ≤ Q ζB.1 ζB.1 := by
    have := (hbd ζB.1).1
    have h2 := hcs ζB.1
    have h3 : 0 ≤ 2 * cK * curlNormSq (supBall o (2 * R)) ζB.1 := by positivity
    linarith
  have hAA : Q A A ≤ CQ * 2 ^ 13 * ((R : ℝ) ^ 4 * δ ^ 2) := by
    have h1 := (hbd A).2
    have h2 := hA.curlNormSq_le
    have h3 : CQ * curlNormSq (supBall o (2 * R)) A ≤ CQ * (2 ^ 13 * (R : ℝ) ^ 4 * δ ^ 2) :=
      mul_le_mul_of_nonneg_left h2 (by linarith)
    calc Q A A ≤ _ := h1
      _ ≤ _ := h3
      _ = _ := by ring
  refine ⟨B, by rw [hBA]; exact ζB.2, hcrit, ?_, ?_, by linarith, ?_⟩
  · have h1 := (hbd B).1
    rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
    linarith
  · intro b hb
    have hbs : bondNormSq (supBall o (2 * R)) ζB.1 ≤ (CQ * 2 ^ 12 / cK) * ((R : ℝ) ^ 6 * δ ^ 2) := by
      have h1 := hlow ζB.1 ζB.2
      have h2 : 2 * cK * ((R : ℝ) ^ 2)⁻¹ * bondNormSq (supBall o (2 * R)) ζB.1 ≤
          CQ * 2 ^ 13 * ((R : ℝ) ^ 4 * δ ^ 2) := by linarith
      rw [div_mul_eq_mul_div, le_div_iff₀ hcK]
      have h3 : 2 * cK * bondNormSq (supBall o (2 * R)) ζB.1 ≤
          CQ * 2 ^ 13 * ((R : ℝ) ^ 4 * δ ^ 2) * (R : ℝ) ^ 2 := by
        have h4 := mul_le_mul_of_nonneg_right h2 (by positivity : (0 : ℝ) ≤ (R : ℝ) ^ 2)
        have h5 : 2 * cK * ((R : ℝ) ^ 2)⁻¹ * bondNormSq (supBall o (2 * R)) ζB.1 * (R : ℝ) ^ 2 =
            2 * cK * bondNormSq (supBall o (2 * R)) ζB.1 := by
          field_simp
        rw [h5] at h4
        exact h4
      nlinarith [h3]
    have h1 : ‖ζB.1 b‖ ^ 2 ≤ bondNormSq (supBall o (2 * R)) ζB.1 :=
      Finset.single_le_sum (f := fun b => ‖ζB.1 b‖ ^ 2) (fun _ _ => by positivity) hb
    set c₂ : ℝ := CQ * 2 ^ 12 / cK with hc₂
    have hc₂0 : 0 ≤ c₂ := by positivity
    have h2 : ‖ζB.1 b‖ ≤ Real.sqrt c₂ * ((R : ℝ) ^ 3 * δ) := by
      have h3 : ‖ζB.1 b‖ ^ 2 ≤ (Real.sqrt c₂ * ((R : ℝ) ^ 3 * δ)) ^ 2 := by
        rw [mul_pow, Real.sq_sqrt hc₂0]
        calc ‖ζB.1 b‖ ^ 2 ≤ c₂ * ((R : ℝ) ^ 6 * δ ^ 2) := h1.trans hbs
          _ = _ := by ring
      exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 h3
    have h4 : ‖A b‖ ≤ 7 * R * δ := hA.norm_le b hb
    have h5 : 7 * (R : ℝ) * δ ≤ 7 * ((R : ℝ) ^ 3 * δ) := by
      have : (R : ℝ) ≤ (R : ℝ) ^ 3 := by nlinarith [mul_self_nonneg ((R : ℝ) - 1), hR1]
      nlinarith [mul_le_mul_of_nonneg_right this hδ]
    calc ‖B b‖ ≤ ‖A b‖ + ‖ζB.1 b‖ := norm_add_le _ _
      _ ≤ _ := by nlinarith
  · intro u
    obtain ⟨w, hw0, hw1, hw2⟩ := exists_curl_potential (supBall o (2 * R)) Q M G hcol hblind hG hdet u
    obtain ⟨h, hh, φ, hwe⟩ := exists_slice_add_grad hR h16 A hz w hw0
    have hΛg : curlPairingLinear (supBall o (2 * R)) u (latticeGrad φ) = 0 := by
      show colourPairing _ u (lieFormCurl (latticeGrad φ)) = 0
      simp only [colourPairing, lieFormCurl_latticeGrad, imaginaryComponent_zero, mul_zero,
        Finset.sum_const_zero]
    have hQη : ∀ η ∈ gaugeSlice o R A, Qb h η = curlPairingLinear (supBall o (2 * R)) u η := by
      intro η hη
      have h1 : Q η w = colourPairing (supBall o (2 * R)) u (lieFormCurl η) := hw1 η (hoff η hη)
      have h2 : Qb η w = Qb η h + Qb η (latticeGrad φ) := by rw [hwe]; simp
      rw [hQb, hQb, hQb, hsym η (latticeGrad φ), hblind, h1] at h2
      rw [hQb, hsym h η]
      show Q η h = colourPairing _ u (lieFormCurl η)
      linarith
    have hQh : Qb h h = var u := by
      rw [hQη h hh, hvar, ← hw2]
      show curlPairingLinear _ u h = curlPairingLinear _ u w
      rw [hwe, map_add, hΛg, add_zero]
    let F : (TorusBond n → imaginaryQuaternions) → ℝ := fun ζ =>
      colourPairing (supBall o (2 * R)) u fun p => lieFormCurl (A + ζ) p - lieFormCurl B p
    have hFe0 : ∀ ζ, F ζ = curlPairingLinear (supBall o (2 * R)) u (A + ζ - B) := by
      intro ζ
      show colourPairing _ u _ = colourPairing _ u _
      congr 1
      funext p
      rw [lieFormCurl_sub]
    have hFm : Measurable F := by
      have hc : Continuous fun ζ : TorusBond n → imaginaryQuaternions =>
          curlPairingLinear (supBall o (2 * R)) u (A + ζ - B) :=
        ((curlPairingLinear (supBall o (2 * R)) u).continuous_of_finiteDimensional).comp
          ((continuous_const.add continuous_id).sub continuous_const)
      have : F = fun ζ => curlPairingLinear (supBall o (2 * R)) u (A + ζ - B) := funext hFe0
      rw [this]
      exact hc.measurable
    have hFe : ∀ ζ ∈ gaugeSlice o R A, F ζ = Qb h (ζ - (B - A)) := by
      intro ζ hζ
      have h1 : ζ - (B - A) ∈ gaugeSlice o R A := Submodule.sub_mem _ hζ (by rw [hBA]; exact ζB.2)
      rw [hFe0, hQη _ h1]
      congr 1
      abel
    have := map_sliceGaussian (gaugeSlice o R A) Qb (fun u v => hsym u v) hp x hx A B h hBs
      (by rw [hBA]; exact ζB.2) hh F hFm hFe
    rw [hQh] at this
    exact this
private theorem le_boxRadius {κ₀ x : ℝ} {N : ℕ} (h27 : 1 / 27 ≤ κ₀) (hx1 : 1 ≤ x) (hN : (N : ℝ) ^ 27 ≤ x) :
    N ≤ boxRadius κ₀ x := by
  have h1 : x ^ (1 / 27 : ℝ) ≤ x ^ κ₀ := Real.rpow_le_rpow_of_exponent_le hx1 h27
  have h2 : ((N : ℝ) ^ 27) ^ (1 / 27 : ℝ) ≤ x ^ (1 / 27 : ℝ) :=
    Real.rpow_le_rpow (by positivity) hN (by norm_num)
  have h3 : ((N : ℝ) ^ 27) ^ (1 / 27 : ℝ) = N := by
    rw [show (1 / 27 : ℝ) = ((27 : ℕ) : ℝ)⁻¹ by norm_num]
    exact Real.pow_rpow_inv_natCast (by positivity) (by norm_num)
  have h4 : (N : ℝ) ≤ x ^ κ₀ := by linarith
  have h5 : (N : ℝ) ≤ (boxRadius κ₀ x : ℝ) := h4.trans (Nat.le_ceil _)
  exact_mod_cast h5
end SliceCurlGaussian
theorem sliceCurlGaussianStatement_holds (h₁ : cubeHessianStatement) (h₂ : curlCovarianceBoundsStatement)
    (h₃ : ellipsoidBoundsStatement) : sliceCurlGaussianStatement := by
  intro Tb hd κ₀ h27 h21
  obtain ⟨CQ, R₁, hCQ, hF⟩ := h₁ Tb hd
  obtain ⟨R₂, hK⟩ := h₂ Tb hd
  obtain ⟨K, xs₃, -, hE⟩ := h₃ Tb hd κ₀ h27 h21 1 one_pos
  have hc := hd.cK_pos
  set C₁ : ℝ := CQ * 2 ^ 13 / (2 * Tb.coercivity) with hC₁
  set C₂ : ℝ := 7 + Real.sqrt (CQ * 2 ^ 12 / Tb.coercivity) with hC₂
  have hC₁0 : 0 ≤ C₁ := by positivity
  have hC₂0 : 0 ≤ C₂ := by positivity
  refine ⟨C₁ + C₂, max (max xs₃ 1) (((R₁ + R₂ + 1 : ℕ) : ℝ) ^ 27), ?_⟩
  intro x R k n _ o A hx hR h16 hA
  have hx1 : 1 ≤ x := (le_max_right _ _).trans ((le_max_left _ _).trans hx)
  have hx3 : xs₃ ≤ x := (le_max_left _ _).trans ((le_max_left _ _).trans hx)
  have hRN : R₁ + R₂ + 1 ≤ R := by
    rw [hR]
    exact SliceCurlGaussian.le_boxRadius h27 hx1 ((le_max_right _ _).trans hx)
  have hδ : 0 ≤ boxScale x := by
    have : 0 ≤ Real.log x := Real.log_nonneg hx1
    have h2 : 0 < x ^ (-(1 / 2 : ℝ)) := Real.rpow_pos_of_pos (by linarith) _
    unfold boxScale
    positivity
  obtain ⟨-, -, hs, hl, hb, hg, hcol⟩ := hF k n o R (by omega) h16
  obtain ⟨hdet, -, -⟩ := hK k n o R (by omega) h16
  obtain ⟨hlow, -⟩ := hE x R k n o A hx3 hR h16 hA
  obtain ⟨B, h1, h2, h3, h4, h5, h6⟩ := SliceCurlGaussian.sliceGaussian_core
    (hessianForm Tb.coupling Tb.side k (supBall o (2 * R)))
    (fun b b' => mixedDeriv (actionAtLevel Tb.coupling Tb.side k (supBall o (2 * R))) (trivialField n) ![b, b']
      ![imaginaryUnitI, imaginaryUnitI])
    (regularizedHessian Tb.coupling Tb.side k o R) (curlQuadForm Tb.coupling Tb.side k o R) x (boxScale x)
    Tb.coercivity CQ (by linarith) hδ hc hCQ
    (by omega) h16 A hA hs hl hb hg hcol (fun _ _ => rfl) hdet (fun _ => rfl) hlow
  have hRR : (0 : ℝ) ≤ (R : ℝ) ^ 4 * boxScale x ^ 2 := by positivity
  have hRR3 : (0 : ℝ) ≤ (R : ℝ) ^ 3 * boxScale x := by positivity
  refine ⟨B, h1, h2, ?_, fun b hb' => ?_, h5, h6⟩
  · calc curlNormSq (supBall o (2 * R)) B ≤ C₁ * ((R : ℝ) ^ 4 * boxScale x ^ 2) := h3
      _ ≤ (C₁ + C₂) * ((R : ℝ) ^ 4 * boxScale x ^ 2) := by nlinarith
      _ = _ := by ring
  · calc ‖B b‖ ≤ C₂ * ((R : ℝ) ^ 3 * boxScale x) := h4 b hb'
      _ ≤ (C₁ + C₂) * ((R : ℝ) ^ 3 * boxScale x) := by nlinarith
      _ = _ := by ring
end YangMills.Construction.BoxGaussian
end
