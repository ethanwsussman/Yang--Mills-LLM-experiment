import YangMills.Construction.ComplexMeasures.UniquenessOfMeasuresAndTheIntegralOfAComplexMeasure
import YangMills.Construction.MeasureTheory.ComplexMeasureFacts
import YangMills.Construction.SpectralTheory.FactsOnResolvedOperators
import YangMills.Construction.SpectralTheory.MeasuresIntegralsProductsImagesAndTransportOfAProjectionValuedMeasure
import YangMills.Construction.SpectralTheory.ProjectionValuedMeasureFromScalarMeasures
import Mathlib
set_option autoImplicit false
open MeasureTheory Set Filter Topology
open scoped InnerProductSpace ComplexConjugate NNReal ENNReal ComplexOrder
noncomputable section
namespace YangMills.Construction.ResolvedFacts
open YangMills.Construction.HilbertSpaceBasics (UnboundedOp IsContraction)
open YangMills.Construction.OperatorTransport
  (IsBoundedAdjoint IsContractionSemigroup IsUnitaryGroup IsUnitaryMap)
open YangMills.Construction.BorelSpectral YangMills.Construction.SpectralTheorem
open YangMills.Construction.BorelSpectral.SpectralMeasure
open YangMills.Construction.SelfAdjointFunctions (fnCalc expI)
open YangMills.Construction.ResolvedOps (IsDiagonalized expComplex)
open YangMills.Construction.SpectralMeasureCalculus
open YangMills.Construction.BorelCalculus (IsBoundedFn IsRealValued conjFn)
open YangMills.Construction.SetFunctions (MeasurableSets IsCountablyAdditive CountablyAdditiveFn)
open YangMills.Construction.BorelComplexMeasures (IsJordanCombination IsIntegralOf combinedIntegral)
open YangMills.Construction.SpectralFromScalar (AllBoundedMeasurable SeparatesComplexMeasures)
section MeasurableTransfer
variable {X T : Type} [MeasurableSpace X] [MeasurableSpace T]
theorem nonnegToMeasure_real {m : MeasurableSets T → ℂ}
    (hm : SetFunctions.IsFiniteNonnegMeasure m) (Δ : MeasurableSets T) :
    (((SetFunctions.nonnegToMeasure m).real Δ : ℝ) : ℂ) = m Δ := by
  have h₁ : SetFunctions.nonnegToMeasure m (Δ : Set T) = ENNReal.ofReal (m Δ).re :=
    hm.2.2.2 Δ
  have h₂ := hm.2.1 Δ
  rw [Measure.real, h₁, ENNReal.toReal_ofReal h₂.2]
  exact Complex.ext (by simp) (by simp [h₂.1])
theorem exists_jordanCombination (hF : SetFunctions.ComplexMeasureFacts)
    (ν : MeasurableSets T → ℂ) (hν : IsCountablyAdditive ν) :
    ∃ ν₁ ν₂ ν₃ ν₄ : Measure T, IsJordanCombination ν ν₁ ν₂ ν₃ ν₄ := by
  obtain ⟨hTV, hPN, -⟩ := hF T
  obtain ⟨-, -, hre, him, -, -⟩ := hTV ν hν
  obtain ⟨hp₁, hn₁, -, -, he₁⟩ := hPN _ hre fun A => by simp [SetFunctions.reFn]
  obtain ⟨hp₂, hn₂, -, -, he₂⟩ := hPN _ him fun A => by simp [SetFunctions.imFn]
  refine ⟨SetFunctions.nonnegToMeasure (SetFunctions.posPart
      (SetFunctions.reFn ν)), SetFunctions.nonnegToMeasure
      (SetFunctions.negPart (SetFunctions.reFn ν)),
    SetFunctions.nonnegToMeasure (SetFunctions.posPart
      (SetFunctions.imFn ν)), SetFunctions.nonnegToMeasure
      (SetFunctions.negPart (SetFunctions.imFn ν)),
    hp₁.2.2.1, hn₁.2.2.1, hp₂.2.2.1, hn₂.2.2.1, fun Δ => ?_⟩
  push_cast
  rw [nonnegToMeasure_real hp₁, nonnegToMeasure_real hn₁, nonnegToMeasure_real hp₂,
    nonnegToMeasure_real hn₂, ← he₁, ← he₂]
  simp only [SetFunctions.reFn, SetFunctions.imFn]
  rw [mul_comm]
  exact (Complex.re_add_im _).symm
theorem separates_of_measurableEquiv (hF : SetFunctions.ComplexMeasureFacts) (e : X ≃ᵐ T)
    (hX : ∀ (ν : MeasurableSets X → ℂ) (g : X → ℂ) (c : ℂ), IsIntegralOf ν g c →
      BorelComplexMeasures.integralOf ν g = c)
    {ι : Type} (h : ι → T → ℂ) (hh : ∀ i, Measurable (h i) ∧ ∃ c : ℝ, ∀ x, ‖h i x‖ ≤ c)
    (hT : ∀ ν : CountablyAdditiveFn T, (∀ i, BorelComplexMeasures.integralOf ν.1 (h i) = 0) →
      ∀ Δ, ν.1 Δ = 0) :
    SeparatesComplexMeasures (Set.range fun i => h i ∘ e) := by
  intro ν hν Δ
  let ν' : MeasurableSets T → ℂ := fun B => ν.1 ⟨e ⁻¹' B.1, e.measurable B.2⟩
  have hν' : IsCountablyAdditive ν' := by
    intro A hA
    have h₀ := ν.2 (fun j => ⟨e ⁻¹' (A j).1, e.measurable (A j).2⟩)
      (fun i j hij => (hA hij).preimage e)
    have hu : ν' (SetFunctions.iUnionSets A) =
        ν.1 (SetFunctions.iUnionSets fun j => ⟨e ⁻¹' (A j).1, e.measurable (A j).2⟩) :=
      congrArg ν.1 (Subtype.ext (preimage_iUnion))
    rw [hu]
    exact h₀
  have key : ∀ i, BorelComplexMeasures.integralOf ν' (h i) = 0 := by
    intro i
    obtain ⟨hmeas, c, hc⟩ := hh i
    have hint : ∀ (m : Measure T), IsFiniteMeasure m → Integrable (h i) m := fun m _ =>
      (integrable_const c).mono' hmeas.aestronglyMeasurable (ae_of_all _ hc)
    obtain ⟨m₁, m₂, m₃, m₄, hm⟩ := exists_jordanCombination hF ν' hν'
    have hex : ∃ c, IsIntegralOf ν' (h i) c :=
      ⟨_, m₁, m₂, m₃, m₄, hm, hmeas, hint _ hm.1, hint _ hm.2.1, hint _ hm.2.2.1,
        hint _ hm.2.2.2.1, rfl⟩
    have hs : IsIntegralOf ν' (h i) (BorelComplexMeasures.integralOf ν' (h i)) :=
      Classical.epsilon_spec hex
    obtain ⟨n₁, n₂, n₃, n₄, ⟨f₁, f₂, f₃, f₄, hn⟩, -, i₁, i₂, i₃, i₄, hval⟩ := hs
    have hmap : ∀ (n : Measure T), ∫ x, (h i ∘ e) x ∂(n.map e.symm) = ∫ x, h i x ∂n := by
      intro n
      rw [integral_map_equiv]
      simp
    have himap : ∀ (n : Measure T), Integrable (h i) n → Integrable (h i ∘ e) (n.map e.symm) := by
      intro n hn'
      rw [e.symm.measurableEmbedding.integrable_map_iff]
      simpa [Function.comp_def] using hn'
    have hreal : ∀ (n : Measure T) (Δ : MeasurableSets X),
        (n.map e.symm).real Δ.1 = n.real (e.symm ⁻¹' Δ.1) := by
      intro n Δ
      exact map_measureReal_apply e.symm.measurable Δ.2
    have hv : IsIntegralOf ν.1 (h i ∘ e)
        (BorelComplexMeasures.integralOf ν' (h i)) := by
      refine ⟨n₁.map e.symm, n₂.map e.symm, n₃.map e.symm, n₄.map e.symm,
        ⟨inferInstance, inferInstance, inferInstance, inferInstance, fun Δ => ?_⟩,
        hmeas.comp e.measurable, himap _ i₁, himap _ i₂, himap _ i₃, himap _ i₄, ?_⟩
      · have h₁ := hn ⟨e.symm ⁻¹' Δ.1, e.symm.measurable Δ.2⟩
        have h₂ : ν' ⟨e.symm ⁻¹' Δ.1, e.symm.measurable Δ.2⟩ = ν.1 Δ :=
          congrArg ν.1 (Subtype.ext (by ext x; simp))
        rw [h₂] at h₁
        rw [h₁, hreal, hreal, hreal, hreal]
      · rw [hval]
        simp only [combinedIntegral, hmap]
    have h₀ := hX _ _ _ hv
    rw [← h₀]
    exact hν _ ⟨i, rfl⟩
  have := hT ⟨ν', hν'⟩ key ⟨e.symm ⁻¹' Δ.1, e.symm.measurable Δ.2⟩
  have h₂ : ν' ⟨e.symm ⁻¹' Δ.1, e.symm.measurable Δ.2⟩ = ν.1 Δ :=
    congrArg ν.1 (Subtype.ext (by ext x; simp))
  rw [← h₂]
  exact this
end MeasurableTransfer
section LineFunctions
variable {n : ℕ} {Y : Set (Fin n → ℝ)} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]
theorem eq_of_isSpectralIntegralOf {E : SpectralMeasure Y H} {g : Y → ℂ} {A B : UnboundedOp H}
    (hA : IsSpectralIntegralOf A E g) (hB : IsSpectralIntegralOf B E g) : A = B := by
  have hd : A.domain = B.domain := by
    ext ψ
    rw [hA.1, hB.1]
  refine LinearPMap.ext hd fun x hx hy => ?_
  rw [hA.2, hB.2]
theorem eq_spectralIntegralOp {E : SpectralMeasure Y H} {g : Y → ℂ} {A : UnboundedOp H}
    (hE : UnboundedCalculusLaws E) (hg : Measurable g) (hA : IsSpectralIntegralOf A E g) :
    A = spectralIntegralOp E g :=
  eq_of_isSpectralIntegralOf hA (hE.isIntegralOf g hg)
theorem integralOp_one {E : SpectralMeasure Y H} (hB : BoundedCalculusLaws E) :
    E.integralOp (fun _ => 1) = 1 := by
  have h := hB.indicator ⟨univ, MeasurableSet.univ⟩
  rw [E.map_univ, indicator_univ] at h
  exact h
theorem measurable_coord : Measurable fun y : RealLineSet => y.1 0 :=
  (measurable_pi_apply 0).comp measurable_subtype_coe
theorem measurable_coordVar : Measurable (coordVar : RealLineSet → ℂ) :=
  Complex.measurable_ofReal.comp measurable_coord
def expIFn (s : ℝ) (y : RealLineSet) : ℂ := Complex.exp (Complex.I * s * (y.1 0 : ℝ))
theorem measurable_expIFn (s : ℝ) : Measurable (expIFn s) :=
  Complex.measurable_exp.comp (measurable_const.mul measurable_coordVar)
theorem norm_expIFn (s : ℝ) (y : RealLineSet) : ‖expIFn s y‖ = 1 := by
  have : Complex.I * s * (y.1 0 : ℝ) = ((s * y.1 0 : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  rw [expIFn, this, Complex.norm_exp_ofReal_mul_I]
theorem isBoundedFn_expIFn (s : ℝ) : IsBoundedFn (expIFn s) :=
  ⟨1, fun y => (norm_expIFn s y).le⟩
theorem expIFn_add (s t : ℝ) :
    expIFn (s + t) = expIFn s * expIFn t := by
  funext y
  simp only [expIFn, Pi.mul_apply, ← Complex.exp_add]
  congr 1
  push_cast
  ring
theorem expIFn_zero : expIFn 0 = fun _ => 1 := by
  funext y
  simp [expIFn]
def diffQuotFn (h : ℝ) (y : RealLineSet) : ℂ :=
  (-Complex.I * (h⁻¹ : ℝ)) * (expIFn h y - 1)
theorem measurable_diffQuotFn (h : ℝ) : Measurable (diffQuotFn h) :=
  measurable_const.mul ((measurable_expIFn h).sub measurable_const)
theorem norm_diffQuotFn_le {h : ℝ} (hh : h ≠ 0) (y : RealLineSet) :
    ‖diffQuotFn h y‖ ≤ ‖coordVar y‖ := by
  have h₁ : ‖expIFn h y - 1‖ ≤ ‖h * y.1 0‖ := by
    have := @Real.norm_exp_I_mul_ofReal_sub_one_le (h * y.1 0)
    have h₂ : Complex.I * ((h * y.1 0 : ℝ) : ℂ) = Complex.I * h * (y.1 0 : ℝ) := by
      push_cast
      ring
    rwa [h₂] at this
  have h₃ : ‖coordVar y‖ = |y.1 0| := by simp [coordVar]
  rw [diffQuotFn, norm_mul, norm_mul, h₃]
  simp only [norm_neg, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs] at h₁ ⊢
  rw [abs_mul] at h₁
  rw [abs_inv]
  have hp : 0 < |h| := abs_pos.mpr hh
  rw [inv_mul_le_iff₀ hp]
  exact h₁
theorem tendsto_diffQuotFn (y : RealLineSet) :
    Tendsto (fun h => diffQuotFn h y) (𝓝[≠] 0) (𝓝 (coordVar y)) := by
  have hd : HasDerivAt (fun h : ℝ => Complex.exp (Complex.I * h * (y.1 0 : ℝ)))
      (Complex.I * (y.1 0 : ℝ)) 0 := by
    have h₁ : HasDerivAt (fun h : ℝ => Complex.I * (h : ℂ) * (y.1 0 : ℝ))
        (Complex.I * (y.1 0 : ℝ)) 0 := by
      have := ((hasDerivAt_id (0 : ℝ)).ofReal_comp.const_mul Complex.I).mul_const ((y.1 0 : ℝ) : ℂ)
      simpa using this
    have := h₁.cexp
    simpa using this
  have h₂ := hasDerivAt_iff_tendsto_slope_zero.mp hd
  have h₃ := h₂.const_smul (-Complex.I)
  have h₄ : -Complex.I • (Complex.I * ((y.1 0 : ℝ) : ℂ)) = coordVar y := by
    simp only [coordVar, smul_eq_mul]
    rw [← mul_assoc]
    simp
  rw [h₄] at h₃
  refine h₃.congr fun h => ?_
  simp only [diffQuotFn, expIFn, zero_add, smul_eq_mul, Complex.real_smul]
  simp
  ring
end LineFunctions
section DerivativeOfExpI
variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
theorem integralOp_diffQuotFn {E : SpectralMeasure RealLineSet H}
    (hB : BoundedCalculusLaws E) (h : ℝ) :
    E.integralOp (diffQuotFn h) =
      (-Complex.I * (h⁻¹ : ℝ)) • (E.integralOp (expIFn h) - 1) := by
  have h₁ : diffQuotFn h =
      (-Complex.I * (h⁻¹ : ℝ)) • (expIFn h + (-1 : ℂ) • fun _ => (1 : ℂ)) := by
    funext y
    simp only [diffQuotFn, Pi.smul_apply, Pi.add_apply, smul_eq_mul]
    ring
  have hb₁ : IsBoundedFn fun _ : RealLineSet => (1 : ℂ) := ⟨1, fun _ => by simp⟩
  have hb₂ : IsBoundedFn ((-1 : ℂ) • fun _ : RealLineSet => (1 : ℂ)) :=
    ⟨1, fun _ => by simp⟩
  have hm₂ : Measurable ((-1 : ℂ) • fun _ : RealLineSet => (1 : ℂ)) := measurable_const
  have hb₃ : IsBoundedFn (expIFn h + (-1 : ℂ) • fun _ : RealLineSet => (1 : ℂ)) :=
    ⟨2, fun y => by
      refine (norm_add_le _ _).trans ?_
      have := norm_expIFn h y
      simp only [Pi.smul_apply, smul_eq_mul, mul_one, norm_neg, norm_one, this]
      norm_num⟩
  rw [h₁, hB.smul _ _ ((measurable_expIFn h).add hm₂) hb₃,
    hB.add _ _ (measurable_expIFn h) (isBoundedFn_expIFn h) hm₂ hb₂,
    hB.smul _ _ measurable_const hb₁, integralOp_one hB]
  simp [sub_eq_add_neg]
theorem integrable_norm_coordVar_sq {E : SpectralMeasure RealLineSet H} {φ : H}
    (hφ : φ ∈ E.integralDom coordVar) :
    Integrable (fun y => ‖coordVar y‖ ^ 2) (E.diagMeasure φ) := by
  refine ⟨(measurable_coordVar.norm.pow_const 2).aestronglyMeasurable, ?_⟩
  have : ∀ y, ‖‖coordVar y‖ ^ 2‖ₑ = ‖coordVar y‖ₑ ^ 2 := fun y => by
    simp [enorm_pow]
  simp only [HasFiniteIntegral, this]
  exact hφ
theorem tendsto_integralOp_diffQuotFn {E : SpectralMeasure RealLineSet H}
    (hA : UnboundedCalculusLaws E) {φ : H}
    (hφ : φ ∈ E.integralDom coordVar) :
    Tendsto (fun h : ℝ => E.integralOp (diffQuotFn h) φ) (𝓝[≠] 0)
      (𝓝 (E.integralApply coordVar φ)) := by
  have hq : ∀ h : ℝ, h ≠ 0 → IsBoundedFn (diffQuotFn h) := fun h hh =>
    ⟨|h⁻¹| * 2, fun y => by
      rw [diffQuotFn, norm_mul, norm_mul]
      simp only [norm_neg, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]
      refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
      refine (norm_sub_le _ _).trans ?_
      rw [norm_expIFn]
      norm_num⟩
  have hint : Tendsto (fun h : ℝ => ∫ y, ‖coordVar y - diffQuotFn h y‖ ^ 2
      ∂E.diagMeasure φ) (𝓝[≠] 0) (𝓝 (∫ _, (0 : ℝ) ∂E.diagMeasure φ)) := by
    refine tendsto_integral_filter_of_dominated_convergence
      (fun y => 4 * ‖coordVar y‖ ^ 2) ?_ ?_ ((integrable_norm_coordVar_sq hφ).const_mul 4) ?_
    · exact Eventually.of_forall fun h => ((measurable_coordVar.sub
        (measurable_diffQuotFn h)).norm.pow_const 2).aestronglyMeasurable
    · filter_upwards [self_mem_nhdsWithin] with h hh
      refine ae_of_all _ fun y => ?_
      have h₁ := norm_diffQuotFn_le hh y
      have h₂ : ‖coordVar y - diffQuotFn h y‖ ≤ 2 * ‖coordVar y‖ := by
        refine (norm_sub_le _ _).trans ?_
        linarith
      rw [Real.norm_of_nonneg (by positivity)]
      nlinarith [norm_nonneg (coordVar y - diffQuotFn h y), norm_nonneg (coordVar y)]
    · refine ae_of_all _ fun y => ?_
      have h₁ := (tendsto_const_nhds (x := coordVar y)).sub (tendsto_diffQuotFn y)
      have h₂ := (h₁.norm).pow 2
      simpa using h₂
  rw [integral_zero] at hint
  have hsq : Tendsto (fun h : ℝ => ‖E.integralApply coordVar φ -
      E.integralOp (diffQuotFn h) φ‖ ^ 2) (𝓝[≠] 0) (𝓝 0) := by
    refine hint.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with h hh
    exact (hA.norm_sub_sq _ _ measurable_coordVar (measurable_diffQuotFn h) (hq h hh)
      φ hφ).symm
  have hn : Tendsto (fun h : ℝ => ‖E.integralApply coordVar φ -
      E.integralOp (diffQuotFn h) φ‖) (𝓝[≠] 0) (𝓝 0) := by
    have := hsq.sqrt
    simpa [Real.sqrt_sq (norm_nonneg _)] using this
  have := (tendsto_iff_norm_sub_tendsto_zero.mpr (by
    simpa [norm_sub_rev] using hn) :
    Tendsto (fun h : ℝ => E.integralOp (diffQuotFn h) φ) (𝓝[≠] 0)
      (𝓝 (E.integralApply coordVar φ)))
  exact this
theorem integralOp_expIFn_mem {E : SpectralMeasure RealLineSet H}
    (hP : ProductLaws E) (s : ℝ) {ψ : H} (hψ : ψ ∈ E.integralDom coordVar) :
    E.integralOp (expIFn s) ψ ∈ E.integralDom coordVar := by
  refine hP.boundedIntegral_mem _ _ measurable_coordVar (measurable_expIFn s)
    (isBoundedFn_expIFn s) ψ ?_
  have h₁ : ∀ y, ‖(coordVar * expIFn s) y‖ₑ = ‖coordVar y‖ₑ := fun y => by
    rw [Pi.mul_apply, enorm_mul]
    have : ‖expIFn s y‖ₑ = 1 := by
      rw [← ofReal_norm, norm_expIFn]
      simp
    rw [this, mul_one]
  have h₂ : E.integralDom (coordVar * expIFn s) =
      E.integralDom coordVar := by
    unfold integralDom
    simp only [h₁]
  rw [h₂]
  exact hψ
theorem hasDerivAt_integralOp_expIFn {E : SpectralMeasure RealLineSet H}
    (hB : BoundedCalculusLaws E) (hA : UnboundedCalculusLaws E) (hP : ProductLaws E) {ψ : H}
    (hψ : ψ ∈ E.integralDom coordVar) (s : ℝ) :
    HasDerivAt (fun s => E.integralOp (expIFn s) ψ)
      (Complex.I • E.integralApply coordVar (E.integralOp (expIFn s) ψ)) s := by
  rw [hasDerivAt_iff_tendsto_slope_zero]
  have h₁ := (tendsto_integralOp_diffQuotFn hA
    (integralOp_expIFn_mem hP s hψ)).const_smul Complex.I
  refine h₁.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with h hh
  have hh' : h ≠ 0 := hh
  have hadd : E.integralOp (expIFn (s + h)) ψ =
      E.integralOp (expIFn h) (E.integralOp (expIFn s) ψ) := by
    rw [add_comm, expIFn_add, hB.mul _ _ (measurable_expIFn h)
      (isBoundedFn_expIFn h) (measurable_expIFn s) (isBoundedFn_expIFn s)]
    rfl
  rw [hadd, integralOp_diffQuotFn hB]
  simp only [smul_apply, sub_apply, one_apply_eq_self]
  rw [smul_smul, ← mul_assoc]
  simp only [mul_neg, Complex.I_mul_I, neg_neg, one_mul, Complex.coe_smul]
end DerivativeOfExpI
section SpectralMeasureUniqueness
variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
open YangMills.Construction.MeasureUniqueness (fourierExp laplaceExp)
theorem fourierExp_comp_univ (v : Fin 1 → ℝ) :
    fourierExp v ∘ (MeasurableEquiv.Set.univ (Fin 1 → ℝ)) = expIFn (v 0) := by
  funext y
  have h₁ : MeasurableEquiv.Set.univ (Fin 1 → ℝ) y = y.1 := rfl
  simp only [Function.comp_apply, h₁, fourierExp, expIFn]
  congr 1
  simp [dotProduct]
  ring
theorem separates_line (hF : SetFunctions.ComplexMeasureFacts)
    (hM : MeasureUniqueness.UniquenessAndIntegral) :
    SeparatesComplexMeasures (Set.range fun v : Fin 1 → ℝ =>
      fourierExp v ∘ (MeasurableEquiv.Set.univ (Fin 1 → ℝ))) := by
  obtain ⟨-, -, -, ⟨hFour, -⟩, hInd, -⟩ := hM
  refine separates_of_measurableEquiv hF (MeasurableEquiv.Set.univ (Fin 1 → ℝ))
    (hInd 1 le_rfl univ MeasurableSet.univ).2 (fun v => fourierExp v) (fun v => ?_)
    (fun ν hν => hFour 1 le_rfl ν hν)
  refine ⟨?_, 1, fun q => ?_⟩
  · unfold fourierExp
    fun_prop
  · have : Complex.I * ((v ⬝ᵥ q : ℝ) : ℂ) = ((v ⬝ᵥ q : ℝ) : ℂ) * Complex.I := mul_comm _ _
    rw [fourierExp, this, Complex.norm_exp_ofReal_mul_I]
theorem eq_of_integralOp_expIFn (hF : SetFunctions.ComplexMeasureFacts)
    (hM : MeasureUniqueness.UniquenessAndIntegral)
    (hU : SpectralFromScalar.ScalarDeterminationTheorem)
    (E E' : SpectralMeasure RealLineSet H)
    (h : ∀ s, E.integralOp (expIFn s) = E'.integralOp (expIFn s)) :
    E = E' := by
  have hb : AllBoundedMeasurable (Set.range fun v : Fin 1 → ℝ =>
      fourierExp v ∘ (MeasurableEquiv.Set.univ (Fin 1 → ℝ))) := by
    rintro _ ⟨v, rfl⟩
    simp only [fourierExp_comp_univ]
    exact ⟨measurable_expIFn _, isBoundedFn_expIFn _⟩
  refine (hU H 1 le_rfl univ MeasurableSet.univ ⟨fun _ => 0, mem_univ _⟩ _ hb
    (separates_line hF hM)).1 E E' ?_
  rintro _ ⟨v, rfl⟩
  simp only [fourierExp_comp_univ]
  exact h _
theorem eq_of_spectralIntegralOp_coordVar (hC : SpectralMeasureCalculus.CalculusTheorem)
    (hF : SetFunctions.ComplexMeasureFacts)
    (hM : MeasureUniqueness.UniquenessAndIntegral)
    (hU : SpectralFromScalar.ScalarDeterminationTheorem)
    (E E' : SpectralMeasure RealLineSet H)
    (h : spectralIntegralOp E' coordVar = spectralIntegralOp E coordVar) : E' = E := by
  obtain ⟨-, hB, hA, hP, -⟩ := hC H 1 univ E
  obtain ⟨-, hB', hA', hP', -⟩ := hC H 1 univ E'
  have iA : IsSpectralIntegralOf (spectralIntegralOp E coordVar) E coordVar :=
    hA.isIntegralOf _ measurable_coordVar
  have iA' : IsSpectralIntegralOf (spectralIntegralOp E coordVar) E' coordVar :=
    h ▸ hA'.isIntegralOf _ measurable_coordVar
  generalize spectralIntegralOp E coordVar = A at iA iA'
  have hconj : conjFn (coordVar : RealLineSet → ℂ) = coordVar :=
    funext fun y => by simp [conjFn, coordVar]
  have hsym : ∀ φ ψ : A.domain, ⟪(φ : H), A ψ⟫_ℂ = ⟪A φ, (ψ : H)⟫_ℂ := by
    intro φ ψ
    have h₁ := hA.inner_conjugate coordVar measurable_coordVar φ ((iA.1 φ).1 φ.2) ψ
      ((iA.1 ψ).1 ψ.2)
    rw [hconj] at h₁
    rw [iA.2, iA.2]
    exact h₁
  have hzero : ∀ ψ ∈ A.domain, ∀ s, E.integralOp (expIFn s) ψ =
      E'.integralOp (expIFn s) ψ := by
    intro ψ hψ s
    have m : ψ ∈ E.integralDom coordVar := (iA.1 ψ).1 hψ
    have m' : ψ ∈ E'.integralDom coordVar := (iA'.1 ψ).1 hψ
    have hu : ∀ s, E.integralOp (expIFn s) ψ ∈ A.domain := fun s =>
      (iA.1 _).2 (integralOp_expIFn_mem hP s m)
    have hu' : ∀ s, E'.integralOp (expIFn s) ψ ∈ A.domain := fun s =>
      (iA'.1 _).2 (integralOp_expIFn_mem hP' s m')
    have hδm : ∀ s, E.integralOp (expIFn s) ψ -
        E'.integralOp (expIFn s) ψ ∈ A.domain := fun s =>
      A.domain.sub_mem (hu s) (hu' s)
    have hd : ∀ s, HasDerivAt (fun s => E.integralOp (expIFn s) ψ -
        E'.integralOp (expIFn s) ψ) (Complex.I • A ⟨_, hδm s⟩) s := by
      intro s
      have d := hasDerivAt_integralOp_expIFn hB hA hP m s
      have d' := hasDerivAt_integralOp_expIFn hB' hA' hP' m' s
      have hv : A ⟨_, hδm s⟩ = E.integralApply coordVar
          (E.integralOp (expIFn s) ψ) - E'.integralApply coordVar
          (E'.integralOp (expIFn s) ψ) := by
        have h₁ : (⟨_, hδm s⟩ : A.domain) = ⟨_, hu s⟩ - ⟨_, hu' s⟩ := rfl
        rw [h₁, LinearPMap.map_sub, iA.2, iA'.2]
      rw [hv, smul_sub]
      exact d.sub d'
    have hf : ∀ s, HasDerivAt (fun s => ⟪E.integralOp (expIFn s) ψ -
        E'.integralOp (expIFn s) ψ, E.integralOp (expIFn s) ψ -
        E'.integralOp (expIFn s) ψ⟫_ℂ) 0 s := by
      intro s
      have h₁ := (hd s).inner ℂ (hd s)
      have h₂ := hsym ⟨_, hδm s⟩ ⟨_, hδm s⟩
      simp only at h₂
      have key : ∀ a b : H, ⟪a, b⟫_ℂ = ⟪b, a⟫_ℂ →
          ⟪a, Complex.I • b⟫_ℂ + ⟪Complex.I • b, a⟫_ℂ = 0 := by
        intro a b hab
        rw [inner_smul_right, inner_smul_left, hab]
        simp
      rw [key _ _ h₂] at h₁
      exact h₁
    have hconst := is_const_of_deriv_eq_zero (fun s => (hf s).differentiableAt)
      (fun s => (hf s).deriv) s 0
    have h0 : E.integralOp (expIFn 0) ψ - E'.integralOp (expIFn 0) ψ
        = 0 := by
      rw [expIFn_zero, integralOp_one hB, integralOp_one hB', sub_self]
    simp only [h0, inner_zero_left] at hconst
    exact sub_eq_zero.mp (inner_self_eq_zero.mp hconst)
  have hd : Dense (A.domain : Set H) := by
    have h₁ := hA.dense_domain _ measurable_coordVar
    have h₂ : (A.domain : Set H) = E.integralDom coordVar := by
      ext ψ
      exact iA.1 ψ
    rwa [h₂]
  refine (eq_of_integralOp_expIFn hF hM hU E E' fun s => ?_).symm
  exact DFunLike.coe_injective (Continuous.ext_on hd (map_continuous _) (map_continuous _)
    fun ψ hψ => hzero ψ hψ s)
theorem isSpectralMeasureFor_spectralMeasure {A : UnboundedOp H} (hA : IsDiagonalized A) :
    IsSpectralMeasureFor (spectralMeasure A) A := by
  unfold spectralMeasure
  exact Classical.epsilon_spec hA
theorem spectralMeasure_eq_of_isSpectralMeasureFor
    (hC : SpectralMeasureCalculus.CalculusTheorem)
    (hF : SetFunctions.ComplexMeasureFacts)
    (hM : MeasureUniqueness.UniquenessAndIntegral)
    (hU : SpectralFromScalar.ScalarDeterminationTheorem)
    {A : UnboundedOp H} {E : SpectralMeasure RealLineSet H} (hE : IsSpectralMeasureFor E A) :
    spectralMeasure A = E := by
  obtain ⟨-, -, hA₁, -⟩ := hC H 1 univ E
  obtain ⟨-, -, hA₂, -⟩ := hC H 1 univ (spectralMeasure A)
  have hs : IsSpectralMeasureFor (spectralMeasure A) A := by
    unfold spectralMeasure
    exact Classical.epsilon_spec (p := fun E => IsSpectralMeasureFor E A) ⟨E, hE⟩
  refine eq_of_spectralIntegralOp_coordVar hC hF hM hU E _ ?_
  rw [← eq_spectralIntegralOp hA₁ measurable_coordVar hE,
    ← eq_spectralIntegralOp hA₂ measurable_coordVar hs]
theorem apply_congr {n : ℕ} {Y : Set (Fin n → ℝ)} (E : SpectralMeasure Y H)
    {Δ Δ' : BorelSubsets Y} (h : Δ.1 = Δ'.1) : E Δ = E Δ' :=
  congrArg _ (Subtype.ext h)
theorem isCarriedBy_univ {n : ℕ} {Y : Set (Fin n → ℝ)} (E : SpectralMeasure Y H) :
    E.IsCarriedBy ⟨univ, MeasurableSet.univ⟩ :=
  (apply_congr E compl_univ).trans E.apply_empty
theorem norm_integralOp_le {n : ℕ} {Y : Set (Fin n → ℝ)} {E : SpectralMeasure Y H}
    (hB : BoundedCalculusLaws E) {g : Y → ℂ} (hg : Measurable g) {c : ℝ} (hc₀ : 0 ≤ c)
    (hc : ∀ y, ‖g y‖ ≤ c) : ‖E.integralOp g‖ ≤ c :=
  (hB.norm_le g _ hg ⟨c, hc⟩ (isCarriedBy_univ E)).trans (Real.iSup_le (fun y => hc y) hc₀)
def nonnegHalfLine : BorelSubsets ℝ := ⟨Ici 0, measurableSet_Ici⟩
theorem isCarriedBy_nonneg_of_neg {E : SpectralMeasure RealLineSet H}
    (h : E (realLineSet negHalfLine) = 0) : E.IsCarriedBy (realLineSet nonnegHalfLine) := by
  refine (apply_congr E ?_).trans h
  ext y
  simp [realLineSet, nonnegHalfLine, negHalfLine]
def negBand (k : ℕ) : BorelSubsets RealLineSet :=
  realLineSet ⟨Icc (-((k : ℝ) + 1)) (-((k : ℝ) + 1)⁻¹), measurableSet_Icc⟩
theorem apply_negBand {E : SpectralMeasure RealLineSet H} (hA : UnboundedCalculusLaws E)
    (hP : ProductLaws E) {ψ₀ : H} (k : ℕ) (hn : ∀ ψ ∈ E.integralDom coordVar,
      0 ≤ ⟪ψ, E.integralApply coordVar ψ⟫_ℂ) : E (negBand k) ψ₀ = 0 := by
  set χ := E (negBand k) ψ₀ with hχ
  have hnull : E.diagMeasure χ (negBand k).1ᶜ = 0 := by
    have h₁ := hP.real_value ψ₀ (negBand k) ⟨(negBand k).1ᶜ, (negBand k).2.compl⟩
    have h₂ : (negBand k).1 ∩ (negBand k).1ᶜ = ∅ := inter_compl_self _
    simp only [h₂, measureReal_empty] at h₁
    exact (measureReal_eq_zero_iff).mp h₁
  have hae : ∀ᵐ y ∂E.diagMeasure χ, y ∈ (negBand k).1 := by
    rw [ae_iff]
    exact hnull
  have hmem : χ ∈ E.integralDom coordVar := by
    have hle : ∀ᵐ y ∂E.diagMeasure χ, ‖coordVar y‖ₑ ^ 2 ≤ ENNReal.ofReal ((k : ℝ) + 1) ^ 2 := by
      filter_upwards [hae] with y hy
      obtain ⟨h₁, h₂⟩ : -((k : ℝ) + 1) ≤ y.1 0 ∧ y.1 0 ≤ -((k : ℝ) + 1)⁻¹ := hy
      gcongr
      rw [← ofReal_norm]
      refine ENNReal.ofReal_le_ofReal ?_
      have : ((k : ℝ) + 1)⁻¹ > 0 := by positivity
      simp only [coordVar, Complex.norm_real, Real.norm_eq_abs]
      rw [abs_le]
      constructor <;> linarith
    refine (lintegral_mono_ae hle).trans_lt ?_
    rw [lintegral_const]
    exact ENNReal.mul_lt_top (by simp) (measure_lt_top _ _)
  have h₀ := hn χ hmem
  rw [hA.inner_self _ measurable_coordVar χ hmem] at h₀
  have hint := hA.integrable _ measurable_coordVar χ hmem
  have hreal : Integrable (fun y : RealLineSet => y.1 0) (E.diagMeasure χ) := by
    have := hint.re
    simpa [coordVar] using this
  have hcast : ∫ y, coordVar y ∂E.diagMeasure χ =
      ((∫ y : RealLineSet, y.1 0 ∂E.diagMeasure χ : ℝ) : ℂ) := integral_ofReal
  rw [hcast, Complex.zero_le_real] at h₀
  have hupper : ∫ y : RealLineSet, y.1 0 ∂E.diagMeasure χ ≤
      ∫ _ : RealLineSet, -((k : ℝ) + 1)⁻¹ ∂E.diagMeasure χ := by
    refine integral_mono_ae hreal (integrable_const _) ?_
    filter_upwards [hae] with y hy
    exact hy.2
  rw [integral_const, smul_eq_mul] at hupper
  have hmass : (E.diagMeasure χ).real univ = ‖χ‖ ^ 2 := by
    simp only [Measure.real, diagMeasure_univ]
    exact ENNReal.toReal_ofReal (by positivity)
  rw [show (E.diagMeasure χ).real univ = ‖χ‖ ^ 2 from hmass] at hupper
  have hpos : ((k : ℝ) + 1)⁻¹ > 0 := by positivity
  have hsq : ‖χ‖ ^ 2 ≤ 0 := by
    by_contra hc
    have : 0 < ‖χ‖ ^ 2 := not_le.mp hc
    nlinarith
  have : ‖χ‖ = 0 := by
    have := le_antisymm hsq (by positivity)
    exact pow_eq_zero_iff (by norm_num) |>.mp this
  exact norm_eq_zero.mp this
theorem nonnegIffNegHalfLineNull_holds (hC : SpectralMeasureCalculus.CalculusTheorem) :
    NonnegIffNegHalfLineNull H := by
  intro A hres
  have hs := isSpectralMeasureFor_spectralMeasure hres
  generalize spectralMeasure A = E at hs ⊢
  obtain ⟨hMs, -, hA, hP, -, -, hR, -⟩ := hC H 1 univ E
  constructor
  · intro hnn
    have hn : ∀ ψ ∈ E.integralDom coordVar,
        0 ≤ ⟪ψ, E.integralApply coordVar ψ⟫_ℂ := by
      intro ψ hψ
      have h₁ := hnn ⟨ψ, (hs.1 ψ).2 hψ⟩
      rwa [hs.2] at h₁
    have hz : E ⟨⋃ k, (negBand k).1, MeasurableSet.iUnion fun k => (negBand k).2⟩ = 0 :=
      hMs.value_iUnion ℕ negBand fun k => by
        ext ψ
        exact apply_negBand hA hP k hn
    refine (apply_congr E ?_).trans hz
    ext y
    simp only [realLineSet, negHalfLine, mem_ofPred_eq, mem_Iio, negBand, mem_iUnion, mem_Icc]
    constructor
    · intro hy
      obtain ⟨k₁, hk₁⟩ := exists_nat_gt (-(y.1 0))
      obtain ⟨k₂, hk₂⟩ := exists_nat_gt (-(y.1 0))⁻¹
      have hpos : 0 < -(y.1 0) := by linarith
      refine ⟨max k₁ k₂, ?_, ?_⟩
      · have : (k₁ : ℝ) ≤ (max k₁ k₂ : ℕ) := by exact_mod_cast le_max_left _ _
        linarith
      · have h₂ : (k₂ : ℝ) ≤ (max k₁ k₂ : ℕ) := by exact_mod_cast le_max_right _ _
        have h₃ : (-(y.1 0))⁻¹ < ((max k₁ k₂ : ℕ) : ℝ) + 1 := by linarith
        have h₄ := inv_lt_of_inv_lt₀ hpos h₃
        linarith
    · rintro ⟨k, -, hk⟩
      have : ((k : ℝ) + 1)⁻¹ > 0 := by positivity
      linarith
  · intro hz
    have h₁ := hR.isNonnegative coordVar (realLineSet nonnegHalfLine) measurable_coordVar
      (fun y => by simp [coordVar]) (isCarriedBy_nonneg_of_neg hz) (fun y hy => by
        have h₂ : 0 ≤ y.1 0 := hy
        simpa [coordVar] using h₂)
    rwa [← eq_spectralIntegralOp hA measurable_coordVar hs] at h₁
end SpectralMeasureUniqueness
section ExponentialFamilies
variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
theorem conjFn_expIFn (s : ℝ) :
    conjFn (expIFn s) = expIFn (-s) := by
  funext y
  simp only [conjFn, expIFn, ← Complex.exp_conj]
  congr 1
  simp
theorem isBoundedAdjoint_star {B : H →L[ℂ] H} : IsBoundedAdjoint (star B) B := fun φ ψ => by
  rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_left]
theorem expIFormsUnitaryGroup_holds (hC : SpectralMeasureCalculus.CalculusTheorem) :
    ExpIFormsUnitaryGroup H := by
  intro B _
  obtain ⟨-, hB, -⟩ := hC H 1 univ (spectralMeasure B)
  have hU : ∀ s, expI B s =
      (spectralMeasure B).integralOp (expIFn s) := fun s => rfl
  generalize spectralMeasure B = E at hB hU
  have hadj : ∀ s, IsBoundedAdjoint (expI B (-s)) (expI B s) := by
    intro s
    rw [hU, hU, ← conjFn_expIFn, hB.conjugate _ (measurable_expIFn s)
      (isBoundedFn_expIFn s)]
    exact isBoundedAdjoint_star
  have hmul : ∀ s t, expI B s * expI B t =
      expI B (s + t) := by
    intro s t
    rw [hU, hU, hU, expIFn_add, hB.mul _ _ (measurable_expIFn s)
      (isBoundedFn_expIFn s) (measurable_expIFn t) (isBoundedFn_expIFn t)]
  have hone : expI B 0 = 1 := by
    rw [hU, expIFn_zero, integralOp_one hB]
  have happ : ∀ s t ψ, expI B s (expI B t ψ) =
      expI B (s + t) ψ := fun s t ψ => by
    rw [← hmul]
    rfl
  have hinv : ∀ s ψ, expI B (-s) (expI B s ψ) = ψ := fun s ψ => by
    rw [happ, neg_add_cancel, hone]
    rfl
  have hinv' : ∀ s ψ, expI B s (expI B (-s) ψ) = ψ := fun s ψ => by
    rw [happ, add_neg_cancel, hone]
    rfl
  refine ⟨⟨fun s => ⟨?_, ?_⟩, ?_, ?_, ?_⟩, hadj⟩
  · exact Function.bijective_iff_has_inverse.mpr
      ⟨expI B (-s), hinv s, hinv' s⟩
  · intro φ ψ
    have h₁ := hadj s (expI B s φ) ψ
    simp only [ContinuousLinearMap.coe_coe]
    rw [h₁, hinv]
  · ext ψ
    simp [hone]
  · intro s s'
    ext ψ
    simp only [LinearMap.comp_apply, ContinuousLinearMap.coe_coe]
    exact happ s s' ψ
  · intro ψ
    simp only [ContinuousLinearMap.coe_coe]
    refine continuous_iff_seqContinuous.mpr fun x p hx => ?_
    rw [hU]
    have h₁ := hB.tendsto (fun k => expIFn (x k)) (expIFn p) 1
      ⟨univ, MeasurableSet.univ⟩ (fun k => measurable_expIFn _)
      (measurable_expIFn _) (fun k y => (norm_expIFn _ y).le)
      (fun y => (norm_expIFn _ y).le) (isCarriedBy_univ E) (fun y _ => ?_) ψ
    · simpa only [Function.comp_def, hU] using h₁
    · have hc : Continuous fun s : ℝ => expIFn s y := by
        unfold expIFn
        fun_prop
      exact (hc.tendsto p).comp hx
def expDecayFn (ζ : ℂ) (y : RealLineSet) : ℂ :=
  (Ici (0 : ℝ)).indicator (fun x => Complex.exp (-ζ * (x : ℂ))) (y.1 0)
theorem measurable_expDecayFn (ζ : ℂ) : Measurable (expDecayFn ζ) := by
  have h₁ : Measurable ((Ici (0 : ℝ)).indicator fun x : ℝ => Complex.exp (-ζ * (x : ℂ))) :=
    (by fun_prop : Measurable fun x : ℝ => Complex.exp (-ζ * (x : ℂ))).indicator measurableSet_Ici
  exact h₁.comp measurable_coord
theorem norm_expDecayFn_le {ζ : ℂ} (hζ : 0 ≤ ζ.re) (y : RealLineSet) :
    ‖expDecayFn ζ y‖ ≤ 1 := by
  unfold expDecayFn
  by_cases hy : y.1 0 ∈ Ici (0 : ℝ)
  · rw [indicator_of_mem hy, Complex.norm_exp]
    have h₂ : 0 ≤ y.1 0 := hy
    have : (-ζ * ((y.1 0 : ℝ) : ℂ)).re = -(ζ.re * y.1 0) := by simp
    rw [this, Real.exp_le_one_iff]
    have := mul_nonneg hζ h₂
    linarith
  · rw [indicator_of_notMem hy]
    simp
theorem isBoundedFn_expDecayFn {ζ : ℂ} (hζ : 0 ≤ ζ.re) : IsBoundedFn (expDecayFn ζ) :=
  ⟨1, norm_expDecayFn_le hζ⟩
theorem expDecayFn_add (ζ ζ' : ℂ) :
    expDecayFn (ζ + ζ') = expDecayFn ζ * expDecayFn ζ' := by
  funext y
  simp only [expDecayFn, Pi.mul_apply]
  by_cases hy : y.1 0 ∈ Ici (0 : ℝ)
  · simp only [indicator_of_mem hy, ← Complex.exp_add]
    congr 1
    ring
  · simp only [indicator_of_notMem hy, zero_mul]
theorem conjFn_expDecayFn (ζ : ℂ) :
    conjFn (expDecayFn ζ) = expDecayFn (conj ζ) := by
  funext y
  simp only [conjFn, expDecayFn]
  by_cases hy : y.1 0 ∈ Ici (0 : ℝ)
  · simp only [indicator_of_mem hy, ← Complex.exp_conj]
    congr 1
    simp
  · simp only [indicator_of_notMem hy, map_zero]
theorem expDecayFn_zero_apply (y : RealLineSet) (hy : y ∈ (realLineSet nonnegHalfLine).1) :
    expDecayFn 0 y = 1 := by
  have h₁ : y.1 0 ∈ Ici (0 : ℝ) := hy
  simp [expDecayFn, indicator_of_mem h₁]
theorem continuous_expDecayFn (y : RealLineSet) : Continuous fun ζ => expDecayFn ζ y := by
  unfold expDecayFn
  by_cases hy : y.1 0 ∈ Ici (0 : ℝ)
  · simp only [indicator_of_mem hy]
    fun_prop
  · simp only [indicator_of_notMem hy]
    exact continuous_const
theorem integralOp_expDecayFn_zero {E : SpectralMeasure RealLineSet H}
    (hB : BoundedCalculusLaws E) (hc : E.IsCarriedBy (realLineSet nonnegHalfLine)) :
    E.integralOp (expDecayFn 0) = 1 := by
  rw [hB.congr _ (fun _ => 1) (realLineSet nonnegHalfLine) (measurable_expDecayFn 0)
    (isBoundedFn_expDecayFn (by simp)) measurable_const ⟨1, fun _ => by simp⟩ hc
    expDecayFn_zero_apply, integralOp_one hB]
theorem expComplex_props_of_nonneg (hC : SpectralMeasureCalculus.CalculusTheorem)
    {A : UnboundedOp H} (hres : IsDiagonalized A)
    (hnn : OperatorTransport.IsNonnegUnbounded A) :
    (∀ ζ ∈ rightClosedHalfPlane, IsContraction (expComplex A ζ)) ∧
    (∀ ζ ∈ rightClosedHalfPlane, ∀ ζ' ∈ rightClosedHalfPlane,
      expComplex A ζ * expComplex A ζ' = expComplex A (ζ + ζ')) ∧
    (∀ ζ ∈ rightClosedHalfPlane, IsBoundedAdjoint (expComplex A (conj ζ)) (expComplex A ζ)) ∧
    expComplex A 0 = 1 ∧
    (∀ ψ : H, ContinuousOn (fun ζ => expComplex A ζ ψ) rightClosedHalfPlane) ∧
    IsContractionSemigroup (fun t : ℝ≥0 => expComplex A ((t : ℝ) : ℂ)) := by
  have hz := (nonnegIffNegHalfLineNull_holds hC A hres).mp hnn
  have hc := isCarriedBy_nonneg_of_neg hz
  obtain ⟨-, hB, -⟩ := hC H 1 univ (spectralMeasure A)
  have hU : ∀ ζ, expComplex A ζ = (spectralMeasure A).integralOp (expDecayFn ζ) :=
    fun ζ => rfl
  generalize spectralMeasure A = E at hB hU hc
  have hcon : ∀ ζ ∈ rightClosedHalfPlane, IsContraction (expComplex A ζ) := fun ζ hζ => by
    rw [hU]
    exact norm_integralOp_le hB (measurable_expDecayFn ζ) zero_le_one
      (norm_expDecayFn_le hζ)
  have hmul : ∀ ζ ∈ rightClosedHalfPlane, ∀ ζ' ∈ rightClosedHalfPlane,
      expComplex A ζ * expComplex A ζ' = expComplex A (ζ + ζ') := fun ζ hζ ζ' hζ' => by
    rw [hU, hU, hU, expDecayFn_add, hB.mul _ _ (measurable_expDecayFn ζ)
      (isBoundedFn_expDecayFn hζ) (measurable_expDecayFn ζ') (isBoundedFn_expDecayFn hζ')]
  have hadj : ∀ ζ ∈ rightClosedHalfPlane,
      IsBoundedAdjoint (expComplex A (conj ζ)) (expComplex A ζ) :=
    fun ζ hζ => by
      rw [hU, hU, ← conjFn_expDecayFn, hB.conjugate _ (measurable_expDecayFn ζ)
        (isBoundedFn_expDecayFn hζ)]
      exact isBoundedAdjoint_star
  have hone : expComplex A 0 = 1 := by
    rw [hU]
    exact integralOp_expDecayFn_zero hB hc
  have hcont : ∀ ψ : H, ContinuousOn (fun ζ => expComplex A ζ ψ) rightClosedHalfPlane := by
    intro ψ
    refine continuousOn_iff_continuous_domRestrict.mpr ?_
    refine continuous_iff_seqContinuous.mpr fun x p hx => ?_
    have h₁ := hB.tendsto (fun k => expDecayFn (x k).1) (expDecayFn p.1) 1
      ⟨univ, MeasurableSet.univ⟩ (fun k => measurable_expDecayFn _)
      (measurable_expDecayFn _) (fun k y => norm_expDecayFn_le (x k).2 y)
      (norm_expDecayFn_le p.2) (isCarriedBy_univ E) (fun y _ =>
        ((continuous_expDecayFn y).tendsto p.1).comp
          ((continuous_subtype_val.tendsto p).comp hx)) ψ
    simpa only [Function.comp_def, domRestrict_apply, hU] using h₁
  refine ⟨hcon, hmul, hadj, hone, hcont, ?_⟩
  have hreal : ∀ t : ℝ≥0, ((t : ℝ) : ℂ) ∈ rightClosedHalfPlane := fun t => by
    simp [rightClosedHalfPlane]
  refine ⟨fun t => ?_, fun t => hcon _ (hreal t), ?_, fun t t' => ?_, fun ψ => ?_⟩
  · have h₁ := hadj _ (hreal t)
    rw [Complex.conj_ofReal] at h₁
    exact h₁
  · simpa using hone
  · rw [hmul _ (hreal t) _ (hreal t')]
    simp
  · have h₁ := hcont ψ
    have h₂ : Continuous fun t : ℝ≥0 => ((t : ℝ) : ℂ) := by fun_prop
    exact h₁.comp_continuous h₂ hreal
end ExponentialFamilies
section Analyticity
variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
def taylorCoeffFn (ζ : ℂ) (k : ℕ) (y : RealLineSet) : ℂ :=
  (Ici (0 : ℝ)).indicator
    (fun x => (-(x : ℂ)) ^ k / (k.factorial : ℂ) * Complex.exp (-ζ * (x : ℂ))) (y.1 0)
def taylorPartialFn (ζ u : ℂ) (p : ℕ) (y : RealLineSet) : ℂ :=
  ∑ k ∈ Finset.range p, u ^ k * taylorCoeffFn ζ k y
theorem measurable_taylorCoeffFn (ζ : ℂ) (k : ℕ) : Measurable (taylorCoeffFn ζ k) := by
  have h₁ : Measurable ((Ici (0 : ℝ)).indicator fun x : ℝ =>
      (-(x : ℂ)) ^ k / (k.factorial : ℂ) * Complex.exp (-ζ * (x : ℂ))) :=
    (by fun_prop : Measurable fun x : ℝ =>
      (-(x : ℂ)) ^ k / (k.factorial : ℂ) * Complex.exp (-ζ * (x : ℂ))).indicator measurableSet_Ici
  exact h₁.comp measurable_coord
theorem norm_taylorCoeffFn_le {ζ : ℂ} (hr : 0 < ζ.re) (k : ℕ) (y : RealLineSet) :
    ‖taylorCoeffFn ζ k y‖ ≤ ζ.re⁻¹ ^ k := by
  unfold taylorCoeffFn
  by_cases hy : y.1 0 ∈ Ici (0 : ℝ)
  · have hx : 0 ≤ y.1 0 := hy
    rw [indicator_of_mem hy]
    generalize y.1 0 = x at hx
    have h₁ : ‖(-(x : ℂ)) ^ k / (k.factorial : ℂ) * Complex.exp (-ζ * (x : ℂ))‖ =
        x ^ k / k.factorial * Real.exp (-(ζ.re * x)) := by
      rw [norm_mul, norm_div, norm_pow, norm_neg, Complex.norm_real, Real.norm_of_nonneg hx,
        Complex.norm_natCast, Complex.norm_exp]
      simp
    rw [h₁]
    have h₂ := Real.pow_div_factorial_le_exp (x := ζ.re * x) (by positivity) k
    have h₃ : x ^ k / k.factorial * Real.exp (-(ζ.re * x)) =
        ζ.re⁻¹ ^ k * ((ζ.re * x) ^ k / k.factorial * Real.exp (-(ζ.re * x))) := by
      rw [mul_pow, ← mul_assoc, mul_div_assoc', ← mul_assoc, ← mul_pow,
        inv_mul_cancel₀ hr.ne', one_pow, one_mul]
    rw [h₃]
    have h₄ : (ζ.re * x) ^ k / k.factorial * Real.exp (-(ζ.re * x)) ≤ 1 := by
      calc _ ≤ Real.exp (ζ.re * x) * Real.exp (-(ζ.re * x)) := by gcongr
        _ = 1 := by rw [← Real.exp_add]; simp
    have h₅ : 0 ≤ ζ.re⁻¹ ^ k := by positivity
    nlinarith
  · rw [indicator_of_notMem hy, norm_zero]
    positivity
theorem norm_mul_taylorCoeffFn_le {ζ u : ℂ} (hr : 0 < ζ.re) (hu : ‖u‖ ≤ ζ.re / 2) (k : ℕ)
    (y : RealLineSet) : ‖u ^ k * taylorCoeffFn ζ k y‖ ≤ (1 / 2 : ℝ) ^ k := by
  rw [norm_mul, norm_pow]
  calc ‖u‖ ^ k * ‖taylorCoeffFn ζ k y‖ ≤ (ζ.re / 2) ^ k * ζ.re⁻¹ ^ k := by
        have := norm_taylorCoeffFn_le hr k y
        gcongr
    _ = (1 / 2 : ℝ) ^ k := by
        rw [← mul_pow]
        congr 1
        field_simp
theorem measurable_taylorPartialFn (ζ u : ℂ) (p : ℕ) : Measurable (taylorPartialFn ζ u p) := by
  unfold taylorPartialFn
  exact Finset.measurable_fun_sum _ fun k _ => measurable_const.mul (measurable_taylorCoeffFn ζ k)
theorem norm_taylorPartialFn_le {ζ u : ℂ} (hr : 0 < ζ.re) (hu : ‖u‖ ≤ ζ.re / 2) (p : ℕ)
    (y : RealLineSet) : ‖taylorPartialFn ζ u p y‖ ≤ 2 :=
  (norm_sum_le _ _).trans ((Finset.sum_le_sum fun k _ =>
    norm_mul_taylorCoeffFn_le hr hu k y).trans (sum_geometric_two_le p))
theorem tendsto_taylorPartialFn (ζ u : ℂ) (y : RealLineSet) :
    Tendsto (fun p => taylorPartialFn ζ u p y) atTop (𝓝 (expDecayFn (ζ + u) y)) := by
  by_cases hy : y.1 0 ∈ Ici (0 : ℝ)
  · have hs := (NormedSpace.expSeries_div_hasSum_exp (-u * ((y.1 0 : ℝ) : ℂ))).mul_right
      (Complex.exp (-ζ * ((y.1 0 : ℝ) : ℂ)))
    rw [← Complex.exp_eq_exp_ℂ, ← Complex.exp_add] at hs
    have h₁ : expDecayFn (ζ + u) y =
        Complex.exp (-u * ((y.1 0 : ℝ) : ℂ) + -ζ * ((y.1 0 : ℝ) : ℂ)) := by
      simp only [expDecayFn, indicator_of_mem hy]
      congr 1
      ring
    rw [h₁]
    refine hs.tendsto_sum_nat.congr fun p => ?_
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [taylorCoeffFn, indicator_of_mem hy]
    rw [show -u * ((y.1 0 : ℝ) : ℂ) = u * (-((y.1 0 : ℝ) : ℂ)) by ring, mul_pow]
    ring
  · have h₁ : expDecayFn (ζ + u) y = 0 := by
      simp only [expDecayFn, indicator_of_notMem hy]
    rw [h₁]
    refine tendsto_const_nhds.congr fun p => ?_
    simp [taylorPartialFn, taylorCoeffFn, indicator_of_notMem hy]
theorem integralOp_taylorPartialFn {E : SpectralMeasure RealLineSet H}
    (hB : BoundedCalculusLaws E) {ζ u : ℂ} (hr : 0 < ζ.re) (hu : ‖u‖ ≤ ζ.re / 2) (p : ℕ) :
    E.integralOp (taylorPartialFn ζ u p) =
      ∑ k ∈ Finset.range p, u ^ k • E.integralOp (taylorCoeffFn ζ k) := by
  have hbt : ∀ k, IsBoundedFn (taylorCoeffFn ζ k) := fun k =>
    ⟨_, norm_taylorCoeffFn_le hr k⟩
  have hbp : ∀ p, IsBoundedFn (taylorPartialFn ζ u p) := fun p =>
    ⟨2, norm_taylorPartialFn_le hr hu p⟩
  induction p with
  | zero =>
    have h₁ : taylorPartialFn ζ u 0 = (0 : ℂ) • fun _ => 1 := by
      funext y
      simp [taylorPartialFn]
    rw [h₁, hB.smul _ _ measurable_const ⟨1, fun _ => by simp⟩]
    simp
  | succ p ih =>
    have h₁ : taylorPartialFn ζ u (p + 1) =
        taylorPartialFn ζ u p + u ^ p • taylorCoeffFn ζ p := by
      funext y
      simp [taylorPartialFn, Finset.sum_range_succ]
    have hb₂ : IsBoundedFn (u ^ p • taylorCoeffFn ζ p) :=
      ⟨_, fun y => norm_mul_taylorCoeffFn_le hr hu p y⟩
    rw [h₁, hB.add _ _ (measurable_taylorPartialFn ζ u p) (hbp p)
      ((measurable_taylorCoeffFn ζ p).const_smul _) hb₂,
      hB.smul _ _ (measurable_taylorCoeffFn ζ p) (hbt p), ih, Finset.sum_range_succ]
theorem hasSum_integralOp_expDecayFn {E : SpectralMeasure RealLineSet H}
    (hB : BoundedCalculusLaws E) {ζ u : ℂ}
    (hr : 0 < ζ.re) (hu : ‖u‖ ≤ ζ.re / 2) :
    HasSum (fun k => u ^ k • E.integralOp (taylorCoeffFn ζ k))
      (E.integralOp (expDecayFn (ζ + u))) := by
  have hnorm : ∀ k, ‖u ^ k • E.integralOp (taylorCoeffFn ζ k)‖ ≤ (1 / 2 : ℝ) ^ k := by
    intro k
    rw [norm_smul, norm_pow]
    have h₁ := norm_integralOp_le hB (measurable_taylorCoeffFn ζ k) (by positivity)
      (norm_taylorCoeffFn_le hr k)
    calc ‖u‖ ^ k * ‖E.integralOp (taylorCoeffFn ζ k)‖ ≤ (ζ.re / 2) ^ k * ζ.re⁻¹ ^ k := by
          gcongr
      _ = (1 / 2 : ℝ) ^ k := by
          rw [← mul_pow]
          congr 1
          field_simp
  have hsum : Summable fun k => u ^ k • E.integralOp (taylorCoeffFn ζ k) :=
    Summable.of_norm_bounded summable_geometric_two hnorm
  have hT := hsum.hasSum
  have hre : 0 ≤ (ζ + u).re := by
    have h₁ : |u.re| ≤ ‖u‖ := Complex.abs_re_le_norm u
    have h₂ := abs_le.mp h₁
    simp only [Complex.add_re]
    linarith
  have heq : ∑' k, u ^ k • E.integralOp (taylorCoeffFn ζ k) =
      E.integralOp (expDecayFn (ζ + u)) := by
    ext ψ
    have h₁ : Tendsto (fun p => (∑ k ∈ Finset.range p,
        u ^ k • E.integralOp (taylorCoeffFn ζ k)) ψ) atTop
        (𝓝 ((∑' k, u ^ k • E.integralOp (taylorCoeffFn ζ k)) ψ)) :=
      ((continuous_eval_const ψ).tendsto _).comp hT.tendsto_sum_nat
    have h₂ := hB.tendsto (taylorPartialFn ζ u) (expDecayFn (ζ + u)) 2
      ⟨univ, MeasurableSet.univ⟩ (measurable_taylorPartialFn ζ u) (measurable_expDecayFn _)
      (norm_taylorPartialFn_le hr hu)
      (fun y => (norm_expDecayFn_le hre y).trans (by norm_num)) (isCarriedBy_univ E)
      (fun y _ => tendsto_taylorPartialFn ζ u y) ψ
    refine tendsto_nhds_unique h₁ (h₂.congr fun p => ?_)
    rw [integralOp_taylorPartialFn hB hr hu p]
  rwa [heq] at hT
theorem isOperatorHolomorphicOn_expComplex (hC : SpectralMeasureCalculus.CalculusTheorem)
    (A : UnboundedOp H) :
    BanachValued.IsOperatorHolomorphicOn rightOpenHalfPlane
      (fun z : Coordinates.ComplexCoordinates 1 => expComplex A (z 0)) := by
  obtain ⟨-, hB, -⟩ := hC H 1 univ (spectralMeasure A)
  refine ⟨?_, Or.inl ⟨le_rfl, fun c hc => ?_⟩⟩
  · exact isOpen_lt continuous_const (by fun_prop)
  have hr : 0 < (c 0).re := hc
  have hnorm : ∀ k, ‖(spectralMeasure A).integralOp (taylorCoeffFn (c 0) k)‖ *
      ((c 0).re / 2) ^ k ≤ (1 / 2 : ℝ) ^ k := by
    intro k
    have h₁ := norm_integralOp_le hB (measurable_taylorCoeffFn (c 0) k) (by positivity)
      (norm_taylorCoeffFn_le hr k)
    calc _ ≤ (c 0).re⁻¹ ^ k * ((c 0).re / 2) ^ k := by gcongr
      _ = (1 / 2 : ℝ) ^ k := by
          rw [← mul_pow]
          congr 1
          field_simp
  have hsum : Summable fun k => ‖(spectralMeasure A).integralOp (taylorCoeffFn (c 0) k)‖ *
      ((c 0).re / 2) ^ k :=
    Summable.of_nonneg_of_le (fun k => by positivity) hnorm summable_geometric_two
  refine ⟨(c 0).re / 2, fun γ => (spectralMeasure A).integralOp (taylorCoeffFn (c 0) (γ 0)),
    ⟨by positivity, fun z hz => ?_, ?_, fun w hw => ?_⟩⟩
  · have h₁ : ‖(z - c) 0‖ ≤ ‖z - c‖ := norm_le_pi_norm (z - c) 0
    have h₂ : ‖z - c‖ ≤ (c 0).re / 2 := hz
    have h₃ : |((z - c) 0).re| ≤ ‖(z - c) 0‖ := Complex.abs_re_le_norm _
    have h₄ := abs_le.mp h₃
    have h₅ : ((z - c) 0).re = (z 0).re - (c 0).re := by simp
    show 0 < (z 0).re
    linarith [h₄.1]
  · refine ((Equiv.funUnique (Fin 1) ℕ).summable_iff.mpr hsum).congr fun γ => ?_
    simp [PowerSeries.MultiIndex.order]
  · have h₁ : ‖w 0‖ ≤ (c 0).re / 2 := (norm_le_pi_norm w 0).trans hw
    have h₂ := (Equiv.funUnique (Fin 1) ℕ).hasSum_iff.mpr (hasSum_integralOp_expDecayFn hB hr h₁)
    have h₃ : (fun γ : PowerSeries.MultiIndex 1 => PowerSeries.MultiIndex.monomial w γ •
        (spectralMeasure A).integralOp (taylorCoeffFn (c 0) (γ 0))) =
        (fun k => w 0 ^ k • (spectralMeasure A).integralOp (taylorCoeffFn (c 0) k)) ∘
          (Equiv.funUnique (Fin 1) ℕ) := by
      funext γ
      simp [PowerSeries.MultiIndex.monomial]
    rw [h₃]
    exact h₂
end Analyticity
section DeterminationAndTransport
variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
open YangMills.Construction.MeasureUniqueness (laplaceExp)
def halfLineSet : Set (Fin 1 → ℝ) := {y | 0 ≤ y 0}
theorem measurableSet_halfLineSet : MeasurableSet halfLineSet :=
  measurableSet_le measurable_const (measurable_pi_apply 0)
def halfLineSetEquivIci : halfLineSet ≃ᵐ Ici (0 : ℝ) where
  toFun y := ⟨y.1 0, y.2⟩
  invFun x := ⟨fun _ => x.1, x.2⟩
  left_inv y := Subtype.ext (funext fun i => by rw [Subsingleton.elim i 0])
  right_inv x := rfl
  measurable_toFun :=
    Measurable.subtype_mk ((measurable_pi_apply 0).comp measurable_subtype_coe)
  measurable_invFun :=
    Measurable.subtype_mk (measurable_pi_iff.mpr fun _ => measurable_subtype_coe)
theorem measurable_laplaceExp (k : ℕ) : Measurable (laplaceExp k) := by
  unfold laplaceExp
  have : Measurable fun E : Ici (0 : ℝ) => ((E : ℝ) : ℂ) :=
    Complex.measurable_ofReal.comp measurable_subtype_coe
  exact Complex.measurable_exp.comp (measurable_const.mul this)
theorem norm_laplaceExp_le (k : ℕ) (E : Ici (0 : ℝ)) : ‖laplaceExp k E‖ ≤ 1 := by
  rw [laplaceExp, Complex.norm_exp]
  have h₁ : (-(k : ℂ) * ((E : ℝ) : ℂ)).re = -((k : ℝ) * (E : ℝ)) := by simp
  rw [h₁, Real.exp_le_one_iff]
  have h₂ : 0 ≤ (E : ℝ) := E.2
  have h₃ : 0 ≤ (k : ℝ) * (E : ℝ) := by positivity
  linarith
theorem separates_halfLineSet (hF : SetFunctions.ComplexMeasureFacts)
    (hM : MeasureUniqueness.UniquenessAndIntegral) :
    SeparatesComplexMeasures (Set.range fun k : ℕ => laplaceExp k ∘ halfLineSetEquivIci) := by
  obtain ⟨-, -, -, ⟨-, hLap⟩, hInd, -⟩ := hM
  exact separates_of_measurableEquiv hF halfLineSetEquivIci
    (hInd 1 le_rfl halfLineSet measurableSet_halfLineSet).2
    (fun k => laplaceExp k)
    (fun k => ⟨measurable_laplaceExp k, 1, norm_laplaceExp_le k⟩) hLap
def clampToHalfLine (y : RealLineSet) : halfLineSet :=
  ⟨fun _ => max (y.1 0) 0, show (0 : ℝ) ≤ max (y.1 0) 0 from le_max_right _ _⟩
theorem measurable_clampToHalfLine : Measurable clampToHalfLine := by
  unfold clampToHalfLine
  exact Measurable.subtype_mk (measurable_pi_iff.mpr fun _ =>
    measurable_coord.max (measurable_const (a := (0 : ℝ))))
def restrictToHalfLine (E : SpectralMeasure RealLineSet H) : SpectralMeasure halfLineSet H :=
  E.pushforward le_rfl measurableSet_halfLineSet clampToHalfLine measurable_clampToHalfLine
theorem integralOp_restrictToHalfLine (hC : SpectralMeasureCalculus.CalculusTheorem)
    {E : SpectralMeasure RealLineSet H} (k : ℕ)
    (hc : E.IsCarriedBy (realLineSet nonnegHalfLine)) :
    (restrictToHalfLine E).integralOp (laplaceExp k ∘ halfLineSetEquivIci) =
      E.integralOp (expDecayFn (k : ℂ)) := by
  obtain ⟨-, hB, -, -, hI, -⟩ := hC H 1 univ E
  have hg : Measurable (laplaceExp k ∘ halfLineSetEquivIci) :=
    (measurable_laplaceExp k).comp halfLineSetEquivIci.measurable
  have hb : ∀ y, ‖(laplaceExp k ∘ halfLineSetEquivIci) y‖ ≤ 1 := fun y =>
    norm_laplaceExp_le k _
  have hb' : ∀ y, ‖((laplaceExp k ∘ halfLineSetEquivIci) ∘ clampToHalfLine) y‖ ≤ 1 :=
    fun y => hb _
  have hs := hI.integral_image le_rfl measurableSet_halfLineSet clampToHalfLine
    measurable_clampToHalfLine (laplaceExp k ∘ halfLineSetEquivIci) hg
  have h₁ : (restrictToHalfLine E).integralOp (laplaceExp k ∘ halfLineSetEquivIci) =
      E.integralOp ((laplaceExp k ∘ halfLineSetEquivIci) ∘ clampToHalfLine) := by
    ext ψ
    rw [← integralApply_eq_integralOp _ hb ψ, ← integralApply_eq_integralOp _ hb' ψ]
    exact hs.2 ψ (by
      have h₂ := integralDom_eq_univ (restrictToHalfLine E) hb
      change ψ ∈ (restrictToHalfLine E).integralDom _
      rw [h₂]
      exact mem_univ _)
  rw [h₁]
  refine hB.congr _ _ (realLineSet nonnegHalfLine) (hg.comp measurable_clampToHalfLine) ⟨1, hb'⟩
    (measurable_expDecayFn _) (isBoundedFn_expDecayFn (by simp)) hc fun y hy => ?_
  have h₂ : y.1 0 ∈ Ici (0 : ℝ) := hy
  have h₃ : (0 : ℝ) ≤ y.1 0 := h₂
  simp [expDecayFn, indicator_of_mem h₂, laplaceExp, halfLineSetEquivIci, clampToHalfLine,
    max_eq_left h₃]
def borelCutToHalfLine (Δ : BorelSubsets RealLineSet) : BorelSubsets halfLineSet :=
  ⟨(fun x : halfLineSet => (⟨x.1, mem_univ _⟩ : RealLineSet)) ⁻¹' Δ.1,
    (Measurable.subtype_mk measurable_subtype_coe) Δ.2⟩
theorem apply_eq_restrictToHalfLine (hC : SpectralMeasureCalculus.CalculusTheorem)
    {E : SpectralMeasure RealLineSet H} (hc : E.IsCarriedBy (realLineSet nonnegHalfLine))
    (Δ : BorelSubsets RealLineSet) : E Δ = restrictToHalfLine E (borelCutToHalfLine Δ) := by
  obtain ⟨-, -, -, -, hI, -⟩ := hC H 1 univ E
  have h₁ : restrictToHalfLine E (borelCutToHalfLine Δ) =
      E ⟨clampToHalfLine ⁻¹' (borelCutToHalfLine Δ).1,
        measurable_clampToHalfLine (borelCutToHalfLine Δ).2⟩ := rfl
  have e₁ := hI.value_inter_carrier _ Δ hc
  have e₂ := hI.value_inter_carrier _
    ⟨clampToHalfLine ⁻¹' (borelCutToHalfLine Δ).1,
      measurable_clampToHalfLine (borelCutToHalfLine Δ).2⟩ hc
  rw [h₁, e₁, e₂]
  refine apply_congr E ?_
  ext y
  simp only [mem_inter_iff]
  refine and_congr_left fun hy => ?_
  have h₂ : (0 : ℝ) ≤ y.1 0 := hy
  have h₃ : (⟨(clampToHalfLine y).1, mem_univ _⟩ : RealLineSet) = y := by
    refine Subtype.ext (funext fun i => ?_)
    rw [Subsingleton.elim i 0]
    exact max_eq_left h₂
  change y ∈ Δ.1 ↔ (⟨(clampToHalfLine y).1, mem_univ _⟩ : RealLineSet) ∈ Δ.1
  rw [h₃]
theorem op_eq_of_spectralMeasure_eq (hC : SpectralMeasureCalculus.CalculusTheorem)
    {A A' : UnboundedOp H} (hA : IsDiagonalized A) (hA' : IsDiagonalized A')
    (h : spectralMeasure A = spectralMeasure A') : A = A' := by
  obtain ⟨-, -, hAll, -⟩ := hC H 1 univ (spectralMeasure A)
  have h₁ := eq_spectralIntegralOp hAll measurable_coordVar
    (isSpectralMeasureFor_spectralMeasure hA)
  have h₂ := isSpectralMeasureFor_spectralMeasure hA'
  rw [← h] at h₂
  rw [h₁, eq_spectralIntegralOp hAll measurable_coordVar h₂]
theorem expDeterminesOp_holds (hC : SpectralMeasureCalculus.CalculusTheorem)
    (hF : SetFunctions.ComplexMeasureFacts)
    (hM : MeasureUniqueness.UniquenessAndIntegral)
    (hU : SpectralFromScalar.ScalarDeterminationTheorem) :
    ExpDeterminesOp H := by
  refine ⟨fun B B' hB hB' h => ?_, fun A A' hA hA' hn hn' h => ?_⟩
  · exact op_eq_of_spectralMeasure_eq hC hB hB' (eq_of_integralOp_expIFn hF hM hU _ _ h)
  · have hc := isCarriedBy_nonneg_of_neg ((nonnegIffNegHalfLineNull_holds hC A hA).mp hn)
    have hc' := isCarriedBy_nonneg_of_neg ((nonnegIffNegHalfLineNull_holds hC A' hA').mp hn')
    have hb : AllBoundedMeasurable (Set.range fun k : ℕ =>
        laplaceExp k ∘ halfLineSetEquivIci) := by
      rintro _ ⟨k, rfl⟩
      exact ⟨(measurable_laplaceExp k).comp halfLineSetEquivIci.measurable, 1,
        fun y => norm_laplaceExp_le k _⟩
    have heq : restrictToHalfLine (spectralMeasure A) =
        restrictToHalfLine (spectralMeasure A') := by
      refine (hU H 1 le_rfl halfLineSet measurableSet_halfLineSet
        ⟨fun _ => 0, le_refl (0 : ℝ)⟩ _ hb (separates_halfLineSet hF hM)).1 _ _ ?_
      rintro _ ⟨k, rfl⟩
      simp only
      rw [integralOp_restrictToHalfLine hC k hc, integralOp_restrictToHalfLine hC k hc']
      exact h k
    refine op_eq_of_spectralMeasure_eq hC hA hA' (SpectralMeasure.ext_apply fun Δ => ?_)
    rw [apply_eq_restrictToHalfLine hC hc, apply_eq_restrictToHalfLine hC hc', heq]
theorem spectralIntegralOp_eq_of_integralsAgree {n n' : ℕ} {Y : Set (Fin n → ℝ)}
    {Y' : Set (Fin n' → ℝ)}
    {E : SpectralMeasure Y H} {E' : SpectralMeasure Y' H} {g : Y → ℂ} {g' : Y' → ℂ}
    (hA : UnboundedCalculusLaws E) (hA' : UnboundedCalculusLaws E') (hg : Measurable g)
    (hg' : Measurable g') (h : IntegralsAgree E g E' g') :
    spectralIntegralOp E g = spectralIntegralOp E' g' := by
  have iB := hA'.isIntegralOf g' hg'
  refine eq_of_isSpectralIntegralOf (hA.isIntegralOf g hg) ⟨fun ψ => ?_, fun ψ => ?_⟩
  · rw [iB.1, h.1]
  · rw [iB.2]
    exact (h.2 _ (by rw [h.1]; exact (iB.1 _).1 ψ.2)).symm
theorem realIntegralsDiagonalized_holds (hC : SpectralMeasureCalculus.CalculusTheorem)
    (hF : SetFunctions.ComplexMeasureFacts)
    (hM : MeasureUniqueness.UniquenessAndIntegral)
    (hU : SpectralFromScalar.ScalarDeterminationTheorem) :
    RealIntegralsDiagonalized H := by
  intro n Y E _
  obtain ⟨-, -, hA, -, hI, -, hR, -⟩ := hC H n Y E
  have main : ∀ (g : Y → ℝ) (hg : Measurable g),
      IsSpectralMeasureFor (pushforwardToLine E g hg) (realSpectralIntegral E g) := by
    intro g hg
    have hg' : Measurable fun y => ((g y : ℝ) : ℂ) := Complex.measurable_ofReal.comp hg
    have h₁ := hR.eq_integral_lineImage _ hg' (fun y => by simp)
    obtain ⟨-, -, hA', -⟩ := hC H 1 univ (pushforwardToLine E g hg)
    have h₂ := hA'.isIntegralOf _ measurable_coordVar
    unfold realSpectralIntegral IsSpectralMeasureFor
    rw [h₁]
    exact h₂
  have hsm : ∀ (g : Y → ℝ) (hg : Measurable g),
      spectralMeasure (realSpectralIntegral E g) = pushforwardToLine E g hg := fun g hg =>
    spectralMeasure_eq_of_isSpectralMeasureFor hC hF hM hU (main g hg)
  refine ⟨fun g hg => ⟨⟨_, main g hg⟩, hsm g hg, fun u hu => ?_⟩, fun g g' hg hg' Δ₁ Δ₂ => ?_⟩
  · obtain ⟨-, -, hA', -⟩ := hC H 1 univ (pushforwardToLine E g hg)
    have hu' : Measurable fun y : RealLineSet => u (y.1 0) := hu.comp measurable_coord
    have hκ : Measurable fun y : Y => (⟨fun _ => g y, mem_univ _⟩ : RealLineSet) :=
      Measurable.subtype_mk (measurable_pi_iff.mpr fun _ => hg)
    unfold fnCalc
    rw [hsm g hg]
    exact spectralIntegralOp_eq_of_integralsAgree hA' hA hu' (hu'.comp hκ)
      (hI.integral_image le_rfl MeasurableSet.univ _ hκ _ hu')
  · rw [hsm g hg, hsm g' hg']
    have h₁ : ∀ Δ Δ' : BorelSubsets Y, Commute (E Δ) (E Δ') := fun Δ Δ' => by
      show E Δ * E Δ' = E Δ' * E Δ
      rw [← E.map_inter, ← E.map_inter]
      exact apply_congr E (inter_comm _ _)
    exact h₁ _ _
theorem conjOpDiagonalized_holds (hC : SpectralMeasureCalculus.CalculusTheorem)
    (hF : SetFunctions.ComplexMeasureFacts)
    (hM : MeasureUniqueness.UniquenessAndIntegral)
    (hU : SpectralFromScalar.ScalarDeterminationTheorem)
    (H' : Type) [NormedAddCommGroup H'] [InnerProductSpace ℂ H'] [CompleteSpace H'] :
    ConjOpDiagonalized H H' := by
  intro A V hV hres
  have hs := isSpectralMeasureFor_spectralMeasure hres
  obtain ⟨-, -, hA, -, -, hT, -⟩ := hC H 1 univ (spectralMeasure A)
  obtain ⟨E', hv, -, hi⟩ := hT H' V hV
  obtain ⟨-, -, hA', -⟩ := hC H' 1 univ E'
  have hop : spectralIntegralOp E' coordVar = OperatorTransport.conjOp hV A := by
    rw [hi _ measurable_coordVar, ← eq_spectralIntegralOp hA measurable_coordVar hs]
  have hsp : IsSpectralMeasureFor E' (OperatorTransport.conjOp hV A) :=
    hop ▸ hA'.isIntegralOf _ measurable_coordVar
  have heq : spectralMeasure (OperatorTransport.conjOp hV A) = E' :=
    spectralMeasure_eq_of_isSpectralMeasureFor hC hF hM hU hsp
  refine ⟨⟨E', hsp⟩, fun Δ => ?_, fun u hu => ?_⟩
  · rw [heq]
    exact hv Δ
  · unfold fnCalc
    rw [heq]
    exact hi _ (hu.comp measurable_coord)
end DeterminationAndTransport
theorem diagonalizedFacts_holds (hC : SpectralMeasureCalculus.CalculusTheorem)
    (hU : SpectralFromScalar.ScalarDeterminationTheorem)
    (hM : MeasureUniqueness.UniquenessAndIntegral)
    (hF : SetFunctions.ComplexMeasureFacts) : DiagonalizedFacts := by
  intro H _ _ _
  refine ⟨fun E => ⟨?_, fun E' h => eq_of_spectralIntegralOp_coordVar hC hF hM hU E E' h⟩,
    nonnegIffNegHalfLineNull_holds hC, expIFormsUnitaryGroup_holds hC, fun A hA hn => ?_,
    expDeterminesOp_holds hC hF hM hU, realIntegralsDiagonalized_holds hC hF hM hU,
    fun H' _ _ _ => conjOpDiagonalized_holds hC hF hM hU H'⟩
  · obtain ⟨-, -, -, -, -, -, hR, -⟩ := hC H 1 univ E
    exact hR.isSelfAdjoint _ measurable_coordVar fun y => by simp [coordVar]
  · obtain ⟨h₁, h₂, h₃, h₄, h₅, h₆⟩ := expComplex_props_of_nonneg hC hA hn
    exact ⟨h₁, h₂, h₃, h₄, h₅, h₆, isOperatorHolomorphicOn_expComplex hC A⟩
end YangMills.Construction.ResolvedFacts
