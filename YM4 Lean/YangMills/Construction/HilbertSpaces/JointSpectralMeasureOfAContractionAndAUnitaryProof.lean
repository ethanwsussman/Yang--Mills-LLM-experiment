import YangMills.Construction.HilbertSpaces.JointSpectralMeasureOfAContractionAndAUnitary
import YangMills.Construction.HilbertSpaces.PolynomialsOfACommutingPairAreBoundedByTheirSuprema
import YangMills.Construction.Measurability.BoundedLimitClassStatement
import YangMills.Construction.Measures.RieszMarkovCompactMetrizable
import YangMills.Construction.SpectralMeasures.IntegralsOfBoundedFunctionsAgainstAProjectionValuedMeasure
import Mathlib
set_option autoImplicit false
set_option linter.unusedSectionVars false
open MeasureTheory Filter Topology ComplexConjugate
open scoped InnerProductSpace ComplexOrder
noncomputable section
namespace YangMills.Construction
open OneLoopNotation ComplexHilbert SpectralMeasures LatticeConventions
namespace ContractionUnitary.JointSpectral
abbrev BddLimitClassHyp : Prop := Measurability.BoundedLimitClass.Claim
abbrev BddCalculusHyp : Prop := BddCalculus.Statement
abbrev RieszHyp : Prop := Measures.RieszMarkov.positiveFunctional_representation
section Functions
variable {X : Type} [MeasurableSpace X]
theorem isBddMeasurable_add {f g : X → ℂ} (hf : IsBddMeasurable f)
    (hg : IsBddMeasurable g) : IsBddMeasurable (f + g) := by
  obtain ⟨hm, C, hC⟩ := hf
  obtain ⟨hm', C', hC'⟩ := hg
  exact ⟨hm.add hm', C + C', fun x => (norm_add_le _ _).trans (add_le_add (hC x) (hC' x))⟩
theorem isBddMeasurable_smul (z : ℂ) {f : X → ℂ} (hf : IsBddMeasurable f) :
    IsBddMeasurable (z • f) := by
  obtain ⟨hm, C, hC⟩ := hf
  refine ⟨hm.const_smul z, ‖z‖ * C, fun x => ?_⟩
  rw [Pi.smul_apply, norm_smul]
  exact mul_le_mul_of_nonneg_left (hC x) (norm_nonneg z)
theorem isBddMeasurable_mul {f g : X → ℂ} (hf : IsBddMeasurable f)
    (hg : IsBddMeasurable g) : IsBddMeasurable (f * g) := by
  obtain ⟨hm, C, hC⟩ := hf
  obtain ⟨hm', C', hC'⟩ := hg
  refine ⟨hm.mul hm', C * C', fun x => ?_⟩
  have h₀ : 0 ≤ C := (norm_nonneg _).trans (hC x)
  simpa using mul_le_mul (hC x) (hC' x) (norm_nonneg _) h₀
theorem isBddMeasurable_indicatorOne (Y : MeasSet X) :
    IsBddMeasurable (indicatorOne Y.1 : X → ℂ) := by
  refine ⟨Measurable.indicator measurable_const Y.2, 1, fun x => ?_⟩
  by_cases h : x ∈ Y.1 <;> simp [indicatorOne, constOne, h]
theorem isBddMeasurable_of_tendsto (F : ℕ → X → ℂ) (f : X → ℂ)
    (hF : ∀ n, IsBddMeasurable (F n)) (hC : ∃ C : ℝ, ∀ n x, ‖F n x‖ ≤ C)
    (hl : ∀ x, Tendsto (fun n => F n x) atTop (𝓝 (f x))) : IsBddMeasurable f := by
  obtain ⟨C, hC⟩ := hC
  exact ⟨measurable_of_tendsto_metrizable (fun n => (hF n).1) (tendsto_pi_nhds.mpr hl), C,
    fun x => le_of_tendsto (hl x).norm (Eventually.of_forall fun n => hC n x)⟩
theorem integrable_of_isBddMeasurable {f : X → ℂ} (hf : IsBddMeasurable f)
    (μ : Measure X) [IsFiniteMeasure μ] : Integrable f μ := by
  obtain ⟨hm, C, hC⟩ := hf
  exact Integrable.of_bound hm.aestronglyMeasurable C (Eventually.of_forall hC)
theorem tendsto_integral_of_unifBdd (μ : Measure X) [IsFiniteMeasure μ] (F : ℕ → X → ℂ)
    (f : X → ℂ) (hF : ∀ n, IsBddMeasurable (F n)) (hC : ∃ C : ℝ, ∀ n x, ‖F n x‖ ≤ C)
    (hl : ∀ x, Tendsto (fun n => F n x) atTop (𝓝 (f x))) :
    Tendsto (fun n => ∫ x, F n x ∂μ) atTop (𝓝 (∫ x, f x ∂μ)) := by
  obtain ⟨C, hC⟩ := hC
  exact tendsto_integral_of_dominated_convergence (fun _ => C)
    (fun n => (hF n).1.aestronglyMeasurable) (integrable_const C)
    (fun n => Eventually.of_forall (hC n)) (Eventually.of_forall hl)
end Functions
theorem bddMeasurable_induction {X : Type} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
    (hclass : BddLimitClassHyp) (P : (X → ℂ) → Prop)
    (hadd : ∀ f g, IsBddMeasurable f → IsBddMeasurable g → P f → P g →
      P (f + g))
    (hsmul : ∀ (z : ℂ) f, IsBddMeasurable f → P f → P (z • f))
    (hcont : ∀ f, Continuous f → (∃ C : ℝ, ∀ x, ‖f x‖ ≤ C) → P f)
    (hlim : ∀ (F : ℕ → X → ℂ) (f : X → ℂ), (∀ n, IsBddMeasurable (F n)) →
      IsBddMeasurable f → (∀ n, P (F n)) → (∃ C : ℝ, ∀ n x, ‖F n x‖ ≤ C) →
      (∀ x, Tendsto (fun n => F n x) atTop (𝓝 (f x))) → P f) :
    ∀ f, IsBddMeasurable f → P f := by
  let K : Submodule ℂ (X → ℂ) :=
    { carrier := {f | IsBddMeasurable f ∧ P f}
      add_mem' := fun {f g} hf hg =>
        ⟨isBddMeasurable_add hf.1 hg.1, hadd f g hf.1 hg.1 hf.2 hg.2⟩
      zero_mem' := ⟨⟨measurable_const, 0, by simp⟩, hcont 0 continuous_const ⟨0, by simp⟩⟩
      smul_mem' := fun z f hf => ⟨isBddMeasurable_smul z hf.1, hsmul z f hf.1 hf.2⟩ }
  have hK : Measurability.BoundedLimitClass.IsBoundedLimitClosed K :=
    { boundedMeasurable := fun f hf => hf.1
      continuous_mem := fun f hf hb => ⟨⟨hf.measurable, hb⟩, hcont f hf hb⟩
      limit_mem := fun u f hu hC hl => by
        have hb := isBddMeasurable_of_tendsto u f (fun n => (hu n).1) hC hl
        exact ⟨hb, hlim u f (fun n => (hu n).1) hb (fun n => (hu n).2) hC hl⟩ }
  intro f hf
  have h₁ : f ∈ (K : Set (X → ℂ)) := by
    rw [hclass X K hK]
    exact hf
  exact h₁.2
section Representation
variable {X H : Type} [MetricSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
structure IsStarRep (L : C(X, ℂ) →ₗ[ℂ] BddOp H) : Prop where
  map_one : L 1 = 1
  map_mul : ∀ f g, L (f * g) = L f * L g
  map_star : ∀ f φ ψ, ⟪φ, L f ψ⟫_ℂ = ⟪L (star f) φ, ψ⟫_ℂ
theorem exists_diagMeasure (hriesz : RieszHyp) {L : C(X, ℂ) →ₗ[ℂ] BddOp H}
    (hL : IsStarRep L) (ψ : H) :
    ∃ μ : Measure X, IsFiniteMeasure μ ∧ ∀ f : C(X, ℂ), ⟪ψ, L f ψ⟫_ℂ = ∫ x, f x ∂μ := by
  let ℓ : C(X, ℂ) →ₗ[ℂ] ℂ :=
    { toFun := fun f => ⟪ψ, L f ψ⟫_ℂ
      map_add' := fun f g => by simp [inner_add_right]
      map_smul' := fun z f => by simp [inner_smul_right] }
  have hpos : ∀ f : C(X, ℂ), (∀ x, 0 ≤ f x) → 0 ≤ ℓ f := by
    intro f hf
    let g : C(X, ℂ) := ⟨fun x => ((Real.sqrt (f x).re : ℝ) : ℂ),
      Complex.continuous_ofReal.comp (Real.continuous_sqrt.comp
        (Complex.continuous_re.comp f.continuous))⟩
    have hg : f = star g * g := by
      ext x
      have h₁ := Complex.nonneg_iff.mp (hf x)
      have h₂ : star (g x) * g x = f x := by
        change conj ((Real.sqrt (f x).re : ℝ) : ℂ) * ((Real.sqrt (f x).re : ℝ) : ℂ) = f x
        rw [Complex.conj_ofReal, ← Complex.ofReal_mul, Real.mul_self_sqrt h₁.1]
        exact Complex.ext rfl (by simpa using h₁.2)
      exact h₂.symm
    have h₂ : ℓ f = ⟪L g ψ, L g ψ⟫_ℂ := by
      change ⟪ψ, L f ψ⟫_ℂ = _
      rw [hg, hL.map_mul]
      change ⟪ψ, L (star g) (L g ψ)⟫_ℂ = _
      rw [hL.map_star, star_star]
    rw [h₂, inner_self_eq_norm_sq_to_K]
    have h₃ := Complex.zero_le_real.mpr (sq_nonneg ‖L g ψ‖)
    simpa using h₃
  obtain ⟨⟨μ, ⟨hfin, hμ⟩, -⟩, -⟩ := (hriesz X).2.1 ℓ hpos
  exact ⟨μ, hfin, hμ⟩
def polarization (D : H → ℂ) (φ ψ : H) : ℂ :=
  (D (ψ + φ) - D (ψ - φ) + Complex.I * D (ψ + Complex.I • φ)
    - Complex.I * D (ψ - Complex.I • φ)) / 4
theorem polarization_inner (T : BddOp H) (φ ψ : H) :
    polarization (fun x => ⟪x, T x⟫_ℂ) φ ψ = ⟪φ, T ψ⟫_ℂ := by
  simp only [polarization, map_add, map_sub, map_smul, inner_add_left, inner_add_right,
    inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right, Complex.conj_I]
  ring_nf
  simp only [Complex.I_sq, Complex.I_pow_three]
  ring
theorem eq_of_inner_self {B B' : BddOp H} (h : ∀ ψ, ⟪ψ, B ψ⟫_ℂ = ⟪ψ, B' ψ⟫_ℂ) : B = B' := by
  ext ψ
  refine ext_inner_left ℂ fun φ => ?_
  have h₁ : (fun x => ⟪x, B x⟫_ℂ) = fun x => ⟪x, B' x⟫_ℂ := funext h
  rw [← polarization_inner, ← polarization_inner, h₁]
theorem norm_apply_le_of_inner_self (B : BddOp H) {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ ψ, ‖⟪ψ, B ψ⟫_ℂ‖ ≤ C * ‖ψ‖ ^ 2) (ψ : H) : ‖B ψ‖ ≤ 4 * C * ‖ψ‖ := by
  by_cases hψ : ψ = 0
  · simp [hψ]
  by_cases hB : B ψ = 0
  · rw [hB, norm_zero]
    positivity
  have hs : 0 < ‖ψ‖ := norm_pos_iff.mpr hψ
  have hr : 0 < ‖B ψ‖ := norm_pos_iff.mpr hB
  let ψ₁ : H := ((‖ψ‖⁻¹ : ℝ) : ℂ) • ψ
  let φ₁ : H := ((‖B ψ‖⁻¹ : ℝ) : ℂ) • B ψ
  have hψ₁ : ‖ψ₁‖ = 1 := by
    simp only [ψ₁, norm_smul, Complex.norm_real, norm_inv, norm_norm]
    exact inv_mul_cancel₀ hs.ne'
  have hφ₁ : ‖φ₁‖ = 1 := by
    simp only [φ₁, norm_smul, Complex.norm_real, norm_inv, norm_norm]
    exact inv_mul_cancel₀ hr.ne'
  have hval : ⟪φ₁, B ψ₁⟫_ℂ = ((‖B ψ‖ / ‖ψ‖ : ℝ) : ℂ) := by
    simp only [φ₁, ψ₁, map_smul, inner_smul_left, inner_smul_right, Complex.conj_ofReal,
      inner_self_eq_norm_sq_to_K]
    have h₁ : (‖B ψ‖ : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
    have h₂ : (‖ψ‖ : ℂ) ≠ 0 := by exact_mod_cast hs.ne'
    push_cast
    simp only [Complex.coe_algebraMap]
    field_simp
  have hterm : ∀ x : H, ‖x‖ ≤ 2 → ‖⟪x, B x⟫_ℂ‖ ≤ 4 * C := by
    intro x hx
    refine (h x).trans ?_
    have h₁ : ‖x‖ ^ 2 ≤ 2 ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hx 2
    nlinarith
  have hI : ‖Complex.I • φ₁‖ = 1 := by rw [norm_smul, Complex.norm_I, one_mul, hφ₁]
  have ha : ‖ψ₁ + φ₁‖ ≤ 2 := (norm_add_le _ _).trans (by rw [hψ₁, hφ₁]; norm_num)
  have hb : ‖ψ₁ - φ₁‖ ≤ 2 := (norm_sub_le _ _).trans (by rw [hψ₁, hφ₁]; norm_num)
  have hc : ‖ψ₁ + Complex.I • φ₁‖ ≤ 2 := (norm_add_le _ _).trans (by rw [hψ₁, hI]; norm_num)
  have hd : ‖ψ₁ - Complex.I • φ₁‖ ≤ 2 := (norm_sub_le _ _).trans (by rw [hψ₁, hI]; norm_num)
  have hbound : ‖⟪φ₁, B ψ₁⟫_ℂ‖ ≤ 4 * C := by
    rw [← polarization_inner]
    simp only [polarization, norm_div, Complex.norm_ofNat]
    have h₁ := hterm _ ha
    have h₂ := hterm _ hb
    have h₃ := hterm _ hc
    have h₄ := hterm _ hd
    have h₅ : ‖Complex.I * ⟪ψ₁ + Complex.I • φ₁, B (ψ₁ + Complex.I • φ₁)⟫_ℂ‖ ≤ 4 * C := by
      rw [norm_mul, Complex.norm_I, one_mul]
      exact h₃
    have h₆ : ‖Complex.I * ⟪ψ₁ - Complex.I • φ₁, B (ψ₁ - Complex.I • φ₁)⟫_ℂ‖ ≤ 4 * C := by
      rw [norm_mul, Complex.norm_I, one_mul]
      exact h₄
    have h₇ := norm_sub_le (⟪ψ₁ + φ₁, B (ψ₁ + φ₁)⟫_ℂ) (⟪ψ₁ - φ₁, B (ψ₁ - φ₁)⟫_ℂ)
    have h₈ := norm_add_le (⟪ψ₁ + φ₁, B (ψ₁ + φ₁)⟫_ℂ - ⟪ψ₁ - φ₁, B (ψ₁ - φ₁)⟫_ℂ)
      (Complex.I * ⟪ψ₁ + Complex.I • φ₁, B (ψ₁ + Complex.I • φ₁)⟫_ℂ)
    have h₉ := norm_sub_le (⟪ψ₁ + φ₁, B (ψ₁ + φ₁)⟫_ℂ - ⟪ψ₁ - φ₁, B (ψ₁ - φ₁)⟫_ℂ
      + Complex.I * ⟪ψ₁ + Complex.I • φ₁, B (ψ₁ + Complex.I • φ₁)⟫_ℂ)
      (Complex.I * ⟪ψ₁ - Complex.I • φ₁, B (ψ₁ - Complex.I • φ₁)⟫_ℂ)
    rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 4)]
    linarith
  rw [hval, Complex.norm_real, Real.norm_of_nonneg (by positivity), div_le_iff₀ hs] at hbound
  exact hbound
theorem exists_op_of_diagMeasure (hclass : BddLimitClassHyp) {L : C(X, ℂ) →ₗ[ℂ] BddOp H}
    (hL : IsStarRep L) (μ : H → Measure X) (hfin : ∀ ψ, IsFiniteMeasure (μ ψ))
    (hμ : ∀ ψ (f : C(X, ℂ)), ⟪ψ, L f ψ⟫_ℂ = ∫ x, f x ∂(μ ψ)) :
    ∀ F : X → ℂ, IsBddMeasurable F →
      ∃ B : BddOp H, ∀ ψ, ⟪ψ, B ψ⟫_ℂ = ∫ x, F x ∂(μ ψ) := by
  have hmass : ∀ ψ, (μ ψ).real Set.univ = ‖ψ‖ ^ 2 := by
    intro ψ
    have h₁ := hμ ψ 1
    rw [hL.map_one] at h₁
    have h₂ : ⟪ψ, (1 : BddOp H) ψ⟫_ℂ = ((‖ψ‖ ^ 2 : ℝ) : ℂ) := by
      rw [ContinuousLinearMap.one_apply, inner_self_eq_norm_sq_to_K]
      push_cast
      rfl
    rw [h₂] at h₁
    have h₃ : ∫ x, (1 : C(X, ℂ)) x ∂(μ ψ) = (((μ ψ).real Set.univ : ℝ) : ℂ) := by
      simp
    rw [h₃] at h₁
    exact_mod_cast h₁.symm
  refine bddMeasurable_induction hclass _ ?_ ?_ ?_ ?_
  · rintro f g hf hg ⟨B, hB⟩ ⟨B', hB'⟩
    refine ⟨B + B', fun ψ => ?_⟩
    have h₁ := integral_add (integrable_of_isBddMeasurable hf (μ ψ))
      (integrable_of_isBddMeasurable hg (μ ψ))
    simp only [Pi.add_apply]
    rw [h₁, ← hB, ← hB', ContinuousLinearMap.add_apply, inner_add_right]
  · rintro z f hf ⟨B, hB⟩
    refine ⟨z • B, fun ψ => ?_⟩
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [integral_const_mul, ← hB, ContinuousLinearMap.smul_apply, inner_smul_right]
  · intro f hf _
    exact ⟨L ⟨f, hf⟩, fun ψ => hμ ψ ⟨f, hf⟩⟩
  · intro F f hF hf hB hC hl
    choose B hB using hB
    have hconv : ∀ ψ, Tendsto (fun n => ∫ x, F n x ∂(μ ψ)) atTop (𝓝 (∫ x, f x ∂(μ ψ))) :=
      fun ψ => tendsto_integral_of_unifBdd (μ ψ) F f hF hC hl
    obtain ⟨C₀, hC₀⟩ := hC
    have hC₁ : ∀ n x, ‖F n x‖ ≤ |C₀| := fun n x => (hC₀ n x).trans (le_abs_self _)
    have hdiag : ∀ n ψ, ‖⟪ψ, B n ψ⟫_ℂ‖ ≤ |C₀| * ‖ψ‖ ^ 2 := by
      intro n ψ
      rw [hB, ← hmass]
      exact norm_integral_le_of_norm_le_const (Eventually.of_forall (hC₁ n))
    have hnorm : ∀ n ψ, ‖B n ψ‖ ≤ 4 * |C₀| * ‖ψ‖ :=
      fun n => norm_apply_le_of_inner_self (B n) (abs_nonneg _) (hdiag n)
    let D : H → ℂ := fun x => ∫ y, f y ∂(μ x)
    have hweak : ∀ φ ψ, Tendsto (fun n => ⟪φ, B n ψ⟫_ℂ) atTop (𝓝 (polarization D φ ψ)) := by
      intro φ ψ
      have h₁ : (fun n => ⟪φ, B n ψ⟫_ℂ) =
          fun n => polarization (fun x => ∫ y, F n y ∂(μ x)) φ ψ := by
        funext n
        rw [← polarization_inner]
        simp only [hB]
      rw [h₁]
      exact ((((hconv _).sub (hconv _)).add ((hconv _).const_mul _)).sub
        ((hconv _).const_mul _)).div_const 4
    have hbound : ∀ φ ψ, ‖polarization D φ ψ‖ ≤ 4 * |C₀| * ‖φ‖ * ‖ψ‖ := by
      intro φ ψ
      refine le_of_tendsto (hweak φ ψ).norm (Eventually.of_forall fun n => ?_)
      refine (norm_inner_le_norm _ _).trans ?_
      have h₁ := mul_le_mul_of_nonneg_left (hnorm n ψ) (norm_nonneg φ)
      nlinarith
    let q : H →ₗ⋆[ℂ] H →ₗ[ℂ] ℂ := LinearMap.mk₂'ₛₗ (starRingEnd ℂ) (RingHom.id ℂ) (polarization D)
      (fun φ φ' ψ => tendsto_nhds_unique (hweak _ _)
        (by simpa [inner_add_left] using (hweak φ ψ).add (hweak φ' ψ)))
      (fun z φ ψ => tendsto_nhds_unique (hweak _ _)
        (by simpa [inner_smul_left, mul_comm] using (hweak φ ψ).const_mul (conj z)))
      (fun φ ψ ψ' => tendsto_nhds_unique (hweak _ _)
        (by simpa [inner_add_right] using (hweak φ ψ).add (hweak φ ψ')))
      (fun z φ ψ => tendsto_nhds_unique (hweak _ _)
        (by simpa [inner_smul_right] using (hweak φ ψ).const_mul z))
    let qc : H →L⋆[ℂ] H →L[ℂ] ℂ := q.mkContinuous₂ (4 * |C₀|) hbound
    refine ⟨ContinuousLinearMap.adjoint (InnerProductSpace.continuousLinearMapOfBilin qc),
      fun ψ => ?_⟩
    rw [ContinuousLinearMap.adjoint_inner_right, InnerProductSpace.continuousLinearMapOfBilin_apply]
    have h₁ : Tendsto (fun n => ⟪ψ, B n ψ⟫_ℂ) atTop (𝓝 (∫ x, f x ∂(μ ψ))) := by
      simpa only [hB] using hconv ψ
    exact tendsto_nhds_unique (hweak ψ ψ) h₁
theorem exists_pvm_of_starRep (hclass : BddLimitClassHyp) (hriesz : RieszHyp)
    (hrules : BddCalculusHyp) {L : C(X, ℂ) →ₗ[ℂ] BddOp H} (hL : IsStarRep L) :
    ∃ E : PVM X H, ∀ f : C(X, ℂ), E.bddIntegral f = L f := by
  choose μ hfin hμ using exists_diagMeasure (X := X) hriesz hL
  choose! Φ hΦ using exists_op_of_diagMeasure hclass hL μ hfin hμ
  have bmCont : ∀ f : C(X, ℂ), IsBddMeasurable (f : X → ℂ) :=
    fun f => ⟨f.continuous.measurable, ‖f‖, fun x => f.norm_coe_le_norm x⟩
  have hcontΦ : ∀ f : C(X, ℂ), Φ f = L f := fun f =>
    eq_of_inner_self fun ψ => by rw [hΦ _ (bmCont f), hμ]
  have hadd : ∀ F G, IsBddMeasurable F → IsBddMeasurable G →
      Φ (F + G) = Φ F + Φ G := fun F G hF hG => eq_of_inner_self fun ψ => by
    rw [hΦ _ (isBddMeasurable_add hF hG), ContinuousLinearMap.add_apply, inner_add_right,
      hΦ _ hF, hΦ _ hG]
    exact integral_add (integrable_of_isBddMeasurable hF (μ ψ))
      (integrable_of_isBddMeasurable hG (μ ψ))
  have hsmul : ∀ (z : ℂ) F, IsBddMeasurable F → Φ (z • F) = z • Φ F :=
    fun z F hF => eq_of_inner_self fun ψ => by
      rw [hΦ _ (isBddMeasurable_smul z hF), ContinuousLinearMap.smul_apply, inner_smul_right,
        hΦ _ hF, ← integral_const_mul]
      rfl
  have hweak : ∀ (F : ℕ → X → ℂ) (f : X → ℂ), (∀ n, IsBddMeasurable (F n)) →
      IsBddMeasurable f → (∃ C : ℝ, ∀ n x, ‖F n x‖ ≤ C) →
      (∀ x, Tendsto (fun n => F n x) atTop (𝓝 (f x))) →
      ∀ φ ψ, Tendsto (fun n => ⟪φ, Φ (F n) ψ⟫_ℂ) atTop (𝓝 ⟪φ, Φ f ψ⟫_ℂ) := by
    intro F f hF hf hC hl φ ψ
    have hconv : ∀ x, Tendsto (fun n => ∫ y, F n y ∂(μ x)) atTop (𝓝 (∫ y, f y ∂(μ x))) :=
      fun x => tendsto_integral_of_unifBdd (μ x) F f hF hC hl
    have h₁ : (fun n => ⟪φ, Φ (F n) ψ⟫_ℂ) =
        fun n => polarization (fun x => ∫ y, F n y ∂(μ x)) φ ψ := by
      funext n
      rw [← polarization_inner]
      simp only [hΦ _ (hF n)]
    have h₂ : ⟪φ, Φ f ψ⟫_ℂ = polarization (fun x => ∫ y, f y ∂(μ x)) φ ψ := by
      rw [← polarization_inner]
      simp only [hΦ _ hf]
    rw [h₁, h₂]
    exact ((((hconv _).sub (hconv _)).add ((hconv _).const_mul _)).sub
      ((hconv _).const_mul _)).div_const 4
  have hmul₁ : ∀ (f : C(X, ℂ)) G, IsBddMeasurable G →
      Φ ((f : X → ℂ) * G) = L f * Φ G := by
    intro f
    refine bddMeasurable_induction hclass _ ?_ ?_ ?_ ?_
    · intro G G' hG hG' h h'
      rw [mul_add, hadd _ _ (isBddMeasurable_mul (bmCont f) hG)
        (isBddMeasurable_mul (bmCont f) hG'), hadd _ _ hG hG', h, h', mul_add]
    · intro z G hG h
      rw [mul_smul_comm, hsmul _ _ (isBddMeasurable_mul (bmCont f) hG), hsmul _ _ hG, h,
        mul_smul_comm]
    · intro G hG hb
      have h₁ := hcontΦ (f * ⟨G, hG⟩)
      rw [hL.map_mul, ← hcontΦ ⟨G, hG⟩] at h₁
      exact h₁
    · intro G g hG hg h hC hl
      ext ψ
      refine ext_inner_left ℂ fun φ => ?_
      obtain ⟨C, hC⟩ := hC
      have h₁ : Tendsto (fun n => ⟪φ, Φ ((f : X → ℂ) * G n) ψ⟫_ℂ) atTop
          (𝓝 ⟪φ, Φ ((f : X → ℂ) * g) ψ⟫_ℂ) :=
        hweak _ _ (fun n => isBddMeasurable_mul (bmCont f) (hG n))
          (isBddMeasurable_mul (bmCont f) hg)
          ⟨‖f‖ * C, fun n x => by
            have h₀ : 0 ≤ C := (norm_nonneg _).trans (hC n x)
            simpa using mul_le_mul (f.norm_coe_le_norm x) (hC n x) (norm_nonneg _) (norm_nonneg f)⟩
          (fun x => (hl x).const_mul (f x)) φ ψ
      have h₂ : Tendsto (fun n => ⟪L (star f) φ, Φ (G n) ψ⟫_ℂ) atTop
          (𝓝 ⟪L (star f) φ, Φ g ψ⟫_ℂ) :=
        hweak _ _ hG hg ⟨C, hC⟩ hl _ ψ
      have h₃ : ∀ n, ⟪φ, Φ ((f : X → ℂ) * G n) ψ⟫_ℂ = ⟪L (star f) φ, Φ (G n) ψ⟫_ℂ := by
        intro n
        rw [h n, ContinuousLinearMap.mul_apply, hL.map_star]
      simp only [h₃] at h₁
      rw [tendsto_nhds_unique h₁ h₂, ContinuousLinearMap.mul_apply, hL.map_star]
  have hmul : ∀ G, IsBddMeasurable G → ∀ F, IsBddMeasurable F →
      Φ (F * G) = Φ F * Φ G := by
    intro G hG
    refine bddMeasurable_induction hclass _ ?_ ?_ ?_ ?_
    · intro F F' hF hF' h h'
      rw [add_mul, hadd _ _ (isBddMeasurable_mul hF hG) (isBddMeasurable_mul hF' hG),
        hadd _ _ hF hF', h, h', add_mul]
    · intro z F hF h
      rw [smul_mul_assoc, hsmul _ _ (isBddMeasurable_mul hF hG), hsmul _ _ hF, h, smul_mul_assoc]
    · intro F hF hb
      have h₁ := hmul₁ ⟨F, hF⟩ G hG
      rw [← hcontΦ ⟨F, hF⟩] at h₁
      exact h₁
    · intro F f hF hf h hC hl
      ext ψ
      refine ext_inner_left ℂ fun φ => ?_
      obtain ⟨C, hC⟩ := hC
      obtain ⟨hm, C', hC'⟩ := id hG
      have h₁ : Tendsto (fun n => ⟪φ, Φ (F n * G) ψ⟫_ℂ) atTop (𝓝 ⟪φ, Φ (f * G) ψ⟫_ℂ) :=
        hweak _ _ (fun n => isBddMeasurable_mul (hF n) hG) (isBddMeasurable_mul hf hG)
          ⟨C * C', fun n x => by
            have h₀ : 0 ≤ C := (norm_nonneg _).trans (hC n x)
            simpa using mul_le_mul (hC n x) (hC' x) (norm_nonneg _) h₀⟩
          (fun x => (hl x).mul_const (G x)) φ ψ
      have h₂ := hweak _ _ hF hf ⟨C, hC⟩ hl φ (Φ G ψ)
      have h₃ : ∀ n, ⟪φ, Φ (F n * G) ψ⟫_ℂ = ⟪φ, Φ (F n) (Φ G ψ)⟫_ℂ := by
        intro n
        rw [h n, ContinuousLinearMap.mul_apply]
      simp only [h₃] at h₁
      rw [tendsto_nhds_unique h₁ h₂, ContinuousLinearMap.mul_apply]
  let e : MeasSet X → BddOp H := fun Y => Φ (indicatorOne Y.1)
  have hdiag : ∀ ψ (Y : MeasSet X), ⟪ψ, e Y ψ⟫_ℂ = (((μ ψ).real Y.1 : ℝ) : ℂ) := by
    intro ψ Y
    change ⟪ψ, Φ (indicatorOne Y.1) ψ⟫_ℂ = _
    rw [hΦ _ (isBddMeasurable_indicatorOne Y)]
    have h₁ := integral_indicator_const (μ := μ ψ) (1 : ℂ) Y.2
    change ∫ x, Y.1.indicator (fun _ => (1 : ℂ)) x ∂(μ ψ) = _
    simpa using h₁
  have hinter : ∀ Y Y' : MeasSet X,
      e ⟨Y.1 ∩ Y'.1, Y.2.inter Y'.2⟩ = e Y * e Y' := by
    intro Y Y'
    have h₁ : (indicatorOne (Y.1 ∩ Y'.1) : X → ℂ) =
        indicatorOne Y.1 * indicatorOne Y'.1 := by
      funext x
      by_cases h : x ∈ Y.1 <;> by_cases h' : x ∈ Y'.1 <;>
        simp [indicatorOne, constOne, h, h']
    change Φ (indicatorOne (Y.1 ∩ Y'.1)) = _
    rw [h₁]
    exact hmul _ (isBddMeasurable_indicatorOne Y') _ (isBddMeasurable_indicatorOne Y)
  have hself : ∀ Y, IsSymmetricOp (e Y) := by
    intro Y
    rw [isSymmetricOp_iff, ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric,
      LinearMap.isSymmetric_iff_inner_map_self_real]
    intro ψ
    have h₁ : ⟪(e Y : H →ₗ[ℂ] H) ψ, ψ⟫_ℂ = conj ⟪ψ, e Y ψ⟫_ℂ :=
      (inner_conj_symm _ _).symm
    rw [h₁, hdiag, Complex.conj_ofReal, Complex.conj_ofReal]
  have hpvm : IsPVM e :=
    { isOrthProj := fun Y => ⟨hself Y, by
        have h₁ := hinter Y Y
        have h₂ : (⟨Y.1 ∩ Y.1, Y.2.inter Y.2⟩ : MeasSet X) = Y :=
          Subtype.ext (Set.inter_self _)
        rw [h₂] at h₁
        rw [pow_two]
        exact h₁.symm⟩
      map_univ := by
        have h₁ : (indicatorOne (Set.univ : Set X) : X → ℂ) = ((1 : C(X, ℂ)) : X → ℂ) := by
          funext x
          simp [indicatorOne, constOne]
        change Φ (indicatorOne Set.univ) = _
        rw [h₁, hcontΦ, hL.map_one]
        rfl
      map_inter := hinter
      countablyAdditive := fun ψ Y hd => by
        have h₁ := measure_iUnion (μ := μ ψ) hd (fun k => (Y k).2)
        have h₂ : ∑' k, μ ψ (Y k).1 ≠ ⊤ := by
          rw [← h₁]
          exact measure_ne_top _ _
        have h₃ := ENNReal.hasSum_toReal h₂
        rw [← ENNReal.tsum_toReal_eq (fun k => measure_ne_top _ _), ← h₁] at h₃
        have h₄ := Complex.hasSum_ofReal.mpr h₃
        simp only [diagForm, hdiag]
        exact h₄ }
  let E : PVM X H := ⟨e, hpvm⟩
  have hsm : ∀ ψ, E.diagMeasure ψ = μ ψ := fun ψ => Measure.ext fun Y hY => by
    have h₁ := E.diagMeasure_apply ψ ⟨Y, hY⟩
    have h₂ : diagForm E ψ ⟨Y, hY⟩ = (((μ ψ).real Y : ℝ) : ℂ) := hdiag ψ ⟨Y, hY⟩
    rw [h₂, Complex.ofReal_re] at h₁
    rw [h₁, Measure.real, ENNReal.ofReal_toReal (measure_ne_top _ _)]
  refine ⟨E, fun f => ?_⟩
  have h₁ : E.IsBddIntegral f (L f) := fun ψ => by
    rw [hsm, hμ]
  exact ((hrules X H E).existsUnique_bddIntegral f (bmCont f)).unique
    (E.isBddIntegral_bddIntegral ⟨_, h₁⟩) h₁
end Representation
section Polynomials
theorem evalPoly_zero : evalPoly 0 = 0 := by
  funext p
  simp [evalPoly]
theorem evalPoly_add (c c' : Coeffs) :
    evalPoly (c + c') = evalPoly c + evalPoly c' := by
  funext p
  simp only [evalPoly, Pi.add_apply]
  exact Finsupp.sum_add_index' (by simp) (fun i a b => by ring)
theorem evalPoly_smul (z : ℂ) (c : Coeffs) :
    evalPoly (z • c) = z • evalPoly c := by
  funext p
  simp only [evalPoly, Pi.smul_apply, smul_eq_mul]
  rw [Finsupp.sum_smul_index (by simp), Finsupp.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring
theorem evalPoly_single (i : ℕ × ℤ) (z : ℂ) :
    evalPoly (Finsupp.single i z) =
      fun p => z * ((p.1.1 : ℝ) : ℂ) ^ i.1 * p.1.2 ^ i.2 := by
  funext p
  simp [evalPoly]
def evalPolyCM : Coeffs →ₗ[ℂ] C(intervalCircle, ℂ) where
  toFun c := ⟨evalPoly c, PolynomialBound.continuous_evalPoly c⟩
  map_add' c c' := ContinuousMap.ext fun p => congrFun (evalPoly_add c c') p
  map_smul' z c := ContinuousMap.ext fun p => congrFun (evalPoly_smul z c) p
theorem evalPolyCM_coe (c : Coeffs) :
    (evalPolyCM c : intervalCircle → ℂ) = evalPoly c := rfl
theorem snd_ne_zero (p : intervalCircle) : p.1.2 ≠ 0 := by
  intro h
  have h₁ : ‖p.1.2‖ = 1 := p.2.2
  rw [h] at h₁
  simp at h₁
theorem conj_snd (p : intervalCircle) : conj p.1.2 = p.1.2⁻¹ :=
  (Complex.inv_eq_conj p.2.2).symm
theorem isBddMeasurable_continuousMap (f : C(intervalCircle, ℂ)) :
    IsBddMeasurable (f : intervalCircle → ℂ) :=
  ⟨f.continuous.measurable, ‖f‖, fun x => f.norm_coe_le_norm x⟩
theorem isBddMeasurable_evalPoly (c : Coeffs) : IsBddMeasurable (evalPoly c) :=
  isBddMeasurable_continuousMap (evalPolyCM c)
end Polynomials
section Pair
variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {A V : BddOp H}
theorem evalPolyOp_zero : evalPolyOp 0 A V = 0 := by
  simp [evalPolyOp]
theorem evalPolyOp_add (c c' : Coeffs) :
    evalPolyOp (c + c') A V = evalPolyOp c A V + evalPolyOp c' A V :=
  Finsupp.sum_add_index' (by simp) (fun i a b => add_smul a b _)
theorem evalPolyOp_smul (z : ℂ) (c : Coeffs) :
    evalPolyOp (z • c) A V = z • evalPolyOp c A V := by
  simp only [evalPolyOp]
  rw [Finsupp.sum_smul_index (by simp), Finsupp.smul_sum]
  exact Finset.sum_congr rfl fun i _ => mul_smul _ _ _
theorem evalPolyOp_single (i : ℕ × ℤ) (z : ℂ) :
    evalPolyOp (Finsupp.single i z) A V = z • (A ^ i.1 * zpowOp V i.2) := by
  simp [evalPolyOp]
variable (A V) in
def evalPolyOpLin : Coeffs →ₗ[ℂ] BddOp H where
  toFun c := evalPolyOp c A V
  map_add' := evalPolyOp_add
  map_smul' := evalPolyOp_smul
def unitOp (hp : IsCommutingPair A V) : (BddOp H)ˣ :=
  ⟨V, opInv V, (isTwoSidedInverse_opInv hp.unitary).1,
    (isTwoSidedInverse_opInv hp.unitary).2⟩
theorem zpowOp_eq_zpow (hp : IsCommutingPair A V) (y : ℤ) :
    zpowOp V y = ((unitOp hp ^ y : (BddOp H)ˣ) : BddOp H) := by
  obtain ⟨n, rfl | rfl⟩ := y.eq_nat_or_neg
  · rw [zpowOp_natCast, zpow_natCast, Units.val_pow_eq_pow_val]
    rfl
  · rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [zpowOp_zero]
    · rw [zpowOp_of_neg _ (by omega), zpow_neg, zpow_natCast, ← inv_pow,
        Units.val_pow_eq_pow_val]
      simp only [neg_neg, Int.toNat_natCast]
      rfl
theorem zpowOp_add (hp : IsCommutingPair A V) (y y' : ℤ) :
    zpowOp V (y + y') = zpowOp V y * zpowOp V y' := by
  rw [zpowOp_eq_zpow hp, zpowOp_eq_zpow hp, zpowOp_eq_zpow hp, zpow_add, Units.val_mul]
theorem commute_zpowOp (hp : IsCommutingPair A V) (y : ℤ) :
    Commute A (zpowOp V y) := by
  rw [zpowOp_eq_zpow hp]
  exact Commute.units_zpow_right (u := unitOp hp) hp.comm y
theorem star_eq_self (hp : IsCommutingPair A V) : star A = A :=
  ((isSymmetricOp_iff A).mp hp.symm).star_eq
theorem star_eq_opInv (hp : IsCommutingPair A V) : star V = opInv V := by
  have hiso : ∀ φ ψ, ⟪V φ, V ψ⟫_ℂ = ⟪φ, ψ⟫_ℂ :=
    (LinearIsometry.mk (V : H →ₗ[ℂ] H) hp.unitary.isometric).inner_map_map
  have h₁ : star V * V = 1 := by
    ext ψ
    refine ext_inner_left ℂ fun φ => ?_
    rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.mul_apply,
      ContinuousLinearMap.adjoint_inner_right, hiso, ContinuousLinearMap.one_apply]
  calc star V = star V * (V * opInv V) := by
        rw [(isTwoSidedInverse_opInv hp.unitary).1, mul_one]
    _ = opInv V := by rw [← mul_assoc, h₁, one_mul]
theorem star_zpowOp (hp : IsCommutingPair A V) (y : ℤ) :
    star (zpowOp V y) = zpowOp V (-y) := by
  obtain ⟨n, rfl | rfl⟩ := y.eq_nat_or_neg
  · rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [zpowOp_zero]
    · rw [zpowOp_natCast, star_pow, star_eq_opInv hp, zpowOp_of_neg _ (by omega)]
      simp
  · rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [zpowOp_zero]
    · rw [zpowOp_of_neg _ (by omega), star_pow, ← star_eq_opInv hp, star_star, neg_neg,
        zpowOp_natCast]
      simp
theorem exists_coeffs_mul (hp : IsCommutingPair A V) (c c' : Coeffs) :
    ∃ d : Coeffs,
      evalPoly d = evalPoly c * evalPoly c' ∧
      evalPolyOp d A V = evalPolyOp c A V * evalPolyOp c' A V := by
  induction c using Finsupp.induction_linear with
  | zero =>
    exact ⟨0, by rw [evalPoly_zero, zero_mul], by rw [evalPolyOp_zero, zero_mul]⟩
  | add a b ha hb =>
    obtain ⟨d, h₁, h₂⟩ := ha
    obtain ⟨d', h₁', h₂'⟩ := hb
    exact ⟨d + d', by rw [evalPoly_add, evalPoly_add, h₁, h₁', add_mul],
      by rw [evalPolyOp_add, evalPolyOp_add, h₂, h₂', add_mul]⟩
  | single i z =>
    induction c' using Finsupp.induction_linear with
    | zero =>
      exact ⟨0, by rw [evalPoly_zero, mul_zero], by rw [evalPolyOp_zero, mul_zero]⟩
    | add a b ha hb =>
      obtain ⟨d, h₁, h₂⟩ := ha
      obtain ⟨d', h₁', h₂'⟩ := hb
      exact ⟨d + d', by rw [evalPoly_add, evalPoly_add, h₁, h₁', mul_add],
        by rw [evalPolyOp_add, evalPolyOp_add, h₂, h₂', mul_add]⟩
    | single j w =>
      refine ⟨Finsupp.single (i + j) (z * w), ?_, ?_⟩
      · rw [evalPoly_single, evalPoly_single, evalPoly_single]
        funext p
        simp only [Pi.mul_apply, Prod.fst_add, Prod.snd_add]
        rw [pow_add, zpow_add₀ (snd_ne_zero p)]
        ring
      · rw [evalPolyOp_single, evalPolyOp_single, evalPolyOp_single, smul_mul_smul_comm]
        congr 1
        have h₁ : zpowOp V i.2 * A ^ j.1 = A ^ j.1 * zpowOp V i.2 :=
          (((commute_zpowOp hp i.2).pow_left j.1).eq).symm
        simp only [Prod.fst_add, Prod.snd_add]
        rw [pow_add, zpowOp_add hp, mul_assoc, mul_assoc, ← mul_assoc (zpowOp V i.2),
          h₁, mul_assoc]
theorem exists_coeffs_star (hp : IsCommutingPair A V) (c : Coeffs) :
    ∃ d : Coeffs,
      evalPoly d = (fun p => conj (evalPoly c p)) ∧
      evalPolyOp d A V = star (evalPolyOp c A V) := by
  induction c using Finsupp.induction_linear with
  | zero =>
    refine ⟨0, ?_, by rw [evalPolyOp_zero, star_zero]⟩
    funext p
    simp [evalPoly_zero]
  | add a b ha hb =>
    obtain ⟨d, h₁, h₂⟩ := ha
    obtain ⟨d', h₁', h₂'⟩ := hb
    refine ⟨d + d', ?_, by rw [evalPolyOp_add, evalPolyOp_add, h₂, h₂', star_add]⟩
    funext p
    rw [evalPoly_add, evalPoly_add, Pi.add_apply, Pi.add_apply, h₁, h₁', map_add]
  | single i z =>
    refine ⟨Finsupp.single (i.1, -i.2) (conj z), ?_, ?_⟩
    · rw [evalPoly_single, evalPoly_single]
      funext p
      simp only [map_mul, map_pow, map_zpow₀, Complex.conj_ofReal, conj_snd, zpow_neg, inv_zpow]
    · rw [evalPolyOp_single, evalPolyOp_single, star_smul, star_mul, star_pow,
        star_eq_self hp, star_zpowOp hp]
      have h₁ := ((commute_zpowOp hp (-i.2)).pow_left i.1).eq
      simp only [h₁]
      rfl
theorem norm_evalPolyOp_le (hb : PolynomialBound.statement) (hp : IsCommutingPair A V)
    (c : Coeffs) : ‖evalPolyOp c A V‖ ≤ ‖evalPolyCM c‖ := by
  obtain ⟨c', hf', ht'⟩ := exists_coeffs_star hp c
  obtain ⟨d, hf, ht⟩ := exists_coeffs_mul hp c' c
  refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun ψ => ?_
  have h₁ : ⟪ψ, evalPolyOp d A V ψ⟫_ℂ = ((‖evalPolyOp c A V ψ‖ ^ 2 : ℝ) : ℂ) := by
    rw [ht, ht', ContinuousLinearMap.mul_apply, ContinuousLinearMap.star_eq_adjoint,
      ContinuousLinearMap.adjoint_inner_right, inner_self_eq_norm_sq_to_K]
    push_cast
    rfl
  have h₂ := (hb H A V hp d ψ).1
  have h₃ : (⨆ x : intervalCircle, ‖evalPoly d x‖) ≤ ‖evalPolyCM c‖ ^ 2 := by
    haveI := PolynomialBound.nonempty_intervalCircle
    refine ciSup_le fun x => ?_
    rw [hf, Pi.mul_apply, hf', norm_mul, Complex.norm_conj, ← pow_two]
    exact pow_le_pow_left₀ (norm_nonneg _) ((evalPolyCM c).norm_coe_le_norm x) 2
  rw [h₁, Complex.norm_real, Real.norm_of_nonneg (by positivity)] at h₂
  have h₄ : ‖evalPolyOp c A V ψ‖ ^ 2 ≤ (‖evalPolyCM c‖ * ‖ψ‖) ^ 2 := by
    rw [mul_pow]
    exact h₂.trans (mul_le_mul_of_nonneg_right h₃ (by positivity))
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp h₄
theorem evalPolyCM_radial :
    (evalPolyCM (Finsupp.single (1, 0) 1) : intervalCircle → ℂ) = radialCoord := by
  rw [evalPolyCM_coe, evalPoly_single]
  funext p
  simp [radialCoord]
theorem evalPolyCM_angular :
    (evalPolyCM (Finsupp.single (0, 1) 1) : intervalCircle → ℂ) = angularCoord := by
  rw [evalPolyCM_coe, evalPoly_single]
  funext p
  simp [angularCoord]
theorem evalPolyCM_const (z : ℂ) :
    evalPolyCM (Finsupp.single (0, 0) z) = algebraMap ℂ C(intervalCircle, ℂ) z := by
  refine ContinuousMap.ext fun p => ?_
  change evalPoly (Finsupp.single (0, 0) z) p = z
  rw [evalPoly_single]
  simp
theorem denseRange_evalPolyCM (hp : IsCommutingPair A V) :
    DenseRange (evalPolyCM : Coeffs → C(intervalCircle, ℂ)) := by
  let S : StarSubalgebra ℂ C(intervalCircle, ℂ) :=
    { carrier := Set.range evalPolyCM
      mul_mem' := by
        rintro _ _ ⟨c, rfl⟩ ⟨c', rfl⟩
        obtain ⟨d, hd, -⟩ := exists_coeffs_mul hp c c'
        exact ⟨d, ContinuousMap.ext fun p => congrFun hd p⟩
      add_mem' := by
        rintro _ _ ⟨c, rfl⟩ ⟨c', rfl⟩
        exact ⟨c + c', map_add _ _ _⟩
      algebraMap_mem' := fun z => ⟨_, evalPolyCM_const z⟩
      star_mem' := by
        rintro _ ⟨c, rfl⟩
        obtain ⟨d, hd, -⟩ := exists_coeffs_star hp c
        exact ⟨d, ContinuousMap.ext fun p => congrFun hd p⟩ }
  have hsep : S.SeparatesPoints := by
    intro p q hpq
    by_cases h : p.1.1 = q.1.1
    · have h₂ : p.1.2 ≠ q.1.2 := fun h₂ => hpq (Subtype.ext (Prod.ext h h₂))
      refine ⟨_, ⟨evalPolyCM (Finsupp.single (0, 1) 1), ⟨_, rfl⟩, rfl⟩, ?_⟩
      beta_reduce
      rw [evalPolyCM_angular]
      exact h₂
    · refine ⟨_, ⟨evalPolyCM (Finsupp.single (1, 0) 1), ⟨_, rfl⟩, rfl⟩, ?_⟩
      beta_reduce
      rw [evalPolyCM_radial]
      exact fun h₂ => h (Complex.ofReal_injective h₂)
  have hcl := ContinuousMap.starSubalgebra_topologicalClosure_eq_top_of_separatesPoints S hsep
  intro f
  exact show f ∈ S.topologicalClosure from by
    rw [hcl]
    trivial
theorem exists_starRep (hb : PolynomialBound.statement) (hp : IsCommutingPair A V) :
    ∃ L : C(intervalCircle, ℂ) →ₗ[ℂ] BddOp H, IsStarRep L ∧
      ∀ c, L (evalPolyCM c) = evalPolyOp c A V := by
  have hd := denseRange_evalPolyCM hp
  have hn : ∀ c, ‖evalPolyOpLin A V c‖ ≤ 1 * ‖evalPolyCM c‖ := fun c => by
    rw [one_mul]
    exact norm_evalPolyOp_le hb hp c
  let Λ : C(intervalCircle, ℂ) →L[ℂ] BddOp H := (evalPolyOpLin A V).extendOfNorm evalPolyCM
  have heq : ∀ c, Λ (evalPolyCM c) = evalPolyOp c A V :=
    fun c => LinearMap.extendOfNorm_eq hd ⟨1, hn⟩ c
  have hmul : ∀ f g, Λ (f * g) = Λ f * Λ g := by
    intro f g
    refine hd.induction_on₂ (p := fun f g => Λ (f * g) = Λ f * Λ g) (isClosed_eq ?_ ?_) ?_ f g
    · exact Λ.continuous.comp (continuous_fst.mul continuous_snd)
    · exact (Λ.continuous.comp continuous_fst).mul (Λ.continuous.comp continuous_snd)
    · intro c c'
      obtain ⟨d, hf, ht⟩ := exists_coeffs_mul hp c c'
      have h₁ : evalPolyCM c * evalPolyCM c' = evalPolyCM d :=
        ContinuousMap.ext fun p => (congrFun hf p).symm
      rw [h₁, heq, heq, heq, ht]
  have hstar : ∀ f, star (Λ f) = Λ (star f) := by
    intro f
    refine hd.induction_on (p := fun f => star (Λ f) = Λ (star f)) f (isClosed_eq ?_ ?_) ?_
    · exact continuous_star.comp Λ.continuous
    · exact Λ.continuous.comp continuous_star
    · intro c
      obtain ⟨d, hf, ht⟩ := exists_coeffs_star hp c
      have h₁ : star (evalPolyCM c) = evalPolyCM d :=
        ContinuousMap.ext fun p => (congrFun hf p).symm
      rw [h₁, heq, heq, ht]
  refine ⟨(Λ : C(intervalCircle, ℂ) →ₗ[ℂ] BddOp H), ⟨?_, hmul, ?_⟩, heq⟩
  · change Λ 1 = 1
    have h₁ : (1 : C(intervalCircle, ℂ)) = evalPolyCM (Finsupp.single (0, 0) 1) := by
      rw [evalPolyCM_const, map_one]
    rw [h₁, heq, evalPolyOp_single]
    simp [zpowOp_zero]
  · intro f φ ψ
    change ⟪φ, Λ f ψ⟫_ℂ = ⟪Λ (star f) φ, ψ⟫_ℂ
    rw [← hstar, ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_left]
theorem exists_isJointSpectralMeasure (hb : PolynomialBound.statement)
    (hclass : BddLimitClassHyp) (hriesz : RieszHyp) (hrules : BddCalculusHyp)
    (hp : IsCommutingPair A V) : ∃ E, IsJointSpectralMeasure A V E := by
  obtain ⟨L, hL, hc⟩ := exists_starRep hb hp
  obtain ⟨E, hE⟩ := exists_pvm_of_starRep hclass hriesz hrules hL
  refine ⟨E, ?_, ?_⟩
  · have h₁ := hE (evalPolyCM (Finsupp.single (1, 0) 1))
    rw [evalPolyCM_radial, hc, evalPolyOp_single] at h₁
    rw [h₁]
    simp [zpowOp_zero]
  · have h₁ := hE (evalPolyCM (Finsupp.single (0, 1) 1))
    rw [evalPolyCM_angular, hc, evalPolyOp_single] at h₁
    rw [h₁]
    have h₂ := zpowOp_natCast V 1
    simpa using h₂
theorem isJointSpectralMeasure_jointSpectralMeasure (hb : PolynomialBound.statement)
    (hclass : BddLimitClassHyp) (hriesz : RieszHyp) (hrules : BddCalculusHyp)
    (hp : IsCommutingPair A V) : IsJointSpectralMeasure A V (jointSpectralMeasure A V) := by
  unfold jointSpectralMeasure
  exact Classical.epsilon_spec (exists_isJointSpectralMeasure hb hclass hriesz hrules hp)
end Pair
section Integrals
variable {X H : Type} [MeasurableSpace X]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
theorem isBddMeasurable_pow {u : X → ℂ} (hu : IsBddMeasurable u) (n : ℕ) :
    IsBddMeasurable (u ^ n) := by
  induction n with
  | zero =>
    rw [pow_zero]
    exact ⟨measurable_const, 1, by simp⟩
  | succ n ih =>
    rw [pow_succ]
    exact isBddMeasurable_mul ih hu
theorem bddIntegral_pow {E : PVM X H} (R : BddCalculus.Laws E)
    {u : X → ℂ} (hu : IsBddMeasurable u) (n : ℕ) :
    E.bddIntegral (u ^ n) = E.bddIntegral u ^ n := by
  induction n with
  | zero =>
    rw [pow_zero, pow_zero]
    exact R.bddIntegral_one
  | succ n ih =>
    rw [pow_succ, pow_succ, R.bddIntegral_mul _ _ (isBddMeasurable_pow hu n) hu, ih]
theorem bddIntegral_zero {E : PVM X H} (R : BddCalculus.Laws E) :
    E.bddIntegral (0 : X → ℂ) = 0 := by
  have h₁ := R.bddIntegral_smul 0 0 ⟨measurable_const, 0, by simp⟩
  simpa using h₁
theorem pvm_ext {E E' : PVM X H} (h : ∀ Y, E Y = E' Y) : E = E' := by
  obtain ⟨e, he⟩ := E
  obtain ⟨e', he'⟩ := E'
  have h₁ : e = e' := funext h
  cases h₁
  rfl
end Integrals
section Comparison
variable {H H' : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup H'] [InnerProductSpace ℂ H'] [CompleteSpace H']
  {A V : BddOp H} {A' V' : BddOp H'}
theorem zpowOp_neg_natCast (V : BddOp H) (n : ℕ) :
    zpowOp V (-(n : ℤ)) = opInv V ^ n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [zpowOp_zero]
  · rw [zpowOp_of_neg _ (by omega)]
    simp
theorem bddIntegral_zpow_angular (hrules : BddCalculusHyp) (hp : IsCommutingPair A V)
    {E : PVM intervalCircle H} (hE : IsJointSpectralMeasure A V E) (y : ℤ) :
    E.bddIntegral (fun p : intervalCircle => p.1.2 ^ y) = zpowOp V y := by
  have R := hrules intervalCircle H E
  have hζ : IsBddMeasurable angularCoord :=
    evalPolyCM_angular ▸ isBddMeasurable_continuousMap _
  have hc : (fun p : intervalCircle => p.1.2⁻¹) = evalPoly (Finsupp.single (0, -1) 1) := by
    rw [evalPoly_single]
    funext p
    simp
  have hζ' : IsBddMeasurable (fun p : intervalCircle => p.1.2⁻¹) :=
    hc ▸ isBddMeasurable_evalPoly _
  have hinv : E.bddIntegral (fun p : intervalCircle => p.1.2⁻¹) = opInv V := by
    have h₁ := R.bddIntegral_mul _ _ hζ' hζ
    have h₂ : (fun p : intervalCircle => p.1.2⁻¹) * angularCoord = fun _ => 1 := by
      funext p
      exact inv_mul_cancel₀ (snd_ne_zero p)
    rw [h₂, R.bddIntegral_one, hE.2] at h₁
    have h₃ := (isTwoSidedInverse_opInv hp.unitary).1
    calc E.bddIntegral (fun p : intervalCircle => p.1.2⁻¹)
        = E.bddIntegral (fun p : intervalCircle => p.1.2⁻¹) * (V * opInv V) := by
          rw [h₃, mul_one]
      _ = opInv V := by
          rw [← mul_assoc, ← h₁]
          exact one_mul _
  obtain ⟨n, rfl | rfl⟩ := y.eq_nat_or_neg
  · have h₁ : (fun p : intervalCircle => p.1.2 ^ (n : ℤ)) = angularCoord ^ n := by
      funext p
      simp [angularCoord]
    rw [h₁, bddIntegral_pow R hζ, hE.2, zpowOp_natCast]
  · have h₁ : (fun p : intervalCircle => p.1.2 ^ (-(n : ℤ))) =
        (fun p : intervalCircle => p.1.2⁻¹) ^ n := by
      funext p
      simp
    rw [h₁, bddIntegral_pow R hζ', hinv, zpowOp_neg_natCast]
theorem bddIntegral_evalPoly (hrules : BddCalculusHyp) (hp : IsCommutingPair A V)
    {E : PVM intervalCircle H} (hE : IsJointSpectralMeasure A V E) (c : Coeffs) :
    E.bddIntegral (evalPoly c) = evalPolyOp c A V := by
  have R := hrules intervalCircle H E
  have hrad : IsBddMeasurable radialCoord :=
    evalPolyCM_radial ▸ isBddMeasurable_continuousMap _
  induction c using Finsupp.induction_linear with
  | zero => rw [evalPoly_zero, evalPolyOp_zero, bddIntegral_zero R]
  | add a b ha hb =>
    rw [evalPoly_add, evalPolyOp_add,
      R.bddIntegral_add _ _ (isBddMeasurable_evalPoly a) (isBddMeasurable_evalPoly b), ha, hb]
  | single i z =>
    have hZ : (fun p : intervalCircle => p.1.2 ^ i.2) =
        evalPoly (Finsupp.single (0, i.2) 1) := by
      rw [evalPoly_single]
      funext p
      simp
    have hZb : IsBddMeasurable (fun p : intervalCircle => p.1.2 ^ i.2) :=
      hZ ▸ isBddMeasurable_evalPoly _
    have h₁ : evalPoly (Finsupp.single i z) =
        z • (radialCoord ^ i.1 * fun p : intervalCircle => p.1.2 ^ i.2) := by
      rw [evalPoly_single]
      funext p
      simp [radialCoord, mul_assoc]
    rw [h₁, evalPolyOp_single,
      R.bddIntegral_smul _ _ (isBddMeasurable_mul (isBddMeasurable_pow hrad _) hZb),
      R.bddIntegral_mul _ _ (isBddMeasurable_pow hrad _) hZb, bddIntegral_pow R hrad, hE.1,
      bddIntegral_zpow_angular hrules hp hE]
theorem intervalCircle_induction (hclass : BddLimitClassHyp) (hp : IsCommutingPair A V)
    (P : (intervalCircle → ℂ) → Prop)
    (hadd : ∀ f g, IsBddMeasurable f → IsBddMeasurable g → P f → P g →
      P (f + g))
    (hsmul : ∀ (z : ℂ) f, IsBddMeasurable f → P f → P (z • f))
    (hpoly : ∀ c, P (evalPoly c))
    (hlim : ∀ (F : ℕ → intervalCircle → ℂ) (f : intervalCircle → ℂ),
      (∀ n, IsBddMeasurable (F n)) → IsBddMeasurable f → (∀ n, P (F n)) →
      (∃ C : ℝ, ∀ n x, ‖F n x‖ ≤ C) → (∀ x, Tendsto (fun n => F n x) atTop (𝓝 (f x))) → P f) :
    ∀ f, IsBddMeasurable f → P f := by
  refine bddMeasurable_induction hclass P hadd hsmul ?_ hlim
  intro f hf hb
  let g : C(intervalCircle, ℂ) := ⟨f, hf⟩
  have hcl : g ∈ closure (Set.range (evalPolyCM : Coeffs → C(intervalCircle, ℂ))) :=
    denseRange_evalPolyCM hp g
  obtain ⟨u, hu, hl⟩ := mem_closure_iff_seq_limit.mp hcl
  choose c hc using hu
  have hval : ∀ n x, evalPoly (c n) x = u n x := fun n x => by
    rw [← hc n]
    rfl
  have hbd : ∃ C : ℝ, ∀ n x, ‖evalPoly (c n) x‖ ≤ C := by
    obtain ⟨C, hC⟩ := (Metric.isBounded_range_of_tendsto u hl).exists_norm_le
    refine ⟨C, fun n x => ?_⟩
    rw [hval]
    exact ((u n).norm_coe_le_norm x).trans (hC _ ⟨n, rfl⟩)
  refine hlim (fun n => evalPoly (c n)) f
    (fun n => isBddMeasurable_evalPoly _) ⟨hf.measurable, hb⟩ (fun n => hpoly _) hbd
    fun x => ?_
  have h₂ : Tendsto (fun n => u n x) atTop (𝓝 (g x)) :=
    ((continuous_eval_const x).tendsto g).comp hl
  simp only [hval]
  exact h₂
theorem comp_evalPolyOp (hp : IsCommutingPair A V) (hp' : IsCommutingPair A' V')
    (B : BddOpBetween H H') (hA : B ∘L A = A' ∘L B) (hV : B ∘L V = V' ∘L B)
    (c : Coeffs) :
    B ∘L evalPolyOp c A V = evalPolyOp c A' V' ∘L B := by
  have hAψ : ∀ ψ, B (A ψ) = A' (B ψ) := fun ψ => DFunLike.congr_fun hA ψ
  have hVψ : ∀ ψ, B (V ψ) = V' (B ψ) := fun ψ => DFunLike.congr_fun hV ψ
  have hWψ : ∀ ψ, B (opInv V ψ) = opInv V' (B ψ) := by
    intro ψ
    have h₁ : V (opInv V ψ) = ψ :=
      DFunLike.congr_fun (isTwoSidedInverse_opInv hp.unitary).1 ψ
    have h₂ : opInv V' (V' (B (opInv V ψ))) = B (opInv V ψ) :=
      DFunLike.congr_fun (isTwoSidedInverse_opInv hp'.unitary).2 _
    rw [← h₂, ← hVψ, h₁]
  have hpow : ∀ (S : BddOp H) (S' : BddOp H'),
      (∀ ψ, B (S ψ) = S' (B ψ)) → ∀ (n : ℕ) ψ, B ((S ^ n) ψ) = (S' ^ n) (B ψ) := by
    intro S S' hS n
    induction n with
    | zero => intro ψ; simp
    | succ n ih =>
      intro ψ
      rw [pow_succ', pow_succ', ContinuousLinearMap.mul_apply, ContinuousLinearMap.mul_apply, hS,
        ih]
  have hP : ∀ (y : ℤ) ψ, B (zpowOp V y ψ) = zpowOp V' y (B ψ) := by
    intro y ψ
    obtain ⟨n, rfl | rfl⟩ := y.eq_nat_or_neg
    · rw [zpowOp_natCast, zpowOp_natCast]
      exact hpow V V' hVψ n ψ
    · rw [zpowOp_neg_natCast, zpowOp_neg_natCast]
      exact hpow _ _ hWψ n ψ
  induction c using Finsupp.induction_linear with
  | zero =>
    rw [evalPolyOp_zero, evalPolyOp_zero]
    simp
  | add a b ha hb =>
    rw [evalPolyOp_add, evalPolyOp_add, ContinuousLinearMap.comp_add,
      ContinuousLinearMap.add_comp, ha, hb]
  | single i z =>
    ext ψ
    rw [evalPolyOp_single, evalPolyOp_single]
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.mul_apply, map_smul]
    rw [hpow A A' hAψ, hP]
theorem comp_bddIntegral (hclass : BddLimitClassHyp) (hrules : BddCalculusHyp)
    (hp : IsCommutingPair A V) (hp' : IsCommutingPair A' V')
    {E : PVM intervalCircle H} {E' : PVM intervalCircle H'}
    (hE : IsJointSpectralMeasure A V E) (hE' : IsJointSpectralMeasure A' V' E')
    (B : BddOpBetween H H') (hA : B ∘L A = A' ∘L B) (hV : B ∘L V = V' ∘L B) :
    ∀ f : intervalCircle → ℂ, IsBddMeasurable f →
      B ∘L E.bddIntegral f = E'.bddIntegral f ∘L B := by
  have R := hrules intervalCircle H E
  have R' := hrules intervalCircle H' E'
  refine intervalCircle_induction hclass hp _ ?_ ?_ ?_ ?_
  · intro f g hf hg h h'
    rw [R.bddIntegral_add _ _ hf hg, R'.bddIntegral_add _ _ hf hg, ContinuousLinearMap.comp_add,
      ContinuousLinearMap.add_comp, h, h']
  · intro z f hf h
    rw [R.bddIntegral_smul _ _ hf, R'.bddIntegral_smul _ _ hf, ContinuousLinearMap.comp_smul,
      ContinuousLinearMap.smul_comp, h]
  · intro c
    rw [bddIntegral_evalPoly hrules hp hE, bddIntegral_evalPoly hrules hp' hE']
    exact comp_evalPolyOp hp hp' B hA hV c
  · intro F f hF hf h hC hl
    ext ψ
    have h₁ := R.tendsto_bddIntegral F f hF hf hl hC ψ
    have h₂ := R'.tendsto_bddIntegral F f hF hf hl hC (B ψ)
    have h₃ : Tendsto (fun n => B (E.bddIntegral (F n) ψ)) atTop
        (𝓝 (B (E.bddIntegral f ψ))) :=
      (B.continuous.tendsto _).comp h₁
    have h₄ : ∀ n, B (E.bddIntegral (F n) ψ) = E'.bddIntegral (F n) (B ψ) :=
      fun n => DFunLike.congr_fun (h n) ψ
    simp only [h₄] at h₃
    exact tendsto_nhds_unique h₃ h₂
theorem eq_of_isJointSpectralMeasure (hclass : BddLimitClassHyp) (hrules : BddCalculusHyp)
    (hp : IsCommutingPair A V) {E E' : PVM intervalCircle H}
    (hE : IsJointSpectralMeasure A V E) (hE' : IsJointSpectralMeasure A V E') : E = E' := by
  have R := hrules intervalCircle H E
  have R' := hrules intervalCircle H E'
  refine pvm_ext fun Y => ?_
  have h₁ := comp_bddIntegral hclass hrules hp hp hE hE' (ContinuousLinearMap.id ℂ H)
    (by ext ψ; rfl) (by ext ψ; rfl) _ (isBddMeasurable_indicatorOne Y)
  rw [R.bddIntegral_indicator, R'.bddIntegral_indicator] at h₁
  simpa using h₁
def collapseAngle : intervalCircle → intervalCircle :=
  fun p => ⟨(p.1.1, 1), p.2.1, by simp [circleSet]⟩
theorem measurable_collapseAngle : Measurable collapseAngle :=
  Measurable.subtype_mk ((measurable_fst.comp measurable_subtype_coe).prodMk measurable_const)
theorem isCommutingPair_one (hp : IsCommutingPair A V) : IsCommutingPair A 1 :=
  { symm := hp.symm
    nonneg := hp.nonneg
    le_one := hp.le_one
    unitary := ⟨fun ψ => rfl, fun ψ => ⟨ψ, rfl⟩⟩
    comm := by simp }
theorem exists_collapsed (hrules : BddCalculusHyp) {E : PVM intervalCircle H}
    (hE : IsJointSpectralMeasure A V E) :
    ∃ D : PVM intervalCircle H, IsJointSpectralMeasure A 1 D ∧
      ∀ f : intervalCircle → ℂ, IsBddMeasurable f →
        D.bddIntegral f = E.bddIntegral (f ∘ collapseAngle) := by
  have R := hrules intervalCircle H E
  have hrad : IsBddMeasurable radialCoord :=
    evalPolyCM_radial ▸ isBddMeasurable_continuousMap _
  have hζ : IsBddMeasurable angularCoord :=
    evalPolyCM_angular ▸ isBddMeasurable_continuousMap _
  obtain ⟨h, -, hint⟩ := R.pushforward_laws intervalCircle collapseAngle measurable_collapseAngle
  refine ⟨⟨_, h⟩, ⟨?_, ?_⟩, hint⟩
  · rw [hint _ hrad]
    exact hE.1
  · rw [hint _ hζ]
    exact R.bddIntegral_one
theorem bddIntegral_comp_projIcc_eq (hclass : BddLimitClassHyp) (hrules : BddCalculusHyp)
    (hp : IsCommutingPair A V) {V₂ : BddOp H}
    {E E₂ : PVM intervalCircle H}
    (hE : IsJointSpectralMeasure A V E) (hE₂ : IsJointSpectralMeasure A V₂ E₂)
    (g : Set.Icc (0 : ℝ) 1 → ℂ) (hg : IsBddMeasurable g) :
    E.bddIntegral (g ∘ projIcc) = E₂.bddIntegral (g ∘ projIcc) := by
  obtain ⟨D, hD, hDi⟩ := exists_collapsed hrules hE
  obtain ⟨D₂, hD₂, hDi₂⟩ := exists_collapsed hrules hE₂
  have hDD : D = D₂ :=
    eq_of_isJointSpectralMeasure hclass hrules (isCommutingPair_one hp) hD hD₂
  have hb : IsBddMeasurable (g ∘ projIcc) := by
    obtain ⟨hm, C, hC⟩ := hg
    exact ⟨hm.comp measurable_projIcc, C, fun x => hC _⟩
  have h₁ := hDi _ hb
  have h₂ := hDi₂ _ hb
  have h₃ : (g ∘ projIcc) ∘ collapseAngle = g ∘ projIcc := rfl
  rw [h₃] at h₁ h₂
  rw [← h₁, ← h₂, hDD]
theorem isOrthProjOnto_ker (hrules : BddCalculusHyp)
    {E : PVM intervalCircle H} (hE : IsJointSpectralMeasure A V E) :
    IsOrthProjOnto (E (tube ⟨{0}, measurableSet_singleton 0⟩))
      (LinearMap.ker (A : H →ₗ[ℂ] H)) := by
  have R := hrules intervalCircle H E
  obtain ⟨Y₀, hY₀⟩ : ∃ Y₀, Y₀ = tube ⟨{0}, measurableSet_singleton 0⟩ := ⟨_, rfl⟩
  rw [← hY₀]
  have hmem : ∀ p : intervalCircle, radialCoord p = 0 → p ∈ Y₀.1 := by
    intro p hp
    have h₁ : p.1.1 = 0 := Complex.ofReal_eq_zero.mp hp
    rw [hY₀]
    exact Subtype.ext h₁
  have hmem' : ∀ p : intervalCircle, p ∈ Y₀.1 → radialCoord p = 0 := by
    intro p hp
    rw [hY₀] at hp
    have h₁ : projIcc p = 0 := hp
    have h₂ : p.1.1 = 0 := congrArg Subtype.val h₁
    simp [radialCoord, h₂]
  have hrad : IsBddMeasurable radialCoord :=
    evalPolyCM_radial ▸ isBddMeasurable_continuousMap _
  have hind := isBddMeasurable_indicatorOne Y₀
  have hzero : A * E Y₀ = 0 := by
    have h₁ := R.bddIntegral_mul _ _ hrad hind
    have h₂ : radialCoord * (indicatorOne Y₀.1 : intervalCircle → ℂ) = 0 := by
      funext p
      by_cases h : p ∈ Y₀.1
      · simp [hmem' p h]
      · simp [indicatorOne, h]
    rw [h₂, bddIntegral_zero R, hE.1, R.bddIntegral_indicator] at h₁
    exact h₁.symm
  refine ⟨E.2.isOrthProj Y₀, ?_⟩
  ext ψ
  constructor
  · intro hψ
    have hAψ : A ψ = 0 := hψ
    let w : intervalCircle → ℂ := (fun _ => 1) + (-1 : ℂ) • indicatorOne Y₀.1
    have h₁b : IsBddMeasurable (fun _ : intervalCircle => (1 : ℂ)) :=
      ⟨measurable_const, 1, by simp⟩
    have hw : IsBddMeasurable w :=
      isBddMeasurable_add h₁b (isBddMeasurable_smul _ hind)
    have hΦ : E.bddIntegral w = 1 - E Y₀ := by
      rw [R.bddIntegral_add _ _ h₁b (isBddMeasurable_smul _ hind), R.bddIntegral_smul _ _ hind,
        R.bddIntegral_one, R.bddIntegral_indicator, neg_one_smul, sub_eq_add_neg]
      rfl
    have h₀ : ∫ x, ‖radialCoord x‖ ^ 2 ∂(E.diagMeasure ψ) = 0 := by
      rw [← R.norm_bddIntegral_sq _ hrad, hE.1, hAψ]
      simp
    have hint : Integrable (fun x => ‖radialCoord x‖ ^ 2) (E.diagMeasure ψ) := by
      obtain ⟨hm, C, hC⟩ := hrad
      refine Integrable.of_bound (hm.norm.pow_const 2).aestronglyMeasurable (C ^ 2)
        (Eventually.of_forall fun x => ?_)
      rw [Real.norm_of_nonneg (by positivity)]
      exact pow_le_pow_left₀ (norm_nonneg _) (hC x) 2
    have hae := (integral_eq_zero_iff_of_nonneg (fun x => by positivity) hint).mp h₀
    have h₂ : ∫ x, ‖w x‖ ^ 2 ∂(E.diagMeasure ψ) = 0 := by
      refine integral_eq_zero_of_ae (hae.mono fun x hx => ?_)
      have h₃ : radialCoord x = 0 := by simpa using hx
      have h₄ := hmem x h₃
      simp [w, indicatorOne, constOne, h₄]
    have h₃ := R.norm_bddIntegral_sq w hw ψ
    rw [h₂, hΦ] at h₃
    have h₄ : (1 - E Y₀) ψ = 0 := by simpa using h₃
    have h₅ : ψ - E Y₀ ψ = 0 := h₄
    exact (sub_eq_zero.mp h₅).symm
  · intro hψ
    have hfix : E Y₀ ψ = ψ := hψ
    have h₁ : A (E Y₀ ψ) = 0 := DFunLike.congr_fun hzero ψ
    rw [hfix] at h₁
    exact h₁
end Comparison
theorem statement_of_hyps (hbern : PolynomialBound.statement)
    (hclass : Measurability.BoundedLimitClass.Claim)
    (hrules : BddCalculus.Statement)
    (hriesz : Measures.RieszMarkov.positiveFunctional_representation) : statement := by
  intro H _ _ _ A V hp
  have hE := isJointSpectralMeasure_jointSpectralMeasure hbern hclass hriesz hrules hp
  have R := hrules intervalCircle H (jointSpectralMeasure A V)
  refine ⟨⟨⟨_, hE, fun E' hE' => eq_of_isJointSpectralMeasure hclass hrules hp hE' hE⟩, hE⟩,
    fun c => bddIntegral_evalPoly hrules hp hE c, ⟨?_, ?_⟩, ?_,
    isOrthProjOnto_ker hrules hE⟩
  · intro H' _ _ _ A' V' B hp' hA hV
    have hE' := isJointSpectralMeasure_jointSpectralMeasure hbern hclass hriesz hrules hp'
    have R' := hrules intervalCircle H' (jointSpectralMeasure A' V')
    have hint := comp_bddIntegral hclass hrules hp hp' hE hE' B hA hV
    refine ⟨hint, fun hB => ?_⟩
    funext Y
    have h₁ := hint _ (isBddMeasurable_indicatorOne Y)
    rw [R.bddIntegral_indicator, R'.bddIntegral_indicator] at h₁
    ext χ
    obtain ⟨ψ, rfl⟩ := hB.onto χ
    have h₂ := (jointSpectralMeasure A V).conj_apply hB Y ψ
    have h₃ : B ((jointSpectralMeasure A V) Y ψ) = (jointSpectralMeasure A' V') Y (B ψ) :=
      DFunLike.congr_fun h₁ ψ
    exact h₃.symm.trans h₂.symm
  · intro C hA hV f hf
    exact comp_bddIntegral hclass hrules hp hp hE hE C hA hV f hf
  · intro V₂ hV₂ hc
    have hp₂ : IsCommutingPair A V₂ :=
      { symm := hp.symm
        nonneg := hp.nonneg
        le_one := hp.le_one
        unitary := hV₂
        comm := hc }
    have hE₂ := isJointSpectralMeasure_jointSpectralMeasure hbern hclass hriesz hrules hp₂
    have R₂ := hrules intervalCircle H (jointSpectralMeasure A V₂)
    have hg := fun g hg => bddIntegral_comp_projIcc_eq hclass hrules hp hE hE₂ g hg
    refine ⟨hg, fun Y => ?_⟩
    have h₁ := hg (indicatorOne Y.1) (isBddMeasurable_indicatorOne Y)
    have h₂ : (indicatorOne Y.1 : Set.Icc (0 : ℝ) 1 → ℂ) ∘ projIcc =
        indicatorOne (tube Y).1 := by
      funext p
      by_cases h : projIcc p ∈ Y.1
      · have h' : p ∈ (tube Y).1 := h
        simp [indicatorOne, constOne, h, h']
      · have h' : p ∉ (tube Y).1 := h
        simp [indicatorOne, constOne, h, h']
    rw [h₂, R.bddIntegral_indicator, R₂.bddIntegral_indicator] at h₁
    exact h₁
end ContractionUnitary.JointSpectral
end YangMills.Construction
end
