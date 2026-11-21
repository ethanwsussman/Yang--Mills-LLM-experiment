import YangMills.Construction.Probability.ExpectationBasicProperties
import Mathlib
open MeasureTheory
namespace YangMills.Construction.Probability
variable {Ω : Type} [MeasurableSpace Ω]
theorem IsBoundedComplexRV.measurable {f : Ω → ℂ}
    (hf : IsBoundedComplexRV f) : Measurable f := by
  have hdecomp : f = fun ω => ((f ω).re : ℂ) + ((f ω).im : ℂ) * Complex.I :=
    funext fun ω => (Complex.re_add_im _).symm
  rw [hdecomp]
  exact (Complex.measurable_ofReal.comp hf.measurable_re).add
    ((Complex.measurable_ofReal.comp hf.measurable_im).mul_const _)
theorem IsBoundedComplexRV.of_measurable {f : Ω → ℂ} (hm : Measurable f) (M : ℝ)
    (hM : ∀ ω, ‖f ω‖ ≤ M) : IsBoundedComplexRV f :=
  ⟨Complex.measurable_re.comp hm, Complex.measurable_im.comp hm, M, hM⟩
theorem IsBoundedComplexRV.integrable {f : Ω → ℂ}
    (hf : IsBoundedComplexRV f) (μ : Measure Ω) [IsFiniteMeasure μ] :
    Integrable f μ := by
  obtain ⟨M, hM⟩ := hf.bounded
  exact Integrable.of_bound hf.measurable.aestronglyMeasurable M (ae_of_all _ hM)
theorem IsBoundedRealRV.add {X Y : Ω → ℝ} (hX : IsBoundedRealRV X)
    (hY : IsBoundedRealRV Y) : IsBoundedRealRV (X + Y) := by
  obtain ⟨M, hM⟩ := hX.bounded
  obtain ⟨N, hN⟩ := hY.bounded
  exact ⟨hX.measurable.add hY.measurable, M + N, fun ω =>
    (abs_add_le _ _).trans (add_le_add (hM ω) (hN ω))⟩
theorem IsBoundedRealRV.smul (a : ℝ) {X : Ω → ℝ}
    (hX : IsBoundedRealRV X) : IsBoundedRealRV (a • X) := by
  obtain ⟨M, hM⟩ := hX.bounded
  refine ⟨hX.measurable.const_smul a, |a| * M, fun ω => ?_⟩
  simp only [Pi.smul_apply, smul_eq_mul, abs_mul]
  exact mul_le_mul_of_nonneg_left (hM ω) (abs_nonneg a)
theorem IsBoundedRealRV.const (a : ℝ) :
    IsBoundedRealRV fun _ : Ω => a :=
  ⟨measurable_const, |a|, fun _ => le_rfl⟩
theorem IsBoundedRealRV.mul {X Y : Ω → ℝ} (hX : IsBoundedRealRV X)
    (hY : IsBoundedRealRV Y) : IsBoundedRealRV (X * Y) := by
  obtain ⟨M, hM⟩ := hX.bounded
  obtain ⟨N, hN⟩ := hY.bounded
  refine ⟨hX.measurable.mul hY.measurable, M * N, fun ω => ?_⟩
  simp only [Pi.mul_apply, abs_mul]
  exact mul_le_mul (hM ω) (hN ω) (abs_nonneg _) ((abs_nonneg _).trans (hM ω))
theorem IsBoundedComplexRV.add {f g : Ω → ℂ}
    (hf : IsBoundedComplexRV f) (hg : IsBoundedComplexRV g) :
    IsBoundedComplexRV (f + g) := by
  obtain ⟨M, hM⟩ := hf.bounded
  obtain ⟨N, hN⟩ := hg.bounded
  exact .of_measurable (hf.measurable.add hg.measurable) (M + N) fun ω =>
    (norm_add_le _ _).trans (add_le_add (hM ω) (hN ω))
theorem IsBoundedComplexRV.smul (a : ℂ) {f : Ω → ℂ}
    (hf : IsBoundedComplexRV f) : IsBoundedComplexRV (a • f) := by
  obtain ⟨M, hM⟩ := hf.bounded
  refine .of_measurable (hf.measurable.const_mul a) (‖a‖ * M) fun ω => ?_
  simp only [Pi.smul_apply, smul_eq_mul, norm_mul]
  exact mul_le_mul_of_nonneg_left (hM ω) (norm_nonneg a)
theorem IsBoundedComplexRV.const (a : ℂ) :
    IsBoundedComplexRV fun _ : Ω => a :=
  .of_measurable measurable_const ‖a‖ fun _ => le_rfl
theorem IsBoundedComplexRV.mul {f g : Ω → ℂ}
    (hf : IsBoundedComplexRV f) (hg : IsBoundedComplexRV g) :
    IsBoundedComplexRV (f * g) := by
  obtain ⟨M, hM⟩ := hf.bounded
  obtain ⟨N, hN⟩ := hg.bounded
  refine .of_measurable (hf.measurable.mul hg.measurable) (M * N) fun ω => ?_
  simp only [Pi.mul_apply, norm_mul]
  exact mul_le_mul (hM ω) (hN ω) (norm_nonneg _) ((norm_nonneg _).trans (hM ω))
theorem IsBoundedRealRV.ofReal {X : Ω → ℝ}
    (hX : IsBoundedRealRV X) :
    IsBoundedComplexRV fun ω => (X ω : ℂ) := by
  obtain ⟨M, hM⟩ := hX.bounded
  refine .of_measurable (Complex.measurable_ofReal.comp hX.measurable) M fun ω => ?_
  simpa using hM ω
theorem isBoundedComplexRV_continuous_comp {n : ℕ} {X : Fin n → Ω → ℝ} {F : (Fin n → ℝ) → ℂ}
    (hX : ∀ i, IsBoundedRealRV (X i)) (hF : Continuous F) :
    IsBoundedComplexRV fun ω => F fun i => X i ω := by
  choose M hM using fun i => (hX i).bounded
  have hmeas : Measurable fun ω => (fun i => X i ω : Fin n → ℝ) :=
    measurable_pi_lambda _ fun i => (hX i).measurable
  have hbox : IsCompact (Set.pi Set.univ fun i => Set.Icc (-M i) (M i)) :=
    isCompact_univ_pi fun _ => isCompact_Icc
  obtain ⟨B, hB⟩ := hbox.exists_bound_of_continuousOn hF.continuousOn
  refine .of_measurable (hF.measurable.comp hmeas) B fun ω => hB _ ?_
  intro i _
  exact abs_le.mp (hM i ω)
theorem expectationBasicProperties_holds : ExpectationBasicProperties := by
  intro Ω _ μ _
  refine ⟨⟨?_, IsBoundedRealRV.const, fun _ _ => .mul, ?_,
    IsBoundedComplexRV.const, fun _ _ => .mul, fun _ => IsBoundedRealRV.ofReal⟩,
    ⟨?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  · exact ⟨{ carrier := {X | IsBoundedRealRV X}
             add_mem' := fun hX hY => hX.add hY
             zero_mem' := IsBoundedRealRV.const 0
             smul_mem' := fun a _ hX => hX.smul a }, rfl⟩
  · exact ⟨{ carrier := {f | IsBoundedComplexRV f}
             add_mem' := fun hf hg => hf.add hg
             zero_mem' := IsBoundedComplexRV.const 0
             smul_mem' := fun a _ hf => hf.smul a }, rfl⟩
  · intro f g a b hf hg
    unfold complexExpectation
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [integral_add ((hf.integrable μ).const_mul a) ((hg.integrable μ).const_mul b),
      integral_const_mul, integral_const_mul]
  · intro f _ hreal
    have hre : ∫ ω, f ω ∂μ = ∫ ω, (((f ω).re : ℝ) : ℂ) ∂μ :=
      integral_congr_ae (ae_of_all _ fun ω => Complex.ext rfl (by simp [hreal ω]))
    unfold complexExpectation
    rw [hre, integral_complex_ofReal]
    exact Complex.ofReal_im _
  · simp [complexExpectation]
  · intro f hf
    obtain ⟨M, hM⟩ := hf.bounded
    have hbdd : BddAbove (Set.range fun ω => ‖f ω‖) := ⟨M, by rintro _ ⟨ω, rfl⟩; exact hM ω⟩
    have hle := norm_integral_le_of_norm_le_const (μ := μ) (f := f) (C := supModulus f)
      (ae_of_all _ fun ω => le_ciSup hbdd ω)
    simpa [complexExpectation] using hle
  · intro X a hX ha
    obtain ⟨M, hM⟩ := hX.bounded
    have hint : Integrable X μ := Integrable.of_bound hX.measurable.aestronglyMeasurable M
      (ae_of_all _ fun ω => by simpa [Real.norm_eq_abs] using hM ω)
    unfold complexExpectation
    rw [integral_complex_ofReal, Complex.ofReal_re]
    calc a = ∫ _, a ∂μ := by simp
      _ ≤ ∫ ω, X ω ∂μ := integral_mono (integrable_const a) hint ha
  · intro n _ X F hX hF
    have hc := isBoundedComplexRV_continuous_comp hX hF
    refine ⟨hc, fun _ => ?_⟩
    obtain ⟨B, hB⟩ := hc.bounded
    exact ⟨hc.measurable_re, B, fun ω => (Complex.abs_re_le_norm _).trans (hB ω)⟩
end YangMills.Construction.Probability
