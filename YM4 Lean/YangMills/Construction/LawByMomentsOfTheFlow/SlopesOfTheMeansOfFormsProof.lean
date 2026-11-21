import YangMills.Construction.LawByMomentsOfTheFlow.CompletedFormAcrossAStepProof
import YangMills.Construction.LawByMomentsOfTheFlow.ContractionOfTheResponse
import YangMills.Construction.LawByMomentsOfTheFlow.GaussianAgainstACutLawProof
import YangMills.Construction.LawByMomentsOfTheFlow.MeansOfFormsAtAWeightProof
import YangMills.Construction.LawByMomentsOfTheFlow.SlopesOfTheMeansOfForms
import YangMills.Construction.ResponseInTheExpansion.TheCurvatureIsTheDescendedFormProof
import Mathlib
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
noncomputable section
open MeasureTheory ProbabilityTheory
namespace YangMills.Construction.MomentLaw
open TorusFields TorusLumps WeightedResponses BlockAverages StepCosts ColdStepAtMirrorFrames MomentMethod RenormalizationStepParameters
section AffineMeans
variable {E W V Ω : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] (T : E →L[ℝ] W) (ξ : Ω → W)
private theorem one_add_norm_affine_le (A : E) (w : Ω) :
    1 + ‖T A + ξ w‖ ≤ (1 + ‖T‖) * ((1 + ‖A‖) * (1 + ‖ξ w‖)) := by
  have h1 := norm_add_le (T A) (ξ w)
  have h2 := T.le_opNorm A
  have a := norm_nonneg A
  have b := norm_nonneg (ξ w)
  have c := norm_nonneg T
  nlinarith [mul_nonneg a b, mul_nonneg c a, mul_nonneg c b, mul_nonneg (mul_nonneg c a) b]
private theorem one_add_norm_affine_pow_le (A : E) (w : Ω) (k : ℕ) :
    (1 + ‖T A + ξ w‖) ^ k ≤ (1 + ‖T‖) ^ k * (1 + ‖A‖) ^ k * (1 + ‖ξ w‖) ^ k := by
  rw [← mul_pow, ← mul_pow, mul_assoc]
  exact pow_le_pow_left₀ (by positivity) (one_add_norm_affine_le T ξ A w) k
variable (hξ : AEStronglyMeasurable ξ μ) (hm : ∀ k : ℕ, Integrable (fun w => (1 + ‖ξ w‖) ^ k) μ)
include hξ hm in
private theorem hasFDerivAt_integral_affine (Q : W → V) (hQ : ContDiff ℝ 1 Q) (C : ℝ) (k : ℕ) (h0 : ∀ z, ‖Q z‖ ≤ C * (1 + ‖z‖) ^ k)
    (h1 : ∀ z, ‖fderiv ℝ Q z‖ ≤ C * (1 + ‖z‖) ^ k) (A : E) :
    HasFDerivAt (fun A => ∫ w, Q (T A + ξ w) ∂μ) (∫ w, (fderiv ℝ Q (T A + ξ w)).comp T ∂μ) A := by
  have hQc : Continuous Q := hQ.continuous
  have hdc : Continuous (fderiv ℝ Q) := hQ.continuous_fderiv (by norm_num)
  have hC : 0 ≤ C := by
    have h := le_trans (norm_nonneg _) (h0 0)
    have hp : (0 : ℝ) < (1 + ‖(0 : W)‖) ^ k := by positivity
    exact nonneg_of_mul_nonneg_left h hp
  have hbd : ∀ (A' : E) (w : Ω), ‖A' - A‖ < 1 → C * ((1 + ‖T‖) ^ k * (2 + ‖A‖) ^ k * (1 + ‖ξ w‖) ^ k) * ‖T‖ ≥ ‖(fderiv ℝ Q (T A' + ξ w)).comp T‖ := by
    intro A' w hA'
    have a1 : ‖A'‖ ≤ 1 + ‖A‖ := by
      have := norm_sub_norm_le A' A
      linarith
    have a2 : (1 + ‖A'‖) ^ k ≤ (2 + ‖A‖) ^ k := pow_le_pow_left₀ (by positivity) (by linarith) k
    have a3 : (1 + ‖T A' + ξ w‖) ^ k ≤ (1 + ‖T‖) ^ k * (2 + ‖A‖) ^ k * (1 + ‖ξ w‖) ^ k :=
      le_trans (one_add_norm_affine_pow_le T ξ A' w k) (by gcongr)
    calc ‖(fderiv ℝ Q (T A' + ξ w)).comp T‖ ≤ ‖fderiv ℝ Q (T A' + ξ w)‖ * ‖T‖ := ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ (C * (1 + ‖T A' + ξ w‖) ^ k) * ‖T‖ := by gcongr; exact h1 _
      _ ≤ (C * ((1 + ‖T‖) ^ k * (2 + ‖A‖) ^ k * (1 + ‖ξ w‖) ^ k)) * ‖T‖ := by gcongr
  have hmeasA : ∀ A' : E, AEStronglyMeasurable (fun w => T A' + ξ w) μ := fun A' => aestronglyMeasurable_const.add hξ
  have hint0 : ∀ A' : E, Integrable (fun w => Q (T A' + ξ w)) μ := fun A' => by
    refine ((hm k).const_mul (C * ((1 + ‖T‖) ^ k * (1 + ‖A'‖) ^ k))).mono' (hQc.comp_aestronglyMeasurable (hmeasA A'))
      (Filter.Eventually.of_forall fun w => ?_)
    calc ‖Q (T A' + ξ w)‖ ≤ C * (1 + ‖T A' + ξ w‖) ^ k := h0 _
      _ ≤ C * ((1 + ‖T‖) ^ k * (1 + ‖A'‖) ^ k * (1 + ‖ξ w‖) ^ k) := by gcongr; exact one_add_norm_affine_pow_le T ξ A' w k
      _ = _ := by ring
  refine (hasFDerivAt_integral_of_dominated_of_fderiv_le (F := fun A w => Q (T A + ξ w))
    (F' := fun A w => (fderiv ℝ Q (T A + ξ w)).comp T)
    (bound := fun w => C * ((1 + ‖T‖) ^ k * (2 + ‖A‖) ^ k * (1 + ‖ξ w‖) ^ k) * ‖T‖)
    (s := Metric.ball A 1) (Metric.ball_mem_nhds A one_pos) ?_ (hint0 A) ?_ ?_ ?_ ?_)
  · exact Filter.Eventually.of_forall fun A' => hQc.comp_aestronglyMeasurable (hmeasA A')
  · have c1 : Continuous fun z => (fderiv ℝ Q z).comp T := hdc.clm_comp continuous_const
    exact c1.comp_aestronglyMeasurable (hmeasA A)
  · refine Filter.Eventually.of_forall fun w A' hA' => hbd A' w ?_
    rwa [Metric.mem_ball, dist_eq_norm] at hA'
  · exact ((((hm k).const_mul ((1 + ‖T‖) ^ k * (2 + ‖A‖) ^ k)).const_mul C).mul_const ‖T‖).congr
      (Filter.Eventually.of_forall fun w => by ring)
  · refine Filter.Eventually.of_forall fun w A' _ => ?_
    have h2 : HasFDerivAt Q (fderiv ℝ Q (T A' + ξ w)) (T A' + ξ w) := ((hQ.differentiable (by norm_num)) _).hasFDerivAt
    exact h2.comp A' (T.hasFDerivAt.add_const (ξ w))
include hξ hm in
private theorem norm_integral_affine_le (Q : W → V) (hQ : Continuous Q) (C : ℝ) (hC : 0 ≤ C) (k : ℕ) (h0 : ∀ z, ‖Q z‖ ≤ C * (1 + ‖z‖) ^ k) (A : E) :
    ‖∫ w, Q (T A + ξ w) ∂μ‖ ≤ (C * (1 + ‖T‖) ^ k * ∫ w, (1 + ‖ξ w‖) ^ k ∂μ) * (1 + ‖A‖) ^ k := by
  have hb : ∀ w, ‖Q (T A + ξ w)‖ ≤ (C * (1 + ‖T‖) ^ k * (1 + ‖A‖) ^ k) * (1 + ‖ξ w‖) ^ k := fun w => by
    calc ‖Q (T A + ξ w)‖ ≤ C * (1 + ‖T A + ξ w‖) ^ k := h0 _
      _ ≤ C * ((1 + ‖T‖) ^ k * (1 + ‖A‖) ^ k * (1 + ‖ξ w‖) ^ k) := by gcongr; exact one_add_norm_affine_pow_le T ξ A w k
      _ = _ := by ring
  refine le_trans (norm_integral_le_of_norm_le ((hm k).const_mul _) (Filter.Eventually.of_forall hb)) (le_of_eq ?_)
  rw [integral_const_mul]
  ring
include hξ hm in
private theorem integrable_affine (Q : W → V) (hQ : Continuous Q) (C : ℝ) (k : ℕ) (h0 : ∀ z, ‖Q z‖ ≤ C * (1 + ‖z‖) ^ k) (A : E) :
    Integrable (fun w => Q (T A + ξ w)) μ := by
  have hC : 0 ≤ C := by
    have h := le_trans (norm_nonneg _) (h0 0)
    have hp : (0 : ℝ) < (1 + ‖(0 : W)‖) ^ k := by positivity
    exact nonneg_of_mul_nonneg_left h hp
  refine ((hm k).const_mul (C * ((1 + ‖T‖) ^ k * (1 + ‖A‖) ^ k))).mono'
    (hQ.comp_aestronglyMeasurable (aestronglyMeasurable_const.add hξ)) (Filter.Eventually.of_forall fun w => ?_)
  calc ‖Q (T A + ξ w)‖ ≤ C * (1 + ‖T A + ξ w‖) ^ k := h0 _
    _ ≤ C * ((1 + ‖T‖) ^ k * (1 + ‖A‖) ^ k * (1 + ‖ξ w‖) ^ k) := by gcongr; exact one_add_norm_affine_pow_le T ξ A w k
    _ = _ := by ring
include hξ hm in
private theorem contDiff_one_integral_affine (Q : W → V) (hQ : ContDiff ℝ 2 Q) (C : ℝ) (k : ℕ)
    (hb : ∀ z, ∀ l : ℕ, l ≤ 2 → ‖iteratedFDeriv ℝ l Q z‖ ≤ C * (1 + ‖z‖) ^ k) :
    ContDiff ℝ 1 (fun A => ∫ w, Q (T A + ξ w) ∂μ) ∧
      ∃ C₁ : ℝ, ∀ A, ‖fderiv ℝ (fun A => ∫ w, Q (T A + ξ w) ∂μ) A‖ ≤ C₁ * (1 + ‖A‖) ^ k := by
  have hC : 0 ≤ C := by
    have h := le_trans (norm_nonneg _) (hb 0 0 (by norm_num))
    have hp : (0 : ℝ) < (1 + ‖(0 : W)‖) ^ k := by positivity
    exact nonneg_of_mul_nonneg_left h hp
  have hQ1 : ContDiff ℝ 1 (fderiv ℝ Q) := hQ.fderiv_right (by norm_num)
  have b0 : ∀ z, ‖Q z‖ ≤ C * (1 + ‖z‖) ^ k := fun z => by
    have := hb z 0 (by norm_num)
    rwa [norm_iteratedFDeriv_zero] at this
  have b1 : ∀ z, ‖fderiv ℝ Q z‖ ≤ C * (1 + ‖z‖) ^ k := fun z => by
    have := hb z 1 (by norm_num)
    rwa [norm_iteratedFDeriv_one] at this
  have b2 : ∀ z, ‖fderiv ℝ (fderiv ℝ Q) z‖ ≤ C * (1 + ‖z‖) ^ k := fun z => by
    have := hb z 2 (by norm_num)
    rwa [show (2 : ℕ) = 1 + 1 from rfl, ← norm_iteratedFDeriv_fderiv, norm_iteratedFDeriv_one] at this
  set Cc : (W →L[ℝ] V) →L[ℝ] (E →L[ℝ] V) := (ContinuousLinearMap.compL ℝ E W V).flip T with hCc
  have e0 : ∀ A, HasFDerivAt (fun A => ∫ w, Q (T A + ξ w) ∂μ) (Cc (∫ w, fderiv ℝ Q (T A + ξ w) ∂μ)) A := fun A => by
    have h := hasFDerivAt_integral_affine μ T ξ hξ hm Q (hQ.of_le (by norm_num)) C k b0 b1 A
    rwa [show (∫ w, (fderiv ℝ Q (T A + ξ w)).comp T ∂μ) = Cc (∫ w, fderiv ℝ Q (T A + ξ w) ∂μ) from
      Cc.integral_comp_comm (integrable_affine μ T ξ hξ hm _ hQ1.continuous C k b1 A)] at h
  have e1 : Continuous (fun A => ∫ w, fderiv ℝ Q (T A + ξ w) ∂μ) := continuous_iff_continuousAt.2 fun A =>
    (hasFDerivAt_integral_affine μ T ξ hξ hm (fderiv ℝ Q) hQ1 C k b1 b2 A).continuousAt
  have f0 : fderiv ℝ (fun A => ∫ w, Q (T A + ξ w) ∂μ) = fun A => Cc (∫ w, fderiv ℝ Q (T A + ξ w) ∂μ) :=
    funext fun A => (e0 A).fderiv
  refine ⟨contDiff_one_iff_fderiv.2 ⟨fun A => (e0 A).differentiableAt, ?_⟩,
    ‖Cc‖ * (C * (1 + ‖T‖) ^ k * ∫ w, (1 + ‖ξ w‖) ^ k ∂μ), fun A => ?_⟩
  · rw [f0]
    exact Cc.continuous.comp e1
  · rw [f0]
    have n1 := norm_integral_affine_le μ T ξ hξ hm (fderiv ℝ Q) hQ1.continuous C hC k b1 A
    calc ‖Cc (∫ w, fderiv ℝ Q (T A + ξ w) ∂μ)‖ ≤ ‖Cc‖ * ‖∫ w, fderiv ℝ Q (T A + ξ w) ∂μ‖ := Cc.le_opNorm _
      _ ≤ ‖Cc‖ * ((C * (1 + ‖T‖) ^ k * ∫ w, (1 + ‖ξ w‖) ^ k ∂μ) * (1 + ‖A‖) ^ k) := by gcongr
      _ = _ := by ring
include hξ hm in
private theorem contDiff_two_integral_affine (P : W → ℝ) (hP : ContDiff ℝ 3 P) (C : ℝ) (k : ℕ)
    (hb : ∀ z, ∀ l : ℕ, l ≤ 3 → ‖iteratedFDeriv ℝ l P z‖ ≤ C * (1 + ‖z‖) ^ k) :
    ContDiff ℝ 2 (fun A => ∫ w, P (T A + ξ w) ∂μ) ∧
    (∃ (C' : ℝ) (k' : ℕ), ∀ (A : E) (l : ℕ), l ≤ 2 → ‖iteratedFDeriv ℝ l (fun A => ∫ w, P (T A + ξ w) ∂μ) A‖ ≤ C' * (1 + ‖A‖) ^ k') ∧
    ∀ A v, fderiv ℝ (fun A => ∫ w, P (T A + ξ w) ∂μ) A v = ∫ w, fderiv ℝ P (T A + ξ w) (T v) ∂μ := by
  have hC : 0 ≤ C := by
    have h := le_trans (norm_nonneg _) (hb 0 0 (by norm_num))
    have hp : (0 : ℝ) < (1 + ‖(0 : W)‖) ^ k := by positivity
    exact nonneg_of_mul_nonneg_left h hp
  have hP1 : ContDiff ℝ 2 (fderiv ℝ P) := hP.fderiv_right (by norm_num)
  have b0 : ∀ z, ‖P z‖ ≤ C * (1 + ‖z‖) ^ k := fun z => by
    have := hb z 0 (by norm_num)
    rwa [norm_iteratedFDeriv_zero] at this
  have b1 : ∀ z, ‖fderiv ℝ P z‖ ≤ C * (1 + ‖z‖) ^ k := fun z => by
    have := hb z 1 (by norm_num)
    rwa [norm_iteratedFDeriv_one] at this
  have bQ : ∀ z, ∀ l : ℕ, l ≤ 2 → ‖iteratedFDeriv ℝ l (fderiv ℝ P) z‖ ≤ C * (1 + ‖z‖) ^ k := fun z l hl => by
    rw [norm_iteratedFDeriv_fderiv]
    exact hb z (l + 1) (by omega)
  obtain ⟨c1, C₁, hC₁⟩ := contDiff_one_integral_affine μ T ξ hξ hm (fderiv ℝ P) hP1 C k bQ
  set Cc : (W →L[ℝ] ℝ) →L[ℝ] (E →L[ℝ] ℝ) := (ContinuousLinearMap.compL ℝ E W ℝ).flip T with hCc
  have e0 : ∀ A, HasFDerivAt (fun A => ∫ w, P (T A + ξ w) ∂μ) (Cc (∫ w, fderiv ℝ P (T A + ξ w) ∂μ)) A := fun A => by
    have h := hasFDerivAt_integral_affine μ T ξ hξ hm P (hP.of_le (by norm_num)) C k b0 b1 A
    rwa [show (∫ w, (fderiv ℝ P (T A + ξ w)).comp T ∂μ) = Cc (∫ w, fderiv ℝ P (T A + ξ w) ∂μ) from
      Cc.integral_comp_comm (integrable_affine μ T ξ hξ hm _ hP1.continuous C k b1 A)] at h
  have f0 : fderiv ℝ (fun A => ∫ w, P (T A + ξ w) ∂μ) = fun A => Cc (∫ w, fderiv ℝ P (T A + ξ w) ∂μ) :=
    funext fun A => (e0 A).fderiv
  set M := ∫ w, (1 + ‖ξ w‖) ^ k ∂μ with hM
  have hM0 : 0 ≤ M := integral_nonneg fun w => by positivity
  set B₀ := C * (1 + ‖T‖) ^ k * M with hB₀
  have hB₀0 : 0 ≤ B₀ := by positivity
  refine ⟨?_, ⟨B₀ + ‖Cc‖ * B₀ + ‖Cc‖ * |C₁|, k, fun A l hl => ?_⟩, fun A v => ?_⟩
  · rw [show (2 : WithTop ℕ∞) = 1 + 1 by norm_num, contDiff_succ_iff_fderiv]
    refine ⟨fun A => (e0 A).differentiableAt, by simp, ?_⟩
    rw [f0]
    exact Cc.contDiff.comp c1
  · have n0 := norm_integral_affine_le μ T ξ hξ hm P hP.continuous C hC k b0 A
    have n1 := norm_integral_affine_le μ T ξ hξ hm (fderiv ℝ P) hP1.continuous C hC k b1 A
    have hA : 0 ≤ (1 + ‖A‖) ^ k := by positivity
    have hc : 0 ≤ ‖Cc‖ := ContinuousLinearMap.opNorm_nonneg Cc
    have hX : 0 ≤ B₀ * (1 + ‖A‖) ^ k := by positivity
    have hY : 0 ≤ ‖Cc‖ * B₀ * (1 + ‖A‖) ^ k := by positivity
    have hZ : 0 ≤ ‖Cc‖ * |C₁| * (1 + ‖A‖) ^ k := by positivity
    interval_cases l
    · rw [norm_iteratedFDeriv_zero]
      refine le_trans n0 ?_
      nlinarith
    · rw [norm_iteratedFDeriv_one, f0]
      have : ‖Cc (∫ w, fderiv ℝ P (T A + ξ w) ∂μ)‖ ≤ ‖Cc‖ * (B₀ * (1 + ‖A‖) ^ k) :=
        le_trans (Cc.le_opNorm _) (mul_le_mul_of_nonneg_left n1 hc)
      nlinarith
    · rw [show (2 : ℕ) = 1 + 1 from rfl, ← norm_iteratedFDeriv_fderiv, norm_iteratedFDeriv_one, f0]
      have hd : HasFDerivAt (fun A => Cc (∫ w, fderiv ℝ P (T A + ξ w) ∂μ))
          (Cc.comp (fderiv ℝ (fun A => ∫ w, fderiv ℝ P (T A + ξ w) ∂μ) A)) A :=
        Cc.hasFDerivAt.comp A ((c1.differentiable (by norm_num)) A).hasFDerivAt
      rw [hd.fderiv]
      have h1 := le_trans (ContinuousLinearMap.opNorm_comp_le Cc (fderiv ℝ (fun A => ∫ w, fderiv ℝ P (T A + ξ w) ∂μ) A))
        (mul_le_mul_of_nonneg_left (le_trans (hC₁ A) (mul_le_mul_of_nonneg_right (le_abs_self C₁) hA)) hc)
      nlinarith
  · rw [f0]
    have h1 : Cc (∫ w, fderiv ℝ P (T A + ξ w) ∂μ) v = (∫ w, fderiv ℝ P (T A + ξ w) ∂μ) (T v) := rfl
    rw [h1]
    exact ContinuousLinearMap.integral_apply (integrable_affine μ T ξ hξ hm _ hP1.continuous C k b1 A) (T v)
end AffineMeans
section PolynomialGrowth
variable {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W]
private def PolyGrowthC3 (f : W → ℝ) : Prop :=
  ContDiff ℝ 3 f ∧ ∃ (C : ℝ) (k : ℕ), 0 ≤ C ∧ ∀ z, ∀ l : ℕ, l ≤ 3 → ‖iteratedFDeriv ℝ l f z‖ ≤ C * (1 + ‖z‖) ^ k
private theorem PolyGrowthC3.const (c : ℝ) : PolyGrowthC3 (fun _ : W => c) := by
  refine ⟨contDiff_const, |c|, 0, abs_nonneg _, fun z l _ => ?_⟩
  rcases Nat.eq_zero_or_pos l with rfl | hl
  · simp
  · rw [iteratedFDeriv_const_of_ne hl.ne']
    simp
private theorem PolyGrowthC3.clm (L : W →L[ℝ] ℝ) : PolyGrowthC3 (fun z => L z) := by
  refine ⟨L.contDiff, ‖L‖ + 1, 1, by positivity, fun z l hl => ?_⟩
  have hn := ContinuousLinearMap.opNorm_nonneg L
  have hz := norm_nonneg z
  rcases l with _ | l
  · rw [norm_iteratedFDeriv_zero]
    have := L.le_opNorm z
    simp only [pow_one]
    nlinarith
  · rw [← norm_iteratedFDeriv_fderiv]
    have e : fderiv ℝ (fun z => L z) = fun _ => L := funext fun z => L.fderiv
    rw [e]
    rcases l with _ | l
    · rw [norm_iteratedFDeriv_zero]
      simp only [pow_one]
      nlinarith
    · rw [iteratedFDeriv_const_of_ne (by omega)]
      simp only [Pi.zero_apply, norm_zero, pow_one]
      positivity
private theorem one_le_one_add_norm (z : W) : (1 : ℝ) ≤ 1 + ‖z‖ := by linarith [norm_nonneg z]
private theorem PolyGrowthC3.add {f g : W → ℝ} (hf : PolyGrowthC3 f) (hg : PolyGrowthC3 g) : PolyGrowthC3 (fun z => f z + g z) := by
  obtain ⟨cf, C₁, k₁, hC₁, b₁⟩ := hf
  obtain ⟨cg, C₂, k₂, hC₂, b₂⟩ := hg
  refine ⟨cf.add cg, C₁ + C₂, k₁ + k₂, by positivity, fun z l hl => ?_⟩
  have e : iteratedFDeriv ℝ l (fun z => f z + g z) z = iteratedFDeriv ℝ l f z + iteratedFDeriv ℝ l g z := by
    have := iteratedFDeriv_add_apply (𝕜 := ℝ) (i := l) (x := z) (f := f) (g := g)
      ((cf.contDiffAt).of_le (by exact_mod_cast hl)) ((cg.contDiffAt).of_le (by exact_mod_cast hl))
    exact this
  rw [e]
  have h1 := one_le_one_add_norm z
  have p₁ : (1 + ‖z‖) ^ k₁ ≤ (1 + ‖z‖) ^ (k₁ + k₂) := pow_le_pow_right₀ h1 (by omega)
  have p₂ : (1 + ‖z‖) ^ k₂ ≤ (1 + ‖z‖) ^ (k₁ + k₂) := pow_le_pow_right₀ h1 (by omega)
  calc _ ≤ ‖iteratedFDeriv ℝ l f z‖ + ‖iteratedFDeriv ℝ l g z‖ := norm_add_le _ _
    _ ≤ C₁ * (1 + ‖z‖) ^ (k₁ + k₂) + C₂ * (1 + ‖z‖) ^ (k₁ + k₂) :=
        add_le_add (le_trans (b₁ z l hl) (mul_le_mul_of_nonneg_left p₁ hC₁)) (le_trans (b₂ z l hl) (mul_le_mul_of_nonneg_left p₂ hC₂))
    _ = _ := by ring
private theorem PolyGrowthC3.mul {f g : W → ℝ} (hf : PolyGrowthC3 f) (hg : PolyGrowthC3 g) : PolyGrowthC3 (fun z => f z * g z) := by
  obtain ⟨cf, C₁, k₁, hC₁, b₁⟩ := hf
  obtain ⟨cg, C₂, k₂, hC₂, b₂⟩ := hg
  refine ⟨cf.mul cg, 8 * (C₁ * C₂), k₁ + k₂, by positivity, fun z l hl => ?_⟩
  have h1 := norm_iteratedFDeriv_mul_le (𝕜 := ℝ) (N := 3) cf cg z (n := l) (by exact_mod_cast hl)
  refine le_trans h1 ?_
  have h2 : ∀ i ∈ Finset.range (l + 1), (l.choose i : ℝ) * ‖iteratedFDeriv ℝ i f z‖ * ‖iteratedFDeriv ℝ (l - i) g z‖ ≤
      (l.choose i : ℝ) * (C₁ * C₂ * (1 + ‖z‖) ^ (k₁ + k₂)) := fun i hi => by
    have hi' : i ≤ l := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
    rw [mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
    calc _ ≤ (C₁ * (1 + ‖z‖) ^ k₁) * (C₂ * (1 + ‖z‖) ^ k₂) :=
          mul_le_mul (b₁ z i (by omega)) (b₂ z (l - i) (by omega)) (norm_nonneg _) (by positivity)
      _ = _ := by rw [pow_add]; ring
  refine le_trans (Finset.sum_le_sum h2) ?_
  rw [← Finset.sum_mul]
  have h3 : ∑ i ∈ Finset.range (l + 1), (l.choose i : ℝ) ≤ 8 := by
    have := Nat.sum_range_choose l
    have h4 : ∑ i ∈ Finset.range (l + 1), (l.choose i : ℝ) = (2 : ℝ) ^ l := by exact_mod_cast this
    rw [h4]
    calc (2 : ℝ) ^ l ≤ 2 ^ 3 := pow_le_pow_right₀ (by norm_num) hl
      _ = 8 := by norm_num
  have hX : 0 ≤ C₁ * C₂ * (1 + ‖z‖) ^ (k₁ + k₂) := by positivity
  nlinarith
private theorem PolyGrowthC3.sum {α : Type} (s : Finset α) (f : α → W → ℝ) (h : ∀ a ∈ s, PolyGrowthC3 (f a)) :
    PolyGrowthC3 (fun z => ∑ a ∈ s, f a z) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using PolyGrowthC3.const (W := W) 0
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self _ _)).add (ih fun b hb => h b (Finset.mem_insert_of_mem hb))
private theorem PolyGrowthC3.prod {α : Type} (s : Finset α) (f : α → W → ℝ) (h : ∀ a ∈ s, PolyGrowthC3 (f a)) :
    PolyGrowthC3 (fun z => ∏ a ∈ s, f a z) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using PolyGrowthC3.const (W := W) 1
  | insert a s ha ih =>
    simp only [Finset.prod_insert ha]
    exact (h a (Finset.mem_insert_self _ _)).mul (ih fun b hb => h b (Finset.mem_insert_of_mem hb))
end PolynomialGrowth
section ColourFormsAsPolynomials
variable {N : ℕ} [NeZero N]
private def coordCLM (e : Fin 3) (b : TorusBond N) : ColourForm N →L[ℝ] ℝ :=
  (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : TorusBond N => ℝ) b).comp
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 3 => TorusBond N → ℝ) e)
private theorem polyGrowthC3_colourEval (q : BondBilinear N) : PolyGrowthC3 (fun Z : ColourForm N => colourEval q Z Z) := by
  unfold colourEval bilinearEval
  refine PolyGrowthC3.sum _ _ fun e _ => PolyGrowthC3.sum _ _ fun b _ => PolyGrowthC3.sum _ _ fun b' _ => ?_
  exact ((PolyGrowthC3.clm (coordCLM e b)).mul (PolyGrowthC3.const (q b b'))).mul (PolyGrowthC3.clm (coordCLM e b'))
end ColourFormsAsPolynomials
section Descent
variable (a ρA : ℝ) {L : ℕ} [NeZero L]
private theorem pushColours_add (u : ℕ) {n : ℕ} [NeZero n] (X Y : ColourForm n) :
    pushColours a ρA L u (X + Y) = pushColours a ρA L u X + pushColours a ρA L u Y := by
  funext e b
  simp only [pushColours, responseMap, Pi.add_apply, mul_add, Finset.sum_add_distrib]
private theorem pushColours_smul (u : ℕ) {n : ℕ} [NeZero n] (c : ℝ) (X : ColourForm n) :
    pushColours a ρA L u (c • X) = c • pushColours a ρA L u X := by
  funext e b
  simp only [pushColours, responseMap, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun c' _ => ?_
  ring
private theorem descend_add (t : ℕ) : ∀ (d n : ℕ) [NeZero n] (X Y : ColourForm n),
    descend (L := L) a ρA t d n (X + Y) = descend (L := L) a ρA t d n X + descend (L := L) a ρA t d n Y
  | 0, _, _, _, _ => rfl
  | d + 1, n, _, X, Y => by
    simp only [descend]
    rw [pushColours_add a ρA (L := L) (t + d) X Y, descend_add t d (n * L)]
    rfl
private theorem descend_smul (t : ℕ) : ∀ (d n : ℕ) [NeZero n] (c : ℝ) (X : ColourForm n),
    descend (L := L) a ρA t d n (c • X) = c • descend (L := L) a ρA t d n X
  | 0, _, _, _, _ => rfl
  | d + 1, n, _, c, X => by
    simp only [descend]
    rw [pushColours_smul a ρA (L := L) (t + d) c X, descend_smul t d (n * L)]
    rfl
private def descendCLM (t d n : ℕ) [NeZero n] : ColourForm n →L[ℝ] ColourForm (fineSide L d n) :=
  LinearMap.toContinuousLinearMap
    { toFun := descend (L := L) a ρA t d n
      map_add' := descend_add a ρA t d n
      map_smul' := fun c X => descend_smul a ρA t d n c X }
private theorem descendWithNoise_eq_add (t : ℕ) (c : ℝ) : ∀ (d n : ℕ) [NeZero n] (A : ColourForm n) (w : FluctuationSample L t d n),
    descendWithNoise a ρA t c d n A w = descend (L := L) a ρA t d n A + descendWithNoise a ρA t c d n 0 w
  | 0, _, _, A, w => by
    show A = A + 0
    simp
  | d + 1, n, _, A, w => by
    have h0 : pushColours a ρA L (t + d) (0 : ColourForm n) = 0 := by
      funext e b
      simp [pushColours, responseMap]
    have hY : (fun e b => pushColours a ρA L (t + d) A e b + c * extendFluctuation w.1 e b) =
        pushColours a ρA L (t + d) A + (fun e b => c * extendFluctuation w.1 e b) := rfl
    have hY0 : (fun e b => pushColours a ρA L (t + d) (0 : ColourForm n) e b + c * extendFluctuation w.1 e b) =
        (fun e b => c * extendFluctuation w.1 e b) := by
      rw [h0]
      funext e b
      simp
    simp only [descendWithNoise, descend]
    rw [hY, hY0, descendWithNoise_eq_add t c d (n * L) (_ + _),
      descendWithNoise_eq_add t c d (n * L) (fun e b => c * extendFluctuation w.1 e b), descend_add]
    abel
end Descent
section Holder
variable {X : Type} [MeasurableSpace X] (P : Measure X) [IsProbabilityMeasure P]
private theorem eLpNorm_finsetProd_le {α : Type} (s : Finset α) (f : α → X → ℝ) (hf : ∀ i ∈ s, AEStronglyMeasurable (f i) P) (p : ENNReal) :
    eLpNorm (fun z => ∏ i ∈ s, f i z) (∑ _i ∈ s, p⁻¹)⁻¹ P ≤ ∏ i ∈ s, eLpNorm (f i) p P := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.prod_empty, Finset.sum_empty, ENNReal.inv_zero]
    rw [eLpNorm_exponent_top, eLpNormEssSup_const _ (IsProbabilityMeasure.ne_zero P)]
    simp
  | insert a s ha ih =>
    simp only [Finset.prod_insert ha, Finset.sum_insert ha]
    have h1 : AEStronglyMeasurable (fun z => ∏ i ∈ s, f i z) P :=
      Finset.aestronglyMeasurable_fun_prod _ fun i hi => hf i (Finset.mem_insert_of_mem hi)
    have h2 := eLpNorm_smul_le_mul_eLpNorm (μ := P) (p := p) (q := (∑ _i ∈ s, p⁻¹)⁻¹) (r := (p⁻¹ + ∑ _i ∈ s, p⁻¹)⁻¹)
      h1 (hf a (Finset.mem_insert_self _ _)) (hpqr := ⟨by simp⟩)
    exact le_trans h2 (mul_le_mul' le_rfl (ih fun i hi => hf i (Finset.mem_insert_of_mem hi)))
private theorem eLpNorm_finsetProd_mul_le {α : Type} (s : Finset α) (f : α → X → ℝ) (hf : ∀ i ∈ s, AEStronglyMeasurable (f i) P) (g : X → ℝ)
    (hg : AEStronglyMeasurable g P) :
    eLpNorm (fun z => (∏ i ∈ s, f i z) * g z) 2 P ≤
      eLpNorm g ((2 * (s.card + 1) : ℕ) : ENNReal) P * ∏ i ∈ s, eLpNorm (f i) ((2 * (s.card + 1) : ℕ) : ENNReal) P := by
  set p : ENNReal := ((2 * (s.card + 1) : ℕ) : ENNReal) with hp
  have h1 : AEStronglyMeasurable (fun z => ∏ i ∈ s, f i z) P := Finset.aestronglyMeasurable_fun_prod _ hf
  have hr : (p⁻¹ + ∑ _i ∈ s, p⁻¹)⁻¹ = 2 := by
    set c : ENNReal := ((s.card + 1 : ℕ) : ENNReal) with hc
    have hc0 : c ≠ 0 := by
      rw [hc]
      exact Nat.cast_ne_zero.2 (Nat.succ_ne_zero s.card)
    have hct : c ≠ ⊤ := ENNReal.natCast_ne_top (s.card + 1)
    have hpc : p = 2 * c := by
      rw [hp, hc]
      push_cast
      ring
    have h3 : p⁻¹ + ∑ _i ∈ s, p⁻¹ = 2⁻¹ := by
      rw [Finset.sum_const, nsmul_eq_mul]
      calc p⁻¹ + (s.card : ENNReal) * p⁻¹ = c * p⁻¹ := by
            rw [hc]
            push_cast
            ring
        _ = c * (2⁻¹ * c⁻¹) := by rw [hpc, ENNReal.mul_inv (Or.inl two_ne_zero) (Or.inl ENNReal.ofNat_ne_top)]
        _ = 2⁻¹ := by rw [mul_left_comm, ENNReal.mul_inv_cancel hc0 hct, mul_one]
    rw [h3, inv_inv]
  have h2 := eLpNorm_smul_le_mul_eLpNorm (μ := P) (p := p) (q := (∑ _i ∈ s, p⁻¹)⁻¹) (r := (p⁻¹ + ∑ _i ∈ s, p⁻¹)⁻¹)
    h1 hg (hpqr := ⟨by simp⟩)
  rw [hr] at h2
  have e : (fun z => (∏ i ∈ s, f i z) * g z) = g • fun z => ∏ i ∈ s, f i z := by
    funext z
    simp [mul_comm]
  rw [e]
  exact le_trans h2 (mul_le_mul' le_rfl (eLpNorm_finsetProd_le P s f hf p))
end Holder
section DerivativeOfProducts
variable {N : ℕ} [NeZero N]
private theorem hasFDerivAt_colourEval_diag (q : BondBilinear N) (Z : ColourForm N) :
    ∃ l : ColourForm N →L[ℝ] ℝ, HasFDerivAt (fun Z : ColourForm N => colourEval q Z Z) l Z ∧
      ∀ Y, l Y = colourEval q Y Z + colourEval q Z Y := by
  have hc : ∀ (e : Fin 3) (b : TorusBond N), HasFDerivAt (fun Z : ColourForm N => Z e b) (coordCLM e b) Z := fun e b => (coordCLM e b).hasFDerivAt
  have h1 : ∀ (e : Fin 3) (b b' : TorusBond N), HasFDerivAt (fun Z : ColourForm N => Z e b * q b b' * Z e b')
      (((Z e b * q b b') • coordCLM e b') + (Z e b' • (q b b' • coordCLM e b))) Z := fun e b b' => by
    have h2 := ((hc e b).mul_const (q b b')).mul (hc e b')
    exact h2
  refine ⟨∑ e : Fin 3, ∑ b : TorusBond N, ∑ b' : TorusBond N, (((Z e b * q b b') • coordCLM e b') + (Z e b' • (q b b' • coordCLM e b))), ?_, fun Y => ?_⟩
  · unfold colourEval bilinearEval
    exact HasFDerivAt.fun_sum fun e _ => HasFDerivAt.fun_sum fun b _ => HasFDerivAt.fun_sum fun b' _ => h1 e b b'
  · simp only [sum_apply, add_apply, smul_apply, smul_eq_mul,
      colourEval, bilinearEval, coordCLM, ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun e _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun b' _ => ?_
    ring
private theorem fderiv_prod_colourEval {k : ℕ} (Qf : Fin k → BondBilinear N) (x : ℝ) (B : Finset (Fin k)) (Z Y : ColourForm N) :
    fderiv ℝ (fun Z : ColourForm N => ∏ i ∈ B, x / 2 * colourEval (Qf i) Z Z) Z Y =
      ∑ i ∈ B, (∏ i' ∈ B.erase i, x / 2 * colourEval (Qf i') Z Z) *
        (x / 2 * (colourEval (Qf i) Y Z + colourEval (Qf i) Z Y)) := by
  choose l hl hl' using fun i => hasFDerivAt_colourEval_diag (Qf i) Z
  have h1 : ∀ i ∈ B, HasFDerivAt (fun Z : ColourForm N => x / 2 * colourEval (Qf i) Z Z) ((x / 2) • l i) Z := fun i _ =>
    (hl i).const_mul (x / 2)
  have h2 := HasFDerivAt.finsetProd h1
  rw [h2.fderiv]
  simp only [sum_apply, smul_apply, smul_eq_mul, hl']
private theorem abs_colourEval_le (q : BondBilinear N) (PL : Finset (TorusPlaquette N)) (κ : TorusPlaquette N → TorusPlaquette N → ℝ)
    (hκ : ∀ X X' : ColourForm N, colourEval q X X' = ∑ p ∈ PL, ∑ p' ∈ PL, κ p p' * ∑ e : Fin 3, curl (X e) p * curl (X' e) p')
    (X X' : ColourForm N) :
    |colourEval q X X'| ≤ ∑ p ∈ PL, ∑ p' ∈ PL, |κ p p'| * (curlNorm X p * curlNorm X' p') := by
  rw [hκ]
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum fun p _ => ?_)
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum fun p' _ => ?_)
  rw [abs_mul]
  refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
  have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun e : Fin 3 => curl (X e) p) (fun e : Fin 3 => curl (X' e) p')
  unfold curlNorm
  rw [← Real.sqrt_mul (Finset.sum_nonneg fun e _ => sq_nonneg _), ← Real.sqrt_sq_eq_abs]
  exact Real.sqrt_le_sqrt h
private theorem weighted_kernel_sum_le {J : Type} [Fintype J] {k : ℕ} (B : Finset (Fin k)) (PL : Finset (TorusPlaquette N))
    (κ : Fin k → TorusPlaquette N → TorusPlaquette N → ℝ)
    (ω : TorusPlaquette N → ℝ) (hω : ∀ p, 0 < ω p) (w : J → ℝ) (hw : ∀ j, 0 ≤ w j) (cj : J → TorusPlaquette N → ℝ) (hc : ∀ j p, 0 ≤ cj j p)
    (x W₁ c₁ : ℝ)
    (hx : 0 ≤ x) (hW : 0 ≤ W₁) (hsum : ∀ i, ∑ p ∈ PL, ∑ p' ∈ PL, |κ i p p'| * (ω p)⁻¹ * (ω p')⁻¹ ≤ c₁)
    (hY : ∀ p ∈ PL, ∑ j, w j * cj j p ≤ W₁ * (ω p)⁻¹) :
    ∑ j, ∑ i ∈ B, ∑ p ∈ PL, ∑ p' ∈ PL, x / 2 * |κ i p p'| * (w j * cj j p * (ω p')⁻¹ + w j * cj j p' * (ω p)⁻¹) ≤
      (B.card : ℝ) * (x * W₁ * c₁) := by
  rw [Finset.sum_comm]
  have h1 : ∀ i ∈ B, ∑ j, ∑ p ∈ PL, ∑ p' ∈ PL, x / 2 * |κ i p p'| * (w j * cj j p * (ω p')⁻¹ + w j * cj j p' * (ω p)⁻¹) ≤ x * W₁ * c₁ := fun i _ => by
    rw [Finset.sum_comm]
    have h2 : ∀ p ∈ PL, ∑ j, ∑ p' ∈ PL, x / 2 * |κ i p p'| * (w j * cj j p * (ω p')⁻¹ + w j * cj j p' * (ω p)⁻¹) ≤
        ∑ p' ∈ PL, x * W₁ * (|κ i p p'| * (ω p)⁻¹ * (ω p')⁻¹) := fun p hp => by
      rw [Finset.sum_comm]
      refine Finset.sum_le_sum fun p' hp' => ?_
      have a1 := hY p hp
      have a2 := hY p' hp'
      have ip : 0 ≤ (ω p)⁻¹ := (inv_pos.2 (hω p)).le
      have ip' : 0 ≤ (ω p')⁻¹ := (inv_pos.2 (hω p')).le
      have e : ∑ j, x / 2 * |κ i p p'| * (w j * cj j p * (ω p')⁻¹ + w j * cj j p' * (ω p)⁻¹) =
          x / 2 * |κ i p p'| * ((∑ j, w j * cj j p) * (ω p')⁻¹ + (∑ j, w j * cj j p') * (ω p)⁻¹) := by
        rw [Finset.sum_mul, Finset.sum_mul, ← Finset.sum_add_distrib, Finset.mul_sum]
      rw [e]
      calc x / 2 * |κ i p p'| * ((∑ j, w j * cj j p) * (ω p')⁻¹ + (∑ j, w j * cj j p') * (ω p)⁻¹)
          ≤ x / 2 * |κ i p p'| * ((W₁ * (ω p)⁻¹) * (ω p')⁻¹ + (W₁ * (ω p')⁻¹) * (ω p)⁻¹) := by gcongr
        _ = _ := by ring
    refine le_trans (Finset.sum_le_sum h2) ?_
    simp_rw [← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left (hsum i) (by positivity)
  refine le_trans (Finset.sum_le_sum h1) ?_
  rw [Finset.sum_const, nsmul_eq_mul]
private theorem eLpNorm_const_mul_add_abs_le {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) (a c c' : ℝ) (ha : 0 ≤ a) (hc : 0 ≤ c) (hc' : 0 ≤ c')
    (g g' : Ω → ℝ) (hg : Measurable g) (hg' : Measurable g') :
    eLpNorm (fun z => a * (c * |g z| + c' * |g' z|)) 2 P ≤
      ENNReal.ofReal a * (ENNReal.ofReal c * eLpNorm g 2 P + ENNReal.ofReal c' * eLpNorm g' 2 P) := by
  have e : (fun z => a * (c * |g z| + c' * |g' z|)) = a • ((fun z => c * |g z|) + fun z => c' * |g' z|) := by
    funext z
    simp
  have m₁ : AEStronglyMeasurable (fun z => c * |g z|) P := (hg.abs.const_mul c).aestronglyMeasurable
  have m₂ : AEStronglyMeasurable (fun z => c' * |g' z|) P := (hg'.abs.const_mul c').aestronglyMeasurable
  have h1 : ∀ (c : ℝ) (hc : 0 ≤ c) (g : Ω → ℝ), eLpNorm (fun z => c * |g z|) 2 P = ENNReal.ofReal c * eLpNorm g 2 P := fun c hc g => by
    have e2 : (fun z => c * |g z|) = c • fun z => ‖g z‖ := rfl
    rw [e2, eLpNorm_const_smul, Real.enorm_eq_ofReal hc, eLpNorm_norm]
  rw [e, eLpNorm_const_smul, Real.enorm_eq_ofReal ha]
  refine mul_le_mul' le_rfl (le_trans (eLpNorm_add_le m₁ m₂ (by norm_num)) ?_)
  rw [h1 c hc, h1 c' hc']
private theorem ofReal_weighted_term_eq (w a c c' u u' : ℝ) (hw : 0 ≤ w) (ha : 0 ≤ a) (hc : 0 ≤ c) (hc' : 0 ≤ c') (hu : 0 ≤ u) (hu' : 0 ≤ u')
    (Bn : ENNReal) :
    ENNReal.ofReal w * (ENNReal.ofReal a * (ENNReal.ofReal c * (ENNReal.ofReal u * Bn) + ENNReal.ofReal c' * (ENNReal.ofReal u' * Bn))) =
      ENNReal.ofReal (a * (w * c * u + w * c' * u')) * Bn := by
  have h1 : 0 ≤ w * c * u := by positivity
  have h2 : 0 ≤ w * c' * u' := by positivity
  have e1 : ENNReal.ofReal (w * c * u) = ENNReal.ofReal w * ENNReal.ofReal c * ENNReal.ofReal u := by
    rw [ENNReal.ofReal_mul (mul_nonneg hw hc), ENNReal.ofReal_mul hw]
  have e2 : ENNReal.ofReal (w * c' * u') = ENNReal.ofReal w * ENNReal.ofReal c' * ENNReal.ofReal u' := by
    rw [ENNReal.ofReal_mul (mul_nonneg hw hc'), ENNReal.ofReal_mul hw]
  rw [ENNReal.ofReal_mul ha, ENNReal.ofReal_add h1 h2, e1, e2]
  ring
private theorem weighted_fderiv_eLpNorm_sum_le {J Ω : Type} [Fintype J] {k : ℕ} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Qf : Fin k → BondBilinear N) (B : Finset (Fin k)) (x : ℝ) (hx : 0 ≤ x) (PL : Finset (TorusPlaquette N))
    (κ : Fin k → TorusPlaquette N → TorusPlaquette N → ℝ)
    (hκ : ∀ i, ∀ X X' : ColourForm N, colourEval (Qf i) X X' = ∑ p ∈ PL, ∑ p' ∈ PL, κ i p p' * ∑ e : Fin 3, curl (X e) p * curl (X' e) p')
    (ω : TorusPlaquette N → ℝ) (hω : ∀ p, 0 < ω p) (c₁ : ℝ) (hc₁ : 0 ≤ c₁)
    (hsum : ∀ i, ∑ p ∈ PL, ∑ p' ∈ PL, |κ i p p'| * (ω p)⁻¹ * (ω p')⁻¹ ≤ c₁)
    (Z : Ω → ColourForm N) (hZ : Measurable Z) (Y : J → ColourForm N) (w : J → ℝ) (hw : ∀ j, 0 ≤ w j) (W₁ : ℝ) (hW : 0 ≤ W₁)
    (hY : ∀ p ∈ PL, ∑ j, w j * curlNorm (Y j) p ≤ W₁ * (ω p)⁻¹) (Nz : ENNReal)
    (hZ1 : ∀ p ∈ PL, eLpNorm (fun z => curlNorm (Z z) p) ((2 * B.card : ℕ) : ENNReal) P ≤ ENNReal.ofReal (ω p)⁻¹ * Nz)
    (hZ2 : ∀ i, eLpNorm (fun z => colourEval (Qf i) (Z z) (Z z)) ((2 * B.card : ℕ) : ENNReal) P ≤ ENNReal.ofReal c₁ * Nz ^ 2) :
    ∑ j, ENNReal.ofReal (w j) * eLpNorm (fun z => fderiv ℝ (fun Z : ColourForm N => ∏ i ∈ B, x / 2 * colourEval (Qf i) Z Z) (Z z) (Y j)) 2 P ≤
      ENNReal.ofReal ((B.card : ℝ) * (x * W₁ * c₁)) * (Nz * (ENNReal.ofReal (x / 2) * (ENNReal.ofReal c₁ * Nz ^ 2)) ^ (B.card - 1)) := by
  classical
  set Qb := ENNReal.ofReal (x / 2) * (ENNReal.ofReal c₁ * Nz ^ 2) with hQb
  set Bn := Nz * Qb ^ (B.card - 1) with hBn
  have hcs : ∀ (X : ColourForm N) p, 0 ≤ curlNorm X p := fun _ _ => Real.sqrt_nonneg _
  have cf : ∀ i, Continuous fun Z : ColourForm N => colourEval (Qf i) Z Z := fun i => (polyGrowthC3_colourEval (Qf i)).1.continuous
  have mf : ∀ i, Measurable fun z => x / 2 * colourEval (Qf i) (Z z) (Z z) := fun i =>
    ((continuous_const.mul (cf i)).measurable).comp hZ
  have mc : ∀ p, Measurable fun z => curlNorm (Z z) p := fun p => by
    have : Continuous fun X : ColourForm N => curlNorm X p := by
      unfold curlNorm curl
      fun_prop
    exact this.measurable.comp hZ
  set G : Fin k → TorusPlaquette N → Ω → ℝ := fun i p z => (∏ i' ∈ B.erase i, x / 2 * colourEval (Qf i') (Z z) (Z z)) * curlNorm (Z z) p with hG
  have mG : ∀ i p, Measurable (G i p) := fun i p =>
    (Finset.measurable_fun_prod _ fun i' _ => mf i').mul (mc p)
  have hA : ∀ i ∈ B, ∀ p ∈ PL, eLpNorm (G i p) 2 P ≤ ENNReal.ofReal (ω p)⁻¹ * Bn := fun i hi p hp => by
    have hcard : (B.erase i).card + 1 = B.card := Finset.card_erase_add_one hi
    have h1 := eLpNorm_finsetProd_mul_le P (B.erase i) (fun i' z => x / 2 * colourEval (Qf i') (Z z) (Z z))
      (fun i' _ => (mf i').aestronglyMeasurable) (fun z => curlNorm (Z z) p) (mc p).aestronglyMeasurable
    rw [hcard] at h1
    refine le_trans h1 ?_
    have h2 : ∀ i' ∈ B.erase i, eLpNorm (fun z => x / 2 * colourEval (Qf i') (Z z) (Z z)) ((2 * B.card : ℕ) : ENNReal) P ≤ Qb := fun i' _ => by
      have e : (fun z => x / 2 * colourEval (Qf i') (Z z) (Z z)) = (x / 2) • fun z => colourEval (Qf i') (Z z) (Z z) := rfl
      rw [e, eLpNorm_const_smul, Real.enorm_eq_ofReal (by positivity)]
      exact mul_le_mul' le_rfl (hZ2 i')
    have h3 := Finset.prod_le_prod' h2
    rw [Finset.prod_const, Finset.card_erase_of_mem hi] at h3
    rw [hBn, ← mul_assoc]
    exact mul_le_mul' (hZ1 p hp) h3
  set Tt := B ×ˢ (PL ×ˢ PL) with hT
  set at' : Fin k × TorusPlaquette N × TorusPlaquette N → ℝ := fun t => x / 2 * |κ t.1 t.2.1 t.2.2| with hat
  have hat0 : ∀ t, 0 ≤ at' t := fun t => by positivity
  have hpt : ∀ (j : J) (z : Ω), |fderiv ℝ (fun Z : ColourForm N => ∏ i ∈ B, x / 2 * colourEval (Qf i) Z Z) (Z z) (Y j)| ≤
      ∑ t ∈ Tt, at' t * (curlNorm (Y j) t.2.1 * |G t.1 t.2.2 z| + curlNorm (Y j) t.2.2 * |G t.1 t.2.1 z|) := fun j z => by
    rw [fderiv_prod_colourEval, hT, Finset.sum_product]
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum fun i _ => ?_)
    rw [Finset.sum_product]
    simp only [hat, hG]
    set R := ∏ i' ∈ B.erase i, x / 2 * colourEval (Qf i') (Z z) (Z z) with hR
    have h1 := abs_colourEval_le (Qf i) PL (κ i) (hκ i) (Y j) (Z z)
    have h2 := abs_colourEval_le (Qf i) PL (κ i) (hκ i) (Z z) (Y j)
    have hx2 : 0 ≤ x / 2 := by positivity
    calc |R * (x / 2 * (colourEval (Qf i) (Y j) (Z z) + colourEval (Qf i) (Z z) (Y j)))|
        = |R| * (x / 2) * |colourEval (Qf i) (Y j) (Z z) + colourEval (Qf i) (Z z) (Y j)| := by
          rw [abs_mul, abs_mul, abs_of_nonneg hx2]
          ring
      _ ≤ |R| * (x / 2) * (|colourEval (Qf i) (Y j) (Z z)| + |colourEval (Qf i) (Z z) (Y j)|) := by
          gcongr
          exact abs_add_le _ _
      _ ≤ |R| * (x / 2) * ((∑ p ∈ PL, ∑ p' ∈ PL, |κ i p p'| * (curlNorm (Y j) p * curlNorm (Z z) p')) +
            ∑ p ∈ PL, ∑ p' ∈ PL, |κ i p p'| * (curlNorm (Z z) p * curlNorm (Y j) p')) := by
          gcongr
      _ = _ := by
          rw [← Finset.sum_add_distrib, Finset.mul_sum]
          refine Finset.sum_congr rfl fun p _ => ?_
          rw [← Finset.sum_add_distrib, Finset.mul_sum]
          refine Finset.sum_congr rfl fun p' _ => ?_
          rw [abs_mul R, abs_mul R, abs_of_nonneg (hcs _ _), abs_of_nonneg (hcs _ _)]
          ring
  have hj : ∀ j : J, eLpNorm (fun z => fderiv ℝ (fun Z : ColourForm N => ∏ i ∈ B, x / 2 * colourEval (Qf i) Z Z) (Z z) (Y j)) 2 P ≤
      ∑ t ∈ Tt, ENNReal.ofReal (at' t) * (ENNReal.ofReal (curlNorm (Y j) t.2.1) * (ENNReal.ofReal (ω t.2.2)⁻¹ * Bn) +
        ENNReal.ofReal (curlNorm (Y j) t.2.2) * (ENNReal.ofReal (ω t.2.1)⁻¹ * Bn)) := fun j => by
    have hf : ∀ t ∈ Tt, AEStronglyMeasurable (fun z => at' t * (curlNorm (Y j) t.2.1 * |G t.1 t.2.2 z| + curlNorm (Y j) t.2.2 * |G t.1 t.2.1 z|)) P :=
      fun t _ => (((((mG _ _).abs.const_mul _).add ((mG _ _).abs.const_mul _))).const_mul _).aestronglyMeasurable
    have h1 : eLpNorm (fun z => fderiv ℝ (fun Z : ColourForm N => ∏ i ∈ B, x / 2 * colourEval (Qf i) Z Z) (Z z) (Y j)) 2 P ≤
        eLpNorm (∑ t ∈ Tt, fun z => at' t * (curlNorm (Y j) t.2.1 * |G t.1 t.2.2 z| + curlNorm (Y j) t.2.2 * |G t.1 t.2.1 z|)) 2 P := by
      refine eLpNorm_mono_real fun z => ?_
      rw [Real.norm_eq_abs, Finset.sum_apply]
      exact hpt j z
    refine le_trans h1 (le_trans (eLpNorm_sum_le hf (by norm_num)) (Finset.sum_le_sum fun t ht => ?_))
    have ht' := Finset.mem_product.1 ht
    have ht'' := Finset.mem_product.1 ht'.2
    refine le_trans (eLpNorm_const_mul_add_abs_le P _ _ _ (hat0 t) (hcs _ _) (hcs _ _) _ _ (mG _ _) (mG _ _)) ?_
    exact mul_le_mul' le_rfl (add_le_add (mul_le_mul' le_rfl (hA _ ht'.1 _ ht''.2)) (mul_le_mul' le_rfl (hA _ ht'.1 _ ht''.1)))
  have hωi : ∀ p, 0 ≤ (ω p)⁻¹ := fun p => (inv_pos.2 (hω p)).le
  have hreal := weighted_kernel_sum_le B PL κ ω hω w hw (fun j p => curlNorm (Y j) p) (fun j p => hcs _ _) x W₁ c₁ hx hW hsum hY
  calc ∑ j, ENNReal.ofReal (w j) * eLpNorm (fun z => fderiv ℝ (fun Z : ColourForm N => ∏ i ∈ B, x / 2 * colourEval (Qf i) Z Z) (Z z) (Y j)) 2 P
      ≤ ∑ j, ∑ t ∈ Tt, ENNReal.ofReal (at' t * (w j * curlNorm (Y j) t.2.1 * (ω t.2.2)⁻¹ + w j * curlNorm (Y j) t.2.2 * (ω t.2.1)⁻¹)) * Bn := by
        refine Finset.sum_le_sum fun j _ => ?_
        refine le_trans (mul_le_mul' le_rfl (hj j)) (le_of_eq ?_)
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun t _ => ofReal_weighted_term_eq _ _ _ _ _ _ (hw j) (hat0 t) (hcs _ _) (hcs _ _) (hωi _) (hωi _) Bn
    _ = ENNReal.ofReal (∑ j, ∑ t ∈ Tt, at' t * (w j * curlNorm (Y j) t.2.1 * (ω t.2.2)⁻¹ + w j * curlNorm (Y j) t.2.2 * (ω t.2.1)⁻¹)) * Bn := by
        have hnn : ∀ (j : J) (t : Fin k × TorusPlaquette N × TorusPlaquette N),
            0 ≤ at' t * (w j * curlNorm (Y j) t.2.1 * (ω t.2.2)⁻¹ + w j * curlNorm (Y j) t.2.2 * (ω t.2.1)⁻¹) := fun j t =>
          mul_nonneg (hat0 t) (add_nonneg (mul_nonneg (mul_nonneg (hw j) (hcs _ _)) (hωi _)) (mul_nonneg (mul_nonneg (hw j) (hcs _ _)) (hωi _)))
        rw [ENNReal.ofReal_sum_of_nonneg fun j _ => Finset.sum_nonneg fun t _ => hnn j t, Finset.sum_mul]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [ENNReal.ofReal_sum_of_nonneg fun t _ => hnn j t, Finset.sum_mul]
    _ ≤ _ := by
        refine mul_le_mul' (ENNReal.ofReal_le_ofReal (le_trans (le_of_eq ?_) hreal)) le_rfl
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [hT, Finset.sum_product]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.sum_product]
end DerivativeOfProducts
section FluctuationSamples
variable (a ρA : ℝ) (L : ℕ) [NeZero L]
private def extendFluctuationCLM (u n : ℕ) [NeZero n] : StepFluctuation L u n →L[ℝ] ColourForm (n * L) :=
  LinearMap.toContinuousLinearMap
    { toFun := extendFluctuation
      map_add' := fun k k' => by
        funext e c
        simp only [extendFluctuation, extendChart, Pi.add_apply, PiLp.add_apply]
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun b _ => ?_
        split_ifs <;> simp
      map_smul' := fun r k => by
        funext e c
        simp only [extendFluctuation, extendChart, Pi.smul_apply, PiLp.smul_apply, RingHom.id_apply, smul_eq_mul, Finset.mul_sum]
        refine Finset.sum_congr rfl fun b _ => ?_
        split_ifs <;> simp }
private theorem integrable_one_add_norm_pow_gaussian {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H] [MeasurableSpace H] [BorelSpace H]
    [SecondCountableTopology H] [CompleteSpace H] (ν : Measure H) [IsGaussian ν] (m : ℕ) :
    Integrable (fun w => (1 + ‖w‖) ^ m) ν := by apply _root_.YangMills.SharedProofs.p133249 <;> assumption
private theorem descendWithNoise_zero_succ (t : ℕ) (c : ℝ) (d n : ℕ) [NeZero n] (w : FluctuationSample L t (d + 1) n) :
    descendWithNoise a ρA t c (d + 1) n 0 w =
      descend (L := L) a ρA t d (n * L) (c • extendFluctuation w.1) + descendWithNoise a ρA t c d (n * L) 0 w.2 := by
  have h0 : pushColours a ρA L (t + d) (0 : ColourForm n) = 0 := by
    funext e b
    simp [pushColours, responseMap]
  have hY0 : (fun e b => pushColours a ρA L (t + d) (0 : ColourForm n) e b + c * extendFluctuation w.1 e b) = c • extendFluctuation w.1 := by
    rw [h0]
    funext e b
    simp
  simp only [descendWithNoise]
  rw [hY0, descendWithNoise_eq_add a ρA t c d (n * L)]
private theorem fluctuationSample_facts (t : ℕ) (c : ℝ) : ∀ (d n : ℕ) [NeZero n],
    IsProbabilityMeasure (fluctuationSampleLaw a L t d n) ∧ Measurable (fun w => descendWithNoise (L := L) a ρA t c d n 0 w) ∧
      ∀ k : ℕ, Integrable (fun w => (1 + ‖descendWithNoise (L := L) a ρA t c d n 0 w‖) ^ k) (fluctuationSampleLaw a L t d n)
  | 0, n, _ => by
    have h1 : IsProbabilityMeasure (fluctuationSampleLaw a L t 0 n) := by
      show IsProbabilityMeasure (Measure.dirac ())
      infer_instance
    refine ⟨h1, measurable_const, fun k => ?_⟩
    have := h1
    exact integrable_const ((1 + ‖(0 : ColourForm (fineSide L 0 n))‖) ^ k)
  | d + 1, n, _ => by
    obtain ⟨p1, m1, i1⟩ := fluctuationSample_facts t c d (n * L)
    let := instMeasurableSpaceFluctuationSample L t d (n * L)
    have hγ : IsProbabilityMeasure (fluctuationGaussian a L 1 (t + d) n) := by
      unfold fluctuationGaussian
      infer_instance
    have hG : IsGaussian (fluctuationGaussian a L 1 (t + d) n) := by
      unfold fluctuationGaussian
      infer_instance
    have hprob : IsProbabilityMeasure ((fluctuationGaussian a L 1 (t + d) n).prod (fluctuationSampleLaw a L t d (n * L))) := inferInstance
    set Lv : StepFluctuation L (t + d) n →L[ℝ] ColourForm (fineSide L d (n * L)) :=
      (descendCLM a ρA t d (n * L)).comp (c • extendFluctuationCLM L (t + d) n) with hLv
    have hv : ∀ η, descend (L := L) a ρA t d (n * L) (c • extendFluctuation η) = Lv η := fun η => rfl
    have hlaw : fluctuationSampleLaw a L t (d + 1) n = (fluctuationGaussian a L 1 (t + d) n).prod (fluctuationSampleLaw a L t d (n * L)) := rfl
    have hsplit : (fun w : StepFluctuation L (t + d) n × FluctuationSample L t d (n * L) => descendWithNoise (L := L) a ρA t c (d + 1) n 0 w) =
        fun w => Lv w.1 + descendWithNoise (L := L) a ρA t c d (n * L) 0 w.2 := by
      funext w
      exact descendWithNoise_zero_succ a ρA L t c d n w
    refine ⟨hprob, ?_, fun k => ?_⟩
    · show Measurable (fun w : StepFluctuation L (t + d) n × FluctuationSample L t d (n * L) => descendWithNoise (L := L) a ρA t c (d + 1) n 0 w)
      rw [hsplit]
      exact (Lv.continuous.measurable.comp measurable_fst).add (m1.comp measurable_snd)
    · show Integrable (fun w : StepFluctuation L (t + d) n × FluctuationSample L t d (n * L) =>
          (1 + ‖descendWithNoise (L := L) a ρA t c (d + 1) n 0 w‖) ^ k)
        ((fluctuationGaussian a L 1 (t + d) n).prod (fluctuationSampleLaw a L t d (n * L)))
      have e : (fun w : StepFluctuation L (t + d) n × FluctuationSample L t d (n * L) => (1 + ‖descendWithNoise (L := L) a ρA t c (d + 1) n 0 w‖) ^ k) =
          fun w => (1 + ‖Lv w.1 + descendWithNoise (L := L) a ρA t c d (n * L) 0 w.2‖) ^ k := by
        funext w
        rw [show descendWithNoise (L := L) a ρA t c (d + 1) n 0 w = Lv w.1 + descendWithNoise (L := L) a ρA t c d (n * L) 0 w.2 from congrFun hsplit w]
        rfl
      rw [e]
      have hg : Integrable (fun η : StepFluctuation L (t + d) n => (1 + ‖Lv η‖) ^ k) (fluctuationGaussian a L 1 (t + d) n) := by
        refine ((integrable_one_add_norm_pow_gaussian (fluctuationGaussian a L 1 (t + d) n) k).const_mul ((1 + ‖Lv‖) ^ k)).mono'
          ((continuous_const.add (continuous_norm.comp Lv.continuous)).pow k).aestronglyMeasurable (Filter.Eventually.of_forall fun η => ?_)
        rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), ← mul_pow]
        refine pow_le_pow_left₀ (by positivity) ?_ k
        have h1 := Lv.le_opNorm η
        have h2 := norm_nonneg η
        have h3 := norm_nonneg Lv
        nlinarith [mul_nonneg h3 h2]
      have hp := Integrable.mul_prod hg (i1 k)
      have hZm : Measurable fun w : StepFluctuation L (t + d) n × FluctuationSample L t d (n * L) =>
          Lv w.1 + descendWithNoise (L := L) a ρA t c d (n * L) 0 w.2 := (Lv.continuous.measurable.comp measurable_fst).add (m1.comp measurable_snd)
      have hcn : Continuous fun Z : ColourForm (fineSide L d (n * L)) => (1 + ‖Z‖) ^ k := (continuous_const.add continuous_norm).pow k
      refine hp.mono (hcn.measurable.comp hZm).aestronglyMeasurable (Filter.Eventually.of_forall fun w => ?_)
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), Real.norm_eq_abs, abs_of_nonneg (by positivity), ← mul_pow]
      refine pow_le_pow_left₀ (by positivity) ?_ k
      have h1 := norm_add_le (Lv w.1) (descendWithNoise (L := L) a ρA t c d (n * L) 0 w.2)
      have h2 := norm_nonneg (Lv w.1)
      have h3 := norm_nonneg (descendWithNoise (L := L) a ρA t c d (n * L) 0 w.2)
      nlinarith [mul_nonneg h2 h3]
end FluctuationSamples
private theorem zmod_cast_cast_eq (P m : ℕ) (h : P = m) (a : ZMod m) :
    (((((a.cast : ℤ) : ZMod P)).cast : ℤ) : ZMod m) = a := by apply _root_.YangMills.Construction.FrameTorusAction.intCast_cast_roundTrip <;> assumption
section SignChoice
variable (a ρA : ℝ) {L : ℕ} [NeZero L]
private def descendOne (t : ℕ) : (d n : ℕ) → [NeZero n] → (TorusBond n → ℝ) → (TorusBond (fineSide L d n) → ℝ)
  | 0, _, _, f => f
  | d + 1, n, _, f => descendOne t d (n * L) (responseMap a ρA L (t + d) f)
private theorem descend_apply_colour (t : ℕ) : ∀ (d n : ℕ) [NeZero n] (X : ColourForm n) (e : Fin 3),
    descend (L := L) a ρA t d n X e = descendOne (L := L) a ρA t d n (X e)
  | 0, _, _, _, _ => rfl
  | d + 1, n, _, X, e => descend_apply_colour t d (n * L) (pushColours a ρA L (t + d) X) e
private theorem responseMap_add_apply (u : ℕ) {n : ℕ} [NeZero n] (f g : TorusBond n → ℝ) :
    responseMap a ρA L u (f + g) = responseMap a ρA L u f + responseMap a ρA L u g := by
  funext b
  simp only [responseMap, Pi.add_apply, mul_add, Finset.sum_add_distrib]
private theorem responseMap_smul_apply (u : ℕ) {n : ℕ} [NeZero n] (c : ℝ) (f : TorusBond n → ℝ) :
    responseMap a ρA L u (c • f) = c • responseMap a ρA L u f := by
  funext b
  simp only [responseMap, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun c' _ => ?_
  ring
private theorem descendOne_add (t : ℕ) : ∀ (d n : ℕ) [NeZero n] (f g : TorusBond n → ℝ),
    descendOne (L := L) a ρA t d n (f + g) = descendOne (L := L) a ρA t d n f + descendOne (L := L) a ρA t d n g
  | 0, _, _, _, _ => rfl
  | d + 1, n, _, f, g => by
    simp only [descendOne]
    rw [responseMap_add_apply a ρA (L := L) (t + d) f g, descendOne_add t d (n * L)]
    rfl
private theorem descendOne_smul (t : ℕ) : ∀ (d n : ℕ) [NeZero n] (c : ℝ) (f : TorusBond n → ℝ),
    descendOne (L := L) a ρA t d n (c • f) = c • descendOne (L := L) a ρA t d n f
  | 0, _, _, _, _ => rfl
  | d + 1, n, _, c, f => by
    simp only [descendOne]
    rw [responseMap_smul_apply a ρA (L := L) (t + d) c f, descendOne_smul t d (n * L)]
    rfl
private def descendOneLinear (t d n : ℕ) [NeZero n] : (TorusBond n → ℝ) →ₗ[ℝ] (TorusBond (fineSide L d n) → ℝ) where
  toFun := descendOne (L := L) a ρA t d n
  map_add' := descendOne_add a ρA t d n
  map_smul' := fun c f => descendOne_smul a ρA t d n c f
variable {u n : ℕ} [NeZero n]
private def chartBondForm (b : ChartBondIndex L u n) : TorusBond (n * L) → ℝ := extendChart (Pi.single b 1)
private theorem extendChart_eq_sum (g : ChartBondIndex L u n → ℝ) : extendChart g = ∑ b, g b • chartBondForm b := by
  classical
  funext c
  simp only [extendChart, chartBondForm, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  set key := (torusSiteInFrame (torusFrame L u n) (torusFrame L u n).depth c.1, c.2) with hkey
  by_cases hk : ∃ b₀ : ChartBondIndex L u n, key = b₀.1
  · obtain ⟨b₀, hb₀⟩ := hk
    have hu : ∀ b : ChartBondIndex L u n, key = b.1 ↔ b = b₀ := fun b =>
      ⟨fun h => Subtype.ext (h.symm.trans hb₀), fun h => h ▸ hb₀⟩
    simp only [hu]
    simp [Pi.single_apply]
  · have hu : ∀ b : ChartBondIndex L u n, ¬ key = b.1 := fun b h => hk ⟨b, h⟩
    simp [hu]
private theorem extendChart_cases (g : ChartBondIndex L u n → ℝ) (c : TorusBond (n * L)) :
    extendChart g c = 0 ∨ ∃ b : ChartBondIndex L u n, toTorusSite (n * L) b.1.1 = c.1 ∧ extendChart g c = g b := by
  classical
  set key := (torusSiteInFrame (torusFrame L u n) (torusFrame L u n).depth c.1, c.2) with hkey
  by_cases hk : ∃ b₀ : ChartBondIndex L u n, key = b₀.1
  · obtain ⟨b₀, hb₀⟩ := hk
    right
    refine ⟨b₀, ?_, ?_⟩
    · rw [← hb₀]
      funext i
      have hp : (torusFrame L u n).period (torusFrame L u n).depth i = n * L := by
        simp [BlockFrame.period, torusFrame]
      exact zmod_cast_cast_eq _ _ hp (c.1 i)
    · have hu : ∀ b : ChartBondIndex L u n, key = b.1 ↔ b = b₀ := fun b =>
        ⟨fun h => Subtype.ext (h.symm.trans hb₀), fun h => h ▸ hb₀⟩
      simp only [extendChart, ← hkey, hu]
      simp
  · left
    have hu : ∀ b : ChartBondIndex L u n, ¬ key = b.1 := fun b h => hk ⟨b, h⟩
    simp only [extendChart, ← hkey, hu]
    simp
private def curlLinear {m : ℕ} (p : TorusPlaquette m) : (TorusBond m → ℝ) →ₗ[ℝ] ℝ where
  toFun f := curl f p
  map_add' f g := by
    simp only [curl, Pi.add_apply]
    ring
  map_smul' c f := by
    simp only [curl, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring
private theorem supDist_add_unitStep_le {m : ℕ} [NeZero m] (z : TorusSite m) (i : Fin 4) : TorusFields.supDist (z + TorusFields.unitStep m i) z ≤ 1 := by apply _root_.YangMills.SharedProofs.p63420 <;> assumption
private theorem chartColourForm_unitVariation (e e' : Fin 3) (b : ChartBondIndex L u n) :
    chartColourForm (unitVariation (e, b)) e' = if e' = e then chartBondForm b else 0 := by
  classical
  unfold chartColourForm chartBondForm
  split_ifs with h
  · subst h
    congr 1
    funext b'
    by_cases hb : b' = b
    · subst hb
      simp [unitVariation, ColdStepAtMirrorFrames.bondVariation]
    · simp [unitVariation, ColdStepAtMirrorFrames.bondVariation, Pi.single_eq_of_ne hb]
  · have : (fun b' => unitVariation ((e, b) : Fin 3 × ChartBondIndex L u n) b' e') = 0 := by
      funext b'
      by_cases hb : b' = b
      · subst hb
        simp [unitVariation, ColdStepAtMirrorFrames.bondVariation, h]
      · simp [unitVariation, ColdStepAtMirrorFrames.bondVariation, Pi.single_eq_of_ne hb]
    rw [this]
    funext c
    simp [extendChart]
private theorem weighted_unit_curl_sum_le (t d : ℕ) (ω₀ : TorusPlaquette (fineSide L d (n * L)) → ℝ) (hω₀ : ∀ p, 0 ≤ ω₀ p)
    (ω₁ : TorusPlaquette (n * L) → ℝ) (hω₁ : ∀ p, 0 ≤ ω₁ p)
    (hdown : ∀ (X : ColourForm (n * L)) (b : ℝ), 0 ≤ b → (∀ p' : OrientedPlaquette (n * L), ω₁ p'.1 * curlNorm X p'.1 ≤ b) →
      ∀ p : OrientedPlaquette (fineSide L d (n * L)), ω₀ p.1 * curlNorm (descend (L := L) a ρA t d (n * L) X) p.1 ≤ b)
    (w : ChartBondIndex L u n → ℝ) (hw : ∀ b, 0 ≤ w b) (W : ℝ) (hW : 0 ≤ W)
    (hwW : ∀ (b : ChartBondIndex L u n) (p' : TorusPlaquette (n * L)), TorusFields.supDist (toTorusSite (n * L) b.1.1) p'.1 ≤ 1 → w b * ω₁ p' ≤ W)
    (p : OrientedPlaquette (fineSide L d (n * L))) :
    (∑ j : Fin 3 × ChartBondIndex L u n, w j.2 * curlNorm (descend (L := L) a ρA t d (n * L) (chartColourForm (unitVariation j))) p.1) * ω₀ p.1 ≤ 24 * W := by
  classical
  set τ : ChartBondIndex L u n → ℝ := fun b => curl (descendOne (L := L) a ρA t d (n * L) (chartBondForm b)) p.1 with hτ
  have h1 : ∀ j : Fin 3 × ChartBondIndex L u n, curlNorm (descend (L := L) a ρA t d (n * L) (chartColourForm (unitVariation j))) p.1 = |τ j.2| := fun j => by
    obtain ⟨e, b⟩ := j
    unfold curlNorm
    simp only [descend_apply_colour, chartColourForm_unitVariation]
    rw [Finset.sum_eq_single e]
    · simp [hτ, Real.sqrt_sq_eq_abs]
    · intro e' _ he
      have h0 : descendOne (L := L) a ρA t d (n * L) 0 = 0 := map_zero (descendOneLinear (L := L) a ρA t d (n * L))
      rw [if_neg he, h0]
      simp [curl]
    · simp
  have h2 : ∑ j : Fin 3 × ChartBondIndex L u n, w j.2 * curlNorm (descend (L := L) a ρA t d (n * L) (chartColourForm (unitVariation j))) p.1 =
      3 * ∑ b, w b * |τ b| := by
    simp only [h1]
    rw [Fintype.sum_prod_type]
    simp
  set v := ∑ b, w b * |τ b| with hv
  set σ : ChartBondIndex L u n → ℝ := fun b => if 0 ≤ τ b then 1 else -1 with hσ
  set g : ChartBondIndex L u n → ℝ := fun b => σ b * w b with hg
  have hgabs : ∀ b, |g b| = w b := fun b => by
    simp only [hg, hσ]
    split_ifs <;> simp [abs_of_nonneg (hw b)]
  have h3 : curl (descendOne (L := L) a ρA t d (n * L) (extendChart g)) p.1 = v := by
    rw [extendChart_eq_sum]
    have e1 : descendOne (L := L) a ρA t d (n * L) (∑ b, g b • chartBondForm b) =
        ∑ b, g b • descendOne (L := L) a ρA t d (n * L) (chartBondForm b) := by
      calc descendOne (L := L) a ρA t d (n * L) (∑ b, g b • chartBondForm b) =
            descendOneLinear (L := L) a ρA t d (n * L) (∑ b, g b • chartBondForm b) := rfl
        _ = ∑ b, descendOneLinear (L := L) a ρA t d (n * L) (g b • chartBondForm b) := map_sum _ _ _
        _ = ∑ b, g b • descendOneLinear (L := L) a ρA t d (n * L) (chartBondForm b) := Finset.sum_congr rfl fun b _ => map_smul _ _ _
        _ = _ := rfl
    rw [e1]
    have e2 := map_sum (curlLinear p.1) (fun b => g b • descendOne (L := L) a ρA t d (n * L) (chartBondForm b)) Finset.univ
    refine Eq.trans e2 (Finset.sum_congr rfl fun b _ => ?_)
    have e3 : curlLinear p.1 (g b • descendOne (L := L) a ρA t d (n * L) (chartBondForm b)) = g b * τ b := by
      rw [map_smul]
      rfl
    rw [e3]
    simp only [hg, hσ]
    split_ifs with h
    · rw [abs_of_nonneg h]
      ring
    · rw [abs_of_neg (not_le.1 h)]
      ring
  set f := extendChart g with hf
  have hedge : ∀ (p' : TorusPlaquette (n * L)) (c : TorusBond (n * L)), TorusFields.supDist c.1 p'.1 ≤ 1 → ω₁ p' * |f c| ≤ W := fun p' c hc => by
    rcases extendChart_cases g c with h0 | ⟨b, hb, hval⟩
    · rw [hf, h0, abs_zero, mul_zero]
      exact hW
    · rw [hf, hval, hgabs, mul_comm]
      exact hwW b p' (by rw [hb]; exact hc)
  have hX : ∀ p' : OrientedPlaquette (n * L), ω₁ p'.1 * curlNorm (fun _ : Fin 3 => f) p'.1 ≤ 8 * W := fun p' => by
    have e1 : curlNorm (fun _ : Fin 3 => f) p'.1 ≤ 2 * |curl f p'.1| := by
      unfold curlNorm
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      refine Real.sqrt_le_iff.2 ⟨by positivity, ?_⟩
      rw [mul_pow, sq_abs]
      have := sq_nonneg (curl f p'.1)
      norm_num
      nlinarith
    have t0 : ∀ i, TorusFields.supDist (p'.1.1 + TorusFields.unitStep (n * L) i) p'.1.1 ≤ 1 := fun i => supDist_add_unitStep_le _ i
    have t1 : TorusFields.supDist p'.1.1 p'.1.1 ≤ 1 := by
      have : TorusFields.supDist p'.1.1 p'.1.1 = 0 := by
        have h := supDist_add_siteOfInt_le p'.1.1 0 0 (by simp)
        have e0 : (siteOfInt (0 : Fin 4 → ℤ) : TorusSite (n * L)) = 0 := by
          funext i
          simp [siteOfInt]
        rw [e0, add_zero] at h
        omega
      omega
    have a1 := hedge p'.1 (p'.1.1, p'.1.2.1) t1
    have a2 := hedge p'.1 (p'.1.1 + TorusFields.unitStep (n * L) p'.1.2.1, p'.1.2.2) (t0 _)
    have a3 := hedge p'.1 (p'.1.1 + TorusFields.unitStep (n * L) p'.1.2.2, p'.1.2.1) (t0 _)
    have a4 := hedge p'.1 (p'.1.1, p'.1.2.2) t1
    have hc : |curl f p'.1| ≤ |f (p'.1.1, p'.1.2.1)| + |f (p'.1.1 + TorusFields.unitStep (n * L) p'.1.2.1, p'.1.2.2)| +
        |f (p'.1.1 + TorusFields.unitStep (n * L) p'.1.2.2, p'.1.2.1)| + |f (p'.1.1, p'.1.2.2)| := by
      unfold curl
      refine le_trans (abs_sub _ _) ?_
      refine add_le_add (le_trans (abs_sub _ _) (add_le_add (abs_add_le _ _) le_rfl)) le_rfl
    have hω := hω₁ p'.1
    calc ω₁ p'.1 * curlNorm (fun _ : Fin 3 => f) p'.1 ≤ ω₁ p'.1 * (2 * |curl f p'.1|) := by gcongr
      _ ≤ ω₁ p'.1 * (2 * (|f (p'.1.1, p'.1.2.1)| + |f (p'.1.1 + TorusFields.unitStep (n * L) p'.1.2.1, p'.1.2.2)| +
          |f (p'.1.1 + TorusFields.unitStep (n * L) p'.1.2.2, p'.1.2.1)| + |f (p'.1.1, p'.1.2.2)|)) := by gcongr
      _ ≤ 8 * W := by nlinarith
  have h4 := hdown (fun _ : Fin 3 => f) (8 * W) (by positivity) hX p
  have h5 : v ≤ curlNorm (descend (L := L) a ρA t d (n * L) (fun _ : Fin 3 => f)) p.1 := by
    unfold curlNorm
    simp only [descend_apply_colour, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, h3]
    refine Real.le_sqrt_of_sq_le ?_
    have := sq_nonneg v
    norm_num
    nlinarith
  rw [h2]
  have h6 : ω₀ p.1 * v ≤ 8 * W := le_trans (mul_le_mul_of_nonneg_left h5 (hω₀ p.1)) h4
  nlinarith
end SignChoice
section Assembly
private theorem weightedCurvatureNorm_mono {m : ℕ} [NeZero m] {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (ω : TorusPlaquette m → ℝ) (q q' : ENNReal) (hqq : q ≤ q') (X : Ω → ColourForm m) (hX : Measurable X) :
    weightedCurvatureNorm P ω q X ≤ weightedCurvatureNorm P ω q' X := by apply _root_.YangMills.SharedProofs.p123435 <;> assumption
private theorem eLpNorm_integral_prod_le {Ω D : Type} [MeasurableSpace Ω] [MeasurableSpace D] (μ : Measure Ω) [SFinite μ] (ν : Measure D)
    [IsProbabilityMeasure ν] (f : Ω × D → ℝ) (hf : Measurable f) :
    eLpNorm (fun z => ∫ w, f (z, w) ∂ν) 2 μ ≤ eLpNorm f 2 (μ.prod ν) := by
  have hsq : ∀ z, ‖∫ w, f (z, w) ∂ν‖ₑ ^ (2 : ℝ) ≤ ∫⁻ w, ‖f (z, w)‖ₑ ^ (2 : ℝ) ∂ν := fun z => by
    have hm : Measurable fun w => f (z, w) := hf.comp measurable_prodMk_left
    have h1 : ‖∫ w, f (z, w) ∂ν‖ₑ ≤ eLpNorm (fun w => f (z, w)) 1 ν := by
      rw [eLpNorm_one_eq_lintegral_enorm]
      exact enorm_integral_le_lintegral_enorm _
    have h2 := eLpNorm_le_eLpNorm_of_exponent_le (μ := ν) (p := 1) (q := 2) (by norm_num) hm.aestronglyMeasurable
    have h3 := le_trans h1 h2
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)] at h3
    simp only [ENNReal.toReal_ofNat] at h3
    have h4 := ENNReal.rpow_le_rpow h3 (show (0 : ℝ) ≤ 2 by norm_num)
    rw [← ENNReal.rpow_mul] at h4
    simpa using h4
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num),
    eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)]
  simp only [ENNReal.toReal_ofNat]
  refine ENNReal.rpow_le_rpow ?_ (by norm_num)
  rw [lintegral_prod _ (hf.enorm.pow_const _).aemeasurable]
  exact lintegral_mono hsq
variable (a ρA : ℝ) (L : ℕ) [NeZero L]
private theorem descendWithNoise_zero_eq_smul (t : ℕ) (c : ℝ) : ∀ (d n : ℕ) [NeZero n] (w : FluctuationSample L t d n),
    descendWithNoise (L := L) a ρA t c d n 0 w = c • descendWithNoise (L := L) a ρA t 1 d n 0 w
  | 0, _, _, _ => by
    show (0 : ColourForm _) = c • (0 : ColourForm _)
    simp
  | d + 1, n, _, w => by
    rw [descendWithNoise_zero_succ a ρA L t c d n w, descendWithNoise_zero_succ a ρA L t 1 d n w,
      descendWithNoise_zero_eq_smul t c d (n * L) w.2, one_smul, descend_smul]
    exact (smul_add c _ _).symm
private theorem curlNorm_add_le {m : ℕ} (X X' : ColourForm m) (p : TorusPlaquette m) : curlNorm (X + X') p ≤ curlNorm X p + curlNorm X' p := by
  have hv : ∀ Y : ColourForm m, curlNorm Y p = ‖(WithLp.toLp 2 fun e => curl (Y e) p : EuclideanSpace ℝ (Fin 3))‖ := fun Y => by
    rw [EuclideanSpace.norm_eq]
    simp [curlNorm, Real.norm_eq_abs, sq_abs]
  have e : (WithLp.toLp 2 fun e => curl ((X + X') e) p : EuclideanSpace ℝ (Fin 3)) =
      (WithLp.toLp 2 fun e => curl (X e) p) + (WithLp.toLp 2 fun e => curl (X' e) p) := by
    ext e
    simp [curl]
    ring
  rw [hv, hv, hv, e]
  exact norm_add_le _ _
private theorem weightedCurvatureNorm_prod_add_le {m : ℕ} [NeZero m] {Ω D : Type} [MeasurableSpace Ω] [MeasurableSpace D] (μ : Measure Ω) [SFinite μ]
    (ν : Measure D) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (ω : TorusPlaquette m → ℝ) (q : ENNReal) (hq : 1 ≤ q) (X : Ω → ColourForm m)
    (Ξ : D → ColourForm m) (hX : Measurable X) (hΞ : Measurable Ξ) :
    weightedCurvatureNorm (μ.prod ν) ω q (fun z => X z.1 + Ξ z.2) ≤ weightedCurvatureNorm μ ω q X + weightedCurvatureNorm ν ω q Ξ := by
  refine iSup_le fun p => ?_
  have hc : Continuous fun Y : ColourForm m => curlNorm Y p.1 := by
    unfold curlNorm curl
    fun_prop
  have m₁ : Measurable fun z : Ω × D => curlNorm (X z.1) p.1 := hc.measurable.comp (hX.comp measurable_fst)
  have m₂ : Measurable fun z : Ω × D => curlNorm (Ξ z.2) p.1 := hc.measurable.comp (hΞ.comp measurable_snd)
  have e₁ : eLpNorm (fun z : Ω × D => curlNorm (X z.1) p.1) q (μ.prod ν) = eLpNorm (fun z => curlNorm (X z) p.1) q μ :=
    eLpNorm_comp_measurePreserving (g := fun z => curlNorm (X z) p.1) (hc.measurable.comp hX).aestronglyMeasurable measurePreserving_fst
  have e₂ : eLpNorm (fun z : Ω × D => curlNorm (Ξ z.2) p.1) q (μ.prod ν) = eLpNorm (fun z => curlNorm (Ξ z) p.1) q ν :=
    eLpNorm_comp_measurePreserving (g := fun z => curlNorm (Ξ z) p.1) (hc.measurable.comp hΞ).aestronglyMeasurable measurePreserving_snd
  have h1 : eLpNorm (fun z : Ω × D => curlNorm (X z.1 + Ξ z.2) p.1) q (μ.prod ν) ≤
      eLpNorm (fun z => curlNorm (X z) p.1) q μ + eLpNorm (fun z => curlNorm (Ξ z) p.1) q ν := by
    rw [← e₁, ← e₂]
    have hadd := eLpNorm_add_le (p := q) (μ := μ.prod ν) (f := fun z : Ω × D => curlNorm (X z.1) p.1)
      (g := fun z : Ω × D => curlNorm (Ξ z.2) p.1) m₁.aestronglyMeasurable m₂.aestronglyMeasurable hq
    have hmono : eLpNorm (fun z : Ω × D => curlNorm (X z.1 + Ξ z.2) p.1) q (μ.prod ν) ≤
        eLpNorm ((fun z : Ω × D => curlNorm (X z.1) p.1) + fun z : Ω × D => curlNorm (Ξ z.2) p.1) q (μ.prod ν) := by
      refine eLpNorm_mono_real fun z => ?_
      rw [Real.norm_eq_abs, abs_of_nonneg (show 0 ≤ curlNorm (X z.1 + Ξ z.2) p.1 from Real.sqrt_nonneg _)]
      exact curlNorm_add_le _ _ _
    exact le_trans hmono hadd
  calc _ ≤ ENNReal.ofReal (ω p.1) * (eLpNorm (fun z => curlNorm (X z) p.1) q μ + eLpNorm (fun z => curlNorm (Ξ z) p.1) q ν) :=
        mul_le_mul' le_rfl h1
    _ = ENNReal.ofReal (ω p.1) * eLpNorm (fun z => curlNorm (X z) p.1) q μ +
        ENNReal.ofReal (ω p.1) * eLpNorm (fun z => curlNorm (Ξ z) p.1) q ν := mul_add _ _ _
    _ ≤ _ := add_le_add (le_iSup (fun p : OrientedPlaquette m => ENNReal.ofReal (ω p.1) * eLpNorm (fun z => curlNorm (X z) p.1) q μ) p)
        (le_iSup (fun p : OrientedPlaquette m => ENNReal.ofReal (ω p.1) * eLpNorm (fun z => curlNorm (Ξ z) p.1) q ν) p)
private theorem weightedCurvatureNorm_smul_le {m : ℕ} {D : Type} [MeasurableSpace D] (ν : Measure D) (ω : TorusPlaquette m → ℝ)
    (hω0 : ∀ p, 0 ≤ ω p) (hω1 : ∀ p, ω p ≤ 1) (q : ENNReal)
    (Ξ : D → ColourForm m) (c b : ℝ) (hc : 0 ≤ c) (hb : weightedCurvatureNorm ν (fun _ => 1) q Ξ ≤ ENNReal.ofReal b) :
    weightedCurvatureNorm ν ω q (fun z => c • Ξ z) ≤ ENNReal.ofReal c * ENNReal.ofReal b := by
  refine iSup_le fun p => ?_
  have hs : ∀ Y : ColourForm m, curlNorm (c • Y) p.1 = c * curlNorm Y p.1 := fun Y => by
    unfold curlNorm
    have e : ∀ e', curl ((c • Y) e') p.1 = c * curl (Y e') p.1 := fun e' => by
      simp only [curl, Pi.smul_apply, smul_eq_mul]
      ring
    simp only [e, mul_pow, ← Finset.mul_sum]
    rw [Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq hc]
  have e1 : (fun z => curlNorm (c • Ξ z) p.1) = c • fun z => curlNorm (Ξ z) p.1 := by
    funext z
    simp [hs]
  rw [e1, eLpNorm_const_smul, Real.enorm_eq_ofReal hc]
  have h1 : eLpNorm (fun z => curlNorm (Ξ z) p.1) q ν ≤ ENNReal.ofReal b := by
    have h2 := le_iSup (fun p : OrientedPlaquette m => ENNReal.ofReal 1 * eLpNorm (fun z => curlNorm (Ξ z) p.1) q ν) p
    simp only [ENNReal.ofReal_one, one_mul] at h2
    refine le_trans h2 ?_
    simpa [weightedCurvatureNorm] using hb
  calc _ ≤ 1 * (ENNReal.ofReal c * ENNReal.ofReal b) := by
        refine mul_le_mul' ?_ (mul_le_mul' le_rfl h1)
        exact ENNReal.ofReal_le_one.2 (hω1 p.1)
    _ = _ := one_mul _
private theorem final_real_bound (x e h r C₀ c₀ D₁ W : ℝ) (m kk : ℕ) (hnk : m + 1 ≤ kk) (hh : 0 < h) (he : 0 < e) (hhe : h * e = 1) (hxh : x = h * h)
    (hr : 1 ≤ r) (hC₀ : C₀ ≤ c₀) (hc₁ : 0 ≤ C₀ * r ^ 4) (hc₀ : 0 ≤ c₀) (hD : 1 ≤ D₁) (hW : 0 ≤ W) :
    ((m + 1 : ℕ) : ℝ) * (x * (24 * W) * (C₀ * r ^ 4)) * (e * D₁) * (x / 2 * (C₀ * r ^ 4) * (e * D₁) ^ 2) ^ m ≤
      24 * (kk : ℝ) * ((1 + c₀) ^ kk * D₁ ^ (2 * kk)) * W * r ^ (4 * (m + 1)) * h := by
  have hr4 : 0 ≤ r ^ 4 := by positivity
  set c₁ := C₀ * r ^ 4 with hc₁d
  have hcc : c₁ ≤ c₀ * r ^ 4 := mul_le_mul_of_nonneg_right hC₀ hr4
  have e1 : x * e = h := by rw [hxh, mul_assoc, hhe, mul_one]
  have e2 : x / 2 * c₁ * (e * D₁) ^ 2 = c₁ * D₁ ^ 2 / 2 := by
    have : x * e ^ 2 = 1 := by
      rw [sq, ← mul_assoc, e1, hhe]
    calc x / 2 * c₁ * (e * D₁) ^ 2 = (x * e ^ 2) * (c₁ * D₁ ^ 2 / 2) := by ring
      _ = _ := by rw [this, one_mul]
  rw [e2]
  have e3 : ((m + 1 : ℕ) : ℝ) * (x * (24 * W) * c₁) * (e * D₁) = 24 * ((m + 1 : ℕ) : ℝ) * W * h * c₁ * D₁ := by
    rw [← e1]
    ring
  rw [e3]
  have h1 : (c₁ * D₁ ^ 2 / 2) ^ m ≤ (c₀ * r ^ 4 * D₁ ^ 2) ^ m := by
    refine pow_le_pow_left₀ (by positivity) ?_ m
    have a1 : 0 ≤ c₁ * D₁ ^ 2 := by positivity
    have a2 : c₁ * D₁ ^ 2 ≤ c₀ * r ^ 4 * D₁ ^ 2 := mul_le_mul_of_nonneg_right hcc (by positivity)
    linarith
  have hnk' : ((m + 1 : ℕ) : ℝ) ≤ (kk : ℝ) := by exact_mod_cast hnk
  have hc1 : c₀ ^ (m + 1) ≤ (1 + c₀) ^ kk :=
    le_trans (pow_le_pow_left₀ hc₀ (by linarith) _) (pow_le_pow_right₀ (by linarith) hnk)
  have hd1 : D₁ ^ (2 * m + 1) ≤ D₁ ^ (2 * kk) := pow_le_pow_right₀ hD (by omega)
  calc 24 * ((m + 1 : ℕ) : ℝ) * W * h * c₁ * D₁ * (c₁ * D₁ ^ 2 / 2) ^ m
      ≤ 24 * ((m + 1 : ℕ) : ℝ) * W * h * (c₀ * r ^ 4) * D₁ * (c₀ * r ^ 4 * D₁ ^ 2) ^ m := by gcongr
    _ = 24 * ((m + 1 : ℕ) : ℝ) * W * h * r ^ (4 * (m + 1)) * (c₀ ^ (m + 1) * D₁ ^ (2 * m + 1)) := by
        rw [mul_pow, mul_pow, ← pow_mul, ← pow_mul, pow_succ c₀, show 4 * (m + 1) = 4 * m + 4 by ring, pow_add r, pow_succ D₁,
          show 2 * m = 2 * m from rfl, mul_comm 2 m, mul_comm 4 m]
        ring
    _ ≤ 24 * (kk : ℝ) * W * h * r ^ (4 * (m + 1)) * ((1 + c₀) ^ kk * D₁ ^ (2 * kk)) := by gcongr
    _ = _ := by ring
private theorem eLpNorm_fderiv_integral_le {E Wv Ω D : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup Wv] [NormedSpace ℝ Wv]
    [MeasurableSpace Wv] [BorelSpace Wv] [MeasurableSpace Ω] [MeasurableSpace D] (μ : Measure Ω) [SFinite μ] (ν : Measure D) [IsProbabilityMeasure ν]
    (T : E →L[ℝ] Wv) (ξ : D → Wv) (Pf : Wv → ℝ) (G : E → ℝ) (hcf : Continuous (fderiv ℝ Pf))
    (hfd : ∀ A v, fderiv ℝ G A v = ∫ w, fderiv ℝ Pf (T A + ξ w) (T v) ∂ν) (A : Ω → E)
    (hZ : Measurable fun z : Ω × D => T (A z.1) + ξ z.2) (v : E) :
    eLpNorm (fun z => fderiv ℝ G (A z) v) 2 μ ≤ eLpNorm (fun z : Ω × D => fderiv ℝ Pf (T (A z.1) + ξ z.2) (T v)) 2 (μ.prod ν) := by
  have hc : Continuous fun Y : Wv => fderiv ℝ Pf Y (T v) := hcf.clm_apply continuous_const
  have hm : Measurable fun z : Ω × D => fderiv ℝ Pf (T (A z.1) + ξ z.2) (T v) := hc.measurable.comp hZ
  have hle := eLpNorm_integral_prod_le μ ν (fun z : Ω × D => fderiv ℝ Pf (T (A z.1) + ξ z.2) (T v)) hm
  have e : (fun z => fderiv ℝ G (A z) v) = fun z => ∫ w, fderiv ℝ Pf (T (A z) + ξ w) (T v) ∂ν := funext fun z => hfd (A z) v
  rw [e]
  exact hle
private theorem weightedCurvatureNorm_add_noise_le {m : ℕ} [NeZero m] {Ω D : Type} [MeasurableSpace Ω] [MeasurableSpace D] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (ν : Measure D) [IsProbabilityMeasure ν] (ω : TorusPlaquette m → ℝ) (hω0 : ∀ p, 0 ≤ ω p) (hω1 : ∀ p, ω p ≤ 1)
    (q : ENNReal) (hq : 1 ≤ q)
    (X : Ω → ColourForm m) (ξ₁ : D → ColourForm m) (hX : Measurable X) (hξ₁ : Measurable ξ₁) (e h Cd D₁ : ℝ) (Aν : ENNReal) (hh : 0 < h) (he : 0 < e)
    (hhe : h * e = 1) (hD1 : 1 ≤ D₁) (hCd : 0 ≤ Cd) (hDC : Cd ≤ D₁) (hb : weightedCurvatureNorm μ ω q X ≤ Aν)
    (hc : weightedCurvatureNorm ν (fun _ => 1) q ξ₁ ≤ ENNReal.ofReal Cd) (ξ : D → ColourForm m) (hξ : ∀ w, ξ w = e • ξ₁ w) :
    weightedCurvatureNorm (μ.prod ν) ω q (fun z => X z.1 + ξ z.2) ≤ ENNReal.ofReal (e * D₁) * (1 + ENNReal.ofReal h * Aν) := by
  have e0 : ξ = fun w => e • ξ₁ w := funext hξ
  subst e0
  have mξ : Measurable fun w => e • ξ₁ w := hξ₁.const_smul e
  have h1 := weightedCurvatureNorm_prod_add_le μ ν ω q hq X (fun w => e • ξ₁ w) hX mξ
  have h3 := weightedCurvatureNorm_smul_le ν ω hω0 hω1 q ξ₁ e Cd he.le hc
  refine le_trans h1 (le_trans (add_le_add hb h3) ?_)
  have e1 : ENNReal.ofReal (e * D₁) * (1 + ENNReal.ofReal h * Aν) = ENNReal.ofReal (e * D₁) + ENNReal.ofReal D₁ * Aν := by
    rw [mul_add, mul_one, ← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
    congr 3
    calc e * D₁ * h = (h * e) * D₁ := by ring
      _ = D₁ := by rw [hhe, one_mul]
  rw [e1, add_comm]
  refine add_le_add ?_ ?_
  · rw [← ENNReal.ofReal_mul he.le]
    exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hDC he.le)
  · calc Aν = 1 * Aν := (one_mul _).symm
      _ ≤ _ := mul_le_mul' (ENNReal.one_le_ofReal.2 hD1) le_rfl
private theorem ofReal_pow_mul_eq (α β γ₁ γ₂ : ℝ) (hα : 0 ≤ α) (hβ : 0 ≤ β) (h₁ : 0 ≤ γ₁) (h₂ : 0 ≤ γ₂) (Y : ENNReal) (m : ℕ) :
    ENNReal.ofReal α * ((ENNReal.ofReal β * Y) * (ENNReal.ofReal γ₁ * (ENNReal.ofReal γ₂ * (ENNReal.ofReal β * Y) ^ 2)) ^ m) =
      ENNReal.ofReal (α * β * (γ₁ * γ₂ * β ^ 2) ^ m) * Y ^ (2 * m + 1) := by
  rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul hα, ENNReal.ofReal_pow (by positivity), ENNReal.ofReal_mul (by positivity),
    ENNReal.ofReal_mul h₁, ENNReal.ofReal_pow hβ]
  ring
private theorem weighted_fderiv_sum_final_le {J : Type} [Fintype J] (wj : J → ℝ) (a₁ a₂ : J → ENNReal) (hJ : ∀ j, a₁ j ≤ a₂ j)
    (x e h r C₀ c₀ D₁ W : ℝ) (n kk : ℕ) (Nz : ENNReal) (m : ℕ)
    (hm : n = m + 1) (hnk : n ≤ kk) (hh : 0 < h) (he : 0 < e) (hhe : h * e = 1) (hxh : x = h * h) (hr : 1 ≤ r) (hC₀ : C₀ ≤ c₀)
    (hc₁ : 0 ≤ C₀ * r ^ 4) (hc₀ : 0 ≤ c₀) (hD : 1 ≤ D₁) (hW : 0 ≤ W) (hw : ∀ j, 0 ≤ wj j) (Aν Yv : ENNReal) (hYv : Yv = 1 + ENNReal.ofReal h * Aν)
    (core : ∑ j, ENNReal.ofReal (wj j) * a₂ j ≤ ENNReal.ofReal ((n : ℝ) * (x * (24 * W) * (C₀ * r ^ 4))) *
      (Nz * (ENNReal.ofReal (x / 2) * (ENNReal.ofReal (C₀ * r ^ 4) * Nz ^ 2)) ^ (n - 1)))
    (hNz : Nz ≤ ENNReal.ofReal (e * D₁) * Yv) :
    ∑ j, ENNReal.ofReal (wj j) * a₁ j ≤
      ENNReal.ofReal (24 * (kk : ℝ) * ((1 + c₀) ^ kk * D₁ ^ (2 * kk)) * W * r ^ (4 * n) * h) * Yv ^ (2 * n - 1) := by
  subst hm
  have hx0 : 0 ≤ x := by rw [hxh]; positivity
  have h1 : ∑ j, ENNReal.ofReal (wj j) * a₁ j ≤ ∑ j, ENNReal.ofReal (wj j) * a₂ j :=
    Finset.sum_le_sum fun j _ => mul_le_mul' le_rfl (hJ j)
  refine le_trans h1 (le_trans core ?_)
  have h2 : Nz * (ENNReal.ofReal (x / 2) * (ENNReal.ofReal (C₀ * r ^ 4) * Nz ^ 2)) ^ (m + 1 - 1) ≤
      (ENNReal.ofReal (e * D₁) * Yv) * (ENNReal.ofReal (x / 2) * (ENNReal.ofReal (C₀ * r ^ 4) * (ENNReal.ofReal (e * D₁) * Yv) ^ 2)) ^ m := by
    simp only [Nat.add_sub_cancel]
    gcongr
  refine le_trans (mul_le_mul' le_rfl h2) ?_
  rw [ofReal_pow_mul_eq _ _ _ _ (by positivity) (by positivity) (by positivity) hc₁, show 2 * (m + 1) - 1 = 2 * m + 1 by omega]
  refine mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) le_rfl
  exact final_real_bound x e h r C₀ c₀ D₁ W m kk hnk hh he hhe hxh hr hC₀ hc₁ hc₀ hD hW
private theorem weighted_fderiv_sum_at_level {Λ : MomentParameters} (S : MomentPoint Λ) (C₀ : ℝ)
    (hQ : ∀ i : Fin Λ.k, ∃ κ : TorusPlaquette (S.levelSide S.lastSeparated) → TorusPlaquette (S.levelSide S.lastSeparated) → ℝ,
      (∀ X X' : ColourForm (S.levelSide S.lastSeparated), colourEval (S.supportForm S.lastSeparated (S.levelSide S.lastSeparated) i) X X' =
        ∑ p ∈ plaquettesIn (Finset.univ : Finset (TorusSite (S.levelSide S.lastSeparated))),
          ∑ p' ∈ plaquettesIn (Finset.univ : Finset (TorusSite (S.levelSide S.lastSeparated))),
          κ p p' * ∑ e : Fin 3, curl (X e) p * curl (X' e) p') ∧
      ∑ p ∈ plaquettesIn (Finset.univ : Finset (TorusSite (S.levelSide S.lastSeparated))),
        ∑ p' ∈ plaquettesIn (Finset.univ : Finset (TorusSite (S.levelSide S.lastSeparated))),
        |κ p p'| * (S.distanceWeight S.lastSeparated (S.levelSide S.lastSeparated) p)⁻¹ *
          (S.distanceWeight S.lastSeparated (S.levelSide S.lastSeparated) p')⁻¹ ≤ C₀ * (S.range : ℝ) ^ 4 ∧
      ∀ (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω) (X X' : Ω → ColourForm (S.levelSide S.lastSeparated)) (q : ℝ), 1 ≤ q →
        Measurable X → Measurable X' →
        eLpNorm (fun e => colourEval (S.supportForm S.lastSeparated (S.levelSide S.lastSeparated) i) (X e) (X' e)) (ENNReal.ofReal q) μ ≤
          ENNReal.ofReal (C₀ * (S.range : ℝ) ^ 4) *
            weightedCurvatureNorm μ (S.distanceWeight S.lastSeparated (S.levelSide S.lastSeparated)) (ENNReal.ofReal (2 * q)) X *
            weightedCurvatureNorm μ (S.distanceWeight S.lastSeparated (S.levelSide S.lastSeparated)) (ENNReal.ofReal (2 * q)) X')
    {N : ℕ} [NeZero N] (hN : N = S.levelSide S.lastSeparated) (hωp : ∀ p, 0 < S.distanceWeight S.lastSeparated N p) {J Ω : Type} [Fintype J]
    [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (B : Finset (Fin Λ.k)) (hB : B.Nonempty) (hx : 0 ≤ S.scaleCoupling) (Z : Ω → ColourForm N) (hZ : Measurable Z)
    (Y : J → ColourForm N) (w : J → ℝ) (hw : ∀ j, 0 ≤ w j) (W₁ : ℝ) (hW : 0 ≤ W₁)
    (hY : ∀ p : OrientedPlaquette N, ∑ j, w j * curlNorm (Y j) p.1 ≤ W₁ * (S.distanceWeight S.lastSeparated N p.1)⁻¹) :
    ∑ j, ENNReal.ofReal (w j) * eLpNorm (fun z => fderiv ℝ (S.formProduct S.lastSeparated N B) (Z z) (Y j)) 2 P ≤
      ENNReal.ofReal ((B.card : ℝ) * (S.scaleCoupling * W₁ * (C₀ * (S.range : ℝ) ^ 4))) *
        (weightedCurvatureNorm P (S.distanceWeight S.lastSeparated N) (8 * (Λ.k : ENNReal)) Z * (ENNReal.ofReal (S.scaleCoupling / 2) *
          (ENNReal.ofReal (C₀ * (S.range : ℝ) ^ 4) *
            weightedCurvatureNorm P (S.distanceWeight S.lastSeparated N) (8 * (Λ.k : ENNReal)) Z ^ 2)) ^ (B.card - 1)) := by
  subst hN
  choose κ h1 h2 h3 using hQ
  have hcard : B.card ≤ Λ.k := by simpa using Finset.card_le_univ B
  have hpos : 1 ≤ B.card := hB.card_pos
  obtain ⟨i₀, -⟩ := hB
  have hc₁ : 0 ≤ C₀ * (S.range : ℝ) ^ 4 := by
    refine le_trans (Finset.sum_nonneg fun p _ => Finset.sum_nonneg fun p' _ => ?_) (h2 i₀)
    have a1 := (inv_pos.2 (hωp p)).le
    have a2 := (inv_pos.2 (hωp p')).le
    positivity
  set Nz := weightedCurvatureNorm P (S.distanceWeight S.lastSeparated (S.levelSide S.lastSeparated)) (8 * (Λ.k : ENNReal)) Z with hNz
  have hple : ∀ p ∈ plaquettesIn (Finset.univ : Finset (TorusSite (S.levelSide S.lastSeparated))), p.2.1 < p.2.2 := fun p hp =>
    (Finset.mem_filter.1 hp).2.1
  have q1 : ((2 * B.card : ℕ) : ENNReal) ≤ 8 * (Λ.k : ENNReal) := by
    have : ((2 * B.card : ℕ) : ENNReal) ≤ ((8 * Λ.k : ℕ) : ENNReal) := by exact_mod_cast (by omega : 2 * B.card ≤ 8 * Λ.k)
    simpa using this
  have q2 : ENNReal.ofReal (2 * (2 * B.card : ℕ)) ≤ 8 * (Λ.k : ENNReal) := by
    have e : ENNReal.ofReal (2 * (2 * B.card : ℕ)) = ((4 * B.card : ℕ) : ENNReal) := by
      rw [show (2 * ((2 * B.card : ℕ) : ℝ)) = ((4 * B.card : ℕ) : ℝ) by push_cast; ring, ENNReal.ofReal_natCast]
    rw [e]
    have : ((4 * B.card : ℕ) : ENNReal) ≤ ((8 * Λ.k : ℕ) : ENNReal) := by exact_mod_cast (by omega : 4 * B.card ≤ 8 * Λ.k)
    simpa using this
  have hZ1 : ∀ p ∈ plaquettesIn (Finset.univ : Finset (TorusSite (S.levelSide S.lastSeparated))),
      eLpNorm (fun z => curlNorm (Z z) p) ((2 * B.card : ℕ) : ENNReal) P ≤
        ENNReal.ofReal (S.distanceWeight S.lastSeparated (S.levelSide S.lastSeparated) p)⁻¹ * Nz := fun p hp => by
    have hmono := weightedCurvatureNorm_mono P (S.distanceWeight S.lastSeparated (S.levelSide S.lastSeparated)) _ _ q1 Z hZ
    have hle : ENNReal.ofReal (S.distanceWeight S.lastSeparated (S.levelSide S.lastSeparated) p) *
        eLpNorm (fun z => curlNorm (Z z) p) ((2 * B.card : ℕ) : ENNReal) P ≤ Nz :=
      le_trans (le_iSup (fun p' : OrientedPlaquette (S.levelSide S.lastSeparated) =>
        ENNReal.ofReal (S.distanceWeight S.lastSeparated (S.levelSide S.lastSeparated) p'.1) *
        eLpNorm (fun z => curlNorm (Z z) p'.1) ((2 * B.card : ℕ) : ENNReal) P) ⟨p, hple p hp⟩) hmono
    have hω := hωp p
    calc _ = ENNReal.ofReal (S.distanceWeight S.lastSeparated (S.levelSide S.lastSeparated) p)⁻¹ *
          (ENNReal.ofReal (S.distanceWeight S.lastSeparated (S.levelSide S.lastSeparated) p) *
          eLpNorm (fun z => curlNorm (Z z) p) ((2 * B.card : ℕ) : ENNReal) P) := by
          rw [← mul_assoc, ← ENNReal.ofReal_mul (inv_pos.2 hω).le, inv_mul_cancel₀ hω.ne']
          simp
      _ ≤ _ := mul_le_mul' le_rfl hle
  have hZ2 : ∀ i, eLpNorm (fun z => colourEval (S.supportForm S.lastSeparated (S.levelSide S.lastSeparated) i) (Z z) (Z z))
      ((2 * B.card : ℕ) : ENNReal) P ≤ ENNReal.ofReal (C₀ * (S.range : ℝ) ^ 4) * Nz ^ 2 := fun i => by
    have h4 := h3 i Ω P Z Z ((2 * B.card : ℕ) : ℝ) (by exact_mod_cast (by omega : 1 ≤ 2 * B.card)) hZ hZ
    rw [ENNReal.ofReal_natCast] at h4
    refine le_trans h4 ?_
    have hmono := weightedCurvatureNorm_mono P (S.distanceWeight S.lastSeparated (S.levelSide S.lastSeparated)) _ _ q2 Z hZ
    rw [mul_assoc, sq]
    exact mul_le_mul' le_rfl (mul_le_mul' hmono hmono)
  exact weighted_fderiv_eLpNorm_sum_le P (fun i => S.supportForm S.lastSeparated (S.levelSide S.lastSeparated) i) B S.scaleCoupling hx _ κ h1
    (S.distanceWeight S.lastSeparated (S.levelSide S.lastSeparated)) hωp _ hc₁ h2 Z hZ Y w hw W₁ hW
    (fun p hp => hY ⟨p, hple p hp⟩) Nz hZ1 hZ2
end Assembly
private theorem forAllParameters_and {P P' : MomentParameters → Prop} (h : ForAllParameters P) (h' : ForAllParameters P') :
    ForAllParameters fun Λ => P Λ ∧ P' Λ := by apply _root_.YangMills.SharedProofs.p2495 <;> assumption
private theorem forAllParameters_mono {P P' : MomentParameters → Prop} (h : ForAllParameters P) (f : ∀ Λ, P Λ → P' Λ) :
    ForAllParameters P' := by apply _root_.YangMills.SharedProofs.p9549 <;> assumption
private theorem forAllParameters_contraction (h : responseContractionStatement) :
    ForAllParameters fun Λ => 4 ≤ Λ.stepParams.side ∧ 0 < Λ.stepParams.weightRate ∧ ∃ θ : ℝ, 0 ≤ θ ∧ θ ≤ 1 ∧
    ∀ (u n : ℕ) [NeZero n], 64 ≤ n →
      ∀ (ω : TorusPlaquette (n * Λ.stepParams.side) → ℝ) (ω' : TorusPlaquette n → ℝ), (∀ p, 0 < ω p) → (∀ p, 0 < ω' p) →
      IsSlowlyVaryingPair Λ.stepParams.side (Λ.stepParams.weightRate / 8) ω ω' →
      ∀ (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω) (X : Ω → ColourForm n) (q : ENNReal), 1 ≤ q → Measurable X →
        weightedCurvatureNorm μ ω q (fun e => pushColours Λ.stepParams.coupling Λ.table.ρA Λ.stepParams.side u (X e)) ≤
          ENNReal.ofReal θ * weightedCurvatureNorm μ ω' q X := by
  intro a ha
  obtain ⟨Cw, hCw, L₀, rt₀, C₀, hrt, H⟩ := h a ha
  refine ⟨max L₀ 4, rt₀, C₀, hrt, ?_⟩
  intro L hL hLL Tb ha' hLT hD hCs hO hrtT hCd Kr hKr
  obtain ⟨hsmall, y₀, Hy⟩ := H L hL (le_trans (le_max_left _ _) hLL) Tb ha' hLT hD hCs hO hrtT hCd
  have hL4 : 4 ≤ L := le_trans (le_max_right _ _) hLL
  refine ⟨y₀, fun y hy hret hwil g hg hgy k _ hk2 hk8 R d hd => ⟨?_, ?_, Cw * (L : ℝ) ^ (-(1 / 2) : ℝ), by positivity, ?_, ?_⟩⟩
  · show 4 ≤ (Tb.stepParameters y).side
    have e : (Tb.stepParameters y).side = Tb.side := rfl
    rw [e, hLT]
    exact hL4
  · have := hD.rt_pos
    show 0 < (Tb.stepParameters y).rt / 2 ^ 10
    have e : (Tb.stepParameters y).rt = Tb.rt := rfl
    rw [e]
    positivity
  · refine le_trans hsmall ?_
    have h1 : (L : ℝ) ^ (-(1 / 4) : ℝ) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast (by omega : 1 ≤ L)) (by norm_num)
    have h2 : (0 : ℝ) ≤ (L : ℝ) ^ (-(1 / 4) : ℝ) := by positivity
    norm_num
    nlinarith
  · intro u n _ hn ω ω' h1 h2 hs Ω _ μ X q hq hX
    exact Hy y hy hret hwil u n hn ω ω' h1 h2 hs Ω μ X q hq hX
private theorem eLpNorm_const_dirac (c : ℝ) : eLpNorm (fun _ : Unit => c) ⊤ (Measure.dirac ()) = ENNReal.ofReal |c| := by
  rw [eLpNorm_exponent_top, eLpNormEssSup_const _ (by simp), Real.enorm_eq_ofReal_abs]
private theorem descend_weighted_curlNorm_le (a ρA : ℝ) (L : ℕ) [NeZero L] (hL : 1 ≤ L) (t : ℕ) (ωf : (u m : ℕ) → TorusPlaquette m → ℝ)
    (hstep : ∀ (u m : ℕ) [NeZero m], 64 ≤ m → ∀ (X : ColourForm m) (b : ℝ), 0 ≤ b →
      (∀ p' : OrientedPlaquette m, ωf (u + 1) m p'.1 * curlNorm X p'.1 ≤ b) →
      ∀ p : OrientedPlaquette (m * L), ωf u (m * L) p.1 * curlNorm (pushColours a ρA L u X) p.1 ≤ b) :
    ∀ (d m : ℕ) [NeZero m], 64 ≤ m → ∀ (X : ColourForm m) (b : ℝ), 0 ≤ b →
      (∀ p' : OrientedPlaquette m, ωf (t + d) m p'.1 * curlNorm X p'.1 ≤ b) →
      ∀ p : OrientedPlaquette (fineSide L d m), ωf t (fineSide L d m) p.1 * curlNorm (descend (L := L) a ρA t d m X) p.1 ≤ b
  | 0, m, _, _, X, b, _, h, p => h p
  | d + 1, m, _, h64, X, b, hb, h, p => by
    have h1 := hstep (t + d) m h64 X b hb h
    exact descend_weighted_curlNorm_le a ρA L hL t ωf hstep d (m * L) (le_trans h64 (Nat.le_mul_of_pos_right m hL)) _ b hb h1 p
private theorem isSlowlyVaryingPair_sqrt {n : ℕ} (L : ℕ) (c : ℝ) (hc : 0 ≤ c) (ω : TorusPlaquette (n * L) → ℝ) (ω' : TorusPlaquette n → ℝ)
    (h' : ∀ p, 0 ≤ ω' p)
    (h : IsSlowlyVaryingPair L c ω ω') : IsSlowlyVaryingPair L c (fun p => Real.sqrt (ω p)) (fun p => Real.sqrt (ω' p)) := fun p p' => by
  have hE : 1 ≤ Real.exp (c * (1 + (TorusFields.supDist (parentBlock L p.1) p'.1 : ℝ))) := Real.one_le_exp (by positivity)
  have h1 := Real.sqrt_le_sqrt (h p p')
  rw [Real.sqrt_mul (by positivity)] at h1
  refine le_trans h1 (mul_le_mul_of_nonneg_right ?_ (Real.sqrt_nonneg _))
  exact Real.sqrt_le_iff.2 ⟨by positivity, by nlinarith⟩
set_option maxHeartbeats 4000000 in
theorem formMeanDerivBound (hQ : supportFormCurvatureKernelStatement) (hR : responseContractionStatement)
    (hA : weightContractionStatement) (hW : formMeansStatement) (hN : scaleWindowStatement) :
    formMeanDerivBoundStatement := by
  unfold supportFormCurvatureKernelStatement weightContractionStatement formMeansStatement
    scaleWindowStatement ForAllPoints at *
  unfold formMeanDerivBoundStatement ForAllPoints
  refine forAllParameters_mono (forAllParameters_and (forAllParameters_contraction hR)
    (forAllParameters_and hQ (forAllParameters_and hA (forAllParameters_and hW hN)))) ?_
  rintro Λ ⟨⟨hL4, hrate, θ, hθ0, hθ1, hcon⟩, ⟨Cq, _, _, _, _, hq⟩, ⟨Ca, _, _, _, _, ha⟩, ⟨Cw, _, _, _, _, hw⟩, ⟨Cn, _, Xn, _, _, hn⟩⟩
  set c₀ := |Cq 0| with hc₀
  set Cd := |Cw (8 * Λ.k)| with hCd
  set D₁ := 1 + Cd with hD₁
  set K := 24 * (Λ.k : ℝ) * ((1 + c₀) ^ Λ.k * D₁ ^ (2 * Λ.k)) with hK
  refine ⟨fun _ => K, 1, max Xn (max 1 Λ.floor), one_pos, le_trans (le_max_right _ _) (le_max_right _ _), ?_⟩
  intro S hx d n _ hd hn' B
  have hxn : Xn ≤ S.scaleCoupling := le_trans (le_max_left _ _) hx
  have hx1 : 1 ≤ S.scaleCoupling := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hx
  have hx0 : 0 < S.scaleCoupling := by linarith only [hx1]
  obtain ⟨-, -, h3, -, -, hKle, hwin⟩ := hn S hxn
  have h64 : 64 ≤ n := by
    have h1 := (hwin (S.lastSeparated + d + 1) (by omega) (by omega)).2
    rw [← hn'] at h1
    calc 64 = 4 ^ 3 := by norm_num
      _ ≤ Λ.stepParams.side ^ 3 := Nat.pow_le_pow_left hL4 3
      _ ≤ Λ.stepParams.side ^ S.logIndex := Nat.pow_le_pow_right (by omega) h3
      _ ≤ n := h1
  have hL1 : 1 ≤ Λ.stepParams.side := by omega
  have h64m : 64 ≤ n * Λ.stepParams.side := le_trans h64 (Nat.le_mul_of_pos_right n hL1)
  have hmL : n * Λ.stepParams.side = S.levelSide (S.lastSeparated + d) := by
    have h1 : S.lastSeparated + d + 1 ≤ S.data.windowLevel := by omega
    rw [hn']
    show S.data.period Λ.stepParams.side * Λ.stepParams.side ^ (S.data.windowLevel - (S.lastSeparated + d + 1)) * Λ.stepParams.side =
      S.data.period Λ.stepParams.side * Λ.stepParams.side ^ (S.data.windowLevel - (S.lastSeparated + d))
    rw [mul_assoc, ← pow_succ]
    congr 2
    omega
  have hNt : fineSide Λ.stepParams.side d (n * Λ.stepParams.side) = S.levelSide S.lastSeparated := by
    have h1 : S.lastSeparated + d ≤ S.data.windowLevel := by omega
    rw [fineSide_eq, hmL]
    show S.data.period Λ.stepParams.side * Λ.stepParams.side ^ (S.data.windowLevel - (S.lastSeparated + d)) * Λ.stepParams.side ^ d =
      S.data.period Λ.stepParams.side * Λ.stepParams.side ^ (S.data.windowLevel - S.lastSeparated)
    rw [mul_assoc, ← pow_add]
    congr 2
    omega
  obtain ⟨hprob, hξm, hξi⟩ := fluctuationSample_facts Λ.stepParams.coupling Λ.table.ρA Λ.stepParams.side S.lastSeparated
    (S.scaleCoupling ^ (-(1 / 2) : ℝ)) d (n * Λ.stepParams.side)
  have := hprob
  have hG : S.formProductMean d (n * Λ.stepParams.side) B = fun A =>
      ∫ w, S.formProduct S.lastSeparated (fineSide Λ.stepParams.side d (n * Λ.stepParams.side)) B
      (descendCLM Λ.stepParams.coupling Λ.table.ρA S.lastSeparated d (n * Λ.stepParams.side) A +
        descendWithNoise (L := Λ.stepParams.side) Λ.stepParams.coupling Λ.table.ρA S.lastSeparated (S.scaleCoupling ^ (-(1 / 2) : ℝ)) d
          (n * Λ.stepParams.side) 0 w)
        ∂fluctuationSampleLaw Λ.stepParams.coupling Λ.stepParams.side S.lastSeparated d (n * Λ.stepParams.side) := funext fun A => by
    unfold MomentPoint.formProductMean
    refine integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
    show S.formProduct _ _ _ _ = S.formProduct _ _ _ _
    rw [descendWithNoise_eq_add Λ.stepParams.coupling Λ.table.ρA S.lastSeparated _ d (n * Λ.stepParams.side) A w]
    rfl
  have hPol : PolyGrowthC3 (S.formProduct S.lastSeparated (fineSide Λ.stepParams.side d (n * Λ.stepParams.side)) B) :=
    PolyGrowthC3.prod B _ fun i _ => (PolyGrowthC3.const _).mul (polyGrowthC3_colourEval _)
  obtain ⟨c3, Cp, kp, hCp, hbp⟩ := hPol
  obtain ⟨hsm, hgr, hfd⟩ := contDiff_two_integral_affine
    (fluctuationSampleLaw Λ.stepParams.coupling Λ.stepParams.side S.lastSeparated d (n * Λ.stepParams.side))
    (descendCLM Λ.stepParams.coupling Λ.table.ρA S.lastSeparated d (n * Λ.stepParams.side))
    (fun w => descendWithNoise (L := Λ.stepParams.side) Λ.stepParams.coupling Λ.table.ρA S.lastSeparated (S.scaleCoupling ^ (-(1 / 2) : ℝ)) d
      (n * Λ.stepParams.side) 0 w) hξm.aestronglyMeasurable hξi _ c3 Cp kp hbp
  rw [hG]
  refine ⟨hsm, hgr, ?_⟩
  intro w W hw0 hW0 hwW Ω _ μ _ A hAm
  rcases B.eq_empty_or_nonempty with rfl | hB
  · have hconst : (fun A : ColourForm (n * Λ.stepParams.side) =>
        ∫ w, S.formProduct S.lastSeparated (fineSide Λ.stepParams.side d (n * Λ.stepParams.side)) ∅
        (descendCLM Λ.stepParams.coupling Λ.table.ρA S.lastSeparated d (n * Λ.stepParams.side) A +
          descendWithNoise (L := Λ.stepParams.side) Λ.stepParams.coupling Λ.table.ρA S.lastSeparated (S.scaleCoupling ^ (-(1 / 2) : ℝ)) d
            (n * Λ.stepParams.side) 0 w)
        ∂fluctuationSampleLaw Λ.stepParams.coupling Λ.stepParams.side S.lastSeparated d (n * Λ.stepParams.side)) = fun _ => 1 := by
      funext A
      simp [MomentPoint.formProduct]
    rw [hconst]
    simp
  have hωp : ∀ (u m : ℕ) (p : TorusPlaquette m), 0 < S.distanceWeight u m p := fun u m p => Real.exp_pos _
  have hω1 : ∀ (u m : ℕ) (p : TorusPlaquette m), S.distanceWeight u m p ≤ 1 := fun u m p => by
    refine Real.exp_le_one_iff.2 ?_
    have : 0 ≤ Λ.stepParams.weightRate / 8 * max 0 ((TorusFields.supDist p.1 (S.originSite u m) : ℝ) - (S.radius : ℝ)) :=
      mul_nonneg (by positivity) (le_max_left _ _)
    linarith only [this]
  obtain ⟨hCa0, hCa1, hslow, -, -, -, hlast⟩ := ha S
  have hcs : ∀ {m : ℕ} (X : ColourForm m) (p : TorusPlaquette m), 0 ≤ curlNorm X p := fun _ _ => Real.sqrt_nonneg _
  have hstep : ∀ (u m : ℕ) [NeZero m], 64 ≤ m → ∀ (X : ColourForm m) (b : ℝ), 0 ≤ b →
      (∀ p' : OrientedPlaquette m, Real.sqrt (S.distanceWeight (u + 1) m p'.1) * curlNorm X p'.1 ≤ b) →
      ∀ p : OrientedPlaquette (m * Λ.stepParams.side), Real.sqrt (S.distanceWeight u (m * Λ.stepParams.side) p.1) *
        curlNorm (pushColours Λ.stepParams.coupling Λ.table.ρA Λ.stepParams.side u X) p.1 ≤ b := by
    intro u m _ hm X b hb hX p
    have hmain := hcon u m hm (fun p => Real.sqrt (S.distanceWeight u (m * Λ.stepParams.side) p))
      (fun p => Real.sqrt (S.distanceWeight (u + 1) m p))
      (fun p => Real.sqrt_pos.2 (hωp _ _ _)) (fun p => Real.sqrt_pos.2 (hωp _ _ _))
      (isSlowlyVaryingPair_sqrt Λ.stepParams.side _ (by positivity) _ _ (fun p => (hωp _ _ _).le) (hslow u m)) Unit (Measure.dirac ())
      (fun _ => X) ⊤ le_top measurable_const
    have h1 : ENNReal.ofReal (Real.sqrt (S.distanceWeight u (m * Λ.stepParams.side) p.1) *
        curlNorm (pushColours Λ.stepParams.coupling Λ.table.ρA Λ.stepParams.side u X) p.1) ≤
        weightedCurvatureNorm (Measure.dirac ()) (fun p => Real.sqrt (S.distanceWeight u (m * Λ.stepParams.side) p)) ⊤
          (fun _ : Unit => pushColours Λ.stepParams.coupling Λ.table.ρA Λ.stepParams.side u X) := by
      refine le_trans (le_of_eq ?_) (le_iSup _ p)
      rw [eLpNorm_const_dirac, abs_of_nonneg (hcs _ _), ENNReal.ofReal_mul (Real.sqrt_nonneg _)]
    have h2 : weightedCurvatureNorm (Measure.dirac ()) (fun p => Real.sqrt (S.distanceWeight (u + 1) m p)) ⊤ (fun _ : Unit => X) ≤
        ENNReal.ofReal b := by
      refine iSup_le fun p' => ?_
      rw [eLpNorm_const_dirac, abs_of_nonneg (hcs _ _), ← ENNReal.ofReal_mul (Real.sqrt_nonneg _)]
      exact ENNReal.ofReal_le_ofReal (hX p')
    have h3 := le_trans h1 (le_trans hmain (mul_le_mul' le_rfl h2))
    rw [← ENNReal.ofReal_mul hθ0] at h3
    have h4 := (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 h3
    nlinarith
  have hY : ∀ p : OrientedPlaquette (fineSide Λ.stepParams.side d (n * Λ.stepParams.side)),
      ∑ j : Fin 3 × ChartBondIndex Λ.stepParams.side (S.lastSeparated + d) n, w j.2 *
        curlNorm (descend (L := Λ.stepParams.side) Λ.stepParams.coupling Λ.table.ρA S.lastSeparated d (n * Λ.stepParams.side)
          (chartColourForm (unitVariation j))) p.1 ≤
        (24 * W) * (S.distanceWeight S.lastSeparated (fineSide Λ.stepParams.side d (n * Λ.stepParams.side)) p.1)⁻¹ := fun p => by
    have hsb := weighted_unit_curl_sum_le Λ.stepParams.coupling Λ.table.ρA S.lastSeparated d
      (fun p => Real.sqrt (S.distanceWeight S.lastSeparated (fineSide Λ.stepParams.side d (n * Λ.stepParams.side)) p)) (fun p => Real.sqrt_nonneg _)
      (fun p => Real.sqrt (S.distanceWeight (S.lastSeparated + d) (n * Λ.stepParams.side) p)) (fun p => Real.sqrt_nonneg _)
      (fun X b hb h p => descend_weighted_curlNorm_le Λ.stepParams.coupling Λ.table.ρA Λ.stepParams.side hL1 S.lastSeparated
        (fun u m p => Real.sqrt (S.distanceWeight u m p)) hstep d (n * Λ.stepParams.side) h64m X b hb h p)
      w hw0 W hW0 hwW p
    have hω := hωp S.lastSeparated _ p.1
    have hs : S.distanceWeight S.lastSeparated (fineSide Λ.stepParams.side d (n * Λ.stepParams.side)) p.1 ≤
        Real.sqrt (S.distanceWeight S.lastSeparated (fineSide Λ.stepParams.side d (n * Λ.stepParams.side)) p.1) := by
      refine Real.le_sqrt_of_sq_le ?_
      have := hω1 S.lastSeparated _ p.1
      nlinarith
    have hsum0 : 0 ≤ ∑ j : Fin 3 × ChartBondIndex Λ.stepParams.side (S.lastSeparated + d) n, w j.2 *
        curlNorm (descend (L := Λ.stepParams.side) Λ.stepParams.coupling Λ.table.ρA S.lastSeparated d (n * Λ.stepParams.side)
          (chartColourForm (unitVariation j))) p.1 :=
      Finset.sum_nonneg fun j _ => mul_nonneg (hw0 _) (hcs _ _)
    rw [← div_eq_mul_inv, le_div_iff₀ hω]
    exact le_trans (mul_le_mul_of_nonneg_left hs hsum0) hsb
  have hcard : B.card ≤ Λ.k := by simpa using Finset.card_le_univ B
  obtain ⟨m, hm⟩ : ∃ m, B.card = m + 1 := ⟨B.card - 1, by have := hB.card_pos; omega⟩
  have hZm : Measurable fun z : Ω × FluctuationSample Λ.stepParams.side S.lastSeparated d (n * Λ.stepParams.side) =>
      descendCLM Λ.stepParams.coupling Λ.table.ρA S.lastSeparated d (n * Λ.stepParams.side) (A z.1) +
      descendWithNoise (L := Λ.stepParams.side) Λ.stepParams.coupling Λ.table.ρA S.lastSeparated (S.scaleCoupling ^ (-(1 / 2) : ℝ)) d
        (n * Λ.stepParams.side) 0 z.2 :=
    ((descendCLM Λ.stepParams.coupling Λ.table.ρA S.lastSeparated d (n * Λ.stepParams.side)).continuous.measurable.comp
      (hAm.comp measurable_fst)).add (hξm.comp measurable_snd)
  have core := weighted_fderiv_sum_at_level S (Cq 0) (hq S) hNt (hωp S.lastSeparated _)
    (μ.prod (fluctuationSampleLaw Λ.stepParams.coupling Λ.stepParams.side S.lastSeparated d (n * Λ.stepParams.side))) B hB hx0.le _ hZm
    (fun j : Fin 3 × ChartBondIndex Λ.stepParams.side (S.lastSeparated + d) n =>
      descend (L := Λ.stepParams.side) Λ.stepParams.coupling Λ.table.ρA S.lastSeparated d (n * Λ.stepParams.side) (chartColourForm (unitVariation j)))
    (fun j => w j.2) (fun j => hw0 j.2) (24 * W) (by positivity) hY
  have hcf : Continuous (fderiv ℝ (S.formProduct S.lastSeparated (fineSide Λ.stepParams.side d (n * Λ.stepParams.side)) B)) :=
    c3.continuous_fderiv (by norm_num)
  have hJ := fun j : Fin 3 × ChartBondIndex Λ.stepParams.side (S.lastSeparated + d) n => eLpNorm_fderiv_integral_le μ
    (fluctuationSampleLaw Λ.stepParams.coupling Λ.stepParams.side S.lastSeparated d (n * Λ.stepParams.side))
    (descendCLM Λ.stepParams.coupling Λ.table.ρA S.lastSeparated d (n * Λ.stepParams.side)) _ _ _ hcf hfd A hZm (chartColourForm (unitVariation j))
  have hk1 : 1 ≤ 8 * Λ.k := by
    have := NeZero.pos Λ.k
    omega
  have hqc : (8 * (Λ.k : ENNReal)) = ((8 * Λ.k : ℕ) : ENNReal) := by push_cast; rfl
  have hq1 : (1 : ENNReal) ≤ 8 * (Λ.k : ENNReal) := by
    rw [hqc]
    exact_mod_cast hk1
  have hhh : S.scaleCoupling ^ ((1 : ℝ) / 2) * S.scaleCoupling ^ ((1 : ℝ) / 2) = S.scaleCoupling := by
    rw [← Real.rpow_add hx0]
    norm_num
  have hhe : S.scaleCoupling ^ ((1 : ℝ) / 2) * S.scaleCoupling ^ (-(1 / 2) : ℝ) = 1 := by
    rw [← Real.rpow_add hx0]
    norm_num
  have hh0 : 0 < S.scaleCoupling ^ ((1 : ℝ) / 2) := Real.rpow_pos_of_pos hx0 _
  have he0 : 0 < S.scaleCoupling ^ (-(1 / 2) : ℝ) := Real.rpow_pos_of_pos hx0 _
  have hCd0 : 0 ≤ Cd := abs_nonneg _
  have hD1 : 1 ≤ D₁ := by
    rw [hD₁]
    linarith only [hCd0]
  have hDC : Cd ≤ D₁ := by
    rw [hD₁]
    linarith only []
  have hθa0 : 0 ≤ Ca 0 * (Λ.stepParams.side : ℝ) ^ (-(1 / 2) : ℝ) := mul_nonneg hCa0 (by positivity)
  have hθa1 : Ca 0 * (Λ.stepParams.side : ℝ) ^ (-(1 / 2) : ℝ) ≤ 1 := by
    refine le_trans hCa1 ?_
    have h1 : (Λ.stepParams.side : ℝ) ^ (-(1 / 4) : ℝ) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hL1) (by norm_num)
    have h2 : (0 : ℝ) ≤ (Λ.stepParams.side : ℝ) ^ (-(1 / 4) : ℝ) := by positivity
    norm_num
    nlinarith only [h1, h2]
  have hM : weightedCurvatureNorm μ (S.distanceWeight S.lastSeparated (fineSide Λ.stepParams.side d (n * Λ.stepParams.side)))
      (8 * (Λ.k : ENNReal)) (fun z => descendCLM Λ.stepParams.coupling Λ.table.ρA S.lastSeparated d (n * Λ.stepParams.side) (A z)) ≤
      weightedCurvatureNorm μ (S.distanceWeight (S.lastSeparated + d) (n * Λ.stepParams.side)) (8 * (Λ.k : ENNReal)) A := by
    refine le_trans (hlast d (n * Λ.stepParams.side) h64m Ω μ A _ hq1 hAm) ?_
    calc _ ≤ 1 * weightedCurvatureNorm μ (S.distanceWeight (S.lastSeparated + d) (n * Λ.stepParams.side)) (8 * (Λ.k : ENNReal)) A :=
          mul_le_mul' (ENNReal.ofReal_le_one.2 (pow_le_one₀ hθa0 hθa1)) le_rfl
      _ = _ := one_mul _
  have hξ₁ := (fluctuationSample_facts Λ.stepParams.coupling Λ.table.ρA Λ.stepParams.side S.lastSeparated 1 d (n * Λ.stepParams.side)).2.1
  have hc4 : weightedCurvatureNorm (fluctuationSampleLaw Λ.stepParams.coupling Λ.stepParams.side S.lastSeparated d (n * Λ.stepParams.side))
      (fun _ => 1) (8 * (Λ.k : ENNReal))
      (fun w => descendWithNoise (L := Λ.stepParams.side) Λ.stepParams.coupling Λ.table.ρA S.lastSeparated 1 d (n * Λ.stepParams.side) 0 w) ≤
      ENNReal.ofReal Cd := by
    have h4 := (hw S).1 d (n * Λ.stepParams.side) (by omega) hmL (8 * Λ.k) hk1
    rw [← hqc] at h4
    exact le_trans h4 (ENNReal.ofReal_le_ofReal (le_abs_self _))
  have hZe : (fun w => descendWithNoise (L := Λ.stepParams.side) Λ.stepParams.coupling Λ.table.ρA S.lastSeparated
      (S.scaleCoupling ^ (-(1 / 2) : ℝ)) d (n * Λ.stepParams.side) 0 w) =
      fun w => S.scaleCoupling ^ (-(1 / 2) : ℝ) •
        descendWithNoise (L := Λ.stepParams.side) Λ.stepParams.coupling Λ.table.ρA S.lastSeparated 1 d (n * Λ.stepParams.side) 0 w :=
    funext fun w => descendWithNoise_zero_eq_smul Λ.stepParams.coupling Λ.table.ρA Λ.stepParams.side S.lastSeparated _ d (n * Λ.stepParams.side) w
  have hNz := weightedCurvatureNorm_add_noise_le μ
    (fluctuationSampleLaw Λ.stepParams.coupling Λ.stepParams.side S.lastSeparated d (n * Λ.stepParams.side))
    (S.distanceWeight S.lastSeparated (fineSide Λ.stepParams.side d (n * Λ.stepParams.side))) (fun p => (hωp _ _ p).le) (hω1 _ _) _ hq1
    (fun z => descendCLM Λ.stepParams.coupling Λ.table.ρA S.lastSeparated d (n * Λ.stepParams.side) (A z)) _
    ((descendCLM Λ.stepParams.coupling Λ.table.ρA S.lastSeparated d (n * Λ.stepParams.side)).continuous.measurable.comp hAm) hξ₁
    _ _ Cd D₁ _ hh0 he0 hhe hD1 hCd0 hDC hM hc4 _ (fun w => congrFun hZe w)
  have hr1 : (1 : ℝ) ≤ (S.range : ℝ) := by
    have : 0 < S.range := Nat.ceil_pos.2 (Real.rpow_pos_of_pos hx0 _)
    exact_mod_cast this
  have hc₁ : 0 ≤ Cq 0 * (S.range : ℝ) ^ 4 := by
    obtain ⟨κ, -, h2, -⟩ := hq S ⟨0, NeZero.pos Λ.k⟩
    refine le_trans (Finset.sum_nonneg fun p _ => Finset.sum_nonneg fun p' _ => ?_) h2
    have a1 := (inv_pos.2 (hωp S.lastSeparated _ p)).le
    have a2 := (inv_pos.2 (hωp S.lastSeparated _ p')).le
    positivity
  exact weighted_fderiv_sum_final_le _ _ _ hJ _ _ _ _ _ c₀ D₁ W _ Λ.k _ m hm hcard hh0 he0 hhe hhh.symm hr1 (le_abs_self _) hc₁
    (abs_nonneg _) hD1 hW0 (fun j => hw0 j.2) _ _ rfl core hNz
end YangMills.Construction.MomentLaw
end
