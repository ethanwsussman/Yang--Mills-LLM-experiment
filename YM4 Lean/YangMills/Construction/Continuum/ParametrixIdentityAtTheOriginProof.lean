import YangMills.Construction.Continuum.ParametrixIdentityAtTheOrigin
import YangMills.Construction.Continuum.PartialIntegrationOfTheCubeOfTheLaplacian
import YangMills.Construction.Continuum.PlateauOfAFunctionOnTuples
import YangMills.Construction.Continuum.RationalKernelsApproximateTheDelta
import YangMills.Construction.Continuum.RegularityAndSupportsOfTheUnitKernels
import YangMills.Construction.Continuum.ThreeLaplaciansOfTheLogKernel
import Mathlib
set_option autoImplicit false
open scoped ContDiff
namespace YangMills.Construction.Parametrix
open EuclideanFunctionals TorusMetric TestFunctions MeasureTheory Filter Topology
theorem partialDerivR4_eq_fderiv {f : R4 → ℂ} (hf : Differentiable ℝ f) (μ : Fin 4) :
    partialDerivR4 μ f = fun x => fderiv ℝ f x (Pi.single μ (1 : ℝ)) := by
  funext x
  have hline : HasDerivAt (fun t : ℝ => x + t • (Pi.single μ (1 : ℝ) : R4))
      (Pi.single μ (1 : ℝ) : R4) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (Pi.single μ (1 : ℝ) : R4)).const_add x
  have hat : HasFDerivAt f (fderiv ℝ f x) (x + (0 : ℝ) • (Pi.single μ (1 : ℝ) : R4)) := by
    simpa using (hf x).hasFDerivAt
  exact (hat.comp_hasDerivAt (0 : ℝ) hline).deriv
theorem partialDerivR4_smooth_compact {f : R4 → ℂ} (hf : ContDiff ℝ ∞ f)
    (hsupp : HasCompactSupport f) (μ : Fin 4) :
    ContDiff ℝ ∞ (partialDerivR4 μ f) ∧ HasCompactSupport (partialDerivR4 μ f) := by
  rw [partialDerivR4_eq_fderiv (hf.differentiable (by simp)) μ]
  refine ⟨?_, hsupp.fderiv_apply (𝕜 := ℝ) _⟩
  exact (hf.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const
theorem laplacianR4_smooth_compact {f : R4 → ℂ} (hf : ContDiff ℝ ∞ f)
    (hsupp : HasCompactSupport f) :
    ContDiff ℝ ∞ (laplacianR4 f) ∧ HasCompactSupport (laplacianR4 f) := by
  have h : ∀ μ, ContDiff ℝ ∞ (partialDerivR4 μ (partialDerivR4 μ f)) ∧
      HasCompactSupport (partialDerivR4 μ (partialDerivR4 μ f)) := fun μ =>
    partialDerivR4_smooth_compact (partialDerivR4_smooth_compact hf hsupp μ).1
      (partialDerivR4_smooth_compact hf hsupp μ).2 μ
  have hsum : laplacianR4 f = partialDerivR4 0 (partialDerivR4 0 f) +
      partialDerivR4 1 (partialDerivR4 1 f) + partialDerivR4 2 (partialDerivR4 2 f) +
      partialDerivR4 3 (partialDerivR4 3 f) := by
    funext x
    simp [laplacianR4, Fin.sum_univ_four]
  rw [hsum]
  exact ⟨(((h 0).1.add (h 1).1).add (h 2).1).add (h 3).1,
    (((h 0).2.add (h 1).2).add (h 2).2).add (h 3).2⟩
theorem logKernel_eq_mul_log (ε : ℝ) (hε : 0 ≤ ε) (x : R4) :
    logKernel ε x = -(128 * Real.pi ^ 2)⁻¹ *
      ((euclidNormVec x ^ 2 + ε) * Real.log (euclidNormVec x ^ 2 + ε)) := by
  unfold logKernel
  split_ifs with h
  · ring
  · have hzero : euclidNormVec x ^ 2 + ε = 0 :=
      le_antisymm (not_lt.1 h) (add_nonneg (sq_nonneg _) hε)
    simp [hzero]
theorem continuous_euclidNormVec : Continuous euclidNormVec := by apply _root_.YangMills.Construction.SeparatedTuples.continuous_euclidNormVec <;> assumption
theorem continuous_logKernel (ε : ℝ) (hε : 0 ≤ ε) : Continuous (logKernel ε) := by
  have hs : Continuous fun x : R4 => euclidNormVec x ^ 2 + ε :=
    (continuous_euclidNormVec.pow 2).add continuous_const
  have : logKernel ε = fun x => -(128 * Real.pi ^ 2)⁻¹ *
      ((euclidNormVec x ^ 2 + ε) * Real.log (euclidNormVec x ^ 2 + ε)) :=
    funext (logKernel_eq_mul_log ε hε)
  rw [this]
  exact continuous_const.mul (Real.continuous_mul_log.comp hs)
theorem tendsto_integral_mul_logKernel {G : R4 → ℂ} (hG : Continuous G)
    (hsupp : HasCompactSupport G) :
    Tendsto (fun ε : ℝ => ∫ x, G x * (logKernel ε x : ℂ)) (𝓝[>] 0)
      (𝓝 (∫ x, G x * (logKernel 0 x : ℂ))) := by
  obtain ⟨R, hR⟩ := (hsupp.isCompact).exists_bound_of_continuousOn
    (f := fun x : R4 => euclidNormVec x ^ 2) (continuous_euclidNormVec.pow 2).continuousOn
  obtain ⟨M, hM⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := R + 1)).exists_bound_of_continuousOn
    (f := fun s : ℝ => s * Real.log s) Real.continuous_mul_log.continuousOn
  set c : ℝ := (128 * Real.pi ^ 2)⁻¹ with hc_def
  have hc_nonneg : 0 ≤ c := by positivity
  refine tendsto_integral_filter_of_dominated_convergence (fun x => ‖G x‖ * (c * M)) ?_ ?_ ?_ ?_
  · filter_upwards [self_mem_nhdsWithin] with ε hε
    exact (hG.mul (Complex.continuous_ofReal.comp
      (continuous_logKernel ε (le_of_lt hε)))).aestronglyMeasurable
  · filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with ε hε
    refine Eventually.of_forall fun x => ?_
    by_cases hx : x ∈ tsupport G
    · have hbound : ‖(euclidNormVec x ^ 2 + ε) * Real.log (euclidNormVec x ^ 2 + ε)‖ ≤ M := by
        refine hM _ ⟨add_nonneg (sq_nonneg _) hε.1.le, ?_⟩
        have := hR x hx
        have habs := le_abs_self (euclidNormVec x ^ 2)
        rw [Real.norm_eq_abs] at this
        linarith [hε.2]
      rw [norm_mul, Complex.norm_real, logKernel_eq_mul_log ε hε.1.le, norm_mul, norm_neg,
        Real.norm_of_nonneg (by positivity : (0 : ℝ) ≤ (128 * Real.pi ^ 2)⁻¹)]
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hbound hc_nonneg) (norm_nonneg _)
    · simp [image_eq_zero_of_notMem_tsupport hx]
  · exact (hG.norm.integrable_of_hasCompactSupport hsupp.norm).mul_const _
  · refine Eventually.of_forall fun x => ?_
    have hs : Tendsto (fun ε : ℝ => euclidNormVec x ^ 2 + ε) (𝓝[>] 0)
        (𝓝 (euclidNormVec x ^ 2 + 0)) :=
      (tendsto_nhdsWithin_of_tendsto_nhds tendsto_id).const_add _
    have hf := (Real.continuous_mul_log.tendsto _).comp hs
    have hlim : Tendsto (fun ε : ℝ => logKernel ε x) (𝓝[>] 0) (𝓝 (logKernel 0 x)) := by
      rw [logKernel_eq_mul_log 0 le_rfl x]
      refine (hf.const_mul (-(128 * Real.pi ^ 2)⁻¹)).congr' ?_
      filter_upwards [self_mem_nhdsWithin] with ε hε
      exact (logKernel_eq_mul_log ε (le_of_lt hε) x).symm
    exact ((Complex.continuous_ofReal.tendsto _).comp hlim).const_mul (G x)
theorem originIdentity_holds
    (hSA : LaplacianCubeSelfAdjoint)
    (hDelta : RationalKernelTendstoDelta)
    (hTri : TripleLaplacianLogKernel)
    (hUnit : UnitKernelRegularity) :
    OriginIdentity := by
  intro φ hφ hφc
  have h1 := laplacianR4_smooth_compact hφ hφc
  have h2 := laplacianR4_smooth_compact h1.1 h1.2
  have h3 := laplacianR4_smooth_compact h2.1 h2.2
  have hGeq : laplacianR4^[3] φ = laplacianR4 (laplacianR4 (laplacianR4 φ)) := rfl
  rw [hGeq]
  set G := laplacianR4 (laplacianR4 (laplacianR4 φ)) with hG_def
  have hGc : Continuous G := h3.1.continuous
  have hGs : HasCompactSupport G := h3.2
  have hφb : IsBoundedFun φ := by
    obtain ⟨C, hC⟩ := hφ.continuous.bounded_above_of_compact_support hφc
    exact ⟨C, hC⟩
  have hlim := hDelta φ hφ.continuous hφb
  have hident : ∀ ε : ℝ, 0 < ε → (∫ x, G x * (logKernel ε x : ℂ)) =
      ∫ x : R4, ((12 * ε ^ 3 / Real.pi ^ 2 * (euclidNormVec x ^ 2 + ε) ^ (-5 : ℤ) : ℝ) : ℂ) *
        φ x := by
    intro ε hε
    have hpos : ∀ x : R4, 0 < euclidNormVec x ^ 2 + ε := fun x => by positivity
    have hsmooth : ContDiff ℝ ∞ (logKernel ε) := by
      have := (hTri.1 ε hε.le).1
      rwa [show {x | 0 < euclidNormVec x ^ 2 + ε} = Set.univ from
        Set.eq_univ_of_forall hpos, contDiffOn_univ] at this
    have hparts := hSA φ (logKernel ε) hφ hφc hsmooth
    rw [show (laplacianR4^[3] φ) = G from rfl] at hparts
    rw [hparts]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only
    rw [(hTri.1 ε hε.le).2 x (hpos x), mul_comm]
  have hzero : (∫ x, G x * (logKernel 0 x : ℂ)) = φ 0 := by
    refine tendsto_nhds_unique (tendsto_integral_mul_logKernel hGc hGs) (hlim.congr' ?_)
    filter_upwards [self_mem_nhdsWithin] with ε hε
    exact (hident ε hε).symm
  have houter := hSA φ outerLogKernel hφ hφc hUnit.2.1
  rw [show (laplacianR4^[3] φ) = G from rfl] at houter
  have hint : ∀ v : R4 → ℝ, Continuous v → Integrable fun x => G x * (v x : ℂ) := fun v hv =>
    (hGc.mul (Complex.continuous_ofReal.comp hv)).integrable_of_hasCompactSupport hGs.mul_right
  have houter_cont : Continuous outerLogKernel := hUnit.2.1.continuous
  calc ∫ x, (innerKernelUnit x : ℂ) * G x
      = ∫ x, (G x * (logKernel 0 x : ℂ) - G x * (outerLogKernel x : ℂ)) := by
        refine integral_congr_ae (Eventually.of_forall fun x => ?_)
        simp only [innerKernelUnit, outerLogKernel]
        push_cast
        ring
    _ = (∫ x, G x * (logKernel 0 x : ℂ)) - ∫ x, G x * (outerLogKernel x : ℂ) :=
        integral_sub (hint _ (continuous_logKernel 0 le_rfl)) (hint _ houter_cont)
    _ = φ 0 - ∫ x, (outerKernelUnit x : ℂ) * φ x := by
        rw [hzero, houter]
        congr 1
        refine integral_congr_ae (Eventually.of_forall fun x => ?_)
        simp only [outerKernelUnit]
        rw [mul_comm]
end YangMills.Construction.Parametrix
