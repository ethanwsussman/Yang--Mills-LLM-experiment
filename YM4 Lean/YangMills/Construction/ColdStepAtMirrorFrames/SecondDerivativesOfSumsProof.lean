import YangMills.Construction.ColdStepAtMirrorFrames.SecondDerivativesOfSums
import Mathlib
set_option autoImplicit false
noncomputable section
open Topology
namespace YangMills.Construction.Calculus
theorem fderivFinsetSum_holds : FderivFinsetSum := by
  intro E ι _ _ s f x hf
  have hsum : ContDiffAt ℝ 3 (fun y => ∑ i ∈ s, f i y) x := ContDiffAt.sum hf
  refine ⟨hsum, fun u w => ?_⟩
  have hdiff : ∀ᶠ y in 𝓝 x, ∀ i ∈ s, DifferentiableAt ℝ (f i) y := by
    rw [Filter.eventually_all_finset]
    intro i his
    filter_upwards [(hf i his).eventually (by simp)] with y hy
    exact hy.differentiableAt (by norm_num)
  have hfirst : ∀ y, (∀ i ∈ s, DifferentiableAt ℝ (f i) y) →
      fderiv ℝ (fun z => ∑ i ∈ s, f i z) y u = ∑ i ∈ s, fderiv ℝ (f i) y u := by
    intro y hy
    have hy' : HasFDerivAt (fun z => ∑ i ∈ s, f i z) (∑ i ∈ s, fderiv ℝ (f i) y) y :=
      HasFDerivAt.fun_sum fun i his => (hy i his).hasFDerivAt
    rw [hy'.fderiv, ContinuousLinearMap.sum_apply]
  refine ⟨hfirst x hdiff.self_of_nhds, ?_⟩
  have heq : (fun y => fderiv ℝ (fun z => ∑ i ∈ s, f i z) y u) =ᶠ[𝓝 x]
      fun y => ∑ i ∈ s, fderiv ℝ (f i) y u := by
    filter_upwards [hdiff] with y hy using hfirst y hy
  rw [heq.fderiv_eq]
  have hdu : ∀ i ∈ s, DifferentiableAt ℝ (fun y => fderiv ℝ (f i) y u) x := by
    intro i his
    have h2 : ContDiffAt ℝ 2 (fderiv ℝ (f i)) x := (hf i his).fderiv_right (by norm_num)
    exact (h2.differentiableAt (by norm_num)).clm_apply (differentiableAt_const u)
  have hsecond : HasFDerivAt (fun y => ∑ i ∈ s, fderiv ℝ (f i) y u)
      (∑ i ∈ s, fderiv ℝ (fun y => fderiv ℝ (f i) y u) x) x :=
    HasFDerivAt.fun_sum fun i his => (hdu i his).hasFDerivAt
  rw [hsecond.fderiv, ContinuousLinearMap.sum_apply]
end YangMills.Construction.Calculus
end
