import YangMills.Construction.ChessboardTori.BoxAgainstTheTorus
import YangMills.Construction.ChessboardTori.GibbsPropertyInTheFormsInWhichItIsRead
import YangMills.Construction.ChessboardTori.GibbsStateAgainstTheTorusOnABox
import Mathlib
set_option autoImplicit false
open MeasureTheory
open scoped ComplexOrder
noncomputable section
namespace YangMills.Construction
open InfiniteLattice InfiniteLattice.GibbsEquivalences
namespace ChessboardTori.GibbsBoundByTorusOnBlock
theorem exp_integral_le_integral_exp {X : Type*} [MeasurableSpace X] (μ : Measure X)
    [IsProbabilityMeasure μ] {f : X → ℝ} (hf : Measurable f) {B : ℝ} (hB : ∀ x, |f x| ≤ B) :
    Real.exp (∫ x, f x ∂μ) ≤ ∫ x, Real.exp (f x) ∂μ := by
  have hfi : Integrable f μ :=
    Integrable.of_bound hf.aestronglyMeasurable B (ae_of_all _ fun x => by simpa using hB x)
  have hexpi : Integrable (Real.exp ∘ f) μ := by
    refine Integrable.of_bound (Real.measurable_exp.comp hf).aestronglyMeasurable (Real.exp B)
      (ae_of_all _ fun x => ?_)
    simp only [Function.comp_apply, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_exp.2 ((le_abs_self _).trans (hB x))
  exact convexOn_exp.map_integral_le Real.continuous_exp.continuousOn isClosed_univ
    (ae_of_all _ fun _ => Set.mem_univ _) hfi hexpi
theorem gibbsBoundByTorusOnBlock_holds (hComparison : BoxTorusComparison.Statement)
    (hGibbsForms : GibbsForms.Statement)
    (hEquiv : GibbsEquivalenceStatement) :
    GibbsBoundByTorusOnBlock.Statement := by
  intro D g hg hside ν hν H hH hreal hHmeas
  have : IsProbabilityMeasure ν := hν.1
  obtain ⟨hfaces, hcompare⟩ := hComparison D g hg hside
  have hsub : ((g.openBlockLinks : Finset D.Link) : Set D.Link) ⊆ positiveLinkSet D.mesh :=
    D.coe_boxLinks_subset_positive _
  have hkern := (hEquiv D.mesh D.β D.mesh_pos D.beta_pos).2.1 g.openBlockLinks hsub
  have hHre : ∀ U, H U = (((H U).re : ℝ) : ℂ) := fun U => Complex.ext rfl (by simp [hreal U])
  have hexpRe : ∀ U, Complex.exp (H U) = ((Real.exp (H U).re : ℝ) : ℂ) := fun U => by
    rw [Complex.ofReal_exp, ← hHre U]
  have hexpObs : IsBoundedObservable fun U => Complex.exp (H U) := by
    obtain ⟨hm, B, hB⟩ := hH
    refine ⟨Complex.measurable_exp.comp hm, Real.exp B, fun U => ?_⟩
    show ‖Complex.exp (H U)‖ ≤ _
    rw [hexpRe U, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_exp.2 ((Complex.re_le_norm _).trans (hB U))
  have hexpMeas : IsRegionMeasurable g.fundamentalBlockInterior fun U => Complex.exp (H U) :=
    Complex.measurable_exp.comp hHmeas
  have hexpNonneg : ∀ U, 0 ≤ Complex.exp (H U) := fun U => by
    rw [hexpRe U]
    exact Complex.zero_le_real.2 (Real.exp_pos _).le
  have hfactor : (Constants.SurfaceTerms.surfaceFactor : ℝ) =
      2 * (Constants.SurfaceTerms.plaquetteCount : ℝ) := by
    simp [Constants.SurfaceTerms.surfaceFactor]
  have hpointwise : ∀ ξ, (specKernel D.mesh_pos D.β _ hsub H ξ).re ≤
      Real.log (D.periodicExpectation (D.liftedObservable fun U => Complex.exp (H U))).re +
        (Constants.SurfaceTerms.surfaceFactor : ℝ) * D.β *
          (PeriodicLattice.torusSide D.L D.m / D.mesh) ^ 3 := by
    intro ξ
    obtain ⟨hprob, hintegral⟩ := hkern.2.1 ξ
    have hremeas : Measurable fun U => (H U).re := Complex.measurable_re.comp hH.1
    obtain ⟨B, hB⟩ := hH.2
    have hreBound : ∀ U, |(H U).re| ≤ B := fun U => (Complex.abs_re_le_norm _).trans (hB U)
    have hjensen := exp_integral_le_integral_exp (specImage D.mesh_pos D.β _ hsub ξ) hremeas hreBound
    have hkernH : specKernel D.mesh_pos D.β _ hsub H ξ =
        ((∫ U, (H U).re ∂specImage D.mesh_pos D.β _ hsub ξ : ℝ) : ℂ) := by
      rw [(hintegral H hH).1, ← integral_complex_ofReal]
      exact integral_congr_ae (ae_of_all _ hHre)
    have hkernExp : specKernel D.mesh_pos D.β _ hsub (fun U => Complex.exp (H U)) ξ =
        ((∫ U, Real.exp (H U).re ∂specImage D.mesh_pos D.β _ hsub ξ : ℝ) : ℂ) := by
      rw [(hintegral _ hexpObs).1, ← integral_complex_ofReal]
      exact integral_congr_ae (ae_of_all _ hexpRe)
    have hbound := hcompare _ hexpObs hexpMeas hexpNonneg ξ
    have hbound' : specKernel D.mesh_pos D.β _ hsub (fun U => Complex.exp (H U)) ξ ≤ _ := hbound
    rw [hkernExp] at hbound'
    have hreal' := (Complex.le_def.1 hbound').1
    rw [Complex.ofReal_re, Complex.re_ofReal_mul] at hreal'
    have hexpect : (PeriodicLattice.gibbsExpectation D.L D.m D.K D.β
        (D.liftedObservable fun U => Complex.exp (H U))).re =
        (D.periodicExpectation (D.liftedObservable fun U => Complex.exp (H U))).re := rfl
    rw [hexpect] at hreal'
    set R := (D.periodicExpectation (D.liftedObservable fun U => Complex.exp (H U))).re
    set m := ∫ U, (H U).re ∂specImage D.mesh_pos D.β _ hsub ξ
    set n : ℝ := (g.boundaryFaceCount : ℝ)
    have hexpm : Real.exp m ≤ Real.exp (2 * D.β * n) * R := hjensen.trans hreal'
    have hRpos : 0 < R := by
      by_contra hRpos
      have := mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos (2 * D.β * n)).le (not_lt.1 hRpos)
      linarith [Real.exp_pos m]
    have hlog : m ≤ 2 * D.β * n + Real.log R := by
      have := Real.log_le_log (Real.exp_pos m) hexpm
      rwa [Real.log_exp, Real.log_mul (Real.exp_pos _).ne' hRpos.ne', Real.log_exp] at this
    have hn : 2 * D.β * n ≤ 2 * D.β * ((Constants.SurfaceTerms.plaquetteCount : ℝ) *
        (PeriodicLattice.torusSide D.L D.m / D.mesh) ^ 3) :=
      mul_le_mul_of_nonneg_left hfaces (by linarith [D.beta_pos])
    rw [hkernH, Complex.ofReal_re, hfactor]
    linarith
  have hDLR := ((hGibbsForms D).2.1 ν hν.1 hν g.openBlockLinks hsub H hH).1
  rw [hDLR]
  have hkernInt : Integrable (specKernel D.mesh_pos D.β _ hsub H) ν := by
    obtain ⟨hm, B, hB⟩ := (hkern.1 H hH).1
    exact Integrable.of_bound hm.aestronglyMeasurable B (ae_of_all _ hB)
  have hre : (∫ U, specKernel D.mesh_pos D.β _ hsub H U ∂ν).re =
      ∫ U, (specKernel D.mesh_pos D.β _ hsub H U).re ∂ν :=
    (Complex.reCLM.integral_comp_comm hkernInt).symm
  rw [hre]
  refine (integral_mono hkernInt.re (integrable_const _) hpointwise).trans_eq ?_
  simp
end ChessboardTori.GibbsBoundByTorusOnBlock
end YangMills.Construction
end
