import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion Topology
open Filter
namespace YangMills.Construction
namespace LineCalculus
section AlongLines
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
theorem hasDerivAt_comp_affineLine {f : E → F} {x d : E} {t : ℝ} (hf : DifferentiableAt ℝ f (x + t • d)) :
    HasDerivAt (fun s : ℝ => f (x + s • d)) (fderiv ℝ f (x + t • d) d) t := by
  have hline : HasDerivAt (fun s : ℝ => x + s • d) d t := by
    simpa using ((hasDerivAt_id t).smul_const d).const_add x
  exact hf.hasFDerivAt.comp_hasDerivAt t hline
theorem eventually_differentiableAt_of_contDiffAt_two {f : E → F} {x : E} (hf : ContDiffAt ℝ 2 f x) :
    ∀ᶠ y in 𝓝 x, DifferentiableAt ℝ f y := by
  have hf1 : ContDiffAt ℝ 1 f x := hf.of_le (by norm_num)
  filter_upwards [hf1.eventually (by norm_num)] with y hy
  exact hy.differentiableAt (by norm_num)
theorem eventually_along_affineLine {P : E → Prop} {x d : E} (hP : ∀ᶠ y in 𝓝 x, P y) :
    ∀ᶠ t in 𝓝 (0 : ℝ), P (x + t • d) := by
  have htend : Filter.Tendsto (fun t : ℝ => x + t • d) (𝓝 0) (𝓝 x) := by
    have : Continuous fun t : ℝ => x + t • d := by fun_prop
    simpa using this.tendsto 0
  exact htend.eventually hP
theorem hasFDerivAt_fderiv_of_contDiffAt_two {f : E → F} {x : E} (hf : ContDiffAt ℝ 2 f x) :
    HasFDerivAt (fderiv ℝ f) (fderiv ℝ (fderiv ℝ f) x) x := by
  have hf1 : ContDiffAt ℝ 1 (fderiv ℝ f) x := hf.fderiv_right (by norm_num)
  exact (hf1.differentiableAt (by norm_num)).hasFDerivAt
theorem hasDerivAt_fderiv_apply_along_line {f : E → F} {x d e : E} (hf : ContDiffAt ℝ 2 f x) :
    HasDerivAt (fun t : ℝ => fderiv ℝ f (x + t • d) e) (fderiv ℝ (fderiv ℝ f) x d e) 0 := by
  have hD := hasFDerivAt_fderiv_of_contDiffAt_two hf
  have hline : HasDerivAt (fun t : ℝ => x + t • d) d 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const d).const_add x
  have hx : x + (0 : ℝ) • d = x := by simp
  have hcomp : HasDerivAt (fun t : ℝ => fderiv ℝ f (x + t • d)) (fderiv ℝ (fderiv ℝ f) x d) 0 := by
    refine HasFDerivAt.comp_hasDerivAt (f := fun t : ℝ => x + t • d) (l := fderiv ℝ f) 0 ?_ hline
    simpa [hx] using hD
  exact hcomp.clm_apply (hasDerivAt_const 0 e) |>.congr_deriv (by simp)
theorem second_deriv_along_line {f : E → F} {x d : E} (hf : ContDiffAt ℝ 2 f x) :
    deriv (deriv fun t : ℝ => f (x + t • d)) 0 = fderiv ℝ (fderiv ℝ f) x d d := by
  have heq : (deriv fun t : ℝ => f (x + t • d)) =ᶠ[𝓝 0] fun t => fderiv ℝ f (x + t • d) d := by
    filter_upwards [eventually_along_affineLine (d := d) (eventually_differentiableAt_of_contDiffAt_two hf)] with t ht
    exact (hasDerivAt_comp_affineLine ht).deriv
  rw [heq.deriv_eq]
  exact (hasDerivAt_fderiv_apply_along_line hf).deriv
theorem deriv_along_line {f : E → F} {x d : E} (hf : DifferentiableAt ℝ f x) :
    deriv (fun t : ℝ => f (x + t • d)) 0 = fderiv ℝ f x d := by
  have hf0 : DifferentiableAt ℝ f (x + (0 : ℝ) • d) := by simpa using hf
  simpa using (hasDerivAt_comp_affineLine hf0).deriv
theorem mixed_second_deriv_along_lines {f : E → F} {x d e : E} (hf : ContDiffAt ℝ 2 f x) :
    deriv (fun t : ℝ => deriv (fun s : ℝ => f ((x + t • d) + s • e)) 0) 0 =
      fderiv ℝ (fderiv ℝ f) x d e := by
  have heq : (fun t : ℝ => deriv (fun s : ℝ => f ((x + t • d) + s • e)) 0) =ᶠ[𝓝 0]
      fun t => fderiv ℝ f (x + t • d) e := by
    filter_upwards [eventually_along_affineLine (d := d) (eventually_differentiableAt_of_contDiffAt_two hf)] with t ht
    exact deriv_along_line ht
  rw [heq.deriv_eq]
  exact (hasDerivAt_fderiv_apply_along_line hf).deriv
end AlongLines
section Compositions
variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]
theorem fderiv_of_eventuallyEq_comp {f : E → G} {g : F → G} {h : E → F} {x : E}
    (hfg : f =ᶠ[𝓝 x] g ∘ h) (hg : DifferentiableAt ℝ g (h x)) (hh : DifferentiableAt ℝ h x) :
    fderiv ℝ f x = (fderiv ℝ g (h x)).comp (fderiv ℝ h x) := by
  rw [hfg.fderiv_eq]
  exact fderiv_comp x hg hh
theorem second_fderiv_of_eventuallyEq_comp {f : E → G} {g : F → G} {h : E → F} {x : E}
    (hfg : f =ᶠ[𝓝 x] g ∘ h) (hg : ContDiffAt ℝ 2 g (h x)) (hh : ContDiffAt ℝ 2 h x) (d e : E) :
    fderiv ℝ (fderiv ℝ f) x d e =
      fderiv ℝ (fderiv ℝ g) (h x) (fderiv ℝ h x d) (fderiv ℝ h x e) +
        fderiv ℝ g (h x) (fderiv ℝ (fderiv ℝ h) x d e) := by
  have hcont : ContinuousAt h x := hh.continuousAt
  have hgev : ∀ᶠ y in 𝓝 x, DifferentiableAt ℝ g (h y) :=
    hcont.eventually (eventually_differentiableAt_of_contDiffAt_two hg)
  have hhev := eventually_differentiableAt_of_contDiffAt_two hh
  have hfgev : ∀ᶠ y in 𝓝 x, f =ᶠ[𝓝 y] g ∘ h := hfg.eventually_nhds
  have hD : fderiv ℝ f =ᶠ[𝓝 x] fun y => (fderiv ℝ g (h y)).comp (fderiv ℝ h y) := by
    filter_upwards [hgev, hhev, hfgev] with y h1 h2 h3
    exact fderiv_of_eventuallyEq_comp h3 h1 h2
  rw [hD.fderiv_eq]
  have h1 : HasFDerivAt (fun y => fderiv ℝ g (h y))
      ((fderiv ℝ (fderiv ℝ g) (h x)).comp (fderiv ℝ h x)) x :=
    (hasFDerivAt_fderiv_of_contDiffAt_two hg).comp x (hh.differentiableAt (by norm_num)).hasFDerivAt
  have h2 := hasFDerivAt_fderiv_of_contDiffAt_two hh
  have h3 := h1.clm_comp h2
  rw [h3.fderiv]
  simp [add_comm]
end Compositions
end LineCalculus
end YangMills.Construction
end
