import YangMills.Construction.Towers.SecondDerivativesOfTheLogarithmicDensity
import YangMills.Construction.Towers.TheAbelianOperatorsGiveLocalSettings
import YangMills.Construction.Towers.TheSecondDerivativesOfTheDensityByLogarithmicDensities
import Mathlib
set_option autoImplicit false
open Filter Topology YangMills.Construction.OperatorCalculus
open YangMills.Construction.Tower.UnitLatticeL2 YangMills.Construction.Tower.LocalFamilies
noncomputable section
namespace YangMills.Construction.Tower.AbelianFieldDensity.SecondDerivViaLogTraces
theorem differentiableAt_partial_of_contDiffAt {g : ℝ × ℝ → ℂ} (hg : ContDiffAt ℝ 2 g 0) :
    (∀ᶠ s : ℝ in 𝓝 0, DifferentiableAt ℝ (fun t : ℝ => g (s, t)) 0) ∧
      DifferentiableAt ℝ (fun s : ℝ => deriv (fun t : ℝ => g (s, t)) 0) 0 := by
  have hnear : ∀ᶠ p in 𝓝 (0 : ℝ × ℝ), HasFDerivAt g (fderiv ℝ g p) p := by
    filter_upwards [hg.eventually (by simp)] with p hp
    exact (hp.differentiableAt (by simp)).hasFDerivAt
  have hsecond : DifferentiableAt ℝ (fderiv ℝ g) 0 :=
    (hg.fderiv_right (m := 1) (by norm_num)).differentiableAt (by simp)
  have hcont : Continuous (fun s : ℝ => ((s, 0) : ℝ × ℝ)) := by fun_prop
  have hlim : Tendsto (fun s : ℝ => ((s, 0) : ℝ × ℝ)) (𝓝 0) (𝓝 0) :=
    hcont.tendsto 0
  have hvert : ∀ s : ℝ, HasDerivAt (fun t : ℝ => ((s, t) : ℝ × ℝ)) (0, 1) 0 := fun s =>
    (hasDerivAt_const (0 : ℝ) s).prodMk (hasDerivAt_id (0 : ℝ))
  have hslice : ∀ᶠ s : ℝ in 𝓝 0, HasDerivAt (fun t : ℝ => g (s, t)) (fderiv ℝ g (s, 0) (0, 1)) 0 := by
    filter_upwards [hlim.eventually hnear] with s hs
    exact hs.comp_hasDerivAt (0 : ℝ) (hvert s)
  refine ⟨hslice.mono fun s hs => hs.differentiableAt, ?_⟩
  have hfun : (fun s : ℝ => deriv (fun t : ℝ => g (s, t)) 0) =ᶠ[𝓝 0]
      fun s => fderiv ℝ g (s, 0) (0, 1) := hslice.mono fun s hs => hs.deriv
  refine DifferentiableAt.congr_of_eventuallyEq ?_ hfun
  have horigin : DifferentiableAt ℝ (fderiv ℝ g) (((0 : ℝ), (0 : ℝ)) : ℝ × ℝ) := hsecond
  have hcomp : DifferentiableAt ℝ (fun s : ℝ => fderiv ℝ g (s, 0)) 0 :=
    DifferentiableAt.comp (0 : ℝ) horigin (by fun_prop)
  exact hcomp.clm_apply (differentiableAt_const _)
theorem deriv_deriv_sub_const_mul {f₁ f₂ : ℝ × ℝ → ℂ} (hf₁ : ContDiffAt ℝ 2 f₁ 0)
    (hf₂ : ContDiffAt ℝ 2 f₂ 0) (a : ℂ) :
    deriv (fun s : ℝ => deriv (fun t : ℝ => f₁ (s, t) - a * f₂ (s, t)) 0) 0 =
      deriv (fun s : ℝ => deriv (fun t : ℝ => f₁ (s, t)) 0) 0 -
        a * deriv (fun s : ℝ => deriv (fun t : ℝ => f₂ (s, t)) 0) 0 := by
  obtain ⟨e₁, d₁⟩ := differentiableAt_partial_of_contDiffAt hf₁
  obtain ⟨e₂, d₂⟩ := differentiableAt_partial_of_contDiffAt hf₂
  have hfun : (fun s : ℝ => deriv (fun t : ℝ => f₁ (s, t) - a * f₂ (s, t)) 0) =ᶠ[𝓝 0]
      fun s => deriv (fun t : ℝ => f₁ (s, t)) 0 - a * deriv (fun t : ℝ => f₂ (s, t)) 0 := by
    filter_upwards [e₁, e₂] with s hs₁ hs₂
    have := (hs₁.hasDerivAt.sub (hs₂.hasDerivAt.const_mul a)).deriv
    exact this
  rw [hfun.deriv_eq]
  have := (d₁.hasDerivAt.sub (d₂.hasDerivAt.const_mul a)).deriv
  exact this
theorem statement_of_logTrace (hSecond : LogTraceSecondDerivative.IntegralFormula)
    (hExp : AbelianOperatorsLocalExpansion) : Statement := by
  intro z hz L hL x b b'
  obtain ⟨C, hC, hloc⟩ := hExp z hz
  obtain ⟨locV, locE⟩ := hloc L hL
  obtain ⟨m, hm⟩ := locV.space.placement.on_lattice ((0 : Fin 3), x)
  have hx : (x : InfiniteLattice.AmbientSpace) = PeriodicOperators.castVec m := hm
  have hV := (hSecond (VertexIndex L) _ (vertexPos L) (positiveEdgeInitial (L := L)) 3 4 z C
    (laplacianOp (L := L)) hz hC locV m b b').1
  have hE := (hSecond (EdgeIndex L) _ (edgePos L) (positiveEdgeInitial (L := L)) 12 4 z C
    (AbelianFieldDensity.massiveOp (L := L)) hz hC locE m b b').1
  have hdiff := deriv_deriv_sub_const_mul hV hE (1 / 2 : ℂ)
  have hpair : ∀ s t : ℝ, (fun c => s * edgeIndicator b c + t * edgeIndicator b' c) = twoBondField b b' s t := by
    intro s t
    funext c
    simp only [twoBondField, bondIndicator, edgeIndicator]
    congr!
  unfold secondDerivative logTraceHessian
  rw [hx]
  simp only [hpair]
  rw [← hx]
  simp only [densityAt, logTraceAt] at hdiff ⊢
  rw [hx]
  exact hdiff
end YangMills.Construction.Tower.AbelianFieldDensity.SecondDerivViaLogTraces
end
