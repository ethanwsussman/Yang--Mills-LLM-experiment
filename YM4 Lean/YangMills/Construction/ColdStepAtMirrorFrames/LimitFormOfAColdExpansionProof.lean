import YangMills.Construction.ColdChainAtEveryLevel.LocalFormOfTheLinesProof
import YangMills.Construction.ColdChainAtEveryLevel.PathsOnTheLattice
import YangMills.Construction.ColdStepAtMirrorFrames.ResponsesNearAFlatTopProof
import YangMills.Construction.RunningCouplingSlope.CoefficientOfALocalDensityProof
import YangMills.Construction.RunningCouplingSlope.ContourKernelsAreLocalProof
import YangMills.Construction.RunningCouplingSlope.DensityOfTheStepIsLocalProof
import YangMills.Construction.SummableBoundsOfTheFlow.FlatFormOfTheMeanProof
import YangMills.Construction.ClusterExpansionOfAStep.SecondOrderOnMultiplesOfASideProof
import YangMills.Construction.ColdStepAtMirrorFrames.LimitFormOfAColdExpansion
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion Topology
open Filter
namespace YangMills.Construction
open TorusFields TorusLumps
open BlockAverages hiding unitStep gaugeTransform
namespace ColdStepAtMirrorFrames
namespace SecondVariation
section Calculus
variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
theorem fderiv_fderiv_apply_eq_zero_of_invariant {Ψ : H → ℝ} (hΨ : ContDiffAt ℝ 3 Ψ 0)
    (hd : fderiv ℝ Ψ 0 = 0)
    {γ : ℝ × ℝ → H} (hγ : ContDiffAt ℝ 2 γ (0, 0)) (w : H)
    (h0 : ∀ᶠ s in 𝓝 (0 : ℝ), γ (0, s) = s • w)
    (hinv : ∀ᶠ p in 𝓝 ((0 : ℝ), (0 : ℝ)), Ψ (γ p) = Ψ (p.2 • w)) :
    fderiv ℝ (fderiv ℝ Ψ) 0 w (fderiv ℝ γ (0, 0) (1, 0)) = 0 := by
  have hΨd : ∀ᶠ A in 𝓝 (0 : H), DifferentiableAt ℝ Ψ A :=
    (hΨ.eventually (by simp)).mono fun A hA => hA.differentiableAt (by simp)
  have hγd : ∀ᶠ p in 𝓝 ((0 : ℝ), (0 : ℝ)), DifferentiableAt ℝ γ p :=
    (hγ.eventually (by simp)).mono fun A hA => hA.differentiableAt (by simp)
  have hs0 : Tendsto (fun s : ℝ => ((0 : ℝ), s)) (𝓝 0) (𝓝 ((0 : ℝ), (0 : ℝ))) :=
    (Continuous.prodMk_right (0 : ℝ)).tendsto' 0 _ rfl
  have hsw : Tendsto (fun s : ℝ => s • w) (𝓝 0) (𝓝 (0 : H)) := by
    have : Continuous fun s : ℝ => s • w := by fun_prop
    simpa using this.tendsto 0
  set P : ℝ → H := fun s => fderiv ℝ γ (0, s) (1, 0) with hP
  have hzero : ∀ᶠ s in 𝓝 (0 : ℝ), fderiv ℝ Ψ (s • w) (P s) = 0 := by
    filter_upwards [hs0.eventually hγd, hs0.eventually hinv.eventually_nhds, h0,
      hsw.eventually hΨd] with s h1 h2 h3 h4
    have hcurve : HasDerivAt (fun τ : ℝ => (τ, s)) ((1 : ℝ), (0 : ℝ)) 0 :=
      (hasDerivAt_id (0 : ℝ)).prodMk (hasDerivAt_const (0 : ℝ) s)
    have hl : HasDerivAt (fun τ : ℝ => γ (τ, s)) (P s) 0 :=
      h1.hasFDerivAt.comp_hasDerivAt (0 : ℝ) hcurve
    have hΨ' : HasFDerivAt Ψ (fderiv ℝ Ψ (s • w)) (γ (0, s)) := by
      rw [h3]
      exact h4.hasFDerivAt
    have hc := hΨ'.comp_hasDerivAt (0 : ℝ) hl
    have hcongr : (fun τ : ℝ => Ψ (γ (τ, s))) =ᶠ[𝓝 0] fun _ => Ψ (s • w) := by
      have hts : Tendsto (fun τ : ℝ => (τ, s)) (𝓝 0) (𝓝 ((0 : ℝ), s)) :=
        (Continuous.prodMk_left s).tendsto' 0 _ rfl
      exact hts.eventually h2
    exact (hc.congr_of_eventuallyEq hcongr.symm).unique (hasDerivAt_const (0 : ℝ) _)
  have hΨ2 : DifferentiableAt ℝ (fderiv ℝ Ψ) 0 :=
    (hΨ.fderiv_right (m := 2) (by norm_num)).differentiableAt (by simp)
  have hγ2 : DifferentiableAt ℝ (fderiv ℝ γ) ((0 : ℝ), (0 : ℝ)) :=
    (hγ.fderiv_right (m := 1) (by norm_num)).differentiableAt (by simp)
  have hline : HasDerivAt (fun s : ℝ => s • w) w 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).smul_const w
  have h1 : HasDerivAt (fun s : ℝ => fderiv ℝ Ψ (s • w)) (fderiv ℝ (fderiv ℝ Ψ) 0 w) 0 := by
    have h : HasFDerivAt (fderiv ℝ Ψ) (fderiv ℝ (fderiv ℝ Ψ) 0) ((0 : ℝ) • w) := by
      rw [zero_smul]
      exact hΨ2.hasFDerivAt
    exact h.comp_hasDerivAt (0 : ℝ) hline
  have hcurve0 : HasDerivAt (fun s : ℝ => ((0 : ℝ), s)) ((0 : ℝ), (1 : ℝ)) 0 :=
    (hasDerivAt_const (0 : ℝ) (0 : ℝ)).prodMk (hasDerivAt_id (0 : ℝ))
  have h2 : HasDerivAt P (fderiv ℝ (fderiv ℝ γ) (0, 0) (0, 1) (1, 0)) 0 := by
    have h := hγ2.hasFDerivAt.comp_hasDerivAt (0 : ℝ) hcurve0
    exact h.clm_apply (hasDerivAt_const (0 : ℝ) ((1 : ℝ), (0 : ℝ))) |>.congr_deriv (by simp)
  have h3 := h1.clm_apply h2
  have h4 : HasDerivAt (fun s : ℝ => fderiv ℝ Ψ (s • w) (P s)) 0 0 :=
    (hasDerivAt_const (0 : ℝ) (0 : ℝ)).congr_of_eventuallyEq hzero
  have := h3.unique h4
  simpa [hd, hP] using this
theorem fderiv_fderiv_comp_clm {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {Ψ : H → ℝ}
    (hΨ : ContDiffAt ℝ 3 Ψ 0) (L : E →L[ℝ] H) (u v : E) :
    fderiv ℝ (fderiv ℝ (Ψ ∘ L)) 0 u v = fderiv ℝ (fderiv ℝ Ψ) 0 (L u) (L v) := by
  have hΨd : ∀ᶠ A in 𝓝 (0 : H), DifferentiableAt ℝ Ψ A :=
    (hΨ.eventually (by simp)).mono fun A hA => hA.differentiableAt (by simp)
  have hL0 : Tendsto L (𝓝 0) (𝓝 (0 : H)) := by
    simpa using L.continuous.tendsto 0
  have hev : fderiv ℝ (Ψ ∘ L) =ᶠ[𝓝 0] fun y => (fderiv ℝ Ψ (L y)).comp L := by
    filter_upwards [hL0.eventually hΨd] with y hy
    rw [fderiv_comp y hy L.differentiableAt, L.fderiv]
  rw [hev.fderiv_eq]
  have hΨ2 : DifferentiableAt ℝ (fderiv ℝ Ψ) 0 :=
    (hΨ.fderiv_right (m := 2) (by norm_num)).differentiableAt (by simp)
  have h1 : HasFDerivAt (fun y => fderiv ℝ Ψ (L y)) ((fderiv ℝ (fderiv ℝ Ψ) 0).comp L) 0 := by
    have h : HasFDerivAt (fderiv ℝ Ψ) (fderiv ℝ (fderiv ℝ Ψ) 0) (L 0) := by
      rw [map_zero]
      exact hΨ2.hasFDerivAt
    exact h.comp (0 : E) L.hasFDerivAt
  have h2 := ((ContinuousLinearMap.compL ℝ E H ℝ).flip L).hasFDerivAt.comp (0 : E) h1
  have h3 : (fun y => (fderiv ℝ Ψ (L y)).comp L) =
      ((ContinuousLinearMap.compL ℝ E H ℝ).flip L) ∘ fun y => fderiv ℝ Ψ (L y) := by
    funext y
    simp
  rw [h3, h2.fderiv]
  simp
end Calculus
section Logarithm
def imPartLinear : ℍ[ℝ] →ₗ[ℝ] imaginaryQuaternions where
  toFun v := ⟨⟨0, v.imI, v.imJ, v.imK⟩, rfl⟩
  map_add' := by
    intro a b
    apply Subtype.ext
    ext
    · show (0 : ℝ) = 0 + 0
      simp
    all_goals rfl
  map_smul' := by
    intro c a
    apply Subtype.ext
    ext
    · show (0 : ℝ) = c * 0
      simp
    all_goals rfl
def imPart : ℍ[ℝ] →L[ℝ] imaginaryQuaternions := LinearMap.toContinuousLinearMap imPartLinear
theorem imPart_coe (a : imaginaryQuaternions) : imPart (a : ℍ[ℝ]) = a := by
  apply Subtype.ext
  have h : (a : ℍ[ℝ]).re = 0 := a.2
  change (⟨0, _, _, _⟩ : ℍ[ℝ]) = _
  ext <;> simp [h]
def quatExp (q : ℍ[ℝ]) : ℍ[ℝ] := NormedSpace.exp q
theorem contDiffAt_quatExp (q : ℍ[ℝ]) (n : WithTop ℕ∞) : ContDiffAt ℝ n quatExp q :=
  (NormedSpace.exp_analytic (𝕂 := ℝ) q).contDiffAt
theorem quatExp_zero : quatExp 0 = 1 := NormedSpace.exp_zero
theorem hasFDerivAt_quatExp_zero :
    HasFDerivAt quatExp ((ContinuousLinearEquiv.refl ℝ ℍ[ℝ] : ℍ[ℝ] ≃L[ℝ] ℍ[ℝ]) : ℍ[ℝ] →L[ℝ] ℍ[ℝ]) 0 :=
  (hasStrictFDerivAt_exp_zero (𝕂 := ℝ) (𝔸 := ℍ[ℝ])).hasFDerivAt
def quatLog : ℍ[ℝ] → ℍ[ℝ] :=
  (contDiffAt_quatExp 0 2).localInverse hasFDerivAt_quatExp_zero (by simp)
theorem hasStrictFDerivAt_quatExp_zero : HasStrictFDerivAt quatExp
    ((ContinuousLinearEquiv.refl ℝ ℍ[ℝ] : ℍ[ℝ] ≃L[ℝ] ℍ[ℝ]) : ℍ[ℝ] →L[ℝ] ℍ[ℝ]) 0 :=
  (contDiffAt_quatExp 0 2).hasStrictFDerivAt' hasFDerivAt_quatExp_zero (by simp)
theorem contDiffAt_quatLog : ContDiffAt ℝ 2 quatLog 1 := by
  have h := (contDiffAt_quatExp 0 2).to_localInverse hasFDerivAt_quatExp_zero (by simp)
  rwa [quatExp_zero] at h
theorem hasFDerivAt_quatLog : HasFDerivAt quatLog (ContinuousLinearMap.id ℝ ℍ[ℝ]) 1 := by
  have h := hasStrictFDerivAt_quatExp_zero.to_localInverse.hasFDerivAt
  rw [quatExp_zero] at h
  exact h
theorem quatExp_quatLog : ∀ᶠ y in 𝓝 (1 : ℍ[ℝ]), quatExp (quatLog y) = y := by
  have h := hasStrictFDerivAt_quatExp_zero.eventually_right_inverse
  rw [quatExp_zero] at h
  exact h
theorem quatLog_quatExp : ∀ᶠ q in 𝓝 (0 : ℍ[ℝ]), quatLog (quatExp q) = q :=
  hasStrictFDerivAt_quatExp_zero.eventually_left_inverse
def unitLog (y : ℍ[ℝ]) : imaginaryQuaternions := imPart (quatLog y)
theorem contDiffAt_unitLog : ContDiffAt ℝ 2 unitLog 1 :=
  imPart.contDiff.contDiffAt.comp 1 contDiffAt_quatLog
theorem hasFDerivAt_unitLog : HasFDerivAt unitLog imPart 1 := by
  have h := imPart.hasFDerivAt.comp (1 : ℍ[ℝ]) hasFDerivAt_quatLog
  rw [ContinuousLinearMap.comp_id] at h
  exact h
theorem quatExp_unitLog :
    ∀ᶠ y in 𝓝 (1 : ℍ[ℝ]), ‖y‖ = 1 → quatExp (unitLog y : ℍ[ℝ]) = y := by
  filter_upwards [quatExp_quatLog] with y hy hn
  have hre : (quatLog y).re = 0 := by
    have h1 : ‖NormedSpace.exp (quatLog y)‖ = 1 := by
      have : NormedSpace.exp (quatLog y) = y := hy
      rw [this, hn]
    rw [Quaternion.norm_exp] at h1
    have h2 : Real.exp (quatLog y).re = 1 := by
      have h3 := Real.exp_pos (quatLog y).re
      rw [← Real.exp_eq_exp_ℝ, Real.norm_eq_abs, abs_of_pos h3] at h1
      exact h1
    simpa using h2
  have hc : ((unitLog y : imaginaryQuaternions) : ℍ[ℝ]) = quatLog y := by
    change (⟨0, _, _, _⟩ : ℍ[ℝ]) = _
    ext <;> simp [hre]
  rw [hc]
  exact hy
theorem unitLog_quatExp :
    ∀ᶠ a : imaginaryQuaternions in 𝓝 (0 : imaginaryQuaternions),
      unitLog (quatExp (a : ℍ[ℝ])) = a := by
  have hc : Tendsto (fun a : imaginaryQuaternions => (a : ℍ[ℝ])) (𝓝 0) (𝓝 (0 : ℍ[ℝ])) := by
    simpa using (continuous_subtype_val (p := fun q : ℍ[ℝ] => q ∈ imaginaryQuaternions)).tendsto 0
  filter_upwards [hc.eventually quatLog_quatExp] with a ha
  unfold unitLog
  rw [ha, imPart_coe]
theorem coe_expUnit (a : imaginaryQuaternions) :
    ((expUnit a : UnitQuaternion) : ℍ[ℝ]) = quatExp (a : ℍ[ℝ]) := rfl
theorem expUnit_zero : expUnit 0 = 1 := by apply _root_.YangMills.Construction.TorusFields.expUnit_zero <;> assumption
theorem norm_coe_unit (g : UnitQuaternion) : ‖((g : UnitQuaternion) : ℍ[ℝ])‖ = 1 := by apply _root_.YangMills.Construction.BlockAverages.norm_coe_unitQuaternion <;> assumption
theorem star_coe_imaginary (a : imaginaryQuaternions) : star (a : ℍ[ℝ]) = -(a : ℍ[ℝ]) := by apply _root_.YangMills.Construction.GaugeMotions.star_coe_imaginary <;> assumption
theorem coe_expUnit_inv (a : imaginaryQuaternions) :
    (((expUnit a)⁻¹ : UnitQuaternion) : ℍ[ℝ]) = quatExp (-(a : ℍ[ℝ])) := by
  have h : (-(a : ℍ[ℝ])).re = 0 := by
    have h : (a : ℍ[ℝ]).re = 0 := a.2
    simp [h]
  change star (NormedSpace.exp (a : ℍ[ℝ])) = NormedSpace.exp (-(a : ℍ[ℝ]))
  rw [Quaternion.exp_of_re_eq_zero _ a.2, Quaternion.exp_of_re_eq_zero _ h, norm_neg]
  simp [star_coe_imaginary]
theorem continuous_expUnit : Continuous expUnit := by apply _root_.YangMills.Construction.TorusFields.continuous_expUnit <;> assumption
end Logarithm
section Torus
variable {n : ℕ} [NeZero n]
abbrev LinkLogs (n : ℕ) [NeZero n] : Type := TorusBond n → imaginaryQuaternions
def fieldOfLogs (A : LinkLogs n) : TorusField n := fun x i => expUnit (A (x, i))
def onLogs (G : TorusField n → ℝ) (A : LinkLogs n) : ℝ := G (fieldOfLogs A)
def singleLink (b : TorusBond n) (X : imaginaryQuaternions) : LinkLogs n := Pi.single b X
def linkDirection {k : ℕ} (c : Fin k → TorusBond n) (X : Fin k → imaginaryQuaternions) :
    (Fin k → ℝ) →L[ℝ] LinkLogs n :=
  ContinuousLinearMap.pi fun b => ∑ l, if c l = b then
    (ContinuousLinearMap.proj l : (Fin k → ℝ) →L[ℝ] ℝ).smulRight (X l) else 0
theorem linkDirection_apply {k : ℕ} (c : Fin k → TorusBond n) (X : Fin k → imaginaryQuaternions)
    (σ : Fin k → ℝ) (b : TorusBond n) :
    linkDirection c X σ b = ∑ l, if c l = b then σ l • X l else 0 := by
  simp only [linkDirection, ContinuousLinearMap.coe_pi', ContinuousLinearMap.sum_apply]
  refine Finset.sum_congr rfl fun l _ => ?_
  split_ifs <;> simp
theorem linkDirection_single {k : ℕ} (c : Fin k → TorusBond n) (X : Fin k → imaginaryQuaternions)
    (l : Fin k) : linkDirection c X (Pi.single l 1) = singleLink (c l) (X l) := by
  funext b
  rw [linkDirection_apply, singleLink, Pi.single_apply, Finset.sum_eq_single l]
  · by_cases h : c l = b
    · simp [h]
    · simp [h, Ne.symm h]
  · intro l' _ hne
    split_ifs <;> simp [hne]
  · simp
theorem perturb_trivialField {k : ℕ} (c : Fin k → TorusBond n) (X : Fin k → imaginaryQuaternions)
    (σ : Fin k → ℝ) : perturb c X σ (trivialField n) = fieldOfLogs (linkDirection c X σ) := by
  funext x i
  simp only [perturb, trivialField, fieldOfLogs, linkDirection_apply, mul_one]
theorem onLogs_comp {k : ℕ} (G : TorusField n → ℝ) (c : Fin k → TorusBond n)
    (X : Fin k → imaginaryQuaternions) :
    (fun σ : Fin k → ℝ => G (perturb c X σ (trivialField n))) = onLogs G ∘ linkDirection c X := by
  funext σ
  simp only [Function.comp, onLogs, perturb_trivialField]
instance finiteDimensional_imaginaryQuaternions : FiniteDimensional ℝ imaginaryQuaternions :=
  FiniteDimensional.finiteDimensional_submodule imaginaryQuaternions
theorem contDiffAt_onLogs {G : TorusField n → ℝ} (hG : ContDiffThreeAt G (trivialField n)) :
    ContDiffAt ℝ 3 (onLogs G) 0 := by
  classical
  let bs := Module.finBasis ℝ imaginaryQuaternions
  let ι := TorusBond n × Fin (Module.finrank ℝ imaginaryQuaternions)
  let e := (Fintype.equivFin ι).symm
  let c : Fin (Fintype.card ι) → TorusBond n := fun l => (e l).1
  let X : Fin (Fintype.card ι) → imaginaryQuaternions := fun l => bs (e l).2
  let π₀ : LinkLogs n →ₗ[ℝ] (Fin (Fintype.card ι) → ℝ) :=
    { toFun := fun A l => bs.repr (A (e l).1) (e l).2
      map_add' := by intro a b; funext l; simp
      map_smul' := by intro r a; funext l; simp }
  let π : LinkLogs n →L[ℝ] (Fin (Fintype.card ι) → ℝ) := LinearMap.toContinuousLinearMap π₀
  have hid : ∀ A : LinkLogs n, linkDirection c X (π A) = A := by
    intro A
    funext b
    rw [linkDirection_apply]
    have h1 : ∑ l, (if c l = b then (π A l) • X l else 0) =
        ∑ p : ι, (if p.1 = b then bs.repr (A p.1) p.2 • bs p.2 else 0) :=
      e.sum_comp fun p : ι => if p.1 = b then bs.repr (A p.1) p.2 • bs p.2 else 0
    rw [h1, Fintype.sum_prod_type, Finset.sum_eq_single b]
    · simp only [if_true]
      exact bs.sum_repr (A b)
    · intro b' _ hne
      simp [hne]
    · simp
  have hφ := hG (Fintype.card ι) c X
  have hcomp : onLogs G = (fun σ => G (perturb c X σ (trivialField n))) ∘ π := by
    funext A
    simp only [Function.comp, perturb_trivialField, onLogs, hid]
  rw [hcomp]
  refine ContDiffAt.comp (0 : LinkLogs n) ?_ π.contDiff.contDiffAt
  simpa using hφ
theorem mixedDeriv_two_eq {G : TorusField n → ℝ} (hG : ContDiffThreeAt G (trivialField n))
    (c : Fin 2 → TorusBond n) (X : Fin 2 → imaginaryQuaternions) :
    mixedDeriv G (trivialField n) c X =
      fderiv ℝ (fderiv ℝ (onLogs G)) 0 (singleLink (c 0) (X 0)) (singleLink (c 1) (X 1)) := by
  unfold mixedDeriv
  rw [iteratedFDeriv_two_apply, onLogs_comp,
    fderiv_fderiv_comp_clm (contDiffAt_onLogs hG), linkDirection_single, linkDirection_single]
end Torus
section Gauge
variable {n : ℕ} [NeZero n]
theorem continuous_expUnit_apply (b : TorusBond n) :
    Continuous fun A : LinkLogs n => expUnit (A b) :=
  continuous_expUnit.comp (continuous_apply b)
theorem fieldOfLogs_zero : fieldOfLogs (0 : LinkLogs n) = trivialField n := by apply _root_.YangMills.Construction.RunningCouplingSlope.LocalDensityCoefficient.expOfCoords_zero <;> assumption
theorem eventually_isCold_fieldOfLogs {σ : ℝ} (hσ : 0 < σ) :
    ∀ᶠ A in 𝓝 (0 : LinkLogs n), IsCold σ (fieldOfLogs A) := by
  have hone : ∀ x μ ν, ∀ᶠ A in 𝓝 (0 : LinkLogs n), curvature (fieldOfLogs A) x μ ν < σ := by
    intro x μ ν
    have hc : Continuous fun A : LinkLogs n => curvature (fieldOfLogs A) x μ ν := by
      unfold curvature holonomy fieldOfLogs
      refine Continuous.norm (Continuous.sub (continuous_subtype_val.comp ?_) continuous_const)
      exact (((continuous_expUnit_apply _).mul (continuous_expUnit_apply _)).mul
        (continuous_expUnit_apply _).inv).mul (continuous_expUnit_apply _).inv
    have h0 : curvature (fieldOfLogs (0 : LinkLogs n)) x μ ν = 0 := by
      rw [fieldOfLogs_zero]
      simp [curvature, holonomy, trivialField]
    exact hc.continuousAt.eventually_lt continuousAt_const (by rw [h0]; exact hσ)
  have : ∀ᶠ A in 𝓝 (0 : LinkLogs n), ∀ x μ ν, curvature (fieldOfLogs A) x μ ν < σ :=
    eventually_all.mpr fun x => eventually_all.mpr fun μ => eventually_all.mpr fun ν => hone x μ ν
  exact this.mono fun A hA x μ ν _ => hA x μ ν
def gaugeCurve (lam : TorusSite n → imaginaryQuaternions) (w : LinkLogs n) (b : TorusBond n)
    (p : ℝ × ℝ) : UnitQuaternion :=
  expUnit (p.1 • lam b.1) * expUnit (p.2 • w b) * (expUnit (p.1 • lam (b.1 + unitStep n b.2)))⁻¹
theorem coe_gaugeCurve (lam : TorusSite n → imaginaryQuaternions) (w : LinkLogs n)
    (b : TorusBond n) (p : ℝ × ℝ) :
    ((gaugeCurve lam w b p : UnitQuaternion) : ℍ[ℝ]) =
      quatExp (p.1 • (lam b.1 : ℍ[ℝ])) * quatExp (p.2 • (w b : ℍ[ℝ])) *
        quatExp (-(p.1 • (lam (b.1 + unitStep n b.2) : ℍ[ℝ]))) := by
  simp only [gaugeCurve, Submonoid.coe_mul, coe_expUnit_inv, coe_expUnit, Submodule.coe_smul]
theorem gaugeCurve_zero (lam : TorusSite n → imaginaryQuaternions) (w : LinkLogs n)
    (b : TorusBond n) : ((gaugeCurve lam w b (0, 0) : UnitQuaternion) : ℍ[ℝ]) = 1 := by
  rw [coe_gaugeCurve]
  simp [quatExp_zero]
theorem contDiffAt_gaugeCurve (lam : TorusSite n → imaginaryQuaternions) (w : LinkLogs n)
    (b : TorusBond n) :
    ContDiffAt ℝ 2 (fun p : ℝ × ℝ => ((gaugeCurve lam w b p : UnitQuaternion) : ℍ[ℝ])) (0, 0) := by
  have he : ∀ (f : ℝ × ℝ → ℍ[ℝ]), ContDiff ℝ 2 f →
      ContDiffAt ℝ 2 (fun p => quatExp (f p)) ((0 : ℝ), (0 : ℝ)) := fun f hf =>
    ContDiffAt.comp _ (contDiffAt_quatExp _ 2) hf.contDiffAt
  simp only [coe_gaugeCurve]
  refine ContDiffAt.mul (ContDiffAt.mul (he _ ?_) (he _ ?_)) (he _ ?_)
  · exact contDiff_fst.smul contDiff_const
  · exact contDiff_snd.smul contDiff_const
  · exact (contDiff_fst.smul contDiff_const).neg
def gaugeFamily (lam : TorusSite n → imaginaryQuaternions) (w : LinkLogs n) (p : ℝ × ℝ) :
    LinkLogs n :=
  fun b => unitLog (gaugeCurve lam w b p : UnitQuaternion)
theorem contDiffAt_gaugeFamily (lam : TorusSite n → imaginaryQuaternions) (w : LinkLogs n) :
    ContDiffAt ℝ 2 (gaugeFamily lam w) (0, 0) := by
  refine contDiffAt_pi.mpr fun b => ?_
  have h : ContDiffAt ℝ 2 unitLog ((gaugeCurve lam w b (0, 0) : UnitQuaternion) : ℍ[ℝ]) := by
    rw [gaugeCurve_zero]
    exact contDiffAt_unitLog
  exact h.comp ((0 : ℝ), (0 : ℝ)) (contDiffAt_gaugeCurve lam w b)
theorem expUnit_gaugeFamily (lam : TorusSite n → imaginaryQuaternions) (w : LinkLogs n) :
    ∀ᶠ p in 𝓝 ((0 : ℝ), (0 : ℝ)), ∀ b, expUnit (gaugeFamily lam w p b) = gaugeCurve lam w b p := by
  refine eventually_all.mpr fun b => ?_
  have hc : Tendsto (fun p : ℝ × ℝ => ((gaugeCurve lam w b p : UnitQuaternion) : ℍ[ℝ]))
      (𝓝 (0, 0)) (𝓝 1) := by
    have := (contDiffAt_gaugeCurve lam w b).continuousAt.tendsto
    rwa [gaugeCurve_zero] at this
  filter_upwards [hc.eventually quatExp_unitLog] with p hp
  apply Subtype.ext
  rw [coe_expUnit]
  exact hp (norm_coe_unit _)
theorem gaugeFamily_zero_fst (lam : TorusSite n → imaginaryQuaternions) (w : LinkLogs n) :
    ∀ᶠ s in 𝓝 (0 : ℝ), gaugeFamily lam w (0, s) = s • w := by
  have hone : ∀ b, ∀ᶠ s in 𝓝 (0 : ℝ), gaugeFamily lam w (0, s) b = s • w b := by
    intro b
    have hc : Tendsto (fun s : ℝ => s • w b) (𝓝 0) (𝓝 (0 : imaginaryQuaternions)) := by
      have : Continuous fun s : ℝ => s • w b := by fun_prop
      simpa using this.tendsto 0
    filter_upwards [hc.eventually unitLog_quatExp] with s hs
    have h1 : ((gaugeCurve lam w b (0, s) : UnitQuaternion) : ℍ[ℝ]) =
        quatExp ((s • w b : imaginaryQuaternions) : ℍ[ℝ]) := by
      rw [coe_gaugeCurve]
      simp [quatExp_zero]
    simp only [gaugeFamily]
    rw [h1, hs]
  exact (eventually_all.mpr hone).mono fun s hs => funext hs
theorem onLogs_gaugeFamily {G : TorusField n → ℝ} {σ : ℝ} (hσ : 0 < σ)
    (hgauge : ∀ (g : TorusSite n → UnitQuaternion) (W : TorusField n), IsCold σ W →
      G (gaugeTransform g W) = G W)
    (lam : TorusSite n → imaginaryQuaternions) (w : LinkLogs n) :
    ∀ᶠ p in 𝓝 ((0 : ℝ), (0 : ℝ)), onLogs G (gaugeFamily lam w p) = onLogs G (p.2 • w) := by
  have hsw : Tendsto (fun p : ℝ × ℝ => p.2 • w) (𝓝 (0, 0)) (𝓝 (0 : LinkLogs n)) := by
    have : Continuous fun p : ℝ × ℝ => p.2 • w := by fun_prop
    simpa using this.tendsto (0, 0)
  filter_upwards [expUnit_gaugeFamily lam w, hsw.eventually (eventually_isCold_fieldOfLogs hσ)]
    with p hp hcold
  have hfield : fieldOfLogs (gaugeFamily lam w p) =
      gaugeTransform (fun x => expUnit (p.1 • lam x)) (fieldOfLogs (p.2 • w)) := by
    funext x i
    simp only [fieldOfLogs, gaugeTransform, hp (x, i), gaugeCurve, Pi.smul_apply]
  simp only [onLogs]
  rw [hfield, hgauge _ _ hcold]
theorem fderiv_gaugeFamily_fst (lam : TorusSite n → imaginaryQuaternions) (w : LinkLogs n) :
    fderiv ℝ (gaugeFamily lam w) (0, 0) (1, 0) = fun b => lam b.1 - lam (b.1 + unitStep n b.2) := by
  have hdiff : DifferentiableAt ℝ (gaugeFamily lam w) ((0 : ℝ), (0 : ℝ)) :=
    (contDiffAt_gaugeFamily lam w).differentiableAt (by simp)
  have hcurve : HasDerivAt (fun τ : ℝ => (τ, (0 : ℝ))) ((1 : ℝ), (0 : ℝ)) 0 :=
    (hasDerivAt_id (0 : ℝ)).prodMk (hasDerivAt_const (0 : ℝ) (0 : ℝ))
  have h1 : HasDerivAt (fun τ : ℝ => gaugeFamily lam w (τ, 0))
      (fderiv ℝ (gaugeFamily lam w) (0, 0) (1, 0)) 0 :=
    HasFDerivAt.comp_hasDerivAt (f := fun τ : ℝ => (τ, (0 : ℝ))) (0 : ℝ) hdiff.hasFDerivAt hcurve
  have h2 : HasDerivAt (fun τ : ℝ => gaugeFamily lam w (τ, 0))
      (fun b => lam b.1 - lam (b.1 + unitStep n b.2)) 0 := by
    refine hasDerivAt_pi.mpr fun b => ?_
    have hm : HasDerivAt (fun τ : ℝ => ((gaugeCurve lam w b (τ, 0) : UnitQuaternion) : ℍ[ℝ]))
        ((lam b.1 : ℍ[ℝ]) - (lam (b.1 + unitStep n b.2) : ℍ[ℝ])) 0 := by
      have ha : HasDerivAt (fun τ : ℝ => quatExp (τ • (lam b.1 : ℍ[ℝ]))) (lam b.1 : ℍ[ℝ]) 0 := by
        have := hasDerivAt_exp_smul_const (𝕂 := ℝ) (lam b.1 : ℍ[ℝ]) (0 : ℝ)
        rw [zero_smul, NormedSpace.exp_zero, one_mul] at this
        exact this
      have hb : HasDerivAt (fun τ : ℝ => quatExp (-(τ • (lam (b.1 + unitStep n b.2) : ℍ[ℝ]))))
          (-(lam (b.1 + unitStep n b.2) : ℍ[ℝ])) 0 := by
        have := hasDerivAt_exp_smul_const (𝕂 := ℝ) (-(lam (b.1 + unitStep n b.2) : ℍ[ℝ])) (0 : ℝ)
        rw [zero_smul, NormedSpace.exp_zero, one_mul] at this
        have heq : (fun τ : ℝ => quatExp (-(τ • (lam (b.1 + unitStep n b.2) : ℍ[ℝ])))) =
            fun τ : ℝ => NormedSpace.exp (τ • (-(lam (b.1 + unitStep n b.2) : ℍ[ℝ]))) := by
          funext τ
          rw [smul_neg]
          rfl
        rw [heq]
        exact this
      have h := ha.mul hb
      have hfun : (fun τ : ℝ => ((gaugeCurve lam w b (τ, 0) : UnitQuaternion) : ℍ[ℝ])) =
          (fun τ : ℝ => quatExp (τ • (lam b.1 : ℍ[ℝ]))) *
            fun τ : ℝ => quatExp (-(τ • (lam (b.1 + unitStep n b.2) : ℍ[ℝ]))) := by
        funext τ
        rw [coe_gaugeCurve]
        simp [quatExp_zero]
      have e : (lam b.1 : ℍ[ℝ]) * quatExp (-((0 : ℝ) • (lam (b.1 + unitStep n b.2) : ℍ[ℝ]))) +
          quatExp ((0 : ℝ) • (lam b.1 : ℍ[ℝ])) * (-(lam (b.1 + unitStep n b.2) : ℍ[ℝ])) =
          (lam b.1 : ℍ[ℝ]) - (lam (b.1 + unitStep n b.2) : ℍ[ℝ]) := by
        simp [quatExp_zero, sub_eq_add_neg]
      rw [e] at h
      rw [hfun]
      exact h
    have hl : HasFDerivAt unitLog imPart ((gaugeCurve lam w b (0, 0) : UnitQuaternion) : ℍ[ℝ]) := by
      rw [gaugeCurve_zero]
      exact hasFDerivAt_unitLog
    have h := hl.comp_hasDerivAt (0 : ℝ) hm
    rw [← Submodule.coe_sub, imPart_coe] at h
    exact h
  funext b
  exact congrFun (h1.unique h2) b
theorem fderiv_fderiv_onLogs_gauge_direction {G : TorusField n → ℝ} {σ : ℝ} (hσ : 0 < σ)
    (hG : ContDiffThreeAt G (trivialField n))
    (hgauge : ∀ (g : TorusSite n → UnitQuaternion) (W : TorusField n), IsCold σ W →
      G (gaugeTransform g W) = G W)
    (hd : fderiv ℝ (onLogs G) 0 = 0) (lam : TorusSite n → imaginaryQuaternions) (w : LinkLogs n) :
    fderiv ℝ (fderiv ℝ (onLogs G)) 0 w (fun b => lam b.1 - lam (b.1 + unitStep n b.2)) = 0 := by
  have h := fderiv_fderiv_apply_eq_zero_of_invariant (contDiffAt_onLogs hG) hd
    (contDiffAt_gaugeFamily lam w) w
    (gaugeFamily_zero_fst lam w) (onLogs_gaugeFamily hσ hgauge lam w)
  rwa [fderiv_gaugeFamily_fst] at h
end Gauge
section First
variable {n : ℕ} [NeZero n]
theorem singleLink_add (b : TorusBond n) (X Y : imaginaryQuaternions) :
    singleLink b (X + Y) = singleLink b X + singleLink b Y := by
  simp [singleLink, Pi.single_add]
theorem singleLink_smul (b : TorusBond n) (r : ℝ) (X : imaginaryQuaternions) :
    singleLink b (r • X) = r • singleLink b X := by
  simp [singleLink, Pi.single_smul]
theorem conj_expUnit_of_anticomm (g : UnitQuaternion) (Y : imaginaryQuaternions)
    (h : ((g : UnitQuaternion) : ℍ[ℝ]) * (Y : ℍ[ℝ]) = -((Y : ℍ[ℝ]) * (g : ℍ[ℝ]))) :
    g * expUnit Y * g⁻¹ = expUnit (-Y) := by
  have hneg : (-(Y : ℍ[ℝ])).re = 0 := by
    have h0 : (Y : ℍ[ℝ]).re = 0 := Y.2
    simp [h0]
  have hcomm : ((g : UnitQuaternion) : ℍ[ℝ]) * quatExp (Y : ℍ[ℝ]) =
      quatExp (-(Y : ℍ[ℝ])) * (g : ℍ[ℝ]) := by
    simp only [quatExp]
    rw [Quaternion.exp_of_re_eq_zero _ Y.2, Quaternion.exp_of_re_eq_zero _ hneg, norm_neg, mul_add,
      add_mul, Quaternion.mul_coe_eq_smul, Quaternion.coe_mul_eq_smul, mul_smul_comm, h,
      smul_mul_assoc, neg_mul]
  apply Subtype.ext
  have hstar : ((g : UnitQuaternion) : ℍ[ℝ]) * star (g : ℍ[ℝ]) = 1 :=
    Unitary.mul_star_self_of_mem g.2
  change ((g : UnitQuaternion) : ℍ[ℝ]) * quatExp (Y : ℍ[ℝ]) * star (g : ℍ[ℝ]) =
    quatExp (-(Y : ℍ[ℝ]))
  rw [hcomm, mul_assoc, hstar, mul_one]
theorem fderiv_onLogs_singleLink_of_anticomm {G : TorusField n → ℝ} {σ : ℝ} (hσ : 0 < σ)
    (hG : ContDiffThreeAt G (trivialField n))
    (hgauge : ∀ (g : TorusSite n → UnitQuaternion) (W : TorusField n), IsCold σ W →
      G (gaugeTransform g W) = G W)
    (X : imaginaryQuaternions) (g : UnitQuaternion)
    (hconj : ((g : UnitQuaternion) : ℍ[ℝ]) * (X : ℍ[ℝ]) = -((X : ℍ[ℝ]) * (g : ℍ[ℝ])))
    (b : TorusBond n) : fderiv ℝ (onLogs G) 0 (singleLink b X) = 0 := by
  set v := singleLink b X with hv
  have hflip : ∀ s : ℝ, gaugeTransform (fun _ => g) (fieldOfLogs (s • v)) =
      fieldOfLogs ((-s) • v) := by
    intro s
    funext x i
    simp only [gaugeTransform, fieldOfLogs]
    by_cases hb : (x, i) = b
    · have h1 : (s • v) (x, i) = s • X := by simp [hv, singleLink, hb]
      have h2 : ((-s) • v) (x, i) = -(s • X) := by
        rw [Pi.smul_apply, hv, singleLink, hb, Pi.single_eq_same]
        exact neg_smul s X
      rw [h1, h2]
      refine conj_expUnit_of_anticomm g (s • X) ?_
      simp only [Submodule.coe_smul, mul_smul_comm, smul_mul_assoc, hconj, smul_neg]
    · have h1 : (s • v) (x, i) = 0 := by simp [hv, singleLink, Pi.single_eq_of_ne hb]
      have h2 : ((-s) • v) (x, i) = 0 := by simp [hv, singleLink, Pi.single_eq_of_ne hb]
      rw [h1, h2, expUnit_zero]
      simp
  have hsv : Tendsto (fun s : ℝ => s • v) (𝓝 0) (𝓝 (0 : LinkLogs n)) := by
    have : Continuous fun s : ℝ => s • v := by fun_prop
    simpa using this.tendsto 0
  have heven : (fun s : ℝ => onLogs G (s • v)) =ᶠ[𝓝 0] fun s => onLogs G ((-s) • v) := by
    filter_upwards [hsv.eventually (eventually_isCold_fieldOfLogs hσ)] with s hs
    simp only [onLogs]
    rw [← hflip s, hgauge _ _ hs]
  have hdiff : HasFDerivAt (onLogs G) (fderiv ℝ (onLogs G) 0) ((0 : ℝ) • v) := by
    rw [zero_smul]
    exact ((contDiffAt_onLogs hG).differentiableAt (by simp)).hasFDerivAt
  have hdiff' : HasFDerivAt (onLogs G) (fderiv ℝ (onLogs G) 0) ((-(0 : ℝ)) • v) := by
    rw [neg_zero]
    exact hdiff
  have h1 : HasDerivAt (fun s : ℝ => onLogs G (s • v)) (fderiv ℝ (onLogs G) 0 v) 0 := by
    have hl : HasDerivAt (fun s : ℝ => s • v) v 0 := by
      simpa using (hasDerivAt_id (0 : ℝ)).smul_const v
    exact hdiff.comp_hasDerivAt (0 : ℝ) hl
  have h2 : HasDerivAt (fun s : ℝ => onLogs G ((-s) • v)) (fderiv ℝ (onLogs G) 0 (-v)) 0 := by
    have hl : HasDerivAt (fun s : ℝ => (-s) • v) (-v) 0 := by
      have h := (hasDerivAt_neg (0 : ℝ)).smul_const v
      rwa [neg_smul, one_smul] at h
    exact hdiff'.comp_hasDerivAt (0 : ℝ) hl
  have h3 := (h1.congr_of_eventuallyEq heven.symm).unique h2
  rw [map_neg] at h3
  linarith
def quatMk (a b c d : ℝ) : ℍ[ℝ] := ⟨a, b, c, d⟩
@[simp] theorem quatMk_re (a b c d : ℝ) : (quatMk a b c d).re = a := rfl
@[simp] theorem quatMk_imI (a b c d : ℝ) : (quatMk a b c d).imI = b := rfl
@[simp] theorem quatMk_imJ (a b c d : ℝ) : (quatMk a b c d).imJ = c := rfl
@[simp] theorem quatMk_imK (a b c d : ℝ) : (quatMk a b c d).imK = d := rfl
def unitQuatI : UnitQuaternion := ⟨quatMk 0 1 0 0, by
  rw [Unitary.mem_iff]; constructor <;> ext <;> simp⟩
def unitQuatJ : UnitQuaternion := ⟨quatMk 0 0 1 0, by
  rw [Unitary.mem_iff]; constructor <;> ext <;> simp⟩
def unitQuatK : UnitQuaternion := ⟨quatMk 0 0 0 1, by
  rw [Unitary.mem_iff]; constructor <;> ext <;> simp⟩
def imaginaryI : imaginaryQuaternions := ⟨quatMk 0 1 0 0, rfl⟩
def imaginaryJ : imaginaryQuaternions := ⟨quatMk 0 0 1 0, rfl⟩
def imaginaryK : imaginaryQuaternions := ⟨quatMk 0 0 0 1, rfl⟩
theorem imaginary_decomp (X : imaginaryQuaternions) :
    X = (X : ℍ[ℝ]).imI • imaginaryI + (X : ℍ[ℝ]).imJ • imaginaryJ + (X : ℍ[ℝ]).imK • imaginaryK := by
  apply Subtype.ext
  have h0 : (X : ℍ[ℝ]).re = 0 := X.2
  ext <;> simp [imaginaryI, imaginaryJ, imaginaryK, h0]
theorem fderiv_onLogs_eq_zero {G : TorusField n → ℝ} {σ : ℝ} (hσ : 0 < σ)
    (hG : ContDiffThreeAt G (trivialField n))
    (hgauge : ∀ (g : TorusSite n → UnitQuaternion) (W : TorusField n), IsCold σ W →
      G (gaugeTransform g W) = G W) :
    fderiv ℝ (onLogs G) 0 = 0 := by
  have hI : ∀ b : TorusBond n, fderiv ℝ (onLogs G) 0 (singleLink b imaginaryI) = 0 := fun b =>
    fderiv_onLogs_singleLink_of_anticomm hσ hG hgauge imaginaryI unitQuatJ
      (by ext <;> simp [imaginaryI, unitQuatJ]) b
  have hJ : ∀ b : TorusBond n, fderiv ℝ (onLogs G) 0 (singleLink b imaginaryJ) = 0 := fun b =>
    fderiv_onLogs_singleLink_of_anticomm hσ hG hgauge imaginaryJ unitQuatK
      (by ext <;> simp [imaginaryJ, unitQuatK]) b
  have hK : ∀ b : TorusBond n, fderiv ℝ (onLogs G) 0 (singleLink b imaginaryK) = 0 := fun b =>
    fderiv_onLogs_singleLink_of_anticomm hσ hG hgauge imaginaryK unitQuatI
      (by ext <;> simp [imaginaryK, unitQuatI]) b
  have hall : ∀ (b : TorusBond n) (X : imaginaryQuaternions),
      fderiv ℝ (onLogs G) 0 (singleLink b X) = 0 := by
    intro b X
    rw [imaginary_decomp X, singleLink_add, singleLink_add, singleLink_smul, singleLink_smul,
      singleLink_smul, map_add, map_add, map_smul, map_smul, map_smul, hI, hJ, hK]
    simp
  ext v
  have hv : v = ∑ b, singleLink b (v b) := (Finset.univ_sum_single v).symm
  rw [hv, map_sum]
  simp [hall]
end First
section Sums
def supNormInt (h : Fin 4 → ℤ) : ℕ := Finset.univ.sup fun i => (h i).natAbs
theorem natAbs_le_supNormInt (h : Fin 4 → ℤ) (i : Fin 4) : (h i).natAbs ≤ supNormInt h := by apply _root_.YangMills.Construction.LatticePaths.natAbs_le_supNorm <;> assumption
theorem abs_le_supNormInt (h : Fin 4 → ℤ) (i : Fin 4) : |((h i : ℤ) : ℝ)| ≤ supNormInt h := by apply _root_.YangMills.Construction.BlockAverages.abs_coord_le_supNorm <;> assumption
theorem supNormInt_add_single_le (h : Fin 4 → ℤ) (i : Fin 4) :
    supNormInt (h + Pi.single i 1) ≤ supNormInt h + 1 := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.NearUniformTop.offsetSupNorm_add_single_le <;> assumption
theorem summable_prod_pow_natAbs {r : ℝ} (h0 : 0 ≤ r) (h1 : r < 1) :
    Summable fun h : Fin 4 → ℤ => ∏ i, r ^ (h i).natAbs := by apply _root_.YangMills.Construction.RunningCouplingSlope.LocalDensityCoefficient.summable_prod_pow_natAbs <;> assumption
def decayWeight (c : ℝ) (h : Fin 4 → ℤ) : ℝ :=
  Real.exp (-(c * supNormInt h)) * (1 + (supNormInt h : ℝ)) ^ 2
theorem decayWeight_nonneg (c : ℝ) (h : Fin 4 → ℤ) : 0 ≤ decayWeight c h := by
  unfold decayWeight
  positivity
theorem summable_decayWeight {c : ℝ} (hc : 0 < c) : Summable (decayWeight c) := by apply _root_.YangMills.Construction.SummableBounds.MeanHessian.summable_exp_mul_sq <;> assumption
abbrev LatticeBond : Type := (Fin 4 → ℤ) × Fin 4
def bondWeight (c : ℝ) (b : _root_.YangMills.Construction.ColdStepAtMirrorFrames.SecondVariation.LatticeBond) : ℝ := decayWeight c b.1
theorem summable_bondWeight {c : ℝ} (hc : 0 < c) : Summable (bondWeight c) := by apply _root_.YangMills.Construction.SummableBounds.MeanHessian.summable_bondWeight <;> assumption
theorem bondWeight_nonneg (c : ℝ) (b : _root_.YangMills.Construction.ColdStepAtMirrorFrames.SecondVariation.LatticeBond) : 0 ≤ bondWeight c b := by apply _root_.YangMills.Construction.SummableBounds.MeanHessian.bondWeight_nonneg <;> assumption
def QuadGrowth (B : _root_.YangMills.Construction.ColdStepAtMirrorFrames.SecondVariation.LatticeBond → imaginaryQuaternions) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ b, ‖B b‖ ≤ C * (1 + (supNormInt b.1 : ℝ)) ^ 2
def QuadGrowthSite (φ : (Fin 4 → ℤ) → imaginaryQuaternions) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ h, ‖φ h‖ ≤ C * (1 + (supNormInt h : ℝ)) ^ 2
theorem QuadGrowthSite.add {φ ψ : (Fin 4 → ℤ) → imaginaryQuaternions} (h1 : QuadGrowthSite φ)
    (h2 : QuadGrowthSite ψ) : QuadGrowthSite fun h => φ h + ψ h := by
  obtain ⟨C, hC, h⟩ := h1
  obtain ⟨C', hC', h'⟩ := h2
  refine ⟨C + C', add_nonneg hC hC', fun x => ?_⟩
  calc ‖φ x + ψ x‖ ≤ ‖φ x‖ + ‖ψ x‖ := norm_add_le _ _
    _ ≤ _ := by
      rw [add_mul]
      exact add_le_add (h x) (h' x)
theorem QuadGrowthSite.smul {φ : (Fin 4 → ℤ) → imaginaryQuaternions} (r : ℝ)
    (h1 : QuadGrowthSite φ) : QuadGrowthSite fun h => r • φ h := by
  obtain ⟨C, hC, h⟩ := h1
  refine ⟨|r| * C, by positivity, fun x => ?_⟩
  rw [norm_smul, Real.norm_eq_abs, mul_assoc]
  exact mul_le_mul_of_nonneg_left (h x) (abs_nonneg r)
theorem QuadGrowthSite.sum {ι : Type*} (s : Finset ι) {φ : ι → (Fin 4 → ℤ) → imaginaryQuaternions}
    (h1 : ∀ i ∈ s, QuadGrowthSite (φ i)) : QuadGrowthSite fun h => ∑ i ∈ s, φ i h := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨0, le_rfl, fun h => by simp⟩
  | insert a s ha ih =>
    have := (h1 a (Finset.mem_insert_self a s)).add
      (ih fun i hi => h1 i (Finset.mem_insert_of_mem hi))
    simpa [Finset.sum_insert ha] using this
theorem quadGrowthSite_quadratic (μ ν : Fin 4) (S : imaginaryQuaternions) :
    QuadGrowthSite fun h => (((h μ : ℤ) : ℝ) * ((h ν : ℤ) : ℝ)) • S := by
  refine ⟨‖S‖, norm_nonneg S, fun h => ?_⟩
  rw [norm_smul, Real.norm_eq_abs, abs_mul, mul_comm]
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg S)
  have h1 := abs_le_supNormInt h μ
  have h2 := abs_le_supNormInt h ν
  have h3 : (0 : ℝ) ≤ supNormInt h := Nat.cast_nonneg _
  calc |((h μ : ℤ) : ℝ)| * |((h ν : ℤ) : ℝ)| ≤ (supNormInt h : ℝ) * supNormInt h :=
        mul_le_mul h1 h2 (abs_nonneg _) h3
    _ ≤ _ := by nlinarith
theorem quadGrowthSite_linear (μ : Fin 4) (S : imaginaryQuaternions) :
    QuadGrowthSite fun h => ((h μ : ℤ) : ℝ) • S := by
  refine ⟨‖S‖, norm_nonneg S, fun h => ?_⟩
  rw [norm_smul, Real.norm_eq_abs, mul_comm]
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg S)
  have h1 := abs_le_supNormInt h μ
  nlinarith
theorem quadGrowth_shift {φ : (Fin 4 → ℤ) → imaginaryQuaternions} (h1 : QuadGrowthSite φ) :
    QuadGrowth fun b => φ (b.1 + Pi.single b.2 1) := by
  obtain ⟨C, hC, h⟩ := h1
  refine ⟨4 * C, by positivity, fun b => (h _).trans ?_⟩
  have h2 : ((supNormInt (b.1 + Pi.single b.2 1) : ℕ) : ℝ) ≤ supNormInt b.1 + 1 := by
    exact_mod_cast supNormInt_add_single_le b.1 b.2
  have h4 : (1 + ((supNormInt (b.1 + Pi.single b.2 1) : ℕ) : ℝ)) ^ 2 ≤
      4 * (1 + (supNormInt b.1 : ℝ)) ^ 2 := by
    nlinarith
  nlinarith
theorem quadGrowth_base {φ : (Fin 4 → ℤ) → imaginaryQuaternions} (h1 : QuadGrowthSite φ) :
    QuadGrowth fun b => φ b.1 := by
  obtain ⟨C, hC, h⟩ := h1
  exact ⟨C, hC, fun b => h b.1⟩
theorem QuadGrowth.sub {B B' : _root_.YangMills.Construction.ColdStepAtMirrorFrames.SecondVariation.LatticeBond → imaginaryQuaternions} (h1 : QuadGrowth B)
    (h2 : QuadGrowth B') : QuadGrowth fun b => B b - B' b := by
  obtain ⟨C, hC, h⟩ := h1
  obtain ⟨C', hC', h'⟩ := h2
  refine ⟨C + C', add_nonneg hC hC', fun x => ?_⟩
  calc ‖B x - B' x‖ ≤ ‖B x‖ + ‖B' x‖ := norm_sub_le _ _
    _ ≤ _ := by
      rw [add_mul]
      exact add_le_add (h x) (h' x)
theorem quadGrowth_linearPotential (A : Fin 4 → Fin 4 → imaginaryQuaternions) :
    QuadGrowth (linearPotential A) := by
  refine ⟨∑ ν, ∑ μ, ‖A ν μ‖, by positivity, fun b => ?_⟩
  have h3 : (0 : ℝ) ≤ supNormInt b.1 := Nat.cast_nonneg _
  unfold linearPotential
  rw [norm_smul]
  have h1 : ‖∑ ν, ((b.1 ν : ℤ) : ℝ) • A ν b.2‖ ≤ ∑ ν, (supNormInt b.1 : ℝ) * ∑ μ, ‖A ν μ‖ := by
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun ν _ => ?_)
    rw [norm_smul, Real.norm_eq_abs]
    refine mul_le_mul (abs_le_supNormInt b.1 ν) ?_ (norm_nonneg _) h3
    exact Finset.single_le_sum (f := fun μ => ‖A ν μ‖) (fun _ _ => norm_nonneg _)
      (Finset.mem_univ b.2)
  rw [← Finset.mul_sum] at h1
  have hC : 0 ≤ ∑ ν, ∑ μ, ‖A ν μ‖ := by positivity
  have h4 : ‖(1 / 2 : ℝ)‖ ≤ 1 := by norm_num
  calc ‖(1 / 2 : ℝ)‖ * ‖∑ ν, ((b.1 ν : ℤ) : ℝ) • A ν b.2‖
      ≤ 1 * ((supNormInt b.1 : ℝ) * ∑ ν, ∑ μ, ‖A ν μ‖) :=
        mul_le_mul h4 h1 (norm_nonneg _) zero_le_one
    _ ≤ _ := by
      nlinarith [mul_nonneg hC h3, mul_nonneg hC (sq_nonneg (supNormInt b.1 : ℝ))]
theorem tsum_latticeBond {g : _root_.YangMills.Construction.ColdStepAtMirrorFrames.SecondVariation.LatticeBond → ℝ} (hg : Summable g) :
    ∑' b, g b = ∑ i, ∑' h, g (h, i) := by
  have hs : Summable fun p : Fin 4 × (Fin 4 → ℤ) => g (p.2, p.1) :=
    (Equiv.prodComm _ _).summable_iff.mpr hg
  rw [← (Equiv.prodComm (Fin 4) (Fin 4 → ℤ)).tsum_eq g]
  simp only [Equiv.prodComm_apply, Prod.swap]
  rw [hs.tsum_prod, tsum_fintype]
theorem summable_latticeBond_fiber {g : _root_.YangMills.Construction.ColdStepAtMirrorFrames.SecondVariation.LatticeBond → ℝ} (hg : Summable g) (i : Fin 4) :
    Summable fun h => g (h, i) :=
  hg.comp_injective fun a b hab => (Prod.mk.inj hab).1
end Sums
section Limit
variable {ℓ : _root_.YangMills.Construction.TorusLumps.StepParameters} {t : ℕ} {x : ℝ} {D : TorusFunctional} {f : LocalDensity}
def secondDerivSeq (f : LocalDensity) (b b' : _root_.YangMills.Construction.ColdStepAtMirrorFrames.SecondVariation.LatticeBond) (X X' : imaginaryQuaternions)
    (n : ℕ) : ℝ :=
  mixedDeriv (f n 0) (trivialField n) ![bondFrom 0 b, bondFrom 0 b'] ![X, X']
theorem isCold_trivialField {σ : ℝ} (hσ : 0 < σ) (n : ℕ) : IsCold σ (trivialField n) := by apply _root_.YangMills.SharedProofs.p4747 <;> assumption
theorem secondDerivSeq_eq (hF : ℓ.Admissible) (hR : ColdExpansion ℓ t x D f) {n : ℕ} [NeZero n]
    (hn : ℓ.n₀ ≤ n) (b b' : _root_.YangMills.Construction.ColdStepAtMirrorFrames.SecondVariation.LatticeBond) (X X' : imaginaryQuaternions) :
    secondDerivSeq f b b' X X' n =
      fderiv ℝ (fderiv ℝ (onLogs (f n 0))) 0 (singleLink (bondFrom 0 b) X)
        (singleLink (bondFrom 0 b') X') := by
  unfold secondDerivSeq
  rw [mixedDeriv_two_eq (hR.smooth n hn 0 _ (isCold_trivialField hF.σ_pos n))]
  rfl
theorem eventually_admissible_side (hF : ℓ.Admissible) :
    ∀ᶠ n : ℕ in atTop, ℓ.n₀ ≤ n ∧ 0 < n := by
  filter_upwards [eventually_ge_atTop ℓ.n₀] with n hn
  have := hF.n₀_ge
  exact ⟨hn, by omega⟩
theorem weightRate_pos (hF : ℓ.Admissible) : 0 < ℓ.weightRate := by apply _root_.YangMills.Construction.AbelianSecondOrder.weightRate_pos <;> assumption
theorem exp_le_weight (m : ℕ) : Real.exp (ℓ.weightRate * m) ≤ ℓ.weight m := by apply _root_.YangMills.SharedProofs.p47115 <;> assumption
theorem div_weight_le (hF : ℓ.Admissible) (m : ℕ) :
    ℓ.E / ℓ.weight m ≤ ℓ.E * Real.exp (-(ℓ.weightRate * m)) := by
  have h1 := exp_le_weight (ℓ := ℓ) m
  have h2 : 0 < Real.exp (ℓ.weightRate * m) := Real.exp_pos _
  rw [Real.exp_neg, ← div_eq_mul_inv]
  exact div_le_div_of_nonneg_left hF.E_pos.le h2 h1
theorem bondOffsetInBox_of_supNormInt (b : _root_.YangMills.Construction.ColdStepAtMirrorFrames.SecondVariation.LatticeBond) {m : ℕ} (hm : supNormInt b.1 + 1 ≤ m) :
    BondOffsetInBox m b := by apply _root_.YangMills.DeltaSharedProofs.p501634 <;> assumption
theorem mixedDeriv_centered {n k : ℕ} (hk : k = 2) (y : TorusSite n) (W : TorusField n)
    (c : Fin k → TorusBond n) (X : Fin k → imaginaryQuaternions) :
    mixedDeriv (centered f n y) W c X = mixedDeriv (f n y) W c X := by
  subst hk
  unfold mixedDeriv centered
  simp only [iteratedFDeriv_two_apply]
  have h : (fun z => fderiv ℝ (fun σ : Fin 2 → ℝ =>
      f n y (perturb c X σ W) - f n y (trivialField n)) z) =
      fun z => fderiv ℝ (fun σ : Fin 2 → ℝ => f n y (perturb c X σ W)) z := by
    funext z
    exact fderiv_sub_const _
  rw [show fderiv ℝ (fun σ : Fin 2 → ℝ => f n y (perturb c X σ W) - f n y (trivialField n)) =
    fderiv ℝ (fun σ : Fin 2 → ℝ => f n y (perturb c X σ W)) from h]
theorem cauchySeq_secondDerivSeq (hF : ℓ.Admissible) (hR : ColdExpansion ℓ t x D f)
    (b b' : _root_.YangMills.Construction.ColdStepAtMirrorFrames.SecondVariation.LatticeBond) {X X' : imaginaryQuaternions}
    (hX : ‖X‖ = 1) (hX' : ‖X'‖ = 1) : CauchySeq (secondDerivSeq f b b' X X') := by
  rw [Metric.cauchySeq_iff]
  intro ε hε
  have hdec : Tendsto (fun m : ℕ => ℓ.E * Real.exp (-(ℓ.weightRate * m))) atTop (𝓝 0) := by
    have h1 : Tendsto (fun m : ℕ => ℓ.weightRate * (m : ℝ)) atTop atTop :=
      tendsto_natCast_atTop_atTop.const_mul_atTop (weightRate_pos hF)
    have h2 := (Real.tendsto_exp_neg_atTop_nhds_zero.comp h1).const_mul ℓ.E
    simpa using h2
  obtain ⟨m, hm1, hm2⟩ := ((hdec.eventually (gt_mem_nhds hε)).and
    (eventually_ge_atTop (supNormInt b.1 + supNormInt b'.1 + 1))).exists
  refine ⟨max ℓ.n₀ (2 * m + 3), fun n hn n' hn' => ?_⟩
  have hn0 : ℓ.n₀ ≤ n := le_trans (le_max_left _ _) hn
  have hn0' : ℓ.n₀ ≤ n' := le_trans (le_max_left _ _) hn'
  have hn1 : 2 * m + 3 ≤ n := le_trans (le_max_right _ _) hn
  have hn1' : 2 * m + 3 ≤ n' := le_trans (le_max_right _ _) hn'
  haveI : NeZero n := ⟨by omega⟩
  haveI : NeZero n' := ⟨by omega⟩
  have hagree : FieldsAgreeNear (trivialField n) (trivialField n') (0 : TorusSite n)
      (0 : TorusSite n') m := fun _ _ => rfl
  have hbox : ∀ l, BondOffsetInBox m ((![b, b'] : Fin 2 → _root_.YangMills.Construction.ColdStepAtMirrorFrames.SecondVariation.LatticeBond) l) := by
    intro l
    fin_cases l
    · exact bondOffsetInBox_of_supNormInt b (show supNormInt b.1 + 1 ≤ m by omega)
    · exact bondOffsetInBox_of_supNormInt b' (show supNormInt b'.1 + 1 ≤ m by omega)
  have hun : AreUnitVectors (![X, X'] : Fin 2 → imaginaryQuaternions) := by
    intro l
    fin_cases l
    · simpa using hX
    · simpa using hX'
  have h := hR.local_density n n' hn0 hn0' 0 0 (trivialField n) (trivialField n') m (by omega)
    (by omega) (isCold_trivialField hF.σ_pos n) (isCold_trivialField hF.σ_pos n') hagree 2
    ![b, b'] ![X, X'] le_rfl hbox hun
  rw [mixedDeriv_centered rfl, mixedDeriv_centered rfl] at h
  have hc : ∀ k : ℕ, (fun l => bondFrom (0 : TorusSite k) ((![b, b'] : Fin 2 → _root_.YangMills.Construction.ColdStepAtMirrorFrames.SecondVariation.LatticeBond) l)) =
      ![bondFrom 0 b, bondFrom 0 b'] := by
    intro k
    funext l
    fin_cases l <;> rfl
  rw [hc, hc] at h
  rw [Real.dist_eq]
  exact lt_of_le_of_lt (h.trans (div_weight_le hF m)) hm1
theorem secondDerivSeq_zero_left (hF : ℓ.Admissible) (hR : ColdExpansion ℓ t x D f)
    (b b' : _root_.YangMills.Construction.ColdStepAtMirrorFrames.SecondVariation.LatticeBond) (X' : imaginaryQuaternions) :
    ∀ᶠ n in atTop, secondDerivSeq f b b' 0 X' n = 0 := by
  filter_upwards [eventually_admissible_side hF] with n hn
  haveI : NeZero n := ⟨hn.2.ne'⟩
  rw [secondDerivSeq_eq hF hR hn.1,
    show singleLink (bondFrom 0 b) (0 : imaginaryQuaternions) = 0 from Pi.single_zero _]
  simp
theorem secondDerivSeq_zero_right (hF : ℓ.Admissible) (hR : ColdExpansion ℓ t x D f)
    (b b' : _root_.YangMills.Construction.ColdStepAtMirrorFrames.SecondVariation.LatticeBond) (X : imaginaryQuaternions) :
    ∀ᶠ n in atTop, secondDerivSeq f b b' X 0 n = 0 := by
  filter_upwards [eventually_admissible_side hF] with n hn
  haveI : NeZero n := ⟨hn.2.ne'⟩
  rw [secondDerivSeq_eq hF hR hn.1,
    show singleLink (bondFrom 0 b') (0 : imaginaryQuaternions) = 0 from Pi.single_zero _]
  simp
theorem secondDerivSeq_smul (hF : ℓ.Admissible) (hR : ColdExpansion ℓ t x D f)
    (b b' : _root_.YangMills.Construction.ColdStepAtMirrorFrames.SecondVariation.LatticeBond) (r r' : ℝ) (X X' : imaginaryQuaternions) :
    ∀ᶠ n in atTop, secondDerivSeq f b b' (r • X) (r' • X') n =
      r * r' * secondDerivSeq f b b' X X' n := by
  filter_upwards [eventually_admissible_side hF] with n hn
  haveI : NeZero n := ⟨hn.2.ne'⟩
  rw [secondDerivSeq_eq hF hR hn.1, secondDerivSeq_eq hF hR hn.1, singleLink_smul, singleLink_smul]
  simp only [map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul]
  ring
theorem secondDerivSeq_add (hF : ℓ.Admissible) (hR : ColdExpansion ℓ t x D f)
    (b b' : _root_.YangMills.Construction.ColdStepAtMirrorFrames.SecondVariation.LatticeBond) (X₁ X₂ X' : imaginaryQuaternions) :
    ∀ᶠ n in atTop, secondDerivSeq f b b' (X₁ + X₂) X' n =
      secondDerivSeq f b b' X₁ X' n + secondDerivSeq f b b' X₂ X' n := by
  filter_upwards [eventually_admissible_side hF] with n hn
  haveI : NeZero n := ⟨hn.2.ne'⟩
  rw [secondDerivSeq_eq hF hR hn.1, secondDerivSeq_eq hF hR hn.1, secondDerivSeq_eq hF hR hn.1,
    singleLink_add]
  simp only [map_add, ContinuousLinearMap.add_apply]
theorem secondDerivSeq_symm (hF : ℓ.Admissible) (hR : ColdExpansion ℓ t x D f)
    (b b' : _root_.YangMills.Construction.ColdStepAtMirrorFrames.SecondVariation.LatticeBond) (X X' : imaginaryQuaternions) :
    ∀ᶠ n in atTop, secondDerivSeq f b b' X X' n = secondDerivSeq f b' b X' X n := by
  filter_upwards [eventually_admissible_side hF] with n hn
  haveI : NeZero n := ⟨hn.2.ne'⟩
  rw [secondDerivSeq_eq hF hR hn.1, secondDerivSeq_eq hF hR hn.1]
  have hs := (contDiffAt_onLogs (hR.smooth n hn.1 0 _
    (isCold_trivialField hF.σ_pos n))).isSymmSndFDerivAt (by simp; norm_num)
  exact hs _ _
theorem secondDerivSeq_converges (hF : ℓ.Admissible) (hR : ColdExpansion ℓ t x D f)
    (b b' : _root_.YangMills.Construction.ColdStepAtMirrorFrames.SecondVariation.LatticeBond) (X X' : imaginaryQuaternions) :
    ∃ a, Tendsto (secondDerivSeq f b b' X X') atTop (𝓝 a) := by
  by_cases hX : X = 0
  · subst hX
    exact ⟨0, tendsto_const_nhds.congr'
      ((secondDerivSeq_zero_left hF hR b b' X').mono fun _ h => h.symm)⟩
  by_cases hX' : X' = 0
  · subst hX'
    exact ⟨0, tendsto_const_nhds.congr'
      ((secondDerivSeq_zero_right hF hR b b' X).mono fun _ h => h.symm)⟩
  have hn : ‖X‖ ≠ 0 := norm_ne_zero_iff.mpr hX
  have hn' : ‖X'‖ ≠ 0 := norm_ne_zero_iff.mpr hX'
  have hU : ‖(‖X‖⁻¹ : ℝ) • X‖ = 1 := by
    rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hn]
  have hU' : ‖(‖X'‖⁻¹ : ℝ) • X'‖ = 1 := by
    rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hn']
  obtain ⟨a, ha⟩ := cauchySeq_tendsto_of_complete (cauchySeq_secondDerivSeq hF hR b b' hU hU')
  refine ⟨‖X‖ * ‖X'‖ * a, (ha.const_mul _).congr' ?_⟩
  filter_upwards [secondDerivSeq_smul hF hR b b' ‖X‖ ‖X'‖ ((‖X‖⁻¹ : ℝ) • X)
    ((‖X'‖⁻¹ : ℝ) • X')] with n hh
  rw [smul_smul, smul_smul, mul_inv_cancel₀ hn, mul_inv_cancel₀ hn', one_smul, one_smul] at hh
  exact hh.symm
theorem tendsto_secondDerivLimit (hF : ℓ.Admissible) (hR : ColdExpansion ℓ t x D f)
    (b b' : _root_.YangMills.Construction.ColdStepAtMirrorFrames.SecondVariation.LatticeBond) (X X' : imaginaryQuaternions) :
    Tendsto (secondDerivSeq f b b' X X') atTop (𝓝 (secondDerivLimit f b b' X X')) :=
  tendsto_nhds_limUnder (secondDerivSeq_converges hF hR b b' X X')
theorem secondDerivLimit_smul (hF : ℓ.Admissible) (hR : ColdExpansion ℓ t x D f)
    (b b' : _root_.YangMills.Construction.ColdStepAtMirrorFrames.SecondVariation.LatticeBond) (r r' : ℝ) (X X' : imaginaryQuaternions) :
    secondDerivLimit f b b' (r • X) (r' • X') = r * r' * secondDerivLimit f b b' X X' :=
  tendsto_nhds_unique (tendsto_secondDerivLimit hF hR b b' _ _)
    (((tendsto_secondDerivLimit hF hR b b' X X').const_mul _).congr'
      ((secondDerivSeq_smul hF hR b b' r r' X X').mono fun _ h => h.symm))
theorem secondDerivLimit_add (hF : ℓ.Admissible) (hR : ColdExpansion ℓ t x D f)
    (b b' : _root_.YangMills.Construction.ColdStepAtMirrorFrames.SecondVariation.LatticeBond) (X₁ X₂ X' : imaginaryQuaternions) :
    secondDerivLimit f b b' (X₁ + X₂) X' =
      secondDerivLimit f b b' X₁ X' + secondDerivLimit f b b' X₂ X' :=
  tendsto_nhds_unique (tendsto_secondDerivLimit hF hR b b' _ _)
    (((tendsto_secondDerivLimit hF hR b b' X₁ X').add
      (tendsto_secondDerivLimit hF hR b b' X₂ X')).congr'
      ((secondDerivSeq_add hF hR b b' X₁ X₂ X').mono fun _ h => h.symm))
theorem secondDerivLimit_symm (hF : ℓ.Admissible) (hR : ColdExpansion ℓ t x D f)
    (b b' : _root_.YangMills.Construction.ColdStepAtMirrorFrames.SecondVariation.LatticeBond) (X X' : imaginaryQuaternions) :
    secondDerivLimit f b b' X X' = secondDerivLimit f b' b X' X :=
  tendsto_nhds_unique (tendsto_secondDerivLimit hF hR b b' _ _)
    ((tendsto_secondDerivLimit hF hR b' b X' X).congr'
      ((secondDerivSeq_symm hF hR b b' X X').mono fun _ h => h.symm))
theorem secondDerivLimit_add_right (hF : ℓ.Admissible) (hR : ColdExpansion ℓ t x D f)
    (b b' : _root_.YangMills.Construction.ColdStepAtMirrorFrames.SecondVariation.LatticeBond) (X X₁ X₂ : imaginaryQuaternions) :
    secondDerivLimit f b b' X (X₁ + X₂) =
      secondDerivLimit f b b' X X₁ + secondDerivLimit f b b' X X₂ := by
  rw [secondDerivLimit_symm hF hR b b' X, secondDerivLimit_add hF hR,
    secondDerivLimit_symm hF hR b' b X₁, secondDerivLimit_symm hF hR b' b X₂]
theorem secondDerivLimit_sub (hF : ℓ.Admissible) (hR : ColdExpansion ℓ t x D f)
    (b b' : _root_.YangMills.Construction.ColdStepAtMirrorFrames.SecondVariation.LatticeBond) (X₁ X₂ X' : imaginaryQuaternions) :
    secondDerivLimit f b b' (X₁ - X₂) X' =
      secondDerivLimit f b b' X₁ X' - secondDerivLimit f b b' X₂ X' := by
  have h := secondDerivLimit_add hF hR b b' (X₁ - X₂) X₂ X'
  rw [sub_add_cancel] at h
  linarith
theorem supDist_siteOfInt {n : ℕ} [NeZero n] (h : Fin 4 → ℤ) (hn : 2 * supNormInt h + 1 < n) :
    supDist (0 : TorusSite n) (0 + siteOfInt h) = supNormInt h := by
  unfold supDist supNormInt
  refine congrArg (fun g : Fin 4 → ℕ => Finset.univ.sup g) (funext fun i => ?_)
  have h1 := natAbs_le_supNormInt h i
  have hv : ((0 : TorusSite n) i - (0 + siteOfInt h : TorusSite n) i).valMinAbs = -(h i) := by
    rw [ZMod.valMinAbs_spec]
    refine ⟨by simp [siteOfInt], ?_⟩
    rw [Set.mem_Ioc]
    constructor <;> omega
  change ((0 : TorusSite n) i - (0 + siteOfInt h : TorusSite n) i).valMinAbs.natAbs = _
  rw [hv, Int.natAbs_neg]
theorem abs_secondDerivLimit_le_of_unit (hF : ℓ.Admissible) (hR : ColdExpansion ℓ t x D f)
    (b b' : _root_.YangMills.Construction.ColdStepAtMirrorFrames.SecondVariation.LatticeBond) {X X' : imaginaryQuaternions}
    (hX : ‖X‖ = 1) (hX' : ‖X'‖ = 1) :
    |secondDerivLimit f b b' X X'| ≤
      ℓ.E * Real.exp (-(ℓ.weightRate * ((max (supNormInt b.1) (supNormInt b'.1) : ℕ) : ℝ))) := by
  refine le_of_tendsto (tendsto_secondDerivLimit hF hR b b' X X').abs ?_
  filter_upwards [eventually_admissible_side hF,
    eventually_gt_atTop (2 * (supNormInt b.1 + supNormInt b'.1) + 1)] with n hn hbig
  haveI : NeZero n := ⟨hn.2.ne'⟩
  have hun : AreUnitVectors (![X, X'] : Fin 2 → imaginaryQuaternions) := by
    intro l
    fin_cases l
    · simpa using hX
    · simpa using hX'
  have h := hR.decay n hn.1 0 (trivialField n) (isCold_trivialField hF.σ_pos n) 2
    ![bondFrom 0 b, bondFrom 0 b'] ![X, X'] (by norm_num) (by norm_num) hun
  simp only [show ¬ (2 = 3) by norm_num, if_false] at h
  set sp := supportDiam (0 : TorusSite n) ![bondFrom 0 b, bondFrom 0 b'] with hsp
  have h1 : supNormInt b.1 ≤ sp := by
    have h2 := supDist_siteOfInt (n := n) b.1 (by omega)
    have h3 : supDist (0 : TorusSite n)
        ((![bondFrom (0 : TorusSite n) b, bondFrom 0 b'] : Fin 2 → TorusBond n) 0).1 ≤
        Finset.univ.sup fun l : Fin 2 =>
          supDist (0 : TorusSite n)
            ((![bondFrom (0 : TorusSite n) b, bondFrom 0 b'] : Fin 2 → TorusBond n) l).1 :=
      Finset.le_sup (f := fun l : Fin 2 =>
        supDist (0 : TorusSite n)
          ((![bondFrom (0 : TorusSite n) b, bondFrom 0 b'] : Fin 2 → TorusBond n) l).1)
        (Finset.mem_univ 0)
    have h4 : supNormInt b.1 ≤ Finset.univ.sup fun l : Fin 2 =>
        supDist (0 : TorusSite n)
          ((![bondFrom (0 : TorusSite n) b, bondFrom 0 b'] : Fin 2 → TorusBond n) l).1 := by
      rw [← h2]
      exact h3
    exact h4.trans (le_max_left _ _)
  have h1' : supNormInt b'.1 ≤ sp := by
    have h2 := supDist_siteOfInt (n := n) b'.1 (by omega)
    have h3 : supDist (0 : TorusSite n)
        ((![bondFrom (0 : TorusSite n) b, bondFrom 0 b'] : Fin 2 → TorusBond n) 1).1 ≤
        Finset.univ.sup fun l : Fin 2 =>
          supDist (0 : TorusSite n)
            ((![bondFrom (0 : TorusSite n) b, bondFrom 0 b'] : Fin 2 → TorusBond n) l).1 :=
      Finset.le_sup (f := fun l : Fin 2 =>
        supDist (0 : TorusSite n)
          ((![bondFrom (0 : TorusSite n) b, bondFrom 0 b'] : Fin 2 → TorusBond n) l).1)
        (Finset.mem_univ 1)
    have h4 : supNormInt b'.1 ≤ Finset.univ.sup fun l : Fin 2 =>
        supDist (0 : TorusSite n)
          ((![bondFrom (0 : TorusSite n) b, bondFrom 0 b'] : Fin 2 → TorusBond n) l).1 := by
      rw [← h2]
      exact h3
    exact h4.trans (le_max_left _ _)
  have hmax : ((max (supNormInt b.1) (supNormInt b'.1) : ℕ) : ℝ) ≤ sp := by
    exact_mod_cast max_le h1 h1'
  calc |secondDerivSeq f b b' X X' n| ≤ ℓ.E / ℓ.weight sp := h
    _ ≤ ℓ.E * Real.exp (-(ℓ.weightRate * sp)) := div_weight_le hF sp
    _ ≤ _ := by
      refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hF.E_pos.le
      have := weightRate_pos hF
      nlinarith
theorem abs_secondDerivLimit_le (hF : ℓ.Admissible) (hR : ColdExpansion ℓ t x D f)
    (b b' : _root_.YangMills.Construction.ColdStepAtMirrorFrames.SecondVariation.LatticeBond) (X X' : imaginaryQuaternions) :
    |secondDerivLimit f b b' X X'| ≤ ℓ.E * (‖X‖ * ‖X'‖) *
      (Real.exp (-(ℓ.weightRate / 2 * supNormInt b.1)) *
        Real.exp (-(ℓ.weightRate / 2 * supNormInt b'.1))) := by
  have hE := hF.E_pos
  by_cases hX : X = 0
  · subst hX
    have h := secondDerivLimit_smul hF hR b b' 0 1 0 X'
    simp only [zero_smul, one_smul, zero_mul] at h
    rw [h]
    simp
  by_cases hX' : X' = 0
  · subst hX'
    have h := secondDerivLimit_smul hF hR b b' 1 0 X 0
    simp only [zero_smul, one_smul, mul_zero, zero_mul] at h
    rw [h]
    simp
  have hn : ‖X‖ ≠ 0 := norm_ne_zero_iff.mpr hX
  have hn' : ‖X'‖ ≠ 0 := norm_ne_zero_iff.mpr hX'
  have hU : ‖(‖X‖⁻¹ : ℝ) • X‖ = 1 := by
    rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hn]
  have hU' : ‖(‖X'‖⁻¹ : ℝ) • X'‖ = 1 := by
    rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hn']
  have hs := secondDerivLimit_smul hF hR b b' ‖X‖ ‖X'‖ ((‖X‖⁻¹ : ℝ) • X) ((‖X'‖⁻¹ : ℝ) • X')
  rw [smul_smul, smul_smul, mul_inv_cancel₀ hn, mul_inv_cancel₀ hn', one_smul, one_smul] at hs
  rw [hs, abs_mul, abs_of_nonneg (by positivity : 0 ≤ ‖X‖ * ‖X'‖)]
  have hb := abs_secondDerivLimit_le_of_unit hF hR b b' hU hU'
  have hexp : Real.exp (-(ℓ.weightRate * ((max (supNormInt b.1) (supNormInt b'.1) : ℕ) : ℝ))) ≤
      Real.exp (-(ℓ.weightRate / 2 * supNormInt b.1)) *
        Real.exp (-(ℓ.weightRate / 2 * supNormInt b'.1)) := by
    rw [← Real.exp_add, Real.exp_le_exp]
    have hr := weightRate_pos hF
    have h1 : (supNormInt b.1 : ℝ) ≤ ((max (supNormInt b.1) (supNormInt b'.1) : ℕ) : ℝ) := by
      exact_mod_cast le_max_left _ _
    have h2 : (supNormInt b'.1 : ℝ) ≤ ((max (supNormInt b.1) (supNormInt b'.1) : ℕ) : ℝ) := by
      exact_mod_cast le_max_right _ _
    nlinarith
  calc ‖X‖ * ‖X'‖ * |secondDerivLimit f b b' ((‖X‖⁻¹ : ℝ) • X) ((‖X'‖⁻¹ : ℝ) • X')|
      ≤ ‖X‖ * ‖X'‖ * (ℓ.E * (Real.exp (-(ℓ.weightRate / 2 * supNormInt b.1)) *
          Real.exp (-(ℓ.weightRate / 2 * supNormInt b'.1)))) :=
        mul_le_mul_of_nonneg_left (hb.trans (mul_le_mul_of_nonneg_left hexp hE.le)) (by positivity)
    _ = _ := by ring
end Limit
section Final
variable {ℓ : _root_.YangMills.Construction.TorusLumps.StepParameters} {t : ℕ} {x : ℝ} {D : TorusFunctional} {f : LocalDensity}
theorem sum_singleLink_apply {n : ℕ} [NeZero n] (g : Fin 4 → TorusSite n) (Y : imaginaryQuaternions)
    (y : TorusSite n) (j : Fin 4) :
    (∑ i, singleLink (g i, i) Y) (y, j) = if y = g j then Y else 0 := by
  rw [Finset.sum_apply, Finset.sum_eq_single j]
  · simp only [singleLink, Pi.single_apply, Prod.mk.injEq, and_true]
  · intro i _ hne
    simp only [singleLink]
    exact Pi.single_eq_of_ne (fun h => hne (Prod.mk.inj h).2.symm) _
  · simp
theorem siteOfInt_sub_single {n : ℕ} (h : Fin 4 → ℤ) (i : Fin 4) :
    (siteOfInt (h - Pi.single i 1) : TorusSite n) = siteOfInt h - unitStep n i := by apply _root_.YangMills.DeltaSharedProofs.p500696 <;> assumption
theorem secondDerivLimit_divergence (hF : ℓ.Admissible) (hR : ColdExpansion ℓ t x D f)
    (h : Fin 4 → ℤ) (Y : imaginaryQuaternions) (b' : _root_.YangMills.Construction.ColdStepAtMirrorFrames.SecondVariation.LatticeBond) (X' : imaginaryQuaternions) :
    ∑ i, secondDerivLimit f (h, i) b' Y X' -
      ∑ i, secondDerivLimit f (h - Pi.single i 1, i) b' Y X' = 0 := by
  refine tendsto_nhds_unique ((tendsto_finset_sum _ fun i _ =>
    tendsto_secondDerivLimit hF hR (h, i) b' Y X').sub
    (tendsto_finset_sum _ fun i _ => tendsto_secondDerivLimit hF hR (h - Pi.single i 1, i) b' Y X'))
    (tendsto_const_nhds.congr' ?_)
  filter_upwards [eventually_admissible_side hF] with n hn
  haveI : NeZero n := ⟨hn.2.ne'⟩
  have hC := hR.smooth n hn.1 0 _ (isCold_trivialField hF.σ_pos n)
  have hg : ∀ (g : TorusSite n → UnitQuaternion) (W : TorusField n), IsCold ℓ.threshold W →
      f n 0 (gaugeTransform g W) = f n 0 W := fun g W hW => hR.gauge n hn.1 0 g W hW
  have hd := fderiv_onLogs_eq_zero hF.σ_pos hC hg
  have hsym := (contDiffAt_onLogs hC).isSymmSndFDerivAt (by simp; norm_num)
  set z : TorusSite n := siteOfInt h with hz
  have h0 := fderiv_fderiv_onLogs_gauge_direction hF.σ_pos hC hg hd (Pi.single z Y)
    (singleLink (bondFrom 0 b') X')
  have hdir : (fun b : TorusBond n => (Pi.single z Y : TorusSite n → imaginaryQuaternions) b.1 -
      (Pi.single z Y : TorusSite n → imaginaryQuaternions) (b.1 + unitStep n b.2)) =
      ∑ i, singleLink (z, i) Y - ∑ i, singleLink (z - unitStep n i, i) Y := by
    funext ⟨y, j⟩
    simp only [Pi.sub_apply]
    rw [sum_singleLink_apply (fun _ => z), sum_singleLink_apply (fun i => z - unitStep n i)]
    simp only [Pi.single_apply, eq_sub_iff_add_eq]
  rw [hdir, map_sub, map_sum, map_sum] at h0
  have hterm : ∀ c : TorusBond n,
      fderiv ℝ (fderiv ℝ (onLogs (f n 0))) 0 (singleLink (bondFrom 0 b') X') (singleLink c Y) =
      fderiv ℝ (fderiv ℝ (onLogs (f n 0))) 0 (singleLink c Y) (singleLink (bondFrom 0 b') X') :=
    fun c => hsym _ _
  simp only [hterm] at h0
  simp only [secondDerivSeq_eq hF hR hn.1]
  have hb1 : ∀ i, bondFrom (0 : TorusSite n) (h, i) = (z, i) := fun i => by
    simp [bondFrom, hz]
  have hb2 : ∀ i, bondFrom (0 : TorusSite n) (h - Pi.single i 1, i) = (z - unitStep n i, i) :=
    fun i => by
      simp [bondFrom, hz, siteOfInt_sub_single]
  simp only [hb1, hb2]
  exact h0.symm
theorem summable_secondDerivLimit (hF : ℓ.Admissible) (hR : ColdExpansion ℓ t x D f)
    {B : _root_.YangMills.Construction.ColdStepAtMirrorFrames.SecondVariation.LatticeBond → imaginaryQuaternions} (hB : QuadGrowth B) (b' : _root_.YangMills.Construction.ColdStepAtMirrorFrames.SecondVariation.LatticeBond)
    (X' : imaginaryQuaternions) : Summable fun b => secondDerivLimit f b b' (B b) X' := by
  obtain ⟨C, hC, hBC⟩ := hB
  have hc : 0 < ℓ.weightRate / 2 := by have := weightRate_pos hF; positivity
  refine Summable.of_norm_bounded (g := fun b => (ℓ.E * (C * ‖X'‖) *
    Real.exp (-(ℓ.weightRate / 2 * supNormInt b'.1))) * bondWeight (ℓ.weightRate / 2) b)
    ((summable_bondWeight hc).mul_left _) fun b => ?_
  rw [Real.norm_eq_abs]
  refine (abs_secondDerivLimit_le hF hR b b' _ _).trans ?_
  have hE := hF.E_pos
  have h1 := hBC b
  calc ℓ.E * (‖B b‖ * ‖X'‖) * (Real.exp (-(ℓ.weightRate / 2 * supNormInt b.1)) *
        Real.exp (-(ℓ.weightRate / 2 * supNormInt b'.1)))
      ≤ ℓ.E * ((C * (1 + (supNormInt b.1 : ℝ)) ^ 2) * ‖X'‖) *
        (Real.exp (-(ℓ.weightRate / 2 * supNormInt b.1)) *
        Real.exp (-(ℓ.weightRate / 2 * supNormInt b'.1))) := by
        refine mul_le_mul_of_nonneg_right ?_ (by positivity)
        refine mul_le_mul_of_nonneg_left ?_ hE.le
        exact mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
    _ = _ := by
        unfold bondWeight decayWeight
        ring
theorem summable_secondDerivLimit_prod (hF : ℓ.Admissible) (hR : ColdExpansion ℓ t x D f)
    {B B' : _root_.YangMills.Construction.ColdStepAtMirrorFrames.SecondVariation.LatticeBond → imaginaryQuaternions} (hB : QuadGrowth B) (hB' : QuadGrowth B') :
    Summable fun p : _root_.YangMills.Construction.ColdStepAtMirrorFrames.SecondVariation.LatticeBond × _root_.YangMills.Construction.ColdStepAtMirrorFrames.SecondVariation.LatticeBond => secondDerivLimit f p.1 p.2 (B p.1) (B' p.2) := by
  obtain ⟨C, hC, hBC⟩ := hB
  obtain ⟨C', hC', hBC'⟩ := hB'
  have hc : 0 < ℓ.weightRate / 2 := by have := weightRate_pos hF; positivity
  have hs := (Summable.mul_of_nonneg (summable_bondWeight hc) (summable_bondWeight hc)
    (bondWeight_nonneg _) (bondWeight_nonneg _)).mul_left (ℓ.E * (C * C'))
  refine Summable.of_norm_bounded hs fun p => ?_
  rw [Real.norm_eq_abs]
  refine (abs_secondDerivLimit_le hF hR p.1 p.2 _ _).trans ?_
  have hE := hF.E_pos
  have h1 := hBC p.1
  have h2 := hBC' p.2
  calc ℓ.E * (‖B p.1‖ * ‖B' p.2‖) * (Real.exp (-(ℓ.weightRate / 2 * supNormInt p.1.1)) *
        Real.exp (-(ℓ.weightRate / 2 * supNormInt p.2.1)))
      ≤ ℓ.E * ((C * (1 + (supNormInt p.1.1 : ℝ)) ^ 2) * (C' * (1 + (supNormInt p.2.1 : ℝ)) ^ 2)) *
        (Real.exp (-(ℓ.weightRate / 2 * supNormInt p.1.1)) *
          Real.exp (-(ℓ.weightRate / 2 * supNormInt p.2.1))) := by
        refine mul_le_mul_of_nonneg_right ?_ (by positivity)
        refine mul_le_mul_of_nonneg_left ?_ hE.le
        exact mul_le_mul h1 h2 (norm_nonneg _) (by positivity)
    _ = _ := by
        unfold bondWeight decayWeight
        ring
theorem tsum_secondDerivLimit_pureGauge (hF : ℓ.Admissible) (hR : ColdExpansion ℓ t x D f)
    {lam : (Fin 4 → ℤ) → imaginaryQuaternions} (hl : QuadGrowthSite lam)
    (b' : _root_.YangMills.Construction.ColdStepAtMirrorFrames.SecondVariation.LatticeBond) (X' : imaginaryQuaternions) :
    ∑' b : _root_.YangMills.Construction.ColdStepAtMirrorFrames.SecondVariation.LatticeBond, secondDerivLimit f b b' (lam (b.1 + Pi.single b.2 1) - lam b.1) X' = 0 := by
  have hA := summable_secondDerivLimit hF hR (quadGrowth_shift hl) b' X'
  have hB := summable_secondDerivLimit hF hR (quadGrowth_base hl) b' X'
  simp only [secondDerivLimit_sub hF hR]
  rw [hA.tsum_sub hB, tsum_latticeBond hA, tsum_latticeBond hB, ← Finset.sum_sub_distrib]
  set φ : Fin 4 → (Fin 4 → ℤ) → ℝ :=
    fun i h => secondDerivLimit f (h - Pi.single i 1, i) b' (lam h) X' with hφ
  set ψ : Fin 4 → (Fin 4 → ℤ) → ℝ := fun i h => secondDerivLimit f (h, i) b' (lam h) X' with hψ
  have hφs : ∀ i, Summable (φ i) := by
    intro i
    refine ((Equiv.addRight (Pi.single i 1 : Fin 4 → ℤ)).summable_iff).mp ?_
    have := summable_latticeBond_fiber hA i
    simpa [Function.comp_def, hφ] using this
  have hψs : ∀ i, Summable (ψ i) := fun i => summable_latticeBond_fiber hB i
  have hAφ : ∀ i, ∑' h, secondDerivLimit f (h, i) b' (lam (h + Pi.single i 1)) X' =
      ∑' h, φ i h := by
    intro i
    rw [← (Equiv.addRight (Pi.single i 1 : Fin 4 → ℤ)).tsum_eq (φ i)]
    simp [hφ]
  have hstep : ∀ i, ∑' h, secondDerivLimit f (h, i) b' (lam (h + Pi.single i 1)) X' -
      ∑' h, secondDerivLimit f (h, i) b' (lam h) X' = ∑' h, (φ i h - ψ i h) := by
    intro i
    rw [hAφ, (hφs i).tsum_sub (hψs i)]
  simp only [hstep]
  rw [← Summable.tsum_finsetSum fun i _ => (hφs i).sub (hψs i)]
  have hz : ∀ h, ∑ i, (φ i h - ψ i h) = 0 := by
    intro h
    have := secondDerivLimit_divergence hF hR h (lam h) b' X'
    rw [Finset.sum_sub_distrib]
    simp only [hφ, hψ]
    linarith
  simp [hz]
theorem hasSum_secondDerivLimit_pureGauge (hF : ℓ.Admissible) (hR : ColdExpansion ℓ t x D f)
    {lam : (Fin 4 → ℤ) → imaginaryQuaternions} (hl : QuadGrowthSite lam)
    {K : _root_.YangMills.Construction.ColdStepAtMirrorFrames.SecondVariation.LatticeBond → imaginaryQuaternions} (hK : QuadGrowth K) :
    HasSum (fun p : _root_.YangMills.Construction.ColdStepAtMirrorFrames.SecondVariation.LatticeBond × _root_.YangMills.Construction.ColdStepAtMirrorFrames.SecondVariation.LatticeBond => secondDerivLimit f p.1 p.2
      (lam (p.1.1 + Pi.single p.1.2 1) - lam p.1.1) (K p.2)) 0 := by
  have hS := summable_secondDerivLimit_prod hF hR ((quadGrowth_shift hl).sub (quadGrowth_base hl)) hK
  have hsw := (Equiv.prodComm _root_.YangMills.Construction.ColdStepAtMirrorFrames.SecondVariation.LatticeBond _root_.YangMills.Construction.ColdStepAtMirrorFrames.SecondVariation.LatticeBond).summable_iff.mpr hS
  have h0 : ∑' p : _root_.YangMills.Construction.ColdStepAtMirrorFrames.SecondVariation.LatticeBond × _root_.YangMills.Construction.ColdStepAtMirrorFrames.SecondVariation.LatticeBond, secondDerivLimit f p.1 p.2
      (lam (p.1.1 + Pi.single p.1.2 1) - lam p.1.1) (K p.2) = 0 := by
    rw [← (Equiv.prodComm _root_.YangMills.Construction.ColdStepAtMirrorFrames.SecondVariation.LatticeBond _root_.YangMills.Construction.ColdStepAtMirrorFrames.SecondVariation.LatticeBond).tsum_eq]
    have := hsw.tsum_prod
    simp only [Function.comp_def, Equiv.prodComm_apply, Prod.swap, Prod.fst, Prod.snd] at this ⊢
    rw [this]
    simp [tsum_secondDerivLimit_pureGauge hF hR hl]
  rw [← h0]
  exact hS.hasSum
theorem quadraticPotential_step (S : Fin 4 → Fin 4 → imaginaryQuaternions)
    (hS : ∀ μ ν, S μ ν = S ν μ) (e : Fin 4 → imaginaryQuaternions)
    (y : Fin 4 → ℤ) (μ : Fin 4) :
    ((1 / 2 : ℝ) • ∑ α, ∑ β, ((((y + Pi.single μ 1 : Fin 4 → ℤ) α : ℤ) : ℝ) *
        (((y + Pi.single μ 1 : Fin 4 → ℤ) β : ℤ) : ℝ)) • S α β +
      (-(1 / 2) : ℝ) • ∑ α, (((y + Pi.single μ 1 : Fin 4 → ℤ) α : ℤ) : ℝ) • S α α +
      ∑ α, (((y + Pi.single μ 1 : Fin 4 → ℤ) α : ℤ) : ℝ) • e α) -
    ((1 / 2 : ℝ) • ∑ α, ∑ β, (((y α : ℤ) : ℝ) * ((y β : ℤ) : ℝ)) • S α β +
      (-(1 / 2) : ℝ) • ∑ α, ((y α : ℤ) : ℝ) • S α α +
      ∑ α, ((y α : ℤ) : ℝ) • e α) = ∑ ν, ((y ν : ℤ) : ℝ) • S μ ν + e μ := by
  have h10 := hS 1 0
  have h20 := hS 2 0
  have h30 := hS 3 0
  have h21 := hS 2 1
  have h31 := hS 3 1
  have h32 := hS 3 2
  simp only [Fin.sum_univ_four]
  fin_cases μ <;> simp [h10, h20, h30, h21, h31, h32] <;> module
theorem linearPotential_decomp {Fm : Fin 4 → Fin 4 → imaginaryQuaternions}
    {B : _root_.YangMills.Construction.ColdStepAtMirrorFrames.SecondVariation.LatticeBond → imaginaryQuaternions} (hFm : IsAntisymmetricCurvature Fm)
    (hB : IsLinearPotential Fm B) : ∃ lam : (Fin 4 → ℤ) → imaginaryQuaternions,
      QuadGrowthSite lam ∧
      ∀ b, B b = linearPotential Fm b + (lam (b.1 + Pi.single b.2 1) - lam b.1) := by
  obtain ⟨A, e, hform, hcurl⟩ := hB
  set Sy : Fin 4 → Fin 4 → imaginaryQuaternions := fun μ ν => A μ ν - (1 / 2 : ℝ) • Fm ν μ with hSy
  have hsym : ∀ μ ν, Sy μ ν = Sy ν μ := by
    intro μ ν
    have h1 := hcurl μ ν
    have h2 := hFm ν μ
    simp only [hSy]
    have h3 : A ν μ = A μ ν + Fm μ ν := by
      rw [← h1]
      abel
    rw [h2, h3]
    module
  refine ⟨fun h => (1 / 2 : ℝ) • ∑ α, ∑ β, (((h α : ℤ) : ℝ) * ((h β : ℤ) : ℝ)) • Sy α β +
      (-(1 / 2) : ℝ) • ∑ α, ((h α : ℤ) : ℝ) • Sy α α + ∑ α, ((h α : ℤ) : ℝ) • e α, ?_, ?_⟩
  · refine QuadGrowthSite.add (QuadGrowthSite.add (QuadGrowthSite.smul _ ?_)
      (QuadGrowthSite.smul _ ?_)) ?_
    · exact QuadGrowthSite.sum _ fun α _ => QuadGrowthSite.sum _ fun β _ =>
        quadGrowthSite_quadratic α β _
    · exact QuadGrowthSite.sum _ fun α _ => quadGrowthSite_linear α _
    · exact QuadGrowthSite.sum _ fun α _ => quadGrowthSite_linear α _
  · rintro ⟨y, μ⟩
    simp only
    rw [quadraticPotential_step Sy hsym e y μ, hform y μ]
    have h1 : ∑ ν, ((y ν : ℤ) : ℝ) • A μ ν =
        ∑ ν, ((y ν : ℤ) : ℝ) • Sy μ ν + (1 / 2 : ℝ) • ∑ ν, ((y ν : ℤ) : ℝ) • Fm ν μ := by
      rw [Finset.smul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun ν _ => ?_
      simp only [hSy]
      module
    rw [h1]
    simp only [linearPotential]
    abel
end Final
end SecondVariation
open SecondVariation in
theorem limitFormVanishesOnLinearPotentials_proof : LimitFormVanishesOnLinearPotentials := by
  intro ℓ t x D f hF hR
  refine ⟨fun b b' X X' => secondDerivLimit f b b' X X',
    fun b b' X X' => tendsto_secondDerivLimit hF hR b b' X X', ?_⟩
  intro Fm Fm' B B' hFm hFm' hB hB'
  obtain ⟨lam, hlam, hdec⟩ := linearPotential_decomp hFm hB
  obtain ⟨lam', hlam', hdec'⟩ := linearPotential_decomp hFm' hB'
  have hM := quadGrowth_linearPotential Fm
  have hM' := quadGrowth_linearPotential Fm'
  have hd' : QuadGrowth fun b : _root_.YangMills.Construction.ColdStepAtMirrorFrames.SecondVariation.LatticeBond => lam' (b.1 + Pi.single b.2 1) - lam' b.1 :=
    (quadGrowth_shift hlam').sub (quadGrowth_base hlam')
  have h1 : HasSum (fun p : _root_.YangMills.Construction.ColdStepAtMirrorFrames.SecondVariation.LatticeBond × _root_.YangMills.Construction.ColdStepAtMirrorFrames.SecondVariation.LatticeBond => secondDerivLimit f p.1 p.2
      (linearPotential Fm p.1) (linearPotential Fm' p.2)) 0 :=
    hR.no_curvature_term Fm Fm' hFm hFm'
  have h2 := hasSum_secondDerivLimit_pureGauge hF hR hlam hM'
  have h3 := hasSum_secondDerivLimit_pureGauge hF hR hlam hd'
  have h4 : HasSum (fun p : _root_.YangMills.Construction.ColdStepAtMirrorFrames.SecondVariation.LatticeBond × _root_.YangMills.Construction.ColdStepAtMirrorFrames.SecondVariation.LatticeBond => secondDerivLimit f p.1 p.2
      (linearPotential Fm p.1) (lam' (p.2.1 + Pi.single p.2.2 1) - lam' p.2.1)) 0 := by
    have h := (Equiv.prodComm _root_.YangMills.Construction.ColdStepAtMirrorFrames.SecondVariation.LatticeBond _root_.YangMills.Construction.ColdStepAtMirrorFrames.SecondVariation.LatticeBond).hasSum_iff.mpr
      (hasSum_secondDerivLimit_pureGauge hF hR hlam' hM)
    convert h using 2 with p
    exact secondDerivLimit_symm hF hR _ _ _ _
  have h5 := ((h1.add h2).add h4).add h3
  simp only [add_zero] at h5
  convert h5 using 2 with p
  change secondDerivLimit f p.1 p.2 (B p.1) (B' p.2) = _
  rw [hdec p.1, hdec' p.2, secondDerivLimit_add hF hR, secondDerivLimit_add_right hF hR,
    secondDerivLimit_add_right hF hR]
  ring
end ColdStepAtMirrorFrames
end YangMills.Construction
end
