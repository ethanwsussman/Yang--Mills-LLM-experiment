import YangMills.Construction.RunningCouplingSlope.ActionOnTheFibreIsSmooth
import YangMills.Construction.RunningCouplingSlope.ActionOnTheFibreUnderAGaugeFunction
import YangMills.Construction.RunningCouplingSlope.FibreDirectionsAtALeastPoint
import YangMills.Construction.RunningCouplingSlope.FibreFormAtALeastPoint
import YangMills.Construction.RunningCouplingSlope.FlatPointIsLeast
import YangMills.Construction.RunningCouplingSlope.LeastPointsAreGaugeImagesOfSmallTangents
import YangMills.Construction.RunningCouplingSlope.MapsOfTheChainAtALeastPoint
import YangMills.Construction.RunningCouplingSlope.TangentsOfTheLastNoise
import YangMills.Construction.RunningCouplingSlope.TheGaugeShiftReadsNearCellsProof
import YangMills.Construction.RunningCouplingSlope.ZeroOfTheFibreFormAtTheFlatPoint
import Mathlib
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
noncomputable section
namespace YangMills.Construction.RunningCouplingSlope.FibreHessianMinimizerProof
open Filter
open scoped Topology
section Calculus
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F]
theorem hasDerivAt_deriv_comp_two {Φ : E → F} {x : E} (hΦ : ContDiffAt ℝ 2 Φ x) {g : ℝ → ℝ → E}
    {v : ℝ → E} {u w : E} (hg0 : g 0 0 = x) (hv : ∀ᶠ s in 𝓝 (0 : ℝ), HasDerivAt (g s) (v s) 0)
    (hu : HasDerivAt (fun s => g s 0) u 0) (hw : HasDerivAt v w 0) :
    HasDerivAt (fun s => deriv (fun t => Φ (g s t)) 0)
      (fderiv ℝ (fderiv ℝ Φ) x u (v 0) + fderiv ℝ Φ x w) 0 := by
  have hd : ∀ᶠ y in 𝓝 x, DifferentiableAt ℝ Φ y :=
    (hΦ.eventually (by simp)).mono fun y hy => hy.differentiableAt (by norm_num)
  have hc : Tendsto (fun s => g s 0) (𝓝 0) (𝓝 x) := by
    have := hu.continuousAt.tendsto
    simpa [hg0] using this
  have heq : (fun s => deriv (fun t => Φ (g s t)) 0) =ᶠ[𝓝 0]
      fun s => fderiv ℝ Φ (g s 0) (v s) := by
    filter_upwards [hc.eventually hd, hv] with s h1 h2
    exact (h1.hasFDerivAt.comp_hasDerivAt 0 h2).deriv
  have hD : HasFDerivAt (fderiv ℝ Φ) (fderiv ℝ (fderiv ℝ Φ) x) x :=
    ((hΦ.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)).hasFDerivAt
  have hL : HasDerivAt (fun s => fderiv ℝ Φ (g s 0)) (fderiv ℝ (fderiv ℝ Φ) x u) 0 := by
    have h := HasFDerivAt.comp_hasDerivAt (x := (0 : ℝ)) (f := fun s => g s 0)
      (l := fderiv ℝ Φ) (l' := fderiv ℝ (fderiv ℝ Φ) x) (f' := u) (by simpa [hg0] using hD) hu
    exact h
  have h3 := hL.clm_apply hw
  rw [hg0] at h3
  exact h3.congr_of_eventuallyEq heq
theorem hasDerivAt_deriv_line {Φ : E → F} (hΦ : ContDiffAt ℝ 2 Φ 0) (a b : E) :
    HasDerivAt (fun s : ℝ => deriv (fun t : ℝ => Φ (s • a + t • b)) 0)
      (fderiv ℝ (fderiv ℝ Φ) 0 a b) 0 := by
  have h := hasDerivAt_deriv_comp_two (g := fun s t => s • a + t • b) (v := fun _ => b) (u := a)
    (w := 0) hΦ
    (by simp) (Eventually.of_forall fun s => by
      have h1 : HasDerivAt (fun t : ℝ => t • b) ((1 : ℝ) • b) 0 :=
        (hasDerivAt_id (0 : ℝ)).smul_const b
      simpa using h1.const_add (s • a))
    (by
      have h1 : HasDerivAt (fun s : ℝ => s • a) ((1 : ℝ) • a) 0 :=
        (hasDerivAt_id (0 : ℝ)).smul_const a
      simpa using h1)
    (hasDerivAt_const _ _)
  simpa using h
def bilinComp {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] (ι : E →L[ℝ] P) :
    (P →L[ℝ] P →L[ℝ] ℝ) →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ :=
  (ContinuousLinearMap.compL ℝ E (P →L[ℝ] ℝ) (E →L[ℝ] ℝ)
      ((ContinuousLinearMap.compL ℝ E P ℝ).flip ι)).comp
    ((ContinuousLinearMap.compL ℝ E P (P →L[ℝ] ℝ)).flip ι)
theorem bilinComp_apply {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] (ι : E →L[ℝ] P)
    (G : P →L[ℝ] P →L[ℝ] ℝ) (u v : E) : bilinComp ι G u v = G (ι u) (ι v) := rfl
theorem fderiv_fderiv_comp_affine {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    {Ψ : P → ℝ} {p : P} (h : ContDiffAt ℝ 2 Ψ p) (ι : E →L[ℝ] P) :
    fderiv ℝ (fderiv ℝ fun w : E => Ψ (p + ι w)) 0 = bilinComp ι (fderiv ℝ (fderiv ℝ Ψ) p) := by
  have hc : Tendsto (fun w : E => p + ι w) (𝓝 0) (𝓝 p) := by
    have h1 : Continuous fun w : E => p + ι w := by fun_prop
    simpa using h1.tendsto (0 : E)
  have hd : ∀ᶠ w in 𝓝 (0 : E), DifferentiableAt ℝ Ψ (p + ι w) :=
    hc.eventually ((h.eventually (by simp)).mono fun y hy => hy.differentiableAt (by norm_num))
  have hι : ∀ w : E, HasFDerivAt (fun w : E => p + ι w) ι w := fun w =>
    ι.hasFDerivAt.const_add p
  have heq : fderiv ℝ (fun w : E => Ψ (p + ι w)) =ᶠ[𝓝 0]
      fun w => ((ContinuousLinearMap.compL ℝ E P ℝ).flip ι) (fderiv ℝ Ψ (p + ι w)) := by
    filter_upwards [hd] with w hw
    exact (hw.hasFDerivAt.comp w (hι w)).fderiv
  have hD : HasFDerivAt (fderiv ℝ Ψ) (fderiv ℝ (fderiv ℝ Ψ) p) (p + ι 0) := by
    rw [map_zero, add_zero]
    exact ((h.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)).hasFDerivAt
  have h2 := (((ContinuousLinearMap.compL ℝ E P ℝ).flip ι).hasFDerivAt.comp _
    (hD.comp (0 : E) (hι 0)))
  rw [heq.fderiv_eq]
  exact h2.fderiv
theorem apply_eq_zero_of_nonneg_of_self (H : E →L[ℝ] E →L[ℝ] ℝ) (hs : ∀ u v, H u v = H v u)
    (hp : ∀ u, 0 ≤ H u u) {u : E} (hu : H u u = 0) : H u = 0 := by
  ext v
  by_contra hne
  change ¬ H u v = 0 at hne
  have h := hp (((-(H v v + 1)) / (2 * H u v)) • u + v)
  simp only [map_add, map_smul, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    hu, smul_eq_mul, hs v u] at h
  have e : (-(H v v + 1)) / (2 * H u v) * H u v = -(H v v + 1) / 2 := by
    field_simp
  nlinarith [e]
theorem exists_finrank_isotropic_le [FiniteDimensional ℝ E] (T : E →L[ℝ] E →L[ℝ] ℝ)
    (Z : Submodule ℝ E) (hpos : ∀ u, 0 ≤ T u u) (hZ : ∀ u, T u u = 0 → u ∈ Z) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ S : E →L[ℝ] E →L[ℝ] ℝ, ‖S - T‖ < δ → ∀ M : Submodule ℝ E,
      (∀ u ∈ M, S u u = 0) → Module.finrank ℝ M ≤ Module.finrank ℝ Z := by
  obtain ⟨C, hC⟩ := Submodule.exists_isCompl Z
  have hsum := Submodule.finrank_add_eq_of_isCompl hC
  by_cases hbot : C = ⊥
  · refine ⟨1, one_pos, fun S _ M _ => ?_⟩
    have h1 := Submodule.finrank_le M
    rw [hbot, finrank_bot] at hsum
    omega
  have hne : (Metric.sphere (0 : C) 1).Nonempty := by
    obtain ⟨x, hx⟩ := (Submodule.ne_bot_iff C).1 hbot
    obtain ⟨hxC, hx0⟩ := hx
    refine ⟨(‖x‖⁻¹ : ℝ) • (⟨x, hxC⟩ : C), ?_⟩
    have : ‖(⟨x, hxC⟩ : C)‖ = ‖x‖ := rfl
    rw [mem_sphere_zero_iff_norm, norm_smul, this, norm_inv, norm_norm,
      inv_mul_cancel₀ (norm_ne_zero_iff.2 hx0)]
  have hcont : ContinuousOn (fun u : C => T (u : E) (u : E)) (Metric.sphere (0 : C) 1) := by
    have h1 : Continuous fun u : C => (u : E) := continuous_subtype_val
    exact ((T.continuous.comp h1).clm_apply h1).continuousOn
  obtain ⟨u₀, hu₀, hmin⟩ := (isCompact_sphere (0 : C) 1).exists_isMinOn hne hcont
  have hu₀n : ‖u₀‖ = 1 := by simpa using hu₀
  have hc : 0 < T (u₀ : E) (u₀ : E) := by
    refine lt_of_le_of_ne (hpos _) fun h => ?_
    have h1 : (u₀ : E) ∈ Z := hZ _ h.symm
    have h2 : (u₀ : E) = 0 := by
      have := hC.disjoint.le_bot ⟨h1, u₀.2⟩
      simpa using this
    have h3 : ‖(u₀ : E)‖ = 1 := hu₀n
    rw [h2, norm_zero] at h3
    exact zero_ne_one h3
  refine ⟨_, hc, fun S hS M hM => ?_⟩
  have hdis : Disjoint M C := by
    rw [Submodule.disjoint_def]
    intro x hxM hxC
    by_contra hx
    set y : C := (‖x‖⁻¹ : ℝ) • (⟨x, hxC⟩ : C) with hy
    have hyn : ‖(y : E)‖ = 1 := by
      change ‖(‖x‖⁻¹ : ℝ) • x‖ = 1
      rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (norm_ne_zero_iff.2 hx)]
    have hyM : (y : E) ∈ M := M.smul_mem _ hxM
    have h1 : T (u₀ : E) (u₀ : E) ≤ T (y : E) (y : E) :=
      hmin (show y ∈ Metric.sphere (0 : C) 1 by
        rw [mem_sphere_zero_iff_norm]
        exact hyn)
    have h2 : S (y : E) (y : E) = 0 := hM _ hyM
    have h3 : |(S - T) (y : E) (y : E)| ≤ ‖S - T‖ := by
      have := ((S - T).le_opNorm₂ (y : E) (y : E))
      rw [Real.norm_eq_abs, hyn] at this
      simpa using this
    have h4 : (S - T) (y : E) (y : E) = - T (y : E) (y : E) := by
      simp [h2]
    rw [h4, abs_neg] at h3
    have h5 := le_abs_self (T (y : E) (y : E))
    linarith
  have h1 := Submodule.finrank_add_finrank_le_of_disjoint hdis
  omega
theorem eventually_norm_sub_lt {Z : Type*} [TopologicalSpace Z] {z₀ : Z}
    {f : Z → E →L[ℝ] E →L[ℝ] ℝ} {T : E →L[ℝ] E →L[ℝ] ℝ} (hf : ContinuousAt f z₀) (hT : f z₀ = T)
    {δ : ℝ} (hδ : 0 < δ) : ∀ᶠ z in 𝓝 z₀, ‖f z - T‖ < δ := by
  subst hT
  have hf' : @ContinuousAt Z (E →L[ℝ] E →L[ℝ] ℝ) _
      (PseudoMetricSpace.toUniformSpace.toTopologicalSpace) f z₀ := hf
  have h := Metric.continuousAt_iff'.1 hf' δ hδ
  filter_upwards [h] with z hz
  have h1 := @dist_eq_norm (E →L[ℝ] E →L[ℝ] ℝ) _ (f z) (f z₀)
  exact h1 ▸ hz
theorem deriv_deriv_line_eq_hessian {A : Type*} [AddCommGroup A] [Module ℝ A] (e : E →ₗ[ℝ] A)
    (G : A → ℝ) (h : ContDiffAt ℝ 2 (fun w => G (e w)) 0) (u v : E) :
    deriv (fun s : ℝ => deriv (fun t : ℝ => G (s • e u + t • e v)) 0) 0 =
      fderiv ℝ (fderiv ℝ fun w => G (e w)) 0 u v := by
  have h1 := hasDerivAt_deriv_line h u v
  have e1 : (fun s : ℝ => deriv (fun t : ℝ => G (s • e u + t • e v)) 0) =
      fun s : ℝ => deriv (fun t : ℝ => G (e (s • u + t • v))) 0 := by
    funext s
    congr 1
    funext t
    rw [map_add, map_smul, map_smul]
  rw [e1]
  exact h1.deriv
theorem smul_add_smul_add {A : Type*} [AddCommGroup A] [Module ℝ A] (ξ τ : A) (s t : ℝ) :
    s • (ξ + τ) + t • (ξ + τ) = (s • ξ + t • ξ) + (s • τ + t • τ) := by
  simp only [smul_add]
  abel
theorem smul_zero_add_smul_zero {A : Type*} [AddCommGroup A] [Module ℝ A] (s t : ℝ) :
    s • (0 : A) + t • (0 : A) = 0 := by
  simp
end Calculus
section Coordinates
variable {L n k : ℕ}
theorem expMove_zero_unitPoint :
    expMove (0 : LevelForms L n k) (unitPoint L n k) = unitPoint L n k := by apply _root_.YangMills.SharedProofs.p5970 <;> assumption
variable {N : ℕ} (e : (Fin N → ℝ) ≃ₗ[ℝ] LevelForms L n k)
def coordAction (a : ℝ) (Y : ChainPoint L n k) (w : Fin N → ℝ) : ℝ :=
  chainAction a (fibreMove Y (e w))
theorem fibreSecondDeriv_eq_hessian {a : ℝ} {Y : ChainPoint L n k}
    (h : ContDiffAt ℝ 2 (coordAction e a Y) 0) (u v : Fin N → ℝ) :
    fibreSecondDeriv a Y (e u) (e v) = fderiv ℝ (fderiv ℝ (coordAction e a Y)) 0 u v := deriv_deriv_line_eq_hessian e.toLinearMap (fun ξ => chainAction a (fibreMove Y ξ)) h u v
theorem fibreSecondDeriv_add_finalNoise (h : ∀ (X : ChainPoint L n k) (ξ τ : LevelForms L n k),
      τ ∈ finalNoiseTangents L n k → fibreMove X (ξ + τ) = fibreMove X ξ)
    (a : ℝ) (Y : ChainPoint L n k) (ξ : LevelForms L n k) {τ : LevelForms L n k}
    (hτ : τ ∈ finalNoiseTangents L n k) :
    fibreSecondDeriv a Y (ξ + τ) (ξ + τ) = fibreSecondDeriv a Y ξ ξ := by
  have e1 : ∀ s t : ℝ, fibreMove Y (s • (ξ + τ) + t • (ξ + τ)) = fibreMove Y (s • ξ + t • ξ) := by
    intro s t
    rw [smul_add_smul_add]
    exact h _ _ _ (Submodule.add_mem _ (Submodule.smul_mem _ _ hτ) (Submodule.smul_mem _ _ hτ))
  simp only [fibreSecondDeriv, e1]
theorem fibreSecondDeriv_zero (a : ℝ) (Y : ChainPoint L n k) :
    fibreSecondDeriv a Y (0 : LevelForms L n k) 0 = 0 := by
  simp only [fibreSecondDeriv, smul_zero_add_smul_zero]
  simp
theorem fibreHessian_of_kernel_bound [FiniteDimensional ℝ (LevelForms L n k)] {a : ℝ}
    {X : ChainPoint L n k}
    (hcX : ContDiffAt ℝ 2 (coordAction e a X) 0) (hm : ChainLinearMapsAt X)
    (hT : ∀ (ξ τ : LevelForms L n k), τ ∈ finalNoiseTangents L n k →
      fibreMove X (ξ + τ) = fibreMove X ξ)
    (hTr : ∀ τ ∈ finalNoiseTangents L n k, topDeriv X τ = 0 → τ = 0)
    (hDp : ∀ ξ : LevelForms L n k, 0 ≤ fibreSecondDeriv a X ξ ξ)
    (hDo : ∀ l ∈ topVanishingGauges L n k, ∀ ξ : LevelForms L n k,
      formValues ξ = gaugeOrbitValues X (l : Tower.Vertex L n k 0 → Matrices.ComplexMatrix2) →
        fibreSecondDeriv a X ξ ξ = 0)
    (D₁ : topVanishingGauges L n k →ₗ[ℝ] LevelForms L n k) (hD₁ : Function.Injective D₁)
    (hrank : ∀ NX : Submodule ℝ (Fin N → ℝ),
      (∀ u ∈ NX, fderiv ℝ (fderiv ℝ (coordAction e a X)) 0 u u = 0) →
      Module.finrank ℝ NX ≤ Module.finrank ℝ (LinearMap.range D₁ ⊔ finalNoiseTangents L n k :
        Submodule ℝ (LevelForms L n k))) :
    (∀ ξ, 0 ≤ fibreHessian a X ξ) ∧
      ∀ ξ : LinearMap.ker (topDeriv X), fibreHessian a X ξ = 0 ↔
        (ξ : LevelForms L n k) ∈ (topVanishingGauges L n k).map (gaugeOrbitMap X) := by
  obtain ⟨H, hH⟩ : ∃ H, H = fderiv ℝ (fderiv ℝ (coordAction e a X)) 0 := ⟨_, rfl⟩
  rw [← hH] at hrank
  have hsecond : ∀ u, H u u = fibreSecondDeriv a X (e u) (e u) := fun u => by
    rw [hH]
    exact (fibreSecondDeriv_eq_hessian e hcX u u).symm
  have hpos : ∀ u, 0 ≤ H u u := fun u => by
    rw [hsecond]
    exact hDp _
  have hsym : ∀ u v, H u v = H v u := fun u v => by
    rw [hH]
    exact hcX.isSymmSndFDerivAt (by simp) u v
  have hnull : ∀ {u}, H u u = 0 → H u = 0 := fun hu =>
    apply_eq_zero_of_nonneg_of_self H hsym hpos hu
  obtain ⟨NX, hNX⟩ : ∃ NX : Submodule ℝ (Fin N → ℝ), NX = LinearMap.ker H.toLinearMap := ⟨_, rfl⟩
  have hmemN : ∀ {u}, H u u = 0 → u ∈ NX := fun hu => by
    rw [hNX]
    exact LinearMap.mem_ker.2 (hnull hu)
  obtain ⟨Nn, hNn⟩ : ∃ Nn : Submodule ℝ (LevelForms L n k),
    Nn = NX.map (e : (Fin N → ℝ) →ₗ[ℝ] LevelForms L n k) := ⟨_, rfl⟩
  have hmemA : ∀ {ξ : LevelForms L n k}, fibreSecondDeriv a X ξ ξ = 0 → ξ ∈ Nn := by
    intro ξ hξ
    rw [hNn]
    refine ⟨e.symm ξ, hmemN ?_, e.apply_symm_apply ξ⟩
    rw [hsecond, e.apply_symm_apply]
    exact hξ
  obtain ⟨Dk, hDk⟩ : ∃ Dk : topVanishingGauges L n k →ₗ[ℝ] LevelForms L n k,
    Dk = gaugeOrbitMap X ∘ₗ (topVanishingGauges L n k).subtype := ⟨_, rfl⟩
  have hDkv : ∀ l : topVanishingGauges L n k, Dk l = gaugeOrbitMap X l := fun l => by rw [hDk]; rfl
  have hle : LinearMap.range Dk ⊔ finalNoiseTangents L n k ≤ Nn := by
    refine sup_le ?_ ?_
    · rintro _ ⟨⟨l, hl⟩, rfl⟩
      rw [hDkv]
      exact hmemA (hDo l hl _ (hm.orbit_spec l))
    · intro τ hτ
      refine hmemA ?_
      have h1 : fibreSecondDeriv a X (0 + τ) (0 + τ) = fibreSecondDeriv a X 0 0 := by
        have e1 : ∀ s t : ℝ, fibreMove X (s • ((0 : LevelForms L n k) + τ) + t • (0 + τ)) =
            fibreMove X (s • (0 : LevelForms L n k) + t • 0) := by
          intro s t
          rw [smul_add_smul_add]
          exact hT _ _ (Submodule.add_mem _ (Submodule.smul_mem _ _ hτ) (Submodule.smul_mem _ _ hτ))
        simp only [fibreSecondDeriv, e1]
      rw [zero_add, fibreSecondDeriv_zero] at h1
      exact h1
  have htop : ∀ l : topVanishingGauges L n k, topDeriv X (Dk l) = 0 := by
    rintro ⟨l, hl⟩
    have h1 := hm.topDeriv_orbit l
    have h2 : restrictToTopLinear L n k l = 0 := by
      apply Subtype.ext
      rw [hm.restrict_apply l, ZeroMemClass.coe_zero]
      funext y
      exact hl y
    rw [h2, map_zero] at h1
    rw [hDkv]
    exact h1
  have hdis : Disjoint (LinearMap.range Dk) (finalNoiseTangents L n k) := by
    rw [Submodule.disjoint_def]
    rintro _ ⟨l, rfl⟩ hτ
    exact hTr _ hτ (htop l)
  have hinj : Function.Injective Dk := by
    rw [hDk]
    exact hm.orbit_injective
  have hrank' : Module.finrank ℝ Nn ≤ Module.finrank ℝ
      (LinearMap.range D₁ ⊔ finalNoiseTangents L n k : Submodule ℝ (LevelForms L n k)) := by
    have h1 : Module.finrank ℝ Nn = Module.finrank ℝ NX := by
      rw [hNn]
      exact LinearEquiv.finrank_map_eq e NX
    rw [h1]
    refine hrank NX fun u hu => ?_
    rw [hNX] at hu
    have h5 : H u = 0 := LinearMap.mem_ker.1 hu
    rw [h5]
    rfl
  have hEq : LinearMap.range Dk ⊔ finalNoiseTangents L n k = Nn :=
    by
      refine Submodule.eq_of_le_of_finrank_le hle ?_
      have h1 := Submodule.finrank_add_le_finrank_add_finrank (LinearMap.range D₁)
        (finalNoiseTangents L n k)
      have h2 := Submodule.finrank_sup_add_finrank_inf_eq (LinearMap.range Dk)
        (finalNoiseTangents L n k)
      rw [hdis.eq_bot, finrank_bot, add_zero] at h2
      have h3 := LinearMap.finrank_range_of_inj hD₁
      have h4 := LinearMap.finrank_range_of_inj hinj
      omega
  have hex : ∃ T : QuadraticForm ℝ (LinearMap.ker (topDeriv X)), IsFibreHessian a X T := by
    obtain ⟨c, hc⟩ : ∃ c : LinearMap.ker (topDeriv X) →ₗ[ℝ] Fin N → ℝ,
      c = (e.symm : LevelForms L n k →ₗ[ℝ] Fin N → ℝ) ∘ₗ
        (LinearMap.ker (topDeriv X)).subtype := ⟨_, rfl⟩
    refine ⟨LinearMap.BilinMap.toQuadraticMap (LinearMap.mk₂ ℝ (fun u v => H (c u) (c v))
      ?_ ?_ ?_ ?_), fun ξ => ?_⟩
    · intro u u' v
      simp [map_add]
    · intro r u v
      simp [map_smul]
    · intro u v v'
      simp [map_add]
    · intro r u v
      simp [map_smul]
    · have h1 : c ξ = e.symm (ξ : LevelForms L n k) := by rw [hc]; rfl
      change H (c ξ) (c ξ) = _
      rw [h1, hsecond, e.apply_symm_apply]
  have hs : IsFibreHessian a X (fibreHessian a X) := Classical.epsilon_spec hex
  have hf : ∀ η : LinearMap.ker (topDeriv X), fibreHessian a X η =
      H (e.symm (η : LevelForms L n k)) (e.symm (η : LevelForms L n k)) := fun η => by
    rw [hs η, hsecond, e.apply_symm_apply]
  refine ⟨fun ξ => ?_, fun ξ => ⟨fun h0 => ?_, ?_⟩⟩
  · rw [hf]
    exact hpos _
  · rw [hf] at h0
    have h1 : (ξ : LevelForms L n k) ∈ Nn := by
      rw [hNn]
      exact ⟨_, hmemN h0, e.apply_symm_apply _⟩
    rw [← hEq] at h1
    obtain ⟨x, ⟨l, rfl⟩, τ, hτ, hxτ⟩ := Submodule.mem_sup.1 h1
    have h2 : topDeriv X τ = 0 := by
      have h3 := LinearMap.mem_ker.1 ξ.2
      rw [← hxτ, map_add, htop l, zero_add] at h3
      exact h3
    have h4 := hTr τ hτ h2
    rw [h4, add_zero, hDkv] at hxτ
    exact ⟨l.1, l.2, hxτ⟩
  · rintro ⟨l, hl, hlξ⟩
    rw [hs ξ, ← hlξ]
    exact hDo l hl _ (hm.orbit_spec l)
end Coordinates
theorem fibreHessianAtMinimizer_holds (hSp : Tower.FiniteSideFormSpaces)
    (hMaps : ChainMapsAtMinimizers) (hFlat : UnitPointIsMinimizer)
    (hLast : FinalNoiseComplement) (hSmooth : ChainActionFibreContDiff)
    (hImage : MinimizerGaugeEquivalentToSmallMove)
    (hGauge : FibreActionGaugeInvariant)
    (hDir : FibreHessianNonnegAtMinimizer)
    (hZero : FibreHessianKernelAtUnit) :
    FibreHessianAtMinimizer := by
  intro a ha L hL k n hk hn
  have h₀ := hSp L n k 0 hL hn (Nat.zero_le k)
  have hi : ∀ i : Fin k, _ := fun i : Fin k => hSp L n k (i + 1) hL hn i.2
  haveI := h₀.2.1
  haveI : ∀ i : Fin k, FiniteDimensional ℝ (Tower.edgeFormSpace L n k (i + 1)) := fun i =>
    (hi i).2.1
  haveI : FiniteDimensional ℝ (LevelForms L n k) := inferInstance
  set N := Module.finrank ℝ (LevelForms L n k) with hN
  let e : (Fin N → ℝ) ≃ₗ[ℝ] LevelForms L n k :=
    (Module.finBasis ℝ (LevelForms L n k)).equivFun.symm
  obtain ⟨hread, hleast⟩ := hFlat a ha L hL k n hk hn
  have hM := hMaps a ha L hL k n hk hn
  obtain ⟨hT, hTr⟩ := hLast L hL k n hk hn
  have hD := hDir a ha L hL k n hk hn
  let Ψ : (Fin N → ℝ) × (Fin N → ℝ) → ℝ := fun p =>
    chainAction a (fibreMove (expMove (e p.1) (unitPoint L n k)) (e p.2))
  have hΨ : ContDiffAt ℝ 2 Ψ 0 := hSmooth a L hL k n hk hn N e.toLinearMap
  let ι : (Fin N → ℝ) →L[ℝ] (Fin N → ℝ) × (Fin N → ℝ) := ContinuousLinearMap.inr ℝ _ _
  have hnear : ∀ᶠ ζ in 𝓝 (0 : Fin N → ℝ), ContDiffAt ℝ 2 Ψ (ζ, 0) := by
    have hc : Tendsto (fun ζ : Fin N → ℝ => (ζ, (0 : Fin N → ℝ))) (𝓝 0) (𝓝 0) := by
      have h1 : Continuous fun ζ : Fin N → ℝ => (ζ, (0 : Fin N → ℝ)) := by fun_prop
      exact h1.tendsto' _ _ rfl
    exact hc.eventually (hΨ.eventually (by simp))
  have hslice : ∀ ζ : Fin N → ℝ, (fun w : Fin N → ℝ => Ψ ((ζ, 0) + ι w)) =
      coordAction e a (expMove (e ζ) (unitPoint L n k)) := by
    intro ζ
    funext w
    simp [Ψ, ι, coordAction]
  have hcdζ : ∀ ζ : Fin N → ℝ, ContDiffAt ℝ 2 Ψ (ζ, 0) →
      ContDiffAt ℝ 2 (coordAction e a (expMove (e ζ) (unitPoint L n k))) 0 := by
    intro ζ h
    rw [← hslice ζ]
    have h1 : ContDiffAt ℝ 2
        (fun w : Fin N → ℝ => ((ζ, 0) : (Fin N → ℝ) × (Fin N → ℝ)) + ι w) 0 :=
      (contDiff_const.add ι.contDiff).contDiffAt
    have h2 : ContDiffAt ℝ 2 Ψ (((ζ, 0) : (Fin N → ℝ) × (Fin N → ℝ)) + ι 0) := by
      simpa using h
    exact ContDiffAt.comp (g := Ψ)
      (f := fun w : Fin N → ℝ => ((ζ, 0) : (Fin N → ℝ) × (Fin N → ℝ)) + ι w)
      (0 : Fin N → ℝ) h2 h1
  have hQ : ∀ ζ : Fin N → ℝ, ContDiffAt ℝ 2 Ψ (ζ, 0) →
      fderiv ℝ (fderiv ℝ (coordAction e a (expMove (e ζ) (unitPoint L n k)))) 0 =
        bilinComp ι (fderiv ℝ (fderiv ℝ Ψ) (ζ, 0)) := by
    intro ζ h
    rw [← hslice ζ]
    exact fderiv_fderiv_comp_affine h ι
  have hz : e 0 = 0 := map_zero e
  have hc0 : ContDiffAt ℝ 2 (coordAction e a (unitPoint L n k)) 0 := by
    have := hcdζ 0 hnear.self_of_nhds
    rwa [hz, expMove_zero_unitPoint] at this
  set T₀ := fderiv ℝ (fderiv ℝ (coordAction e a (unitPoint L n k))) 0 with hT₀
  have hpos₀ : ∀ u, 0 ≤ T₀ u u := fun u => by
    rw [hT₀, ← fibreSecondDeriv_eq_hessian e hc0]
    exact (hD _ _ hleast).1 _
  have hmf : ChainLinearMapsAt (unitPoint L n k) := hM.self_of_nhds _ hread _ hleast
  set S₁ : Submodule ℝ (LevelForms L n k) :=
    LinearMap.range (gaugeOrbitMap (unitPoint L n k) ∘ₗ (topVanishingGauges L n k).subtype) ⊔
      finalNoiseTangents L n k with hS₁
  have hZ₀ : ∀ u, T₀ u u = 0 → u ∈ S₁.map (e.symm : LevelForms L n k →ₗ[ℝ] Fin N → ℝ) := by
    intro u hu
    obtain ⟨τ, hτ, hτ0⟩ := (hTr _ hleast.compact).2 (e u)
    have h1 : fibreSecondDeriv a (unitPoint L n k) (e u + τ) (e u + τ) = 0 := by
      rw [fibreSecondDeriv_add_finalNoise hT _ _ _ hτ, fibreSecondDeriv_eq_hessian e hc0]
      exact hu
    obtain ⟨l, hl, hlη⟩ := hZero a ha L hL k n hk hn _ hτ0 h1
    refine ⟨e u, ?_, by simp⟩
    have h2 : e u = gaugeOrbitMap (unitPoint L n k) l + -τ := by
      rw [← hlη]
      abel
    rw [h2]
    exact Submodule.add_mem_sup ⟨⟨l, hl⟩, rfl⟩ (Submodule.neg_mem _ hτ)
  obtain ⟨δ, hδ, hrank⟩ := exists_finrank_isotropic_le T₀ _ hpos₀ hZ₀
  have hclose : ∀ᶠ ζ in 𝓝 (0 : Fin N → ℝ),
      ‖bilinComp ι (fderiv ℝ (fderiv ℝ Ψ) (ζ, 0)) - T₀‖ < δ := by
    have hDc : ContinuousAt (fderiv ℝ (fderiv ℝ Ψ)) 0 :=
      ((hΨ.fderiv_right (m := 1) (by norm_num)).fderiv_right (m := 0) (by norm_num)).continuousAt
    have h1 : Continuous fun ζ : Fin N → ℝ => (ζ, (0 : Fin N → ℝ)) := by fun_prop
    have h2 : ContinuousAt (fun ζ : Fin N → ℝ => bilinComp ι (fderiv ℝ (fderiv ℝ Ψ) (ζ, 0))) 0 :=
      (bilinComp ι).continuous.continuousAt.comp
        (ContinuousAt.comp (g := fderiv ℝ (fderiv ℝ Ψ)) hDc h1.continuousAt)
    have h3 : bilinComp ι (fderiv ℝ (fderiv ℝ Ψ) ((0 : Fin N → ℝ), (0 : Fin N → ℝ))) = T₀ := by
      rw [hT₀, ← hQ 0 hnear.self_of_nhds, hz, expMove_zero_unitPoint]
    exact eventually_norm_sub_lt h2 h3 hδ
  have hO : {ζ : Fin N → ℝ | ContDiffAt ℝ 2 Ψ (ζ, 0) ∧
      ‖bilinComp ι (fderiv ℝ (fderiv ℝ Ψ) (ζ, 0)) - T₀‖ < δ} ∈ 𝓝 (0 : Fin N → ℝ) :=
    hnear.and hclose
  filter_upwards [hM, hImage a ha L hL k n hk hn N e _ hO] with V hV₁ hV₂ W hW X hX
  have hm : ChainLinearMapsAt X := hV₁ W hW X hX
  obtain ⟨v, w₀, hvr, hv1, ⟨hw₁, hw₂⟩, hgv⟩ := hV₂ W hW X hX
  obtain ⟨A, -, hA⟩ := hGauge a L hL k n hk hn X hX.compact v hvr hv1
  have hAe := hA N e.toLinearMap
  let R : (Fin N → ℝ) ≃ₗ[ℝ] (Fin N → ℝ) := (e.trans A).trans e.symm
  let Rc : (Fin N → ℝ) →L[ℝ] (Fin N → ℝ) := LinearMap.toContinuousLinearMap R.toLinearMap
  have hR : ∀ w, e (Rc w) = A (e w) := fun w => e.apply_symm_apply _
  have hf₀ := hcdζ w₀ hw₁
  have hg : coordAction e a X =ᶠ[𝓝 0]
      fun w => coordAction e a (expMove (e w₀) (unitPoint L n k)) (0 + Rc w) := by
    filter_upwards [hAe] with w hw
    rw [zero_add]
    change chainAction a (fibreMove X (e w)) =
      chainAction a (fibreMove (expMove (e w₀) (unitPoint L n k)) (e (Rc w)))
    rw [hR, ← hgv]
    exact hw.symm
  have hcomp : ContDiffAt ℝ 2
      (fun w => coordAction e a (expMove (e w₀) (unitPoint L n k)) (0 + Rc w)) 0 := by
    have h1 : ContDiffAt ℝ 2 (fun w : Fin N → ℝ => (0 : Fin N → ℝ) + Rc w) 0 :=
      (contDiff_const.add Rc.contDiff).contDiffAt
    have h2 : ContDiffAt ℝ 2 (coordAction e a (expMove (e w₀) (unitPoint L n k)))
        ((0 : Fin N → ℝ) + Rc 0) := by
      simpa using hf₀
    exact ContDiffAt.comp (g := coordAction e a (expMove (e w₀) (unitPoint L n k)))
      (f := fun w : Fin N → ℝ => (0 : Fin N → ℝ) + Rc w) (0 : Fin N → ℝ) h2 h1
  have hcX : ContDiffAt ℝ 2 (coordAction e a X) 0 := hcomp.congr_of_eventuallyEq hg
  have hHS : ∀ u v, fderiv ℝ (fderiv ℝ (coordAction e a X)) 0 u v =
      bilinComp ι (fderiv ℝ (fderiv ℝ Ψ) (w₀, 0)) (Rc u) (Rc v) := by
    intro u v
    have h1 : fderiv ℝ (fderiv ℝ (coordAction e a X)) 0 = fderiv ℝ (fderiv ℝ
        fun w => coordAction e a (expMove (e w₀) (unitPoint L n k)) (0 + Rc w)) 0 :=
      hg.fderiv.fderiv_eq
    rw [h1, fderiv_fderiv_comp_affine hf₀ Rc, bilinComp_apply, hQ w₀ hw₁]
  refine fibreHessian_of_kernel_bound e hcX hm (hT X) (hTr X hX.compact).1 (hD _ _ hX).1
    (hD _ _ hX).2 _ hmf.orbit_injective ?_
  intro NX hNX
  have h2 : Module.finrank ℝ (NX.map (R : (Fin N → ℝ) →ₗ[ℝ] Fin N → ℝ)) = Module.finrank ℝ NX :=
    LinearEquiv.finrank_map_eq R NX
  have h3 : Module.finrank ℝ
      (S₁.map (e.symm : LevelForms L n k →ₗ[ℝ] Fin N → ℝ)) = Module.finrank ℝ S₁ :=
    LinearEquiv.finrank_map_eq e.symm S₁
  have h4 := hrank _ hw₂ (NX.map (R : (Fin N → ℝ) →ₗ[ℝ] Fin N → ℝ)) (by
    rintro _ ⟨u, hu, rfl⟩
    have h6 := hNX u hu
    rw [hHS] at h6
    exact h6)
  rw [h2, h3] at h4
  exact h4
end YangMills.Construction.RunningCouplingSlope.FibreHessianMinimizerProof
end
