import YangMills.Construction.Calculus.AnalyticConstrainedMinimizers
import Mathlib
set_option autoImplicit false
open Set Metric Filter
open scoped Topology
noncomputable section
namespace YangMills.Construction.ConstrainedMinima
section InverseFunction
variable {F H : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  [NormedAddCommGroup H] [NormedSpace ℝ H] [CompleteSpace H]
omit [CompleteSpace F] [CompleteSpace H] in
theorem analyticAt_symm_of_fderiv_eq_equiv (e : OpenPartialHomeomorph F H) {a : F}
    (ha : a ∈ e.source) (hA : AnalyticAt ℝ e a) {i : F ≃L[ℝ] H} (hi : fderiv ℝ e a = i) :
    AnalyticAt ℝ e.symm (e a) := by
  obtain ⟨p, hp⟩ := hA
  refine (e.hasFPowerSeriesAt_symm ha hp (i := i) ?_).analyticAt
  have h := hp.fderiv_eq
  rw [hi] at h
  rw [h, LinearIsometryEquiv.symm_apply_apply]
theorem exists_openPartialHomeomorph_analytic_inverse (Ψ : F → H) (a : F)
    (hΨ : AnalyticAt ℝ Ψ a) (i : F ≃L[ℝ] H) (hi : fderiv ℝ Ψ a = i) :
    ∃ e : OpenPartialHomeomorph F H, a ∈ e.source ∧ ⇑e = Ψ ∧
      ∀ p ∈ e.target, AnalyticAt ℝ e.symm p := by
  have hs : HasStrictFDerivAt Ψ (i : F →L[ℝ] H) a := hi ▸ hΨ.hasStrictFDerivAt
  let e₀ := hs.toOpenPartialHomeomorph Ψ
  have he₀ : ⇑e₀ = Ψ := hs.toOpenPartialHomeomorph_coe
  let U : Set F := {y | AnalyticAt ℝ Ψ y ∧ ∃ j : F ≃L[ℝ] H, fderiv ℝ Ψ y = j}
  have hU : U ∈ 𝓝 a := by
    have h2 : ∀ᶠ y in 𝓝 a, ∃ j : F ≃L[ℝ] H, fderiv ℝ Ψ y = j := by
      have hc : ContinuousAt (fderiv ℝ Ψ) a := hΨ.fderiv.continuousAt
      have hr : range ((↑) : (F ≃L[ℝ] H) → F →L[ℝ] H) ∈ 𝓝 (fderiv ℝ Ψ a) := by
        rw [hi]
        exact i.nhds
      filter_upwards [hc hr] with y hy
      obtain ⟨j, hj⟩ := hy
      exact ⟨j, hj.symm⟩
    exact hΨ.eventually_analyticAt.and h2
  let e := e₀.restrOpen (interior U) isOpen_interior
  have hcoe : ⇑e = Ψ := he₀
  have hsrc : e.source = e₀.source ∩ interior U := e₀.restrOpen_source _ _
  refine ⟨e, ?_, hcoe, ?_⟩
  · rw [hsrc]
    exact ⟨hs.mem_toOpenPartialHomeomorph_source, mem_interior_iff_mem_nhds.mpr hU⟩
  · intro p hp
    have hy : e.symm p ∈ e.source := e.map_target hp
    have hyU : e.symm p ∈ U := by
      rw [hsrc] at hy
      exact interior_subset hy.2
    obtain ⟨j, hj⟩ := hyU.2
    have h := analyticAt_symm_of_fderiv_eq_equiv e hy (by rw [hcoe]; exact hyU.1) (i := j)
      (by rw [hcoe]; exact hj)
    rwa [e.right_inv hp] at h
end InverseFunction
section Convexity
variable {K : Type*} [NormedAddCommGroup K] [NormedSpace ℝ K]
theorem strictMin_of_pos_second_deriv (φ : K → ℝ) (φ₁ : K → K →L[ℝ] ℝ)
    (φ₂ : K → K →L[ℝ] K →L[ℝ] ℝ) {O : Set K} (hO : Convex ℝ O)
    (h₁ : ∀ x ∈ O, HasFDerivAt φ (φ₁ x) x) (h₂ : ∀ x ∈ O, HasFDerivAt φ₁ (φ₂ x) x)
    (hpos : ∀ x ∈ O, ∀ h : K, h ≠ 0 → 0 < φ₂ x h h) {x₀ x : K} (hx₀ : x₀ ∈ O) (hx : x ∈ O)
    (hcrit : φ₁ x₀ = 0) (hne : x ≠ x₀) : 0 < φ₁ x (x - x₀) ∧ φ x₀ < φ x := by
  obtain ⟨v, hv⟩ : ∃ v, v = x - x₀ := ⟨_, rfl⟩
  rw [← hv]
  have hv0 : v ≠ 0 := hv ▸ sub_ne_zero.mpr hne
  let γ : ℝ → K := fun t => x₀ + t • v
  have hγO : ∀ t ∈ Icc (0 : ℝ) 1, γ t ∈ O := fun t ht => by
    have := hO.add_smul_sub_mem hx₀ hx ht
    rwa [← hv] at this
  have hγ : ∀ t, HasDerivAt γ v t := fun t =>
    (((hasDerivAt_id t).smul_const v).const_add x₀).congr_deriv (one_smul ℝ v)
  let u : ℝ → ℝ := fun t => φ₁ (γ t) v
  let w : ℝ → ℝ := fun t => φ (γ t)
  have hu : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivAt u (φ₂ (γ t) v v) t := fun t ht => by
    have h := (h₂ _ (hγO t ht)).comp_hasDerivAt t (hγ t)
    exact ((ContinuousLinearMap.apply ℝ ℝ v).hasFDerivAt).comp_hasDerivAt t h
  have hw : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivAt w (u t) t := fun t ht =>
    (h₁ _ (hγO t ht)).comp_hasDerivAt t (hγ t)
  have hu_mono : StrictMonoOn u (Icc 0 1) := by
    refine strictMonoOn_of_deriv_pos (convex_Icc 0 1)
      (fun t ht => (hu t ht).continuousAt.continuousWithinAt) (fun t ht => ?_)
    have ht' := interior_subset ht
    rw [(hu t ht').deriv]
    exact hpos _ (hγO t ht') v hv0
  have hu0 : u 0 = 0 := by simp [u, γ, hcrit]
  have hu_pos : ∀ t ∈ Ioc (0 : ℝ) 1, 0 < u t := fun t ht => by
    have := hu_mono (left_mem_Icc.mpr zero_le_one) ⟨ht.1.le, ht.2⟩ ht.1
    rwa [hu0] at this
  have hw_mono : StrictMonoOn w (Icc 0 1) := by
    refine strictMonoOn_of_deriv_pos (convex_Icc 0 1)
      (fun t ht => (hw t ht).continuousAt.continuousWithinAt) (fun t ht => ?_)
    rw [interior_Icc] at ht
    rw [(hw t ⟨ht.1.le, ht.2.le⟩).deriv]
    exact hu_pos t ⟨ht.1, ht.2.le⟩
  have hγ1 : γ 1 = x := by simp [γ, hv]
  have hγ0 : γ 0 = x₀ := by simp [γ]
  refine ⟨?_, ?_⟩
  · have := hu_pos 1 ⟨zero_lt_one, le_rfl⟩
    simpa [u, hγ1] using this
  · have := hw_mono (left_mem_Icc.mpr zero_le_one) (right_mem_Icc.mpr zero_le_one) zero_lt_one
    simpa [w, hγ1, hγ0] using this
theorem eventually_pos_of_continuousAt_bilinear [FiniteDimensional ℝ K] {Y : Type*}
    [TopologicalSpace Y] (H : Y → K →L[ℝ] K →L[ℝ] ℝ) (y₀ : Y) (hH : ContinuousAt H y₀)
    (hpos : ∀ u : K, u ≠ 0 → 0 < H y₀ u u) : ∀ᶠ y in 𝓝 y₀, ∀ u : K, u ≠ 0 → 0 < H y u u := by
  have : ProperSpace K := FiniteDimensional.proper_real K
  have hS : IsCompact (sphere (0 : K) 1) := isCompact_sphere 0 1
  obtain ⟨κ, hκ, hmin⟩ : ∃ κ : ℝ, 0 < κ ∧ ∀ u ∈ sphere (0 : K) 1, κ ≤ H y₀ u u := by
    rcases (sphere (0 : K) 1).eq_empty_or_nonempty with he | hne
    · exact ⟨1, one_pos, by simp [he]⟩
    · have hc : ContinuousOn (fun u => H y₀ u u) (sphere (0 : K) 1) :=
        ((H y₀).continuous.clm_apply continuous_id).continuousOn
      obtain ⟨u₀, hu₀, hm⟩ := hS.exists_isMinOn hne hc
      refine ⟨H y₀ u₀ u₀, hpos u₀ ?_, fun u hu => hm hu⟩
      rintro rfl
      simp at hu₀
  have hev : ∀ᶠ y in 𝓝 y₀, ‖H y - H y₀‖ < κ := by
    filter_upwards [hH (ball_mem_nhds (H y₀) hκ)] with y hy
    rw [mem_preimage, mem_ball] at hy
    calc ‖H y - H y₀‖ = dist (H y) (H y₀) := (dist_eq_norm (H y) (H y₀)).symm
      _ < κ := hy
  filter_upwards [hev] with y hy u hu
  have hnu : 0 < ‖u‖ := norm_pos_iff.mpr hu
  obtain ⟨w, hwdef⟩ : ∃ w, w = ‖u‖⁻¹ • u := ⟨_, rfl⟩
  have hw : ‖w‖ = 1 := by
    rw [hwdef, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hnu.ne']
  have hmem : w ∈ sphere (0 : K) 1 := by simpa using hw
  have h1 := hmin w hmem
  have h2 : ‖(H y - H y₀) w w‖ ≤ ‖H y - H y₀‖ := by
    have := (H y - H y₀).le_opNorm₂ w w
    rwa [hw, mul_one, mul_one] at this
  have h3 : 0 < H y w w := by
    have h4 : (H y - H y₀) w w = H y w w - H y₀ w w := by simp
    rw [h4, Real.norm_eq_abs] at h2
    have := abs_le.mp (h2.trans le_rfl)
    linarith [this.1]
  have hu' : u = ‖u‖ • w := by rw [hwdef, smul_smul, mul_inv_cancel₀ hnu.ne', one_smul]
  have h5 : H y u u = ‖u‖ * (‖u‖ * H y w w) := by
    calc H y u u = H y (‖u‖ • w) (‖u‖ • w) := by rw [← hu']
      _ = _ := by simp only [map_smul, smul_apply, smul_eq_mul]
  rw [h5]
  positivity
end Convexity
section LocalMinimizers
variable {K G E : Type*} [NormedAddCommGroup K] [NormedSpace ℝ K] [FiniteDimensional ℝ K]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
theorem exists_fiber_minimizers (C : K × G → E) (f : E → ℝ) (ι : K →L[ℝ] E)
    (hC : AnalyticAt ℝ C 0) (hC0 : C 0 = 0) (hf : AnalyticAt ℝ f 0) (hcrit : fderiv ℝ f 0 = 0)
    (hι : ∀ ξ : K, fderiv ℝ C 0 (ξ, 0) = ι ξ)
    (hpos : ∀ ξ : K, ξ ≠ 0 → 0 < fderiv ℝ (fderiv ℝ f) 0 (ι ξ) (ι ξ))
    {P : Set (K × G)} (hP : P ∈ 𝓝 (0 : K × G)) :
    ∃ (r r' : ℝ) (b : G → K) (D : G →L[ℝ] E), 0 < r ∧ 0 < r' ∧
      ball (0 : K) r ×ˢ ball (0 : G) r' ⊆ P ∧
      AnalyticOnNhd ℝ b (ball 0 r') ∧ b 0 = 0 ∧ (∀ Z ∈ ball (0 : G) r', b Z ∈ ball (0 : K) r) ∧
      (∀ Z ∈ ball (0 : G) r', ∀ x ∈ ball (0 : K) r, ∀ h : K, h ≠ 0 →
        0 < fderiv ℝ (fderiv ℝ fun x => f (C (x, Z))) x h h) ∧
      (∀ Z ∈ ball (0 : G) r', fderiv ℝ (fun x => f (C (x, Z))) (b Z) = 0) ∧
      (∀ Z ∈ ball (0 : G) r', ∀ x ∈ ball (0 : K) r,
        fderiv ℝ (fun x => f (C (x, Z))) x = 0 → x = b Z) ∧
      (∀ Z ∈ ball (0 : G) r', ∀ x ∈ ball (0 : K) r, x ≠ b Z → f (C (b Z, Z)) < f (C (x, Z))) ∧
      HasFDerivAt (fun Z => C (b Z, Z)) D 0 ∧
      ∀ (Z : G) (ξ : K), fderiv ℝ (fderiv ℝ f) 0 (D Z) (ι ξ) = 0 := by
  have : CompleteSpace K := FiniteDimensional.complete ℝ K
  have : CompleteSpace G := FiniteDimensional.complete ℝ G
  have : CompleteSpace E := FiniteDimensional.complete ℝ E
  let g : K × G → ℝ := fun p => f (C p)
  let inl' : K →L[ℝ] K × G := ContinuousLinearMap.inl ℝ K G
  let R : (K × G →L[ℝ] ℝ) →L[ℝ] K →L[ℝ] ℝ :=
    (ContinuousLinearMap.compL ℝ K (K × G) ℝ).flip inl'
  let R₂ : (K × G →L[ℝ] K →L[ℝ] ℝ) →L[ℝ] K →L[ℝ] K →L[ℝ] ℝ :=
    (ContinuousLinearMap.compL ℝ K (K × G) (K →L[ℝ] ℝ)).flip inl'
  let Rc : (K × G →L[ℝ] E) →L[ℝ] K →L[ℝ] E :=
    (ContinuousLinearMap.compL ℝ K (K × G) E).flip inl'
  let Q : K × G → K →L[ℝ] ℝ := fun p => R (fderiv ℝ g p)
  let H : K × G → K →L[ℝ] K →L[ℝ] ℝ := fun p => R₂ (fderiv ℝ Q p)
  have hfC : AnalyticAt ℝ f (C 0) := by rwa [hC0]
  have hg : AnalyticAt ℝ g 0 := hfC.comp hC
  have hQ : AnalyticAt ℝ Q 0 := (R.analyticAt _).comp hg.fderiv
  have hHc : ContinuousAt H 0 := R₂.continuous.continuousAt.comp hQ.fderiv.continuousAt
  have hQform : ∀ᶠ p in 𝓝 (0 : K × G),
      Q p = (fderiv ℝ f (C p)).comp ((fderiv ℝ C p).comp inl') := by
    have hfev : ∀ᶠ p in 𝓝 (0 : K × G), AnalyticAt ℝ f (C p) :=
      hC.continuousAt.eventually hfC.eventually_analyticAt
    filter_upwards [hfev, hC.eventually_analyticAt] with p h1 h2
    have h3 : fderiv ℝ g p = (fderiv ℝ f (C p)).comp (fderiv ℝ C p) :=
      fderiv_comp p h1.differentiableAt h2.differentiableAt
    show R (fderiv ℝ g p) = _
    rw [h3]
    rfl
  have hQ0 : Q 0 = 0 := by
    rw [hQform.self_of_nhds, hC0, hcrit]
    simp
  have hA : ∀ (v : K × G) (ξ : K),
      fderiv ℝ Q 0 v ξ = fderiv ℝ (fderiv ℝ f) 0 (fderiv ℝ C 0 v) (ι ξ) := by
    have h1 : HasFDerivAt (fderiv ℝ f) (fderiv ℝ (fderiv ℝ f) 0) (C 0) := by
      rw [hC0]
      exact hf.fderiv.differentiableAt.hasFDerivAt
    have hD : HasFDerivAt (fun p => fderiv ℝ f (C p))
        ((fderiv ℝ (fderiv ℝ f) 0).comp (fderiv ℝ C 0)) (0 : K × G) :=
      h1.comp 0 hC.differentiableAt.hasFDerivAt
    have hB : DifferentiableAt ℝ (fun p => (fderiv ℝ C p).comp inl') (0 : K × G) :=
      ((Rc.analyticAt _).comp hC.fderiv).differentiableAt
    have hQd := ((hD.clm_comp hB.hasFDerivAt).congr_of_eventuallyEq hQform).fderiv
    intro v ξ
    rw [hQd]
    simp [hC0, hcrit, inl', hι]
  have hH0 : ∀ u : K, u ≠ 0 → 0 < H 0 u u := by
    intro u hu
    have h1 : H 0 u u = fderiv ℝ Q 0 (u, 0) u := rfl
    rw [h1, hA, hι]
    exact hpos u hu
  let Φ : K × G → (K →L[ℝ] ℝ) × G := fun p => (Q p, p.2)
  have hΦ : AnalyticAt ℝ Φ 0 := hQ.prod analyticAt_snd
  let T : K × G →L[ℝ] (K →L[ℝ] ℝ) × G := (fderiv ℝ Q 0).prod (ContinuousLinearMap.snd ℝ K G)
  have hΦd : fderiv ℝ Φ 0 = T := (hQ.differentiableAt.hasFDerivAt.prodMk hasFDerivAt_snd).fderiv
  have hTinj : Function.Injective T := by
    rw [injective_iff_map_eq_zero]
    rintro ⟨h, Z⟩ hT
    have h1 : fderiv ℝ Q 0 (h, Z) = 0 := congrArg Prod.fst hT
    have h2 : Z = 0 := congrArg Prod.snd hT
    subst h2
    by_contra hne
    have hne' : h ≠ 0 := fun hh => hne (by simp [hh])
    have h3 := hA (h, 0) h
    rw [h1, hι] at h3
    have h4 := hpos h hne'
    rw [← h3] at h4
    simp at h4
  have hfin : Module.Finite ℝ (K →L[ℝ] ℝ) :=
    Module.Finite.equiv (LinearMap.toContinuousLinearMap (𝕜 := ℝ) (E := K) (F' := ℝ))
  have hdim : Module.finrank ℝ (K × G) = Module.finrank ℝ ((K →L[ℝ] ℝ) × G) := by
    rw [Module.finrank_prod, Module.finrank_prod]
    congr 1
    rw [← (LinearMap.toContinuousLinearMap (𝕜 := ℝ) (E := K) (F' := ℝ)).finrank_eq]
    exact Subspace.dual_finrank_eq.symm
  let i : (K × G) ≃L[ℝ] (K →L[ℝ] ℝ) × G :=
    (LinearMap.linearEquivOfInjective (T : K × G →ₗ[ℝ] (K →L[ℝ] ℝ) × G) hTinj
      hdim).toContinuousLinearEquiv
  have hi : fderiv ℝ Φ 0 = i := by
    rw [hΦd]
    exact ContinuousLinearMap.ext fun v => rfl
  obtain ⟨e, he0, hecoe, hean⟩ := exists_openPartialHomeomorph_analytic_inverse Φ 0 hΦ i hi
  have he00 : e 0 = 0 := by
    rw [hecoe]
    exact Prod.ext hQ0 rfl
  have htar0 : (0 : (K →L[ℝ] ℝ) × G) ∈ e.target := by
    rw [← he00]
    exact e.map_source he0
  have hsymm0 : e.symm 0 = 0 := by
    rw [← he00]
    exact e.left_inv he0
  let ψ : G → (K →L[ℝ] ℝ) × G := fun Z => (0, Z)
  have hψ : ∀ Z, AnalyticAt ℝ ψ Z := fun Z => analyticAt_const.prod analyticAt_id
  have hψ0 : ψ 0 = 0 := rfl
  let b : G → K := fun Z => (e.symm (ψ Z)).1
  have htarZ : ∀ᶠ Z in 𝓝 (0 : G), ψ Z ∈ e.target :=
    (hψ 0).continuousAt (by rw [hψ0]; exact e.open_target.mem_nhds htar0)
  have hbZ : ∀ Z, ψ Z ∈ e.target → Q (b Z, Z) = 0 := by
    intro Z hZ
    have h1 : e (e.symm (ψ Z)) = ψ Z := e.right_inv hZ
    rw [hecoe] at h1
    have h2 : (e.symm (ψ Z)).2 = Z := congrArg Prod.snd h1
    have h3 : e.symm (ψ Z) = (b Z, Z) := Prod.ext rfl h2
    have h4 : Q (e.symm (ψ Z)) = 0 := congrArg Prod.fst h1
    rwa [h3] at h4
  have hbAn : ∀ Z, ψ Z ∈ e.target → AnalyticAt ℝ b Z := fun Z hZ =>
    ((ContinuousLinearMap.fst ℝ K G).analyticAt _).comp ((hean _ hZ).comp (hψ Z))
  have hb0 : b 0 = 0 := by
    show (e.symm (ψ 0)).1 = 0
    rw [hψ0, hsymm0]
    rfl
  let P' : Set (K × G) := {p | p ∈ P ∧ AnalyticAt ℝ g p ∧ AnalyticAt ℝ Q p ∧
    ∀ u : K, u ≠ 0 → 0 < H p u u}
  have hP' : P' ∈ 𝓝 (0 : K × G) := by
    filter_upwards [hP, hg.eventually_analyticAt, hQ.eventually_analyticAt,
      eventually_pos_of_continuousAt_bilinear H 0 hHc hH0] with p a1 a2 a3 a4
      using ⟨a1, a2, a3, a4⟩
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp hP'
  have hbc : ContinuousAt b 0 := (hbAn 0 htarZ.self_of_nhds).continuousAt
  have hbr : ∀ᶠ Z in 𝓝 (0 : G), b Z ∈ ball (0 : K) r :=
    hbc (by rw [hb0]; exact ball_mem_nhds _ hr)
  have hW : ∀ᶠ Z in 𝓝 (0 : G), ψ Z ∈ e.target ∧ b Z ∈ ball (0 : K) r ∧ Z ∈ ball (0 : G) r :=
    htarZ.and (hbr.and (ball_mem_nhds _ hr))
  obtain ⟨r₁, hr₁, hW'⟩ := Metric.mem_nhds_iff.mp hW
  have hsub : ∀ x ∈ ball (0 : K) r, ∀ Z ∈ ball (0 : G) r₁, (x, Z) ∈ P' := fun x hx Z hZ =>
    hball (by
      rw [← Prod.mk_zero_zero, ← ball_prod_same]
      exact ⟨hx, (hW' hZ).2.2⟩)
  have hd1 : ∀ Z ∈ ball (0 : G) r₁, ∀ x ∈ ball (0 : K) r,
      HasFDerivAt (fun x => f (C (x, Z))) (Q (x, Z)) x := by
    intro Z hZ x hx
    have h := (hsub x hx Z hZ).2.1.differentiableAt.hasFDerivAt
    exact HasFDerivAt.comp (f := fun y : K => (y, Z)) x h (hasFDerivAt_prodMk_left x Z)
  have hd2 : ∀ Z ∈ ball (0 : G) r₁, ∀ x ∈ ball (0 : K) r,
      HasFDerivAt (fderiv ℝ fun x => f (C (x, Z))) (H (x, Z)) x := by
    intro Z hZ x hx
    have h := (hsub x hx Z hZ).2.2.1.differentiableAt.hasFDerivAt
    have h' : HasFDerivAt (fun x => Q (x, Z)) (H (x, Z)) x :=
      HasFDerivAt.comp (f := fun y : K => (y, Z)) x h (hasFDerivAt_prodMk_left x Z)
    refine h'.congr_of_eventuallyEq ?_
    filter_upwards [isOpen_ball.mem_nhds hx] with y hy using (hd1 Z hZ y hy).fderiv
  have hcritZ : ∀ Z ∈ ball (0 : G) r₁, Q (b Z, Z) = 0 := fun Z hZ => hbZ Z (hW' hZ).1
  have hmin : ∀ Z ∈ ball (0 : G) r₁, ∀ x ∈ ball (0 : K) r, x ≠ b Z →
      0 < Q (x, Z) (x - b Z) ∧ f (C (b Z, Z)) < f (C (x, Z)) := fun Z hZ x hx hne =>
    strictMin_of_pos_second_deriv (fun x => f (C (x, Z))) (fun x => Q (x, Z))
      (fun x => H (x, Z)) (convex_ball 0 r) (hd1 Z hZ)
      (fun y hy => by
        have h := (hsub y hy Z hZ).2.2.1.differentiableAt.hasFDerivAt
        exact HasFDerivAt.comp (f := fun y : K => (y, Z)) y h (hasFDerivAt_prodMk_left y Z))
      (fun y hy => (hsub y hy Z hZ).2.2.2) (hW' hZ).2.1 hx (hcritZ Z hZ) hne
  have hbd : HasFDerivAt b (fderiv ℝ b 0) 0 :=
    (hbAn 0 htarZ.self_of_nhds).differentiableAt.hasFDerivAt
  let S : G →L[ℝ] K × G := (fderiv ℝ b 0).prod (ContinuousLinearMap.id ℝ G)
  have hβ : HasFDerivAt (fun Z => (b Z, Z)) S 0 := hbd.prodMk (hasFDerivAt_id 0)
  have hβ0 : ((b 0, 0) : K × G) = 0 := Prod.ext hb0 rfl
  have hC1 : HasFDerivAt C (fderiv ℝ C 0) ((b 0, 0) : K × G) := by
    rw [hβ0]
    exact hC.differentiableAt.hasFDerivAt
  have hQ1 : HasFDerivAt Q (fderiv ℝ Q 0) ((b 0, 0) : K × G) := by
    rw [hβ0]
    exact hQ.differentiableAt.hasFDerivAt
  have hQβ : HasFDerivAt (fun Z => Q (b Z, Z)) ((fderiv ℝ Q 0).comp S) 0 :=
    HasFDerivAt.comp (f := fun Z => (b Z, Z)) 0 hQ1 hβ
  have hzero : (fun _ : G => (0 : K →L[ℝ] ℝ)) =ᶠ[𝓝 0] fun Z => Q (b Z, Z) := by
    filter_upwards [htarZ] with Z hZ using (hbZ Z hZ).symm
  have hQS : (fderiv ℝ Q 0).comp S = 0 :=
    (hQβ.congr_of_eventuallyEq hzero).unique (hasFDerivAt_const _ _)
  refine ⟨r, r₁, b, (fderiv ℝ C 0).comp S, hr, hr₁, ?_, ?_, hb0, ?_, ?_, ?_, ?_, ?_,
    HasFDerivAt.comp (f := fun Z => (b Z, Z)) 0 hC1 hβ, ?_⟩
  · rintro ⟨x, Z⟩ ⟨hx, hZ⟩
    exact (hsub x hx Z hZ).1
  · exact fun Z hZ => hbAn Z (hW' hZ).1
  · exact fun Z hZ => (hW' hZ).2.1
  · intro Z hZ x hx h hh
    rw [(hd2 Z hZ x hx).fderiv]
    exact (hsub x hx Z hZ).2.2.2 h hh
  · intro Z hZ
    rw [(hd1 Z hZ _ (hW' hZ).2.1).fderiv]
    exact hcritZ Z hZ
  · intro Z hZ x hx hcr
    by_contra hne
    have h1 := (hmin Z hZ x hx hne).1
    rw [← (hd1 Z hZ x hx).fderiv, hcr] at h1
    simp at h1
  · exact fun Z hZ x hx hne => (hmin Z hZ x hx hne).2
  · intro Z ξ
    have h1 := hA (S Z) ξ
    have h2 : fderiv ℝ Q 0 (S Z) = 0 := by
      have := DFunLike.congr_fun hQS Z
      simpa using this
    rw [h2] at h1
    simpa using h1.symm
end LocalMinimizers
theorem existsMinimizerChart_holds : ExistsMinimizerChart := by
  intro E G _ _ _ _ _ _ m f hc T hT
  have : CompleteSpace E := FiniteDimensional.complete ℝ E
  have : CompleteSpace G := FiniteDimensional.complete ℝ G
  let K : Submodule ℝ E := tangentKernel m
  have : CompleteSpace K := FiniteDimensional.complete ℝ K
  let L : E →L[ℝ] G := fderiv ℝ m 0
  have hK : ∀ k : K, L (k : E) = 0 := fun k => k.2
  obtain ⟨p, hp⟩ := K.subtype.exists_leftInverse_of_injective (Submodule.ker_subtype K)
  let ρ : E →L[ℝ] K := LinearMap.toContinuousLinearMap p
  have hρ : ∀ x : K, ρ (x : E) = x := fun x => LinearMap.congr_fun hp x
  let Ψ : E → K × G := fun y => (ρ y, m y)
  have hΨ : AnalyticAt ℝ Ψ 0 := (ρ.analyticAt 0).prod hc.analyticAt_map
  let T₀ : E →L[ℝ] K × G := ρ.prod L
  have hΨd : HasFDerivAt Ψ T₀ 0 :=
    ρ.hasFDerivAt.prodMk hc.analyticAt_map.differentiableAt.hasFDerivAt
  have hinj : Function.Injective T₀ := by
    rw [injective_iff_map_eq_zero]
    intro y hy
    have h1 : ρ y = 0 := congrArg Prod.fst hy
    have h2 : L y = 0 := congrArg Prod.snd hy
    have h3 : ρ y = (⟨y, h2⟩ : K) := hρ ⟨y, h2⟩
    rw [h1] at h3
    exact (congrArg Subtype.val h3).symm
  have hsurj : Function.Surjective T₀ := by
    rintro ⟨x, Z⟩
    obtain ⟨y₀, hy₀⟩ := hc.fderiv_surjective Z
    refine ⟨y₀ + (x : E) - (ρ y₀ : E), Prod.ext ?_ ?_⟩
    · show ρ (y₀ + (x : E) - (ρ y₀ : E)) = x
      rw [map_sub, map_add, hρ, hρ]
      abel
    · show L (y₀ + (x : E) - (ρ y₀ : E)) = Z
      rw [map_sub, map_add, hK, hK, add_zero, sub_zero]
      exact hy₀
  let i : E ≃L[ℝ] K × G :=
    (LinearEquiv.ofBijective (T₀ : E →ₗ[ℝ] K × G) ⟨hinj, hsurj⟩).toContinuousLinearEquiv
  have hiT : (i : E →L[ℝ] K × G) = T₀ := ContinuousLinearMap.ext fun v => rfl
  obtain ⟨e, he0, hecoe, hean⟩ :=
    exists_openPartialHomeomorph_analytic_inverse Ψ 0 hΨ i (by rw [hΨd.fderiv, hiT])
  have he00 : e 0 = 0 := by
    rw [hecoe]
    exact Prod.ext (map_zero ρ) hc.map_zero
  have htar : (0 : K × G) ∈ e.target := by
    rw [← he00]
    exact e.map_source he0
  have hsymm0 : e.symm 0 = 0 := by
    rw [← he00]
    exact e.left_inv he0
  have hCd : HasFDerivAt e.symm (i.symm : K × G →L[ℝ] E) 0 := by
    apply e.hasFDerivAt_symm htar
    rw [hsymm0, hecoe, hiT]
    exact hΨd
  have hι : ∀ ξ : K, fderiv ℝ e.symm 0 (ξ, 0) = K.subtypeL ξ := by
    intro ξ
    rw [hCd.fderiv]
    have h1 : i (ξ : E) = (ξ, 0) := Prod.ext (hρ ξ) (hK ξ)
    show i.symm (ξ, 0) = (ξ : E)
    rw [← h1]
    exact i.symm_apply_apply _
  have hCc : ContinuousAt e.symm (0 : K × G) := (hean 0 htar).continuousAt
  have hT' : ∀ᶠ y in 𝓝 (e.symm (0 : K × G)), y ∈ T := by rwa [hsymm0]
  have hm' : ∀ᶠ y in 𝓝 (e.symm (0 : K × G)), AnalyticAt ℝ m y := by
    rw [hsymm0]
    exact hc.analyticAt_map.eventually_analyticAt
  have hf' : ∀ᶠ y in 𝓝 (e.symm (0 : K × G)), AnalyticAt ℝ f y := by
    rw [hsymm0]
    exact hc.analyticAt_fun.eventually_analyticAt
  let P : Set (K × G) := {p | p ∈ e.target ∧ e.symm p ∈ T ∧ AnalyticAt ℝ m (e.symm p) ∧
    AnalyticAt ℝ f (e.symm p)}
  have hP : P ∈ 𝓝 (0 : K × G) := by
    filter_upwards [e.open_target.mem_nhds htar, hCc.eventually hT', hCc.eventually hm',
      hCc.eventually hf'] with p a1 a2 a3 a4 using ⟨a1, a2, a3, a4⟩
  obtain ⟨r, r', b, D, hr, hr', hsub, hban, hb0, hbmem, hposZ, hcritZ, honly, hleast, hDd, horth⟩ :=
    exists_fiber_minimizers e.symm f K.subtypeL (hean 0 htar) hsymm0 hc.analyticAt_fun
      hc.fderiv_eq_zero hι (fun ξ hξ => hc.hessian_pos ξ ξ.2 (by simpa using hξ)) hP
  let O : Set K := ball 0 r
  let W : Set G := ball 0 r'
  let N : Set E := e.source ∩ e ⁻¹' (O ×ˢ W)
  let c : K → G → E := fun x Z => e.symm (x, Z)
  have hOW : IsOpen (O ×ˢ W) := isOpen_ball.prod isOpen_ball
  have h0O : (0 : K) ∈ O := mem_ball_self hr
  have h0W : (0 : G) ∈ W := mem_ball_self hr'
  have hNP : ∀ y ∈ N, e y ∈ P := fun y hy => hsub hy.2
  have hNsymm : ∀ y ∈ N, e.symm (e y) = y := fun y hy => e.left_inv hy.1
  have hPt : ∀ x ∈ O, ∀ Z ∈ W, (x, Z) ∈ e.target := fun x hx Z hZ => (hsub ⟨hx, hZ⟩).1
  have hΨc : ∀ x ∈ O, ∀ Z ∈ W, Ψ (c x Z) = (x, Z) := fun x hx Z hZ => by
    have h := e.right_inv (hPt x hx Z hZ)
    rwa [hecoe] at h
  have hlevel : ∀ x ∈ O, ∀ Z ∈ W, m (c x Z) = Z := fun x hx Z hZ =>
    congrArg Prod.snd (hΨc x hx Z hZ)
  have hS0 : fiberMinimizer c b 0 = 0 := by
    show e.symm (b 0, 0) = 0
    rw [hb0]
    exact hsymm0
  have hDd' : HasFDerivAt (fiberMinimizer c b) D 0 := hDd
  refine ⟨N, O, W, ρ, c, b, ?_, ?_⟩
  · exact
      { isOpen_nhd := e.isOpen_inter_preimage hOW
        zero_mem_nhd := ⟨he0, by rw [mem_preimage, he00]; exact ⟨h0O, h0W⟩⟩
        isOpen_params := isOpen_ball
        zero_mem_params := h0O
        convex_params := convex_ball 0 r
        isOpen_values := isOpen_ball
        zero_mem_values := h0W
        analyticOnNhd_map := fun y hy => by
          have h := (hNP y hy).2.2.1
          rwa [hNsymm y hy] at h
        analyticOnNhd_fun := fun y hy => by
          have h := (hNP y hy).2.2.2
          rwa [hNsymm y hy] at h
        proj_apply_kernel := hρ
        analyticOnNhd_chart := fun q hq => hean q (hsub hq).1
        chart_zero_zero := hsymm0
        chart_mem_nhd := fun x hx Z hZ => ⟨e.map_target (hPt x hx Z hZ), by
          rw [mem_preimage, e.right_inv (hPt x hx Z hZ)]
          exact ⟨hx, hZ⟩⟩
        map_chart := hlevel
        proj_chart := fun x hx Z hZ => congrArg Prod.fst (hΨc x hx Z hZ)
        chart_surj := fun y hy => by
          have h : e y = (ρ y, m y) := by rw [hecoe]
          have h1 := hy.2
          rw [mem_preimage, h] at h1
          refine ⟨h1.1, h1.2, ?_⟩
          show e.symm (ρ y, m y) = y
          rw [← h]
          exact hNsymm y hy
        hessian_pos_params := hposZ
        analyticOnNhd_min := hban
        min_zero := hb0
        min_mem := hbmem
        fderiv_min_eq_zero := hcritZ
        eq_min_of_critical := honly
        min_lt := hleast
        fderiv_section := fun Z => by
          have hm1 : HasFDerivAt m (fderiv ℝ m 0) (fiberMinimizer c b 0) := by
            rw [hS0]
            exact hc.analyticAt_map.differentiableAt.hasFDerivAt
          have hcomp := hm1.comp 0 hDd'
          have hid : (fun Z : G => Z) =ᶠ[𝓝 0] m ∘ fiberMinimizer c b := by
            filter_upwards [isOpen_ball.mem_nhds h0W] with Z' hZ'
            exact (hlevel _ (hbmem Z' hZ') Z' hZ').symm
          have h2 := (hcomp.congr_of_eventuallyEq hid).unique (hasFDerivAt_id 0)
          rw [hDd'.fderiv]
          exact DFunLike.congr_fun h2 Z
        hessian_orthogonal := fun Z ξ => by
          rw [hDd'.fderiv]
          exact horth Z ξ }
  · intro y hy
    have h := (hNP y hy).2.1
    rwa [hNsymm y hy] at h
end YangMills.Construction.ConstrainedMinima
