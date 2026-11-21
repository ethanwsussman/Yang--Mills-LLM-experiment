import YangMills.Construction.Coordinates.PowerSeriesHolomorphy
import YangMills.Construction.Lattice.DerivativeOfAHolomorphicMapAndOpenBalls
import YangMills.Construction.Matrices.ExpLogEstimates
import YangMills.Construction.Matrices.FiniteMatrixProducts
import YangMills.Construction.Towers.SecondDifferentialInTheLeftChart
import Mathlib
set_option autoImplicit false
open Filter Set
open scoped Topology ContDiff Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction.Tower.LeftChartSecondDerivative
section Abstract
variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {V E : Type*} [NormedAddCommGroup V] [NormedSpace 𝕜 V] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable (𝕜) in
structure SymmetricSecondDerivAtZero (g : V → E) : Prop where
  near : ∀ᶠ y in 𝓝 (0 : V), DifferentiableAt 𝕜 g y
  second : DifferentiableAt 𝕜 (fderiv 𝕜 g) 0
  symm : ∀ v w, fderiv 𝕜 (fderiv 𝕜 g) 0 v w = fderiv 𝕜 (fderiv 𝕜 g) 0 w v
theorem mixedDeriv_eq_second {g : V → E} (hg : SymmetricSecondDerivAtZero 𝕜 g)
    (F : 𝕜 → 𝕜 → E) (v v' : V)
    (hF : ∀ᶠ p : 𝕜 × 𝕜 in 𝓝 0, F p.1 p.2 = g (p.1 • v + p.2 • v')) :
    (∀ᶠ p : 𝕜 × 𝕜 in 𝓝 0, DifferentiableAt 𝕜 (F p.1) p.2) ∧
      DifferentiableAt 𝕜 (fun s => deriv (F s) 0) 0 ∧
      deriv (fun s => deriv (F s) 0) 0 = fderiv 𝕜 (fderiv 𝕜 g) 0 v v' := by
  have hcont : Continuous fun p : 𝕜 × 𝕜 => p.1 • v + p.2 • v' := by fun_prop
  have hnear : ∀ᶠ p : 𝕜 × 𝕜 in 𝓝 0, DifferentiableAt 𝕜 g (p.1 • v + p.2 • v') := by
    have h := hcont.tendsto (0 : 𝕜 × 𝕜)
    simp only [Prod.fst_zero, Prod.snd_zero, zero_smul, add_zero] at h
    exact h.eventually hg.near
  have hder : ∀ᶠ p : 𝕜 × 𝕜 in 𝓝 0,
      HasDerivAt (F p.1) (fderiv 𝕜 g (p.1 • v + p.2 • v') v') p.2 := by
    filter_upwards [hF.eventually_nhds, hnear] with p hp hd
    have hline : HasDerivAt (fun t : 𝕜 => p.1 • v + t • v') v' p.2 := by
      simpa using ((hasDerivAt_id p.2).smul_const v').const_add (p.1 • v)
    have hcomp : HasDerivAt (fun t : 𝕜 => g (p.1 • v + t • v'))
        (fderiv 𝕜 g (p.1 • v + p.2 • v') v') p.2 :=
      hd.hasFDerivAt.comp_hasDerivAt p.2 hline
    have hc : ContinuousAt (fun t : 𝕜 => (p.1, t)) p.2 := by fun_prop
    have heq : (F p.1) =ᶠ[𝓝 p.2] fun t => g (p.1 • v + t • v') := hc.eventually hp
    exact hcomp.congr_of_eventuallyEq heq
  have hs : ∀ᶠ s : 𝕜 in 𝓝 0, deriv (F s) 0 = fderiv 𝕜 g (s • v) v' := by
    have hc : Tendsto (fun s : 𝕜 => (s, (0 : 𝕜))) (𝓝 0) (𝓝 (0 : 𝕜 × 𝕜)) := by
      have h : Continuous fun s : 𝕜 => (s, (0 : 𝕜)) := by fun_prop
      exact h.tendsto 0
    filter_upwards [hc.eventually hder] with s h
    simpa using h.deriv
  have hline : HasDerivAt (fun s : 𝕜 => s • v) v 0 := by
    simpa using (hasDerivAt_id (0 : 𝕜)).smul_const v
  have h2 : HasFDerivAt (fderiv 𝕜 g) (fderiv 𝕜 (fderiv 𝕜 g) 0) ((0 : 𝕜) • v) := by
    simpa using hg.second.hasFDerivAt
  have hD : HasDerivAt (fun s : 𝕜 => fderiv 𝕜 g (s • v)) (fderiv 𝕜 (fderiv 𝕜 g) 0 v) 0 :=
    h2.comp_hasDerivAt 0 hline
  have hA : HasDerivAt (fun s : 𝕜 => fderiv 𝕜 g (s • v) v') (fderiv 𝕜 (fderiv 𝕜 g) 0 v v') 0 := by
    simpa using hD.clm_apply (hasDerivAt_const (0 : 𝕜) v')
  have hB := hA.congr_of_eventuallyEq hs
  exact ⟨hder.mono fun p h => h.differentiableAt, hB.differentiableAt, hB.deriv⟩
theorem differentiableAt_clm_of_basis {X F : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F] {m : ℕ} (A : X → (Fin m → 𝕜) →L[𝕜] F) {x₀ : X}
    (h : ∀ k, DifferentiableAt 𝕜 (fun x => A x (Pi.single k 1)) x₀) :
    DifferentiableAt 𝕜 A x₀ := by
  have hA : A = fun x => ∑ k, (ContinuousLinearMap.proj k : (Fin m → 𝕜) →L[𝕜] 𝕜).smulRight
      (A x (Pi.single k 1)) := by
    funext x
    apply ContinuousLinearMap.ext
    intro w
    have hw : w = ∑ k, w k • (Pi.single k (1 : 𝕜) : Fin m → 𝕜) := by
      ext j
      simp [Finset.sum_apply, Pi.single_apply]
    conv_lhs => rw [hw]
    simp [map_sum]
  rw [hA]
  apply DifferentiableAt.fun_sum
  intro k _
  exact (ContinuousLinearMap.smulRightL 𝕜 (Fin m → 𝕜) F
    (ContinuousLinearMap.proj k)).differentiableAt.comp x₀ (h k)
end Abstract
section Facts
variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [NormedAlgebra 𝕜 ℂ]
  {V E : Type*} [NormedAddCommGroup V] [NormedSpace 𝕜 V] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {α : Type*} {N : ℕ}
theorem mixedPartialProperties_of_factor {O : Set (Fin N → Matrices.ComplexMatrix2)}
    {f : (Fin N → Matrices.ComplexMatrix2) → E} {b : Fin N → α}
    {U : α → Matrices.ComplexMatrix2} {𝒮 𝒯 : Set (α → Matrices.ComplexMatrix2)} (h𝒮 : 𝒮 ⊆ 𝒯)
    (hclosed : ∀ B₁ ∈ 𝒯, ∀ B₂ ∈ 𝒯, ∀ c : 𝕜, algebraMap 𝕜 ℂ c • B₁ + B₂ ∈ 𝒯)
    {ℓ : (α → Matrices.ComplexMatrix2) → V}
    (hlin : ∀ B₁ ∈ 𝒯, ∀ B₂ ∈ 𝒯, ∀ c : 𝕜, ℓ (algebraMap 𝕜 ℂ c • B₁ + B₂) = c • ℓ B₁ + ℓ B₂)
    (hloc : ∀ B₁ ∈ 𝒯, ∀ B₂ ∈ 𝒯, (∀ i, B₁ (b i) = B₂ (b i)) → ℓ B₁ = ℓ B₂)
    {g : V → E} (hg : SymmetricSecondDerivAtZero 𝕜 g)
    (hval : ∀ B ∈ 𝒯, ∀ B' ∈ 𝒯, ∀ᶠ p : 𝕜 × 𝕜 in 𝓝 0,
      chartPoint b U (algebraMap 𝕜 ℂ p.1 • B + algebraMap 𝕜 ℂ p.2 • B') ∈ O ∧
        chartValue f b U (algebraMap 𝕜 ℂ p.1 • B + algebraMap 𝕜 ℂ p.2 • B') =
          g (p.1 • ℓ B + p.2 • ℓ B')) :
    MixedPartialProperties 𝕜 𝒮 O f b U := by
  have key : ∀ B ∈ 𝒯, ∀ B' ∈ 𝒯, MixedPartialExists 𝕜 O f b U B B' ∧
      mixedAt 𝕜 f b U B B' = fderiv 𝕜 (fderiv 𝕜 g) 0 (ℓ B) (ℓ B') := by
    intro B hB B' hB'
    obtain ⟨h₁, h₂, h₃⟩ := mixedDeriv_eq_second hg
      (fun s t => chartValue f b U (algebraMap 𝕜 ℂ s • B + algebraMap 𝕜 ℂ t • B')) (ℓ B) (ℓ B')
      ((hval B hB B' hB').mono fun p h => h.2)
    exact ⟨⟨(hval B hB B' hB').mono fun p h => h.1, h₁, h₂⟩, h₃⟩
  have hm := fun B hB B' hB' => (key B hB B' hB').2
  refine ⟨fun B hB B' hB' => (key B (h𝒮 hB) B' (h𝒮 hB')).1, ?_, ?_, ?_, ?_⟩
  · intro B₁ h₁ B₂ h₂ B' h' c
    rw [hm _ (hclosed _ (h𝒮 h₁) _ (h𝒮 h₂) c) _ (h𝒮 h'), hm _ (h𝒮 h₁) _ (h𝒮 h'),
      hm _ (h𝒮 h₂) _ (h𝒮 h'), hlin _ (h𝒮 h₁) _ (h𝒮 h₂)]
    simp
  · intro B hB B₁ h₁ B₂ h₂ c
    rw [hm _ (h𝒮 hB) _ (hclosed _ (h𝒮 h₁) _ (h𝒮 h₂) c), hm _ (h𝒮 hB) _ (h𝒮 h₁),
      hm _ (h𝒮 hB) _ (h𝒮 h₂), hlin _ (h𝒮 h₁) _ (h𝒮 h₂)]
    simp
  · intro B hB B' hB'
    rw [hm _ (h𝒮 hB) _ (h𝒮 hB'), hm _ (h𝒮 hB') _ (h𝒮 hB), hg.symm]
  · intro B₁ h₁ B₂ h₂ B₁' h₁' B₂' h₂' e e'
    rw [hm _ (h𝒮 h₁) _ (h𝒮 h₁'), hm _ (h𝒮 h₂) _ (h𝒮 h₂'), hloc _ (h𝒮 h₁) _ (h𝒮 h₂) e,
      hloc _ (h𝒮 h₁') _ (h𝒮 h₂') e']
end Facts
section Chart
variable {E₀ : Type} [NormedAddCommGroup E₀] [NormedSpace ℝ E₀]
def chartOfFlattening (M : Set E₀) {l l' : ℕ}
    (q : OpenPartialHomeomorph E₀ ((Fin l → ℝ) × (Fin l' → ℝ)))
    (hq : ContDiffOn ℝ ∞ q q.source) (hqs : ContDiffOn ℝ ∞ q.symm q.target)
    (hM : q '' (q.source ∩ M) = q.target ∩ {z | z.2 = 0}) :
    Matrices.EmbeddedSubmanifold.Chart M where
  dim := l
  source := {v | (v, (0 : Fin l' → ℝ)) ∈ q.target}
  param v := q.symm (v, 0)
  isOpen_source := q.open_target.preimage (by fun_prop)
  contDiffOn_param :=
    hqs.comp (contDiff_prodMk_left (0 : Fin l' → ℝ)).contDiffOn fun _ hv => hv
  injective_fderiv_param := by
    intro v hv
    have hopen : IsOpen {v : Fin l → ℝ | (v, (0 : Fin l' → ℝ)) ∈ q.target} :=
      q.open_target.preimage (by fun_prop)
    have hp : ContDiffOn ℝ ∞ (fun v : Fin l → ℝ => q.symm (v, 0))
        {v | (v, (0 : Fin l' → ℝ)) ∈ q.target} :=
      hqs.comp (contDiff_prodMk_left (0 : Fin l' → ℝ)).contDiffOn fun _ hv => hv
    have hpd : DifferentiableAt ℝ (fun v : Fin l → ℝ => q.symm (v, 0)) v :=
      (hp.contDiffAt (hopen.mem_nhds hv)).differentiableAt (by simp)
    have hqd : DifferentiableAt ℝ q (q.symm (v, 0)) :=
      (hq.contDiffAt (q.open_source.mem_nhds (q.map_target hv))).differentiableAt (by simp)
    have hcomp := hqd.hasFDerivAt.comp v hpd.hasFDerivAt
    have heq : (fun w : Fin l → ℝ => (w, (0 : Fin l' → ℝ))) =ᶠ[𝓝 v]
        q ∘ fun w : Fin l → ℝ => q.symm (w, 0) := by
      filter_upwards [hopen.mem_nhds hv] with w hw
      exact (q.right_inv hw).symm
    have hinl : HasFDerivAt (fun w : Fin l → ℝ => (w, (0 : Fin l' → ℝ)))
        (ContinuousLinearMap.inl ℝ (Fin l → ℝ) (Fin l' → ℝ)) v :=
      (ContinuousLinearMap.inl ℝ (Fin l → ℝ) (Fin l' → ℝ)).hasFDerivAt
    have huniq := (hcomp.congr_of_eventuallyEq heq).unique hinl
    intro w w' h
    have h' := congrArg (fderiv ℝ q (q.symm (v, 0))) h
    have e₁ := congrArg (fun A => A w) huniq
    have e₂ := congrArg (fun A => A w') huniq
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inl_apply] at e₁ e₂
    exact (Prod.mk.inj (e₁.symm.trans (h'.trans e₂))).1
  injOn_param := by
    intro v hv w hw h
    have h' := congrArg q h
    rw [q.right_inv hv, q.right_inv hw] at h'
    exact (Prod.mk.inj h').1
  isRelativelyOpen_image := by
    intro W hW hWo
    refine ⟨q.source ∩ q ⁻¹' (W ×ˢ univ), q.isOpen_inter_preimage (hWo.prod isOpen_univ), ?_⟩
    ext x
    constructor
    · rintro ⟨v, hv, rfl⟩
      have hmem : (v, (0 : Fin l' → ℝ)) ∈ q.target := hW hv
      refine ⟨⟨q.map_target hmem, ?_⟩, ?_⟩
      · show q (q.symm (v, 0)) ∈ W ×ˢ (univ : Set (Fin l' → ℝ))
        rw [q.right_inv hmem]
        exact ⟨hv, mem_univ _⟩
      · have hi : (v, (0 : Fin l' → ℝ)) ∈ q '' (q.source ∩ M) := by
          rw [hM]
          exact ⟨hmem, rfl⟩
        obtain ⟨y, ⟨hy, hyM⟩, hyv⟩ := hi
        show q.symm (v, 0) ∈ M
        rw [← hyv, q.left_inv hy]
        exact hyM
    · rintro ⟨⟨hs, hW'⟩, hxM⟩
      have h0 : q x ∈ q.target ∩ {z | z.2 = 0} := by
        rw [← hM]
        exact ⟨x, ⟨hs, hxM⟩, rfl⟩
      refine ⟨(q x).1, hW'.1, ?_⟩
      have hx : ((q x).1, (0 : Fin l' → ℝ)) = q x := Prod.ext rfl h0.2.symm
      show q.symm ((q x).1, 0) = x
      rw [hx, q.left_inv hs]
theorem exists_symmSecond_of_submanifold {V F : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {M O : Set E₀} {f : E₀ → F}
    (hM : Submanifolds.IsSmoothSubmanifold M) (hOpen : Matrices.ComplexMatrix2.IsRelativelyOpen M O)
    (hf : Matrices.EmbeddedSubmanifold.HasDifferentiablePartialsOn M O f)
    {e : V → E₀} (he : ContDiffAt ℝ 2 e 0) (he0 : e 0 ∈ O) (S : Set V)
    (heS : ∀ y ∈ S, e y ∈ M) :
    ∃ g : V → F, SymmetricSecondDerivAtZero ℝ g ∧
      ∀ᶠ y in 𝓝 (0 : V), y ∈ S → e y ∈ O ∧ f (e y) = g y := by
  obtain ⟨O', hO', rfl⟩ := hOpen
  obtain ⟨l, l', q, hp, hq, hqs, hqM⟩ := hM (e 0) he0.2
  let c := chartOfFlattening M q hq hqs hqM
  let par : (Fin l → ℝ) → E₀ := fun v => q.symm (v, 0)
  let D : Set (Fin l → ℝ) := {v | (v, (0 : Fin l' → ℝ)) ∈ q.target} ∩ par ⁻¹' (O' ∩ M)
  let ψ : (Fin l → ℝ) → F := f ∘ par
  have hinM : ∀ v, (v, (0 : Fin l' → ℝ)) ∈ q.target → par v ∈ M := by
    intro v hv
    have hi : (v, (0 : Fin l' → ℝ)) ∈ q '' (q.source ∩ M) := by
      rw [hqM]
      exact ⟨hv, rfl⟩
    obtain ⟨y, ⟨hy, hyM⟩, hyv⟩ := hi
    show q.symm (v, 0) ∈ M
    rw [← hyv, q.left_inv hy]
    exact hyM
  have hDo : IsOpen D := by
    have hcont : ContinuousOn par {v | (v, (0 : Fin l' → ℝ)) ∈ q.target} :=
      c.contDiffOn_param.continuousOn
    have hset : D = {v | (v, (0 : Fin l' → ℝ)) ∈ q.target} ∩ par ⁻¹' O' := by
      ext v
      constructor
      · rintro ⟨h₁, h₂⟩
        exact ⟨h₁, h₂.1⟩
      · rintro ⟨h₁, h₂⟩
        exact ⟨h₁, h₂, hinM v h₁⟩
    rw [hset]
    exact hcont.isOpen_inter_preimage c.isOpen_source hO'
  have hψ₀ : DifferentiableOn ℝ ψ D := hf.1.2 c
  have hψ : ∀ v ∈ D, DifferentiableAt ℝ ψ v := fun v hv => hψ₀.differentiableAt (hDo.mem_nhds hv)
  have hψ₁ : ∀ k : Fin l, DifferentiableOn ℝ (fun v => fderiv ℝ ψ v (Pi.single k 1)) D :=
    fun k => hf.2 c k
  have hψ2 : ∀ v ∈ D, DifferentiableAt ℝ (fderiv ℝ ψ) v := fun v hv =>
    differentiableAt_clm_of_basis _ fun k => (hψ₁ k).differentiableAt (hDo.mem_nhds hv)
  have hqat : ContDiffAt ℝ 2 q (e 0) := by
    exact_mod_cast contDiffAt_infty.1 (hq.contDiffAt (q.open_source.mem_nhds hp)) 2
  let θ : V → Fin l → ℝ := fun y => (q (e y)).1
  have hθ : ContDiffAt ℝ 2 θ 0 := contDiffAt_fst.comp _ (hqat.comp _ he)
  have hsrc : ∀ᶠ y in 𝓝 (0 : V), e y ∈ q.source :=
    he.continuousAt.eventually (q.open_source.mem_nhds hp)
  have hback : ∀ y, e y ∈ q.source → e y ∈ M →
      (θ y, (0 : Fin l' → ℝ)) ∈ q.target ∧ par (θ y) = e y := by
    intro y hs hm
    have h0 : q (e y) ∈ q.target ∩ {z | z.2 = 0} := by
      rw [← hqM]
      exact ⟨e y, ⟨hs, hm⟩, rfl⟩
    have hx : (θ y, (0 : Fin l' → ℝ)) = q (e y) := Prod.ext rfl h0.2.symm
    refine ⟨?_, ?_⟩
    · rw [hx]
      exact h0.1
    · show q.symm (θ y, 0) = e y
      rw [hx, q.left_inv hs]
  have hθ0 : θ 0 ∈ D := by
    obtain ⟨h₁, h₂⟩ := hback 0 hp he0.2
    refine ⟨h₁, ?_⟩
    show par (θ 0) ∈ O' ∩ M
    rw [h₂]
    exact he0
  have hθD : ∀ᶠ y in 𝓝 (0 : V), θ y ∈ D :=
    hθ.continuousAt.eventually (hDo.mem_nhds hθ0)
  have hθnear : ∀ᶠ y in 𝓝 (0 : V), ContDiffAt ℝ 2 θ y := hθ.eventually (by simp)
  have hfd : ∀ᶠ y in 𝓝 (0 : V),
      HasFDerivAt (ψ ∘ θ) ((fderiv ℝ ψ (θ y)).comp (fderiv ℝ θ y)) y := by
    filter_upwards [hθD, hθnear] with y h₁ h₂
    exact (hψ _ h₁).hasFDerivAt.comp y (h₂.differentiableAt (by simp)).hasFDerivAt
  have hfeq : fderiv ℝ (ψ ∘ θ) =ᶠ[𝓝 0] fun y => (fderiv ℝ ψ (θ y)).comp (fderiv ℝ θ y) :=
    hfd.mono fun y h => h.fderiv
  have hθ1 : DifferentiableAt ℝ (fderiv ℝ θ) 0 :=
    (hθ.fderiv_right (m := 1) (by norm_num)).differentiableAt (by simp)
  have hsec : DifferentiableAt ℝ (fderiv ℝ (ψ ∘ θ)) 0 := by
    rw [hfeq.differentiableAt_iff]
    exact ((hψ2 _ hθ0).comp 0 (hθ.differentiableAt (by simp))).clm_comp hθ1
  refine ⟨ψ ∘ θ, ⟨hfd.mono fun y h => h.differentiableAt, hsec, fun v w => ?_⟩, ?_⟩
  · exact second_derivative_symmetric_of_eventually
      (hfd.mono fun y h => h.differentiableAt.hasFDerivAt) hsec.hasFDerivAt v w
  · filter_upwards [hsrc, hθD] with y hs hD' hy
    obtain ⟨-, h₂⟩ := hback y hs (heS y hy)
    have hmem : par (θ y) ∈ O' ∩ M := hD'.2
    rw [h₂] at hmem
    refine ⟨hmem, ?_⟩
    show f (e y) = f (par (θ y))
    rw [h₂]
end Chart
section RealConditions
theorem tendsto_linearCombination_zero {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (v v' : V) : Tendsto (fun p : ℝ × ℝ => p.1 • v + p.2 • v') (𝓝 0) (𝓝 0) := by
  have hc : Continuous fun p : ℝ × ℝ => p.1 • v + p.2 • v' := by fun_prop
  have h := hc.tendsto (0 : ℝ × ℝ)
  simpa using h
theorem matExp_I_smul_mem_specialUnitary (hexp : Matrices.ComplexMatrix2.ExpLogEstimates)
    {Y : Matrices.ComplexMatrix2} (hY : Y ∈ Matrices.ComplexMatrix2.hermitianTraceless) :
    Matrices.ComplexMatrix2.matExp (Complex.I • Y) ∈ Matrices.ComplexMatrix2.specialUnitary := by
  have hY' : Y = Y.conjTranspose ∧ Matrices.ComplexMatrix2.fullTrace Y = 0 := hY
  rw [Matrix.mem_specialUnitaryGroup_iff]
  refine ⟨?_, ?_⟩
  · have hs : (Complex.I • Y).conjTranspose = -(Complex.I • Y) := by
      rw [Matrix.conjTranspose_smul, ← hY'.1]
      simp
    rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, Matrices.ComplexMatrix2.matExp,
      ← Matrix.exp_conjTranspose, hs, Matrix.exp_neg]
    exact Matrix.mul_nonsing_inv _
      ((Matrix.isUnit_iff_isUnit_det _).1 (Matrix.isUnit_exp _))
  · obtain ⟨-, -, -, -, -, hdet, -⟩ := hexp
    rw [hdet]
    have h0 : Matrices.ComplexMatrix2.fullTrace (Complex.I • Y) = 0 := by
      have h1 : Matrices.ComplexMatrix2.fullTrace Y = 0 := hY'.2
      simp only [Matrices.ComplexMatrix2.fullTrace, Matrix.trace_smul] at h1 ⊢
      rw [h1, smul_zero]
    rw [h0, Complex.exp_zero]
theorem contDiff_leftTranslatedExp {N : ℕ} (W : Fin N → Matrices.ComplexMatrix2) :
    ContDiff ℝ 2 fun (y : Fin N → Matrices.ComplexMatrix2) (i : Fin N) =>
      Matrices.ComplexMatrix2.matExp (Complex.I • y i) * W i := by
  have hexp : ContDiff ℝ 2 (NormedSpace.exp : Matrices.ComplexMatrix2 → Matrices.ComplexMatrix2) :=
    contDiff_iff_contDiffAt.2 fun x => (NormedSpace.exp_analytic (𝕂 := ℝ) x).contDiffAt
  refine contDiff_pi.2 fun i => ?_
  have h₁ : ContDiff ℝ 2 fun y : Fin N → Matrices.ComplexMatrix2 => Complex.I • y i :=
    (contDiff_apply ℝ Matrices.ComplexMatrix2 i).const_smul Complex.I
  exact (hexp.comp h₁).mul contDiff_const
theorem holdsRealVariables (hprod : Matrices.FamilyProducts.FamilyProductsStatement)
    (hexp : Matrices.ComplexMatrix2.ExpLogEstimates) {α : Type} {N : ℕ} (hN : 1 ≤ N) (E : Type)
    [NormedAddCommGroup E] [NormedSpace ℝ E] (𝒜 𝒱 : Set (α → Matrices.ComplexMatrix2))
    (b : Fin N → α)
    (h𝒜 : ∀ B ∈ 𝒜, ∀ i, B (b i) ∈ Matrices.ComplexMatrix2.hermitianTraceless)
    (h𝒱 : ∀ U ∈ 𝒱, ∀ i, U (b i) ∈ Matrices.ComplexMatrix2.specialUnitary) :
    HoldsRealVariables E 𝒜 𝒱 b := by
  intro O f hO hf U hU hUO
  have : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
  have hM : Submanifolds.IsSmoothSubmanifold (Matrices.specialUnitaryPower (Fin N)) :=
    (hprod (Fin N)).2.2
  let e : (Fin N → Matrices.ComplexMatrix2) → Fin N → Matrices.ComplexMatrix2 :=
    fun y i => Matrices.ComplexMatrix2.matExp (Complex.I • y i) * U (b i)
  have he : ContDiff ℝ 2 e := contDiff_leftTranslatedExp fun i => U (b i)
  have he0 : e 0 ∈ O := by
    have h : e 0 = fun i => U (b i) := by
      funext i
      simp [e, Matrices.ComplexMatrix2.matExp]
    rwa [h]
  let S : Set (Fin N → Matrices.ComplexMatrix2) :=
    {y | ∀ i, y i ∈ Matrices.ComplexMatrix2.hermitianTraceless}
  have heS : ∀ y ∈ S, e y ∈ Matrices.specialUnitaryPower (Fin N) := fun y hy i =>
    Matrices.ComplexMatrix2.specialUnitary.mul_mem
      (matExp_I_smul_mem_specialUnitary hexp (hy i)) (h𝒱 U hU i)
  obtain ⟨g, hg, hge⟩ := exists_symmSecond_of_submanifold hM hO hf he.contDiffAt he0 S heS
  have hval : ∀ (B : α → Matrices.ComplexMatrix2) (c : ℝ) (i : Fin N),
      (algebraMap ℝ ℂ c • B) (b i) = c • B (b i) :=
    fun B c i => by simp
  refine mixedPartialProperties_of_factor
    (𝒯 := {B | ∀ i, B (b i) ∈ Matrices.ComplexMatrix2.hermitianTraceless})
    (ℓ := fun B i => B (b i)) (g := g) (fun B hB => h𝒜 B hB) ?_ ?_ ?_ hg ?_
  · intro B₁ h₁ B₂ h₂ c i
    rw [Pi.add_apply, hval]
    exact Matrices.ComplexMatrix2.hermitianTraceless.add_mem
      (Matrices.ComplexMatrix2.hermitianTraceless.smul_mem c (h₁ i)) (h₂ i)
  · intro B₁ _ B₂ _ c
    funext i
    rw [Pi.add_apply, hval]
    rfl
  · intro B₁ _ B₂ _ h
    funext i
    exact h i
  · intro B hB B' hB'
    filter_upwards
      [(tendsto_linearCombination_zero (fun i => B (b i)) fun i => B' (b i)).eventually hge]
      with p hp
    have hmem : (p.1 • (fun i => B (b i)) + p.2 • fun i => B' (b i)) ∈ S := fun i =>
      Matrices.ComplexMatrix2.hermitianTraceless.add_mem
        (Matrices.ComplexMatrix2.hermitianTraceless.smul_mem _ (hB i))
        (Matrices.ComplexMatrix2.hermitianTraceless.smul_mem _ (hB' i))
    obtain ⟨h₁, h₂⟩ := hp hmem
    have hpt : chartPoint b U (algebraMap ℝ ℂ p.1 • B + algebraMap ℝ ℂ p.2 • B') =
        e (p.1 • (fun i => B (b i)) + p.2 • fun i => B' (b i)) := by
      funext i
      simp only [chartPoint, e, Pi.add_apply, hval, Pi.smul_apply]
    refine ⟨hpt ▸ h₁, ?_⟩
    show f (chartPoint b U _) = _
    rw [hpt]
    exact h₂
end RealConditions
section ComplexConditions
theorem holomorphic_differentiableAt
    (hps : Coordinates.ComplexCoordinates.PowerSeriesHolomorphy.Properties) {M N' : ℕ}
    {D : Set (Coordinates.ComplexCoordinates M)}
    {H : Coordinates.ComplexCoordinates M → Coordinates.ComplexCoordinates N'}
    (hH : Coordinates.ComplexCoordinates.IsHolomorphicIn D H) {z : Coordinates.ComplexCoordinates M}
    (hz : z ∈ D) :
    DifferentiableAt ℂ H z ∧ ∀ h, fderiv ℝ H z h = fderiv ℂ H z h := by
  obtain ⟨L, hL⟩ := ((hps.1 M D hH.1).1 N' H hH).2.2.1 z hz
  have hc : HasFDerivAt H L z := hasFDerivAt_of_restrictScalars ℝ hL rfl
  refine ⟨hc.differentiableAt, fun h => ?_⟩
  rw [hL.fderiv, hc.fderiv]
  rfl
theorem symmSecond_of_holomorphic
    (hps : Coordinates.ComplexCoordinates.PowerSeriesHolomorphy.Properties)
    (hder : SeparatedFrame.HolomorphicDerivatives.Claim) {M : ℕ}
    {D : Set (Coordinates.ComplexCoordinates M)}
    {G : Coordinates.ComplexCoordinates M → Coordinates.ComplexCoordinates 1}
    (hG : Coordinates.ComplexCoordinates.IsHolomorphicIn D G)
    (h0 : (0 : Coordinates.ComplexCoordinates M) ∈ D) :
    SymmetricSecondDerivAtZero ℂ fun w => G w 0 := by
  have hD : D ∈ 𝓝 (0 : Coordinates.ComplexCoordinates M) := hG.1.mem_nhds h0
  have hG2 : DifferentiableAt ℂ (fderiv ℂ G) 0 := by
    refine differentiableAt_clm_of_basis _ fun k => ?_
    have hk := (hder M 1 D G hG).1 (Pi.single k 1)
    have heq : (fun z => fderiv ℂ G z (Pi.single k 1)) =ᶠ[𝓝 0]
        fun z => fderiv ℝ G z (Pi.single k 1) := by
      filter_upwards [hD] with z hz
      exact ((holomorphic_differentiableAt hps hG hz).2 _).symm
    rw [heq.differentiableAt_iff]
    exact (holomorphic_differentiableAt hps hk h0).1
  let π : Coordinates.ComplexCoordinates 1 →L[ℂ] ℂ := ContinuousLinearMap.proj 0
  have hfd : ∀ᶠ z in 𝓝 (0 : Coordinates.ComplexCoordinates M),
      HasFDerivAt (fun w => G w 0) (π.comp (fderiv ℂ G z)) z := by
    filter_upwards [hD] with z hz
    exact π.hasFDerivAt.comp z (holomorphic_differentiableAt hps hG hz).1.hasFDerivAt
  have hfeq : fderiv ℂ (fun w => G w 0) =ᶠ[𝓝 0] fun z => π.comp (fderiv ℂ G z) :=
    hfd.mono fun z h => h.fderiv
  have hsec : DifferentiableAt ℂ (fderiv ℂ fun w => G w 0) 0 := by
    rw [hfeq.differentiableAt_iff]
    exact (differentiableAt_const π).clm_comp hG2
  exact ⟨hfd.mono fun z h => h.differentiableAt, hsec, fun v w =>
    second_derivative_symmetric_of_eventually
      (hfd.mono fun y h => h.differentiableAt.hasFDerivAt) hsec.hasFDerivAt v w⟩
def basisCoord (β : Module.Basis (Fin 3) ℂ Matrices.ComplexMatrix2.traceless)
    (X : Matrices.ComplexMatrix2) (c : Fin 3) : ℂ :=
  open Classical in if h : X ∈ Matrices.ComplexMatrix2.traceless then β.repr ⟨X, h⟩ c else 0
theorem sum_basisCoord_smul (β : Module.Basis (Fin 3) ℂ Matrices.ComplexMatrix2.traceless)
    {X : Matrices.ComplexMatrix2} (h : X ∈ Matrices.ComplexMatrix2.traceless) :
    ∑ c, basisCoord β X c • (β c : Matrices.ComplexMatrix2) = X := by
  have hs := congrArg Subtype.val (β.sum_repr ⟨X, h⟩)
  rw [AddSubmonoidClass.coe_finsetSum] at hs
  simp only [basisCoord, dif_pos h]
  exact hs
theorem basisCoord_linearCombination (β : Module.Basis (Fin 3) ℂ Matrices.ComplexMatrix2.traceless)
    {X Y : Matrices.ComplexMatrix2} (hX : X ∈ Matrices.ComplexMatrix2.traceless)
    (hY : Y ∈ Matrices.ComplexMatrix2.traceless) (a a' : ℂ) (c : Fin 3) :
    basisCoord β (a • X + a' • Y) c = a * basisCoord β X c + a' * basisCoord β Y c := by
  have hXY : a • X + a' • Y ∈ Matrices.ComplexMatrix2.traceless :=
    Matrices.ComplexMatrix2.traceless.add_mem (Matrices.ComplexMatrix2.traceless.smul_mem _ hX)
      (Matrices.ComplexMatrix2.traceless.smul_mem _ hY)
  have he : (⟨a • X + a' • Y, hXY⟩ : Matrices.ComplexMatrix2.traceless) =
      a • ⟨X, hX⟩ + a' • ⟨Y, hY⟩ := rfl
  simp only [basisCoord, dif_pos hX, dif_pos hY, dif_pos hXY, he, map_add, map_smul]
  simp
def tupleCoords {τ : Type} [Fintype τ] (β : Module.Basis (Fin 3) ℂ Matrices.ComplexMatrix2.traceless)
    (ν : τ ≃ Fin (Fintype.card τ)) (A : τ → Matrices.ComplexMatrix2) :
    Coordinates.ComplexCoordinates (Fintype.card τ * 3) :=
  fun k => basisCoord β (A (ν.symm (finProdFinEquiv.symm k).1)) (finProdFinEquiv.symm k).2
theorem tupleOfCoords_tupleCoords {τ : Type} [Fintype τ]
    (β : Module.Basis (Fin 3) ℂ Matrices.ComplexMatrix2.traceless)
    (ν : τ ≃ Fin (Fintype.card τ)) {A : τ → Matrices.ComplexMatrix2}
    (hA : ∀ i, A i ∈ Matrices.ComplexMatrix2.traceless) :
    Matrices.GroupLieProduct.tupleOfCoords β ν (tupleCoords β ν A) = A := by
  funext i
  simp only [Matrices.GroupLieProduct.tupleOfCoords, Coordinates.ComplexCoordinates.tracelessTuple,
    tupleCoords, Equiv.symm_apply_apply]
  exact sum_basisCoord_smul β (hA i)
theorem holdsComplexVariables
    (hps : Coordinates.ComplexCoordinates.PowerSeriesHolomorphy.Properties)
    (hder : SeparatedFrame.HolomorphicDerivatives.Claim) {σ : Type} {N : ℕ}
    (𝒰 : Set (σ → Matrices.ComplexMatrix2)) (b : Fin N → σ) : HoldsComplexVariables 𝒰 b := by
  intro β O f hO hf U hU hUO
  let p := Matrices.GroupLieProduct.asGroupFactors fun i => U (b i)
  have hpW : p ∈ Matrices.GroupLieProduct.asGroupFactors '' O := ⟨_, hUO, rfl⟩
  obtain ⟨O', h0, hch, hhol⟩ := hf.2.2 p hpW
  let ν := Fintype.equivFin (Fin N ⊕ Empty)
  let T := Matrices.GroupLieProduct.tupleOfCoords β ν
  have hG := hhol.2 ν
  have hT0 : (0 : Coordinates.ComplexCoordinates _) ∈ T ⁻¹' O' := by
    have h : T 0 = 0 := by
      funext i
      simp [T, Matrices.GroupLieProduct.tupleOfCoords, Coordinates.ComplexCoordinates.tracelessTuple]
    show T 0 ∈ O'
    rwa [h]
  have hg := symmSecond_of_holomorphic hps hder hG hT0
  let 𝒯 : Set (σ → Matrices.ComplexMatrix2) :=
    (Matrices.GroupLieProduct.tracelessFunctions σ : Set (σ → Matrices.ComplexMatrix2))
  have h𝒯 : ∀ B ∈ 𝒯, ∀ s, B s ∈ Matrices.ComplexMatrix2.traceless := fun B hB s => hB s (mem_univ s)
  let tup : (σ → Matrices.ComplexMatrix2) → Fin N ⊕ Empty → Matrices.ComplexMatrix2 :=
    fun B => Matrices.GroupLieProduct.asGroupFactors fun i => Complex.I • B (b i)
  have htup : ∀ B ∈ 𝒯, ∀ j, tup B j ∈ Matrices.ComplexMatrix2.traceless := by
    rintro B hB (i | e)
    · exact Matrices.ComplexMatrix2.traceless.smul_mem _ (h𝒯 B hB _)
    · exact e.elim
  let crd : (σ → Matrices.ComplexMatrix2) →
      Coordinates.ComplexCoordinates (Fintype.card (Fin N ⊕ Empty) * 3) :=
    fun B => tupleCoords β ν (tup B)
  have hcomb : ∀ B₁ ∈ 𝒯, ∀ B₂ ∈ 𝒯, ∀ a a' : ℂ,
      crd (a • B₁ + a' • B₂) = a • crd B₁ + a' • crd B₂ := by
    intro B₁ h₁ B₂ h₂ a a'
    have ht : ∀ j, tup (a • B₁ + a' • B₂) j = a • tup B₁ j + a' • tup B₂ j := by
      rintro (i | e)
      · show Complex.I • (a • B₁ (b i) + a' • B₂ (b i)) =
          a • (Complex.I • B₁ (b i)) + a' • (Complex.I • B₂ (b i))
        rw [smul_add, smul_comm Complex.I a, smul_comm Complex.I a']
      · exact e.elim
    funext k
    simp only [crd, tupleCoords, ht, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    exact basisCoord_linearCombination β (htup _ h₁ _) (htup _ h₂ _) _ _ _
  refine mixedPartialProperties_of_factor (𝒯 := 𝒯) (ℓ := crd) (g := fun w => _) subset_rfl
    ?_ ?_ ?_ hg ?_
  · intro B₁ h₁ B₂ h₂ c s _
    exact Matrices.ComplexMatrix2.traceless.add_mem
      (Matrices.ComplexMatrix2.traceless.smul_mem _ (h𝒯 _ h₁ s)) (h𝒯 _ h₂ s)
  · intro B₁ h₁ B₂ h₂ c
    have h := hcomb B₁ h₁ B₂ h₂ c 1
    simpa using h
  · intro B₁ _ B₂ _ h
    have ht : tup B₁ = tup B₂ := by
      funext j
      rcases j with i | e
      · show Complex.I • B₁ (b i) = Complex.I • B₂ (b i)
        rw [h i]
      · exact e.elim
    show tupleCoords β ν (tup B₁) = tupleCoords β ν (tup B₂)
    rw [ht]
  · intro B hB B' hB'
    have hc : Tendsto (fun q : ℂ × ℂ => q.1 • crd B + q.2 • crd B') (𝓝 0) (𝓝 0) := by
      have hcont : Continuous fun q : ℂ × ℂ => q.1 • crd B + q.2 • crd B' := by fun_prop
      have h := hcont.tendsto (0 : ℂ × ℂ)
      simpa using h
    filter_upwards [hc.eventually ((hhol.2 ν).1.mem_nhds hT0)] with q hq
    have hXm : q.1 • B + q.2 • B' ∈ 𝒯 := fun s _ =>
      Matrices.ComplexMatrix2.traceless.add_mem
        (Matrices.ComplexMatrix2.traceless.smul_mem _ (h𝒯 _ hB s))
        (Matrices.ComplexMatrix2.traceless.smul_mem _ (h𝒯 _ hB' s))
    have hTX : T (q.1 • crd B + q.2 • crd B') = tup (q.1 • B + q.2 • B') := by
      rw [← hcomb B hB B' hB']
      exact tupleOfCoords_tupleCoords β ν (htup _ hXm)
    have hmem : tup (q.1 • B + q.2 • B') ∈ O' := by
      rw [← hTX]
      exact hq
    obtain ⟨x, hxO, hx⟩ := hch _ hmem
    have hpt : chartPoint b U (q.1 • B + q.2 • B') = x := by
      funext i
      exact (congrFun hx (.inl i)).symm
    refine ⟨?_, ?_⟩
    · show chartPoint b U (q.1 • B + q.2 • B') ∈ O
      rw [hpt]
      exact hxO
    · show f (chartPoint b U (q.1 • B + q.2 • B')) = _
      show _ = f fun i => Matrices.GroupLieProduct.expChartAt p
        (T (q.1 • crd B + q.2 • crd B')) (.inl i)
      rw [hTX]
      rfl
end ComplexConditions
theorem mainStatement_holds (hprod : Matrices.FamilyProducts.FamilyProductsStatement)
    (hexp : Matrices.ComplexMatrix2.ExpLogEstimates)
    (hps : Coordinates.ComplexCoordinates.PowerSeriesHolomorphy.Properties)
    (hder : SeparatedFrame.HolomorphicDerivatives.Claim) : MainStatement := by
  intro L k j N hL hj hN
  refine ⟨fun n hn b => ⟨?_, ?_, holdsComplexVariables hps hder _ b⟩, fun b =>
    ⟨?_, ?_, holdsComplexVariables hps hder _ b⟩⟩
  · exact holdsRealVariables hprod hexp hN ℝ _ _ _ (fun B hB i => hB.1 _ (b i).2)
      fun U hU i => hU.1 _ (mem_univ _)
  · exact holdsRealVariables hprod hexp hN ℂ _ _ _ (fun B hB i => hB.1 _ (b i).2)
      fun U hU i => hU.1 _ (mem_univ _)
  · exact holdsRealVariables hprod hexp hN ℝ _ _ _ (fun B hB i => hB.1 _ (b i).2)
      fun U hU i => hU.1 _
  · exact holdsRealVariables hprod hexp hN ℂ _ _ _ (fun B hB i => hB.1 _ (b i).2)
      fun U hU i => hU.1 _
end YangMills.Construction.Tower.LeftChartSecondDerivative
end
