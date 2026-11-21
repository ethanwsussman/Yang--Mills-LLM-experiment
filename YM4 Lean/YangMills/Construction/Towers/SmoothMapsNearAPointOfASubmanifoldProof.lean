import YangMills.Construction.Towers.SmoothMapsNearAPointOfASubmanifold
import Mathlib
set_option autoImplicit false
open Set Filter
open scoped ContDiff Topology
noncomputable section
namespace YangMills.Construction.Manifolds
open YangMills.Construction.Matrices.EmbeddedSubmanifold
variable {E E' P Q : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup E'] [NormedSpace ℝ E'] [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup Q] [NormedSpace ℝ Q]
private theorem exists_continuous_leftInverse [FiniteDimensional ℝ P] (T : P →L[ℝ] E)
    (hT : Function.Injective T) : ∃ l : E →L[ℝ] P, ∀ a, l (T a) = a := by
  let R : Submodule ℝ E := LinearMap.range (T : P →ₗ[ℝ] E)
  obtain ⟨π, hπ⟩ := Submodule.ClosedComplemented.of_finiteDimensional R
  let e : P ≃ₗ[ℝ] R := LinearEquiv.ofInjective (T : P →ₗ[ℝ] E) hT
  let e' : P ≃L[ℝ] R := e.toContinuousLinearEquiv
  refine ⟨(e'.symm : R →L[ℝ] P).comp π, fun a => ?_⟩
  have h1 : π (T a) = e' a := hπ (e' a)
  simp [h1]
private theorem exists_smooth_localInverse [FiniteDimensional ℝ P] {M : Set E} {O : Set P}
    {φ : P → E} {z : P} (hφ : IsSmoothParametrization M O φ) (hz : z ∈ O) :
    ∃ (Ω : Set E) (ρ : E → P), IsOpen Ω ∧ φ z ∈ Ω ∧ ContDiffOn ℝ ∞ ρ Ω ∧
      ∀ p ∈ M ∩ Ω, ρ p ∈ O ∧ φ (ρ p) = p := by
  obtain ⟨⟨hO, -, -, -, hD, himg⟩, hsm⟩ := hφ
  have hφz : ContDiffAt ℝ ∞ φ z := hsm.contDiffAt (hO.mem_nhds hz)
  have hφd : HasFDerivAt φ (fderiv ℝ φ z) z := (hφz.differentiableAt (by simp)).hasFDerivAt
  obtain ⟨l, hl⟩ := exists_continuous_leftInverse (fderiv ℝ φ z) (hD z hz)
  let h : P → P := fun w => l (φ w)
  have hhc : ContDiffOn ℝ ∞ h O := l.contDiff.comp_contDiffOn hsm
  have hhz : ContDiffAt ℝ ∞ h z := hhc.contDiffAt (hO.mem_nhds hz)
  have hderiv : HasFDerivAt h ((ContinuousLinearEquiv.refl ℝ P : P ≃L[ℝ] P) : P →L[ℝ] P) z := by
    have h1 : HasFDerivAt h (l.comp (fderiv ℝ φ z)) z := l.hasFDerivAt.comp z hφd
    have h2 : l.comp (fderiv ℝ φ z) = ((ContinuousLinearEquiv.refl ℝ P : P ≃L[ℝ] P) : P →L[ℝ] P) := by
      ext a
      simp [hl]
    rwa [h2] at h1
  let e := hhz.toOpenPartialHomeomorph h hderiv (by simp)
  have hzs : z ∈ e.source := hhz.mem_toOpenPartialHomeomorph_source hderiv (by simp)
  have hcont : ContinuousOn (fderiv ℝ h) O := hhc.continuousOn_fderiv_of_isOpen hO (by simp)
  have hnear : ∀ᶠ w in 𝓝 z, fderiv ℝ h w ∈ range ((↑) : (P ≃L[ℝ] P) → P →L[ℝ] P) :=
    (hcont.continuousAt (hO.mem_nhds hz)).eventually_mem
      (by rw [hderiv.fderiv]; exact ContinuousLinearEquiv.nhds _)
  have hset : {w | fderiv ℝ h w ∈ range ((↑) : (P ≃L[ℝ] P) → P →L[ℝ] P)} ∩ O ∩ e.source ∈ 𝓝 z :=
    inter_mem (inter_mem hnear (hO.mem_nhds hz)) (e.open_source.mem_nhds hzs)
  obtain ⟨W, hWs, hWo, hzW⟩ := mem_nhds_iff.1 hset
  let V : Set P := e.target ∩ e.symm ⁻¹' W
  have hVo : IsOpen V := e.isOpen_inter_preimage_symm hWo
  have hsymm : ContDiffOn ℝ ∞ e.symm V := by
    rintro y ⟨hy, hyW⟩
    obtain ⟨⟨⟨A, hA⟩, hyO⟩, -⟩ := hWs hyW
    have hat : ContDiffAt ℝ ∞ h (e.symm y) := hhc.contDiffAt (hO.mem_nhds hyO)
    have hA' : HasFDerivAt e (A : P →L[ℝ] P) (e.symm y) := by
      rw [hA]
      exact (hat.differentiableAt (by simp)).hasFDerivAt
    exact (e.contDiffAt_symm hy hA' hat).contDiffWithinAt
  have key : ∀ w ∈ W, h w ∈ V ∧ e.symm (h w) = w := by
    intro w hw
    have hws : w ∈ e.source := (hWs hw).2
    have hinv : e.symm (e w) = w := e.left_inv hws
    exact ⟨⟨e.map_source hws, by
      show e.symm (e w) ∈ W
      rw [hinv]
      exact hw⟩, hinv⟩
  obtain ⟨O₁, hO₁, hO₁eq⟩ := himg W (fun w hw => (hWs hw).1.2) hWo
  refine ⟨O₁ ∩ l ⁻¹' V, e.symm ∘ l, hO₁.inter (hVo.preimage l.continuous), ⟨?_, (key z hzW).1⟩, ?_, ?_⟩
  · have h1 : φ z ∈ φ '' W := mem_image_of_mem _ hzW
    rw [hO₁eq] at h1
    exact h1.1
  · exact hsymm.comp l.contDiff.contDiffOn fun p hp => hp.2
  · rintro p ⟨hpM, hpO₁, -⟩
    have h1 : p ∈ φ '' W := by
      rw [hO₁eq]
      exact ⟨hpO₁, hpM⟩
    obtain ⟨w, hw, rfl⟩ := h1
    have h2 : (e.symm ∘ l) (φ w) = w := (key w hw).2
    rw [h2]
    exact ⟨(hWs hw).1.2, rfl⟩
private theorem param_mapsTo {M : Set E} (c : Chart M) : MapsTo c.param c.source M := by
  intro u hu
  obtain ⟨O', -, h⟩ := c.isRelativelyOpen_image c.source subset_rfl c.isOpen_source
  have h1 : c.param u ∈ c.param '' c.source := mem_image_of_mem _ hu
  rw [h] at h1
  exact h1.2
private theorem chart_isSmoothParametrization {M : Set E} (c : Chart M) :
    IsSmoothParametrization M c.source c.param :=
  ⟨⟨c.isOpen_source, c.contDiffOn_param.of_le (WithTop.coe_le_coe.2 le_top),
    c.injOn_param, param_mapsTo c, c.injective_fderiv_param, c.isRelativelyOpen_image⟩,
    c.contDiffOn_param⟩
private theorem exists_local_factorization [FiniteDimensional ℝ P] {M : Set E} {O : Set P}
    {φ : P → E} {z : P} (hφ : IsSmoothParametrization M O φ) (hz : z ∈ O) {c : Q → E} {u : Q}
    (hc : ContDiffAt ℝ ∞ c u) (hM : ∀ᶠ u' in 𝓝 u, c u' ∈ M) (hcu : c u = φ z) :
    ∃ g : Q → P, ContDiffAt ℝ ∞ g u ∧ g u = z ∧ ∀ᶠ u' in 𝓝 u, g u' ∈ O ∧ φ (g u') = c u' := by
  obtain ⟨Ω, ρ, hΩ, hzΩ, hρ, hinv⟩ := exists_smooth_localInverse hφ hz
  have hρat : ContDiffAt ℝ ∞ ρ (c u) := by
    rw [hcu]
    exact hρ.contDiffAt (hΩ.mem_nhds hzΩ)
  have hcΩ : ∀ᶠ u' in 𝓝 u, c u' ∈ Ω :=
    hc.continuousAt.eventually_mem (hΩ.mem_nhds (hcu ▸ hzΩ))
  refine ⟨ρ ∘ c, hρat.comp u hc, ?_, ?_⟩
  · have hpM : φ z ∈ M := hφ.1.2.2.2.1 hz
    have h1 := hinv (φ z) ⟨hpM, hzΩ⟩
    show ρ (c u) = z
    rw [hcu]
    exact hφ.1.2.2.1 h1.1 hz h1.2
  · filter_upwards [hM, hcΩ] with u' h1 h2
    exact hinv (c u') ⟨h1, h2⟩
private theorem fderiv_eq_comp_of_eventually {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {φ : P → F} {c : Q → F} {g : Q → P} {u : Q} {z : P} (hφ : DifferentiableAt ℝ φ z)
    (hg : DifferentiableAt ℝ g u) (hgu : g u = z) (hev : ∀ᶠ u' in 𝓝 u, φ (g u') = c u') :
    fderiv ℝ c u = (fderiv ℝ φ z).comp (fderiv ℝ g u) := by
  subst hgu
  have h1 : HasFDerivAt (φ ∘ g) ((fderiv ℝ φ (g u)).comp (fderiv ℝ g u)) u :=
    hφ.hasFDerivAt.comp u hg.hasFDerivAt
  have h2 : c =ᶠ[𝓝 u] φ ∘ g := by
    filter_upwards [hev] with u' h
    exact h.symm
  exact (h1.congr_of_eventuallyEq h2).fderiv
private theorem isOpen_coords {M O : Set E} (c : Chart M)
    (hO : Matrices.ComplexMatrix2.IsRelativelyOpen M O) : IsOpen (c.coords O) := by
  obtain ⟨O', hO', rfl⟩ := hO
  have h1 : c.coords (O' ∩ M) = c.source ∩ c.param ⁻¹' O' := by
    ext u
    constructor
    · rintro ⟨hu, h, -⟩
      exact ⟨hu, h⟩
    · rintro ⟨hu, h⟩
      exact ⟨hu, h, param_mapsTo c hu⟩
  rw [h1]
  exact c.contDiffOn_param.continuousOn.isOpen_inter_preimage c.isOpen_source hO'
private theorem pullback_contDiffAt {M O : Set E} {f : E → E'} (hf : IsSmoothOnOpen M O f)
    (c : Chart M) {u : Fin c.dim → ℝ} (hu : u ∈ c.source) (hp : c.param u ∈ O) :
    ContDiffAt ℝ ∞ (c.pullback f) u :=
  (hf.2 c).contDiffAt ((isOpen_coords c hf.1).mem_nhds ⟨hu, hp⟩)
private theorem param_eventually_mem {M : Set E} (c : Chart M) {u : Fin c.dim → ℝ}
    (hu : u ∈ c.source) : ∀ᶠ u' in 𝓝 u, c.param u' ∈ M := by
  filter_upwards [c.isOpen_source.mem_nhds hu] with u' h
  exact param_mapsTo c h
private theorem param_contDiffAt {M : Set E} (c : Chart M) {u : Fin c.dim → ℝ}
    (hu : u ∈ c.source) : ContDiffAt ℝ ∞ c.param u :=
  c.contDiffOn_param.contDiffAt (c.isOpen_source.mem_nhds hu)
private theorem parametrization_eventually_mem [FiniteDimensional ℝ P] {M : Set E} {O : Set P}
    {φ : P → E} {z : P} (hφ : IsSmoothParametrization M O φ) (hz : z ∈ O) :
    ∀ᶠ z' in 𝓝 z, φ z' ∈ M := by
  filter_upwards [hφ.1.1.mem_nhds hz] with z' h
  exact hφ.1.2.2.2.1 h
private theorem parametrization_contDiffAt [FiniteDimensional ℝ P] {M : Set E} {O : Set P}
    {φ : P → E} {z : P} (hφ : IsSmoothParametrization M O φ) (hz : z ∈ O) :
    ContDiffAt ℝ ∞ φ z :=
  hφ.2.contDiffAt (hφ.1.1.mem_nhds hz)
private theorem comp_contDiffAt_of_mem {M O : Set E} {f : E → E'} {c : Q → E} {u : Q}
    (hM : IsChartedSubset M) (hf : IsSmoothOnOpen M O f) (hc : ContDiffAt ℝ ∞ c u)
    (hev : ∀ᶠ u' in 𝓝 u, c u' ∈ M) (hu : c u ∈ O) : ContDiffAt ℝ ∞ (f ∘ c) u := by
  obtain ⟨d, u₀, hu₀, hdu⟩ := hM (c u) hev.self_of_nhds
  obtain ⟨g, hg, hgu, hgev⟩ :=
    exists_local_factorization (chart_isSmoothParametrization d) hu₀ hc hev hdu.symm
  have hread : ContDiffAt ℝ ∞ (d.pullback f) (g u) := by
    rw [hgu]
    exact pullback_contDiffAt hf d hu₀ (hdu ▸ hu)
  refine (hread.comp u hg).congr_of_eventuallyEq ?_
  filter_upwards [hgev] with u' h
  show f (c u') = f (d.param (g u'))
  rw [h.2]
private theorem tangentSpace_eq_range [FiniteDimensional ℝ P] {M : Set E} {O : Set P}
    {φ : P → E} {z : P} (hM : IsChartedSubset M) (hφ : IsSmoothParametrization M O φ)
    (hz : z ∈ O) : tangentSpace M (φ z) = LinearMap.range (fderiv ℝ φ z : P →ₗ[ℝ] E) := by
  have hφz := parametrization_contDiffAt hφ hz
  apply le_antisymm
  · refine iSup_le fun c => iSup_le fun u => iSup_le fun hu => ?_
    obtain ⟨g, hg, hgu, hgev⟩ := exists_local_factorization hφ hz (param_contDiffAt c hu.1)
      (param_eventually_mem c hu.1) hu.2
    have hcomp := fderiv_eq_comp_of_eventually (hφz.differentiableAt (by simp))
      (hg.differentiableAt (by simp)) hgu (hgev.mono fun _ h => h.2)
    rintro _ ⟨w, rfl⟩
    exact ⟨fderiv ℝ g u w, by simp [hcomp]⟩
  · obtain ⟨d, u, hu, hdu⟩ := hM (φ z) (hφ.1.2.2.2.1 hz)
    obtain ⟨g, hg, hgu, hgev⟩ := exists_local_factorization (chart_isSmoothParametrization d) hu
      hφz (parametrization_eventually_mem hφ hz) hdu.symm
    have hcomp := fderiv_eq_comp_of_eventually ((param_contDiffAt d hu).differentiableAt (by simp))
      (hg.differentiableAt (by simp)) hgu (hgev.mono fun _ h => h.2)
    have hle : LinearMap.range (fderiv ℝ d.param u :
        (Fin d.dim → ℝ) →ₗ[ℝ] E) ≤ tangentSpace M (φ z) :=
      le_iSup_of_le d (le_iSup_of_le u (le_iSup_of_le ⟨hu, hdu⟩ le_rfl))
    rintro _ ⟨a, rfl⟩
    exact hle ⟨fderiv ℝ g z a, by simp [hcomp]⟩
private theorem exists_isTangentDifferential {M O : Set E} {f : E → E'} {p : E}
    (hM : IsChartedSubset M) (hf : IsSmoothOnOpen M O f) (hpM : p ∈ M) (hp : p ∈ O) :
    ∃ L, IsTangentDifferential M f p L := by
  obtain ⟨d, u, hu, hdu⟩ := hM p hpM
  have hd := chart_isSmoothParametrization d
  obtain ⟨Ω, ρ, hΩ, hpΩ, hρ, hinv⟩ := exists_smooth_localInverse hd hu
  rw [hdu] at hpΩ
  have h1 := hinv p ⟨hpM, hpΩ⟩
  have hρp : ρ p = u := d.injOn_param h1.1 hu (h1.2.trans hdu.symm)
  have hρat : ContDiffAt ℝ ∞ ρ p := hρ.contDiffAt (hΩ.mem_nhds hpΩ)
  have hread : ContDiffAt ℝ ∞ (d.pullback f) (ρ p) := by
    rw [hρp]
    exact pullback_contDiffAt hf d hu (hdu ▸ hp)
  have hhat : DifferentiableAt ℝ (d.pullback f ∘ ρ) p :=
    (hread.comp p hρat).differentiableAt (by simp)
  refine ⟨(fderiv ℝ (d.pullback f ∘ ρ) p : E →ₗ[ℝ] E') ∘ₗ (tangentSpace M p).subtype, ?_⟩
  intro c u' hu' hcu' w v hv
  have hcd : DifferentiableAt ℝ c.param u' :=
    (param_contDiffAt c hu').differentiableAt (by simp)
  have hcΩ : ∀ᶠ u'' in 𝓝 u', c.param u'' ∈ Ω :=
    hcd.continuousAt.eventually_mem (hΩ.mem_nhds (hcu' ▸ hpΩ))
  have hcomp := fderiv_eq_comp_of_eventually (φ := d.pullback f ∘ ρ) (c := c.pullback f)
    (g := c.param) (z := p) hhat hcd hcu' (by
      filter_upwards [param_eventually_mem c hu', hcΩ] with u'' h2 h3
      show f (d.param (ρ (c.param u''))) = f (c.param u'')
      rw [(hinv _ ⟨h2, h3⟩).2])
  simp [hcomp, hv]
private theorem tangentDifferential_eq [FiniteDimensional ℝ P] {M O' : Set E} {f : E → E'}
    {O : Set P} {φ : P → E} {z a : P} (v : tangentSpace M (φ z)) (hM : IsChartedSubset M)
    (hf : IsSmoothOnOpen M O' f) (hφ : IsSmoothParametrization M O φ) (hz : z ∈ O)
    (hO' : φ z ∈ O') (hv : (v : E) = fderiv ℝ φ z a) :
    tangentDifferential M f (φ z) v = fderiv ℝ (f ∘ φ) z a := by
  have hpM := hφ.1.2.2.2.1 hz
  have hspec : IsTangentDifferential M f (φ z) (tangentDifferential M f (φ z)) :=
    Classical.epsilon_spec (exists_isTangentDifferential hM hf hpM hO')
  obtain ⟨d, u, hu, hdu⟩ := hM (φ z) hpM
  obtain ⟨g, hg, hgu, hgev⟩ := exists_local_factorization (chart_isSmoothParametrization d) hu
    (parametrization_contDiffAt hφ hz) (parametrization_eventually_mem hφ hz) hdu.symm
  have hgd : DifferentiableAt ℝ g z := hg.differentiableAt (by simp)
  have hcomp := fderiv_eq_comp_of_eventually ((param_contDiffAt d hu).differentiableAt (by simp))
    hgd hgu (hgev.mono fun _ h => h.2)
  have hread : DifferentiableAt ℝ (d.pullback f) u :=
    (pullback_contDiffAt hf d hu (hdu ▸ hO')).differentiableAt (by simp)
  have hcomp' := fderiv_eq_comp_of_eventually (c := f ∘ φ) hread hgd hgu (by
    filter_upwards [hgev] with z' h
    show f (d.param (g z')) = f (φ z')
    rw [h.2])
  rw [hspec d u hu hdu (fderiv ℝ g z a) v (by simp [hv, hcomp]), hcomp']
  rfl
omit [NormedSpace ℝ E] in
private theorem isRelativelyOpen_inter {N A O' : Set E}
    (h : Matrices.ComplexMatrix2.IsRelativelyOpen N A) (hs : A ⊆ O') :
    Matrices.ComplexMatrix2.IsRelativelyOpen (O' ∩ N) A := by
  obtain ⟨O₂, hO₂, rfl⟩ := h
  refine ⟨O₂, hO₂, ?_⟩
  ext x
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1, hs ⟨h1, h2⟩, h2⟩
  · rintro ⟨h1, -, h2⟩
    exact ⟨h1, h2⟩
private theorem isChartedSubset_of_isRelativelyOpen {M O : Set E} (hM : IsChartedSubset M)
    (hO : Matrices.ComplexMatrix2.IsRelativelyOpen M O) : IsChartedSubset O := by
  obtain ⟨O', hO', rfl⟩ := hO
  intro x hx
  obtain ⟨c, u, hu, rfl⟩ := hM x hx.2
  refine ⟨{ dim := c.dim
            source := c.source ∩ c.param ⁻¹' O'
            param := c.param
            isOpen_source :=
              c.contDiffOn_param.continuousOn.isOpen_inter_preimage c.isOpen_source hO'
            contDiffOn_param := c.contDiffOn_param.mono inter_subset_left
            injective_fderiv_param := fun w hw => c.injective_fderiv_param w hw.1
            injOn_param := c.injOn_param.mono inter_subset_left
            isRelativelyOpen_image := fun W hW hWo =>
              isRelativelyOpen_inter (c.isRelativelyOpen_image W (hW.trans inter_subset_left) hWo)
                (by
                  rintro _ ⟨w, hw, rfl⟩
                  exact (hW hw).2) }, u, ⟨hu, hx.1⟩, rfl⟩
private theorem isSmoothParametrization_restrict [FiniteDimensional ℝ P] {N N' : Set E}
    {O : Set P} {φ : P → E} (hφ : IsSmoothParametrization N O φ)
    (hN : Matrices.ComplexMatrix2.IsRelativelyOpen N N') :
    IsSmoothParametrization N' (O ∩ φ ⁻¹' N') φ := by
  obtain ⟨⟨hO, h2, hinj, hmaps, hD, himg⟩, hsm⟩ := hφ
  obtain ⟨O'', hO'', rfl⟩ := hN
  have hset : O ∩ φ ⁻¹' (O'' ∩ N) = O ∩ φ ⁻¹' O'' := by
    ext w
    constructor
    · rintro ⟨h1, h3, -⟩
      exact ⟨h1, h3⟩
    · rintro ⟨h1, h3⟩
      exact ⟨h1, h3, hmaps h1⟩
  refine ⟨⟨?_, h2.mono inter_subset_left, hinj.mono inter_subset_left, fun w hw => hw.2,
    fun w hw => hD w hw.1, fun W hW hWo => isRelativelyOpen_inter
      (himg W (hW.trans inter_subset_left) hWo) ?_⟩, hsm.mono inter_subset_left⟩
  · rw [hset]
    exact hsm.continuousOn.isOpen_inter_preimage hO hO''
  · rintro _ ⟨w, hw, rfl⟩
    exact (hW hw).2.1
theorem localSmoothCalculus_holds : LocalSmoothCalculus := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · introv hφ hz
    exact exists_smooth_localInverse hφ hz
  · introv hM hf hc hev hu
    exact comp_contDiffAt_of_mem hM hf hc hev hu
  · introv hM hφ hz
    exact tangentSpace_eq_range hM hφ hz
  · introv hM hf hφ hz hO' hv
    exact tangentDifferential_eq v hM hf hφ hz hO' hv
  · introv hM hO
    exact isChartedSubset_of_isRelativelyOpen hM hO
  · introv
    exact chart_isSmoothParametrization c
  · introv hφ hN
    exact isSmoothParametrization_restrict hφ hN
end YangMills.Construction.Manifolds
end
