import YangMills.Construction.Towers.CoordinatesOfTwoSubmersions
import YangMills.Construction.Towers.SmoothMapsNearAPointOfASubmanifold
import Mathlib
set_option autoImplicit false
open Set Filter
open scoped ContDiff Topology
noncomputable section
namespace YangMills.Construction
open Manifolds Matrices.EmbeddedSubmanifold
namespace SubmersionCoordinates
section Parametrizations
variable {E E' : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {P Q : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
  [NormedAddCommGroup Q] [NormedSpace ℝ Q] [FiniteDimensional ℝ Q]
theorem parametrization_contDiffAt {N : Set E} {O : Set P} {φ : P → E}
    (h : IsSmoothParametrization N O φ) {z : P} (hz : z ∈ O) : ContDiffAt ℝ ∞ φ z :=
  h.2.contDiffAt (h.1.1.mem_nhds hz)
theorem parametrization_hasFDerivAt {N : Set E} {O : Set P} {φ : P → E}
    (h : IsSmoothParametrization N O φ) {z : P} (hz : z ∈ O) :
    HasFDerivAt φ (fderiv ℝ φ z) z :=
  ((parametrization_contDiffAt h hz).differentiableAt (by simp)).hasFDerivAt
theorem parametrization_mem {N : Set E} {O : Set P} {φ : P → E}
    (h : IsSmoothParametrization N O φ) {z : P} (hz : z ∈ O) : φ z ∈ N :=
  h.1.2.2.2.1 hz
theorem parametrization_eventually_mem {N : Set E} {O : Set P} {φ : P → E}
    (h : IsSmoothParametrization N O φ) {z : P} (hz : z ∈ O) : ∀ᶠ x in 𝓝 z, φ x ∈ N := by
  filter_upwards [h.1.1.mem_nhds hz] with x hx using parametrization_mem h hx
theorem parametrization_restrict {N : Set E} {O O' : Set P} {φ : P → E}
    (h : IsSmoothParametrization N O φ) (hO' : IsOpen O') (hsub : O' ⊆ O) :
    IsSmoothParametrization N O' φ := by
  obtain ⟨⟨_, h2, hinj, hmaps, hd, himg⟩, hs⟩ := h
  exact ⟨⟨hO', h2.mono hsub, hinj.mono hsub, hmaps.mono_left hsub, fun z hz => hd z (hsub hz),
    fun W hW hWo => himg W (hW.trans hsub) hWo⟩, hs.mono hsub⟩
theorem parametrization_comp_linearEquiv {N : Set E} {O : Set P} {φ : P → E}
    (h : IsSmoothParametrization N O φ) (e : Q ≃L[ℝ] P) :
    IsSmoothParametrization N (e ⁻¹' O) (φ ∘ e) := by
  have hdiff := fun z (hz : e z ∈ O) => parametrization_hasFDerivAt h hz
  obtain ⟨⟨hO, h2, hinj, hmaps, hd, himg⟩, hs⟩ := h
  refine ⟨⟨hO.preimage e.continuous, h2.comp e.contDiff.contDiffOn (fun _ h => h), ?_,
    fun z hz => hmaps hz, ?_, ?_⟩, hs.comp e.contDiff.contDiffOn (fun _ h => h)⟩
  · intro a ha b hb hab
    exact e.injective (hinj ha hb hab)
  · intro z hz
    have hc := (hdiff z hz).comp z e.hasFDerivAt
    rw [hc.fderiv, ContinuousLinearMap.coe_comp]
    exact (hd _ hz).comp e.injective
  · intro W hW hWo
    rw [image_comp]
    exact himg _ (image_subset_iff.2 hW) (e.toHomeomorph.isOpenMap W hWo)
theorem parametrization_slice {N : Set E} {A : Set P} {B : Set Q} {φ : P × Q → E} {g : E → E'}
    {κ : P → E'} (h : IsSmoothParametrization N (A ×ˢ B) φ) (hA : IsOpen A) (hB : IsOpen B)
    (hκ : InjOn κ A) (hg : ∀ p ∈ A, ∀ q ∈ B, g (φ (p, q)) = κ p) {p : P} (hp : p ∈ A) :
    IsSmoothParametrization (fiber N g (κ p)) B fun q => φ (p, q) := by
  have hdiff := fun z (hz : z ∈ A ×ˢ B) => parametrization_hasFDerivAt h hz
  obtain ⟨⟨hO, h2, hinj, hmaps, hd, himg⟩, hs⟩ := h
  have hin : ∀ n : WithTop ℕ∞, ContDiff ℝ n fun q : Q => (p, q) :=
    fun n => contDiff_const.prodMk contDiff_id
  have hmem : MapsTo (fun q : Q => (p, q)) B (A ×ˢ B) := fun q hq => ⟨hp, hq⟩
  have hfib : ∀ x, x ∈ fiber N g (κ p) ↔ x ∈ N ∧ g x = κ p := fun _ => Iff.rfl
  refine ⟨⟨hB, h2.comp (hin 2).contDiffOn hmem, ?_, ?_, ?_, ?_⟩,
    hs.comp (hin ∞).contDiffOn hmem⟩
  · intro a ha b hb hab
    exact (Prod.ext_iff.1 (hinj (hmem ha) (hmem hb) hab)).2
  · intro q hq
    exact (hfib _).2 ⟨hmaps (hmem hq), hg p hp q hq⟩
  · intro q hq
    have hinr : HasFDerivAt (fun q : Q => (p, q)) (ContinuousLinearMap.inr ℝ P Q) q :=
      hasFDerivAt_prodMk_right p q
    have hc := (hdiff (p, q) (hmem hq)).comp q hinr
    have hc' : fderiv ℝ (fun q => φ (p, q)) q =
        (fderiv ℝ φ (p, q)).comp (ContinuousLinearMap.inr ℝ P Q) := hc.fderiv
    rw [hc', ContinuousLinearMap.coe_comp]
    exact (hd _ (hmem hq)).comp fun a b hab => (Prod.ext_iff.1 hab).2
  · intro W hW hWo
    obtain ⟨O, hOo, hOeq⟩ := himg (A ×ˢ W) (prod_mono_right hW) (hA.prod hWo)
    refine ⟨O, hOo, ?_⟩
    ext x
    constructor
    · rintro ⟨q, hq, rfl⟩
      have hx : φ (p, q) ∈ φ '' (A ×ˢ W) := ⟨_, ⟨hp, hq⟩, rfl⟩
      rw [hOeq] at hx
      exact ⟨hx.1, (hfib _).2 ⟨hmaps (hmem (hW hq)), hg p hp q (hW hq)⟩⟩
    · rintro ⟨hxO, hx⟩
      obtain ⟨hxN, hgx⟩ := (hfib _).1 hx
      have hx' : x ∈ φ '' (A ×ˢ W) := by
        rw [hOeq]
        exact ⟨hxO, hxN⟩
      obtain ⟨⟨p', q⟩, ⟨hp', hq⟩, rfl⟩ := hx'
      have hpp : p' = p := hκ hp' hp ((hg p' hp' q (hW hq)).symm.trans hgx)
      subst hpp
      exact ⟨q, hq, rfl⟩
def chartOfParametrization {d : ℕ} {N : Set E} {O : Set (Fin d → ℝ)} {φ : (Fin d → ℝ) → E}
    (h : IsSmoothParametrization N O φ) : Chart N where
  dim := d
  source := O
  param := φ
  isOpen_source := h.1.1
  contDiffOn_param := h.2
  injective_fderiv_param := h.1.2.2.2.2.1
  injOn_param := h.1.2.2.1
  isRelativelyOpen_image := h.1.2.2.2.2.2
end Parametrizations
section Inverse
variable {D P : Type} [NormedAddCommGroup D] [NormedSpace ℝ D] [FiniteDimensional ℝ D]
  [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
omit [FiniteDimensional ℝ P] in
theorem exists_linearEquiv_prod_kernelCoords (L : D →L[ℝ] P) (hL : Function.Surjective L) :
    ∃ (d : ℕ) (ℓ : D →L[ℝ] (Fin d → ℝ)) (e : D ≃L[ℝ] P × (Fin d → ℝ)),
      ∀ a, e a = (L a, ℓ a) := by
  obtain ⟨K, hK⟩ : ∃ K : Submodule ℝ D, K = LinearMap.ker (L : D →ₗ[ℝ] P) := ⟨_, rfl⟩
  have hKL : ∀ a, a ∈ K ↔ L a = 0 := fun a => by rw [hK]; exact LinearMap.mem_ker
  obtain ⟨g, hg⟩ := K.subtype.exists_leftInverse_of_injective K.ker_subtype
  obtain ⟨eK, -⟩ : ∃ eK : K ≃ₗ[ℝ] (Fin (Module.finrank ℝ K) → ℝ), True :=
    ⟨(Module.finBasis ℝ K).equivFun, trivial⟩
  obtain ⟨ℓ, hℓ⟩ : ∃ ℓ : D →L[ℝ] (Fin (Module.finrank ℝ K) → ℝ), ∀ a, ℓ a = eK (g a) :=
    ⟨LinearMap.toContinuousLinearMap (eK.toLinearMap ∘ₗ g), fun _ => rfl⟩
  have hℓK : ∀ k : K, ℓ k = eK k := fun k => by
    rw [hℓ]
    congr 1
    exact LinearMap.congr_fun hg k
  have hbij : Function.Bijective (L.prod ℓ : D →L[ℝ] P × (Fin (Module.finrank ℝ K) → ℝ)) := by
    constructor
    · intro a b hab
      have h1 : L a = L b := congrArg Prod.fst hab
      have h2 : ℓ a = ℓ b := congrArg Prod.snd hab
      have hk : a - b ∈ K := (hKL _).2 (by rw [map_sub, h1, sub_self])
      have h3 : eK ⟨a - b, hk⟩ = 0 := by
        rw [← hℓK]
        show ℓ (a - b) = 0
        rw [map_sub, h2, sub_self]
      have h4 : (⟨a - b, hk⟩ : K) = 0 := by simpa using h3
      exact sub_eq_zero.1 (congrArg Subtype.val h4)
    · rintro ⟨p, t⟩
      obtain ⟨a, rfl⟩ := hL p
      obtain ⟨k, hk⟩ := eK.surjective (t - ℓ a)
      refine ⟨a + k, ?_⟩
      have hLk : L k = 0 := (hKL _).1 k.2
      show (L (a + k), ℓ (a + k)) = (L a, t)
      rw [map_add, map_add, hLk, hℓK, hk, add_zero, add_sub_cancel]
  exact ⟨_, ℓ, (LinearEquiv.ofBijective
    ((L.prod ℓ : D →L[ℝ] P × (Fin (Module.finrank ℝ K) → ℝ)) :
      D →ₗ[ℝ] P × (Fin (Module.finrank ℝ K) → ℝ)) hbij).toContinuousLinearEquiv, fun a => rfl⟩
omit [FiniteDimensional ℝ P] in
theorem exists_local_smooth_inverse {Θ : D → P} {U₁ : Set D} {u : D} (hU₁ : IsOpen U₁)
    (hu : u ∈ U₁) (hΘ : ContDiffOn ℝ ∞ Θ U₁) (e : D ≃L[ℝ] P)
    (he : fderiv ℝ Θ u = (e : D →L[ℝ] P)) :
    ∃ (T : Set P) (ψ : P → D), IsOpen T ∧ Θ u ∈ T ∧ ψ (Θ u) = u ∧ InjOn ψ T ∧
      (∀ z ∈ T, ψ z ∈ U₁ ∧ Θ (ψ z) = z ∧ ContDiffAt ℝ ∞ ψ z ∧
        Function.Injective (fderiv ℝ ψ z)) ∧
      ∀ W ⊆ T, IsOpen W → IsOpen (ψ '' W) := by
  have : CompleteSpace D := FiniteDimensional.complete ℝ D
  have hat : ContDiffAt ℝ ∞ Θ u := hΘ.contDiffAt (hU₁.mem_nhds hu)
  have hd : HasFDerivAt Θ (e : D →L[ℝ] P) u := by
    rw [← he]
    exact (hat.differentiableAt (by simp)).hasFDerivAt
  obtain ⟨h, hcoe, hus⟩ : ∃ h : OpenPartialHomeomorph D P, (h : D → P) = Θ ∧ u ∈ h.source :=
    ⟨hat.toOpenPartialHomeomorph Θ hd (by simp), hat.toOpenPartialHomeomorph_coe hd _,
      hat.mem_toOpenPartialHomeomorph_source hd _⟩
  have hcont : ContinuousAt (fderiv ℝ Θ) u :=
    (hΘ.continuousOn_fderiv_of_isOpen hU₁ (by simp)).continuousAt (hU₁.mem_nhds hu)
  have hpre : fderiv ℝ Θ ⁻¹' range ((↑) : (D ≃L[ℝ] P) → D →L[ℝ] P) ∈ 𝓝 u :=
    hcont.preimage_mem_nhds (by rw [he]; exact ContinuousLinearEquiv.nhds e)
  obtain ⟨S, hSsub, hS, huS⟩ := mem_nhds_iff.1
    (inter_mem (inter_mem (hU₁.mem_nhds hu) (h.open_source.mem_nhds hus)) hpre)
  have hright : ∀ z ∈ h.target, Θ (h.symm z) = z := fun z hz => by
    have := h.right_inv hz
    rwa [hcoe] at this
  have hleft : h.symm (Θ u) = u := by
    have := h.left_inv hus
    rwa [hcoe] at this
  have hmapu : Θ u ∈ h.target := by
    have := h.map_source hus
    rwa [hcoe] at this
  refine ⟨h.target ∩ h.symm ⁻¹' S, h.symm, h.isOpen_inter_preimage_symm hS, ⟨hmapu, ?_⟩, hleft,
    ?_, ?_, ?_⟩
  · show h.symm (Θ u) ∈ S
    rw [hleft]
    exact huS
  · exact h.symm.injOn.mono fun z hz => hz.1
  · intro z hz
    obtain ⟨⟨hzU, -⟩, e', he'⟩ := hSsub hz.2
    have hat' : ContDiffAt ℝ ∞ Θ (h.symm z) := hΘ.contDiffAt (hU₁.mem_nhds hzU)
    have hd' : HasFDerivAt h (e' : D →L[ℝ] P) (h.symm z) := by
      rw [hcoe, he']
      exact (hat'.differentiableAt (by simp)).hasFDerivAt
    have hsymm : HasFDerivAt h.symm (e'.symm : P →L[ℝ] D) z := h.hasFDerivAt_symm hz.1 hd'
    refine ⟨hzU, hright z hz.1, h.contDiffAt_symm hz.1 hd' (by rw [hcoe]; exact hat'), ?_⟩
    rw [hsymm.fderiv]
    exact e'.symm.injective
  · intro W hW hWo
    exact h.symm.isOpen_image_of_subset_source hWo fun z hz => (hW hz).1
end Inverse
section Submersions
variable {E₁ E₂ E₃ : Type} [NormedAddCommGroup E₁] [NormedSpace ℝ E₁]
  [NormedAddCommGroup E₂] [NormedSpace ℝ E₂] [NormedAddCommGroup E₃] [NormedSpace ℝ E₃]
  {D P : Type} [NormedAddCommGroup D] [NormedSpace ℝ D] [FiniteDimensional ℝ D]
  [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
theorem contDiffAt_comp_parametrization (H : LocalSmoothCalculus) {𝒳 : Set E₁}
    {f : E₁ → E₂} (hX : IsChartedSubset 𝒳) (hf : IsSmoothOnOpen 𝒳 𝒳 f) {U : Set D} {φ : D → E₁}
    (hφ : IsSmoothParametrization 𝒳 U φ) {z : D} (hz : z ∈ U) : ContDiffAt ℝ ∞ (f ∘ φ) z :=
  H.2.1 E₁ E₂ D 𝒳 𝒳 f φ z hX hf (parametrization_contDiffAt hφ hz)
    (parametrization_eventually_mem hφ hz) (parametrization_mem hφ hz)
theorem range_tangentDifferential_eq (H : LocalSmoothCalculus) {𝒳 : Set E₁}
    {f : E₁ → E₂} (hX : IsChartedSubset 𝒳) (hf : IsSmoothOnOpen 𝒳 𝒳 f) {U : Set D} {φ : D → E₁}
    (hφ : IsSmoothParametrization 𝒳 U φ) {z : D} (hz : z ∈ U) :
    LinearMap.range (tangentDifferential 𝒳 f (φ z)) =
      LinearMap.range (fderiv ℝ (f ∘ φ) z : D →ₗ[ℝ] E₂) := by
  have hT := H.2.2.1 E₁ D 𝒳 U φ z hX hφ hz
  have hzX := parametrization_mem hφ hz
  ext y
  constructor
  · rintro ⟨v, rfl⟩
    have hv : (v : E₁) ∈ LinearMap.range (fderiv ℝ φ z : D →ₗ[ℝ] E₁) := hT ▸ v.2
    obtain ⟨a, ha⟩ := hv
    exact ⟨a, (H.2.2.2.1 E₁ E₂ D 𝒳 𝒳 f U φ z a v hX hf hφ hz hzX ha.symm).symm⟩
  · rintro ⟨a, rfl⟩
    have hmem : fderiv ℝ φ z a ∈ tangentSpace 𝒳 (φ z) := by
      rw [hT]
      exact ⟨a, rfl⟩
    exact ⟨⟨_, hmem⟩, H.2.2.2.1 E₁ E₂ D 𝒳 𝒳 f U φ z a ⟨_, hmem⟩ hX hf hφ hz hzX rfl⟩
theorem exists_lift_through_submersion (H : LocalSmoothCalculus) {𝒳 : Set E₁} {𝒴 : Set E₂}
    {m : E₁ → E₂} (hX : IsChartedSubset 𝒳) (hY : IsChartedSubset 𝒴)
    (hm : IsSmoothSubmersion 𝒳 𝒴 m) {U : Set D} {φ : D → E₁}
    (hφ : IsSmoothParametrization 𝒳 U φ) {z : D} (hz : z ∈ U)
    {O : Set P} {η : P → E₂} (hη : IsSmoothParametrization 𝒴 O η) {p : P} (hp : p ∈ O)
    (hpz : η p = m (φ z)) :
    ∃ (U₁ : Set D) (μ : D → P), IsOpen U₁ ∧ z ∈ U₁ ∧ U₁ ⊆ U ∧ ContDiffOn ℝ ∞ μ U₁ ∧
      MapsTo μ U₁ O ∧ (∀ u ∈ U₁, η (μ u) = m (φ u)) ∧ μ z = p ∧
      Function.Surjective (fderiv ℝ μ z) := by
  obtain ⟨Ω, ρ, hΩ, hpΩ, hρ, hinv⟩ := H.1 E₂ P 𝒴 O η p hη hp
  have hU := hφ.1.1
  have hmφ : ContDiffOn ℝ ∞ (m ∘ φ) U :=
    fun u hu => (contDiffAt_comp_parametrization H hX hm.smooth hφ hu).contDiffWithinAt
  have hU₁ : IsOpen (U ∩ (m ∘ φ) ⁻¹' Ω) := hmφ.continuousOn.isOpen_inter_preimage hU hΩ
  have hval : ∀ u ∈ U ∩ (m ∘ φ) ⁻¹' Ω, ρ (m (φ u)) ∈ O ∧ η (ρ (m (φ u))) = m (φ u) :=
    fun u hu => hinv _ ⟨hm.mapsTo (parametrization_mem hφ hu.1), hu.2⟩
  have hzU : z ∈ U ∩ (m ∘ φ) ⁻¹' Ω := ⟨hz, by
    show m (φ z) ∈ Ω
    rw [← hpz]
    exact hpΩ⟩
  have hμz : ρ (m (φ z)) = p := hη.1.2.2.1 (hval z hzU).1 hp ((hval z hzU).2.trans hpz.symm)
  have hμ : ContDiffOn ℝ ∞ (ρ ∘ (m ∘ φ)) (U ∩ (m ∘ φ) ⁻¹' Ω) :=
    hρ.comp (hmφ.mono inter_subset_left) (fun u hu => hu.2)
  refine ⟨_, ρ ∘ (m ∘ φ), hU₁, hzU, inter_subset_left, hμ, fun u hu => (hval u hu).1,
    fun u hu => (hval u hu).2, hμz, ?_⟩
  have hμd : HasFDerivAt (ρ ∘ (m ∘ φ)) (fderiv ℝ (ρ ∘ (m ∘ φ)) z) z :=
    ((hμ.contDiffAt (hU₁.mem_nhds hzU)).differentiableAt (by simp)).hasFDerivAt
  have hηd : HasFDerivAt η (fderiv ℝ η p) ((ρ ∘ (m ∘ φ)) z) := by
    rw [show (ρ ∘ (m ∘ φ)) z = p from hμz]
    exact parametrization_hasFDerivAt hη hp
  have hc := hηd.comp z hμd
  have hev : (m ∘ φ) =ᶠ[𝓝 z] η ∘ (ρ ∘ (m ∘ φ)) := by
    filter_upwards [hU₁.mem_nhds hzU] with u hu using ((hval u hu).2).symm
  have hfd := (hc.congr_of_eventuallyEq hev).fderiv
  have hrange : LinearMap.range (fderiv ℝ (m ∘ φ) z : D →ₗ[ℝ] E₂) =
      LinearMap.range (fderiv ℝ η p : P →ₗ[ℝ] E₂) := by
    rw [← range_tangentDifferential_eq H hX hm.smooth hφ hz,
      hm.differential_surjective _ (parametrization_mem hφ hz),
      ← hpz, H.2.2.1 E₂ P 𝒴 O η p hY hη hp]
  intro y
  have hy : (fderiv ℝ η p) y ∈ LinearMap.range (fderiv ℝ (m ∘ φ) z : D →ₗ[ℝ] E₂) := by
    rw [hrange]
    exact ⟨y, rfl⟩
  obtain ⟨a, ha⟩ := hy
  refine ⟨a, hη.1.2.2.2.2.1 p hp ?_⟩
  have ha' : (fderiv ℝ (m ∘ φ) z) a = (fderiv ℝ η p) y := ha
  rw [hfd] at ha'
  exact ha'
theorem isSmoothSubmersion_comp (H : LocalSmoothCalculus) {𝒳 : Set E₁}
    {𝒴 : Set E₂} {𝒵 : Set E₃} {m : E₁ → E₂} {n : E₂ → E₃} (hX : IsChartedSubset 𝒳)
    (hY : IsChartedSubset 𝒴) (hm : IsSmoothSubmersion 𝒳 𝒴 m) (hn : IsSmoothSubmersion 𝒴 𝒵 n) :
    IsSmoothSubmersion 𝒳 𝒵 (n ∘ m) := by
  have hsm : IsSmoothOnOpen 𝒳 𝒳 (n ∘ m) := by
    refine ⟨⟨univ, isOpen_univ, (univ_inter _).symm⟩, fun c u hu => ?_⟩
    have hu' : u ∈ c.source := (show u ∈ c.source ∩ c.param ⁻¹' 𝒳 from hu).1
    have hφ := H.2.2.2.2.2.1 E₁ 𝒳 c
    have hat : ContDiffAt ℝ ∞ (n ∘ (m ∘ c.param)) u :=
      H.2.1 E₂ E₃ _ 𝒴 𝒴 n (m ∘ c.param) u hY hn.smooth
        (contDiffAt_comp_parametrization H hX hm.smooth hφ hu')
        ((parametrization_eventually_mem hφ hu').mono fun _ h => hm.mapsTo h)
        (hm.mapsTo (parametrization_mem hφ hu'))
    exact hat.contDiffWithinAt
  refine ⟨fun x hx => hn.mapsTo (hm.mapsTo hx), hsm, ?_⟩
  intro x hx
  obtain ⟨c, u, hu, rfl⟩ := hX x hx
  have hφ := H.2.2.2.2.2.1 E₁ 𝒳 c
  obtain ⟨c', p, hp, hcp⟩ := hY _ (hm.mapsTo hx)
  have hψ := H.2.2.2.2.2.1 E₂ 𝒴 c'
  obtain ⟨U₁, μ, hU₁, huU₁, -, hμ, -, hμη, hμu, hsurj⟩ :=
    exists_lift_through_submersion H hX hY hm hφ hu hψ hp hcp
  have h1 : HasFDerivAt (n ∘ c'.param) (fderiv ℝ (n ∘ c'.param) p) (μ u) := by
    rw [hμu]
    exact ((contDiffAt_comp_parametrization H hY hn.smooth hψ hp).differentiableAt
      (by simp)).hasFDerivAt
  have h2 : HasFDerivAt μ (fderiv ℝ μ u) u :=
    ((hμ.contDiffAt (hU₁.mem_nhds huU₁)).differentiableAt (by simp)).hasFDerivAt
  have hev : ((n ∘ m) ∘ c.param) =ᶠ[𝓝 u] (n ∘ c'.param) ∘ μ := by
    filter_upwards [hU₁.mem_nhds huU₁] with u' hu'
    show n (m (c.param u')) = n (c'.param (μ u'))
    rw [hμη u' hu']
  have hfd := ((h1.comp u h2).congr_of_eventuallyEq hev).fderiv
  have hT : tangentSpace 𝒵 ((n ∘ m) (c.param u)) =
      LinearMap.range (fderiv ℝ (n ∘ c'.param) p : (Fin c'.dim → ℝ) →ₗ[ℝ] E₃) := by
    have h3 := hn.differential_surjective _ (parametrization_mem hψ hp)
    rw [range_tangentDifferential_eq H hY hn.smooth hψ hp, hcp] at h3
    exact h3.symm
  rw [range_tangentDifferential_eq H hX hsm hφ hu, hT, hfd]
  ext y
  constructor
  · rintro ⟨a, rfl⟩
    exact ⟨fderiv ℝ μ u a, rfl⟩
  · rintro ⟨b, rfl⟩
    obtain ⟨a, rfl⟩ := hsurj b
    exact ⟨a, rfl⟩
theorem exists_straightening_parametrization (H : LocalSmoothCalculus) {𝒳 : Set E₁}
    {𝒴 : Set E₂} {m : E₁ → E₂} (hX : IsChartedSubset 𝒳) (hY : IsChartedSubset 𝒴)
    (hm : IsSmoothSubmersion 𝒳 𝒴 m) {O : Set P} {η : P → E₂}
    (hη : IsSmoothParametrization 𝒴 O η) {p : P} (hp : p ∈ O) {x₀ : E₁} (hx₀ : x₀ ∈ 𝒳)
    (hpx : η p = m x₀) :
    ∃ (d : ℕ) (T : Set (P × (Fin d → ℝ))) (t₀ : Fin d → ℝ) (ξ : P × (Fin d → ℝ) → E₁),
      IsSmoothParametrization 𝒳 T ξ ∧ (p, t₀) ∈ T ∧ ξ (p, t₀) = x₀ ∧
        ∀ z ∈ T, z.1 ∈ O ∧ m (ξ z) = η z.1 := by
  obtain ⟨c, u, hu, rfl⟩ := hX x₀ hx₀
  have hφ := H.2.2.2.2.2.1 E₁ 𝒳 c
  obtain ⟨U₁, μ, hU₁, huU₁, hsub, hμ, hμO, hμη, hμu, hsurj⟩ :=
    exists_lift_through_submersion H hX hY hm hφ hu hη hp hpx
  have hμd : HasFDerivAt μ (fderiv ℝ μ u) u :=
    ((hμ.contDiffAt (hU₁.mem_nhds huU₁)).differentiableAt (by simp)).hasFDerivAt
  obtain ⟨d, ℓ, e, he⟩ := exists_linearEquiv_prod_kernelCoords (fderiv ℝ μ u) hsurj
  have hΘ : ContDiffOn ℝ ∞ (fun a => (μ a, ℓ a)) U₁ := hμ.prodMk ℓ.contDiff.contDiffOn
  have hΘd : fderiv ℝ (fun a => (μ a, ℓ a)) u = (e : _ →L[ℝ] P × (Fin d → ℝ)) := by
    rw [(hμd.prodMk ℓ.hasFDerivAt).fderiv]
    ext1 a
    exact (he a).symm
  obtain ⟨T, ψ, hT, huT, hψu, hψinj, hψ, hψopen⟩ := exists_local_smooth_inverse hU₁ huU₁ hΘ e hΘd
  have hψU : ∀ z ∈ T, ψ z ∈ c.source := fun z hz => hsub (hψ z hz).1
  have hat : ∀ z ∈ T, ContDiffAt ℝ ∞ (c.param ∘ ψ) z := fun z hz =>
    (parametrization_contDiffAt hφ (hψU z hz)).comp z (hψ z hz).2.2.1
  refine ⟨d, T, ℓ u, c.param ∘ ψ, ⟨⟨hT, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩, ?_, ?_, ?_⟩
  · exact fun z hz => ((hat z hz).of_le ENat.LEInfty.out).contDiffWithinAt
  · intro a ha b hb hab
    exact hψinj ha hb (hφ.1.2.2.1 (hψU a ha) (hψU b hb) hab)
  · exact fun z hz => parametrization_mem hφ (hψU z hz)
  · intro z hz
    have hψd : HasFDerivAt ψ (fderiv ℝ ψ z) z :=
      ((hψ z hz).2.2.1.differentiableAt (by simp)).hasFDerivAt
    rw [((parametrization_hasFDerivAt hφ (hψU z hz)).comp z hψd).fderiv,
      ContinuousLinearMap.coe_comp]
    exact (hφ.1.2.2.2.2.1 _ (hψU z hz)).comp (hψ z hz).2.2.2
  · intro W hW hWo
    rw [image_comp]
    exact hφ.1.2.2.2.2.2 _ (image_subset_iff.2 fun z hz => hψU z (hW hz)) (hψopen W hW hWo)
  · exact fun z hz => (hat z hz).contDiffWithinAt
  · have : (p, ℓ u) = (μ u, ℓ u) := by rw [hμu]
    rw [this]
    exact huT
  · have : (p, ℓ u) = (μ u, ℓ u) := by rw [hμu]
    rw [this]
    show c.param (ψ (μ u, ℓ u)) = _
    rw [hψu]
  · intro z hz
    obtain ⟨hzU, hzΘ, -⟩ := hψ z hz
    have h1 : μ (ψ z) = z.1 := congrArg Prod.fst hzΘ
    refine ⟨h1 ▸ hμO hzU, ?_⟩
    rw [← h1]
    exact (hμη _ hzU).symm
theorem fiber_isChartedSubset (H : LocalSmoothCalculus) {𝒳 : Set E₁}
    {𝒴 : Set E₂} {m : E₁ → E₂} (y : E₂) (hX : IsChartedSubset 𝒳) (hY : IsChartedSubset 𝒴)
    (hm : IsSmoothSubmersion 𝒳 𝒴 m) : IsChartedSubset (fiber 𝒳 m y) := by
  rintro x ⟨hx, rfl⟩
  obtain ⟨c, p, hp, hcp⟩ := hY _ (hm.mapsTo hx)
  have hη := H.2.2.2.2.2.1 E₂ 𝒴 c
  obtain ⟨d, T, t₀, ξ, hξ, hT, hξx, hξT⟩ :=
    exists_straightening_parametrization H hX hY hm hη hp hx hcp
  obtain ⟨A, B, hA, hB, hpA, htB, hsub⟩ := isOpen_prod_iff.1 hξ.1.1 p t₀ hT
  have hAO : A ⊆ c.source := fun a ha => (hξT (a, t₀) (hsub ⟨ha, htB⟩)).1
  have hs := parametrization_slice (parametrization_restrict hξ (hA.prod hB) hsub) hA hB
    (κ := c.param) (g := m) (hη.1.2.2.1.mono hAO)
    (fun a ha b hb => (hξT (a, b) (hsub ⟨ha, hb⟩)).2) hpA
  rw [hcp] at hs
  exact ⟨chartOfParametrization hs, t₀, htB, hξx⟩
theorem exists_adapted_coordinates (H : LocalSmoothCalculus) {𝒳 : Set E₁}
    {𝒴 : Set E₂} {𝒵 : Set E₃} {m : E₁ → E₂} {n : E₂ → E₃} {x₀ : E₁} (hX : IsChartedSubset 𝒳)
    (hY : IsChartedSubset 𝒴) (hZ : IsChartedSubset 𝒵) (hm : IsSmoothSubmersion 𝒳 𝒴 m)
    (hn : IsSmoothSubmersion 𝒴 𝒵 n) (hx₀ : x₀ ∈ 𝒳) :
    ∃ (a b c : ℕ) (Ow : Set (Fin a → ℝ)) (Ov : Set (Fin b → ℝ)) (Ou : Set (Fin c → ℝ))
      (w₀ : Fin a → ℝ) (v₀ : Fin b → ℝ) (u₀ : Fin c → ℝ)
      (ε : (Fin a → ℝ) → E₃) (η : (Fin a → ℝ) × (Fin b → ℝ) → E₂)
      (ξ : (Fin a → ℝ) × (Fin b → ℝ) × (Fin c → ℝ) → E₁),
      w₀ ∈ Ow ∧ v₀ ∈ Ov ∧ u₀ ∈ Ou ∧ ξ (w₀, v₀, u₀) = x₀ ∧
      IsOpen Ow ∧ IsOpen Ov ∧ IsOpen Ou ∧
      IsSmoothParametrization 𝒵 Ow ε ∧
      IsSmoothParametrization 𝒴 (Ow ×ˢ Ov) η ∧
      IsSmoothParametrization 𝒳 (Ow ×ˢ Ov ×ˢ Ou) ξ ∧
      (∀ w ∈ Ow, ∀ v ∈ Ov, n (η (w, v)) = ε w) ∧
      (∀ w ∈ Ow, ∀ v ∈ Ov, ∀ u ∈ Ou, m (ξ (w, v, u)) = η (w, v)) ∧
      (∀ w ∈ Ow, IsSmoothParametrization (fiber 𝒴 n (ε w)) Ov fun v => η (w, v)) ∧
      (∀ w ∈ Ow, IsSmoothParametrization (fiber 𝒳 (n ∘ m) (ε w)) (Ov ×ˢ Ou)
        fun p => ξ (w, p)) ∧
      (∀ w ∈ Ow, ∀ v ∈ Ov, IsSmoothParametrization (fiber 𝒳 m (η (w, v))) Ou
        fun u => ξ (w, v, u)) := by
  obtain ⟨c, w₀, hw₀, hcw⟩ := hZ (n (m x₀)) (hn.mapsTo (hm.mapsTo hx₀))
  have hε := H.2.2.2.2.2.1 E₃ 𝒵 c
  obtain ⟨b, T₁, v₀, η, hη, hT₁, hηx, hηT⟩ :=
    exists_straightening_parametrization H hY hZ hn hε hw₀ (hm.mapsTo hx₀) hcw
  obtain ⟨d, T₂, u₀, ξ₁, hξ, hT₂, hξx, hξT⟩ :=
    exists_straightening_parametrization H hX hY hm hη hT₁ hx₀ hηx
  obtain ⟨A, Ou, hA, hOu, hwv, hu₀, hsub⟩ := isOpen_prod_iff.1 hξ.1.1 (w₀, v₀) u₀ hT₂
  obtain ⟨Ow, Ov, hOw, hOv, hw, hv, hsub'⟩ := isOpen_prod_iff.1 hA w₀ v₀ hwv
  have hbox₂ : (Ow ×ˢ Ov) ×ˢ Ou ⊆ T₂ := (prod_mono_left hsub').trans hsub
  have hbox₁ : Ow ×ˢ Ov ⊆ T₁ := fun z hz => (hξT (z, u₀) (hbox₂ ⟨hz, hu₀⟩)).1
  have hbox₀ : Ow ⊆ c.source := fun w hw' => (hηT (w, v₀) (hbox₁ ⟨hw', hv⟩)).1
  have hε' := parametrization_restrict hε hOw hbox₀
  have hη' := parametrization_restrict hη (hOw.prod hOv) hbox₁
  have hξ' := parametrization_restrict hξ ((hOw.prod hOv).prod hOu) hbox₂
  have hnη : ∀ w ∈ Ow, ∀ v ∈ Ov, n (η (w, v)) = c.param w :=
    fun w hw' v hv' => (hηT (w, v) (hbox₁ ⟨hw', hv'⟩)).2
  have hmξ : ∀ z ∈ Ow ×ˢ Ov, ∀ u ∈ Ou, m (ξ₁ (z, u)) = η z :=
    fun z hz u hu => (hξT (z, u) (hbox₂ ⟨hz, hu⟩)).2
  have hξ'' : IsSmoothParametrization 𝒳 (Ow ×ˢ Ov ×ˢ Ou)
      fun p : (Fin c.dim → ℝ) × (Fin b → ℝ) × (Fin d → ℝ) => ξ₁ ((p.1, p.2.1), p.2.2) := by
    have h := parametrization_comp_linearEquiv hξ'
      (ContinuousLinearEquiv.prodAssoc ℝ (Fin c.dim → ℝ) (Fin b → ℝ) (Fin d → ℝ)).symm
    have hset : (ContinuousLinearEquiv.prodAssoc ℝ (Fin c.dim → ℝ) (Fin b → ℝ)
        (Fin d → ℝ)).symm ⁻¹' ((Ow ×ˢ Ov) ×ˢ Ou) = Ow ×ˢ Ov ×ˢ Ou := by
      ext ⟨w, v, u⟩
      simp [and_assoc]
    rw [hset] at h
    exact h
  refine ⟨c.dim, b, d, Ow, Ov, Ou, w₀, v₀, u₀, c.param, η,
    fun p => ξ₁ ((p.1, p.2.1), p.2.2), hw, hv, hu₀, hξx, hOw, hOv, hOu, hε', hη', hξ'', hnη,
    fun w hw' v hv' u hu => hmξ (w, v) ⟨hw', hv'⟩ u hu, ?_, ?_, ?_⟩
  · exact fun w hw' => parametrization_slice hη' hOw hOv hε'.1.2.2.1 hnη hw'
  · refine fun w hw' =>
      parametrization_slice hξ'' hOw (hOv.prod hOu) hε'.1.2.2.1 (g := n ∘ m) ?_ hw'
    rintro w' hw'' ⟨v, u⟩ ⟨hv', hu⟩
    show n (m (ξ₁ ((w', v), u))) = _
    rw [hmξ (w', v) ⟨hw'', hv'⟩ u hu, hnη w' hw'' v hv']
  · exact fun w hw' v hv' => parametrization_slice hξ' (hOw.prod hOv) hOu hη'.1.2.2.1 hmξ
      (p := (w, v)) ⟨hw', hv'⟩
end Submersions
theorem coordinatesOfTwoSubmersions_of_localSmoothCalculus (H : LocalSmoothCalculus) :
    Manifolds.CoordinatesOfTwoSubmersions :=
  ⟨fun _ _ _ _ _ _ _ _ _ y hX hY hm => fiber_isChartedSubset H y hX hY hm,
    fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ hX hY _ hm hn => isSmoothSubmersion_comp H hX hY hm hn,
    fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hX hY hZ hm hn hx₀ =>
      exists_adapted_coordinates H hX hY hZ hm hn hx₀⟩
end SubmersionCoordinates
end YangMills.Construction
end
