import YangMills.Construction.Matrices.LinearMapsCompositesAndCoordinatesOfRealAnalyticMapsProof
import YangMills.Construction.Matrices.UnitaryLogConjugation
import YangMills.Construction.Numerics.ExpLogNumericBounds
import Mathlib
set_option autoImplicit false
open Set Filter YangMills.Construction.Matrices.GroupLieProduct
open scoped ContDiff Matrix.Norms.L2Operator Topology
open YangMills.Construction.Coordinates.ComplexCoordinates.PowerSeriesHolomorphy
  (closedPolydisk openPolydisk monomialTerm)
noncomputable section
namespace YangMills.Construction.Matrices.LocalParametrization
open EmbeddedSubmanifold
variable {E F V : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup V] [NormedSpace ℝ V]
structure SmoothLocalParam (M : Set E) (p : E) (χ : V → E) (ℓ : E → V) (B : Set V) (D : Set E) :
    Prop where
  isOpen_src : IsOpen B
  zero_mem : (0 : V) ∈ B
  isOpen_invDom : IsOpen D
  contDiffOn_map : ContDiffOn ℝ ∞ χ B
  contDiffOn_inv : ContDiffOn ℝ ∞ ℓ D
  mapsTo : MapsTo χ B (D ∩ M)
  inv_map : ∀ Y ∈ B, ℓ (χ Y) = Y
  map_zero_eq : χ 0 = p
  isRelativelyOpen_range : ComplexMatrix2.IsRelativelyOpen M (χ '' B)
variable {M : Set E} {p : E} {χ : V → E} {ℓ : E → V} {B : Set V} {D : Set E}
theorem SmoothLocalParam.mem_invDom (hP : SmoothLocalParam M p χ ℓ B D) : p ∈ D := by
  have := (hP.mapsTo hP.zero_mem).1
  rwa [hP.map_zero_eq] at this
theorem SmoothLocalParam.contDiffAt_map (hP : SmoothLocalParam M p χ ℓ B D) {Y : V} (hY : Y ∈ B) :
    ContDiffAt ℝ ∞ χ Y :=
  hP.contDiffOn_map.contDiffAt (hP.isOpen_src.mem_nhds hY)
theorem SmoothLocalParam.contDiffAt_inv (hP : SmoothLocalParam M p χ ℓ B D) {X : E} (hX : X ∈ D) :
    ContDiffAt ℝ ∞ ℓ X :=
  hP.contDiffOn_inv.contDiffAt (hP.isOpen_invDom.mem_nhds hX)
theorem SmoothLocalParam.differentiableAt_map (hP : SmoothLocalParam M p χ ℓ B D) {Y : V}
    (hY : Y ∈ B) : DifferentiableAt ℝ χ Y :=
  (hP.contDiffAt_map hY).differentiableAt (by simp)
theorem SmoothLocalParam.differentiableAt_inv (hP : SmoothLocalParam M p χ ℓ B D) {X : E}
    (hX : X ∈ D) : DifferentiableAt ℝ ℓ X :=
  (hP.contDiffAt_inv hX).differentiableAt (by simp)
theorem SmoothLocalParam.fderiv_inv_map (hP : SmoothLocalParam M p χ ℓ B D) {Y : V} (hY : Y ∈ B)
    (v : V) : fderiv ℝ ℓ (χ Y) (fderiv ℝ χ Y v) = v := by
  have h1 : HasFDerivAt (ℓ ∘ χ) ((fderiv ℝ ℓ (χ Y)).comp (fderiv ℝ χ Y)) Y :=
    (hP.differentiableAt_inv (hP.mapsTo hY).1).hasFDerivAt.comp Y
      (hP.differentiableAt_map hY).hasFDerivAt
  have h2 : HasFDerivAt (ℓ ∘ χ) (ContinuousLinearMap.id ℝ V) Y := by
    refine (hasFDerivAt_id Y).congr_of_eventuallyEq ?_
    filter_upwards [hP.isOpen_src.mem_nhds hY] with Z hZ
    exact hP.inv_map Z hZ
  have := h1.unique h2
  exact congrArg (fun L : V →L[ℝ] V => L v) this
theorem param_mem {c : Chart M} {u : Fin c.dim → ℝ} (hu : u ∈ c.source) :
    c.param u ∈ M := by
  obtain ⟨U, -, hU⟩ := c.isRelativelyOpen_image c.source subset_rfl c.isOpen_source
  have : c.param u ∈ c.param '' c.source := ⟨u, hu, rfl⟩
  rw [hU] at this
  exact this.2
theorem SmoothLocalParam.factor_through (hP : SmoothLocalParam M p χ ℓ B D) (c : Chart M)
    {u₀ : Fin c.dim → ℝ} (hu₀ : u₀ ∈ c.source) (hp : c.param u₀ = p) :
    ContDiffAt ℝ ∞ (ℓ ∘ c.param) u₀ ∧ (ℓ ∘ c.param) u₀ = 0 ∧
      ∀ᶠ u in 𝓝 u₀, (ℓ ∘ c.param) u ∈ B ∧
        χ ((ℓ ∘ c.param) u) = c.param u := by
  have hφ : ContDiffAt ℝ ∞ c.param u₀ :=
    c.contDiffOn_param.contDiffAt (c.isOpen_source.mem_nhds hu₀)
  refine ⟨?_, ?_, ?_⟩
  · refine ContDiffAt.comp u₀ ?_ hφ
    rw [hp]
    exact hP.contDiffAt_inv hP.mem_invDom
  · have := hP.inv_map 0 hP.zero_mem
    rw [hP.map_zero_eq] at this
    simpa [hp] using this
  · obtain ⟨U, hU, hEq⟩ := hP.isRelativelyOpen_range
    have hpU : p ∈ U := by
      have : p ∈ χ '' B := ⟨0, hP.zero_mem, hP.map_zero_eq⟩
      rw [hEq] at this
      exact this.1
    have hφc : ContinuousAt c.param u₀ := hφ.continuousAt
    have hmem : c.param ⁻¹' U ∈ 𝓝 u₀ :=
      hφc (by rw [hp]; exact hU.mem_nhds hpU)
    filter_upwards [hmem, c.isOpen_source.mem_nhds hu₀] with u hu hd
    have : c.param u ∈ χ '' B := by
      rw [hEq]
      exact ⟨hu, param_mem hd⟩
    obtain ⟨Y, hY, hYe⟩ := this
    simp only [Function.comp_apply, ← hYe, hP.inv_map Y hY]
    exact ⟨hY, trivial⟩
def SmoothLocalParam.toChart {d : ℕ} (κ : (Fin d → ℝ) ≃L[ℝ] V)
    (hP : SmoothLocalParam M p χ ℓ B D) : Chart M where
  dim := d
  source := κ ⁻¹' B
  param := χ ∘ κ
  isOpen_source := hP.isOpen_src.preimage κ.continuous
  contDiffOn_param :=
    hP.contDiffOn_map.comp κ.contDiff.contDiffOn fun _ hu => hu
  injective_fderiv_param := by
    intro u hu w w' hw
    have hk : HasFDerivAt κ (κ : (Fin d → ℝ) →L[ℝ] V) u := κ.hasFDerivAt
    have hd : HasFDerivAt (χ ∘ κ) ((fderiv ℝ χ (κ u)).comp (κ : (Fin d → ℝ) →L[ℝ] V)) u :=
      (hP.differentiableAt_map hu).hasFDerivAt.comp u hk
    rw [hd.fderiv] at hw
    have h1 := hP.fderiv_inv_map hu (κ w)
    have h2 := hP.fderiv_inv_map hu (κ w')
    have h3 : fderiv ℝ χ (κ u) (κ w) = fderiv ℝ χ (κ u) (κ w') := hw
    rw [h3, h2] at h1
    exact κ.injective h1.symm
  injOn_param := by
    intro u hu u' hu' h
    have h1 := hP.inv_map _ hu
    have h2 := hP.inv_map _ hu'
    have h3 : χ (κ u) = χ (κ u') := h
    rw [h3, h2] at h1
    exact κ.injective h1.symm
  isRelativelyOpen_image := by
    intro W hW hWo
    obtain ⟨U, hU, hEq⟩ := hP.isRelativelyOpen_range
    have hW' : IsOpen (κ.symm ⁻¹' W) := hWo.preimage κ.symm.continuous
    have hopen : IsOpen (D ∩ ℓ ⁻¹' (κ.symm ⁻¹' W)) :=
      hP.contDiffOn_inv.continuousOn.isOpen_inter_preimage hP.isOpen_invDom hW'
    refine ⟨U ∩ (D ∩ ℓ ⁻¹' (κ.symm ⁻¹' W)), hU.inter hopen, ?_⟩
    ext X
    constructor
    · rintro ⟨u, hu, rfl⟩
      have hB : κ u ∈ B := hW hu
      have hUM : (χ ∘ κ) u ∈ U ∩ M := by
        rw [← hEq]
        exact ⟨κ u, hB, rfl⟩
      refine ⟨⟨hUM.1, (hP.mapsTo hB).1, ?_⟩, hUM.2⟩
      simp only [mem_preimage, Function.comp_apply, hP.inv_map _ hB]
      simpa using hu
    · rintro ⟨⟨hXU, hXD, hXW⟩, hXM⟩
      have : X ∈ χ '' B := by
        rw [hEq]
        exact ⟨hXU, hXM⟩
      obtain ⟨Y, hY, rfl⟩ := this
      simp only [mem_preimage, hP.inv_map Y hY] at hXW
      exact ⟨κ.symm Y, hXW, by simp⟩
omit [NormedAddCommGroup F] [NormedSpace ℝ F] in
theorem SmoothLocalParam.pullback_toChart {d : ℕ} (κ : (Fin d → ℝ) ≃L[ℝ] V)
    (hP : SmoothLocalParam M p χ ℓ B D) (f : E → F) :
    f ∘ χ = (hP.toChart κ).pullback f ∘ κ.symm := by
  funext Y
  simp [Chart.pullback, SmoothLocalParam.toChart]
theorem SmoothLocalParam.mapsTo_coords {d : ℕ} (κ : (Fin d → ℝ) ≃L[ℝ] V)
    (hP : SmoothLocalParam M p χ ℓ B D) (O : Set E) :
    MapsTo κ.symm (B ∩ χ ⁻¹' O) ((hP.toChart κ).coords O) := by
  intro Y hY
  refine ⟨?_, ?_⟩
  · show κ (κ.symm Y) ∈ B
    simpa using hY.1
  · show χ (κ (κ.symm Y)) ∈ O
    simpa using hY.2
theorem SmoothLocalParam.isOpen_preimage_inter (hP : SmoothLocalParam M p χ ℓ B D) {O : Set E}
    (hO : ComplexMatrix2.IsRelativelyOpen M O) : IsOpen (B ∩ χ ⁻¹' O) := by
  obtain ⟨U, hU, rfl⟩ := hO
  have : B ∩ χ ⁻¹' (U ∩ M) = B ∩ χ ⁻¹' U := by
    ext Y
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨h1, h2.1⟩
    · rintro ⟨h1, h2⟩
      exact ⟨h1, h2, (hP.mapsTo h1).2⟩
  rw [this]
  exact hP.contDiffOn_map.continuousOn.isOpen_inter_preimage hP.isOpen_src hU
theorem SmoothLocalParam.preimage_inter_mem_nhds (hP : SmoothLocalParam M p χ ℓ B D) {O : Set E}
    (hO : ComplexMatrix2.IsRelativelyOpen M O) (hp : p ∈ O) : B ∩ χ ⁻¹' O ∈ 𝓝 (0 : V) :=
  (hP.isOpen_preimage_inter hO).mem_nhds ⟨hP.zero_mem, by simpa [hP.map_zero_eq] using hp⟩
omit [NormedAddCommGroup F] [NormedSpace ℝ F] in
theorem SmoothLocalParam.pullback_eventuallyEq (hP : SmoothLocalParam M p χ ℓ B D) (c : Chart M)
    {u₀ : Fin c.dim → ℝ} (hu₀ : u₀ ∈ c.source) (hp : c.param u₀ = p) (f : E → F) :
    c.pullback f =ᶠ[𝓝 u₀] (f ∘ χ) ∘ (ℓ ∘ c.param) := by
  obtain ⟨-, -, h⟩ := hP.factor_through c hu₀ hp
  filter_upwards [h] with u hu
  simp only [Chart.pullback, Function.comp_apply]
  rw [show χ (ℓ (c.param u)) = c.param u from hu.2]
theorem SmoothLocalParam.differentiableAt_pullback (hP : SmoothLocalParam M p χ ℓ B D)
    (c : Chart M) {u₀ : Fin c.dim → ℝ} (hu₀ : u₀ ∈ c.source) (hp : c.param u₀ = p) {f : E → F}
    (hg : DifferentiableAt ℝ (f ∘ χ) 0) : DifferentiableAt ℝ (c.pullback f) u₀ := by
  obtain ⟨hψ, h0, -⟩ := hP.factor_through c hu₀ hp
  refine DifferentiableAt.congr_of_eventuallyEq ?_ (hP.pullback_eventuallyEq c hu₀ hp f)
  refine DifferentiableAt.comp u₀ ?_ (hψ.differentiableAt (by simp))
  rw [h0]
  exact hg
theorem SmoothLocalParam.contDiffAt_pullback (hP : SmoothLocalParam M p χ ℓ B D) (c : Chart M)
    {u₀ : Fin c.dim → ℝ} (hu₀ : u₀ ∈ c.source) (hp : c.param u₀ = p) {f : E → F}
    (hg : ContDiffAt ℝ ∞ (f ∘ χ) 0) : ContDiffAt ℝ ∞ (c.pullback f) u₀ := by
  obtain ⟨hψ, h0, -⟩ := hP.factor_through c hu₀ hp
  refine ContDiffAt.congr_of_eventuallyEq ?_ (hP.pullback_eventuallyEq c hu₀ hp f)
  refine ContDiffAt.comp u₀ ?_ hψ
  rw [h0]
  exact hg
def IsParamSystem (M : Set E) (S : E → V → E) : Prop :=
  ∀ p ∈ M, ∃ (ℓ : E → V) (B : Set V) (D : Set E), SmoothLocalParam M p (S p) ℓ B D
variable {S : E → V → E} {O : Set E} {d : ℕ}
omit [NormedSpace ℝ E] in
theorem subset_of_isRelativelyOpen (hO : ComplexMatrix2.IsRelativelyOpen M O) : O ⊆ M := by
  obtain ⟨U, -, rfl⟩ := hO
  exact inter_subset_right
theorem exists_nhds_mapsTo (hS : IsParamSystem M S) (hO : ComplexMatrix2.IsRelativelyOpen M O)
    {p : E} (hp : p ∈ O) : ∃ N ∈ 𝓝 (0 : V), MapsTo (S p) N O := by
  obtain ⟨ℓ, B, D, hP⟩ := hS p (subset_of_isRelativelyOpen hO hp)
  exact ⟨_, hP.preimage_inter_mem_nhds hO hp, fun _ hY => hY.2⟩
theorem differentiableOnOpen_iff (κ : (Fin d → ℝ) ≃L[ℝ] V) (hS : IsParamSystem M S)
    (hO : ComplexMatrix2.IsRelativelyOpen M O) (f : E → F) :
    DifferentiableOnOpen M O f ↔ ∀ p ∈ O, ∃ N ∈ 𝓝 (0 : V), MapsTo (S p) N O ∧
      DifferentiableOn ℝ (f ∘ S p) N := by
  constructor
  · rintro ⟨-, h⟩ p hp
    obtain ⟨ℓ, B, D, hP⟩ := hS p (subset_of_isRelativelyOpen hO hp)
    refine ⟨_, hP.preimage_inter_mem_nhds hO hp, fun _ hY => hY.2, ?_⟩
    rw [hP.pullback_toChart κ f]
    exact (h (hP.toChart κ)).comp κ.symm.differentiable.differentiableOn
      (hP.mapsTo_coords κ O)
  · intro h
    refine ⟨hO, fun c u hu => ?_⟩
    obtain ⟨N, hN, -, hd⟩ := h _ hu.2
    obtain ⟨ℓ, B, D, hP⟩ := hS _ (subset_of_isRelativelyOpen hO hu.2)
    exact (hP.differentiableAt_pullback c hu.1 rfl
      ((hd 0 (mem_of_mem_nhds hN)).differentiableAt hN)).differentiableWithinAt
theorem contDiffOn_pullback_iff (κ : (Fin d → ℝ) ≃L[ℝ] V) (hS : IsParamSystem M S)
    (hO : ComplexMatrix2.IsRelativelyOpen M O) (f : E → F) :
    (∀ c : Chart M, ContDiffOn ℝ ∞ (c.pullback f) (c.coords O)) ↔
      ∀ p ∈ O, ∃ N ∈ 𝓝 (0 : V), MapsTo (S p) N O ∧ ContDiffOn ℝ ∞ (f ∘ S p) N := by
  constructor
  · intro h p hp
    obtain ⟨ℓ, B, D, hP⟩ := hS p (subset_of_isRelativelyOpen hO hp)
    refine ⟨_, hP.preimage_inter_mem_nhds hO hp, fun _ hY => hY.2, ?_⟩
    rw [hP.pullback_toChart κ f]
    exact (h (hP.toChart κ)).comp κ.symm.contDiff.contDiffOn (hP.mapsTo_coords κ O)
  · intro h c u hu
    obtain ⟨N, hN, -, hd⟩ := h _ hu.2
    obtain ⟨ℓ, B, D, hP⟩ := hS _ (subset_of_isRelativelyOpen hO hu.2)
    exact (hP.contDiffAt_pullback c hu.1 rfl
      ((hd 0 (mem_of_mem_nhds hN)).contDiffAt hN)).contDiffWithinAt
theorem hasDerivAt_tangentDifferential (κ : (Fin d → ℝ) ≃L[ℝ] V) (hS : IsParamSystem M S)
    (hO : ComplexMatrix2.IsRelativelyOpen M O) {f : E → F} (h : DifferentiableOnOpen M O f)
    {p : E} (hp : p ∈ O) (Y : V) :
    ∃ hm : fderiv ℝ (S p) 0 Y ∈ tangentSpace M p,
      HasDerivAt (fun t : ℝ => f (S p (t • Y)))
        (tangentDifferential M f p ⟨fderiv ℝ (S p) 0 Y, hm⟩) 0 := by
  obtain ⟨ℓ, B, D, hP⟩ := hS p (subset_of_isRelativelyOpen hO hp)
  obtain ⟨N, hN', -, hd⟩ := (differentiableOnOpen_iff κ hS hO f).1 h p hp
  have hg : DifferentiableAt ℝ (f ∘ S p) 0 := (hd 0 (mem_of_mem_nhds hN')).differentiableAt hN'
  have hχ0 : DifferentiableAt ℝ (S p) 0 := hP.differentiableAt_map hP.zero_mem
  have hκ0 : κ (0 : Fin d → ℝ) = 0 := map_zero κ
  have hu0 : (0 : Fin d → ℝ) ∈ (hP.toChart κ).source := by
    show κ 0 ∈ B
    rw [hκ0]
    exact hP.zero_mem
  have hc0 : (hP.toChart κ).param (0 : Fin d → ℝ) = p := by
    show S p (κ 0) = p
    rw [hκ0, hP.map_zero_eq]
  have hfd : fderiv ℝ (S p ∘ κ) (0 : Fin d → ℝ) =
      (fderiv ℝ (S p) 0).comp (κ : (Fin d → ℝ) →L[ℝ] V) := by
    have : HasFDerivAt (S p ∘ κ) ((fderiv ℝ (S p) 0).comp (κ : (Fin d → ℝ) →L[ℝ] V)) 0 := by
      refine HasFDerivAt.comp (0 : Fin d → ℝ) ?_ κ.hasFDerivAt
      rw [hκ0]
      exact hχ0.hasFDerivAt
    exact this.fderiv
  have hm : fderiv ℝ (S p) 0 Y ∈ tangentSpace M p := by
    refine Submodule.mem_iSup_of_mem (hP.toChart κ) (Submodule.mem_iSup_of_mem (0 : Fin d → ℝ)
      (Submodule.mem_iSup_of_mem ⟨hu0, hc0⟩ ?_))
    refine ⟨κ.symm Y, ?_⟩
    show fderiv ℝ (S p ∘ κ) (0 : Fin d → ℝ) (κ.symm Y) = _
    rw [hfd]
    simp
  let L : tangentSpace M p →ₗ[ℝ] F :=
    (((fderiv ℝ (f ∘ S p) 0).comp (fderiv ℝ ℓ p)) : E →L[ℝ] F).toLinearMap.comp
      (tangentSpace M p).subtype
  have hL : IsTangentDifferential M f p L := by
    intro c' u' hu' hφ w v hv
    obtain ⟨hψ, h0, hev⟩ := hP.factor_through c' hu' hφ
    have hψd : DifferentiableAt ℝ (ℓ ∘ c'.param) u' := hψ.differentiableAt (by simp)
    have hφe : c'.param =ᶠ[𝓝 u'] S p ∘ (ℓ ∘ c'.param) := by
      filter_upwards [hev] with u hu
      exact hu.2.symm
    have hφd : fderiv ℝ c'.param u' =
        (fderiv ℝ (S p) 0).comp (fderiv ℝ (ℓ ∘ c'.param) u') := by
      rw [hφe.fderiv_eq]
      have : HasFDerivAt (S p ∘ (ℓ ∘ c'.param))
          ((fderiv ℝ (S p) 0).comp (fderiv ℝ (ℓ ∘ c'.param) u')) u' := by
        refine HasFDerivAt.comp u' ?_ hψd.hasFDerivAt
        rw [h0]
        exact hχ0.hasFDerivAt
      exact this.fderiv
    have hrd : fderiv ℝ (c'.pullback f) u' =
        (fderiv ℝ (f ∘ S p) 0).comp (fderiv ℝ (ℓ ∘ c'.param) u') := by
      rw [(hP.pullback_eventuallyEq c' hu' hφ f).fderiv_eq]
      have : HasFDerivAt ((f ∘ S p) ∘ (ℓ ∘ c'.param))
          ((fderiv ℝ (f ∘ S p) 0).comp (fderiv ℝ (ℓ ∘ c'.param) u')) u' := by
        refine HasFDerivAt.comp u' ?_ hψd.hasFDerivAt
        rw [h0]
        exact hg.hasFDerivAt
      exact this.fderiv
    have hinv := hP.fderiv_inv_map hP.zero_mem (fderiv ℝ (ℓ ∘ c'.param) u' w)
    rw [hP.map_zero_eq] at hinv
    show (fderiv ℝ (f ∘ S p) 0) (fderiv ℝ ℓ p (v : E)) = _
    rw [hv, hφd, hrd]
    simp only [ContinuousLinearMap.comp_apply]
    rw [hinv]
  have hspec : IsTangentDifferential M f p (tangentDifferential M f p) :=
    Classical.epsilon_spec ⟨L, hL⟩
  refine ⟨hm, ?_⟩
  have hval : tangentDifferential M f p ⟨fderiv ℝ (S p) 0 Y, hm⟩ = fderiv ℝ (f ∘ S p) 0 Y := by
    have h1 : tangentDifferential M f p ⟨fderiv ℝ (S p) 0 Y, hm⟩ =
        fderiv ℝ ((f ∘ S p) ∘ κ) (0 : Fin d → ℝ) (κ.symm Y) :=
      hspec (hP.toChart κ) (0 : Fin d → ℝ) hu0 hc0 (κ.symm Y) ⟨fderiv ℝ (S p) 0 Y, hm⟩ (by
        show _ = fderiv ℝ (S p ∘ κ) (0 : Fin d → ℝ) (κ.symm Y)
        rw [hfd]
        simp)
    rw [h1]
    have h3 : fderiv ℝ ((f ∘ S p) ∘ κ) 0 =
        (fderiv ℝ (f ∘ S p) 0).comp (κ : (Fin d → ℝ) →L[ℝ] V) := by
      have : HasFDerivAt ((f ∘ S p) ∘ κ)
          ((fderiv ℝ (f ∘ S p) 0).comp (κ : (Fin d → ℝ) →L[ℝ] V)) 0 := by
        refine HasFDerivAt.comp (0 : Fin d → ℝ) ?_ κ.hasFDerivAt
        rw [hκ0]
        exact hg.hasFDerivAt
      exact this.fderiv
    rw [h3]
    simp
  rw [hval]
  have hline : HasDerivAt (fun t : ℝ => t • Y) Y 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).smul_const Y
  have hg' : HasFDerivAt (f ∘ S p) (fderiv ℝ (f ∘ S p) 0) ((0 : ℝ) • Y) := by
    rw [zero_smul]
    exact hg.hasFDerivAt
  exact hg'.comp_hasDerivAt (0 : ℝ) hline
theorem eq_sum_coords (κ : (Fin d → ℝ) ≃L[ℝ] V) (v : V) :
    v = ∑ j, (κ.symm v j) • κ (Pi.single j 1) := by
  have h : κ.symm v = ∑ j, (κ.symm v j) • (Pi.single j (1 : ℝ) : Fin d → ℝ) := by
    ext i
    simp [Finset.sum_apply, Pi.single_apply]
  conv_lhs => rw [← κ.apply_symm_apply v, h]
  simp [map_sum]
theorem hasDifferentiablePartialsOn_iff (κ : (Fin d → ℝ) ≃L[ℝ] V) (hS : IsParamSystem M S)
    (hO : ComplexMatrix2.IsRelativelyOpen M O) {f : E → F} (h : DifferentiableOnOpen M O f) :
    HasDifferentiablePartialsOn M O f ↔ ∀ p ∈ O, ∃ N ∈ 𝓝 (0 : V), MapsTo (S p) N O ∧
      ∀ k : Fin d, DifferentiableOn ℝ (fun Y => fderiv ℝ (f ∘ S p) Y (κ (Pi.single k 1))) N := by
  constructor
  · rintro ⟨-, h2⟩ p hp
    obtain ⟨ℓ, B, D, hP⟩ := hS p (subset_of_isRelativelyOpen hO hp)
    refine ⟨_, hP.preimage_inter_mem_nhds hO hp, fun _ hY => hY.2, fun k => ?_⟩
    have heq : (fun Y => fderiv ℝ (f ∘ S p) Y (κ (Pi.single k 1))) =
        (fun u : Fin d → ℝ => fderiv ℝ ((f ∘ S p) ∘ κ) u (Pi.single k 1)) ∘ κ.symm := by
      funext Y
      have h3 : f ∘ S p = ((f ∘ S p) ∘ κ) ∘ κ.symm := by
        funext Z
        simp
      conv_lhs => rw [h3]
      rw [ContinuousLinearEquiv.comp_right_fderiv]
      simp
    rw [heq]
    exact (h2 (hP.toChart κ) k).comp κ.symm.differentiable.differentiableOn
      (hP.mapsTo_coords κ O)
  · intro h2
    refine ⟨h, fun c k u₀ hu₀ => ?_⟩
    obtain ⟨N, hN, -, hdN⟩ := h2 _ hu₀.2
    obtain ⟨ℓ, B, D, hP⟩ := hS _ (subset_of_isRelativelyOpen hO hu₀.2)
    set p := c.param u₀ with hpdef
    set g := f ∘ S p with hgdef
    set ψ := ℓ ∘ c.param with hψdef
    obtain ⟨hψ', h0', -⟩ := hP.factor_through c hu₀.1 rfl
    have hψ : ContDiffAt ℝ ∞ ψ u₀ := hψ'
    have h0 : ψ u₀ = 0 := h0'
    have hgN : DifferentiableOn ℝ g (B ∩ S p ⁻¹' O) := by
      rw [hgdef, hP.pullback_toChart κ f]
      exact (h.2 (hP.toChart κ)).comp κ.symm.differentiable.differentiableOn
        (hP.mapsTo_coords κ O)
    have hform := hP.isOpen_preimage_inter hO
    have hnear : ∀ᶠ u in 𝓝 u₀, ψ u ∈ B ∩ S p ⁻¹' O := by
      have : ContinuousAt ψ u₀ := hψ.continuousAt
      exact this (by rw [h0]; exact hP.preimage_inter_mem_nhds hO hu₀.2)
    have hψ1 : ∀ᶠ u in 𝓝 u₀, ContDiffAt ℝ 1 ψ u :=
      (hψ.of_le (by simp)).eventually (by simp)
    have hre : ∀ᶠ u in 𝓝 u₀, c.pullback f =ᶠ[𝓝 u] g ∘ ψ :=
      (hP.pullback_eventuallyEq c hu₀.1 rfl f).eventually_nhds
    have hform' : ∀ᶠ u in 𝓝 u₀, fderiv ℝ (c.pullback f) u (Pi.single k 1) =
        ∑ j, (κ.symm (fderiv ℝ ψ u (Pi.single k 1)) j) • fderiv ℝ g (ψ u) (κ (Pi.single j 1)) := by
      filter_upwards [hnear, hψ1, hre] with u h1 h2' h3
      rw [h3.fderiv_eq]
      have hgd : DifferentiableAt ℝ g (ψ u) := (hgN _ h1).differentiableAt (hform.mem_nhds h1)
      have hψd : DifferentiableAt ℝ ψ u := h2'.differentiableAt (by simp)
      have : HasFDerivAt (g ∘ ψ) ((fderiv ℝ g (ψ u)).comp (fderiv ℝ ψ u)) u :=
        hgd.hasFDerivAt.comp u hψd.hasFDerivAt
      rw [this.fderiv, ContinuousLinearMap.comp_apply]
      conv_lhs => rw [eq_sum_coords κ (fderiv ℝ ψ u (Pi.single k 1))]
      simp [map_sum]
    refine DifferentiableAt.differentiableWithinAt ?_
    refine DifferentiableAt.congr_of_eventuallyEq ?_ hform'
    refine DifferentiableAt.fun_sum fun j _ => ?_
    refine DifferentiableAt.smul ?_ ?_
    · have h1 : ContDiffAt ℝ 1 (fderiv ℝ ψ) u₀ := hψ.fderiv_right (by norm_cast)
      have h2' : DifferentiableAt ℝ (fderiv ℝ ψ) u₀ := h1.differentiableAt (by simp)
      have h3 : DifferentiableAt ℝ (fun u => fderiv ℝ ψ u (Pi.single k 1)) u₀ :=
        h2'.clm_apply (differentiableAt_const _)
      have h4 : DifferentiableAt ℝ (fun u => κ.symm (fderiv ℝ ψ u (Pi.single k 1))) u₀ :=
        κ.symm.differentiable.differentiableAt.comp u₀ h3
      exact (differentiableAt_pi.1 h4) j
    · have h1 : DifferentiableAt ℝ (fun Y => fderiv ℝ g Y (κ (Pi.single j 1))) (ψ u₀) := by
        rw [h0]
        exact (hdN j 0 (mem_of_mem_nhds hN)).differentiableAt hN
      exact h1.comp u₀ (hψ.differentiableAt (by simp))
end YangMills.Construction.Matrices.LocalParametrization
namespace YangMills.Construction.Matrices.PowerExpCharts
open LocalParametrization EmbeddedSubmanifold
variable {σ τ : Type}
private def matrixLinearEquiv : ComplexMatrix2 ≃ₗ[ℝ] Coordinates.ComplexCoordinates 4 :=
  { Coordinates.ComplexCoordinates.matrixEquiv with
    map_add' := fun _ _ => rfl
    map_smul' := fun _ _ => rfl }
private def matrixCLE : ComplexMatrix2 ≃L[ℝ] Coordinates.ComplexCoordinates 4 :=
  matrixLinearEquiv.toContinuousLinearEquiv
private theorem matrixCLE_apply (X : ComplexMatrix2) :
    matrixCLE X = Coordinates.ComplexCoordinates.matrixEquiv X := rfl
private theorem matrixCLE_symm_apply (z : Coordinates.ComplexCoordinates 4) :
    matrixCLE.symm z = Coordinates.ComplexCoordinates.matrixEquiv.symm z := rfl
private theorem contDiff_matExp
    (hH : Coordinates.ComplexCoordinates.PowerSeriesHolomorphy.Properties) :
    ContDiff ℝ ∞ ComplexMatrix2.matExp := by
  have hh := hH.2.2.2.2.1
  have hd := (((hH.1 4 _ hh.1).1 4 _ hh).2.1)
  rw [image_univ, Coordinates.ComplexCoordinates.matrixEquiv.surjective.range_eq,
    contDiffOn_univ] at hd
  have h2 := matrixCLE.symm.contDiff.comp (hd.comp matrixCLE.contDiff)
  have h3 : ComplexMatrix2.matExp = matrixCLE.symm ∘
      (Coordinates.ComplexCoordinates.matrixEquiv ∘ ComplexMatrix2.matExp ∘
        Coordinates.ComplexCoordinates.matrixEquiv.symm) ∘ matrixCLE := by
    funext X
    simp [matrixCLE_apply, matrixCLE_symm_apply]
  rw [h3]
  exact h2
private theorem contDiffOn_logSeries
    (hH : Coordinates.ComplexCoordinates.PowerSeriesHolomorphy.Properties) :
    ContDiffOn ℝ ∞ ComplexMatrix2.logSeries ComplexMatrix2.logBall := by
  have hh := hH.2.2.2.2.2
  have hd := (((hH.1 4 _ hh.1).1 4 _ hh).2.1)
  have h1 := hd.comp matrixCLE.contDiff.contDiffOn
    (s := ComplexMatrix2.logBall) fun X hX => ⟨X, hX, rfl⟩
  have h2 := matrixCLE.symm.contDiff.comp_contDiffOn h1
  refine h2.congr fun X _ => ?_
  simp [matrixCLE_apply, matrixCLE_symm_apply]
private theorem isOpen_logBall : IsOpen ComplexMatrix2.logBall :=
  isOpen_lt (continuous_norm.comp (continuous_id.sub continuous_const)) continuous_const
private def toMatrixCLM : ComplexMatrix2.LieElement →L[ℝ] ComplexMatrix2 :=
  LinearMap.toContinuousLinearMap
    { toFun := ComplexMatrix2.LieElement.toMatrix
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
private theorem toMatrixCLM_apply (Y : ComplexMatrix2.LieElement) : toMatrixCLM Y = Y.toMatrix :=
  rfl
private def reTraceForm (A : ComplexMatrix2) : ComplexMatrix2 →ₗ[ℝ] ℝ where
  toFun X := (ComplexMatrix2.halfTrace (A * X)).re
  map_add' X Z := by
    simp [ComplexMatrix2.halfTrace, ComplexMatrix2.fullTrace, mul_add, Matrix.trace_add]
  map_smul' c X := by
    simp [ComplexMatrix2.halfTrace, ComplexMatrix2.fullTrace, Matrix.trace_smul]
    ring
private def lieProjection (e : OrthonormalBasis (Fin 3) ℝ ComplexMatrix2.LieElement) :
    ComplexMatrix2 →L[ℝ] ComplexMatrix2.LieElement :=
  LinearMap.toContinuousLinearMap
    (∑ a, (reTraceForm (e a).toMatrix).smulRight (e a))
private theorem lieProjection_toMatrix (e : OrthonormalBasis (Fin 3) ℝ ComplexMatrix2.LieElement)
    (Y : ComplexMatrix2.LieElement) : lieProjection e Y.toMatrix = Y := by
  have h := e.sum_repr' Y
  conv_rhs => rw [← h]
  simp only [lieProjection, LinearMap.coe_toContinuousLinearMap', LinearMap.sum_apply,
    LinearMap.smulRight_apply]
  rfl
private theorem mul_inv_of_mem {U : ComplexMatrix2} (hU : U ∈ ComplexMatrix2.specialUnitary) :
    U * U⁻¹ = 1 ∧ U⁻¹ * U = 1 := by
  have hdet : IsUnit U.det := by
    rw [(Matrix.mem_specialUnitaryGroup_iff.1 hU).2]
    exact isUnit_one
  exact ⟨Matrix.mul_nonsing_inv _ hdet, Matrix.nonsing_inv_mul _ hdet⟩
private theorem inv_mem_specialUnitary {U : ComplexMatrix2}
    (hU : U ∈ ComplexMatrix2.specialUnitary) : U⁻¹ ∈ ComplexMatrix2.specialUnitary := by apply _root_.YangMills.Construction.Tower.WilsonAnalyticity.inv_mem_specialUnitary <;> assumption
private theorem expChartI_apply (p₀ : σ → ComplexMatrix2) (Y : σ → ComplexMatrix2.LieElement)
    (s : σ) :
    expChartI p₀ Y s = ComplexMatrix2.matExp (Complex.I • (Y s).toMatrix) * p₀ s := rfl
private theorem operatorNorm_I_smul (A : ComplexMatrix2) :
    ComplexMatrix2.operatorNorm (Complex.I • A) = ComplexMatrix2.operatorNorm A := by
  simp [ComplexMatrix2.operatorNorm, norm_smul]
private theorem expChartI_mem (hI : ComplexMatrix2.UnitaryLogConjugationProperties)
    {p₀ : σ → ComplexMatrix2} (hp : p₀ ∈ specialUnitaryPower σ)
    (Y : σ → ComplexMatrix2.LieElement) :
    expChartI p₀ Y ∈ specialUnitaryPower σ := fun s =>
  Submonoid.mul_mem _ (hI.1 _ (Y s).2).2.2 (hp s)
private theorem lt_log_two_of_exp_le {ε : ℝ} (hε : Real.exp ε ≤ 19 / 10) : ε < Real.log 2 := by
  rw [Real.lt_log_iff_exp_lt (by norm_num)]
  linarith
private def logImage (p₀ : σ → ComplexMatrix2) (ε : ℝ) : Set (σ → ComplexMatrix2) :=
  {X | ∀ s, X s * (p₀ s)⁻¹ ∈ ComplexMatrix2.logBall ∧
    ComplexMatrix2.operatorNorm (ComplexMatrix2.logSeries (X s * (p₀ s)⁻¹)) < ε}
private theorem isOpen_logImage [Fintype σ]
    (hH : Coordinates.ComplexCoordinates.PowerSeriesHolomorphy.Properties)
    (p₀ : σ → ComplexMatrix2) (ε : ℝ) : IsOpen (logImage p₀ ε) := by
  have h1 : IsOpen (ComplexMatrix2.logBall ∩
      ComplexMatrix2.logSeries ⁻¹' {Z | ComplexMatrix2.operatorNorm Z < ε}) :=
    (contDiffOn_logSeries hH).continuousOn.isOpen_inter_preimage isOpen_logBall
      (isOpen_lt continuous_norm continuous_const)
  have h2 : logImage p₀ ε = ⋂ s, (fun X : σ → ComplexMatrix2 => X s * (p₀ s)⁻¹) ⁻¹'
      (ComplexMatrix2.logBall ∩
        ComplexMatrix2.logSeries ⁻¹' {Z | ComplexMatrix2.operatorNorm Z < ε}) := by
    ext X
    simp [logImage]
  rw [h2]
  exact isOpen_iInter_of_finite fun s =>
    h1.preimage ((continuous_apply s).mul continuous_const)
private theorem log_expChartI_mul_inv (hE : ComplexMatrix2.ExpLogEstimates)
    {p₀ : σ → ComplexMatrix2} (hp : p₀ ∈ specialUnitaryPower σ) {ε : ℝ}
    (hε : Real.exp ε ≤ 19 / 10)
    {Y : σ → ComplexMatrix2.LieElement} (hY : Y ∈ smallBall σ ε) (s : σ) :
    expChartI p₀ Y s * (p₀ s)⁻¹ ∈ ComplexMatrix2.logBall ∧
      ComplexMatrix2.logSeries (expChartI p₀ Y s * (p₀ s)⁻¹) = Complex.I • (Y s).toMatrix := by
  have h1 : expChartI p₀ Y s * (p₀ s)⁻¹ = ComplexMatrix2.matExp (Complex.I • (Y s).toMatrix) := by
    rw [expChartI_apply, mul_assoc, (mul_inv_of_mem (hp s)).1, mul_one]
  have h2 : ComplexMatrix2.operatorNorm (Complex.I • (Y s).toMatrix) < Real.log 2 := by
    rw [operatorNorm_I_smul]
    exact (hY s).trans (lt_log_two_of_exp_le hε)
  rw [h1]
  exact hE.2.2.2.2.1 _ h2
private theorem image_smallBall (hE : ComplexMatrix2.ExpLogEstimates)
    (hI : ComplexMatrix2.UnitaryLogConjugationProperties)
    {p₀ : σ → ComplexMatrix2} (hp : p₀ ∈ specialUnitaryPower σ) {ε : ℝ}
    (hε : Real.exp ε ≤ 19 / 10) :
    expChartI p₀ '' smallBall σ ε = logImage p₀ ε ∩ specialUnitaryPower σ := by
  ext X
  constructor
  · rintro ⟨Y, hY, rfl⟩
    refine ⟨fun s => ?_, expChartI_mem hI hp Y⟩
    obtain ⟨h1, h2⟩ := log_expChartI_mul_inv hE hp hε hY s
    refine ⟨h1, ?_⟩
    rw [h2, operatorNorm_I_smul]
    exact hY s
  · rintro ⟨hX, hXM⟩
    have key : ∀ s, ∃ Y : ComplexMatrix2.LieElement, ComplexMatrix2.operatorNorm Y.toMatrix < ε ∧
        ComplexMatrix2.matExp (Complex.I • Y.toMatrix) * p₀ s = X s := by
      intro s
      obtain ⟨h1, h2⟩ := hX s
      have hA : X s * (p₀ s)⁻¹ ∈ ComplexMatrix2.specialUnitary :=
        Submonoid.mul_mem _ (hXM s) (inv_mem_specialUnitary (hp s))
      have hA' := Matrix.mem_specialUnitaryGroup_iff.1 hA
      obtain ⟨H, -, hl, -, he, -, hdet⟩ := hE.2.2.2.2.2.2.2.1 _ hA'.1 h1
      obtain ⟨-, hsu, -⟩ := hdet hA'.2
      refine ⟨⟨H, hsu⟩, ?_, ?_⟩
      · rw [hl, operatorNorm_I_smul] at h2
        exact h2
      · show ComplexMatrix2.matExp (Complex.I • H) * p₀ s = X s
        rw [he, mul_assoc, (mul_inv_of_mem (hp s)).2, mul_one]
    choose Y hY1 hY2 using key
    exact ⟨Y, hY1, funext hY2⟩
private def chartInverse (e : OrthonormalBasis (Fin 3) ℝ ComplexMatrix2.LieElement)
    (p₀ X : σ → ComplexMatrix2) : σ → ComplexMatrix2.LieElement :=
  fun s => lieProjection e (logChart p₀ X s)
private theorem contDiffOn_logChart [Fintype σ]
    (hH : Coordinates.ComplexCoordinates.PowerSeriesHolomorphy.Properties)
    (p₀ : σ → ComplexMatrix2) :
    ContDiffOn ℝ ∞ (logChart p₀) (logDomain p₀) := by
  refine contDiffOn_pi.2 fun s => ?_
  refine ContDiffOn.const_smul (1 / Complex.I : ℂ) ?_
  have h1 : ContDiff ℝ ∞ fun X : σ → ComplexMatrix2 => X s * (p₀ s)⁻¹ :=
    (contDiff_apply ℝ ComplexMatrix2 s).mul contDiff_const
  exact (contDiffOn_logSeries hH).comp h1.contDiffOn fun X hX => hX s
private theorem logDomain_isOpen [Fintype σ] (p₀ : σ → ComplexMatrix2) :
    IsOpen (logDomain p₀) := by
  have h2 : logDomain p₀ =
      ⋂ s, (fun X : σ → ComplexMatrix2 => X s * (p₀ s)⁻¹) ⁻¹' ComplexMatrix2.logBall := by
    ext X
    simp [logDomain, ComplexMatrix2.logBall]
  rw [h2]
  exact isOpen_iInter_of_finite fun s =>
    isOpen_logBall.preimage ((continuous_apply s).mul continuous_const)
private theorem contDiff_expChartI [Fintype σ]
    (hH : Coordinates.ComplexCoordinates.PowerSeriesHolomorphy.Properties)
    (p₀ : σ → ComplexMatrix2) :
    ContDiff ℝ ∞ (expChartI p₀) := by
  refine contDiff_pi.2 fun s => ?_
  have h1 : ContDiff ℝ ∞ fun Y : σ → ComplexMatrix2.LieElement =>
      Complex.I • (Y s).toMatrix :=
    (toMatrixCLM.contDiff.comp (contDiff_apply ℝ ComplexMatrix2.LieElement s)).const_smul
      Complex.I
  exact ((contDiff_matExp hH).comp h1).mul contDiff_const
private theorem isOpen_smallBall [Fintype σ] (ε : ℝ) : IsOpen (smallBall σ ε) := by
  have h2 : smallBall σ ε =
      ⋂ s, (fun Y : σ → ComplexMatrix2.LieElement => toMatrixCLM (Y s)) ⁻¹'
        {Z | ComplexMatrix2.operatorNorm Z < ε} := by
    ext Y
    simp [smallBall, toMatrixCLM_apply]
  rw [h2]
  exact isOpen_iInter_of_finite fun s =>
    (isOpen_lt continuous_norm continuous_const).preimage
      (toMatrixCLM.continuous.comp (continuous_apply s))
abbrev _root_.YangMills.SharedProofs.p16540 := @isOpen_smallBall
private theorem expChartI_zero (p₀ : σ → ComplexMatrix2) : expChartI p₀ 0 = p₀ := by
  funext s
  rw [expChartI_apply]
  have : (0 : ComplexMatrix2.LieElement).toMatrix = 0 := rfl
  simp [ComplexMatrix2.matExp, this]
abbrev _root_.YangMills.SharedProofs.p27659 := @expChartI_zero
private theorem expChartI_localParam [Fintype σ]
    (hH : Coordinates.ComplexCoordinates.PowerSeriesHolomorphy.Properties)
    (hE : ComplexMatrix2.ExpLogEstimates)
    (hI : ComplexMatrix2.UnitaryLogConjugationProperties)
    (e : OrthonormalBasis (Fin 3) ℝ ComplexMatrix2.LieElement)
    {p₀ : σ → ComplexMatrix2} (hp : p₀ ∈ specialUnitaryPower σ) {ε : ℝ} (h0 : 0 < ε)
    (hε : Real.exp ε ≤ 19 / 10) :
    SmoothLocalParam (specialUnitaryPower σ) p₀ (expChartI p₀) (chartInverse e p₀)
      (smallBall σ ε) (logDomain p₀) where
  isOpen_src := isOpen_smallBall ε
  zero_mem := fun s => by
    have : (0 : ComplexMatrix2.LieElement).toMatrix = 0 := rfl
    simpa [this, ComplexMatrix2.operatorNorm] using h0
  isOpen_invDom := logDomain_isOpen p₀
  contDiffOn_map := (contDiff_expChartI hH p₀).contDiffOn
  contDiffOn_inv := by
    refine contDiffOn_pi.2 fun s => ?_
    exact (lieProjection e).contDiff.comp_contDiffOn
      ((contDiffOn_pi.1 (contDiffOn_logChart hH p₀)) s)
  mapsTo := fun Y hY =>
    ⟨fun s => (log_expChartI_mul_inv hE hp hε hY s).1, expChartI_mem hI hp Y⟩
  inv_map := by
    intro Y hY
    funext s
    have h1 : logChart p₀ (expChartI p₀ Y) s = (Y s).toMatrix := by
      simp only [logChart]
      rw [(log_expChartI_mul_inv hE hp hε hY s).2, smul_smul]
      simp
    simp only [chartInverse]
    rw [h1, lieProjection_toMatrix]
  map_zero_eq := expChartI_zero p₀
  isRelativelyOpen_range :=
    ⟨logImage p₀ ε, isOpen_logImage hH p₀ ε, image_smallBall hE hI hp hε⟩
private theorem toMatrix_injective {A B : ComplexMatrix2.LieElement}
    (h : A.toMatrix = B.toMatrix) : A = B :=
  Subtype.ext h
private def coeffLinearEquiv [Fintype σ] (e : OrthonormalBasis (Fin 3) ℝ ComplexMatrix2.LieElement)
    (he : ∀ a, e a = pauliLie a) {d : ℕ} (ν : σ × Fin 3 ≃ Fin d) :
    (Fin d → ℝ) ≃ₗ[ℝ] (σ → ComplexMatrix2.LieElement) where
  toFun u := ofCoeffs fun s a => u (ν (s, a))
  invFun Y k := inner ℝ (e (ν.symm k).2) (Y (ν.symm k).1)
  map_add' u v := by
    funext s
    simp [ofCoeffs, add_smul, Finset.sum_add_distrib]
  map_smul' c u := by
    funext s
    simp [ofCoeffs, mul_smul, Finset.smul_sum]
  left_inv u := by
    funext k
    obtain ⟨⟨s, a⟩, rfl⟩ := ν.surjective k
    simp [ofCoeffs, ← he, inner_sum, inner_smul_right, orthonormal_iff_ite.1 e.orthonormal]
  right_inv Y := by
    funext s
    simp only [ofCoeffs, ← he, Equiv.symm_apply_apply]
    exact e.sum_repr' (Y s)
private def coeffEquiv [Fintype σ] (e : OrthonormalBasis (Fin 3) ℝ ComplexMatrix2.LieElement)
    (he : ∀ a, e a = pauliLie a) {d : ℕ} (ν : σ × Fin 3 ≃ Fin d) :
    (Fin d → ℝ) ≃L[ℝ] (σ → ComplexMatrix2.LieElement) :=
  (coeffLinearEquiv e he ν).toContinuousLinearEquiv
private theorem coeffEquiv_apply [Fintype σ]
    (e : OrthonormalBasis (Fin 3) ℝ ComplexMatrix2.LieElement)
    (he : ∀ a, e a = pauliLie a) {d : ℕ} (ν : σ × Fin 3 ≃ Fin d) (u : Fin d → ℝ) :
    coeffEquiv e he ν u = ofCoeffs fun s a => u (ν (s, a)) := rfl
private theorem coeffEquiv_single [Fintype σ]
    (e : OrthonormalBasis (Fin 3) ℝ ComplexMatrix2.LieElement)
    (he : ∀ a, e a = pauliLie a) {d : ℕ} (ν : σ × Fin 3 ≃ Fin d) (s : σ) (a : Fin 3) :
    coeffEquiv e he ν (Pi.single (ν (s, a)) 1) = coeffDirection s a := by
  rw [coeffEquiv_apply]
  classical
  funext s'
  simp only [ofCoeffs, coeffDirection, Pi.single_apply, EmbeddingLike.apply_eq_iff_eq,
    Prod.mk.injEq]
  by_cases h : s' = s
  · subst h
    simp
  · simp [h]
private theorem expChartI_system [Fintype σ]
    (hH : Coordinates.ComplexCoordinates.PowerSeriesHolomorphy.Properties)
    (hE : ComplexMatrix2.ExpLogEstimates)
    (hI : ComplexMatrix2.UnitaryLogConjugationProperties) (hN : Numerics.ExpLogNumericBounds)
    (e : OrthonormalBasis (Fin 3) ℝ ComplexMatrix2.LieElement) :
    IsParamSystem (specialUnitaryPower σ) (expChartI (σ := σ)) := fun _ hp =>
  ⟨_, _, _, expChartI_localParam hH hE hI e hp (ε := 1 / 5) (by norm_num)
    (by have := hN.2.2.2.2.2.1; norm_num at this ⊢; linarith)⟩
private theorem logChart_expChartI (hE : ComplexMatrix2.ExpLogEstimates)
    {p₀ : σ → ComplexMatrix2} (hp : p₀ ∈ specialUnitaryPower σ) {ε : ℝ}
    (hε : Real.exp ε ≤ 19 / 10)
    {Y : σ → ComplexMatrix2.LieElement} (hY : Y ∈ smallBall σ ε) :
    logChart p₀ (expChartI p₀ Y) = fun s => (Y s).toMatrix := by
  funext s
  simp only [logChart]
  rw [(log_expChartI_mul_inv hE hp hε hY s).2, smul_smul]
  simp
private theorem powerCharts_holds [Fintype σ]
    (hH : Coordinates.ComplexCoordinates.PowerSeriesHolomorphy.Properties)
    (hE : ComplexMatrix2.ExpLogEstimates)
    (hI : ComplexMatrix2.UnitaryLogConjugationProperties)
    (e : OrthonormalBasis (Fin 3) ℝ ComplexMatrix2.LieElement) (he : ∀ a, e a = pauliLie a) :
    PowerCharts σ := by
  intro p₀ hp
  refine ⟨fun s => (Matrix.mem_specialUnitaryGroup_iff.1 (hp s)).2, fun Y => ⟨fun s => ?_, rfl,
    expChartI_mem hI hp Y⟩, fun ε h0 hε => ?_⟩
  · have h := (Y s).2.2
    show ComplexMatrix2.fullTrace (Complex.I • (Y s).toMatrix) = 0
    simp only [ComplexMatrix2.fullTrace] at h ⊢
    rw [Matrix.trace_smul, show Matrix.trace (Y s).toMatrix = 0 from h, smul_zero]
  · have hP := expChartI_localParam hH hE hI e hp h0 hε
    refine ⟨fun Y hY Y' hY' h => ?_, hP.isRelativelyOpen_range,
      ⟨0, hP.zero_mem, expChartI_zero p₀⟩, hP.contDiffOn_map,
      hP.isOpen_invDom, contDiffOn_logChart hH p₀, ?_, fun Y hY => logChart_expChartI hE hp hε hY,
      hP.toChart (coeffEquiv e he (Fintype.equivFin (σ × Fin 3))),
      Fintype.equivFin (σ × Fin 3), rfl, fun _ _ => rfl⟩
    · rw [← hP.inv_map Y hY, ← hP.inv_map Y' hY', h]
    · rintro _ ⟨Y, hY, rfl⟩
      exact (hP.mapsTo hY).1
private theorem hasDerivAt_expChartI_line (p₀ : σ → ComplexMatrix2) [Fintype σ]
    (Y : σ → ComplexMatrix2.LieElement) :
    HasDerivAt (fun t : ℝ => expChartI p₀ (t • Y)) (tangentVectorAt p₀ Y) 0 := by
  refine hasDerivAt_pi.2 fun s => ?_
  have h1 := hasDerivAt_exp_smul_const (𝕂 := ℝ) (Complex.I • (Y s).toMatrix) (0 : ℝ)
  have h2 := h1.mul_const (p₀ s)
  simp only [zero_smul, NormedSpace.exp_zero, one_mul] at h2
  have h3 : (fun t : ℝ => expChartI p₀ (t • Y) s) =
      fun y : ℝ => NormedSpace.exp (y • Complex.I • (Y s).toMatrix) * p₀ s := by
    funext t
    rw [expChartI_apply]
    show ComplexMatrix2.matExp (Complex.I • (t • (Y s).toMatrix)) * p₀ s = _
    rw [smul_comm]
  rw [h3]
  exact h2
private theorem readInCharts_holds [Fintype σ]
    (hH : Coordinates.ComplexCoordinates.PowerSeriesHolomorphy.Properties)
    (hE : ComplexMatrix2.ExpLogEstimates)
    (hI : ComplexMatrix2.UnitaryLogConjugationProperties) (hN : Numerics.ExpLogNumericBounds)
    (e : OrthonormalBasis (Fin 3) ℝ ComplexMatrix2.LieElement) (he : ∀ a, e a = pauliLie a)
    (F : Type) [NormedAddCommGroup F] [NormedSpace ℝ F] : ReadInCharts σ F := by
  intro O f hO
  have hS := expChartI_system (σ := σ) hH hE hI hN e
  set κ := coeffEquiv e he (Fintype.equivFin (σ × Fin 3))
  refine ⟨fun p₀ hp => exists_nhds_mapsTo hS hO hp, differentiableOnOpen_iff κ hS hO f,
    fun hd p₀ hp Y => ?_, contDiffOn_pullback_iff κ hS hO f⟩
  obtain ⟨hm, hder⟩ := hasDerivAt_tangentDifferential κ hS hO hd hp Y
  have hline := hasDerivAt_expChartI_line p₀ Y
  refine ⟨hline, ?_⟩
  have hχ : DifferentiableAt ℝ (expChartI p₀) 0 :=
    ((contDiff_expChartI hH p₀).differentiable (by simp)) 0
  have ht : fderiv ℝ (expChartI p₀) 0 Y = tangentVectorAt p₀ Y := by
    have h1 : HasFDerivAt (expChartI p₀) (fderiv ℝ (expChartI p₀) 0) ((0 : ℝ) • Y) := by
      rw [zero_smul]
      exact hχ.hasFDerivAt
    have hl : HasDerivAt (fun t : ℝ => t • Y) Y 0 := by
      simpa using (hasDerivAt_id (0 : ℝ)).smul_const Y
    have h2 := h1.comp_hasDerivAt (0 : ℝ) hl
    exact h2.unique hline
  refine ⟨ht ▸ hm, ?_⟩
  have hv : (⟨tangentVectorAt p₀ Y, ht ▸ hm⟩ : tangentSpace (specialUnitaryPower σ) p₀) =
      ⟨fderiv ℝ (expChartI p₀) 0 Y, hm⟩ := Subtype.ext ht.symm
  rw [hv]
  exact hder
private theorem differentialReadInCharts_holds [Fintype σ]
    (hH : Coordinates.ComplexCoordinates.PowerSeriesHolomorphy.Properties)
    (hE : ComplexMatrix2.ExpLogEstimates)
    (hI : ComplexMatrix2.UnitaryLogConjugationProperties) (hN : Numerics.ExpLogNumericBounds)
    (e : OrthonormalBasis (Fin 3) ℝ ComplexMatrix2.LieElement) (he : ∀ a, e a = pauliLie a)
    (F : Type) [NormedAddCommGroup F] [NormedSpace ℝ F] : DifferentialReadInCharts σ F := by
  intro O f hO hd
  have hS := expChartI_system (σ := σ) hH hE hI hN e
  rw [hasDifferentiablePartialsOn_iff (coeffEquiv e he (Fintype.equivFin (σ × Fin 3))) hS hO hd]
  constructor
  · intro h p₀ hp
    obtain ⟨N, hN', hf, hk⟩ := h p₀ hp
    refine ⟨N, hN', hf, fun s a => ?_⟩
    have := hk (Fintype.equivFin (σ × Fin 3) (s, a))
    rwa [coeffEquiv_single] at this
  · intro h p₀ hp
    obtain ⟨N, hN', hf, hk⟩ := h p₀ hp
    refine ⟨N, hN', hf, fun k => ?_⟩
    obtain ⟨⟨s, a⟩, rfl⟩ := (Fintype.equivFin (σ × Fin 3)).surjective k
    rw [coeffEquiv_single]
    exact hk s a
private theorem powerMapsReadComponentwise_holds [Fintype σ] [Fintype τ] :
    PowerMapsReadComponentwise σ τ := by
  intro O g hO hg
  constructor
  · rintro ⟨⟨ho, h⟩, -⟩ t
    exact ⟨ho, fun c => (differentiableOn_pi.1 (h c)) t⟩
  · intro h
    exact ⟨⟨hO, fun c => differentiableOn_pi.2 fun t => (h t).2 c⟩, hg⟩
private theorem continuous_asGroupFactors :
    Continuous (asGroupFactors : (σ → ComplexMatrix2) → σ ⊕ Empty → ComplexMatrix2) := by apply _root_.YangMills.SharedProofs.p11373 <;> assumption
private theorem expChartAt_asGroupFactors (p₀ A : σ → ComplexMatrix2) :
    expChartAt (asGroupFactors p₀) (asGroupFactors A) = asGroupFactors (expChart p₀ A) := by
  funext i
  cases i with
  | inl s => rfl
  | inr k => exact k.elim
private def coordIndex {n : ℕ} (ν : σ ⊕ Empty ≃ Fin n) : σ × Fin 3 ≃ Fin (n * 3) :=
  (Equiv.prodCongr ((Equiv.sumEmpty σ Empty).symm.trans ν) (Equiv.refl _)).trans finProdFinEquiv
private def realPoint {N : ℕ} (μ : σ × Fin 3 ≃ Fin N) (y : σ → Fin 3 → ℝ) :
    Coordinates.ComplexCoordinates N :=
  fun k => ((y (μ.symm k).1 (μ.symm k).2 : ℝ) : ℂ)
private theorem realPoint_apply {N : ℕ} (μ : σ × Fin 3 ≃ Fin N) (y : σ → Fin 3 → ℝ)
    (s : σ) (a : Fin 3) : realPoint μ y (μ (s, a)) = ((y s a : ℝ) : ℂ) := by
  simp [realPoint]
private theorem ofCoeffs_toMatrix [Fintype σ] (y : σ → Fin 3 → ℝ) (s : σ) :
    (ofCoeffs y s).toMatrix = ∑ a, y s a • pauliFamily a := by
  have h := map_sum toMatrixCLM (fun a => y s a • pauliLie a) Finset.univ
  simp only [map_smul] at h
  exact h
private theorem tupleOfCoords_realPoint [Fintype σ]
    (b' : Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless)
    (hb' : ∀ a, ((b' a : ComplexMatrix2.traceless) : ComplexMatrix2) = Complex.I • pauliFamily a)
    (ν : σ ⊕ Empty ≃ Fin (Fintype.card (σ ⊕ Empty))) (y : σ → Fin 3 → ℝ) :
    tupleOfCoords b' ν (realPoint (coordIndex ν) y) =
      asGroupFactors (mulI (ofCoeffs y)) := by
  funext i
  cases i with
  | inl s =>
    have h1 : ∀ c, finProdFinEquiv (ν (.inl s), c) = coordIndex ν (s, c) := fun _ => rfl
    show ∑ c, realPoint (coordIndex ν) y (finProdFinEquiv (ν (.inl s), c)) •
        (b' c : ComplexMatrix2) = Complex.I • (ofCoeffs y s).toMatrix
    rw [ofCoeffs_toMatrix, Finset.smul_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [h1, realPoint_apply, hb', Complex.coe_smul, smul_comm]
  | inr k => exact k.elim
private theorem ofCoeffs_inner [Fintype σ]
    (e : OrthonormalBasis (Fin 3) ℝ ComplexMatrix2.LieElement)
    (he : ∀ a, e a = pauliLie a) (Y : σ → ComplexMatrix2.LieElement) :
    ofCoeffs (fun s a => inner ℝ (e a) (Y s)) = Y := by
  funext s
  simp only [ofCoeffs, ← he]
  exact e.sum_repr' (Y s)
private theorem inner_ofCoeffs [Fintype σ]
    (e : OrthonormalBasis (Fin 3) ℝ ComplexMatrix2.LieElement)
    (he : ∀ a, e a = pauliLie a) (y : σ → Fin 3 → ℝ) (s : σ) (a : Fin 3) :
    inner ℝ (e a) (ofCoeffs y s) = y s a := by
  simp [ofCoeffs, ← he, inner_sum, inner_smul_right,
    orthonormal_iff_ite.1 e.orthonormal]
private theorem holomorphic_expChartI_series [Fintype σ]
    (hH : Coordinates.ComplexCoordinates.PowerSeriesHolomorphy.Properties)
    (hC : GroupLieProduct.ExpChartHolomorphy.ExpChartTheory)
    (e : OrthonormalBasis (Fin 3) ℝ ComplexMatrix2.LieElement) (he : ∀ a, e a = pauliLie a)
    (b' : Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless)
    (hb' : ∀ a, ((b' a : ComplexMatrix2.traceless) : ComplexMatrix2) = Complex.I • pauliFamily a)
    {T : Type} {l : ℕ} (b : Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless)
    (ee : T ≃ Coordinates.ComplexCoordinates l)
    {W : Set (σ ⊕ Empty → ComplexMatrix2)} {Φ : (σ ⊕ Empty → ComplexMatrix2) → T}
    (hΦ : IsHolomorphicToCoords b ee W Φ) {p₀ : σ → ComplexMatrix2}
    (hW : asGroupFactors p₀ ∈ W) :
    ∃ (N : Set (σ → ComplexMatrix2.LieElement))
      (c : (σ → Fin 3 → ℕ) → Coordinates.ComplexCoordinates l),
      IsOpen N ∧ (0 : σ → ComplexMatrix2.LieElement) ∈ N ∧
      (∀ Y ∈ N, asGroupFactors (expChartI p₀ Y) ∈ W) ∧
      ContDiffOn ℝ ∞ (fun Y => ee (Φ (asGroupFactors (expChartI p₀ Y)))) N ∧
      ∀ y : σ → Fin 3 → ℝ, ofCoeffs y ∈ N →
        HasSum (fun m : σ → Fin 3 → ℕ => (∏ s, ∏ a, y s a ^ m s a) • c m)
          (ee (Φ (asGroupFactors (expChartI p₀ (ofCoeffs y))))) := by
  obtain ⟨-, -, hloc⟩ := hΦ
  obtain ⟨O', h0, hW', hhol⟩ := hloc _ hW
  have hhol' := ((hC.2.1 (σ ⊕ Empty)).2.1 T l ee b b' O' _).1 hhol
  let ν := Fintype.equivFin (σ ⊕ Empty)
  let μ := coordIndex ν
  have hG := hhol'.2 ν
  let G : Coordinates.ComplexCoordinates (Fintype.card (σ ⊕ Empty) * 3) →
      Coordinates.ComplexCoordinates l :=
    ee ∘ (Φ ∘ expChartAt (asGroupFactors p₀)) ∘ tupleOfCoords b' ν
  let D := tupleOfCoords b' ν ⁻¹' O'
  have hD : IsOpen D := hG.1
  have h0D : (0 : Coordinates.ComplexCoordinates (Fintype.card (σ ⊕ Empty) * 3)) ∈ D := by
    show tupleOfCoords b' ν 0 ∈ O'
    have : tupleOfCoords b' ν 0 = 0 := by
      funext i
      simp [tupleOfCoords, Coordinates.ComplexCoordinates.tracelessTuple]
    rwa [this]
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.1 hD 0 h0D
  have hρ : 0 < δ / 2 := by positivity
  have hsub : closedPolydisk 0 (δ / 2) ⊆ D := fun z hz => hball (by
    rw [mem_ball_zero_iff]
    have : ‖z‖ ≤ δ / 2 := (pi_norm_le_iff_of_nonneg hρ.le).2 fun j => by simpa using hz j
    linarith)
  obtain ⟨hser, hsm, -⟩ := (hH.1 _ D hD).1 _ G hG
  obtain ⟨c0, hsum, -⟩ := hser 0 h0D (δ / 2) hρ hsub
  let coef : (σ → ComplexMatrix2.LieElement) → σ → Fin 3 → ℝ := fun Y s a => inner ℝ (e a) (Y s)
  let A : (σ → ComplexMatrix2.LieElement) →
      Coordinates.ComplexCoordinates (Fintype.card (σ ⊕ Empty) * 3) :=
    fun Y => realPoint μ (coef Y)
  have hAc : ContDiff ℝ ∞ A := contDiff_pi.2 fun k =>
    Complex.ofRealCLM.contDiff.comp (contDiff_const.inner ℝ (contDiff_apply ℝ _ _))
  have hcoef : ∀ y, coef (ofCoeffs y) = y := fun y => by
    funext s a
    exact inner_ofCoeffs e he y s a
  have htup : ∀ Y, tupleOfCoords b' ν (A Y) = asGroupFactors (mulI Y) := fun Y => by
    have := tupleOfCoords_realPoint b' hb' ν (coef Y)
    rwa [ofCoeffs_inner e he Y] at this
  have hGA : ∀ Y, G (A Y) = ee (Φ (asGroupFactors (expChartI p₀ Y))) := fun Y => by
    simp only [G, Function.comp_apply]
    rw [htup, expChartAt_asGroupFactors]
    rfl
  let eqv : (σ → Fin 3 → ℕ) ≃ (Fin (Fintype.card (σ ⊕ Empty) * 3) → ℕ) :=
    { toFun := fun m j => m (μ.symm j).1 (μ.symm j).2
      invFun := fun m s a => m (μ (s, a))
      left_inv := fun m => by
        funext s a
        simp
      right_inv := fun m => by
        funext j
        simp }
  refine ⟨A ⁻¹' Metric.ball 0 (δ / 2), c0 ∘ eqv, Metric.isOpen_ball.preimage hAc.continuous, ?_,
    ?_, ?_, ?_⟩
  · have : A 0 = 0 := by
      funext k
      simp [A, coef, realPoint]
    simp [this, hρ]
  · intro Y hY
    have hmem : A Y ∈ D := hball (Metric.ball_subset_ball (by linarith) hY)
    have h1 := hW' _ hmem
    rw [htup, expChartAt_asGroupFactors] at h1
    exact h1
  · refine ContDiffOn.congr ?_ (fun Y _ => (hGA Y).symm)
    exact hsm.comp hAc.contDiffOn fun Y hY =>
      hball (Metric.ball_subset_ball (by linarith) hY)
  · intro y hy
    have hpoly : A (ofCoeffs y) ∈ openPolydisk 0 (δ / 2) := by
      intro j
      have h1 : ‖A (ofCoeffs y)‖ < δ / 2 := by
        simpa using hy
      have h2 := norm_le_pi_norm (A (ofCoeffs y)) j
      simpa using lt_of_le_of_lt h2 h1
    have hz := (Equiv.hasSum_iff eqv).2 (hsum _ hpoly)
    rw [hGA] at hz
    convert hz using 1
    funext m
    have hprod : ∏ j, (A (ofCoeffs y) j -
        (0 : Coordinates.ComplexCoordinates _) j) ^ (eqv m j) =
        ((∏ s, ∏ a, y s a ^ m s a : ℝ) : ℂ) := by
      rw [← Equiv.prod_comp μ, Fintype.prod_prod_type]
      push_cast
      refine Finset.prod_congr rfl fun s _ => Finset.prod_congr rfl fun a _ => ?_
      have h1 : A (ofCoeffs y) = realPoint μ y := by
        simp only [A, hcoef]
      rw [h1, realPoint_apply]
      simp [eqv]
    simp only [Function.comp_apply, monomialTerm]
    rw [hprod]
    funext k
    simp
private def HasLocalSeries {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] [Fintype σ]
    (O : Set (σ → ComplexMatrix2)) (f : (σ → ComplexMatrix2) → F) (p₀ : σ → ComplexMatrix2) :
    Prop :=
  ∃ N ∈ 𝓝 (0 : σ → ComplexMatrix2.LieElement), ChartMapsInto O p₀ N ∧
    ContDiffOn ℝ ∞ (f ∘ expChartI p₀) N ∧
    ∃ c : (σ → Fin 3 → ℕ) → F, ∀ y : σ → Fin 3 → ℝ, ofCoeffs y ∈ N →
      HasSum (fun m : σ → Fin 3 → ℕ => (∏ s, ∏ a, y s a ^ m s a) • c m)
        (f (expChartI p₀ (ofCoeffs y)))
private theorem hasLocalSeries_of_holomorphic [Fintype σ] {F : Type} [NormedAddCommGroup F]
    [NormedSpace ℝ F]
    (hH : Coordinates.ComplexCoordinates.PowerSeriesHolomorphy.Properties)
    (hC : GroupLieProduct.ExpChartHolomorphy.ExpChartTheory)
    (e : OrthonormalBasis (Fin 3) ℝ ComplexMatrix2.LieElement) (he : ∀ a, e a = pauliLie a)
    (b' : Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless)
    (hb' : ∀ a, ((b' a : ComplexMatrix2.traceless) : ComplexMatrix2) = Complex.I • pauliFamily a)
    (hS : IsParamSystem (specialUnitaryPower σ) (expChartI (σ := σ)))
    {O : Set (σ → ComplexMatrix2)} (hO : ComplexMatrix2.IsRelativelyOpen (specialUnitaryPower σ) O)
    {f : (σ → ComplexMatrix2) → F}
    {T : Type} {l : ℕ} (b : Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless)
    (ee : T ≃ Coordinates.ComplexCoordinates l)
    {W : Set (σ ⊕ Empty → ComplexMatrix2)} {Φ : (σ ⊕ Empty → ComplexMatrix2) → T}
    (hΦ : IsHolomorphicToCoords b ee W Φ) {p₀ : σ → ComplexMatrix2} (hp : p₀ ∈ O)
    (hW : asGroupFactors p₀ ∈ W) (Λ : Coordinates.ComplexCoordinates l →L[ℝ] F)
    (hag : ∀ x ∈ O, asGroupFactors x ∈ W → Λ (ee (Φ (asGroupFactors x))) = f x) :
    HasLocalSeries O f p₀ := by
  obtain ⟨N, c, hNo, hN0, hNW, hsm, hsum⟩ :=
    holomorphic_expChartI_series hH hC e he b' hb' b ee hΦ hW
  obtain ⟨ℓ, B, D, hP⟩ := hS p₀ (subset_of_isRelativelyOpen hO hp)
  have hval : ∀ Y ∈ N ∩ (B ∩ expChartI p₀ ⁻¹' O), f (expChartI p₀ Y) =
      Λ (ee (Φ (asGroupFactors (expChartI p₀ Y)))) := fun Y hY =>
    (hag _ hY.2.2 (hNW Y hY.1)).symm
  refine ⟨N ∩ (B ∩ expChartI p₀ ⁻¹' O),
    inter_mem (hNo.mem_nhds hN0) (hP.preimage_inter_mem_nhds hO hp),
    fun Y hY => hY.2.2, ?_, fun m => Λ (c m), fun y hy => ?_⟩
  · exact (Λ.contDiff.comp_contDiffOn (hsm.mono inter_subset_left)).congr hval
  · have h1 := Λ.hasSum (hsum y hy.1)
    rw [← hval _ hy] at h1
    simpa [map_smul] using h1
private theorem hasLocalSeries_pi [Fintype σ] [Fintype τ] [Nonempty τ]
    {O : Set (σ → ComplexMatrix2)}
    {f : (σ → ComplexMatrix2) → τ → ComplexMatrix2} {p₀ : σ → ComplexMatrix2}
    (h : ∀ t, HasLocalSeries O (fun x => f x t) p₀) : HasLocalSeries O f p₀ := by
  choose N hN hf hs c hc using h
  refine ⟨⋂ t, N t, iInter_mem.2 hN, ?_, ?_, fun m t => c t m, fun y hy => ?_⟩
  · obtain ⟨t⟩ := ‹Nonempty τ›
    exact fun Y hY => hf t (mem_iInter.1 hY t)
  · refine contDiffOn_pi.2 fun t => ?_
    exact (hs t).mono (iInter_subset _ t)
  · refine Pi.hasSum.2 fun t => ?_
    exact hc t y (mem_iInter.1 hy t)
private theorem of_hasLocalSeries [Fintype σ] {F : Type} [NormedAddCommGroup F]
    [NormedSpace ℝ F]
    {d : ℕ} (κ : (Fin d → ℝ) ≃L[ℝ] (σ → ComplexMatrix2.LieElement))
    (hS : IsParamSystem (specialUnitaryPower σ) (expChartI (σ := σ)))
    {O : Set (σ → ComplexMatrix2)} (hO : ComplexMatrix2.IsRelativelyOpen (specialUnitaryPower σ) O)
    {f : (σ → ComplexMatrix2) → F}
    (h : ∀ p ∈ O, HasLocalSeries O f p) :
    HasChartPowerSeries O f ∧ DifferentiableOnOpen (specialUnitaryPower σ) O f ∧
      HasDifferentiablePartialsOn (specialUnitaryPower σ) O f := by
  have hd : DifferentiableOnOpen (specialUnitaryPower σ) O f := by
    refine (differentiableOnOpen_iff κ hS hO f).2 fun p hp => ?_
    obtain ⟨N, hN, hf, hc, -⟩ := h p hp
    exact ⟨N, hN, hf, hc.differentiableOn (by simp)⟩
  refine ⟨⟨fun p hp => ?_, ?_⟩, hd, ?_⟩
  · obtain ⟨N, hN, hf, hc, c, hs⟩ := h p hp
    exact ⟨N, hN, hf, hc, c, hs⟩
  · refine (contDiffOn_pullback_iff κ hS hO f).2 fun p hp => ?_
    obtain ⟨N, hN, hf, hc, -⟩ := h p hp
    exact ⟨N, hN, hf, hc⟩
  · refine (hasDifferentiablePartialsOn_iff κ hS hO hd).2 fun p hp => ?_
    obtain ⟨N, hN, hf, hc, -⟩ := h p hp
    refine ⟨interior N, interior_mem_nhds.2 hN, hf.mono_left interior_subset, fun k => ?_⟩
    have h1 : ContDiffOn ℝ ∞ (f ∘ expChartI p) (interior N) := hc.mono interior_subset
    have h2 : ContDiffOn ℝ 1 (fderiv ℝ (f ∘ expChartI p)) (interior N) :=
      h1.fderiv_of_isOpen isOpen_interior (by norm_cast)
    exact (h2.differentiableOn (by simp)).clm_apply (differentiableOn_const _)
private def firstCoordCLM : Coordinates.ComplexCoordinates 1 →L[ℝ] ℂ :=
  (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 1 => ℂ) 0).restrictScalars ℝ
private theorem realAnalyticReadInCharts_holds [Fintype σ] [Fintype τ] [Nonempty τ]
    (hH : Coordinates.ComplexCoordinates.PowerSeriesHolomorphy.Properties)
    (hC : GroupLieProduct.ExpChartHolomorphy.ExpChartTheory)
    (hE : ComplexMatrix2.ExpLogEstimates)
    (hI : ComplexMatrix2.UnitaryLogConjugationProperties) (hN : Numerics.ExpLogNumericBounds)
    (e : OrthonormalBasis (Fin 3) ℝ ComplexMatrix2.LieElement) (he : ∀ a, e a = pauliLie a)
    (b' : Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless)
    (hb' : ∀ a, ((b' a : ComplexMatrix2.traceless) : ComplexMatrix2) = Complex.I • pauliFamily a)
    (b : Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless) : RealAnalyticReadInCharts σ τ b := by
  intro O hO
  have hS := expChartI_system (σ := σ) hH hE hI hN e
  have κ := coeffEquiv (σ := σ) e he (Fintype.equivFin (σ × Fin 3))
  refine ⟨fun f hf => ?_, fun f hf => ?_, fun f hf => ?_, fun f hm hf => ?_⟩
  · refine of_hasLocalSeries κ hS hO fun p hp => ?_
    obtain ⟨W, Φ, hpW, hΦ, hag⟩ := hf p hp
    refine hasLocalSeries_of_holomorphic hH hC e he b' hb' hS hO b _ hΦ hp hpW
      (Complex.reCLM.comp firstCoordCLM) fun x hx hxW => ?_
    rw [hag x hx hxW]
    simp [firstCoordCLM]
  · refine of_hasLocalSeries κ hS hO fun p hp => ?_
    obtain ⟨W, Φ, hpW, hΦ, hag⟩ := hf p hp
    refine hasLocalSeries_of_holomorphic hH hC e he b' hb' hS hO b _ hΦ hp hpW
      firstCoordCLM fun x hx hxW => ?_
    rw [hag x hx hxW]
    simp [firstCoordCLM]
  · have hl : ∀ p ∈ O, HasLocalSeries O f p := fun p hp => by
      obtain ⟨W, Φ, hpW, hΦ, hag⟩ := hf p hp
      refine hasLocalSeries_of_holomorphic hH hC e he b' hb' hS hO b _ hΦ hp hpW
        (matrixCLE.symm : Coordinates.ComplexCoordinates 4 →L[ℝ] ComplexMatrix2)
        fun x hx hxW => ?_
      rw [hag x hx hxW]
      simp [matrixCLE_symm_apply]
    have h := of_hasLocalSeries κ hS hO hl
    exact ⟨h.1, h.2.1⟩
  · have hl : ∀ p ∈ O, HasLocalSeries O f p := fun p hp => hasLocalSeries_pi fun t => by
      obtain ⟨W, Ψ, hpW, hΨ, hag⟩ := hf p hp
      have hgrp := hΨ.2.1 t
      have hco := ((hC.2.2.2.1 σ Empty).2.1 b W _ hΨ.1 hgrp.2.1).1 hgrp
      refine hasLocalSeries_of_holomorphic hH hC e he b' hb' hS hO b _ hco hp hpW
        (matrixCLE.symm : Coordinates.ComplexCoordinates 4 →L[ℝ] ComplexMatrix2)
        fun x hx hxW => ?_
      rw [hag x hx hxW]
      simp [matrixCLE_symm_apply, asGroupFactors]
    have h := of_hasLocalSeries κ hS hO hl
    exact ⟨h.1, h.2.1, hm⟩
private theorem asGroupFactors_mem {x : σ → ComplexMatrix2} (hx : x ∈ specialUnitaryPower σ) :
    asGroupFactors x ∈ GroupLieProduct σ Empty := by
  intro i
  cases i with
  | inl s => exact (Matrix.mem_specialUnitaryGroup_iff.1 (hx s)).2
  | inr k => exact k.elim
private theorem restrictionsRealAnalytic_holds [Fintype σ]
    (b : Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless) :
    RestrictionsRealAnalytic σ b := by
  intro W hW
  refine ⟨?_, fun Φ hΦ p hp => ⟨W, Φ, hp.1, hΦ, fun _ _ _ => rfl⟩,
    fun Φ hΦ p hp => ⟨W, Φ, hp.1, hΦ, fun _ _ _ => rfl⟩⟩
  obtain ⟨U, hU, rfl⟩ := hW
  refine ⟨asGroupFactors ⁻¹' U, hU.preimage continuous_asGroupFactors, ?_⟩
  ext x
  constructor
  · rintro ⟨⟨h1, -⟩, h3⟩
    exact ⟨h1, h3⟩
  · rintro ⟨h1, h3⟩
    exact ⟨⟨h1, asGroupFactors_mem h3⟩, h3⟩
theorem expChartsStatement_holds (hN : Numerics.ExpLogNumericBounds)
    (hI : ComplexMatrix2.UnitaryLogConjugationProperties)
    (hE : ComplexMatrix2.ExpLogEstimates)
    (hH : Coordinates.ComplexCoordinates.PowerSeriesHolomorphy.Properties)
    (hP : OneLoop.PauliMatrixRelations)
    (hC : GroupLieProduct.ExpChartHolomorphy.ExpChartTheory) : ExpChartsStatement := by
  intro σ τ _ _ _ _
  obtain ⟨e, he0⟩ := hP.2.2.1
  have he : ∀ a, e a = pauliLie a := fun a => toMatrix_injective (he0 a)
  obtain ⟨e', he'⟩ := hP.2.2.2.1
  let b' : Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless :=
    e'.unitsSMul fun _ => Units.mk0 Complex.I Complex.I_ne_zero
  have hb' : ∀ a, ((b' a : ComplexMatrix2.traceless) : ComplexMatrix2) =
      Complex.I • pauliFamily a := fun a => by
    have h1 : b' a = Units.mk0 Complex.I Complex.I_ne_zero • e' a :=
      Module.Basis.unitsSMul_apply a
    rw [h1, Units.smul_def, Submodule.coe_smul, he' a]
    rfl
  exact ⟨powerCharts_holds hH hE hI e he, readInCharts_holds hH hE hI hN e he ℝ,
    readInCharts_holds hH hE hI hN e he ℂ, readInCharts_holds hH hE hI hN e he ComplexMatrix2,
    differentialReadInCharts_holds hH hE hI hN e he ℝ,
    differentialReadInCharts_holds hH hE hI hN e he ℂ, powerMapsReadComponentwise_holds,
    fun b => ⟨realAnalyticReadInCharts_holds hH hC hE hI hN e he b' hb' b,
      restrictionsRealAnalytic_holds b⟩⟩
end YangMills.Construction.Matrices.PowerExpCharts
