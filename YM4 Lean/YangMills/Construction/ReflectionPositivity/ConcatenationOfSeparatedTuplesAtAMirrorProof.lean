import YangMills.Construction.ReflectionPositivity.ConcatenationOfSeparatedTuplesAtAMirror
import YangMills.Construction.ReflectionPositivity.MirrorAndItsOpenSidesPartTheSpace
import YangMills.Construction.ReflectionPositivity.ReflectionAtACoordinateMirror
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.ReflectionPositivity.AxisMirror
namespace ReflectAppend
section Metric
variable {α : Type*} {d : α → α → ℝ} {σ : α → α}
private theorem isOpenWrt_preimage (hd : ∀ x y, d (σ x) (σ y) = d x y) {U : Set α}
    (hU : MetricNotions.IsOpenWrt d U) : MetricNotions.IsOpenWrt d (σ ⁻¹' U) := by
  intro x hx
  obtain ⟨ε, hε, hball⟩ := hU (σ x) hx
  refine ⟨ε, hε, fun y hy => hball (σ y) ?_⟩
  rw [hd]
  exact hy
private theorem closureWrt_preimage (hσ : Function.Involutive σ)
    (hd : ∀ x y, d (σ x) (σ y) = d x y) (S : Set α) :
    MetricNotions.closureWrt d (σ ⁻¹' S) = σ ⁻¹' MetricNotions.closureWrt d S := by
  ext x
  constructor
  · intro hx ε hε
    obtain ⟨y, hy, hxy⟩ := hx ε hε
    exact ⟨σ y, hy, by rwa [hd]⟩
  · intro hx ε hε
    obtain ⟨y, hy, hxy⟩ := hx ε hε
    refine ⟨σ y, ?_, ?_⟩
    · change σ (σ y) ∈ S
      rwa [hσ y]
    · rw [← hd x (σ y), hσ y]
      exact hxy
private theorem isCompactWrt_preimage (hσ : Function.Involutive σ)
    (hd : ∀ x y, d (σ x) (σ y) = d x y) {C : Set α}
    (hC : MetricNotions.IsCompactWrt d C) : MetricNotions.IsCompactWrt d (σ ⁻¹' C) := by
  intro 𝒰 h𝒰 hcov
  have hopen : ∀ V ∈ preimage σ '' 𝒰, MetricNotions.IsOpenWrt d V := by
    rintro _ ⟨U, hU, rfl⟩
    exact isOpenWrt_preimage hd (h𝒰 U hU)
  have hcover : C ⊆ ⋃₀ (preimage σ '' 𝒰) := by
    intro x hx
    have hx' : σ x ∈ σ ⁻¹' C := by
      change σ (σ x) ∈ C
      rwa [hσ x]
    obtain ⟨U, hU, hxU⟩ := hcov hx'
    exact ⟨σ ⁻¹' U, ⟨U, hU, rfl⟩, hxU⟩
  obtain ⟨𝒱, h𝒱, hfin, hsub⟩ := hC _ hopen hcover
  refine ⟨preimage σ '' 𝒱, ?_, hfin.image _, ?_⟩
  · rintro _ ⟨V, hV, rfl⟩
    obtain ⟨U, hU, rfl⟩ := h𝒱 hV
    have hUU : σ ⁻¹' (σ ⁻¹' U) = U := by
      ext x
      change σ (σ x) ∈ U ↔ x ∈ U
      rw [hσ x]
    rwa [hUU]
  · intro x hx
    obtain ⟨V, hV, hxV⟩ := hsub hx
    exact ⟨σ ⁻¹' V, ⟨V, hV, rfl⟩, hxV⟩
end Metric
private theorem reflectAt_involutive (h : ReflectionProperties) (D : MirrorData)
    (μ : Fin 4) (c : ℝ) (E : Ambient) : Function.Involutive (Ambient.reflectAt D μ c E) := by
  obtain ⟨⟨-, hinv, -, -, htinv, -⟩, -, -⟩ := h D μ c
  cases E with
  | torus => exact fun x => congrFun htinv x
  | euclidean => exact fun x => congrFun hinv x
private theorem reflectAt_metric (h : ReflectionProperties) (D : MirrorData)
    (μ : Fin 4) (c : ℝ) (E : Ambient) (x y : E.Point D) :
    Ambient.metric D E (Ambient.reflectAt D μ c E x) (Ambient.reflectAt D μ c E y) =
      Ambient.metric D E x y := by
  obtain ⟨⟨hiso, -, -, htiso, -⟩, -, -⟩ := h D μ c
  cases E with
  | torus => exact htiso x y
  | euclidean => exact hiso x y
private theorem contDiff_euclidReflect (μ : Fin 4) (c : ℝ) :
    ContDiff ℝ 1 (euclidReflect μ c) :=
  contDiff_id.sub
    ((contDiff_const.mul ((contDiff_apply ℝ ℝ μ).sub contDiff_const)).smul contDiff_const)
private theorem isC1_pullback (h : ProjectionFacts) (D : MirrorData) (μ : Fin 4)
    (c : ℝ) (E : Ambient) {f : E.Point D → ℝ} (hf : Ambient.IsC1 D E f) :
    Ambient.IsC1 D E (CoordMirror.pullback D ⟨μ, c⟩ E f) := by
  cases E with
  | torus =>
    obtain ⟨-, -, -, -, -, hdesc, -⟩ :=
      (h D).2.2.2.2.2 (axisSignFlip μ) ((2 * c) • PeriodicLattice.coordVec μ)
    rw [← euclidReflect_eq_frameAffine] at hdesc
    have hf' : ContDiff ℝ 1 (fun y => f (D.projection y)) := hf
    have hcomp : ContDiff ℝ 1 (fun y => f (D.projection (euclidReflect μ c y))) :=
      hf'.comp (contDiff_euclidReflect μ c)
    have heq : (fun y => f (D.descended (euclidReflect μ c) (D.projection y))) =
        fun y => f (D.projection (euclidReflect μ c y)) :=
      funext fun y => congrArg f (congrFun hdesc y)
    exact (congrArg (ContDiff ℝ 1) heq).mpr hcomp
  | euclidean =>
    have hf' : ContDiff ℝ 1 (fun y : Fin 4 → ℝ => f y) := hf
    exact hf'.comp (contDiff_euclidReflect μ c)
private theorem closedSupport_pullback (h : ReflectionProperties) (D : MirrorData)
    (μ : Fin 4) (c : ℝ) (E : Ambient) (f : E.Point D → ℝ) :
    Ambient.closedSupport D E (CoordMirror.pullback D ⟨μ, c⟩ E f) =
      Ambient.reflectAt D μ c E ⁻¹' Ambient.closedSupport D E f :=
  closureWrt_preimage (reflectAt_involutive h D μ c E) (reflectAt_metric h D μ c E)
    {x | f x ≠ 0}
private theorem pullback_mem_compactC1 (hp : ProjectionFacts)
    (h : ReflectionProperties) (D : MirrorData) (μ : Fin 4) (c : ℝ) (E : Ambient)
    {f : E.Point D → ℝ} (hf : f ∈ Ambient.compactC1 D ℝ E) :
    CoordMirror.pullback D ⟨μ, c⟩ E f ∈ Ambient.compactC1 D ℝ E := by
  refine ⟨isC1_pullback hp D μ c E hf.1, ?_⟩
  rw [closedSupport_pullback h]
  exact isCompactWrt_preimage (reflectAt_involutive h D μ c E)
    (reflectAt_metric h D μ c E) hf.2
private theorem closedSupport_pullback_subset (h : ReflectionProperties) (D : MirrorData)
    (μ : Fin 4) (c : ℝ) (E : Ambient) {f : E.Point D → ℝ}
    (hf : Ambient.closedSupport D E f ⊆ CoordMirror.upperSide D ⟨μ, c⟩ E) :
    Ambient.closedSupport D E (CoordMirror.pullback D ⟨μ, c⟩ E f) ⊆
      CoordMirror.lowerSide D ⟨μ, c⟩ E := by
  intro x hx
  rw [closedSupport_pullback h] at hx
  have himage := ((h D μ c).2.2 E).1
  rw [← himage]
  exact ⟨Ambient.reflectAt D μ c E x, hf hx, reflectAt_involutive h D μ c E x⟩
private theorem mem_separatedAll_iff {D : MirrorData} {E : Ambient} {F : Ambient.FnList D E} :
    F ∈ Ambient.separatedAll D E ↔ Ambient.IsSeparatedList D E F := by
  constructor
  · intro hF
    obtain ⟨n, -, hs⟩ := mem_iUnion.1 hF
    exact hs
  · intro hF
    exact mem_iUnion.2 ⟨_, rfl, hF⟩
end ReflectAppend
open ReflectAppend in
theorem reflectAppendSeparated (h₁ : ProjectionFacts)
    (h₂ : CarrierAndSidesPartition)
    (h₃ : ReflectionProperties) : ReflectAppendSeparated := by
  intro D E μ c F G hF hG
  obtain ⟨hFs, hFu⟩ := hF
  obtain ⟨hGs, hGu⟩ := hG
  rw [mem_separatedAll_iff] at hFs hGs
  have hσ : Ambient.IsSeparatedList D E (CoordMirror.reflectList D ⟨μ, c⟩ E F) := by
    refine ⟨?_, ?_⟩
    · intro g hg
      obtain ⟨f, hf, rfl⟩ := List.mem_map.1 hg
      exact pullback_mem_compactC1 h₁ h₃ D μ c E (hFs.1 f hf)
    · refine List.pairwise_map.2 (hFs.2.imp ?_)
      intro f g hfg
      rw [closedSupport_pullback h₃, closedSupport_pullback h₃]
      exact hfg.preimage _
  have hlow : ∀ g ∈ CoordMirror.reflectList D ⟨μ, c⟩ E F,
      Ambient.closedSupport D E g ⊆ CoordMirror.lowerSide D ⟨μ, c⟩ E := by
    intro g hg
    obtain ⟨f, hf, rfl⟩ := List.mem_map.1 hg
    exact closedSupport_pullback_subset h₃ D μ c E (hFu f hf)
  refine ⟨⟨mem_separatedAll_iff.2 hσ, hlow⟩, mem_separatedAll_iff.2 ⟨?_, ?_⟩⟩
  · intro g hg
    rcases List.mem_append.1 hg with hg | hg
    · exact hσ.1 g hg
    · exact hGs.1 g hg
  · refine List.pairwise_append.2 ⟨hσ.2, hGs.2, ?_⟩
    intro f hf g hg
    have hsides := ((h₂ D ⟨μ, c⟩).1 E).1.2.2.2
    exact (hsides.symm.mono (hlow f hf) (hGu g hg))
end YangMills.Construction.ReflectionPositivity.AxisMirror
