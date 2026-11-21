import YangMills.Construction.ToriAtArbitraryCouplings.ClassesOfFunctionsSeparatedTuplesAndTheSeparation
import YangMills.Construction.Torus.DistanceOfAPointAndASetAndNeighbourhoodsOfTorusOrFourSpace
import Mathlib
set_option autoImplicit false
open scoped ENNReal
noncomputable section
namespace YangMills.Construction.ToriAtArbitraryCouplings
open YangMills.Construction.ReflectionPositivity.AxisMirror (Ambient)
namespace TorusSide
variable (s : TorusSide)
def openThickening : (E : Ambient) → Set (s.Point E) → ℝ → Set (s.Point E)
  | .torus, P, η => AmbientPoints.openThickening s.asMirrorData.toStandingParameters .torus P η
  | .euclidean, P, η =>
    AmbientPoints.openThickening s.asMirrorData.toStandingParameters .euclidean P η
def closedThickening : (E : Ambient) → Set (s.Point E) → ℝ → Set (s.Point E)
  | .torus, P, η => AmbientPoints.closedThickening s.asMirrorData.toStandingParameters .torus P η
  | .euclidean, P, η =>
    AmbientPoints.closedThickening s.asMirrorData.toStandingParameters .euclidean P η
theorem mem_openThickening_iff (E : Ambient) (P : Set (s.Point E)) (η : ℝ) (x : s.Point E) :
    x ∈ s.openThickening E P η ↔ s.setDist E {x} P < ENNReal.ofReal η := by
  cases E <;> rfl
theorem mem_closedThickening_iff (E : Ambient) (P : Set (s.Point E)) (η : ℝ) (x : s.Point E) :
    x ∈ s.closedThickening E P η ↔ s.setDist E {x} P ≤ ENNReal.ofReal η := by
  cases E <;> rfl
def c1Submodule : (E : Ambient) → Set (s.Point E) → Submodule ℝ (s.Point E → ℝ)
  | .torus, A => AmbientPoints.c1Submodule (s := s.asMirrorData.toStandingParameters) (E := .torus) A
  | .euclidean, A =>
    AmbientPoints.c1Submodule (s := s.asMirrorData.toStandingParameters) (E := .euclidean) A
private theorem closureWrt_dist_eq_closure {X : Type*} [PseudoMetricSpace X] (Z : Set X) :
    MetricNotions.closureWrt (dist : X → X → ℝ) Z = closure Z := by
  ext x
  exact Metric.mem_closure_iff.symm
private theorem isOpenWrt_dist_iff {X : Type*} [PseudoMetricSpace X] (U : Set X) :
    MetricNotions.IsOpenWrt (dist : X → X → ℝ) U ↔ IsOpen U := by
  rw [Metric.isOpen_iff]
  refine forall₂_congr fun x _ => ?_
  constructor
  · rintro ⟨r, hr, h⟩
    exact ⟨r, hr, fun y hy => h y (by rwa [dist_comm, ← Metric.mem_ball])⟩
  · rintro ⟨r, hr, h⟩
    exact ⟨r, hr, fun y hy => h (by rwa [Metric.mem_ball, dist_comm])⟩
private theorem isCompactWrt_dist_iff {X : Type*} [PseudoMetricSpace X] (Z : Set X) :
    MetricNotions.IsCompactWrt (dist : X → X → ℝ) Z ↔ IsCompact Z := by
  constructor
  · intro hZ
    refine isCompact_of_finite_subcover fun {ι} U hU hcov => ?_
    obtain ⟨𝒰, hsub, hfin, hcov'⟩ := hZ (Set.range U)
      (by rintro _ ⟨i, rfl⟩; exact (isOpenWrt_dist_iff _).2 (hU i)) (by rwa [Set.sUnion_range])
    classical
    have hpick : ∀ V ∈ 𝒰, ∃ i, U i = V := fun V hV => hsub hV
    choose g hg using hpick
    refine ⟨hfin.toFinset.attach.image fun V => g V.1 (hfin.mem_toFinset.1 V.2), fun x hx => ?_⟩
    obtain ⟨V, hV, hxV⟩ := hcov' hx
    refine Set.mem_iUnion₂.2 ⟨g V hV, Finset.mem_image.2
      ⟨⟨V, hfin.mem_toFinset.2 hV⟩, Finset.mem_attach _ _, rfl⟩, ?_⟩
    rw [hg V hV]
    exact hxV
  · intro hZ 𝒰 hU hcov
    obtain ⟨t, ht, hfin, hcov'⟩ := hZ.elim_finite_subcover_image (b := 𝒰) (c := id)
      (fun V hV => (isOpenWrt_dist_iff V).1 (hU V hV)) (by simpa [Set.sUnion_eq_biUnion] using hcov)
    exact ⟨t, ht, hfin, by simpa [Set.sUnion_eq_biUnion] using hcov'⟩
private theorem compactTsupport_iff {X : Type*} [PseudoMetricSpace X] (f : X → ℝ) (A : Set X)
    {C C' : Prop} (hC : C ↔ C') :
    (C ∧ IsCompact (tsupport f) ∧ tsupport f ⊆ A) ↔
      (C' ∧ MetricNotions.IsCompactWrt (dist : X → X → ℝ)
          (MetricNotions.closureWrt (dist : X → X → ℝ) {x | f x ≠ 0}) ∧
        MetricNotions.closureWrt (dist : X → X → ℝ) {x | f x ≠ 0} ⊆ A) := by
  rw [closureWrt_dist_eq_closure, isCompactWrt_dist_iff, hC]
  rfl
theorem mem_c1Submodule_iff (E : Ambient) (A : Set (s.Point E)) (f : s.Point E → ℝ) :
    f ∈ s.c1Submodule E A ↔ f ∈ s.c1SuppIn E A := by
  cases E
  · exact compactTsupport_iff (X := AmbientPoints.Pt s.asMirrorData.toStandingParameters .torus)
      f A Iff.rfl
  · exact compactTsupport_iff (X := AmbientPoints.Pt s.asMirrorData.toStandingParameters .euclidean)
      f A Iff.rfl
end TorusSide
end YangMills.Construction.ToriAtArbitraryCouplings
end
