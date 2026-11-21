import YangMills.Construction.ReflectionPositivity.SeparatedTuplesOfFourSpaceAndTheirFunctionals
import Mathlib
set_option autoImplicit false
open Filter Topology
noncomputable section
namespace YangMills.Construction.SeparatedTuples
open YangMills.Construction.InfiniteLattice (AmbientSpace)
open YangMills.Construction.TorusMetric (euclidNormVec)
def atInfinity : Filter AmbientSpace := comap euclidNormVec atTop
instance atInfinity_neBot : atInfinity.NeBot := by
  refine NeBot.comap_of_range_mem inferInstance (mem_of_superset (Ici_mem_atTop (0 : ℝ)) ?_)
  intro r hr
  refine ⟨fun _ => r / 2, ?_⟩
  have hsum : (∑ _i : Fin 4, (r / 2) ^ 2) = r ^ 2 := by
    simp
    ring
  simp only [euclidNormVec]
  rw [hsum]
  exact Real.sqrt_sq hr
theorem tsupport_comp_sub (f : RealValued) (v : AmbientSpace) :
    tsupport (fun x => f (x - v)) = (fun x => x - v) ⁻¹' tsupport f := by
  have hf : (fun x => f (x - v)) = f ∘ Homeomorph.addRight (-v) := by
    funext x
    simp [sub_eq_add_neg]
  rw [hf, tsupport_comp_eq_preimage]
  ext x
  simp [sub_eq_add_neg]
theorem isDisjointlySupported_pushList_translate (v : AmbientSpace) {Y : List RealValued}
    (hY : IsDisjointlySupported Y) : IsDisjointlySupported (pushList (translate v) Y) := by
  rw [pushList_translate]
  refine ⟨?_, ?_⟩
  · intro g hg
    obtain ⟨f, hf, rfl⟩ := List.mem_map.1 hg
    obtain ⟨hsmooth, hcpt⟩ := hY.1 f hf
    refine ⟨ContDiff.comp hsmooth (contDiff_id.sub contDiff_const), ?_⟩
    have hcomp : (fun x => f (x - v)) = f ∘ Homeomorph.addRight (-v) := by
      funext x
      simp [sub_eq_add_neg]
    rw [hcomp]
    exact hcpt.comp_homeomorph _
  · refine List.pairwise_map.2 (hY.2.imp fun {f g} hfg => ?_)
    rw [tsupport_comp_sub, tsupport_comp_sub]
    exact hfg.preimage _
theorem push_translate_val (v : AmbientSpace) (Y : SepTuple) :
    (push (translate v) Y).1 = pushList (translate v) Y.1 := by
  simp [push, isDisjointlySupported_pushList_translate v Y.2]
def unionOfSupports (X Y : SepTuple) : Set AmbientSpace :=
  (⋃ f ∈ X.1, tsupport f) ∪ ⋃ g ∈ Y.1, tsupport g
theorem isCompact_unionOfSupports (X Y : SepTuple) : IsCompact (unionOfSupports X Y) :=
  ((List.finite_toSet X.1).isCompact_biUnion fun f hf => (X.2.1 f hf).2).union
    ((List.finite_toSet Y.1).isCompact_biUnion fun f hf => (Y.2.1 f hf).2)
theorem composable_translate_of_far {X Y : SepTuple} {v : AmbientSpace}
    (hv : ∀ x ∈ unionOfSupports X Y, ∀ y ∈ unionOfSupports X Y,
      euclidNormVec (x - y) < euclidNormVec v) :
    SepTuple.Composable X (push (translate v) Y) := by
  intro f hf g hg
  rw [push_translate_val, pushList_translate] at hg
  obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hg
  refine Set.disjoint_left.2 fun x hx hx' => ?_
  rw [tsupport_comp_sub] at hx'
  have hxU : x ∈ unionOfSupports X Y := Or.inl (Set.mem_biUnion hf hx)
  have hyU : x - v ∈ unionOfSupports X Y := Or.inr (Set.mem_biUnion hk hx')
  have hlt := hv x hxU (x - v) hyU
  simp at hlt
theorem continuous_euclidNormVec : Continuous euclidNormVec := by
  unfold euclidNormVec
  fun_prop
theorem eventually_composable (X Y : SepTuple) :
    ∀ᶠ v in atInfinity, SepTuple.Composable X (push (translate v) Y) := by
  have hK := isCompact_unionOfSupports X Y
  have hc : IsCompact ((fun p : AmbientSpace × AmbientSpace => euclidNormVec (p.1 - p.2)) ''
      (unionOfSupports X Y ×ˢ unionOfSupports X Y)) :=
    (hK.prod hK).image (continuous_euclidNormVec.comp (continuous_fst.sub continuous_snd))
  obtain ⟨D, hD⟩ := hc.bddAbove
  have hfar : {v : AmbientSpace | D < euclidNormVec v} ∈ atInfinity :=
    mem_comap.2 ⟨Set.Ioi D, Ioi_mem_atTop D, subset_rfl⟩
  filter_upwards [hfar] with v hv
  exact composable_translate_of_far fun x hx y hy =>
    lt_of_le_of_lt (hD ⟨(x, y), ⟨hx, hy⟩, rfl⟩) hv
end YangMills.Construction.SeparatedTuples
