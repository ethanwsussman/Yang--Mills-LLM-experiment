import YangMills.Construction.PassageToTheLimit.BoundedFormsThatConvergeAreEquicontinuous
import YangMills.Construction.PassageToTheLimit.RestrictionsOfCentredFunctionalsToProducts
import YangMills.Construction.PassageToTheLimit.SpaceAsAMetricSpaceTestFunctionsTranslationsReflections
import Mathlib
set_option autoImplicit false
open Filter Set Topology
noncomputable section
namespace YangMills.Construction.LimitSpaces
open YangMills.Construction.LimitSpaces.Ambient YangMills.Construction.ReflectionPositivity.CutoffMirrors
namespace Ambient
variable {s : Conventions.StandingParameters} {E : Ambient} {q : ℕ}
private theorem isCompactSubset_iUnion {W : Fin q → Set (E.Carrier s)}
    (hW : ∀ l, E.IsCompactSubset s (W l)) : E.IsCompactSubset s (⋃ l, W l) := by
  intro 𝒰 hopen hcover
  have hpiece : ∀ l, ∃ 𝒰' ⊆ 𝒰, 𝒰'.Finite ∧ W l ⊆ ⋃₀ 𝒰' := fun l =>
    hW l 𝒰 hopen ((subset_iUnion W l).trans hcover)
  choose piece hsub hfin hcov using hpiece
  refine ⟨⋃ l, piece l, iUnion_subset hsub, finite_iUnion hfin, iUnion_subset fun l => ?_⟩
  exact (hcov l).trans (sUnion_mono (subset_iUnion piece l))
private theorem infinite_of_eventually_mem {𝒥 𝒥' : Set ℕ+} (h𝒥 : 𝒥.Infinite)
    (h : ∀ᶠ j in indexAtTop 𝒥, j.1 ∈ 𝒥') : 𝒥'.Infinite := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp (eventually_comap.mp h)
  intro hfin
  refine h𝒥 ((hfin.union (finite_Iio N)).subset fun j hj => ?_)
  by_cases hjN : N ≤ j
  · exact Or.inl (hN j hjN ⟨j, hj⟩ rfl)
  · exact Or.inr (not_le.mp hjN)
variable {𝒥 : Set ℕ+} {Dom : 𝒥 → Set (E.Carrier s)}
private theorem tendsto_coveringIndex {W : Fin q → Set (E.Carrier s)} :
    Tendsto (coveringIndex (Dom := Dom) (W := W)) (indexAtTop (coveringIndices Dom W))
      (indexAtTop 𝒥) :=
  tendsto_comap_iff.mpr tendsto_comap
private theorem isSepTuple_univ {W : Fin q → Set (E.Carrier s)}
    (hW : E.ProductElementsAreSepTuples s W) (h : E.C1ProductSpace s W) :
    E.IsSepTuple s .cOne univ (components h) := by
  have hh := hW h
  exact ⟨⟨fun i => ⟨(hh.1.1 i).1, (hh.1.1 i).2.1, subset_univ _⟩, hh.1.2⟩, hh.2⟩
private theorem isSepTuple_dom {W : Fin q → Set (E.Carrier s)}
    (hW : E.ProductElementsAreSepTuples s W) (j : coveringIndices Dom W) (h : E.C1ProductSpace s W) :
    E.IsSepTuple s .lip (Dom (coveringIndex j)) (components h) := by
  have hh := hW h
  exact ⟨fun i => ⟨(hh.1.1 i).1, (hh.1.1 i).2.1, (hh.1.1 i).2.2.trans j.2.choose_spec⟩, hh.1.2⟩
private theorem isMultilinearRealForm_restrictedCentred {W : Fin q → Set (E.Carrier s)}
    (hq : 1 ≤ q) (hW : E.ProductElementsAreSepTuples s W)
    (hsep : Pairwise fun l l' => E.PositivelySeparated s (W l) (W l'))
    (Φ : (j : 𝒥) → E.TupleFunctionals s .lip (Dom j))
    (hmult : ∀ (j : 𝒥) (q : ℕ), 1 ≤ q → E.IsMultilinearOn s (E.centredSum s (Φ j) (q := q)))
    (j : coveringIndices Dom W) : IsMultilinearRealForm (restrictedCentred Φ j) := by
  intro i a b X Y Z hY hZ hi
  have hform : ∀ x : E.C1ProductSpace s W, restrictedCentred Φ j x =
      E.centredSum s (Φ (coveringIndex j)) ⟨components x, isSepTuple_dom hW j x⟩ :=
    fun x => dif_pos (isSepTuple_dom hW j x)
  have hsupp : ∀ (x : E.C1ProductSpace s W) (l : Fin q),
      components x l ∈ E.testWithin s .lip (W l) := fun x l =>
    ⟨(hW x).1.1 l |>.1, (x l).2.2⟩
  rw [hform Z, hform X, hform Y]
  exact hmult (coveringIndex j) q hq W
    (fun l => (subset_iUnion W l).trans j.2.choose_spec) hsep i a b
    ⟨components X, isSepTuple_dom hW j X⟩ ⟨components Y, isSepTuple_dom hW j Y⟩
    ⟨components Z, isSepTuple_dom hW j Z⟩ (hsupp X) (hsupp Y) (hsupp Z) hY hZ hi
end Ambient
theorem Ambient.centredRestrictionsToProducts_holds
    (hPass : Ambient.limitPassageStatement)
    (hConv : Ambient.pointwiseConvergentFormsEquicontinuous)
    (hMetric : AmbientMetric.Claim) :
    Ambient.centredRestrictionsToProducts := by
  intro s E q hq W hcompact hdisjoint 𝒥 Dom Φ hhead
  obtain ⟨hTup, hLim⟩ := hConv s E q hq W hcompact hdisjoint
  have hLimit : E.LimitCentredProperties s Φ :=
    ((hPass s E ⟨1, le_refl (1 : ℝ)⟩).2.2 𝒥 Dom Φ hhead).2.1
  have hsep : Pairwise fun l l' => E.PositivelySeparated s (W l) (W l') := fun l l' hne =>
    (hMetric s E).2.1.1 (W l) (W l') (hcompact l) (hcompact l') (hdisjoint hne)
  have hlarge : ∀ᶠ j in indexAtTop 𝒥, j.1 ∈ coveringIndices Dom W :=
    (hhead.exhausts _ (isCompactSubset_iUnion hcompact)).mono fun j hj => ⟨j.2, hj⟩
  have hreal : ∀ j : coveringIndices Dom W, IsMultilinearRealForm (restrictedCentred Φ j) :=
    isMultilinearRealForm_restrictedCentred hq hTup hsep Φ hLimit.2.1
  have hlim : ∀ h : E.C1ProductSpace s W, Tendsto (fun j => restrictedCentred Φ j h)
      (indexAtTop (coveringIndices Dom W))
      (𝓝 (E.evalOrZero s (E.centredSum s (E.limitFunctionals s Φ) (q := q)) (components h))) := by
    intro h
    have hY := isSepTuple_univ hTup h
    rw [show E.evalOrZero s (E.centredSum s (E.limitFunctionals s Φ) (q := q)) (components h) =
      E.centredSum s (E.limitFunctionals s Φ) ⟨components h, hY⟩ from dif_pos hY]
    exact ((hLimit.2.2.2 q ⟨components h, hY⟩).2).comp tendsto_coveringIndex
  refine ⟨hlarge, isSepTuple_dom hTup, isSepTuple_univ hTup, hreal, hlim,
    fun hbounded => ?_⟩
  exact hLim _ (restrictedCentred Φ) (infinite_of_eventually_mem hhead.infinite_index hlarge) hreal
    hbounded fun h => ⟨_, hlim h⟩
end YangMills.Construction.LimitSpaces
end
