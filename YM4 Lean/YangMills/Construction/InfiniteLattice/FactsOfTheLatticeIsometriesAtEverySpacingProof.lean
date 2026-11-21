import YangMills.Construction.InfiniteLattice.FactsOfTheLatticeIsometriesAtEverySpacing
import YangMills.Construction.InfiniteLattice.FactsOfTheLocalFunctionsAtEverySpacing
import YangMills.Construction.InfiniteLattice.MeasurabilityIsDependenceOnVariablesAtEverySpacing
import YangMills.Construction.InfiniteLattice.SpaceOfConfigurationsAndLatticeIsometries
import Mathlib
set_option autoImplicit false
open MeasureTheory Set
namespace YangMills.Construction.InfiniteLattice
namespace LatticeSymmetryFacts
variable {a : ℝ}
theorem orientedRepresentative_of_pos {b : Link a} (h : b.IsPositivelyOriented) :
    b.orientedRepresentative = b := by
  rw [Link.orientedRepresentative, if_pos h]
theorem orientedRepresentative_of_not_pos {b : Link a} (h : ¬ b.IsPositivelyOriented) :
    b.orientedRepresentative = b.opposite := by
  rw [Link.orientedRepresentative, if_neg h]
theorem orientedRepresentative_opposite
    (hx : ∀ b : Link a, Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented)
    (b : Link a) : b.opposite.orientedRepresentative = b.orientedRepresentative := by
  rcases hx b with ⟨h, h'⟩ | ⟨h', h⟩
  · rw [orientedRepresentative_of_not_pos h', orientedRepresentative_of_pos h]
    rfl
  · rw [orientedRepresentative_of_pos h', orientedRepresentative_of_not_pos h]
theorem orientedRepresentative_mem_positiveLinks
    (hx : ∀ b : Link a, Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented)
    (b : Link a) : b.orientedRepresentative ∈ positiveLinks a := by
  rcases hx b with ⟨h, _⟩ | ⟨h', h⟩
  · rw [orientedRepresentative_of_pos h]
    exact h
  · rw [orientedRepresentative_of_not_pos h]
    exact h'
theorem orientedRepresentative_linkMap_comp
    (hx : ∀ b : Link a, Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented)
    (r r' : LatticeSymmetry a) (b : Link a) :
    (r.linkMap (r'.linkMap b).orientedRepresentative).orientedRepresentative =
      ((r.comp r').linkMap b).orientedRepresentative := by
  by_cases h : (r'.linkMap b).IsPositivelyOriented
  · rw [orientedRepresentative_of_pos h]
    rfl
  · rw [orientedRepresentative_of_not_pos h]
    have e : r.linkMap (r'.linkMap b).opposite = (r.linkMap (r'.linkMap b)).opposite := rfl
    rw [e, orientedRepresentative_opposite hx]
    rfl
theorem linkMap_linkMap_of_leftInverse {r s : LatticeSymmetry a}
    (h : ∀ x, r.toFun (s.toFun x) = x) (b : Link a) :
    r.linkMap (s.linkMap b) = b :=
  Link.ext (Subtype.ext (h _)) (Subtype.ext (h _))
theorem orientedRepresentative_linkMap_cancel
    (hx : ∀ b : Link a, Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented)
    {r s : LatticeSymmetry a} (h : ∀ x, r.toFun (s.toFun x) = x) {b : Link a}
    (hb : b ∈ positiveLinks a) :
    (r.linkMap (s.linkMap b).orientedRepresentative).orientedRepresentative = b := by
  rw [orientedRepresentative_linkMap_comp hx]
  have e : (r.comp s).linkMap b = b := linkMap_linkMap_of_leftInverse h b
  rw [e]
  exact orientedRepresentative_of_pos hb
theorem actOn_actOn_of_leftInverse {r s : LatticeSymmetry a}
    (h : ∀ x, r.toFun (s.toFun x) = x)
    (F : GaugeField a → ℂ) : r.actOn (s.actOn F) = F := by
  funext U
  have e : s.pullbackField (r.pullbackField U) = U := by
    apply Subtype.ext
    funext b
    change U.1 (r.linkMap (s.linkMap b)) = U.1 b
    rw [linkMap_linkMap_of_leftInverse h]
  change F (s.pullbackField (r.pullbackField U)) = F U
  rw [e]
theorem isLinkSet_linkImage
    (hx : ∀ b : Link a, Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented)
    (r : LatticeSymmetry a) (M : Set (Link a)) : IsLinkSet (r.linkImage M) := by
  rintro _ ⟨b, _, rfl⟩
  exact orientedRepresentative_mem_positiveLinks hx _
theorem dependsOnlyOn_linkImage (r : LatticeSymmetry a) {M : Set (Link a)}
    {F : GaugeField a → ℂ} (h : DependsOnlyOn M F) :
    DependsOnlyOn (r.linkImage M) (r.actOn F) := by
  intro U U' hU
  refine h _ _ fun b hb => ?_
  have hm : (r.linkMap b).orientedRepresentative ∈ r.linkImage M := ⟨b, hb, rfl⟩
  have h1 := hU _ hm
  change U.1 (r.linkMap b) = U'.1 (r.linkMap b)
  by_cases hp : (r.linkMap b).IsPositivelyOriented
  · rwa [orientedRepresentative_of_pos hp] at h1
  · rw [orientedRepresentative_of_not_pos hp] at h1
    have h2 : (U.1 (r.linkMap b))⁻¹ = (U'.1 (r.linkMap b))⁻¹ := by
      rw [← U.2, ← U'.2]
      exact h1
    exact inv_injective h2
end LatticeSymmetryFacts
open LatticeSymmetryFacts in
theorem latticeSymmetryPropertiesAtEverySpacing_of
    (space : FieldSpace.SymmetryProperties)
    (localFunctions : LocalFunctionPropertiesForAllSpacings)
    (measurability : MeasurableIffDependsOnlyAllSpacings) :
    LatticeSymmetryPropertiesAtEverySpacing := by
  intro a ha
  obtain ⟨-, hact, -, -, -, ⟨G, hG⟩, -, hx, -⟩ := space a ha
  have hloc := (measurability a ha).2.2.2
  obtain ⟨-, -, -, -, -, hsep, -, hsupp⟩ := localFunctions a ha
  have observ : ∀ (t : LatticeSymmetry a) (F : GaugeField a → ℂ), IsBoundedObservable F →
      IsBoundedObservable (t.actOn F) := fun t F hF => ((hact t t).2.2.1 F F hF hF).1
  have localImage : ∀ (t : LatticeSymmetry a) (F : GaugeField a → ℂ), IsBoundedObservable F →
      IsLocalObservable F → IsLocalObservable (t.actOn F) := by
    intro t F hF hL
    obtain ⟨M, -, hfin, hdep⟩ := (hloc F hF).mp hL
    exact (hloc _ (observ t F hF)).mpr
      ⟨t.linkImage M, isLinkSet_linkImage hx t M, hfin.image _, dependsOnlyOn_linkImage t hdep⟩
  have clocImage : ∀ (t : LatticeSymmetry a) (F : GaugeField a → ℂ),
      F ∈ continuousLocalFunctions a → t.actOn F ∈ continuousLocalFunctions a := by
    rintro t F ⟨h1, h2, h3⟩
    exact ⟨observ t F h1, localImage t F h1 h2, ((hact t t).2.2.1 F F h1 h1).2.2.1 h3⟩
  have suppSub : ∀ (t : LatticeSymmetry a) (F : GaugeField a → ℂ), IsBoundedObservable F →
      IsLocalObservable F →
      observableSupport (t.actOn F) ⊆ t.linkImage (observableSupport F) := by
    intro t F hF hL
    obtain ⟨hd, -, hfin, -⟩ := hsupp F hF hL
    exact (hsupp _ (observ t F hF) (localImage t F hF hL)).2.2.2 _
      (isLinkSet_linkImage hx t _) (hfin.image _) (dependsOnlyOn_linkImage t hd)
  intro r r'
  obtain ⟨s, hsr, hrs⟩ : ∃ s : LatticeSymmetry a,
      (∀ x, s.toFun (r.toFun x) = x) ∧ ∀ x, r.toFun (s.toFun x) = x := by
    obtain ⟨g, hg, hgr⟩ := (hG r.toFun).mp ⟨r, rfl⟩
    obtain ⟨s, hs⟩ := (hG (⇑g⁻¹)).mpr ⟨g⁻¹, G.inv_mem hg, rfl⟩
    refine ⟨s, fun x => ?_, fun x => ?_⟩
    · rw [hs, ← hgr]
      exact g.symm_apply_apply x
    · rw [hs, ← hgr]
      exact g.apply_symm_apply x
  refine ⟨?_, fun b _ => orientedRepresentative_linkMap_comp hx r r' b, ?_,
    fun M F _ _ h => dependsOnlyOn_linkImage r h, ?_, ?_, ?_⟩
  · refine InvOn.bijOn (f' := fun b => (s.linkMap b).orientedRepresentative)
      ⟨fun b hb => orientedRepresentative_linkMap_cancel hx hsr hb,
        fun b hb => orientedRepresentative_linkMap_cancel hx hrs hb⟩
      (fun b _ => orientedRepresentative_mem_positiveLinks hx _)
      (fun b _ => orientedRepresentative_mem_positiveLinks hx _)
  · intro M _
    ext c
    constructor
    · rintro ⟨_, ⟨b, hb, rfl⟩, rfl⟩
      exact ⟨b, hb, (orientedRepresentative_linkMap_comp hx r r' b).symm⟩
    · rintro ⟨b, hb, rfl⟩
      exact ⟨_, ⟨b, hb, rfl⟩, orientedRepresentative_linkMap_comp hx r r' b⟩
  · ext F
    constructor
    · rintro ⟨F', hF', rfl⟩
      exact clocImage r F' hF'
    · intro hF
      exact ⟨s.actOn F, clocImage s F hF, actOn_actOn_of_leftInverse hrs F⟩
  · intro F hF hL
    refine Subset.antisymm (suppSub r F hF hL) ?_
    have hrF := observ r F hF
    have hrL := localImage r F hF hL
    have h := suppSub s (r.actOn F) hrF hrL
    rw [actOn_actOn_of_leftInverse hsr] at h
    have hset := (hsupp _ hrF hrL).2.1
    rintro _ ⟨b, hb, rfl⟩
    obtain ⟨c, hc, rfl⟩ := h hb
    have e : (r.linkMap (s.linkMap c).orientedRepresentative).orientedRepresentative = c :=
      orientedRepresentative_linkMap_cancel hx hrs (hset hc)
    change (r.linkMap (s.linkMap c).orientedRepresentative).orientedRepresentative ∈ _
    rw [e]
    exact hc
  · intro ν hν
    have hmeas : Measurable r.pullbackField := (hact r r).1.continuous.measurable
    have hprob : IsProbabilityMeasure (ν.map r.pullbackField) :=
      Measure.isProbabilityMeasure_map hmeas.aemeasurable
    have hint : ∀ F : GaugeField a → ℂ, IsBoundedObservable F →
        stateEval (ν.map r.pullbackField) F = stateEval ν (r.actOn F) :=
      fun F hF => integral_map hmeas.aemeasurable hF.1.aestronglyMeasurable
    refine ⟨hprob, hint, fun hI F hF => hI F hF.1, fun hI A hA => ?_⟩
    have heq : ν.map r.pullbackField = ν :=
      hsep _ _ hprob hν fun F hF => (hint F hF.1).trans (hI F hF)
    change stateEval ν (r.actOn A) = stateEval ν A
    rw [← hint A hA, heq]
end YangMills.Construction.InfiniteLattice
