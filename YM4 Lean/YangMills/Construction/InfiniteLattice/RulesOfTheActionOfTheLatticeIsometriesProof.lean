import YangMills.Construction.InfiniteLattice.BondsAndCutPlaquettesAtAMirrorProof
import YangMills.Construction.InfiniteLattice.LatticeIsometriesOfASpacingAsMotionsAndTheirAction
import YangMills.Construction.InfiniteLattice.RulesOfTheActionOfTheLatticeIsometries
import YangMills.Construction.InfiniteLattice.WhatAnObservableDependsOnAndItsSupport
import Mathlib
set_option autoImplicit false
open Set
namespace YangMills.Construction.InfiniteLattice.SymmetryActionRules
theorem orientedRepresentative_mem_positiveLinks (e : Link 1) :
    e.orientedRepresentative ∈ positiveLinks 1 := by apply _root_.YangMills.Construction.NormalFamilies.LevelCuts.orientedRepresentative_mem <;> assumption
theorem isLinkSet_linkImage (g : LatticeSymmetry 1) (S : Set (Link 1)) :
    IsLinkSet (g.linkImage S) := by
  rintro _ ⟨e, -, rfl⟩
  exact orientedRepresentative_mem_positiveLinks _
theorem eq_of_eq_orientedRepresentative (A B : GaugeField 1) (e : Link 1)
    (h : A e.orientedRepresentative = B e.orientedRepresentative) : A e = B e := by apply _root_.YangMills.Construction.NormalFamilies.LevelCuts.apply_eq_of_orientedRepresentative <;> assumption
theorem dependsOnlyOn_linkImage (g : LatticeSymmetry 1) {S : Set (Link 1)}
    {F : GaugeField 1 → ℂ} (h : DependsOnlyOn S F) :
    DependsOnlyOn (g.linkImage S) (g.actOn F) := by
  intro A B hAB
  refine h _ _ fun e he => ?_
  exact eq_of_eq_orientedRepresentative A B (g.linkMap e) (hAB _ ⟨e, he, rfl⟩)
theorem linkImage_linkImage_of_rightInverse (g h : LatticeSymmetry 1)
    (hgh : Function.RightInverse h.toFun g.toFun) {T : Set (Link 1)} (hT : IsLinkSet T) :
    g.linkImage (h.linkImage T) = T := by
  classical
  have hpt : ∀ x : LatticePoint 1, g.pointMap (h.pointMap x) = x := fun x =>
    Subtype.ext (hgh (x : AmbientSpace))
  have hlink : ∀ e : Link 1, g.linkMap (h.linkMap e) = e := fun e =>
    Link.ext (hpt _) (hpt _)
  have hopp : ∀ e : Link 1, g.linkMap e.opposite = (g.linkMap e).opposite := fun e =>
    Link.ext rfl rfl
  have hmain : ∀ e ∈ T, (g.linkMap (h.linkMap e).orientedRepresentative).orientedRepresentative = e := by
    intro e he
    have hpos : e.IsPositivelyOriented := hT he
    by_cases hc : (h.linkMap e).IsPositivelyOriented
    · have q : (h.linkMap e).orientedRepresentative = h.linkMap e := if_pos hc
      rw [q, hlink]
      exact if_pos hpos
    · have q : (h.linkMap e).orientedRepresentative = (h.linkMap e).opposite := if_neg hc
      rw [q, hopp, hlink]
      have hn : ¬ e.opposite.IsPositivelyOriented :=
        Link.opposite_not_isPositivelyOriented one_pos hpos
      have q' : e.opposite.orientedRepresentative = e.opposite.opposite := if_neg hn
      rw [q']
      rfl
  ext e
  constructor
  · rintro ⟨_, ⟨c, hc, rfl⟩, rfl⟩
    change (g.linkMap (h.linkMap c).orientedRepresentative).orientedRepresentative ∈ T
    rw [hmain c hc]
    exact hc
  · intro he
    exact ⟨_, ⟨e, he, rfl⟩, hmain e he⟩
theorem linkImage_mono (g : LatticeSymmetry 1) {S T : Set (Link 1)} (h : S ⊆ T) :
    g.linkImage S ⊆ g.linkImage T :=
  Set.image_mono h
theorem holds (hMotion : SymmetriesAsMotions.Statement)
    (hAction : SymmetryActionOnObservables)
    (hSupport : ObservableDependence.Statement) :
    SymmetryActionRules.Statement := by
  have hLeast : ∀ F : GaugeField 1 → ℂ, IsBoundedObservable F → IsLocalObservable F →
      IsLeast {T : Set (Link 1) | IsLinkSet T ∧ DependsOnlyOn T F}
        (observableSupport F) := fun F hF hl =>
    ((hSupport F hF ∅ ∅ (Set.empty_subset _) (Set.empty_subset _) Set.univ).2.2.2.2.1 hl).1
  have hBorel : ∀ g : LatticeSymmetry 1, ∀ F : GaugeField 1 → ℂ, IsBoundedObservable F →
      IsBoundedObservable (g.actOn F) ∧ (Continuous F → Continuous (g.actOn F)) ∧
        (IsLocalObservable F → IsLocalObservable (g.actOn F)) := by
    intro g F hF
    obtain ⟨-, -, -, -, -, ⟨-, h⟩, -⟩ := hMotion 1 one_pos g g
    have h' := h F F hF hF
    exact ⟨h'.1, h'.2.2.2.2.2.2.2.1, h'.2.2.2.2.2.2.2.2.2⟩
  have hSub : ∀ g : LatticeSymmetry 1, ∀ F : GaugeField 1 → ℂ, IsBoundedObservable F →
      IsLocalObservable F → observableSupport (g.actOn F) ⊆ g.linkImage (observableSupport F) := by
    intro g F hF hl
    have hb := hBorel g F hF
    exact (hLeast _ hb.1 (hb.2.2 hl)).2
      ⟨isLinkSet_linkImage g _, dependsOnlyOn_linkImage g (hLeast F hF hl).1.2⟩
  intro g g'
  obtain ⟨-, ⟨-, h, hh⟩, -, hFace, ⟨-, hComp, hHomeo, hInv⟩, ⟨-, hFun⟩, hEnergy, -⟩ :=
    hMotion 1 one_pos g g'
  have hleft := (hInv h hh).1
  have hright := (hInv h hh).2
  have hgh : ∀ F : GaugeField 1 → ℂ, g.actOn (h.actOn F) = F := fun F =>
    funext fun A => congrArg F (hleft A)
  have hhg : ∀ F : GaugeField 1 → ℂ, h.actOn (g.actOn F) = F := fun F =>
    funext fun A => congrArg F (hright A)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hComp, ?_, ?_⟩
  · intro F _
    funext A
    exact congrArg F (congrFun hComp A).symm
  · intro F F' _ _
    rfl
  · intro F _
    rfl
  · intro p
    exact ⟨fun q => hFace.1 p q, (hEnergy p).2⟩
  · intro O
    exact ((hAction ⟨1, one_pos⟩).2.2.1 g).2 O
  · ext F
    constructor
    · rintro ⟨G, ⟨hG, hl, hc⟩, rfl⟩
      have hb := hBorel g G hG
      exact ⟨hb.1, hb.2.2 hl, hb.2.1 hc⟩
    · rintro ⟨hF, hl, hc⟩
      have hb := hBorel h F hF
      exact ⟨h.actOn F, ⟨hb.1, hb.2.2 hl, hb.2.1 hc⟩, hgh F⟩
  · intro F hF hl
    have hb := hBorel g F hF
    refine Set.Subset.antisymm (hSub g F hF hl) ?_
    have h₁ : observableSupport F ⊆ h.linkImage (observableSupport (g.actOn F)) := by
      have := hSub h (g.actOn F) hb.1 (hb.2.2 hl)
      rwa [hhg F] at this
    have h₂ := linkImage_mono g h₁
    rwa [linkImage_linkImage_of_rightInverse g h hh.2 (hLeast _ hb.1 (hb.2.2 hl)).1.1] at h₂
  · exact ⟨h, funext hh.1, funext hh.2⟩
  · exact ⟨g.comp g', rfl⟩
  · exact ⟨hHomeo.homeomorph, rfl⟩
  · intro F hF
    exact (hFun F F hF hF).2.1
end YangMills.Construction.InfiniteLattice.SymmetryActionRules
