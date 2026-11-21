import YangMills.Construction.InfiniteLattice.ElementaryFactsOfBondsSpecificationAndGaugeTransformations
import YangMills.Construction.InfiniteLattice.SupportsOfAnArrayAreLocallyFinite
import Mathlib
set_option autoImplicit false
namespace YangMills.Construction
open Set
namespace InfiniteLattice
theorem arraySupportsLocallyFinite_holds
    (hFacts : ElementaryLatticeFacts) :
    ArraySupportsLocallyFinite := by
  intro 𝔸
  obtain ⟨-, -, -, hLoc, -, -, -, hSym, -⟩ := hFacts 1 1 one_pos one_pos
  have hSupp : ∀ i : 𝔸.Label, observableSupport (𝔸.translate i) =
      shiftLinks (observableSupport (𝔸.gen i.2)) (i.1 : LatticePoint 1) := by
    intro i
    have hGen := 𝔸.gen_mem i.2
    exact (hSym (shift (i.1 : LatticePoint 1)) (shift (i.1 : LatticePoint 1))).2.2.2.2.2.1 _
      hGen.1 hGen.2.1
  have hFin : ∀ ι, (observableSupport (𝔸.gen ι)).Finite := fun ι =>
    (hLoc.2.2.2.2.2.2.2 _ (𝔸.gen_mem ι).1 (𝔸.gen_mem ι).2.1).2.2.1
  have hDiff : ∀ (b b' : Link 1) (v : LatticePoint 1),
      ((shift v).linkMap b').orientedRepresentative = b →
        v = b.initial - b'.initial ∨ v = b.terminal - b'.initial := by
    intro b b' v h
    unfold Link.orientedRepresentative at h
    split_ifs at h
    · left
      subst h
      apply Subtype.ext
      change v.1 = (b'.initial.1 + v.1) - b'.initial.1
      abel
    · right
      subst h
      apply Subtype.ext
      change v.1 = (b'.initial.1 + v.1) - b'.initial.1
      abel
  have hLink : ∀ b : Link 1, {i : 𝔸.Label | b ∈ observableSupport (𝔸.translate i)}.Finite := by
    intro b
    have hOffsets : (⋃ ι, ((fun b' : Link 1 => b.initial - b'.initial) ''
        observableSupport (𝔸.gen ι) ∪
        (fun b' : Link 1 => b.terminal - b'.initial) '' observableSupport (𝔸.gen ι))).Finite :=
      finite_iUnion fun ι => ((hFin ι).image _).union ((hFin ι).image _)
    have hInj : Function.Injective (fun i : 𝔸.Label => ((i.1 : LatticePoint 1), i.2)) := by
      rintro ⟨v, ι⟩ ⟨v', ι'⟩ h
      simp only [Prod.mk.injEq] at h
      exact Prod.ext (Subtype.ext h.1) h.2
    refine ((hOffsets.prod (finite_univ (α := Fin 𝔸.size))).preimage hInj.injOn).subset ?_
    intro i hi
    have hi' : b ∈ observableSupport (𝔸.translate i) := hi
    rw [hSupp i] at hi'
    obtain ⟨b', hb', hbb⟩ := hi'
    refine ⟨mem_iUnion.2 ⟨i.2, ?_⟩, mem_univ _⟩
    rcases hDiff b b' _ hbb with h | h
    · exact Or.inl ⟨b', hb', h.symm⟩
    · exact Or.inr ⟨b', hb', h.symm⟩
  refine ⟨hSupp, fun b _ => hLink b, fun W => ?_⟩
  refine (W.links.finite_toSet.biUnion fun b _ => hLink b).subset ?_
  rintro i ⟨b, hb, hbW⟩
  exact mem_biUnion hbW hb
end InfiniteLattice
end YangMills.Construction
