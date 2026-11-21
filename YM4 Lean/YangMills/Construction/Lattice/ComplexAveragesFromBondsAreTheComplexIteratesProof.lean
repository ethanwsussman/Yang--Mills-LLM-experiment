import YangMills.Construction.Lattice.BondOrientationDichotomy
import YangMills.Construction.Lattice.ComplexAverageReadsTheDoubleBlock
import YangMills.Construction.Lattice.ComplexAveragesFromBondsAreTheComplexIterates
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.PeriodicLattice
theorem complexAverageEqComplexIterate_of_local
    (hloc : ComplexAverageIsLocal)
    (hdich : BondOrientationDichotomy) :
    ComplexAverageEqComplexIterate := by
  classical
  intro L m K hL hm ℬ U j
  induction j with
  | zero =>
    intro _ c
    exact ⟨Iff.rfl, fun _ => rfl⟩
  | succ j ih =>
    intro hj c
    have ih' := ih (by omega)
    have hdepth : -(m : ℤ) < levelDepth K (j + 1) := by
      have : (0 : ℤ) ≤ levelDepth K (j + 1) := by
        simp only [levelDepth]
        omega
      omega
    have hoo : ∀ b : BondAtLevel L m K (j + 1), b.opposite.opposite = b := fun b => Bond.ext rfl rfl
    have onPos : ∀ p : BondAtLevel L m K (j + 1), p.IsPositivelyOriented →
        (((∀ b ∈ (bondsInDoubleBlock p : Set (BondAtLevel L m K j)),
            ComplexAverageIsDefined K ℬ U j b) ∧
          complexBlockFieldAtLevel j U ∈
            (complexAveragingDomainNearOne p : Set (BondAtLevel L m K j → Matrices.ComplexMatrix2))) ↔
            ComplexIterateDefinedAt ℬ U (j + 1) p) ∧
        (ComplexIterateDefinedAt ℬ U (j + 1) p →
          complexBlockAverageOnPositive (complexBlockFieldAtLevel j U) p =
            complexIterate ℬ U (j + 1) p) := by
      intro p hp
      have hr := hloc L m K j hL.1 hL.2 hm (by omega) p hp
      have agree : (∀ b ∈ (bondsInDoubleBlock p : Set (BondAtLevel L m K j)),
          ComplexIterateDefinedAt ℬ U j b) →
          ∀ b ∈ (bondsInDoubleBlock p : Set (BondAtLevel L m K j)), complexBlockFieldAtLevel j U b =
            onSetElseOne (bondsInDoubleBlock p) (complexIterate ℬ U j) b := by
        intro h b hb
        rw [(ih' b).2 (h b hb)]
        simp [onSetElseOne, hb]
      constructor
      · rw [complexIterateDefinedAt_succ ℬ U j hp]
        constructor
        · rintro ⟨h₁, h₂⟩
          have h₁' : ∀ b ∈ (bondsInDoubleBlock p : Set (BondAtLevel L m K j)),
              ComplexIterateDefinedAt ℬ U j b := fun b hb => (ih' b).1.1 (h₁ b hb)
          exact ⟨h₁', (hr.mem_domain_iff _ _ (agree h₁')).1 h₂⟩
        · rintro ⟨h₁, h₂⟩
          exact ⟨fun b hb => (ih' b).1.2 (h₁ b hb), (hr.mem_domain_iff _ _ (agree h₁)).2 h₂⟩
      · intro h
        rw [complexIterate_succ ℬ U j hp]
        exact hr.average_eq _ _ (agree ((complexIterateDefinedAt_succ ℬ U j hp).1 h).1)
    have defined : ∀ p : BondAtLevel L m K (j + 1), p.IsPositivelyOriented →
        ¬p.opposite.IsPositivelyOriented →
        (c = p ∨ c = p.opposite) →
        (ComplexAverageIsDefined K ℬ U (j + 1) c ↔
          ((∀ b ∈ (bondsInDoubleBlock p : Set (BondAtLevel L m K j)),
            ComplexAverageIsDefined K ℬ U j b) ∧
          complexBlockFieldAtLevel j U ∈
            (complexAveragingDomainNearOne p : Set (BondAtLevel L m K j → Matrices.ComplexMatrix2)))) := by
      intro p hp hp' hc
      rw [ComplexAverageIsDefined]
      constructor
      · intro h
        refine h p ?_ hp
        rcases hc with rfl | rfl
        · exact Or.inl rfl
        · exact Or.inr (hoo p).symm
      · intro h c' hc' hpos
        have : c' = p := by
          rcases hc with rfl | rfl
          · rcases hc' with rfl | rfl
            · rfl
            · exact absurd hpos hp'
          · rcases hc' with rfl | rfl
            · exact absurd hpos hp'
            · exact hoo p
        subst this
        exact h
    have hx := hdich L m hL hm _ hdepth c
    by_cases hc : c.IsPositivelyOriented
    · have hc' : ¬c.opposite.IsPositivelyOriented := by
        rcases hx with h | h
        · exact h.2
        · exact absurd hc h.2
      refine ⟨(defined c hc hc' (Or.inl rfl)).trans (onPos c hc).1, fun h => ?_⟩
      have := (onPos c hc).2 h
      rw [← this]
      show complexBlockAverage (complexBlockFieldAtLevel j U) c = _
      rw [complexBlockAverage, if_pos hc]
    · have hp : c.opposite.IsPositivelyOriented := by
        rcases hx with h | h
        · exact absurd h.1 hc
        · exact h.1
      have hp' : ¬c.opposite.opposite.IsPositivelyOriented := by
        rw [hoo]
        exact hc
      have hdef : ComplexIterateDefinedAt ℬ U (j + 1) c ↔
          ComplexIterateDefinedAt ℬ U (j + 1) c.opposite := by
        have := complexIterateDefinedAt_succ_opposite ℬ U j hp hp'
        rwa [hoo] at this
      refine ⟨((defined c.opposite hp hp' (Or.inr (hoo c).symm)).trans (onPos _ hp).1).trans
        hdef.symm, fun h => ?_⟩
      have hv := complexIterate_succ_opposite ℬ U j hp hp'
      rw [hoo] at hv
      rw [hv, ← (onPos _ hp).2 (hdef.1 h)]
      show complexBlockAverage (complexBlockFieldAtLevel j U) c = _
      rw [complexBlockAverage, if_neg hc]
end YangMills.Construction.PeriodicLattice
