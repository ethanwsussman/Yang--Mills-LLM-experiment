import YangMills.Construction.Lattice.ComplexAverageReadsTheDoubleBlock
import YangMills.Construction.Lattice.ComplexBondwiseIteratesAreFormedByTheBondwiseMaps
import YangMills.Construction.Lattice.PositiveOneOfABondAndItsReverse
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.PeriodicLattice
variable {L m K : ℕ}
namespace ComplexPartialIters
theorem support_and_field (k : ℕ) (V : PartialGaugeField L m (levelDepth K k)) :
    ∀ (i : ℕ) (c : Bond L m (levelDepth K (k + i))),
      (c ∈ (complexPartialBlockAverageIter k V i).support ↔ ComplexPartialDefinedAt k V i c) ∧
      (ComplexPartialDefinedAt k V i c →
        (complexPartialBlockAverageIter k V i).field c = complexPartialValues k V i c)
  | 0, _ => ⟨Iff.rfl, fun _ => rfl⟩
  | i + 1, c => by
    have ih := support_and_field k V i
    have agree : (∀ b ∈ (bondsInDoubleBlock c : Set (Bond L m (levelDepth K (k + i)))),
          ComplexPartialDefinedAt k V i b) →
        onSetElseOne (bondsInDoubleBlock c) (complexPartialBlockAverageIter k V i).field =
          onSetElseOne (bondsInDoubleBlock c) (complexPartialValues k V i) := by
      intro hall
      funext b
      by_cases hb : b ∈ (bondsInDoubleBlock c : Set (Bond L m (levelDepth K (k + i))))
      · simp only [onSetElseOne, if_pos hb]
        exact (ih b).2 (hall b hb)
      · simp only [onSetElseOne, if_neg hb]
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · rintro ⟨hsub, hdom⟩
      have hdef : ∀ b ∈ (bondsInDoubleBlock c : Set (Bond L m (levelDepth K (k + i)))),
          ComplexPartialDefinedAt k V i b := fun b hb => (ih b).1.1 (hsub hb)
      refine ⟨hdef, ?_⟩
      rw [← agree hdef]
      exact hdom
    · rintro ⟨hdef, hdom⟩
      refine ⟨fun b hb => (ih b).1.2 (hdef b hb), ?_⟩
      rw [← agree hdef] at hdom
      exact hdom
    · rintro ⟨hdef, -⟩
      change complexBlockAverage (onSetElseOne (bondsInDoubleBlock c)
          (complexPartialBlockAverageIter k V i).field) c =
        complexBlockAverage (onSetElseOne (bondsInDoubleBlock c)
          (complexPartialValues k V i)) c
      rw [agree hdef]
theorem extendByOne_eq_on_doubleBlock {j j' : ℤ} (c : Bond L m j)
    (U : Bond L m j' → Matrices.ComplexMatrix2) :
    ∀ b ∈ (bondsInDoubleBlock c : Set (Bond L m j')),
      U b = onSetElseOne (bondsInDoubleBlock c) U b := by
  intro b hb
  simp only [onSetElseOne, if_pos hb]
theorem partialBlockAverage_univ (hL : Conventions.IsAdmissibleBlockingFactor L) (hm : 0 < m)
    {i : ℕ} (hi : i < K)
    (hpos : PositiveOrientationOfBondAndOpposite)
    (hloc : ComplexAverageIsLocal)
    (F : BondAtLevel L m K i → Matrices.ComplexMatrix2)
    (hF : ∀ c : BondAtLevel L m K (i + 1), c.IsPositivelyOriented →
      F ∈ complexAveragingDomainNearOne c) :
    (complexPartialBlockAverage (⟨univ, F⟩ : PartialGaugeField L m (levelDepth K i)) :
        PartialGaugeField L m (levelDepth K (i + 1))) =
      ⟨univ, complexBlockAverage F⟩ := by
  have hK : 0 < K := lt_of_le_of_lt (Nat.zero_le _) hi
  have key := hpos L m K hL hm hK i hi
  have local' := hloc L m K i hL.1 hL.2 hm hi
  have hsupp : ({c | bondsInDoubleBlock c ⊆ (univ : Set (BondAtLevel L m K i)) ∧
      onSetElseOne (bondsInDoubleBlock c) F ∈
        complexAveragingDomainNearOne c.positivelyOriented} :
        Set (BondAtLevel L m K (i + 1))) = univ := by
    refine eq_univ_of_forall fun c => ⟨subset_univ _, ?_⟩
    obtain ⟨-, -, hp, -, -, -, hP⟩ := key c
    refine ((local' c.positivelyOriented hp).mem_domain_iff F _ ?_).1 (hF _ hp)
    rw [hP]
    exact extendByOne_eq_on_doubleBlock c F
  have hfield : (fun c : BondAtLevel L m K (i + 1) =>
      complexBlockAverage (onSetElseOne (bondsInDoubleBlock c) F) c) = complexBlockAverage F := by
    funext c
    obtain ⟨-, -, hp, -, -, -, hP⟩ := key c
    by_cases hc : c.IsPositivelyOriented
    · simp only [complexBlockAverage, if_pos hc]
      exact ((local' c hc).average_eq F _ (extendByOne_eq_on_doubleBlock c F)).symm
    · have hopp : c.positivelyOriented = c.opposite := by
        simp only [Bond.positivelyOriented, if_neg hc]
      rw [hopp] at hp hP
      simp only [complexBlockAverage, if_neg hc]
      have hsame : ∀ b ∈ (bondsInDoubleBlock c.opposite : Set (BondAtLevel L m K i)),
          F b = onSetElseOne (bondsInDoubleBlock c) F b := by
        rw [hP]
        exact extendByOne_eq_on_doubleBlock c F
      rw [(local' c.opposite hp).average_eq F _ hsame]
  change (⟨_, _⟩ : PartialGaugeField L m (levelDepth K (i + 1))) = _
  rw [hsupp, hfield]
theorem cast_partialBlockAverage {a b : ℕ} (h : a = b)
    (W : PartialGaugeField L m (levelDepth K a))
    (h₁ : PartialGaugeField L m (levelDepth K (a + 1)) =
      PartialGaugeField L m (levelDepth K (b + 1)))
    (h₂ : PartialGaugeField L m (levelDepth K a) = PartialGaugeField L m (levelDepth K b)) :
    cast h₁ (complexPartialBlockAverage W : PartialGaugeField L m (levelDepth K (a + 1))) =
      (complexPartialBlockAverage (cast h₂ W) : PartialGaugeField L m (levelDepth K (b + 1))) := by
  subst h
  rfl
theorem bareIter_univ (hL : Conventions.IsAdmissibleBlockingFactor L) (hm : 0 < m)
    (hpos : PositiveOrientationOfBondAndOpposite)
    (hloc : ComplexAverageIsLocal)
    (U : BondAtLevel L m K 0 → Matrices.ComplexMatrix2) :
    ∀ i : ℕ, i ≤ K → U ∈ complexBlockFieldDomain (K := K) i →
      bareComplexPartialIter (⟨univ, U⟩ : PartialGaugeField L m (levelDepth K 0)) i =
        (⟨univ, complexBlockFieldAtLevel i U⟩ : PartialGaugeField L m (levelDepth K i))
  | 0, _, _ => rfl
  | i + 1, hi, hU => by
    have ih := bareIter_univ hL hm hpos hloc U i (Nat.le_of_succ_le hi) hU.1
    have step : bareComplexPartialIter
          (⟨univ, U⟩ : PartialGaugeField L m (levelDepth K 0)) (i + 1) =
        (complexPartialBlockAverage (bareComplexPartialIter
          (⟨univ, U⟩ : PartialGaugeField L m (levelDepth K 0)) i) :
            PartialGaugeField L m (levelDepth K (i + 1))) :=
      cast_partialBlockAverage (Nat.zero_add i) _ _ _
    rw [step, ih]
    exact partialBlockAverage_univ hL hm (Nat.lt_of_succ_le hi) hpos hloc _ hU.2
end ComplexPartialIters
open ComplexPartialIters in
theorem complexPartialItersFormedByPartialMaps_holds
    (hpos : PositiveOrientationOfBondAndOpposite)
    (hloc : ComplexAverageIsLocal) :
    ComplexPartialItersFormedByPartialMaps := by
  intro L m K hL hm j _
  exact ⟨fun V _ _ i _ c => support_and_field j V i c,
    fun U _ i hi hU => bareIter_univ hL hm hpos hloc U i hi hU⟩
end YangMills.Construction.PeriodicLattice
