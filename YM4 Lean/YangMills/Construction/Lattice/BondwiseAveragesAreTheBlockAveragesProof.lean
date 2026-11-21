import YangMills.Construction.Lattice.AveragingMapIsABorelMap
import YangMills.Construction.Lattice.BlockAverageLocality
import YangMills.Construction.Lattice.BondwiseAveragesAreTheBlockAverages
import YangMills.Construction.Lattice.ComplexBondwiseIteratesAreFormedByTheBondwiseMaps
import YangMills.Construction.Lattice.RealAverageIsDefinedAtInnerBonds
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.PeriodicLattice
variable {L m K : ℕ}
namespace PartialAverages
theorem blockAverage_extendByOne (hloc : BlockAverageDependsOnDoubleBlock)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hm : 0 < m) {j : ℕ} (hj : j < K) (ω : ℝ)
    (U : BondAtLevel L m K j → Matrices.ComplexMatrix2) (c : BondAtLevel L m K (j + 1)) :
    blockAverage ω (onSetElseOne (bondsInDoubleBlock c) U) c = blockAverage ω U c :=
  hloc L m K j hL hm hj ω c _ _ fun _ hb => if_pos hb
theorem partialBlockAverage_univ (hloc : BlockAverageDependsOnDoubleBlock)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hm : 0 < m) {j : ℕ} (hj : j < K) (ω : ℝ)
    (U : BondAtLevel L m K j → Matrices.ComplexMatrix2) :
    (realPartialBlockAverage ω (⟨univ, U⟩ : PartialGaugeField L m (levelDepth K j)) :
        PartialGaugeField L m (levelDepth K (j + 1))) =
      ⟨univ, blockAverage ω U⟩ := by
  have hsupp : ({c | bondsInDoubleBlock c ⊆ (univ : Set (BondAtLevel L m K j))} :
      Set (BondAtLevel L m K (j + 1))) = univ :=
    eq_univ_of_forall fun _ => subset_univ _
  have hfield : (fun c : BondAtLevel L m K (j + 1) =>
      blockAverage ω (onSetElseOne (bondsInDoubleBlock c) U) c) = blockAverage ω U :=
    funext fun c => blockAverage_extendByOne hloc hL hm hj ω U c
  change (⟨_, _⟩ : PartialGaugeField L m (levelDepth K (j + 1))) = _
  rw [hsupp, hfield]
theorem cast_partialBlockAverage {a b : ℕ} (h : a = b) (ω : ℝ)
    (W : PartialGaugeField L m (levelDepth K a))
    (h₁ : PartialGaugeField L m (levelDepth K (a + 1)) =
      PartialGaugeField L m (levelDepth K (b + 1)))
    (h₂ : PartialGaugeField L m (levelDepth K a) = PartialGaugeField L m (levelDepth K b)) :
    cast h₁ (realPartialBlockAverage ω W : PartialGaugeField L m (levelDepth K (a + 1))) =
      (realPartialBlockAverage ω (cast h₂ W) : PartialGaugeField L m (levelDepth K (b + 1))) := by
  subst h
  rfl
theorem barePartialBlockAverageIter_univ (hloc : BlockAverageDependsOnDoubleBlock)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hm : 0 < m) (ω : ℝ)
    (U : BondAtLevel L m K 0 → Matrices.ComplexMatrix2) :
    ∀ i : ℕ, i ≤ K →
      barePartialBlockAverageIter ω (⟨univ, U⟩ : PartialGaugeField L m (levelDepth K 0)) i =
        (⟨univ, blockFieldAtLevel ω i U⟩ : PartialGaugeField L m (levelDepth K i))
  | 0, _ => rfl
  | i + 1, hi => by
    have ih := barePartialBlockAverageIter_univ hloc hL hm ω U i (Nat.le_of_succ_le hi)
    have hstep : barePartialBlockAverageIter ω
          (⟨univ, U⟩ : PartialGaugeField L m (levelDepth K 0)) (i + 1) =
        (realPartialBlockAverage ω (barePartialBlockAverageIter ω
          (⟨univ, U⟩ : PartialGaugeField L m (levelDepth K 0)) i) :
            PartialGaugeField L m (levelDepth K (i + 1))) :=
      cast_partialBlockAverage (Nat.zero_add i) ω _ _ _
    rw [hstep, ih]
    exact partialBlockAverage_univ hloc hL hm (Nat.lt_of_succ_le hi) ω _
theorem blockFieldAtLevel_mem {ω : ℝ} (hborel : ∀ k : ℕ, k < K → BlockAverageBorel L m K ω k)
    {U : BondAtLevel L m K 0 → Matrices.ComplexMatrix2} (hU : U ∈ gaugeFieldsAtLevel L m K 0) :
    ∀ i : ℕ, i ≤ K → blockFieldAtLevel ω i U ∈ gaugeFieldsAtLevel L m K i
  | 0, _ => hU
  | i + 1, hi => by
    obtain ⟨h, -⟩ := hborel i (Nat.lt_of_succ_le hi)
    exact h (blockFieldAtLevel_mem hborel hU i (Nat.le_of_succ_le hi))
theorem extendByOne_eq_of_isRestriction {j' : ℤ} {V V' : PartialGaugeField L m j'}
    (h : V'.IsRestriction V) {P : Set (Bond L m j')} (hP : P ⊆ V'.support) :
    onSetElseOne P V'.field = onSetElseOne P V.field := by
  funext b
  by_cases hb : b ∈ P
  · simp only [onSetElseOne, if_pos hb]
    exact h.2 b (hP hb)
  · simp only [onSetElseOne, if_neg hb]
theorem partialBlockAverage_isRestriction {i i' : ℤ} (ω : ℝ) {V V' : PartialGaugeField L m i'}
    (h : V'.IsRestriction V) :
    (realPartialBlockAverage ω V' : PartialGaugeField L m i).IsRestriction
      (realPartialBlockAverage ω V) := by
  refine ⟨fun c hc => Subset.trans hc h.1, fun c hc => ?_⟩
  change blockAverage ω (onSetElseOne (bondsInDoubleBlock c) V'.field) c =
    blockAverage ω (onSetElseOne (bondsInDoubleBlock c) V.field) c
  rw [extendByOne_eq_of_isRestriction h hc]
theorem complexPartialBlockAverage_isRestriction {i i' : ℤ} {V V' : PartialGaugeField L m i'}
    (h : V'.IsRestriction V) :
    (complexPartialBlockAverage V' : PartialGaugeField L m i).IsRestriction
      (complexPartialBlockAverage V) := by
  refine ⟨fun c hc => ⟨Subset.trans hc.1 h.1, ?_⟩, fun c hc => ?_⟩
  · rw [← extendByOne_eq_of_isRestriction h hc.1]
    exact hc.2
  · change complexBlockAverage (onSetElseOne (bondsInDoubleBlock c) V'.field) c =
      complexBlockAverage (onSetElseOne (bondsInDoubleBlock c) V.field) c
    rw [extendByOne_eq_of_isRestriction h hc.1]
theorem partialBlockAverageIter_isRestriction (ω : ℝ) (k : ℕ)
    {V V' : PartialGaugeField L m (levelDepth K k)} (h : V'.IsRestriction V) :
    ∀ i : ℕ, (partialBlockAverageIter ω k V' i).IsRestriction (partialBlockAverageIter ω k V i)
  | 0 => h
  | i + 1 => partialBlockAverage_isRestriction ω (partialBlockAverageIter_isRestriction ω k h i)
theorem complexPartialBlockAverageIter_isRestriction (k : ℕ)
    {V V' : PartialGaugeField L m (levelDepth K k)} (h : V'.IsRestriction V) :
    ∀ i : ℕ, (complexPartialBlockAverageIter k V' i).IsRestriction
      (complexPartialBlockAverageIter k V i)
  | 0 => h
  | i + 1 => complexPartialBlockAverage_isRestriction
      (complexPartialBlockAverageIter_isRestriction k h i)
end PartialAverages
open PartialAverages in
theorem PartialAveragesAgreeWithBlockAverage.proof
    (hborel : BlockAverageIsBorelMap)
    (hloc : BlockAverageDependsOnDoubleBlock)
    (hinner : RealAverageDefinedAtInnerBonds)
    (hcomplex : ComplexPartialItersFormedByPartialMaps) :
    PartialAveragesAgreeWithBlockAverage.Statement := by
  intro L m K hL hm j hj
  have hK : 0 < K := lt_of_le_of_lt (Nat.zero_le _) hj
  have hB : ∀ k : ℕ, k < K →
      BlockAverageBorel L m K (Averaging.smoothingRadius L) k := fun k hk =>
    hborel ⟨L, hL, ⟨K, hK⟩, ⟨m, hm⟩⟩ k hk
  refine ⟨fun U hU => ⟨partialBlockAverage_univ hloc hL hm hj _ U, ?_⟩,
    fun U hU i hi => ⟨barePartialBlockAverageIter_univ hloc hL hm _ U i hi,
      blockFieldAtLevel_mem hB hU i hi⟩,
    fun X hX U hU c hc => ?_, (hcomplex L m K hL hm j hj).1, (hcomplex L m K hL hm j hj).2,
    fun V V' _ _ h => ⟨fun _ i _ => partialBlockAverageIter_isRestriction _ j h i,
      fun _ i _ => complexPartialBlockAverageIter_isRestriction j h i⟩⟩
  · obtain ⟨h, -⟩ := hB j hj
    exact h hU
  · have hP : (bondsInDoubleBlock c : Set (BondAtLevel L m K j)) ⊆ bondsInside X :=
      (hinner L m K hL hm j hj X hX U hU c hc).1
    exact ⟨hP, hP, blockAverage_extendByOne hloc hL hm hj _ U c⟩
end YangMills.Construction.PeriodicLattice
