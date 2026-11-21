import YangMills.Construction.Dirichlet.CoverCountProof
import YangMills.Construction.DirichletOperator.FactsOfTheSettingInLevelUnitsProof
import YangMills.Construction.RegionSequence.AvgOpWeightSum
import YangMills.Construction.RegionSequence.WeightedDistTriangle
import Mathlib
set_option autoImplicit false
open Set MeasureTheory
open YangMills.Construction.Torus
noncomputable section
namespace YangMills.Construction.RegionSequence.WeightedDist
section Segments
variable {d : ℕ} {S : ℝ}
theorem torusProj_surjective : Function.Surjective (torusProj d S) := by apply _root_.YangMills.Construction.Dirichlet.CoverCountProof.torusProj_surjective <;> assumption
theorem continuous_pointAt (s : TorusSegment d) : Continuous (s.pointAt S) := by apply _root_.YangMills.Construction.LevelUnitFacts.pointAt_continuous <;> assumption
theorem segmentUnion_singleton (s : TorusSegment d) :
    segmentUnion S [s] = s.pointAt S '' Icc 0 1 := by
  ext p
  constructor
  · rintro ⟨s', hs', τ, hτ, rfl⟩
    obtain rfl := List.mem_singleton.1 hs'
    exact ⟨τ, hτ, rfl⟩
  · rintro ⟨τ, hτ, rfl⟩
    exact ⟨s, List.mem_singleton.2 rfl, τ, hτ, rfl⟩
theorem segmentUnion_append (Γ Γ' : List (TorusSegment d)) :
    segmentUnion S (Γ ++ Γ') = segmentUnion S Γ ∪ segmentUnion S Γ' := by apply _root_.YangMills.Construction.LevelUnitFacts.segmentUnion_append <;> assumption
theorem lengthWithin_append (Γ Γ' : List (TorusSegment d)) (X : Set (PeriodicTorus d S)) :
    lengthWithin (Γ ++ Γ') X = lengthWithin Γ X + lengthWithin Γ' X := by
  simp [lengthWithin]
theorem lengthWithin_nonneg (Γ : List (TorusSegment d)) (X : Set (PeriodicTorus d S)) :
    0 ≤ lengthWithin Γ X := by apply _root_.YangMills.Construction.Dirichlet.Crossing.lengthWithin_nonneg <;> assumption
end Segments
variable (𝒮 : NestedRegions)
theorem scale_pos (n : ℕ) : 0 < 𝒮.scale n := by apply _root_.YangMills.Construction.RegionSequence.AvgOpWeightSum.scale_pos <;> assumption
theorem chainWeight_append (Γ Γ' : List (TorusSegment 4)) :
    𝒮.chainWeight (Γ ++ Γ') = 𝒮.chainWeight Γ + 𝒮.chainWeight Γ' := by
  simp only [NestedRegions.chainWeight, lengthWithin_append, mul_add, Finset.sum_add_distrib]
  ring
theorem chainWeight_nonneg (Γ : List (TorusSegment 4)) : 0 ≤ 𝒮.chainWeight Γ := by
  unfold NestedRegions.chainWeight
  exact add_nonneg
    (Finset.sum_nonneg fun n _ =>
      mul_nonneg (inv_nonneg.2 (scale_pos 𝒮 n).le) (lengthWithin_nonneg _ _))
    (mul_nonneg (inv_nonneg.2 𝒮.ξ_pos.le) (lengthWithin_nonneg _ _))
def connectingWeights (y y' : 𝒮.Point) : Set ℝ :=
  {r | ∃ Γ : List (TorusSegment 4), IsConnected (segmentUnion 𝒮.side Γ) ∧
    y ∈ segmentUnion 𝒮.side Γ ∧ y' ∈ segmentUnion 𝒮.side Γ ∧ r = 𝒮.chainWeight Γ}
theorem connectingWeights_nonempty (y y' : 𝒮.Point) : (connectingWeights 𝒮 y y').Nonempty := by
  obtain ⟨v, rfl⟩ := torusProj_surjective y
  obtain ⟨w, rfl⟩ := torusProj_surjective y'
  let s : TorusSegment 4 := ⟨v, w - v⟩
  refine ⟨_, [s], ?_, ?_, ?_, rfl⟩
  · rw [segmentUnion_singleton]
    exact (isConnected_Icc zero_le_one).image _ (continuous_pointAt s).continuousOn
  · exact ⟨s, List.mem_singleton.2 rfl, 0, ⟨le_rfl, zero_le_one⟩, by simp [s, TorusSegment.pointAt]⟩
  · exact ⟨s, List.mem_singleton.2 rfl, 1, ⟨zero_le_one, le_rfl⟩, by simp [s, TorusSegment.pointAt]⟩
theorem connectingWeights_bddBelow (y y' : 𝒮.Point) : BddBelow (connectingWeights 𝒮 y y') := by
  refine ⟨0, ?_⟩
  rintro r ⟨Γ, -, -, -, rfl⟩
  exact chainWeight_nonneg 𝒮 Γ
theorem sInf_connectingWeights_le_add (p q q' : 𝒮.Point) {a b : ℝ}
    (ha : a ∈ connectingWeights 𝒮 p q) (hb : b ∈ connectingWeights 𝒮 q q') :
    sInf (connectingWeights 𝒮 p q') ≤ a + b := by
  obtain ⟨Γ, hΓ, hp, hq, rfl⟩ := ha
  obtain ⟨Γ', hΓ', hq₁, hq', rfl⟩ := hb
  rw [← chainWeight_append]
  refine csInf_le (connectingWeights_bddBelow 𝒮 p q') ⟨Γ ++ Γ', ?_, ?_, ?_, rfl⟩
  · rw [segmentUnion_append]
    exact IsConnected.union ⟨q, hq, hq₁⟩ hΓ hΓ'
  · rw [segmentUnion_append]
    exact Or.inl hp
  · rw [segmentUnion_append]
    exact Or.inr hq'
theorem weightedDistTriangle_holds : WeightedDistTriangle := by
  intro 𝒮 p q q'
  change sInf (connectingWeights 𝒮 p q') ≤
    sInf (connectingWeights 𝒮 p q) + sInf (connectingWeights 𝒮 q q')
  have h₁ : ∀ b ∈ connectingWeights 𝒮 q q',
      sInf (connectingWeights 𝒮 p q') - b ≤ sInf (connectingWeights 𝒮 p q) :=
    fun b hb => le_csInf (connectingWeights_nonempty 𝒮 p q) fun a ha => by
      linarith [sInf_connectingWeights_le_add 𝒮 p q q' ha hb]
  have h₂ : sInf (connectingWeights 𝒮 p q') - sInf (connectingWeights 𝒮 p q) ≤
      sInf (connectingWeights 𝒮 q q') :=
    le_csInf (connectingWeights_nonempty 𝒮 q q') fun b hb => by linarith [h₁ b hb]
  linarith
end YangMills.Construction.RegionSequence.WeightedDist
