import YangMills.Construction.Lattice.IteratesOfAComplexConfiguration
import YangMills.Construction.Lattice.OneStepObjectsAtRealBondFunctionsProof
import YangMills.Construction.Lattice.SchemeAverageDependsOnTheDoubleBlockAlone
import YangMills.Construction.Lattice.SchemeIterateReadsTheBareDoubleBlock
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.PeriodicLattice
variable {L m K : ℕ}
private theorem refinedBlock_eq_of_coe_eq {j₁ j₂ : ℤ} (e : j₁ = j₂) (n : ℕ) (x : Site L m j₁)
    (x' : Site L m j₂) (h : (x : FourTorus L m) = (x' : FourTorus L m)) :
    refinedBlock n x = refinedBlock n x' := by
  subst e
  rw [Subtype.ext h]
private theorem refinedBlock_subset_of_mem {n : ℕ}
    (hB : RefinedBlockNesting L m K (n + 1) (n + 1) n)
    (y : SiteAtLevel L m K (n + 1)) (x : SiteAtLevel L m K n)
    (hx : (x : FourTorus L m) ∈ refinedBlock (n + 1 - n) y) :
    refinedBlock n x ⊆ refinedBlock (n + 1) y := by
  have e : levelDepth K n = levelDepth K (n + 1) + ((n + 1 - n : ℕ) : ℤ) := by
    have h : n + 1 - n = 1 := by omega
    rw [h]
    simp only [levelDepth]
    push_cast
    ring
  have hmem : (x : FourTorus L m) ∈
      sublattice L m (levelDepth K (n + 1) + ((n + 1 - n : ℕ) : ℤ)) := by
    rw [← e]
    exact x.2
  intro z hz
  rw [(hB y).1]
  refine Set.mem_iUnion₂.mpr ⟨⟨(x : FourTorus L m), hmem⟩, hx, ?_⟩
  rw [← refinedBlock_eq_of_coe_eq e n x ⟨(x : FourTorus L m), hmem⟩ rfl]
  exact hz
private theorem sitesInBondBlockPair_zero_subset {n : ℕ}
    (hB : RefinedBlockNesting L m K (n + 1) (n + 1) n)
    (c : BondAtLevel L m K (n + 1)) (b : BondAtLevel L m K n)
    (hb : b ∈ (bondsWithin (sitesInBondBlockPair n c)).bonds) :
    sitesInBondBlockPair 0 b ⊆ sitesInBondBlockPair 0 c := by
  have hsite : ∀ x : SiteAtLevel L m K n, x ∈ sitesInBondBlockPair n c →
      refinedBlock n x ⊆ bondBlockPair 0 c := by
    intro x hx
    rcases hx with hx | hx
    · exact (refinedBlock_subset_of_mem hB c.source x hx).trans Set.subset_union_left
    · exact (refinedBlock_subset_of_mem hB c.target x hx).trans Set.subset_union_right
  intro z hz
  rcases hz with hz | hz
  · exact hsite b.source hb.1 hz
  · exact hsite b.target hb.2 hz
private theorem bondsWithin_sitesInBondBlockPair {n : ℕ} (c : BondAtLevel L m K (n + 1)) :
    (bondsWithin (sitesInBondBlockPair n c)).bonds =
      (bondsInDoubleBlock c : Set (BondAtLevel L m K n)) := by apply _root_.YangMills.Construction.PeriodicLattice.RealBondFieldStep.bondsWithin_sitesInBondBlockPair <;> assumption
private theorem bondsInDoubleBlock_opposite_eq {j j' : ℤ} (c : Bond L m j) :
    (bondsInDoubleBlock c.opposite : Set (Bond L m j')) = bondsInDoubleBlock c := by apply _root_.YangMills.Construction.PeriodicLattice.bondsInDoubleBlock_opposite <;> assumption
private theorem isGaugeField_of_eqOn {j j' : ℤ} {c : Bond L m j}
    {W W' : Bond L m j' → Matrices.ComplexMatrix2}
    (hW : IsGaugeField complexGaugeGroup (bondsInDoubleBlock c) W)
    (hEq : Set.EqOn W W' (bondsInDoubleBlock c)) :
    IsGaugeField complexGaugeGroup (bondsInDoubleBlock c) W' := by
  refine ⟨fun b hb => hEq hb ▸ hW.1 b hb, fun b hb => ?_⟩
  have hr : b.opposite ∈ (bondsInDoubleBlock c : Set (Bond L m j')) := ⟨hb.2, hb.1⟩
  rw [← hEq hr, ← hEq hb]
  exact hW.2 b hb
private theorem schemeBlockAverage_congr_of_positive (hloc : OneStepAverageIsLocal)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hm : 0 < m) {n : ℕ} (hn : n < K)
    (s : AveragingScheme) (c : BondAtLevel L m K (n + 1)) (hc : c.IsPositivelyOriented)
    (W W' : BondAtLevel L m K n → Matrices.ComplexMatrix2)
    (hEq : Set.EqOn W W' (bondsInDoubleBlock c)) (hd : IsSchemeAverageDefined s W c) :
    IsSchemeAverageDefined s W' c ∧ schemeBlockAverage s W c = schemeBlockAverage s W' c ∧
      schemeBlockAverage s W c.opposite = schemeBlockAverage s W' c.opposite := by
  have h := hloc L hL m K n hm hn s c hc W W' hd.1 (isGaugeField_of_eqOn hd.1 hEq) hEq
  exact ⟨h.1.mp hd, h.2 hd⟩
private theorem schemeBlockAverage_congr (hloc : OneStepAverageIsLocal)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hm : 0 < m) {n : ℕ} (hn : n < K)
    (s : AveragingScheme) (c : BondAtLevel L m K (n + 1))
    (W W' : BondAtLevel L m K n → Matrices.ComplexMatrix2)
    (hEq : Set.EqOn W W' (bondsInDoubleBlock c)) :
    (IsSchemeAverageDefinedAt s W c ↔ IsSchemeAverageDefinedAt s W' c) ∧
      (IsSchemeAverageDefinedAt s W c → schemeBlockAverage s W c = schemeBlockAverage s W' c) := by
  by_cases hc : c.IsPositivelyOriented
  · simp only [IsSchemeAverageDefinedAt, if_pos hc]
    exact ⟨⟨fun h => (schemeBlockAverage_congr_of_positive hloc hL hm hn s c hc W W' hEq h).1,
        fun h => (schemeBlockAverage_congr_of_positive hloc hL hm hn s c hc W' W hEq.symm h).1⟩,
      fun h => (schemeBlockAverage_congr_of_positive hloc hL hm hn s c hc W W' hEq h).2.1⟩
  · have hr : c.opposite.IsPositivelyOriented := by
      obtain ⟨μ, h | h⟩ := c.isNeighbour
      · exact absurd ⟨μ, h⟩ hc
      · refine ⟨μ, ?_⟩
        change c.source - c.target = unitStep L m (levelDepth K (n + 1)) μ
        rw [← neg_sub, h, neg_neg]
    have hEq' : Set.EqOn W W' (bondsInDoubleBlock c.opposite) := by
      rw [bondsInDoubleBlock_opposite_eq]
      exact hEq
    simp only [IsSchemeAverageDefinedAt, if_neg hc]
    exact ⟨⟨fun h =>
          (schemeBlockAverage_congr_of_positive hloc hL hm hn s c.opposite hr W W' hEq' h).1,
        fun h =>
          (schemeBlockAverage_congr_of_positive hloc hL hm hn s c.opposite hr W' W hEq'.symm h).1⟩,
      fun h => (schemeBlockAverage_congr_of_positive hloc hL hm hn s c.opposite hr W W' hEq' h).2.2⟩
theorem iteratedAverageLocality_of_coordinates (hcoord : CoordinateDescription)
    (hloc : OneStepAverageIsLocal) : IteratedAverageLocality := by
  intro L hL m K hm hK s
  have hlat := hcoord L m hL.1 hL.2 hm
  have main : ∀ j : ℕ, j ≤ K → ∀ (c : BondAtLevel L m K j)
      (U U' : BondAtLevel L m K 0 → Matrices.ComplexMatrix2),
      (∀ b ∈ (bondsWithin (sitesInBondBlockPair 0 c)).bonds, U b = U' b) →
      (IsIteratedAverageDefinedAt s U j c ↔ IsIteratedAverageDefinedAt s U' j c) ∧
        (IsIteratedAverageDefinedAt s U j c →
          iteratedAverage s j U c = iteratedAverage s j U' c) := by
    intro j
    induction j with
    | zero =>
      intro _ c U U' hUU
      have hself : ∀ x : SiteAtLevel L m K 0, (x : FourTorus L m) ∈ refinedBlock 0 x := by
        intro x
        rw [((hlat.2.2.1 (levelDepth K 0) 0 (by simp only [levelDepth]; omega)) x).2.2.2.2]
        exact Set.mem_singleton _
      have hc : c ∈ (bondsWithin (sitesInBondBlockPair 0 c)).bonds :=
        ⟨Or.inl (hself c.source), Or.inr (hself c.target)⟩
      exact ⟨Iff.rfl.trans (by simp only [IsIteratedAverageDefinedAt]), fun _ => hUU c hc⟩
    | succ n ih =>
      intro hn c U U' hUU
      have hnK : n < K := hn
      have hB : RefinedBlockNesting L m K (n + 1) (n + 1) n :=
        hlat.2.2.2 K (n + 1) (n + 1) n hK (by omega) le_rfl hn
      have ihb : ∀ b ∈ (bondsWithin (sitesInBondBlockPair n c)).bonds,
          (IsIteratedAverageDefinedAt s U n b ↔ IsIteratedAverageDefinedAt s U' n b) ∧
            (IsIteratedAverageDefinedAt s U n b →
              iteratedAverage s n U b = iteratedAverage s n U' b) := by
        intro b hb
        refine ih hnK.le b U U' fun a ha => hUU a ?_
        have hsub := sitesInBondBlockPair_zero_subset hB c b hb
        exact ⟨hsub ha.1, hsub ha.2⟩
      have hall : (∀ b ∈ (bondsWithin (sitesInBondBlockPair n c)).bonds,
            IsIteratedAverageDefinedAt s U n b) ↔
          ∀ b ∈ (bondsWithin (sitesInBondBlockPair n c)).bonds,
            IsIteratedAverageDefinedAt s U' n b :=
        forall₂_congr fun b hb => (ihb b hb).1
      have heq : (∀ b ∈ (bondsWithin (sitesInBondBlockPair n c)).bonds,
            IsIteratedAverageDefinedAt s U n b) →
          Set.EqOn (iteratedAverage s n U) (iteratedAverage s n U') (bondsInDoubleBlock c) := by
        intro hd b hb
        rw [← bondsWithin_sitesInBondBlockPair c] at hb
        exact (ihb b hb).2 (hd b hb)
      have hstep := fun hd => schemeBlockAverage_congr hloc hL hm hnK s c (iteratedAverage s n U)
        (iteratedAverage s n U') (heq hd)
      refine ⟨⟨fun h => ⟨hall.mp h.1, (hstep h.1).1.mp h.2⟩, fun h => ?_⟩,
        fun h => (hstep h.1).2 h.2⟩
      have hd := hall.mpr h.1
      exact ⟨hd, (hstep hd).1.mpr h.2⟩
  exact fun j hj c U U' _ _ hUU => main j hj c U U' hUU
end YangMills.Construction.PeriodicLattice
