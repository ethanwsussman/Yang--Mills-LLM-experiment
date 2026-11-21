import YangMills.Construction.Lattice.ComplexAverageReadsTheDoubleBlockProof
import YangMills.Construction.Lattice.IteratesOfAComplexConfiguration
import YangMills.Construction.Lattice.SchemeAverageDependsOnTheDoubleBlockAlone
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.PeriodicLattice
variable {L m : ℕ} {j j' : ℤ}
private theorem pathHolonomy_congr {U U' : Bond L m j' → Matrices.ComplexMatrix2}
    {γ : List (Bond L m j')}
    (h : ∀ b ∈ γ, U b = U' b) : pathHolonomy U γ = pathHolonomy U' γ := by apply _root_.YangMills.Construction.PeriodicLattice.ComplexAverageLocality.pathHolonomy_congr <;> assumption
private theorem contourHolonomies_congr {U U' : Bond L m j' → Matrices.ComplexMatrix2}
    {e : Bond L m j} (hP : PathsInsideDoubleBlock j' e)
    (hE : Set.EqOn U U' (bondsInDoubleBlock e)) {y : Site L m j}
    (hy : y = e.source ∨ y = e.target) {x : Site L m j'} (hx : x ∈ sitesInBlock j' y) :
    contourHolonomies U y x = contourHolonomies U' y x :=
  funext fun σ => pathHolonomy_congr fun b hb => hE ((hP.1 y hy x hx).1 _ ⟨σ, rfl⟩ b hb)
private theorem contourHolonomy_congr {U U' : Bond L m j' → Matrices.ComplexMatrix2}
    {e : Bond L m j} (hP : PathsInsideDoubleBlock j' e)
    (hE : Set.EqOn U U' (bondsInDoubleBlock e)) (s : AveragingScheme)
    {y : Site L m j} (hy : y = e.source ∨ y = e.target) {x : Site L m j'}
    (hx : x ∈ sitesInBlock j' y) : contourHolonomy s U y x = contourHolonomy s U' y x := by
  cases s with
  | centred =>
    simp only [contourHolonomy, complexMeanContourHolonomy]
    rw [contourHolonomies_congr hP hE hy hx]
  | cornered =>
    simp only [contourHolonomy]
    exact pathHolonomy_congr fun b hb => hE ((hP.1 y hy x hx).2 b hb)
private theorem bondsInside_unitBlock_subset {e : Bond L m j} {y : Site L m j}
    (hy : y = e.source ∨ y = e.target) :
    (bondsInside (unitBlock y) : Set (Bond L m j')) ⊆ bondsInDoubleBlock e := by
  have hsub : unitBlock y ⊆ bondDoubleBlock e := by
    rcases hy with rfl | rfl
    · exact Set.subset_union_left
    · exact Set.subset_union_right
  exact fun b hb => ⟨hsub hb.1, hsub hb.2⟩
private theorem isGaugeField_of_eqOn_inside {U U' : Bond L m j' → Matrices.ComplexMatrix2}
    {X : Set (FourTorus L m)} (hU : IsGaugeField complexGaugeGroup (bondsInside X) U)
    (hE : Set.EqOn U U' (bondsInside X)) :
    IsGaugeField complexGaugeGroup (bondsInside X) U' := by
  refine ⟨fun b hb => hE hb ▸ hU.1 b hb, fun b hb => ?_⟩
  have hr : b.opposite ∈ (bondsInside X : Set (Bond L m j')) := ⟨hb.2, hb.1⟩
  rw [← hE hr, ← hE hb]
  exact hU.2 b hb
private theorem isContourHolonomyDefined_of_eqOn
    {U U' : Bond L m j' → Matrices.ComplexMatrix2} {e : Bond L m j}
    (hP : PathsInsideDoubleBlock j' e) (hE : Set.EqOn U U' (bondsInDoubleBlock e))
    (s : AveragingScheme) {y : Site L m j} (hy : y = e.source ∨ y = e.target)
    {x : Site L m j'} (h : IsContourHolonomyDefined s U y x) :
    IsContourHolonomyDefined s U' y x := by
  obtain ⟨hx, hconf, hs⟩ := h
  refine ⟨hx, isGaugeField_of_eqOn_inside hconf
    (hE.mono (bondsInside_unitBlock_subset hy)), ?_⟩
  cases s with
  | centred =>
    change Matrices.ComplexMatrix2.familyDiameter (contourHolonomies U' y x) <
      Averaging.centreOfMassDiameter
    rw [← contourHolonomies_congr hP hE hy hx]
    exact hs
  | cornered => trivial
private theorem baseTransport_congr {U U' : Bond L m j' → Matrices.ComplexMatrix2}
    {e : Bond L m j} {μ : Fin 4} (hP : PathsInsideDoubleBlock j' e)
    (hS : DoubleBlockAxialPaths j' e μ)
    (hE : Set.EqOn U U' (bondsInDoubleBlock e)) (s : AveragingScheme)
    (ht : e.source.toSublattice j' ∈ sitesInBlock j' e.source)
    (ho : blockAnchor j' e.source ∈ sitesInBlock j' e.source) :
    baseTransport s U e = baseTransport s U' e := by
  cases s with
  | centred =>
    change pathHolonomy U (axialPath (e.source.toSublattice j') (e.target.toSublattice j')) =
      pathHolonomy U' (axialPath (e.source.toSublattice j') (e.target.toSublattice j'))
    rw [hS.2.1]
    exact pathHolonomy_congr fun b hb => hE (hP.2 _ ht b hb)
  | cornered =>
    change pathHolonomy U (axialPath (blockAnchor j' e.source) (blockAnchor j' e.target)) =
      pathHolonomy U' (axialPath (blockAnchor j' e.source) (blockAnchor j' e.target))
    rw [hS.2.2]
    exact pathHolonomy_congr fun b hb => hE (hP.2 _ ho b hb)
private theorem shiftAcross_mem_sitesInBlock {e : Bond L m j} {μ : Fin 4}
    (hD : DoubleBlockCoordinates j' e μ) {x : Site L m j'}
    (hx : x ∈ sitesInBlock j' e.source) :
    shiftAcross e x ∈ sitesInBlock j' e.target := by
  rw [hD.2.2.2.2.1 x hx, ← hD.2.2.2.1]
  exact ⟨x, hx, rfl⟩
private theorem localDefect_congr {U U' : Bond L m j' → Matrices.ComplexMatrix2}
    {e : Bond L m j} {μ : Fin 4} (hD : DoubleBlockCoordinates j' e μ)
    (hP : PathsInsideDoubleBlock j' e) (hS : DoubleBlockAxialPaths j' e μ)
    (hE : Set.EqOn U U' (bondsInDoubleBlock e)) (s : AveragingScheme)
    (ht : e.source.toSublattice j' ∈ sitesInBlock j' e.source)
    (ho : blockAnchor j' e.source ∈ sitesInBlock j' e.source) {x : Site L m j'}
    (hx : x ∈ sitesInBlock j' e.source) : localDefect s U e x = localDefect s U' e x := by
  unfold localDefect
  rw [contourHolonomy_congr hP hE s (Or.inl rfl) hx,
    contourHolonomy_congr hP hE s (Or.inr rfl) (shiftAcross_mem_sitesInBlock hD hx),
    baseTransport_congr hP hS hE s ht ho,
    pathHolonomy_congr (U := U) (U' := U') fun b hb => hE (hP.2 x hx b hb)]
private theorem sublatticeSite_and_anchor_mem {y : Site L m j} (hL : 1 ≤ L)
    (hB : BlockCoordinates j' y) :
    y.toSublattice j' ∈ sitesInBlock j' y ∧ blockAnchor j' y ∈ sitesInBlock j' y := by
  refine ⟨?_, hB.2.2⟩
  have h₀ : (0 : ℤ) ≤ centreToFaceSteps L := by
    unfold centreToFaceSteps
    omega
  have hq : (0 : Fin 4 → ℤ) ∈ blockIndexBox L := fun ν => by
    simpa using h₀
  have hmem := Set.mem_image_of_mem
    (fun p => (offsetSite (y.toSublattice j') p : FourTorus L m)) hq
  rw [hB.1.2] at hmem
  change (y.toSublattice j' : FourTorus L m) ∈ unitBlock y
  simpa [offsetSite] using hmem
private theorem positiveBondAverage_congr (h : BlockPaths.Statement) {K n : ℕ}
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hm : 0 < m) (hn : n < K)
    (s : AveragingScheme) (e : BondAtLevel L m K (n + 1)) (he : e.IsPositivelyOriented)
    {U U' : BondAtLevel L m K n → Matrices.ComplexMatrix2}
    (hE : Set.EqOn U U' (bondsInDoubleBlock e)) :
    positiveBondAverage s U e = positiveBondAverage s U' e ∧
      (IsGaugeField complexGaugeGroup (bondsInDoubleBlock e) U' →
        IsSchemeAverageDefined s U e → IsSchemeAverageDefined s U' e) := by
  obtain ⟨μ, hμ⟩ := he
  obtain ⟨hsite, hbond⟩ := h L m K hL.1 hL.2 hm n hn
  obtain ⟨hD, -, -, hS, hP⟩ := hbond e μ hμ
  obtain ⟨ht, ho⟩ := sublatticeSite_and_anchor_mem (by have := hL.2; omega) (hsite e.source).1
  have hel : ∀ x ∈ sitesInBlock (levelDepth K n) e.source,
      localDefect s U e x = localDefect s U' e x :=
    fun x hx => localDefect_congr hD hP hS hE s ht ho hx
  refine ⟨?_, fun hU' hd => ⟨hU', ⟨fun x hx => ?_, fun x hx => ?_⟩, fun x hx => ?_⟩⟩
  · unfold positiveBondAverage
    rw [finsum_mem_congr rfl fun x hx => by rw [hel x hx],
      baseTransport_congr hP hS hE s ht ho]
  · exact isContourHolonomyDefined_of_eqOn hP hE s (Or.inl rfl) (hd.2.1.1 x hx)
  · exact isContourHolonomyDefined_of_eqOn hP hE s (Or.inr rfl) (hd.2.1.2 x hx)
  · rw [← hel x hx]
    exact hd.2.2 x hx
theorem oneStepAverageIsLocal_holds (h : BlockPaths.Statement) :
    OneStepAverageIsLocal := by
  intro L hL m K n hm hn s e he U U' hU hU' hE
  have hpos := positiveBondAverage_congr h hL hm hn s e he hE
  have hneg := positiveBondAverage_congr h hL hm hn s e he hE.symm
  refine ⟨⟨hpos.2 hU', hneg.2 hU⟩, fun _ => ⟨?_, ?_⟩⟩
  · simp only [oneStepAverage, schemeBlockAverage, if_pos he]
    exact hpos.1
  · have hE' : Set.EqOn U U' (bondsInDoubleBlock e.opposite) := by
      rw [bondsInDoubleBlock_opposite]
      exact hE
    by_cases hr : e.opposite.IsPositivelyOriented
    · simp only [oneStepAverage, schemeBlockAverage, if_pos hr]
      exact (positiveBondAverage_congr h hL hm hn s e.opposite hr hE').1
    · simp only [oneStepAverage, schemeBlockAverage, if_neg hr]
      have hoo : e.opposite.opposite = e := rfl
      rw [hoo, hpos.1]
end YangMills.Construction.PeriodicLattice
