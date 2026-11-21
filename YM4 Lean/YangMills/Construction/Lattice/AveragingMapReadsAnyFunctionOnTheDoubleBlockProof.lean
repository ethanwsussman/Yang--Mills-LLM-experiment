import YangMills.Construction.Lattice.BlockAverageLocality
import YangMills.Construction.Lattice.ComplexAverageReadsTheDoubleBlockProof
import YangMills.Construction.Lattice.ElementaryBoundsOfOneStepProof
import YangMills.Construction.Lattice.IteratesOfAComplexConfiguration
import YangMills.Construction.Lattice.LieFieldsOnBondSets
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.PeriodicLattice
variable {L m : ℕ} {j j' : ℤ}
private theorem pathHolonomy_congr {U U' : Bond L m j → Matrices.ComplexMatrix2}
    {Γ : List (Bond L m j)} (h : ∀ b ∈ Γ, U b = U' b) :
    pathHolonomy U Γ = pathHolonomy U' Γ := by apply _root_.YangMills.Construction.PeriodicLattice.ComplexAverageLocality.pathHolonomy_congr <;> assumption
private theorem boundaryBonds_mem_bondsInside {X : Set (FourTorus L m)} {p : Plaquette L m j'}
    (hp : p ∈ (plaquettesInside X : Set (Plaquette L m j'))) :
    ∀ b ∈ p.boundaryBonds, b ∈ (bondsInside X : Set (Bond L m j')) := by apply _root_.YangMills.Construction.PeriodicLattice.SingleStepEstimate.boundaryBonds_mem_bondsInside <;> assumption
private theorem opposite_isPositivelyOriented {c : Bond L m j} (hc : ¬c.IsPositivelyOriented) :
    c.opposite.IsPositivelyOriented := by apply _root_.YangMills.Construction.PeriodicLattice.Bond.opposite_isPositivelyOriented <;> assumption
variable {K k : ℕ}
private theorem toSublattice_mem_sitesInBlock (hP : BlockPaths.Statement)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hm : 0 < m) (hk : k < K)
    (y : SiteAtLevel L m K (k + 1)) :
    y.toSublattice (levelDepth K k) ∈ sitesInBlock (levelDepth K k) y := by
  obtain ⟨⟨⟨-, himg⟩, -, -⟩, -, -⟩ := (hP L m K hL.1 hL.2 hm k hk).1 y
  have h0 : (0 : Fin 4 → ℤ) ∈ blockIndexBox L := by
    intro ν
    have hL2 := hL.2
    have : 0 ≤ centreToFaceSteps L := by
      unfold centreToFaceSteps
      omega
    simpa using this
  exact show ((y.toSublattice (levelDepth K k) : SiteAtLevel L m K k) : FourTorus L m) ∈
      unitBlock y from by
    rw [← himg]
    exact ⟨0, h0, by simp [offsetSite]⟩
abbrev _root_.YangMills.SharedProofs.p38533 := @toSublattice_mem_sitesInBlock
private theorem blockAverageOnPositive_congr (hP : BlockPaths.Statement)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hm : 0 < m) (hk : k < K) (ω : ℝ)
    {c : BondAtLevel L m K (k + 1)} (hc : c.IsPositivelyOriented)
    {U U' : BondAtLevel L m K k → Matrices.ComplexMatrix2}
    (h : ∀ b ∈ (bondsInDoubleBlock c : Set (BondAtLevel L m K k)), U b = U' b) :
    blockAverageOnPositive ω U c = blockAverageOnPositive ω U' c := by
  obtain ⟨μ, hμ⟩ := hc
  obtain ⟨⟨-, -, -, hd4, hd5, -⟩, -, -, hS, hPth⟩ := (hP L m K hL.1 hL.2 hm k hk).2 c μ hμ
  have hTargetMem : ∀ x ∈ sitesInBlock (levelDepth K k) c.source,
      shiftAcross c x ∈ sitesInBlock (levelDepth K k) c.target := by
    intro x hx
    rw [hd5 x hx, ← hd4]
    exact ⟨x, hx, rfl⟩
  have hSource : ∀ x ∈ sitesInBlock (levelDepth K k) c.source,
      contourHolonomies U c.source x = contourHolonomies U' c.source x := fun x hx =>
    funext fun σ => pathHolonomy_congr fun b hb =>
      h b ((hPth.1 c.source (Or.inl rfl) x hx).1 _ ⟨σ, rfl⟩ b hb)
  have hTarget : ∀ x ∈ sitesInBlock (levelDepth K k) c.target,
      contourHolonomies U c.target x = contourHolonomies U' c.target x := fun x hx =>
    funext fun σ => pathHolonomy_congr fun b hb =>
      h b ((hPth.1 c.target (Or.inr rfl) x hx).1 _ ⟨σ, rfl⟩ b hb)
  have hCross : ∀ x ∈ sitesInBlock (levelDepth K k) c.source,
      pathHolonomy U (crossingPath c x) = pathHolonomy U' (crossingPath c x) := fun x hx =>
    pathHolonomy_congr fun b hb => h b (hPth.2 x hx b hb)
  have hTransport : parallelTransport U c = parallelTransport U' c := by
    unfold parallelTransport
    rw [hS.2.1]
    exact hCross _ (toSublattice_mem_sitesInBlock hP hL hm hk c.source)
  have hDefect : ∀ x ∈ sitesInBlock (levelDepth K k) c.source,
      crossingDefect U c x = crossingDefect U' c x := by
    intro x hx
    unfold crossingDefect meanContourHolonomy
    rw [hSource x hx, hTarget _ (hTargetMem x hx), hCross x hx, hTransport]
  have hContourDefect : ∀ x ∈ sitesInBlock (levelDepth K k) c.source, ∀ σ σ',
      contourCrossingDefect U c x σ σ' = contourCrossingDefect U' c x σ σ' := by
    intro x hx σ σ'
    have e1 : pathHolonomy U (orderedContour c.source x σ) =
        pathHolonomy U' (orderedContour c.source x σ) :=
      congrFun (hSource x hx) σ
    have e2 : pathHolonomy U (orderedContour c.target (shiftAcross c x) σ') =
        pathHolonomy U' (orderedContour c.target (shiftAcross c x) σ') :=
      congrFun (hTarget _ (hTargetMem x hx)) σ'
    unfold contourCrossingDefect
    rw [e1, e2, hCross x hx, hTransport]
  have hRegular : IsRegularAveragingCase ω U c ↔ IsRegularAveragingCase ω U' c := by
    unfold IsRegularAveragingCase HasContourMean DoubleBlockPlaquettesNear
    refine and_congr ?_ (and_congr ?_ (and_congr ?_ ?_))
    · refine forall₂_congr fun p hp => ?_
      unfold plaquetteHolonomy
      rw [pathHolonomy_congr fun b hb => h b (boundaryBonds_mem_bondsInside hp b hb)]
    · exact forall₂_congr fun x hx => by rw [hSource x hx]
    · exact forall₂_congr fun x hx => by rw [hTarget x hx]
    · exact forall₂_congr fun x hx => by rw [hDefect x hx]
  have hNoMinusOne : (∀ x ∈ sitesInBlock (levelDepth K k) c.source, ∀ σ σ',
      contourCrossingDefect U c x σ σ' ≠ -1) ↔
      ∀ x ∈ sitesInBlock (levelDepth K k) c.source, ∀ σ σ',
        contourCrossingDefect U' c x σ σ' ≠ -1 :=
    forall₂_congr fun x hx => forall_congr' fun σ => forall_congr' fun σ' => by
      rw [hContourDefect x hx σ σ']
  have hRegularValue : regularAverageValue U c = regularAverageValue U' c := by
    unfold regularAverageValue
    rw [hTransport]
    refine congrArg (fun Z => Matrices.ComplexMatrix2.matExp (inverseFourthPowerWeight L • Z) *
      parallelTransport U' c) (finsum_mem_congr rfl fun x hx => ?_)
    rw [hDefect x hx]
  have hLogValue : logAverageValue U c = logAverageValue U' c := by
    unfold logAverageValue
    rw [hTransport]
    refine congrArg (fun Z => Matrices.ComplexMatrix2.matExp (inverseFourthPowerWeight L • Z) *
      parallelTransport U' c) (finsum_mem_congr rfl fun x hx => ?_)
    simp only [hContourDefect x hx]
  unfold blockAverageOnPositive
  by_cases h1 : IsRegularAveragingCase ω U c
  · rw [if_pos h1, if_pos (hRegular.1 h1)]
    exact hRegularValue
  · rw [if_neg h1, if_neg fun h' => h1 (hRegular.2 h')]
    by_cases h2 : ∀ x ∈ sitesInBlock (levelDepth K k) c.source, ∀ σ σ',
        contourCrossingDefect U c x σ σ' ≠ -1
    · rw [if_pos h2, if_pos (hNoMinusOne.1 h2)]
      exact hLogValue
    · rw [if_neg h2, if_neg fun h' => h2 (hNoMinusOne.2 h')]
      exact hTransport
theorem blockAverageDependsOnDoubleBlock_holds (hP : BlockPaths.Statement) :
    BlockAverageDependsOnDoubleBlock := by
  intro L m K k hL hm hk ω c U U' h
  by_cases hc : c.IsPositivelyOriented
  · simp only [blockAverage, if_pos hc]
    exact blockAverageOnPositive_congr hP hL hm hk ω hc h
  · have hr := opposite_isPositivelyOriented hc
    simp only [blockAverage, if_neg hc]
    rw [blockAverageOnPositive_congr hP hL hm hk ω hr fun b hb =>
      h b (by rwa [bondsInDoubleBlock_opposite] at hb)]
end YangMills.Construction.PeriodicLattice
