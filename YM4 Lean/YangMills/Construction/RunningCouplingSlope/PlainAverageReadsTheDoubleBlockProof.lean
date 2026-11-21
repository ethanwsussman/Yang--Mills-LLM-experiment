import YangMills.Construction.Lattice.PathsOfBlocksAndDoubleBlocks
import YangMills.Construction.RunningCouplingSlope.LegsOfTheOrdersAreContours
import YangMills.Construction.RunningCouplingSlope.PlainAverageReadsTheDoubleBlock
import YangMills.Construction.Towers.AveragedContourOfAPairDoesNotDependOnTheBondProof
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.RunningCouplingSlope
open Tower
private theorem pathHolonomy_congr {L n k j : ℕ} {U U' : Edge L n k j → Matrices.ComplexMatrix2}
    {γ : List (Edge L n k j)} (h : ∀ b ∈ γ, U b = U' b) :
    PeriodicLattice.pathHolonomy U γ = PeriodicLattice.pathHolonomy U' γ := by apply _root_.YangMills.Construction.Tower.PairContourIndependence.pathHolonomy_congr <;> assumption
theorem normalizedMeanLocal_of_blockPaths (hpaths : PeriodicLattice.BlockPaths.Statement)
    (hlegs : AxisOrderLegsAreContours) : NormalizedMeanLocal := by
  intro L hL n k j hn hj c hc U U' h
  obtain ⟨μ, hμ⟩ := hc
  obtain ⟨-, hdouble⟩ := hpaths L n k hL.1 hL.2 hn j hj
  obtain ⟨hD, -, -, -, hP⟩ := hdouble c μ hμ
  obtain ⟨-, -, -, himage, hshift, -⟩ := hD
  have htarget : ∀ x ∈ PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k j) c.source,
      PeriodicLattice.shiftAcross c x ∈
        PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k j) c.target := by
    intro x hx
    rw [hshift x hx, ← himage]
    exact ⟨x, hx, rfl⟩
  have hleg : ∀ y : Vertex L n k (j + 1), (y = c.source ∨ y = c.target) →
      ∀ x ∈ PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k j) y,
        ∀ π : Equiv.Perm (Fin 4),
          PeriodicLattice.pathHolonomy U (contourLeg y x π) =
            PeriodicLattice.pathHolonomy U' (contourLeg y x π) := by
    intro y hy x hx π
    obtain ⟨σ, hσ⟩ := hlegs L n _ _ y x π
    refine pathHolonomy_congr fun b hb => h b ?_
    have hb' : b ∈ PeriodicLattice.orderedContour y x σ := by
      rw [← hσ]
      exact hb
    exact (hP.1 y hy x hx).1 _ ⟨σ, rfl⟩ b hb'
  have hcontour : ∀ x ∈ PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k j) c.source,
      ∀ π : Equiv.Perm (Fin 4), contourHolonomy U c x π = contourHolonomy U' c x π := by
    intro x hx π
    simp only [contourHolonomy]
    rw [hleg c.source (Or.inl rfl) x hx π, hleg c.target (Or.inr rfl) _ (htarget x hx) π,
      pathHolonomy_congr fun b hb => h b (hP.2 x hx b hb)]
  have hmean : contourMean U c = contourMean U' c := by
    simp only [contourMean]
    congr 1
    exact finsum_mem_congr rfl fun x hx => Finset.sum_congr rfl fun π _ => hcontour x hx π
  have hradius : meanRadius U c = meanRadius U' c := by
    simp only [meanRadius, hmean]
  refine ⟨hmean, hradius, ?_⟩
  simp only [normalizedMean, hradius, hmean]
end YangMills.Construction.RunningCouplingSlope
end
