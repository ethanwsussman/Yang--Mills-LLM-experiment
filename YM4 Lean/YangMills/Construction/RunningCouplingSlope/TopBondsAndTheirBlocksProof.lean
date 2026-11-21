import YangMills.Construction.RunningCouplingSlope.CellsOfNeighbouringFineSitesProof
import YangMills.Construction.RunningCouplingSlope.TopBondsAndTheirBlocks
import YangMills.Construction.Towers.BlocksStraightPathsContoursAndPivotBondsOfATower
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.RunningCouplingSlope
open Tower TorusMetric
private theorem torusEuclidNorm_le_two_mul {S : ℝ} (x : TorusMetric.Torus4 S) (c : ℝ) (hc : 0 ≤ c)
    (h : ∀ μ, ‖x μ‖ ≤ c) : TorusMetric.torusEuclidNorm x ≤ 2 * c := by apply _root_.YangMills.SharedProofs.p16188 <;> assumption
private theorem meshSize_levelDepth_self (L k : ℕ) :
    PeriodicLattice.meshSize L (PeriodicLattice.levelDepth k k) = 1 := by
  simp [PeriodicLattice.meshSize, PeriodicLattice.levelDepth]
theorem topEdgesAndCubes_holds
    (hZ : Tower.BlockPathContourPivotStatement) :
    TopEdgesAndCubes := by
  intro L hL n k hn hk
  refine ⟨fun y => ?_, fun c => ?_, fun y y' p hy hy' => ?_⟩
  · unfold cellDist
    rw [sub_self, AmbientPoints.torusEuclidNorm_eq_sqrt]
    simp
  · unfold cellDist
    obtain ⟨μ, h⟩ := c.isNeighbour
    have hstep : ∀ ν, ‖((PeriodicLattice.unitStep L n _ μ : Tower.Vertex L n k k) :
        PeriodicLattice.FourTorus L n) ν‖ ≤ 1 := by
      intro ν
      by_cases e : ν = μ
      · subst e
        simp only [PeriodicLattice.unitStep, PeriodicLattice.pointOnAxis, Pi.single_eq_same]
        refine (TorusMetric.addCircle_norm_coe_le_abs _).trans ?_
        rw [meshSize_levelDepth_self, abs_one]
      · simp [PeriodicLattice.unitStep, PeriodicLattice.pointOnAxis, Pi.single_eq_of_ne e]
    have hdiff : ∀ ν, ‖((c.source : PeriodicLattice.FourTorus L n) - c.target) ν‖ ≤ 1 := by
      intro ν
      rcases h with h | h
      · have e : (c.source : PeriodicLattice.FourTorus L n) - c.target =
            -((PeriodicLattice.unitStep L n _ μ : Tower.Vertex L n k k) :
              PeriodicLattice.FourTorus L n) := by
          rw [← h]
          simp
        rw [e, Pi.neg_apply, norm_neg]
        exact hstep ν
      · have e : (c.source : PeriodicLattice.FourTorus L n) - c.target =
            ((PeriodicLattice.unitStep L n _ μ : Tower.Vertex L n k k) :
              PeriodicLattice.FourTorus L n) := by
          have h' := congrArg
            (fun x : Tower.Vertex L n k k => -(x : PeriodicLattice.FourTorus L n)) h
          simpa using h'
        rw [e]
        exact hstep ν
    have := torusEuclidNorm_le_two_mul (S := PeriodicLattice.torusSide L n) _ 1 zero_le_one hdiff
    linarith
  · have H := ((hZ L hL k k k hk le_rfl le_rfl).1 n hn).1
    exact (H.existsUnique_mem ⟨p, H.subset_sublattice y hy⟩).unique hy hy'
end YangMills.Construction.RunningCouplingSlope
end
