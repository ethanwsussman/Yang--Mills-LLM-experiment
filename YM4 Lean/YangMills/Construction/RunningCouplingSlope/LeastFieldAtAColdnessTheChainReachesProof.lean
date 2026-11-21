import YangMills.Construction.RunningCouplingSlope.DensityOfTheStepIsAnalyticAtParametersProof
import YangMills.Construction.RunningCouplingSlope.LeastFieldAtAColdnessTheChainReaches
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open BlockAverages ColdStepAtMirrorFrames
namespace RunningCouplingSlope
variable {F : BlockFrame}
private theorem isSmallCurvature_of_isCold (hodd : Odd F.blockSide) (hs : ∀ i, 0 < F.extent i) {j : ℕ}
    (hj : j ≤ F.top) {s : ℝ} {X : F.GaugeField j}
    (h : IsCold (finiteCells F) j s X) : IsSmallCurvature s X := by apply _root_.YangMills.SharedProofs.p16091 <;> assumption
private theorem minimizingCoordinates_spec (hUnique : MinimizingChartUnique) (hL : Odd F.blockSide)
    (hs : ∀ i, 2 ≤ F.extent i)
    {a ρ N0 s : ℝ} {V : F.GaugeField F.top} (hρ : ρ ≤ 1) (h : HasColdMinimizer a ρ N0 s (finiteCells F) V) :
    IsMinimizingChart a (finiteCells F) V ρ (minimizingCoordinates a (finiteCells F) V ρ) ∧
      ∀ b ∈ chordBonds (finiteCells F), ‖minimizingCoordinates a (finiteCells F) V ρ b.1 b.2‖ ≤ N0 * s := by apply _root_.YangMills.SharedProofs.p45920 <;> assumption
theorem minimizerAtReachableColdness_holds (hUnique : MinimizingChartUnique) :
    MinimizerAtReachableColdness := by
  intro a L c _ hL hL40 hc F s V hF hs hV
  obtain ⟨⟨-, hρ1, -⟩, -⟩ := hc.classical
  obtain ⟨-, -, -, hσA, -, hNpos, -⟩ := hc.positivity
  have hodd : Odd F.blockSide := by
    rw [hF.1]
    exact hL
  obtain ⟨n, hn, hside⟩ := hF.2
  have hs2 : ∀ i, 2 ≤ F.extent i := fun i => by
    rw [hside]
    omega
  have hs1 : ∀ i, 0 < F.extent i := fun i => by
    rw [hside]
    omega
  have hs0 := hs.pos
  have hcla := hc.estimates F s V hF hs0 hs.le_bound hV
  obtain ⟨hleast, hsmall0⟩ := minimizingCoordinates_spec hUnique hodd hs2 hρ1 hcla.minimizer
  have hone := (hUnique F a c.ρA (c.N 0) s V _ hodd hs2 hρ1 hcla.minimizer hleast).2
  have hcold : IsSmallCurvature (s / 8) (torusMinimizingField a c.ρA V) :=
    isSmallCurvature_of_isCold hodd hs1 (Nat.le_succ _) hone
  have hframe : ∀ b : F.Site F.depth × Fin 4,
      stepFrame true a c.ρA 0 b V = minimizingBondCoordinate a c.ρA (finiteCells F) b V :=
    fun b => by simp [stepFrame]
  have hfun : (fun x i => stepFrame true a c.ρA 0 (x, i) V) = minimizingCoordinates a (finiteCells F) V c.ρA := by
    funext x i
    simp [stepFrame, minimizingBondCoordinate]
  have hsize : ∀ b ∈ chordBonds (finiteCells F), ‖stepFrame true a c.ρA 0 b V‖ ≤ c.N 0 * s := fun b hb => by
    rw [hframe]
    exact hsmall0 b hb
  have hLpos : (0 : ℝ) < L := by
    have : 0 < L := lt_of_lt_of_le (by positivity) hL40
    exact_mod_cast this
  have hN0 := hNpos 0
  have hsm := hs.small_vs_block
  have hε : 2 ^ 10 * ((L : ℝ) * (c.N 0 * s)) ≤ 9 / 8 := by
    have : 0 ≤ (L : ℝ) * s := by positivity
    nlinarith
  refine ⟨hleast, hsize, hcold, ⟨fun b hb => (hsize b hb).trans ?_, fun p hp => ?_⟩, fun b hb => ?_⟩
  · rw [le_div_iff₀ (by positivity)]
    nlinarith
  · rw [hfun]
    have := hs.le_bound
    exact (hcold p hp).trans_le (by linarith)
  · have e : stepFrame true a c.ρA 0 b = minimizingBondCoordinate a c.ρA (finiteCells F) b := by
      funext V'
      simp [stepFrame]
    rw [e]
    refine ⟨(hcla.coordinates b hb).1, fun k e' X hk hX => ?_⟩
    have h := (hcla.coordinates b hb).2 k e' X hk hX
    rw [neg_mul] at h
    exact h
end RunningCouplingSlope
end YangMills.Construction
end
