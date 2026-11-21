import YangMills.Construction.RunningCouplingSlope.DerivativeOfThePlainAverageAtOneProof
import YangMills.Construction.RunningCouplingSlope.LinearAverageIsTheMeanOverTheContours
import Mathlib
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
noncomputable section
namespace YangMills.Construction.RunningCouplingSlope.SmoothingAsContourMean
open Tower
section AxisOrders
variable {E : Type*} [AddCommGroup E] [Module ℝ E]
abbrev permutedAxes (π : Equiv.Perm (Fin 4)) : List (Fin 4) := (List.finRange 4).map π
abbrev axesInOrder {S : Finset (Fin 4)} (σ : Fin S.card ≃ S) : List (Fin 4) :=
  (List.finRange S.card).map fun i => ((σ i : S) : Fin 4)
end AxisOrders
section LatticePaths
variable {L m : ℕ} {j : ℤ}
theorem sum_perm_bondFormSumAlong (A : PeriodicLattice.Bond L m j → Matrices.ComplexMatrix2)
    {i : ℤ} (y : PeriodicLattice.Site L m i) (x : PeriodicLattice.Site L m j) :
    ∑ π : Equiv.Perm (Fin 4), PeriodicLattice.bondFormSumAlong A
        (PeriodicLattice.stepsThroughAxes (PeriodicLattice.blockOffset y x) (y.toSublattice j)
          (permutedAxes π)) =
      (24 : ℂ) • PeriodicLattice.contourFormAverage A y x := by apply _root_.YangMills.Construction.RunningCouplingSlope.NormalizedMeanAtOneProof.sum_perm_bondFormSumAlong <;> assumption
end LatticePaths
theorem linearSmoothingContourFormula_of_crossings
    (hb : PeriodicLattice.CrossingsAndBareBlocks.Statement) :
    LinearSmoothingContourFormula := by
  intro L hL n k j hn hj A c hc
  have hLpos : 0 < L := by have := hL.2; omega
  have hcard := ((hb L hL n k hn).1 j hj c hc).1
  have hfin : (PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k j) c.source :
      Set (Vertex L n k j)).Finite := by
    have h4 : Nat.card ↥(PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k j) c.source :
        Set (Vertex L n k j)) ≠ 0 := by rw [hcard]; positivity
    have := Nat.finite_of_card_ne_zero h4
    exact Set.toFinite _
  have hQ : ∀ x, ∑ π : Equiv.Perm (Fin 4),
        (PeriodicLattice.bondFormSumAlong A (contourLeg c.source x π) +
        PeriodicLattice.bondFormSumAlong A (PeriodicLattice.crossingPath c x) -
        PeriodicLattice.bondFormSumAlong A
          (contourLeg c.target (PeriodicLattice.shiftAcross c x) π)) =
      (24 : ℂ) • (PeriodicLattice.contourFormAverage A c.source x +
        PeriodicLattice.bondFormSumAlong A (PeriodicLattice.crossingPath c x) -
        PeriodicLattice.contourFormAverage A c.target (PeriodicLattice.shiftAcross c x)) := by
    intro x
    have h1 := sum_perm_bondFormSumAlong A c.source x
    have h2 := sum_perm_bondFormSumAlong A c.target (PeriodicLattice.shiftAcross c x)
    rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, smul_sub, smul_add]
    simp only [contourLeg]
    rw [h1, h2]
    congr 2
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_perm]
    simp only [Fintype.card_fin]
    rw [← Nat.cast_smul_eq_nsmul ℂ]
    norm_num [Nat.factorial]
  have e1 : Tower.linearSmoothing L n k j A c = PeriodicLattice.inverseFourthPowerWeight L •
      ∑ᶠ x ∈ PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k j) c.source,
        (PeriodicLattice.contourFormAverage A c.source x +
        PeriodicLattice.bondFormSumAlong A (PeriodicLattice.crossingPath c x) -
        PeriodicLattice.contourFormAverage A c.target (PeriodicLattice.shiftAcross c x)) := rfl
  rw [e1, finsum_mem_eq_finite_toFinset_sum _ hfin, finsum_mem_eq_finite_toFinset_sum _ hfin]
  simp only [hQ, ← Finset.smul_sum, smul_smul]
  congr 1
  ring
end YangMills.Construction.RunningCouplingSlope.SmoothingAsContourMean
end
