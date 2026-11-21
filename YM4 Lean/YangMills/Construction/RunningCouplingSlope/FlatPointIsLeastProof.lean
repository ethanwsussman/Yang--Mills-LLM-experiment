import YangMills.Construction.Towers.TheActionOnATowerProof
import YangMills.Construction.Lattice.AveragingMapIsABorelMapProof
import YangMills.Construction.RunningCouplingSlope.DerivativeOfThePlainAverageAtOne
import YangMills.Construction.RunningCouplingSlope.FlatPointIsLeast
import YangMills.Construction.Towers.TrivialConfigurationAtAStepProof
import Mathlib
set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
open scoped Quaternion
noncomputable section
namespace YangMills.Construction.RunningCouplingSlope
open Tower Matrices
namespace UnitMinimizer
private theorem re_fullTrace_le_two {W : ComplexMatrix2} (hW : W ∈ ComplexMatrix2.specialUnitary) :
    (ComplexMatrix2.fullTrace W).re ≤ 2 := by
  have hU : W ∈ Matrix.unitaryGroup (Fin 2) ℂ := (Matrix.mem_specialUnitaryGroup_iff.mp hW).1
  have h0 : ‖W 0 0‖ ≤ 1 := entry_norm_bound_of_unitary hU 0 0
  have h1 : ‖W 1 1‖ ≤ 1 := entry_norm_bound_of_unitary hU 1 1
  have r0 := Complex.re_le_norm (W 0 0)
  have r1 := Complex.re_le_norm (W 1 1)
  have e : ComplexMatrix2.fullTrace W = W 0 0 + W 1 1 := Matrix.trace_fin_two W
  rw [e, Complex.add_re]
  linarith
private theorem traceDefect_nonneg {g : ComplexMatrix2} (hg : g ∈ ComplexMatrix2.specialUnitary) :
    0 ≤ traceDefect g := by
  have := re_fullTrace_le_two hg
  simp only [traceDefect, ComplexMatrix2.halfTrace, Complex.mul_re]
  simp
  linarith
abbrev _root_.YangMills.SharedProofs.p31272 := @traceDefect_nonneg
private theorem traceDefect_one : traceDefect 1 = 0 := by
  simp [traceDefect, ComplexMatrix2.halfTrace, ComplexMatrix2.fullTrace]
private theorem re_sqrt_nonneg (w : ℂ) : 0 ≤ (w ^ (1 / 2 : ℂ)).re := by
  by_cases hw : w = 0
  · subst hw
    simp
  rw [Complex.cpow_def_of_ne_zero hw, Complex.exp_re]
  refine mul_nonneg (Real.exp_pos _).le (Real.cos_nonneg_of_neg_pi_div_two_le_of_le ?_ ?_)
  · have := Complex.neg_pi_lt_arg w
    simp [Complex.log_im, Complex.mul_im]
    linarith
  · have := Complex.arg_le_pi w
    simp [Complex.log_im, Complex.mul_im]
    linarith
abbrev _root_.YangMills.SharedProofs.p69172 := @re_sqrt_nonneg
variable {L n k : ℕ}
private theorem pathHolonomy_one {j : ℤ} (γ : List (PeriodicLattice.Bond L n j)) :
    PeriodicLattice.pathHolonomy (fun _ => (1 : ComplexMatrix2)) γ = 1 := by apply _root_.YangMills.SharedProofs.p14112 <;> assumption
private theorem pathHolonomy_mem {j : ℤ} {U : PeriodicLattice.Bond L n j → ComplexMatrix2}
    (hU : U ∈ PeriodicLattice.compactGaugeFields L n j) (γ : List (PeriodicLattice.Bond L n j)) :
    PeriodicLattice.pathHolonomy U γ ∈ ComplexMatrix2.specialUnitary := by apply _root_.YangMills.SharedProofs.p3102 <;> assumption
private theorem plaquetteAction_nonneg {U : Edge L n k 0 → ComplexMatrix2} (hU : U ∈ fieldSpace L n k 0) :
    0 ≤ plaquetteAction L n k U := by
  refine finsum_nonneg fun p => ?_
  have := re_fullTrace_le_two (pathHolonomy_mem hU p.boundaryBonds)
  simp only [PeriodicLattice.plaquetteCost, PeriodicLattice.plaquetteHolonomy]
  linarith
abbrev _root_.YangMills.SharedProofs.p50075 := @plaquetteAction_nonneg
private theorem plaquetteAction_one : plaquetteAction L n k (fun _ => 1) = 0 := by apply _root_.YangMills.Construction.Tower.ActionFacts.totalAction_trivial <;> assumption
private theorem levelField_unitPoint (hD : NormalizedMeanAtOne)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) :
    ∀ j, j ≤ k → levelField (unitPoint L n k) j = fun _ => 1 := by
  intro j
  induction j with
  | zero => intro _; rfl
  | succ j ih =>
    intro hj
    have hlt : j < k := hj
    rw [levelField, dif_pos hlt, ih hlt.le]
    funext b
    have hav : ∀ c : PositiveEdge L n k (j + 1),
        (unitPoint L n k).noise ⟨j, hlt⟩ c * normalizedMean (fun _ : Edge L n k j => (1 : ComplexMatrix2)) c.1 = 1 := by
      intro c
      have := (hD L hL n k j hn hlt 0 (Submodule.zero_mem _) c.1 c.2).2.2.1
      rw [this]
      simp [unitPoint]
    simp only [fieldOfPositiveValues, hav]
    split_ifs <;> simp
abbrev _root_.YangMills.SharedProofs.p64130 := @levelField_unitPoint
end UnitMinimizer
theorem UnitMinimizer.unitPointIsMinimizer_holds (hD : NormalizedMeanAtOne) :
    UnitPointIsMinimizer := by
  intro a ha L hL k n hk hn
  have hconf : ∀ j, (fun _ => (1 : ComplexMatrix2)) ∈ fieldSpace L n k j := fun j =>
    ⟨fun _ _ => one_mem _, fun _ _ => by simp⟩
  have hflat := UnitMinimizer.levelField_unitPoint (k := k) hD hL hn
  refine ⟨⟨hconf k, fun w μ => ?_⟩, ⟨⟨fun i c => one_mem _, fun j hj => ?_⟩, hflat k le_rfl, fun X' hX' _ => ?_⟩⟩
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [TorusFields.trivialField, SoftAverages.quaternionToMatrix]
  · rw [hflat j hj]
    exact hconf j
  · have h0 : chainAction a (unitPoint L n k) = 0 := by
      simp only [chainAction]
      have h1 : plaquetteAction L n k (unitPoint L n k).fine = 0 := UnitMinimizer.plaquetteAction_one
      rw [h1]
      simp [unitPoint, UnitMinimizer.traceDefect_one]
    rw [h0]
    have hb : X'.fine ∈ fieldSpace L n k 0 := hX'.2 0 (Nat.zero_le _)
    refine add_nonneg (UnitMinimizer.plaquetteAction_nonneg hb) (mul_nonneg ha.le (Finset.sum_nonneg fun i _ => ?_))
    exact finsum_nonneg fun c => mul_nonneg (UnitMinimizer.re_sqrt_nonneg _)
      (UnitMinimizer.traceDefect_nonneg (hX'.1 i c))
end YangMills.Construction.RunningCouplingSlope
end
