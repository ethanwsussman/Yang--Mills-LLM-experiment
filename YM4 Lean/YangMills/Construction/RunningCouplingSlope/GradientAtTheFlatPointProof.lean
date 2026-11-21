import YangMills.Construction.Towers.TheActionOnATowerProof
import YangMills.Construction.RunningCouplingSlope.FlatPointIsLeastProof
import YangMills.Construction.RunningCouplingSlope.GradientAtTheFlatPoint
import YangMills.Construction.RunningCouplingSlope.TheGaugeShiftReadsNearCellsProof
import YangMills.Construction.Towers.SecondDifferentialAtACriticalPointProof
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.RunningCouplingSlope
open Tower
namespace UnitPointGradient
private theorem traceDefect_nonneg {g : Matrices.ComplexMatrix2}
    (hg : g ∈ Matrices.ComplexMatrix2.specialUnitary) : 0 ≤ traceDefect g := by apply _root_.YangMills.SharedProofs.p31272 <;> assumption
private theorem traceDefect_one : traceDefect 1 = 0 := by
  simp [traceDefect, Matrices.ComplexMatrix2.halfTrace, Matrices.ComplexMatrix2.fullTrace]
private theorem re_cpow_half_nonneg (w : ℂ) : 0 ≤ (w ^ (1 / 2 : ℂ)).re := by apply _root_.YangMills.SharedProofs.p69172 <;> assumption
private theorem matExp_I_smul_mem {ξ : Matrices.ComplexMatrix2}
    (hξ : ξ ∈ Matrices.ComplexMatrix2.hermitianTraceless) :
    Matrices.ComplexMatrix2.matExp (Complex.I • ξ) ∈ Matrices.ComplexMatrix2.specialUnitary := by apply _root_.YangMills.Construction.Matrices.ComplexMatrix2.ExpSurjective.matExp_I_smul_mem_specialUnitary <;> assumption
variable {L n k : ℕ}
private theorem plaquetteAction_nonneg {U : Edge L n k 0 → Matrices.ComplexMatrix2}
    (hU : U ∈ fieldSpace L n k 0) : 0 ≤ plaquetteAction L n k U := by apply _root_.YangMills.SharedProofs.p50075 <;> assumption
private theorem pathHolonomy_one {m : ℤ} (γ : List (PeriodicLattice.Bond L n m)) :
    PeriodicLattice.pathHolonomy (fun _ => (1 : Matrices.ComplexMatrix2)) γ = 1 := by apply _root_.YangMills.SharedProofs.p14112 <;> assumption
private theorem plaquetteAction_one : plaquetteAction L n k (fun _ => 1) = 0 := by apply _root_.YangMills.Construction.Tower.ActionFacts.totalAction_trivial <;> assumption
private theorem edgeFormPairing_zero {m : ℕ} (B : Edge L n k m → Matrices.ComplexMatrix2) :
    edgeFormPairing (0 : Edge L n k m → Matrices.ComplexMatrix2) B = 0 := by apply _root_.YangMills.Construction.Tower.CriticalSecondDeriv.edgeFormPairing_zero <;> assumption
private theorem expMove_zero :
    expMove (0 : LevelForms L n k) (unitPoint L n k) = unitPoint L n k := by apply _root_.YangMills.SharedProofs.p5970 <;> assumption
end UnitPointGradient
open UnitPointGradient in
theorem gradientAtUnitPoint_of_smoothingNearTrivialField (hV : SmoothingNearTrivialField) :
    GradientAtUnitPoint := by
  intro a ha L hL k n hk hn ξ
  have h₂ : levelPairing (formValues (0 : LevelForms L n k)) (formValues ξ) = 0 := by
    unfold levelPairing formValues
    have h₃ : ∀ i : Fin k, edgeFormPairing (((0 : LevelForms L n k).2 i : edgeFormSpace L n k (i + 1)) :
        Edge L n k (i + 1) → Matrices.ComplexMatrix2)
          (ξ.2 i : Edge L n k (i + 1) → Matrices.ComplexMatrix2) = 0 :=
      fun i => edgeFormPairing_zero _
    have h₄ : edgeFormPairing (((0 : LevelForms L n k).1 : edgeFormSpace L n k 0) :
        Edge L n k 0 → Matrices.ComplexMatrix2)
          (ξ.1 : Edge L n k 0 → Matrices.ComplexMatrix2) = 0 := edgeFormPairing_zero _
    simp only [h₃, h₄, Complex.zero_re, Finset.sum_const_zero, add_zero]
  rw [h₂]
  have h0 : chainAction a (unitPoint L n k) = 0 := by
    simp only [chainAction]
    have h1 : plaquetteAction L n k (unitPoint L n k).fine = 0 := plaquetteAction_one
    rw [h1]
    simp [unitPoint, traceDefect_one]
  have hconf : (fun _ : Edge L n k 0 => (1 : Matrices.ComplexMatrix2)) ∈ fieldSpace L n k 0 :=
    ⟨fun _ _ => one_mem _, fun _ _ => by simp⟩
  have hmin : IsLocalMin (fun t : ℝ => chainAction a (expMove (t • ξ) (unitPoint L n k))) 0 := by
    refine Filter.Eventually.of_forall fun t => ?_
    show chainAction a (expMove ((0 : ℝ) • ξ) (unitPoint L n k)) ≤ _
    rw [zero_smul, expMove_zero, h0]
    have hb : (expMove (t • ξ) (unitPoint L n k)).fine ∈ fieldSpace L n k 0 :=
      (hV L n k hL hn hk).2 0 (Nat.zero_le k) _ (t • ξ).1.2 _ hconf
    refine add_nonneg (plaquetteAction_nonneg hb) (mul_nonneg ha.le (Finset.sum_nonneg fun i _ => ?_))
    refine finsum_nonneg fun c => mul_nonneg (re_cpow_half_nonneg _) (traceDefect_nonneg ?_)
    have hν : ((t • ξ).2 i : Edge L n k (i + 1) → Matrices.ComplexMatrix2) c.1 ∈
        Matrices.ComplexMatrix2.hermitianTraceless := ((t • ξ).2 i).2.1 c.1 c.2
    show Matrices.ComplexMatrix2.matExp
        (Complex.I • ((t • ξ).2 i : Edge L n k (i + 1) → Matrices.ComplexMatrix2) c.1) * 1 ∈
          Matrices.ComplexMatrix2.specialUnitary
    rw [mul_one]
    exact matExp_I_smul_mem hν
  exact hmin.deriv_eq_zero.symm
end YangMills.Construction.RunningCouplingSlope
end
