import YangMills.Construction.RunningCouplingSlope.IteratesOfThePlainAverageProof
import YangMills.Construction.RunningCouplingSlope.PlainIteratesAreNearOne
import Mathlib
set_option autoImplicit false
open Set
open scoped ENNReal Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction.RunningCouplingSlope.MeanIteratesNearIdentity
open Matrices
open Tower
open Tower.IteratedSmallFieldMeans (smallFormBall)
variable {L n k j : ℕ}
private theorem norm_expTwist_sub_one_le (hexp : ComplexMatrix2.ExpLogEstimates)
    (A : Edge L n k j → ComplexMatrix2) (hA : A ∈ complexEdgeForms L n k j) (a : ℝ) (ha : a ≤ 1)
    (hbound : ∀ e, ‖A e‖ ≤ a) (e : Edge L n k j) :
    ‖PeriodicLattice.expTwist A (fun _ => 1) e - 1‖ ≤ 2 * a := by apply _root_.YangMills.Construction.RunningCouplingSlope.PlainMeanIterates.norm_expTwist_sub_one_le <;> assumption
theorem claim_holds (hlog : MeanIterateLogarithms)
    (hexp : ComplexMatrix2.ExpLogEstimates) : MeanIteratesNearIdentity.Claim := by
  intro L hL r hr
  obtain ⟨ρ₁, hρ₁, H₁⟩ := hlog L hL
  set ρ : ℝ := min ρ₁ (min (r / 40) (1 / 20)) with hρ
  have hρ0 : 0 < ρ := lt_min hρ₁ (lt_min (by positivity) (by norm_num))
  have hρa : ρ ≤ ρ₁ := min_le_left _ _
  have hρd : ρ ≤ r / 40 := (min_le_right _ _).trans (min_le_left _ _)
  have hρe : ρ ≤ 1 / 20 := (min_le_right _ _).trans (min_le_right _ _)
  have hLpos : 0 < L := by have := hL.2; omega
  refine ⟨ρ, hρ0, fun n k hn hk v hv j hj => ?_⟩
  have hv₁ : v ∈ smallFormBall L n k ρ₁ := ⟨hv.1, hv.2.trans (ENNReal.ofReal_le_ofReal hρa)⟩
  have hmesh : meshAt L k j ≤ 1 := by
    have h1 : (1 : ℝ) ≤ L := by exact_mod_cast hLpos
    exact zpow_le_one_of_nonpos₀ h1 (by omega)
  have hmesh0 : 0 ≤ meshAt L k j := by
    have : (0 : ℝ) ≤ L := by positivity
    exact zpow_nonneg this _
  obtain ⟨h₁, h₂, -⟩ := H₁ n k hn hk v hv₁
  refine ⟨(h₂ j hj).1, fun e => ?_⟩
  obtain ⟨A, hA, he, hs⟩ := h₁ j hj.le
  have ht : (maxOperatorNorm v).toReal ≤ ρ := ENNReal.toReal_le_of_le_ofReal hρ0.le hv.2
  have ht0 : 0 ≤ (maxOperatorNorm v).toReal := ENNReal.toReal_nonneg
  have hpos : 0 ≤ 10 * meshAt L k j * (maxOperatorNorm v).toReal := by positivity
  have hbound : ∀ e, ‖A e‖ ≤ 10 * meshAt L k j * (maxOperatorNorm v).toReal := by
    intro e
    have h1 : ENNReal.ofReal ‖A e‖ ≤ maxOperatorNorm A :=
      le_iSup (fun e => ENNReal.ofReal (ComplexMatrix2.operatorNorm (A e))) e
    exact (ENNReal.ofReal_le_ofReal_iff hpos).mp (h1.trans hs)
  have h4 : meshAt L k j * (maxOperatorNorm v).toReal ≤ ρ := by nlinarith
  have ha : 10 * meshAt L k j * (maxOperatorNorm v).toReal ≤ 1 := by nlinarith
  rw [he]
  have h3 := norm_expTwist_sub_one_le hexp A hA _ ha hbound e
  have h5 : ComplexMatrix2.operatorNorm (PeriodicLattice.expTwist A (fun _ => 1) e - 1) =
      ‖PeriodicLattice.expTwist A (fun _ => 1) e - 1‖ := rfl
  rw [h5]
  nlinarith
end YangMills.Construction.RunningCouplingSlope.MeanIteratesNearIdentity
end
