import YangMills.Construction.RunningCouplingSlope.ChainCloseToReferenceChain
import YangMills.Construction.RunningCouplingSlope.CoefficientsOfTheChainAdd
import YangMills.Construction.RunningCouplingSlope.OneLoopCoefficientsHaveTheSlope
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.RunningCouplingSlope
theorem stepSlopeCoefficients_haveAverageSlope (hAdd : ChainSlopeCoefficientsAdd)
    (hNear : ChainNearNormaliserSum) (hLaw : OneLoopLaw.NormaliserLaw.NormaliserStiffnessLaw) :
    SlopeCoefficient.StepSlopeCoefficientsHaveAverageSlope := by
  intro a L hT
  have ha : 0 < a := by
    obtain ⟨T, hD, rfl, -⟩ := hT
    linarith [hD.a_ge]
  have hL : Conventions.IsAdmissibleBlockingFactor L := by
    obtain ⟨T, hD, -, rfl⟩ := hT
    exact ⟨hD.L_odd, le_trans (by norm_num) hD.L_ge⟩
  have hL0 : 0 < L := by have := hL.2; omega
  obtain ⟨b, hb, hsum⟩ := hAdd a L hT
  obtain ⟨C, hC0, hC⟩ := hNear a ha L hL0 hL
  obtain ⟨hdev, -, -⟩ := hLaw L hL0 hL
  have hcoef : ParameterChoice.oneLoopCoefficient L = CouplingFlow.slopeConst L := by
    simp only [ParameterChoice.oneLoopCoefficient, ParameterChoice.colorNumber,
      CouplingFlow.slopeConst]
    push_cast
    ring
  set B := OneLoopLaw.NormaliserLaw.deviationBound L with hB
  have hmain : ∀ k : ℕ,
      |∑ l ∈ Finset.range k, b l - (k : ℝ) * CouplingFlow.slopeConst L| ≤ C + B := by
    intro k
    have e1 := hC k 1 _ one_pos le_rfl (hsum k 1 one_pos le_rfl)
    have e2 := hdev k
    rw [hcoef] at e2
    calc |∑ l ∈ Finset.range k, b l - (k : ℝ) * CouplingFlow.slopeConst L| =
        |(∑ l ∈ Finset.range k, b l -
            ∑ m ∈ Finset.range k, OneLoopLaw.NormaliserLaw.normaliserStiffness hL0 m) +
          (∑ m ∈ Finset.range k, OneLoopLaw.NormaliserLaw.normaliserStiffness hL0 m -
            (k : ℝ) * CouplingFlow.slopeConst L)| := by congr 1; ring
      _ ≤ _ := abs_add_le _ _
      _ ≤ C + B := add_le_add e1 e2
  have hCB : 0 ≤ C + B := (abs_nonneg _).trans (hmain 0)
  refine ⟨b, C + B, hCB, hb, hmain, fun i m him => ?_⟩
  have hI : ∑ l ∈ Finset.Ico i m, b l =
      ∑ l ∈ Finset.range m, b l - ∑ l ∈ Finset.range i, b l := by
    rw [Finset.sum_Ico_eq_sub _ him]
  rw [hI]
  have e1 := abs_le.mp (hmain i)
  have e2 := abs_le.mp (hmain m)
  rw [abs_le]
  constructor <;> nlinarith [e1.1, e1.2, e2.1, e2.2]
end YangMills.Construction.RunningCouplingSlope
end
