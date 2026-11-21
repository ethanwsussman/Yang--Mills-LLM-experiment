import YangMills.Construction.InfiniteLattice.FactsOfToriArraysAndPerturbedMeasures
import YangMills.Construction.InfiniteLattice.FinitenessOfATorusNormalisersAndExtendedMeasures
import Mathlib
set_option autoImplicit false
open MeasureTheory
namespace YangMills.Construction.InfiniteLattice
theorem finiteTorusPartitionsAndLifts_of_facts
    (facts : ToriArraysAndTiltedMeasuresFacts) :
    FiniteTorusPartitionsAndLifts := by
  intro β hβ Γ
  obtain ⟨hTori, hArrays, -, -⟩ := facts β hβ
  obtain ⟨hFaithful, hLift, -⟩ := hTori 1 one_pos Γ
  refine ⟨fun Q hQ => ?_, fun 𝔸 hD t => ?_⟩
  · have hΓ : Γ.periods.FiniteIndex := hFaithful.periods_finiteIndex
    have hQi : Q.FiniteIndex := AddSubgroup.finiteIndex_of_le hQ
    have hCosets : Finite (Q ⧸ Γ.periods.addSubgroupOf Q) :=
      AddSubgroup.finite_quotient_of_finiteIndex
    have hRel : Γ.periods.relIndex Q * Q.index = Γ.periods.index :=
      AddSubgroup.relIndex_mul_index hQ
    have hIndex : Γ.periods.index = Q.index * (Γ.periods.addSubgroupOf Q).index := by
      rw [mul_comm]
      exact hRel.symm
    exact ⟨hΓ, hQi, hFaithful.finite_quotientTorus, hCosets, hFaithful.finite_quotientLink,
      hFaithful.finite_quotientPlaquette, hIndex⟩
  · obtain ⟨-, hKernel, hDescent⟩ := hArrays 𝔸 t
    have hPeriodic := hDescent Γ hD
    have hContinuous : Continuous Γ.lift := hLift.isEmbedding_lift.continuous
    refine ⟨⟨hKernel.windowPartition_pos, hPeriodic.tiltedPartition_pos⟩,
      ⟨hContinuous, hLift.isEmbedding_lift.injective,
        hPeriodic.isProbabilityMeasure_tiltedLift, fun F hF => ?_⟩⟩
    have : SecondCountableTopology Matrices.ComplexMatrix2 :=
      inferInstanceAs (SecondCountableTopology (Fin 2 → Fin 2 → ℂ))
    have : SecondCountableTopology Matrices.ComplexMatrix2.specialUnitary :=
      TopologicalSpace.Subtype.secondCountableTopology _
    have hMeasurable : Measurable Γ.lift := hContinuous.measurable
    have hFc : Continuous F := hF.2.2
    have hFm : Measurable F := hFc.measurable
    unfold LocalObservableArray.tiltedLiftMeasure PeriodSublattice.integralOf
      PeriodSublattice.periodize
    exact integral_map hMeasurable.aemeasurable hFm.aestronglyMeasurable
end YangMills.Construction.InfiniteLattice
