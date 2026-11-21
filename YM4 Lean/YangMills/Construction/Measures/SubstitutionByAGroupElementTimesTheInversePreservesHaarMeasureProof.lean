import YangMills.Construction.Haar.NormalizedHaarMeasure
import YangMills.Construction.Measures.SubstitutionByAGroupElementTimesTheInversePreservesHaarMeasure
import Mathlib
set_option autoImplicit false
open MeasureTheory
namespace YangMills.Construction.Measures
theorem haarMapMulInvEq_of_normalizedHaarFacts (hFacts : Haar.NormalizedHaarFacts) :
    HaarMapMulInvEq := by
  intro g
  have hSU : Haar.NormalizedHaarSpecialUnitary := hFacts.2.2.2
  obtain ⟨⟨_, _, hMet⟩, hHaarEq⟩ := hSU
  have := hMet
  have hUniq : Haar.NormalizedHaarUniqueInvariant := hFacts.1
  obtain ⟨_, hIsHaar, _, hInv⟩ := hUniq Matrices.ComplexMatrix2.specialUnitary
  rw [hHaarEq] at hIsHaar hInv
  have hMulLeft := hIsHaar.2 g
  have hInvMeas : Measurable fun u : Matrices.ComplexMatrix2.specialUnitary => u⁻¹ :=
    continuous_inv.measurable
  have hMulMeas : Measurable fun u : Matrices.ComplexMatrix2.specialUnitary => g * u :=
    (continuous_const.mul continuous_id).measurable
  calc Matrices.ComplexMatrix2.haarProb.map
        (fun u : Matrices.ComplexMatrix2.specialUnitary => g * u⁻¹)
      = (Matrices.ComplexMatrix2.haarProb.map
          fun u : Matrices.ComplexMatrix2.specialUnitary => u⁻¹).map
          (fun u : Matrices.ComplexMatrix2.specialUnitary => g * u) :=
        (Measure.map_map hMulMeas hInvMeas).symm
    _ = Matrices.ComplexMatrix2.haarProb := by rw [hInv, hMulLeft]
end YangMills.Construction.Measures
