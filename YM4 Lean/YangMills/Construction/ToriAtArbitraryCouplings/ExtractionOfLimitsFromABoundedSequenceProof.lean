import YangMills.Construction.ToriAtArbitraryCouplings.CentredMomentsOfALimitOfABoundedSequence
import YangMills.Construction.ToriAtArbitraryCouplings.DeterminationOfALimitOfABoundedSequence
import YangMills.Construction.ToriAtArbitraryCouplings.EquicontinuityAlongABoundedSequence
import YangMills.Construction.ToriAtArbitraryCouplings.ExtractionOfASetOfIndices
import YangMills.Construction.ToriAtArbitraryCouplings.ExtractionOfLimitsFromABoundedSequence
import YangMills.Construction.ToriAtArbitraryCouplings.LimitOfABoundedSequenceIsASymmetricFamily
import YangMills.Construction.ToriAtArbitraryCouplings.SystemsOfSourceEnergiesGiveABoundedSequence
import Mathlib
set_option autoImplicit false
namespace YangMills.Construction.ToriAtArbitraryCouplings.LimitExtraction
theorem combined (hEqui : EquicontinuityAlongSequence.Holds)
    (hExtract : SubsequenceExtraction.Holds)
    (hSymm : SymmetricLimitFamily.Statement)
    (hMoments : CenteredMomentsOfLimit.Statement)
    (hDet : LimitDetermination.Holds)
    (hEnergies : LocalizedEnergySystemsBound.Holds) : Combined := by
  refine ⟨?_, hEnergies⟩
  intro s hs m' K β C h
  refine ⟨hExtract s hs m' K β C h, hEqui s hs m' K β C h, ?_⟩
  intro J hJ S hS
  obtain ⟨F, rfl, hFSymm, hFBound, hFEqui⟩ := hSymm s hs m' K β C h J hJ S hS
  exact ⟨F, rfl, hFSymm, hFBound, hFEqui, hMoments s hs m' K β C h J hJ F hS hFSymm,
    hDet s hs m' K β C h J hJ F hS hFSymm hFBound⟩
end YangMills.Construction.ToriAtArbitraryCouplings.LimitExtraction
