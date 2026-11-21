import YangMills.Construction.SystemsWithFiveBounds.ListOfTheReconstructionOfALimitProof
import YangMills.Construction.TotalDensitiesGiveASystem.SpaceOfAContinuousFunctionalIsSeparable
import Mathlib
set_option autoImplicit false
noncomputable section
open Filter MeasureTheory Topology
open scoped ComplexOrder ENNReal InnerProductSpace NNReal
namespace YangMills.Construction.TotalDensitiesGiveASystem
namespace PhysicalSpaceSeparability
section SeparabilityOfPhysicalSpace
open TestFunctions TorusMetric
open SeparatedTuples ReflectionPositivity.TupleForm HilbertSpaceBasics
open ReflectionPositivity.Reconstruction (PhysicalSpace posClass posTupleVec)
open TimeAxis (timeReflection upperHalfSpace)
open InfiniteLattice (AmbientSpace)
private theorem separableSpace_physicalSpace {σ : TupleFunctional} (hc : σ.IsAdmissiblyContinuous)
    (hfam : CanonicalDecomposition.SeparatingTuplesProperties.Claim)
    (hS : ∀ f : RealValued, IsC1c f → c1NormR4 f ≤ sharpNormR4 1 f)
    (s : Conventions.StandingParameters) (h : IsPosSemidef (reflectionForm σ)) :
    TopologicalSpace.SeparableSpace (PhysicalSpace σ h) := by apply _root_.YangMills.SharedProofs.p25811 <;> assumption
end SeparabilityOfPhysicalSpace
end PhysicalSpaceSeparability
open PhysicalSpaceSeparability in
theorem physicalSpaceSeparable_holds
    (hbd : ReflectionPositivity.ApproximatingSequences.LimitsOnTuplesImplyBounded)
    (hfam : CanonicalDecomposition.SeparatingTuplesProperties.Claim) :
    PhysicalSpaceSeparable := fun σ h hc => by
  have hL : Conventions.IsAdmissibleBlockingFactor 13 := ⟨by decide, le_rfl⟩
  exact separableSpace_physicalSpace hc hfam (fun f hf => (hbd.2.1 1 le_rfl f hf).1) ⟨13, hL, 1, 1⟩ h
end YangMills.Construction.TotalDensitiesGiveASystem
end
