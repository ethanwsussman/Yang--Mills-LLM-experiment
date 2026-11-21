import YangMills.Construction.EuclideanFunctionals.CombinationsOfTuplesComplexComponentsAndConvergenceInC1
import YangMills.Construction.LimitsAlongPeriodicGibbsStates.ReflectionsInHyperplanesAndTheSixteenFamiliesOfMirrors
import Mathlib
set_option autoImplicit false
open scoped ComplexOrder
noncomputable section
namespace YangMills.Construction.FirstPassageSeqs
open EuclideanFunctionals
def CenteredIsEuclidInvariant (T : ConnFamily) : Prop :=
  ∀ w ∈ hyperoctahedral, ∀ (v : R4) (G : FreeSep),
    centeredFnFree T ((EuclidMotion.transl v * w).actFree G) =
      centeredFnFree T G
def CenteredIsReflectionPositive (T : ConnFamily) : Prop :=
  ∀ (u : R4) (hu : TwoPoints.euclidNorm u = 1),
    (u ∈ TwoPoints.normalRepresentatives ∨ -u ∈ TwoPoints.normalRepresentatives) →
    ∀ G ∈ finCombIn {x : R4 | 0 < TwoPoints.euclidDot u x},
      MulDefined (PeriodicGibbsLimits.reflectedConj u hu 0 G) G ∧
        0 ≤ centeredFnFree T
          (freeMul (PeriodicGibbsLimits.reflectedConj u hu 0 G) G)
end YangMills.Construction.FirstPassageSeqs
end
