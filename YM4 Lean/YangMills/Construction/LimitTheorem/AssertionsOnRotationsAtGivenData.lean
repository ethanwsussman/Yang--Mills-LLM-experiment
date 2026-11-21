import YangMills.Construction.LimitTheorem.AssertionsAtGivenConstants
import YangMills.Construction.LimitTheorem.ConstantsOfTheTheoremBehindThereAre
import YangMills.Construction.LimitTheorem.ComponentFieldData
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.LimitTheorem
open SeparatedTuples
open ConfigSpace (FlatSequence schwartzFlatOffDiagonal bracketNorm toSchwartzFn)
variable (C : ExistentialConstants)
structure OSConditionsAt (T : FlatSequence) : Prop where
  growth : SatisfiesGrowth T C.kE C.cE C.CE C.κ
  euclid_invariant : ConfigSpace.IsEuclidInvariant T
  reflection_positive : ConfigSpace.IsOSPositive T
  perm_symmetric : ConfigSpace.IsPermSymmetric T
  cluster : ConfigSpace.HasClusterProperty T
  reflection_real : ConfigSpace.IsReflectionReal T
structure SatisfiesAxiomListsAt (T : FlatSequence) : Prop where
  osConditions : OSConditionsAt C T
  growth : ∀ (m : ℕ) (f : schwartzFlatOffDiagonal (m + 1)),
    ‖T.atSucc m f‖ ≤
      C.cE * Real.exp C.CE * ((m + 1).factorial : ℝ) ^ (C.κ + 1) *
        bracketNorm (C.kE * (m + 1)) (toSchwartzFn f)
def ComponentOSAt (F : TupleFunctional) : Prop :=
  (∀ T, HasSchwingerSequence F T → SatisfiesAxiomListsAt C T) ∧ ComponentFieldData F
structure RotationAssertionsAt (S : CumulantFamily) : Prop where
  o4Invariant : IsO4Invariant S
  permute : ∀ D : DecompositionData, D.IsCanonical (centredOf S) →
    NonLatticeRotationsPermute D
  componentsO4 : ∀ D : DecompositionData, D.IsCanonical (centredOf S) →
    ∀ ξ, IsO4InvariantFunctional (D.comp ξ)
  jointSpectrum : ∀ D : DecompositionData, D.IsCanonical (centredOf S) →
    ∀ ξ, JointSpectrumInForwardCone (D.comp ξ)
  spatialRotations : ∀ D : DecompositionData,
    D.IsCanonical (centredOf S) →
    ∀ ξ, HasSpatialRotationRep (D.comp ξ)
  componentOS : ∀ D : DecompositionData, D.IsCanonical (centredOf S) →
    ∀ ξ, ComponentOSAt C (D.comp ξ)
end YangMills.Construction.LimitTheorem
end
