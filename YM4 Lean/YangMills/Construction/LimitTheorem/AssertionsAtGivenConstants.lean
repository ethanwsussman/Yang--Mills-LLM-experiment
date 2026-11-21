import YangMills.Construction.Continuum.CanonicalDecompositionOfAFunctional
import YangMills.Construction.LimitTheorem.ConditionsAtGivenConstants
import Mathlib
set_option autoImplicit false
open Filter MeasureTheory Set
open scoped ComplexOrder InnerProductSpace NNReal Topology
noncomputable section
namespace YangMills.Construction.LimitTheorem
open TestSpaces (SepTupleOfCard)
open SeparatedTuples ReflectionPositivity.TupleForm
open HilbertSpaceBasics (IsPosSemidef)
open ReflectionPositivity.Reconstruction (PhysicalSpace posClass vacuum timeShift)
open ReflectionPositivity.PairMeasureOperators (pairHamiltonian pairMomentum energyMomentumPair
  groundStateProjection)
open SpectralTheory
open InfiniteLattice (AmbientSpace)
open TorusTransport (hyperoctahedral)
open ConfigSpace (FlatSequence schwartzFlatOffDiagonal bracketNorm toSchwartzFn)
variable (C : ConditionConstants)
structure LatticeSymmetries (S : CumulantFamily) : Prop where
  shift_invariant : ∀ v, IsFamilyInvariant S (shiftMotion v)
  hyperoctahedral_invariant : ∀ r, IsHyperoctahedralMotion r → r.shift = 0 → IsFamilyInvariant S r
  perm_symmetric : IsFamilySymmetric S
  centred_motion_invariant : ∀ r, IsHyperoctahedralMotion r → IsMotionInvariant (centredOf S) r
  centred_perm_invariant : (centredOf S).IsPermInvariant
def HasDistributions (S : CumulantFamily) : Prop :=
  TestSpaces.IsSepFunctional (evalOnMap (centredOf S)) ∧
    IsRegular (centredOf S) ∧ ∀ (n : ℕ) (hn : 2 ≤ n),
      ∃! u, IsDistribution (offDiagonal n) u ∧ AgreesOnTensors (S n hn) u
def HamiltonianGeMomentum (σ : TupleFunctional) (h : IsPosSemidef (reflectionForm σ))
    (i : Fin 3) : Prop :=
  ∃ Y, IsJointSpectrum Y (energyMomentumPair σ h i) ∧ Y ⊆ {y | |y 1| ≤ y 0}
def IsO4Invariant (S : CumulantFamily) : Prop :=
  ∀ R, IsFamilyInvariant S (ofOrthogonal R)
def transportedDecomposition (A : DecompositionData) (r : AmbientSpace → AmbientSpace) :
    DecompositionData where
  space := A.space
  law := A.law
  comp ξ := compInv (A.comp ξ) r
def PermutesComponents (A : DecompositionData) (r : AmbientSpace → AmbientSpace) : Prop :=
  ∃ h : A.space ≃ₜ A.space, A.law.map h = A.law ∧
    ∀ ξ, A.comp (h ξ) = compInv (A.comp ξ) r
def IsHyperoctahedral (R : Orthogonal.orthogonalGroupFour) : Prop :=
  IsHyperoctahedralMotion (ofOrthogonal R)
def hamiltonianKernel (σ : TupleFunctional) (h : IsPosSemidef (reflectionForm σ)) :
    Submodule ℂ (PhysicalSpace σ h) :=
  Submodule.span ℂ (opKernel (pairHamiltonian σ h))
def GroundStatesAsL2 (σ : TupleFunctional) (A : DecompositionData) : Prop :=
  ∀ h : IsPosSemidef (reflectionForm σ),
    ∃ U : hamiltonianKernel σ h ≃ₗᵢ[ℂ] Lp ℂ 2 A.law,
      (∀ F : PositiveSpan,
        ∃ hF : groundStateProjection σ h (posClass σ h F) ∈ hamiltonianKernel σ h,
          (U ⟨_, hF⟩ : A.space → ℂ) =ᵐ[A.law]
            fun ξ => (A.comp ξ).spanExtension F.1) ∧
      (∃ hΩ : vacuum σ h ∈ hamiltonianKernel σ h,
        (U ⟨_, hΩ⟩ : A.space → ℂ) =ᵐ[A.law] fun _ => 1) ∧
      ENat.card A.space = Cardinal.toENat (Module.rank ℂ (hamiltonianKernel σ h))
def TransportedCanonical (σ : TupleFunctional) (A : DecompositionData) : Prop :=
  ∀ r : AmbientSpace → AmbientSpace, IsEuclidIsometry r → σ.IsInvariant r →
    (transportedDecomposition A r).IsCanonical σ
def LatticeSymmetriesPermute (A : DecompositionData) : Prop :=
  (∀ v, PermutesComponents A (SeparatedTuples.translate v)) ∧ ∀ w : hyperoctahedral, PermutesComponents A w.1
def NonLatticeRotationsPermute (A : DecompositionData) : Prop :=
  ∀ R, ¬ IsHyperoctahedral R → PermutesComponents A (orthogonalMap R)
structure DecompositionProperties (σ : TupleFunctional) : Prop where
  exists_canonical : ∃ A : DecompositionData, A.IsCanonical σ
  canonical_isomorphic : ∀ A B : DecompositionData, A.IsCanonical σ →
    B.IsCanonical σ → A.Isomorphic B
  groundStates : ∀ A : DecompositionData, A.IsCanonical σ →
    GroundStatesAsL2 σ A
  transported : ∀ A : DecompositionData, A.IsCanonical σ → TransportedCanonical σ A
  latticePermute : ∀ A : DecompositionData, A.IsCanonical σ →
    LatticeSymmetriesPermute A
structure ComponentSymmetries (σ : TupleFunctional) : Prop where
  shift_invariant : ∀ v, σ.IsInvariant (SeparatedTuples.translate v)
  hyperoctahedral_invariant : ∀ w : hyperoctahedral, σ.IsInvariant w.1
  axialPositive : IsReflectionPositiveAxial σ
  diagonalPositive : IsReflectionPositiveDiagonal σ
  permInvariant : σ.IsPermInvariant
  regular : IsRegular σ
structure ComponentReconstruction (σ : TupleFunctional) : Prop where
  reconstruction : ReconstructionProperties σ
  kernel_eq : ∀ h : IsPosSemidef (reflectionForm σ),
    opKernel (pairHamiltonian σ h) = (ℂ ∙ vacuum σ h : Submodule ℂ (PhysicalSpace σ h))
  hamiltonianBounds : ∀ (h : IsPosSemidef (reflectionForm σ)) (i : Fin 3), HamiltonianGeMomentum σ h i
def JointSpectrumInForwardCone (σ : TupleFunctional) : Prop :=
  ∀ h : IsPosSemidef (reflectionForm σ),
    JointSpectrumSubset σ h {y | Real.sqrt (y 1 ^ 2 + y 2 ^ 2 + y 3 ^ 2) ≤ y 0}
def HasSpatialRotationRep (σ : TupleFunctional) : Prop :=
  ∀ h : IsPosSemidef (reflectionForm σ),
    ∃ U : Orthogonal.orthogonalGroupThree → PhysicalSpace σ h →L[ℂ] PhysicalSpace σ h,
      (∀ R, ActsOnClasses σ h (orthogonalMap (Orthogonal.embedOrthogonal R)) (U R)) ∧
      IsUnitaryRep σ h U ∧
      (∀ ψ, Continuous fun R : Orthogonal.orthogonalGroupThree => U R ψ) ∧
      (∀ R, U R (vacuum σ h) = vacuum σ h) ∧ CommutesWithHamiltonian σ h U
end YangMills.Construction.LimitTheorem
end
