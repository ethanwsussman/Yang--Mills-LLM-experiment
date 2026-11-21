import YangMills.Construction.Continuum.CanonicalDecompositionOfAFunctional
import YangMills.Construction.Continuum.ConditionsOnASequenceOfFunctionalsOnFlatSpaces
import YangMills.Construction.LimitTheorem.FunctionalDefs
import YangMills.Construction.SystemsWithFiveBounds.SystemWithFiveBounds
import YangMills.Construction.Torus.HypercubicGroupTranslationsAndInvarianceOnTorusOrFourSpace
import YangMills.Construction.LimitTheorem.ComponentFieldData
import Mathlib
set_option autoImplicit false
open Filter MeasureTheory Set
open scoped ComplexOrder InnerProductSpace NNReal Topology
noncomputable section
namespace YangMills.Construction.SystemsWithFiveBounds
open LimitTheorem
open TestSpaces (SepTupleOfCard)
open SeparatedTuples ReflectionPositivity.TupleForm
open HilbertSpaceBasics (IsPosSemidef)
open ReflectionPositivity.Reconstruction (PhysicalSpace posClass vacuum)
open ReflectionPositivity.PairMeasureOperators (pairHamiltonian pairMomentum energyMomentumPair
  groundStateProjection)
open SpectralTheory
open InfiniteLattice (GaugeField IsShiftInvariant IsInfiniteVolumeLimit AmbientSpace periodicGibbsSet
  smearedEnergyCumulant)
open TestFunctions (closedBallR4 setDistR4 sharpNormR4 separatedPairsR4 inverseEighthKernel)
open TorusTransport (hyperoctahedral)
open ConfigSpace (FlatSequence schwartzFlatOffDiagonal bracketNorm toSchwartzFn)
structure LimitConstants where
  localBound : ℕ → ℝ → ℝ → ℝ
  globalPrefactor : ℝ → ℝ → ℝ
  globalBase : ℝ → ℝ
  globalExp : ℝ
  schwartzOrder : ℕ
  schwartzPrefactor : ℝ
  schwartzBase : ℝ
  schwartzExp : ℝ
  clusterConst : SepTuple → SepTuple → ℝ
  clusterRadius : SepTuple → SepTuple → ℝ
structure LimitConstants.Valid (K : LimitConstants) : Prop where
  globalExp_nonneg : 0 ≤ K.globalExp
  localBound_antitone : ∀ n : ℕ, 2 ≤ n → ∀ R : ℝ, 0 < R →
    AntitoneOn (fun d => K.localBound n d R) (Ioi 0)
  localBound_pos : ∀ n : ℕ, 2 ≤ n → ∀ d R : ℝ, 0 < d → 0 < R → 0 < K.localBound n d R
  globalPrefactor_pos : ∀ d R : ℝ, 0 < d → 0 < R → 0 < K.globalPrefactor d R
  globalBase_pos : ∀ R : ℝ, 0 < R → 0 < K.globalBase R
  schwartzOrder_pos : 0 < K.schwartzOrder
  schwartzPrefactor_pos : 0 < K.schwartzPrefactor
  schwartzBase_pos : 0 < K.schwartzBase
  schwartzExp_pos : 0 < K.schwartzExp
  clusterConst_pos : ∀ X Y : SepTuple, 0 < K.clusterConst X Y
  clusterRadius_pos : ∀ X Y : SepTuple, 0 < K.clusterRadius X Y
def sepFamilyToSepTuple (X : ConfigSpace.SeparatedFamily) : TestSpaces.SepTuple :=
  ⟨X.1, X.2.1, fun i => by
      obtain ⟨-, h₁, h₂, h₃⟩ := ConfigSpace.mem_realC1CompactIn_iff.1 (X.2.2.1 i)
      exact ⟨h₁, h₂, h₃⟩, X.2.2.2⟩
def evalOnSepFamily (σ : TupleFunctional) (X : ConfigSpace.SeparatedFamily) : ℝ :=
  evalOnMap σ (sepFamilyToSepTuple X)
def HasSchwingerSequence (σ : TupleFunctional) (T : FlatSequence) : Prop :=
  ConfigSpace.IsSchwingerSequenceOf (evalOnSepFamily σ) T
def SatisfiesGrowth (T : FlatSequence) (k : ℕ) (c C ϰ : ℝ) : Prop :=
  ∀ (m : ℕ) (φ : schwartzFlatOffDiagonal (m + 1)),
    ‖T.atSucc m φ‖ ≤
      c * C ^ (m + 1) * ((m + 1).factorial : ℝ) ^ ϰ *
        bracketNorm (k * (m + 1)) (toSchwartzFn φ)
section Conditions
variable (M ϑ d₀ : ℝ) (ηBar : ℝ → ℝ) (K : LimitConstants)
def LocalCumulantBounds (σ : TupleFunctional) : Prop :=
  ∀ n : ℕ, 2 ≤ n → ∀ R : ℝ, 0 < R → ∀ d : ℝ, 0 < d → ∀ X : SepTupleOfCard n,
    (∀ i, ∃ x, tsupport (X.1 i) ⊆ closedBallR4 x R) →
    (∀ i l, i ≠ l → ENNReal.ofReal d ≤ setDistR4 (tsupport (X.1 i)) (tsupport (X.1 l))) →
    |connectedFn σ X| ≤ K.localBound n d R * ∏ i, sharpNormR4 M (X.1 i) ∧
      |connectedFn σ X| ≤ K.globalPrefactor d R * K.globalBase R ^ n *
        (n.factorial : ℝ) ^ K.globalExp * ∏ i, sharpNormR4 M (X.1 i)
def SchwingerGrowth (σ : TupleFunctional) : Prop :=
  ∃ T, HasSchwingerSequence σ T ∧
    SatisfiesGrowth T K.schwartzOrder K.schwartzPrefactor K.schwartzBase K.schwartzExp
def TwoPointLawHolds (σ : TupleFunctional) : Prop :=
  ∀ d ∈ Ioc (0 : ℝ) d₀, ∀ f h : AmbientSpace → ℝ, (f, h) ∈ separatedPairsR4 d ϑ →
    ContDiff ℝ 1 f → ContDiff ℝ 1 h →
      ∃ X : SepTupleOfCard 2, X.1 = ![f, h] ∧ SatisfiesTwoPointLaw ηBar d (connectedFn σ X) f h
def energyMomentumOps (σ : TupleFunctional) (h : IsPosSemidef (reflectionForm σ)) :
    Fin 4 → UnboundedOperator (PhysicalSpace σ h) :=
  ![pairHamiltonian σ h, pairMomentum σ h 0, pairMomentum σ h 1, pairMomentum σ h 2]
def JointSpectrumSubset (σ : TupleFunctional) (h : IsPosSemidef (reflectionForm σ))
    (Z : Set (Fin 4 → ℝ)) : Prop :=
  ∃ Y, IsJointSpectrum Y (energyMomentumOps σ h) ∧ Y ⊆ Z
structure IsStabilizerRep (σ : TupleFunctional) (h : IsPosSemidef (reflectionForm σ))
    (U : TorusSymmetries.timeVecStabilizer →
      PhysicalSpace σ h →L[ℂ] PhysicalSpace σ h) : Prop where
  acts_unique : ∀ w, ActsOnClasses σ h w.1.1 (U w) ∧
    ∀ U', ActsOnClasses σ h w.1.1 U' → U' = U w
  unitary : IsUnitaryRep σ h U
  fixes_vacuum : ∀ w, U w (vacuum σ h) = vacuum σ h
  comm_hamiltonian : CommutesWithHamiltonian σ h U
def ReconstructionConditions (σ : TupleFunctional) : Prop :=
  σ.IsPermInvariant ∧ σ.IsTranslateInvariant ∧
    ∃ h : IsPosSemidef (reflectionForm σ), HasReconstruction σ h ∧
      TopologicalSpace.SeparableSpace (PhysicalSpace σ h) ∧
      (∀ i : Fin 3, StronglyCommute (energyMomentumPair σ h i)) ∧
      JointSpectrumSubset σ h {y | 0 ≤ y 0} ∧
      ∃ U, IsStabilizerRep σ h U
def InverseSquareClustering (σ : TupleFunctional) : Prop :=
  ∀ (X Y : SepTuple) (v : AmbientSpace), K.clusterRadius X Y ≤ TorusMetric.euclidNormVec v →
    SepTuple.Composable X (push (translate v) Y) ∧
      |σ (SepTuple.juxt X (push (translate v) Y)) - σ X * σ Y| ≤
        K.clusterConst X Y * (TorusMetric.euclidNormVec v ^ 2)⁻¹
def EnergyDominatesMomentum (σ : TupleFunctional) (h : IsPosSemidef (reflectionForm σ))
    (i : Fin 3) : Prop :=
  ∃ Y, IsJointSpectrum Y (energyMomentumPair σ h i) ∧ Y ⊆ {y | |y 1| ≤ y 0}
end Conditions
structure PairSequence (L : ℕ) (IsPair : ℕ+ → ℝ → Prop) where
  cutoff : ℕ+ → ℕ+
  tendsto_cutoff : Tendsto (fun j => (cutoff j : ℕ)) atTop atTop
  coupling : ℕ+ → ℝ
  pair : ∀ j, IsPair (cutoff j) (coupling j)
  state : ∀ j, Measure (GaugeField (PeriodicLattice.meshSize L (((cutoff j : ℕ)) : ℤ)))
  isLimit : ∀ j, IsInfiniteVolumeLimit L (cutoff j) (coupling j) (state j)
namespace PairSequence
variable {L : ℕ} {IsPair : ℕ+ → ℝ → Prop} (Q : PairSequence L IsPair)
def subseq (φ : ℕ+ → ℕ+) (hφ : Tendsto φ atTop atTop) : PairSequence L IsPair where
  cutoff j := Q.cutoff (φ j)
  tendsto_cutoff := Q.tendsto_cutoff.comp hφ
  coupling j := Q.coupling (φ j)
  pair j := Q.pair (φ j)
  state j := Q.state (φ j)
  isLimit j := Q.isLimit (φ j)
def Defines (S : CumulantFamily) : Prop :=
  ∀ (n : ℕ) (hn : 2 ≤ n) (X : SepTupleOfCard n),
    Tendsto (fun j => smearedEnergyCumulant (Q.state j) X.1) atTop (𝓝 ((S n hn X : ℝ) : ℂ))
def PeriodicInvariantStates : Prop :=
  ∀ j, Q.state j ∈ periodicGibbsSet L (Q.cutoff j) (Q.coupling j) ∧ IsShiftInvariant (Q.state j)
def LimitOfGrowingTori (S : CumulantFamily) : Prop :=
  ∃ m : ℕ+ → ℕ, Tendsto (fun j => PeriodicLattice.torusSide L (m j)) atTop atTop ∧
    ∀ (n : ℕ) (hn : 2 ≤ n) (X : SepTupleOfCard n),
      (∀ᶠ j in atTop, SchwingerFunctions.IsR4TestFamily (PeriodicLattice.torusSide L (m j)) X.1) ∧
      Tendsto (fun j => SchwingerFunctions.connectedSchwingerR4 L (m j) (Q.cutoff j) (Q.coupling j) X.1)
        atTop (𝓝 ((S n hn X : ℝ) : ℂ))
end PairSequence
structure LatticeSymmetries (S : CumulantFamily) : Prop where
  translate_inv : ∀ v, IsFamilyInvariant S (shiftMotion v)
  hyperoctahedral_inv : ∀ r, IsHyperoctahedralMotion r → r.shift = 0 → IsFamilyInvariant S r
  symm : IsFamilySymmetric S
  centred_motion_inv : ∀ r, IsHyperoctahedralMotion r → IsMotionInvariant (centredOf S) r
  centred_symm : (centredOf S).IsPermInvariant
def DistributionalExtension (S : CumulantFamily) : Prop :=
  TestSpaces.IsSepFunctional (evalOnMap (centredOf S)) ∧
    IsRegular (centredOf S) ∧ ∀ (n : ℕ) (hn : 2 ≤ n),
      ∃! u, IsDistribution (offDiagonal n) u ∧ AgreesOnTensors (S n hn) u
def RotationInvariant (S : CumulantFamily) : Prop :=
  ∀ R, IsFamilyInvariant S (ofOrthogonal R)
section Requirements
variable (M ϑ d₀ : ℝ) (ηBar : ℝ → ℝ) (K : LimitConstants)
structure LimitConditions (S : CumulantFamily) : Prop where
  localBounds : LocalCumulantBounds M K (centredOf S)
  growth : SchwingerGrowth K (centredOf S)
  reconstruction : ReconstructionConditions (centredOf S)
  twoPointLaw : TwoPointLawHolds ϑ d₀ ηBar (centredOf S)
  cumulants_eq : HasCumulants (centredOf S) S
  twoPoint_pos : ∀ d ∈ Ioc (0 : ℝ) d₀, ∀ X : SepTupleOfCard 2,
    (X.1 0, X.1 1) ∈ separatedPairsR4 d ϑ → 0 < S 2 le_rfl X
  two_le_rank : ∀ h : IsPosSemidef (reflectionForm (centredOf S)),
    2 ≤ Module.rank ℂ (PhysicalSpace (centredOf S) h)
structure LimitProperties {L : ℕ} {IsPair : ℕ+ → ℝ → Prop} (Q : PairSequence L IsPair)
    (S : CumulantFamily) : Prop where
  states : Q.PeriodicInvariantStates
  tori : Q.LimitOfGrowingTori S
  symmetries : LatticeSymmetries S
  axialPositive : IsReflectionPositiveAxial (centredOf S)
  distributions : DistributionalExtension S
  conditions : LimitConditions M ϑ d₀ ηBar K S
  diagonalPositive : IsReflectionPositiveDiagonal (centredOf S)
  energyBound : ∀ (h : IsPosSemidef (reflectionForm (centredOf S))) (i : Fin 3),
    EnergyDominatesMomentum (centredOf S) h i
  rotationInv : RotationInvariant S
end Requirements
def transportDecomposition (A : DecompositionData) (r : AmbientSpace → AmbientSpace) :
    DecompositionData where
  space := A.space
  law := A.law
  comp ξ := compInv (A.comp ξ) r
def PermutesComponents (A : DecompositionData) (r : AmbientSpace → AmbientSpace) : Prop :=
  ∃ h : A.space ≃ₜ A.space, A.law.map h = A.law ∧
    ∀ ξ, A.comp (h ξ) = compInv (A.comp ξ) r
def rotationMap (R : Orthogonal.orthogonalGroupFour) : AmbientSpace → AmbientSpace :=
  (ofOrthogonal R).toFun
def hamiltonianKernel (σ : TupleFunctional) (h : IsPosSemidef (reflectionForm σ)) :
    Submodule ℂ (PhysicalSpace σ h) :=
  Submodule.span ℂ (opKernel (pairHamiltonian σ h))
def ZeroEnergyIsL2 (σ : TupleFunctional) (A : DecompositionData) : Prop :=
  ∀ h : IsPosSemidef (reflectionForm σ),
    ∃ U : hamiltonianKernel σ h ≃ₗᵢ[ℂ] Lp ℂ 2 A.law,
      (∀ F : PositiveSpan,
        ∃ hF : groundStateProjection σ h (posClass σ h F) ∈ hamiltonianKernel σ h,
          (U ⟨_, hF⟩ : A.space → ℂ) =ᵐ[A.law]
            fun ξ => (A.comp ξ).spanExtension F.1) ∧
      (∃ hΩ : vacuum σ h ∈ hamiltonianKernel σ h,
        (U ⟨_, hΩ⟩ : A.space → ℂ) =ᵐ[A.law] fun _ => 1) ∧
      ENat.card A.space = Cardinal.toENat (Module.rank ℂ (hamiltonianKernel σ h))
structure DecompositionProperties (σ : TupleFunctional) : Prop where
  exists_canonical : ∃ A : DecompositionData, A.IsCanonical σ
  canonical_isomorphic : ∀ A B : DecompositionData, A.IsCanonical σ →
    B.IsCanonical σ → A.Isomorphic B
  zeroEnergy : ∀ A : DecompositionData, A.IsCanonical σ → ZeroEnergyIsL2 σ A
  transport_canonical : ∀ A : DecompositionData, A.IsCanonical σ →
    ∀ r : AmbientSpace → AmbientSpace, IsEuclidIsometry r → σ.IsInvariant r →
      (transportDecomposition A r).IsCanonical σ
  translate_permutes : ∀ A : DecompositionData, A.IsCanonical σ →
    ∀ v, PermutesComponents A (SeparatedTuples.translate v)
  hyperoctahedral_permutes : ∀ A : DecompositionData, A.IsCanonical σ →
    ∀ w : hyperoctahedral, PermutesComponents A w.1
  rotation_permutes : ∀ A : DecompositionData, A.IsCanonical σ →
    ∀ R, PermutesComponents A (rotationMap R)
structure ComponentSymmetries (σ : TupleFunctional) : Prop where
  translate_inv : ∀ v, σ.IsInvariant (SeparatedTuples.translate v)
  hyperoctahedral_inv : ∀ w : hyperoctahedral, σ.IsInvariant w.1
  rotation_inv : ∀ R, σ.IsInvariant (rotationMap R)
  axialPositive : IsReflectionPositiveAxial σ
  diagonalPositive : IsReflectionPositiveDiagonal σ
  symm : σ.IsPermInvariant
  regular : IsRegular σ
def SpatialRotationRep (σ : TupleFunctional) : Prop :=
  ∀ h : IsPosSemidef (reflectionForm σ),
    ∃ U : Orthogonal.orthogonalGroupThree → PhysicalSpace σ h →L[ℂ] PhysicalSpace σ h,
      (∀ R, ActsOnClasses σ h (rotationMap (Orthogonal.embedOrthogonal R)) (U R)) ∧
      IsUnitaryRep σ h U ∧
      (∀ ψ, Continuous fun R : Orthogonal.orthogonalGroupThree => U R ψ) ∧
      (∀ R, U R (vacuum σ h) = vacuum σ h) ∧ CommutesWithHamiltonian σ h U
structure ComponentReconstruction (σ : TupleFunctional) : Prop where
  conditions : ReconstructionConditions σ
  kernel_eq : ∀ h : IsPosSemidef (reflectionForm σ),
    opKernel (pairHamiltonian σ h) = (ℂ ∙ vacuum σ h : Submodule ℂ (PhysicalSpace σ h))
  energyBound : ∀ (h : IsPosSemidef (reflectionForm σ)) (i : Fin 3), EnergyDominatesMomentum σ h i
  forwardCone : ∀ h : IsPosSemidef (reflectionForm σ),
    JointSpectrumSubset σ h {y | Real.sqrt (y 1 ^ 2 + y 2 ^ 2 + y 3 ^ 2) ≤ y 0}
  spatialRotations : SpatialRotationRep σ
structure OSAxioms (K : LimitConstants) (T : FlatSequence) : Prop where
  growth : SatisfiesGrowth T K.schwartzOrder K.schwartzPrefactor K.schwartzBase K.schwartzExp
  euclidInv : ConfigSpace.IsEuclidInvariant T
  osPositive : ConfigSpace.IsOSPositive T
  permSymm : ConfigSpace.IsPermSymmetric T
  cluster : ConfigSpace.HasClusterProperty T
  reality : ConfigSpace.IsReflectionReal T
section Assertions
variable (M ϑ d₀ : ℝ) (ηBar : ℝ → ℝ) (K : LimitConstants)
structure ComponentProperties (σ : TupleFunctional) : Prop where
  symmetries : ComponentSymmetries σ
  localBounds : LocalCumulantBounds M K σ
  growth : SchwingerGrowth K σ
  twoPointLaw : TwoPointLawHolds ϑ d₀ ηBar σ
  reconstruction : ComponentReconstruction σ
  clustering : InverseSquareClustering K σ
  componentOS : ∀ T, HasSchwingerSequence σ T → OSAxioms K T
  fieldData : LimitTheorem.ComponentFieldData σ
structure ErgodicDecompositionConclusion {L : ℕ} {IsPair : ℕ+ → ℝ → Prop}
    (Q : PairSequence L IsPair) (S : CumulantFamily) : Prop where
  limit : LimitProperties M ϑ d₀ ηBar K Q S
  decomposition : DecompositionProperties (centredOf S)
  onePoint : ∀ A : DecompositionData, A.IsCanonical (centredOf S) →
    ∃ c : A.space → ℝ, Continuous c ∧ ∫ ξ, c ξ ∂A.law = 0 ∧
      ∀ (ξ : A.space) (X : SepTupleOfCard 1), connectedFn (A.comp ξ) X = c ξ * ∫ x, X.1 0 x
  components : ∀ A : DecompositionData, A.IsCanonical (centredOf S) →
    ∀ ξ, ComponentProperties M ϑ d₀ ηBar K (A.comp ξ)
end Assertions
namespace MainTheorem
def Statement : Prop :=
  ∀ Y : FiveBoundSystem, ∃ K : ℝ → LimitConstants, ∀ g ∈ Ioc 0 Y.top,
    (K g).Valid ∧
    (∃ (Q : PairSequence Y.L (Y.IsPair g)) (S : CumulantFamily), Q.Defines S) ∧
    (∀ Q : PairSequence Y.L (Y.IsPair g), ∃ (φ : ℕ+ → ℕ+) (hφ : Tendsto φ atTop atTop)
      (S : CumulantFamily), (Q.subseq φ hφ).Defines S) ∧
    ∀ (Q : PairSequence Y.L (Y.IsPair g)) (S : CumulantFamily), Q.Defines S →
      ErgodicDecompositionConclusion Y.M Y.ϑ (Y.consts g).lawScale (Y.consts g).lawError (K g) Q S
end MainTheorem
end YangMills.Construction.SystemsWithFiveBounds
end
