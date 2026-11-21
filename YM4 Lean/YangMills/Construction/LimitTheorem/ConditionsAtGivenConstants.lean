import YangMills.Construction.Continuum.AxiomsOfOsterwalderAndSchrader
import YangMills.Construction.Continuum.ConditionsOnASequenceOfFunctionalsOnFlatSpaces
import YangMills.Construction.LimitTheorem.FunctionalDefs
import YangMills.Construction.Torus.HypercubicGroupTranslationsAndInvarianceOnTorusOrFourSpace
import Mathlib
set_option autoImplicit false
open Filter MeasureTheory Set
open scoped ComplexOrder InnerProductSpace NNReal Topology
noncomputable section
namespace YangMills.Construction.LimitTheorem
structure ConditionConstants where
  perBallConst : ℕ → ℝ → ℝ → ℝ
  A : ℝ → ℝ → ℝ
  B : ℝ → ℝ
  κStar : ℝ
  kE : ℕ
  cE : ℝ
  CE : ℝ
  κ : ℝ
  clusterCoeff : ℝ
  radiusCoeff : ℝ
  secondMoment : ℝ → ℝ → SeparatedTuples.SepTuple → ℝ
  d₀ : ℝ
  ηBar : ℝ → ℝ
variable (C : ConditionConstants)
def ofConfigTuple (X : ConfigSpace.SeparatedFamily) : TestSpaces.SepTuple :=
  ⟨X.1, X.2.1, fun i => by
      obtain ⟨-, h₁, h₂, h₃⟩ := ConfigSpace.mem_realC1CompactIn_iff.1 (X.2.2.1 i)
      exact ⟨h₁, h₂, h₃⟩, X.2.2.2⟩
def evalOnConfig (F : SeparatedTuples.TupleFunctional) (X : ConfigSpace.SeparatedFamily) : ℝ :=
  evalOnMap F (ofConfigTuple X)
def HasSchwingerSequence (F : SeparatedTuples.TupleFunctional) (T : ConfigSpace.FlatSequence) :
    Prop :=
  ConfigSpace.IsSchwingerSequenceOf (evalOnConfig F) T
def SatisfiesGrowth (T : ConfigSpace.FlatSequence) (k : ℕ) (c K ϰ : ℝ) : Prop :=
  ∀ (m : ℕ) (φ : ConfigSpace.schwartzFlatOffDiagonal (m + 1)),
    ‖T.atSucc m φ‖ ≤
      c * K ^ (m + 1) * ((m + 1).factorial : ℝ) ^ ϰ *
        ConfigSpace.bracketNorm (k * (m + 1)) (ConfigSpace.toSchwartzFn φ)
def boxedSeparatedTuples (ϖ d R : ℝ) : Set SeparatedTuples.SepTuple :=
  {X | (∃ x : Fin X.1.length → InfiniteLattice.AmbientSpace, ∀ i,
      tsupport (X.1.get i) ⊆ TestFunctions.closedBallR4 (x i) R ∧
      ∀ y ∈ TestFunctions.closedBallR4 (x i) R, ∀ μ, |y μ| < ϖ - d / 2) ∧
    ∀ i l : Fin X.1.length, i ≠ l →
      ENNReal.ofReal d ≤ TestFunctions.setDistR4 (tsupport (X.1.get i)) (tsupport (X.1.get l))}
def GrowthBound (F : SeparatedTuples.TupleFunctional) : Prop :=
  ∃ T, HasSchwingerSequence F T ∧ SatisfiesGrowth T C.kE C.cE C.CE C.κ
def twoPointFactor : ℝ :=
  3 * (2 ^ 2 - 1) / Real.pi ^ 4 * (12 * Real.pi ^ 2 / (11 * 2 ^ 2)) ^ 2
def TwoPointAsymptotic (d value : ℝ) (f h : InfiniteLattice.AmbientSpace → ℝ) : Prop :=
  ∃ η : ℝ, value = twoPointFactor * TestFunctions.inverseEighthKernel f h / Real.log (1 / d) ^ 2 * (1 + η) ∧
    1 / 2 * (1 - C.ηBar d) ^ 4 ≤ 1 + η ∧ 1 + η ≤ 3 / 2 * (1 + C.ηBar d) ^ 4
def energyMomentumOps (F : SeparatedTuples.TupleFunctional)
    (h : HilbertSpaceBasics.IsPosSemidef (ReflectionPositivity.TupleForm.reflectionForm F)) :
    Fin 4 → SpectralTheory.UnboundedOperator (ReflectionPositivity.Reconstruction.PhysicalSpace F h) :=
  ![ReflectionPositivity.PairMeasureOperators.pairHamiltonian F h,
    ReflectionPositivity.PairMeasureOperators.pairMomentum F h 0,
    ReflectionPositivity.PairMeasureOperators.pairMomentum F h 1,
    ReflectionPositivity.PairMeasureOperators.pairMomentum F h 2]
def JointSpectrumSubset (F : SeparatedTuples.TupleFunctional)
    (h : HilbertSpaceBasics.IsPosSemidef (ReflectionPositivity.TupleForm.reflectionForm F))
    (Z : Set (Fin 4 → ℝ)) : Prop :=
  ∃ Y, SpectralTheory.IsJointSpectrum Y (energyMomentumOps F h) ∧ Y ⊆ Z
structure IsStabilizerRep (F : SeparatedTuples.TupleFunctional)
    (h : HilbertSpaceBasics.IsPosSemidef (ReflectionPositivity.TupleForm.reflectionForm F))
    (U : TorusSymmetries.timeVecStabilizer →
      ReflectionPositivity.Reconstruction.PhysicalSpace F h →L[ℂ]
        ReflectionPositivity.Reconstruction.PhysicalSpace F h) : Prop where
  acts : ∀ w, ActsOnClasses F h w.1.1 (U w) ∧
    ∀ U', ActsOnClasses F h w.1.1 U' → U' = U w
  isUnitary : IsUnitaryRep F h U
  fixes_vacuum : ∀ w, U w (ReflectionPositivity.Reconstruction.vacuum F h) =
    ReflectionPositivity.Reconstruction.vacuum F h
  comm_hamiltonian : CommutesWithHamiltonian F h U
def ReconstructionProperties (F : SeparatedTuples.TupleFunctional) : Prop :=
  F.IsPermInvariant ∧ F.IsTranslateInvariant ∧
    ∃ h : HilbertSpaceBasics.IsPosSemidef (ReflectionPositivity.TupleForm.reflectionForm F),
      HasReconstruction F h ∧
      TopologicalSpace.SeparableSpace (ReflectionPositivity.Reconstruction.PhysicalSpace F h) ∧
      (∀ i : Fin 3, SpectralTheory.StronglyCommute
        (ReflectionPositivity.PairMeasureOperators.energyMomentumPair F h i)) ∧
      JointSpectrumSubset F h {y | 0 ≤ y 0} ∧
      ∃ U, IsStabilizerRep F h U
structure OSConditions (T : ConfigSpace.FlatSequence) : Prop where
  growth : SatisfiesGrowth T C.kE C.cE C.CE C.κ
  euclid_invariant : ConfigSpace.IsEuclidInvariant T
  reflection_positive : ConfigSpace.IsOSPositive T
  perm_symmetric : ConfigSpace.IsPermSymmetric T
  cluster : ConfigSpace.HasClusterProperty T
  reflection_real : ConfigSpace.IsReflectionReal T
open SeparatedTuples
open InfiniteLattice (AmbientSpace)
open ConfigSpace (FlatSequence schwartzFlatOffDiagonal bracketNorm toSchwartzFn)
def orthogonalMap (R : Orthogonal.orthogonalGroupFour) : AmbientSpace → AmbientSpace :=
  (ofOrthogonal R).toFun
def IsO4InvariantFunctional (σ : TupleFunctional) : Prop :=
  ∀ R, σ.IsInvariant (orthogonalMap R)
structure SatisfiesAxiomLists (T : FlatSequence) : Prop where
  osConditions : OSConditions C T
  growth : ∀ (m : ℕ) (φ : schwartzFlatOffDiagonal (m + 1)),
    ‖T.atSucc m φ‖ ≤
      C.cE * Real.exp C.CE * ((m + 1).factorial : ℝ) ^ (C.κ + 1) *
        bracketNorm (C.kE * (m + 1)) (toSchwartzFn φ)

namespace ComponentConditions
open SeparatedTuples ReflectionPositivity.TupleForm
open TorusMetric (euclidNormVec)
open HilbertSpaceBasics (IsPosSemidef)
def ClustersAtInfinity (σ : TupleFunctional) : Prop :=
  ∀ X Y : SepTuple, ∃ C r : ℝ, ∀ v : AmbientSpace, r ≤ euclidNormVec v →
    SepTuple.Composable X (push (translate v) Y) ∧
      |σ (SepTuple.juxt X (push (translate v) Y)) - σ X * σ Y| ≤ C * (euclidNormVec v ^ 2)⁻¹

/-- Euclidean hypotheses sufficient for all six axioms of a component. -/
def OSFromConditionsStatement : Prop :=
  ∀ (C : ConditionConstants) (σ : TupleFunctional), 0 ≤ C.cE → 0 ≤ C.CE →
    IsPosSemidef (reflectionForm σ) → TestSpaces.IsSepFunctional (evalOnMap σ) →
    (∀ v : AmbientSpace, σ.IsInvariant (SeparatedTuples.translate v)) →
    IsO4InvariantFunctional σ → σ.IsPermInvariant → GrowthBound C σ →
    ClustersAtInfinity σ → ∀ T, HasSchwingerSequence σ T → SatisfiesAxiomLists C T
end ComponentConditions
end YangMills.Construction.LimitTheorem
end
