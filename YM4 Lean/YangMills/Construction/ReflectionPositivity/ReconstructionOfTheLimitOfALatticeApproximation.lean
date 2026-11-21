import YangMills.Construction.Conventions.ContinuumLimitsOfLatticeApproximationsDefs
import YangMills.Construction.ReflectionPositivity.BoundedLatticeApproximationsAndTheirC1Constants
import YangMills.Construction.ReflectionPositivity.HamiltonianAndMomentaFromThePairMeasures
import Mathlib
set_option autoImplicit false
open MeasureTheory Set
open scoped ComplexOrder NNReal
noncomputable section
namespace YangMills.Construction.ReflectionPositivity.LimitReconstruction
open YangMills.Construction.SeparatedTuples YangMills.Construction.ReflectionPositivity.TupleForm YangMills.Construction.SpectralTheory
open YangMills.Construction.HilbertSpaceBasics (IsPosSemidef ofBounded)
open YangMills.Construction.ReflectionPositivity.ApproximatingSequences (LatticeApproximation)
open YangMills.Construction.ReflectionPositivity.Reconstruction (PhysicalSpace IsSpaceShiftFamily
  IsTimeShiftFamily MatrixElementFormula VacuumProperties spaceShift spatialBasisVec timeShift
  timeBasisVec vacuum)
open YangMills.Construction.ReflectionPositivity.PairMeasureOperators (pairHamiltonian pairMomentum)
open YangMills.Construction.ReflectionPositivity.ContractionFunctionals (IsAdmissible)
open YangMills.Construction.LimitConventions.ApproxTriple (ConvergesTo IsReflPos tupleRep)
def ContractsAtAllTimes (σ : TupleFunctional) : Prop :=
  ∀ (Z : PositiveSpan) (t : ℝ), 0 < t →
    reflectedCorrelation σ Z ((2 * t) • timeBasisVec) ≤ reflectionForm σ Z Z
section Objects
variable (σ : TupleFunctional) (h : IsPosSemidef (reflectionForm σ))
def IsHeatGenerator (A : UnboundedOperator (PhysicalSpace σ h)) : Prop :=
  ∃ F : ProjectionMeasure 1 (PhysicalSpace σ h),
    HasSpectralResolution A F ∧ F.IsConcentratedOn nonnegReals ∧
      ∀ t : ℝ≥0, ofBounded (timeShift σ h t) = F.expNegMulOp t
def IsShiftGenerator (i : Fin 3) (A : UnboundedOperator (PhysicalSpace σ h)) : Prop :=
  ∃ F : ProjectionMeasure 1 (PhysicalSpace σ h),
    HasSpectralResolution A F ∧
      ∀ u : ℝ, ofBounded (spaceShift σ h (u • spatialBasisVec i)) = F.expIMulOp u
def TimeSemigroupProperties : Prop :=
  (∃! T, IsTimeShiftFamily σ h T) ∧ IsTimeShiftFamily σ h (timeShift σ h) ∧
    StronglyContinuous (timeShift σ h) ∧ IsOperatorSemigroup (timeShift σ h) ∧
    (∀ t, IsSelfAdjoint (timeShift σ h t) ∧ IsContractive (timeShift σ h t) ∧
      LinearMap.ker (timeShift σ h t : PhysicalSpace σ h →ₗ[ℂ] PhysicalSpace σ h) = ⊥) ∧
    IsHeatGenerator σ h (pairHamiltonian σ h) ∧
    (∀ A, IsHeatGenerator σ h A → A = pairHamiltonian σ h) ∧
    ∃ hΩ : vacuum σ h ∈ (pairHamiltonian σ h).domain, pairHamiltonian σ h ⟨vacuum σ h, hΩ⟩ = 0
def SpaceShiftProperties : Prop :=
  (∃! U, IsSpaceShiftFamily σ h U) ∧ IsSpaceShiftFamily σ h (spaceShift σ h) ∧
    StronglyContinuous (spaceShift σ h) ∧
    IsAddUnitaryRep (spaceShift σ h) ∧
    (∀ a t, Commute (spaceShift σ h a) (timeShift σ h t)) ∧
    (∀ a, spaceShift σ h a (vacuum σ h) = vacuum σ h) ∧
    ∀ i : Fin 3, IsShiftGenerator σ h i (pairMomentum σ h i) ∧
      (∀ A, IsShiftGenerator σ h i A → A = pairMomentum σ h i) ∧
      ∃ hΩ : vacuum σ h ∈ (pairMomentum σ h i).domain, pairMomentum σ h i ⟨vacuum σ h, hΩ⟩ = 0
end Objects
def LimitReconstructionTheorem : Prop :=
  ∀ (D : YangMills.Construction.ReflectionPositivity.AxisMirror.MirrorData)
      (A : YangMills.Construction.LimitConventions.ApproxTriple D.L) (σ : TupleFunctional),
    LatticeApproximation.IsBoundedForSomeM D A →
    IsReflPos A → ConvergesTo A σ →
    IsAdmissible σ ∧ ContractsAtAllTimes σ ∧
      ∃ h : IsPosSemidef (reflectionForm σ),
        VacuumProperties σ h ∧ TimeSemigroupProperties σ h ∧ SpaceShiftProperties σ h ∧
          MatrixElementFormula σ h
end YangMills.Construction.ReflectionPositivity.LimitReconstruction
