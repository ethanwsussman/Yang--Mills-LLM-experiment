import YangMills.Construction.Continuum.CubicGroupAndHypercubicMapsKeepingTheTimeAxis
import YangMills.Construction.ReflectionPositivity.BoundedLatticeApproximationsAndTheirC1Constants
import YangMills.Construction.ReflectionPositivity.HamiltonianAndMomentaFromThePairMeasures
import Mathlib
set_option autoImplicit false
open MeasureTheory Set
open scoped NNReal
noncomputable section
namespace YangMills.Construction.ReflectionPositivity.ReconstructionComplements
open YangMills.Construction.SeparatedTuples YangMills.Construction.ReflectionPositivity.TupleForm YangMills.Construction.SpectralTheory YangMills.Construction.LimitConventions
open YangMills.Construction.InfiniteLattice (AmbientSpace hyperoctahedralLinearGroup)
open YangMills.Construction.ReflectionPositivity.Reconstruction (PhysicalSpace spanClass posClass
  spaceShift vacuum)
open YangMills.Construction.Continuum.AxisPreservingSymmetries (timeBasisVector)
open YangMills.Construction.ReflectionPositivity.PairMeasureOperators (pairHamiltonian pairMomentum)
open YangMills.Construction.ReflectionPositivity.ShiftSpectralMeasure (shiftSpectralMeasure)
open YangMills.Construction.HilbertSpaceBasics (IsPosSemidef)
section Products
variable {𝓗 : Type*} [NormedAddCommGroup 𝓗] [InnerProductSpace ℂ 𝓗] [CompleteSpace 𝓗]
def compBounded (A : UnboundedOperator 𝓗) (B : 𝓗 →L[ℂ] 𝓗) : UnboundedOperator 𝓗 where
  domain := A.domain.comap (B : 𝓗 →ₗ[ℂ] 𝓗)
  toFun := A.toFun ∘ₗ (B : 𝓗 →ₗ[ℂ] 𝓗).restrict fun _ hx => hx
def boundedComp (B : 𝓗 →L[ℂ] 𝓗) (A : UnboundedOperator 𝓗) : UnboundedOperator 𝓗 where
  domain := A.domain
  toFun := (B : 𝓗 →ₗ[ℂ] 𝓗) ∘ₗ A.toFun
end Products
def spatialPart (y : Fin 4 → ℝ) : SpaceVec :=
  fun i => y i.succ
def energyMomentumProj (i : Fin 3) (y : Fin 4 → ℝ) : Fin 2 → ℝ :=
  ![y 0, y i.succ]
theorem measurable_energyMomentumProj (i : Fin 3) : Measurable (energyMomentumProj i) := by
  refine measurable_pi_iff.mpr fun r => ?_
  fin_cases r
  · exact measurable_pi_apply 0
  · exact measurable_pi_apply i.succ
def nonnegEnergy : BorelSets 4 :=
  ⟨{y | 0 ≤ y 0}, measurableSet_le measurable_const (measurable_pi_apply 0)⟩
def forwardCone : BorelSets 4 :=
  ⟨{y | ∀ i : Fin 3, |y i.succ| ≤ y 0}, by
    have hcone : {y : Fin 4 → ℝ | ∀ i : Fin 3, |y i.succ| ≤ y 0} =
        ⋂ i : Fin 3, {y | |y i.succ| ≤ y 0} := by
      ext
      simp
    rw [hcone]
    exact MeasurableSet.iInter fun i =>
      measurableSet_le (measurable_pi_apply i.succ).abs (measurable_pi_apply 0)⟩
def unitaryPhase (τ : ℝ) (a : SpaceVec) (y : Fin 4 → ℝ) : ℂ :=
  Complex.exp (Complex.I * ((τ * y 0 + spaceDot a (spatialPart y) : ℝ) : ℂ))
def heatPhase (t : ℝ≥0) (a : SpaceVec) (y : Fin 4 → ℝ) : ℂ :=
  Complex.exp (((-(t : ℝ) * y 0 : ℝ) : ℂ) + Complex.I * ((spaceDot a (spatialPart y) : ℝ) : ℂ))
section Objects
variable (σ : TupleFunctional) (hσ : IsPosSemidef (reflectionForm σ))
def IsJointGroupMeasure (E : ProjectionMeasure 4 (PhysicalSpace σ hσ)) : Prop :=
  ∃ F : ProjectionMeasure 1 (PhysicalSpace σ hσ),
    HasSpectralResolution (pairHamiltonian σ hσ) F ∧
      ∀ (τ : ℝ) (a : SpaceVec),
        compBounded (F.expIMulOp τ) (spaceShift σ hσ a) = E.functionalCalculus (unitaryPhase τ a)
def jointMeasure : ProjectionMeasure 4 (PhysicalSpace σ hσ) :=
  haveI : Nonempty (ProjectionMeasure 4 (PhysicalSpace σ hσ)) :=
    ⟨(SpectralMeasureOn.dirac ⟨univ, MeasurableSet.univ⟩ 0 (mem_univ _)).extend⟩
  Classical.epsilon (IsJointGroupMeasure σ hσ)
def energyMomentumOps : Fin 4 → UnboundedOperator (PhysicalSpace σ hσ) :=
  Fin.cons (α := fun _ => UnboundedOperator (PhysicalSpace σ hσ)) (pairHamiltonian σ hσ)
    (pairMomentum σ hσ)
def IsOctahedralUnitary (w : SpaceVec ≃ₗ[ℝ] SpaceVec)
    (V : PhysicalSpace σ hσ ≃ₗᵢ[ℂ] PhysicalSpace σ hσ) : Prop :=
  ∀ Z : PositiveSpan,
    V (posClass σ hσ Z) = spanClass σ hσ (pushSpan (timeExtension w) Z.1)
def octahedralUnitary (w : SpaceVec ≃ₗ[ℝ] SpaceVec) :
    PhysicalSpace σ hσ ≃ₗᵢ[ℂ] PhysicalSpace σ hσ :=
  haveI : Nonempty (PhysicalSpace σ hσ ≃ₗᵢ[ℂ] PhysicalSpace σ hσ) :=
    ⟨LinearIsometryEquiv.refl ℂ _⟩
  Classical.epsilon (IsOctahedralUnitary σ hσ w)
def octahedralUnitaryCLM (w : SpaceVec ≃ₗ[ℝ] SpaceVec) :
    PhysicalSpace σ hσ →L[ℂ] PhysicalSpace σ hσ :=
  (octahedralUnitary σ hσ w).toContinuousLinearEquiv
def octahedralUnitaryInvCLM (w : SpaceVec ≃ₗ[ℝ] SpaceVec) :
    PhysicalSpace σ hσ →L[ℂ] PhysicalSpace σ hσ :=
  (octahedralUnitary σ hσ w).symm.toContinuousLinearEquiv
end Objects
def MeasureClaim (σ : TupleFunctional) (hσ : IsPosSemidef (reflectionForm σ)) : Prop :=
  (∃! E, IsJointGroupMeasure σ hσ E) ∧ IsJointGroupMeasure σ hσ (jointMeasure σ hσ)
def OperatorClaim (σ : TupleFunctional) (hσ : IsPosSemidef (reflectionForm σ)) : Prop :=
  pairHamiltonian σ hσ = (jointMeasure σ hσ).coordinateOp 0 ∧
    (∀ i : Fin 3, pairMomentum σ hσ i = (jointMeasure σ hσ).coordinateOp i.succ) ∧
    StronglyCommute (energyMomentumOps σ hσ) ∧
    IsJointSpectralMeasure (jointMeasure σ hσ) (energyMomentumOps σ hσ)
def SupportClaim (σ : TupleFunctional) (hσ : IsPosSemidef (reflectionForm σ)) : Prop :=
  (jointMeasure σ hσ).IsConcentratedOn nonnegEnergy ∧
    ∃ F : ProjectionMeasure 1 (PhysicalSpace σ hσ),
      HasSpectralResolution (pairHamiltonian σ hσ) F ∧ F.IsConcentratedOn nonnegReals ∧
        ∀ (t : ℝ≥0) (a : SpaceVec),
          compBounded (F.expNegMulOp t) (spaceShift σ hσ a) =
            (jointMeasure σ hσ).functionalCalculus (heatPhase t a)
def MarginalClaim (σ : TupleFunctional) (hσ : IsPosSemidef (reflectionForm σ)) : Prop :=
  (∀ (i : Fin 3) (B : BorelSets 2),
    (jointMeasure σ hσ).pushforward (energyMomentumProj i) (measurable_energyMomentumProj i) B =
      (shiftSpectralMeasure σ hσ i).extend B) ∧
    (jointMeasure σ hσ).IsConcentratedOn forwardCone
def UnitaryClaim (σ : TupleFunctional) (hσ : IsPosSemidef (reflectionForm σ))
    (w : SpaceVec ≃ₗ[ℝ] SpaceVec) : Prop :=
  (∃! V, IsOctahedralUnitary σ hσ w V) ∧ IsOctahedralUnitary σ hσ w (octahedralUnitary σ hσ w)
def IntertwiningClaim (σ : TupleFunctional) (hσ : IsPosSemidef (reflectionForm σ))
    (w : SpaceVec ≃ₗ[ℝ] SpaceVec) : Prop :=
  octahedralUnitary σ hσ w (vacuum σ hσ) = vacuum σ hσ ∧
    (∃ F : ProjectionMeasure 1 (PhysicalSpace σ hσ),
      HasSpectralResolution (pairHamiltonian σ hσ) F ∧ F.IsConcentratedOn nonnegReals ∧
        ∀ t : ℝ≥0,
          boundedComp (octahedralUnitaryCLM σ hσ w) (F.expNegMulOp t) =
            compBounded (F.expNegMulOp t) (octahedralUnitaryCLM σ hσ w)) ∧
    SpectralTheory.unitaryConj (octahedralUnitary σ hσ w) (pairHamiltonian σ hσ) =
      pairHamiltonian σ hσ ∧
    ∀ a : SpaceVec,
      octahedralUnitaryCLM σ hσ w * spaceShift σ hσ a * octahedralUnitaryInvCLM σ hσ w =
        spaceShift σ hσ (w a)
def OctahedralFixesTime : Prop :=
  ∀ g : AmbientSpace ≃ₗ[ℝ] AmbientSpace,
    (g ∈ hyperoctahedralLinearGroup ∧ g timeBasisVector = timeBasisVector) ↔
      ∃ w ∈ octahedralGroup3, g = timeExtension w
def ComplementsTheorem : Prop :=
  OctahedralFixesTime ∧
    ∀ (D : ReflectionPositivity.AxisMirror.MirrorData)
        (T : LimitConventions.ApproxTriple D.L) (σ : TupleFunctional),
      ReflectionPositivity.ApproximatingSequences.LatticeApproximation.IsBoundedForSomeM D T →
      LimitConventions.ApproxTriple.IsReflPos T →
      LimitConventions.ApproxTriple.ConvergesTo T σ →
      ∃ hσ : IsPosSemidef (reflectionForm σ),
        MeasureClaim σ hσ ∧ OperatorClaim σ hσ ∧ SupportClaim σ hσ ∧ MarginalClaim σ hσ ∧
          ∀ w ∈ octahedralGroup3, UnitaryClaim σ hσ w ∧ IntertwiningClaim σ hσ w
end YangMills.Construction.ReflectionPositivity.ReconstructionComplements
