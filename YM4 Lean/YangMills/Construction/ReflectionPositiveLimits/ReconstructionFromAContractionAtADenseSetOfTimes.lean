import YangMills.Construction.EnergyMomentum.MomentumLineCoordinates
import YangMills.Construction.EuclideanSpectral.FunctionalCalculus
import YangMills.Construction.ReflectionPositiveLimits.FormAndHilbertSpaceOfAFunctional
import Mathlib
set_option autoImplicit false
open Filter Set Topology
open scoped ComplexConjugate ComplexOrder InnerProductSpace NNReal
noncomputable section
namespace YangMills.Construction.ReflectionPositivity
open EuclidIsometry EnergyMomentum EuclideanSpectral PeriodicLattice
theorem pushComb_translate_mem {v : Space} (hv : 0 ≤ v timeAxis) {Z : TupleComb}
    (hZ : Z ∈ combsSupportedIn upperHalfSpace) :
    pushComb (translate v) Z ∈ combsSupportedIn upperHalfSpace := by
  classical
  rw [mem_combsSupportedIn_iff] at hZ ⊢
  intro Y hY
  have hsupp := Finsupp.mapDomain_support (f := push (translate v)) (s := Z) (Finset.mem_coe.1 hY)
  obtain ⟨X, hX, rfl⟩ := Finset.mem_image.1 hsupp
  intro g hg
  obtain ⟨f, hf, rfl⟩ := List.mem_map.1 hg
  rw [tsupport_pushFn]
  intro y hy
  have hpos : 0 < ((EuclidIsometry.translate v).symm.toFun y) timeAxis := hZ hX f hf hy
  rw [symm_translate] at hpos
  change 0 < y timeAxis
  have hsub : (y - v) timeAxis = y timeAxis - v timeAxis := rfl
  linarith
def translateComb (v : Space) (hv : 0 ≤ v timeAxis)
    (Z : combsSupportedIn upperHalfSpace) : combsSupportedIn upperHalfSpace :=
  ⟨pushComb (translate v) Z, pushComb_translate_mem hv Z.2⟩
def timeShiftVec (t : ℝ≥0) : Space := (t : ℝ) • coordVec timeAxis
theorem timeShiftVec_timeAxis (t : ℝ≥0) : timeShiftVec t timeAxis = t := by
  simp [timeShiftVec, coordVec]
def timeShiftComb (t : ℝ≥0) (Z : combsSupportedIn upperHalfSpace) : combsSupportedIn upperHalfSpace :=
  translateComb (timeShiftVec t) (by rw [timeShiftVec_timeAxis]; exact t.2) Z
def spaceShiftComb (y : Momentum3) (Z : combsSupportedIn upperHalfSpace) :
    combsSupportedIn upperHalfSpace :=
  translateComb (embedSpatial y) (embedSpatial_timeAxis y).ge Z
def spacetimeShiftComb (t : ℝ≥0) (y : Momentum3) (Z : combsSupportedIn upperHalfSpace) :
    combsSupportedIn upperHalfSpace :=
  translateComb (timeShiftVec t + embedSpatial y)
    (by simp [timeShiftVec_timeAxis, embedSpatial_timeAxis]) Z
def tupleToComb (X : Tuple) (hX : X ∈ tuplesSupportedIn upperHalfSpace) :
    combsSupportedIn upperHalfSpace :=
  ⟨basisOf X, Submodule.subset_span (mem_image_of_mem _ hX)⟩
def ContractsAtTime (σ : Tuple → ℝ) (t : ℝ≥0) : Prop :=
  ∀ Z : combsSupportedIn upperHalfSpace,
    reflForm σ Z (timeShiftComb (2 * t) Z) ≤ reflForm σ Z Z
def ContractsOnDenseTimes (σ : Tuple → ℝ) : Prop :=
  ∃ D : Set ℝ≥0, (∀ t ∈ D, 0 < t) ∧ Ioi 0 ⊆ closure D ∧ ∀ t ∈ D, ContractsAtTime σ t
structure ReconstructionHypotheses (σ : Tuple → ℝ) : Prop where
  isNormalized : IsNormalizedFunctional σ
  isAdmissiblyContinuous : IsAdmissiblyContinuous σ
  isPermInvariant : IsPermInvariant σ
  isTranslInvariant : IsTranslInvariant σ
  isReflectionInvariant : IsIsomInvariant timeZeroMirror.reflectIso σ
  isReflectionPositive : ReflectionPositiveAt timeZeroMirror σ
section Operators
variable (σ : Tuple → ℝ) (h : ReflectionPositiveAt timeZeroMirror σ)
def IsTransferSemigroup
    (T : ℝ≥0 → ReconstructionSpace σ h →L[ℂ] ReconstructionSpace σ h) : Prop :=
  ∀ t Z, T t (toReconstruction σ h Z) = toReconstruction σ h (timeShiftComb t Z)
def transferSemigroup : ℝ≥0 → ReconstructionSpace σ h →L[ℂ] ReconstructionSpace σ h :=
  Classical.epsilon (IsTransferSemigroup σ h)
def IsSpatialTranslationRep
    (U : Momentum3 → ReconstructionSpace σ h →L[ℂ] ReconstructionSpace σ h) : Prop :=
  ∀ y Z, U y (toReconstruction σ h Z) = toReconstruction σ h (spaceShiftComb y Z)
def spatialTranslationRep :
    Momentum3 → ReconstructionSpace σ h →L[ℂ] ReconstructionSpace σ h :=
  Classical.epsilon (IsSpatialTranslationRep σ h)
def IsJointSpectralMeasure
    (E : SpectralMeasure EnergyMomentumSpace (ReconstructionSpace σ h)) : Prop :=
  ∀ t y, transferSemigroup σ h t * spatialTranslationRep σ h y =
    E.boundedCalculus (laplaceFourierExp t y)
def jointSpectralMeasure : SpectralMeasure EnergyMomentumSpace (ReconstructionSpace σ h) :=
  haveI := SpectralMeasure.nonempty_of_isEuclideanBorel
    (K := ReconstructionSpace σ h) isEuclideanBorel_energyMomentumSpace
  Classical.epsilon (IsJointSpectralMeasure σ h)
def IsAxisSpectralMeasure (i : Fin 3)
    (F : SpectralMeasure EnergyMomentumLine (ReconstructionSpace σ h)) : Prop :=
  ∀ (t : ℝ≥0) (s : ℝ), transferSemigroup σ h t *
      spatialTranslationRep σ h (s • EuclideanSpace.single i (1 : ℝ)) =
    F.boundedCalculus (laplaceFourierExpLine t s)
def axisSpectralMeasure (i : Fin 3) :
    SpectralMeasure EnergyMomentumLine (ReconstructionSpace σ h) :=
  haveI := SpectralMeasure.nonempty_of_isEuclideanBorel
    (K := ReconstructionSpace σ h) isEuclideanBorel_energyMomentumLine
  Classical.epsilon (IsAxisSpectralMeasure σ h i)
def hamiltonian : ReconstructionSpace σ h →ₗ.[ℂ] ReconstructionSpace σ h :=
  (jointSpectralMeasure σ h).calculusOperator coordEnergy
def momentumOp (i : Fin 3) :
    ReconstructionSpace σ h →ₗ.[ℂ] ReconstructionSpace σ h :=
  (jointSpectralMeasure σ h).calculusOperator (coordMomentum i)
end Operators
namespace DenseTimeReconstruction
def ReflectionInvarianceFollows : Prop :=
  ∀ σ : Tuple → ℝ, IsNormalizedFunctional σ → IsTranslInvariant σ →
    ReflectionPositiveAt timeZeroMirror σ → IsIsomInvariant timeZeroMirror.reflectIso σ
variable (σ : Tuple → ℝ) (h : ReflectionPositiveAt timeZeroMirror σ)
structure FormAndVacuumProps : Prop where
  isHermitian : HilbertSpaceBasics.IsHermitianForm (reflForm σ)
  isPosSemidef : HilbertSpaceBasics.IsPosSemidef (reflForm σ)
  norm_vacuum : ‖vacuum σ h‖ = 1
  inner_class_vacuum : ∀ (X : Tuple) (hX : X ∈ tuplesSupportedIn upperHalfSpace),
    ⟪toReconstruction σ h (tupleToComb X hX), vacuum σ h⟫_ℂ = (σ X : ℂ)
  inner_vacuum_class : ∀ (X : Tuple) (hX : X ∈ tuplesSupportedIn upperHalfSpace),
    ⟪vacuum σ h, toReconstruction σ h (tupleToComb X hX)⟫_ℂ = (σ X : ℂ)
structure TimeShiftProps : Prop where
  mem_combsSupportedIn : ∀ (Z : combsSupportedIn upperHalfSpace) (t : ℝ≥0),
    pushComb (EuclidIsometry.translate (timeShiftVec t)) Z ∈ combsSupportedIn upperHalfSpace
  form_eq_norm_sq : ∀ (Z : combsSupportedIn upperHalfSpace) (t : ℝ≥0),
    reflForm σ Z (timeShiftComb (2 * t) Z) =
      ((‖toReconstruction σ h (timeShiftComb t Z)‖ ^ 2 : ℝ) : ℂ)
  contractsAtTime : ContractsOnDenseTimes σ → ∀ t : ℝ≥0, ContractsAtTime σ t
structure TransferSemigroupProps : Prop where
  existsUnique : ∃! T : ℝ≥0 → ReconstructionSpace σ h →L[ℂ] ReconstructionSpace σ h,
    IsTransferSemigroup σ h T
  isTransferSemigroup : IsTransferSemigroup σ h (transferSemigroup σ h)
  isSelfAdjoint : ∀ t, IsSelfAdjointOp (transferSemigroup σ h t)
  isContraction : ∀ t, IsContractionOp (transferSemigroup σ h t)
  isStronglyContinuous : IsStrongContinuous (transferSemigroup σ h)
  zero : transferSemigroup σ h 0 = 1
  add : ∀ t t', transferSemigroup σ h t * transferSemigroup σ h t' =
    transferSemigroup σ h (t + t')
  kernel_eq : ∀ t, opKernel (transferSemigroup σ h t) = {0}
  fixes_vacuum : ∀ t, transferSemigroup σ h t (vacuum σ h) = vacuum σ h
structure SpatialRepProps : Prop where
  existsUnique : ∃! U : Momentum3 → ReconstructionSpace σ h →L[ℂ] ReconstructionSpace σ h,
    IsSpatialTranslationRep σ h U
  isSpatialTranslationRep : IsSpatialTranslationRep σ h (spatialTranslationRep σ h)
  isStronglyContinuous : IsStrongContinuous (spatialTranslationRep σ h)
  isUnitary : ∀ y, IsUnitaryOp (spatialTranslationRep σ h y)
  add : ∀ y y', spatialTranslationRep σ h y * spatialTranslationRep σ h y' =
    spatialTranslationRep σ h (y + y')
  commutes : ∀ t y, transferSemigroup σ h t * spatialTranslationRep σ h y =
    spatialTranslationRep σ h y * transferSemigroup σ h t
  fixes_vacuum : ∀ y, spatialTranslationRep σ h y (vacuum σ h) = vacuum σ h
structure MatrixElementProps : Prop where
  inner_eq : ∀ (Z W : combsSupportedIn upperHalfSpace) (t : ℝ≥0) (y : Momentum3),
    ⟪toReconstruction σ h Z, transferSemigroup σ h t
      (spatialTranslationRep σ h y (toReconstruction σ h W))⟫_ℂ =
        reflForm σ Z (spacetimeShiftComb t y W)
  inner_vacuum : ∀ (X : Tuple) (hX : X ∈ tuplesSupportedIn upperHalfSpace),
    ⟪vacuum σ h, toReconstruction σ h (tupleToComb X hX)⟫_ℂ = (σ X : ℂ)
structure AxisMeasureProps (i : Fin 3) : Prop where
  existsUnique : ∃! F : SpectralMeasure EnergyMomentumLine (ReconstructionSpace σ h),
    IsAxisSpectralMeasure σ h i F
  isAxisSpectralMeasure :
    IsAxisSpectralMeasure σ h i (axisSpectralMeasure σ h i)
  eq_pushforward : axisSpectralMeasure σ h i =
    (jointSpectralMeasure σ h).pushforward isEuclideanBorel_energyMomentumLine
      (projMomentum i) (measurable_projMomentum i)
  calculusOperator_energy : (axisSpectralMeasure σ h i).calculusOperator lineEnergyCoord =
    hamiltonian σ h
  calculusOperator_momentum : (axisSpectralMeasure σ h i).calculusOperator lineMomentumCoord =
    momentumOp σ h i
def energyDiffQuot (ψ : ReconstructionSpace σ h) (t : ℝ≥0) : ReconstructionSpace σ h :=
  (((t : ℝ)⁻¹ : ℝ) : ℂ) • (ψ - transferSemigroup σ h t ψ)
def momentumDiffQuot (i : Fin 3) (ψ : ReconstructionSpace σ h) (s : ℝ) :
    ReconstructionSpace σ h :=
  (Complex.I * (s : ℂ))⁻¹ •
    (spatialTranslationRep σ h (s • EuclideanSpace.single i (1 : ℝ)) ψ - ψ)
structure JointMeasureProps : Prop where
  existsUnique : ∃! E : SpectralMeasure EnergyMomentumSpace (ReconstructionSpace σ h),
    IsJointSpectralMeasure σ h E
  isJointSpectralMeasure : IsJointSpectralMeasure σ h (jointSpectralMeasure σ h)
  hamiltonian_isSelfAdjoint : IsSelfAdjointPartial (hamiltonian σ h)
  momentum_isSelfAdjoint : ∀ i, IsSelfAdjointPartial (momentumOp σ h i)
  hamiltonian_nonneg : IsNonnegPartial (hamiltonian σ h)
  mem_hamiltonian_domain_iff : ∀ ψ, ψ ∈ (hamiltonian σ h).domain ↔
    ∃ χ, Tendsto (energyDiffQuot σ h ψ) (𝓝[>] 0) (𝓝 χ)
  tendsto_hamiltonian : ∀ ψ : (hamiltonian σ h).domain,
    Tendsto (energyDiffQuot σ h ψ) (𝓝[>] 0) (𝓝 (hamiltonian σ h ψ))
  mem_momentum_domain_iff : ∀ i ψ, ψ ∈ (momentumOp σ h i).domain ↔
    ∃ χ, Tendsto (momentumDiffQuot σ h i ψ) (𝓝[≠] 0) (𝓝 χ)
  tendsto_momentum : ∀ (i : Fin 3) (ψ : (momentumOp σ h i).domain),
    Tendsto (momentumDiffQuot σ h i ψ) (𝓝[≠] 0) (𝓝 (momentumOp σ h i ψ))
  vacuum_mem_hamiltonian_kernel : vacuum σ h ∈ pmapKernel (hamiltonian σ h)
  vacuum_mem_momentum_kernel : ∀ i,
    vacuum σ h ∈ pmapKernel (momentumOp σ h i)
def DenseTimeReconstructionHolds : Prop :=
  ReflectionInvarianceFollows ∧
    ∀ (σ : Tuple → ℝ) (hσ : ReconstructionHypotheses σ),
      FormAndVacuumProps σ hσ.isReflectionPositive ∧ TimeShiftProps σ hσ.isReflectionPositive ∧
        (ContractsOnDenseTimes σ →
          TransferSemigroupProps σ hσ.isReflectionPositive ∧
            SpatialRepProps σ hσ.isReflectionPositive ∧
            MatrixElementProps σ hσ.isReflectionPositive ∧
            (∀ i, AxisMeasureProps σ hσ.isReflectionPositive i) ∧
            JointMeasureProps σ hσ.isReflectionPositive)
end DenseTimeReconstruction
end YangMills.Construction.ReflectionPositivity
