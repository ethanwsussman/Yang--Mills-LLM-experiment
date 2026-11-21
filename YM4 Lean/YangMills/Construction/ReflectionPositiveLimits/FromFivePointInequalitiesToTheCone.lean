import YangMills.Construction.ReflectionPositiveLimits.ReconstructionOfAFunctional
import Mathlib
set_option autoImplicit false
open Filter Set Topology
open scoped ComplexOrder InnerProductSpace NNReal
noncomputable section
namespace YangMills.Construction
namespace EnergyMomentum
def sinhSinRegion (t : ℝ≥0) : Set EnergyMomentumLine :=
  {p | |Real.sin ((t : ℝ) * p.2 / 2)| ≤ Real.sinh ((t : ℝ) * (p.1 : ℝ) / 2)}
theorem measurableSet_sinhSinRegion (t : ℝ≥0) : MeasurableSet (sinhSinRegion t) := by
  refine (isClosed_le ?_ ?_).measurableSet
  · exact (Real.continuous_sin.comp (by fun_prop)).abs
  · exact Real.continuous_sinh.comp (by fun_prop)
theorem measurableSet_energyGeAbsMomentum : MeasurableSet energyGeAbsMomentum :=
  (isClosed_le (by fun_prop) (by fun_prop)).measurableSet
end EnergyMomentum
namespace ReflectionPositivity
open EnergyMomentum EuclideanSpectral
def shiftedPairing (σ : Tuple → ℝ) (Z : combsSupportedIn upperHalfSpace) (v : Space)
    (hv : 0 ≤ v timeAxis) : ℂ :=
  reflForm σ Z (translateComb v hv Z)
theorem timeShiftVec_add_embedSpatial_timeAxis_nonneg (t : ℝ≥0) (y : Momentum3) :
    0 ≤ (timeShiftVec t + embedSpatial y) timeAxis := by
  simp [timeShiftVec_timeAxis, embedSpatial_timeAxis]
def fivePointExpr (σ : Tuple → ℝ) (k : Fin 3) (Z : combsSupportedIn upperHalfSpace)
    (t : ℝ≥0) : ℂ :=
  shiftedPairing σ Z 0 le_rfl
    - 4 * shiftedPairing σ Z (timeShiftVec t) (by rw [timeShiftVec_timeAxis]; exact t.2)
    + shiftedPairing σ Z (timeShiftVec (2 * t)) (by rw [timeShiftVec_timeAxis]; exact (2 * t).2)
    + shiftedPairing σ Z (timeShiftVec t + embedSpatial ((t : ℝ) • EuclideanSpace.single k (1 : ℝ)))
        (timeShiftVec_add_embedSpatial_timeAxis_nonneg t _)
    + shiftedPairing σ Z
        (timeShiftVec t + embedSpatial ((-(t : ℝ)) • EuclideanSpace.single k (1 : ℝ)))
        (timeShiftVec_add_embedSpatial_timeAxis_nonneg t _)
def FivePointPositive (σ : Tuple → ℝ) (k : Fin 3) (D : Set ℝ≥0) : Prop :=
  ∀ (Z : combsSupportedIn upperHalfSpace), ∀ t ∈ D, 0 ≤ fivePointExpr σ k Z t
def fivePointOp (σ : Tuple → ℝ) (h : ReflectionPositiveAt timeZeroMirror σ) (k : Fin 3)
    (t : ℝ≥0) : ReconstructionSpace σ h →L[ℂ] ReconstructionSpace σ h :=
  (1 - transferSemigroup σ h t) ^ 2 - transferSemigroup σ h t *
    ((2 : ℂ) • (1 : ReconstructionSpace σ h →L[ℂ] ReconstructionSpace σ h)
      - spatialTranslationRep σ h ((t : ℝ) • EuclideanSpace.single k (1 : ℝ))
      - spatialTranslationRep σ h ((-(t : ℝ)) • EuclideanSpace.single k (1 : ℝ)))
end ReflectionPositivity
namespace ReflectionPositivity.FivePointCone
open ReflectionPositivity ReflectionPositivity.FunctionalReconstruction EnergyMomentum EuclideanSpectral
variable (σ : Tuple → ℝ) (hσ : ReconstructionData σ) (k : Fin 3)
structure FivePointOpProps (D : Set ℝ≥0) : Prop where
  fivePointExpr_eq : ∀ t : ℝ≥0, 0 < t → ∀ Z : combsSupportedIn upperHalfSpace,
    fivePointExpr σ k Z t =
      ⟪toReconstruction σ hσ.reflectionPositive Z,
        fivePointOp σ hσ.reflectionPositive k t
          (toReconstruction σ hσ.reflectionPositive Z)⟫_ℂ
  isSelfAdjoint : ∀ t : ℝ≥0, 0 < t →
    IsSelfAdjointOp (fivePointOp σ hσ.reflectionPositive k t)
  isAdjointPair : ∀ t : ℝ≥0, 0 < t →
    IsAdjointPair
      (spatialTranslationRep σ hσ.reflectionPositive
        ((-(t : ℝ)) • EuclideanSpace.single k (1 : ℝ)))
      (spatialTranslationRep σ hσ.reflectionPositive
        ((t : ℝ) • EuclideanSpace.single k (1 : ℝ)))
  nonneg : ∀ t ∈ D,
    OpGe (fivePointOp σ hσ.reflectionPositive k t) (scalarOp 0)
def CarriedBySinhRegions (D : Set ℝ≥0) : Prop :=
  ∀ t ∈ D, (axisSpectralMeasure σ hσ.reflectionPositive k).IsCarriedBy
    ⟨sinhSinRegion t, measurableSet_sinhSinRegion t⟩
structure ConeSupport : Prop where
  carriedBy : (axisSpectralMeasure σ hσ.reflectionPositive k).IsCarriedBy
    ⟨energyGeAbsMomentum, measurableSet_energyGeAbsMomentum⟩
  energyDominates : EnergyDominatesMomentum σ hσ k
structure DomainComparison : Prop where
  domain_le : (hamiltonianOp σ hσ).domain ≤ (momentumOpOf σ hσ k).domain
  domain_eq : (momentumOpOf σ hσ k).domain = (absMomentumOp σ hσ k).domain
  inner_le : ∀ (ψ : ReconstructionSpace σ hσ.reflectionPositive)
    (hH : ψ ∈ (hamiltonianOp σ hσ).domain) (hP : ψ ∈ (absMomentumOp σ hσ k).domain),
    ⟪ψ, absMomentumOp σ hσ k ⟨ψ, hP⟩⟫_ℂ ≤ ⟪ψ, hamiltonianOp σ hσ ⟨ψ, hH⟩⟫_ℂ
def KernelTranslationInvariant : Prop :=
  ∀ ψ ∈ pmapKernel (hamiltonianOp σ hσ), ∀ u : ℝ, coordTranslationOperator σ hσ k u ψ = ψ
def FivePointConeTheorem : Prop :=
  ∀ (σ : Tuple → ℝ) (hσ : ReconstructionData σ) (k : Fin 3),
    (∀ D : Set ℝ≥0, (∀ t ∈ D, 0 < t) → AccPt (0 : ℝ≥0) (𝓟 D) → FivePointPositive σ k D →
      FivePointOpProps σ hσ k D ∧ CarriedBySinhRegions σ hσ k D ∧ ConeSupport σ hσ k ∧
        DomainComparison σ hσ k ∧ KernelTranslationInvariant σ hσ k) ∧
    (EnergyDominatesMomentum σ hσ k →
      DomainComparison σ hσ k ∧ KernelTranslationInvariant σ hσ k)
end ReflectionPositivity.FivePointCone
end YangMills.Construction
