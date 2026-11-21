import YangMills.Construction.Coordinates.HolomorphyInCoordinates
import YangMills.Construction.InfiniteLattice.ConfigurationsFunctionsAndMeasures
import YangMills.Construction.InfiniteLattice.UnitSpacingLatticeData
import Mathlib
set_option autoImplicit false
open MeasureTheory Set
open scoped ComplexConjugate
noncomputable section
namespace YangMills.Construction.InfiniteLattice.AmbientFacts
open YangMills.Construction.FixedSpacing
section Preliminaries
variable {X : Type*} [TopologicalSpace X]
def IsSeparatingStarSubalgebra (A : Set (X → ℂ)) : Prop :=
  A ⊆ continuousSet X ∧
    (∀ f ∈ A, ∀ g ∈ A, f + g ∈ A ∧ f * g ∈ A) ∧
    (∀ (c : ℂ), ∀ f ∈ A, c • f ∈ A) ∧
    (∀ c : ℂ, (fun _ => c) ∈ A) ∧
    (∀ f ∈ A, (fun x => conj (f x)) ∈ A) ∧
    ∀ x y : X, x ≠ y → ∃ f ∈ A, f x ≠ f y
def IsSupDense (A : Set (X → ℂ)) : Prop :=
  ∀ F ∈ continuousSet X, ∀ ε : ℝ, 0 < ε →
    ∃ H ∈ A, normSup (F - H) < ENNReal.ofReal ε
def HasSupDenseSpan (S : Set (X → ℂ)) : Prop :=
  S ⊆ continuousSet X ∧
    IsSupDense (Submodule.span ℂ S : Set (X → ℂ))
end Preliminaries
def finiteCoordContinuous (ι : Type) : Set (LinkVariables ι → ℂ) :=
  {f | Continuous f ∧ DependsOnFinitelyManyCoords f}
def CompactMetrizableProducts (a : ℝ) : Prop :=
  (∀ S : Set (Link a), S ⊆ positiveLinkSet a →
    CompactSpace (LinkVariables S) ∧ TopologicalSpace.MetrizableSpace (LinkVariables S)) ∧
  CompactSpace (GaugeField a) ∧ TopologicalSpace.MetrizableSpace (GaugeField a)
def CylinderFunctionsDense (a : ℝ) : Prop :=
  (∀ S : Set (Link a), S ⊆ positiveLinkSet a →
    IsSeparatingStarSubalgebra (finiteCoordContinuous S) ∧
      IsSupDense (finiteCoordContinuous S)) ∧
  IsSupDense (continuousCylinderFunctions a)
def WeakProbabilitiesCompactMetrizable (a : ℝ) : Prop :=
  CompactSpace (GaugeFieldProbability a) ∧
    TopologicalSpace.MetrizableSpace (GaugeFieldProbability a)
def DenseSpanDeterminesMeasure (a : ℝ) : Prop :=
  HasSupDenseSpan (continuousCylinderFunctions a) ∧
  ∀ S : Set (GaugeField a → ℂ), HasSupDenseSpan S →
    ∀ (μ μ' : Measure (GaugeField a)) [IsProbabilityMeasure μ] [IsProbabilityMeasure μ'],
      (∀ F ∈ S, ∫ U, F U ∂μ = ∫ U, F U ∂μ') → μ = μ'
def ContinuousDenseInMeanSquare : Prop :=
  ∀ (Y : Type) [TopologicalSpace Y] [CompactSpace Y] [TopologicalSpace.MetrizableSpace Y]
    [MeasurableSpace Y] [BorelSpace Y] (μ : Measure Y) [IsProbabilityMeasure μ],
    (∀ H : Y → ℂ, Continuous H → GibbsAtFixedSpacing.IsSqIntegrable μ H) ∧
    ∀ F : Y → ℂ, GibbsAtFixedSpacing.IsSqIntegrable μ F → ∀ ε : ℝ, 0 < ε →
      ∃ H : Y → ℂ, Continuous H ∧ ∫⁻ y, ‖F y - H y‖ₑ ^ 2 ∂μ ≤ ENNReal.ofReal ε
open Classical in
def HaarInvariance : Prop :=
  Measure.IsMulLeftInvariant Matrices.ComplexMatrix2.haarProb ∧
  Measure.IsMulRightInvariant Matrices.ComplexMatrix2.haarProb ∧
  Measure.IsInvInvariant Matrices.ComplexMatrix2.haarProb ∧
  ∀ (κ : Type) [Finite κ],
    (∀ σ : Equiv.Perm κ, MeasurePreserving (fun V : LinkVariables κ => V ∘ σ)
      (LinkVariables.haarMeasure κ) (LinkVariables.haarMeasure κ)) ∧
    (∀ J : Set κ, MeasurePreserving
      (fun (V : LinkVariables κ) (i : κ) => if i ∈ J then (V i)⁻¹ else V i)
      (LinkVariables.haarMeasure κ) (LinkVariables.haarMeasure κ)) ∧
    ∀ W : LinkVariables κ, MeasurePreserving (fun V : LinkVariables κ => W * V)
      (LinkVariables.haarMeasure κ) (LinkVariables.haarMeasure κ)
def iterCircleIntegral (t : ℝ) : (n : ℕ) → (Coordinates.ComplexCoordinates n → ℂ) → ℂ
  | 0, f => f 0
  | n + 1, f => circleIntegral
      (fun z : ℂ => iterCircleIntegral t n fun w => f (Fin.cons z w)) 0 t
def CauchyMixedDerivative : Prop :=
  ∀ (n : ℕ), 1 ≤ n → ∀ t : ℝ, 0 < t → ∀ h : Coordinates.ComplexCoordinates n → ℂ,
    Coordinates.ComplexCoordinates.IsHolomorphicIn (N' := 1) {z | ∀ j, ‖z j‖ < 2 * t}
      (fun z _ => h z) →
    iteratedFDeriv ℂ n h 0 (fun i => Pi.single i 1) =
      (2 * (Real.pi : ℂ) * Complex.I) ^ (-(n : ℤ)) *
        iterCircleIntegral t n fun z => h z * ∏ j, z j ^ (-2 : ℤ)
def AllFacts : Prop :=
  (∀ P : Params, CompactMetrizableProducts P.mesh ∧
    CylinderFunctionsDense P.mesh ∧
    WeakProbabilitiesCompactMetrizable P.mesh ∧
    DenseSpanDeterminesMeasure P.mesh) ∧
  ContinuousDenseInMeanSquare ∧ HaarInvariance ∧ CauchyMixedDerivative
end YangMills.Construction.InfiniteLattice.AmbientFacts
