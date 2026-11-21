import YangMills.Construction.Torus.DistanceBallsIntegralAndVolumeInPhysicalUnits
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open MeasureTheory Set TorusMetric TestFunctions TorusMeasure
namespace TorusCovering
def IsBddMeasurable {P : Conventions.StandingParameters} (F : P.Torus → ℝ) : Prop :=
  IsBoundedFun F ∧ IsMeasurableFun F
abbrev periodVec (P : Conventions.StandingParameters) (k : Fin 4 → ℤ) : Fin 4 → ℝ :=
  latticeTranslate (PeriodicLattice.torusSide P.L P.m) k
def ProjectionProperties (P : Conventions.StandingParameters) : Prop :=
  (∀ θ : ℝ, PeriodicLattice.toLevelUnits P.L P.K P.K θ = θ) ∧
  (∀ y, proj P y = classOf P y) ∧
  (∀ y, proj P ⁻¹' {proj P y} = {y' | ∃ k, y' = y + periodVec P k}) ∧
  (∀ z y, IsLift P z y ↔ proj P y = z) ∧
  (∀ z y, IsLift P z y → ∀ y', IsLift P z y' ↔ ∃ k, y' = y + periodVec P k) ∧
  (∀ y y', proj P (y + y') = proj P y + proj P y') ∧
  Function.Surjective (proj P) ∧
  (∀ y, proj P y = 0 ↔ ∃ k, y = periodVec P k) ∧
  (∀ z y, addVec P z y = z + proj P y) ∧
  ∀ z : P.Torus, IsLeast (euclidNormVec '' {y | IsLift P z y}) (pointNorm z)
def IntegralProperties (P : Conventions.StandingParameters) : Prop :=
  ∀ (F F' : P.Torus → ℝ), IsBddMeasurable F → IsBddMeasurable F' → ∀ α α' : ℝ,
    IsBddMeasurable (fun z => α * F z + α' * F' z) ∧
    IsBddMeasurable (fun z => F z * F' z) ∧
    torusIntegral (fun z => α * F z + α' * F' z) = α * torusIntegral F + α' * torusIntegral F' ∧
    ((∀ z, F z ≤ F' z) → torusIntegral F ≤ torusIntegral F')
def VolumeProperties (P : Conventions.StandingParameters) : Prop :=
  (∀ A A' : Set P.Torus, IsMeasurableTorusSet A → IsMeasurableTorusSet A' → A ⊆ A' →
    torusVolume A ≤ torusVolume A') ∧
  (∀ (n : ℕ) (A : Fin n → Set P.Torus), (∀ i, IsMeasurableTorusSet (A i)) →
    Pairwise (Function.onFun Disjoint A) →
    IsMeasurableTorusSet (⋃ i, A i) ∧
    torusVolume (⋃ i, A i) = ∑ i, torusVolume (A i) ∧
    ∀ F : P.Torus → ℝ, IsBddMeasurable F →
      setTorusIntegral (⋃ i, A i) F = ∑ i, setTorusIntegral (A i) F) ∧
  IsMeasurableTorusSet (univ : Set P.Torus) ∧
  torusVolume (univ : Set P.Torus) = PeriodicLattice.torusSide P.L P.m ^ 4
def PeriodizationProperties (P : Conventions.StandingParameters) : Prop :=
  ∀ (S : Set (Fin 4 → ℝ)) (f : (Fin 4 → ℝ) → ℝ),
    HasDiameterLE S (PeriodicLattice.torusSide P.L P.m / 2) →
    IsBoundedFun f → IsNullMeasurableFunR4 f → (∀ y, y ∉ S → f y = 0) →
    (∀ y, {k : Fin 4 → ℤ | f (y + periodVec P k) ≠ 0}.Subsingleton) ∧
    IsBddMeasurable (periodize (PeriodicLattice.torusSide P.L P.m) f : P.Torus → ℝ) ∧
    torusIntegral (periodize (PeriodicLattice.torusSide P.L P.m) f : P.Torus → ℝ) = integralR4 f
def CoveringIntegralVolumeStatement : Prop :=
  ∀ P : Conventions.StandingParameters, ProjectionProperties P ∧ IntegralProperties P ∧
    VolumeProperties P ∧ PeriodizationProperties P
end TorusCovering
end YangMills.Construction
