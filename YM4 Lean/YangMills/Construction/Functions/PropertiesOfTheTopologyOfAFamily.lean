import YangMills.Construction.TorusOrFourSpace.EvaluationsAtDegenerateArguments
import Mathlib
set_option autoImplicit false
open scoped Topology
noncomputable section
namespace YangMills.Construction.FamilyTopology.Properties
def RealTendstoAlong (J : Set ℕ+) (hJ : J.Infinite) (r : J → ℝ) (z : ℝ) : Prop :=
  PeriodicSpace.DiagonalLimits.TendsToWhereDefined (𝕜 := ℝ) ⟨J, hJ⟩ (fun j => j ∈ J)
    (fun j hj => r ⟨j, hj⟩) z
abbrev restrictTopology {X : Type} (T : TopologicalSpace X) (E : Set X) : TopologicalSpace E :=
  TopologicalSpace.induced Subtype.val T
def IsCoarsestMakingContinuous : Prop :=
  ∀ (X ι : Type) (e : ι → X → ℝ),
    (∀ U : Set X, IsOpen[familyTopology e] U ↔ U ∈ familyOpens e) ∧
    (∀ a, Continuous[familyTopology e, inferInstance] (e a)) ∧
    ∀ T : TopologicalSpace X, (∀ a, Continuous[T, inferInstance] (e a)) →
      ∀ U : Set X, IsOpen[familyTopology e] U → IsOpen[T] U
def ContinuousIffCoordsContinuous : Prop :=
  ∀ (X ι Z : Type) (e : ι → X → ℝ) (TZ : TopologicalSpace Z) (g : Z → X),
    Continuous[TZ, familyTopology e] g ↔ ∀ a, Continuous[TZ, inferInstance] (e a ∘ g)
def TendstoIffCoordsTendsto : Prop :=
  ∀ (X ι : Type) (e : ι → X → ℝ) (J : Set ℕ+) (hJ : J.Infinite) (x : J → X) (y : X),
    TendstoAlong (familyTopology e) J hJ x y ↔
      ∀ a, RealTendstoAlong J hJ (fun j => e a (x j)) (e a y)
def RealTendstoAgreement : Prop :=
  ∀ (J : Set ℕ+) (hJ : J.Infinite) (r : J → ℝ) (z : ℝ),
    TendstoAlong inferInstance J hJ r z ↔ RealTendstoAlong J hJ r z
def InducedEqRestrictedFamily : Prop :=
  ∀ (X ι : Type) (e : ι → X → ℝ) (E : Set X),
    restrictTopology (familyTopology e) E = familyTopology fun a (x : E) => e a x
def CountableSeparatingMetrization : Prop :=
  ∀ (X ι : Type) (e : ι → X → ℝ), Countable ι → Nonempty ι → SeparatesPoints e →
    ∀ (σ : ℕ+ → ι) (hσ : Function.Surjective σ),
      IsMetricFunction (familyDistance e σ hσ) ∧
      (∀ U : Set X, IsUnionOfBalls (familyDistance e σ hσ) U ↔ U ∈ familyOpens e) ∧
      IsMetrizableVia (familyTopology e) ∧
      ∀ E : Set X,
        IsMetricFunction (fun x x' : E => familyDistance e σ hσ x x') ∧
        (∀ U : Set E, IsUnionOfBalls (fun x x' : E => familyDistance e σ hσ x x') U ↔
          IsOpen[restrictTopology (familyTopology e) E] U) ∧
        IsMetrizableVia (restrictTopology (familyTopology e) E)
def ContinuousOfUniformLimit : Prop :=
  ∀ (Z : Type) (TZ : TopologicalSpace Z) (u : Z → ℝ) (v : ℕ+ → Z → ℝ),
    (∀ s, Continuous[TZ, inferInstance] (v s)) →
    Filter.Tendsto (fun s => ⨆ z, ENNReal.ofReal |u z - v s z|) Filter.atTop (𝓝 0) →
    Continuous[TZ, inferInstance] u
def TopologyProperties : Prop :=
  IsCoarsestMakingContinuous ∧
  ContinuousIffCoordsContinuous ∧
  (TendstoIffCoordsTendsto ∧ RealTendstoAgreement) ∧
  InducedEqRestrictedFamily ∧
  CountableSeparatingMetrization ∧
  ContinuousOfUniformLimit
end YangMills.Construction.FamilyTopology.Properties
end
