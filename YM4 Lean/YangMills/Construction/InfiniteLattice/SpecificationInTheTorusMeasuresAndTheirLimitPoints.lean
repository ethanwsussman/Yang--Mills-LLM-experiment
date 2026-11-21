import YangMills.Construction.InfiniteLattice.PeriodicExtensionsStatesAndTorusFunctionalsAtOneSpacing
import YangMills.Construction.InfiniteLattice.SpecificationDensitiesAndTheDensityDistanceAtOneSpacing
import YangMills.Construction.Probability.BoundedComplexExpectation
import Mathlib
set_option autoImplicit false
open MeasureTheory Set Filter
noncomputable section
namespace YangMills.Construction.FixedSpacing
open YangMills.Construction.InfiniteLattice YangMills.Construction.GibbsAtFixedSpacing
namespace Setup
variable (D : Setup) (Λ : LinkWindow D.mesh)
def DensityLocalityAndBounds : Prop :=
  FactorsThroughFinite ((Λ.links : Set (Link D.mesh)) ∪ Λ.rim)
      (fun U => (D.localAction Λ U : ℂ)) ∧
    FactorsThroughFinite Λ.rim (fun U' => (D.localPartition Λ U' : ℂ)) ∧
    (∃ φ : Λ.Assignments × LinkVariables Λ.rim → ℝ, Continuous φ ∧
      ∀ (V : Λ.Assignments) (U' : D.Fields),
        D.conditionalDensity Λ V U' = φ (V, restrictField U' Λ.rim)) ∧
    (∀ (V : Λ.Assignments) (U' : D.Fields),
      Real.exp (-(2 * D.β * (Λ.faceCount : ℝ))) ≤ D.conditionalDensity Λ V U' ∧
        D.conditionalDensity Λ V U' ≤ Real.exp (2 * D.β * (Λ.faceCount : ℝ))) ∧
    ∀ U' : D.Fields, ∫ V, D.conditionalDensity Λ V U' ∂Λ.haarProd = 1
def DensityIsWilsonKernel : Prop :=
  ∀ U' : D.Fields,
    Λ.haarProd.withDensity (fun V => ENNReal.ofReal (D.conditionalDensity Λ V U')) =
      InfiniteLattice.wilsonSpecification D.β Λ.links U'
def KernelPreservesLocal : Prop :=
  (∀ F ∈ finiteLinkFunctions D.mesh, D.conditionalKernel Λ F ∈ finiteLinkFunctions D.mesh) ∧
    ∀ (A : Set (Link D.mesh)) (F : D.Fields → ℂ), FactorsThroughFinite A F →
      FactorsThroughFinite (Λ.rim ∪ (A \ (Λ.links : Set (Link D.mesh)))) (D.conditionalKernel Λ F)
def LiftedGibbsDLR : Prop :=
  ∀ (A : Set (Link D.mesh)) (F : D.Fields → ℂ), FactorsThroughFinite A F →
    ∀ r : ℝ, 0 ≤ r →
      (∀ e ∈ (Λ.links : Set (Link D.mesh)) ∪ A,
        (e.initial : AmbientSpace) ∈ closedCube r ∧ (e.terminal : AmbientSpace) ∈ closedCube r) →
      r + D.mesh < D.side / 2 →
      YangMills.Construction.Probability.complexExpectation D.liftedGibbs (D.conditionalKernel Λ F) =
        YangMills.Construction.Probability.complexExpectation D.liftedGibbs F
def SatisfiesDLR (ν : Measure D.Fields) : Prop :=
  ∀ Λ : LinkWindow D.mesh,
    (∀ F ∈ finiteLinkFunctions D.mesh,
      YangMills.Construction.Probability.complexExpectation ν (D.conditionalKernel Λ F) =
        YangMills.Construction.Probability.complexExpectation ν F) ∧
    ∀ F : D.Fields → ℂ, IsBoundedObservable F →
      IsBoundedObservable (D.conditionalKernel Λ F) ∧
        YangMills.Construction.Probability.complexExpectation ν (D.conditionalKernel Λ F) =
          YangMills.Construction.Probability.complexExpectation ν F
def TorusLimitsSubsequential : Prop :=
  ∀ n : ℕ → ℕ+, Tendsto (fun i => (D.withExponent (n i)).side) atTop atTop →
    ∃ (φ : ℕ → ℕ) (ρ : ℕ → BorelProb D.mesh) (ρ' : BorelProb D.mesh), StrictMono φ ∧
      (∀ i, (ρ i).1 = (D.withExponent (n (φ i))).liftedGibbs) ∧
      ρ'.1 ∈ D.torusLimits ∧ BorelProb.TendstoWeak ρ ρ'
end Setup
def TorusSpecification.Statement : Prop :=
  ∀ D : Setup,
    (∀ Λ : LinkWindow D.mesh,
      D.DensityLocalityAndBounds Λ ∧ D.DensityIsWilsonKernel Λ ∧
        D.KernelPreservesLocal Λ ∧ D.LiftedGibbsDLR Λ) ∧
    D.torusLimits.Nonempty ∧ D.TorusLimitsSubsequential ∧
    (∀ ν ∈ D.torusLimits, D.SatisfiesDLR ν ∧ IsShiftInvariant ν) ∧
    IsShiftInvariant D.liftedGibbs ∧
    D.torusLimits ⊆ D.periodicGibbsSet
end YangMills.Construction.FixedSpacing
