import YangMills.Construction.Conventions.StandingParameters
import YangMills.Construction.Cumulants.TupleGeneratingFunctionAndItsLogarithm
import YangMills.Construction.Lattice.SourcesAndGeneratingFunction
import Mathlib
set_option autoImplicit false
open MeasureTheory Set
open scoped ENNReal
noncomputable section
namespace YangMills.Construction
namespace LatticeProbability
open Cumulants Cumulants.TupleLogMGF
variable (s : Conventions.StandingParameters)
abbrev GaugeConfig : Type := ↥(PeriodicLattice.compactGaugeFields s.L s.m ((s.K : ℕ) : ℤ))
abbrev Plaq : Type := PeriodicLattice.Plaquette s.L s.m ((s.K : ℕ) : ℤ)
def haarMeasureOn : Measure (GaugeConfig s) :=
  (PeriodicLattice.productHaarMeasure s.L s.m ((s.K : ℕ) : ℤ)).comap Subtype.val
def gibbsMeasureOn (β : ℝ) : Measure (GaugeConfig s) :=
  (PeriodicLattice.wilsonGibbsMeasure s.L s.m s.K β).comap Subtype.val
def plaquetteEnergyOn (p : Plaq s) : GaugeConfig s → ℝ :=
  fun U => PeriodicLattice.plaquetteCost U.1 p
def observableOn (f : s.Torus → ℝ) : GaugeConfig s → ℝ :=
  fun U => PeriodicLattice.smearedObservable f U.1
variable {n : ℕ}
def observableVector (f : Fin n → s.Torus → ℝ) : Fin n → GaugeConfig s → ℝ :=
  fun i => observableOn s (f i)
def cumulantOfObservables (β : ℝ) (f : Fin n → s.Torus → ℝ) : ℂ :=
  PeriodicLattice.gibbsCumulant s.L s.m s.K β fun i => PeriodicLattice.smearedObservable (f i)
def expectationExpSum (β : ℝ) (f : Fin n → s.Torus → ℝ) :
    Coordinates.ComplexCoordinates n → ℂ :=
  fun z => PeriodicLattice.gibbsExpectation s.L s.m s.K β
    (ComplexVariables.expComp fun U =>
      ∑ i, z i * ((PeriodicLattice.smearedObservable (f i) U : ℝ) : ℂ))
def GibbsIsProbabilitySpace (β : ℝ) : Prop :=
  (inferInstance : MeasurableSpace (GaugeConfig s)) = borel (GaugeConfig s) ∧
  gibbsMeasureOn s β =
    (ENNReal.ofReal (PeriodicLattice.partitionFunction s.L s.m s.K β))⁻¹ •
      (haarMeasureOn s).withDensity
        (fun U => ENNReal.ofReal (PeriodicLattice.boltzmannWeight β U.1)) ∧
  IsProbabilityMeasure (gibbsMeasureOn s β) ∧
  (∀ F : GaugeConfig s → ℂ, Probability.IsBoundedComplexRV F ↔
    Measurable[borel (GaugeConfig s)] F ∧ TestFunctions.IsBoundedFun F) ∧
  (∀ F : GaugeConfig s → ℂ, Probability.IsBoundedComplexRV F →
    Probability.complexExpectation (gibbsMeasureOn s β) F =
      ((PeriodicLattice.partitionFunction s.L s.m s.K β : ℝ) : ℂ)⁻¹ *
        ∫ U, F U * ((PeriodicLattice.boltzmannWeight β U.1 : ℝ) : ℂ) ∂haarMeasureOn s) ∧
  ∀ G : (PeriodicLattice.Bond s.L s.m ((s.K : ℕ) : ℤ) → Matrices.ComplexMatrix2) → ℂ,
    Probability.IsBoundedComplexRV (fun U : GaugeConfig s => G U.1) →
      PeriodicLattice.gibbsExpectation s.L s.m s.K β G =
        Probability.complexExpectation (gibbsMeasureOn s β) fun U => G U.1
def PlaquetteEnergyBoundedRV : Prop :=
  Finite (Plaq s) ∧
  ∀ p : Plaq s,
    Continuous (plaquetteEnergyOn s p) ∧
    (∀ U, 0 ≤ plaquetteEnergyOn s p U ∧ plaquetteEnergyOn s p U ≤ 2) ∧
    Probability.IsBoundedRealRV (plaquetteEnergyOn s p)
def LipschitzImpliesBounded (E : Type*) [NormedAddCommGroup E] : Prop :=
  ∀ g : s.Torus → E, TestFunctions.IsLipschitzFor TestFunctions.euclidDistTorus g →
    TestFunctions.IsBoundedFun g ∧
      ∀ x y : s.Torus, ‖g x‖ ≤ ‖g y‖ + s.side * TestFunctions.lipConstTorus g
def DistBoundedBySide : Prop :=
  (∀ x y : s.Torus, TestFunctions.euclidDistTorus x y ≤ s.side) ∧
    LipschitzImpliesBounded s ℝ ∧ LipschitzImpliesBounded s ℂ
def ObservablesBoundedRV : Prop :=
  (∀ f : s.Torus → ℝ, Probability.IsBoundedRealRV (observableOn s f)) ∧
  (∀ f g : s.Torus → ℝ, (∀ p : Plaq s, f p.barycenter = g p.barycenter) →
    observableOn s f = observableOn s g) ∧
  (∃ (B : Submodule ℝ (GaugeConfig s → ℝ)) (T : (s.Torus → ℝ) →ₗ[ℝ] B),
    (B : Set (GaugeConfig s → ℝ)) = {X | Probability.IsBoundedRealRV X} ∧
    ∀ f, ((T f : B) : GaugeConfig s → ℝ) = observableOn s f) ∧
  ∃ (V : Submodule ℝ (s.Torus → ℝ)) (B : Submodule ℝ (GaugeConfig s → ℝ)) (T : V →ₗ[ℝ] B),
    (V : Set (s.Torus → ℝ)) =
      {f | TestFunctions.IsLipschitzFor TestFunctions.euclidDistTorus f} ∧
    (B : Set (GaugeConfig s → ℝ)) = {X | Probability.IsBoundedRealRV X} ∧
    ∀ f : V, ((T f : B) : GaugeConfig s → ℝ) = observableOn s f.1
def CumulantEqMixedCumulant (β : ℝ) (f : Fin n → s.Torus → ℝ) : Prop :=
  cumulantOfObservables s β f =
    mixedCumulant (gibbsMeasureOn s β) (observableVector s f) ∧
  ComplexVariables.HasPartialOverFinset
    (logDomain (gibbsMeasureOn s β) (observableVector s f)) Finset.univ
    (fun z => ComplexVariables.logPrincipal (expectationExpSum s β f z)) ∧
  cumulantOfObservables s β f = ComplexVariables.mixedPartialAtOrigin
    (fun z => ComplexVariables.logPrincipal (expectationExpSum s β f z)) ∧
  HasIteratedRealPartial
    (logDomain (gibbsMeasureOn s β) (observableVector s f) ∩
      Coordinates.ComplexCoordinates.realLocus n)
    (List.finRange n)
    (realLogTupleMGF (gibbsMeasureOn s β) (observableVector s f)) ∧
  cumulantOfObservables s β f = iteratedRealPartial (List.finRange n)
    (realLogTupleMGF (gibbsMeasureOn s β) (observableVector s f)) 0
def GeneratingFunctionRatio (β : ℝ) (f : Fin n → s.Torus → ℝ) : Prop :=
  (∀ z : Coordinates.ComplexCoordinates n,
    tupleMomentGeneratingFunction (gibbsMeasureOn s β) (observableVector s f) z =
      PeriodicLattice.generatingFunction s.L s.m s.K β f z /
        PeriodicLattice.generatingFunction s.L s.m s.K β f 0) ∧
  PeriodicLattice.generatingFunction s.L s.m s.K β f 0 =
    ((PeriodicLattice.partitionFunction s.L s.m s.K β : ℝ) : ℂ)
def LogGeneratingFunctionCumulant (β : ℝ) (f : Fin n → s.Torus → ℝ) : Prop :=
  ComplexVariables.IsEntireFun (PeriodicLattice.generatingFunction s.L s.m s.K β f) ∧
  (∀ z ∈ logDomain (gibbsMeasureOn s β) (observableVector s f),
    PeriodicLattice.generatingFunction s.L s.m s.K β f z ∈
        ComplexVariables.nonpositiveRayComplement ∧
      ComplexVariables.logPrincipal (PeriodicLattice.generatingFunction s.L s.m s.K β f z) =
        ((Real.log (PeriodicLattice.partitionFunction s.L s.m s.K β) : ℝ) : ℂ) +
          logMomentGeneratingFunction (gibbsMeasureOn s β) (observableVector s f) z) ∧
  ComplexVariables.HasPartialOverFinset
    (logDomain (gibbsMeasureOn s β) (observableVector s f)) Finset.univ
    (fun z => ComplexVariables.logPrincipal
      (PeriodicLattice.generatingFunction s.L s.m s.K β f z)) ∧
  cumulantOfObservables s β f = ComplexVariables.mixedPartialAtOrigin
    (fun z => ComplexVariables.logPrincipal
      (PeriodicLattice.generatingFunction s.L s.m s.K β f z))
namespace ProbabilitySpaceTheorem
def claim : Prop :=
  ∀ (s : Conventions.StandingParameters) (β : ℝ), 0 < β →
    GibbsIsProbabilitySpace s β ∧
    PlaquetteEnergyBoundedRV s ∧
    DistBoundedBySide s ∧
    ObservablesBoundedRV s ∧
    (∀ (n : ℕ) (f : Fin n → s.Torus → ℝ), 1 ≤ n → CumulantEqMixedCumulant s β f) ∧
    ∀ (n : ℕ) (f : Fin n → s.Torus → ℝ), 1 ≤ n →
      (∀ i, TestFunctions.IsLipschitzFor TestFunctions.euclidDistTorus (f i)) →
        GeneratingFunctionRatio s β f ∧
          LogGeneratingFunctionCumulant s β f
end ProbabilitySpaceTheorem
end LatticeProbability
end YangMills.Construction
end
