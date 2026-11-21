import YangMills.Construction.ReflectionPositivity.IsometriesCentringTuplesAndTheTwoFunctionals
import Mathlib
set_option autoImplicit false
open MeasureTheory
noncomputable section
namespace YangMills.Construction.ReflectionPositivity.CutoffMirrors
def CentredMomentCumulantExpansion : Prop :=
  (∀ (Ω : Type) [MeasurableSpace Ω] (ν : Measure Ω) [IsProbabilityMeasure ν] (q : ℕ), 1 ≤ q →
    ∀ x : Fin q → Ω → ℝ, Probability.AllBoundedRealRV x →
      (((∫ ω, ∏ l, (x l ω - ∫ ω', x l ω' ∂ν) ∂ν : ℝ)) : ℂ) =
        ∑ π ∈ SetPartition.singletonFree q, ∏ J ∈ π.parts,
          Probability.subfamilyCumulant ν x J) ∧
  ∀ (D : MirrorData) (q : ℕ) (h : Fin q → D.Torus → ℝ), MirrorData.IsAdmissibleArg (D := D) h →
    D.gibbsFunctional h =
        PeriodicLattice.gibbsExpectation D.L D.m D.K D.coupling
          (fun U => ∏ l, D.centredObservable (h l) U) ∧
      ((PeriodicLattice.gibbsExpectation D.L D.m D.K D.coupling
          (fun U => ∏ l, D.centredObservable (h l) U) : ℝ) : ℂ) = D.truncatedFunctional h
end YangMills.Construction.ReflectionPositivity.CutoffMirrors
end
