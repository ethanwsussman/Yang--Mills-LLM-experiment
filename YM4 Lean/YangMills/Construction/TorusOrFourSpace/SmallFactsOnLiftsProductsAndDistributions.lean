import YangMills.Construction.TorusOrFourSpace.ClassesOfFunctionsWithSupportInASet
import YangMills.Construction.TorusOrFourSpace.QuarterSideOpenBallsDistinctPointsAndBoundedFamilies
import YangMills.Construction.TorusOrFourSpace.TestFunctionsAndDistributionsOnASet
import Mathlib
set_option autoImplicit false
open Filter
open scoped ENNReal Topology
noncomputable section
namespace YangMills.Construction.PeriodicSpace.LiftsProductsDistributions
open Kind.Tuple
open TorusMetric (euclidNormVec)
variable (D : Params) (E : Kind)
def QuotMapDistLE : Prop :=
  ∀ x x' : Fin 4 → ℝ,
    E.quotDist D (E.quotMap D x) (E.quotMap D x') ≤ euclidNormVec (x - x') ∧
      (ENNReal.ofReal (euclidNormVec (x - x')) < 2 * E.periodQuarter D →
        E.quotDist D (E.quotMap D x) (E.quotMap D x') = euclidNormVec (x - x'))
def ExistsLiftAtDist : Prop :=
  ∀ (x : Fin 4 → ℝ) (y : E.Pt D),
    ∃ x', Kind.IsLift D E y x' ∧ euclidNormVec (x - x') = E.quotDist D (E.quotMap D x) y
def LeibnizBound (p : ℕ+) (ν : ℕ) : Prop :=
  ∀ F H : E.Tuple D p → ℂ, IsClassC D E ν F → IsClassC D E ν H →
    cNorm D E ν F < ⊤ → cNorm D E ν H < ⊤ →
      cNorm D E ν (F * H) ≤ 2 ^ ν * cNorm D E ν F * cNorm D E ν H
def ReImC1NormLE : Prop :=
  ∀ g : E.Pt D → ℂ, IsClassC D E 1 (ofSingle D E g) → c1NormSingle D E g < ⊤ →
    c1NormSingleReal D E (fun y => (g y).re) ≤ c1NormSingle D E g ∧
      c1NormSingleReal D E (fun y => (g y).im) ≤ c1NormSingle D E g
def C1ClassLipschitz : Prop :=
  ∀ g ∈ Kind.c1SupportedIn D E Set.univ,
    Kind.IsLipschitzQ D E g ∧
      ENNReal.ofReal (Kind.lipConstQ D E g) ≤ 2 * c1NormSingleReal D E g ∧
      Kind.sharpNormQ D E g ≤ ENNReal.ofReal (80 * D.M) * c1NormSingleReal D E g
def RestrictDistrib (p : ℕ+) : Prop :=
  ∀ U' U : Set (E.Tuple D p), IsOpenT D E U' → IsOpenT D E U →
    ∀ (hsub : U' ⊆ U) (T : testFns D E U → ℂ), IsDistrib T →
      testFns D E U' ⊆ testFns D E U ∧
        IsDistrib (restrictDistrib hsub T) ∧
        ∀ k : ℕ, IsDistribOfOrderLE k T →
          IsDistribOfOrderLE k (restrictDistrib hsub T)
def DistribSeqContinuous (p : ℕ+) : Prop :=
  ∀ U : Set (E.Tuple D p), IsOpenT D E U →
    ∀ T : testFns D E U → ℂ, IsDistrib T →
      ∀ (Fs : ℕ+ → testFns D E U) (F : testFns D E U),
        TendstoInTestFns Fs F → Tendsto (fun t => T (Fs t)) atTop (𝓝 (T F))
def Statement : Prop :=
  ∀ (D : Params) (E : Kind),
    QuotMapDistLE D E ∧
    ExistsLiftAtDist D E ∧
    (∀ (p : ℕ+) (ν : ℕ), LeibnizBound D E p ν) ∧
    ReImC1NormLE D E ∧
    C1ClassLipschitz D E ∧
    (∀ p : ℕ+, RestrictDistrib D E p) ∧
    (∀ p : ℕ+, DistribSeqContinuous D E p)
end YangMills.Construction.PeriodicSpace.LiftsProductsDistributions
