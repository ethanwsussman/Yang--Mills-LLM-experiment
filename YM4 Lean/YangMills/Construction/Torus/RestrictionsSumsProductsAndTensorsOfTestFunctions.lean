import YangMills.Construction.Torus.GradientNormOfAFunctionOfOnePoint
import YangMills.Construction.Torus.TestFunctionsAndDistributionsOnOpenSetsOfTuples
import Mathlib
set_option autoImplicit false
open Filter
open scoped ENNReal Topology
noncomputable section
namespace YangMills.Construction.AmbientPoints
variable {s : Conventions.StandingParameters} {E : ReflectionPositivity.AxisMirror.Ambient} {p : ℕ}
def realPartFn (F : Tuple s E p → ℂ) : Tuple s E p → ℂ := fun y => ((F y).re : ℂ)
def imPartFn (F : Tuple s E p → ℂ) : Tuple s E p → ℂ := fun y => ((F y).im : ℂ)
def appendMultiIndex {p' : ℕ} (α : PowerSeries.MultiIndex (4 * p))
    (α' : PowerSeries.MultiIndex (4 * p')) : PowerSeries.MultiIndex (4 * (p + p')) :=
  fun j => Fin.append α α' (Fin.cast (Nat.mul_add 4 p p') j)
def prodTupleSets {p' : ℕ} (A : Set (Tuple s E p)) (B : Set (Tuple s E p')) :
    Set (Tuple s E (p + p')) :=
  {z | (fun i => z (Fin.castAdd p' i)) ∈ A ∧ (fun i => z (Fin.natAdd p i)) ∈ B}
def singletonTupleSet (O : Set (Pt s E)) : Set (Tuple s E 1) := {y | y 0 ∈ O}
def RestrictionFacts {Ω' Ω : Set (Tuple s E p)} (h : Ω' ⊆ Ω) : Prop :=
  testFns Ω' ⊆ testFns Ω ∧
    (∀ (Fs : ℕ+ → Tuple s E p → ℂ) (F : Tuple s E p → ℂ),
      TestFnTendsto Ω' Fs F → TestFnTendsto Ω Fs F) ∧
    ∀ T : testFns Ω → ℂ, IsDistrib T →
      IsDistrib (restrictDistrib h T) ∧
        ∀ ν₀ : ℕ, HasOrderLE ν₀ T → HasOrderLE ν₀ (restrictDistrib h T)
def DistribSeqContinuous (Ω : Set (Tuple s E p)) : Prop :=
  ∀ T : testFns Ω → ℂ, IsDistrib T →
    ∀ (Fs : ℕ+ → Tuple s E p → ℂ) (F : Tuple s E p → ℂ) (h : TestFnTendsto Ω Fs F),
      Tendsto (fun t => T ⟨Fs t, h.1 t⟩) atTop (𝓝 (T ⟨F, h.2.1⟩))
def LinearCombFacts (Ω : Set (Tuple s E p)) : Prop :=
  ∀ F ∈ testFns Ω, ∀ F' ∈ testFns Ω, ∀ b b' : ℂ,
    b • F + b' • F' ∈ testFns Ω ∧
      closedSupport (b • F + b' • F') ⊆ closedSupport F ∪ closedSupport F'
def PartsDerivNormFacts (Ω : Set (Tuple s E p)) : Prop :=
  ∀ F ∈ testFns Ω,
    (realPartFn F ∈ testFns Ω ∧ closedSupport (realPartFn F) ⊆ closedSupport F) ∧
      (imPartFn F ∈ testFns Ω ∧ closedSupport (imPartFn F) ⊆ closedSupport F) ∧
      (∀ α : PowerSeries.MultiIndex (4 * p),
        multiDeriv α F ∈ testFns Ω ∧ closedSupport (multiDeriv α F) ⊆ closedSupport F) ∧
      ∀ ν : ℕ, cnNorm ν F < ⊤
def SmoothMulFacts (Ω : Set (Tuple s E p)) : Prop :=
  ∀ φ F : Tuple s E p → ℂ, IsSmoothFn φ → IsSmoothFn F →
    IsSmoothFn (φ * F) ∧ closedSupport (φ * F) ⊆ closedSupport φ ∩ closedSupport F ∧
      (φ ∈ testFns Ω ∨ F ∈ testFns Ω → φ * F ∈ testFns Ω) ∧
      ∀ Ω'' : Set (Tuple s E p), IsOpen Ω'' → F ∈ testFns Ω → φ ∈ testFns Ω'' →
        φ * F ∈ testFns (Ω ∩ Ω'')
def TensorPairFacts {p' : ℕ} (F : Tuple s E p → ℂ) (H : Tuple s E p' → ℂ) : Prop :=
  IsSmoothFn (tensorPair F H) ∧
    (∀ (α : PowerSeries.MultiIndex (4 * p)) (α' : PowerSeries.MultiIndex (4 * p')),
      multiDeriv (appendMultiIndex α α') (tensorPair F H) =
        tensorPair (multiDeriv α F) (multiDeriv α' H)) ∧
    closedSupport (tensorPair F H) ⊆ prodTupleSets (closedSupport F) (closedSupport H) ∧
    ∀ ν : ℕ, cnNorm ν F ≠ ⊤ → cnNorm ν H ≠ ⊤ →
      cnNorm ν (tensorPair F H) ≤ cnNorm ν F * cnNorm ν H
def TensorProdFacts (O : Fin p → Set (Pt s E)) (φ : Fin p → Pt s E → ℂ) : Prop :=
  tensorProd φ ∈ testFns (Set.pi Set.univ O) ∧
    closedSupport (tensorProd φ) ⊆ Set.pi Set.univ fun i => tsupport (φ i)
def TestFnOperations : Prop :=
  ∀ (s : Conventions.StandingParameters) (E : ReflectionPositivity.AxisMirror.Ambient) (p : ℕ),
    1 ≤ p →
    (∀ (Ω' Ω : Set (Tuple s E p)) (h : Ω' ⊆ Ω), IsOpen Ω' → IsOpen Ω → RestrictionFacts h) ∧
    (∀ Ω : Set (Tuple s E p), IsOpen Ω →
      DistribSeqContinuous Ω ∧ LinearCombFacts Ω ∧ PartsDerivNormFacts Ω ∧ SmoothMulFacts Ω) ∧
    (∀ p' : ℕ, 1 ≤ p' → ∀ (F : Tuple s E p → ℂ) (H : Tuple s E p' → ℂ),
      IsSmoothFn F → IsSmoothFn H → TensorPairFacts F H) ∧
    ∀ (O : Fin p → Set (Pt s E)) (φ : Fin p → Pt s E → ℂ), (∀ i, IsOpen (O i)) →
      (∀ i, ofSinglePoint (φ i) ∈ testFns (singletonTupleSet (O i))) →
      TensorProdFacts O φ
end YangMills.Construction.AmbientPoints
end
