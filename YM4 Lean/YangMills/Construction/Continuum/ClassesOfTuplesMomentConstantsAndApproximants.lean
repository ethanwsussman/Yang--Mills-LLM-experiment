import YangMills.Construction.Continuum.SeparatingFamilyAndTheCoordinateMap
import YangMills.Construction.ReflectionPositiveLimits.NormsReflectionsCubesAndLatticesOfFourSpace
import YangMills.Construction.Torus.FunctionalsOnATorusAndFamiliesUnderABoundFunctionOnTorusOrFourSpace
import YangMills.Construction.Torus.LipschitzTuplesSeparationConcatenationAndTransport
import Mathlib
set_option autoImplicit false
open Filter
open scoped ENNReal Topology
noncomputable section
namespace YangMills.Construction.SeparatedClasses
section Classes
variable (s : Conventions.StandingParameters)
def PairwiseSupportSep {n : ℕ} (d : ℝ) (f : Fin n → AmbientPoints.Pt s .euclidean → ℝ) : Prop :=
  Pairwise fun i k =>
    ENNReal.ofReal d ≤ AmbientPoints.setDist s .euclidean (tsupport (f i)) (tsupport (f k))
def classOf (ϖ d R : ℝ) : Set (AmbientPoints.FunctionTuple s .euclidean) :=
  {X | X ∈ AmbientPoints.allSeparatedTuples s .euclidean ∧ AmbientPoints.IsSupportedInBalls R X.2 ∧
    (∀ i, tsupport (X.2 i) ⊆ ReflectionPositivity.centredCube (ϖ - d / 2)) ∧
    PairwiseSupportSep s d X.2}
end Classes
def momentConst (Cstar : ℕ → ℝ → ℝ → ℝ) (C₁ : ℝ → ℝ) (k : ℕ) (d R : ℝ) : ℝ :=
  ∑ I : Finset (Fin k), C₁ R ^ I.card *
    ∑ π ∈ TorusFunctionals.singletonFreePartitions Iᶜ, ∏ J ∈ π.parts, Cstar J.card d R
section Weights
variable (s : Conventions.StandingParameters) (M : ℕ) (Cstar : ℕ → ℝ → ℝ → ℝ) (C₁ : ℝ → ℝ)
  (d R : ℝ)
def momentWeight (X : AmbientPoints.FunctionTuple s .euclidean) : ℝ :=
  momentConst Cstar C₁ X.1 d R * ∏ i, TorusFunctionals.sharpNormAt s .euclidean M (X.2 i)
def momentWeightSq (X : AmbientPoints.FunctionTuple s .euclidean) : ℝ :=
  momentConst Cstar C₁ (2 * X.1) d R * ∏ i, TorusFunctionals.sharpNormAt s .euclidean M (X.2 i) ^ 2
end Weights
section Approximation
variable (s : Conventions.StandingParameters) (M : ℕ)
structure IsApproxSeqOn (X : AmbientPoints.FunctionTuple s .euclidean)
    (O : Fin X.1 → Set (AmbientPoints.Pt s .euclidean))
    (φ : ℕ → Fin X.1 → AmbientPoints.Pt s .euclidean → ℝ) : Prop where
  isOpen : ∀ i, IsOpen (O i)
  tsupport_subset : ∀ i, tsupport (X.2 i) ⊆ O i
  mem_separatingTuples : ∀ l, List.ofFn (φ l) ∈ SeparatingFamily.separatingTuples s.L
  tsupport_get_subset : ∀ l i, tsupport (φ l i) ⊆ O i
  tendsto : ∀ i,
    Tendsto (fun l => TorusFunctionals.sharpNormAt s .euclidean M (φ l i - X.2 i)) atTop (𝓝 0)
end Approximation
end YangMills.Construction.SeparatedClasses
end
