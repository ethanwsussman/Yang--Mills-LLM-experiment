import YangMills.Construction.Continuum.DistinctPointConfigs
import YangMills.Construction.Continuum.PointsDerivativesDiagonalsAndTheGradientSupremum
import YangMills.Construction.Continuum.SeparatedTuplesWithSmoothEntriesAndTheirSeparation
import YangMills.Construction.Continuum.TestFunctionsOfConfigurationSpace
import Mathlib
set_option autoImplicit false
open scoped ENNReal
namespace YangMills.Construction.ConfigurationSpace
def DiagonalsAndMinSeparationFacts (n : ℕ) : Prop :=
  (∀ i j : Fin n, i < j → ∃ W : Submodule ℝ (Config n),
    (W : Set (Config n)) = pairDiagonal i j ∧ Module.finrank ℝ (Config n ⧸ W) = 4) ∧
  (∀ x : Config n, minSeparation x ≠ ⊤) ∧
  (∀ x y : Config n,
    |(minSeparation x).toReal - (minSeparation y).toReal| ≤ 2 * configMaxNorm (x - y)) ∧
  fatDiagonal n = {x | minSeparation x = 0} ∧
  IsClosed (fatDiagonal n)
def WeightComparison (n : ℕ) : Prop :=
  ∀ x : Config n,
    (1 + configNorm x ^ 2) ^ (1 / 2 : ℝ) ≤ 1 + configNorm x ∧
    1 + configNorm x ≤ Real.sqrt 2 * (1 + configNorm x ^ 2) ^ (1 / 2 : ℝ)
def SeminormComparison (n : ℕ) : Prop :=
  ∀ φ ∈ schwartzSet n, ∀ k q m : ℕ,
    (max k q ≤ m →
      decaySeminorm k q φ ≤ ENNReal.ofReal (2 ^ ((k : ℝ) / 2)) * sobolevWeightNorm m φ) ∧
    sobolevWeightNorm m φ ≤ decaySeminorm m m φ ∧
    (k ≤ m → sobolevWeightNorm k φ ≤ sobolevWeightNorm m φ)
def DualBoundedByWeightNorms (n : ℕ) : Prop :=
  ∀ S : flatSchwartzSet n → ℂ, IsLinearOnFlatSchwartz S →
    (S ∈ flatSchwartzDualSet n ↔ ∃ (m : ℕ) (b : ℝ), 0 ≤ b ∧
      ∀ φ : flatSchwartzSet n,
        ENNReal.ofReal ‖S φ‖ ≤ ENNReal.ofReal b * sobolevWeightNorm m φ.1)
def AgreesWithTestSpaces (n : ℕ) : Prop :=
  schwartzSet n = TestSpaces.schwartzSet n ∧
  (∀ φ ∈ schwartzSet n, ∀ m : ℕ, 1 ≤ m →
    sobolevWeightNorm m φ = TestSpaces.weightedSeminorm m φ) ∧
  flatSchwartzSet n = TestSpaces.flatSchwartzSet n
def FlatSchwartzClosedSubspace (n : ℕ) : Prop :=
  flatSchwartzSet n ⊆ schwartzSet n ∧
  IsLinearFunctionSet (flatSchwartzSet n) ∧
  (∀ (ψ : ℕ → Config n → ℂ) (φ : Config n → ℂ), (∀ j, ψ j ∈ flatSchwartzSet n) →
    φ ∈ schwartzSet n →
    (∀ m : ℕ, Filter.Tendsto (fun j => sobolevWeightNorm m (ψ j - φ)) Filter.atTop (nhds 0)) →
    φ ∈ flatSchwartzSet n) ∧
  offDiagonalTestSet n ⊆ flatSchwartzSet n
def TensorsOffDiagonal (n : ℕ) : Prop :=
  ∀ f ∈ SmoothSepR4.smoothSepR4 n,
    ofRealFun (TestSpaces.tensorProd f) ∈ offDiagonalTestSet n
def LipschitzConstEqGradSup (f : (Fin 4 → ℝ) → ℝ) : Prop :=
  TestFunctions.IsLipschitzFor TestFunctions.euclidDistR4 f ∧
  ENNReal.ofReal (TestFunctions.lipConstR4 f) = ConfigGradients.gradSup f ∧
  ∀ M : ℝ, TestFunctions.sharpNormR4 M f =
    max (TestFunctions.uniformNorm f)
      (40 * M * (ConfigGradients.gradSup f).toReal)
def ConfigSpaceTestFunctionFacts : Prop :=
  (∀ n : ℕ, 1 ≤ n →
    (2 ≤ n → DiagonalsAndMinSeparationFacts n) ∧
    distinctConfigs n = (fatDiagonal n)ᶜ ∧
    WeightComparison n ∧
    SeminormComparison n ∧
    DualBoundedByWeightNorms n ∧
    AgreesWithTestSpaces n ∧
    FlatSchwartzClosedSubspace n ∧
    TensorsOffDiagonal n) ∧
  ∀ f ∈ (TestSpaces.c1CompactSupp Set.univ : Set ((Fin 4 → ℝ) → ℝ)),
    LipschitzConstEqGradSup f
end YangMills.Construction.ConfigurationSpace
