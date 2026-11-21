import YangMills.Construction.Lattice.ObservablesAndTestNorms
import Mathlib
set_option autoImplicit false
open MeasureTheory Set
open scoped ENNReal
noncomputable section
namespace YangMills.Construction.TestFunctions
open YangMills.Construction.TorusMetric
def torusVolumeIntegral (ℓ : ℝ) (f : Torus4 ℓ → ℝ) : ℝ :=
  ∫ v in Set.pi univ fun _ : Fin 4 => Ico (0 : ℝ) ℓ, f (torusProj ℓ v)
section Class
variable {Y : Type*} [TopologicalSpace Y]
def IsShapedBump (dist : Y → Y → ℝ) (ball : Y → ℝ → Set Y) (integral : (Y → ℝ) → ℝ) (d ϑ : ℝ)
    (x : Y) (f : Y → ℝ) : Prop :=
  IsLipschitzFor dist f ∧ (∀ y, 0 ≤ f y) ∧ (∃ y, f y ≠ 0) ∧ tsupport f ⊆ ball x d ∧
    ϑ * uniformNorm f * d ^ 4 ≤ integral f ∧ bestLipschitzConstant dist f ≤ uniformNorm f / (ϑ * d)
def separatedPairs (dist : Y → Y → ℝ) (ball : Y → ℝ → Set Y) (setDist : Set Y → Set Y → ℝ≥0∞)
    (integral : (Y → ℝ) → ℝ) (d ϑ : ℝ) : Set ((Y → ℝ) × (Y → ℝ)) :=
  {p | ∃ x₁ x₂ : Y, IsShapedBump dist ball integral d ϑ x₁ p.1 ∧
    IsShapedBump dist ball integral d ϑ x₂ p.2 ∧
    ENNReal.ofReal d ≤ setDist (tsupport p.1) (tsupport p.2) ∧
    setDist (tsupport p.1) (tsupport p.2) ≤ ENNReal.ofReal (6 * d)}
end Class
def separatedPairsR4 (d ϑ : ℝ) : Set (((Fin 4 → ℝ) → ℝ) × ((Fin 4 → ℝ) → ℝ)) :=
  separatedPairs euclidDistR4 closedBallR4 setDistR4 (fun f => ∫ x, f x) d ϑ
def separatedPairsTorus (ℓ d ϑ : ℝ) : Set ((Torus4 ℓ → ℝ) × (Torus4 ℓ → ℝ)) :=
  separatedPairs euclidDistTorus closedBallTorus setEuclidDist (torusVolumeIntegral ℓ) d ϑ
def separatedPairsFourTorus (L m : ℕ) (d ϑ : ℝ) :
    Set ((YangMills.Construction.PeriodicLattice.FourTorus L m → ℝ) ×
      (YangMills.Construction.PeriodicLattice.FourTorus L m → ℝ)) :=
  separatedPairsTorus (YangMills.Construction.PeriodicLattice.torusSide L m) d ϑ
end YangMills.Construction.TestFunctions
