import YangMills.Construction.Torus.TestFunctionsAndDistributionsOnOpenSetsOfTuples
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction
open ReflectionPositivity.AxisMirror (Ambient)
namespace AmbientPoints
variable {s : Conventions.StandingParameters} {E : Ambient} {p : ℕ}
def IsUnitIntervalValued (φ : Tuple s E p → ℂ) : Prop :=
  ∀ y, ∃ t ∈ Icc (0 : ℝ) 1, φ y = (t : ℂ)
def SmoothPartitionOfUnityStatement : Prop :=
  ∀ (s : Conventions.StandingParameters) (E : Ambient) (p : ℕ), 1 ≤ p →
    (∀ (r : ℕ), 1 ≤ r → ∀ (K : Set (Tuple s E p)) (W : Fin r → Set (Tuple s E p)),
      IsCompact K → (∀ a, IsOpen (W a)) → K ⊆ ⋃ a, W a →
      ∃ φ : Fin r → Tuple s E p → ℂ,
        (∀ a, φ a ∈ testFns (W a)) ∧ (∀ a, IsUnitIntervalValued (φ a)) ∧
        ∃ N : Set (Tuple s E p), IsNhdOfSet N K ∧ ∀ y ∈ N, ∑ a, φ a y = 1) ∧
    ∀ (K W : Set (Tuple s E p)), IsCompact K → IsOpen W → K ⊆ W →
      ∃ φ : Tuple s E p → ℂ,
        φ ∈ testFns W ∧ IsUnitIntervalValued φ ∧
        ∃ N : Set (Tuple s E p), IsNhdOfSet N K ∧ ∀ y ∈ N, φ y = 1
end AmbientPoints
end YangMills.Construction
