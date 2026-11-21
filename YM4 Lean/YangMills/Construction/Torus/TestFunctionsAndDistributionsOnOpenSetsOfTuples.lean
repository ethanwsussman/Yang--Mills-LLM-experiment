import YangMills.Construction.Torus.FunctionsOfSeveralPointsOfTorusOrFourSpace
import Mathlib
set_option autoImplicit false
open Filter
open YangMills.Construction.ReflectionPositivity.AxisMirror (Ambient)
open scoped ENNReal NNReal Topology
noncomputable section
namespace YangMills.Construction.AmbientPoints
variable {s : Conventions.StandingParameters} {E : Ambient} {p : ℕ}
def testFns (U : Set (Tuple s E p)) : Set (Tuple s E p → ℂ) :=
  {φ | IsSmoothFn φ ∧ IsCompact (closedSupport φ) ∧ closedSupport φ ⊆ U}
def TestFnTendsto (U : Set (Tuple s E p)) (φs : ℕ+ → Tuple s E p → ℂ)
    (φ : Tuple s E p → ℂ) : Prop :=
  (∀ t, φs t ∈ testFns U) ∧ φ ∈ testFns U ∧
    (∃ K, IsCompact K ∧ K ⊆ U ∧ closedSupport φ ⊆ K ∧ ∀ t, closedSupport (φs t) ⊆ K) ∧
    ∀ k : ℕ, Tendsto (fun t => cnNorm k (φs t - φ)) atTop (𝓝 0)
variable {U : Set (Tuple s E p)}
def IsComplexLinearForm (T : testFns U → ℂ) : Prop :=
  (∀ φ ψ χ : testFns U, χ.1 = φ.1 + ψ.1 → T χ = T φ + T ψ) ∧
    ∀ (c : ℂ) (φ χ : testFns U), χ.1 = c • φ.1 → T χ = c * T φ
def OrderBoundsOn (T : testFns U → ℂ) (K : Set (Tuple s E p)) (k : ℕ) : Prop :=
  ∃ C : ℝ≥0, ∀ φ : testFns U, closedSupport φ.1 ⊆ K →
    ENNReal.ofReal ‖T φ‖ ≤ (C : ℝ≥0∞) * cnNorm k φ.1
def IsDistrib (T : testFns U → ℂ) : Prop :=
  IsComplexLinearForm T ∧ ∀ K, IsCompact K → K ⊆ U → ∃ k, OrderBoundsOn T K k
def distribs (U : Set (Tuple s E p)) : Set (testFns U → ℂ) := {T | IsDistrib T}
def HasOrderLE (k₀ : ℕ) (T : testFns U → ℂ) : Prop :=
  IsDistrib T ∧ ∀ K, IsCompact K → K ⊆ U → OrderBoundsOn T K k₀
theorem testFns_mono {V : Set (Tuple s E p)} (h : V ⊆ U) : testFns V ⊆ testFns U :=
  fun _ hφ => ⟨hφ.1, hφ.2.1, hφ.2.2.trans h⟩
def restrictDistrib {V : Set (Tuple s E p)} (h : V ⊆ U) (T : testFns U → ℂ) :
    testFns V → ℂ :=
  fun φ => T ⟨φ.1, testFns_mono h φ.2⟩
def DenseInTestFns (U : Set (Tuple s E p)) (S : Set (Tuple s E p → ℂ)) : Prop :=
  S ⊆ testFns U ∧ ∀ φ ∈ testFns U, ∃ φs : ℕ+ → Tuple s E p → ℂ,
    (∀ t, φs t ∈ S) ∧ TestFnTendsto U φs φ
end YangMills.Construction.AmbientPoints
