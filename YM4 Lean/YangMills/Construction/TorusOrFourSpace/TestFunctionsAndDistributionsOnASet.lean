import YangMills.Construction.TorusOrFourSpace.FunctionsOfSeveralPoints
import Mathlib
set_option autoImplicit false
open Filter
open scoped ENNReal NNReal Topology
noncomputable section
namespace YangMills.Construction.PeriodicSpace.Kind.Tuple
variable (D : Params) (E : Kind) {p : ℕ+}
def testFns (Ω : Set (E.Tuple D p)) : Set (E.Tuple D p → ℂ) :=
  {F | IsSmoothT D E F ∧ IsCompactT D E (supportT D E F) ∧ supportT D E F ⊆ Ω}
variable {D E} {Ω : Set (E.Tuple D p)}
def TendstoInTestFns (Fs : ℕ+ → testFns D E Ω) (F : testFns D E Ω) : Prop :=
  (∃ K, IsCompactT D E K ∧ K ⊆ Ω ∧ supportT D E F.1 ⊆ K ∧ ∀ t, supportT D E (Fs t).1 ⊆ K) ∧
    ∀ ν : ℕ, Tendsto (fun t => cNorm D E ν ((Fs t).1 - F.1)) atTop (𝓝 0)
def IsComplexLinearForm (T : testFns D E Ω → ℂ) : Prop :=
  (∀ F G H : testFns D E Ω, H.1 = F.1 + G.1 → T H = T F + T G) ∧
    ∀ (c : ℂ) (F H : testFns D E Ω), H.1 = c • F.1 → T H = c * T F
def HasOrderBoundOn (T : testFns D E Ω → ℂ) (K : Set (E.Tuple D p)) (ν : ℕ) : Prop :=
  ∃ C : ℝ≥0, ∀ F : testFns D E Ω, supportT D E F.1 ⊆ K →
    ENNReal.ofReal ‖T F‖ ≤ (C : ℝ≥0∞) * cNorm D E ν F.1
def IsDistrib (T : testFns D E Ω → ℂ) : Prop :=
  IsComplexLinearForm T ∧ ∀ K, IsCompactT D E K → K ⊆ Ω → ∃ ν, HasOrderBoundOn T K ν
def IsDistribOfOrderLE (ν₀ : ℕ) (T : testFns D E Ω → ℂ) : Prop :=
  IsDistrib T ∧ ∀ K, IsCompactT D E K → K ⊆ Ω → HasOrderBoundOn T K ν₀
def restrictDistrib {Ω' : Set (E.Tuple D p)} (h : Ω' ⊆ Ω) (T : testFns D E Ω → ℂ) :
    testFns D E Ω' → ℂ :=
  fun F => T ⟨F.1, F.2.1, F.2.2.1, F.2.2.2.trans h⟩
def DenseInTestFns (S : Set (testFns D E Ω)) : Prop :=
  ∀ F : testFns D E Ω, ∃ Fs : ℕ+ → testFns D E Ω,
    (∀ t, Fs t ∈ S) ∧ TendstoInTestFns Fs F
end YangMills.Construction.PeriodicSpace.Kind.Tuple
