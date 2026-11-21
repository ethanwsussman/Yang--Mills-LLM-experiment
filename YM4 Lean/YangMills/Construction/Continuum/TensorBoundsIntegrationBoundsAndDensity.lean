import YangMills.Construction.Continuum.OpenHalvesAndFlatnessOutsideAnOpenSet
import YangMills.Construction.Continuum.TensorProductsAndIntegrationOverArguments
import Mathlib
set_option autoImplicit false
open MeasureTheory Set
open scoped ENNReal
noncomputable section
namespace YangMills.Construction.TestSpaces
namespace TestSpaceFacts
def TensorProductBound : Prop :=
  ∀ q q' k : ℕ, 0 < q → 0 < q' → 0 < k →
    ∀ φ ∈ schwartzSet q, ∀ ψ ∈ schwartzSet q',
      tensorFun φ ψ ∈ schwartzSet (q + q') ∧
      weightedSeminorm k (tensorFun φ ψ) ≤ weightedSeminorm k φ * weightedSeminorm k ψ ∧
      (VanishesToInfiniteOrderOff φ (negativeTimeLocus q) →
        VanishesToInfiniteOrderOff ψ (positiveTimeLocus q') →
        tensorFun φ ψ ∈ flatSchwartzSet (q + q'))
def ScalarTensorBound : Prop :=
  ∀ q' k : ℕ, 0 < q' → 0 < k → ∀ c : ℂ, ∀ ψ ∈ schwartzSet q',
    weightedSeminorm k (scalarTensorLeft c ψ) = ENNReal.ofReal ‖c‖ * weightedSeminorm k ψ
def IntegrateOutBound : Prop :=
  ∀ n k : ℕ, 0 < n → 4 < k → ∀ φ ∈ flatSchwartzSet n, ∀ A : Finset (Fin n),
    (A.card < n →
      (1 ≤ A.card → ∀ y : PointTuple (n - A.card), y ∈ integrableFibers A φ) ∧
      integrateOut A φ ∈ flatSchwartzSet (n - A.card) ∧
      weightedSeminorm (k * (n - A.card)) (integrateOut A φ) ≤
        weightIntegral k ^ A.card * weightedSeminorm (k * n) φ) ∧
    Integrable φ ∧
    ENNReal.ofReal ‖∫ x, φ x‖ ≤ weightIntegral k ^ n * weightedSeminorm (k * n) φ
def tensorCombination {n m : ℕ} (c : Fin m → ℂ) (f : Fin m → Fin n → (Fin 4 → ℝ) → ℝ) :
    PointTuple n → ℂ :=
  fun x => ∑ ι, c ι * ((tensorProd (f ι) x : ℝ) : ℂ)
def IsNearTensorCombination {n : ℕ} (O : Set (Fin 4 → ℝ)) (k : ℕ) (φ : PointTuple n → ℂ)
    (ε : ℝ) {m : ℕ} (c : Fin m → ℂ) (f : Fin m → Fin n → (Fin 4 → ℝ) → ℝ) : Prop :=
  0 < m ∧ (∀ ι, f ι ∈ disjointSupportTuples O n ∧ HasSmoothComponents O (f ι)) ∧
    weightedSeminorm k (φ - tensorCombination c f) ≤ ENNReal.ofReal ε
def TensorDenseAt {n : ℕ} (V : Set (PointTuple n)) (O : Set (Fin 4 → ℝ)) (k : ℕ) : Prop :=
  ∀ φ ∈ schwartzSet n, VanishesToInfiniteOrderOff φ V → ∀ ε : ℝ, 0 < ε →
    (∃ (m : ℕ) (c : Fin m → ℂ) (f : Fin m → Fin n → (Fin 4 → ℝ) → ℝ),
      IsNearTensorCombination O k φ ε c f) ∧
    ((∀ x, (φ x).im = 0) →
      ∃ (m : ℕ) (c : Fin m → ℝ) (f : Fin m → Fin n → (Fin 4 → ℝ) → ℝ),
        IsNearTensorCombination O k φ ε (fun ι => (c ι : ℂ)) f)
def TensorDensity : Prop :=
  ∀ n k : ℕ, 0 < n → 0 < k →
    TensorDenseAt (distinctLocus n) univ k ∧ TensorDenseAt (positiveTimeLocus n) upperHalfSpace k
end TestSpaceFacts
open TestSpaceFacts in
def TestSpaceFacts.Statement : Prop :=
  TensorProductBound ∧ ScalarTensorBound ∧ IntegrateOutBound ∧ TensorDensity
end YangMills.Construction.TestSpaces
