import YangMills.Construction.EuclideanFunctionals.SymmetricEuclideanFunctional
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.EuclideanFunctionals
open ReflectionPositivity.AxisMirror EuclideanSpectral
def IsEntrywiseLinear (σ : sepAll → ℝ) : Prop :=
  ∀ (n : ℕ) (f : Fin n → R4 → ℝ) (i : Fin n) (g : R4 → ℝ), g ≠ f i →
    List.ofFn f ∈ sepAll → List.ofFn (Function.update f i g) ∈ sepAll → ∀ a a' : ℝ,
      Ambient.evalOrZero σ (List.ofFn (Function.update f i (a • f i + a' • g))) =
        a * Ambient.evalOrZero σ (List.ofFn f) +
          a' * Ambient.evalOrZero σ (List.ofFn (Function.update f i g))
def realTensor {n : ℕ} (f : Fin n → R4 → ℝ) : TestSpaces.PointTuple n → ℂ :=
  tensorOfFns fun l x => (f l x : ℂ)
def combTensor {n : ℕ} {ι : Type} (B : Finset ι) (z : ι → ℂ)
    (f : ι → Fin n → R4 → ℝ) : TestSpaces.PointTuple n → ℂ :=
  ∑ b ∈ B, z b • realTensor (f b)
def combValue (σ : sepAll → ℝ) {n : ℕ} {ι : Type} (B : Finset ι) (z : ι → ℂ)
    (f : ι → Fin n → R4 → ℝ) : ℂ :=
  ∑ b ∈ B, z b * (Ambient.evalOrZero σ (List.ofFn (f b)) : ℂ)
def tupleTensorSpan (n : ℕ) : Submodule ℂ (TestSpaces.PointTuple n → ℂ) :=
  Submodule.span ℂ
    {T | ∃ f : Fin n → R4 → ℝ, List.ofFn f ∈ sepN n ∧ T = realTensor f}
theorem combTensor_mem_sepTensorSpan {n : ℕ} {ι : Type} {B : Finset ι} (z : ι → ℂ)
    {f : ι → Fin n → R4 → ℝ} (hf : ∀ b ∈ B, List.ofFn (f b) ∈ sepN n) :
    combTensor B z f ∈ tupleTensorSpan n :=
  Submodule.sum_mem _ fun b hb =>
    Submodule.smul_mem _ _ (Submodule.subset_span ⟨f b, hf b hb, rfl⟩)
namespace TensorValues
def VanishesOnZeroTensor (σ : sepAll → ℝ) : Prop :=
  ∀ n : ℕ, 1 ≤ n → ∀ {ι : Type} (B : Finset ι) (z : ι → ℂ) (f : ι → Fin n → R4 → ℝ),
    (∀ b ∈ B, List.ofFn (f b) ∈ sepN n) →
      combTensor B z f = 0 → combValue σ B z f = 0
def FactorsThroughTensor (σ : sepAll → ℝ) : Prop :=
  ∀ n : ℕ, 1 ≤ n → ∀ {ι ι' : Type} (B : Finset ι) (B' : Finset ι') (z : ι → ℂ) (z' : ι' → ℂ)
    (f : ι → Fin n → R4 → ℝ) (f' : ι' → Fin n → R4 → ℝ),
    (∀ b ∈ B, List.ofFn (f b) ∈ sepN n) →
      (∀ b ∈ B', List.ofFn (f' b) ∈ sepN n) →
        combTensor B z f = combTensor B' z' f' →
          combValue σ B z f = combValue σ B' z' f'
def EqOnEqualTopComponent (σ : sepAll → ℝ) : Prop :=
  ∀ n : ℕ, 1 ≤ n → ∀ F ∈ combSpan n, ∀ F' ∈ combSpan n,
    tensorComp n F = tensorComp n F' → liftReal σ F = liftReal σ F'
def IsLinearOnSpan (σ : sepAll → ℝ) : Prop :=
  ∀ n : ℕ, 1 ≤ n → ∃ φ : tupleTensorSpan n →ₗ[ℂ] ℂ,
    ∀ {ι : Type} (B : Finset ι) (z : ι → ℂ) (f : ι → Fin n → R4 → ℝ)
      (hf : ∀ b ∈ B, List.ofFn (f b) ∈ sepN n),
      φ ⟨combTensor B z f, combTensor_mem_sepTensorSpan z hf⟩ = combValue σ B z f
def AgreesOnSameTensors (σ : sepAll → ℝ) : Prop :=
  ∀ F F' : FreeSep, SameTensors F F' → liftReal σ F = liftReal σ F'
def EntrywiseLinearValues : Prop :=
  ∀ σ : sepAll → ℝ, IsEntrywiseLinear σ →
    VanishesOnZeroTensor σ ∧ FactorsThroughTensor σ ∧ EqOnEqualTopComponent σ ∧
      IsLinearOnSpan σ ∧ AgreesOnSameTensors σ
end TensorValues
end YangMills.Construction.EuclideanFunctionals
