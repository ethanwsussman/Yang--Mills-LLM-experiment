import YangMills.Construction.SourcesAndGluing.LogarithmDerivativesPartitionsCumulantsAndConnectedFunctions
import Mathlib
set_option autoImplicit false
open MeasureTheory
noncomputable section
namespace YangMills.Construction.SourcesAndGluing
section Linearity
variable {V W : Type*} [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]
def IsLinearOnSubspace (A : Submodule ℝ V) (F : V → W) : Prop :=
  ∀ x ∈ A, ∀ y ∈ A, ∀ s t : ℝ, F (s • x + t • y) = s • F x + t • F y
def IsMultilinearOnSubspace {n : ℕ} (A : Submodule ℝ V) (F : (Fin n → V) → W) : Prop :=
  ∀ v : Fin n → V, (∀ i, v i ∈ A) → ∀ i, IsLinearOnSubspace A fun x => F (Function.update v i x)
end Linearity
def boundedRVSubspace (Ω : Type*) [MeasurableSpace Ω] : Submodule ℝ (Ω → ℝ) where
  carrier := {x | Probability.IsBoundedRealRV x}
  add_mem' := by
    rintro x y ⟨hx, C, hC⟩ ⟨hy, C', hC'⟩
    exact ⟨hx.add hy, C + C', fun ω => (abs_add_le _ _).trans (add_le_add (hC ω) (hC' ω))⟩
  zero_mem' := ⟨measurable_const, 0, fun _ => by simp⟩
  smul_mem' := by
    rintro c x ⟨hx, C, hC⟩
    refine ⟨hx.const_smul c, |c| * C, fun ω => ?_⟩
    simpa [abs_mul] using mul_le_mul_of_nonneg_left (hC ω) (abs_nonneg c)
def boundedFunSubspace (X : Type*) : Submodule ℝ (X → ℝ) where
  carrier := {f | TestFunctions.IsBoundedFun f}
  add_mem' := by
    rintro f g ⟨C, hC⟩ ⟨C', hC'⟩
    exact ⟨C + C', fun x => (norm_add_le _ _).trans (add_le_add (hC x) (hC' x))⟩
  zero_mem' := ⟨0, fun _ => by simp⟩
  smul_mem' := by
    rintro c f ⟨C, hC⟩
    refine ⟨‖c‖ * C, fun x => ?_⟩
    simpa [norm_smul] using mul_le_mul_of_nonneg_left (hC x) (norm_nonneg c)
def compactBorelSubspace : Submodule ℝ ((Fin 4 → ℝ) → ℝ) where
  carrier := {f | InfiniteLattice.IsBoundedBorelCompactlySupported f}
  add_mem' := by
    rintro f g ⟨hf, ⟨C, hC⟩, cf⟩ ⟨hg, ⟨C', hC'⟩, cg⟩
    exact ⟨hf.add hg, ⟨C + C', fun x => (norm_add_le _ _).trans (add_le_add (hC x) (hC' x))⟩,
      cf.add cg⟩
  zero_mem' := ⟨measurable_const, ⟨0, fun _ => by simp⟩, HasCompactSupport.zero⟩
  smul_mem' := by
    rintro c f ⟨hf, ⟨C, hC⟩, cf⟩
    refine ⟨hf.const_smul c, ⟨‖c‖ * C, fun x => ?_⟩, cf.smul_left (f := fun _ => c)⟩
    simpa [norm_smul] using mul_le_mul_of_nonneg_left (hC x) (norm_nonneg c)
namespace BoundedCumulants
def Multilinear : Prop :=
  ∀ (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] (n : ℕ), 1 ≤ n →
    IsMultilinearOnSubspace (boundedRVSubspace Ω)
      (cumulant μ : (Fin n → Ω → ℝ) → ℂ)
def FactorialBound : Prop :=
  ∀ (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω) (n : ℕ) (X : Fin n → Ω → ℝ) (b : Fin n → ℝ),
    BoundedRVFamily μ X → (∀ i, 0 ≤ b i) → (∀ i ω, |X i ω| ≤ b i) →
      ‖cumulant μ X‖ ≤ ((n - 1).factorial : ℝ) * (2 ^ n - 1) * ∏ i, b i
def SmearedLinear : Prop :=
  ∀ D : GluingSetup,
    (∀ f ∈ boundedFunSubspace D.Torus,
      Probability.IsBoundedRealRV (D.smearedOnGaugeFields f)) ∧
    (∀ f ∈ compactBorelSubspace,
      Probability.IsBoundedRealRV
        fun U : D.GridField => InfiniteLattice.smearedEnergy f U) ∧
    IsLinearOnSubspace (boundedFunSubspace D.Torus) D.smearedOnGaugeFields ∧
    IsLinearOnSubspace compactBorelSubspace
      (fun (f : (Fin 4 → ℝ) → ℝ) (U : D.GridField) =>
        InfiniteLattice.smearedEnergy f U) ∧
    (∀ n : ℕ, 1 ≤ n →
      IsMultilinearOnSubspace (boundedFunSubspace D.Torus)
        (D.torusConnected : (Fin n → D.Torus → ℝ) → ℂ)) ∧
    ∀ ν : Measure D.GridField, InfiniteLattice.IsGibbs D.β ν →
      ∀ n : ℕ, 1 ≤ n →
        IsMultilinearOnSubspace compactBorelSubspace
          (D.gibbsConnected ν : (Fin n → (Fin 4 → ℝ) → ℝ) → ℂ)
def Corollary : Prop := Multilinear ∧ FactorialBound ∧ SmearedLinear
end BoundedCumulants
end YangMills.Construction.SourcesAndGluing
end
