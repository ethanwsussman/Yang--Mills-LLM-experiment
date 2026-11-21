import YangMills.Construction.TorusOrFourSpace.HierarchiesCentredMomentsAndObeyingABoundFunction
import YangMills.Construction.TorusOrFourSpace.TensorsOfSeparatedTuples
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.PeriodicSpace.Kind
variable (D : Params) (E : Kind)
theorem tensorFn_mem_sepTensorSpan {n : ℕ} (f : sepC1Tuples D E n) :
    tensorFn D E (fun i y => ((f.1 i y : ℝ) : ℂ)) ∈ sepTensorSpan D E n :=
  Submodule.subset_span ⟨f.1, f.2, rfl⟩
def TensorRelationsHold {n : ℕ} (Ψ : sepC1Tuples D E n → ℝ) : Prop :=
  ∀ (J : ℕ) (f : Fin J → sepC1Tuples D E n) (c : Fin J → ℂ),
    ∑ j, c j • tensorFn D E (fun i y => (((f j).1 i y : ℝ) : ℂ)) = 0 →
      ∑ j, c j * ((Ψ (f j) : ℝ) : ℂ) = 0
def UniqueLinearFormOnTensors {n : ℕ} (Ψ : sepC1Tuples D E n → ℝ) : Prop :=
  ∃! T : sepTensorSpan D E n →ₗ[ℂ] ℂ, ∀ f : sepC1Tuples D E n,
    T ⟨_, tensorFn_mem_sepTensorSpan D E f⟩ = ((Ψ f : ℝ) : ℂ)
def ExtendsToTensorSpan {n : ℕ} (Ψ : sepC1Tuples D E n → ℝ) : Prop :=
  TensorRelationsHold D E Ψ ∧ UniqueLinearFormOnTensors D E Ψ
namespace TensorExtension
def Claim : Prop :=
  ∀ (D : Params) (E : Kind),
    (∀ (n : ℕ), 1 ≤ n → ∀ Ψ : sepC1Tuples D E n → ℝ,
      IsMultilinearOn D E (sepC1Tuples D E n) Ψ →
        ExtendsToTensorSpan D E Ψ) ∧
    ∀ Φ : Hierarchy D E,
      (∀ (n : ℕ) (hn : 2 ≤ n), ExtendsToTensorSpan D E (Φ.func n hn)) ∧
      ∀ (q : ℕ), 1 ≤ q →
        ExtendsToTensorSpan D E (fun f : sepC1Tuples D E q => Φ.partitionMoment f)
end TensorExtension
end YangMills.Construction.PeriodicSpace.Kind
