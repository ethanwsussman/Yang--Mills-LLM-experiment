import YangMills.Construction.Torus.TestFunctionsAndDistributionsOnOpenSetsOfTuples
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.AmbientPoints
def DistributionsGlueUniquely : Prop :=
  ∀ (s : Conventions.StandingParameters) (E : ReflectionPositivity.AxisMirror.Ambient) (p : ℕ), 1 ≤ p →
    ∀ (U : Set (Tuple s E p)), IsOpen U →
    ∀ (Γ : Type) (O : Γ → Set (Tuple s E p)), (∀ γ, IsOpen (O γ)) →
    ∀ hU : ⋃ γ, O γ = U,
    ∀ T : ∀ γ, testFns (O γ) → ℂ, (∀ γ, IsDistrib (T γ)) →
      (∀ (γ γ' : Γ) (F : testFns (O γ ∩ O γ')),
        restrictDistrib Set.inter_subset_left (T γ) F =
          restrictDistrib Set.inter_subset_right (T γ') F) →
      (∃! S : testFns U → ℂ, IsDistrib S ∧
        ∀ γ, restrictDistrib ((Set.subset_iUnion O γ).trans hU.subset) S = T γ) ∧
      ∀ k : ℕ, (∀ γ, HasOrderLE k (T γ)) →
        ∀ S : testFns U → ℂ, IsDistrib S →
          (∀ γ, restrictDistrib ((Set.subset_iUnion O γ).trans hU.subset) S = T γ) →
          HasOrderLE k S
end YangMills.Construction.AmbientPoints
