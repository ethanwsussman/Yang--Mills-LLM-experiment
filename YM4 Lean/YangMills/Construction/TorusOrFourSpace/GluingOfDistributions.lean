import YangMills.Construction.TorusOrFourSpace.TestFunctionsAndDistributionsOnASet
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.PeriodicSpace.Kind.Tuple
def DistribGluing.Statement : Prop :=
  ∀ (D : Params) (E : Kind) (p : ℕ+) (ν₀ : ℕ) (Γ : Type) (Ω : Set (E.Tuple D p))
    (O : Γ → Set (E.Tuple D p)) (hΩ : ⋃ γ, O γ = Ω),
    IsOpenT D E Ω → (∀ γ, IsOpenT D E (O γ)) →
    ∀ T : ∀ γ, testFns D E (O γ) → ℂ,
      (∀ γ, IsDistrib (T γ)) →
      (∀ (γ γ' : Γ) (F : testFns D E (O γ ∩ O γ')),
        restrictDistrib Set.inter_subset_left (T γ) F =
          restrictDistrib Set.inter_subset_right (T γ') F) →
      (∃! S : testFns D E Ω → ℂ, IsDistrib S ∧
        ∀ γ, restrictDistrib ((Set.subset_iUnion O γ).trans hΩ.subset) S = T γ) ∧
      ((∀ γ, IsDistribOfOrderLE ν₀ (T γ)) →
        ∀ S : testFns D E Ω → ℂ, IsDistrib S →
          (∀ γ, restrictDistrib ((Set.subset_iUnion O γ).trans hΩ.subset) S = T γ) →
          IsDistribOfOrderLE ν₀ S)
end YangMills.Construction.PeriodicSpace.Kind.Tuple
