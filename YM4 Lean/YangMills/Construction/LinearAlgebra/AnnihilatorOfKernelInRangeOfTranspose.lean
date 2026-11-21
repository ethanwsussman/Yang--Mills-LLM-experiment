import Mathlib
set_option autoImplicit false
namespace YangMills.Construction.LinearAlgebra.AnnihilatorOfKernel
def AnnihilatorSubsetRangeTranspose (𝕜 : Type) [Field 𝕜] : Prop :=
  ∀ (V W : Type) [AddCommGroup V] [Module 𝕜 V] [FiniteDimensional 𝕜 V]
    [AddCommGroup W] [Module 𝕜 W] [FiniteDimensional 𝕜 W]
    (B : LinearMap.BilinForm 𝕜 V) (B' : LinearMap.BilinForm 𝕜 W),
    (∀ v w, B v w = B w v) → (∀ v, (∀ w, B v w = 0) → v = 0) →
    (∀ v w, B' v w = B' w v) → (∀ v, (∀ w, B' v w = 0) → v = 0) →
    ∀ (M : V →ₗ[𝕜] W) (Mt : W →ₗ[𝕜] V),
      (∀ (l : W) (d : V), B (Mt l) d = B' l (M d)) →
      ∀ f : V, (∀ d : V, M d = 0 → B f d = 0) → ∃ l : W, f = Mt l
def AnnihilatorSubsetRangeTransposeRealComplex : Prop :=
  AnnihilatorSubsetRangeTranspose ℝ ∧ AnnihilatorSubsetRangeTranspose ℂ
end YangMills.Construction.LinearAlgebra.AnnihilatorOfKernel
