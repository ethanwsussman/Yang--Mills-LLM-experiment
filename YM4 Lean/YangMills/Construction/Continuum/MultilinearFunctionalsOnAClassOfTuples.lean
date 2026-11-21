import YangMills.Construction.Continuum.ClassesOfTuples
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.TorusTransport
variable (D : TransportData)
def IsMultilinearOn {n : ℕ+} {𝕜 : Type*} [RCLike 𝕜]
    (C : Set (Domain.euclidean.FnFamily D n ℝ))
    (_hC : ∀ f ∈ C, Domain.euclidean.IsSepLipschitz D f) (Ψ : C → 𝕜) : Prop :=
  ∀ (i : Fin n) (u v : C), (∀ j, j ≠ i → u.1 j = v.1 j) →
    ∀ (s s' : ℝ) (hmem : Function.update u.1 i (s • u.1 i + s' • v.1 i) ∈ C),
      Ψ ⟨_, hmem⟩ = (s : 𝕜) * Ψ u + (s' : 𝕜) * Ψ v
end YangMills.Construction.TorusTransport
end
