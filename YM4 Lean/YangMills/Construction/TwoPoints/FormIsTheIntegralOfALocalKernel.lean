import YangMills.Construction.TwoPoints.LocalKernelOfAForm
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.TwoPoints
open YangMills.Construction.InfiniteLattice (AmbientSpace)
def KernelRepresentsForm.Statement : Prop :=
  ∀ (σ : FixedScale) (S : (AmbientSpace → ℂ) → (AmbientSpace → ℂ) → ℝ), IsDisjointForm S →
    IsAdmissibleForm σ S →
    ∀ K : AmbientSpace → ℝ, ContinuousOn (fun x => (K x : ℂ)) {0}ᶜ →
      (∀ ξ : AmbientSpace, ξ ≠ 0 → IsLocalKernelNear S ξ fun x => (K x : ℂ)) →
        ∀ u ∈ compactC1Complex, ∀ w ∈ compactC1Complex, DisjointSupports u w →
          complexifyForm S u w =
            lebesgueIntegral fun y : AmbientSpace =>
              lebesgueIntegral fun x : AmbientSpace => u x * w y * (K (y - x) : ℂ)
end YangMills.Construction.TwoPoints
end
