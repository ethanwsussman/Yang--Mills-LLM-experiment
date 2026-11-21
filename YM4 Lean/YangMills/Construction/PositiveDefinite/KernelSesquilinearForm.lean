import YangMills.Construction.PositiveDefinite.HalfPlaneKernelDefs
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped ComplexConjugate ComplexOrder
namespace YangMills.Construction.PositiveDefinite
def kernelSesqForm {Y : Type*} (k : Y → Y → ℂ) (f f' : Y →₀ ℂ) : ℂ :=
  ∑ u ∈ f.support, ∑ u' ∈ f'.support, conj (f u) * f' u' * k u u'
namespace KernelSesqForm
def SesqFormProperties : Prop :=
  ∀ (Y : Type) (k : Y → Y → ℂ), KernelPosSemidef k →
    ((∀ (f g g' : Y →₀ ℂ), kernelSesqForm k f (g + g') = kernelSesqForm k f g + kernelSesqForm k f g') ∧
      (∀ (c : ℂ) (f g : Y →₀ ℂ), kernelSesqForm k f (c • g) = c * kernelSesqForm k f g) ∧
      (∀ (f g g' : Y →₀ ℂ), kernelSesqForm k (g + g') f = kernelSesqForm k g f + kernelSesqForm k g' f) ∧
      (∀ (c : ℂ) (f g : Y →₀ ℂ), kernelSesqForm k (c • g) f = conj c * kernelSesqForm k g f) ∧
      ∀ f f' : Y →₀ ℂ,
        0 ≤ kernelSesqForm k f f ∧
          kernelSesqForm k f' f = conj (kernelSesqForm k f f') ∧
          ((‖kernelSesqForm k f f'‖ ^ 2 : ℝ) : ℂ) ≤ kernelSesqForm k f f * kernelSesqForm k f' f') ∧
    ∀ u u' : Y,
      0 ≤ k u u ∧
        k u' u = conj (k u u') ∧
        ((‖k u u'‖ ^ 2 : ℝ) : ℂ) ≤ k u u * k u' u'
end KernelSesqForm
end YangMills.Construction.PositiveDefinite
end
