import YangMills.Construction.ColdStepAtMirrorFrames.ConvexMeasuresOnBalls
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.RestrictedPotentials
open YangMills.Construction.ColdStepAtMirrorFrames
def extendByHeld {ι ι' : Type} (e : ι' → ι) (c : BondField ι) (ξ : BondField ι') : BondField ι :=
  c + Function.extend e ξ 0
def UniformlyConvexOnSubfamily : Prop :=
  ∀ (ι ι' : Type) [Fintype ι] [DecidableEq ι] [Fintype ι'] [DecidableEq ι'] (e : ι' → ι) (ρ m κ : ℝ)
    (d : ι → ι → ℝ) (Ψ : BondField ι → ℝ) (K : ι → ι → ℝ) (c : BondField ι),
    Function.Injective e → 0 < ρ → 0 ≤ κ → IsPseudoMetricOnBonds d → IsUniformlyConvexDecaying ρ m κ d Ψ K →
    (∀ b, ‖c b‖ < ρ) → (∀ b, c (e b) = 0) →
    IsUniformlyConvexDecaying ρ m κ (fun b b' => d (e b) (e b')) (fun ξ => Ψ (extendByHeld e c ξ))
      (fun b b' => K (e b) (e b')) ∧
    ∀ (ξ : BondField ι') (b : ι') (X : BondVector),
      fderiv ℝ (fun ξ => Ψ (extendByHeld e c ξ)) ξ (bondVariation b X) =
        fderiv ℝ Ψ (extendByHeld e c ξ) (bondVariation (e b) X)
end YangMills.Construction.RestrictedPotentials
end
