import YangMills.Construction.OneLoopLaw.CoefficientOfAFunctional
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.OneLoopLaw.KernelStiffness
open Filter YangMills.Construction.PeriodicOperators.Tempered
open YangMills.Construction.OneLoopLaw.FunctionalStiffness YangMills.Construction.Conventions
open scoped Topology
def StiffnessFromKernelLimit : Prop :=
  ∀ (L : ℕ) (hL : 0 < L), IsAdmissibleBlockingFactor L → ∀ (F : FieldFamily L), IsLatticeFunctional L F →
    ∀ (P : Fin 4 → Fin 4 → EffectiveAction.IntPoint → ℝ) (c : ℝ),
      (∀ (b b' : EffectiveAction.IntBond) (a a' : Fin 3),
        Tendsto (fun n => complexHessian F n (liftedPauliForm L n a b) (liftedPauliForm L n a' b'))
          atTop (𝓝 (if a = a' then ((P b.2 b'.2 (b'.1 - b.1) : ℝ) : ℂ) else 0))) →
      (∀ μ ν : Fin 4, μ ≠ ν →
        HasSum (fun u : EffectiveAction.IntPoint => P μ ν u * (u μ : ℝ) * (u ν : ℝ)) c) →
      HasStiffnessConstant hL F c ∧ stiffnessConstant hL F = c
end YangMills.Construction.OneLoopLaw.KernelStiffness
end
