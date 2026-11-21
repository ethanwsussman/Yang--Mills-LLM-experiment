import YangMills.Construction.ReflectionPositivity.FunctionsOfClassC1AndSupports
import Mathlib
set_option autoImplicit false
namespace YangMills.Construction.ReflectionPositivity.AxisMirror
def gradAtAnyLift : Prop :=
  ∀ (D : MirrorData) (𝕜 : Type) [RCLike 𝕜] (f : D.Torus → 𝕜),
    Ambient.IsC1 D Ambient.torus f → ∀ y : Fin 4 → ℝ,
      Ambient.grad D Ambient.torus f (D.projection y) =
        Ambient.gradR4 (f ∘ D.projection) y
end YangMills.Construction.ReflectionPositivity.AxisMirror
