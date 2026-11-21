import YangMills.Construction.ReflectionPositivity.SeparatedTuplesAndFunctionals
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ReflectionPositivity.AxisMirror
def ReflectAppendSeparated : Prop :=
  ∀ (D : MirrorData) (E : Ambient) (μ : Fin 4) (c : ℝ) (X Y : Ambient.FnList D E),
    X ∈ Ambient.separatedWithin D E (CoordMirror.upperSide D ⟨μ, c⟩ E) →
    Y ∈ Ambient.separatedWithin D E (CoordMirror.upperSide D ⟨μ, c⟩ E) →
    CoordMirror.reflectList D ⟨μ, c⟩ E X ∈
        Ambient.separatedWithin D E (CoordMirror.lowerSide D ⟨μ, c⟩ E) ∧
      CoordMirror.reflectAppend D ⟨μ, c⟩ E X Y ∈ Ambient.separatedAll D E
end YangMills.Construction.ReflectionPositivity.AxisMirror
end
