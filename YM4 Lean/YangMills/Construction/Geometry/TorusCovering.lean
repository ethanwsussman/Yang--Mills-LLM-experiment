import YangMills.Construction.Lattice.ObservablesAndTestNorms
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open Set Function TorusMetric
open TestFunctions (euclidDistR4 euclidDistTorus latticeTranslate)
namespace TorusCovering
variable {ℓ : ℝ}
def torusProjHom (ℓ : ℝ) : (Fin 4 → ℝ) →+ Torus4 ℓ where
  toFun := torusProj ℓ
  map_zero' := by
    funext μ
    simp [torusProj]
  map_add' v w := by
    funext μ
    simp [torusProj]
theorem torusProjHom_apply (v : Fin 4 → ℝ) : torusProjHom ℓ v = torusProj ℓ v := rfl
theorem torusProjHom_surjective (ℓ : ℝ) : Surjective (torusProjHom ℓ) :=
  TestFunctions.torusProj_surjective ℓ
section
variable {X E : Type*} [TopologicalSpace X] [Zero E]
def closedSupport (f : X → E) : Set X := closure {x | f x ≠ 0}
def IsSupportedIn (f : X → E) (A : Set X) : Prop := closedSupport f ⊆ A
end
end TorusCovering
end YangMills.Construction
end
