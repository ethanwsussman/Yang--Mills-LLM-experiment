import YangMills.Construction.TwoPoints.TranslationModulusAndSuperpositionsOfTranslates
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.TwoPoints
open YangMills.Construction.InfiniteLattice (AmbientSpace)
def ConvolveC1.Statement : Prop :=
  ∀ k ∈ ccIn (Set.univ : Set AmbientSpace), ∀ φ ∈ compactC1Complex,
    convolve k φ ∈ compactC1Complex ∧
      tsupport (convolve k φ) ⊆ minkowskiSum (tsupport k) (tsupport φ)
end YangMills.Construction.TwoPoints
