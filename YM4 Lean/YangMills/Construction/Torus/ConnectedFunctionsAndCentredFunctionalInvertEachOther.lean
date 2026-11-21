import YangMills.Construction.Torus.MultilinearFunctionalsOnSeparatedTuplesOfTorusOrFourSpace
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open ReflectionPositivity.AxisMirror (Ambient)
open AmbientPoints
namespace TorusOrFourSpace
def connectedFamilyOf {s : Conventions.StandingParameters} {E : Ambient}
    (σ : allSeparatedTuples s E → ℝ)
    (hσ : ∀ n : ℕ, 1 ≤ n → IsTupleMultilinear (connectedOf σ n)) :
    ConnectedFamily s E where
  fn n _ := connectedOf σ n
  fn_multilinear n hn := hσ n (by omega)
def ConnectedFamilyCentredInverse : Prop :=
  ∀ (s : Conventions.StandingParameters) (E : Ambient) (σ : allSeparatedTuples s E → ℝ),
    IsTupleFunctional σ →
      ∃ hσ : ∀ n : ℕ, 1 ≤ n → IsTupleMultilinear (connectedOf σ n),
        (∀ f : separatedTuples s E 1, σ (toAllSeparated f) = 0) →
          (connectedFamilyOf σ hσ).centred = σ
end TorusOrFourSpace
end YangMills.Construction
