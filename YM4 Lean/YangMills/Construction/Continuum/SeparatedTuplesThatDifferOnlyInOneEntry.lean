import YangMills.Construction.Torus.SeparatedTuplesAndIsometriesOfTorusOrFourSpace
import Mathlib
set_option autoImplicit false
namespace YangMills.Construction.AmbientPoints
def AgreeOffComponent (s : Conventions.StandingParameters) {n : ℕ} (i : Fin n)
    (u v : Fin n → Pt s .euclidean → ℝ) : Prop :=
  u ∈ separatedTuples s .euclidean n ∧ v ∈ separatedTuples s .euclidean n ∧
    ∀ j, j ≠ i → u j = v j
end YangMills.Construction.AmbientPoints
