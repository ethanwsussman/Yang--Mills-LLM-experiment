import YangMills.Construction.Torus.SeparatedTuplesAndIsometriesOfTorusOrFourSpace
import Mathlib
set_option autoImplicit false
open Filter
noncomputable section
namespace YangMills.Construction
namespace FamiliesOfLimits
abbrev SeparatedTupleFunctions (s : Conventions.StandingParameters) : Type :=
  ∀ n : ℕ, 2 ≤ n → AmbientPoints.separatedTuples s .euclidean n → ℂ
end FamiliesOfLimits
end YangMills.Construction
end
