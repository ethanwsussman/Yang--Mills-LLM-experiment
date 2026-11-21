import YangMills.Construction.SummableBoundsOfTheFlow.FamiliesOfANorm
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
namespace FamilyNorms
open BlockAverages TorusLumps TorusFields
structure IsCurvatureFreeTilt (ℓ : StepParameters) (t : ℕ) (x : ℝ) (D : TorusFunctional)
    (f h : LocalDensity) (ε : ℝ) : Prop where
  normBounded : IsNormBoundedFamily ℓ ε (thirdOrderSize ℓ ε) h
  curvatureForm_vanishes : HasVanishingCurvatureForm h
  log_density_eq : ∀ n [NeZero n], ℓ.n₀ ≤ n → ∀ W : TorusField n, IsCold ℓ.threshold W →
    Real.log (D n W) - Real.log (D n (trivialField n)) =
      -x * actionAtLevel ℓ.coupling ℓ.side t Finset.univ W + ∑ y, centered (f + h) n y W
def HasRefinedExpansion (ℓ : StepParameters) (Bh : ℝ) (f : LocalDensity) (t : ℕ) (x : ℝ)
    (D : TorusFunctional) : Prop :=
  HasExpansion ℓ t x D ∧ ∃ h : LocalDensity, IsCurvatureFreeTilt ℓ t x D f h (Bh * x ^ (-(3 / 4 : ℝ)))
end FamilyNorms
end YangMills.Construction
end
