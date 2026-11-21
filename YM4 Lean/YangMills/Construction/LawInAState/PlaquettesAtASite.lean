import YangMills.Construction.LawInAState.ResponsesInOneBox
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.StateLaws
open TorusFields WeightedResponses BoxResponses
open InfiniteLattice (AmbientSpace)
def plaquetteWeightAtSiteStatement : Prop :=
  ∀ (L : ℕ) [NeZero L], Odd L → ∀ (K k : ℕ), k ≤ K → ∀ (f : AmbientSpace → ℝ) (y : TorusSite (boxSide L K k))
    (u : Fin 4 → ℤ),
    (∀ i, ((u i : ℤ) : ZMod (boxSide L K k)) = y i) → ∀ p : TorusPlaquette (fineSide L k (boxSide L K k)),
    IsPlaquetteAt L k y p →
    ∃ θ : AmbientSpace, (∀ i, |θ i| ≤ (L : ℝ) ^ k / (L : ℝ) ^ K / 2) ∧
      unitTorusWeight L K k f p = periodizeUnitTorus f fun i => (u i : ℝ) * ((L : ℝ) ^ k / (L : ℝ) ^ K) + θ i
end YangMills.Construction.StateLaws
end
