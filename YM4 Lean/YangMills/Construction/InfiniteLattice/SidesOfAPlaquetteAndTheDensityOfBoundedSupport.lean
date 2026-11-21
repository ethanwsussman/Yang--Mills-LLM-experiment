import YangMills.Construction.InfiniteLattice.GaugeFieldsAndStates
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
namespace InfiniteLattice
variable {a : ℝ}
namespace ElementaryPlaquette
def sideLinks (p : ElementaryPlaquette a) : List (Link a) :=
  [Link.forwardFrom p.corner p.lowAxis, Link.forwardFrom (p.corner + axisStep a p.highAxis) p.lowAxis,
    Link.forwardFrom p.corner p.highAxis, Link.forwardFrom (p.corner + axisStep a p.lowAxis) p.highAxis]
def HasEdgeIn (p : ElementaryPlaquette a) (W : Set (Link a)) : Prop := ∃ b ∈ p.sideLinks, b ∈ W
end ElementaryPlaquette
def IsBoundedOfBoundedSupport (f : AmbientSpace → ℂ) : Prop :=
  (∃ C : ℝ, ∀ x, ‖f x‖ ≤ C) ∧ Bornology.IsBounded (Function.support f)
def boundedSupportObservable (f : AmbientSpace → ℂ) (U : GaugeField a) : ℂ :=
  ∑ᶠ p ∈ {p : ElementaryPlaquette a | f p.center ≠ 0}, f p.center * (faceEnergy U p : ℂ)
end InfiniteLattice
end YangMills.Construction
