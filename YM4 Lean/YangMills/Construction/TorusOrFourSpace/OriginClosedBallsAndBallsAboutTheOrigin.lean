import YangMills.Construction.TorusOrFourSpace.SpaceQuotientMapAndDistance
import Mathlib
set_option autoImplicit false
open scoped ENNReal
noncomputable section
namespace YangMills.Construction.PeriodicSpace.Kind
variable (P : Params) (K : Kind)
def origin : K.Pt P := K.quotMap P 0
def closedBallAbout (x : K.Pt P) (R : ℝ) : Set (K.Pt P) := {y | quotDist P K y x ≤ R}
def IsClosedBallWithRadius (S : Set (K.Pt P)) (R : ℝ) : Prop :=
  0 < R ∧ ∃ x, S = closedBallAbout P K x R
def centredBall (ρ : ℝ≥0∞) : Set (K.Pt P) :=
  if ρ = ∞ then Set.univ else {y | quotDist P K y (origin P K) < ρ.toReal}
end YangMills.Construction.PeriodicSpace.Kind
end
