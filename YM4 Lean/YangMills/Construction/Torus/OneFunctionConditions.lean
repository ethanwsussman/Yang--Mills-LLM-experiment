import YangMills.Construction.Lattice.PlaquetteFunctionsAndTwoNotionsOfSupport
import YangMills.Construction.Torus.DistanceBallsIntegralAndVolumeInPhysicalUnits
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.BumpConditions
open Set TestFunctions TorusMeasure PlaquetteSupports
section Torus
variable {s : Conventions.StandingParameters}
def SupportInBallTorus (x : s.Torus) (r₀ : ℝ) (f : s.Torus → ℝ) : Prop :=
  torusTSupport f ⊆ closedWrapBall x r₀
def MassBoundTorus (r₀ ϑ : ℝ) (f : s.Torus → ℝ) : Prop :=
  ϑ * uniformNorm f * r₀ ^ 4 ≤ torusIntegral f
def LipBoundTorus (r₀ ϑ : ℝ) (f : s.Torus → ℝ) : Prop :=
  lipConstTorus f ≤ uniformNorm f / (ϑ * r₀)
def SatisfiesTorus (x : s.Torus) (r₀ ϑ : ℝ) (f : s.Torus → ℝ) : Prop :=
  0 < r₀ ∧ ϑ ∈ Ioc (0 : ℝ) 1 ∧ IsLipschitzFor pointDist f ∧ (∀ u, 0 ≤ f u) ∧
    SupportInBallTorus x r₀ f ∧ MassBoundTorus r₀ ϑ f ∧ LipBoundTorus r₀ ϑ f
end Torus
def SupportInBallR4 (x : Fin 4 → ℝ) (r₀ : ℝ) (f : (Fin 4 → ℝ) → ℝ) : Prop :=
  euclideanTSupport f ⊆ closedWrapBallR4 x r₀
def MassBoundR4 (r₀ ϑ : ℝ) (f : (Fin 4 → ℝ) → ℝ) : Prop :=
  ϑ * uniformNorm f * r₀ ^ 4 ≤ integralR4 f
def LipBoundR4 (r₀ ϑ : ℝ) (f : (Fin 4 → ℝ) → ℝ) : Prop :=
  lipConstR4 f ≤ uniformNorm f / (ϑ * r₀)
def SatisfiesR4 (x : Fin 4 → ℝ) (r₀ ϑ : ℝ) (f : (Fin 4 → ℝ) → ℝ) : Prop :=
  0 < r₀ ∧ ϑ ∈ Ioc (0 : ℝ) 1 ∧ IsLipschitzFor euclidDistR4 f ∧ (∀ t, 0 ≤ f t) ∧
    SupportInBallR4 x r₀ f ∧ MassBoundR4 r₀ ϑ f ∧ LipBoundR4 r₀ ϑ f
end YangMills.Construction.BumpConditions
