import YangMills.Construction.Torus.SeparatedQuadruples
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open TestFunctions TorusMetric TorusMeasure PlaquetteSupports
namespace QuadrupleClasses
def ballLift (p : Conventions.StandingParameters) (r : ℝ) (x₀ : Fin 4 → ℝ) (φ : p.Torus → ℝ) :
    (Fin 4 → ℝ) → ℝ :=
  (closedBallR4 x₀ (9 * r)).indicator (φ ∘ TorusMeasure.proj p)
def IsBallLift (p : Conventions.StandingParameters) (r θ : ℝ) (φ : Fin 4 → p.Torus → ℝ)
    (ψ : Fin 4 → (Fin 4 → ℝ) → ℝ) : Prop :=
  φ ∈ quadsTorus p r θ ∧ ∃ x₀ : Fin 4 → ℝ,
    (∀ k, torusTSupport (φ k) ⊆ TorusMeasure.proj p '' closedBallR4 x₀ (9 * r)) ∧
      ∀ k, ψ k = ballLift p r x₀ (φ k)
def IsShapeAxis (v : Fin 4 → ℝ) (ψ : Fin 4 → (Fin 4 → ℝ) → ℝ) : Prop :=
  euclidNormVec v = 1 ∧ ∀ k l, k ≠ l → ∀ x ∈ euclideanTSupport (ψ k), ∀ y ∈ euclideanTSupport (ψ l),
    euclidNormVec ((x - y) - dotProduct (x - y) v • v) ≤ 1 / 8 * euclidNormVec (x - y)
def ShapeCondition (r θ : ℝ) (ψ : Fin 4 → (Fin 4 → ℝ) → ℝ) : Prop :=
  ψ ∈ quadsR4 r θ ∧ ∃ v, IsShapeAxis v ψ
def TorusShapeCondition (p : Conventions.StandingParameters) (r θ : ℝ)
    (φ : Fin 4 → p.Torus → ℝ) : Prop :=
  ∃ ψ, IsBallLift p r θ φ ψ ∧ ShapeCondition r θ ψ
def shapeQuadsR4 (r θ : ℝ) : Set (Fin 4 → (Fin 4 → ℝ) → ℝ) :=
  {ψ | ψ ∈ quadsR4 r θ ∧ ShapeCondition r θ ψ}
def shapeQuadsTorus (p : Conventions.StandingParameters) (r θ : ℝ) : Set (Fin 4 → p.Torus → ℝ) :=
  {φ | φ ∈ quadsTorus p r θ ∧ TorusShapeCondition p r θ φ}
def realLine (v : Fin 4 → ℝ) : Set (Fin 4 → ℝ) := {x | ∃ t : ℝ, x = t • v}
def IsLineDirection (v : Fin 4 → ℝ) (x : Fin 4 → Fin 4 → ℝ) : Prop :=
  euclidNormVec v = 1 ∧ ∀ k l, x k - x l ∈ realLine v
def AreCollinear (x : Fin 4 → Fin 4 → ℝ) : Prop := ∃ v, IsLineDirection v x
def collinearQuadsR4 (r θ : ℝ) : Set (Fin 4 → (Fin 4 → ℝ) → ℝ) :=
  {ψ | ψ ∈ quadsR4 r θ ∧ ∃ x : Fin 4 → Fin 4 → ℝ, AreCollinear x ∧
    ∀ k, euclideanTSupport (ψ k) ⊆ closedBallR4 (x k) (r / 16)}
def collinearQuadsTorus (p : Conventions.StandingParameters) (r θ : ℝ) :
    Set (Fin 4 → p.Torus → ℝ) :=
  {φ | φ ∈ quadsTorus p r θ ∧
    ∃ ψ, IsBallLift p r θ φ ψ ∧ ψ ∈ collinearQuadsR4 r θ}
end QuadrupleClasses
end YangMills.Construction
