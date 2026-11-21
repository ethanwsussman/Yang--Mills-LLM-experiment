import YangMills.Construction.ComplexAnalysis.JoukowskiEllipses
import YangMills.Construction.Conventions.RealPowerAndLogarithm
import YangMills.Construction.Coordinates.HolomorphyInCoordinates
import Mathlib
noncomputable section
namespace YangMills.Construction.JointHolomorphy
open Coordinates.ComplexCoordinates Ellipses RealPower
def realClosedCube (n : ℕ) : Set (Coordinates.ComplexCoordinates n) :=
  {x | ∀ j, (x j).im = 0 ∧ (x j).re ∈ Set.Icc (-1 : ℝ) 1}
def realOpenCube (n : ℕ) : Set (Coordinates.ComplexCoordinates n) :=
  {x | ∀ j, (x j).im = 0 ∧ (x j).re ∈ Set.Ioo (-1 : ℝ) 1}
def IsBoundedSliceExtension {n : ℕ} (ς : ℝ) (hς : 1 < ς) (A : ℝ)
    (F : Coordinates.ComplexCoordinates n → ℂ) (j : Fin n) (x : Coordinates.ComplexCoordinates n)
    (h : ℂ → ℂ) : Prop :=
  IsHolomorphicVia (Equiv.funUnique (Fin 1) ℂ).symm (Equiv.funUnique (Fin 1) ℂ).symm
      (focalEllipse ς hς) h ∧
    (∀ w ∈ focalEllipse ς hς, ‖h w‖ ≤ A) ∧
    ∀ t ∈ Set.Icc (-1 : ℝ) 1, h (t : ℂ) = F (Function.update x j (t : ℂ))
def HasPolyellipseBound {n : ℕ} (ς A : ℝ) (G : Coordinates.ComplexCoordinates n → ℂ)
    (s : Fin n → ℝ) : Prop :=
  ∀ z : Coordinates.ComplexCoordinates n, (∀ j, joukowskiRadius (z j) ≤ rpowPos ς (s j)) →
    ‖G z‖ ≤ (2 : ℝ) ^ n * A * (1 - rpowPos ς (-(1 - ∑ j, s j) / (n : ℝ))) ^ (-(n : ℤ))
def SeparateImpliesJoint : Prop :=
  ∀ (n : ℕ) (hn : 1 ≤ n) (ς : ℝ) (hς : 1 < ς) (A : ℝ), 0 ≤ A →
    ∀ F : Coordinates.ComplexCoordinates n → ℂ, ContinuousOn F (realClosedCube n) →
      (∀ j : Fin n, ∀ x ∈ realClosedCube n, ∃ h : ℂ → ℂ, IsBoundedSliceExtension ς hς A F j x h) →
      (∃ G : Coordinates.ComplexCoordinates n → ℂ,
        IsHolomorphicIn (N' := 1) (polyEllipseDomain n hn ς hς) (fun z _ => G z) ∧
        realClosedCube n ⊆ polyEllipseDomain n hn ς hς ∧
        (∀ x ∈ realClosedCube n, G x = F x) ∧
        ∀ s : Fin n → ℝ, (∀ j, 0 ≤ s j) → ∑ j, s j < 1 → HasPolyellipseBound ς A G s) ∧
      IsRealAnalyticIn (N' := 1) (realOpenCube n) (fun z _ => F z)
end YangMills.Construction.JointHolomorphy
