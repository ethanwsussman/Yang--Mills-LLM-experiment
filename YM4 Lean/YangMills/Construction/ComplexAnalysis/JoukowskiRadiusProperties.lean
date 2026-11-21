import YangMills.Construction.ComplexAnalysis.JoukowskiEllipses
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.JoukowskiRadius
open Ellipses
def unitSegment : Set ℂ := (fun x : ℝ => (x : ℂ)) '' Set.Icc (-1 : ℝ) 1
def unitCube (n : ℕ) : Set (Fin n → ℂ) :=
  {z | ∀ j : Fin n, z j ∈ unitSegment}
def JoukowskiRadiusProperties : Prop :=
  (∀ z : ℂ, joukowskiRadius z ∈ Set.Ici (1 : ℝ)) ∧
  Continuous joukowskiRadius ∧
  (∀ z : ℂ, joukowskiRadius z = 1 ↔ z ∈ unitSegment) ∧
  (∀ (ρ : ℝ) (hρ : 1 < ρ), IsOpen (focalEllipse ρ hρ)) ∧
  (∀ (ρ : ℝ) (hρ : 1 < ρ) (n : ℕ) (hn : 1 ≤ n),
    IsOpen (polyEllipseDomain n hn ρ hρ) ∧ unitCube n ⊆ polyEllipseDomain n hn ρ hρ) ∧
  (∀ w : ℂ, w ≠ 0 → joukowskiRadius ((1 / 2 : ℂ) * (w + w⁻¹)) = max ‖w‖ ‖w‖⁻¹) ∧
  (∀ z : ℂ, ∃ w : ℂ, z = (1 / 2 : ℂ) * (w + w⁻¹) ∧ ‖w‖ = joukowskiRadius z) ∧
  (∀ (ρ : ℝ) (hρ : 1 < ρ), ∀ z ∈ focalEllipse ρ hρ,
    |z.re| < (1 / 2 : ℝ) * (ρ + ρ⁻¹) ∧ |z.im| < (1 / 2 : ℝ) * (ρ - ρ⁻¹)) ∧
  (∀ y : ℝ, ∃! τ : ℝ, 0 ≤ τ ∧ Real.sinh τ = |y|) ∧
  (∀ y τ : ℝ, 0 ≤ τ → Real.sinh τ = |y| →
    joukowskiRadius (Complex.I * (y : ℂ)) = Real.exp τ) ∧
  (∀ x y y' : ℝ, |y| ≤ |y'| →
    joukowskiRadius ((x : ℂ) + Complex.I * (y : ℂ)) ≤
      joukowskiRadius ((x : ℂ) + Complex.I * (y' : ℂ))) ∧
  (∀ x x' : ℝ, |x| ≤ |x'| → joukowskiRadius (x : ℂ) ≤ joukowskiRadius (x' : ℂ))
end YangMills.Construction.JoukowskiRadius
