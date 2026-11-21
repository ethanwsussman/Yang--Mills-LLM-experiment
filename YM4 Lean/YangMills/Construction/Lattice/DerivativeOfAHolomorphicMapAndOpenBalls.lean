import YangMills.Construction.Coordinates.HolomorphyInCoordinates
import Mathlib
noncomputable section
namespace YangMills.Construction.Coordinates.ComplexCoordinates
variable {N N' : ℕ}
def derivAlongLine (f : ComplexCoordinates N → ComplexCoordinates N')
    (z k h : ComplexCoordinates N) : ℝ → ComplexCoordinates N' :=
  fun s => fderiv ℝ f (z + s • k) h
def secondDeriv (f : ComplexCoordinates N → ComplexCoordinates N')
    (z k h : ComplexCoordinates N) : ComplexCoordinates N' :=
  deriv (derivAlongLine f z k h) 0
end YangMills.Construction.Coordinates.ComplexCoordinates
namespace YangMills.Construction.SeparatedFrame
open YangMills.Construction.Coordinates
structure IsNormOverComplex {V : Type} [AddCommGroup V] [Module ℂ V] (ν : V → ℝ) : Prop where
  nonneg : ∀ v, 0 ≤ ν v
  eq_zero : ∀ v, ν v = 0 → v = 0
  smul : ∀ (c : ℂ) (v : V), ν (c • v) = ‖c‖ * ν v
  add_le : ∀ v w, ν (v + w) ≤ ν v + ν w
namespace HolomorphicDerivatives
def Claim : Prop :=
  ∀ (N N' : ℕ) (O : Set (ComplexCoordinates N)) (f : ComplexCoordinates N → ComplexCoordinates N'),
    ComplexCoordinates.IsHolomorphicIn O f →
      (∀ h : ComplexCoordinates N,
        ComplexCoordinates.IsHolomorphicIn O fun z => fderiv ℝ f z h) ∧
      ∀ z ∈ O,
        (∀ k h : ComplexCoordinates N,
          DifferentiableAt ℝ (ComplexCoordinates.derivAlongLine f z k h) 0) ∧
        (∃ B : ComplexCoordinates N →ₗ[ℂ] ComplexCoordinates N →ₗ[ℂ] ComplexCoordinates N',
          ∀ k h, B k h = ComplexCoordinates.secondDeriv f z k h) ∧
        ∀ k h : ComplexCoordinates N,
          ComplexCoordinates.secondDeriv f z k h =
            ComplexCoordinates.secondDeriv f z h k
end HolomorphicDerivatives
end YangMills.Construction.SeparatedFrame
