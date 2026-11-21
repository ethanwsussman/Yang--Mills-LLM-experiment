import YangMills.Construction.SummableBoundsOfTheFlow.AdmittedObservables
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.TorusComparison
open YangMills.Construction.BlockAverages YangMills.Construction.ColdStepAtMirrorFrames YangMills.Construction.Interpolation
variable {F F' : BlockFrame}
def cellExponentRemainder (s a ρA lam x : ℝ) (m : ℕ) (Y : F.Cell) (V : F.GaugeField F.top)
    (η : StepVariable (finiteCells F)) : ℝ :=
  interpolatedBlockExponent s a ρA x m Y V η - cellQuadratic lam x Y η
def HasGradientBound {ι : Type} [Fintype ι] [DecidableEq ι] (ρ : ℝ) (r : ℝ → ℝ)
    (Ψ : BondField ι → ℝ) (x κ h : ℝ) (dZ : ι → ℝ) (H : BondField ι → ℝ) : Prop :=
  (∀ η : BondField ι, (∀ b, ‖η b‖ < ρ) → DifferentiableAt ℝ H η) ∧
    (∀ q : ℕ, 1 ≤ q → MeasureTheory.Integrable (fun η => |H η| ^ q * ballDensity r Ψ η) ∧
      ∀ b : ι, MeasureTheory.Integrable fun η => |bondGradNorm H b η| ^ q * ballDensity r Ψ η) ∧
    ∀ b : ι, MomentBound r Ψ (bondGradNorm H b) 2 (Real.sqrt x * h * Real.exp (-(2 * κ * dZ b)))
structure ComparisonHypothesesOnTorus (ρ lam x κ α : ℝ) (p : ℝ → ℝ) (q : ℕ) (Y : F.Cell)
    (Ψ A : StepVariable (finiteCells F) → ℝ) : Prop where
  integrable_mul : MeasureTheory.Integrable fun η => A η * radialWeightProd (cutoffFactor ρ p) η
  integrable_freeze_mul : MeasureTheory.Integrable fun η =>
    A (freezeOutside (bondsNearCell Y q) η) * radialWeightProd (cutoffFactor ρ p) η
  hasGradientBound : ∀ v : ℝ, 0 ≤ v → v ≤ 1 →
    HasGradientBound ρ (cutoffFactor ρ p) (freezingHomotopy lam x (bondsNearCell Y q) Ψ v) x κ α
      (bondDistToCell Y) A
  hasGradientBound_freeze : ∀ v : ℝ, 0 ≤ v → v ≤ 1 →
    HasGradientBound ρ (cutoffFactor ρ p) (freezingHomotopy lam x (bondsNearCell Y q) Ψ v) x κ α
      (bondDistToCell Y) fun η => A (freezeOutside (bondsNearCell Y q) η)
  expectation_freeze_sub_le : ∀ v : ℝ, 0 ≤ v → v ≤ 1 →
    |ballExpectation (cutoffFactor ρ p) (freezingHomotopy lam x (bondsNearCell Y q) Ψ v)
      fun η => A η - A (freezeOutside (bondsNearCell Y q) η)| ≤ α * Real.exp (-(4 * κ * q))
structure ComparisonHypotheses (ρ lam x κ α : ℝ) (p : ℝ → ℝ) (r₂ q : ℕ) (Y : F.Cell) (Y' : F'.Cell)
    {ι : Type} [Fintype ι] [DecidableEq ι] (j : ι → ↥(chordBonds (finiteCells F)))
    (j' : ι → ↥(chordBonds (finiteCells F'))) (Ψ A : StepVariable (finiteCells F) → ℝ)
    (Ψ' A' : StepVariable (finiteCells F') → ℝ) : Prop where
  left : ComparisonHypothesesOnTorus ρ lam x κ α p q Y Ψ A
  right : ComparisonHypothesesOnTorus ρ lam x κ α p q Y' Ψ' A'
  expectation_sub_le : |ballExpectation (cutoffFactor ρ p) Ψ A - ballExpectation (cutoffFactor ρ p) Ψ' A'| ≤ α
  hasGradientBound_shared : ∀ th : ℝ, 0 ≤ th → th ≤ 1 →
    HasGradientBound ρ (cutoffFactor ρ p) (pairingHomotopy j j' Ψ Ψ' th) x κ α
      (fun i => bondDistToCell Y (j i)) (fun ζ => A (toTorus j ζ)) ∧
    HasGradientBound ρ (cutoffFactor ρ p) (pairingHomotopy j j' Ψ Ψ' th) x κ α
      (fun i => bondDistToCell Y (j i)) (fun ζ => A' (toTorus j' ζ))
  expectation_shared_le : r₂ ≤ q → ∀ th : ℝ, 0 ≤ th → th ≤ 1 →
    |ballExpectation (cutoffFactor ρ p) (pairingHomotopy j j' Ψ Ψ' th)
      fun ζ => A (toTorus j ζ) - A' (toTorus j' ζ)| ≤ α * Real.exp (-(4 * κ * q))
end YangMills.Construction.TorusComparison
end
