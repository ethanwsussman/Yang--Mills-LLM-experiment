import YangMills.Construction.Conventions.StandingParameters
import YangMills.Construction.Lattice.WilsonGibbsMeasure
import Mathlib
open Set
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.PeriodicLattice
variable {L m : ℕ} {j : ℤ}
def Plaquette.IsBoundedBy (p : Plaquette L m j) (e₁ e₂ e₃ e₄ : Bond L m j) : Prop :=
  (e₁.source = p.origin ∧ e₁.target = p.origin + unitStep L m j p.firstAxis) ∧
  (e₂.source = p.origin + unitStep L m j p.firstAxis ∧
    e₂.target = p.origin + unitStep L m j p.firstAxis + unitStep L m j p.secondAxis) ∧
  (e₃.source = p.origin + unitStep L m j p.firstAxis + unitStep L m j p.secondAxis ∧
    e₃.target = p.origin + unitStep L m j p.secondAxis) ∧
  (e₄.source = p.origin + unitStep L m j p.secondAxis ∧ e₄.target = p.origin)
def cyclicBoundaryPaths (e₁ e₂ e₃ e₄ : Bond L m j) : List (List (Bond L m j)) :=
  [[e₁, e₂, e₃, e₄], [e₂, e₃, e₄, e₁], [e₃, e₄, e₁, e₂], [e₄, e₁, e₂, e₃]]
def PlaquetteHolonomyTraceBounds : Prop :=
  ∀ s : Conventions.StandingParameters,
    (∀ j : ℤ, -(s.m : ℤ) ≤ j →
      ∀ (p : Plaquette s.L s.m j) (e₁ e₂ e₃ e₄ : Bond s.L s.m j), p.IsBoundedBy e₁ e₂ e₃ e₄ →
      ∀ (E : Set (Bond s.L s.m j)) (U : Bond s.L s.m j → Matrices.ComplexMatrix2),
        IsReversalClosed E → IsGaugeField compactGaugeGroup E U →
        e₁ ∈ E → e₂ ∈ E → e₃ ∈ E → e₄ ∈ E →
        (plaquetteHolonomy U p = U e₁ * U e₂ * U e₃ * U e₄ ∧
          plaquetteHolonomy U p ∈ compactGaugeGroup ∧
          (∃ t ∈ Icc (-1 : ℝ) 1,
            Matrices.ComplexMatrix2.halfTrace (plaquetteHolonomy U p) = t) ∧
          1 - (1 / 2) * (Matrices.ComplexMatrix2.fullTrace (plaquetteHolonomy U p)).re ∈
            Icc (0 : ℝ) 2) ∧
        (U e₂ * U e₃ * U e₄ * U e₁ = (U e₁)⁻¹ * plaquetteHolonomy U p * U e₁ ∧
          U e₁ ∈ compactGaugeGroup ∧
          U e₃ * U e₄ * U e₁ * U e₂ =
            (U e₁ * U e₂)⁻¹ * plaquetteHolonomy U p * (U e₁ * U e₂) ∧
          U e₁ * U e₂ ∈ compactGaugeGroup ∧
          U e₄ * U e₁ * U e₂ * U e₃ =
            (U e₁ * U e₂ * U e₃)⁻¹ * plaquetteHolonomy U p * (U e₁ * U e₂ * U e₃) ∧
          U e₁ * U e₂ * U e₃ ∈ compactGaugeGroup ∧
          U e₄.opposite * U e₃.opposite * U e₂.opposite * U e₁.opposite =
            (plaquetteHolonomy U p)⁻¹ ∧
          (plaquetteHolonomy U p)⁻¹ = (plaquetteHolonomy U p).conjTranspose ∧
          ∀ γ ∈ cyclicBoundaryPaths e₁ e₂ e₃ e₄,
            (1 / 2) * (Matrices.ComplexMatrix2.fullTrace (pathHolonomy U γ)).re =
                (1 / 2) * (Matrices.ComplexMatrix2.fullTrace (plaquetteHolonomy U p)).re ∧
            (1 / 2) * (Matrices.ComplexMatrix2.fullTrace (pathHolonomy U (reversePath γ))).re =
              (1 / 2) * (Matrices.ComplexMatrix2.fullTrace (plaquetteHolonomy U p)).re)) ∧
    ∀ (p : Plaquette s.L s.m ((s.K : ℕ) : ℤ)),
      ∀ U ∈ compactGaugeFields s.L s.m ((s.K : ℕ) : ℤ), plaquetteCost U p ∈ Icc (0 : ℝ) 2
end YangMills.Construction.PeriodicLattice
