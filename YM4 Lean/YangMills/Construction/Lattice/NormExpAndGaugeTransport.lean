import YangMills.Construction.Conventions.StandingParameters
import YangMills.Construction.Lattice.GaugeConfigurations
import Mathlib
open YangMills.Construction.Matrices
noncomputable section
namespace YangMills.Construction.PeriodicLattice
variable {L m : ℕ} {j : ℤ}
def endpointsOf (B : Set (Bond L m j)) : Set (Site L m j) :=
  {x | ∃ b ∈ B, x = b.source ∨ x = b.target}
def NormExpAndGaugeTransport : Prop :=
  ((∀ X Y : ComplexMatrix2,
      ComplexMatrix2.operatorNorm (X * Y) ≤
        ComplexMatrix2.operatorNorm X * ComplexMatrix2.operatorNorm Y) ∧
    ComplexMatrix2.operatorNorm (1 : ComplexMatrix2) = 1 ∧
    (∀ X u v : ComplexMatrix2, u ∈ Matrix.unitaryGroup (Fin 2) ℂ →
      v ∈ Matrix.unitaryGroup (Fin 2) ℂ →
      ComplexMatrix2.operatorNorm (u * X * v) = ComplexMatrix2.operatorNorm X) ∧
    ∀ g ∈ ComplexMatrix2.specialUnitary, ∀ X : ComplexMatrix2,
      ComplexMatrix2.operatorNorm (g * X * g⁻¹ - 1) = ComplexMatrix2.operatorNorm (X - 1) ∧
        ComplexMatrix2.operatorNorm (ComplexMatrix2.conjugateBy g X) =
          ComplexMatrix2.operatorNorm X) ∧
  ((∀ A ∈ ComplexMatrix2.traceless,
      ComplexMatrix2.matExp (Complex.I • A) ∈ ComplexMatrix2.unitDeterminant) ∧
    ∀ A ∈ ComplexMatrix2.hermitianTraceless,
      ComplexMatrix2.matExp (Complex.I • A) ∈ ComplexMatrix2.specialUnitary) ∧
  (∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∀ m K n : ℕ, 0 < m → 0 < K → n ≤ K →
    ∀ (B : Set (BondAtLevel L m K n)) (U : BondAtLevel L m K n → ComplexMatrix2)
      (u : SiteAtLevel L m K n → ComplexMatrix2),
      IsReversalClosed B → IsGaugeField complexGaugeGroup B U →
      (∀ x ∈ endpointsOf B, u x ∈ compactGaugeGroup) →
      IsGaugeField complexGaugeGroup B (gaugeTransform u U) ∧
      (IsGaugeField compactGaugeGroup B U →
        IsGaugeField compactGaugeGroup B (gaugeTransform u U)) ∧
      (∀ (γ : List (BondAtLevel L m K n)) (x x' : SiteAtLevel L m K n),
        x ∈ endpointsOf B → IsBondPathFromTo γ x x' → (∀ b ∈ γ, b ∈ B) →
        pathHolonomy (gaugeTransform u U) γ = u x * pathHolonomy U γ * (u x')⁻¹) ∧
      ∀ p : PlaquetteAtLevel L m K n, (∀ b ∈ p.boundaryBonds, b ∈ B) →
        plaquetteHolonomy (gaugeTransform u U) p =
          u p.origin * plaquetteHolonomy U p * (u p.origin)⁻¹) ∧
  ∀ g ∈ ComplexMatrix2.specialUnitary,
    (∀ Z : ComplexMatrix2,
      ComplexMatrix2.matExp (g * Z * g⁻¹) = g * ComplexMatrix2.matExp Z * g⁻¹) ∧
    ∀ X : ComplexMatrix2, ComplexMatrix2.operatorNorm (X - 1) < 1 →
      ComplexMatrix2.operatorNorm (g * X * g⁻¹ - 1) < 1 ∧
        ComplexMatrix2.logSeries (g * X * g⁻¹) = g * ComplexMatrix2.logSeries X * g⁻¹
end YangMills.Construction.PeriodicLattice
