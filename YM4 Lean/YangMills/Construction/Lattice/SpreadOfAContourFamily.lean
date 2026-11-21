import YangMills.Construction.Conventions.StandingParameters
import YangMills.Construction.Lattice.BlockAveraging
import YangMills.Construction.Matrices.SpecialUnitaryAngles
import Mathlib
noncomputable section
namespace YangMills.Construction.PeriodicLattice
open YangMills.Construction.Matrices
variable {L m : ℕ} {j j' : ℤ}
def blockPlaquetteDefect (y : Site L m j) (V : Bond L m j' → ComplexMatrix2) : ℝ :=
  ⨆ p : (plaquettesInside (unitBlock y) : Set (Plaquette L m j')),
    ComplexMatrix2.operatorNorm (plaquetteHolonomy V p - 1)
def contourSwapConstant (L : ℕ) : ℝ := 3 / 2 * ((L : ℝ) - 1) ^ 2
def ContourFamilySpread : Prop :=
  ∀ L m K : ℕ, Conventions.IsAdmissibleBlockingFactor L → 0 < m → ∀ n : ℕ, n < K →
  ∀ (y : SiteAtLevel L m K (n + 1)) (V : BondAtLevel L m K n → ComplexMatrix2),
    IsGaugeField compactGaugeGroup (bondsInside (unitBlock y) : Set (BondAtLevel L m K n)) V →
    ∀ x : SiteAtLevel L m K n, (x : FourTorus L m) ∈ unitBlock y →
      (∀ Γ ∈ contourSet y x, ∀ Γ' ∈ contourSet y x,
        ComplexMatrix2.operatorNorm (pathHolonomy V Γ - pathHolonomy V Γ') ≤
          contourSwapConstant L * blockPlaquetteDefect y V) ∧
      ComplexMatrix2.familyDiameter (contourHolonomies V y x) ≤
        contourSwapConstant L * blockPlaquetteDefect y V ∧
      (HasContourMean V y x →
        ComplexMatrix2.IsLogMean compactGaugeGroup (contourHolonomies V y x)
          (meanContourHolonomy V y x) ∧
        ∀ Γ ∈ contourSet y x,
          ComplexMatrix2.operatorNorm (pathHolonomy V Γ * (meanContourHolonomy V y x)⁻¹ - 1) ≤
            ComplexMatrix2.rotationAngle (pathHolonomy V Γ * (meanContourHolonomy V y x)⁻¹) ∧
          ComplexMatrix2.rotationAngle (pathHolonomy V Γ * (meanContourHolonomy V y x)⁻¹) ≤
            2 * Real.pi / (3 * Real.sqrt 3) * contourSwapConstant L *
              blockPlaquetteDefect y V ∧
          2 * Real.pi / (3 * Real.sqrt 3) * contourSwapConstant L * blockPlaquetteDefect y V =
            Real.pi / Real.sqrt 3 * ((L : ℝ) - 1) ^ 2 * blockPlaquetteDefect y V)
end YangMills.Construction.PeriodicLattice
end
