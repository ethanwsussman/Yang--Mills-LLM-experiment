import YangMills.Construction.ColdChainAtEveryLevel.RatesOfTheCriticalChainOnAPatch
import YangMills.Construction.ColdChainAtEveryLevel.RotationOfAFramingOfLevelZero
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction.BlockAverages
def cellGeneratorNearBlockMeanStatement : Prop :=
  ∀ (F : BlockFrame) (m : ℕ) (S : Finset F.Cell) (V : F.GaugeField F.top) (W : F.FieldChain) (kW : F.SiteGauge)
    (X : F.FieldChain) (k : F.SiteGauge)
    (γ : F.Site 0 → UnitQuaternion) (ξ : F.Site 0 → imaginaryQuaternions) (z y₀ : F.Cell) (q r : ℝ)
    (E : (j : ℕ) → F.Site (j + 1) → ℝ),
    Odd F.blockSide → 5 ≤ F.blockSide → IsAdmissibleAmbient F → 1024 ≤ m → IsOrthantRegular S m →
    y₀ ∈ patchCells S z → 0 ≤ q → 0 ≤ r →
    36 * (F.blockSide : ℝ) * q + 8 * r ≤ 1 / 8 → (∀ j y, 0 ≤ E j y) →
    (∀ j, j < F.top → ∑ y ∈ sitesOfCells (patchCells S z) (j + 1), E j y ^ 4 ≤ r ^ 4) →
    (∀ j, j < F.top → ∀ y ∈ sitesOfCells (patchCells S z) (j + 1), distFromOne (kW (j + 1) y) ≤ E j y) →
    (∀ j, j < F.top → ∀ y ∈ sitesOfCells (patchCells S z) (j + 1), ∀ h ∈ centredCube F.blockSide,
      ∀ π : Equiv.Perm (Fin 4),
      distFromOne ((patchFrame S V z (refineSite y))⁻¹ * pathHolonomy (W j) (refineSite y) (axisPath h π) *
        patchFrame S V z (refineSite y + siteOfCoords j h)) ≤ E j y) →
    (∀ j, j < F.top → ∑ b ∈ patchInnerBonds S z j,
      distFromOne (relativeDefect W X (pinnedGaugeOfBase W kW X k γ) j b.1 b.2) ^ 4 ≤ q ^ 4) →
    (∀ j, j < F.top → ∀ y ∈ sitesOfCells (patchCells S z) (j + 1),
      relativePathAverage (gaugeTransform (pinnedGaugeLevel W kW X k γ j) (X j)) (W j) y ≠ 0) →
    ‖adjointAction (patchFrame S V z y₀)⁻¹
        (pinnedGaugeGenerator W kW X k γ (fun x => (ξ x : ℍ[ℝ])) F.top y₀) -
        (1 / ((F.blockSide : ℝ) ^ F.top) ^ 4) • ∑ h ∈ centredCube (F.blockSide ^ F.top),
          adjointAction (GaugeMap.frameChange S V z (cellCentre 0 y₀ + siteOfCoords 0 h))⁻¹
            (ξ (cellCentre 0 y₀ + siteOfCoords 0 h) : ℍ[ℝ])‖ ^ 4 ≤
      9 * (36 * (F.blockSide : ℝ) * q + 8 * r) ^ 4 *
        (∑ x ∈ sitesOfCells ({y₀} : Finset F.Cell) 0, ‖(ξ x : ℍ[ℝ])‖ ^ 4) /
        ((F.blockSide : ℝ) ^ F.top) ^ 4
end YangMills.Construction.BlockAverages
end
