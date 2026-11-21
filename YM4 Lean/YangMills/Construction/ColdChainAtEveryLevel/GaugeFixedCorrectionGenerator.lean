import YangMills.Construction.ColdChainAtEveryLevel.PinOfAFramingOnAPatch
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction
open LatticeFractionalIntegration PinnedGauge PatchLatticeChart
namespace BlockAverages
def pinnedCorrectionGeneratorStatement : Prop :=
  ∀ (F : BlockFrame) (m : ℕ) (S : Finset F.Cell) (V : F.GaugeField F.top) (W : F.FieldChain) (kW : F.SiteGauge)
    (X : F.FieldChain) (k : F.SiteGauge) (γ : Lattice4 → UnitQuaternion) (ξ : Lattice4 → imaginaryQuaternions)
    (z y : F.Cell) (q r : ℝ) (E : (j : ℕ) → F.Site (j + 1) → ℝ),
    Odd F.blockSide → 5 ≤ F.blockSide → IsAdmissibleAmbient F → 1024 ≤ m → IsOrthantRegular S m → z ∈ S →
    y ∈ patchCells S z → 0 ≤ q → 0 ≤ r →
    36 * (F.blockSide : ℝ) * q + 8 * r ≤ 1 / 8 → (∀ j y, 0 ≤ E j y) →
    (∀ j, j < F.top → ∑ y ∈ sitesOfCells (patchCells S z) (j + 1), E j y ^ 4 ≤ r ^ 4) →
    (∀ j, j < F.top → ∀ y ∈ sitesOfCells (patchCells S z) (j + 1), normSubOne (kW (j + 1) y) ≤ E j y) →
    (∀ j, j < F.top → ∀ y ∈ sitesOfCells (patchCells S z) (j + 1), ∀ h ∈ centredCube F.blockSide,
      ∀ π : Equiv.Perm (Fin 4),
      normSubOne ((patchFrame S V z (refineSite y))⁻¹ * pathHolonomy (W j) (refineSite y) (axisPath h π) *
        patchFrame S V z (refineSite y + siteOfCoords j h)) ≤ E j y) →
    (∀ j, j < F.top → ∑ b ∈ patchInnerBonds S z j,
      normSubOne (relativeDefect W X
        (pinnedGaugeOfBase W kW X k (siteGaugeOfLatticeGauge S V z γ)) j b.1 b.2) ^ 4 ≤ q ^ 4) →
    (∀ j, j < F.top → ∀ y ∈ sitesOfCells (patchCells S z) (j + 1),
      relativePathAverage
        (gaugeTransform (pinnedGaugeLevel W kW X k (siteGaugeOfLatticeGauge S V z γ) j) (X j)) (W j) y ≠ 0) →
    ∃ ζ : ℍ[ℝ], ζ.re = 0 ∧
      HasDerivAt (fun τ : ℝ =>
          ((pinnedTopCorrection S V z W kW X k (PinnedGaugeData.rotateAlong ξ τ γ) y : UnitQuaternion) : ℍ[ℝ]))
        (ζ * ((pinnedTopCorrection S V z W kW X k γ y : UnitQuaternion) : ℍ[ℝ])) 0 ∧
      ‖ζ - (pinnedGaugeDataOfPatch S V z W kW X k).cellMean y (fun x => (ξ x : ℍ[ℝ]))‖ ^ 4 ≤
        9 * (36 * (F.blockSide : ℝ) * q + 8 * r) ^ 4 *
            (∑ x ∈ (pinnedGaugeDataOfPatch S V z W kW X k).cellSites y, ‖(ξ x : ℍ[ℝ])‖ ^ 4) /
          (((pinnedGaugeDataOfPatch S V z W kW X k).cellSide : ℕ) : ℝ) ^ 4
end BlockAverages
end YangMills.Construction
end
