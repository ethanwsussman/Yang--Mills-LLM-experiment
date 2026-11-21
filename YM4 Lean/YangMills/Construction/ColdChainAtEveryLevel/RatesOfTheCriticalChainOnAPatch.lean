import YangMills.Construction.ColdChainAtEveryLevel.CellsOfAPatch
import YangMills.Construction.ColdChainAtEveryLevel.ChangesOfFraming
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction.BlockAverages
variable {F : BlockFrame}
def patchFrame (S : Finset F.Cell) (V : F.GaugeField F.top) (z : F.Cell) {j : ℕ} (x : F.Site j) : UnitQuaternion :=
  GaugeMap.frameChange S V z (baseSite x)
structure HasPatchRates (S : Finset F.Cell) (V : F.GaugeField F.top) (z : F.Cell) (W : F.FieldChain)
    (kW : F.SiteGauge) (j : ℕ)
    (E : F.Site (j + 1) → ℝ) (e : F.Site (j + 1) × Fin 4 → ℝ) : Prop where
  gauge_le : ∀ y ∈ sitesOfCells (patchCells S z) (j + 1), _root_.YangMills.Construction.BlockAverages.distFromOne (kW (j + 1) y) ≤ E y
  axisPath_le : ∀ y ∈ sitesOfCells (patchCells S z) (j + 1), ∀ h ∈ centredCube F.blockSide,
    ∀ σ : Equiv.Perm (Fin 4),
    _root_.YangMills.Construction.BlockAverages.distFromOne ((patchFrame S V z (refineSite y))⁻¹ * pathHolonomy (W j) (refineSite y) (axisPath h σ) *
      patchFrame S V z (refineSite y + siteOfCoords j h)) ≤ E y
  contour_le : ∀ b ∈ innerBonds (patchCells S z) (j + 1), ∀ h ∈ centredCube F.blockSide,
    ∀ σ : Equiv.Perm (Fin 4),
    _root_.YangMills.Construction.BlockAverages.distFromOne (pathHolonomy (W j) (refineSite b.1) (bondContour F.blockSide h σ b.2) *
      (polarUnit (_root_.YangMills.Construction.BlockAverages.contourAverage (W j) b))⁻¹) ≤ e b
  bondLine_le : ∀ b ∈ innerBonds (patchCells S z) (j + 1), ∀ h ∈ centredCube F.blockSide,
    ∀ σ : Equiv.Perm (Fin 4), ∀ r, r < F.blockSide →
    _root_.YangMills.Construction.BlockAverages.distFromOne ((patchFrame S V z (refineSite b.1))⁻¹ *
      pathHolonomy (W j) (refineSite b.1) (axisPath h σ ++ List.replicate r (b.2, true)) *
      patchFrame S V z (refineSite b.1 + siteOfCoords j h + (r : ℤ) • unitStep j b.2)) ≤ e b
  average_le : ∀ b ∈ innerBonds (patchCells S z) (j + 1), _root_.YangMills.Construction.BlockAverages.contourAverage (W j) b ≠ 0 ∧
    _root_.YangMills.Construction.BlockAverages.distFromOne ((patchFrame S V z (refineSite b.1))⁻¹ * polarUnit (_root_.YangMills.Construction.BlockAverages.contourAverage (W j) b) *
      patchFrame S V z (refineSite (b.1 + unitStep (j + 1) b.2))) ≤ e b
  bondGauge_le : ∀ b ∈ innerBonds (patchCells S z) (j + 1), _root_.YangMills.Construction.BlockAverages.distFromOne (kW (j + 1) b.1) ≤ e b
  misfit_le : ∀ b ∈ innerBonds (patchCells S z) (j + 1),
    _root_.YangMills.Construction.BlockAverages.distFromOne (bondMisfit (W j) (kW (j + 1)) (W (j + 1)) b) ≤ e b
def criticalChainPatchRatesStatement : Prop :=
  ∀ a θ δ Ca : ℝ, 0 < a → 0 < θ → θ ≤ 1 / 8 → 0 < δ → δ ≤ 1 / 8 → 0 < Ca →
    ∃ L₀ : ℕ, ∀ L : ℕ, Odd L → L₀ ≤ L → ∀ C₁ : ℝ, 0 < C₁ → ∃ C κ : ℝ, 0 < C ∧ 0 < κ ∧
      ∀ (F : BlockFrame) (m : ℕ) (S : Finset F.Cell), F.blockSide = L → IsAdmissibleAmbient F →
        1024 ≤ m → IsOrthantRegular S m →
        ∀ (s : ℝ) (V : F.GaugeField F.top) (v : F.Site F.top → Fin 4 → imaginaryQuaternions),
          0 < s → s ≤ κ → IsCold S F.top s V →
          ∀ U : ChainChart F, IsCriticalChainOverTop a θ δ Ca C₁ s S V (rotatedField v V) U →
            ∀ z ∈ S,
              (∀ j, j < F.top → ∃ (E : F.Site (j + 1) → ℝ) (e : F.Site (j + 1) × Fin 4 → ℝ),
                (∀ y, 0 ≤ E y) ∧ (∀ b, 0 ≤ e b) ∧
                ∑ y ∈ sitesOfCells (patchCells S z) (j + 1), E y ^ 4 ≤ (C * s) ^ 4 ∧
                ∑ b ∈ innerBonds (patchCells S z) (j + 1), e b ^ 4 ≤ (C * s) ^ 4 ∧
                ∑ b ∈ innerBonds (patchCells S z) (j + 1),
                  _root_.YangMills.Construction.BlockAverages.distFromOne (bondMisfit (criticalFieldChain S V v U j) (criticalGauge S V U (j + 1))
                    (criticalFieldChain S V v U (j + 1)) b) ^ 2 ≤ (C * s) ^ 2 ∧
                HasPatchRates S V z (criticalFieldChain S V v U) (criticalGauge S V U) j E e) ∧
              (∀ b ∈ innerBonds (patchCells S z) F.top,
                _root_.YangMills.Construction.BlockAverages.distFromOne ((patchFrame S V z b.1)⁻¹ * criticalFieldChain S V v U F.top b.1 b.2 *
                  patchFrame S V z (b.1 + unitStep F.top b.2)) ≤ C * s) ∧
              ∀ j, j < F.top → ∑ b ∈ innerBonds (patchCells S z) j,
                _root_.YangMills.Construction.BlockAverages.distFromOne (gaugeTransform (fun x => (patchFrame S V z x)⁻¹)
                  (criticalFieldChain S V v U j) b.1 b.2) ^ 4 ≤ (C * s) ^ 4
end YangMills.Construction.BlockAverages
end
