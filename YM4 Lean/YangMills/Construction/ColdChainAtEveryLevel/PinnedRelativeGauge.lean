import YangMills.Construction.ColdChainAtEveryLevel.ChainCoordinatesMovedAndCriticalFormForm
import YangMills.Construction.ColdChainAtEveryLevel.PatchesAndTheGaugeMap
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction
namespace BlockAverages
variable {F : BlockFrame}
open Classical in
def patchBaseSites (S : Finset F.Cell) (z : F.Cell) : Finset (F.Site 0) :=
  (GaugeMap.patchDomain S z).image (GaugeMap.patchSite S z)
open Classical in
def patchPlaquettes (S : Finset F.Cell) (z : F.Cell) : Finset (F.Site 0 × Fin 4 × Fin 4) :=
  (innerPlaquettes S 0).filter fun p => plaquetteCorners p ⊆ patchBaseSites S z
open Classical in
def patchFitBonds (S : Finset F.Cell) (z : F.Cell) (j : ℕ) : Finset (F.Site (j + 1) × Fin 4) :=
  (innerBonds S (j + 1)).filter fun c => ∀ h ∈ centredCube (F.blockSide ^ (j + 1)),
    baseSite c.1 + siteOfCoords 0 h ∈ patchBaseSites S z ∧
      baseSite (c.1 + unitStep (j + 1) c.2) + siteOfCoords 0 h ∈ patchBaseSites S z
def patchAction (a : ℝ) (S : Finset F.Cell) (z : F.Cell) (X : F.FieldChain) (k : F.SiteGauge) : ℝ :=
  ∑ p ∈ patchPlaquettes S z, (1 - ((plaquetteHolonomy (X 0) p : UnitQuaternion) : ℍ[ℝ]).re) +
    a * ∑ j ∈ Finset.range F.top, ∑ c ∈ patchFitBonds S z j,
      gaugedBlockFit (X j) (k (j + 1)) (X (j + 1)) c
def gaugedChainFields (X : F.FieldChain) (Γ : F.SiteGauge) : (j : ℕ) → F.GaugeField j :=
  fun j => gaugeTransform (Γ j) (X j)
def gaugedLink (k Γ : F.SiteGauge) (j : ℕ) (y : F.Site (j + 1)) : UnitQuaternion :=
  Γ (j + 1) y * k (j + 1) y * (Γ j (refineSite y))⁻¹
def balancedLinkAgainst (W : F.FieldChain) (kW : F.SiteGauge) (X : (j : ℕ) → F.GaugeField j) (j : ℕ)
    (y : F.Site (j + 1)) : UnitQuaternion :=
  kW (j + 1) y * balancingGauge (X j) (W j) y
def topCorrection (W : F.FieldChain) (kW : F.SiteGauge) (X : F.FieldChain) (k Γ : F.SiteGauge)
    (y : F.Site F.top) : UnitQuaternion :=
  balancedLinkAgainst W kW (gaugedChainFields X Γ) F.depth y * (gaugedLink k Γ F.depth y)⁻¹
def bondMisfit {j : ℕ} (X : F.GaugeField j) (k : F.Site (j + 1) → UnitQuaternion)
    (X' : F.GaugeField (j + 1)) (c : F.Site (j + 1) × Fin 4) : UnitQuaternion :=
  X' c.1 c.2 * (polarUnit (gaugedContourAverage X k c))⁻¹
def framedUpperField (W : F.FieldChain) (kW : F.SiteGauge) (X : F.FieldChain) (k Γ : F.SiteGauge) (j : ℕ) :
    F.GaugeField (j + 1) := by
  classical exact
    if h : j = F.depth then h ▸ gaugeTransform (topCorrection W kW X k Γ) (X F.top)
    else gaugedChainFields X Γ (j + 1)
def relativeEnergy (a : ℝ) (S : Finset F.Cell) (z : F.Cell) (W : F.FieldChain) (kW : F.SiteGauge)
    (X : F.FieldChain) (k Γ : F.SiteGauge) : ℝ :=
  ∑ p ∈ patchPlaquettes S z,
      ‖((plaquetteHolonomy (gaugedChainFields X Γ 0) p : UnitQuaternion) : ℍ[ℝ]) -
        ((plaquetteHolonomy (W 0) p : UnitQuaternion) : ℍ[ℝ])‖ ^ 2 +
    a * ∑ j ∈ Finset.range F.top, ∑ c ∈ patchFitBonds S z j,
      ‖((bondMisfit (gaugedChainFields X Γ j) (balancedLinkAgainst W kW (gaugedChainFields X Γ) j)
          (framedUpperField W kW X k Γ j) c * (bondMisfit (W j) (kW (j + 1)) (W (j + 1)) c)⁻¹ :
            UnitQuaternion) : ℍ[ℝ]).im‖ ^ 2
def IsPinnedGauge (a C : ℝ) (S : Finset F.Cell) (z : F.Cell) (W : F.FieldChain) (kW : F.SiteGauge)
    (X : F.FieldChain) (k Γ : F.SiteGauge) : Prop :=
  (∀ y, Γ F.top y = 1) ∧
  (∀ j, j + 1 < F.top → ∀ y, baseSite y ∈ patchBaseSites S z →
    gaugedLink k Γ j y = balancedLinkAgainst W kW (gaugedChainFields X Γ) j y) ∧
  (∀ j, j < F.top → (∑ b ∈ innerBonds S j, if baseSite b.1 ∈ patchBaseSites S z ∧
        baseSite (b.1 + unitStep j b.2) ∈ patchBaseSites S z then
      ‖((gaugedChainFields X Γ j b.1 b.2 * (W j b.1 b.2)⁻¹ : UnitQuaternion) : ℍ[ℝ]) - 1‖ ^ 4 else 0) ≤
    (C * Real.sqrt (relativeEnergy a S z W kW X k Γ)) ^ 4) ∧
  ∀ y : F.Site F.top, baseSite y ∈ patchBaseSites S z →
    ‖((topCorrection W kW X k Γ y : UnitQuaternion) : ℍ[ℝ]) - 1‖ ≤
      C * Real.sqrt (relativeEnergy a S z W kW X k Γ)
structure IsCriticalChainOverTop (a θ δ Ca CL s : ℝ) (S : Finset F.Cell) (V V' : F.GaugeField F.top)
    (U : ChainChart F) : Prop where
  critical : ∀ A : ChainChart F, IsStationaryAlong a S (referenceFieldChain S V) V' U A
  split : ∃ Ulin Urest : ChainChart F, ChartEqOnBonds S U (chartSum Ulin Urest) ∧
    ∀ (p : F.Site 0) (y0 : F.Cell) (θ' : ℝ), θ' = θ ∨ θ' = 0 →
      weightedNorm S (referenceFieldChain S V) Ulin (decayWeights F δ θ' p y0) ≤ Ca * s ∧
      weightedNorm S (referenceFieldChain S V) Urest (decayWeights F δ θ' p y0) ≤ CL * s ^ 2
  quartic : ∀ (j : ℕ) (p : F.Site 0) (r : ℝ), j < F.top → 1 ≤ r → r ≤ (F.blockSide : ℝ) ^ (F.top - j) →
    localQuarticSum S (referenceFieldChain S V) U j p r ≤
      (CL * s) ^ 4 * (r / (F.blockSide : ℝ) ^ (F.top - j)) ^ (4 * θ)
  curvature_and_misfits : ∀ (p : F.Site 0) (r : ℝ), 1 ≤ r → r ≤ (F.blockSide : ℝ) ^ F.top →
    localCurvatureSum S (referenceFieldChain S V) U p r ≤
      (CL * s) ^ 2 * (r / (F.blockSide : ℝ) ^ F.top) ^ (2 * θ) ∧
    localMisfitSum S (referenceFieldChain S V) U V' p r ≤
      (CL * s) ^ 2 * (r / (F.blockSide : ℝ) ^ F.top) ^ (2 * θ)
  misfits_on_cells : ∀ (j : ℕ) (z : F.Cell), j < F.top →
    cellMisfitSum S (referenceFieldChain S V) U V' j 4 z ≤
      (CL * s * (4 / (F.blockSide : ℝ) ^ 2) ^ (F.top - 1 - j)) ^ 4 ∧
    cellMisfitSum S (referenceFieldChain S V) U V' j 2 z ≤
      (CL * s * (4 / (F.blockSide : ℝ)) ^ (F.top - 1 - j)) ^ 2
end BlockAverages
end YangMills.Construction
end
