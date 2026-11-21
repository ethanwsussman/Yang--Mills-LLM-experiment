import YangMills.Construction.ColdChainAtEveryLevel.PinnedRelativeGauge
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction.TwistedTops
open YangMills.Construction.BlockAverages YangMills.Construction.GaugeMap
variable {F : BlockFrame}
def twistedTop {k : ℕ} (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions) (ζ : Fin k → ℝ)
    (V : F.GaugeField F.top) : F.GaugeField F.top :=
  rotatedField (bondSpread c X ζ) V
def IsRestrictionOfHolomorphic {k : ℕ} (ρ : ℝ) (f : (Fin k → ℝ) → ℝ) : Prop :=
  ∃ g : (Fin k → ℂ) → ℂ, DifferentiableOn ℂ g {ζ | ∀ l, ‖ζ l‖ < ρ} ∧
    ∀ ζ : Fin k → ℝ, (∀ l, |ζ l| < ρ) → g (fun l => (ζ l : ℂ)) = f ζ
def imagCoord (e : Fin 3) (w : imaginaryQuaternions) : ℝ :=
  ![(w : ℍ[ℝ]).imI, (w : ℍ[ℝ]).imJ, (w : ℍ[ℝ]).imK] e
def chartMixedDeriv {k m : ℕ} (T : (Fin k → ℝ) → ChainChart F) (e : Fin m ↪ Fin k) : ChainChart F :=
  ⟨fun x i => iteratedFDeriv ℝ m (fun ζ => (T ζ).fine x i) 0 (fun l => Pi.single (e l) 1),
    fun j y i => iteratedFDeriv ℝ m (fun ζ => (T ζ).coarse j y i) 0 (fun l => Pi.single (e l) 1)⟩
structure IsTwistedCriticalFamily (a del rL r' : ℝ) (S : Finset F.Cell) (V : F.GaugeField F.top)
    {k : ℕ} (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions)
    (T : (Fin k → ℝ) → ChainChart F) : Prop where
  mem_gaugeSlice : ∀ ζ : Fin k → ℝ, (∀ l, |ζ l| < r' / k) →
    InGaugeSlice S V (referenceFieldChain S V 0) (T ζ).fine
  norm_le : ∀ ζ : Fin k → ℝ, (∀ l, |ζ l| < r' / k) →
    supWeightedNorm S del (referenceFieldChain S V) (T ζ) ≤ rL
  stationary : ∀ ζ : Fin k → ℝ, (∀ l, |ζ l| < r' / k) → ∀ A : ChainChart F,
    IsStationaryAlong a S (referenceFieldChain S V) (twistedTop c X ζ V) (T ζ) A
structure IsTwistedCriticalChain (a θ del Ca rL r' CL s : ℝ) (Ck : ℕ → ℝ) (S : Finset F.Cell)
    (V : F.GaugeField F.top) {k : ℕ} (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions)
    (U : ChainChart F) (T : (Fin k → ℝ) → ChainChart F) : Prop where
  eq_zero : ChartEqOnBonds S (T 0) U
  holo_fine : ∀ b ∈ innerBonds S 0, ∀ e : Fin 3,
    IsRestrictionOfHolomorphic (r' / k) fun ζ => imagCoord e ((T ζ).fine b.1 b.2)
  holo_coarse : ∀ j, j + 1 < F.top → ∀ b ∈ innerBonds S (j + 1), ∀ e : Fin 3,
    IsRestrictionOfHolomorphic (r' / k) fun ζ => imagCoord e ((T ζ).coarse j b.1 b.2)
  analytic_fine : ∀ b ∈ innerBonds S 0, AnalyticAt ℝ (fun ζ => (T ζ).fine b.1 b.2) 0
  analytic_coarse : ∀ j, j + 1 < F.top → ∀ b ∈ innerBonds S (j + 1),
    AnalyticAt ℝ (fun ζ => (T ζ).coarse j b.1 b.2) 0
  mem_gaugeSlice : ∀ ζ : Fin k → ℝ, (∀ l, |ζ l| < r' / k) →
    InGaugeSlice S V (referenceFieldChain S V 0) (T ζ).fine
  norm_le : ∀ ζ : Fin k → ℝ, (∀ l, |ζ l| < r' / k) →
    supWeightedNorm S del (referenceFieldChain S V) (T ζ) ≤ rL
  isCritical : ∀ (ζ : Fin k → ℝ) (σ : ℝ), (∀ l, |ζ l| ≤ σ) → σ < r' / k →
    IsCriticalChainOverTop a θ del Ca CL (s + k * σ) S V (twistedTop c X ζ V) (T ζ)
  hessian_ge : ∀ ζ : Fin k → ℝ, (∀ l, |ζ l| < r' / k) → ∀ A : ChainChart F,
    InGaugeSlice S V (referenceFieldChain S V 0) A.fine →
    (1 / 4) * quadraticFormNormSq a S (referenceFieldChain S V) A (oneSiteWeights F) ≤
      deriv (deriv fun τ : ℝ =>
        chartAction a S (referenceFieldChain S V) (chartMove (T ζ) A τ) (twistedTop c X ζ V)) 0
  mixedDeriv_decay : ∀ (m : ℕ) (e : Fin m ↪ Fin k) (z : F.Cell), 1 ≤ m →
    localNorm S (referenceFieldChain S V) (chartMixedDeriv T e) (oneSiteWeights F) z ≤
      Ck m * Real.exp (-del * bondListDistance z (c ∘ e))
def translateSite {F' : BlockFrame} (Y : F.Cell) (Y' : F'.Cell) {j : ℕ} (x : F.Site j) : F'.Site j :=
  cellCentre j Y' + siteOfCoords j fun i => ((x - cellCentre j Y) i).valMinAbs
def chartTranslate {F' : BlockFrame} (Y : F.Cell) (Y' : F'.Cell) (U' : ChainChart F') : ChainChart F :=
  ⟨fun x i => U'.fine (translateSite Y Y' x) i, fun j y i => U'.coarse j (translateSite Y Y' y) i⟩
structure HasTopLocalBounds (θ CL s : ℝ) (S : Finset F.Cell) (V V' : F.GaugeField F.top)
    (U : ChainChart F) : Prop where
  quartic_le : ∀ (j : ℕ) (p : F.Site 0) (r : ℝ), j < F.top → 1 ≤ r → r ≤ (F.blockSide : ℝ) ^ (F.top - j) →
    localQuarticSum S (referenceFieldChain S V) U j p r ≤
      (CL * s) ^ 4 * (r / (F.blockSide : ℝ) ^ (F.top - j)) ^ (4 * θ)
  curvature_misfit_le : ∀ (p : F.Site 0) (r : ℝ), 1 ≤ r → r ≤ (F.blockSide : ℝ) ^ F.top →
    localCurvatureSum S (referenceFieldChain S V) U p r ≤
        (CL * s) ^ 2 * (r / (F.blockSide : ℝ) ^ F.top) ^ (2 * θ) ∧
      localMisfitSum S (referenceFieldChain S V) U V' p r ≤
        (CL * s) ^ 2 * (r / (F.blockSide : ℝ) ^ F.top) ^ (2 * θ)
  cell_misfit_le : ∀ (j : ℕ) (z : F.Cell), j < F.top →
    cellMisfitSum S (referenceFieldChain S V) U V' j 4 z ≤
        (CL * s * (4 / (F.blockSide : ℝ) ^ 2) ^ (F.top - 1 - j)) ^ 4 ∧
      cellMisfitSum S (referenceFieldChain S V) U V' j 2 z ≤
        (CL * s * (4 / (F.blockSide : ℝ)) ^ (F.top - 1 - j)) ^ 2
end YangMills.Construction.TwistedTops
end
