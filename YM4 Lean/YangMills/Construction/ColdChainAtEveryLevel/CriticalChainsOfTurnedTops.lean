import YangMills.Construction.ColdChainAtEveryLevel.BoundsOfASplitCriticalPoint
import YangMills.Construction.ColdChainAtEveryLevel.PinnedRelativeGauge
import YangMills.Construction.ColdChainAtEveryLevel.PropertiesOfTheColdChainForm
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction
namespace BlockAverages
variable {F : BlockFrame}
def rotatedTop {k : ℕ} (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions) (ζ : Fin k → ℝ)
    (V : F.GaugeField F.top) : F.GaugeField F.top :=
  rotatedField (bondSpread c X ζ) V
def HasHolomorphicExtension {k : ℕ} (ρ : ℝ) (f : (Fin k → ℝ) → ℝ) : Prop :=
  ∃ g : (Fin k → ℂ) → ℂ, DifferentiableOn ℂ g {ζ | ∀ l, ‖ζ l‖ < ρ} ∧
    ∀ ζ : Fin k → ℝ, (∀ l, |ζ l| < ρ) → g (fun l => (ζ l : ℂ)) = f ζ
def imaginaryComponent (e : Fin 3) (w : imaginaryQuaternions) : ℝ :=
  ![(w : ℍ[ℝ]).imI, (w : ℍ[ℝ]).imJ, (w : ℍ[ℝ]).imK] e
def mixedDerivativeChart {k m : ℕ} (T : (Fin k → ℝ) → ChainChart F) (e : Fin m ↪ Fin k) : ChainChart F :=
  ⟨fun x i => iteratedFDeriv ℝ m (fun ζ => (T ζ).fine x i) 0 (fun l => Pi.single (e l) 1),
    fun j y i => iteratedFDeriv ℝ m (fun ζ => (T ζ).coarse j y i) 0 (fun l => Pi.single (e l) 1)⟩
structure IsRotatedChain (a θ δ Cₐ ρL ρ' CL s : ℝ) (Cₖ : ℕ → ℝ) (S : Finset F.Cell) (V : F.GaugeField F.top)
    {k : ℕ} (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions) (U : ChainChart F)
    (T : (Fin k → ℝ) → ChainChart F) : Prop where
  eq_at_zero : ChartEqOnBonds S (T 0) U
  holomorphic_fine : ∀ b ∈ innerBonds S 0, ∀ e : Fin 3,
    HasHolomorphicExtension (ρ' / k) fun ζ => imaginaryComponent e ((T ζ).fine b.1 b.2)
  holomorphic_coarse : ∀ j, j + 1 < F.top → ∀ b ∈ innerBonds S (j + 1), ∀ e : Fin 3,
    HasHolomorphicExtension (ρ' / k) fun ζ => imaginaryComponent e ((T ζ).coarse j b.1 b.2)
  analyticAt_fine : ∀ b ∈ innerBonds S 0, AnalyticAt ℝ (fun ζ => (T ζ).fine b.1 b.2) 0
  analyticAt_coarse : ∀ j, j + 1 < F.top → ∀ b ∈ innerBonds S (j + 1),
    AnalyticAt ℝ (fun ζ => (T ζ).coarse j b.1 b.2) 0
  mem_slice : ∀ ζ : Fin k → ℝ, (∀ l, |ζ l| < ρ' / k) →
    GaugeMap.InGaugeSlice S V (referenceFieldChain S V 0) (T ζ).fine
  small : ∀ ζ : Fin k → ℝ, (∀ l, |ζ l| < ρ' / k) → supWeightedNorm S δ (referenceFieldChain S V) (T ζ) ≤ ρL
  critical : ∀ (ζ : Fin k → ℝ) (σ : ℝ), (∀ l, |ζ l| ≤ σ) → σ < ρ' / k →
    IsCriticalChainOverTop a θ δ Cₐ CL (s + k * σ) S V (rotatedTop c X ζ V) (T ζ)
  floor : ∀ ζ : Fin k → ℝ, (∀ l, |ζ l| < ρ' / k) → ∀ A : ChainChart F,
    GaugeMap.InGaugeSlice S V (referenceFieldChain S V 0) A.fine →
    (1 / 4) * quadraticFormNormSq a S (referenceFieldChain S V) A (oneSiteWeights F) ≤
      deriv (deriv fun τ : ℝ =>
        chartAction a S (referenceFieldChain S V) (chartMove (T ζ) A τ) (rotatedTop c X ζ V)) 0
  decay : ∀ (m : ℕ) (e : Fin m ↪ Fin k) (z : F.Cell), 1 ≤ m →
    localNorm S (referenceFieldChain S V) (mixedDerivativeChart T e) (oneSiteWeights F) z ≤
      Cₖ m * Real.exp (-δ * bondListDistance z (c ∘ e))
def siteAtSameOffset {F' : BlockFrame} (Y : F.Cell) (Y' : F'.Cell) {j : ℕ} (x : F.Site j) : F'.Site j :=
  cellCentre j Y' + siteOfCoords j fun i => ((x - cellCentre j Y) i).valMinAbs
def chartAtSameOffsets {F' : BlockFrame} (Y : F.Cell) (Y' : F'.Cell) (U' : ChainChart F') : ChainChart F :=
  ⟨fun x i => U'.fine (siteAtSameOffset Y Y' x) i, fun j y i => U'.coarse j (siteAtSameOffset Y Y' y) i⟩
def rotatedCriticalChainsStatement : Prop :=
  ∀ a : ℝ, 0 < a → ∃ θ δ Cₐ : ℝ, 0 < θ ∧ θ ≤ 1 / 8 ∧ 0 < δ ∧ δ ≤ 1 / 8 ∧ 0 < Cₐ ∧
    ∃ L₀ : ℕ, ∀ L : ℕ, Odd L → L₀ ≤ L → ∃ (ρL ρ' sL CL : ℝ) (Cₖ : ℕ → ℝ),
      0 < ρL ∧ 0 < ρ' ∧ ρ' ≤ ρL ∧ 0 < sL ∧ 0 < CL ∧ (∀ k, 0 < Cₖ k) ∧
      (∀ (F : BlockFrame) (m : ℕ) (S : Finset F.Cell), F.blockSide = L → IsAdmissibleAmbient F → 1024 ≤ m →
        IsOrthantRegular S m →
        ∀ (s : ℝ) (V : F.GaugeField F.top), 0 < s → s ≤ sL → IsCold S F.top s V →
          ∃ U : ChainChart F, IsSliceCriticalPoint a θ δ Cₐ ρL CL s S V U ∧
            SliceCriticalPointLocalBounds a θ CL s S V U ∧
            ∀ (k : ℕ) (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions), 1 ≤ k →
              AreUnitVectors X →
              ∃ T : (Fin k → ℝ) → ChainChart F, IsRotatedChain a θ δ Cₐ ρL ρ' CL s Cₖ S V c X U T) ∧
      ∀ (F F' : BlockFrame) (m : ℕ) (S : Finset F.Cell) (S' : Finset F'.Cell), F.blockSide = L →
        F'.blockSide = L → F'.depth = F.depth →
        IsAdmissibleAmbient F → IsAdmissibleAmbient F' → 1024 ≤ m → IsOrthantRegular S m → IsOrthantRegular S' m →
        ∀ (s : ℝ) (V : F.GaugeField F.top) (V' : F'.GaugeField F'.top) (Y : F.Cell) (Y' : F'.Cell) (r : ℕ),
          0 < s → s ≤ sL → IsCold S F.top s V → IsCold S' F'.top s V' → 108 ≤ r → AgreeOnBall S V S' V' Y Y' r →
          ∀ (U : ChainChart F) (U' : ChainChart F'),
            IsSliceCriticalPoint a θ δ Cₐ ρL CL s S V U →
            IsSliceCriticalPoint a θ δ Cₐ ρL CL s S' V' U' →
            (∀ z : F.Cell, cellSupDist z Y ≤ 3 →
              localNorm S (referenceFieldChain S V) (chartMove U (chartAtSameOffsets Y Y' U') (-1))
                  (oneSiteWeights F) z ≤
                CL * s * Real.exp (-δ * r / 4)) ∧
            ∀ (k : ℕ) (h : Fin k → (Fin 4 → ℤ) × Fin 4) (X : Fin k → imaginaryQuaternions), 1 ≤ k →
              (∀ l, BondWithinRadius (r / 2) (h l)) → AreUnitVectors X →
              ∀ (T : (Fin k → ℝ) → ChainChart F) (T' : (Fin k → ℝ) → ChainChart F'),
                IsRotatedChain a θ δ Cₐ ρL ρ' CL s Cₖ S V (offsetBonds Y h) X U T →
                IsRotatedChain a θ δ Cₐ ρL ρ' CL s Cₖ S' V' (offsetBonds Y' h) X U' T' →
                ∀ (m' : ℕ) (e : Fin m' ↪ Fin k) (z : F.Cell), 1 ≤ m' → cellSupDist z Y ≤ 3 →
                  localNorm S (referenceFieldChain S V)
                      (chartMove (mixedDerivativeChart T e) (chartAtSameOffsets Y Y' (mixedDerivativeChart T' e)) (-1))
                      (oneSiteWeights F) z ≤
                    Cₖ m' * Real.exp (-δ * r / 4)
end BlockAverages
end YangMills.Construction
end
