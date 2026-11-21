import YangMills.Construction.ColdStepAtMirrorFrames.MirrorTorusAndFrames
import Mathlib
set_option autoImplicit false
noncomputable section
open YangMills.Construction.BlockAverages
namespace YangMills.Construction
namespace ColdStepAtMirrorFrames
variable {F : BlockFrame}
def transferSite (G : BlockFrame) {k : ℕ} (x : F.Site k) : G.Site k := siteOfCoords k (siteCoords x)
def transferField (G : BlockFrame) {k : ℕ} (W : F.GaugeField k) : G.GaugeField k :=
  fun x i => W (transferSite F x) i
structure SharePeriods (F G : BlockFrame) (K : ℕ) : Prop where
  blockSide_eq : F.blockSide = G.blockSide
  blockSide_odd : Odd F.blockSide
  extent_pos_left : ∀ i, 0 < F.extent i
  extent_pos_right : ∀ i, 0 < G.extent i
  le_top_left : K ≤ F.top
  le_top_right : K ≤ G.top
  period_eq : ∀ k, k ≤ K → ∀ i, F.period k i = G.period k i
def MinimalActionTransfer : Prop :=
  ∀ (F G : BlockFrame) (K : ℕ) (a : ℝ), SharePeriods F G K →
    (∀ (k : ℕ) (W : F.GaugeField k), k ≤ K →
      minimalAction a (finiteCells F) k W = minimalAction a (finiteCells G) k (transferField G W)) ∧
    (∀ (k : ℕ) (W : F.GaugeField k) (V : F.GaugeField (k + 1)), k < K →
      blockEnergy a (finiteCells F) k W V =
        blockEnergy a (finiteCells G) k (transferField G W) (transferField G V)) ∧
    (∀ (k : ℕ) (W : F.GaugeField k) (z : Fin 4 → ℤ) (i : Fin 4), k < K →
      contourAverage (transferField G W) (siteOfCoords (k + 1) z, i) =
        contourAverage W (siteOfCoords (k + 1) z, i)) ∧
    (∀ (k : ℕ) (W : F.GaugeField k) (z : Fin 4 → ℤ) (i : Fin 4), k ≤ K →
      transferField G W (siteOfCoords k z) i = W (siteOfCoords k z) i) ∧
    (∀ (k : ℕ) (W : F.GaugeField k) (p : List PathStep) (z : Fin 4 → ℤ), k ≤ K →
      pathHolonomy (transferField G W) (siteOfCoords k z) p = pathHolonomy W (siteOfCoords k z) p) ∧
    (∀ (k : ℕ) (x : F.Site k), k ≤ K → transferSite F (transferSite G x) = x) ∧
    (∀ (k : ℕ) (y : G.Site k), k ≤ K → transferSite G (transferSite F y) = y) ∧
    ∀ (k : ℕ) (x : F.Site k), k ≤ K → siteCoords (transferSite G x) = siteCoords x
end ColdStepAtMirrorFrames
end YangMills.Construction
end
