import YangMills.Construction.ColdChainAtEveryLevel.ChainCoordinatesMovedAndCriticalFormForm
import YangMills.Construction.ColdChainAtEveryLevel.UnitPartsOfQuaternions
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction.BlockAverages
variable {F : BlockFrame}
def treeHolonomy (X : F.GaugeField F.depth) (x : F.Site F.depth) : UnitQuaternion :=
  pathHolonomy X (cellCentre F.depth (enclosingCell x)) (axisPath (cellOffset x) 1)
open Classical in
def gaugedBondElement (X : F.GaugeField F.depth) (k : F.Cell → UnitQuaternion) (V : F.GaugeField F.top)
    (b : F.Site F.depth × Fin 4) : UnitQuaternion :=
  k (enclosingCell b.1) * treeHolonomy X b.1 * X b.1 b.2 * (treeHolonomy X (b.1 + unitStep F.depth b.2))⁻¹ *
    (k (enclosingCell (b.1 + unitStep F.depth b.2)))⁻¹ *
      if IsCrossingBond b then (V (enclosingCell b.1) b.2)⁻¹ else 1
theorem pureComponent_mem_imaginaryQuaternions (q : ℍ[ℝ]) : pureComponent q ∈ imaginaryQuaternions := by
  show (pureComponent q).re = 0
  simp [pureComponent]
def unitLog (g : UnitQuaternion) : imaginaryQuaternions :=
  (Real.arcsin ‖pureComponent (g : ℍ[ℝ])‖ / ‖pureComponent (g : ℍ[ℝ])‖) •
    ⟨pureComponent (g : ℍ[ℝ]), pureComponent_mem_imaginaryQuaternions _⟩
def bondChartCoord (R : F.FieldChain) (V : F.GaugeField F.top) (b : F.Site F.depth × Fin 4) (U : ChainChart F)
    (v : F.Site F.top → Fin 4 → imaginaryQuaternions) : imaginaryQuaternions :=
  unitLog (gaugedBondElement (chartField R U F.depth) (chartGauge R U F.top) (rotatedField v V) b)
open Classical in
def gaugedCellShare (a : ℝ) (S : Finset F.Cell) (Y : F.Cell) (X : F.FieldChain) (k : F.SiteGauge) : ℝ :=
  ∑ p ∈ innerPlaquettes S 0, (∑ x ∈ plaquetteCorners p, if enclosingCell x = Y then (1 / 4 : ℝ) else 0) *
      (1 - ((plaquetteHolonomy (X 0) p : UnitQuaternion) : ℍ[ℝ]).re) +
    a * ∑ j ∈ Finset.range F.top, ∑ c ∈ innerBonds S (j + 1),
      ((if enclosingCell c.1 = Y then (1 / 2 : ℝ) else 0) +
        (if enclosingCell (c.1 + unitStep (j + 1) c.2) = Y then (1 / 2 : ℝ) else 0)) *
      gaugedBlockFit (X j) (k (j + 1)) (X (j + 1)) c
def localCellShare (a : ℝ) (S : Finset F.Cell) (R : F.FieldChain) (V : F.GaugeField F.top) (Y : F.Cell)
    (U : ChainChart F) (v : F.Site F.top → Fin 4 → imaginaryQuaternions) : ℝ :=
  gaugedCellShare a S Y (chartChain R U (rotatedField v V)) (chartGauge R U)
def chartShiftAlong {ι : Type} [Fintype ι] (U : ChainChart F) (A : ι → ChainChart F) (t : ι → ℝ) :
    ChainChart F :=
  ⟨fun x i => U.fine x i + ∑ l, t l • (A l).fine x i, fun j y i => U.coarse j y i + ∑ l, t l • (A l).coarse j y i⟩
def topVariationAlong {ι : Type} [Fintype ι] (e : ι → F.Site F.top → Fin 4 → imaginaryQuaternions) (t : ι → ℝ) :
    F.Site F.top → Fin 4 → imaginaryQuaternions :=
  fun y i => ∑ l, t l • e l y i
def topVariationNorm (B : Finset (F.Site F.top × Fin 4)) (e : F.Site F.top → Fin 4 → imaginaryQuaternions) : ℝ :=
  ∑ b ∈ B, ‖e b.1 b.2‖
def localDirectionSize (S : Finset F.Cell) (R : F.FieldChain) (B : Finset (F.Site F.top × Fin 4)) (z : F.Cell)
    (A : ChainChart F) (e : F.Site F.top → Fin 4 → imaginaryQuaternions) : ℝ :=
  localNorm S R A (oneSiteWeights F) z + topVariationNorm B e
def localIteratedDeriv {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {m : ℕ}
    (Φ : ChainChart F → (F.Site F.top → Fin 4 → imaginaryQuaternions) → E) (U : ChainChart F)
    (A : Fin m → ChainChart F) (e : Fin m → F.Site F.top → Fin 4 → imaginaryQuaternions) : E :=
  iteratedFDeriv ℝ m (fun t : Fin m → ℝ => Φ (chartShiftAlong U A t) (topVariationAlong e t)) 0 (fun l => Pi.single l 1)
structure IsLocalRepresentation {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] (S : Finset F.Cell) (R : F.FieldChain)
    (z : F.Cell) (B : Finset (F.Site F.top × Fin 4)) (Ck : ℕ → ℝ) (U : ChainChart F)
    (Φ : ChainChart F → (F.Site F.top → Fin 4 → imaginaryQuaternions) → E) : Prop where
  congr_of_agree : ∀ U' U'' v, ChartEqOnBonds S U' U'' → Φ U' v = Φ U'' v
  analyticAt : ∀ {ι : Type} [Fintype ι] (A : ι → ChainChart F) (e : ι → F.Site F.top → Fin 4 → imaginaryQuaternions),
    AnalyticAt ℝ (fun t : ι → ℝ => Φ (chartShiftAlong U A t) (topVariationAlong e t)) 0
  iteratedDeriv_le : ∀ (m : ℕ) (A : Fin m → ChainChart F) (e : Fin m → F.Site F.top → Fin 4 → imaginaryQuaternions),
    ‖localIteratedDeriv Φ U A e‖ ≤ Ck m * ∏ l, localDirectionSize S R B z (A l) (e l)
end YangMills.Construction.BlockAverages
end
