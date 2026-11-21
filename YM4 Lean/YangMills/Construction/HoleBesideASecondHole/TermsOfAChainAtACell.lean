import YangMills.Construction.ColdChainAtEveryLevel.NormsOfCoordinates
import YangMills.Construction.HoleBesideASecondHole.CutsLumpsBasesAndContours
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction
namespace CellTerms
open BlockAverages LumpContours
variable {F : BlockFrame}
def cellTerms (a : ℝ) (S : Finset F.Cell) (X : F.FieldChain) (g : F.SiteGauge) (z : F.Cell) : ℝ :=
  ∑ p ∈ plaquettesOver S {z} 0, plaquetteEnergy (X 0) p +
    a * ∑ j ∈ Finset.range F.top, ∑ c ∈ bondsOver S {z} (j + 1),
      gaugedBlockFit (X j) (g (j + 1)) (X (j + 1)) c
def chartCellTerms (a : ℝ) (S : Finset F.Cell) (R : F.FieldChain) (U : ChainChart F)
    (V : F.GaugeField F.top) (z : F.Cell) : ℝ :=
  cellTerms a S (chartChain R U V) (chartGauge R U) z
open Classical in
def centreGauge (g : F.Cell → UnitQuaternion) (x : F.Site F.depth) : UnitQuaternion :=
  if h : ∃ y : F.Cell, refineSite y = x then g h.choose else 1
def chartFieldTopFixed (R : F.FieldChain) (U : ChainChart F) : F.GaugeField F.depth :=
  gaugeTransform (centreGauge (chartGauge R U F.top)) (chartField R U F.depth)
def BondWithin (C : Finset F.Cell) {j : ℕ} (b : F.Site j × Fin 4) : Prop :=
  enclosingCell b.1 ∈ C ∧ enclosingCell (b.1 + unitStep j b.2) ∈ C
structure IsGaugeRotatedOn (C : Finset F.Cell) (γ : F.Site 0 → UnitQuaternion) (R R' : F.FieldChain)
    (U U' : ChainChart F) : Prop where
  reference_eq : ∀ j, j < F.top → ∀ b : F.Site j × Fin 4, BondWithin C b →
    R' j b.1 b.2 = gaugeTransform (fun x => γ (baseSite x)) (R j) b.1 b.2
  fine_eq : ∀ b : F.Site 0 × Fin 4, BondWithin C b →
    ((U'.fine b.1 b.2 : imaginaryQuaternions) : ℍ[ℝ]) = adjointAction (γ (baseSite b.1)) (U.fine b.1 b.2)
  coarse_eq : ∀ j, j + 1 < F.top → ∀ b : F.Site (j + 1) × Fin 4, BondWithin C b →
    ((U'.coarse j b.1 b.2 : imaginaryQuaternions) : ℍ[ℝ]) =
      adjointAction (γ (baseSite b.1)) (U.coarse j b.1 b.2)
def HasNonzeroAveragesOn (C : Finset F.Cell) (R : F.FieldChain) (U : ChainChart F) : Prop :=
  ∀ j, j + 1 < F.top → ∀ c : F.Site (j + 1) × Fin 4, BondWithin C c →
    contourAverage (R j) c ≠ 0 ∧
      gaugedContourAverage (chartField R U j) (balancingGauge (chartField R U j) (R j)) c ≠ 0
def unweightedLocalNorm (S : Finset F.Cell) (R : F.FieldChain) (U : ChainChart F) (z : F.Cell) : ℝ :=
  localNorm S R U (fun _ _ => 1) z
def AgreeNear (r : ℕ) (S S' : Finset F.Cell) (V V' : F.GaugeField F.top) (z : F.Cell) : Prop :=
  (∀ y, cellSupDist z y ≤ r → (y ∈ S ↔ y ∈ S')) ∧
    ∀ (y : F.Cell) (i : Fin 4), cellSupDist z y ≤ r → cellSupDist z (y + unitStep F.top i) ≤ r →
      V y i = V' y i
end CellTerms
end YangMills.Construction
end
