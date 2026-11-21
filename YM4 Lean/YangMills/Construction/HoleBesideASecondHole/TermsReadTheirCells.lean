import YangMills.Construction.HoleBesideASecondHole.TermsOfAChainAtACell
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction.CellTerms
open BlockAverages LumpContours
def cellTermsLocalityStatement : Prop :=
  ∀ (F : BlockFrame) (C : Finset F.Cell) (γ : F.Site 0 → UnitQuaternion) (R R' : F.FieldChain)
    (U U' : ChainChart F),
    Odd F.blockSide → IsAdmissibleAmbient F → IsGaugeRotatedOn C γ R R' U U' → HasNonzeroAveragesOn C R U →
    (∀ j, j < F.top → ∀ e : F.Site j × Fin 4, BondWithin C e →
      chartField R' U' j e.1 e.2 = gaugeTransform (fun x => γ (baseSite x)) (chartField R U j) e.1 e.2) ∧
    (∀ j, j < F.top → ∀ y : F.Site (j + 1), enclosingCell y ∈ C →
      chartGauge R' U' (j + 1) y = γ (baseSite y) * chartGauge R U (j + 1) y * (γ (baseSite y))⁻¹) ∧
    ((∀ y ∈ C, γ (cellCentre 0 y) = 1) →
      (∀ (a : ℝ) (S S' : Finset F.Cell) (V V' : F.GaugeField F.top) (z : F.Cell),
        (∀ y ∈ LumpContours.cellBall z 1, (y ∈ S ↔ y ∈ S') ∧ (y ∈ S → y ∈ C)) →
        (∀ (y : F.Cell) (i : Fin 4), y ∈ C → y + unitStep F.top i ∈ C → V y i = V' y i) →
        chartCellTerms a S R U V z = chartCellTerms a S' R' U' V' z) ∧
      ∀ (π : Equiv.Perm (Fin 4)) (V V' : F.GaugeField F.top) (e : F.Site F.depth × Fin 4), BondWithin C e →
        (IsCrossingBond e → V (enclosingCell e.1) e.2 = V' (enclosingCell e.1) e.2) →
        bondCoordinate π V (chartFieldTopFixed R U) e = bondCoordinate π V' (chartFieldTopFixed R' U') e)
end YangMills.Construction.CellTerms
end
