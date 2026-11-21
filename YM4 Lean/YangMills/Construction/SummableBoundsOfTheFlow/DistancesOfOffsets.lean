import YangMills.Construction.ColdChainAtEveryLevel.PropertiesOfTheColdChainForm
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open BlockAverages
namespace Estimates
variable {F : BlockFrame}
def cellOffset (Y z : F.Cell) : Fin 4 → ℤ := fun i => ((z - Y : F.Cell) i).valMinAbs
def cellOffsetStatement : Prop :=
  ∀ (F : BlockFrame), Odd F.blockSide → (∀ i, 2 ≤ F.extent i) →
    (∀ (Y : F.Cell) (h o : Fin 4 → ℤ) (k : Fin 4), o ∈ centredCube F.blockSide →
      enclosingCell (fineBondAt Y h o k).1 = Y + siteOfCoords F.top h) ∧
    (∀ Y z : F.Cell, Y + siteOfCoords F.top (cellOffset Y z) = z) ∧
    (∀ (Y z : F.Cell) (i : Fin 4), (cellOffset Y z i).natAbs ≤ cellSupDist z Y) ∧
    ∀ (q : ℕ), (∀ i, 2 * q + 2 < F.extent i) → ∀ (Y : F.Cell) (a b : Fin 4 → ℤ),
      (∀ l, 2 * |a l| ≤ q) → (∀ l, 2 * |b l| ≤ q) →
      cellOffset Y (Y + siteOfCoords F.top a) = a ∧
      cellSupDist (Y + siteOfCoords F.top a) (Y + siteOfCoords F.top b) =
        Finset.univ.sup fun i => (a i - b i).natAbs
end Estimates
end YangMills.Construction
end
