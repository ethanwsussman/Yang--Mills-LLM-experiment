import YangMills.Construction.HoleBesideASecondHole.TheInequalityOfAHole
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction
namespace LumpContours
open BlockAverages
variable {F : BlockFrame}
def lexBondCoordinate (V : F.GaugeField F.top) (W : F.GaugeField F.depth) (b : F.Site F.depth × Fin 4) :
    imaginaryQuaternions :=
  bondCoordinate 1 V W b
def LiesNearTop (r : ℝ) (S : Finset F.Cell) (V : F.GaugeField F.top) (W : F.GaugeField F.depth) : Prop :=
  (∀ p ∈ cutPlaquettes (cutBelow F.depth S), plaquetteDefect W p ≤ r) ∧ ∀ c ∈ cutBonds S, blockFit W V c ≤ r ^ 2
def NearTopCoordinateBound : Prop :=
  ∃ K : ℕ → ℝ, (∀ L, 1 ≤ K L) ∧ ∀ (F : BlockFrame), Odd F.blockSide → HoleBounds.IsCubicTorus F 64 →
    ∀ (S : Finset F.Cell) (V : F.GaugeField F.top) (W : F.GaugeField F.depth) (r : ℝ), 0 ≤ r →
      K F.blockSide * r ≤ 1 →
      LiesNearTop r S V W → ∀ b ∈ innerBonds S F.depth, ‖(lexBondCoordinate V W b : ℍ[ℝ])‖ ≤ K F.blockSide * r
end LumpContours
end YangMills.Construction
end
