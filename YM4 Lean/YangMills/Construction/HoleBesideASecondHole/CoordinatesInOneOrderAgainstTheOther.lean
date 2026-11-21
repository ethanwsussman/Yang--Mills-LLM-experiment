import YangMills.Construction.HoleBesideASecondHole.CoordinatesOfAFieldNearATop
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction
open BlockAverages HoleBounds
namespace LumpContours
variable {F : BlockFrame}
def bondsOfEndBlocks (b : F.Site F.depth × Fin 4) : Finset (F.Site F.depth × Fin 4) :=
  cutBonds (sitesBelow F.depth (enclosingCell b.1) ∪ sitesBelow F.depth (enclosingCell (b.1 + unitStep F.depth b.2)))
def BondCoordinatesLexComparison : Prop :=
  ∃ K : ℕ → ℝ, (∀ L, 1 ≤ K L) ∧ ∀ (F : BlockFrame), Odd F.blockSide → IsCubicTorus F 64 →
    ∀ (V : F.GaugeField F.top) (W W' : F.GaugeField F.depth) (b : F.Site F.depth × Fin 4) (d : ℝ),
      (∀ c ∈ bondsOfEndBlocks b, ‖(lexBondCoordinate V W c : ℍ[ℝ])‖ ≤ 1 / K F.blockSide) →
      (∀ c ∈ bondsOfEndBlocks b, ‖(lexBondCoordinate V W' c : ℍ[ℝ])‖ ≤ 1 / K F.blockSide) →
      (∀ c ∈ bondsOfEndBlocks b, ‖(lexBondCoordinate V W c : ℍ[ℝ]) - lexBondCoordinate V W' c‖ ≤ d) →
      ∀ π : Equiv.Perm (Fin 4), ‖(bondCoordinate π V W b : ℍ[ℝ]) - bondCoordinate π V W' b‖ ≤ K F.blockSide * d
end LumpContours
end YangMills.Construction
end
