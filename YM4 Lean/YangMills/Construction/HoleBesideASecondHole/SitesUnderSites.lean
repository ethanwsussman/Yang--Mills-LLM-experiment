import YangMills.Construction.HoleBesideASecondHole.CutsLumpsBasesAndContours
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction.LumpContours
open YangMills.Construction.BlockAverages
def NestedSiteFacts : Prop :=
  (∀ F : BlockFrame, Odd F.blockSide → (∀ i, 0 < F.extent i) →
    (∀ (i j m : ℕ), i ≤ j → j ≤ m → m ≤ F.top → ∀ (x : F.Site m) (w : F.Site j) (z : F.Site i),
      w ∈ sitesBelow j x → z ∈ sitesBelow i w → z ∈ sitesBelow i x) ∧
    (∀ (i j : ℕ), i ≤ j → j ≤ F.top → ∀ (x x' : F.Site j) (z : F.Site i),
      z ∈ sitesBelow i x → z ∈ sitesBelow i x' → x = x') ∧
    (∀ (U : F.GaugeField 0) (p : F.Site 0 × Fin 4 × Fin 4), 0 ≤ plaquetteEnergy U p)) ∧
  ∀ (q : ℍ[ℝ]) (g : UnitQuaternion), 0 ≤ ‖q‖ - (q * (g⁻¹ : UnitQuaternion)).re
end YangMills.Construction.LumpContours
end
