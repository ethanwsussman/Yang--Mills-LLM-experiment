import YangMills.Construction.HoleBesideASecondHole.HolesAtGrowingScales
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction
open BlockAverages LumpContours Holes
namespace HoleGauge
def holeGaugeStatement : Prop :=
  ∀ (F : BlockFrame) (holes : Finset (Hole F)) (cells : Finset F.Cell) (A B : F.GaugeField F.depth) (E : ℝ),
    Odd F.blockSide → (∀ i, 4096 ≤ F.extent i) → 0 ≤ E →
    (∀ H ∈ holes, 99 ≤ H.radius ∧ 100 * H.radius ^ 2 ≤ F.blockSide) →
    (∀ H ∈ holes, ∀ H' ∈ holes, H ≠ H' → ¬ AreWithin (5 * max H.radius H'.radius) H.outerBox H'.outerBox) →
    (∀ b ∈ cutBonds (cutBelow F.depth cells), b.1 ∉ holeSupport holes →
      b.1 + unitStep F.depth b.2 ∉ holeSupport holes → A b.1 b.2 = B b.1 b.2) →
    (∀ y ∈ cells, ∀ y' ∈ cells, cellSupDist y y' ≤ 1 →
      ∑ p ∈ cutPlaquettes (sitesBelow F.depth y ∪ sitesBelow F.depth y'),
        BlockAverages.plaquetteDefect A p ^ 2 ≤ E ^ 2) →
    (∀ y ∈ cells, ∀ y' ∈ cells, cellSupDist y y' ≤ 1 →
      ∑ p ∈ cutPlaquettes (sitesBelow F.depth y ∪ sitesBelow F.depth y'),
        BlockAverages.plaquetteDefect B p ^ 2 ≤ E ^ 2) →
    ∃ γ : F.Site F.depth → UnitQuaternion, (∀ x, x ∉ holeSupport holes → γ x = 1) ∧
      ∀ b : F.Site F.depth × Fin 4, enclosingCell b.1 ∈ cells →
        enclosingCell (b.1 + unitStep F.depth b.2) ∈ cells →
        ‖((gaugeTransform γ A b.1 b.2 : UnitQuaternion) : ℍ[ℝ]) - ((B b.1 b.2 : UnitQuaternion) : ℍ[ℝ])‖ ≤
          Real.sqrt F.blockSide * E
end HoleGauge
end YangMills.Construction
end
