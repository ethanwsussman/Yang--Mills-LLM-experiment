import YangMills.Construction.HoleBesideASecondHole.HolesAtGrowingScales
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open BlockAverages LumpContours Holes
namespace HoleFilling
def eachHoleFilledStatement : Prop :=
  ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ (F : BlockFrame), Odd F.blockSide → (∀ i, 64 ≤ F.extent i) →
    ∀ (holes : Finset (Hole F)) (fine₀ : F.GaugeField 0),
    (∀ H ∈ holes, 99 ≤ H.radius ∧ 100 * H.radius ^ 2 ≤ F.blockSide ∧ 4 * H.annulusEnergy fine₀ ≤ c) →
    (∀ H ∈ holes, ∀ H' ∈ holes, H ≠ H' → ¬ AreWithin 3 H.outerBox H'.outerBox) →
    ∃ (fine' : F.GaugeField 0) (P : Hole F → Finset (F.Site 0 × Fin 4 × Fin 4)),
      (∀ H ∈ holes, ∀ p ∈ P H, plaquetteCorners p ⊆ cutBelow 0 H.outerBox) ∧
      (∀ H ∈ holes, ∀ p : F.Site 0 × Fin 4 × Fin 4, p.2.1 < p.2.2 →
        (∃ x ∈ plaquetteCorners p, x ∈ cutBelow 0 H.innerBox) → p ∈ P H) ∧
      (∀ p : F.Site 0 × Fin 4 × Fin 4, p.2.1 < p.2.2 → (∀ H ∈ holes, p ∉ P H) →
        plaquetteEnergy fine' p = plaquetteEnergy fine₀ p) ∧
      (∀ H ∈ holes, ∑ p ∈ P H, plaquetteEnergy fine' p ≤ C * H.annulusEnergy fine₀) ∧
      ∀ (b : F.Site 0 × Fin 4), (∀ H ∈ holes,
          ¬ (b.1 ∈ cutBelow 0 H.outerBox ∧ b.1 + unitStep 0 b.2 ∈ cutBelow 0 H.outerBox)) →
        fine' b.1 b.2 = fine₀ b.1 b.2
end HoleFilling
end YangMills.Construction
end
