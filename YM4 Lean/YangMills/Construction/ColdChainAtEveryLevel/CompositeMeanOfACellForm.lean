import YangMills.Construction.ColdChainAtEveryLevel.EvaluationsOfAChain
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction
namespace CompositeMean
open BlockAverages LatticeFractionalIntegration
variable {F : BlockFrame}
theorem refineSite_add_siteOfCoords_injective (hodd : Odd F.blockSide) {j : ℕ} (hj : j + 1 ≤ F.top)
    {y y' : F.Site (j + 1)} {h h' : Lattice4}
    (hh : h ∈ centredCube F.blockSide) (hh' : h' ∈ centredCube F.blockSide)
    (e : refineSite y + siteOfCoords j h = refineSite y' + siteOfCoords j h') :
    y = y' ∧ h = h' := by apply _root_.YangMills.Construction.BlockAverages.LocalQuarticNorms.refineSite_add_injective <;> assumption
theorem sum_sum_refineSite_le (hodd : Odd F.blockSide) {D : Finset F.Cell} {j : ℕ} (hj : j + 1 ≤ F.top)
    {G : F.Site j → ℝ} (hG : ∀ x, 0 ≤ G x) :
    ∑ y ∈ sitesOfCells D (j + 1), ∑ h ∈ centredCube F.blockSide, G (refineSite y + siteOfCoords j h) ≤
      ∑ x ∈ sitesOfCells D j, G x := by
  classical
  rw [← Finset.sum_product']
  have hinj : Set.InjOn (fun p : F.Site (j + 1) × Lattice4 => refineSite p.1 + siteOfCoords j p.2)
      ((sitesOfCells D (j + 1) ×ˢ centredCube F.blockSide : Finset (F.Site (j + 1) × Lattice4)) :
        Set (F.Site (j + 1) × Lattice4)) := by
    intro p hp q hq e
    obtain ⟨p1, p2⟩ := Finset.mem_product.1 (Finset.mem_coe.1 hp)
    obtain ⟨q1, q2⟩ := Finset.mem_product.1 (Finset.mem_coe.1 hq)
    obtain ⟨a1, a2⟩ := refineSite_add_siteOfCoords_injective hodd hj p2 q2 e
    exact Prod.ext a1 a2
  rw [← Finset.sum_image (f := G) hinj]
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun _ _ _ => hG _
  intro x hx
  obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 hx
  obtain ⟨p1, p2⟩ := Finset.mem_product.1 hp
  exact ChartCoordinates.refineSite_add_mem_sitesOfCells hodd hj p1 p2
def compositeMeanBoundStatement : Prop :=
  ∀ (F : BlockFrame) (y₀ : F.Cell) (f : (j : ℕ) → F.Site j → ℍ[ℝ]) (β : (j : ℕ) → F.Site (j + 1) → ℝ) (ε : ℝ),
    Odd F.blockSide → 5 ≤ F.blockSide → 0 ≤ ε → ε ≤ 1 / 8 → (∀ j y, 0 ≤ β j y) →
    (∀ j, j < F.top → ∑ y ∈ sitesOfCells ({y₀} : Finset F.Cell) (j + 1), β j y ^ 4 ≤ ε ^ 4) →
    (∀ j, j < F.top → ∀ y ∈ sitesOfCells ({y₀} : Finset F.Cell) (j + 1),
      ‖f (j + 1) y - (1 / (F.blockSide : ℝ) ^ 4) •
          ∑ h ∈ centredCube F.blockSide, f j (refineSite y + siteOfCoords j h)‖ ≤
        β j y * ((1 / (F.blockSide : ℝ) ^ 4) *
          ∑ h ∈ centredCube F.blockSide, ‖f j (refineSite y + siteOfCoords j h)‖)) →
    ‖f F.top y₀ - (1 / ((F.blockSide : ℝ) ^ F.top) ^ 4) •
        ∑ h ∈ centredCube (F.blockSide ^ F.top), f 0 (cellCentre 0 y₀ + siteOfCoords 0 h)‖ ^ 4 ≤
      9 * ε ^ 4 * (∑ x ∈ sitesOfCells ({y₀} : Finset F.Cell) 0, ‖f 0 x‖ ^ 4) / ((F.blockSide : ℝ) ^ F.top) ^ 4
end CompositeMean
end YangMills.Construction
end
