import YangMills.Construction.Dirichlet.BilinearForms
import YangMills.Construction.Torus.DistanceAveragesWholePairMatricesAndNorms
import YangMills.Construction.Torus.PointwiseBoundsOnTheGreenOperator
import YangMills.Construction.Weighted.GivenChainGeneral
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.Weighted.GreenPointwise
variable {D : TorusData}
theorem mem_latticeAt_iff_mem_spacingLattice (p : D.Space) :
    p ∈ D.latticeAt (D.scale 0) ↔
      p ∈ Torus.spacingLattice 4 D.side D.bareSpacing := by
  have h0 : D.scale 0 = D.bareSpacing := by simp [TorusData.scale]
  rw [h0]
  constructor
  · rintro ⟨k, rfl⟩
    exact ⟨k, by funext μ; simp [TorusMetric.torusProj, Torus.torusProj, mul_comm]⟩
  · rintro ⟨k, rfl⟩
    exact ⟨k, by funext μ; simp [TorusMetric.torusProj, Torus.torusProj, mul_comm]⟩
def bareSiteEquiv (D : TorusData) : D.BareSite ≃ Dirichlet.LatticeSite 4 D.side D.bareSpacing where
  toFun x := ⟨x.1, (mem_latticeAt_iff_mem_spacingLattice _).1 x.2⟩
  invFun x := ⟨x.1, (mem_latticeAt_iff_mem_spacingLattice _).2 x.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
def transfer (f : D.BareSite → ℝ) : Dirichlet.LatticeSite 4 D.side D.bareSpacing → ℝ :=
  fun x => f ((bareSiteEquiv D).symm x)
@[simp] theorem transfer_apply_equiv (f : D.BareSite → ℝ) (x : D.BareSite) :
    transfer f (bareSiteEquiv D x) = f x := by
  simp [transfer]
theorem transfer_injective : Function.Injective (transfer : (D.BareSite → ℝ) → _) := by
  intro f g h
  funext x
  rw [← transfer_apply_equiv f, h, transfer_apply_equiv]
variable {B : SeparatedChain D}
open YangMills.Construction.Weighted.GivenChainGeneral
variable (same : AgreesWithGeneral B)
  (hw : ∀ n ≤ D.top, 1 - ((D.L : ℝ) ^ 2)⁻¹ ≤ avgWeight D.L n ∧
    avgWeight D.L n ≤ 1)
include same in
theorem mem_shellSites_iff (y : D.Space) (n : ℕ) :
    y ∈ Torus.shellSites (d := 4) (S := D.side) D.L D.bareSpacing B.stage n ↔
      y ∈ B.layerSites n := by
  by_cases hn : n ≤ D.top
  · rw [same.layerSites_eq_shellSites n hn]
  · have hn' : D.top < n := not_le.1 hn
    constructor
    · rintro ⟨-, -, h⟩
      simp [Torus.shell, B.empty_above n hn'] at h
    · rintro ⟨-, h⟩
      simp [SeparatedChain.layer, not_lt.2 hn'.le, hn'.ne'] at h
end YangMills.Construction.Weighted.GreenPointwise
