import YangMills.Construction.HilbertSpace.FormsAndOperators
import Mathlib
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Filter Set Topology MeasureTheory
open scoped ComplexConjugate ComplexOrder ENNReal InnerProductSpace
noncomputable section
namespace YangMills.Construction
namespace LatticeBasics
def supNormE {S : Type*} (f : S → ℂ) : ℝ≥0∞ := ⨆ x, ‖f x‖ₑ
section Hilbert
variable {H H' : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup H'] [InnerProductSpace ℂ H'] [CompleteSpace H']
theorem le_iff_inner_nonneg {A A' : H →L[ℂ] H} (hA : IsSelfAdjoint A) (hA' : IsSelfAdjoint A') :
    A' ≤ A ↔ ∀ x, 0 ≤ ⟪x, (A - A') x⟫_ℂ := by
  rw [ContinuousLinearMap.le_def]
  refine ⟨fun h x => h.inner_nonneg_right x, fun h => ?_⟩
  refine (ContinuousLinearMap.isPositive_iff' _).mpr ⟨hA.sub hA', fun x => ?_⟩
  rw [← inner_conj_symm, starRingEnd_apply]
  exact star_nonneg_iff.mpr (h x)
def IsIsometricMap (A : H →ₗ[ℂ] H') : Prop := ∀ x, ‖A x‖ = ‖x‖
theorem IsIsometricMap.inner_map_map {A : H →ₗ[ℂ] H'} (h : IsIsometricMap A) (x y : H) :
    ⟪A x, A y⟫_ℂ = ⟪x, y⟫_ℂ :=
  LinearIsometry.inner_map_map ⟨A, h⟩ x y
def IsUnitaryLinearMap (A : H →ₗ[ℂ] H') : Prop := IsIsometricMap A ∧ Function.Surjective A
def nullSet (A : H →L[ℂ] H') : Set H := {x | A x = 0}
theorem tendstoStrongly_iff (A : ℕ → H →L[ℂ] H) (B : H →L[ℂ] H) :
    HilbertSpaceBasics.TendstoStrongly A atTop B ↔
      ∀ x, Tendsto (fun n => ‖A n x - B x‖) atTop (𝓝 0) :=
  forall_congr' fun _ => tendsto_iff_norm_sub_tendsto_zero
end Hilbert
end LatticeBasics
end YangMills.Construction
