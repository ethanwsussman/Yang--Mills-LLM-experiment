import YangMills.Construction.HilbertSpaces.ComplexHilbertSpaceDefs
import Mathlib
set_option autoImplicit false
set_option linter.unusedSectionVars false
open YangMills.Construction.OneLoopNotation YangMills.Construction.ComplexHilbert
noncomputable section
namespace YangMills.Construction
namespace ContractionUnitary
def circleSet : Set ℂ := {w | ‖w‖ = 1}
def intervalCircle : Set (ℝ × ℂ) := Set.Icc 0 1 ×ˢ circleSet
theorem isCompact_intervalCircle : IsCompact intervalCircle := by
  refine isCompact_Icc.prod ?_
  have hc : circleSet = Metric.sphere (0 : ℂ) 1 := by
    ext w
    simp [circleSet]
  rw [hc]
  exact isCompact_sphere 0 1
instance instCompactSpaceElemProdRealComplexIntervalCircle : CompactSpace intervalCircle :=
  isCompact_iff_compactSpace.mp isCompact_intervalCircle
section Pairs
variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
theorem exists_bddOp_of_isUnitaryMap {U : E →ₗ[ℂ] E}
    (hU : IsUnitaryMap U) : ∃ T : BddOp E, (T : E →ₗ[ℂ] E) = U :=
  exists_bddOp_of_hasBound ⟨1, fun v => by rw [hU.isometric v, one_mul]⟩
structure IsCommutingPair (A U : BddOp E) : Prop where
  symm : IsSymmetricOp A
  nonneg : OpGE A 0
  le_one : OpLE A (idOp E)
  unitary : IsUnitaryMap (U : E →ₗ[ℂ] E)
  comm : A * U = U * A
def opInv (U : BddOp E) : BddOp E := Ring.inverse U
theorem isTwoSidedInverse_opInv {U : BddOp E}
    (hU : IsUnitaryMap (U : E →ₗ[ℂ] E)) : IsTwoSidedInverse U (opInv U) := by
  have hs : IsUnitaryMap (hU.toLinearEquiv.symm : E →ₗ[ℂ] E) := by
    refine ⟨fun v => ?_, hU.toLinearEquiv.symm.surjective⟩
    have hn := hU.isometric (hU.toLinearEquiv.symm v)
    have ha : (U : E →ₗ[ℂ] E) (hU.toLinearEquiv.symm v) = v :=
      hU.toLinearEquiv.apply_symm_apply v
    rw [ha] at hn
    exact hn.symm
  obtain ⟨T, hT⟩ := exists_bddOp_of_isUnitaryMap hs
  have hr : U * T = 1 := by
    ext v
    have hv : T v = hU.toLinearEquiv.symm v := LinearMap.congr_fun hT v
    change U (T v) = v
    rw [hv]
    exact hU.toLinearEquiv.apply_symm_apply v
  have hl : T * U = 1 := by
    ext v
    have hv : T (U v) = hU.toLinearEquiv.symm (U v) := LinearMap.congr_fun hT (U v)
    change T (U v) = v
    rw [hv]
    exact hU.toLinearEquiv.symm_apply_apply v
  have hunit : IsUnit U := ⟨⟨U, T, hr, hl⟩, rfl⟩
  exact ⟨Ring.mul_inverse_cancel U hunit, Ring.inverse_mul_cancel U hunit⟩
def zpowOp (U : BddOp E) (k : ℤ) : BddOp E :=
  if 0 ≤ k then U ^ k.toNat else opInv U ^ (-k).toNat
theorem zpowOp_zero (U : BddOp E) : zpowOp U 0 = 1 := by
  simp [zpowOp]
theorem zpowOp_natCast (U : BddOp E) (m : ℕ) :
    zpowOp U (m : ℤ) = U ^ m := by
  simp [zpowOp]
theorem zpowOp_of_neg (U : BddOp E) {k : ℤ} (hk : k < 0) :
    zpowOp U k = opInv U ^ (-k).toNat := by
  simp [zpowOp, not_le.mpr hk]
end Pairs
abbrev Coeffs : Type := ℕ × ℤ →₀ ℂ
def evalPoly (c : Coeffs) : intervalCircle → ℂ := fun x =>
  c.sum fun j a => a * ((x.1.1 : ℝ) : ℂ) ^ j.1 * x.1.2 ^ j.2
def evalPolyOp {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (c : Coeffs) (A U : BddOp E) : BddOp E :=
  c.sum fun j a => a • (A ^ j.1 * zpowOp U j.2)
end ContractionUnitary
end YangMills.Construction
end
