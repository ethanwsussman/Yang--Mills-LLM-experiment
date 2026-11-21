import YangMills.Construction.Towers.LowerBoundsOfTheAbelianOperators
import YangMills.Construction.Towers.TheAbelianOperatorsAreShiftedPositive
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open OperatorCalculus Tower.UnitLatticeL2
namespace Tower.AbelianFieldDensity.ShiftedPositiveProof
section AddScalar
variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
theorem isBoundedBelowBy_addScalar {T : H →L[ℂ] H} {c s c' : ℝ} (h : IsBoundedBelowBy T c)
    (hc : c' ≤ c + s) : IsBoundedBelowBy (addScalar T s) c' := by
  intro ψ
  have hn : (inner ℂ ψ ψ : ℂ) = ((‖ψ‖ ^ 2 : ℝ) : ℂ) := by
    rw [inner_self_eq_norm_sq_to_K]
    push_cast
    rfl
  have happ : addScalar T s ψ = T ψ + (s : ℂ) • ψ := rfl
  have e : inner ℂ ψ (addScalar T s ψ) - (c' : ℂ) * inner ℂ ψ ψ =
      (inner ℂ ψ (T ψ) - (c : ℂ) * inner ℂ ψ ψ) + (((c + s - c') * ‖ψ‖ ^ 2 : ℝ) : ℂ) := by
    rw [happ, inner_add_right, inner_smul_right, hn]
    push_cast
    ring
  obtain ⟨h1, h2⟩ := h ψ
  rw [e]
  refine ⟨?_, ?_⟩
  · rw [Complex.add_im, h1, Complex.ofReal_im, add_zero]
  · rw [Complex.add_re, Complex.ofReal_re]
    have h3 : 0 ≤ (c + s - c') * ‖ψ‖ ^ 2 := mul_nonneg (by linarith) (by positivity)
    linarith
end AddScalar
theorem shiftedPositive_holds (hLow : AbelianOperatorBounds.LowerBoundsHold) :
    AbelianFieldDensity.ShiftedPositive := by
  intro L hL
  refine ⟨?_, ?_, ?_⟩
  · intro z hz θ hθ
    obtain ⟨hK, hΔ⟩ := hLow L hL θ
    have hK' := hK fun p => (hθ p).trans (min_le_left _ _)
    have hsup : (⨆ p : FullSpace.Face L 0 0, |Real.sin (FullSpace.faceAngle θ p)|) ≤ z / 48 :=
      Real.iSup_le (fun p => (Real.abs_sin_le_abs).trans ((hθ p).trans (min_le_right _ _)))
        (by positivity)
    exact ⟨isBoundedBelowBy_addScalar hΔ (by linarith), isBoundedBelowBy_addScalar hK' (by linarith)⟩
  · intro θ r hr p
    have h1 := abs_le.mp (hr (FullSpace.forwardEdge p.corner p.lowAxis))
    have h2 := abs_le.mp
      (hr (FullSpace.forwardEdge (p.corner + InfiniteLattice.axisStep _ p.lowAxis) p.highAxis))
    have h3 := abs_le.mp
      (hr (FullSpace.forwardEdge (p.corner + InfiniteLattice.axisStep _ p.highAxis) p.lowAxis))
    have h4 := abs_le.mp (hr (FullSpace.forwardEdge p.corner p.highAxis))
    simp only [FullSpace.faceAngle, FullSpace.edgeDifference]
    rw [abs_le]
    constructor <;> linarith [h1.1, h1.2, h2.1, h2.2, h3.1, h3.2, h4.1, h4.2]
  · intro θ f p
    simp only [FullSpace.faceAngle, FullSpace.edgeDifference]
    ring
end Tower.AbelianFieldDensity.ShiftedPositiveProof
end YangMills.Construction
end
