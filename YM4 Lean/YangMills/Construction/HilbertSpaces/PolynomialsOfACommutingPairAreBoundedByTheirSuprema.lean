import YangMills.Construction.HilbertSpaces.CommutingPairsOfAContractionAndAUnitary
import Mathlib
set_option autoImplicit false
set_option linter.unusedSectionVars false
open YangMills.Construction.OneLoopNotation YangMills.Construction.ComplexHilbert
open scoped ComplexOrder InnerProductSpace
noncomputable section
namespace YangMills.Construction.ContractionUnitary.PolynomialBound
theorem continuous_evalPoly (c : Coeffs) :
    Continuous (evalPoly c) := by
  unfold evalPoly Finsupp.sum
  refine continuous_finsetSum _ fun i _ => ?_
  refine (continuous_const.mul (((Complex.continuous_ofReal.comp
    (continuous_fst.comp continuous_subtype_val)).pow i.1))).mul ?_
  refine (continuous_snd.comp continuous_subtype_val).zpow₀ i.2 fun p => Or.inl ?_
  intro h
  have h₁ : ‖p.1.2‖ = 1 := p.2.2
  rw [show p.1.2 = 0 from h] at h₁
  simp at h₁
theorem bddAbove_range_norm_evalPoly (c : Coeffs) :
    BddAbove (Set.range fun x : intervalCircle => ‖evalPoly c x‖) :=
  (isCompact_range (continuous_evalPoly c).norm).bddAbove
theorem nonempty_intervalCircle : Nonempty intervalCircle :=
  ⟨⟨(0, 1), Set.left_mem_Icc.mpr zero_le_one, by simp [circleSet]⟩⟩
def statement : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (A V : BddOp H), IsCommutingPair A V →
    ∀ (c : Coeffs) (ψ : H),
      ‖⟪ψ, evalPolyOp c A V ψ⟫_ℂ‖ ≤ (⨆ x : intervalCircle, ‖evalPoly c x‖) * ‖ψ‖ ^ 2 ∧
      ((∀ x : intervalCircle, 0 ≤ evalPoly c x) → 0 ≤ ⟪ψ, evalPolyOp c A V ψ⟫_ℂ)
end YangMills.Construction.ContractionUnitary.PolynomialBound
end
