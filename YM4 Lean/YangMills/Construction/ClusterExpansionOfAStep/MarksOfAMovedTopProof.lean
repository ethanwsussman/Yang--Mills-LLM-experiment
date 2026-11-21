import YangMills.Construction.ClusterExpansionOfAStep.MarksOfAMovedTop
import YangMills.Construction.ClusterExpansionOfAStep.TreesOfABlock
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction.MovedTopMarks
open BlockAverages LumpContours TorusFields TorusLumps StepCosts StepMarks BondMoves
theorem goodMarkAlongMove_holds : GoodMarkAlongMove := by
  classical
  intro ℓ ρA p t m n _ V W k c X b
  set F : BlockFrame := stepBlockFrame ℓ.side n with hF
  set W' := readAtLevel F 0 W with hW'
  set b' : F.Site F.depth × Fin 4 := (torusSiteInFrame F 0 b.1, b.2) with hb'
  set Y : TorusSite n := parentBlock ℓ.side b.1 with hY
  set g : UnitQuaternion := gaugeTransform (axialGauge 1 W') W' b'.1 b'.2 with hg
  by_cases hx : IsCrossingBond b'
  · have hchart : ∀ U : TorusField n, chartCoord ℓ U W b = minimalLog (g * (U Y b.2)⁻¹) := by
      intro U
      unfold chartCoord bondCoordinate
      rw [if_pos hx]
      have := BlockTrees.readAtLevel_enclosingCell (L := ℓ.side) U b.1 b.2
      show minimalLog (gaugeTransform (axialGauge 1 W') W' b'.1 b'.2 *
        (readAtLevel F 1 U (enclosingCell b'.1) b'.2)⁻¹) = _
      rw [show readAtLevel F 1 U (enclosingCell b'.1) b'.2 = U Y b.2 from this]
    by_cases hl : ∃ l, c l = (Y, b.2)
    · refine Or.inr ⟨hl, g * (V Y b.2)⁻¹, fun u => ?_⟩
      simp only [goodMark, frameDeviation, markAlongLog, frameAlongMove]
      rw [hchart, perturb_eq_expUnit_mul, mul_inv_rev, mul_assoc, Submodule.coe_sub]
    · refine Or.inl ⟨(minimalLog (g * (V Y b.2)⁻¹) : imaginaryQuaternions), fun u => ?_⟩
      have h0 : bondMoveLinear c X (Y, b.2) u = 0 := by
        rw [bondMoveLinear_apply]
        exact Finset.sum_eq_zero fun l _ => if_neg fun h => hl ⟨l, h⟩
      have h1 : expUnit (0 : imaginaryQuaternions) = 1 := by
        apply Subtype.ext
        simp [expUnit]
      simp only [goodMark, frameDeviation, frameAlongMove]
      rw [hchart, perturb_eq_expUnit_mul, h0, h1, one_mul, Submodule.coe_sub]
  · refine Or.inl ⟨(minimalLog g : imaginaryQuaternions), fun u => ?_⟩
    have hchart : ∀ U : TorusField n, chartCoord ℓ U W b = minimalLog g := by
      intro U
      unfold chartCoord bondCoordinate
      rw [if_neg hx]
    simp only [goodMark, frameDeviation, frameAlongMove]
    rw [hchart, Submodule.coe_sub]
end YangMills.Construction.MovedTopMarks
end
