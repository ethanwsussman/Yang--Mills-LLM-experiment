import YangMills.Construction.Continuum.FirstFactsOnTheTestSpacesProof
import Mathlib
set_option autoImplicit false
open Filter Topology TopologicalSpace
open scoped ContDiff
noncomputable section
namespace YangMills.Construction.Distributions
abbrev TuplePoint (n : ℕ) : Type := Fin n → Fin 4 → ℝ
variable {n : ℕ}
def testFunctionSpace (W : Opens (TuplePoint n)) : Submodule ℂ (TuplePoint n → ℂ) where
  carrier := {F | ContDiff ℝ ∞ F ∧ HasCompactSupport F ∧ tsupport F ⊆ W}
  add_mem' := by
    rintro F G ⟨hF, cF, sF⟩ ⟨hG, cG, sG⟩
    exact ⟨hF.add hG, cF.add cG, (tsupport_add F G).trans (Set.union_subset sF sG)⟩
  zero_mem' := by
    refine ⟨contDiff_const, HasCompactSupport.zero, ?_⟩
    simp [tsupport]
  smul_mem' := by
    rintro a F ⟨hF, cF, sF⟩
    have hs : Function.support (a • F) ⊆ Function.support F :=
      Function.support_const_smul_subset a F
    exact ⟨hF.const_smul a, cF.mono hs, (closure_mono hs).trans sF⟩
variable {W : Opens (TuplePoint n)}
theorem isOpen_injectiveTuples (n : ℕ) :
    IsOpen (TestFunctions.injectiveTuples (Fin 4 → ℝ) n) := by apply _root_.YangMills.Construction.TestSpaces.Elementary.isOpen_injectiveTuples <;> assumption
def offDiagonalPower (O : Opens (Fin 4 → ℝ)) (n : ℕ) : Opens (TuplePoint n) where
  carrier := Set.univ.pi (fun _ => (O : Set (Fin 4 → ℝ))) ∩
    TestFunctions.injectiveTuples (Fin 4 → ℝ) n
  is_open' :=
    (isOpen_set_pi Set.finite_univ fun _ _ => O.isOpen).inter (isOpen_injectiveTuples n)
end YangMills.Construction.Distributions
end
