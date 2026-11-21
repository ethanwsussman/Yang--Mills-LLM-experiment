import YangMills.Construction.QuaternionicWilsonModel.SomeFunctionalHasSchwingerFunctions
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.TopAux.SchwingerSequenceExists
open ConfigSpace SystemsWithFiveBounds
open SeparatedTuples (TupleFunctional)
def vacuumSequence : ConfigSpace.FlatSequence
  | 0 => fun c => show ℂ from c.1
  | _ + 1 => fun _ => 0
def vacuumFunctional : SeparatedTuples.TupleFunctional where
  toFun X := if X.1 = [] then 1 else 0
  map_nil := by simp [SeparatedTuples.SepTuple.nil]
theorem vacuumFunctional_eval_of_pos {n : ℕ} (hn : 1 ≤ n) (X : ConfigSpace.SepFamilyOfLength n) :
    SystemsWithFiveBounds.evalOnSepFamily vacuumFunctional ⟨n, X⟩ = 0 := by
  have h : List.ofFn X.1 ≠ [] := by
    intro e
    have := congrArg List.length e
    simp at this
    omega
  show (if List.ofFn X.1 = [] then (1 : ℝ) else 0) = 0
  rw [if_neg h]
theorem hasSchwingerSequence_vacuum :
    SystemsWithFiveBounds.HasSchwingerSequence vacuumFunctional vacuumSequence := by
  refine ⟨⟨?_, fun n hn i b b' X X' X'' _ _ _ => ?_⟩, fun _ => rfl, fun m =>
    ⟨⟨fun c c' φ ψ χ _ => ?_, 1, 0, le_rfl, le_rfl, fun φ => ?_⟩, fun X _ h => ?_⟩⟩
  · show (if List.ofFn ConfigSpace.nilFamily = [] then (1 : ℝ) else 0) = 1
    simp
  · show SystemsWithFiveBounds.evalOnSepFamily vacuumFunctional ⟨n, X''⟩ =
      b * SystemsWithFiveBounds.evalOnSepFamily vacuumFunctional ⟨n, X⟩ +
        b' * SystemsWithFiveBounds.evalOnSepFamily vacuumFunctional ⟨n, X'⟩
    rw [vacuumFunctional_eval_of_pos hn, vacuumFunctional_eval_of_pos hn,
      vacuumFunctional_eval_of_pos hn]
    simp
  · show (0 : ℂ) = c * 0 + c' * 0
    simp
  · show ‖(0 : ℂ)‖ ≤ _
    simp
  · show (0 : ℂ) = ((SystemsWithFiveBounds.evalOnSepFamily vacuumFunctional ⟨m + 1, X⟩ : ℝ) : ℂ)
    rw [vacuumFunctional_eval_of_pos (Nat.succ_pos m)]
    simp
theorem holds : Statement :=
  ⟨vacuumFunctional, vacuumSequence, hasSchwingerSequence_vacuum⟩
end YangMills.Construction.TopAux.SchwingerSequenceExists
end
