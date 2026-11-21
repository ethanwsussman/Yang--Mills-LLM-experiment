import YangMills.Construction.Continuum.FormsOfTheSeparatedTuplesOfFourSpaceTheirSpanAndFunctionals
import YangMills.Construction.Continuum.SeparatedTuplesTheirConcatenationAndCombinationsOnFourSpace
import Mathlib
set_option autoImplicit false
open YangMills.Construction.ReflectionPositivity.AxisMirror (Ambient)
open YangMills.Construction.AmbientPoints YangMills.Construction.Continuum.SeparatedFourTuples
noncomputable section
namespace YangMills.Construction.Continuum.CanonicalDecomposition
variable {s : YangMills.Construction.Conventions.StandingParameters}
def transportedTuple (r : EuclideanFour s ≃ EuclideanFour s) (X : FunctionTuple s .euclidean) :
    FunctionTuple s .euclidean :=
  ⟨X.1, transportTuple r X.2⟩
theorem transportedTuple_nil (r : EuclideanFour s ≃ EuclideanFour s) :
    transportedTuple r (nilTuple s .euclidean) = nilTuple s .euclidean := by
  refine Sigma.ext rfl (heq_of_eq ?_)
  funext i
  exact i.elim0
variable (s) in
def shiftedTuple (v : Fin 4 → ℝ) (X : FunctionTuple s .euclidean) :
    FunctionTuple s .euclidean :=
  transportedTuple (YangMills.Construction.R4TupleForms.shiftEquiv s v) X
theorem canConcat_nil_right (X : SepTuple s) :
    CanConcat X (nilSepTuple s) :=
  fun _ j => (show Fin 0 from j).elim0
theorem canConcat_nil_left (X : SepTuple s) :
    CanConcat (nilSepTuple s) X :=
  fun i _ => (show Fin 0 from i).elim0
theorem concat_nil (X : SepTuple s) :
    concat X (nilSepTuple s) (canConcat_nil_right X) = X := by
  refine sepTuple_ext rfl fun i => ?_
  exact congrFun (Fin.append_right_nil (tupleComponents X) (tupleComponents (nilSepTuple s)) rfl) i
theorem nil_concat (X : SepTuple s) :
    concat (nilSepTuple s) X (canConcat_nil_left X) = X := by
  have h : tupleLength (concat (nilSepTuple s) X (canConcat_nil_left X)) = tupleLength X :=
    Nat.zero_add _
  refine sepTuple_ext h fun i => ?_
  exact congrFun (Fin.append_left_nil (tupleComponents (nilSepTuple s)) (tupleComponents X) rfl) i
end YangMills.Construction.Continuum.CanonicalDecomposition
