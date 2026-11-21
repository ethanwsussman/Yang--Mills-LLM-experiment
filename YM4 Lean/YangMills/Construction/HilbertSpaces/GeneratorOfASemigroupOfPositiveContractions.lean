import YangMills.Construction.HilbertSpaces.ReconstructionFromAPositiveFormDefs
import Mathlib
set_option autoImplicit false
open Set Filter Topology
open scoped NNReal ComplexOrder InnerProductSpace
open YangMills.Construction.FormsOperators (TendstoStrongly IsContractive IsOrthProjOnto IsPositiveBounded
  IsSelfAdj IsC0Semigroup ker ofCLM)
noncomputable section
namespace YangMills.Construction.PositiveFormReconstruction.PositiveContractionGenerator
def Statement : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (T : ℝ≥0 → E →L[ℂ] E), IsC0Semigroup T →
    (∀ s, IsPositiveBounded (T s) ∧ IsSelfAdj (ofCLM (T s)) ∧
      IsContractive (T s)) →
    (∀ s, ker (ofCLM (T s)) = {0}) ∧
    ExistsUnique (IsSemigroupGenerator T) ∧
    IsSemigroupGenerator T (semigroupGenerator T) ∧
    IsNegLogOf (semigroupGenerator T) (T 1) ∧
    (∀ x, T 1 x = x → x ∈ ker (semigroupGenerator T)) ∧
    IsOrthProjOnto (kerProjection (semigroupGenerator T)) (ker (semigroupGenerator T)) ∧
    TendstoStrongly atTop T (kerProjection (semigroupGenerator T))
end YangMills.Construction.PositiveFormReconstruction.PositiveContractionGenerator
