import YangMills.Construction.Matrices.SpecialUnitaryTwo
import Mathlib
open Set
open scoped ContDiff Matrix.Norms.L2Operator Topology
noncomputable section
namespace YangMills.Construction.Submanifolds
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
def IsSmoothSubmanifold (S : Set E) : Prop :=
  ∀ p ∈ S, ∃ (k k' : ℕ) (φ : OpenPartialHomeomorph E ((Fin k → ℝ) × (Fin k' → ℝ))),
    p ∈ φ.source ∧ ContDiffOn ℝ ∞ φ φ.source ∧ ContDiffOn ℝ ∞ φ.symm φ.target ∧
      φ '' (φ.source ∩ S) = φ.target ∩ {y | y.2 = 0}
end YangMills.Construction.Submanifolds
namespace YangMills.Construction.Matrices.FamilyProducts
def familyNbhd {ι : Type} (w : ι → ComplexMatrix2) (ε : ℝ) : Set (ι → ComplexMatrix2) :=
  {v | ∀ i, ComplexMatrix2.operatorNorm (v i - w i) < ε}
def FamilyProductsStatement : Prop :=
  ∀ (ι : Type) [Fintype ι] [Nonempty ι],
    (∀ w : ι → ComplexMatrix2,
      (∀ ε : ℝ, 0 < ε → IsOpen (familyNbhd w ε)) ∧
        ∀ U ∈ 𝓝 w, ∃ ε : ℝ, 0 < ε ∧ familyNbhd w ε ⊆ U) ∧
    (∀ S T : Set (ι → ComplexMatrix2), T ⊆ S →
      (ComplexMatrix2.IsRelativelyOpen S T ↔
        ∀ w ∈ T, ∃ ε : ℝ, 0 < ε ∧ ∀ v ∈ S, v ∈ familyNbhd w ε → v ∈ T)) ∧
    Submanifolds.IsSmoothSubmanifold
      (ComplexMatrix2.compactProduct fun _ : ι => ComplexMatrix2.FactorKind.group)
end YangMills.Construction.Matrices.FamilyProducts
