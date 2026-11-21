import YangMills.Construction.TorusOrFourSpace.TestFunctionsAndDistributionsOnASet
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.PeriodicSpace
namespace Kind.Tuple
variable (D : Params) (E : Kind) {p : ℕ+}
def ValuedInUnitInterval (φ : E.Tuple D p → ℂ) : Prop :=
  ∀ x, ∃ t ∈ Set.Icc (0 : ℝ) 1, φ x = (t : ℂ)
def PartitionOfUnityExists (p : ℕ+) : Prop :=
  ∀ (r : ℕ+) (C : Set (E.Tuple D p)) (U : Fin (r : ℕ) → Set (E.Tuple D p)),
    IsCompactT D E C → (∀ b, IsOpenT D E (U b)) → C ⊆ ⋃ b, U b →
    ∃ φ : Fin (r : ℕ) → E.Tuple D p → ℂ,
      (∀ b, φ b ∈ testFns D E (U b)) ∧ (∀ b, ValuedInUnitInterval D E (φ b)) ∧
      ∃ N : Set (E.Tuple D p), IsOpenT D E N ∧ C ⊆ N ∧ ∀ x ∈ N, ∑ b, φ b x = 1
def BumpAboveCompactExists (p : ℕ+) : Prop :=
  ∀ C U : Set (E.Tuple D p), IsCompactT D E C → IsOpenT D E U → C ⊆ U →
    ∃ φ ∈ testFns D E U, ValuedInUnitInterval D E φ ∧
      ∃ N : Set (E.Tuple D p), IsNhd D E C N ∧ ∀ x ∈ N, φ x = 1
end Kind.Tuple
def PartitionsOfUnity.Statement : Prop :=
  ∀ (D : Params) (E : Kind) (p : ℕ+),
    Kind.Tuple.PartitionOfUnityExists D E p ∧
    Kind.Tuple.BumpAboveCompactExists D E p
end YangMills.Construction.PeriodicSpace
