import YangMills.Construction.TorusOrFourSpace.BoxesStockOfSupportsAndFamilyOfTuples
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.PeriodicSpace.Kind
variable (D : Params) (E : Kind)
structure DenseChoiceFamily where
  sets : supportStock D E → Set (E.Pt D → ℝ)
  isDense : IsDenseFamily D E sets
namespace DenseChoiceFamily
variable {D E} (F : DenseChoiceFamily D E)
def tuples : Set (Σ n : ℕ, Fin n → E.Pt D → ℝ) :=
  tupleFamily D E F.sets
def tuplesGeTwo : Set (Σ n : ℕ, Fin n → E.Pt D → ℝ) :=
  tupleFamilyLengthGeTwo D E F.sets
def Builds {n : ℕ} (φ : Fin n → E.Pt D → ℝ) (Q : Fin n → supportStock D E) : Prop :=
  Kind.IsBuiltFrom D E F.sets φ Q
end DenseChoiceFamily
end YangMills.Construction.PeriodicSpace.Kind
