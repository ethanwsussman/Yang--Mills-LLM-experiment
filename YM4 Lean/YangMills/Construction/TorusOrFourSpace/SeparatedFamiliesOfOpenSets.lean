import YangMills.Construction.TorusOrFourSpace.AdmissibleFamiliesOfOpenSets
import Mathlib
set_option autoImplicit false
open scoped ENNReal
noncomputable section
namespace YangMills.Construction.PeriodicSpace.Kind
variable (D : Params) (E : Kind) {n : ℕ+}
def IsSeparatedWith (R d : ℝ) (G : Fin (n : ℕ) → Set (E.Pt D)) : Prop :=
  2 ≤ (n : ℕ) ∧ AdmissibleWith D E R d G
def IsSeparated (G : Fin (n : ℕ) → Set (E.Pt D)) : Prop :=
  ∃ R d : ℝ, IsSeparatedWith D E R d G
end YangMills.Construction.PeriodicSpace.Kind
