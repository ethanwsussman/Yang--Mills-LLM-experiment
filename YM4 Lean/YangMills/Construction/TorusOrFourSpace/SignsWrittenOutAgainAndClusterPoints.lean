import YangMills.Construction.TorusOrFourSpace.EvaluationsAtDegenerateArguments
import Mathlib
set_option autoImplicit false
open scoped ENNReal
noncomputable section
namespace YangMills.Construction.PeriodicSpace.Kind.PartialHierarchySeq
variable {D : Params} {E : Kind} {J₀ : Sequences.PNatIndexSet} {ρ : J₀.carrier → ℝ≥0∞}
def FrequentlyAt (_Φ : PartialHierarchySeq D E J₀ ρ)
    (P : J₀.carrier → Prop) : Prop :=
  ∀ k : ℤ, ∃ j : J₀.carrier, k ≤ (((j.1 : ℕ+) : ℕ) : ℤ) ∧ P j
def IsClusterHierarchy (Φ : PartialHierarchySeq D E J₀ ρ) (Ξ : Hierarchy D E) : Prop :=
  ∀ (F : Finset (SepTuplesAll D E)) (ε : ℝ), 0 < ε →
    Φ.FrequentlyAt fun j => ∀ p ∈ F,
      Φ.HoldsAt j p.1.2 p.2.1 fun x => |x - Ξ.func p.1.1 p.1.2 p.2| < ε
end YangMills.Construction.PeriodicSpace.Kind.PartialHierarchySeq
