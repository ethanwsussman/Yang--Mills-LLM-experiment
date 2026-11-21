import YangMills.Construction.ClusterExpansion.PolymerGraphs
import YangMills.Construction.Conventions.FamiliesAndUnorderedSums
import Mathlib
set_option autoImplicit false
open scoped Classical NNReal
noncomputable section
universe u w
namespace YangMills.Construction
open Families
namespace ClusterExpansion.PolymerRelation
section Tuples
variable {P : Type u}
abbrev NonemptyTuples (P : Type u) : Type u := Σ n : positiveNat, Tuple P (n : ℕ)
end Tuples
variable {P : Type u} [Fintype P] (S : PolymerRelation P)
section Cluster
def clusterTerm (h : P → ℂ) {n : ℕ} (Z : Tuple P n) : ℂ :=
  (1 / (n.factorial : ℂ)) * ((S.ursellFunction Z : ℝ) : ℂ) * ∏ i, h (Z i)
def clusterTermOf (h : P → ℂ) (Z : NonemptyTuples P) : ℂ :=
  S.clusterTerm h Z.2
def ClusterSeriesAbsConv (h : P → ℂ) : Prop :=
  IsAbsSummable (S.clusterTermOf h)
end Cluster
section Fibers
variable {T : Type w}
def fiberSum (u : NonemptyTuples P → T) (t : T) (h : P → ℂ) : ℂ :=
  familySum fun Z : u ⁻¹' {t} => S.clusterTermOf h Z
end Fibers
section Support
variable {L : Type w}
def supportUnion (e : P ↪ Set L) (Z : NonemptyTuples P) : Set L :=
  ⋃ i, e (Z.2 i)
end Support
end ClusterExpansion.PolymerRelation
end YangMills.Construction
