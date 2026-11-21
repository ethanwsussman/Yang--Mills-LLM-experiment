import YangMills.Construction.TorusOrFourSpace.TestFunctionsAndDistributionsOnASet
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.PeriodicSpace.Kind
variable (D : Params) (E : Kind)
def IsIsometry (s : Kind.Pt D E → Kind.Pt D E) : Prop :=
  ∀ y y', Kind.quotDist D E (s y) (s y') = Kind.quotDist D E y y'
namespace Tuple
variable {p : ℕ+}
def supDist (x x' : Kind.Tuple D E p) : ℝ :=
  ⨆ i, Kind.quotDist D E (x i) (x' i)
variable {D E} {Ω Ω' : Set (Kind.Tuple D E p)}
def HasOrderLEOn (h : Ω' ⊆ Ω) (k : ℕ) (T : Kind.Tuple.testFns D E Ω → ℂ) : Prop :=
  Kind.Tuple.IsDistribOfOrderLE k (Kind.Tuple.restrictDistrib h T)
def HasLocallyFiniteOrder (T : Kind.Tuple.testFns D E Ω → ℂ) : Prop :=
  ∀ x ∈ Ω, ∃ (U : Set (Kind.Tuple D E p)) (h : U ⊆ Ω),
    Kind.Tuple.IsOpenT D E U ∧ x ∈ U ∧ ∃ k, HasOrderLEOn h k T
end Tuple
end YangMills.Construction.PeriodicSpace.Kind
end
