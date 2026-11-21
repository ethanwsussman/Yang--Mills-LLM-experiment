import YangMills.Construction.Torus.SeparatedTuplesAndIsometriesOfTorusOrFourSpace
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.AmbientPoints.SeparatedTupleStability
variable (s : Conventions.StandingParameters) (E : ReflectionPositivity.AxisMirror.Ambient)
def InverseContinuousTsupport : Prop :=
  ∀ r : Pt s E ≃ Pt s E, IsDistIsometry r →
    IsDistIsometry r.symm ∧ Continuous r ∧ Continuous r.symm ∧
      ∀ (X : Type) [Zero X] (f : Pt s E → X),
        tsupport (transportFn r f) = r '' tsupport f
def TransportKeepsC1 : Prop :=
  ∀ r : Pt s E ≃ Pt s E, IsDistIsometry r →
    ∀ f : Pt s E → ℝ, IsC1Fn f → IsC1Fn (transportFn r f)
def SeparatedStable : Prop :=
  ∀ n : ℕ, 1 ≤ n → ∀ f ∈ separatedTuples s E n,
    (∀ σ : Equiv.Perm (Fin n), permuteTuple σ f ∈ separatedTuples s E n) ∧
    (∀ J : Finset (Fin n), J.Nonempty → restrictTuple f J ∈ separatedTuples s E J.card) ∧
    ∀ r : Pt s E ≃ Pt s E, IsDistIsometry r →
      transportTuple r f ∈ separatedTuples s E n ∧
        ∀ J : Finset (Fin n), J.Nonempty →
          restrictTuple (transportTuple r f) J = transportTuple r (restrictTuple f J)
def C1SupportedSpaces : Prop :=
  (∀ A : Set (Pt s E), ∃ V : Submodule ℝ (Pt s E → ℝ),
    (V : Set (Pt s E → ℝ)) = c1CompactlySupportedIn A) ∧
  ∀ n : ℕ, 1 ≤ n → ∀ A : Fin n → Set (Pt s E),
    Pairwise (fun i j => PositivelySeparated s E (A i) (A j)) →
      Set.pi Set.univ (fun i => c1CompactlySupportedIn (A i)) ⊆ separatedTuples s E n
def holds : Prop :=
  ∀ (s : Conventions.StandingParameters) (E : ReflectionPositivity.AxisMirror.Ambient),
    InverseContinuousTsupport s E ∧ TransportKeepsC1 s E ∧ SeparatedStable s E ∧
      C1SupportedSpaces s E
end YangMills.Construction.AmbientPoints.SeparatedTupleStability
end
