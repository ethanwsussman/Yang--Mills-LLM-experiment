import YangMills.Construction.ReflectionPositivity.SeparatedTuplesOnOneTorusIsometriesAndSymmetricFunctions
import Mathlib
set_option autoImplicit false
open scoped ENNReal Matrix
noncomputable section
namespace YangMills.Construction.ReflectionPositivity.TorusTuples.SeparationAndSymmetry
variable (s : Conventions.StandingParameters)
def lipTuplesSeparatedBy (n : ℕ) (d : ℝ) : Set (FnTuple s ℝ) :=
  {X | X.length = n ∧ (∀ h ∈ X, IsLipschitzReal (s := s) h) ∧
    TorusCutoffs.PairwiseSeparated (s := s) (fun l : Fin X.length => supp (s := s) (X.get l)) d}
def GapPos : Prop :=
  ∀ X : FnTuple s ℝ, IsDisjointTuple X → 2 ≤ X.length → 0 < gap X
def DisjointTuplesEqIUnion : Prop :=
  ∀ n : ℕ, 2 ≤ n →
    disjointTuples s n = ⋃ (d : ℝ) (_ : 0 < d), lipTuplesSeparatedBy s n d
def LipTuplesSeparatedByEq : Prop :=
  ∀ n : ℕ, 2 ≤ n → ∀ d : ℝ, 0 < d →
    lipTuplesSeparatedBy s n d = {X | X ∈ disjointTuples s n ∧ ENNReal.ofReal d ≤ gap X}
def ComponentsAreTestFamily : Prop :=
  ∀ (n : ℕ), 2 ≤ n → ∀ X : disjointTuples s n,
    SchwingerFunctions.IsTorusTestFamily (L := s.L) (m := s.m) (componentFamily X.1 X.2.2)
def RestrictionsDisjoint : Prop :=
  ∀ X Y : FnTuple s ℝ, IsDisjointTuple X → IsRestriction (s := s) Y X → IsDisjointTuple Y
def SignedMatricesAndShiftsIsometric : Prop :=
  (∀ w : Matrix (Fin 4) (Fin 4) ℝ, w ∈ PeriodicLattice.signedPermMatrices →
    IsTorusIsometry s (signedMatrixMap s w)) ∧
  ∀ v : s.Torus, IsTorusIsometry s (shiftBy v)
def IsometryBijectiveOrthogonal : Prop :=
  ∀ r : s.Torus → s.Torus, IsTorusIsometry s r →
    ∃ e : s.Torus ≃ s.Torus, ⇑e = r ∧ IsTorusIsometry s e.symm ∧
      ∃ R ∈ Matrix.orthogonalGroup (Fin 4) ℝ, ∃ w : Fin 4 → ℝ,
        ∀ y, r (TorusCutoffs.proj s y) = TorusCutoffs.proj s (R *ᵥ y + w)
def IsometryTransportProps : Prop :=
  ∀ r : s.Torus ≃ s.Torus, IsTorusIsometry s r → ∀ h : s.Torus → ℝ, IsLipschitzReal h →
    IsLipschitzReal (transport r h) ∧
    supp (s := s) (transport r h) = r '' supp (s := s) h ∧
    TestFunctions.uniformNorm (transport r h) = TestFunctions.uniformNorm h ∧
    TestFunctions.lipConstTorus (ℓ := PeriodicLattice.torusSide s.L s.m) (transport r h) =
      TestFunctions.lipConstTorus (ℓ := PeriodicLattice.torusSide s.L s.m) h ∧
    (∀ m' : ℕ, TorusCutoffs.TorusData.sharpNorm ⟨s, m'⟩ (transport r h) =
      TorusCutoffs.TorusData.sharpNorm ⟨s, m'⟩ h) ∧
    (TorusCutoffs.IsC1 h → TorusCutoffs.IsC1 (transport r h))
def IsometryTransportTupleProps : Prop :=
  ∀ r : s.Torus ≃ s.Torus, IsTorusIsometry s r → ∀ X : FnTuple s ℝ, IsDisjointTuple X →
    IsDisjointTuple (transportTuple r X) ∧ gap (transportTuple r X) = gap X
def Statement : Prop :=
  ∀ s : Conventions.StandingParameters,
    GapPos s ∧ DisjointTuplesEqIUnion s ∧
    LipTuplesSeparatedByEq s ∧ ComponentsAreTestFamily s ∧
    RestrictionsDisjoint s ∧ SignedMatricesAndShiftsIsometric s ∧
    IsometryBijectiveOrthogonal s ∧ IsometryTransportProps s ∧ IsometryTransportTupleProps s
end YangMills.Construction.ReflectionPositivity.TorusTuples.SeparationAndSymmetry
end
