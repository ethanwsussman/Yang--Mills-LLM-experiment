import YangMills.Construction.PassageToTheLimit.SeparatedTuplesMultilinearFunctionalsCentredFunctionalTensors
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction
namespace LimitSpaces
namespace Ambient
def IsFunctionSubspace {X : Type*} (V : Set (X → ℝ)) : Prop :=
  ∃ W : Submodule ℝ (X → ℝ), (W : Set (X → ℝ)) = V
def IsNormOn {X : Type*} (V : Set (X → ℝ)) (N : (X → ℝ) → ℝ) : Prop :=
  (∀ u ∈ V, 0 ≤ N u) ∧ (∀ u ∈ V, N u = 0 → u = 0) ∧
    (∀ (t : ℝ), ∀ u ∈ V, N (t • u) = |t| * N u) ∧
    ∀ u ∈ V, ∀ v ∈ V, N (u + v) ≤ N u + N v
variable {s : Conventions.StandingParameters} {E : Ambient} {n : ℕ}
theorem IsSepC1Tuple.isSepLipTuple_of_subset {D D' : Set (E.Carrier s)}
    (hsub : D' ⊆ D) {f : Fin n → E.Carrier s → ℝ} (hf : E.IsSepC1Tuple s D' f) :
    E.IsSepLipTuple s D f :=
  ⟨fun i => ⟨(hf.1.1 i).1, (hf.1.1 i).2.1, (hf.1.1 i).2.2.trans hsub⟩, hf.1.2⟩
def restrictToC1 {D D' : Set (E.Carrier s)} (hsub : D' ⊆ D)
    (Φ : E.SepTuple s .lip D n → ℝ) (T : E.SepTuple s .cOne D' n) : ℝ :=
  Φ ⟨T.1, IsSepC1Tuple.isSepLipTuple_of_subset hsub T.2⟩
variable (s E)
def TestSpacesNormed (M : SharpParameter) (A : Set (E.Carrier s)) : Prop :=
  IsFunctionSubspace (E.lipWithin s A) ∧
    (∀ f ∈ E.lipWithin s A,
      E.IsContinuousInto s f ∧ TestFunctions.IsBoundedFun f) ∧
    IsFunctionSubspace (E.c1Within s A) ∧
    E.c1Within s A ⊆ E.lipWithin s A ∧
    IsNormOn (E.lipWithin s A) (E.normSharp s M) ∧
    IsNormOn (E.c1Within s A) (E.normC1 s)
def ProductsSepTuples (D : Set (E.Carrier s)) (n : ℕ) : Prop :=
  (∀ A : Fin n → Set (E.Carrier s), (∀ i, A i ⊆ D) →
    (Pairwise fun i j => E.PositivelySeparated s (A i) (A j)) →
      (∀ f : Fin n → E.Carrier s → ℝ, (∀ i, f i ∈ E.lipWithin s (A i)) →
        E.IsSepLipTuple s D f) ∧
      ∀ f : Fin n → E.Carrier s → ℝ, (∀ i, f i ∈ E.c1Within s (A i)) →
        E.IsSepC1Tuple s D f) ∧
    (∀ f : Fin n → E.Carrier s → ℝ, E.IsSepLipTuple s D f →
      (∀ i, E.closedSupport s (f i) ⊆ D) ∧
      (Pairwise fun i j => E.PositivelySeparated s (E.closedSupport s (f i)) (E.closedSupport s (f j))) ∧
      ∀ i, f i ∈ E.lipWithin s (E.closedSupport s (f i))) ∧
    ∀ f : Fin n → E.Carrier s → ℝ, E.IsSepC1Tuple s D f →
      ∀ i, f i ∈ E.c1Within s (E.closedSupport s (f i))
def SepTuplesStable (D : Set (E.Carrier s)) : Prop :=
  (∀ (m : ℕ) (f : Fin m → E.Carrier s → ℝ), E.IsSepC1Tuple s D f →
    E.IsSepLipTuple s D f) ∧
    (∀ (k : TestKind) (m : ℕ) (D' : Set (E.Carrier s)) (f : Fin m → E.Carrier s → ℝ),
      D' ⊆ D → E.IsSepTuple s k D' f → E.IsSepTuple s k D f) ∧
    (∀ (k : TestKind) (m : ℕ) (f : Fin m → E.Carrier s → ℝ),
      E.IsSepTuple s k D f →
        (∀ J : Finset (Fin m), E.IsSepTuple s k D (pickComponents f J)) ∧
        ∀ σ : Equiv.Perm (Fin m), E.IsSepTuple s k D (f ∘ σ)) ∧
    ∀ (r : ℕ) (len : Fin r → ℕ) (T : (p : Fin r) → Fin (len p) → E.Carrier s → ℝ),
      (∀ p, E.IsSepLipTuple s univ (T p)) →
        E.IsCompactSubset s (⋃ p, ⋃ i, E.closedSupport s (T p i))
def MultilinearRestrictVanish (D : Set (E.Carrier s)) (n : ℕ) : Prop :=
  (∀ (D' : Set (E.Carrier s)) (hsub : D' ⊆ D) (Φ : E.SepTuple s .lip D n → ℝ),
    E.IsMultilinearOn s Φ → E.IsMultilinearOn s (restrictToC1 hsub Φ)) ∧
    ∀ (k : TestKind) (Φ : E.SepTuple s k D n → ℝ), E.IsMultilinearOn s Φ →
      ∀ (T : E.SepTuple s k D n) (i : Fin n), T.1 i = 0 → Φ T = 0
end Ambient
def Ambient.testSpacesAndSepTuples : Prop :=
  ∀ (s : Conventions.StandingParameters) (E : Ambient) (M : SharpParameter) (A D : Set (E.Carrier s)) (n : ℕ), 1 ≤ n →
    E.TestSpacesNormed s M A ∧ E.ProductsSepTuples s D n ∧
      E.SepTuplesStable s D ∧ E.MultilinearRestrictVanish s D n
end LimitSpaces
end YangMills.Construction
end
