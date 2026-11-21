import YangMills.Construction.Lattice.AdicGridPoints
import YangMills.Construction.ToriAtArbitraryCouplings.ChoicesOfCountableDenseSets
import YangMills.Construction.ToriAtArbitraryCouplings.ClassesOfFunctionsSeparatedTuplesAndTheSeparation
import YangMills.Construction.ToriAtArbitraryCouplings.TheCountableFamilyAdaptedToSupports
import Mathlib
set_option autoImplicit false
open scoped ENNReal
noncomputable section
namespace YangMills.Construction.ToriAtArbitraryCouplings
open ReflectionPositivity.AxisMirror (Ambient)
open TorusSymmetries (actOn translateOn)
open TorusTransport (hyperoctahedral)
def DenseForNorm {X : Type*} (N : (X → ℝ) → ℝ) (V A : Set (X → ℝ)) : Prop :=
  ∀ f ∈ V, ∀ ε : ℝ, 0 < ε → ∃ g ∈ A, N (f - g) < ε
structure SeparableBanachSet {X : Type*} (V : Set (X → ℝ)) (N : (X → ℝ) → ℝ) : Prop where
  zero_mem : 0 ∈ V
  add_mem : ∀ f ∈ V, ∀ g ∈ V, f + g ∈ V
  smul_mem : ∀ c : ℝ, ∀ f ∈ V, c • f ∈ V
  norm_eq_zero_iff : ∀ f ∈ V, N f = 0 ↔ f = 0
  norm_add_le : ∀ f ∈ V, ∀ g ∈ V, N (f + g) ≤ N f + N g
  norm_smul : ∀ c : ℝ, ∀ f ∈ V, N (c • f) = |c| * N f
  complete : ∀ u : ℕ → X → ℝ, (∀ k, u k ∈ V) →
    (∀ ε : ℝ, 0 < ε → ∃ K : ℕ, ∀ j k, K ≤ j → K ≤ k → N (u j - u k) < ε) →
    ∃ f ∈ V, ∀ ε : ℝ, 0 < ε → ∃ K : ℕ, ∀ k, K ≤ k → N (u k - f) < ε
  separable : ∃ A : Set (X → ℝ), A ⊆ V ∧ A.Countable ∧ DenseForNorm N V A
namespace TorusSide
variable (t : TorusSide)
def symmetryPerm : (E : Ambient) → hyperoctahedral → Equiv.Perm (t.Point E)
  | .torus, w => actOn t.asMirrorData.toStandingParameters .torus w
  | .euclidean, w => actOn t.asMirrorData.toStandingParameters .euclidean w
def shiftPerm : (E : Ambient) → (Fin 4 → ℝ) → Equiv.Perm (t.Point E)
  | .torus, v => translateOn t.asMirrorData.toStandingParameters .torus
      (AmbientPoints.proj t.asMirrorData.toStandingParameters .torus v)
  | .euclidean, v => translateOn t.asMirrorData.toStandingParameters .euclidean
      (AmbientPoints.proj t.asMirrorData.toStandingParameters .euclidean v)
def IsSymmetryOrGridShift (E : Ambient) (r : Equiv.Perm (t.Point E)) : Prop :=
  (∃ w : hyperoctahedral, r = t.symmetryPerm E w) ∨
    ∃ v : Fin 4 → ℝ, (∀ i, v i ∈ PeriodicLattice.adicGridPoints t.L) ∧ r = t.shiftPerm E v
def choiceComponents (E : Ambient) (D : t.supportFamily E → Set (t.Point E → ℝ)) :
    Set (t.Point E → ℝ) :=
  ⋃ Q, D Q
def SupportsGiveSeparableBanach (m' : ℕ) (E : Ambient) : Prop :=
  (∀ Q ∈ t.supportFamily E, t.IsCompactWrt E Q ∧
    t.c1VanishingOutside E Q = t.c1SuppIn E Q ∧
    SeparableBanachSet (t.c1VanishingOutside E Q) (t.c1NormOn E) ∧
    ∀ A : Set (t.Point E → ℝ), A ⊆ t.c1VanishingOutside E Q →
      (DenseForNorm (t.c1NormOn E) (t.c1VanishingOutside E Q) A ↔
        DenseForNorm (t.c1GradNorm E) (t.c1VanishingOutside E Q) A) ∧
      (DenseForNorm (t.c1NormOn E) (t.c1VanishingOutside E Q) A →
        DenseForNorm (t.sharpNormAt m' E) (t.c1VanishingOutside E Q) A)) ∧
  (∃ D : t.supportFamily E → Set (t.Point E → ℝ), t.IsCountableC1DenseChoice E D) ∧
  ∀ D : t.supportFamily E → Set (t.Point E → ℝ),
    t.IsCountableC1DenseChoice E D ↔ t.IsCountableGradDenseFamily E D
def SupportsSqueezeBetween (E : Ambient) : Prop :=
  (∀ K U : Set (t.Point E), t.IsCompactWrt E K → t.IsOpenWrt E U → K ⊆ U →
    ∃ Q ∈ t.supportFamily E, K ⊆ Q ∧ Q ⊆ U) ∧
  ∀ (n : ℕ) (K U : Fin n → Set (t.Point E)), (∀ i, t.IsCompactWrt E (K i)) →
    Pairwise (Function.onFun Disjoint K) → (∀ i, t.IsOpenWrt E (U i)) → (∀ i, K i ⊆ U i) →
    ∃ Q : Fin n → Set (t.Point E), (∀ i, Q i ∈ t.supportFamily E) ∧ (∀ i, K i ⊆ Q i ∧ Q i ⊆ U i) ∧
      Pairwise (Function.onFun Disjoint Q)
def AdaptedTuplesCountableSeparated (E : Ambient) : Prop :=
  ∀ D : t.supportFamily E → Set (t.Point E → ℝ), t.IsCountableC1DenseChoice E D →
    (t.adaptedTupleSet E D).Countable ∧ t.adaptedTupleSet E D ⊆ t.sepTuples E ∧
    ∀ (n : ℕ), 2 ≤ n → ∀ (Q : Fin n → t.supportFamily E) (g : Fin n → t.Point E → ℝ),
      Pairwise (Function.onFun Disjoint fun i => (Q i).1) → (∀ i, g i ∈ D (Q i)) →
      (⨅ (i : Fin n) (k : Fin n) (_ : i ≠ k), t.setDist E (Q i).1 (Q k).1) ≤
          t.supportGap E (List.ofFn g) ∧
        0 < ⨅ (i : Fin n) (k : Fin n) (_ : i ≠ k), t.setDist E (Q i).1 (Q k).1
structure IsStableDenseChoice (E : Ambient) (D : t.supportFamily E → Set (t.Point E → ℝ)) :
    Prop where
  isChoice : t.IsCountableC1DenseChoice E D
  comp_symm_mem : ∀ r : Equiv.Perm (t.Point E), t.IsSymmetryOrGridShift E r →
    ∀ f ∈ t.choiceComponents E D, f ∘ r.symm ∈ t.choiceComponents E D
  sum_smul_mem : ∀ (n : ℕ) (c : Fin n → ℚ) (f : Fin n → t.Point E → ℝ),
    (∀ i, f i ∈ t.choiceComponents E D) → (∑ i, (c i : ℝ) • f i) ∈ t.choiceComponents E D
  eq_inter : ∀ Q : t.supportFamily E, D Q = t.choiceComponents E D ∩ t.c1VanishingOutside E Q.1
def PairwiseDisjointSupp (E : Ambient) (X : Ambient.FnList t.asMirrorData E) : Prop :=
  X.Pairwise fun f g => Disjoint (t.closedSupport E f) (t.closedSupport E g)
def StableChoicesGiveStableTuples (E : Ambient) : Prop :=
  (∃ D : t.supportFamily E → Set (t.Point E → ℝ), t.IsStableDenseChoice E D) ∧
  ∀ D : t.supportFamily E → Set (t.Point E → ℝ), t.IsStableDenseChoice E D →
    t.adaptedTupleSet E D = {X | 1 ≤ X.length ∧ (∀ f ∈ X, f ∈ t.choiceComponents E D) ∧
      t.PairwiseDisjointSupp E X} ∧
    (∀ r : Equiv.Perm (t.Point E), t.IsSymmetryOrGridShift E r →
      ∀ X ∈ t.adaptedTupleSet E D, X.map (fun f => f ∘ r.symm) ∈ t.adaptedTupleSet E D) ∧
    ∀ X ∈ t.adaptedTupleSet E D, ∀ Y ∈ t.adaptedTupleSet E D,
      t.PairwiseDisjointSupp E (Ambient.append X Y) →
      Ambient.append X Y ∈ t.adaptedTupleSet E D
end TorusSide
namespace SupportAdaptedFamily
def Claim : Prop :=
  ∀ (t : TorusSide), 8 * 105 ^ 4 ≤ t.L → ∀ (m' : ℕ) (E : Ambient),
    t.SupportsGiveSeparableBanach m' E ∧ t.SupportsSqueezeBetween E ∧
      t.AdaptedTuplesCountableSeparated E ∧ t.StableChoicesGiveStableTuples E
end SupportAdaptedFamily
end YangMills.Construction.ToriAtArbitraryCouplings
end
