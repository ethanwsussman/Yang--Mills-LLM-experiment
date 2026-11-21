import YangMills.Construction.TorusOrFourSpace.AdmissibleFamiliesOfOpenSets
import YangMills.Construction.TorusOrFourSpace.CutOffsOnAProductOfOpenSets
import YangMills.Construction.TorusOrFourSpace.HierarchiesCentredMomentsAndObeyingABoundFunction
import YangMills.Construction.TorusOrFourSpace.PermutationsDiagonalActionsTranslationsAndInvariance
import Mathlib
set_option autoImplicit false
open scoped ENNReal
noncomputable section
namespace YangMills.Construction.PeriodicSpace
def factorBoundBase (M : ℝ) : ℝ := 160 * M
namespace Kind
variable (D : Params) (E : Kind) {n : ℕ+}
def tensorSpan (G : Fin (n : ℕ) → Set (E.Pt D)) :
    Set (Tuple.testFns D E (Tuple.boxSet D E G)) :=
  {F | ∃ (m : ℕ) (φ : Fin m → Fin (n : ℕ) → E.Pt D → ℂ),
    (∀ k i, φ k i ∈ Tuple.singleTestFns D E (G i)) ∧
      F.1 = ∑ k, Tuple.tensorProd D E (φ k)}
def EqOneNearSupportProj (χ : Fin (n : ℕ) → E.Pt D → ℝ)
    (F : E.Tuple D n → ℂ) : Prop :=
  ∀ i, ∃ U, IsOpenQ D E U ∧
    (fun y : E.Tuple D n => y i) '' Tuple.supportT D E F ⊆ U ∧
      ∀ y ∈ U, χ i y = 1
namespace Hierarchy
variable {D E}
def ValueAtTensor (S : Hierarchy D E) (hn : 2 ≤ (n : ℕ)) {Ω : Set (E.Tuple D n)}
    (T : Tuple.testFns D E Ω → ℂ) (φ : FnTuple D E (n : ℕ)) : Prop :=
  ∃ (hφ : φ ∈ sepC1Tuples D E (n : ℕ))
    (hF : Tuple.cutoffTensor D E φ ∈ Tuple.testFns D E Ω),
    T ⟨_, hF⟩ = ((S.func (n : ℕ) hn ⟨φ, hφ⟩ : ℝ) : ℂ)
def IsBoxDistrib (S : Hierarchy D E) (hn : 2 ≤ (n : ℕ))
    (G : Fin (n : ℕ) → Set (E.Pt D))
    (T : Tuple.testFns D E (Tuple.boxSet D E G) → ℂ) : Prop :=
  Tuple.IsDistrib T ∧
    ∀ φ, Tuple.IsCutoffFamily D E G φ → S.ValueAtTensor hn T φ
def IsOffDiagDistrib (S : Hierarchy D E) (hn : 2 ≤ (n : ℕ))
    (T : Tuple.testFns D E (pairwiseDistinct D E n) → ℂ) : Prop :=
  Tuple.IsDistrib T ∧
    ∀ G : Fin (n : ℕ) → Set (E.Pt D), Admissible D E G →
      ∃ h : Tuple.boxSet D E G ⊆ pairwiseDistinct D E n,
        S.IsBoxDistrib hn G (Tuple.restrictDistrib h T)
def CutoffBound (C : BoundFamily) (R d : ℝ) (G : Fin (n : ℕ) → Set (E.Pt D))
    (T : Tuple.testFns D E (Tuple.boxSet D E G) → ℂ)
    (χ : Fin (n : ℕ) → E.Pt D → ℝ)
    (F : Tuple.testFns D E (Tuple.boxSet D E G)) : Prop :=
  ENNReal.ofReal ‖T F‖ ≤
    ENNReal.ofReal (factorBoundBase D.M ^ (n : ℕ) *
        C.val (n : ℕ) d (maxMemberDiam D E G).toReal * cutoffBound n (2 * R)) *
      (∏ i, Tuple.c1NormSingleReal D E (χ i)) *
      Tuple.cNorm D E (5 * (n : ℕ) + 1) F.1
def BoxProperties (S : Hierarchy D E) (C : BoundFamily) (hn : 2 ≤ (n : ℕ)) (R d : ℝ)
    (G : Fin (n : ℕ) → Set (E.Pt D)) : Prop :=
  (∃! T, S.IsBoxDistrib hn G T) ∧
    Tuple.DenseInTestFns (tensorSpan D E G) ∧
    ((∃ i, G i = ∅) → Tuple.testFns D E (Tuple.boxSet D E G) = {0}) ∧
    ∀ T, S.IsBoxDistrib hn G T →
      ((∀ i, (G i).Nonempty) → ∀ χ, Tuple.IsCutoffFamily D E G χ →
        ∀ F, EqOneNearSupportProj D E χ F.1 → CutoffBound C R d G T χ F) ∧
      ((∃ i, G i = ∅) → ∀ F, T F = 0) ∧
      Tuple.IsDistribOfOrderLE (5 * (n : ℕ) + 1) T
def OffDiagProperties (S : Hierarchy D E) (hn : 2 ≤ (n : ℕ))
    (T : Tuple.testFns D E (pairwiseDistinct D E n) → ℂ) : Prop :=
  (∀ G : Fin (n : ℕ) → Set (E.Pt D), Admissible D E G →
    ∃ h : Tuple.boxSet D E G ⊆ pairwiseDistinct D E n,
      Tuple.IsDistribOfOrderLE (5 * (n : ℕ) + 1)
        (Tuple.restrictDistrib h T)) ∧
    Tuple.IsDistribOfOrderLE (5 * (n : ℕ) + 1) T ∧
    (∀ f ∈ sepC1Tuples D E (n : ℕ), (∀ i, IsSmoothFn D E (f i)) →
      S.ValueAtTensor hn T f) ∧
    (∀ T' : Tuple.testFns D E (pairwiseDistinct D E n) → ℂ,
      Tuple.IsDistrib T' →
      (∀ f ∈ sepC1Tuples D E (n : ℕ), (∀ i, IsSmoothFn D E (f i)) →
        S.ValueAtTensor hn T' f) → T' = T) ∧
    ∀ ψ : TupleMap D E n, ψ.InvariantFunctional (S.func (n : ℕ) hn) → ψ.InvariantDistrib T
end Hierarchy
end Kind
end YangMills.Construction.PeriodicSpace
