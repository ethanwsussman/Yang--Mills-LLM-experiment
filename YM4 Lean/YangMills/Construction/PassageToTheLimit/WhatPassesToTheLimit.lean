import YangMills.Construction.PassageToTheLimit.SeparatedTuplesMultilinearFunctionalsCentredFunctionalTensors
import Mathlib
set_option autoImplicit false
open Filter Set Topology
open scoped ENNReal ComplexConjugate
noncomputable section
namespace YangMills.Construction
namespace LimitSpaces
def indexAtTop (𝒥 : Set ℕ+) : Filter 𝒥 := comap (fun j : 𝒥 => (j : ℕ+)) atTop
namespace Ambient
variable (s : Conventions.StandingParameters) (E : Ambient)
def ExhaustsCompacts {𝒥 : Set ℕ+} (D : 𝒥 → Set (E.Carrier s)) : Prop :=
  ∀ C : Set (E.Carrier s), E.IsCompactSubset s C → ∀ᶠ j in indexAtTop 𝒥, C ⊆ D j
def lengthBallLT (ρ : ℝ≥0∞) : Set (E.Carrier s) :=
  {y | ENNReal.ofReal (E.euclidLength s y) < ρ}
variable {k : TestKind} {D : Set (E.Carrier s)} {n : ℕ}
open Classical in
def evalOrZero (Ψ : E.SepTuple s k D n → ℝ) (f : Fin n → E.Carrier s → ℝ) : ℝ :=
  if hf : E.IsSepTuple s k D f then Ψ ⟨f, hf⟩ else 0
variable {𝒥 : Set ℕ+} {Dom : 𝒥 → Set (E.Carrier s)}
structure LimitHypotheses (Φ : (j : 𝒥) → E.TupleFunctionals s .lip (Dom j)) : Prop where
  infinite_index : 𝒥.Infinite
  exhausts : E.ExhaustsCompacts s Dom
  multilinear : ∀ (j : 𝒥) (n : ℕ) (hn : 2 ≤ n), E.IsMultilinearOn s (Φ j n hn)
  perm_invariant : ∀ (j : 𝒥) (n : ℕ) (hn : 2 ≤ n), E.IsPermInvariant s (Φ j n hn)
  tendsto_exists : ∀ (n : ℕ) (hn : 2 ≤ n) (X : E.SepTupleUniv s .cOne n), ∃ L : ℝ,
    Tendsto (fun j => E.evalOrZero s (Φ j n hn) X.1) (indexAtTop 𝒥) (𝓝 L)
def limitFunctionals (Φ : (j : 𝒥) → E.TupleFunctionals s .lip (Dom j)) :
    E.TupleFunctionals s .cOne univ :=
  fun n hn X => limUnder (indexAtTop 𝒥) fun j => E.evalOrZero s (Φ j n hn) X.1
def TuplesEventuallyInDomains (Dom : 𝒥 → Set (E.Carrier s)) : Prop :=
  ∀ (n : ℕ) (X : E.SepTupleUniv s .cOne n), ∀ᶠ j in indexAtTop 𝒥,
    E.IsSepTuple s .lip (Dom j) X.1
def LimitCentredProperties (Φ : (j : 𝒥) → E.TupleFunctionals s .lip (Dom j)) : Prop :=
  (∀ (n : ℕ) (hn : 2 ≤ n), E.IsMultilinearOn s (E.limitFunctionals s Φ n hn) ∧
    E.IsPermInvariant s (E.limitFunctionals s Φ n hn)) ∧
  (∀ (j : 𝒥) (q : ℕ), 1 ≤ q → E.IsMultilinearOn s (E.centredSum s (Φ j) (q := q))) ∧
  (∀ q : ℕ, 1 ≤ q → E.IsMultilinearOn s (E.centredSum s (E.limitFunctionals s Φ) (q := q))) ∧
  ∀ (q : ℕ) (Y : E.SepTupleUniv s .cOne q),
    (∀ᶠ j in indexAtTop 𝒥, E.IsSepTuple s .lip (Dom j) Y.1) ∧
    Tendsto (fun j => E.evalOrZero s (E.centredSum s (Φ j) (q := q)) Y.1)
      (indexAtTop 𝒥) (𝓝 (E.centredSum s (E.limitFunctionals s Φ) Y))
def valuesVec (Φ : (j : 𝒥) → E.TupleFunctionals s .lip (Dom j)) {r : ℕ}
    (len : Fin r → ℕ) (hlen : ∀ i, 2 ≤ len i)
    (X : (i : Fin r) → E.SepTupleUniv s .cOne (len i)) (j : 𝒥) : Fin r → ℝ :=
  fun i => E.evalOrZero s (Φ j (len i) (hlen i)) (X i).1
def limitsVec (Φ : (j : 𝒥) → E.TupleFunctionals s .lip (Dom j)) {r : ℕ}
    (len : Fin r → ℕ) (hlen : ∀ i, 2 ≤ len i)
    (X : (i : Fin r) → E.SepTupleUniv s .cOne (len i)) : Fin r → ℝ :=
  fun i => E.limitFunctionals s Φ (len i) (hlen i) (X i)
def ClosedRelationsPersist (Φ : (j : 𝒥) → E.TupleFunctionals s .lip (Dom j)) : Prop :=
  ∀ (r : ℕ), 1 ≤ r → ∀ (len : Fin r → ℕ) (hlen : ∀ i, 2 ≤ len i)
    (X : (i : Fin r) → E.SepTupleUniv s .cOne (len i)),
    (∀ F : Set (Fin r → ℝ), IsClosed F →
      (∀ᶠ j in indexAtTop 𝒥, E.valuesVec s Φ len hlen X j ∈ F) →
        E.limitsVec s Φ len hlen X ∈ F) ∧
    ∀ g : (Fin r → ℝ) → ℝ, Continuous g →
      (∀ᶠ j in indexAtTop 𝒥, g (E.valuesVec s Φ len hlen X j) = 0) →
        g (E.limitsVec s Φ len hlen X) = 0
def BoundsPersist (Φ : (j : 𝒥) → E.TupleFunctionals s .lip (Dom j)) : Prop :=
  ∀ (n : ℕ) (hn : 2 ≤ n) (X : E.SepTupleUniv s .cOne n) (b : ℝ),
    (∀ᶠ j in indexAtTop 𝒥, |E.evalOrZero s (Φ j n hn) X.1| ≤ b) →
      |E.limitFunctionals s Φ n hn X| ≤ b
def PositivityPersists (Φ : (j : 𝒥) → E.TupleFunctionals s .lip (Dom j)) : Prop :=
  ∀ (t : ℕ), 1 ≤ t → ∀ (ζ : Fin t → ℂ) (len : Fin t → Fin t → ℕ)
    (Y : (i i' : Fin t) → E.SepTupleUniv s .cOne (len i i')),
    (∀ᶠ j in indexAtTop 𝒥, (∑ i, ∑ i', conj (ζ i) * ζ i' *
        ((E.evalOrZero s (E.centredSum s (Φ j) (q := len i i')) (Y i i').1 : ℝ) : ℂ)) ∈
      Complex.ofReal '' Ici 0) →
    (∑ i, ∑ i', conj (ζ i) * ζ i' *
        ((E.centredSum s (E.limitFunctionals s Φ) (Y i i') : ℝ) : ℂ)) ∈ Complex.ofReal '' Ici 0
def PairwiseSeparatedBy {q : ℕ} (d : ℝ) (A : Fin q → Set (E.Carrier s)) : Prop :=
  ∀ l l', l ≠ l' → ENNReal.ofReal d ≤ E.infSetDist s (A l) (A l')
def partitionConstant (q : ℕ) (C : ℕ → ℝ) : ℝ :=
  ∑ π ∈ SetPartition.nonSingletonPartitions q, ∏ J ∈ π.parts, C J.card
def BoundedOnSets (M : SharpParameter) (Ψ : E.TupleFunctionals s k D) {q : ℕ}
    (A : Fin q → Set (E.Carrier s)) (C : ℕ → ℝ) : Prop :=
  ∀ (n : ℕ) (hn : 2 ≤ n), n ≤ q → ∀ l : Fin n → Fin q, StrictMono l →
    ∀ h : E.SepTuple s k D n, (∀ i, h.1 i ∈ E.testWithin s k (A (l i))) →
      |Ψ n hn h| ≤ C n * ∏ i, E.normSharp s M (h.1 i)
def CentredContinuousOnSets (M : SharpParameter) (Ψ : E.TupleFunctionals s k D) {q : ℕ}
    (A : Fin q → Set (E.Carrier s)) (C : ℕ → ℝ) : Prop :=
  ∀ f g : E.SepTuple s k D q, (∀ l, f.1 l ∈ E.testWithin s k (A l)) →
    (∀ l, g.1 l ∈ E.testWithin s k (A l)) →
    |E.centredSum s Ψ f - E.centredSum s Ψ g| ≤
      partitionConstant q C * ∑ l, E.normSharp s M (f.1 l - g.1 l) *
        ∏ l' ∈ Finset.univ.erase l, (E.normSharp s M (f.1 l') + E.normSharp s M (g.1 l'))
def EquicontinuityPersists (M : SharpParameter)
    (Φ : (j : 𝒥) → E.TupleFunctionals s .lip (Dom j)) : Prop :=
  ∀ (q : ℕ), 2 ≤ q → ∀ d : ℝ, 0 < d → ∀ C : ℕ → ℝ, (∀ n, 2 ≤ n → n ≤ q → 0 ≤ C n) →
    (∀ (j : 𝒥) (A : Fin q → Set (E.Carrier s)), (∀ l, A l ⊆ Dom j) →
      E.PairwiseSeparatedBy s d A → E.BoundedOnSets s M (Φ j) A C →
        E.CentredContinuousOnSets s M (Φ j) A C) ∧
    (∀ C' : ℕ → ℝ, (∀ n, 2 ≤ n → n ≤ q → C' n = C n) →
      partitionConstant q C' = partitionConstant q C) ∧
    ∀ A : Fin q → Set (E.Carrier s), E.PairwiseSeparatedBy s d A →
      (E.BoundedOnSets s M (E.limitFunctionals s Φ) A C →
        E.CentredContinuousOnSets s M (E.limitFunctionals s Φ) A C) ∧
      ((∀ᶠ j in indexAtTop 𝒥, (∀ l, A l ⊆ Dom j) ∧ E.BoundedOnSets s M (Φ j) A C) →
        E.BoundedOnSets s M (E.limitFunctionals s Φ) A C)
def ApproximatingTuplesConverge (M : SharpParameter)
    (Φ : (j : 𝒥) → E.TupleFunctionals s .lip (Dom j)) : Prop :=
  ∀ (q : ℕ), 2 ≤ q → ∀ d : ℝ, 0 < d → ∀ C : ℕ → ℝ, (∀ n, 2 ≤ n → n ≤ q → 0 ≤ C n) →
    ∀ A : Fin q → Set (E.Carrier s), E.PairwiseSeparatedBy s d A →
      (∀ᶠ j in indexAtTop 𝒥, (∀ l, A l ⊆ Dom j) ∧ E.BoundedOnSets s M (Φ j) A C) →
      ∀ (h : E.SepTupleUniv s .cOne q) (approx : 𝒥 → Fin q → E.Carrier s → ℝ),
        (∀ l, h.1 l ∈ E.c1Within s (A l)) →
        (∀ j l, approx j l ∈ E.lipWithin s (A l)) →
        (∀ l, Tendsto (fun j => E.normSharp s M (approx j l - h.1 l)) (indexAtTop 𝒥) (𝓝 0)) →
        Tendsto (fun j => E.evalOrZero s (E.centredSum s (Φ j) (q := q)) (approx j))
          (indexAtTop 𝒥) (𝓝 (E.centredSum s (E.limitFunctionals s Φ) h))
def complexTensorProd {q : ℕ} (f : Fin q → E.Carrier s → ℝ) : (Fin q → E.Carrier s) → ℂ :=
  E.tensorProd s fun l x => ((f l x : ℝ) : ℂ)
def tensorSpan (D : Set (E.Carrier s)) (q : ℕ) : Submodule ℂ ((Fin q → E.Carrier s) → ℂ) :=
  Submodule.span ℂ (range fun f : E.SepTuple s .cOne D q => E.complexTensorProd s f.1)
def tensorSpanElem {q : ℕ} (f : E.SepTuple s .cOne D q) : E.tensorSpan s D q :=
  ⟨E.complexTensorProd s f.1, Submodule.subset_span ⟨f, rfl⟩⟩
def FactorsThroughTensorSpan {q : ℕ} (Ψ : E.SepTuple s .cOne D q → ℝ) : Prop :=
  (∀ (P : Type) [Fintype P] (ζ : P → ℂ) (f : P → E.SepTuple s .cOne D q),
    ∑ p, ζ p • E.complexTensorProd s (f p).1 = 0 → ∑ p, ζ p * ((Ψ (f p) : ℝ) : ℂ) = 0) ∧
  ∃! form : E.tensorSpan s D q →ₗ[ℂ] ℂ,
    ∀ f : E.SepTuple s .cOne D q, form (E.tensorSpanElem s f) = ((Ψ f : ℝ) : ℂ)
end Ambient
def Ambient.limitPassageStatement : Prop :=
  ∀ (s : Conventions.StandingParameters) (E : Ambient) (M : SharpParameter),
    (∀ (q : ℕ), 1 ≤ q → ∀ (D : Set (E.Carrier s)) (Ψ : E.SepTuple s .cOne D q → ℝ),
      E.IsMultilinearOn s Ψ → E.FactorsThroughTensorSpan s Ψ) ∧
    (∀ 𝒥 : Set ℕ+, 𝒥.Infinite →
      (∀ Dom : 𝒥 → Set (E.Carrier s), (∀ j, Dom j = univ) → E.ExhaustsCompacts s Dom) ∧
      ∀ (ρ : 𝒥 → ℝ≥0∞) (Dom : 𝒥 → Set (E.Carrier s)), (∀ j, 0 < ρ j) →
        Tendsto ρ (indexAtTop 𝒥) (𝓝 ⊤) → (∀ j, Dom j = E.lengthBallLT s (ρ j)) →
          E.ExhaustsCompacts s Dom) ∧
    ∀ (𝒥 : Set ℕ+) (Dom : 𝒥 → Set (E.Carrier s))
      (Φ : (j : 𝒥) → E.TupleFunctionals s .lip (Dom j)),
      E.LimitHypotheses s Φ →
        E.TuplesEventuallyInDomains s Dom ∧ E.LimitCentredProperties s Φ ∧
        E.ClosedRelationsPersist s Φ ∧ E.BoundsPersist s Φ ∧ E.PositivityPersists s Φ ∧
        E.EquicontinuityPersists s M Φ ∧ E.ApproximatingTuplesConverge s M Φ ∧
        ∀ q : ℕ, 1 ≤ q →
          E.FactorsThroughTensorSpan s (E.centredSum s (E.limitFunctionals s Φ) (q := q))
end LimitSpaces
end YangMills.Construction
end
