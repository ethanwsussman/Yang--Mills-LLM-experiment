import YangMills.Construction.EuclideanFunctionals.CombinationsOfTuplesComplexComponentsAndConvergenceInC1
import Mathlib
set_option autoImplicit false
open scoped ComplexConjugate
noncomputable section
namespace YangMills.Construction.EuclideanFunctionals.TupleRules
def MulDefined3 (F A A' : FreeSep) : Prop :=
  MulDefined F A ∧ MulDefined F A' ∧ MulDefined A A'
def fullyExpanded {n : ℕ} (h : Fin n → R4 → ℂ) : FreeSep :=
  ∑ ε : Fin n → Fin 2,
    (Complex.I ^ ∑ l, (ε l : ℕ)) • toFree (List.ofFn fun l => reOrImPart (ε l) (h l))
def ReImAndMotionOfFns : Prop :=
  ∀ (s : SharpScale) (g g' : EuclidMotion) (f : R4 → ℂ), f ∈ C1c ℂ →
    (fun x => (f x).re) ∈ C1c ℝ ∧
    (fun x => (f x).im) ∈ C1c ℝ ∧
    supp (fun x => (f x).re) ∪ supp (fun x => (f x).im) ⊆ supp f ∧
    g.actFn f ∈ C1c ℂ ∧
    supp (g.actFn f) = g '' supp f ∧
    (fun x => (g.actFn f x).re) = g.actFn (fun x => (f x).re) ∧
    (fun x => (g.actFn f x).im) = g.actFn (fun x => (f x).im) ∧
    g.actFn (g'.actFn f) = (g * g').actFn f ∧
    s.sharpNorm (g.actFn f) = s.sharpNorm f
def MotionOfListsAndCombs : Prop :=
  ∀ (g : EuclidMotion) (U : Set R4), IsOpen U →
    IsOpen (g '' U) ∧
    (∀ n : ℕ, Set.BijOn g.actList (sepNIn n U) (sepNIn n (g '' U)) ∧
      Set.InvOn (g⁻¹).actList g.actList (sepNIn n U)
        (sepNIn n (g '' U))) ∧
    Set.BijOn g.actFree (finCombIn U : Set FreeSep) (finCombIn (g '' U) : Set FreeSep)
def MotionOnFree : Prop :=
  ∀ (g g' : EuclidMotion) (F : FreeSep),
    g.actFree (g'.actFree F) = (g * g').actFree F ∧
    freeConj (g.actFree F) = g.actFree (freeConj F) ∧
    combSupp (g.actFree F) = g '' combSupp F ∧
    tensorCompZero (freeConj F) = conj (tensorCompZero F) ∧
    (∀ q, 1 ≤ q → tensorComp q (freeConj F) = fun x => conj (tensorComp q F x)) ∧
    tensorCompZero (g.actFree F) = tensorCompZero F ∧
    (∀ q, 1 ≤ q → ∀ x : YangMills.Construction.TestSpaces.PointTuple q,
      tensorComp q (g.actFree F) x = tensorComp q F fun l => g⁻¹ (x l)) ∧
    ∀ v : R4,
      tensorCompZero ((EuclidMotion.transl v).actFree F) = tensorCompZero F ∧
      ∀ q, 1 ≤ q → tensorComp q ((EuclidMotion.transl v).actFree F) =
        translateArgs v (tensorComp q F)
def SupportListsOfMulSeparated : Prop :=
  ∀ F G : FreeSep, MulDefined F G →
    ∀ X ∈ F.support, ∀ Y ∈ G.support, listAppend X.1 Y.1 ∈ sepAll
def MulOnDisjointOpen : Prop :=
  ∀ U V : Set R4, IsOpen U → IsOpen V → Disjoint U V →
    (∀ F ∈ finCombIn U, ∀ G ∈ finCombIn V,
      MulDefined F G ∧ freeMul F G ∈ finCombIn (U ∪ V)) ∧
    (∀ a b : ℂ, ∀ F₁ ∈ finCombIn U, ∀ F₂ ∈ finCombIn U, ∀ G ∈ finCombIn V,
      freeMul (a • F₁ + b • F₂) G = a • freeMul F₁ G + b • freeMul F₂ G) ∧
    ∀ a b : ℂ, ∀ F ∈ finCombIn U, ∀ G₁ ∈ finCombIn V, ∀ G₂ ∈ finCombIn V,
      freeMul F (a • G₁ + b • G₂) = a • freeMul F G₁ + b • freeMul F G₂
def DefinedMulRules : Prop :=
  ∀ (g : EuclidMotion) (F G : FreeSep), MulDefined F G →
    combSupp (freeMul F G) ⊆ combSupp F ∪ combSupp G ∧
    MulDefined (freeConj F) (freeConj G) ∧
    freeConj (freeMul F G) = freeMul (freeConj F) (freeConj G) ∧
    MulDefined (g.actFree F) (g.actFree G) ∧
    g.actFree (freeMul F G) = freeMul (g.actFree F) (g.actFree G)
def MulAssoc : Prop :=
  ∀ F G H : FreeSep, MulDefined3 F G H →
    MulDefined (freeMul F G) H ∧
    MulDefined F (freeMul G H) ∧
    freeMul (freeMul F G) H = freeMul F (freeMul G H)
def ComplexTupleRules : Prop :=
  ∀ (U : Set R4), IsOpen U → ∀ (g : EuclidMotion) (n : ℕ) (f : Fin n → R4 → ℂ),
    ComplexComponents f → (∀ l, supp (f l) ⊆ U) →
    complexTuple f ∈ finCombIn U ∧
    combSupp (complexTuple f) ⊆ ⋃ l, supp (f l) ∧
    tensorComp n (complexTuple f) = tensorOfFns f ∧
    tensorCompZero (complexTuple f) = 0 ∧
    (∀ q, 1 ≤ q → q ≠ n → tensorComp q (complexTuple f) = 0) ∧
    ComplexComponents (fun l => g.actFn (f l)) ∧
    g.actFree (complexTuple f) = complexTuple (fun l => g.actFn (f l)) ∧
    ComplexComponents (fun l x => conj (f l x)) ∧
    freeConj (complexTuple f) ∈ finCombIn U ∧
    complexTuple (fun l x => conj (f l x)) ∈ finCombIn U ∧
    SameTensors (freeConj (complexTuple f))
      (complexTuple fun l x => conj (f l x)) ∧
    complexTuple f = complexList f ∧
    fullyExpanded f ∈ finCombIn U ∧
    SameTensors (fullyExpanded f) (complexTuple f)
def TimeFlipHalfSpaces : Prop :=
  timeFlip⁻¹ = timeFlip ∧ ∀ t : ℝ, timeFlip '' {x | t < x 3} = {x | x 3 < -t}
def FlipConjMulDefined : Prop :=
  (∀ t : ℝ, 0 ≤ t → ∀ F ∈ finCombIn {x | t < x 3}, ∀ G ∈ finCombIn {x | t < x 3},
    flipConj F ∈ finCombIn {x | x 3 < -t} ∧
    MulDefined (flipConj F) G) ∧
  ∀ t : ℝ, 0 < t → ∀ F ∈ finCombIn {x | t < x 3}, ∀ G ∈ finCombIn {x | t < x 3},
    ∀ f : R4 → ℂ, f ∈ C1c ℂ → supp f ⊆ {x | |x 3| < t} →
      MulDefined3 (flipConj F)
        (complexTuple fun _ : Fin 1 => f) G
def TimeStabilizerCommutes : Prop :=
  ∀ w ∈ timeStabilizer,
    w * timeFlip = timeFlip * w ∧
    w '' upperHalf = upperHalf ∧
    ∀ (v : R4) (β : Type) (f : R4 → β),
      w.actFn ((EuclidMotion.transl v).actFn f) =
        (EuclidMotion.transl (w v)).actFn (w.actFn f)
def FlipConjMulSesquilinear : Prop :=
  ∀ t : ℝ, 0 ≤ t →
    (∀ a b : ℂ, ∀ F₁ ∈ finCombIn {x | t < x 3}, ∀ F₂ ∈ finCombIn {x | t < x 3},
      ∀ G ∈ finCombIn {x | t < x 3},
        freeMul (flipConj (a • F₁ + b • F₂)) G =
          conj a • freeMul (flipConj F₁) G + conj b • freeMul (flipConj F₂) G) ∧
    ∀ a b : ℂ, ∀ F ∈ finCombIn {x | t < x 3}, ∀ G₁ ∈ finCombIn {x | t < x 3},
      ∀ G₂ ∈ finCombIn {x | t < x 3},
        freeMul (flipConj F) (a • G₁ + b • G₂) =
          a • freeMul (flipConj F) G₁ + b • freeMul (flipConj F) G₂
def TupleSpanActionRules : Prop :=
  ReImAndMotionOfFns ∧ MotionOfListsAndCombs ∧ MotionOnFree ∧
    SupportListsOfMulSeparated ∧ MulOnDisjointOpen ∧
    DefinedMulRules ∧ MulAssoc ∧ ComplexTupleRules ∧
    TimeFlipHalfSpaces ∧ FlipConjMulDefined ∧ TimeStabilizerCommutes ∧
    FlipConjMulSesquilinear
end YangMills.Construction.EuclideanFunctionals.TupleRules
