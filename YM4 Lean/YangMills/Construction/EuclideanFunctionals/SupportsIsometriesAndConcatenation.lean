import YangMills.Construction.EuclideanFunctionals.TuplesIsometriesFreeSpaceAndMirrorOfFourSpace
import Mathlib
set_option autoImplicit false
open scoped ComplexConjugate
namespace YangMills.Construction.EuclideanFunctionals.MotionRules
def DisjointCompactPosDist : Prop :=
  ∀ A B : Set R4, IsCompact A → IsCompact B → Disjoint A B →
    0 < YangMills.Construction.TestFunctions.setDistR4 A B
def MotionOnFunctions : Prop :=
  ∀ (g g' : EuclidMotion) (f : R4 → ℂ), f ∈ C1c ℂ →
    g.actFn f ∈ C1c ℂ ∧
    supp (g.actFn f) = g '' supp f ∧
    (fun x => (g.actFn f x).re) = g.actFn (fun x => (f x).re) ∧
    (fun x => (g.actFn f x).im) = g.actFn (fun x => (f x).im) ∧
    (fun x => conj (g.actFn f x)) = g.actFn (fun x => conj (f x)) ∧
    (g * g').actFn f = g.actFn (g'.actFn f)
def MotionOnLists : Prop :=
  ∀ U : Set R4, IsOpen U → ∀ g g' : EuclidMotion,
    IsOpen (g '' U) ∧
    Set.BijOn g.actList (sepIn U) (sepIn (g '' U)) ∧
    (∀ X ∈ sepIn U, (g.actList X).length = X.length) ∧
    Set.BijOn g.actFree (freeSpanIn U) (freeSpanIn (g '' U)) ∧
    (∀ F : FreeSep, (g * g').actFree F = g.actFree (g'.actFree F)) ∧
    (∀ F : FreeSep, freeConj (g.actFree F) = g.actFree (freeConj F)) ∧
    ∀ (n : ℕ), 1 ≤ n → ∀ φ : Fin n → R4 → ℂ, (∀ i, φ i ∈ C1c ℂ) →
      (Pairwise fun i j => Disjoint (supp (φ i)) (supp (φ j))) →
      (∀ i, supp (φ i) ⊆ U) →
      complexList φ ∈ freeSpanIn U ∧
        g.actFree (complexList φ) = complexList fun i => g.actFn (φ i)
def ProductOfTwo : Prop :=
  ∀ U V : Set R4, IsOpen U → IsOpen V → Disjoint U V → ∀ g : EuclidMotion,
    (∀ F ∈ freeSpanIn U, ∀ G ∈ freeSpanIn V, freeMul F G ∈ freeSpanIn (U ∪ V)) ∧
    (∀ (a b : ℂ), ∀ F₁ ∈ freeSpanIn U, ∀ G₁ ∈ freeSpanIn V, ∀ G₂ ∈ freeSpanIn V,
      freeMul F₁ (a • G₁ + b • G₂) = a • freeMul F₁ G₁ + b • freeMul F₁ G₂) ∧
    (∀ (a b : ℂ), ∀ F₁ ∈ freeSpanIn U, ∀ F₂ ∈ freeSpanIn U, ∀ G ∈ freeSpanIn V,
      freeMul (a • F₁ + b • F₂) G = a • freeMul F₁ G + b • freeMul F₂ G) ∧
    (∀ F ∈ freeSpanIn U, ∀ G ∈ freeSpanIn V,
      g.actFree (freeMul F G) = freeMul (g.actFree F) (g.actFree G)) ∧
    ∀ F ∈ freeSpanIn U, ∀ G ∈ freeSpanIn V,
      freeConj (freeMul F G) = freeMul (freeConj F) (freeConj G)
def ProductAssoc : Prop :=
  ∀ U V W : Set R4, IsOpen U → IsOpen V → IsOpen W → Disjoint U V → Disjoint U W →
    Disjoint V W → ∀ F ∈ freeSpanIn U, ∀ G ∈ freeSpanIn V, ∀ H ∈ freeSpanIn W,
      freeMul (freeMul F G) H = freeMul F (freeMul G H)
def TranslationRules : Prop :=
  ∀ (g : EuclidMotion) (v w : R4),
    (∀ x, (EuclidMotion.transl v * EuclidMotion.transl w) x =
      EuclidMotion.transl (v + w) x) ∧
    (∀ x, (g * EuclidMotion.transl v) x = (EuclidMotion.transl (g.lin v) * g) x) ∧
    (∀ F : FreeSep, (EuclidMotion.transl v).actFree ((EuclidMotion.transl w).actFree F) =
      (EuclidMotion.transl (v + w)).actFree F) ∧
    ∀ F : FreeSep, g.actFree ((EuclidMotion.transl v).actFree F) =
      (EuclidMotion.transl (g.lin v)).actFree (g.actFree F)
def FlipAndGroupLinear : Prop :=
  timeFlip.offset = 0 ∧ (∀ w ∈ hyperoctahedral, w.offset = 0) ∧ timeFlip⁻¹ = timeFlip
def HalfSpaceImages : Prop :=
  ∀ c t : ℝ,
    timeFlip '' {x | c < x 3} = {x | x 3 < -c} ∧
    EuclidMotion.transl (t • timeVec) '' {x | c < x 3} = {x | c + t < x 3} ∧
    ∀ v ∈ spatialVecs, EuclidMotion.transl v '' {x | c < x 3} = {x | c < x 3}
def TimeStabilizerRules : Prop :=
  ∀ w ∈ timeStabilizer,
    (∀ x, w x 3 = x 3) ∧
    (∀ c : ℝ, w '' {x | c < x 3} = {x | c < x 3}) ∧
    w '' spatialVecs = spatialVecs ∧
    w * timeFlip = timeFlip * w
def ConjugateFlip : Prop :=
  ∀ w ∈ hyperoctahedral,
    w '' upperHalf = {x | 0 < x ⬝ᵥ w timeVec} ∧
    w '' {x | x 3 = 0} = {x | x ⬝ᵥ w timeVec = 0} ∧
    ∀ x, (w * timeFlip * w⁻¹) x = x - (2 * (x ⬝ᵥ w timeVec)) • w timeVec
def AllRules : Prop :=
  DisjointCompactPosDist ∧ MotionOnFunctions ∧ MotionOnLists ∧ ProductOfTwo ∧
    ProductAssoc ∧ TranslationRules ∧ FlipAndGroupLinear ∧ HalfSpaceImages ∧
    TimeStabilizerRules ∧ ConjugateFlip
end YangMills.Construction.EuclideanFunctionals.MotionRules
