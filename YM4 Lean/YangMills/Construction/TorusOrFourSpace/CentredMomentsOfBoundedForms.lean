import YangMills.Construction.LinearAlgebra.BoundedMultilinearForms
import YangMills.Construction.TorusOrFourSpace.ConvergenceOfPartialHierarchiesTupleByTuple
import YangMills.Construction.TorusOrFourSpace.MomentNumbersAndMomentSums
import YangMills.Construction.TorusOrFourSpace.MultilinearFormsOnGrowingDomainsDefs
import YangMills.Construction.TorusOrFourSpace.MultilinearFunctionalsAndProductsOfClasses
import Mathlib
set_option autoImplicit false
open scoped ENNReal
noncomputable section
namespace YangMills.Construction.PeriodicSpace.Kind
section Bounds
variable (D : Params) (E : Kind)
def SetsInBallsSeparated {q : ℕ} (d R : ℝ) (A : Fin q → Set (E.Pt D)) : Prop :=
  (∀ l, ∃ S, IsClosedBallWithRadius D E S R ∧ A l ⊆ S) ∧
    DiagonalLimits.PairwiseSetDistGe D E A d
def SatisfiesFormBounds {q : ℕ} (K : Set (FnTuple D E q)) (W : Fin q → Set (E.Pt D → ℝ))
    (Ψ : K → ℝ) (b : ℝ) : Prop :=
  (∀ h : K, h.1 ∈ productSet D E W →
    ENNReal.ofReal |Ψ h| ≤ ENNReal.ofReal b * ∏ l, sharpNormQ D E (h.1 l)) ∧
  ∀ f g : K, f.1 ∈ productSet D E W → g.1 ∈ productSet D E W →
    ENNReal.ofReal |Ψ f - Ψ g| ≤
      ENNReal.ofReal b * ∑ l, sharpNormQ D E (f.1 l - g.1 l) *
        ∏ m ∈ Finset.univ.erase l, (sharpNormQ D E (f.1 m) + sharpNormQ D E (g.1 m))
end Bounds
section MomentFunctionals
variable {D : Params} {E : Kind}
def Hierarchy.momentFun (Φ : Hierarchy D E) {q : ℕ} (f : sepC1Tuples D E q) : ℝ :=
  Φ.toFunctionalSystem.momentSum f.1 (Φ.defined_of_mem_sepC1Tuples f.2)
def PartialHierarchySeq.momentFun {J₀ : Sequences.PNatIndexSet} {ρ : J₀.carrier → ℝ≥0∞}
    (S : PartialHierarchySeq D E J₀ ρ) (j : J₀.carrier) {q : ℕ}
    (f : sepLipTuplesWithin D E q (centredBall D E (ρ j))) : ℝ :=
  (S.toFunctionalSystem j).momentSum f.1 (S.defined_of_mem_sepLipTuplesWithin j f.2)
def functionalSystemOfSep (Φ : SepFunctionals D E) :
    FunctionalSystem D E where
  domain n _ := sepC1Tuples D E n
  eval := Φ
def momentFunOfSep (Φ : SepFunctionals D E) {q : ℕ}
    (f : sepC1Tuples D E q) : ℝ :=
  (functionalSystemOfSep Φ).momentSum f.1
    ((functionalSystemOfSep Φ).defined_of_mem_sepC1Tuples (fun _ _ _ h => h) f.2)
def PartialHierarchySeq.MomentsTendToAlong {J₀ : Sequences.PNatIndexSet}
    {ρ : J₀.carrier → ℝ≥0∞} (S : PartialHierarchySeq D E J₀ ρ) (J : Sequences.PNatIndexSet)
    (hJ : J.carrier ⊆ J₀.carrier) {q : ℕ} (F : J.carrier → FnTuple D E q) (z : ℝ) : Prop :=
  ∃ (i : ℤ) (hF : ∀ j : (J.filterGe i).carrier,
      F ⟨j.1, j.2.1⟩ ∈ sepLipTuplesWithin D E q (centredBall D E (ρ ⟨j.1, hJ j.2.1⟩))),
    IndexedLimits.ConvergesToAlong J i
      (fun j => ((S.momentFun ⟨j.1, hJ j.2.1⟩ ⟨F ⟨j.1, j.2.1⟩, hF j⟩ : ℝ) : ℂ)) ((z : ℝ) : ℂ)
end MomentFunctionals
namespace CentredMoments
def AbstractBounds : Prop :=
  ∀ q : ℕ, 1 ≤ q → ∀ (V : Fin q → Type) [∀ l, AddCommGroup (V l)] [∀ l, Module ℝ (V l)]
    (p : ∀ l, Seminorm ℝ (V l)) (c : ℕ → ℝ), (∀ k, 2 ≤ k → k ≤ q → 0 ≤ c k) →
    ∀ Ψ : Multilinear.BlockForms V,
      (∀ (I : Finset (Fin q)) (hI : 2 ≤ I.card) (h : ∀ l, V l),
        |Ψ I hI (Multilinear.restrictOrdered h I)| ≤ c I.card * ∏ l ∈ I, p l (h l)) →
      GrowingDomains.IsMultilinearFun (Multilinear.partitionSum Ψ) ∧
        (∀ h : ∀ l, V l,
          |Multilinear.partitionSum Ψ h| ≤
            Multilinear.partitionBound q c * ∏ l, p l (h l)) ∧
        (∀ f g : ∀ l, V l,
          |Multilinear.partitionSum Ψ f - Multilinear.partitionSum Ψ g| ≤
            Multilinear.partitionBound q c *
              ∑ l, p l (f l - g l) * ∏ m ∈ Finset.univ.erase l, (p m (f m) + p m (g m))) ∧
        (q = 1 → (∀ h : ∀ l, V l, Multilinear.partitionSum Ψ h = 0) ∧
          Multilinear.partitionBound q c = 0)
def HierarchyBounds (D : Params) : Prop :=
  ∀ (C : BoundFamily), ∀ Φ ∈ boundedHierarchies D euclidean C, ∀ q : ℕ, 1 ≤ q →
    ∀ d R : ℝ, 0 < d → 0 < R → ∀ A : Fin q → Set (euclidean.Pt D),
      SetsInBallsSeparated D euclidean d R A →
      IsMultilinearOnProduct D euclidean (sepC1Tuples D euclidean q)
          (fun l => c1SupportedIn D euclidean (A l)) Φ.momentFun ∧
        SatisfiesFormBounds D euclidean (sepC1Tuples D euclidean q)
          (fun l => c1SupportedIn D euclidean (A l)) Φ.momentFun (C.momentBound q d R) ∧
        ∀ hq : 2 ≤ q, SatisfiesFormBounds D euclidean (sepC1Tuples D euclidean q)
          (fun l => c1SupportedIn D euclidean (A l)) (Φ.func q hq) (C.val q d R)
def PartialHierarchyBounds (D : Params) : Prop :=
  ∀ (C : BoundFamily) (J₀ : Sequences.PNatIndexSet) (ρ : J₀.carrier → ℝ≥0∞)
    (S : BoundedPartialHierarchySeq D euclidean J₀ ρ C) (q : ℕ), 1 ≤ q →
    ∀ (d R : ℝ), 0 < d → ∀ hR : R ∈ allowedRadii D euclidean,
    ∀ A : Fin q → Set (euclidean.Pt D), SetsInBallsSeparated D euclidean d R A →
    ∀ j : J₀.carrier,
      (∀ (n : ℕ) (hn : 2 ≤ n), n ≤ q → S.threshold n hn R hR ≤ (((j.1 : ℕ+) : ℕ) : ℤ)) →
      (∀ l, A l ⊆ centredBall D euclidean (ρ j)) →
      IsMultilinearOnProduct D euclidean
          (sepLipTuplesWithin D euclidean q (centredBall D euclidean (ρ j)))
          (fun l => lipschitzSupportedIn D euclidean (A l))
          (S.toPartialHierarchySeq.momentFun j) ∧
        SatisfiesFormBounds D euclidean
          (sepLipTuplesWithin D euclidean q (centredBall D euclidean (ρ j)))
          (fun l => lipschitzSupportedIn D euclidean (A l))
          (S.toPartialHierarchySeq.momentFun j) (C.momentBound q d R) ∧
        ∀ hq : 2 ≤ q, SatisfiesFormBounds D euclidean
          (sepLipTuplesWithin D euclidean q (centredBall D euclidean (ρ j)))
          (fun l => lipschitzSupportedIn D euclidean (A l))
          (S.func j q hq) (C.val q d R)
def MomentConvergence (D : Params) : Prop :=
  ∀ (C : BoundFamily) (J₀ : Sequences.PNatIndexSet) (ρ : J₀.carrier → ℝ≥0∞)
    (S : BoundedPartialHierarchySeq D euclidean J₀ ρ C) (J : Sequences.PNatIndexSet)
    (hJ : J.carrier ⊆ J₀.carrier) (Φ : SepFunctionals D euclidean),
    S.toPartialHierarchySeq.TendsToPointwiseAlong J hJ Φ →
    (∀ (q : ℕ) (f : sepC1Tuples D euclidean q),
      S.toPartialHierarchySeq.MomentsTendToAlong J hJ (fun _ => f.1)
        (momentFunOfSep Φ f)) ∧
    ∀ q : ℕ, 1 ≤ q → ∀ d R : ℝ, 0 < d → 0 < R → ∀ A : Fin q → Set (euclidean.Pt D),
      SetsInBallsSeparated D euclidean d R A →
      ∀ (f : FnTuple D euclidean q) (F : J.carrier → FnTuple D euclidean q),
        f ∈ productSet D euclidean (fun l => c1SupportedIn D euclidean (A l)) →
        (∀ j, F j ∈ productSet D euclidean (fun l => c1SupportedIn D euclidean (A l))) →
        (∀ l, IndexedLimits.ConvergesToAlong J 0
          (fun j => (((sharpNormQ D euclidean (F ⟨j.1, j.2.1⟩ l - f l)).toReal : ℝ) : ℂ)) 0) →
        ∃ hf : f ∈ sepC1Tuples D euclidean q,
          S.toPartialHierarchySeq.MomentsTendToAlong J hJ F
            (momentFunOfSep Φ ⟨f, hf⟩)
def Statement : Prop :=
  AbstractBounds ∧
    ∀ D : Params, GrowingDomains.IsLatticePowerScale D →
      HierarchyBounds D ∧ PartialHierarchyBounds D ∧ MomentConvergence D
end CentredMoments
end YangMills.Construction.PeriodicSpace.Kind
