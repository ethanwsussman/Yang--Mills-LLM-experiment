import YangMills.Construction.EuclideanFunctionals.CentredFunctionalOnSeparatedTensors
import YangMills.Construction.EuclideanFunctionals.PulledDownNormsTheInsertionValueAndClassesOfTensors
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.EuclideanFunctionals
namespace TensorTranslation
def complexOfPart (ε : Fin 2) (h : R4 → ℂ) : R4 → ℂ :=
  fun x => ((reOrImPart ε h x : ℝ) : ℂ)
def RealTensorExpansion {q : ℕ} (h : Fin q → R4 → ℂ) : Prop :=
  tensorOfFns h = ∑ ε : Fin q → Fin 2,
    (Complex.I ^ ∑ l, (ε l : ℕ)) • tensorOfFns fun l => complexOfPart (ε l) (h l)
def RealTermsAbove (c : ℝ) {q : ℕ} (h : Fin q → R4 → ℂ) : Prop :=
  ∀ ε : Fin q → Fin 2,
    (∀ l, reOrImPart (ε l) (h l) ∈ C1c ℝ) ∧
    (Pairwise fun k l =>
      Disjoint (supp (reOrImPart (ε k) (h k))) (supp (reOrImPart (ε l) (h l)))) ∧
    ∀ l, supp (reOrImPart (ε l) (h l)) ⊆ {x | c < x 3}
variable {m : SharpScale} {S : ConnFamily} (σ : EuclidFunctionalWithRecon m S)
def TensorsAboveHeight : Prop :=
  ∀ c : ℝ, 0 ≤ c → ∀ q : ℕ, 1 ≤ q → ∀ h : Fin q → R4 → ℂ,
    (∀ l, h l ∈ C1c ℂ) →
    (Pairwise fun k l => Disjoint (supp (h k)) (supp (h l))) →
    (∀ l, supp (h l) ⊆ {x | c < x 3}) →
      RealTensorExpansion h ∧
      (∀ (ε : Fin 2) (l : Fin q), supp (reOrImPart ε (h l)) ⊆ supp (h l)) ∧
      RealTermsAbove c h ∧
      complexTuple h ∈ finCombIn upperHalf ∧
      HasSoleTensorComp q (tensorOfFns h) (complexTuple h) ∧
      reconClass σ (complexTuple h) = tensorClass σ h ∧
      complexTuple h ∈ finCombIn {x | c < x 3}
def TranslateSepTensors (S : ConnFamily) : Prop :=
  (∀ (z : R4) (q : ℕ), ∀ A ∈ sepTensorSpan q,
    translateArgs z A ∈ sepTensorSpan q ∧
      centeredOnTensor S q (translateArgs z A) = centeredOnTensor S q A) ∧
  sepTensorSpan 0 = ⊤ ∧
  ∀ (z : R4) (A : TestSpaces.PointTuple 0 → ℂ) (e : TestSpaces.PointTuple 0),
    translateArgs z A = A ∧ centeredOnTensor S 0 A = A e
def raise (c : ℝ) (F : FreeSep) : FreeSep := (EuclidMotion.transl (c • timeVec)).actFree F
def RaiseBijIsometric : Prop :=
  ∀ c : ℝ, 0 < c →
    Set.BijOn (raise c) (finCombIn upperHalf) (finCombIn {x | c < x 3}) ∧
    Set.InvOn (pullDown c) (raise c) (finCombIn upperHalf)
      (finCombIn {x | c < x 3}) ∧
    ∀ F ∈ finCombIn upperHalf,
      heightNorm σ c (raise c F) = ‖reconClass σ F‖
def LowerFlipConj : Prop :=
  ∀ F ∈ finCombIn upperHalf, ∀ c : ℝ, 0 ≤ c →
    (EuclidMotion.transl ((-c) • timeVec)).actFree (flipConj F) =
      flipConj (raise c F)
end TensorTranslation
open TensorTranslation in
def TensorTranslation.AllFacts : Prop :=
  ∀ (m : SharpScale) (S : ConnFamily) (σ : EuclidFunctionalWithRecon m S),
    TensorsAboveHeight σ ∧ TranslateSepTensors S ∧ RaiseBijIsometric σ ∧ LowerFlipConj
end YangMills.Construction.EuclideanFunctionals
