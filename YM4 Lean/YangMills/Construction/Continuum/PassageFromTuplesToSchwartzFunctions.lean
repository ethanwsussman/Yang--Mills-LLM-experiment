import YangMills.Construction.Continuum.EuclideanMotionsAndOperationsOnFunctionsAndTuples
import YangMills.Construction.Continuum.FunctionalsOnSeparatedTuples
import YangMills.Construction.Continuum.OpenHalvesAndFlatnessOutsideAnOpenSet
import YangMills.Construction.Continuum.TensorProductsAndIntegrationOverArguments
import Mathlib
set_option autoImplicit false
open scoped ComplexConjugate ENNReal
noncomputable section
namespace YangMills.Construction.TestSpaces
def IsBoundedExtensionFamily (S : SepTuple → ℝ)
    (L : (n : ℕ) → flatSchwartzSet n → ℂ) (m : ℕ → ℕ) (C : ℕ → ℝ) : Prop :=
  (∀ f : flatSchwartzSet 0, L 0 f = f.1 fun i => i.elim0) ∧
    ∀ n, 1 ≤ n → IsCLinearOnFlat (L n) ∧ 0 < m n ∧ 0 ≤ C n ∧
      (∀ f : flatSchwartzSet n,
        ENNReal.ofReal ‖L n f‖ ≤ ENNReal.ofReal (C n) * weightedSeminorm (m n) f.1) ∧
      ∀ F : SepTupleOfCard n, HasSmoothComponents Set.univ F.1 →
        ∀ hF : tensorProdComplex F.1 ∈ flatSchwartzSet n, L n ⟨_, hF⟩ = S ⟨n, F⟩
def SepTupleInvariant (S : SepTuple → ℝ) (n : ℕ) (g : Motions.RigidMotion) : Prop :=
  ∀ F G : SepTupleOfCard n, HasSmoothComponents Set.univ F.1 → G.1 = Motions.actOnTuple g F.1 →
    S ⟨n, G⟩ = S ⟨n, F⟩
def SepTupleSymmetric (S : SepTuple → ℝ) (n : ℕ) : Prop :=
  ∀ (π : Equiv.Perm (Fin n)) (F G : SepTupleOfCard n), HasSmoothComponents Set.univ F.1 →
    (G.1 = fun i => F.1 (π i)) → S ⟨n, G⟩ = S ⟨n, F⟩
abbrev UpperSepTuple : Type := Σ q, disjointSupportTuples upperHalfSpace q
def SepTupleReflectionPositive (S : SepTuple → ℝ) : Prop :=
  ∀ (ι : Type) [Fintype ι] (a : ι → ℂ) (F : ι → UpperSepTuple)
    (G : ∀ i j, SepTupleOfCard ((F i).1 + (F j).1)),
    (∀ i, HasSmoothComponents upperHalfSpace (F i).2.1) →
    (∀ i j, (G i j).1 = Motions.concatTuple (Motions.reflectTuple (F i).2.1) (F j).2.1) →
    (∑ i, ∑ j, conj (a i) * a j * (S ⟨_, G i j⟩ : ℂ)).im = 0 ∧
      0 ≤ (∑ i, ∑ j, conj (a i) * a j * (S ⟨_, G i j⟩ : ℂ)).re
def IsPositiveTimeFlatFamily (N : ℕ) (f : (q : ℕ) → PointTuple q → ℂ) : Prop :=
  ∀ q, 1 ≤ q → q ≤ N → f q ∈ schwartzSet q ∧ VanishesToInfiniteOrderOff (f q) (positiveTimeLocus q)
def SchwingerPropertiesTransfer : Prop :=
  ∀ (S : SepTuple → ℝ) (L : (n : ℕ) → flatSchwartzSet n → ℂ) (m : ℕ → ℕ) (C : ℕ → ℝ),
    IsSepFunctional S → IsBoundedExtensionFamily S L m C →
    IsSchwingerFamily S L ∧
    (∀ n, 1 ≤ n → ∀ f : flatSchwartzSet n,
      (∀ g : Motions.RigidMotion, SepTupleInvariant S n g →
        ∃ hf : Motions.actOnFun g f.1 ∈ flatSchwartzSet n, L n ⟨_, hf⟩ = L n f) ∧
      (SepTupleSymmetric S n → ∀ π : Equiv.Perm (Fin n),
        ∃ hf : Motions.permuteArgs π f.1 ∈ flatSchwartzSet n, L n ⟨_, hf⟩ = L n f) ∧
      ((∀ x, (f.1 x).im = 0) → (L n f).im = 0) ∧
      (∃ hf : (fun x => conj (f.1 x)) ∈ flatSchwartzSet n, L n ⟨_, hf⟩ = conj (L n f)) ∧
      (SepTupleInvariant S n Motions.RigidMotion.timeReflection →
        ∃ hf : Motions.reflectConj f.1 ∈ flatSchwartzSet n, L n ⟨_, hf⟩ = conj (L n f))) ∧
    (SepTupleReflectionPositive S →
      ∀ (N : ℕ) (f : (q : ℕ) → PointTuple q → ℂ), 1 ≤ N → IsPositiveTimeFlatFamily N f →
        ∃ hf : ∀ q q' : Fin (N + 1), tensorFun (Motions.reflectConj (f q)) (f q') ∈
            flatSchwartzSet ((q : ℕ) + q'),
          (∑ q : Fin (N + 1), ∑ q' : Fin (N + 1), L ((q : ℕ) + q') ⟨_, hf q q'⟩).im = 0 ∧
            0 ≤ (∑ q : Fin (N + 1), ∑ q' : Fin (N + 1), L ((q : ℕ) + q') ⟨_, hf q q'⟩).re)
end YangMills.Construction.TestSpaces
