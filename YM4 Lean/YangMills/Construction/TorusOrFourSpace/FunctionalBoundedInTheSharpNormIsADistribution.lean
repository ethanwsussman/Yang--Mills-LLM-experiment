import YangMills.Construction.TorusOrFourSpace.FourKindsOfMapsOfSeveralPoints
import YangMills.Construction.TorusOrFourSpace.MultilinearFormBoundedInTheC1Norms
import YangMills.Construction.TorusOrFourSpace.MultilinearFunctionalsAndSetsAtPositiveDistance
import YangMills.Construction.TorusOrFourSpace.SeparatedFamiliesOfOpenSets
import Mathlib
set_option autoImplicit false
open scoped ENNReal
noncomputable section
namespace YangMills.Construction.PeriodicSpace.Kind.Tuple
section Vocabulary
variable (P : Params) (K : Kind) {n : ℕ+}
def IsFiniteTensorSum (O : Fin (n : ℕ) → Set (K.Pt P))
    (g : K.Tuple P n → ℂ) : Prop :=
  ∃ (m : ℕ) (u : Fin m → Fin (n : ℕ) → K.Pt P → ℂ),
    (∀ l i, u l i ∈ singleTestFns P K (O i)) ∧ g = ∑ l, tensorProd P K (u l)
def EqOneNearProjections (F : K.Tuple P n → ℂ) (χ : Fin (n : ℕ) → K.Pt P → ℝ) :
    Prop :=
  ∀ i, ∃ U, Kind.IsOpenQ P K U ∧ coordProj P K i (supportT P K F) ⊆ U ∧
    ∀ y ∈ U, χ i y = 1
variable {P K}
def SharpNormBounded (c : ℝ → ℝ → ℝ) (Ψ : sepC1Tuples P K (n : ℕ) → ℝ) : Prop :=
  ∀ d R : ℝ, 0 < d → R ∈ allowedRadii P K → ∀ f : sepC1Tuples P K (n : ℕ),
    f.1 ∈ lipTuplesSpacedInBalls P K (n : ℕ) d R →
      ENNReal.ofReal |Ψ f| ≤ ENNReal.ofReal (c d R) * ∏ i, sharpNormQ P K (f.1 i)
def IsFamilyDistrib (Ψ : sepC1Tuples P K (n : ℕ) → ℝ)
    (G : Fin (n : ℕ) → Set (K.Pt P)) (T : testFns P K (boxSet P K G) → ℂ) : Prop :=
  IsDistrib T ∧ ∀ φ : Fin (n : ℕ) → K.Pt P → ℝ,
    (∀ i, (fun y => (φ i y : ℂ)) ∈ singleTestFns P K (G i)) →
      ∃ (hφ : φ ∈ sepC1Tuples P K (n : ℕ))
        (hF : tensorProd P K (fun i y => (φ i y : ℂ)) ∈ testFns P K (boxSet P K G)),
        T ⟨_, hF⟩ = ((Ψ ⟨φ, hφ⟩ : ℝ) : ℂ)
def RestrictsToFamilyDistribs (Ψ : sepC1Tuples P K (n : ℕ) → ℝ)
    (T : testFns P K (pairwiseDistinct P K n) → ℂ) : Prop :=
  IsDistrib T ∧ ∀ G : Fin (n : ℕ) → Set (K.Pt P), IsSeparated P K G →
    ∃ h : boxSet P K G ⊆ pairwiseDistinct P K n,
      IsFamilyDistrib Ψ G (restrictDistrib h T)
def AgreesOnSmoothTensors (Ψ : sepC1Tuples P K (n : ℕ) → ℝ)
    (T : testFns P K (pairwiseDistinct P K n) → ℂ) : Prop :=
  ∀ (f : Fin (n : ℕ) → K.Pt P → ℝ) (hf : f ∈ sepC1Tuples P K (n : ℕ)),
    (∀ i, Kind.IsSmoothFn P K (f i)) →
      ∃ hF : tensorProd P K (fun i y => (f i y : ℂ)) ∈ testFns P K (pairwiseDistinct P K n),
        T ⟨_, hF⟩ = ((Ψ ⟨f, hf⟩ : ℝ) : ℂ)
def SeparatedFamilyDistribSpec (c : ℝ → ℝ → ℝ) (Ψ : sepC1Tuples P K (n : ℕ) → ℝ)
    (R d : ℝ) (G : Fin (n : ℕ) → Set (K.Pt P)) : Prop :=
  (∃! T, IsFamilyDistrib Ψ G T) ∧
  (∀ F : testFns P K (boxSet P K G),
    ∃ Fs : ℕ+ → testFns P K (boxSet P K G),
      (∀ t, IsFiniteTensorSum P K G (Fs t).1) ∧
        TendstoInTestFns Fs F) ∧
  ((∀ i, (G i).Nonempty) →
    maxMemberDiam P K G ≠ ∞ ∧ (maxMemberDiam P K G).toReal ∈ allowedRadii P K) ∧
  ((∃ i, G i = ∅) → testFns P K (boxSet P K G) = {0}) ∧
  ∀ T, IsFamilyDistrib Ψ G T →
    IsDistribOfOrderLE (5 * (n : ℕ) + 1) T ∧
    ((∀ i, (G i).Nonempty) → ∀ χ, IsCutoffFamily P K G χ →
      ∀ F : testFns P K (boxSet P K G), EqOneNearProjections P K F.1 χ →
        ENNReal.ofReal ‖T F‖ ≤
          ENNReal.ofReal ((160 * P.M) ^ (n : ℕ) * c d (maxMemberDiam P K G).toReal *
              cutoffBound n (2 * R)) *
            (∏ i, c1NormSingleReal P K (χ i)) *
              cNorm P K (5 * (n : ℕ) + 1) F.1) ∧
    ((∃ i, G i = ∅) → ∀ F, T F = 0)
end Vocabulary
namespace SharpBoundedIsDistrib
def Statement : Prop :=
  ∀ (P : Params) (K : Kind) (n : ℕ+), 2 ≤ (n : ℕ) →
    ∀ (Ψ : sepC1Tuples P K (n : ℕ) → ℝ) (c : ℝ → ℝ → ℝ),
      IsMultilinearOn P K (sepC1Tuples P K (n : ℕ)) Ψ →
      (∀ d R : ℝ, 0 < d → R ∈ allowedRadii P K → 0 ≤ c d R) →
      SharpNormBounded c Ψ →
      (∀ (R d : ℝ) (G : Fin (n : ℕ) → Set (K.Pt P)), IsSeparatedWith P K R d G →
        SeparatedFamilyDistribSpec c Ψ R d G) ∧
      IsOpenT P K (pairwiseDistinct P K n) ∧
      (∀ G : Fin (n : ℕ) → Set (K.Pt P), IsSeparated P K G →
        IsOpenT P K (boxSet P K G) ∧ boxSet P K G ⊆ pairwiseDistinct P K n) ∧
      (∃! T, RestrictsToFamilyDistribs Ψ T) ∧
      ∀ T, RestrictsToFamilyDistribs Ψ T →
        IsDistribOfOrderLE (5 * (n : ℕ) + 1) T ∧
        AgreesOnSmoothTensors Ψ T ∧
        (∀ T', IsDistrib T' → AgreesOnSmoothTensors Ψ T' → T' = T) ∧
        ∀ ψ : ExtendedTupleMap P K n, ψ.InvariantFunctional Ψ → ψ.InvariantDistrib T
end SharpBoundedIsDistrib
end YangMills.Construction.PeriodicSpace.Kind.Tuple
