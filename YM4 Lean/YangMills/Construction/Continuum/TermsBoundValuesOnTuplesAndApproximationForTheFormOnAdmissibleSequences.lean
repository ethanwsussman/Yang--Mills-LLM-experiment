import YangMills.Construction.Continuum.FormIsSesquilinearAndPositiveSemiDefinite
import YangMills.Construction.Continuum.ReflectionPositivityOfASequenceWithTheValuesOfAFunctional
import YangMills.Construction.Continuum.SequenceOfACombinationIsAdmissibleAndLinear
import YangMills.Construction.Continuum.TestSpacesAndNormsOfTheAxiomsOnSchwartzFunctions
import YangMills.Construction.Continuum.VectorSpaceOfAdmissibleSequences
import Mathlib
set_option autoImplicit false
open scoped ComplexConjugate ENNReal
noncomputable section
namespace YangMills.Construction.AdmissibleForm
open YangMills.Construction.ConfigSpace
open YangMills.Construction.ConfigSpace.UpperCombination (linComb)
open YangMills.Construction.ReflectionPositivityFromValues (AgreesOnTensors)
open YangMills.Construction.SchwartzAxioms (seminormAt)
structure HasGrowthBound (S : FlatSequence) (a : ℕ → ℝ) (kE : ℕ) : Prop where
  isCLMSequence : IsCLMSequence S
  one_le : 1 ≤ kE
  coeff_zero : a 0 = 1
  coeff_nonneg : ∀ n, 0 ≤ a n
  bound : ∀ (m : ℕ) (f : schwartzFlatOffDiagonal (m + 1)),
    ‖S.atSucc m f‖ ≤ a (m + 1) * bracketNorm (kE * (m + 1)) (toSchwartzFn f)
def TermEstimate (S : FlatSequence) (a : ℕ → ℝ) (kE : ℕ) : Prop :=
  ∀ (p p' : ℕ) (χ : flatOffPosTimeAt p) (ψ : flatOffPosTimeAt p') (k : ℕ),
    1 ≤ k → kE * (p + p') ≤ k →
      tensorAt (flipConjAt χ.1) ψ.1 ∈ flatOffDiagonalAt (p + p') ∧
        ENNReal.ofReal ‖S.evalAt (tensorAt (flipConjAt χ.1) ψ.1)‖ ≤
          ENNReal.ofReal (a (p + p')) * seminormAt k χ.1 * seminormAt k ψ.1
def FormEstimate (S : FlatSequence) (a : ℕ → ℝ) (kE : ℕ) : Prop :=
  S.IsSesquilinear ∧
    ∀ (Φ Ψ : AdmissibleSeq) (N : ℕ), 1 ≤ N →
      (∀ p, N < p → (Φ.1 p).1 = zeroOfDegree p) → (∀ p, N < p → (Ψ.1 p).1 = zeroOfDegree p) →
        ENNReal.ofReal ‖S.reflectionForm Φ Ψ‖ ≤
          ∑ p ∈ Finset.range (N + 1), ∑ p' ∈ Finset.range (N + 1),
            ENNReal.ofReal (a (p + p')) * seminormAt (2 * kE * N) (Φ.1 p).1 *
              seminormAt (2 * kE * N) (Ψ.1 p').1
def ListMatchesFamily (L : YangMills.Construction.SeparatedTuples.SepTuple) (T : UpperFamily) : Prop :=
  L.1 = List.ofFn T.2.1
def reflectedPairValue (σ : YangMills.Construction.SeparatedTuples.TupleFunctional)
    (L L' : YangMills.Construction.SeparatedTuples.SepTuple) : ℂ :=
  σ.spanExtension (YangMills.Construction.SeparatedTuples.formalMul
    (YangMills.Construction.SeparatedTuples.pushSpan YangMills.Construction.TimeAxis.timeReflection
      (YangMills.Construction.SeparatedTuples.basisVec L))
    (YangMills.Construction.SeparatedTuples.basisVec L'))
def FormOnTuples (S : FlatSequence) (σ : YangMills.Construction.SeparatedTuples.TupleFunctional) : Prop :=
  ∀ (ι κ : Type) [Fintype ι] [Fintype κ] (c : ι → ℂ) (d : κ → ℂ) (T : ι → UpperFamily) (T' : κ → UpperFamily)
    (L : ι → YangMills.Construction.SeparatedTuples.SepTuple)
    (L' : κ → YangMills.Construction.SeparatedTuples.SepTuple),
    (∀ i, AllSmoothCompact (T i).2.1) → (∀ j, AllSmoothCompact (T' j).2.1) →
      (∀ i, ListMatchesFamily (L i) (T i)) → (∀ j, ListMatchesFamily (L' j) (T' j)) →
      ∀ Φ Ψ : AdmissibleSeq,
        (∀ p, (Φ.1 p).1 = combinationSequence (linComb c T) p) →
        (∀ p, (Ψ.1 p).1 = combinationSequence (linComb d T') p) →
          S.reflectionForm Φ Ψ = ∑ i, ∑ j, conj (c i) * d j * reflectedPairValue σ (L i) (L' j) ∧
            ∀ G G' : YangMills.Construction.ReflectionPositivity.TupleForm.PositiveSpan,
              G.1 = ∑ i, c i • YangMills.Construction.SeparatedTuples.basisVec (L i) →
              G'.1 = ∑ j, d j • YangMills.Construction.SeparatedTuples.basisVec (L' j) →
                S.reflectionForm Φ Ψ = YangMills.Construction.ReflectionPositivity.TupleForm.reflectionForm σ G G'
def SmoothApproximation : Prop :=
  ∀ (Φ : AdmissibleSeq) (N : ℕ), 1 ≤ N → (∀ p, N < p → (Φ.1 p).1 = zeroOfDegree p) →
    ∀ (k : ℕ) (ε : ℝ), 1 ≤ k → 0 < ε →
      ∃ F : UpperCombination, F.HasSmoothFamilies ∧
        (∀ p, N < p → combinationSequence F p = zeroOfDegree p) ∧
        combinationSequence F 0 = (Φ.1 0).1 ∧
        ∀ p, 1 ≤ p → p ≤ N → seminormAt k ((Φ.1 p).1 - combinationSequence F p) ≤ ENNReal.ofReal ε
def Statement : Prop :=
  (∀ (S : FlatSequence) (a : ℕ → ℝ) (kE : ℕ), HasGrowthBound S a kE →
    TermEstimate S a kE ∧ FormEstimate S a kE ∧
      ∀ σ : YangMills.Construction.SeparatedTuples.TupleFunctional,
        AgreesOnTensors (fun T => σ (YangMills.Construction.TupleLists.toList T)) S → FormOnTuples S σ) ∧
    SmoothApproximation
end YangMills.Construction.AdmissibleForm
end
