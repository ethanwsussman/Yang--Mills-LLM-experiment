import YangMills.Construction.Matrices.CalculusOfTheFieldsOnPowersOfG
import YangMills.Construction.Matrices.CoefficientSpacesOfSeveralVariablesArePolynomial
import YangMills.Construction.Matrices.ExpansionInThePeterWeylBasis
import YangMills.Construction.TransferOperators.ComponentFunctionsOfTheProjections
import YangMills.Construction.TransferOperators.FactsOfTheSquareRootOfTheBondKernelProof
import YangMills.Construction.TransferOperators.FieldsKeepProductCoefficientSpaces
import YangMills.Construction.TransferOperators.InverseWeightSumConverges
import YangMills.Construction.TransferOperators.RapidDecayGivesASmoothFunction
import Mathlib
set_option autoImplicit false
open MeasureTheory Filter YangMills.Construction.Matrices YangMills.Construction.Matrices.ComplexMatrix2
open scoped ENNReal
noncomputable section
namespace YangMills.Construction.SpinHarmonics
namespace SmoothFromDecay
theorem countable_halfNatural : Countable HalfNatural :=
  Function.Injective.countable (f := HalfNatural.doubled) fun a b h => by
    cases a; cases b; simp_all
variable {ι : Type} [Finite ι]
theorem toReal_nonneg (s : HalfNatural) : 0 ≤ s.toReal := by apply _root_.YangMills.Construction.TransferOperators.SqrtLinkFacts.halfNatural_toReal_nonneg <;> assumption
omit [Finite ι] in
theorem dimProd_nonneg (j : ι → HalfNatural) : 0 ≤ ∏ᶠ i, (2 * (j i).toReal + 1) :=
  finprod_nonneg fun i => by linarith [toReal_nonneg (j i)]
omit [Finite ι] in
theorem one_add_weightSum_pos (j : ι → HalfNatural) : 0 < 1 + weightSum j := by
  have h : 0 ≤ weightSum j := finsum_nonneg fun i => toReal_nonneg (j i)
  linarith
omit [Finite ι] in
theorem weightDecayTerm_nonneg (q : ℕ) (j : ι → HalfNatural) : 0 ≤ weightDecayTerm q j :=
  mul_nonneg (dimProd_nonneg j) (inv_nonneg.2 (pow_nonneg (one_add_weightSum_pos j).le q))
theorem dimProd_mul_norm_isotypicProj_le (f : HaarL2 ι) (q k : ℕ) (hf : sobolevDecay (q + k) f < ∞)
    (j : ι → HalfNatural) :
    (∏ᶠ i, (2 * (j i).toReal + 1)) * ((1 + weightSum j) ^ k * ‖isotypicProj j f‖) ≤
      weightDecayTerm q j * (sobolevDecay (q + k) f).toReal := by
  have hpos := one_add_weightSum_pos j
  have hle : (1 + weightSum j) ^ (q + k) * ‖isotypicProj j f‖ ≤
      (sobolevDecay (q + k) f).toReal :=
    (ENNReal.ofReal_le_iff_le_toReal hf.ne).1
      (le_iSup (fun j : ι → HalfNatural =>
        ENNReal.ofReal ((1 + weightSum j) ^ (q + k) * ‖isotypicProj j f‖)) j)
  have heq : (∏ᶠ i, (2 * (j i).toReal + 1)) * ((1 + weightSum j) ^ k * ‖isotypicProj j f‖) =
      weightDecayTerm q j * ((1 + weightSum j) ^ (q + k) * ‖isotypicProj j f‖) := by
    have hq : (1 + weightSum j) ^ q ≠ 0 := (pow_pos hpos q).ne'
    unfold weightDecayTerm
    rw [pow_add]
    field_simp
  rw [heq]
  exact mul_le_mul_of_nonneg_left hle (weightDecayTerm_nonneg q j)
theorem exists_continuous_fieldWord_le (hI : IsotypicPartSums.Statement)
    [Nonempty ι] (hV : FieldsPreserveProdCoeffSpan ι) (f : HaarL2 ι)
    (w : List (ι × Fin 3)) (j : ι → HalfNatural) :
    ∃ φ : C(ι → specialUnitary, ℂ), ⇑φ = fieldWord w (isotypicPart j f) ∧
      ‖φ‖ ≤ (∏ᶠ i, (2 * (j i).toReal + 1)) *
        ((1 + weightSum j) ^ w.length * ‖isotypicProj j f‖) := by
  obtain ⟨hmem, hfun, hcl⟩ := (hI ι).1 j f
  obtain ⟨h₁, -, -, h₄⟩ := hV j _ hmem
  obtain ⟨φ, hφ, he⟩ := h₁ w
  obtain ⟨-, -, h₃, -⟩ := hV j φ hφ
  refine ⟨φ, by rw [he, hfun], h₃.trans (mul_le_mul_of_nonneg_left ?_ (dimProd_nonneg j))⟩
  rw [he, ← hcl]
  exact h₄ w
end SmoothFromDecay
open SmoothFromDecay in
theorem sobolevDecayToSmooth
    (hI : IsotypicPartSums.Statement)
    (hV : FieldsPreserveIsotypicSpans.Statement)
    (hW : WeightDecaySum.Statement)
    (hS : FieldCalculus.AllRules)
    (hE : PeterWeylExpansionHolds)
    (hP : SeveralVariables.CoeffSpansArePolynomial) :
    SobolevDecayToSmoothStatement := by
  intro ι _ _ f hdecay
  have := countable_halfNatural
  have hfields := hV ι
  have hcalc := hS.2.2 ι
  have hpoly := hcalc.2.2.2.2.2.1.1
  have hseries := hcalc.2.2.2.2.2.2.2.1
  set q₀ := 2 * Nat.card ι + 1 with hq₀
  have hsum₀ : Summable (weightDecayTerm q₀ : (ι → HalfNatural) → ℝ) := (hW ι).1 q₀ le_rfl
  have hbound : ∀ (w : List (ι × Fin 3)) (q : ℕ) (j : ι → HalfNatural) (u : ι → specialUnitary),
      ‖fieldWord w (isotypicPart j f) u‖ ≤
        weightDecayTerm q j * (sobolevDecay (q + w.length) f).toReal := by
    intro w q j u
    obtain ⟨φ, he, hφ⟩ := exists_continuous_fieldWord_le hI hfields f w j
    rw [← he]
    exact ((φ.norm_coe_le_norm u).trans hφ).trans (dimProd_mul_norm_isotypicProj_le f q _ (hdecay _) j)
  have hsumw : ∀ w : List (ι × Fin 3), Summable fun j : ι → HalfNatural =>
      weightDecayTerm q₀ j * (sobolevDecay (q₀ + w.length) f).toReal :=
    fun w => hsum₀.mul_right _
  have hcomp : ∀ j, (isotypicPartSum j f : (ι → specialUnitary) → ℂ) = isotypicPart j f :=
    fun j => ((hI ι).1 j f).2.1
  refine ⟨fun w => ?_, ?_⟩
  · refine lt_of_le_of_lt (ENNReal.tsum_le_tsum fun j => ?_) (hsumw w).tsum_ofReal_lt_top
    refine iSup_le fun u => ?_
    rw [← ofReal_norm]
    exact ENNReal.ofReal_le_ofReal (hbound w q₀ j u)
  have hsumC : Summable fun j : ι → HalfNatural => isotypicPartSum j f := by
    refine Summable.of_norm_bounded (hsumw []) fun j => ?_
    refine (ContinuousMap.norm_le _ (mul_nonneg (weightDecayTerm_nonneg _ _) ENNReal.toReal_nonneg)).2 fun u => ?_
    have := hbound [] q₀ j u
    rw [hcomp]
    exact this
  set g : C(ι → specialUnitary, ℂ) := ∑' j : ι → HalfNatural, isotypicPartSum j f with hg
  have hval : ∀ u, g u = ∑' j : ι → HalfNatural, isotypicPart j f u := by
    intro u
    rw [hg, ← ContinuousMap.tsum_apply hsumC]
    exact tsum_congr fun j => congrFun (hcomp j) u
  have hsmooth : ∀ j, isotypicPart j f ∈ (smoothSet : Set ((ι → specialUnitary) → ℂ)) := by
    intro j
    rw [← hcomp]
    exact hpoly _ ((hP ι j ⟨0⟩).2.2.1 _ ((hI ι).1 j f).1)
  have hsup : ∀ w : List (ι × Fin 3), Summable fun j : ι → HalfNatural =>
      supNorm (fieldWord w (isotypicPart j f)) := by
    intro w
    refine Summable.of_nonneg_of_le (fun j => Real.iSup_nonneg fun _ => norm_nonneg _)
      (fun j => ?_) (hsumw w)
    exact ciSup_le (hbound w q₀ j)
  have hgfun : (⇑g : (ι → specialUnitary) → ℂ) = fun u => ∑' j : ι → HalfNatural, isotypicPart j f u :=
    funext hval
  refine ⟨g, ?_, ?_, ?_, fun q hq => ?_⟩
  · rw [hgfun]
    exact (hseries (ι → HalfNatural) _ hsmooth hsup).1
  · rw [hgfun]
    have h := tendstoUniformly_tsum (f := fun (j : ι → HalfNatural) (u : ι → specialUnitary) =>
      isotypicPart j f u) (hsumw []) (fun j u => hbound [] q₀ j u)
    exact h
  · have hL : HasSum (fun j : ι → HalfNatural =>
        ContinuousMap.toLp (E := ℂ) 2 (haarPi ι) ℂ (isotypicPartSum j f))
        (ContinuousMap.toLp (E := ℂ) 2 (haarPi ι) ℂ g) :=
      (ContinuousMap.toLp (E := ℂ) 2 (haarPi ι) ℂ).hasSum hsumC.hasSum
    have hclass : ∀ (v : C(ι → specialUnitary, ℂ)),
        toHaarL2 (v : (ι → specialUnitary) → ℂ) = ContinuousMap.toLp (E := ℂ) 2 (haarPi ι) ℂ v := by
      intro v
      have hae := ContinuousMap.coeFn_toLp (p := 2) (E := ℂ) (𝕜 := ℂ) (haarPi ι) v
      have hm : MemLp (v : (ι → specialUnitary) → ℂ) 2 (haarPi ι) := (Lp.memLp _).ae_eq hae
      unfold toHaarL2
      rw [dif_pos hm]
      exact Lp.ext ((hm.coeFn_toLp).trans hae.symm)
    have hproj : ∀ j, ContinuousMap.toLp (E := ℂ) 2 (haarPi ι) ℂ (isotypicPartSum j f) =
        isotypicProj j f := fun j => by
      rw [← hclass]
      exact ((hI ι).1 j f).2.2
    simp only [hproj] at hL
    have hf' := hL.unique ((hE ι f).2.1)
    rw [← hf']
    exact (ContinuousMap.coeFn_toLp (p := 2) (E := ℂ) (𝕜 := ℂ) (haarPi ι) g).symm
  · have hsumq : Summable (weightDecayTerm q : (ι → HalfNatural) → ℝ) := (hW ι).1 q hq
    have hN := hdecay q
    have hK : 0 ≤ weightDecaySum ι q := tsum_nonneg fun j => weightDecayTerm_nonneg q j
    refine iSup_le fun u => ?_
    have h₁ : ‖g u‖ ≤ weightDecaySum ι q * (sobolevDecay q f).toReal := by
      rw [hval u]
      refine tsum_of_norm_bounded (hsumq.hasSum.mul_right _) fun j => ?_
      exact hbound [] q j u
    rw [← ofReal_norm]
    refine (ENNReal.ofReal_le_ofReal h₁).trans (le_of_eq ?_)
    rw [ENNReal.ofReal_mul hK, ENNReal.ofReal_toReal hN.ne]
end YangMills.Construction.SpinHarmonics
end
