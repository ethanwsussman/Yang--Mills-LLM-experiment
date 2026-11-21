import YangMills.Construction.ReflectionPositivity.CrossingWeightExpansion
import Mathlib
set_option autoImplicit false
open scoped ComplexConjugate
noncomputable section
namespace YangMills.Construction
open Matrices
namespace ReflectionPositivity.CrossingWeight
abbrev EntryLabel : Type := Fin 2 × Fin 2 × Bool
def entryValue (l : EntryLabel) (g : ComplexMatrix2.specialUnitary) : ℂ :=
  if l.2.2 then (g : ComplexMatrix2) l.1 l.2.1 else conj ((g : ComplexMatrix2) l.1 l.2.1)
abbrev EntryLabelSequence : Type := Σ k : ℕ, (Fin k → EntryLabel)
def wordMonomial (w : EntryLabelSequence) (g : ComplexMatrix2.specialUnitary) : ℂ :=
  ∏ i, entryValue (w.2 i) g
def wordCoeff (b : ℝ) (w : EntryLabelSequence) : ℝ := (b / 4) ^ w.1 / (w.1.factorial : ℝ)
def wordSummand (b : ℝ) (w : EntryLabelSequence)
    (x : ComplexMatrix2.specialUnitary × ComplexMatrix2.specialUnitary) : ℂ :=
  (wordCoeff b w : ℂ) * wordMonomial w x.1 * conj (wordMonomial w x.2)
def wordFamily (b : ℝ) : CharacterFamily where
  index := EntryLabelSequence
  countable := inferInstance
  coeff := wordCoeff b
  fn := wordMonomial
theorem continuous_entryValue (l : EntryLabel) : Continuous (entryValue l) := by
  have h : Continuous fun g : ComplexMatrix2.specialUnitary => (g : ComplexMatrix2) l.1 l.2.1 :=
    Continuous.matrix_elem continuous_subtype_val _ _
  rcases l with ⟨i, j, _ | _⟩
  · have e : entryValue (i, j, false) =
        fun g : ComplexMatrix2.specialUnitary => conj ((g : ComplexMatrix2) i j) := by
      funext g
      simp [entryValue]
    rw [e]
    exact Complex.continuous_conj.comp h
  · have e : entryValue (i, j, true) =
        fun g : ComplexMatrix2.specialUnitary => (g : ComplexMatrix2) i j := by
      funext g
      simp [entryValue]
    rw [e]
    exact h
theorem norm_entryValue_le (l : EntryLabel) (g : ComplexMatrix2.specialUnitary) :
    ‖entryValue l g‖ ≤ 1 := by
  have h : ‖(g : ComplexMatrix2) l.1 l.2.1‖ ≤ 1 :=
    entry_norm_bound_of_unitary (Matrix.mem_specialUnitaryGroup_iff.mp g.2).1 _ _
  rcases l with ⟨i, j, _ | _⟩
  · simpa [entryValue] using h
  · simpa [entryValue] using h
theorem continuous_wordMonomial (w : EntryLabelSequence) : Continuous (wordMonomial w) :=
  continuous_finsetProd _ fun i _ => continuous_entryValue (w.2 i)
theorem norm_wordMonomial_le (w : EntryLabelSequence) (g : ComplexMatrix2.specialUnitary) :
    ‖wordMonomial w g‖ ≤ 1 := by
  rw [wordMonomial, norm_prod]
  exact Finset.prod_le_one (fun _ _ => norm_nonneg _) fun i _ => norm_entryValue_le (w.2 i) g
theorem wordCoeff_nonneg {b : ℝ} (hb : 0 ≤ b) (w : EntryLabelSequence) : 0 ≤ wordCoeff b w := by
  unfold wordCoeff
  positivity
theorem hasSum_wordCoeff_length (b : ℝ) (k : ℕ) :
    HasSum (fun t : Fin k → EntryLabel => wordCoeff b ⟨k, t⟩)
      ((2 * b) ^ k / (k.factorial : ℝ)) := by
  convert hasSum_fintype (fun t : Fin k → EntryLabel => wordCoeff b ⟨k, t⟩) using 1
  have card : Fintype.card (Fin k → EntryLabel) = 8 ^ k := by simp
  have two : 2 * b = 8 * (b / 4) := by ring
  simp only [wordCoeff, Finset.sum_const, Finset.card_univ, card, nsmul_eq_mul]
  rw [two, mul_pow]
  push_cast
  ring
theorem hasSum_wordCoeff {b : ℝ} (hb : 0 ≤ b) :
    HasSum (wordCoeff b) (Real.exp (2 * b)) := by
  have total : HasSum (fun k : ℕ => (2 * b) ^ k / (k.factorial : ℝ)) (Real.exp (2 * b)) := by
    rw [Real.exp_eq_exp_ℝ]
    exact NormedSpace.expSeries_div_hasSum_exp (2 * b)
  have summable : Summable (wordCoeff b) := by
    refine (summable_sigma_of_nonneg (wordCoeff_nonneg hb)).mpr
      ⟨fun k => (hasSum_wordCoeff_length b k).summable, ?_⟩
    simpa only [fun k => (hasSum_wordCoeff_length b k).tsum_eq] using total.summable
  exact total.sigma_of_hasSum (hasSum_wordCoeff_length b) summable
theorem norm_wordSummand_le {b : ℝ} (hb : 0 ≤ b) (w : EntryLabelSequence)
    (x : ComplexMatrix2.specialUnitary × ComplexMatrix2.specialUnitary) :
    ‖wordSummand b w x‖ ≤ wordCoeff b w := by
  have hc := wordCoeff_nonneg hb w
  rw [wordSummand, norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg hc,
    RCLike.norm_conj]
  have h₁ := norm_wordMonomial_le w x.1
  have h₂ := norm_wordMonomial_le w x.2
  calc wordCoeff b w * ‖wordMonomial w x.1‖ * ‖wordMonomial w x.2‖
      ≤ wordCoeff b w * 1 * 1 := by gcongr
    _ = wordCoeff b w := by ring
theorem sum_entryValue_mul_conj (g h : ComplexMatrix2.specialUnitary) :
    ∑ l : EntryLabel, entryValue l g * conj (entryValue l h) =
      ((2 * (ComplexMatrix2.fullTrace
        ((g * h⁻¹ : ComplexMatrix2.specialUnitary) : ComplexMatrix2)).re : ℝ) : ℂ) := by
  have hmul : ((g * h⁻¹ : ComplexMatrix2.specialUnitary) : ComplexMatrix2) =
      (g : ComplexMatrix2) * star (h : ComplexMatrix2) := rfl
  have htr : ComplexMatrix2.fullTrace ((g * h⁻¹ : ComplexMatrix2.specialUnitary) : ComplexMatrix2) =
      ∑ i, ∑ j, (g : ComplexMatrix2) i j * conj ((h : ComplexMatrix2) i j) := by
    rw [hmul]
    simp [ComplexMatrix2.fullTrace, Matrix.trace, Matrix.mul_apply, Matrix.star_apply]
  have hsum : ∑ l : EntryLabel, entryValue l g * conj (entryValue l h) =
      ComplexMatrix2.fullTrace ((g * h⁻¹ : ComplexMatrix2.specialUnitary) : ComplexMatrix2) +
        conj (ComplexMatrix2.fullTrace
          ((g * h⁻¹ : ComplexMatrix2.specialUnitary) : ComplexMatrix2)) := by
    rw [htr]
    simp [Fintype.sum_prod_type, entryValue, Fin.sum_univ_two]
    ring
  rw [hsum, Complex.add_conj]
theorem hasSum_wordSummand_length (b : ℝ) (k : ℕ)
    (x : ComplexMatrix2.specialUnitary × ComplexMatrix2.specialUnitary) :
    HasSum (fun t : Fin k → EntryLabel => wordSummand b ⟨k, t⟩ x)
      (((b / 2 * (ComplexMatrix2.fullTrace
        ((x.1 * x.2⁻¹ : ComplexMatrix2.specialUnitary) : ComplexMatrix2)).re : ℝ) : ℂ) ^ k /
        (k.factorial : ℂ)) := by
  convert hasSum_fintype (fun t : Fin k → EntryLabel => wordSummand b ⟨k, t⟩ x) using 1
  have split : ∀ t : Fin k → EntryLabel, wordSummand b ⟨k, t⟩ x =
      ((b / 4 : ℂ) ^ k / (k.factorial : ℂ)) *
        ∏ i, (entryValue (t i) x.1 * conj (entryValue (t i) x.2)) := by
    intro t
    simp only [wordSummand, wordCoeff, wordMonomial, map_prod, Finset.prod_mul_distrib]
    push_cast
    ring
  simp only [split]
  rw [← Finset.mul_sum,
    ← Fintype.sum_pow (fun l : EntryLabel => entryValue l x.1 * conj (entryValue l x.2)) k,
    sum_entryValue_mul_conj]
  generalize (ComplexMatrix2.fullTrace
    ((x.1 * x.2⁻¹ : ComplexMatrix2.specialUnitary) : ComplexMatrix2)).re = r
  have exponent : ((b / 2 * r : ℝ) : ℂ) = (b / 4 : ℂ) * ((2 * r : ℝ) : ℂ) := by
    push_cast
    ring
  rw [exponent, mul_pow]
  ring
theorem summable_norm_wordSummand {b : ℝ} (hb : 0 ≤ b)
    (x : ComplexMatrix2.specialUnitary × ComplexMatrix2.specialUnitary) :
    Summable fun w => ‖wordSummand b w x‖ :=
  Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun w => norm_wordSummand_le hb w x)
    (hasSum_wordCoeff hb).summable
theorem hasSum_wordSummand {b : ℝ} (hb : 0 ≤ b)
    (x : ComplexMatrix2.specialUnitary × ComplexMatrix2.specialUnitary) :
    HasSum (fun w => wordSummand b w x) (weightAt b x) := by
  have total := NormedSpace.expSeries_div_hasSum_exp
    ((b / 2 * (ComplexMatrix2.fullTrace
      ((x.1 * x.2⁻¹ : ComplexMatrix2.specialUnitary) : ComplexMatrix2)).re : ℝ) : ℂ)
  have value : NormedSpace.exp
      ((b / 2 * (ComplexMatrix2.fullTrace
        ((x.1 * x.2⁻¹ : ComplexMatrix2.specialUnitary) : ComplexMatrix2)).re : ℝ) : ℂ) =
      weightAt b x := by
    rw [← Complex.exp_eq_exp_ℂ, weightAt, Complex.ofReal_exp]
  rw [value] at total
  exact total.sigma_of_hasSum (fun k => hasSum_wordSummand_length b k x)
    (summable_norm_wordSummand hb x).of_norm
theorem hasSumUniformlyOn_wordSummand {b : ℝ} (hb : 0 ≤ b) :
    HasSumUniformlyOn (wordSummand b) (weightAt b) Set.univ := by
  rw [hasSumUniformlyOn_iff_tendstoUniformlyOn]
  have uniform := tendstoUniformlyOn_tsum (s := Set.univ) (hasSum_wordCoeff hb).summable
    (fun w x _ => norm_wordSummand_le hb w x)
  have value : (fun x => ∑' w, wordSummand b w x) = weightAt b :=
    funext fun x => (hasSum_wordSummand hb x).tsum_eq
  rwa [value] at uniform
theorem wordFamily_expands {b : ℝ} (hb : 0 ≤ b) : (wordFamily b).Expands b :=
  ⟨wordCoeff_nonneg hb, hasSum_wordCoeff hb, continuous_wordMonomial,
    norm_wordMonomial_le, hasSum_wordSummand hb, summable_norm_wordSummand hb,
    hasSumUniformlyOn_wordSummand hb⟩
theorem positiveTypeStatement_holds : PositiveTypeStatement := fun b hb =>
  Classical.epsilon_spec (p := fun E : CharacterFamily => E.Expands b)
    ⟨wordFamily b, wordFamily_expands hb⟩
end ReflectionPositivity.CrossingWeight
end YangMills.Construction
end
