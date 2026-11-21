import YangMills.Construction.RunningCouplingSlope.RateOfASymbolOnAStrip
import YangMills.Construction.Towers.SumsProductsAndTransposesOfDescendingKernelsProof
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.PeriodicOperators.StripDecay
open YangMills.Construction.TorusMetric (l1NormVec)
private def stripCorner (υ : ℝ) (e : Fin 4 → Bool) : Fin 4 → ℂ :=
  fun μ => ((if e μ then -υ else υ : ℝ) : ℂ) * Complex.I
private theorem stripCorner_mem {υ : ℝ} (h : 0 < υ) (e : Fin 4 → Bool) :
    stripCorner υ e ∈ imStrip υ := by
  intro μ
  by_cases he : e μ = true <;> simp [stripCorner, he, abs_of_pos h]
private theorem norm_exp_stripCorner (υ : ℝ) (v : Fin 4 → ℝ) :
    ‖Complex.exp (Complex.I * bilinDot (stripCorner υ fun μ => decide (0 ≤ v μ)) (toComplexVec v))‖ =
      Real.exp (υ * l1NormVec v) := by
  rw [Complex.norm_exp]
  congr 1
  simp only [bilinDot, stripCorner, toComplexVec, l1NormVec, Finset.mul_sum, Complex.re_sum]
  refine Finset.sum_congr rfl fun μ _ => ?_
  by_cases h : 0 ≤ v μ
  · have e : ((if decide (0 ≤ v μ) = true then -υ else υ : ℝ) : ℂ) = ((-υ : ℝ) : ℂ) := by simp [h]
    rw [e, abs_of_nonneg h]
    have : Complex.I * (((-υ : ℝ) : ℂ) * Complex.I * ((v μ : ℝ) : ℂ)) = ((υ * v μ : ℝ) : ℂ) := by
      push_cast
      linear_combination (-(υ : ℂ) * (v μ : ℂ)) * Complex.I_mul_I
    rw [this, Complex.ofReal_re]
  · have e : ((if decide (0 ≤ v μ) = true then -υ else υ : ℝ) : ℂ) = ((υ : ℝ) : ℂ) := by simp [h]
    rw [e, abs_of_neg (not_le.mp h)]
    have : Complex.I * (((υ : ℝ) : ℂ) * Complex.I * ((v μ : ℝ) : ℂ)) = ((υ * -v μ : ℝ) : ℂ) := by
      push_cast
      linear_combination ((υ : ℂ) * (v μ : ℂ)) * Complex.I_mul_I
    rw [this, Complex.ofReal_re]
private theorem exists_translate_of_mkQuot_eq {I : PeriodicData} (hI : IsPeriodic I) (s : ℕ)
    {ι ι' : I.Carrier} (e : I.mkQuot s ι = I.mkQuot s ι') :
    ∃ n : Fin 4 → ℤ, ι' = I.translate (s • n) ι := by apply _root_.YangMills.Construction.LocalKernels.DescendingKernels.exists_translate_of_mkQuot_eq <;> assumption
theorem decayFromStripSymbol_holds : DecayFromStripSymbol := by
  intro I I' hI hI' T υ hυ hcov hform
  have hfin : Finite I.UnitQuot := hI.finite_quot
  have hfin' : Finite I'.UnitQuot := hI'.finite_quot
  let bound : I'.Carrier → I.Carrier → ℝ := fun ι' ι =>
    ∑ e : Fin 4 → Bool, ∑' n, ‖symbolSummand I I' T (stripCorner υ e) ι' ι n‖
  have key : ∀ ι' ι (n : Fin 4 → ℤ),
      ‖T ι' (I.translate n ι)‖ * Real.exp (υ * l1NormVec (I.pos (I.translate n ι) - I'.pos ι')) ≤
        bound ι' ι := by
    intro ι' ι n
    set v := I.pos (I.translate n ι) - I'.pos ι' with hv
    set e : Fin 4 → Bool := fun μ => decide (0 ≤ v μ) with he
    have h1 : ‖symbolSummand I I' T (stripCorner υ e) ι' ι n‖ =
        ‖T ι' (I.translate n ι)‖ * Real.exp (υ * l1NormVec v) := by
      rw [symbolSummand, norm_mul, norm_exp_stripCorner υ v]
    rw [← h1]
    have h2 := (hform _ (stripCorner_mem hυ e) ι' ι).le_tsum n (fun j _ => norm_nonneg _)
    refine h2.trans ?_
    exact Finset.single_le_sum (f := fun e : Fin 4 → Bool =>
      ∑' n, ‖symbolSummand I I' T (stripCorner υ e) ι' ι n‖)
      (fun _ _ => tsum_nonneg fun _ => norm_nonneg _) (Finset.mem_univ e)
  have hrep : ∀ c : I.UnitQuot, ∃ ι, I.mkQuot 1 ι = c := fun c => Quot.exists_rep c
  have hrep' : ∀ c : I'.UnitQuot, ∃ ι, I'.mkQuot 1 ι = c := fun c => Quot.exists_rep c
  choose r hr using hrep
  choose r' hr' using hrep'
  have hbdd : BddAbove (Set.range fun p : I'.UnitQuot × I.UnitQuot => bound (r' p.1) (r p.2)) :=
    (Set.finite_range _).bddAbove
  obtain ⟨C₀, hC₀⟩ := hbdd
  refine ⟨max C₀ 1, lt_of_lt_of_le one_pos (le_max_right _ _), fun ι' ι => ?_⟩
  obtain ⟨m', hm'⟩ := exists_translate_of_mkQuot_eq hI' 1 (hr' (I'.mkQuot 1 ι'))
  obtain ⟨m, hm⟩ := exists_translate_of_mkQuot_eq hI 1 (hr (I.mkQuot 1 ι))
  simp only [one_smul] at hm hm'
  set ρ' := r' (I'.mkQuot 1 ι')
  set ρ := r (I.mkQuot 1 ι)
  have hT : T ρ' (I.translate (m - m') ρ) = T ι' ι := by
    rw [← hcov m' ρ' (I.translate (m - m') ρ), ← hI.translate_add, hm', hm]
    simp
  have hpos : I.pos (I.translate (m - m') ρ) - I'.pos ρ' = I.pos ι - I'.pos ι' := by
    rw [hm', hm, hI.pos_translate, hI.pos_translate, hI'.pos_translate]
    funext μ
    simp [castVec]
    ring
  have hk := key ρ' ρ (m - m')
  rw [hT, hpos] at hk
  have hL : l1NormVec (I.pos ι - I'.pos ι') = l1NormVec (I'.pos ι' - I.pos ι) := by
    simp only [l1NormVec, Pi.sub_apply]
    exact Finset.sum_congr rfl fun μ _ => abs_sub_comm _ _
  rw [hL] at hk
  have hB : bound ρ' ρ ≤ max C₀ 1 :=
    (hC₀ ⟨(I'.mkQuot 1 ι', I.mkQuot 1 ι), rfl⟩).trans (le_max_left _ _)
  have h3 := hk.trans hB
  rw [neg_mul, Real.exp_neg]
  rw [← div_eq_mul_inv, le_div_iff₀ (Real.exp_pos _)]
  exact h3
end YangMills.Construction.PeriodicOperators.StripDecay
end
