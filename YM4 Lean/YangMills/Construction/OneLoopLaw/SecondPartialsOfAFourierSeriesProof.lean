import YangMills.Construction.Dirichlet.CrossingChainSumEstimate
import YangMills.Construction.DirichletOperator.SumOverTheCellsOfACubeProof
import YangMills.Construction.OneLoopLaw.SecondPartialsOfAFourierSeries
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.OneLoopLaw.FourierSecondDerivatives
open YangMills.Construction.PeriodicOperators
open YangMills.Construction.OneLoopLaw.TemperedStiffness
open YangMills.Construction.TorusMetric (l1NormVec)
private theorem summable_exp_neg_mul_abs_int {a : ℝ} (ha : 0 < a) :
    Summable fun k : ℤ => Real.exp (-a * |(k : ℝ)|) := by apply _root_.YangMills.Construction.Dirichlet.ChainSumEstimate.summable_exp_neg_mul_abs <;> assumption
private theorem summable_prod_apply_pi {f : ℤ → ℝ} (hf : Summable f) (hf0 : ∀ k, 0 ≤ f k) (n : ℕ) :
    Summable fun v : Fin n → ℤ => ∏ i, f (v i) := by apply _root_.YangMills.Construction.PartitionCubes.CellCount.summable_pi_prod <;> assumption
private theorem exp_neg_mul_l1NormVec (a : ℝ) (v : Fin 4 → ℤ) :
    Real.exp (-a * l1NormVec (castVec v)) = ∏ i, Real.exp (-a * |(v i : ℝ)|) := by
  rw [← Real.exp_sum, ← Finset.mul_sum]
  rfl
private theorem sq_one_add_mul_exp_le {δ x : ℝ} (hδ : 0 < δ) (hx : 0 ≤ x) :
    (1 + x) ^ 2 * Real.exp (-δ * x) ≤ (1 + 4 / δ) ^ 2 * Real.exp (-(δ / 2) * x) := by
  have hlin : 1 + x ≤ (1 + 4 / δ) * Real.exp (δ * x / 4) := by
    have hy : δ * x / 4 + 1 ≤ Real.exp (δ * x / 4) := Real.add_one_le_exp _
    have hK : 0 ≤ 1 + 4 / δ := by positivity
    have hm : (1 + 4 / δ) * (δ * x / 4 + 1) ≤ (1 + 4 / δ) * Real.exp (δ * x / 4) :=
      mul_le_mul_of_nonneg_left hy hK
    have he : (1 + 4 / δ) * (δ * x / 4 + 1) = 1 + x + (δ * x / 4 + 4 / δ) := by
      field_simp
      ring
    have hp : 0 ≤ δ * x / 4 + 4 / δ := by positivity
    linarith
  have hsq : (1 + x) ^ 2 ≤ ((1 + 4 / δ) * Real.exp (δ * x / 4)) ^ 2 :=
    pow_le_pow_left₀ (by linarith) hlin 2
  have heq : ((1 + 4 / δ) * Real.exp (δ * x / 4)) ^ 2 * Real.exp (-δ * x) =
      (1 + 4 / δ) ^ 2 * Real.exp (-(δ / 2) * x) := by
    rw [mul_pow, mul_assoc, ← Real.exp_nat_mul, ← Real.exp_add]
    congr 2
    push_cast
    ring
  calc (1 + x) ^ 2 * Real.exp (-δ * x)
      ≤ ((1 + 4 / δ) * Real.exp (δ * x / 4)) ^ 2 * Real.exp (-δ * x) :=
        mul_le_mul_of_nonneg_right hsq (Real.exp_pos _).le
    _ = _ := heq
private theorem summable_norm_mul_sq_l1 {δ C : ℝ} {a : (Fin 4 → ℤ) → ℂ} (hδ : 0 < δ)
    (ha : ∀ v, ‖a v‖ ≤ C * Real.exp (-δ * l1NormVec (castVec v))) :
    Summable fun v : Fin 4 → ℤ => ‖a v‖ * (1 + l1NormVec (castVec v)) ^ 2 := by
  have hexp : Summable fun v : Fin 4 → ℤ => Real.exp (-(δ / 2) * l1NormVec (castVec v)) := by
    have hprod := summable_prod_apply_pi (summable_exp_neg_mul_abs_int (a := δ / 2) (by positivity))
      (fun k => (Real.exp_pos _).le) 4
    exact hprod.congr fun v => (exp_neg_mul_l1NormVec (δ / 2) v).symm
  refine Summable.of_nonneg_of_le (fun v => by positivity) (fun v => ?_)
    (hexp.mul_left (|C| * (1 + 4 / δ) ^ 2))
  have hx : 0 ≤ l1NormVec (castVec v) := Finset.sum_nonneg fun i _ => abs_nonneg _
  have hav : ‖a v‖ ≤ |C| * Real.exp (-δ * l1NormVec (castVec v)) :=
    (ha v).trans (mul_le_mul_of_nonneg_right (le_abs_self C) (Real.exp_pos _).le)
  calc ‖a v‖ * (1 + l1NormVec (castVec v)) ^ 2
      ≤ |C| * Real.exp (-δ * l1NormVec (castVec v)) * (1 + l1NormVec (castVec v)) ^ 2 :=
        mul_le_mul_of_nonneg_right hav (by positivity)
    _ = |C| * ((1 + l1NormVec (castVec v)) ^ 2 * Real.exp (-δ * l1NormVec (castVec v))) := by
        ring
    _ ≤ |C| * ((1 + 4 / δ) ^ 2 * Real.exp (-(δ / 2) * l1NormVec (castVec v))) :=
        mul_le_mul_of_nonneg_left (sq_one_add_mul_exp_le hδ hx) (abs_nonneg _)
    _ = _ := by ring
private theorem abs_apply_le_l1NormVec (v : Fin 4 → ℤ) (i : Fin 4) :
    |(v i : ℝ)| ≤ l1NormVec (castVec v) :=
  Finset.single_le_sum (f := fun j => |castVec v j|) (fun _ _ => abs_nonneg _) (Finset.mem_univ i)
private theorem hasDerivAt_mul_cexp_neg_I (a b w : ℂ) (t : ℝ) :
    HasDerivAt (fun t : ℝ => a * Complex.exp (-(Complex.I * (b + t * w))))
      (a * (Complex.exp (-(Complex.I * (b + t * w))) * (-(Complex.I * w)))) t := by
  have hid : HasDerivAt (fun t : ℝ => (t : ℂ)) 1 t := (hasDerivAt_id t).ofReal_comp
  have hall := (((hid.mul_const w).const_add b).const_mul Complex.I).neg.cexp.const_mul a
  exact hall.congr_deriv (by simp)
private theorem norm_cexp_neg_I_mul_real_add (x y : ℝ) :
    ‖Complex.exp (-(Complex.I * ((x : ℂ) + (y : ℂ))))‖ = 1 := by
  have h : -(Complex.I * ((x : ℂ) + (y : ℂ))) = ((-(x + y) : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  rw [h, Complex.norm_exp_ofReal_mul_I]
private theorem bilinDot_single_add_single (i j : Fin 4) (s t : ℝ) (v : Fin 4 → ℤ) :
    bilinDot (toComplexVec (Pi.single i s + Pi.single j t)) (toComplexVec (castVec v)) =
      (s : ℂ) * ((v i : ℝ) : ℂ) + (t : ℂ) * ((v j : ℝ) : ℂ) := by
  simp [bilinDot, toComplexVec, castVec, Pi.single_apply, add_mul, Finset.sum_add_distrib,
    apply_ite Complex.ofReal, ite_mul]
theorem termwiseSecondDerivativeClaim_holds : TermwiseSecondDerivativeClaim := by
  intro δ C a g hδ ha hg i j
  have hW := summable_norm_mul_sq_l1 hδ ha
  have hN : ∀ v : Fin 4 → ℤ, 0 ≤ l1NormVec (castVec v) := fun v =>
    Finset.sum_nonneg fun k _ => abs_nonneg _
  have hplane : ∀ s t : ℝ, HasSum (fun v : Fin 4 → ℤ => a v *
      Complex.exp (-(Complex.I * ((s : ℂ) * ((v i : ℝ) : ℂ) + (t : ℂ) * ((v j : ℝ) : ℂ)))))
      (g (toComplexVec (Pi.single i s + Pi.single j t))) := fun s t => by
    have h := hg (Pi.single i s + Pi.single j t)
    simpa only [bilinDot_single_add_single] using h
  have hfirst : ∀ s : ℝ,
      deriv (fun t : ℝ => g (toComplexVec (Pi.single i s + Pi.single j t))) 0 =
        ∑' v : Fin 4 → ℤ, (a v * (-(Complex.I * ((v j : ℝ) : ℂ)))) *
          Complex.exp (-(Complex.I * (0 + (s : ℂ) * ((v i : ℝ) : ℂ)))) := by
    intro s
    have hfun : (fun t : ℝ => g (toComplexVec (Pi.single i s + Pi.single j t))) =
        fun t : ℝ => ∑' v : Fin 4 → ℤ, a v *
          Complex.exp (-(Complex.I * ((s : ℂ) * ((v i : ℝ) : ℂ) + (t : ℂ) * ((v j : ℝ) : ℂ)))) := by
      funext t
      exact (hplane s t).tsum_eq.symm
    have hd := hasDerivAt_tsum (𝕜 := ℝ) (y₀ := 0) hW
      (g := fun (v : Fin 4 → ℤ) (t : ℝ) => a v *
        Complex.exp (-(Complex.I * ((s : ℂ) * ((v i : ℝ) : ℂ) + (t : ℂ) * ((v j : ℝ) : ℂ)))))
      (g' := fun (v : Fin 4 → ℤ) (t : ℝ) => a v *
        (Complex.exp (-(Complex.I * ((s : ℂ) * ((v i : ℝ) : ℂ) + (t : ℂ) * ((v j : ℝ) : ℂ)))) *
          (-(Complex.I * ((v j : ℝ) : ℂ)))))
      (fun v t => hasDerivAt_mul_cexp_neg_I _ _ _ t)
      (fun v t => by
        have hph := norm_cexp_neg_I_mul_real_add (s * (v i : ℝ)) (t * (v j : ℝ))
        push_cast at hph ⊢
        rw [norm_mul, norm_mul, hph, one_mul, norm_neg, norm_mul, Complex.norm_I, one_mul,
          Complex.norm_intCast]
        refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
        have h1 := abs_apply_le_l1NormVec v j
        have h2 := hN v
        nlinarith)
      (hplane s 0).summable 0
    rw [hfun, hd.deriv]
    refine tsum_congr fun v => ?_
    simp only [Complex.ofReal_zero, zero_mul, add_zero, zero_add]
    ring
  have hsecondDeriv := hasDerivAt_tsum (𝕜 := ℝ) (y₀ := 0) hW
    (g := fun (v : Fin 4 → ℤ) (s : ℝ) => (a v * (-(Complex.I * ((v j : ℝ) : ℂ)))) *
      Complex.exp (-(Complex.I * (0 + (s : ℂ) * ((v i : ℝ) : ℂ)))))
    (g' := fun (v : Fin 4 → ℤ) (s : ℝ) => (a v * (-(Complex.I * ((v j : ℝ) : ℂ)))) *
      (Complex.exp (-(Complex.I * (0 + (s : ℂ) * ((v i : ℝ) : ℂ)))) *
        (-(Complex.I * ((v i : ℝ) : ℂ)))))
    (fun v s => hasDerivAt_mul_cexp_neg_I _ _ _ s)
    (fun v s => by
      have hph := norm_cexp_neg_I_mul_real_add 0 (s * (v i : ℝ))
      push_cast at hph ⊢
      rw [norm_mul, norm_mul, norm_mul, hph, one_mul, norm_neg, norm_neg, norm_mul, norm_mul,
        Complex.norm_I, one_mul, one_mul, Complex.norm_intCast, Complex.norm_intCast, mul_assoc]
      refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
      have h1 := abs_apply_le_l1NormVec v j
      have h2 := abs_apply_le_l1NormVec v i
      have h3 := hN v
      have h4 : |(v j : ℝ)| * |(v i : ℝ)| ≤ l1NormVec (castVec v) * l1NormVec (castVec v) :=
        mul_le_mul h1 h2 (abs_nonneg _) h3
      nlinarith)
    (by
      refine Summable.of_norm_bounded hW fun v => ?_
      have hph := norm_cexp_neg_I_mul_real_add 0 (0 * (v i : ℝ))
      push_cast at hph ⊢
      rw [norm_mul, norm_mul, hph, mul_one, norm_neg, norm_mul, Complex.norm_I, one_mul,
        Complex.norm_intCast]
      refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
      have h1 := abs_apply_le_l1NormVec v j
      have h2 := hN v
      nlinarith) 0
  have hsecond : secondPartialAtZero g i j = ∑' v : Fin 4 → ℤ,
      -(a v * ((v i : ℤ) : ℂ) * ((v j : ℤ) : ℂ)) := by
    have hfun : (fun s : ℝ => deriv (fun t : ℝ =>
        g (toComplexVec (Pi.single i s + Pi.single j t))) 0) = fun s : ℝ =>
        ∑' v : Fin 4 → ℤ, (a v * (-(Complex.I * ((v j : ℝ) : ℂ)))) *
          Complex.exp (-(Complex.I * (0 + (s : ℂ) * ((v i : ℝ) : ℂ)))) := funext hfirst
    rw [secondPartialAtZero, hfun, hsecondDeriv.deriv]
    refine tsum_congr fun v => ?_
    have hI : Complex.I * Complex.I = -1 := Complex.I_mul_I
    simp only [Complex.ofReal_zero, zero_mul, add_zero, mul_zero, neg_zero, Complex.exp_zero,
      one_mul, Complex.ofReal_intCast]
    linear_combination (a v * ((v i : ℤ) : ℂ) * ((v j : ℤ) : ℂ)) * hI
  have hsum : Summable fun v : Fin 4 → ℤ => a v * ((v i : ℤ) : ℂ) * ((v j : ℤ) : ℂ) := by
    refine Summable.of_norm_bounded hW fun v => ?_
    rw [norm_mul, norm_mul, Complex.norm_intCast, Complex.norm_intCast, mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    have h1 := abs_apply_le_l1NormVec v j
    have h2 := abs_apply_le_l1NormVec v i
    have h3 := hN v
    have h4 : |(v i : ℝ)| * |(v j : ℝ)| ≤ l1NormVec (castVec v) * l1NormVec (castVec v) :=
      mul_le_mul h2 h1 (abs_nonneg _) h3
    nlinarith
  rw [hsecond, tsum_neg, neg_neg]
  exact hsum.hasSum
end YangMills.Construction.OneLoopLaw.FourierSecondDerivatives
end
