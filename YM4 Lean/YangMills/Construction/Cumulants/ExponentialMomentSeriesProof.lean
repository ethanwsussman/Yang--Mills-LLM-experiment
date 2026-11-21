import YangMills.Construction.ComplexAnalysis.HolomorphicFunctionFacts
import YangMills.Construction.Cumulants.ExponentialMomentSeries
import YangMills.Construction.Probability.ExpectationBasicProperties
import Mathlib
set_option autoImplicit false
open MeasureTheory Set
namespace YangMills.Construction.Cumulants
open YangMills.Construction.PowerSeries
open YangMills.Construction.Probability (IsBoundedRealRV IsBoundedComplexRV supModulus
  complexExpectation)
open YangMills.Construction.ComplexVariables (expComp IsEntireFun IsHolomorphicScalar absMonomial
  IsAbsSummable indexSum logPrincipal)
private theorem summable_norm_and_hasSum_prod_tsum {R : Type*} [NormedCommRing R]
    [CompleteSpace R] :
    ∀ (n : ℕ) (f : Fin n → ℕ → R), (∀ i, Summable fun k => ‖f i k‖) →
      Summable (fun α : Fin n → ℕ => ‖∏ i, f i (α i)‖) ∧
      HasSum (fun α : Fin n → ℕ => ∏ i, f i (α i)) (∏ i, ∑' k, f i k) := by
  intro n
  induction n with
  | zero =>
    intro f _
    refine ⟨(hasSum_fintype _).summable, ?_⟩
    simp
  | succ n ih =>
    intro f hf
    obtain ⟨hsum, hhas⟩ := ih (fun i => f i.succ) (fun i => hf i.succ)
    let e : ℕ × (Fin n → ℕ) ≃ (Fin (n + 1) → ℕ) := Fin.consEquiv (fun _ => ℕ)
    have hterm : ∀ p : ℕ × (Fin n → ℕ),
        ∏ i, f i (e p i) = f 0 p.1 * ∏ i, f i.succ (p.2 i) := by
      intro p
      rw [Fin.prod_univ_succ]
      rfl
    have hs : Summable fun p : ℕ × (Fin n → ℕ) =>
        ‖f 0 p.1‖ * ‖∏ i, f i.succ (p.2 i)‖ :=
      (hf 0).mul_of_nonneg hsum (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)
    refine ⟨?_, ?_⟩
    · rw [← e.summable_iff]
      refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun p => ?_) hs
      simp only [Function.comp_apply, hterm]
      exact norm_mul_le _ _
    · rw [← e.hasSum_iff]
      have hp := (summable_mul_of_summable_norm (hf 0) hsum).hasSum
      rw [← tsum_mul_tsum_of_summable_norm (hf 0) hsum, hhas.tsum_eq, ← Fin.prod_univ_succ
        (f := fun i => ∑' k, f i k)] at hp
      convert hp using 1
      funext p
      exact hterm p
private theorem hasSum_monomial_div_factorial_complex (n : ℕ) (c : Fin n → ℂ) :
    HasSum (fun α : MultiIndex n =>
      MultiIndex.monomial c α / (MultiIndex.factorial α : ℂ)) (Complex.exp (∑ i, c i)) := by
  have h := (summable_norm_and_hasSum_prod_tsum n (fun i k => c i ^ k / (k.factorial : ℂ))
    fun i => by simpa [norm_div, norm_pow] using Real.summable_pow_div_factorial ‖c i‖).2
  have hs : ∀ i, ∑' k : ℕ, c i ^ k / (k.factorial : ℂ) = Complex.exp (c i) := fun i => by
    rw [Complex.exp_eq_exp_ℂ]
    exact (NormedSpace.expSeries_div_hasSum_exp (c i)).tsum_eq
  beta_reduce at h
  simp only [hs] at h
  have hterm : ∀ α : MultiIndex n, ∏ i, c i ^ α i / ((α i).factorial : ℂ) =
      MultiIndex.monomial c α / (MultiIndex.factorial α : ℂ) := fun α => by
    rw [Finset.prod_div_distrib, MultiIndex.monomial, MultiIndex.factorial, Nat.cast_prod]
  simp only [hterm] at h
  rwa [Complex.exp_sum]
private theorem hasSum_monomial_div_factorial_real (n : ℕ) (c : Fin n → ℝ) :
    HasSum (fun α : MultiIndex n =>
      MultiIndex.monomial c α / (MultiIndex.factorial α : ℝ)) (Real.exp (∑ i, c i)) := by
  have h := (summable_norm_and_hasSum_prod_tsum n (fun i k => c i ^ k / (k.factorial : ℝ))
    fun i => by simpa [norm_div, norm_pow] using Real.summable_pow_div_factorial ‖c i‖).2
  have hs : ∀ i, ∑' k : ℕ, c i ^ k / (k.factorial : ℝ) = Real.exp (c i) := fun i => by
    rw [Real.exp_eq_exp_ℝ]
    exact (NormedSpace.expSeries_div_hasSum_exp (c i)).tsum_eq
  beta_reduce at h
  simp only [hs] at h
  have hterm : ∀ α : MultiIndex n, ∏ i, c i ^ α i / ((α i).factorial : ℝ) =
      MultiIndex.monomial c α / (MultiIndex.factorial α : ℝ) := fun α => by
    rw [Finset.prod_div_distrib, MultiIndex.monomial, MultiIndex.factorial, Nat.cast_prod]
  simp only [hterm] at h
  rwa [Real.exp_sum]
theorem exponentialMomentSeriesExpansion_holds
    (hE : YangMills.Construction.Probability.ExpectationBasicProperties)
    (hT : YangMills.Construction.ComplexVariables.HolomorphicFacts.StandardFacts) :
    YangMills.Construction.Cumulants.ExponentialMomentSeriesExpansion := by
  intro X _ ν _ n x hn hx b e m F U
  obtain ⟨hEa, hEb, -, hEd⟩ := hE X ν
  have : Nonempty X := ν.nonempty_of_neZero
  have hbdd : ∀ i, BddAbove (range fun ω => ‖(x i ω : ℂ)‖) := fun i => by
    obtain ⟨C, hC⟩ := (hx i).bounded
    refine ⟨C, ?_⟩
    rintro _ ⟨ω, rfl⟩
    simpa using hC ω
  have hle : ∀ i ω, |x i ω| ≤ b i := fun i ω =>
    calc |x i ω| = ‖(x i ω : ℂ)‖ := by simp
      _ ≤ b i := le_ciSup (hbdd i) ω
  have hb0 : ∀ i, 0 ≤ b i := fun i => Real.iSup_nonneg fun ω => norm_nonneg _
  have hmonAbs : ∀ (α : MultiIndex n) ω,
      |MultiIndex.monomial x α ω| ≤ MultiIndex.monomial b α := by
    intro α ω
    simp only [MultiIndex.monomial, Finset.prod_apply, Pi.pow_apply, Finset.abs_prod, abs_pow]
    exact Finset.prod_le_prod (fun i _ => by positivity)
      fun i _ => pow_le_pow_left₀ (abs_nonneg _) (hle i ω) _
  have hmonRV : ∀ α : MultiIndex n, IsBoundedRealRV (MultiIndex.monomial x α) := by
    intro α
    refine ⟨?_, _, hmonAbs α⟩
    have h : MultiIndex.monomial x α = fun ω => ∏ i, x i ω ^ α i := by
      funext ω
      simp [MultiIndex.monomial, Finset.prod_apply]
    rw [h]
    exact Finset.measurable_prod _ fun i _ => (hx i).measurable.pow_const _
  have hmonSup : ∀ α : MultiIndex n,
      supModulus (fun ω => ((MultiIndex.monomial x α ω : ℝ) : ℂ)) ≤ MultiIndex.monomial b α :=
    fun α => ciSup_le fun ω => by simpa using hmonAbs α ω
  have heRV : ∀ z : Coordinates.ComplexCoordinates n, IsBoundedComplexRV (e z) := fun z =>
    (hEd n hn x (fun ξ => Complex.exp (∑ i, z i * (ξ i : ℂ))) hx (by fun_prop)).1
  have heBd : ∀ (z : Coordinates.ComplexCoordinates n) ω,
      ‖e z ω‖ ≤ Real.exp (∑ i, ‖z i‖ * b i) := by
    intro z ω
    have h : ‖∑ i, z i * (x i ω : ℂ)‖ ≤ ∑ i, ‖z i‖ * b i :=
      (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => by
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_left (hle i ω) (norm_nonneg _))
    exact (Complex.norm_exp_le_exp_norm _).trans (Real.exp_le_exp.2 h)
  have heReal : ∀ (t : Fin n → ℝ) (ω : X), (e (fun i => (t i : ℂ)) ω).im = 0 ∧
      Real.exp (-∑ i, |t i| * b i) ≤ (e (fun i => (t i : ℂ)) ω).re := by
    intro t ω
    have hsum : ∑ i, (t i : ℂ) * (x i ω : ℂ) = ((∑ i, t i * x i ω : ℝ) : ℂ) := by
      push_cast
      rfl
    have heq : e (fun i => (t i : ℂ)) ω = ((Real.exp (∑ i, t i * x i ω) : ℝ) : ℂ) := by
      change Complex.exp (∑ i, (t i : ℂ) * (x i ω : ℂ)) = _
      rw [hsum, Complex.ofReal_exp]
    rw [heq]
    refine ⟨Complex.ofReal_im _, ?_⟩
    rw [Complex.ofReal_re]
    refine Real.exp_le_exp.2 ?_
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_le_sum fun i _ => ?_
    have h : |t i * x i ω| ≤ |t i| * b i := by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (hle i ω) (abs_nonneg _)
    exact (abs_le.1 h).1
  have hmaj : ∀ z : Coordinates.ComplexCoordinates n, HasSum (fun α : MultiIndex n =>
      absMonomial z α / (MultiIndex.factorial α : ℝ) * MultiIndex.monomial b α)
      (Real.exp (∑ i, ‖z i‖ * b i)) := by
    intro z
    convert hasSum_monomial_div_factorial_real n (fun i => ‖z i‖ * b i) using 2 with α
    simp only [absMonomial, MultiIndex.monomial, mul_pow, Finset.prod_mul_distrib]
    ring
  have hm : ∀ α, ‖m α‖ ≤ MultiIndex.monomial b α := fun α =>
    (hEb.2.2.2 _ (hEa.2.2.2.2.2.2 _ (hmonRV α))).trans (hmonSup α)
  have habs0 : ∀ (z : Coordinates.ComplexCoordinates n) (α : MultiIndex n),
      0 ≤ absMonomial z α :=
    fun z α => by
      simp only [absMonomial, MultiIndex.monomial]
      positivity
  have hnormMon : ∀ (z : Coordinates.ComplexCoordinates n) (α : MultiIndex n),
      ‖MultiIndex.monomial z α‖ = absMonomial z α := by
    intro z α
    simp [MultiIndex.monomial, absMonomial, norm_prod, norm_pow]
  have htermLe : ∀ (z : Coordinates.ComplexCoordinates n) (α : MultiIndex n),
      ‖MultiIndex.monomial z α / (MultiIndex.factorial α : ℂ) * m α‖ ≤
        absMonomial z α / (MultiIndex.factorial α : ℝ) * MultiIndex.monomial b α := by
    intro z α
    rw [norm_mul, norm_div, hnormMon, Complex.norm_natCast]
    exact mul_le_mul_of_nonneg_left (hm α) (div_nonneg (habs0 z α) (Nat.cast_nonneg _))
  have hsummable : ∀ z : Coordinates.ComplexCoordinates n, IsAbsSummable
      (fun α => MultiIndex.monomial z α / (MultiIndex.factorial α : ℂ) * m α) := fun z =>
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (htermLe z) (hmaj z).summable
  have hseries : ∀ z : Coordinates.ComplexCoordinates n, HasSum
      (fun α => MultiIndex.monomial z α / (MultiIndex.factorial α : ℂ) * m α) (F z) := by
    intro z
    have hpoint : ∀ ω, HasSum (fun α : MultiIndex n =>
        MultiIndex.monomial z α / (MultiIndex.factorial α : ℂ) *
          ((MultiIndex.monomial x α ω : ℝ) : ℂ)) (e z ω) := by
      intro ω
      have hterm : ∀ α : MultiIndex n,
          MultiIndex.monomial (fun i => z i * (x i ω : ℂ)) α / (MultiIndex.factorial α : ℂ) =
            MultiIndex.monomial z α / (MultiIndex.factorial α : ℂ) *
              ((MultiIndex.monomial x α ω : ℝ) : ℂ) := fun α => by
        simp only [MultiIndex.monomial, mul_pow, Finset.prod_mul_distrib, Finset.prod_apply,
          Pi.pow_apply]
        push_cast
        ring
      have h := hasSum_monomial_div_factorial_complex n (fun i => z i * (x i ω : ℂ))
      simp only [hterm] at h
      exact h
    have hint := hasSum_integral_of_dominated_convergence (μ := ν)
      (F := fun (α : MultiIndex n) ω =>
        MultiIndex.monomial z α / (MultiIndex.factorial α : ℂ) *
          ((MultiIndex.monomial x α ω : ℝ) : ℂ))
      (f := e z)
      (fun α _ => absMonomial z α / (MultiIndex.factorial α : ℝ) * MultiIndex.monomial b α)
      (fun α => (measurable_const.mul
        (Complex.measurable_ofReal.comp (hmonRV α).measurable)).aestronglyMeasurable)
      (fun α => Filter.Eventually.of_forall fun ω => by
        rw [norm_mul, norm_div, hnormMon, Complex.norm_natCast, Complex.norm_real,
          Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_left (hmonAbs α ω)
          (div_nonneg (habs0 z α) (Nat.cast_nonneg _)))
      (Filter.Eventually.of_forall fun _ => (hmaj z).summable)
      (integrable_const _)
      (Filter.Eventually.of_forall hpoint)
    simp only [integral_const_mul] at hint
    exact hint
  obtain ⟨hTpart, -, -, hTseries, hTlog, -⟩ := hT n hn univ isOpen_univ
  let a : MultiIndex n → ℂ := fun α => m α / (MultiIndex.factorial α : ℂ)
  have haSummable : ∀ z : Coordinates.ComplexCoordinates n,
      Summable fun α => ‖a α‖ * absMonomial z α := by
    intro z
    refine Summable.of_nonneg_of_le (fun α => mul_nonneg (norm_nonneg _) (habs0 z α))
      (fun α => ?_) (hmaj z).summable
    have h := htermLe z α
    rw [norm_mul, norm_div, hnormMon, Complex.norm_natCast] at h
    calc ‖a α‖ * absMonomial z α
        = absMonomial z α / (MultiIndex.factorial α : ℝ) * ‖m α‖ := by
          simp only [a, norm_div, Complex.norm_natCast]
          ring
      _ ≤ _ := h
  have hFeq : F = ComplexVariables.HolomorphicFacts.powerSeriesSum a := by
    funext z
    rw [← (hseries z).tsum_eq]
    refine tsum_congr fun α => ?_
    simp only [a]
    ring
  have hEnt : IsEntireFun F := by
    have h := (hTseries a haSummable).1
    rwa [← hFeq] at h
  have hcont : Continuous F := by
    have h1 : Continuous ((Equiv.funUnique (Fin 1) ℂ).symm ∘ F) := continuousOn_univ.1 hEnt.2.1
    have h2 : Continuous fun g : Fin 1 → ℂ => g 0 := continuous_apply 0
    convert h2.comp h1 using 1
    funext z
    simp
  have hUo : IsOpen U := isOpen_lt (hcont.sub continuous_const).norm continuous_const
  have h0 : F 0 = 1 := by
    have h : e 0 = fun _ => 1 := by
      funext ω
      simp [e, expComp]
    change complexExpectation ν (e 0) = 1
    rw [h]
    exact hEb.2.2.1
  have h0U : (0 : Coordinates.ComplexCoordinates n) ∈ U := by
    change ‖F 0 - 1‖ < 1
    simp [h0]
  have hslit : ∀ z ∈ U, F z ∈ ComplexVariables.nonpositiveRayComplement := fun z hz =>
    hTlog.2.2.2.2.2.2.1 hz
  have hFU : IsHolomorphicScalar U F :=
    ((hTpart F hEnt).2.2.2.2.2.2.2 U hUo (subset_univ _) F fun _ _ => rfl).1
  have hLog : IsHolomorphicScalar U (logPrincipal ∘ F) :=
    ((hT n hn U hUo).2.2.1 ComplexVariables.nonpositiveRayComplement F logPrincipal hTlog.1 hFU
      hslit hTlog.2.1).1
  refine ⟨fun α => ⟨hmonRV α, hmonSup α⟩, fun z => ⟨heRV z, heBd z⟩, heReal,
    fun z => ⟨hsummable z, (hseries z).tsum_eq.symm, hm, hmaj z⟩, hEnt, h0, hUo, h0U, hslit, hLog⟩
end YangMills.Construction.Cumulants
