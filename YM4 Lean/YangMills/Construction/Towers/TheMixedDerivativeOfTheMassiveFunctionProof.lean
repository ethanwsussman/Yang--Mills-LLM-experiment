import YangMills.Construction.InfiniteLattice.BondsPlaquettesCircuitsAndConfigurationsOfTheLatticeOfACutoffProof
import YangMills.Construction.OneLoopLaw.CoefficientOfATemperedFunctional
import YangMills.Construction.PeriodicOperators.EntriesDeterminantsAndHolomorphicFunctionsProof
import YangMills.Construction.PeriodicOperators.FunctionalDeterminesItsPolarisationSymbol
import YangMills.Construction.Towers.FactsOfTheMatricesOfAPeriodicFunctionProof
import YangMills.Construction.Towers.TheBackgroundNumbersNearZero
import YangMills.Construction.Towers.TheMassiveFamilyIsTempered
import YangMills.Construction.Towers.TheMassiveFunctionAsASumOfSymbols
import YangMills.Construction.Towers.TheMassiveFunctionIsLocallyHolomorphic
import YangMills.Construction.Towers.TheMixedDerivativeOfTheMassiveFunction
import Mathlib
set_option autoImplicit false
open Filter Asymptotics Set
open scoped Topology ContDiff
noncomputable section
namespace YangMills.Construction.Tower.MassiveOpFunctions.MixedPartialOfMassiveLogFn
open FullSpace.BackgroundJets
open YangMills.Construction.PeriodicOperators (toComplexVec imStrip)
open YangMills.Construction.PeriodicOperators.Tempered
open YangMills.Construction.OneLoopLaw.TemperedStiffness
  (secondPartialAtZero HasTransverseForm StiffnessFormulas transverseTensor)
open YangMills.Construction.InfiniteLattice (AmbientSpace)
open YangMills.Construction.Coordinates.ComplexCoordinates
open YangMills.Construction.Coordinates.ComplexCoordinates.LogDetSecondDeriv (IsHolomorphicScalarIn asLine)
section Calculus
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
theorem hasDerivAt_fderiv_apply_smul_line {r : E → ℂ} (hr : ContDiffAt ℝ 2 r 0) (e f : E) :
    HasDerivAt (fun s : ℝ => fderiv ℝ r (s • e) f) (fderiv ℝ (fderiv ℝ r) 0 e f) 0 := by
  have hD : DifferentiableAt ℝ (fderiv ℝ r) 0 :=
    (hr.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have h1 : HasDerivAt (fun t : ℝ => t • e) e 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).smul_const e
  have h2 : HasFDerivAt (fderiv ℝ r) (fderiv ℝ (fderiv ℝ r) 0) ((0 : ℝ) • e) := by
    simpa using hD.hasFDerivAt
  have h3 := h2.comp_hasDerivAt (0 : ℝ) h1
  exact (ContinuousLinearMap.apply ℝ ℂ f).hasFDerivAt.comp_hasDerivAt (0 : ℝ) h3
theorem eventually_differentiableAt_of_contDiffAt_two {r : E → ℂ} (hr : ContDiffAt ℝ 2 r 0) :
    ∀ᶠ x in 𝓝 (0 : E), DifferentiableAt ℝ r x := by
  filter_upwards [hr.eventually (by simp)] with x hx using hx.differentiableAt (by norm_num)
theorem tendsto_smul_line_zero (v : E) : Tendsto (fun t : ℝ => t • v) (𝓝 0) (𝓝 0) := by
  have : Continuous fun t : ℝ => t • v := by fun_prop
  simpa using this.tendsto 0
theorem fderiv_fderiv_diag_eq_zero_of_isBigO_cube {r : E → ℂ} (hr : ContDiffAt ℝ 2 r 0)
    (hO : r =O[𝓝 0] fun p => ‖p‖ ^ 3) (v : E) : fderiv ℝ (fderiv ℝ r) 0 v v = 0 := by
  set a := fderiv ℝ (fderiv ℝ r) 0 v v with ha
  have hO' : r =O[𝓝 0] fun p => ‖p - 0‖ ^ 3 := by simpa using hO
  have hr0 : r 0 = 0 := hO'.eq_zero_of_norm_pow (by norm_num)
  have hD0 : fderiv ℝ r 0 = 0 := (hO'.hasFDerivAt (by norm_num)).fderiv
  obtain ⟨ε, hε, hball⟩ :=
    Metric.eventually_nhds_iff_ball.1
      ((tendsto_smul_line_zero v).eventually (eventually_differentiableAt_of_contDiffAt_two hr))
  have hs : Convex ℝ (Metric.ball (0 : ℝ) ε) := convex_ball _ _
  have h0s : (0 : ℝ) ∈ Metric.ball (0 : ℝ) ε := Metric.mem_ball_self hε
  have hnhds : 𝓝[Metric.ball (0 : ℝ) ε] (0 : ℝ) = 𝓝 0 := Metric.isOpen_ball.nhdsWithin_eq h0s
  have hφ : ∀ t ∈ Metric.ball (0 : ℝ) ε,
      HasDerivWithinAt (fun t : ℝ => r (t • v) - (t ^ 2 / 2) • a)
        (fderiv ℝ r (t • v) v - t • a) (Metric.ball (0 : ℝ) ε) t := by
    intro t ht
    have h1 : HasDerivAt (fun t : ℝ => t • v) v t := by
      simpa using (hasDerivAt_id t).smul_const v
    have h2 : HasDerivAt (fun t : ℝ => r (t • v)) (fderiv ℝ r (t • v) v) t :=
      (hball t ht).hasFDerivAt.comp_hasDerivAt t h1
    have h3 : HasDerivAt (fun t : ℝ => (t ^ 2 / 2) • a) (t • a) t := by
      have h4 : HasDerivAt (fun t : ℝ => t ^ 2 / 2) t t := by
        have := (hasDerivAt_pow 2 t).div_const 2
        simpa using this
      exact h4.smul_const a
    exact (h2.sub h3).hasDerivWithinAt
  have hφ' : (fun t : ℝ => fderiv ℝ r (t • v) v - t • a) =o[𝓝[Metric.ball (0 : ℝ) ε] 0]
      fun t => (t - 0) ^ 1 := by
    rw [hnhds]
    have h := hasDerivAt_iff_isLittleO.1 (hasDerivAt_fderiv_apply_smul_line hr v v)
    simpa [hD0] using h
  have hlit := hs.isLittleO_pow_succ_real h0s hφ hφ'
  rw [hnhds] at hlit
  have hlit' : (fun t : ℝ => r (t • v) - (t ^ 2 / 2) • a) =o[𝓝 0] fun t => t ^ 2 := by
    simpa [hr0] using hlit
  have hline : (fun t : ℝ => r (t • v)) =o[𝓝 0] fun t => t ^ 2 := by
    have h1 : (fun t : ℝ => r (t • v)) =O[𝓝 0] fun t => ‖t • v‖ ^ 3 :=
      hO.comp_tendsto (tendsto_smul_line_zero v)
    have h2 : (fun t : ℝ => ‖t • v‖ ^ 3) =O[𝓝 0] fun t : ℝ => t ^ 3 := by
      refine IsBigO.of_bound (‖v‖ ^ 3) (Eventually.of_forall fun t => ?_)
      simp [norm_smul, mul_pow, mul_comm]
    exact (h1.trans h2).trans_isLittleO (isLittleO_pow_pow (by norm_num))
  have hquad : (fun t : ℝ => (t ^ 2 / 2) • a) =o[𝓝 0] fun t => t ^ 2 := by
    simpa using hline.sub hlit'
  by_contra hne
  have hpos : 0 < ‖a‖ / 4 := by
    have := norm_pos_iff.2 hne
    positivity
  have hev := (isLittleO_iff.1 hquad hpos).filter_mono (nhdsWithin_le_nhds (s := {(0 : ℝ)}ᶜ))
  obtain ⟨t, ht, ht0⟩ := (hev.and self_mem_nhdsWithin).exists
  have ht2 : 0 < t ^ 2 := by
    have : t ≠ 0 := ht0
    positivity
  rw [norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (by positivity), abs_of_pos ht2] at ht
  have hna := norm_pos_iff.2 hne
  nlinarith [mul_pos ht2 hna]
theorem deriv_deriv_line_eq_fderiv_fderiv {ρ : E → ℂ} (hρ : ContDiffAt ℝ 2 ρ 0) (e f : E) :
    deriv (fun s : ℝ => deriv (fun t : ℝ => ρ (s • e + t • f)) 0) 0 =
      fderiv ℝ (fderiv ℝ ρ) 0 e f := by
  have hev : (fun s : ℝ => deriv (fun t : ℝ => ρ (s • e + t • f)) 0) =ᶠ[𝓝 0]
      fun s => fderiv ℝ ρ (s • e) f := by
    filter_upwards [(tendsto_smul_line_zero e).eventually
      (eventually_differentiableAt_of_contDiffAt_two hρ)] with s hs
    have h1 : HasDerivAt (fun t : ℝ => s • e + t • f) f 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).smul_const f).const_add (s • e)
    have h2 : HasFDerivAt ρ (fderiv ℝ ρ (s • e)) (s • e + (0 : ℝ) • f) := by
      simpa using hs.hasFDerivAt
    exact (h2.comp_hasDerivAt (0 : ℝ) h1).deriv
  rw [hev.deriv_eq]
  exact (hasDerivAt_fderiv_apply_smul_line hρ e f).deriv
end Calculus
theorem piSingle_eq_smul (μ : Fin 4) (s : ℝ) :
    (Pi.single μ s : AmbientSpace) = s • (Pi.single μ 1 : AmbientSpace) := by apply _root_.YangMills.Construction.RefinedLatticeSymmetries.single_eq_smul_basisVector <;> assumption
theorem secondPartialAtZero_eq_fderiv_fderiv {g : (Fin 4 → ℂ) → ℂ} {ρ : AmbientSpace → ℂ}
    (h : ∀ᶠ p in 𝓝 (0 : AmbientSpace), g (toComplexVec p) = ρ p) (hρ : ContDiffAt ℝ 2 ρ 0)
    (μ ν : Fin 4) :
    secondPartialAtZero g μ ν =
      fderiv ℝ (fderiv ℝ ρ) 0 (Pi.single μ 1 : AmbientSpace) (Pi.single ν 1 : AmbientSpace) := by
  have hc : Tendsto (fun x : ℝ × ℝ => (Pi.single μ x.1 + Pi.single ν x.2 : AmbientSpace))
      (𝓝 (0, 0)) (𝓝 0) := by
    have : Continuous fun x : ℝ × ℝ =>
        (x.1 • (Pi.single μ 1 : AmbientSpace) + x.2 • (Pi.single ν 1 : AmbientSpace)) := by
      fun_prop
    have h0 := this.tendsto (0, 0)
    simp only [zero_smul, add_zero] at h0
    simpa only [← piSingle_eq_smul] using h0
  have h2 := hc.eventually h
  rw [nhds_prod_eq] at h2
  have h3 := h2.curry
  unfold secondPartialAtZero
  have h4 : (fun s : ℝ => deriv (fun t : ℝ =>
        g (toComplexVec (Pi.single μ s + Pi.single ν t))) 0) =ᶠ[𝓝 0]
      fun s => deriv (fun t : ℝ =>
        ρ (s • (Pi.single μ 1 : AmbientSpace) + t • (Pi.single ν 1 : AmbientSpace))) 0 := by
    refine h3.mono fun s hs => EventuallyEq.deriv_eq ?_
    filter_upwards [hs] with t ht
    rw [ht, piSingle_eq_smul μ s, piSingle_eq_smul ν t]
  rw [h4.deriv_eq]
  exact deriv_deriv_line_eq_fderiv_fderiv hρ _ _
theorem secondPartialAtZero_const_mul (u : ℂ) (g : (Fin 4 → ℂ) → ℂ) (μ ν : Fin 4) :
    secondPartialAtZero (fun κ => u * g κ) μ ν = u * secondPartialAtZero g μ ν := by
  simp only [secondPartialAtZero, deriv_const_mul_field]
theorem secondPartialAtZero_comp_smul (c : ℝ) (g : (Fin 4 → ℂ) → ℂ) (μ ν : Fin 4) :
    secondPartialAtZero (fun κ => g fun i => (c : ℂ) * κ i) μ ν =
      (c : ℂ) ^ 2 * secondPartialAtZero g μ ν := by
  have hpt : ∀ s t : ℝ,
      (fun i => (c : ℂ) * toComplexVec (Pi.single μ s + Pi.single ν t : AmbientSpace) i) =
        toComplexVec (Pi.single μ (c * s) + Pi.single ν (c * t) : AmbientSpace) := by
    intro s t
    funext i
    simp only [toComplexVec, Pi.add_apply, Pi.single_apply]
    split_ifs <;> push_cast <;> ring
  unfold secondPartialAtZero
  simp only [hpt]
  have h1 : ∀ s : ℝ, deriv (fun t : ℝ =>
        g (toComplexVec (Pi.single μ s + Pi.single ν (c * t) : AmbientSpace))) 0 =
      (c : ℂ) * deriv (fun t : ℝ =>
        g (toComplexVec (Pi.single μ s + Pi.single ν t : AmbientSpace))) 0 := by
    intro s
    have := deriv_comp_mul_left (x := (0 : ℝ)) c
      (fun t : ℝ => g (toComplexVec (Pi.single μ s + Pi.single ν t : AmbientSpace)))
    simpa [Complex.real_smul] using this
  simp only [h1, deriv_const_mul_field]
  have h2 := deriv_comp_mul_left (x := (0 : ℝ)) c
    (fun s : ℝ => deriv (fun t : ℝ =>
      g (toComplexVec (Pi.single μ s + Pi.single ν t : AmbientSpace))) 0)
  have h3 : deriv (fun s : ℝ => deriv (fun t : ℝ =>
        g (toComplexVec (Pi.single μ (c * s) + Pi.single ν t : AmbientSpace))) 0) 0 =
      (c : ℂ) * deriv (fun s : ℝ => deriv (fun t : ℝ =>
        g (toComplexVec (Pi.single μ s + Pi.single ν t : AmbientSpace))) 0) 0 := by
    simpa [Complex.real_smul] using h2
  rw [h3]
  ring
theorem secondPartialAtZero_eq_of_isBigO_cube {g G : (Fin 4 → ℂ) → ℂ} {ρ₁ ρ₂ : AmbientSpace → ℂ}
    (h₁ : ∀ᶠ p in 𝓝 (0 : AmbientSpace), g (toComplexVec p) = ρ₁ p)
    (h₂ : ∀ᶠ p in 𝓝 (0 : AmbientSpace), G (toComplexVec p) = ρ₂ p)
    (c₁ : ContDiffAt ℝ 2 ρ₁ 0) (c₂ : ContDiffAt ℝ 2 ρ₂ 0)
    (hO : (fun p => ρ₁ p - ρ₂ p) =O[𝓝 0] fun p => ‖p‖ ^ 3) (μ ν : Fin 4) :
    secondPartialAtZero g μ ν = secondPartialAtZero G μ ν := by
  rw [secondPartialAtZero_eq_fderiv_fderiv h₁ c₁, secondPartialAtZero_eq_fderiv_fderiv h₂ c₂]
  have hr : ContDiffAt ℝ 2 (fun p => ρ₁ p - ρ₂ p) 0 := c₁.sub c₂
  have hfirst : fderiv ℝ (fun p => ρ₁ p - ρ₂ p) =ᶠ[𝓝 0]
      fun x => fderiv ℝ ρ₁ x - fderiv ℝ ρ₂ x := by
    filter_upwards [eventually_differentiableAt_of_contDiffAt_two c₁,
      eventually_differentiableAt_of_contDiffAt_two c₂] with x h1 h2
    exact (h1.hasFDerivAt.sub h2.hasFDerivAt).fderiv
  have hd₁ : DifferentiableAt ℝ (fderiv ℝ ρ₁) 0 :=
    (c₁.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hd₂ : DifferentiableAt ℝ (fderiv ℝ ρ₂) 0 :=
    (c₂.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hsecond : fderiv ℝ (fderiv ℝ fun p => ρ₁ p - ρ₂ p) 0 =
      fderiv ℝ (fderiv ℝ ρ₁) 0 - fderiv ℝ (fderiv ℝ ρ₂) 0 := by
    rw [hfirst.fderiv_eq]
    exact (hd₁.hasFDerivAt.sub hd₂.hasFDerivAt).fderiv
  have hdiag := fderiv_fderiv_diag_eq_zero_of_isBigO_cube hr hO
  have hsym := hr.isSymmSndFDerivAt (by simp)
  set e : AmbientSpace := Pi.single μ 1
  set f : AmbientSpace := Pi.single ν 1
  have hsum := hdiag (e + f)
  simp only [map_add, add_apply, hdiag e, hdiag f, zero_add, add_zero] at hsum
  have hef : fderiv ℝ (fderiv ℝ fun p => ρ₁ p - ρ₂ p) 0 e f = 0 := by
    have h := hsym e f
    rw [← h] at hsum
    have h2 : (2 : ℂ) * fderiv ℝ (fderiv ℝ fun p => ρ₁ p - ρ₂ p) 0 e f = 0 := by
      rw [two_mul]; exact hsum
    simpa using h2
  rw [hsecond] at hef
  simpa [sub_eq_zero] using hef
theorem norm_pow_isBigO_norm_pow {a b : ℕ} (h : a ≤ b) :
    (fun p : AmbientSpace => ‖p‖ ^ b) =O[𝓝 0] fun p => ‖p‖ ^ a := by
  refine IsBigO.of_bound 1 ?_
  filter_upwards [Metric.ball_mem_nhds (0 : AmbientSpace) one_pos] with p hp
  have hp' : ‖p‖ ≤ 1 := by
    have := mem_ball_zero_iff.1 hp
    exact this.le
  simpa [abs_of_nonneg (norm_nonneg p)] using pow_le_pow_of_le_one (norm_nonneg p) hp' h
theorem symbolSum_sub_isBigO_cube {S : Finset (Fin 4 → ℤ)} (h0 : (0 : Fin 4 → ℤ) ∈ S)
    (P : (Fin 4 → ℤ) → Fin 4 → Fin 4 → AmbientSpace → ℂ)
    (bp bm : AmbientSpace → Fin 4 → (Fin 4 → ℤ) → ℂ)
    (hPb : ∀ m ρ σ, P m ρ σ =O[𝓝 0] fun _ => (1 : ℝ))
    (hP0 : ∀ ρ σ, P 0 ρ σ =O[𝓝 0] fun p => ‖p‖ ^ 2)
    (hbp : ∀ m ∈ S, m ≠ 0 → ∀ ρ, (fun p => bp p ρ m) =O[𝓝 0] fun p => ‖p‖ ^ 2)
    (hbm : ∀ m ∈ S, m ≠ 0 → ∀ σ, (fun p => bm p σ (-m)) =O[𝓝 0] fun p => ‖p‖ ^ 2)
    (hbp0 : ∀ ρ, (fun p => bp p ρ 0 - if ρ = 0 then 1 else 0) =O[𝓝 0] fun p => ‖p‖ ^ 1)
    (hbm0 : ∀ σ, (fun p => bm p σ 0 - if σ = 1 then 1 else 0) =O[𝓝 0] fun p => ‖p‖ ^ 1) :
    (fun p => (∑ m ∈ S, ∑ ρ : Fin 4, ∑ σ : Fin 4, P m ρ σ p * bp p ρ m * bm p σ (-m)) - P 0 0 1 p)
      =O[𝓝 0] fun p => ‖p‖ ^ 3 := by
  let c : (Fin 4 → ℤ) → Fin 4 → Fin 4 → AmbientSpace → ℂ := fun m ρ σ p =>
    if m = 0 then (if ρ = 0 then (if σ = 1 then P 0 0 1 p else 0) else 0) else 0
  have hc : ∀ p, ∑ m ∈ S, ∑ ρ : Fin 4, ∑ σ : Fin 4, c m ρ σ p = P 0 0 1 p := by
    intro p
    rw [Finset.sum_eq_single_of_mem 0 h0 (fun m _ hm => by simp [c, hm])]
    rw [Fintype.sum_eq_single (0 : Fin 4) (fun ρ hρ => by simp [c, hρ])]
    rw [Fintype.sum_eq_single (1 : Fin 4) (fun σ hσ => by simp [c, hσ])]
    simp [c]
  have hform : (fun p => (∑ m ∈ S, ∑ ρ : Fin 4, ∑ σ : Fin 4, P m ρ σ p * bp p ρ m * bm p σ (-m)) -
        P 0 0 1 p) = fun p => ∑ m ∈ S, ∑ ρ : Fin 4, ∑ σ : Fin 4,
          (P m ρ σ p * bp p ρ m * bm p σ (-m) - c m ρ σ p) := by
    funext p
    simp only [Finset.sum_sub_distrib, hc]
  rw [hform]
  refine IsBigO.fun_sum fun m hm => IsBigO.fun_sum fun ρ _ => IsBigO.fun_sum fun σ _ => ?_
  by_cases hm0 : m = 0
  · subst hm0
    have hX := hbp0 ρ
    have hY := hbm0 σ
    have hconst : ∀ d : ℂ, (fun _ : AmbientSpace => d) =O[𝓝 0] fun p : AmbientSpace => ‖p‖ ^ 0 := by
      intro d
      simpa using isBigO_const_const d (one_ne_zero (α := ℝ)) (𝓝 (0 : AmbientSpace))
    have hpp : (fun p : AmbientSpace => ‖p‖ ^ 1 * ‖p‖ ^ 1) =O[𝓝 0] fun p => ‖p‖ ^ 1 :=
      (norm_pow_isBigO_norm_pow (a := 1) (b := 2) (by norm_num)).congr'
        (Eventually.of_forall fun p => by simp only; ring) EventuallyEq.rfl
    have hXY := (hX.mul hY).trans hpp
    have hXd := hX.mul (hconst (if σ = 1 then 1 else 0))
    have hdY := (hconst (if ρ = 0 then 1 else 0)).mul hY
    have hsum := (hXY.add (by simpa using hXd)).add (by simpa using hdY)
    have hterm := (hP0 ρ σ).mul hsum
    refine (IsBigO.congr' hterm ?_ ?_)
    · refine Eventually.of_forall fun p => ?_
      by_cases hρ : ρ = 0
      · by_cases hσ : σ = 1
        · subst hρ hσ
          simp [c]
          ring
        · subst hρ
          simp [c, hσ]
          ring
      · by_cases hσ : σ = 1
        · subst hσ
          simp [c, hρ]
          ring
        · simp [c, hρ, hσ]
          ring
    · refine Eventually.of_forall fun p => ?_
      simp only
      ring
  · have hterm := ((hPb m ρ σ).mul (hbp m hm hm0 ρ)).mul (hbm m hm hm0 σ)
    have hpow : (fun p : AmbientSpace => (1 : ℝ) * ‖p‖ ^ 2 * ‖p‖ ^ 2) =O[𝓝 0]
        fun p => ‖p‖ ^ 3 := by
      have := norm_pow_isBigO_norm_pow (a := 3) (b := 4) (by norm_num)
      refine this.congr' (Eventually.of_forall fun p => ?_) EventuallyEq.rfl
      simp only
      ring
    refine (hterm.trans hpow).congr' (Eventually.of_forall fun p => ?_) EventuallyEq.rfl
    simp [c, hm0]
theorem euclidNorm_le_two_mul {q : Fin 4 → ℂ} {t : ℝ} (ht : 0 ≤ t) (h : ∀ i, ‖q i‖ ≤ t) :
    ResponseProperties.euclidNorm q ≤ 2 * t := by
  unfold ResponseProperties.euclidNorm
  rw [show 2 * t = Real.sqrt ((2 * t) ^ 2) from (Real.sqrt_sq (by positivity)).symm]
  apply Real.sqrt_le_sqrt
  have h2 : ∀ i, ‖q i‖ ^ 2 ≤ t ^ 2 := fun i => pow_le_pow_left₀ (norm_nonneg _) (h i) 2
  calc ∑ i, ‖q i‖ ^ 2 ≤ ∑ _i : Fin 4, t ^ 2 := Finset.sum_le_sum fun i _ => h2 i
    _ = (2 * t) ^ 2 := by simp; ring
theorem norm_toComplexVec_apply_le (p : AmbientSpace) (i : Fin 4) : ‖toComplexVec p i‖ ≤ ‖p‖ := by
  simpa [toComplexVec] using norm_le_pi_norm p i
theorem continuous_toComplexVec : Continuous (toComplexVec : AmbientSpace → Fin 4 → ℂ) := by apply _root_.YangMills.Construction.PeriodicOperators.EntriesDets.continuous_toComplexVec <;> assumption
theorem toComplexVec_zero : toComplexVec (0 : AmbientSpace) = 0 := by
  funext i
  simp [toComplexVec]
theorem isBigO_norm_pow_of_euclidNorm_bound {f : AmbientSpace → ℂ} {q : AmbientSpace → Fin 4 → ℂ}
    {C : ℝ} {n : ℕ} (hq : ∀ p i, ‖q p i‖ ≤ ‖p‖)
    (h : ∀ᶠ p in 𝓝 (0 : AmbientSpace), ‖f p‖ ≤ C * ResponseProperties.euclidNorm (q p) ^ n) :
    f =O[𝓝 0] fun p => ‖p‖ ^ n := by
  refine IsBigO.of_bound (|C| * 2 ^ n) ?_
  filter_upwards [h] with p hp
  have h1 := euclidNorm_le_two_mul (norm_nonneg p) (hq p)
  have h0 : 0 ≤ ResponseProperties.euclidNorm (q p) := Real.sqrt_nonneg _
  have h2 : ResponseProperties.euclidNorm (q p) ^ n ≤ (2 * ‖p‖) ^ n :=
    pow_le_pow_left₀ h0 h1 n
  calc ‖f p‖ ≤ C * ResponseProperties.euclidNorm (q p) ^ n := hp
    _ ≤ |C| * ResponseProperties.euclidNorm (q p) ^ n :=
        mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity)
    _ ≤ |C| * (2 * ‖p‖) ^ n := mul_le_mul_of_nonneg_left h2 (abs_nonneg C)
    _ = |C| * 2 ^ n * ‖‖p‖ ^ n‖ := by
        rw [mul_pow, norm_pow, norm_norm, mul_assoc]
theorem entry_isBigO_sq_of_transverseForm {π : SymbolArray} {b : ℝ} (h : HasTransverseForm π b)
    (ρ σ : Fin 4) :
    (fun x : AmbientSpace => π ρ σ (toComplexVec x)) =O[𝓝 0] fun x => ‖x‖ ^ 2 := by
  have hsq : ∀ x : AmbientSpace, TorusMetric.euclidNormVec x ^ 2 ≤ 4 * ‖x‖ ^ 2 := by
    intro x
    have h2 : ∀ i, x i ^ 2 ≤ ‖x‖ ^ 2 := fun i => by
      have := norm_le_pi_norm x i
      rw [Real.norm_eq_abs] at this
      calc x i ^ 2 = |x i| ^ 2 := (sq_abs _).symm
        _ ≤ ‖x‖ ^ 2 := pow_le_pow_left₀ (abs_nonneg _) this 2
    unfold TorusMetric.euclidNormVec
    rw [Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _)]
    calc ∑ i, x i ^ 2 ≤ ∑ _i : Fin 4, ‖x‖ ^ 2 := Finset.sum_le_sum fun i _ => h2 i
      _ = 4 * ‖x‖ ^ 2 := by simp
  have hA := h ρ σ
  have hA' : (fun x : AmbientSpace => TorusMetric.euclidNormVec x ^ 4) =O[𝓝 0]
      fun x => ‖x‖ ^ 4 := by
    refine IsBigO.of_bound 16 (Eventually.of_forall fun x => ?_)
    have h4 := pow_le_pow_left₀ (sq_nonneg _) (hsq x) 2
    have hnn : 0 ≤ TorusMetric.euclidNormVec x := Real.sqrt_nonneg _
    rw [norm_pow, norm_pow, norm_norm, Real.norm_eq_abs, abs_of_nonneg hnn]
    calc TorusMetric.euclidNormVec x ^ 4 = (TorusMetric.euclidNormVec x ^ 2) ^ 2 := by ring
      _ ≤ (4 * ‖x‖ ^ 2) ^ 2 := h4
      _ = 16 * ‖x‖ ^ 4 := by ring
  have hB : (fun x : AmbientSpace => (transverseTensor b ρ σ x : ℂ)) =O[𝓝 0]
      fun x => ‖x‖ ^ 2 := by
    refine IsBigO.of_bound (|b| * 5) (Eventually.of_forall fun x => ?_)
    rw [Complex.norm_real, Real.norm_eq_abs, norm_pow, norm_norm]
    unfold transverseTensor
    rw [abs_mul, mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg b)
    have hxρ : |x ρ| ≤ ‖x‖ := norm_le_pi_norm x ρ
    have hxσ : |x σ| ≤ ‖x‖ := norm_le_pi_norm x σ
    have hprod : |x ρ * x σ| ≤ ‖x‖ ^ 2 := by
      rw [abs_mul, sq]
      exact mul_le_mul hxρ hxσ (abs_nonneg _) (norm_nonneg _)
    have hv0 : 0 ≤ TorusMetric.euclidNormVec x ^ 2 := sq_nonneg _
    have hite : |TorusMetric.euclidNormVec x ^ 2 * (if ρ = σ then 1 else 0)| ≤ 4 * ‖x‖ ^ 2 := by
      split_ifs
      · simpa [abs_of_nonneg hv0] using hsq x
      · simp
    calc _ ≤ |TorusMetric.euclidNormVec x ^ 2 * (if ρ = σ then 1 else 0)| + |x ρ * x σ| :=
          abs_sub _ _
      _ ≤ 4 * ‖x‖ ^ 2 + ‖x‖ ^ 2 := add_le_add hite hprod
      _ = 5 * ‖x‖ ^ 2 := by ring
  have hsum := (hA.trans (hA'.trans (norm_pow_isBigO_norm_pow (by norm_num)))).add hB
  refine isBigO_norm_left.1 ?_
  have hn : (fun x : AmbientSpace => ‖π ρ σ (toComplexVec x)‖) = fun x =>
      ‖Complex.exp (Complex.I * (((x ρ - x σ) / 2 : ℝ) : ℂ)) * π ρ σ (toComplexVec x)‖ := by
    funext x
    rw [norm_mul, mul_comm Complex.I, Complex.norm_exp_ofReal_mul_I, one_mul]
  rw [hn, isBigO_norm_left]
  simpa using hsum
theorem contDiffAt_comp_of_holomorphic
    (hH : Coordinates.ComplexCoordinates.PowerSeriesHolomorphy.Properties) {N : ℕ}
    {O : Set (Coordinates.ComplexCoordinates N)} {g : Coordinates.ComplexCoordinates N → ℂ}
    (hg : IsHolomorphicScalarIn O g)
    {ι : AmbientSpace → Coordinates.ComplexCoordinates N} (hι : ContDiff ℝ 2 ι) (h0 : ι 0 ∈ O) :
    ContDiffAt ℝ 2 (fun p => g (ι p)) 0 := by
  have h1 : ContDiffOn ℝ ∞ (asLine g) O := ((hH.1 N O hg.1).1 1 (asLine g) hg).2.1
  have h1' : ContDiffOn ℝ 2 (asLine g) O := by simpa using contDiffOn_infty.1 h1 2
  have h2 : ContDiffAt ℝ 2 (asLine g) (ι 0) := h1'.contDiffAt (hg.1.mem_nhds h0)
  have h3 : ContDiffAt ℝ 2 (fun p => asLine g (ι p)) 0 := h2.comp (0 : AmbientSpace) hι.contDiffAt
  exact contDiffAt_pi.1 h3 0
theorem contDiff_ofReal_coord (j : Fin 4) : ContDiff ℝ 2 fun p : AmbientSpace => ((p j : ℝ) : ℂ) :=
  Complex.ofRealCLM.contDiff.comp (contDiff_apply ℝ ℝ j)
theorem finestMesh_eq_inv_pow (L k : ℕ) : finestMesh L k = ((L : ℝ) ^ k)⁻¹ := by
  simp [finestMesh, meshAt, zpow_neg]
theorem zero_mem_freqBox {L k : ℕ} (hL : 0 < L) : (0 : Fin 4 → ℤ) ∈ PlaneWaves.freqBox L k := by
  rw [PlaneWaves.mem_freqBox]
  intro ν
  have h1 : (1 : ℝ) ≤ (L : ℝ) := by exact_mod_cast hL
  have h2 : (1 : ℝ) ≤ (finestMesh L k)⁻¹ := by
    rw [finestMesh_eq_inv_pow, inv_inv]
    exact one_le_pow₀ h1
  simp only [Pi.zero_apply, Int.cast_zero, abs_zero]
  linarith
theorem neg_mem_freqBox {L k : ℕ} {m : Fin 4 → ℤ} (hm : m ∈ PlaneWaves.freqBox L k) :
    -m ∈ PlaneWaves.freqBox L k := by apply _root_.YangMills.Construction.Tower.PeriodicMultiplierMatrices.neg_mem_freqBox <;> assumption
theorem stripHalfWidth_pos_of_subset {O : Set (Fin 4 → ℂ)} (hO : IsOpen O)
    (h0 : (0 : Fin 4 → ℂ) ∈ O) (hsub : O ⊆ momentumPolydisc stripHalfWidth) : 0 < stripHalfWidth := by
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hO 0 h0
  have hw : (fun _ => ((ε / 2 : ℝ) : ℂ) : Fin 4 → ℂ) ∈ Metric.ball (0 : Fin 4 → ℂ) ε := by
    rw [mem_ball_zero_iff, pi_norm_lt_iff hε]
    intro i
    simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (half_pos hε)]
    linarith
  have := hsub (hball hw) 0
  simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (half_pos hε)] at this
  linarith
theorem smul_shiftedFreq_mem_imStrip {δ : ℝ} (hδ : 0 ≤ δ) (η : ℝ) (p : AmbientSpace)
    (m : Fin 4 → ℤ) :
    (fun μ => (η : ℂ) * PlaneWaves.shiftedFreq (toComplexVec p) m μ) ∈ imStrip δ := by
  intro μ
  have : (η : ℂ) * PlaneWaves.shiftedFreq (toComplexVec p) m μ =
      ((η * (p μ + 2 * Real.pi * (m μ : ℝ)) : ℝ) : ℂ) := by
    simp only [PlaneWaves.shiftedFreq, toComplexVec]
    push_cast
    ring
  simp only [this, Complex.ofReal_im, abs_zero]
  exact hδ
theorem claim_holds (hS : SymbolExpansion.MassiveLogFnAsSymbolSum)
    (hI : LocallyHolomorphic.Claim)
    (hB : BackgroundCoeffsNearZero.Claim)
    (hE : Tempered.MassiveFamilyTempered)
    (hC : YangMills.Construction.OneLoopLaw.TemperedStiffness.TemperedStiffnessClaim)
    (hD : YangMills.Construction.PeriodicOperators.Tempered.HessianSymbolDetermined.Claim)
    (hH : Coordinates.ComplexCoordinates.PowerSeriesHolomorphy.Properties) : Claim := by
  intro L hL hStd k hk z hz
  have hηpos : 0 < finestMesh L k := by
    rw [finestMesh_eq_inv_pow]
    have : (0 : ℝ) < L := by exact_mod_cast hL
    positivity
  have hηne : ((finestMesh L k : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hηpos.ne'
  have hw : 0 < finestMesh L k ^ 2 * z := by positivity
  obtain ⟨hF, δ, π, e, hc⟩ := (hE L hStd _ hw).1
  obtain ⟨-, -, -, b, hT, -, hform⟩ := hC L hL hStd _ δ π e hF hc
  have hmix := (hform 0 1 (by decide)).neg_secondPartial_mixed
  obtain ⟨P₀, hP₀, -⟩ := (hD L hStd _ ⟨hF, δ, π, e, hc⟩).2
  have hPol : IsHessianSymbol L (massiveFieldFamily L (finestMesh L k ^ 2 * z))
      (hessianSymbol L (massiveFieldFamily L (finestMesh L k ^ 2 * z))) :=
    Classical.epsilon_spec ⟨P₀, hP₀⟩
  have hEq := hPol δ π e hc
  have hδ : 0 ≤ δ := hc.delta_pos.le
  obtain ⟨O, hstrip, hhol⟩ := hc.analytic
  let G : (Fin 4 → ℂ) → ℂ := fun κ => (((finestMesh L k : ℝ) : ℂ) ^ 2)⁻¹ *
    π 0 1 fun i => ((finestMesh L k : ℝ) : ℂ) * κ i
  suffices hmain : secondPartialAtZero (fun p => massiveLogFn L k p 0 1 z) 0 1 =
      secondPartialAtZero G 0 1 by
    rw [hmain]
    simp only [G]
    rw [secondPartialAtZero_const_mul, secondPartialAtZero_comp_smul]
    rw [inv_mul_cancel_left₀ (pow_ne_zero 2 hηne)]
    exact hmix
  obtain ⟨OH, ⟨w₀, hw₀, hw₀0, hw₀s⟩, H, hHol, hHval⟩ := hI L hStd k hk z hz
  let ι : AmbientSpace → Coordinates.ComplexCoordinates 5 := fun p =>
    Fin.cons (z : ℂ) (toComplexVec p)
  have hι0 : ι 0 = w₀ := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [ι, hw₀0]
    · simp [ι, hw₀s, toComplexVec_zero]
  have hιc : ContDiff ℝ 2 ι := by
    refine contDiff_pi.2 fun i => ?_
    refine Fin.cases ?_ (fun j => ?_) i
    · simpa [ι] using contDiff_const
    · simpa [ι, toComplexVec] using contDiff_ofReal_coord j
  have hιcont : Continuous ι := hιc.continuous
  obtain ⟨Ob, hObo, h0b, hsub, -, -, Cb, hCb⟩ := hB L hStd k hk
  have hwidth : 0 < massWidth z :=
    lt_min (stripHalfWidth_pos_of_subset hObo h0b hsub)
      (by have := Real.sqrt_pos.2 hz; positivity)
  have hnear₁ : ∀ᶠ p in 𝓝 (0 : AmbientSpace), ι p ∈ OH := by
    refine hιcont.continuousAt.eventually (hHol.1.mem_nhds ?_)
    rw [hι0]
    exact hw₀
  have hnear₂ : ∀ᶠ p in 𝓝 (0 : AmbientSpace), ‖p‖ < massWidth z := by
    filter_upwards [Metric.ball_mem_nhds (0 : AmbientSpace) hwidth] with p hp
    exact mem_ball_zero_iff.1 hp
  have hnear₃ : ∀ᶠ p in 𝓝 (0 : AmbientSpace), toComplexVec p ∈ Ob := by
    refine continuous_toComplexVec.continuousAt.eventually (hObo.mem_nhds ?_)
    rw [toComplexVec_zero]
    exact h0b
  have hnear₄ : ∀ᶠ p in 𝓝 (0 : AmbientSpace), -toComplexVec p ∈ Ob := by
    refine continuous_toComplexVec.neg.continuousAt.eventually (hObo.mem_nhds ?_)
    simpa [toComplexVec_zero] using h0b
  have hval : ∀ᶠ p in 𝓝 (0 : AmbientSpace),
      massiveLogFn L k (toComplexVec p) 0 1 z = H (ι p) := by
    filter_upwards [hnear₁, hnear₂] with p hp₁ hp₂
    have hreal : ι p ∈ realLocus 5 := by
      intro j
      refine Fin.cases ?_ (fun i => ?_) j
      · simp [ι]
      · simp [ι, toComplexVec]
    have h := hHval (ι p) hp₁ hreal (by simpa [ι] using hz) (fun μ => by
      simpa [ι] using lt_of_le_of_lt (norm_toComplexVec_apply_le p μ) hp₂)
    have hpt : (fun μ : Fin 4 => ι p μ.succ) = toComplexVec p := by
      funext μ
      simp [ι]
    rw [h, hpt]
    simp [ι]
  let ι₂ : AmbientSpace → Coordinates.ComplexCoordinates 4 := fun p i =>
    ((finestMesh L k : ℝ) : ℂ) * toComplexVec p i
  have hι₂ : ContDiff ℝ 2 ι₂ := by
    refine contDiff_pi.2 fun i => contDiff_const.mul ?_
    simpa [toComplexVec] using contDiff_ofReal_coord i
  have hι₂0 : ι₂ 0 ∈ O := by
    apply hstrip
    intro μ
    simp [ι₂, toComplexVec, hδ]
  let ρ₂ : AmbientSpace → ℂ := fun p => (((finestMesh L k : ℝ) : ℂ) ^ 2)⁻¹ * π 0 1 (ι₂ p)
  have hc₂ : ContDiffAt ℝ 2 ρ₂ 0 :=
    contDiffAt_const.mul (contDiffAt_comp_of_holomorphic hH (hhol 0 1).1 hι₂ hι₂0)
  have hc₁ : ContDiffAt ℝ 2 (fun p => H (ι p)) 0 :=
    contDiffAt_comp_of_holomorphic hH hHol hιc (by rw [hι0]; exact hw₀)
  refine secondPartialAtZero_eq_of_isBigO_cube hval (Eventually.of_forall fun _ => rfl)
    hc₁ hc₂ ?_ 0 1
  let Pm : (Fin 4 → ℤ) → Fin 4 → Fin 4 → AmbientSpace → ℂ := fun m ρ σ p =>
    π ρ σ fun μ => ((finestMesh L k : ℝ) : ℂ) * PlaneWaves.shiftedFreq (toComplexVec p) m μ
  let bp : AmbientSpace → Fin 4 → (Fin 4 → ℤ) → ℂ := fun p ρ m =>
    backgroundCoeff L k (toComplexVec p) 0 ρ m
  let bm : AmbientSpace → Fin 4 → (Fin 4 → ℤ) → ℂ := fun p σ m =>
    backgroundCoeff L k (-toComplexVec p) 1 σ m
  have hqPlus : ∀ (p : AmbientSpace) (i : Fin 4), ‖toComplexVec p i‖ ≤ ‖p‖ :=
    norm_toComplexVec_apply_le
  have hqMinus : ∀ (p : AmbientSpace) (i : Fin 4), ‖(-toComplexVec p) i‖ ≤ ‖p‖ := fun p i => by
    simpa using norm_toComplexVec_apply_le p i
  have hPb : ∀ m ρ σ, Pm m ρ σ =O[𝓝 0] fun _ => (1 : ℝ) := by
    intro m ρ σ
    obtain ⟨C, hC'⟩ := (hhol ρ σ).2
    refine IsBigO.of_bound C (Eventually.of_forall fun p => ?_)
    simpa [Pm] using hC' _ (hstrip (smul_shiftedFreq_mem_imStrip hδ (finestMesh L k) p m))
  have hP0 : ∀ ρ σ, Pm 0 ρ σ =O[𝓝 0] fun p => ‖p‖ ^ 2 := by
    intro ρ σ
    have hscale : Tendsto (fun p : AmbientSpace => finestMesh L k • p) (𝓝 0) (𝓝 0) := by
      have : Continuous fun p : AmbientSpace => finestMesh L k • p := by fun_prop
      simpa using this.tendsto 0
    have h1 := (entry_isBigO_sq_of_transverseForm hT ρ σ).comp_tendsto hscale
    have h2 : (fun p : AmbientSpace => ‖finestMesh L k • p‖ ^ 2) =O[𝓝 0] fun p => ‖p‖ ^ 2 := by
      refine IsBigO.of_bound (finestMesh L k ^ 2) (Eventually.of_forall fun p => ?_)
      simp [norm_smul, mul_pow, abs_of_pos hηpos]
    refine (h1.trans h2).congr' (Eventually.of_forall fun p => ?_) EventuallyEq.rfl
    have hpt : toComplexVec (finestMesh L k • p) = fun μ => ((finestMesh L k : ℝ) : ℂ) *
        PlaneWaves.shiftedFreq (toComplexVec p) 0 μ := by
      funext μ
      simp [toComplexVec, PlaneWaves.shiftedFreq]
    simp only [Function.comp, Pm]
    rw [hpt]
  have hbp : ∀ m ∈ PlaneWaves.freqBox L k, m ≠ 0 → ∀ ρ,
      (fun p => bp p ρ m) =O[𝓝 0] fun p => ‖p‖ ^ 2 := by
    intro m hm hm0 ρ
    refine isBigO_norm_pow_of_euclidNorm_bound (C := Cb) hqPlus ?_
    filter_upwards [hnear₃] with p hp
    exact (hCb _ hp 0 ρ).1 m hm hm0
  have hbm : ∀ m ∈ PlaneWaves.freqBox L k, m ≠ 0 → ∀ σ,
      (fun p => bm p σ (-m)) =O[𝓝 0] fun p => ‖p‖ ^ 2 := by
    intro m hm hm0 σ
    refine isBigO_norm_pow_of_euclidNorm_bound (C := Cb) hqMinus ?_
    filter_upwards [hnear₄] with p hp
    exact (hCb _ hp 1 σ).1 (-m) (neg_mem_freqBox hm) (neg_ne_zero.2 hm0)
  have hbp0 : ∀ ρ, (fun p => bp p ρ 0 - if ρ = 0 then 1 else 0) =O[𝓝 0] fun p => ‖p‖ ^ 1 := by
    intro ρ
    refine isBigO_norm_pow_of_euclidNorm_bound (C := Cb) hqPlus ?_
    filter_upwards [hnear₃] with p hp
    simpa using (hCb _ hp 0 ρ).2
  have hbm0 : ∀ σ, (fun p => bm p σ 0 - if σ = 1 then 1 else 0) =O[𝓝 0] fun p => ‖p‖ ^ 1 := by
    intro σ
    refine isBigO_norm_pow_of_euclidNorm_bound (C := Cb) hqMinus ?_
    filter_upwards [hnear₄] with p hp
    simpa using (hCb _ hp 1 σ).2
  have hsum := symbolSum_sub_isBigO_cube (zero_mem_freqBox hL) Pm bp bm hPb hP0 hbp hbm hbp0 hbm0
  refine (hsum.const_mul_left ((((finestMesh L k : ℝ) : ℂ) ^ 2)⁻¹)).congr' ?_ EventuallyEq.rfl
  filter_upwards [hval, hnear₂] with p hp₁ hp₂
  have hmem : toComplexVec p ∈ momentumPolydisc (massWidth z) := fun μ =>
    (norm_toComplexVec_apply_le p μ).trans hp₂.le
  have hrep := hS L hStd k hk z hz p hmem 0 1
  have hsumEq : ∑ m ∈ PlaneWaves.freqBox L k, ∑ ρ : Fin 4, ∑ σ : Fin 4,
        hessianSymbol L (massiveFieldFamily L (finestMesh L k ^ 2 * z)) ρ σ
            (fun μ => ((finestMesh L k : ℝ) : ℂ) *
              PlaneWaves.shiftedFreq (toComplexVec p) m μ) *
          backgroundCoeff L k (toComplexVec p) 0 ρ m *
          backgroundCoeff L k (-toComplexVec p) 1 σ (-m) =
      ∑ m ∈ PlaneWaves.freqBox L k, ∑ ρ : Fin 4, ∑ σ : Fin 4,
        Pm m ρ σ p * bp p ρ m * bm p σ (-m) := by
    refine Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun ρ _ =>
      Finset.sum_congr rfl fun σ _ => ?_
    rw [hEq ρ σ (smul_shiftedFreq_mem_imStrip hδ (finestMesh L k) p m)]
  have hshift : Pm 0 0 1 p = π 0 1 (ι₂ p) := by
    simp only [Pm, ι₂]
    congr 1
    funext μ
    simp [PlaneWaves.shiftedFreq]
  rw [← hp₁, hrep, hsumEq, hshift, mul_sub]
end YangMills.Construction.Tower.MassiveOpFunctions.MixedPartialOfMassiveLogFn
end
