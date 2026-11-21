import YangMills.Construction.ClusterExpansionOfAStep.AMoveReadAtZero
import YangMills.Construction.ClusterExpansionOfAStep.JetsOfTheExponential
import YangMills.Construction.ClusterExpansionOfAStep.LeastLogNearOne
import YangMills.Construction.ClusterExpansionOfAStep.MarkAlongAMove
import YangMills.Construction.ColdChainAtEveryLevel.LeastQuarticGaugeProof
import YangMills.Construction.ColdChainAtEveryLevel.TermsAgainstTheirFirstOrderProof
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion Topology
open Filter
namespace YangMills.Construction.TorusLumps
open BlockAverages GaugeFixing LumpContours BondMoves QuaternionExponential QuaternionLog
theorem norm_coe_unitQuaternion (g : UnitQuaternion) : ‖(g : ℍ[ℝ])‖ = 1 := by apply _root_.YangMills.Construction.BlockAverages.norm_coe_unitQuaternion <;> assumption
theorem norm_sub_one_sq_of_norm_eq_one (q : ℍ[ℝ]) (hq : ‖q‖ = 1) : ‖q - 1‖ ^ 2 = 2 - 2 * q.re := by apply _root_.YangMills.Construction.BlockAverages.TermwiseBounds.norm_sub_one_sq_of_norm_eq_one <;> assumption
theorem norm_expUnit_sub_one_le (w : imaginaryQuaternions) (hw : ‖(w : ℍ[ℝ])‖ ≤ 65 / 64) :
    ‖((expUnit w : UnitQuaternion) : ℍ[ℝ]) - 1‖ ≤ 985 / 1000 := by
  have hre : ((expUnit w : UnitQuaternion) : ℍ[ℝ]).re = Real.cos ‖(w : ℍ[ℝ])‖ := by
    have h : NormedSpace.exp (w : ℍ[ℝ]) =
        ((Real.cos ‖(w : ℍ[ℝ])‖ : ℝ) : ℍ[ℝ]) + (Real.sin ‖(w : ℍ[ℝ])‖ / ‖(w : ℍ[ℝ])‖) • (w : ℍ[ℝ]) :=
      Quaternion.exp_of_re_eq_zero _ w.2
    have hw0 : (w : ℍ[ℝ]).re = 0 := w.2
    show (NormedSpace.exp (w : ℍ[ℝ])).re = _
    rw [h]
    simp [hw0]
  have hsq := norm_sub_one_sq_of_norm_eq_one _ (_root_.YangMills.Construction.TorusLumps.norm_coe_unitQuaternion (expUnit w))
  rw [hre] at hsq
  set θ := ‖(w : ℍ[ℝ])‖ with hθ
  have hθ0 : 0 ≤ θ := norm_nonneg _
  have h1 := Real.one_sub_sq_div_two_le_cos (x := θ / 2)
  have hc : (871 : ℝ) / 1000 ≤ Real.cos (θ / 2) := by nlinarith
  have h2 : Real.cos θ = 2 * Real.cos (θ / 2) ^ 2 - 1 := by
    rw [← Real.cos_two_mul]
    ring_nf
  have h3 : (2 : ℝ) - 2 * Real.cos θ ≤ (985 / 1000) ^ 2 := by
    rw [h2]
    nlinarith
  exact (sq_le_sq₀ (norm_nonneg _) (by norm_num)).mp (hsq ▸ h3)
theorem inv_expUnit (w : imaginaryQuaternions) : (expUnit w)⁻¹ = expUnit (-w) := by apply _root_.YangMills.Construction.LeastQuarticGauge.expUnit_inv <;> assumption
theorem logMarkSmoothness_of_bounds (he : IteratedDerivBounded) (hl : MinimalLogAnalyticNearOne) :
    LogMarkSmoothness := by
  classical
  obtain ⟨Lg, hLg, hL⟩ := hl
  choose C hC0 hC using he
  intro ψ ρ hρ hψ hB hz
  choose Bψ hBψ using hB
  set t : Set ℍ[ℝ] := Metric.ball 1 1 with ht
  have htopen : IsOpen t := Metric.isOpen_ball
  have htud : UniqueDiffOn ℝ t := htopen.uniqueDiffOn
  have hLgT : ContDiffOn ℝ ⊤ Lg t := fun x hx => (hLg x hx).contDiffAt.contDiffWithinAt
  have hK : IsCompact (Metric.closedBall (1 : ℍ[ℝ]) (99 / 100)) := isCompact_closedBall _ _
  have hKt : Metric.closedBall (1 : ℍ[ℝ]) (99 / 100) ⊆ t := Metric.closedBall_subset_ball (by norm_num)
  have hjet : ∀ i : ℕ, ∃ c : ℝ, ∀ q ∈ Metric.closedBall (1 : ℍ[ℝ]) (99 / 100),
      ‖iteratedFDerivWithin ℝ i Lg t q‖ ≤ c := fun i =>
    hK.exists_bound_of_continuousOn
      ((hLgT.continuousOn_iteratedFDerivWithin (by exact_mod_cast le_top) htud).mono hKt)
  choose CLf hCLf using hjet
  set CL : ℝ := ∑ i ∈ Finset.range 41, |CLf i| with hCLdef
  set Bs : ℝ := ∑ i ∈ Finset.range 41, |Bψ i| with hBs
  have hCL0 : 0 ≤ CL := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hBs0 : 0 ≤ Bs := Finset.sum_nonneg fun _ _ => abs_nonneg _
  let Dq : ℝ → ℝ := fun S => 1 + ∑ i ∈ Finset.range 41, C i * |S| ^ i
  have hDq1 : ∀ S, 1 ≤ Dq S := fun S => by
    have : 0 ≤ ∑ i ∈ Finset.range 41, C i * |S| ^ i :=
      Finset.sum_nonneg fun i _ => mul_nonneg (hC0 i) (by positivity)
    simp only [Dq]
    linarith
  let Dh : ℝ → ℝ → ℝ := fun F S => 1 + (Nat.factorial 40 : ℝ) * CL * Dq S ^ 40 + |F|
  have hDh1 : ∀ F S, 1 ≤ Dh F S := fun F S => by
    have h1 : 0 ≤ (Nat.factorial 40 : ℝ) * CL * Dq S ^ 40 := by
      have := hDq1 S
      positivity
    have h2 := abs_nonneg F
    simp only [Dh]
    linarith
  have hcomp : ∀ {k : ℕ} (h : (Fin k → ℝ) → ℍ[ℝ]) (s : Set (Fin k → ℝ)) (τ : Fin k → ℝ) (Dd : ℝ), IsOpen s → τ ∈ s →
      ContDiffOn ℝ 40 h s → 1 ≤ Dd → (∀ i, 1 ≤ i → i ≤ 40 → ‖iteratedFDeriv ℝ i h τ‖ ≤ Dd) →
      ∀ j, 1 ≤ j → j ≤ 40 → ‖iteratedFDeriv ℝ j (ψ ∘ h) τ‖ ≤ (Nat.factorial 40 : ℝ) * Bs * Dd ^ 40 := by
    intro k h s τ Dd hs hτ hh hDd hjets j hj1 hj40
    have hj' : ((j : ℕ) : WithTop ℕ∞) ≤ 40 := by exact_mod_cast hj40
    have hm := norm_iteratedFDerivWithin_comp_le (g := ψ) (f := h) (n := j) (s := s) (t := Set.univ) (x := τ) (N := 40)
      (C := Bs) (D := Dd) hψ.contDiffOn hh hj' uniqueDiffOn_univ hs.uniqueDiffOn (fun _ _ => trivial) hτ
      (fun i hi => by
        rw [iteratedFDerivWithin_univ]
        refine (hBψ i _).trans ((le_abs_self _).trans ?_)
        exact Finset.single_le_sum (f := fun i => |Bψ i|) (fun _ _ => abs_nonneg _)
          (Finset.mem_range.mpr (by omega)))
      (fun i hi1 hi2 => by
        rw [iteratedFDerivWithin_of_isOpen i hs hτ]
        exact (hjets i hi1 (by omega)).trans (le_self_pow₀ hDd (by omega)))
    rw [iteratedFDerivWithin_of_isOpen j hs hτ] at hm
    refine hm.trans ?_
    have h1 : (Nat.factorial j : ℝ) ≤ Nat.factorial 40 := by exact_mod_cast Nat.factorial_le hj40
    have h2 : Dd ^ j ≤ Dd ^ 40 := pow_le_pow_right₀ hDd hj40
    have h3 : 0 ≤ Dd ^ j := by positivity
    exact mul_le_mul (mul_le_mul_of_nonneg_right h1 hBs0) h2 h3 (by positivity)
  refine ⟨fun F S => (Nat.factorial 40 : ℝ) * Bs * Dh F S ^ 40, ?_⟩
  intro k U f hU hf hf1
  refine ⟨fun Ξ g => ?_, fun a₀ => ?_⟩
  · let qv : (Fin k → ℝ) → ℍ[ℝ] := fun τ => ((g * (expUnit (Ξ τ))⁻¹ : UnitQuaternion) : ℍ[ℝ])
    let Lm : ℍ[ℝ] →L[ℝ] ℍ[ℝ] := ContinuousLinearMap.mul ℝ ℍ[ℝ] (g : ℍ[ℝ])
    have hqv : qv = Lm ∘ fun τ => NormedSpace.exp (((-Ξ) τ : imaginaryQuaternions) : ℍ[ℝ]) := by
      funext τ
      simp only [qv, inv_expUnit, Function.comp]
      rfl
    have hexpS : ContDiff ℝ ⊤ fun τ => NormedSpace.exp (((-Ξ) τ : imaginaryQuaternions) : ℍ[ℝ]) :=
      contDiff_exp_imaginary.comp (-Ξ).contDiff
    have hqs : ContDiff ℝ ⊤ qv := by
      rw [hqv]
      exact Lm.contDiff.comp hexpS
    have hLn : ‖Lm‖ ≤ 1 := by
      refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun q => ?_
      simp only [Lm, ContinuousLinearMap.mul_apply']
      rw [norm_mul, _root_.YangMills.Construction.TorusLumps.norm_coe_unitQuaternion]
    have hqj : ∀ (i : ℕ) (τ : Fin k → ℝ) (S : ℝ), ‖Ξ‖ ≤ S → ‖iteratedFDeriv ℝ i qv τ‖ ≤ C i * |S| ^ i := by
      intro i τ S hS
      rw [hqv]
      have hcd : ContDiffAt ℝ i (fun τ => NormedSpace.exp (((-Ξ) τ : imaginaryQuaternions) : ℍ[ℝ])) τ :=
        (hexpS.of_le le_top).contDiffAt
      refine (Lm.norm_iteratedFDeriv_comp_left hcd le_rfl).trans ?_
      have h1 := norm_iteratedFDeriv_exp_comp_le (-Ξ) (hC i) τ
      have h2 : ‖-Ξ‖ ≤ |S| := by
        refine ContinuousLinearMap.opNorm_le_bound _ (abs_nonneg S) fun v => ?_
        rw [neg_apply, norm_neg]
        exact (Ξ.le_opNorm v).trans (mul_le_mul_of_nonneg_right (hS.trans (le_abs_self S)) (norm_nonneg v))
      have h3 : C i * ‖-Ξ‖ ^ i ≤ C i * |S| ^ i :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (ContinuousLinearMap.opNorm_nonneg _) h2 i) (hC0 i)
      calc ‖Lm‖ * ‖iteratedFDeriv ℝ i (fun τ => NormedSpace.exp (((-Ξ) τ : imaginaryQuaternions) : ℍ[ℝ])) τ‖
          ≤ 1 * (C i * |S| ^ i) := mul_le_mul hLn (h1.trans h3) (norm_nonneg _) zero_le_one
        _ = C i * |S| ^ i := one_mul _
    have hcont : Continuous fun τ => ‖qv τ - 1‖ := (hqs.continuous.sub continuous_const).norm
    have key : ∀ τ₁ ∈ U, ContDiffAt ℝ 40 (markAlongLog ψ Ξ g f) τ₁ ∧ ∀ F S : ℝ, ‖Ξ‖ ≤ S →
        (∀ i, 1 ≤ i → i ≤ 40 → ‖iteratedFDeriv ℝ i f τ₁‖ ≤ F) → ∀ j, 1 ≤ j → j ≤ 40 →
        ‖iteratedFDeriv ℝ j (markAlongLog ψ Ξ g f) τ₁‖ ≤ (Nat.factorial 40 : ℝ) * Bs * Dh F S ^ 40 := by
      intro τ₁ hτ₁
      by_cases hnear : ‖qv τ₁ - 1‖ < 99 / 100
      · let s : Set (Fin k → ℝ) := U ∩ {τ | ‖qv τ - 1‖ < 99 / 100}
        have hso : IsOpen s := hU.inter (isOpen_lt hcont continuous_const)
        have hτs : τ₁ ∈ s := ⟨hτ₁, hnear⟩
        have hst : Set.MapsTo qv s t := fun τ hτ => by
          have h1 : ‖qv τ - 1‖ < 99 / 100 := hτ.2
          rw [ht, Metric.mem_ball, dist_eq_norm]
          linarith
        have hLq : ContDiffOn ℝ 40 (fun τ => Lg (qv τ)) s :=
          (hLgT.of_le le_top).comp (hqs.contDiffOn.of_le le_top) hst
        let h₁ : (Fin k → ℝ) → ℍ[ℝ] := fun τ => Lg (qv τ) + -f τ
        have hh₁ : ContDiffOn ℝ 40 h₁ s := hLq.add (hf.mono Set.inter_subset_left).neg
        have heq : markAlongLog ψ Ξ g f =ᶠ[𝓝 τ₁] ψ ∘ h₁ := by
          refine Filter.eventually_of_mem (hso.mem_nhds hτs) fun τ hτ => ?_
          have h1 : ‖qv τ - 1‖ < 1 := lt_trans hτ.2 (by norm_num)
          have h2 := hL (g * (expUnit (Ξ τ))⁻¹) h1
          simp only [markAlongLog, Function.comp, h₁]
          rw [h2, sub_eq_add_neg]
        refine ⟨((hψ.comp_contDiffOn hh₁).contDiffAt (hso.mem_nhds hτs)).congr_of_eventuallyEq heq,
          fun F S hS hF j hj1 hj40 => ?_⟩
        have hjets : ∀ i, 1 ≤ i → i ≤ 40 → ‖iteratedFDeriv ℝ i h₁ τ₁‖ ≤ Dh F S := by
          intro i hi1 hi2
          have hi' : ((i : ℕ) : WithTop ℕ∞) ≤ 40 := by exact_mod_cast hi2
          have hLat : ContDiffAt ℝ i (fun τ => Lg (qv τ)) τ₁ := (hLq.of_le hi').contDiffAt (hso.mem_nhds hτs)
          have hfat : ContDiffAt ℝ i f τ₁ := (hf.of_le hi').contDiffAt (hU.mem_nhds hτ₁)
          have e : iteratedFDeriv ℝ i h₁ τ₁ =
              iteratedFDeriv ℝ i (fun τ => Lg (qv τ)) τ₁ + -iteratedFDeriv ℝ i f τ₁ := by
            have h2 := fun_iteratedFDeriv_add_apply hLat hfat.neg
            have h3 : iteratedFDeriv ℝ i (fun τ => -f τ) τ₁ = -iteratedFDeriv ℝ i f τ₁ := iteratedFDeriv_neg_apply
            rw [h3] at h2
            exact h2
          have hmL : ‖iteratedFDeriv ℝ i (fun τ => Lg (qv τ)) τ₁‖ ≤ (Nat.factorial i : ℝ) * CL * Dq S ^ i := by
            have hm := norm_iteratedFDerivWithin_comp_le (g := Lg) (f := qv) (n := i) (s := s) (t := t) (x := τ₁)
              (N := 40) (C := CL) (D := Dq S) (hLgT.of_le le_top) (hqs.contDiffOn.of_le le_top) hi' htud
              hso.uniqueDiffOn hst hτs
              (fun i' hi'' => by
                have hmem : qv τ₁ ∈ Metric.closedBall (1 : ℍ[ℝ]) (99 / 100) := by
                  rw [Metric.mem_closedBall, dist_eq_norm]
                  exact hnear.le
                refine (hCLf i' _ hmem).trans ((le_abs_self _).trans ?_)
                exact Finset.single_le_sum (f := fun i => |CLf i|) (fun _ _ => abs_nonneg _)
                  (Finset.mem_range.mpr (by omega)))
              (fun i' hi1' hi2' => by
                rw [iteratedFDerivWithin_of_isOpen i' hso hτs]
                refine (hqj i' τ₁ S hS).trans (le_trans ?_ (le_self_pow₀ (hDq1 S) (by omega)))
                have h5 := Finset.single_le_sum (f := fun i => C i * |S| ^ i)
                  (fun i _ => mul_nonneg (hC0 i) (by positivity))
                  (Finset.mem_range.mpr (show i' < 41 by omega))
                simp only [Dq]
                linarith)
            rw [iteratedFDerivWithin_of_isOpen i hso hτs] at hm
            exact hm
          have hF' := hF i hi1 hi2
          have hDS := hDq1 S
          have e3 : (Nat.factorial i : ℝ) * CL * Dq S ^ i ≤ (Nat.factorial 40 : ℝ) * CL * Dq S ^ 40 := by
            have h1 : (Nat.factorial i : ℝ) ≤ Nat.factorial 40 := by exact_mod_cast Nat.factorial_le hi2
            have h2 : Dq S ^ i ≤ Dq S ^ 40 := pow_le_pow_right₀ hDS hi2
            exact mul_le_mul (mul_le_mul_of_nonneg_right h1 hCL0) h2 (by positivity) (by positivity)
          rw [e]
          refine (norm_add_le _ _).trans ?_
          rw [norm_neg]
          have h2 := le_abs_self F
          simp only [Dh]
          linarith
        rw [(Filter.EventuallyEq.iteratedFDeriv (𝕜 := ℝ) heq j).eq_of_nhds]
        exact hcomp h₁ s τ₁ (Dh F S) hso hτs hh₁ (hDh1 F S) hjets j hj1 hj40
      · let s : Set (Fin k → ℝ) := {τ | 985 / 1000 < ‖qv τ - 1‖}
        have hso : IsOpen s := isOpen_lt continuous_const hcont
        have hτs : τ₁ ∈ s := by
          show 985 / 1000 < ‖qv τ₁ - 1‖
          have := not_lt.mp hnear
          linarith
        have hzero : markAlongLog ψ Ξ g f =ᶠ[𝓝 τ₁] fun _ => 0 := by
          refine Filter.eventually_of_mem ((hU.inter hso).mem_nhds ⟨hτ₁, hτs⟩) fun τ hτ => ?_
          have hlong : 65 / 64 < ‖((minimalLog (g * (expUnit (Ξ τ))⁻¹) : imaginaryQuaternions) : ℍ[ℝ])‖ := by
            by_contra hcon
            have h1 := norm_expUnit_sub_one_le _ (not_lt.mp hcon)
            rw [expUnit_minimalLog] at h1
            have h2 : 985 / 1000 < ‖qv τ - 1‖ := hτ.2
            exact absurd h1 (not_le.mpr h2)
          have h3 := hf1 τ hτ.1
          apply hz
          have h4 := norm_sub_norm_le ((minimalLog (g * (expUnit (Ξ τ))⁻¹) : imaginaryQuaternions) : ℍ[ℝ]) (f τ)
          linarith
        refine ⟨contDiffAt_const.congr_of_eventuallyEq hzero, fun F S _ _ j hj1 _ => ?_⟩
        rw [(Filter.EventuallyEq.iteratedFDeriv (𝕜 := ℝ) hzero j).eq_of_nhds,
          iteratedFDeriv_const_of_ne (by omega)]
        have := hDh1 F S
        simp only [Pi.zero_apply, norm_zero]
        positivity
    exact ⟨fun τ hτ => (key τ hτ).1.contDiffWithinAt,
      fun τ hτ F S hS hF j hj1 hj40 => (key τ hτ).2 F S hS hF j hj1 hj40⟩
  · have hsm : ContDiffOn ℝ 40 (fun τ => a₀ - f τ) U := contDiffOn_const.sub hf
    refine ⟨hψ.comp_contDiffOn hsm, fun τ hτ F S hF j hj1 hj40 => ?_⟩
    have hjets : ∀ i, 1 ≤ i → i ≤ 40 → ‖iteratedFDeriv ℝ i (fun τ => a₀ - f τ) τ‖ ≤ 1 + |F| := by
      intro i hi1 hi2
      obtain ⟨i', rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
      have e : fderiv ℝ (fun τ => a₀ - f τ) = -fderiv ℝ f := by
        funext σ
        simpa using fderiv_const_sub (𝕜 := ℝ) (f := f) (x := σ) a₀
      rw [← norm_iteratedFDeriv_fderiv, e, iteratedFDeriv_neg_apply, norm_neg, norm_iteratedFDeriv_fderiv]
      have := hF (i' + 1) hi1 hi2
      have h2 := le_abs_self F
      linarith
    have h1 : (1 : ℝ) ≤ 1 + |F| := by
      have := abs_nonneg F
      linarith
    refine (hcomp _ U τ (1 + |F|) hU hτ hsm h1 hjets j hj1 hj40).trans ?_
    refine mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by linarith) ?_ 40) (by positivity)
    have : 0 ≤ (Nat.factorial 40 : ℝ) * CL * Dq S ^ 40 := by
      have := hDq1 S
      positivity
    simp only [Dh]
    linarith
end YangMills.Construction.TorusLumps
end
