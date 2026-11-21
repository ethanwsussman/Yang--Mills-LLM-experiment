import YangMills.Construction.ClusterExpansionOfAStep.FormOfTheShares
import YangMills.Construction.SummableBoundsOfTheFlow.TheSharesAtDrawnParametersProof
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion Topology
namespace YangMills.Construction.ShareFamilies
open YangMills.Construction.BlockAverages YangMills.Construction.TorusLumps YangMills.Construction.TorusFields YangMills.Construction.PlaneFields YangMills.Construction.RenormalizationStepParameters
theorem norm_quaternionI : ‖quaternionI‖ = 1 := by apply _root_.YangMills.SharedProofs.p9532 <;> assumption
theorem curvatureAlong_quaternionI_planeForm :
    curvatureAlong quaternionI (planeForm 0 1) = unitPlaneCurvature := by
  funext i j
  fin_cases i <;> fin_cases j <;> simp [curvatureAlong, planeForm, unitPlaneCurvature, planeCurvature]
  exact neg_one_smul ℝ quaternionI
theorem planeForm_zero_one_antisymm (i j : Fin 4) : planeForm 0 1 i j = - planeForm 0 1 j i := by
  fin_cases i <;> fin_cases j <;> simp [planeForm]
theorem planeForm_zero_one_integral (i j : Fin 4) :
    ∃ k : ℤ, ((1 : ℕ) : ℝ) * planeForm 0 1 i j = k := by apply _root_.YangMills.SharedProofs.p6658 <;> assumption
theorem unitPlaneCurvature_antisymm (μ ν : Fin 4) :
    unitPlaneCurvature μ ν = - unitPlaneCurvature ν μ := by apply _root_.YangMills.SharedProofs.p4715 <;> assumption
theorem curvaturePairing_unitPlaneCurvature_self :
    curvaturePairing unitPlaneCurvature unitPlaneCurvature = 1 := by apply _root_.YangMills.SharedProofs.p11741 <;> assumption
theorem eventually_norm_expUnit_smul_sub_one_lt (X : imaginaryQuaternions) {s : ℝ} (hs : 0 < s) :
    ∀ᶠ τ : ℝ in 𝓝 0, ‖((expUnit (τ • X) : UnitQuaternion) : ℍ[ℝ]) - 1‖ < s := by apply _root_.YangMills.SharedProofs.p49248 <;> assumption
theorem tendsto_two_pi_div_sq : Filter.Tendsto (fun n : ℕ => 2 * Real.pi * ((1 : ℕ) : ℝ) / (n : ℝ) ^ 2)
    Filter.atTop (𝓝 0) := by
  have h1 : Filter.Tendsto (fun n : ℕ => ((n : ℝ)) ^ 2) Filter.atTop Filter.atTop :=
    (Filter.tendsto_pow_atTop (by norm_num)).comp tendsto_natCast_atTop_atTop
  exact h1.const_div_atTop _
theorem abs_one_sub_le_of_action_near_shares {M n θ γ ε v A : ℝ} (hMθ : M ^ 2 * θ = 2 * Real.pi)
    (hnγ : n ^ 2 * γ = 2 * Real.pi)
    (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) (hθγ : θ ≤ γ) (hγε : γ ^ 2 ≤ ε)
    (hA : A = M ^ 4 * (1 - Real.cos θ))
    (hS : |A - n ^ 4 * (γ ^ 2 / 2 * v)| ≤ n ^ 4 * (ε * γ ^ 2)) : |1 - v| ≤ 3 * ε := by exact @_root_.YangMills.SharedProofs.p38896 M n θ γ ε v A hMθ hnγ hθ0 hθ1 hθγ hγε hA hS
theorem levelSharesHaveUnitCurvatureForm_of_parts (h1 : InvariantFamilyCurvatureForm)
    (h2 : SecondOrderAtAbelianFields) (h3 : LevelSharesFormCurvatureFamily)
    (h4 : LeastActionAtPlaneField) :
    LevelSharesHaveUnitCurvatureForm := by
  intro T hD t
  obtain ⟨γ₀, hγ₀, hLA⟩ := h4 T hD
  have hF := hD.fits T.floorMin le_rfl
  obtain ⟨hfam, hcar, hsum⟩ := h3 T hD T.floorMin le_rfl t
  obtain ⟨hT, b, hb⟩ := h1 _ hF _ _ hfam hcar
  have hLim : HasLimitSecondDeriv (levelShareFamily T.coupling T.side (t + 1)) :=
    fun c c' X X' => ⟨_, hT c c' X X'⟩
  obtain ⟨-, -, -, -, -, -, -, hE⟩ := h2 _ hF _ _ hfam
  obtain ⟨v, hv, hvε⟩ := hE (planeForm 0 1) 1 quaternionI planeForm_zero_one_antisymm one_pos
    planeForm_zero_one_integral norm_quaternionI
  rw [curvatureAlong_quaternionI_planeForm] at hv
  have hb1 := hb unitPlaneCurvature unitPlaneCurvature unitPlaneCurvature_antisymm
    unitPlaneCurvature_antisymm
  rw [curvaturePairing_unitPlaneCurvature_self, mul_one] at hb1
  have hvb : v = b := hv.unique hb1
  have hv1 : v = 1 := by
    by_contra hne
    have hpos : 0 < |1 - v| := abs_pos.mpr (sub_ne_zero.mpr (Ne.symm hne))
    set ε := |1 - v| / 4 with hεdef
    have hε0 : 0 < ε := by positivity
    obtain ⟨n₁, hn₁⟩ := hvε ε hε0
    have hc : 0 < min γ₀ (min 1 ε) := lt_min hγ₀ (lt_min one_pos hε0)
    obtain ⟨n, hg, hcold1, hnn, hn1, hn64⟩ :=
      ((tendsto_two_pi_div_sq.eventually (gt_mem_nhds hc)).and
        ((tendsto_two_pi_div_sq.eventually
            (eventually_norm_expUnit_smul_sub_one_lt quaternionI hD.σ_pos)).and
          ((Filter.eventually_ge_atTop T.n₀).and
            ((Filter.eventually_ge_atTop n₁).and (Filter.eventually_ge_atTop 64))))).exists
    haveI : NeZero n := ⟨by omega⟩
    have hnpos : (0 : ℝ) < n := by
      have : 0 < n := by omega
      exact_mod_cast this
    set γ : ℝ := 2 * Real.pi * ((1 : ℕ) : ℝ) / (n : ℝ) ^ 2 with hγdef
    have hγ0 : 0 ≤ γ := by positivity
    have hg0 : γ ≤ γ₀ := le_of_lt (lt_of_lt_of_le hg (min_le_left _ _))
    have hg2 : γ < 1 := lt_of_lt_of_le hg ((min_le_right _ _).trans (min_le_left _ _))
    have hg3 : γ < ε := lt_of_lt_of_le hg ((min_le_right _ _).trans (min_le_right _ _))
    obtain ⟨V, hV, hact⟩ := hLA t n 1 quaternionI 0 1 hn64 norm_quaternionI (by decide) hg0
    have hcold : IsCold T.threshold V := by
      intro x μ ν hμν
      unfold curvature
      rw [hV.2 x μ ν hμν]
      by_cases h01 : μ = 0 ∧ ν = 1
      · have e : γ * planeForm 0 1 μ ν = γ := by simp [planeForm, h01.1, h01.2]
        rw [e]
        exact hcold1
      · have e : planeForm 0 1 μ ν = 0 := by
          unfold planeForm
          rw [if_neg h01, if_neg]
          rintro ⟨rfl, rfl⟩
          exact absurd hμν (by decide)
        rw [e, mul_zero, zero_smul]
        simpa [expUnit] using hD.σ_pos
    have hs := hsum n hnn V hcold
    rw [hact] at hs
    have hY := fun Y => hn₁ n hn1 V hV Y
    have hcard : (Fintype.card (TorusSite n) : ℝ) = (n : ℝ) ^ 4 := by
      simp [ZMod.card]
    have hsumb : |∑ z, centered (levelShareFamily T.coupling T.side (t + 1)) n z V -
        (n : ℝ) ^ 4 * (γ ^ 2 / 2 * v)| ≤ (n : ℝ) ^ 4 * (ε * γ ^ 2) := by
      have e1 : ∑ z, centered (levelShareFamily T.coupling T.side (t + 1)) n z V -
          (n : ℝ) ^ 4 * (γ ^ 2 / 2 * v) =
          ∑ z : TorusSite n,
            (centered (levelShareFamily T.coupling T.side (t + 1)) n z V - γ ^ 2 / 2 * v) := by
        rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hcard]
      rw [e1]
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      refine (Finset.sum_le_sum fun z _ => hY z).trans (le_of_eq ?_)
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hcard]
    set N : ℝ := (T.side : ℝ) ^ (t + 1) with hN
    have hN1 : 1 ≤ N :=
      one_le_pow₀ (by exact_mod_cast (by have := hD.L_ge; omega : 1 ≤ T.side))
    set θ : ℝ := 2 * Real.pi * ((1 : ℕ) : ℝ) / ((n : ℝ) * N) ^ 2 with hθdef
    have hθ0 : 0 ≤ θ := by positivity
    have hθγ : θ ≤ γ := by
      apply div_le_div_of_nonneg_left (by positivity) (by positivity)
      have : (n : ℝ) ≤ (n : ℝ) * N := le_mul_of_one_le_right hnpos.le hN1
      exact pow_le_pow_left₀ hnpos.le this 2
    have hNpos : 0 < N := by linarith
    have hMθ : ((n : ℝ) * N) ^ 2 * θ = 2 * Real.pi := by
      rw [hθdef, Nat.cast_one]
      field_simp
    have hnγ : (n : ℝ) ^ 2 * γ = 2 * Real.pi := by
      rw [hγdef, Nat.cast_one]
      field_simp
    have hfin := abs_one_sub_le_of_action_near_shares (M := (n : ℝ) * N) (n := (n : ℝ)) (θ := θ)
      (γ := γ) (ε := ε) (v := v)
      (A := ∑ z, centered (levelShareFamily T.coupling T.side (t + 1)) n z V)
      hMθ hnγ hθ0 (by linarith) hθγ (by nlinarith) hs hsumb
    have : |1 - v| ≤ 3 / 4 * |1 - v| := by
      rw [hεdef] at hfin
      linarith
    linarith
  rw [hv1] at hvb
  refine ⟨hLim, fun A A' hA hA' => ?_⟩
  rw [hvb]
  exact hb A A' hA hA'
end YangMills.Construction.ShareFamilies
end
