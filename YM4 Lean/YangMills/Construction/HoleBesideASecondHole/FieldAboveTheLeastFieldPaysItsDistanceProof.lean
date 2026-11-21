import YangMills.Construction.ColdChainAtEveryLevel.HessianFloorInTheChart
import YangMills.Construction.ColdChainAtEveryLevel.OneLeastFieldOfAColdTop
import YangMills.Construction.HoleBesideASecondHole.CostOnWholeCellsIsTheLeastAction
import YangMills.Construction.HoleBesideASecondHole.EnergyInTheChart
import YangMills.Construction.HoleBesideASecondHole.FieldAboveTheLeastFieldPaysItsDistance
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction.LumpContours
open YangMills.Construction.BlockAverages YangMills.Construction.GaugeFixing
theorem add_half_le_of_le_deriv_deriv (f : ℝ → ℝ) (c : ℝ) (hc : 0 ≤ c) (hmin : ∀ τ, f 0 ≤ f τ)
    (hfl : ∀ τ, 0 ≤ τ → τ ≤ 1 → c ≤ deriv (deriv f) τ) : f 0 + c / 2 ≤ f 1 := by
  rcases hc.eq_or_lt with h0 | hpos
  · rw [← h0]
    simpa using hmin 1
  have hg0 : deriv f 0 = 0 :=
    IsLocalMin.deriv_eq_zero (Filter.Eventually.of_forall hmin)
  have hdiff : ∀ τ, 0 ≤ τ → τ ≤ 1 → DifferentiableAt ℝ (deriv f) τ := by
    intro τ h0 h1
    by_contra hnd
    have := deriv_zero_of_not_differentiableAt hnd
    have := hfl τ h0 h1
    linarith
  have hlow : ∀ τ, 0 ≤ τ → τ ≤ 1 → c * τ ≤ deriv f τ := by
    intro τ h0 h1
    have := Convex.mul_sub_le_image_sub_of_le_deriv (convex_Icc (0 : ℝ) 1) (f := deriv f) (C := c)
      (fun x hx => (hdiff x hx.1 hx.2).continuousAt.continuousWithinAt)
      (fun x hx => by
        rw [interior_Icc] at hx
        exact (hdiff x hx.1.le hx.2.le).differentiableWithinAt)
      (fun x hx => by
        rw [interior_Icc] at hx
        exact hfl x hx.1.le hx.2.le)
      0 ⟨le_rfl, zero_le_one⟩ τ ⟨h0, h1⟩ h0
    rw [hg0] at this
    linarith
  have hfd : ∀ τ, 0 < τ → τ ≤ 1 → DifferentiableAt ℝ f τ := by
    intro τ h0 h1
    by_contra hnd
    have h2 := deriv_zero_of_not_differentiableAt hnd
    have h3 := hlow τ h0.le h1
    have : 0 < c * τ := mul_pos hpos h0
    linarith
  have hstep : ∀ e, 0 < e → e ≤ 1 → f e + c / 2 - c * e ^ 2 / 2 ≤ f 1 := by
    intro e he0 he1
    set h : ℝ → ℝ := fun τ => f τ - c * τ ^ 2 / 2 with hh
    have hd : ∀ τ, 0 < τ → τ ≤ 1 → HasDerivAt h (deriv f τ - c * τ) τ := by
      intro τ h0 h1
      have h2 := (hfd τ h0 h1).hasDerivAt
      have h3 : HasDerivAt (fun τ : ℝ => c * τ ^ 2 / 2) (c * τ) τ := by
        have := ((hasDerivAt_pow 2 τ).const_mul c).div_const 2
        have e : c * τ = c * (((2 : ℕ) : ℝ) * τ ^ (2 - 1)) / 2 := by norm_num <;> ring
        rw [e]
        exact this
      exact h2.sub h3
    have hmono := Convex.mul_sub_le_image_sub_of_le_deriv (convex_Icc e 1) (f := h) (C := 0)
      (fun x hx => (hd x (he0.trans_le hx.1) hx.2).continuousAt.continuousWithinAt)
      (fun x hx => by
        rw [interior_Icc] at hx
        exact (hd x (he0.trans hx.1) hx.2.le).differentiableAt.differentiableWithinAt)
      (fun x hx => by
        rw [interior_Icc] at hx
        rw [(hd x (he0.trans hx.1) hx.2.le).deriv]
        have := hlow x (he0.le.trans hx.1.le) hx.2.le
        linarith)
      e ⟨le_rfl, he1⟩ 1 ⟨he1, le_rfl⟩ he1
    simp only [hh] at hmono
    nlinarith
  refine le_of_forall_pos_le_add fun δ hδ => ?_
  set e := min 1 (δ / (c + 1)) with he
  have he0 : 0 < e := lt_min one_pos (by positivity)
  have he1 : e ≤ 1 := min_le_left _ _
  have he2 : e * (c + 1) ≤ δ := by
    have := min_le_right 1 (δ / (c + 1))
    rw [← he] at this
    rwa [le_div_iff₀ (by positivity)] at this
  have h1 := hstep e he0 he1
  have h2 := hmin e
  have h3 : c * e ^ 2 / 2 ≤ δ := by nlinarith
  linarith
variable {F : BlockFrame}
theorem cutEffectiveAction_top_eq_minimalAction (hCost : WholeCellCostEqualsMinimalAction)
    (hL : Odd F.blockSide) (a : ℝ) (ha : 0 ≤ a)
    (S : Finset F.Cell) (V : F.GaugeField F.top) :
    cutEffectiveAction a F.top S V = minimalAction a S F.top V := by
  have h := hCost F a S hL ha
  have e : cutBelow F.top S = S := by
    rw [h.1 F.top le_rfl]
    ext y
    exact mem_sitesOfCells_top
  have := h.2.1 F.top le_rfl V
  rwa [e] at this
set_option maxHeartbeats 1000000 in
theorem minimizerQuadraticGap (hOne : uniqueMinimizerStatement) (hH : hessianLowerBoundStatement)
    (hC : NearTopCoordinateBound)
    (hCost : WholeCellCostEqualsMinimalAction) (hG : gaugeCovarianceStatement)
    (hLV : minimalChainExistenceStatement) :
    minimizerQuadraticGapStatement := by
  intro a ha
  have ha0 : 0 < a := by linarith
  obtain ⟨L1, h1⟩ := hH a ha0
  obtain ⟨L2, h2⟩ := hOne a ha0
  obtain ⟨K, hK1, hK⟩ := hC
  refine ⟨max L1 L2, fun L hodd hL => ?_⟩
  obtain ⟨lam, ρ, σ, hlam, hρ, hσ, h1'⟩ := h1 L hodd (le_of_max_le_left hL)
  set ρ' := min ρ (1 / 8) with hρ'
  have hρ'0 : 0 < ρ' := lt_min hρ (by norm_num)
  obtain ⟨σ2, N0, hσ2, hN0, h2'⟩ := h2 L hodd (le_of_max_le_right hL) ρ' hρ'0
  set M := K L + N0 with hM
  have hKL : 1 ≤ K L := hK1 L
  have hMpos : 0 < M := by rw [hM]; linarith
  refine ⟨lam, min (min σ σ2) (min (1 / K L) (min (ρ' / M) (σ / (2 * (1 + 8 * M))))), hlam, ?_, ?_⟩
  · refine lt_min (lt_min hσ hσ2) (lt_min (by positivity) (lt_min (by positivity) (by positivity)))
  intro F m S hFL hcub hm hreg r V W Wl hr hr0 hV hnear hleast
  subst hFL
  have hs : ∀ i, 2 ≤ F.extent i := fun i => by rw [hcub.1 i]; have := hcub.2; omega
  have hs' : ∀ i, 0 < F.extent i := fun i => by have := hs i; omega
  have hA : IsAdmissibleAmbient F := Or.inr fun i => by rw [hcub.1 i]; exact hcub.2
  have r1 : r ≤ σ := hr0.trans ((min_le_left _ _).trans (min_le_left _ _))
  have r2 : r ≤ σ2 := hr0.trans ((min_le_left _ _).trans (min_le_right _ _))
  have r3 : r ≤ 1 / K F.blockSide := hr0.trans ((min_le_right _ _).trans (min_le_left _ _))
  have r4 : r ≤ ρ' / M := hr0.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have r5 : r ≤ σ / (2 * (1 + 8 * M)) :=
    hr0.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  have hKpos : 0 < K F.blockSide := by linarith
  have hKr : K F.blockSide * r ≤ 1 := by
    rwa [le_div_iff₀ hKpos, mul_comm] at r3
  have hMr : M * r ≤ ρ' := by
    rwa [le_div_iff₀ hMpos, mul_comm] at r4
  have hcold' : r + 8 * (M * r) < σ := by
    rw [le_div_iff₀ (by positivity)] at r5
    nlinarith
  obtain ⟨wst, hLC, -, huniq⟩ := h2' F m S rfl hA hm hreg r V hr r2 hV
  have hFl := h1' F m S rfl hA hm hreg r V hr r1 hV
  set w := lexicographicChart S V W with hw
  set dw : F.Site F.depth → Fin 4 → imaginaryQuaternions := fun x i => w x i - wst x i with hdw
  set e := M * r with he
  have hwoff : ∀ b, b ∉ chordBonds S → w b.1 b.2 = 0 := fun b hb => by
    simp only [hw, lexicographicChart]
    exact if_neg hb
  have hstoff : ∀ b, b ∉ chordBonds S → wst b.1 b.2 = 0 := hLC.1
  have hdwoff : ∀ b, b ∉ chordBonds S → dw b.1 b.2 = 0 := fun b hb => by
    simp only [hdw, hwoff b hb, hstoff b hb, sub_zero]
  have hwon : ∀ b ∈ chordBonds S, w b.1 b.2 = bondCoordinate 1 V W b := fun b hb => by
    simp only [hw, lexicographicChart]
    exact if_pos hb
  have hbond : ∀ b ∈ chordBonds S, b ∈ innerBonds S F.depth := fun b hb => by
    simp only [chordBonds, Finset.mem_filter] at hb
    exact hb.1
  have hwle : ∀ b ∈ chordBonds S, ‖(w b.1 b.2 : ℍ[ℝ])‖ ≤ e := fun b hb => by
    rw [hwon b hb]
    have := hK F hodd hcub S V W r hr.le hKr hnear b (hbond b hb)
    refine this.trans ?_
    rw [he, hM]
    nlinarith
  have hstle : ∀ b ∈ chordBonds S, ‖(wst b.1 b.2 : ℍ[ℝ])‖ ≤ e := fun b hb => by
    refine (hLC.2.1 b hb).trans ((min_le_right _ _).trans ?_)
    rw [he, hM]
    nlinarith
  have heρ : e ≤ ρ := hMr.trans (min_le_left _ _)
  have he8 : e ≤ 1 / 8 := hMr.trans (min_le_right _ _)
  set f : ℝ → ℝ := fun τ =>
    blockEnergy a S F.depth (chartedField (fun x i => wst x i + τ • dw x i) V) V with hf
  have hseg : ∀ τ : ℝ, 0 ≤ τ → τ ≤ 1 → ∀ b ∈ chordBonds S,
      ‖((wst b.1 b.2 + τ • dw b.1 b.2 : imaginaryQuaternions) : ℍ[ℝ])‖ ≤ e := by
    intro τ h0 h1 b hb
    have e1 : ((wst b.1 b.2 + τ • dw b.1 b.2 : imaginaryQuaternions) : ℍ[ℝ]) =
        (1 - τ) • (wst b.1 b.2 : ℍ[ℝ]) + τ • (w b.1 b.2 : ℍ[ℝ]) := by
      simp only [hdw, Submodule.coe_add, Submodule.coe_smul, Submodule.coe_sub]
      module
    rw [e1]
    refine (norm_add_le _ _).trans ?_
    rw [norm_smul, norm_smul, Real.norm_of_nonneg (by linarith), Real.norm_of_nonneg h0]
    have a1 := mul_le_mul_of_nonneg_left (hstle b hb) (by linarith : 0 ≤ 1 - τ)
    have a2 := mul_le_mul_of_nonneg_left (hwle b hb) h0
    nlinarith
  have hfl : ∀ τ : ℝ, 0 ≤ τ → τ ≤ 1 →
      lam * ∑ b ∈ chordBonds S, ‖dw b.1 b.2‖ ^ 2 ≤ deriv (deriv f) τ := by
    intro τ h0 h1
    have hcoff : ∀ b, b ∉ chordBonds S → wst b.1 b.2 + τ • dw b.1 b.2 = 0 := fun b hb => by
      rw [hstoff b hb, hdwoff b hb]; simp
    have hall : ∀ b ∈ innerBonds S F.depth,
        ‖((wst b.1 b.2 + τ • dw b.1 b.2 : imaginaryQuaternions) : ℍ[ℝ])‖ ≤ e := fun b hb => by
      by_cases hc : b ∈ chordBonds S
      · exact hseg τ h0 h1 b hc
      · rw [hcoff b hc]
        simpa using (by positivity : (0 : ℝ) ≤ e)
    have hcold : IsCold S F.depth σ (chartedField (fun x i => wst x i + τ • dw x i) V) := by
      intro p hp
      have := plaquetteDefect_chartedField_le hs hodd S V r e hr.le (fun p hp => (hV p hp).trans_le le_rfl)
        (fun x i => wst x i + τ • dw x i) (by linarith) hall p hp
      linarith
    have h3 := hFl (fun x i => wst x i + τ • dw x i) dw hcoff hdwoff
      (fun b hb => (hseg τ h0 h1 b hb).trans heρ) hcold
    have h4 : (fun σ' : ℝ => blockEnergy a S F.depth
        (chartedField (fun x i => (fun x i => wst x i + τ • dw x i) x i + σ' • dw x i) V) V) =
        fun σ' : ℝ => f (τ + σ') := by
      funext σ'
      simp only [hf, add_smul, add_assoc]
    rw [h4] at h3
    have h5 : deriv (fun σ' : ℝ => f (τ + σ')) = fun σ' => deriv f (τ + σ') := by
      funext σ'
      exact deriv_comp_const_add f τ σ'
    rw [h5, deriv_comp_const_add (deriv f) τ 0, add_zero] at h3
    exact h3
  have hf0 : f 0 = blockEnergy a S F.depth (chartedField wst V) V := by
    simp only [hf, zero_smul, add_zero]
  have hf1 : f 1 = blockEnergy a S F.depth W V := by
    have : (fun x i => wst x i + (1 : ℝ) • dw x i) = w := by
      funext x i
      simp [hdw]
    simp only [hf, this]
    exact blockEnergy_lexicographicChart hG hs hodd a S V W
  have hmin : ∀ τ, f 0 ≤ f τ := fun τ => by
    rw [hf0]
    exact hLC.2.2 _
  have hrise := add_half_le_of_le_deriv_deriv f _ (by positivity) hmin hfl
  have hle : cutEffectiveAction a F.top S V ≤ f 0 := by
    rw [cutEffectiveAction_top_eq_minimalAction hCost hodd a ha0.le S V, hf0]
    obtain ⟨W₀, h3, h4⟩ := (hLV F a S ha0.le).2.2.1 F.depth V
    rw [← h3]
    exact h4 _
  have hplain : plainBlockEnergy a S W V = blockEnergy a S F.depth W V :=
    (hCost F a S hodd ha0.le).2.2 W V
  have hlmin : ∀ W'', blockEnergy a S F.depth Wl V ≤ blockEnergy a S F.depth W'' V := fun W'' => by
    have := hleast W''
    rwa [(hCost F a S hodd ha0.le).2.2 Wl V, (hCost F a S hodd ha0.le).2.2 W'' V] at this
  obtain ⟨γ, hγ, hsame⟩ := huniq Wl hlmin
  have hsum : ∑ b ∈ chordBonds S, ‖(lexBondCoordinate V W b : ℍ[ℝ]) - lexBondCoordinate V Wl b‖ ^ 2 =
      ∑ b ∈ chordBonds S, ‖dw b.1 b.2‖ ^ 2 := by
    refine Finset.sum_congr rfl fun b hb => ?_
    have c1 : lexBondCoordinate V Wl b = wst b.1 b.2 :=
      bondCoordinate_of_agreeOnBonds hs hodd S V wst γ Wl hγ hsame b hb (by
        have := hstle b hb
        have := Real.pi_gt_three
        linarith)
    have c2 : lexBondCoordinate V W b = w b.1 b.2 := (hwon b hb).symm
    rw [c1, c2]
    rfl
  rw [hsum, hplain]
  have : f 0 + lam * (∑ b ∈ chordBonds S, ‖dw b.1 b.2‖ ^ 2) / 2 ≤ blockEnergy a S F.depth W V := by
    rw [← hf1]
    exact hrise
  linarith
end YangMills.Construction.LumpContours
end
