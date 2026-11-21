import YangMills.Construction.ClusterExpansionOfAStep.TreesOfABlock
import YangMills.Construction.ClusterExpansionOfAStep.PlaquettesUnderGaugesAndMoves
import YangMills.Construction.ClusterExpansionOfAStep.SitesOfTheTopOfAStep
import YangMills.Construction.ColdChainAtEveryLevel.ChartOverAnotherTopProof
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction
open BlockAverages LumpContours ColdStepAtMirrorFrames
open TorusFields (TorusField TorusSite curvature holonomy norm_unitQuaternion coe_inv_unitQuaternion)
namespace TopLevelSites
section Exp
theorem coe_expUnit (w : imaginaryQuaternions) :
    ((expUnit w : UnitQuaternion) : ℍ[ℝ]) = NormedSpace.exp (w : ℍ[ℝ]) := rfl
theorem exp_imaginary (w : imaginaryQuaternions) : NormedSpace.exp (w : ℍ[ℝ]) =
    ((Real.cos ‖(w : ℍ[ℝ])‖ : ℝ) : ℍ[ℝ]) + (Real.sin ‖(w : ℍ[ℝ])‖ / ‖(w : ℍ[ℝ])‖) • (w : ℍ[ℝ]) :=
  Quaternion.exp_of_re_eq_zero _ w.2
theorem re_expUnit (w : imaginaryQuaternions) :
    ((expUnit w : UnitQuaternion) : ℍ[ℝ]).re = Real.cos ‖(w : ℍ[ℝ])‖ := by apply _root_.YangMills.Construction.GaugeFixing.re_coe_expUnit <;> assumption
theorem expUnit_injective_of_norm_lt_pi {w w' : imaginaryQuaternions} (h1 : ‖(w : ℍ[ℝ])‖ < Real.pi)
    (h2 : ‖(w' : ℍ[ℝ])‖ < Real.pi) (h : expUnit w = expUnit w') : w = w' := by
  have hc : Real.cos ‖(w : ℍ[ℝ])‖ = Real.cos ‖(w' : ℍ[ℝ])‖ := by
    rw [← re_expUnit, ← re_expUnit, h]
  have hn : ‖(w : ℍ[ℝ])‖ = ‖(w' : ℍ[ℝ])‖ :=
    Real.injOn_cos ⟨norm_nonneg _, h1.le⟩ ⟨norm_nonneg _, h2.le⟩ hc
  have hq : NormedSpace.exp (w : ℍ[ℝ]) = NormedSpace.exp (w' : ℍ[ℝ]) :=
    congrArg (fun g : UnitQuaternion => (g : ℍ[ℝ])) h
  rw [exp_imaginary, exp_imaginary, ← hn] at hq
  apply Subtype.ext
  by_cases h0 : ‖(w : ℍ[ℝ])‖ = 0
  · have a1 : (w : ℍ[ℝ]) = 0 := norm_eq_zero.mp h0
    have a2 : (w' : ℍ[ℝ]) = 0 := norm_eq_zero.mp (hn ▸ h0)
    rw [a1, a2]
  · have hpos : 0 < ‖(w : ℍ[ℝ])‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm h0)
    have hs : Real.sin ‖(w : ℍ[ℝ])‖ / ‖(w : ℍ[ℝ])‖ ≠ 0 :=
      div_ne_zero (Real.sin_pos_of_pos_of_lt_pi hpos h1).ne' h0
    exact smul_right_injective _ hs (add_left_cancel hq)
theorem norm_sq_eq_re_sq_add_norm_im_sq (q : ℍ[ℝ]) : ‖q‖ ^ 2 = q.re ^ 2 + ‖q.im‖ ^ 2 := by
  have h1 : ‖q‖ ^ 2 = Quaternion.normSq q := by rw [Quaternion.normSq_eq_norm_mul_self]; ring
  have h2 : ‖q.im‖ ^ 2 = Quaternion.normSq q.im := by rw [Quaternion.normSq_eq_norm_mul_self]; ring
  rw [h1, h2, Quaternion.normSq_def', Quaternion.normSq_def']
  simp
  ring
theorem exists_minimal_log (g : UnitQuaternion) : ∃ w : imaginaryQuaternions, expUnit w = g ∧
    ∀ w' : imaginaryQuaternions, expUnit w' = g → ‖(w : ℍ[ℝ])‖ ≤ ‖(w' : ℍ[ℝ])‖ := by
  set q : ℍ[ℝ] := (g : ℍ[ℝ]) with hq
  have hnorm : ‖q‖ = 1 := norm_unitQuaternion g
  have hparts := norm_sq_eq_re_sq_add_norm_im_sq q
  rw [hnorm] at hparts
  have hre1 : q.re ^ 2 ≤ 1 := by nlinarith [sq_nonneg ‖q.im‖]
  have hle : -1 ≤ q.re ∧ q.re ≤ 1 := abs_le.mp ((sq_le_one_iff_abs_le_one _).mp hre1)
  set θ := Real.arccos q.re with hθ
  have hcos : Real.cos θ = q.re := Real.cos_arccos hle.1 hle.2
  have hθ0 : 0 ≤ θ := Real.arccos_nonneg _
  have hθπ : θ ≤ Real.pi := Real.arccos_le_pi _
  have hsin : Real.sin θ = ‖q.im‖ := by
    have h1 : 0 ≤ Real.sin θ := Real.sin_nonneg_of_nonneg_of_le_pi hθ0 hθπ
    have h2 := Real.sin_sq_add_cos_sq θ
    rw [hcos] at h2
    have h3 : Real.sin θ ^ 2 = ‖q.im‖ ^ 2 := by linarith
    exact (pow_left_inj₀ h1 (norm_nonneg _) two_ne_zero).mp h3
  have hmin : ∀ w' : imaginaryQuaternions, expUnit w' = g → θ ≤ ‖(w' : ℍ[ℝ])‖ := by
    intro w' hw'
    have e : q.re = Real.cos ‖(w' : ℍ[ℝ])‖ := by rw [hq, ← hw', re_expUnit]
    rw [hθ, e]
    by_cases hp : ‖(w' : ℍ[ℝ])‖ ≤ Real.pi
    · rw [Real.arccos_cos (norm_nonneg _) hp]
    · exact (Real.arccos_le_pi _).trans (not_le.mp hp).le
  by_cases hv : q.im = 0
  · by_cases hr : 0 < q.re
    · have hre : q.re = 1 := by
        rw [hv] at hparts
        simp at hparts
        nlinarith
      refine ⟨0, ?_, fun w' _ => by simp⟩
      apply Subtype.ext
      have hq1 : q = 1 := by
        have := Quaternion.re_add_im q
        rw [hv, hre] at this
        simpa using this.symm
      rw [coe_expUnit]
      simp [hq1, hq]
      exact hq1.symm ▸ rfl
    · have hre : q.re = -1 := by
        rw [hv] at hparts
        simp at hparts
        nlinarith
      have hθ' : θ = Real.pi := by rw [hθ, hre, Real.arccos_neg_one]
      let u : imaginaryQuaternions := ⟨(⟨0, Real.pi, 0, 0⟩ : ℍ[ℝ]), rfl⟩
      have hu : ‖(u : ℍ[ℝ])‖ = Real.pi := by
        have h1 : ‖(u : ℍ[ℝ])‖ * ‖(u : ℍ[ℝ])‖ = Real.pi * Real.pi := by
          rw [← Quaternion.normSq_eq_norm_mul_self, Quaternion.normSq_def']
          simp [u]
          ring
        have h2 := Real.pi_pos
        nlinarith [norm_nonneg (u : ℍ[ℝ]), sq_nonneg (‖(u : ℍ[ℝ])‖ - Real.pi), sq_nonneg (‖(u : ℍ[ℝ])‖ + Real.pi)]
      refine ⟨u, ?_, fun w' hw' => hu ▸ hθ' ▸ hmin w' hw'⟩
      apply Subtype.ext
      have hq1 : q = -1 := by
        have := Quaternion.re_add_im q
        rw [hv, hre] at this
        simpa using this.symm
      rw [coe_expUnit, exp_imaginary, hu]
      simp [Real.cos_pi, Real.sin_pi]
      exact hq1.symm
  · have hvn : ‖q.im‖ ≠ 0 := norm_ne_zero_iff.mpr hv
    have hθne : θ ≠ 0 := by
      intro h0
      rw [h0, Real.sin_zero] at hsin
      exact hvn hsin.symm
    let w : imaginaryQuaternions := ⟨(θ / ‖q.im‖) • q.im, by
      show ((θ / ‖q.im‖) • q.im).re = 0
      simp⟩
    have hwn : ‖(w : ℍ[ℝ])‖ = θ := by
      change ‖(θ / ‖q.im‖) • q.im‖ = θ
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (div_nonneg hθ0 (norm_nonneg _))]
      field_simp
    refine ⟨w, ?_, fun w' hw' => hwn ▸ hmin w' hw'⟩
    apply Subtype.ext
    rw [coe_expUnit, exp_imaginary, hwn, hcos, hsin]
    change _ + _ • ((θ / ‖q.im‖) • q.im) = q
    rw [smul_smul]
    have e : ‖q.im‖ / θ * (θ / ‖q.im‖) = 1 := by field_simp
    rw [e, one_smul]
    exact Quaternion.re_add_im q
theorem expUnit_minimalLog (g : UnitQuaternion) : expUnit (minimalLog g) = g := by apply _root_.YangMills.Construction.GaugeFixing.expUnit_minimalLog <;> assumption
theorem norm_expUnit_sub_le (w w' : imaginaryQuaternions) :
    ‖((expUnit w : UnitQuaternion) : ℍ[ℝ]) - ((expUnit w' : UnitQuaternion) : ℍ[ℝ])‖ ≤
      ‖(w : ℍ[ℝ]) - (w' : ℍ[ℝ])‖ := by
  set a : ℍ[ℝ] := (w : ℍ[ℝ]) with ha
  set b : ℍ[ℝ] := (w' : ℍ[ℝ]) with hb
  let f : ℝ → ℍ[ℝ] := fun τ => NormedSpace.exp (τ • a) * NormedSpace.exp ((1 - τ) • b)
  let f' : ℝ → ℍ[ℝ] := fun τ => NormedSpace.exp (τ • a) * (a - b) * NormedSpace.exp ((1 - τ) • b)
  have hder : ∀ τ : ℝ, HasDerivAt f (f' τ) τ := by
    intro τ
    have h1 : HasDerivAt (fun u : ℝ => NormedSpace.exp (u • a)) (NormedSpace.exp (τ • a) * a) τ :=
      hasDerivAt_exp_smul_const a τ
    have h2 : HasDerivAt (fun u : ℝ => NormedSpace.exp (u • b)) (b * NormedSpace.exp ((1 - τ) • b)) (1 - τ) :=
      hasDerivAt_exp_smul_const' b (1 - τ)
    have h3 : HasDerivAt (fun u : ℝ => 1 - u) (-1 : ℝ) τ := by
      simpa using (hasDerivAt_id τ).const_sub (1 : ℝ)
    have h4 := h2.scomp τ h3
    have h5 := h1.mul h4
    have e : f' τ = NormedSpace.exp (τ • a) * a * NormedSpace.exp ((1 - τ) • b) +
        NormedSpace.exp (τ • a) * ((-1 : ℝ) • (b * NormedSpace.exp ((1 - τ) • b))) := by
      simp only [f', neg_smul, one_smul, mul_neg]
      noncomm_ring
    rw [e]
    exact h5
  have hunit : ∀ (v : imaginaryQuaternions) (τ : ℝ), ‖NormedSpace.exp (τ • (v : ℍ[ℝ]))‖ = 1 := by
    intro v τ
    exact norm_unitQuaternion (expUnit (τ • v))
  have hbound : ∀ τ ∈ (Set.univ : Set ℝ), ‖f' τ‖ ≤ ‖a - b‖ := by
    intro τ _
    simp only [f']
    rw [norm_mul, norm_mul, hunit w τ, hunit w' (1 - τ), one_mul, mul_one]
  have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun τ _ => (hder τ).hasDerivWithinAt) hbound convex_univ (Set.mem_univ (0 : ℝ)) (Set.mem_univ (1 : ℝ))
  simp only [f, zero_smul, sub_zero, one_smul, sub_self, NormedSpace.exp_zero, mul_one, one_mul] at h
  have h' : ‖NormedSpace.exp a - NormedSpace.exp b‖ ≤ ‖a - b‖ := by simpa using h
  exact h'
theorem norm_mul_sub_mul_le (g g' h h' : UnitQuaternion) :
    ‖((g * h : UnitQuaternion) : ℍ[ℝ]) - ((g' * h' : UnitQuaternion) : ℍ[ℝ])‖ ≤
      ‖(g : ℍ[ℝ]) - g'‖ + ‖(h : ℍ[ℝ]) - h'‖ := by apply _root_.YangMills.Construction.BlockAverages.ChartOverTop.coe_mul_sub_mul_le <;> assumption
theorem norm_inv_sub_inv (g g' : UnitQuaternion) :
    ‖((g⁻¹ : UnitQuaternion) : ℍ[ℝ]) - ((g'⁻¹ : UnitQuaternion) : ℍ[ℝ])‖ = ‖(g : ℍ[ℝ]) - g'‖ := by apply _root_.YangMills.Construction.LumpContours.BlockLevels.norm_sub_inv_inv <;> assumption
theorem curvature_le_add {N : ℕ} (A B : TorusField N) (x : TorusSite N) (μ ν : Fin 4) :
    curvature A x μ ν ≤ curvature B x μ ν + (‖(A x μ : ℍ[ℝ]) - B x μ‖ +
      ‖(A (x + TorusFields.unitStep N μ) ν : ℍ[ℝ]) - B (x + TorusFields.unitStep N μ) ν‖ +
      ‖(A (x + TorusFields.unitStep N ν) μ : ℍ[ℝ]) - B (x + TorusFields.unitStep N ν) μ‖ +
      ‖(A x ν : ℍ[ℝ]) - B x ν‖) := by
  unfold curvature holonomy
  set P : UnitQuaternion := A x μ * A (x + TorusFields.unitStep N μ) ν *
    (A (x + TorusFields.unitStep N ν) μ)⁻¹ * (A x ν)⁻¹
  set Q : UnitQuaternion := B x μ * B (x + TorusFields.unitStep N μ) ν *
    (B (x + TorusFields.unitStep N ν) μ)⁻¹ * (B x ν)⁻¹
  have h1 : ‖(P : ℍ[ℝ]) - Q‖ ≤ ‖(A x μ : ℍ[ℝ]) - B x μ‖ +
      ‖(A (x + TorusFields.unitStep N μ) ν : ℍ[ℝ]) - B (x + TorusFields.unitStep N μ) ν‖ +
      ‖(A (x + TorusFields.unitStep N ν) μ : ℍ[ℝ]) - B (x + TorusFields.unitStep N ν) μ‖ +
      ‖(A x ν : ℍ[ℝ]) - B x ν‖ := by
    have a1 := norm_mul_sub_mul_le
      (A x μ * A (x + TorusFields.unitStep N μ) ν * (A (x + TorusFields.unitStep N ν) μ)⁻¹)
      (B x μ * B (x + TorusFields.unitStep N μ) ν * (B (x + TorusFields.unitStep N ν) μ)⁻¹)
      (A x ν)⁻¹ (B x ν)⁻¹
    have a2 := norm_mul_sub_mul_le (A x μ * A (x + TorusFields.unitStep N μ) ν)
      (B x μ * B (x + TorusFields.unitStep N μ) ν)
      (A (x + TorusFields.unitStep N ν) μ)⁻¹ (B (x + TorusFields.unitStep N ν) μ)⁻¹
    have a3 := norm_mul_sub_mul_le (A x μ) (B x μ) (A (x + TorusFields.unitStep N μ) ν)
      (B (x + TorusFields.unitStep N μ) ν)
    rw [norm_inv_sub_inv] at a1 a2
    linarith
  have h2 : ‖(P : ℍ[ℝ]) - 1‖ ≤ ‖(Q : ℍ[ℝ]) - 1‖ + ‖(P : ℍ[ℝ]) - Q‖ := by
    have : (P : ℍ[ℝ]) - 1 = ((Q : ℍ[ℝ]) - 1) + ((P : ℍ[ℝ]) - Q) := by abel
    rw [this]
    exact norm_add_le _ _
  linarith
end Exp
section Tree
variable {F : BlockFrame} {j : ℕ}
theorem pathHolonomy_append (X : F.GaugeField j) (x : F.Site j) (l₁ l₂ : List PathStep) :
    pathHolonomy X x (l₁ ++ l₂) =
      pathHolonomy X x l₁ * pathHolonomy X (x + (l₁.map (stepDisplacement j)).sum) l₂ := by
  induction l₁ generalizing x with
  | nil => simp [pathHolonomy]
  | cons st r ih => simp [pathHolonomy, ih, mul_assoc, add_assoc]
def axisSegment (c : ℤ) (k : Fin 4) : List PathStep := List.replicate c.natAbs (k, decide (0 ≤ c))
theorem axisPath_one_eq (h : Fin 4 → ℤ) : axisPath h (1 : Equiv.Perm (Fin 4)) =
    axisSegment (h 0) 0 ++ axisSegment (h 1) 1 ++ axisSegment (h 2) 2 ++ axisSegment (h 3) 3 := by
  have e : List.finRange 4 = [0, 1, 2, 3] := by decide
  simp [axisPath, e, axisSegment, List.flatMap_cons, List.append_assoc]
  first | rfl | congr
theorem axisSegment_displacement (c : ℤ) (k : Fin 4) :
    ((axisSegment c k).map (stepDisplacement (F := F) j)).sum = siteOfCoords j (Pi.single k c) := by
  unfold axisSegment
  rw [List.map_replicate, List.sum_replicate]
  funext l
  by_cases hc : 0 ≤ c
  · obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le hc
    by_cases hl : l = k
    · subst hl
      simp [stepDisplacement, unitStep, siteOfCoords]
    · simp [stepDisplacement, unitStep, siteOfCoords, Pi.single_eq_of_ne hl]
  · have hc' : c < 0 := not_le.mp hc
    have hd : decide (0 ≤ c) = false := by simpa using hc'
    rw [hd]
    obtain ⟨m, rfl⟩ : ∃ m : ℕ, c = -(m : ℤ) := ⟨c.natAbs, by omega⟩
    have e1 : (-(m : ℤ)).natAbs = m := by omega
    rw [e1]
    simp only [stepDisplacement, Bool.false_eq_true, if_false]
    by_cases hl : l = k
    · subst hl
      simp [unitStep, siteOfCoords]
    · simp [unitStep, siteOfCoords, Pi.single_eq_of_ne hl]
theorem axisPath_displacement (h : Fin 4 → ℤ) :
    ((axisPath h (1 : Equiv.Perm (Fin 4))).map (stepDisplacement (F := F) j)).sum = siteOfCoords j h := by apply _root_.YangMills.Construction.BlockTrees.pathDisplacement_axisPath <;> assumption
theorem axisSegment_add_one {c : ℤ} (hc : 0 ≤ c) (k : Fin 4) :
    axisSegment (c + 1) k = axisSegment c k ++ [(k, true)] := by
  obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le hc
  unfold axisSegment
  have e1 : ((m : ℤ) + 1).natAbs = m + 1 := by omega
  have e2 : decide (0 ≤ (m : ℤ) + 1) = true := by simp; omega
  have e3 : decide (0 ≤ (m : ℤ)) = true := by simp
  rw [e1, e2, e3, List.replicate_succ', Int.natAbs_natCast]
theorem axisSegment_of_neg {c : ℤ} (hc : c < 0) (k : Fin 4) :
    axisSegment c k = axisSegment (c + 1) k ++ [(k, false)] := by
  obtain ⟨m, rfl⟩ : ∃ m : ℕ, c = -((m : ℤ) + 1) := ⟨(-c - 1).toNat, by omega⟩
  unfold axisSegment
  have e0 : -((m : ℤ) + 1) + 1 = -(m : ℤ) := by ring
  have e1 : (-((m : ℤ) + 1)).natAbs = m + 1 := by omega
  have e2 : decide (0 ≤ -((m : ℤ) + 1)) = false := by simp; omega
  rw [e0, e1, e2, List.replicate_succ']
  congr 1
  have e3 : (-(m : ℤ)).natAbs = m := by omega
  rw [e3]
  cases m with
  | zero => simp
  | succ m =>
    have e4 : decide (0 ≤ -((m + 1 : ℕ) : ℤ)) = false := by simp; omega
    rw [e4]
theorem axisPath_add_single (h : Fin 4 → ℤ) (i : Fin 4) (hz : ∀ l, i < l → h l = 0) :
    (0 ≤ h i → axisPath (h + Pi.single i 1 : Fin 4 → ℤ) (1 : Equiv.Perm (Fin 4)) =
      axisPath h 1 ++ [(i, true)]) ∧
    (h i < 0 → axisPath h (1 : Equiv.Perm (Fin 4)) =
      axisPath (h + Pi.single i 1 : Fin 4 → ℤ) 1 ++ [(i, false)]) := by
  have hself : (h + Pi.single i 1 : Fin 4 → ℤ) i = h i + 1 := by simp
  have hoth : ∀ l, l ≠ i → (h + Pi.single i 1 : Fin 4 → ℤ) l = h l := fun l hl => by
    simp [Pi.single_eq_of_ne hl]
  have hzero : ∀ l, i < l → axisSegment (h l) l = [] := fun l hl => by simp [axisSegment, hz l hl]
  have hzero' : ∀ l, i < l → axisSegment ((h + Pi.single i 1 : Fin 4 → ℤ) l) l = [] := fun l hl => by
    rw [hoth l hl.ne']
    exact hzero l hl
  have hcases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 :=
    (by decide : ∀ i : Fin 4, i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) i
  rw [axisPath_one_eq, axisPath_one_eq]
  constructor
  · intro h0
    rcases hcases with rfl | rfl | rfl | rfl
    · rw [hself, axisSegment_add_one h0, hzero' 1 (by decide), hzero' 2 (by decide), hzero' 3 (by decide),
        hzero 1 (by decide), hzero 2 (by decide), hzero 3 (by decide)]
      simp
    · rw [hself, axisSegment_add_one h0, hoth 0 (by decide), hzero' 2 (by decide), hzero' 3 (by decide),
        hzero 2 (by decide), hzero 3 (by decide)]
      simp
    · rw [hself, axisSegment_add_one h0, hoth 0 (by decide), hoth 1 (by decide), hzero' 3 (by decide),
        hzero 3 (by decide)]
      simp
    · rw [hself, axisSegment_add_one h0, hoth 0 (by decide), hoth 1 (by decide), hoth 2 (by decide)]
      simp
  · intro h0
    rcases hcases with rfl | rfl | rfl | rfl
    · rw [hself, axisSegment_of_neg h0, hzero' 1 (by decide), hzero' 2 (by decide), hzero' 3 (by decide),
        hzero 1 (by decide), hzero 2 (by decide), hzero 3 (by decide)]
      simp
    · rw [hself, axisSegment_of_neg h0, hoth 0 (by decide), hzero' 2 (by decide), hzero' 3 (by decide),
        hzero 2 (by decide), hzero 3 (by decide)]
      simp
    · rw [hself, axisSegment_of_neg h0, hoth 0 (by decide), hoth 1 (by decide), hzero' 3 (by decide),
        hzero 3 (by decide)]
      simp
    · rw [hself, axisSegment_of_neg h0, hoth 0 (by decide), hoth 1 (by decide), hoth 2 (by decide)]
      simp
theorem axialGauge_treeBond (hL : Odd F.blockSide) (hs : ∀ i, 2 ≤ F.extent i) (W : F.GaugeField F.depth)
    (x : F.Site F.depth) (i : Fin 4) (ht : IsAxialTreeBond (x, i)) :
    gaugeTransform (axialGauge 1 W) W x i = 1 := by
  obtain ⟨z, h, hh, rfl⟩ := exists_centre_add hL hs x
  have htree := (isAxialTreeBond_iff hL hs z h hh i).mp ht
  obtain ⟨hne, hz⟩ := htree
  simp only at hne hz
  have hc := (mem_centredCube_iff h).mp hh
  have hin : (h + Pi.single i 1 : Fin 4 → ℤ) ∈ centredCube F.blockSide := by
    rw [mem_centredCube_iff]
    intro l
    by_cases hl : l = i
    · subst hl
      simp only [Pi.add_apply, Pi.single_eq_same]
      have := hc l
      omega
    · simp only [Pi.add_apply, Pi.single_eq_of_ne hl, add_zero]
      exact hc l
  have t1 : axialGauge 1 W (cellCentre F.depth z + siteOfCoords F.depth h) =
      pathHolonomy W (cellCentre F.depth z) (axisPath h 1) := by
    unfold axialGauge
    rw [enclosingCell_centre_add hL hs z h hh, cellOffset_centre_add hL hs z h hh]
  have t2 : axialGauge 1 W (cellCentre F.depth z + siteOfCoords F.depth h + unitStep F.depth i) =
      pathHolonomy W (cellCentre F.depth z) (axisPath (h + Pi.single i 1 : Fin 4 → ℤ) 1) := by
    unfold axialGauge
    rw [centre_add_add_unitStep, enclosingCell_centre_add hL hs z _ hin, cellOffset_centre_add hL hs z _ hin]
  obtain ⟨lp, ln⟩ := axisPath_add_single h i hz
  unfold gaugeTransform
  rw [t1, t2]
  rcases le_or_gt 0 (h i) with h0 | h0
  · rw [lp h0, pathHolonomy_append, axisPath_displacement]
    simp [pathHolonomy, linkValue, stepDisplacement]
  · rw [ln h0, pathHolonomy_append, axisPath_displacement]
    have e : cellCentre F.depth z + siteOfCoords F.depth (h + Pi.single i 1 : Fin 4 → ℤ) - unitStep F.depth i =
        cellCentre F.depth z + siteOfCoords F.depth h := by
      rw [← centre_add_add_unitStep]
      abel
    simp [pathHolonomy, linkValue, e]
theorem axialGauge_eq_chartedField (hL : Odd F.blockSide) (hs : ∀ i, 2 ≤ F.extent i) (V : F.GaugeField F.top)
    (W : F.GaugeField F.depth) (x : F.Site F.depth) (i : Fin 4) :
    gaugeTransform (axialGauge 1 W) W x i =
      chartedField (fun x i => bondCoordinate 1 V W (x, i)) V x i := by
  unfold chartedField
  split_ifs with h1 h2
  · simp only [bondCoordinate, if_pos h1, expUnit_minimalLog]
    group
  · exact axialGauge_treeBond hL hs W x i h2
  · simp only [bondCoordinate, if_neg h1, expUnit_minimalLog]
theorem gauge_eq_one_on_sites (hL : Odd F.blockSide) (hs : ∀ i, 2 ≤ F.extent i) {S : Finset F.Cell}
    (γ : F.Site F.depth → UnitQuaternion) (h1 : ∀ z, γ (cellCentre F.depth z) = 1)
    (hb : ∀ b ∈ innerBonds S F.depth, IsAxialTreeBond b → γ b.1 = γ (b.1 + unitStep F.depth b.2)) :
    ∀ z ∈ S, ∀ h ∈ centredCube F.blockSide, γ (cellCentre F.depth z + siteOfCoords F.depth h) = 1 := by
  intro z hz
  have hcube : ∀ h ∈ centredCube F.blockSide,
      (cellCentre F.depth z + siteOfCoords F.depth h : F.Site F.depth) ∈ sitesOfCells S F.depth := by
    intro h hh
    rw [mem_sitesOfCells]
    refine ⟨z, hz, h, ?_, rfl⟩
    rw [top_sub_depth, pow_one]
    exact hh
  have key : ∀ (m : ℕ) (h : Fin 4 → ℤ), (∑ i, (h i).natAbs) = m → h ∈ centredCube F.blockSide →
      γ (cellCentre F.depth z + siteOfCoords F.depth h) = 1 := by
    intro m
    induction m using Nat.strong_induction_on with
    | _ m ih =>
      intro h hm hh
      by_cases hall : ∀ i, h i = 0
      · have e : h = 0 := funext hall
        rw [e, siteOfCoords_zero, add_zero]
        exact h1 z
      · obtain ⟨l, hl, hlz⟩ : ∃ l, h l ≠ 0 ∧ ∀ l', l < l' → h l' = 0 := by
          classical
          have hne : (Finset.univ.filter fun i => h i ≠ 0).Nonempty := by
            push Not at hall
            obtain ⟨i, hi⟩ := hall
            exact ⟨i, by simpa using hi⟩
          refine ⟨(Finset.univ.filter fun i => h i ≠ 0).max' hne, ?_, fun l' hl' => ?_⟩
          · exact (Finset.mem_filter.mp (Finset.max'_mem _ hne)).2
          · by_contra hc
            exact absurd (Finset.le_max' _ l' (by simpa using hc)) (not_le.mpr hl')
        have hc := (mem_centredCube_iff h).mp hh
        rcases lt_or_gt_of_ne hl with hneg | hpos
        · set h' : Fin 4 → ℤ := h + Pi.single l 1 with hh'
          have hin : h' ∈ centredCube F.blockSide := by
            rw [mem_centredCube_iff]
            intro i
            by_cases hi : i = l
            · subst hi
              simp only [hh', Pi.add_apply, Pi.single_eq_same]
              have := hc i
              omega
            · simp only [hh', Pi.add_apply, Pi.single_eq_of_ne hi, add_zero]
              exact hc i
          have hless : ∑ i, (h' i).natAbs < m := by
            rw [← hm]
            refine Finset.sum_lt_sum (fun i _ => ?_) ⟨l, Finset.mem_univ _, ?_⟩
            · by_cases hi : i = l
              · subst hi
                simp only [hh', Pi.add_apply, Pi.single_eq_same]
                omega
              · simp [hh', Pi.single_eq_of_ne hi]
            · simp only [hh', Pi.add_apply, Pi.single_eq_same]
              omega
          have hrec := ih _ hless h' rfl hin
          have htr : IsAxialTreeBond ((cellCentre F.depth z + siteOfCoords F.depth h : F.Site F.depth), l) := by
            rw [isAxialTreeBond_iff hL hs z h hh l]
            refine ⟨?_, hlz⟩
            have : 0 ≤ halfWidth F.blockSide := by
              have := hc l
              omega
            simp only
            omega
          have hbond : ((cellCentre F.depth z + siteOfCoords F.depth h : F.Site F.depth), l) ∈
              innerBonds S F.depth := by
            unfold innerBonds
            refine Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hcube h hh, Finset.mem_univ _⟩, ?_⟩
            simp only
            rw [centre_add_add_unitStep]
            exact hcube _ hin
          have := hb _ hbond htr
          simp only at this
          rw [this, centre_add_add_unitStep]
          exact hrec
        · set h' : Fin 4 → ℤ := h + Pi.single l (-1) with hh'
          have hin : h' ∈ centredCube F.blockSide := by
            rw [mem_centredCube_iff]
            intro i
            by_cases hi : i = l
            · subst hi
              simp only [hh', Pi.add_apply, Pi.single_eq_same]
              have := hc i
              omega
            · simp only [hh', Pi.add_apply, Pi.single_eq_of_ne hi, add_zero]
              exact hc i
          have hless : ∑ i, (h' i).natAbs < m := by
            rw [← hm]
            refine Finset.sum_lt_sum (fun i _ => ?_) ⟨l, Finset.mem_univ _, ?_⟩
            · by_cases hi : i = l
              · subst hi
                simp only [hh', Pi.add_apply, Pi.single_eq_same]
                omega
              · simp [hh', Pi.single_eq_of_ne hi]
            · simp only [hh', Pi.add_apply, Pi.single_eq_same]
              omega
          have hrec := ih _ hless h' rfl hin
          have hnext : (h' + Pi.single l 1 : Fin 4 → ℤ) = h := by
            funext i
            by_cases hi : i = l
            · subst hi
              simp [hh']
            · simp [hh', Pi.single_eq_of_ne hi]
          have htr : IsAxialTreeBond ((cellCentre F.depth z + siteOfCoords F.depth h' : F.Site F.depth), l) := by
            rw [isAxialTreeBond_iff hL hs z h' hin l]
            refine ⟨?_, fun l' hl' => ?_⟩
            · simp only [hh', Pi.add_apply, Pi.single_eq_same]
              have := hc l
              omega
            · simp only [hh', Pi.add_apply, Pi.single_eq_of_ne hl'.ne', add_zero]
              exact hlz l' hl'
          have hbond : ((cellCentre F.depth z + siteOfCoords F.depth h' : F.Site F.depth), l) ∈
              innerBonds S F.depth := by
            unfold innerBonds
            refine Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hcube h' hin, Finset.mem_univ _⟩, ?_⟩
            simp only
            rw [centre_add_add_unitStep, hnext]
            exact hcube _ hh
          have := hb _ hbond htr
          simp only at this
          rw [centre_add_add_unitStep, hnext] at this
          rw [← this]
          exact hrec
  exact fun h hh => key _ h rfl hh
theorem minimizingChart_unique (hL : Odd F.blockSide) (hs : ∀ i, 2 ≤ F.extent i) {a ρ : ℝ}
    (hπ : ρ < Real.pi) {S : Finset F.Cell} {V : F.GaugeField F.top}
    {w₁ w₂ : F.Site F.depth → Fin 4 → imaginaryQuaternions}
    (h₁ : IsMinimizingChart a S V ρ w₁) (h₂ : IsMinimizingChart a S V ρ w₂)
    (hone : ∀ W', (∀ W'', blockEnergy a S F.depth W' V ≤ blockEnergy a S F.depth W'' V) →
      ∃ γ : F.Site F.depth → UnitQuaternion, (∀ z, γ (cellCentre F.depth z) = 1) ∧
        AgreeOnBonds S F.depth W' (gaugeTransform γ (chartedField w₂ V))) : w₁ = w₂ := by
  classical
  obtain ⟨γ, hγ, hsame⟩ := hone _ h₁.2.2
  have htreeval : ∀ (w : F.Site F.depth → Fin 4 → imaginaryQuaternions) (b : F.Site F.depth × Fin 4),
      IsAxialTreeBond b → chartedField w V b.1 b.2 = 1 := by
    intro w b hb
    unfold chartedField
    rw [if_neg hb.1, if_pos hb]
  have hb : ∀ b ∈ innerBonds S F.depth, IsAxialTreeBond b → γ b.1 = γ (b.1 + unitStep F.depth b.2) := by
    intro b hbS ht
    have h := hsame b hbS
    rw [htreeval w₁ b ht] at h
    unfold gaugeTransform at h
    rw [htreeval w₂ b ht, mul_one] at h
    exact (mul_inv_eq_one.mp h.symm)
  have hone' := gauge_eq_one_on_sites hL hs γ hγ hb
  have hsite : ∀ x ∈ sitesOfCells S F.depth, γ x = 1 := by
    intro x hx
    obtain ⟨y, hy, h, hh, rfl⟩ := mem_sitesOfCells.mp hx
    rw [top_sub_depth, pow_one] at hh
    exact hone' y hy h hh
  funext x i
  by_cases hc : (x, i) ∈ chordBonds S
  · have hbS := (Finset.mem_filter.mp hc).1
    have hnt := (Finset.mem_filter.mp hc).2
    have hx1 : x ∈ sitesOfCells S F.depth := (Finset.mem_product.mp (Finset.mem_filter.mp hbS).1).1
    have hx2 : x + unitStep F.depth i ∈ sitesOfCells S F.depth := (Finset.mem_filter.mp hbS).2
    have h := hsame _ hbS
    simp only [gaugeTransform, hsite x hx1, hsite _ hx2, one_mul, inv_one, mul_one] at h
    have n1 : ‖((w₁ x i : imaginaryQuaternions) : ℍ[ℝ])‖ < Real.pi := lt_of_le_of_lt (h₁.2.1 _ hc) hπ
    have n2 : ‖((w₂ x i : imaginaryQuaternions) : ℍ[ℝ])‖ < Real.pi := lt_of_le_of_lt (h₂.2.1 _ hc) hπ
    apply expUnit_injective_of_norm_lt_pi n1 n2
    unfold chartedField at h
    by_cases hcr : IsCrossingBond (x, i)
    · rw [if_pos hcr, if_pos hcr] at h
      exact mul_right_cancel h
    · rw [if_neg hcr, if_neg hcr, if_neg hnt, if_neg hnt] at h
      exact h
  · rw [h₁.1 _ hc, h₂.1 _ hc]
theorem minimizingCoordinates_eq {a ρ ρ₀ N0 s : ℝ} (hL : Odd F.blockSide) (hs : ∀ i, 2 ≤ F.extent i)
    (hπ : ρ < Real.pi) (hρ : ρ₀ ≤ ρ) {S : Finset F.Cell} {V : F.GaugeField F.top}
    (hone : HasColdMinimizer a ρ₀ N0 s S V) :
    ∃ w, IsMinimizingChart a S V (min ρ₀ (N0 * s)) w ∧ IsCold S F.depth (s / 8) (chartedField w V) ∧
      minimizingCoordinates a S V ρ = w := by
  obtain ⟨w, hw, hcold, hu⟩ := hone
  refine ⟨w, hw, hcold, ?_⟩
  have hw' : IsMinimizingChart a S V ρ w :=
    ⟨hw.1, fun b hb => (hw.2.1 b hb).trans ((min_le_left _ _).trans hρ), hw.2.2⟩
  have hex : ∃ w, IsMinimizingChart a S V ρ w := ⟨w, hw'⟩
  unfold minimizingCoordinates
  rw [dif_pos hex]
  exact minimizingChart_unique hL hs hπ hex.choose_spec hw' hu
end Tree
end TopLevelSites
end YangMills.Construction
end
