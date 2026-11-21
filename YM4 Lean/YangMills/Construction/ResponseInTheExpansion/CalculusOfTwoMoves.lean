import YangMills.Construction.ColdChainAtEveryLevel.HolonomiesOnTheHullOfABond
import YangMills.Construction.ColdStepAtMirrorFrames.GapTermsOfTheExponentProof
import YangMills.Construction.ColdStepAtMirrorFrames.LieCoordinatesProof
import YangMills.Construction.SummableBoundsOfTheFlow.AdmittedObservables
import YangMills.Construction.SummableBoundsOfTheFlow.ShortMovesOfAChart
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction
open BlockAverages ColdStepAtMirrorFrames TorusComparison Interpolation
namespace SecondOrderMoves
variable {F F' : BlockFrame}
theorem norm_toImaginary (v : BondVector) : ‖toImaginary v‖ = ‖v‖ := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.ImaginaryCoordinates.norm_toImaginary <;> assumption
section BondPoints
variable {ι : Type} [Fintype ι] [DecidableEq ι]
theorem toTorus_zero (j : ι → ↥(chordBonds (finiteCells F))) : toTorus j (0 : BondField ι) = 0 := by
  funext b
  simp [toTorus, _root_.YangMills.Construction.Interpolation.extendByZero]
theorem toTorus_apply_self {j : ι → ↥(chordBonds (finiteCells F))} (hj : Function.Injective j) (ζ : BondField ι)
    (k : ι) : toTorus j ζ (j k) = ζ k := by
  simp only [toTorus, _root_.YangMills.Construction.Interpolation.extendByZero]
  rw [Finset.sum_eq_single k]
  · simp
  · intro i _ hi
    rw [if_neg fun h => hi (hj h)]
  · intro h
    exact absurd (Finset.mem_univ k) h
theorem toTorus_apply_of_forall_ne {j : ι → ↥(chordBonds (finiteCells F))} (ζ : BondField ι)
    {b : ↥(chordBonds (finiteCells F))} (hb : ∀ k, j k ≠ b) : toTorus j ζ b = 0 := by
  simp only [toTorus, _root_.YangMills.Construction.Interpolation.extendByZero]
  exact Finset.sum_eq_zero fun i _ => if_neg (hb i)
theorem norm_toTorus_le {j : ι → ↥(chordBonds (finiteCells F))} (hj : Function.Injective j) {ζ : BondField ι}
    {ρ : ℝ} (hρ : 0 ≤ ρ) (hζ : ∀ i, ‖ζ i‖ ≤ ρ) (b : ↥(chordBonds (finiteCells F))) : ‖toTorus j ζ b‖ ≤ ρ := by
  by_cases hb : ∃ k, j k = b
  · obtain ⟨k, rfl⟩ := hb
    rw [toTorus_apply_self hj]
    exact hζ k
  · push Not at hb
    rw [toTorus_apply_of_forall_ne ζ hb]
    simpa using hρ
theorem stepCoordinates_toTorus_apply {j : ι → ↥(chordBonds (finiteCells F))} (hj : Function.Injective j) (ζ : BondField ι)
    (k : ι) : stepCoordinates (toTorus j ζ) (j k).1.1 (j k).1.2 = toImaginary (ζ k) := by
  have hmem : ((j k).1.1, (j k).1.2) ∈ chordBonds (finiteCells F) := (j k).2
  unfold stepCoordinates
  rw [dif_pos hmem]
  exact congrArg toImaginary (toTorus_apply_self hj ζ k)
theorem norm_stepCoordinates_le (η : StepVariable (finiteCells F)) {ρ : ℝ} (hρ : 0 ≤ ρ) (hη : ∀ b, ‖η b‖ ≤ ρ)
    (z : F.Site F.depth) (i : Fin 4) : ‖stepCoordinates η z i‖ ≤ ρ := by
  unfold stepCoordinates
  split_ifs with h
  · rw [norm_toImaginary]
    exact hη _
  · simpa using hρ
theorem contDiffAt_deriv_of_contDiffAt_two {φ : ℝ → ℝ} {v : ℝ} (h : ContDiffAt ℝ 2 φ v) : ContDiffAt ℝ 1 (deriv φ) v := by
  have e : deriv φ = fun u => fderiv ℝ φ u 1 := by
    funext u
    rw [fderiv_eq_smul_deriv, one_smul]
  rw [e]
  exact (h.fderiv_right (m := 1) (by norm_num)).clm_apply contDiffAt_const
theorem abs_sub_le_of_abs_le_of_second_deriv {φ : ℝ → ℝ} {a τ ε A : ℝ} (ha : 0 ≤ a) (hτ : 0 < τ)
    (hφ : ∀ v ∈ Set.Icc 0 (a + τ), ContDiffAt ℝ 2 φ v) (hb : ∀ v ∈ Set.Icc 0 (a + τ), |φ v| ≤ ε)
    (h2 : ∀ v ∈ Set.Icc 0 (a + τ), |deriv (deriv φ) v| ≤ A) :
    |φ a - φ 0| ≤ a * (2 * ε / τ + τ * A) := by
  have hd1 : ∀ v ∈ Set.Icc 0 (a + τ), HasDerivAt φ (deriv φ v) v := fun v hv =>
    ((hφ v hv).differentiableAt (by norm_num)).hasDerivAt
  have hd2 : ∀ v ∈ Set.Icc 0 (a + τ), HasDerivAt (deriv φ) (deriv (deriv φ) v) v := fun v hv =>
    (contDiffAt_deriv_of_contDiffAt_two (hφ v hv)).differentiableAt (by norm_num) |>.hasDerivAt
  have key : ∀ v ∈ Set.Icc 0 a, ‖deriv φ v‖ ≤ 2 * ε / τ + τ * A := by
    intro v hv
    have hsub : Set.Icc v (v + τ) ⊆ Set.Icc 0 (a + τ) := fun y hy =>
      ⟨hv.1.trans hy.1, hy.2.trans (by linarith [hv.2])⟩
    obtain ⟨c, hc, hce⟩ := exists_hasDerivAt_eq_slope φ (deriv φ) (show v < v + τ by linarith)
      (fun y hy => (hd1 y (hsub hy)).continuousAt.continuousWithinAt)
      (fun y hy => hd1 y (hsub ⟨hy.1.le, hy.2.le⟩))
    have hc' : c ∈ Set.Icc v (v + τ) := ⟨hc.1.le, hc.2.le⟩
    have hdiff : ‖deriv φ c - deriv φ v‖ ≤ A * ‖c - v‖ :=
      Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (s := Set.Icc v (v + τ)) (f := deriv φ)
        (f' := deriv (deriv φ)) (fun y hy => (hd2 y (hsub hy)).hasDerivWithinAt)
        (fun y hy => h2 y (hsub hy)) (convex_Icc _ _) ⟨le_rfl, by linarith⟩ hc'
    have hcv : ‖c - v‖ ≤ τ := by
      rw [Real.norm_eq_abs, abs_of_pos (by linarith [hc.1])]
      linarith [hc.2]
    have hA0 : 0 ≤ A := (abs_nonneg _).trans (h2 v (hsub ⟨le_rfl, by linarith⟩))
    have hs : |deriv φ c| ≤ 2 * ε / τ := by
      rw [hce, abs_div, abs_of_pos (show 0 < v + τ - v by linarith), show v + τ - v = τ by ring]
      refine div_le_div_of_nonneg_right ?_ hτ.le
      have b1 := hb _ (hsub ⟨by linarith, le_rfl⟩)
      have b2 := hb _ (hsub ⟨le_rfl, by linarith⟩)
      exact (abs_sub _ _).trans (by linarith)
    have h3 : ‖deriv φ v‖ ≤ ‖deriv φ c‖ + ‖deriv φ c - deriv φ v‖ := by
      have := norm_sub_le (deriv φ c) (deriv φ c - deriv φ v)
      simpa using this
    rw [Real.norm_eq_abs (deriv φ c)] at h3
    have h4 := mul_le_mul_of_nonneg_left hcv hA0
    nlinarith
  have hsub0 : Set.Icc 0 a ⊆ Set.Icc 0 (a + τ) := fun y hy => ⟨hy.1, hy.2.trans (by linarith)⟩
  have := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (s := Set.Icc 0 a) (f := φ) (f' := deriv φ)
    (fun y hy => (hd1 y (hsub0 hy)).hasDerivWithinAt) key (convex_Icc _ _) (⟨le_rfl, ha⟩ : (0 : ℝ) ∈ Set.Icc 0 a)
    (⟨ha, le_rfl⟩ : a ∈ Set.Icc 0 a)
  rw [Real.norm_eq_abs, Real.norm_eq_abs, sub_zero, abs_of_nonneg ha] at this
  linarith
theorem abs_sub_zero_le_of_second_deriv_along_bonds {ρ ε A : ℝ} (hρ : 0 < ρ) (hε : 0 < ε) (hA : 0 ≤ A) {g : BondField ι → ℝ}
    (hval : ∀ ζ : BondField ι, (∀ i, ‖ζ i‖ < ρ) → |g ζ| ≤ ε)
    (hline : ∀ ζ : BondField ι, (∀ i, ‖ζ i‖ < ρ) → ∀ (i : ι) (e : BondVector), ‖e‖ = 1 →
      ContDiffAt ℝ 2 (fun τ : ℝ => g (ζ + Pi.single i (τ • e))) 0 ∧
        |deriv (deriv fun τ : ℝ => g (ζ + Pi.single i (τ • e))) 0| ≤ A)
    {ζ : BondField ι} (hζ : ∀ i, ‖ζ i‖ < ρ) :
    |g ζ - g 0| ≤ (2 * Real.sqrt ε + 4 * ε / ρ + Real.sqrt ε * A) * ∑ i, ‖ζ i‖ := by
  set B := 2 * Real.sqrt ε + 4 * ε / ρ + Real.sqrt ε * A with hB
  have hsε : 0 < Real.sqrt ε := Real.sqrt_pos.2 hε
  have h00 : ∀ i, ‖(0 : BondField ι) i‖ < ρ := fun i => by simpa using hρ
  by_cases hbig : ∃ i, ρ / 2 ≤ ‖ζ i‖
  · obtain ⟨i, hi⟩ := hbig
    have h1 : |g ζ - g 0| ≤ 2 * ε := (abs_sub _ _).trans (by linarith [hval ζ hζ, hval 0 h00])
    have h2 : ‖ζ i‖ ≤ ∑ i, ‖ζ i‖ := Finset.single_le_sum (f := fun i => ‖ζ i‖) (fun _ _ => norm_nonneg _) (Finset.mem_univ i)
    have h3 : ρ / 2 ≤ ∑ i, ‖ζ i‖ := hi.trans h2
    have h4 : 4 * ε / ρ ≤ B := by
      have : 0 ≤ Real.sqrt ε * A := by positivity
      linarith
    calc _ ≤ 2 * ε := h1
      _ = 4 * ε / ρ * (ρ / 2) := by field_simp; ring
      _ ≤ 4 * ε / ρ * ∑ i, ‖ζ i‖ := mul_le_mul_of_nonneg_left h3 (by positivity)
      _ ≤ B * ∑ i, ‖ζ i‖ := mul_le_mul_of_nonneg_right h4 (Finset.sum_nonneg fun _ _ => norm_nonneg _)
  push Not at hbig
  set τ : ℝ := min (Real.sqrt ε) (ρ / 2) with hτ
  have hτ0 : 0 < τ := lt_min hsε (by positivity)
  have hτ1 : τ ≤ Real.sqrt ε := min_le_left _ _
  have hτ2 : τ ≤ ρ / 2 := min_le_right _ _
  have hrate : 2 * ε / τ + τ * A ≤ B := by
    have e1 : 2 * ε / τ ≤ 2 * Real.sqrt ε + 4 * ε / ρ := by
      rcases le_total (Real.sqrt ε) (ρ / 2) with h | h
      · have : τ = Real.sqrt ε := min_eq_left h
        rw [this]
        have e2 : 2 * ε / Real.sqrt ε = 2 * Real.sqrt ε := by
          have := Real.sq_sqrt hε.le
          field_simp
          nlinarith
        rw [e2]
        have : 0 ≤ 4 * ε / ρ := by positivity
        linarith
      · have : τ = ρ / 2 := min_eq_right h
        rw [this]
        have e2 : 2 * ε / (ρ / 2) = 4 * ε / ρ := by field_simp; ring
        rw [e2]
        linarith
    have e3 : τ * A ≤ Real.sqrt ε * A := mul_le_mul_of_nonneg_right hτ1 hA
    linarith
  let restr : Finset ι → BondField ι := fun s i => if i ∈ s then ζ i else 0
  have hstep : ∀ s : Finset ι, |g (restr s) - g 0| ≤ B * ∑ i ∈ s, ‖ζ i‖ := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      have : restr ∅ = 0 := by
        funext i
        simp [restr]
      simp [this]
    | insert i s hi ih =>
      rw [Finset.sum_insert hi, mul_add]
      have hone : |g (restr (insert i s)) - g (restr s)| ≤ B * ‖ζ i‖ := by
        set a := ‖ζ i‖ with ha
        by_cases ha0 : a = 0
        · have h0 : ζ i = 0 := norm_eq_zero.1 ha0
          have : restr (insert i s) = restr s := by
            funext k
            by_cases hk : k = i
            · subst hk
              simp [restr, hi, h0]
            · simp [restr, Finset.mem_insert, hk]
          rw [this, ha0]
          simp
        have hap : 0 < a := lt_of_le_of_ne (norm_nonneg _) (Ne.symm ha0)
        set e : BondVector := a⁻¹ • ζ i with he
        have he1 : ‖e‖ = 1 := by
          rw [he, norm_smul, norm_inv, Real.norm_of_nonneg hap.le, ← ha]
          field_simp
        let φ : ℝ → ℝ := fun v => g (restr s + Pi.single i (v • e))
        have hpt : ∀ v ∈ Set.Icc 0 (a + τ), ∀ k, ‖(restr s + Pi.single i (v • e) : BondField ι) k‖ < ρ := by
          intro v hv k
          by_cases hk : k = i
          · subst hk
            simp only [Pi.add_apply, restr, hi, if_false, Pi.single_eq_same, zero_add, norm_smul, he1, mul_one,
              Real.norm_eq_abs, abs_of_nonneg hv.1]
            have := hbig k
            linarith [hv.2]
          · simp only [Pi.add_apply, Pi.single_eq_of_ne hk, add_zero, restr]
            split_ifs
            · exact hζ k
            · simpa using hρ
        have hshift : ∀ v u : ℝ, restr s + Pi.single i (v • e) + Pi.single i (u • e) = restr s + Pi.single i ((v + u) • e) := by
          intro v u
          rw [add_assoc, ← Pi.single_add, add_smul]
        have hl : ∀ v ∈ Set.Icc 0 (a + τ), ContDiffAt ℝ 2 φ v ∧ |deriv (deriv φ) v| ≤ A := by
          intro v hv
          obtain ⟨h1, h2⟩ := hline _ (hpt v hv) i e he1
          have e1 : (fun τ : ℝ => g (restr s + Pi.single i (v • e) + Pi.single i (τ • e))) = fun τ => φ (v + τ) := by
            funext τ
            simp only [φ]
            rw [hshift]
          rw [e1] at h1 h2
          constructor
          · have e2 : φ = (fun τ => φ (v + τ)) ∘ fun u => u - v := by
              funext u
              simp
            rw [e2]
            refine ContDiffAt.comp (g := fun τ => φ (v + τ)) (f := fun u => u - v) v ?_ (contDiffAt_id.sub contDiffAt_const)
            simpa using h1
          · have e3 : deriv (fun τ => φ (v + τ)) = fun τ => deriv φ (v + τ) := by
              funext τ
              exact deriv_comp_const_add φ v τ
            rw [e3] at h2
            have e4 : deriv (fun τ => deriv φ (v + τ)) 0 = deriv (deriv φ) (v + 0) :=
              deriv_comp_const_add (deriv φ) v 0
            rw [e4, add_zero] at h2
            exact h2
        have hm := abs_sub_le_of_abs_le_of_second_deriv (φ := φ) (a := a) (τ := τ) (ε := ε) (A := A) hap.le hτ0 (fun v hv => (hl v hv).1)
          (fun v hv => hval _ (hpt v hv)) (fun v hv => (hl v hv).2)
        have e5 : φ a = g (restr (insert i s)) := by
          simp only [φ]
          congr 1
          funext k
          by_cases hk : k = i
          · subst hk
            simp [restr, hi, he, ha, smul_smul, mul_inv_cancel₀ (show ‖ζ k‖ ≠ 0 from ha0)]
          · simp [restr, Finset.mem_insert, hk]
        have e6 : φ 0 = g (restr s) := by
          simp [φ]
        rw [e5, e6] at hm
        refine hm.trans ?_
        rw [mul_comm B]
        exact mul_le_mul_of_nonneg_left hrate hap.le
      have := abs_sub_le (g (restr (insert i s))) (g (restr s)) (g 0)
      linarith
  have : restr Finset.univ = ζ := by
    funext i
    simp [restr]
  have h := hstep Finset.univ
  rwa [this] at h
end BondPoints
section RealVariable
theorem deriv_deriv_sub {φ ψ : ℝ → ℝ} {v : ℝ} (hφ : ContDiffAt ℝ 2 φ v) (hψ : ContDiffAt ℝ 2 ψ v) :
    deriv (deriv fun τ => φ τ - ψ τ) v = deriv (deriv φ) v - deriv (deriv ψ) v := by
  have h1 : ∀ᶠ y in nhds v, ContDiffAt ℝ 2 φ y := hφ.eventually (by simp)
  have h2 : ∀ᶠ y in nhds v, ContDiffAt ℝ 2 ψ y := hψ.eventually (by simp)
  have e : deriv (fun τ => φ τ - ψ τ) =ᶠ[nhds v] fun y => deriv φ y - deriv ψ y := by
    filter_upwards [h1, h2] with y a b
    exact deriv_fun_sub (a.differentiableAt (by norm_num)) (b.differentiableAt (by norm_num))
  rw [e.deriv_eq]
  exact deriv_fun_sub (contDiffAt_deriv_of_contDiffAt_two hφ |>.differentiableAt (by norm_num))
    (contDiffAt_deriv_of_contDiffAt_two hψ |>.differentiableAt (by norm_num))
def bondMoveConstant (K A ρ : ℝ) : ℝ := 2 * Real.sqrt K + 4 * K / ρ + Real.sqrt K * A
theorem bondMoveConstant_nonneg {K A ρ : ℝ} (hK : 0 ≤ K) (hA : 0 ≤ A) (hρ : 0 < ρ) : 0 ≤ bondMoveConstant K A ρ := by
  unfold bondMoveConstant
  positivity
theorem abs_sub_zero_le_of_exp_small {ι : Type} [Fintype ι] [DecidableEq ι] {ρ K A c : ℝ} {q : ℕ} (hρ : 0 < ρ) (hK : 0 < K) (hA : 0 ≤ A)
    (hc : 0 ≤ c) {g : BondField ι → ℝ}
    (hval : ∀ ζ : BondField ι, (∀ i, ‖ζ i‖ < ρ) → |g ζ| ≤ K * Real.exp (-(c * q)))
    (hline : ∀ ζ : BondField ι, (∀ i, ‖ζ i‖ < ρ) → ∀ (i : ι) (e : BondVector), ‖e‖ = 1 →
      ContDiffAt ℝ 2 (fun τ : ℝ => g (ζ + Pi.single i (τ • e))) 0 ∧
        |deriv (deriv fun τ : ℝ => g (ζ + Pi.single i (τ • e))) 0| ≤ A)
    {ζ : BondField ι} (hζ : ∀ i, ‖ζ i‖ < ρ) :
    |g ζ - g 0| ≤ bondMoveConstant K A ρ * Real.exp (-(c / 2 * q)) * ∑ i, ‖ζ i‖ := by
  set ε := K * Real.exp (-(c * q)) with hε
  have hε0 : 0 < ε := by positivity
  have h := abs_sub_zero_le_of_second_deriv_along_bonds hρ hε0 hA hval hline hζ
  refine h.trans (mul_le_mul_of_nonneg_right ?_ (Finset.sum_nonneg fun _ _ => norm_nonneg _))
  have hs : Real.sqrt ε = Real.sqrt K * Real.exp (-(c / 2 * q)) := by
    have e : Real.exp (-(c * q)) = Real.exp (-(c / 2 * q)) ^ 2 := by
      rw [← Real.exp_nat_mul]
      congr 1
      push_cast
      ring
    rw [hε, Real.sqrt_mul hK.le, e, Real.sqrt_sq (Real.exp_pos _).le]
  have h2 : ε ≤ K * Real.exp (-(c / 2 * q)) := by
    have : Real.exp (-(c * q)) ≤ Real.exp (-(c / 2 * q)) := by
      apply Real.exp_le_exp.2
      have : 0 ≤ c * q := by positivity
      linarith
    exact mul_le_mul_of_nonneg_left this hK.le
  rw [hs]
  unfold bondMoveConstant
  have h3 : 4 * ε / ρ ≤ 4 * K / ρ * Real.exp (-(c / 2 * q)) := by
    rw [div_mul_eq_mul_div]
    apply div_le_div_of_nonneg_right _ hρ.le
    linarith
  nlinarith
theorem pow_four_mul_exp_le {d : ℝ} (hd : 0 < d) (q : ℕ) :
    (2 * (q : ℝ) + 1) ^ 4 * Real.exp (-(d / 8 * q)) ≤ (128 / d) ^ 4 * Real.exp (d / 32) * Real.exp (-(d / 16 * q)) := by
  set s := d / 128 with hs
  have h1 : s * (2 * (q : ℝ) + 1) ≤ Real.exp (s * (2 * (q : ℝ) + 1)) := by
    have := Real.add_one_le_exp (s * (2 * (q : ℝ) + 1))
    linarith
  have h2 : (s * (2 * (q : ℝ) + 1)) ^ 4 ≤ Real.exp (s * (2 * (q : ℝ) + 1)) ^ 4 :=
    pow_le_pow_left₀ (by positivity) h1 4
  have h3 : Real.exp (s * (2 * (q : ℝ) + 1)) ^ 4 = Real.exp (d / 16 * q) * Real.exp (d / 32) := by
    rw [← Real.exp_nat_mul, ← Real.exp_add]
    congr 1
    rw [hs]
    push_cast
    ring
  have h4 : (2 * (q : ℝ) + 1) ^ 4 ≤ (128 / d) ^ 4 * (Real.exp (d / 16 * q) * Real.exp (d / 32)) := by
    rw [← h3]
    have e : (128 / d) = s⁻¹ := by
      rw [hs]
      field_simp
    rw [e]
    rw [mul_pow] at h2
    have hp : 0 < s ^ 4 := by positivity
    rw [inv_pow]
    rw [inv_mul_eq_div, le_div_iff₀ hp]
    linarith
  have h5 : Real.exp (d / 16 * q) * Real.exp (-(d / 8 * q)) = Real.exp (-(d / 16 * q)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  calc (2 * (q : ℝ) + 1) ^ 4 * Real.exp (-(d / 8 * q))
      ≤ (128 / d) ^ 4 * (Real.exp (d / 16 * q) * Real.exp (d / 32)) * Real.exp (-(d / 8 * q)) :=
        mul_le_mul_of_nonneg_right h4 (Real.exp_pos _).le
    _ = (128 / d) ^ 4 * Real.exp (d / 32) * (Real.exp (d / 16 * q) * Real.exp (-(d / 8 * q))) := by ring
    _ = _ := by rw [h5]
end RealVariable
section ContourAverages
theorem norm_unitQuaternion (g : UnitQuaternion) : ‖(g : ℍ[ℝ])‖ = 1 := CStarRing.norm_coe_unitary g
theorem norm_contour_mean_le {G : BlockFrame} (hL : Odd G.blockSide) (z : (Fin 4 → ℤ) → Equiv.Perm (Fin 4) → ℍ[ℝ]) {B : ℝ}
    (hz : ∀ h ∈ centredCube G.blockSide, ∀ π, ‖z h π‖ ≤ B) :
    ‖(1 / (24 * (G.blockSide : ℝ) ^ 4)) • ∑ h ∈ centredCube G.blockSide, ∑ π : Equiv.Perm (Fin 4), z h π‖ ≤ B := by apply _root_.YangMills.Construction.BondHull.norm_smul_sum_perm_le <;> assumption
theorem norm_contourAverage_sub_le (hM : ChartLipschitz.ChartedFieldLipschitz) {G : BlockFrame} (hL : Odd G.blockSide)
    (w w' : G.Site G.depth → Fin 4 → imaginaryQuaternions) (W : G.GaugeField G.top) {ε : ℝ} (hε : 0 ≤ ε)
    (hw : ∀ z i, ‖w z i - w' z i‖ ≤ ε) (c : G.Site G.top × Fin 4) :
    ‖_root_.YangMills.Construction.BlockAverages.contourAverage (chartedField w W) c - _root_.YangMills.Construction.BlockAverages.contourAverage (chartedField w' W) c‖ ≤ 5 * (G.blockSide : ℝ) * ε := by
  have e : _root_.YangMills.Construction.BlockAverages.contourAverage (chartedField w W) c - _root_.YangMills.Construction.BlockAverages.contourAverage (chartedField w' W) c =
      (1 / (24 * (G.blockSide : ℝ) ^ 4)) • ∑ h ∈ centredCube G.blockSide, ∑ π : Equiv.Perm (Fin 4),
        (((pathHolonomy (chartedField w W) (refineSite c.1) (bondContour G.blockSide h π c.2) : UnitQuaternion) : ℍ[ℝ]) -
          ((pathHolonomy (chartedField w' W) (refineSite c.1) (bondContour G.blockSide h π c.2) : UnitQuaternion) : ℍ[ℝ])) := by
    unfold _root_.YangMills.Construction.BlockAverages.contourAverage
    simp only [Finset.sum_sub_distrib, smul_sub]
  rw [e]
  refine norm_contour_mean_le hL _ fun h hh π => ?_
  have h1 := (hM.2 G w w' W ε hw hε).1 (refineSite c.1) (bondContour G.blockSide h π c.2)
  have h2 := LatticePaths.length_bondContour_le (L := G.blockSide) π c.2 hL.pos hh
  have h3 : ((bondContour G.blockSide h π c.2).length : ℝ) ≤ 5 * (G.blockSide : ℝ) := by exact_mod_cast h2
  exact h1.trans (mul_le_mul_of_nonneg_right h3 hε)
theorem norm_contourAverage_bounds {G : BlockFrame} (hL : Odd G.blockSide) (W : G.GaugeField G.depth) (V : G.GaugeField G.top)
    (c : G.Site G.top × Fin 4)
    (h : ∀ (h : Fin 4 → ℤ) (π : Equiv.Perm (Fin 4)), h ∈ centredCube G.blockSide → ‖contourHolonomyDefect W V c h π - 1‖ ≤ 1 / 2) :
    1 / 2 ≤ ‖contourAverage W c‖ ∧ ‖contourAverage W c‖ ≤ 1 := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.GapTerms.norm_contourAverage_mem_shell <;> assumption
end ContourAverages
section Increments
theorem abs_sub_sub_le_of_lipschitz_deriv {f f₁ : ℝ → ℝ} {lo hi M₁ M₂ : ℝ} (hM₂ : 0 ≤ M₂)
    (hf : ∀ u ∈ Set.Icc lo hi, HasDerivWithinAt f (f₁ u) (Set.Icc lo hi) u)
    (h₁ : ∀ u ∈ Set.Icc lo hi, |f₁ u| ≤ M₁) (h₂ : ∀ u ∈ Set.Icc lo hi, ∀ v ∈ Set.Icc lo hi, |f₁ u - f₁ v| ≤ M₂ * |u - v|)
    {a₀ a₁ b₀ b₁ : ℝ} (ha₀ : a₀ ∈ Set.Icc lo hi) (ha₁ : a₁ ∈ Set.Icc lo hi) (hb₀ : b₀ ∈ Set.Icc lo hi)
    (hb₁ : b₁ ∈ Set.Icc lo hi) :
    |(f a₁ - f a₀) - (f b₁ - f b₀)| ≤ M₁ * |(a₁ - a₀) - (b₁ - b₀)| +
      M₂ * (|a₀ - b₀| + |(a₁ - a₀) - (b₁ - b₀)|) * |b₁ - b₀| := by
  set R := M₁ * |(a₁ - a₀) - (b₁ - b₀)| + M₂ * (|a₀ - b₀| + |(a₁ - a₀) - (b₁ - b₀)|) * |b₁ - b₀| with hR
  have hseg : ∀ (p r : ℝ), p ∈ Set.Icc lo hi → r ∈ Set.Icc lo hi → ∀ s ∈ Set.Icc (0 : ℝ) 1, p + s * (r - p) ∈ Set.Icc lo hi := by
    intro p r hp hr s hs
    have := (convex_Icc lo hi).add_smul_sub_mem hp hr hs
    simpa using this
  set A : ℝ → ℝ := fun s => a₀ + s * (a₁ - a₀) with hA
  set B : ℝ → ℝ := fun s => b₀ + s * (b₁ - b₀) with hB
  have hd : ∀ (p r : ℝ), p ∈ Set.Icc lo hi → r ∈ Set.Icc lo hi → ∀ s ∈ Set.Icc (0 : ℝ) 1,
      HasDerivWithinAt (fun s => f (p + s * (r - p))) (f₁ (p + s * (r - p)) * (r - p)) (Set.Icc 0 1) s := by
    intro p r hp hr s hs
    have hl : HasDerivWithinAt (fun s : ℝ => p + s * (r - p)) (r - p) (Set.Icc 0 1) s := by
      simpa using (((hasDerivAt_id s).mul_const (r - p)).const_add p).hasDerivWithinAt
    exact (hf _ (hseg p r hp hr s hs)).comp s hl (fun s hs => hseg p r hp hr s hs)
  have hder : ∀ s ∈ Set.Icc (0 : ℝ) 1, HasDerivWithinAt (fun s => f (A s) - f (B s))
      (f₁ (A s) * (a₁ - a₀) - f₁ (B s) * (b₁ - b₀)) (Set.Icc 0 1) s := fun s hs =>
    (hd a₀ a₁ ha₀ ha₁ s hs).sub (hd b₀ b₁ hb₀ hb₁ s hs)
  have hbd : ∀ s ∈ Set.Ico (0 : ℝ) 1, ‖f₁ (A s) * (a₁ - a₀) - f₁ (B s) * (b₁ - b₀)‖ ≤ R := by
    intro s hs
    have hs' : s ∈ Set.Icc (0 : ℝ) 1 := ⟨hs.1, hs.2.le⟩
    have hAs := hseg a₀ a₁ ha₀ ha₁ s hs'
    have hBs := hseg b₀ b₁ hb₀ hb₁ s hs'
    have e : f₁ (A s) * (a₁ - a₀) - f₁ (B s) * (b₁ - b₀) =
        f₁ (A s) * ((a₁ - a₀) - (b₁ - b₀)) + (f₁ (A s) - f₁ (B s)) * (b₁ - b₀) := by ring
    rw [Real.norm_eq_abs, e]
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_mul]
    have t1 := h₁ _ hAs
    have t2 := h₂ _ hAs _ hBs
    have t3 : |A s - B s| ≤ |a₀ - b₀| + |(a₁ - a₀) - (b₁ - b₀)| := by
      have e2 : A s - B s = (a₀ - b₀) + s * ((a₁ - a₀) - (b₁ - b₀)) := by
        simp only [hA, hB]
        ring
      rw [e2]
      refine (abs_add_le _ _).trans (add_le_add le_rfl ?_)
      rw [abs_mul, abs_of_nonneg hs.1]
      have := abs_nonneg ((a₁ - a₀) - (b₁ - b₀))
      nlinarith [hs.2]
    have t4 : |f₁ (A s) - f₁ (B s)| ≤ M₂ * (|a₀ - b₀| + |(a₁ - a₀) - (b₁ - b₀)|) :=
      t2.trans (mul_le_mul_of_nonneg_left t3 hM₂)
    rw [hR]
    exact add_le_add (mul_le_mul_of_nonneg_right t1 (abs_nonneg _)) (mul_le_mul_of_nonneg_right t4 (abs_nonneg _))
  have h := norm_image_sub_le_of_norm_deriv_le_segment_01' hder hbd
  rw [Real.norm_eq_abs] at h
  have e : (f (A 1) - f (B 1)) - (f (A 0) - f (B 0)) = (f a₁ - f a₀) - (f b₁ - f b₀) := by
    simp only [hA, hB]
    ring_nf
  rw [e] at h
  exact h
theorem contDiffAt_and_iteratedFDeriv_comp_add {φ : ℝ → ℝ}
    (hψ : ContDiffAt ℝ 2 (fun σ : Fin 2 → ℝ => φ (σ 0 + σ 1)) 0) :
    ContDiffAt ℝ 2 φ 0 ∧
      iteratedFDeriv ℝ 2 (fun σ : Fin 2 → ℝ => φ (σ 0 + σ 1)) 0 (fun i => Pi.single i 1) = deriv (deriv φ) 0 := by
  have hφ : ContDiffAt ℝ 2 φ 0 := by
    have hl : ContDiffAt ℝ 2 (fun s : ℝ => (![s, 0] : Fin 2 → ℝ)) 0 := by
      have : (fun s : ℝ => (![s, 0] : Fin 2 → ℝ)) = fun s => s • (Pi.single 0 1 : Fin 2 → ℝ) := by
        funext s
        ext l
        fin_cases l <;> simp
      rw [this]
      exact contDiffAt_id.smul contDiffAt_const
    have h0 : (![0, 0] : Fin 2 → ℝ) = 0 := by
      ext l
      fin_cases l <;> simp
    have hc := ContDiffAt.comp (g := fun σ : Fin 2 → ℝ => φ (σ 0 + σ 1)) (f := fun s : ℝ => (![s, 0] : Fin 2 → ℝ)) (0 : ℝ)
      (by simpa [h0] using hψ) hl
    have e : ((fun σ : Fin 2 → ℝ => φ (σ 0 + σ 1)) ∘ fun s : ℝ => (![s, 0] : Fin 2 → ℝ)) = φ := by
      funext s
      simp
    rwa [e] at hc
  refine ⟨hφ, ?_⟩
  let S : (Fin 2 → ℝ) →L[ℝ] ℝ :=
    ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) 0 + ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) 1
  have hS : ∀ σ, S σ = σ 0 + σ 1 := fun σ => rfl
  have hev : ∀ᶠ y in nhds (0 : ℝ), ContDiffAt ℝ 2 φ y := hφ.eventually (by simp)
  have hevS : ∀ᶠ σ in nhds (0 : Fin 2 → ℝ), ContDiffAt ℝ 2 φ (S σ) := by
    have : Filter.Tendsto S (nhds 0) (nhds 0) := by
      have := S.continuous.tendsto 0
      simpa using this
    exact this.eventually hev
  have e1 : fderiv ℝ (fun σ : Fin 2 → ℝ => φ (σ 0 + σ 1)) =ᶠ[nhds 0] fun σ => deriv φ (S σ) • S := by
    filter_upwards [hevS] with σ hσ
    have hd : HasDerivAt φ (deriv φ (S σ)) (S σ) := (hσ.differentiableAt (by norm_num)).hasDerivAt
    have := hd.comp_hasFDerivAt σ S.hasFDerivAt
    exact this.fderiv
  have hd1 : DifferentiableAt ℝ (deriv φ) (S 0) := by
    have : S 0 = 0 := by simp [hS]
    rw [this]
    exact (contDiffAt_deriv_of_contDiffAt_two hφ).differentiableAt (by norm_num)
  have h2 : HasFDerivAt (fun σ => deriv φ (S σ)) (deriv (deriv φ) (S 0) • S) 0 :=
    hd1.hasDerivAt.comp_hasFDerivAt 0 S.hasFDerivAt
  have h3 : HasFDerivAt (fun σ => deriv φ (S σ) • S) ((ContinuousLinearMap.smulRight (deriv (deriv φ) (S 0) • S) S)) 0 := h2.smul_const S
  rw [iteratedFDeriv_two_apply, e1.fderiv_eq, h3.fderiv]
  simp [ContinuousLinearMap.smulRight_apply, hS]
end Increments
section Logarithm
theorem abs_log_sub_log_le {a b : ℝ} (ha : 1 / 2 ≤ a) (hb : 1 / 2 ≤ b) : |Real.log a - Real.log b| ≤ 2 * |a - b| := by
  have one : ∀ u v : ℝ, 1 / 2 ≤ u → 1 / 2 ≤ v → Real.log u - Real.log v ≤ 2 * |u - v| := by
    intro u v hu hv
    have hv0 : 0 < v := by linarith
    have hu0 : 0 < u := by linarith
    rw [← Real.log_div hu0.ne' hv0.ne']
    have h := Real.log_le_sub_one_of_pos (div_pos hu0 hv0)
    have e : u / v - 1 = (u - v) / v := by field_simp
    rw [e] at h
    refine h.trans ?_
    have h1 : (u - v) / v ≤ |u - v| / v := div_le_div_of_nonneg_right (le_abs_self _) hv0.le
    refine h1.trans ?_
    rw [div_le_iff₀ hv0]
    have := abs_nonneg (u - v)
    nlinarith
  rw [abs_le]
  constructor
  · have := one b a hb ha
    rw [abs_sub_comm] at this
    linarith
  · exact one a b ha hb
end Logarithm
end SecondOrderMoves
end YangMills.Construction
end
