import YangMills.Construction.Matrices.MatrixLogarithms
import Mathlib
open scoped Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction.MatrixLog.SeriesSpectral
variable {N : ℕ}
private theorem sum_smul_mul_proj {r : ℕ} {P : Fin r → SqMat N} (h : IsOrthoProjFamily P)
    (z : Fin r → ℂ) (j : Fin r) : (∑ k, z k • P k) * P j = z j • P j := by
  rw [Finset.sum_mul]
  simp only [smul_mul_assoc, h.mul_eq]
  simp
private theorem proj_mul_sum_smul {r : ℕ} {P : Fin r → SqMat N} (h : IsOrthoProjFamily P)
    (z : Fin r → ℂ) (j : Fin r) : P j * (∑ k, z k • P k) = z j • P j := by
  rw [Finset.mul_sum]
  simp only [mul_smul_comm, h.mul_eq]
  simp
private theorem proj_mul_proj_eq_zero_of_ne {r s : ℕ} {z : Fin r → ℂ} {P : Fin r → SqMat N}
    {w : Fin s → ℂ} {Q : Fin s → SqMat N} (hP : IsOrthoProjFamily P) (hQ : IsOrthoProjFamily Q)
    (h : ∑ j, z j • P j = ∑ k, w k • Q k) {j : Fin r} {k : Fin s} (hne : z j ≠ w k) :
    Q k * P j = 0 := by
  have e₁ : Q k * ((∑ j, z j • P j) * P j) = z j • (Q k * P j) := by
    rw [sum_smul_mul_proj hP, mul_smul_comm]
  have e₂ : Q k * ((∑ j, z j • P j) * P j) = w k • (Q k * P j) := by
    rw [← mul_assoc, h, proj_mul_sum_smul hQ, smul_mul_assoc]
  have e₃ : (z j - w k) • (Q k * P j) = 0 := by
    rw [sub_smul, ← e₁, ← e₂, sub_self]
  exact (smul_eq_zero.mp e₃).resolve_left (sub_ne_zero.mpr hne)
private theorem sum_proj_mul_eq {r s : ℕ} {z : Fin r → ℂ} {P : Fin r → SqMat N}
    {w : Fin s → ℂ} {Q : Fin s → SqMat N} (hP : IsOrthoProjFamily P) (hQ : IsOrthoProjFamily Q)
    (h : ∑ j, z j • P j = ∑ k, w k • Q k) (hz : ∀ j, z j ≠ 0) (j : Fin r) :
    (∑ k, Q k) * P j = P j := by
  have e₀ : (∑ k, Q k) * (∑ k, w k • Q k) = ∑ k, w k • Q k := by
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun k _ => proj_mul_sum_smul hQ w k
  have e₁ : z j • ((∑ k, Q k) * P j) = z j • P j := by
    rw [← mul_smul_comm, ← sum_smul_mul_proj hP z j, ← mul_assoc, h, e₀]
  exact smul_right_injective _ (hz j) e₁
private theorem proj_mul_sum_eq {r s : ℕ} {z : Fin r → ℂ} {P : Fin r → SqMat N}
    {w : Fin s → ℂ} {Q : Fin s → SqMat N} (hP : IsOrthoProjFamily P) (hQ : IsOrthoProjFamily Q)
    (h : ∑ j, z j • P j = ∑ k, w k • Q k) (hw : ∀ k, w k ≠ 0) (k : Fin s) :
    Q k * (∑ j, P j) = Q k := by
  have e₀ : (∑ k, z k • P k) * (∑ k, P k) = ∑ k, z k • P k := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => sum_smul_mul_proj hP z k
  have e₁ : w k • (Q k * (∑ j, P j)) = w k • Q k := by
    rw [← smul_mul_assoc, ← proj_mul_sum_smul hQ w k, ← h, mul_assoc, e₀]
  exact smul_right_injective _ (hw k) e₁
private theorem sum_comp_smul_eq {r s : ℕ} {z : Fin r → ℂ} {P : Fin r → SqMat N}
    {w : Fin s → ℂ} {Q : Fin s → SqMat N} (hP : IsOrthoProjFamily P) (hQ : IsOrthoProjFamily Q)
    (h : ∑ j, z j • P j = ∑ k, w k • Q k) (hz : ∀ j, z j ≠ 0) (hw : ∀ k, w k ≠ 0) (f : ℂ → ℂ) :
    ∑ j, f (z j) • P j = ∑ k, f (w k) • Q k := by
  have e₁ : ∑ j, f (z j) • P j = ∑ j, ∑ k, f (z j) • (Q k * P j) := by
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← Finset.smul_sum, ← Finset.sum_mul, sum_proj_mul_eq hP hQ h hz]
  have e₂ : ∑ k, f (w k) • Q k = ∑ k, ∑ j, f (w k) • (Q k * P j) := by
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← Finset.smul_sum, ← Finset.mul_sum, proj_mul_sum_eq hP hQ h hw]
  rw [e₁, e₂, Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => ?_
  by_cases hc : z j = w k
  · rw [hc]
  · rw [proj_mul_proj_eq_zero_of_ne hP hQ h hc, smul_zero, smul_zero]
private theorem exists_eq_term {r s : ℕ} {z : Fin r → ℂ} {P : Fin r → SqMat N}
    {w : Fin s → ℂ} {Q : Fin s → SqMat N} (hP : IsOrthoProjFamily P) (hQ : IsOrthoProjFamily Q)
    (h : ∑ j, z j • P j = ∑ k, w k • Q k) (hz : ∀ j, z j ≠ 0) (hw : ∀ k, w k ≠ 0)
    (iz : Function.Injective z) (iw : Function.Injective w) (j : Fin r) (hne : P j ≠ 0) :
    ∃ k, w k = z j ∧ Q k = P j := by
  have hsum := sum_proj_mul_eq hP hQ h hz j
  rw [Finset.sum_mul] at hsum
  have hex : ∃ k, w k = z j := by
    by_contra hno
    push Not at hno
    apply hne
    rw [← hsum]
    exact Finset.sum_eq_zero fun k _ => proj_mul_proj_eq_zero_of_ne hP hQ h (hno k).symm
  obtain ⟨k, hk⟩ := hex
  refine ⟨k, hk, ?_⟩
  have e₁ : Q k * P j = P j := by
    have hs : ∑ k', Q k' * P j = Q k * P j := Finset.sum_eq_single k
      (fun k' _ hk' => proj_mul_proj_eq_zero_of_ne hP hQ h fun hc => hk' (iw (hc.symm.trans hk.symm)))
      (fun hn => absurd (Finset.mem_univ k) hn)
    exact hs.symm.trans hsum
  have hsum' := sum_proj_mul_eq hQ hP h.symm hw k
  rw [Finset.sum_mul] at hsum'
  have e₂ : P j * Q k = Q k := by
    have hs : ∑ j', P j' * Q k = P j * Q k := Finset.sum_eq_single j
      (fun j' _ hj' => proj_mul_proj_eq_zero_of_ne hQ hP h.symm fun hc => hj' (iz (hc.symm.trans hk)))
      (fun hn => absurd (Finset.mem_univ j) hn)
    exact hs.symm.trans hsum'
  have e₃ : P j * Q k = P j := by
    have := congrArg Matrix.conjTranspose e₁
    rwa [Matrix.conjTranspose_mul, hP.star_eq, hQ.star_eq] at this
  exact e₂.symm.trans e₃
private theorem exists_spectral_decomposition (X : SqMat N) (hX : IsStarNormal X) :
    ∃ (r : ℕ) (z : Fin r → ℂ) (P : Fin r → SqMat N), IsOrthoProjFamily P ∧ Function.Injective z ∧
      (∀ j, z j ∈ spectrum ℂ X) ∧ (∀ j, P j ≠ 0) ∧ ∀ f : ℂ → ℂ, cfc f X = ∑ j, f (z j) • P j := by
  classical
  have hfin : (spectrum ℂ X).Finite := Matrix.finite_spectrum X
  have hcont : ∀ f : ℂ → ℂ, ContinuousOn f (spectrum ℂ X) := fun f => hfin.continuousOn f
  let s : Finset ℂ := hfin.toFinset
  let e := s.equivFin
  let ind : ℂ → ℂ → ℂ := fun w u => if u = w then 1 else 0
  have hmem : ∀ j, ((e.symm j : s) : ℂ) ∈ spectrum ℂ X := fun j => hfin.mem_toFinset.mp (e.symm j).2
  refine ⟨s.card, fun j => (e.symm j : ℂ), fun j => cfc (ind (e.symm j : ℂ)) X, ⟨?_, ?_⟩, ?_, hmem, ?_, ?_⟩
  · intro j
    rw [← Matrix.star_eq_conjTranspose, ← cfc_star]
    refine cfc_congr fun u _ => ?_
    simp only [ind]
    split_ifs <;> simp
  · intro j k
    rw [← cfc_mul _ _ _ (hcont _) (hcont _)]
    split_ifs with hjk
    · subst hjk
      refine cfc_congr fun u _ => ?_
      simp only [ind]
      split_ifs <;> simp
    · rw [← cfc_zero ℂ X]
      refine cfc_congr fun u _ => ?_
      have hne : ((e.symm j : s) : ℂ) ≠ (e.symm k : ℂ) := fun hc =>
        hjk (e.symm.injective (Subtype.ext hc))
      simp only [ind, Pi.zero_apply]
      split_ifs with h₁ h₂ <;> simp_all
  · intro j k hc
    exact e.symm.injective (Subtype.ext hc)
  · intro j hc
    rw [← cfc_zero ℂ X, cfc_eq_cfc_iff_eqOn (hf := hcont _) (hg := hcont _)] at hc
    have := hc (hmem j)
    simp [ind] at this
  · intro f
    have e₀ : ∑ j : Fin s.card, f (e.symm j : ℂ) • cfc (ind (e.symm j : ℂ)) X
        = cfc (fun u => ∑ j : Fin s.card, f (e.symm j : ℂ) • ind (e.symm j : ℂ) u) X := by
      have h₁ := cfc_sum_univ (fun (j : Fin s.card) (u : ℂ) => f (e.symm j : ℂ) • ind (e.symm j : ℂ) u)
        X (fun j => hcont _)
      have h₂ : (∑ j : Fin s.card, fun u : ℂ => f (e.symm j : ℂ) • ind (e.symm j : ℂ) u)
          = fun u => ∑ j : Fin s.card, f (e.symm j : ℂ) • ind (e.symm j : ℂ) u := by
        ext u
        simp
      rw [← h₂, h₁]
      exact Finset.sum_congr rfl fun j _ => (cfc_smul _ _ _ (hcont _)).symm
    rw [e₀]
    refine cfc_congr fun u hu => ?_
    have hus : u ∈ s := by simpa [s] using hu
    have hj : ∑ j : Fin s.card, f (e.symm j : ℂ) • ind (e.symm j : ℂ) u
        = f (e.symm (e ⟨u, hus⟩) : ℂ) • ind (e.symm (e ⟨u, hus⟩) : ℂ) u := by
      refine Finset.sum_eq_single _ (fun j _ hj => ?_) (fun hn => absurd (Finset.mem_univ _) hn)
      have : u ≠ (e.symm j : ℂ) := fun hc => hj (by
        have : e.symm j = ⟨u, hus⟩ := Subtype.ext hc.symm
        simp [← this])
      simp [ind, this]
    rw [hj]
    simp [ind]
section LogSeries
private def logCoeff (n : ℕ) : ℂ := (-1 : ℂ) ^ (n + 2) / ((n : ℂ) + 1)
private theorem norm_logCoeff_le (n : ℕ) : ‖logCoeff n‖ ≤ 1 := by
  have h : ((n : ℂ) + 1) = ((n + 1 : ℕ) : ℂ) := by push_cast; ring
  rw [logCoeff, norm_div, norm_pow, norm_neg, norm_one, one_pow, h, Complex.norm_natCast]
  rw [div_le_one (by positivity)]
  push_cast
  linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
private theorem logCoeff_mul (n : ℕ) : logCoeff n * ((n : ℂ) + 1) = (-1 : ℂ) ^ n := by
  have h : ((n : ℂ) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
  rw [logCoeff, div_mul_cancel₀ _ h]
  ring
variable {A : Type*} [NormedRing A] [NormedAlgebra ℂ A]
private def logSeries (a : A) : A := ∑' n : ℕ, logCoeff n • a ^ (n + 1)
private theorem norm_logTerm_le (a : A) (n : ℕ) : ‖logCoeff n • a ^ (n + 1)‖ ≤ ‖a‖ ^ (n + 1) := by
  calc ‖logCoeff n • a ^ (n + 1)‖ ≤ ‖logCoeff n‖ * ‖a ^ (n + 1)‖ := norm_smul_le _ _
    _ ≤ 1 * ‖a‖ ^ (n + 1) := by
      gcongr
      · exact norm_logCoeff_le n
      · exact norm_pow_le' a n.succ_pos
    _ = ‖a‖ ^ (n + 1) := one_mul _
private theorem summable_logTerm [CompleteSpace A] {a : A} (h : ‖a‖ < 1) :
    Summable fun n : ℕ => logCoeff n • a ^ (n + 1) := by
  refine Summable.of_norm_bounded (g := fun n : ℕ => ‖a‖ ^ (n + 1)) ?_ (norm_logTerm_le a)
  exact (summable_nat_add_iff 1).mpr (summable_geometric_of_lt_one (norm_nonneg a) h)
private theorem logSeries_zero : logSeries (0 : A) = 0 := by
  simp [logSeries]
private theorem const_of_hasDerivAt_zero_on_ball {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {ρ : ℝ} {φ : ℂ → E} (h : ∀ t ∈ Metric.ball (0 : ℂ) ρ, HasDerivAt φ 0 t) {x y : ℂ}
    (hx : x ∈ Metric.ball (0 : ℂ) ρ) (hy : y ∈ Metric.ball (0 : ℂ) ρ) : φ x = φ y := by
  refine Convex.is_const_of_fderivWithin_eq_zero (𝕜 := ℂ) (convex_ball (0 : ℂ) ρ)
    (fun t ht => (h t ht).differentiableAt.differentiableWithinAt) (fun t ht => ?_) hx hy
  rw [fderivWithin_of_isOpen Metric.isOpen_ball ht, (h t ht).hasFDerivAt.fderiv]
  ext
  simp
private theorem exists_one_lt_mul_lt {c d : ℝ} (hc : 0 ≤ c) (h : c < d) :
    ∃ ρ : ℝ, 1 < ρ ∧ ρ * c < d := by
  have hd : 0 < d := lt_of_le_of_lt hc h
  have hcd : 0 < c + d := by linarith
  refine ⟨2 * d / (c + d), ?_, ?_⟩
  · rw [lt_div_iff₀ hcd]
    linarith
  · rw [div_mul_eq_mul_div, div_lt_iff₀ hcd]
    nlinarith [mul_pos hd (sub_pos.mpr h)]
private theorem mem_expSeries_eball (x : A) :
    x ∈ Metric.eball (0 : A) (NormedSpace.expSeries ℂ A).radius :=
  (NormedSpace.expSeries_radius_eq_top ℂ A).symm ▸ edist_lt_top _ _
private theorem norm_exp_sub_one_le_real [CompleteSpace A] (y : A) :
    ‖NormedSpace.exp y - 1‖ ≤ Real.exp ‖y‖ - 1 := by
  have h₁ : HasSum (fun n : ℕ => ((n + 1).factorial⁻¹ : ℂ) • y ^ (n + 1))
      (NormedSpace.exp y - 1) := by
    have := (hasSum_nat_add_iff' (f := fun n : ℕ => ((n.factorial : ℂ)⁻¹) • y ^ n) 1).mpr
      (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) y)
    simpa using this
  have h₂ : HasSum (fun n : ℕ => ((n + 1).factorial : ℝ)⁻¹ * ‖y‖ ^ (n + 1))
      (Real.exp ‖y‖ - 1) := by
    have h₀ := NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) ‖y‖
    rw [← Real.exp_eq_exp_ℝ] at h₀
    have := (hasSum_nat_add_iff' (f := fun n : ℕ => ((n.factorial : ℝ)⁻¹) • ‖y‖ ^ n) 1).mpr h₀
    simpa using this
  refine h₁.norm_le_of_bounded h₂ fun n => ?_
  calc ‖((n + 1).factorial⁻¹ : ℂ) • y ^ (n + 1)‖
      ≤ ‖((n + 1).factorial⁻¹ : ℂ)‖ * ‖y ^ (n + 1)‖ := norm_smul_le _ _
    _ ≤ ((n + 1).factorial : ℝ)⁻¹ * ‖y‖ ^ (n + 1) := by
      have : ‖((n + 1).factorial⁻¹ : ℂ)‖ = ((n + 1).factorial : ℝ)⁻¹ := by
        rw [norm_inv, Complex.norm_natCast]
      rw [this]
      gcongr
      exact norm_pow_le' y n.succ_pos
end LogSeries
section CommutativeCase
variable {B : Type*} [NormedCommRing B] [NormedAlgebra ℂ B] [CompleteSpace B]
private theorem hasFDerivAt_logSeries {a : B} (ha : ‖a‖ < 1) :
    HasFDerivAt (logSeries (A := B)) (ContinuousLinearMap.mul ℂ B (∑' n : ℕ, (-a) ^ n)) a := by
  obtain ⟨ρ, hρa, hρ1⟩ := exists_between ha
  have hρ0 : 0 ≤ ρ := (norm_nonneg a).trans hρa.le
  have hder : ∀ (n : ℕ) (x : B), x ∈ Metric.ball (0 : B) ρ →
      HasFDerivAt (fun y : B => logCoeff n • y ^ (n + 1))
        (ContinuousLinearMap.mul ℂ B ((-x) ^ n)) x := by
    intro n x _
    have h := (hasFDerivAt_pow (𝕜 := ℂ) (x := x) (n + 1)).const_smul (logCoeff n)
    have e : (logCoeff n • ((n + 1) • x ^ (n + 1 - 1)) • ContinuousLinearMap.id ℂ B)
        = ContinuousLinearMap.mul ℂ B ((-x) ^ n) := by
      refine ContinuousLinearMap.ext fun v => ?_
      have hc : ((logCoeff n * ((n : ℂ) + 1)) • (x ^ n * v) : B) = (-x) ^ n * v := by
        rw [logCoeff_mul, show -x = (-1 : ℂ) • x from (neg_one_smul ℂ x).symm, smul_pow,
          smul_mul_assoc]
      show logCoeff n • (((n + 1) • x ^ (n + 1 - 1)) • v) = (-x) ^ n * v
      rw [Nat.add_sub_cancel, smul_eq_mul, ← Nat.cast_smul_eq_nsmul ℂ, smul_mul_assoc, smul_smul]
      push_cast
      exact hc
    rw [e] at h
    exact h
  have hbound : ∀ (n : ℕ) (x : B), x ∈ Metric.ball (0 : B) ρ →
      ‖ContinuousLinearMap.mul ℂ B ((-x) ^ n)‖ ≤ (‖(1 : B)‖ + 1) * ρ ^ n := by
    intro n x hx
    have hx' : ‖x‖ ≤ ρ := by
      have := Metric.mem_ball.mp hx
      rw [dist_zero_right] at this
      exact this.le
    refine (ContinuousLinearMap.opNorm_mul_apply_le ℂ B _).trans ?_
    rcases n with _ | n
    · simp
    · calc ‖(-x) ^ (n + 1)‖ ≤ ‖-x‖ ^ (n + 1) := norm_pow_le' _ n.succ_pos
        _ ≤ ρ ^ (n + 1) := by
          rw [norm_neg]
          gcongr
        _ ≤ (‖(1 : B)‖ + 1) * ρ ^ (n + 1) := by
          have : 0 ≤ ρ ^ (n + 1) := by positivity
          nlinarith [norm_nonneg (1 : B)]
  have hu : Summable fun n : ℕ => (‖(1 : B)‖ + 1) * ρ ^ n :=
    (summable_geometric_of_lt_one hρ0 hρ1).mul_left _
  have hmem : a ∈ Metric.ball (0 : B) ρ := by simpa using hρa
  have h := hasFDerivAt_tsum_of_isPreconnected hu Metric.isOpen_ball
    (convex_ball (0 : B) ρ).isPreconnected hder hbound hmem (summable_logTerm ha) hmem
  have hs : Summable fun n : ℕ => (-a) ^ n :=
    summable_geometric_of_norm_lt_one (by simpa using ha)
  rw [ContinuousLinearMap.map_tsum _ hs]
  exact h
private theorem tsum_neg_pow_mul_one_add {a : B} (ha : ‖a‖ < 1) :
    (∑' n : ℕ, (-a) ^ n) * (1 + a) = 1 := by
  have := geom_series_mul_neg (-a) (by simpa using ha)
  rwa [sub_neg_eq_add] at this
private theorem exp_logSeries_of_comm {a : B} (ha : ‖a‖ < 1) : NormedSpace.exp (logSeries a) = 1 + a := by
  obtain ⟨ρ, hρ1, hρa⟩ := exists_one_lt_mul_lt (norm_nonneg a) ha
  have hnorm : ∀ t ∈ Metric.ball (0 : ℂ) ρ, ‖t • a‖ < 1 := by
    intro t ht
    have ht' : ‖t‖ < ρ := by simpa using ht
    rw [norm_smul]
    exact lt_of_le_of_lt (by gcongr) hρa
  have hconst := const_of_hasDerivAt_zero_on_ball (ρ := ρ)
    (φ := fun t : ℂ => NormedSpace.exp (-logSeries (t • a)) * (1 + t • a)) (fun t ht => by
      have h₁ : HasDerivAt (fun t : ℂ => t • a) a t := by
        simpa using (hasDerivAt_id t).smul_const a
      have h₂ := (hasFDerivAt_logSeries (hnorm t ht)).comp_hasDerivAt t h₁
      have h₃ := (hasFDerivAt_exp (𝕂 := ℂ) (x := -logSeries (t • a))).comp_hasDerivAt t h₂.neg
      have h₄ := h₃.mul (h₁.const_add 1)
      refine h₄.congr_deriv ?_
      have hg := tsum_neg_pow_mul_one_add (hnorm t ht)
      show (NormedSpace.exp (-logSeries (t • a)) * -((∑' n : ℕ, (-(t • a)) ^ n) * a)) * (1 + t • a)
        + NormedSpace.exp (-logSeries (t • a)) * a = 0
      linear_combination (-NormedSpace.exp (-logSeries (t • a)) * a) * hg)
    (x := 1) (y := 0) (by simpa using by linarith) (by simpa using by linarith)
  simp only [one_smul, zero_smul, logSeries_zero, neg_zero, NormedSpace.exp_zero, add_zero, mul_one]
    at hconst
  have hinv : NormedSpace.exp (logSeries a) * NormedSpace.exp (-logSeries a) = 1 := by
    rw [← NormedSpace.exp_add_of_commute_of_mem_ball (𝕂 := ℂ) (Commute.all _ _) (mem_expSeries_eball _)
      (mem_expSeries_eball _), add_neg_cancel, NormedSpace.exp_zero]
  calc NormedSpace.exp (logSeries a)
        = NormedSpace.exp (logSeries a) * (NormedSpace.exp (-logSeries a) * (1 + a)) := by
        rw [hconst, mul_one]
    _ = 1 + a := by rw [← mul_assoc, hinv, one_mul]
private theorem logSeries_exp_sub_one_of_comm {y : B} (hy : ‖y‖ < Real.log 2) :
    logSeries (NormedSpace.exp y - 1) = y := by
  obtain ⟨ρ, hρ1, hρy⟩ := exists_one_lt_mul_lt (norm_nonneg y) hy
  have hnorm : ∀ t ∈ Metric.ball (0 : ℂ) ρ, ‖NormedSpace.exp (t • y) - 1‖ < 1 := by
    intro t ht
    have ht' : ‖t‖ < ρ := by simpa using ht
    have h₁ : ‖t • y‖ < Real.log 2 := by
      rw [norm_smul]
      exact lt_of_le_of_lt (by gcongr) hρy
    have h₂ : Real.exp ‖t • y‖ < 2 := by
      rw [← Real.exp_log (by norm_num : (0 : ℝ) < 2)]
      exact Real.exp_lt_exp.mpr h₁
    linarith [norm_exp_sub_one_le_real (t • y)]
  have hconst := const_of_hasDerivAt_zero_on_ball (ρ := ρ)
    (φ := fun t : ℂ => logSeries (NormedSpace.exp (t • y) - 1) - t • y) (fun t ht => by
      have h₀ : HasDerivAt (fun t : ℂ => t • y) y t := by
        simpa using (hasDerivAt_id t).smul_const y
      have h₁ := (hasDerivAt_exp_smul_const (𝕂 := ℂ) y t).sub_const 1
      have h₂ := ((hasFDerivAt_logSeries (hnorm t ht)).comp_hasDerivAt t h₁).sub h₀
      refine h₂.congr_deriv ?_
      have hg := tsum_neg_pow_mul_one_add (hnorm t ht)
      show (∑' n : ℕ, (-(NormedSpace.exp (t • y) - 1)) ^ n) * (NormedSpace.exp (t • y) * y) - y = 0
      rw [add_sub_cancel] at hg
      linear_combination y * hg)
    (x := 1) (y := 0) (by simpa using by linarith) (by simpa using by linarith)
  simpa [logSeries_zero, sub_eq_zero] using hconst
end CommutativeCase
section Elemental
variable {A : Type*} [NormedRing A] [NormedAlgebra ℂ A] [CompleteSpace A]
private abbrev ElementalAlg (x : A) : Type _ := Algebra.elemental ℂ x
private instance (x : A) : NormedCommRing (ElementalAlg x) :=
  { (inferInstance : NormedRing (Algebra.elemental ℂ x)) with mul_comm := mul_comm }
private theorem coe_logSeries {x : A} {b : ElementalAlg x} (h : ‖b‖ < 1) :
    ((logSeries b : ElementalAlg x) : A) = logSeries (b : A) := by
  have := (summable_logTerm h).map_tsum (Algebra.elemental ℂ x).val continuous_subtype_val
  simpa [logSeries] using this
private theorem exp_logSeries {a : A} (ha : ‖a‖ < 1) : NormedSpace.exp (logSeries a) = 1 + a := by
  let b : ElementalAlg a := ⟨a, Algebra.elemental.self_mem ℂ a⟩
  have hb : ‖b‖ < 1 := ha
  have e := congrArg (Algebra.elemental ℂ a).val (exp_logSeries_of_comm hb)
  rw [NormedSpace.map_exp_of_mem_ball (𝕂 := ℂ) _ continuous_subtype_val _ (mem_expSeries_eball _)] at e
  simpa [coe_logSeries hb] using e
private theorem logSeries_exp_sub_one {y : A} (hy : ‖y‖ < Real.log 2) :
    logSeries (NormedSpace.exp y - 1) = y := by
  let b : ElementalAlg y := ⟨y, Algebra.elemental.self_mem ℂ y⟩
  have hb : ‖b‖ < Real.log 2 := hy
  have h₁ : ‖NormedSpace.exp b - 1‖ < 1 := by
    have h₂ : Real.exp ‖b‖ < 2 := by
      rw [← Real.exp_log (by norm_num : (0 : ℝ) < 2)]
      exact Real.exp_lt_exp.mpr hb
    linarith [norm_exp_sub_one_le_real b]
  have e := congrArg (Subtype.val) (logSeries_exp_sub_one_of_comm hb)
  have e₂ : ((NormedSpace.exp b - 1 : ElementalAlg y) : A) = NormedSpace.exp y - 1 := by
    have := NormedSpace.map_exp_of_mem_ball (𝕂 := ℂ) (Algebra.elemental ℂ y).val
      continuous_subtype_val b (mem_expSeries_eball _)
    simpa using congrArg (· - (1 : A)) this
  rw [coe_logSeries h₁, e₂] at e
  exact e
end Elemental
section Assembly
variable {N : ℕ}
private theorem logOfSeries_eq (X : SqMat N) : logOfSeries X = logSeries (X - 1) := rfl
private def logCoeffFromZero : ℕ → ℂ
  | 0 => 0
  | n + 1 => logCoeff n
private theorem hasFPowerSeriesOnBall_logOfSeries :
    HasFPowerSeriesOnBall (logOfSeries : SqMat N → SqMat N)
      (FormalMultilinearSeries.ofScalars (SqMat N) logCoeffFromZero) 1 1 := by
  refine ⟨?_, one_pos, fun {y} hy => ?_⟩
  · refine ENNReal.le_of_forall_nnreal_lt fun r hr => ?_
    have hr1 : (r : ℝ) ≤ 1 := by
      have : (r : ENNReal) ≤ 1 := hr.le
      exact_mod_cast this
    refine FormalMultilinearSeries.le_radius_of_bound _ 1 fun n => ?_
    rcases n with _ | n
    · have : FormalMultilinearSeries.ofScalars (SqMat N) logCoeffFromZero 0 = 0 :=
        FormalMultilinearSeries.ofScalars_eq_zero_of_scalar_zero _ rfl
      simp [this]
    · have h₁ : ‖FormalMultilinearSeries.ofScalars (SqMat N) logCoeffFromZero (n + 1)‖ ≤ 1 :=
        (FormalMultilinearSeries.ofScalars_norm_le _ _ _ (Nat.succ_pos n)).trans (norm_logCoeff_le n)
      have h₂ : (r : ℝ) ^ (n + 1) ≤ 1 := pow_le_one₀ r.coe_nonneg hr1
      calc _ ≤ (1 : ℝ) * 1 := by gcongr
        _ = 1 := one_mul 1
  · have hy' : ‖y‖ < 1 := by
      rw [← ENNReal.ofReal_one, Metric.eball_ofReal] at hy
      simpa using hy
    rw [logOfSeries_eq, add_sub_cancel_left]
    refine (hasSum_nat_add_iff' 1).mp ?_
    have h : HasSum (fun n : ℕ => logCoeff n • y ^ (n + 1)) (logSeries y) := (summable_logTerm hy').hasSum
    have e₀ : ∑ i ∈ Finset.range 1,
        FormalMultilinearSeries.ofScalars (SqMat N) logCoeffFromZero i (fun _ => y) = 0 := by
      simp [FormalMultilinearSeries.ofScalars_apply_eq, logCoeffFromZero]
    have e₁ : (fun n : ℕ =>
        FormalMultilinearSeries.ofScalars (SqMat N) logCoeffFromZero (n + 1) (fun _ => y))
        = fun n : ℕ => logCoeff n • y ^ (n + 1) :=
      funext fun n => FormalMultilinearSeries.ofScalars_apply_eq _ _ _
    rw [e₀, sub_zero, e₁]
    exact h
private theorem isStarNormal_of_mem_unitaryGroup {U : SqMat N}
    (hU : U ∈ Matrix.unitaryGroup (Fin N) ℂ) : IsStarNormal U :=
  ⟨(Matrix.mem_unitaryGroup_iff'.mp hU).trans (Matrix.mem_unitaryGroup_iff.mp hU).symm⟩
private theorem norm_eq_one_of_mem_spectrum {U : SqMat N} (hU : U ∈ Matrix.unitaryGroup (Fin N) ℂ)
    {x : ℂ} (hx : x ∈ spectrum ℂ U) : ‖x‖ = 1 := by
  simpa using spectrum.subset_circle_of_unitary (𝕜 := ℂ) hU hx
private theorem log_exp_I_mul {t : ℝ} (ht : t ∈ Set.Ioc (-Real.pi) Real.pi) :
    Complex.log (Complex.exp (Complex.I * (t : ℂ))) = Complex.I * (t : ℂ) :=
  Complex.log_exp (by simpa using ht.1) (by simpa using ht.2)
private theorem eq_of_exp_I_mul_eq {s t : ℝ} (hs : s ∈ Set.Ioc (-Real.pi) Real.pi)
    (ht : t ∈ Set.Ioc (-Real.pi) Real.pi)
    (h : Complex.exp (Complex.I * (s : ℂ)) = Complex.exp (Complex.I * (t : ℂ))) : s = t := by
  have e := congrArg Complex.log h
  rw [log_exp_I_mul hs, log_exp_I_mul ht] at e
  exact_mod_cast mul_left_cancel₀ Complex.I_ne_zero e
private theorem spectralLog_eq_sum {D : Set ℂ} {ℓ : ℂ → ℂ} (hℓ : IsLogBranch D ℓ) {X : SqMat N}
    {r : ℕ} {z : Fin r → ℂ} {P : Fin r → SqMat N} (hP : IsOrthoProjFamily P)
    (hX : X = ∑ j, z j • P j) (hz : ∀ j, z j ∈ D) : spectralLog D ℓ X = ∑ j, ℓ (z j) • P j := by
  have hex : ∃ L, IsSpectralLog D ℓ X L := ⟨_, r, z, P, hP, hX, hz, rfl⟩
  obtain ⟨s, w, Q, hQ, hX', hw, hL⟩ := Classical.epsilon_spec hex
  have e : spectralLog D ℓ X = ∑ k, ℓ (w k) • Q k := hL
  rw [e]
  exact (sum_comp_smul_eq hP hQ (hX.symm.trans hX')
    (fun j hj => Complex.exp_ne_zero (ℓ (z j)) ((hℓ _ (hz j)).trans hj))
    (fun k hk => Complex.exp_ne_zero (ℓ (w k)) ((hℓ _ (hw k)).trans hk)) ℓ).symm
private theorem unitaryFormUniqueNonzero_holds (N : ℕ) : UnitaryFormUniqueNonzero N := by
  intro U _ r r' l l' P P' h h' hne hne'
  have hsum : ∑ j, Complex.exp (Complex.I * (l j : ℂ)) • P j
      = ∑ k, Complex.exp (Complex.I * (l' k : ℂ)) • P' k := h.eq_sum.symm.trans h'.eq_sum
  have iz : Function.Injective fun j => Complex.exp (Complex.I * (l j : ℂ)) := fun j k e =>
    h.injective (eq_of_exp_I_mul_eq (h.mem_Ioc j) (h.mem_Ioc k) e)
  have iw : Function.Injective fun k => Complex.exp (Complex.I * (l' k : ℂ)) := fun j k e =>
    h'.injective (eq_of_exp_I_mul_eq (h'.mem_Ioc j) (h'.mem_Ioc k) e)
  choose f hf₁ hf₂ using fun j => exists_eq_term h.proj h'.proj hsum
    (fun _ => Complex.exp_ne_zero _) (fun _ => Complex.exp_ne_zero _) iz iw j (hne j)
  choose g hg₁ hg₂ using fun k => exists_eq_term h'.proj h.proj hsum.symm
    (fun _ => Complex.exp_ne_zero _) (fun _ => Complex.exp_ne_zero _) iw iz k (hne' k)
  refine ⟨⟨f, g, fun j => iz ((hg₁ (f j)).trans (hf₁ j)), fun k => iw ((hf₁ (g k)).trans (hg₁ k))⟩,
    fun j => ⟨eq_of_exp_I_mul_eq (h'.mem_Ioc _) (h.mem_Ioc _) (hf₁ j), hf₂ j⟩⟩
private theorem exists_unitarySpectralForm {U : SqMat N} (hU : U ∈ Matrix.unitaryGroup (Fin N) ℂ) :
    ∃ (r : ℕ) (l : Fin r → ℝ) (P : Fin r → SqMat N), IsUnitarySpectralForm U l P ∧ ∀ j, P j ≠ 0 := by
  obtain ⟨r, z, P, hP, iz, hz, hne, hf⟩ :=
    exists_spectral_decomposition U (isStarNormal_of_mem_unitaryGroup hU)
  have hexp : ∀ j, Complex.exp (Complex.I * ((z j).arg : ℂ)) = z j := fun j => by
    have := Complex.norm_mul_exp_arg_mul_I (z j)
    rw [norm_eq_one_of_mem_spectrum hU (hz j)] at this
    simpa [mul_comm] using this
  refine ⟨r, fun j => (z j).arg, P, ⟨hP, fun j k e => iz ?_, fun j => Complex.arg_mem_Ioc _, ?_⟩, hne⟩
  · rw [← hexp j, ← hexp k]
    exact congrArg (fun t : ℝ => Complex.exp (Complex.I * (t : ℂ))) e
  · have h := hf id
    rw [cfc_id ℂ U (isStarNormal_of_mem_unitaryGroup hU)] at h
    simpa only [hexp, id] using h
theorem matrixLogarithmsSeriesAndSpectral_proof : MatrixLogarithmsSeriesAndSpectral := by
  intro N
  refine ⟨fun X hX => ⟨summable_logTerm hX, ?_⟩, fun Y hY => ⟨?_, logSeries_exp_sub_one hY⟩,
    fun X _ => NormedSpace.analyticAt_exp_of_mem_ball (𝕂 := ℂ) X (mem_expSeries_eball X), ?_, ?_,
    ?_, fun U hU => exists_unitarySpectralForm hU, unitaryFormUniqueNonzero_holds N, ?_⟩
  · rw [logOfSeries_eq, exp_logSeries hX, add_sub_cancel]
  · have h₂ : Real.exp ‖Y‖ < 2 := by
      rw [← Real.exp_log (by norm_num : (0 : ℝ) < 2)]
      exact Real.exp_lt_exp.mpr hY
    linarith [norm_exp_sub_one_le_real Y]
  · intro X hX
    refine hasFPowerSeriesOnBall_logOfSeries.analyticOnNhd X ?_
    rw [← ENNReal.ofReal_one, Metric.eball_ofReal]
    simpa [dist_eq_norm] using hX
  · intro X hX
    obtain ⟨r, z, P, hP, _, _, _, hf⟩ := exists_spectral_decomposition X hX
    refine ⟨r, z, P, hP, ?_⟩
    have h := hf id
    rw [cfc_id ℂ X hX] at h
    simpa only [id] using h
  · intro D ℓ hℓ X _ r z P hP hX hz
    exact spectralLog_eq_sum hℓ hP hX hz
  · intro U hU r l P h
    have hnormal := isStarNormal_of_mem_unitaryGroup hU
    have hlog : principalSpectralLog U
        = ∑ j, Complex.log (Complex.exp (Complex.I * (l j : ℂ))) • P j :=
      spectralLog_eq_sum (fun z hz => Complex.exp_log hz) h.proj h.eq_sum
        (fun j => Complex.exp_ne_zero _)
    have hI : ∑ j, Complex.log (Complex.exp (Complex.I * (l j : ℂ))) • P j
        = Complex.I • phaseMatrix l P := by
      rw [phaseMatrix, Finset.smul_sum]
      exact Finset.sum_congr rfl fun j _ => by rw [log_exp_I_mul (h.mem_Ioc j), mul_smul]
    refine ⟨hlog.trans hI, ?_, ?_⟩
    · rw [Matrix.IsHermitian, phaseMatrix, Matrix.conjTranspose_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Matrix.conjTranspose_smul, h.proj.star_eq j]
      simp
    · obtain ⟨s, w, Q, hQ, _, hw, _, hf⟩ := exists_spectral_decomposition U hnormal
      have hU' : ∑ j, Complex.exp (Complex.I * (l j : ℂ)) • P j = ∑ k, w k • Q k := by
        have h₁ := hf id
        rw [cfc_id ℂ U hnormal] at h₁
        exact h.eq_sum.symm.trans (by simpa only [id] using h₁)
      have hw0 : ∀ k, w k ≠ 0 := fun k hk => by
        have := norm_eq_one_of_mem_spectrum hU (hw k)
        simp [hk] at this
      have e : Complex.I • phaseMatrix l P = cfc Complex.log U := by
        rw [← hI, sum_comp_smul_eq h.proj hQ hU' (fun _ => Complex.exp_ne_zero _) hw0 Complex.log,
          hf Complex.log]
      have hb : ‖cfc Complex.log U‖ ≤ Real.pi := by
        refine norm_cfc_le Real.pi_pos.le fun x hx => ?_
        have hx1 := norm_eq_one_of_mem_spectrum hU hx
        have : Complex.log x = (x.arg : ℂ) * Complex.I := by
          rw [Complex.log, hx1, Real.log_one]
          simp
        rw [this, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
        exact Complex.abs_arg_le_pi x
      rw [← e, norm_smul, Complex.norm_I, one_mul] at hb
      exact hb
end Assembly
end YangMills.Construction.MatrixLog.SeriesSpectral
