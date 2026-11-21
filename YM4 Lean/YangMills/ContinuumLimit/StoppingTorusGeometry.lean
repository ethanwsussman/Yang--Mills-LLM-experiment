import YangMills.ContinuumLimit.StoppedTorusTail
noncomputable section
open Filter
open YangMills.Construction TorusLumps
namespace YangMills.ReferenceCalibration

/-- All size requirements for reading the fixed pair at its stopping scale.
Here `q` is the number of blocked lattice steps in one physical unit and is
also the radius used for the local axial gauge. -/
theorem stopping_torus_geometry (p : StepParameters) {A ell v : ℝ}
    (hA : 1 ≤ A) (hell : 8 ≤ ell) (hv : 0 < v) (hσ : 0 < p.threshold) :
    ∀ᶠ q : ℕ in atTop, ∀ (n : ℕ) (x : ℝ),
      (n:ℝ) = ell*q → 2*p.side ∣ n → (q:ℝ)^92 ≤ x → x ≤ A*(q:ℝ)^92 →
      let d := (6/5:ℝ)*q
      let t := ((q:ℝ)^16)⁻¹
      IsBlockTorusSide p n ∧ p.n₀ ≤ n ∧
      1 ≤ (clusterRange x:ℝ) ∧ (clusterRange x:ℝ)/64 ≤ q ∧
      1 ≤ q ∧ 4*q+4 ≤ n ∧ 0 ≤ t ∧ t ≤ 1 ∧ t < p.threshold ∧
      6*((q:ℝ)+1)*t ≤ 1 ∧ 1 ≤ d ∧
      2^12*(p.side:ℝ)*(clusterRange x:ℝ) ≤ d ∧ 2 ≤ v*d := by
  have hscale := eventually_range_fits_reference_torus A (2^12*(p.side:ℝ)+1) hA (by positivity)
  have hinv : Tendsto (fun q : ℝ => (q^16)⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp (tendsto_pow_atTop (n:=16) (by decide))
  have hreal : Tendsto (fun q : ℕ => (q:ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hvq := (tendsto_id.const_mul_atTop hv).eventually_ge_atTop 2
  filter_upwards [hreal.eventually hscale, hreal.eventually (hinv.eventually (gt_mem_nhds hσ)),
    hreal.eventually hvq, eventually_ge_atTop (12:ℕ), eventually_ge_atTop (p.side*p.n₀),
    eventually_ge_atTop p.n₀] with q hr ht hvq h12 hmin hnmin
  intro n x hn hdiv hlo hhi d t
  have hq : (12:ℝ) ≤ q := by exact_mod_cast h12
  have hq1 : (1:ℝ) ≤ q := by linarith
  have hq0 : (0:ℝ) < q := by linarith
  have hqn : q ≤ n := by exact_mod_cast (show (q:ℝ) ≤ n by rw [hn]; nlinarith)
  have hrad := hr x hlo hhi
  have hrc0 : (0:ℝ) ≤ clusterRange x := Nat.cast_nonneg _
  have hx0 : 0 < x := (pow_pos hq0 92).trans_le hlo
  have hrc1 : 1 ≤ clusterRange x := Nat.ceil_pos.mpr (Real.rpow_pos_of_pos hx0 _)
  have hpow : (q:ℝ)^2 ≤ (q:ℝ)^16 := pow_le_pow_right₀ hq1 (by decide)
  refine ⟨⟨dvd_trans (dvd_mul_left _ _) hdiv, hmin.trans hqn⟩, hnmin.trans hqn,
    by exact_mod_cast hrc1, ?_, by omega, ?_, by dsimp [t]; positivity,
    inv_le_one_of_one_le₀ (one_le_pow₀ hq1), ht, ?_, by dsimp [d]; linarith, ?_, ?_⟩
  · have h0 : 0 ≤ 2^12*(p.side:ℝ)*(clusterRange x:ℝ) := by positivity
    linarith
  · exact_mod_cast (show 4*(q:ℝ)+4 ≤ n by rw [hn]; nlinarith)
  · change 6*((q:ℝ)+1)*(q^16:ℝ)⁻¹ ≤ 1
    rw [←div_eq_mul_inv,div_le_iff₀ (pow_pos hq0 16),one_mul]
    nlinarith [mul_nonneg (sub_nonneg.mpr hq) (sub_nonneg.mpr hq1)]
  · dsimp [d]
    linarith
  · dsimp [d]
    change 2 ≤ v * (q:ℝ) at hvq
    nlinarith [mul_nonneg hv.le hq0.le]

end YangMills.ReferenceCalibration
