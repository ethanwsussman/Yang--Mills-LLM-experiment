import YangMills.Construction.Coordinates.PowerSeriesHolomorphy
import YangMills.Construction.Matrices.DeterminantDerivative
import YangMills.Construction.Matrices.SecondDifferentialOfTheLogarithmOfADeterminant
import Mathlib
set_option autoImplicit false
open Filter Set
open scoped Topology
noncomputable section
namespace YangMills.Construction.Coordinates.ComplexCoordinates.LogDetSecondDeriv
variable {N n : ℕ}
private def dirDerivMatrix (M : ComplexCoordinates N → Matrix (Fin n) (Fin n) ℂ)
    (z v : ComplexCoordinates N) : Matrix (Fin n) (Fin n) ℂ :=
  Matrix.of fun i j => scalarDeriv (fun y => M y i j) z v
private theorem scalarDeriv_eq_apply {g : ComplexCoordinates N → ℂ} {z : ComplexCoordinates N}
    {g' : ComplexCoordinates N →L[ℝ] ℂ} (hg : HasFDerivAt g g' z) (v : ComplexCoordinates N) :
    scalarDeriv g z v = g' v := by
  have h1 : HasFDerivAt (asLine g) (ContinuousLinearMap.pi fun _ : Fin 1 => g') z :=
    (hasFDerivAt_pi (φ := fun _ : Fin 1 => g) (φ' := fun _ => g')).2 fun _ => hg
  simp [scalarDeriv, h1.fderiv]
private theorem hasDerivAt_along_line {g : ComplexCoordinates N → ℂ} {z w : ComplexCoordinates N}
    {t : ℝ} (hg : DifferentiableAt ℝ g (z + t • w)) :
    HasDerivAt (fun s : ℝ => g (z + s • w)) (scalarDeriv g (z + t • w) w) t := by
  have hl : HasDerivAt (fun s : ℝ => z + s • w) w t := by
    simpa using ((hasDerivAt_id t).smul_const w).const_add z
  rw [scalarDeriv_eq_apply hg.hasFDerivAt]
  exact hg.hasFDerivAt.comp_hasDerivAt t hl
private theorem differentiableAt_of_isHolomorphic
    (hS : ComplexCoordinates.PowerSeriesHolomorphy.Properties) {O : Set (ComplexCoordinates N)}
    {g : ComplexCoordinates N → ℂ} (hg : IsHolomorphicScalarIn O g) {z : ComplexCoordinates N}
    (hz : z ∈ O) : DifferentiableAt ℂ g z := by
  obtain ⟨L, hL⟩ := ((hS.1 N O hg.1).1 1 (asLine g) hg).2.2.1 z hz
  have h1 : HasFDerivAt (asLine g) L z := hasFDerivAt_of_restrictScalars ℝ hL rfl
  have h2 := (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 1 => ℂ) 0).hasFDerivAt.comp z h1
  exact h2.differentiableAt
private theorem isHolomorphic_of_differentiableAt {U : Set (ComplexCoordinates N)}
    {g : ComplexCoordinates N → ℂ} (hU : IsOpen U) (hg : ∀ z ∈ U, DifferentiableAt ℂ g z) :
    IsHolomorphicScalarIn U g := by
  have hl : ∀ z ∈ U, DifferentiableAt ℂ (asLine g) z := fun z hz =>
    differentiableAt_pi.2 fun _ => hg z hz
  refine ⟨hU, fun z hz => (hl z hz).continuousAt.continuousWithinAt, fun a ha j => ?_⟩
  have hc : Continuous fun ζ : ℂ => a + ζ • stdBasisVector j := by fun_prop
  have hev : ∀ᶠ ζ in 𝓝 (0 : ℂ), a + ζ • stdBasisVector j ∈ U :=
    hc.continuousAt.eventually_mem (by
      simp only [zero_smul, add_zero]
      exact hU.mem_nhds ha)
  filter_upwards [hev] with ζ hζ
  have hd : DifferentiableAt ℂ (fun ζ : ℂ => a + ζ • stdBasisVector j) ζ := by fun_prop
  exact DifferentiableAt.comp ζ (hl _ hζ) hd
abbrev _root_.YangMills.DeltaSharedProofs.p502090 := @isHolomorphic_of_differentiableAt
private theorem hasDerivAt_scalarDeriv
    (hD : SeparatedFrame.HolomorphicDerivatives.Claim)
    {O : Set (ComplexCoordinates N)} {g : ComplexCoordinates N → ℂ} (hg : IsHolomorphicScalarIn O g)
    {z : ComplexCoordinates N} (hz : z ∈ O) (w v : ComplexCoordinates N) :
    HasDerivAt (fun s : ℝ => scalarDeriv g (z + s • w) v)
      (scalarSecondDeriv g z w v) 0 := by
  have h1 := (((hD N 1 O (asLine g) hg).2 z hz).1 w v).hasDerivAt
  exact hasDerivAt_pi.1 h1 0
private theorem real_line_derivs
    (hD : SeparatedFrame.HolomorphicDerivatives.Claim)
    (hS : ComplexCoordinates.PowerSeriesHolomorphy.Properties)
    {U : Set (ComplexCoordinates N)} {g : ComplexCoordinates N → ℂ} (hU : IsOpen U) (h0 : 0 ∈ U)
    (hg : IsHolomorphicScalarIn U g) (w v : ComplexCoordinates N) :
    HasDerivAt (fun t : ℝ => g (t • w)) (scalarDeriv g 0 w) 0 ∧
      (∀ᶠ t : ℝ in 𝓝 0, DifferentiableAt ℝ (fun t' : ℝ => g (t • w + t' • v)) 0) ∧
      HasDerivAt (fun t : ℝ => deriv (fun t' : ℝ => g (t • w + t' • v)) 0)
        (scalarSecondDeriv g 0 w v) 0 := by
  have hgr : ∀ z ∈ U, DifferentiableAt ℝ g z := fun z hz =>
    (differentiableAt_of_isHolomorphic hS hg hz).restrictScalars ℝ
  have hc : Continuous fun t : ℝ => t • w := by fun_prop
  have hline : ∀ᶠ t : ℝ in 𝓝 0, t • w ∈ U :=
    hc.continuousAt.eventually_mem (by
      simp only [zero_smul]
      exact hU.mem_nhds h0)
  have hderiv : ∀ t : ℝ, t • w ∈ U → HasDerivAt (fun t' : ℝ => g (t • w + t' • v))
      (scalarDeriv g (t • w) v) 0 := by
    intro t ht
    have h1 := hasDerivAt_along_line (g := g) (z := t • w) (w := v) (t := 0) (by simpa using hgr _ ht)
    simpa using h1
  refine ⟨?_, ?_, ?_⟩
  · have h1 := hasDerivAt_along_line (g := g) (z := 0) (w := w) (t := 0) (by simpa using hgr 0 h0)
    simpa using h1
  · filter_upwards [hline] with t ht using (hderiv t ht).differentiableAt
  · have h2 := hasDerivAt_scalarDeriv hD hg h0 w v
    simp only [zero_add] at h2
    refine h2.congr_of_eventuallyEq ?_
    filter_upwards [hline] with t ht using (hderiv t ht).deriv
section Matrices
variable {𝕜 E ι : Type} [NontriviallyNormedField 𝕜] [NormedAlgebra 𝕜 ℂ] [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] [Fintype ι] [DecidableEq ι]
omit [Fintype ι] [DecidableEq ι] in
private theorem differentiableAt_finset_prod' {f : ι → E → ℂ} {x : E} (s : Finset ι)
    (hf : ∀ i, DifferentiableAt 𝕜 (f i) x) : DifferentiableAt 𝕜 (fun y => ∏ i ∈ s, f i y) x := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    simp only [Finset.prod_insert ha]
    exact (hf a).mul ih
private theorem differentiableAt_matrix_det {A : E → Matrix ι ι ℂ} {x : E}
    (hA : ∀ i j, DifferentiableAt 𝕜 (fun y => A y i j) x) :
    DifferentiableAt 𝕜 (fun y => (A y).det) x := by
  simp only [Matrix.det_apply']
  exact DifferentiableAt.fun_sum fun σ _ =>
    (differentiableAt_const _).mul (differentiableAt_finset_prod' _ fun i => hA _ _)
omit [DecidableEq ι] in
private theorem differentiableAt_const_mul_entry {A : E → Matrix ι ι ℂ} {x : E} (P : Matrix ι ι ℂ)
    (hA : ∀ i j, DifferentiableAt 𝕜 (fun y => A y i j) x) (i j : ι) :
    DifferentiableAt 𝕜 (fun y => (P * A y) i j) x := by
  simp only [Matrix.mul_apply]
  exact DifferentiableAt.fun_sum fun l _ => (differentiableAt_const _).mul (hA l j)
private theorem differentiableAt_inv_entry {A : E → Matrix ι ι ℂ} {x : E}
    (hA : ∀ i j, DifferentiableAt 𝕜 (fun y => A y i j) x) (hdet : (A x).det ≠ 0) (i j : ι) :
    DifferentiableAt 𝕜 (fun y => (A y)⁻¹ i j) x := by
  have hadj : DifferentiableAt 𝕜 (fun y => (A y).adjugate i j) x := by
    simp only [Matrix.adjugate_apply]
    refine differentiableAt_matrix_det fun a b => ?_
    simp only [Matrix.updateRow_apply]
    by_cases hab : a = j
    · simp [hab]
    · simpa [hab] using hA a b
  have hinv : ∀ y, (A y)⁻¹ i j = ((A y).det)⁻¹ * (A y).adjugate i j := by
    intro y
    simp [Matrix.inv_def, Ring.inverse_eq_inv']
  simp only [hinv]
  exact ((differentiableAt_matrix_det hA).inv hdet).mul hadj
omit [DecidableEq ι] in
private theorem hasDerivAt_mul_entry {X Y : ℝ → Matrix ι ι ℂ} {X' Y' : Matrix ι ι ℂ} {t : ℝ}
    (hX : ∀ i j, HasDerivAt (fun s => X s i j) (X' i j) t)
    (hY : ∀ i j, HasDerivAt (fun s => Y s i j) (Y' i j) t) (i j : ι) :
    HasDerivAt (fun s => (X s * Y s) i j) ((X' * Y t + X t * Y') i j) t := by
  simp only [Matrix.mul_apply, Matrix.add_apply]
  rw [← Finset.sum_add_distrib]
  exact HasDerivAt.fun_sum fun l _ => (hX i l).mul (hY l j)
omit [DecidableEq ι] in
private theorem hasDerivAt_matrix_trace {Z : ℝ → Matrix ι ι ℂ} {Z' : Matrix ι ι ℂ} {t : ℝ}
    (hZ : ∀ i j, HasDerivAt (fun s => Z s i j) (Z' i j) t) :
    HasDerivAt (fun s => (Z s).trace) Z'.trace t := by
  simp only [Matrix.trace, Matrix.diag_apply]
  exact HasDerivAt.fun_sum fun i _ => hZ i i
end Matrices
private theorem mem_slitPlane_of_norm_sub_one_lt {w : ℂ} (hw : ‖w - 1‖ < 1) :
    w ∈ Complex.slitPlane := by
  simpa using Complex.mem_slitPlane_of_norm_lt_one hw
private theorem seriesLog_eq_log {w : ℂ} (hw : ‖w - 1‖ < 1) :
    seriesLog w = Complex.log w := by
  have h := Complex.hasSum_taylorSeries_log hw
  have h2 := (hasSum_nat_add_iff' 1).2 h
  have h3 : (fun m : ℕ => (-1 : ℂ) ^ m * (w - 1) ^ (m + 1) / ((m + 1 : ℕ) : ℂ)) =
      fun m : ℕ => (-1 : ℂ) ^ (m + 1 + 1) * (w - 1) ^ (m + 1) / ((m + 1 : ℕ) : ℂ) := by
    funext m
    rw [pow_add (-1 : ℂ) (m + 1) 1, pow_add (-1 : ℂ) m 1]
    ring_nf
  unfold seriesLog
  rw [h3, h2.tsum_eq]
  simp
private theorem scalarDeriv_logDet (hJ : Matrices.JacobiDeterminantFormula)
    {O U : Set (ComplexCoordinates N)} {M : ComplexCoordinates N → Matrix (Fin n) (Fin n) ℂ}
    (hU : IsOpen U) (hUO : U ⊆ O)
    (hM : ∀ z ∈ O, ∀ i j, DifferentiableAt ℝ (fun y => M y i j) z) (hM0 : IsUnit (M 0))
    (hnear : ∀ z ∈ U, ‖detNormalized M z - 1‖ < 1)
    (hf : ∀ z ∈ U, DifferentiableAt ℝ (logDetNormalized M) z)
    {z : ComplexCoordinates N} (hz : z ∈ U) (v : ComplexCoordinates N) :
    scalarDeriv (logDetNormalized M) z v =
      ((M z)⁻¹ * dirDerivMatrix M z v).trace := by
  have hopen : IsOpen ((fun t : ℝ => z + t • v) ⁻¹' U) := hU.preimage (by fun_prop)
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hopen 0 (by simpa using hz)
  have hI : ∀ t ∈ Set.Ioo (-ε) ε, z + t • v ∈ U := fun t ht => hball (by
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_lt]
    exact ht)
  have h0I : (0 : ℝ) ∈ Set.Ioo (-ε) ε := ⟨by linarith, hε⟩
  have hnhds : Set.Ioo (-ε) ε ∈ 𝓝 (0 : ℝ) := Ioo_mem_nhds h0I.1 h0I.2
  have hdetP : IsUnit (M 0).det := (Matrix.isUnit_iff_isUnit_det _).1 hM0
  let A : ℝ → Matrix (Fin n) (Fin n) ℂ := fun t => (M 0)⁻¹ * M (z + t • v)
  let A' : ℝ → Matrix (Fin n) (Fin n) ℂ := fun t => (M 0)⁻¹ * dirDerivMatrix M (z + t • v) v
  have hdetA : ∀ t, (A t).det = detNormalized M (z + t • v) := fun t => rfl
  have hAunit : ∀ t ∈ Set.Ioo (-ε) ε, IsUnit (A t) := by
    intro t ht
    rw [Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero, hdetA]
    exact Complex.slitPlane_ne_zero (mem_slitPlane_of_norm_sub_one_lt (hnear _ (hI t ht)))
  have hAder : ∀ t ∈ Set.Ioo (-ε) ε, ∀ i j, HasDerivWithinAt (fun s => A s i j) (A' t i j)
      (Set.Ioo (-ε) ε) t := by
    intro t ht i j
    simp only [A, A', Matrix.mul_apply]
    exact (HasDerivAt.fun_sum fun l _ =>
      (hasDerivAt_along_line (hM _ (hUO (hI t ht)) l j)).const_mul _).hasDerivWithinAt
  have hJ1 := ((hJ (Fin n)).1 (Set.Ioo (-ε) ε) A A' Set.ordConnected_Ioo hAunit hAder 0 h0I
    ).hasDerivAt hnhds
  have hlog := hJ1.clog_real (by
    rw [hdetA]
    exact mem_slitPlane_of_norm_sub_one_lt (hnear _ (hI 0 h0I)))
  have hline := hasDerivAt_along_line (g := logDetNormalized M) (z := z) (w := v) (t := 0)
    (by simpa using hf z hz)
  have hev : (fun s : ℝ => logDetNormalized M (z + s • v)) =ᶠ[𝓝 0]
      fun s => Complex.log (A s).det := by
    filter_upwards [hnhds] with s hs
    exact seriesLog_eq_log (hnear _ (hI s hs))
  have heq := hline.unique (hlog.congr_of_eventuallyEq hev)
  have hA0 : A 0 = (M 0)⁻¹ * M z := by simp [A]
  have hA'0 : A' 0 = (M 0)⁻¹ * dirDerivMatrix M z v := by simp [A']
  have hne : (A 0).det ≠ 0 := (Matrix.isUnit_iff_isUnit_det _).1 (hAunit 0 h0I) |>.ne_zero
  have hdetP' : IsUnit ((M 0)⁻¹).det := Matrix.isUnit_nonsing_inv_det _ hdetP
  have hcancel : (A 0)⁻¹ * A' 0 = (M z)⁻¹ * dirDerivMatrix M z v := by
    rw [hA0, hA'0, Matrix.mul_inv_rev, Matrix.mul_assoc, ← Matrix.mul_assoc _ (M 0)⁻¹,
      Matrix.nonsing_inv_mul _ hdetP', Matrix.one_mul]
  simp only [zero_smul, add_zero] at heq
  rw [heq, mul_div_cancel_left₀ _ hne, hcancel]
private theorem logDet_part
    (hD : SeparatedFrame.HolomorphicDerivatives.Claim)
    (hS : ComplexCoordinates.PowerSeriesHolomorphy.Properties)
    (hJ : Matrices.JacobiDeterminantFormula)
    {O : Set (ComplexCoordinates N)} {M : ComplexCoordinates N → Matrix (Fin n) (Fin n) ℂ}
    (hO : IsOpen O) (h0 : 0 ∈ O) (hM : ∀ i j, IsHolomorphicScalarIn O fun z => M z i j)
    (hM0 : IsUnit (M 0)) :
    (∃ U : Set (ComplexCoordinates N), IsOpen U ∧ 0 ∈ U ∧ U ⊆ O ∧
      (∀ z ∈ U, ‖detNormalized M z - 1‖ < 1) ∧
      IsHolomorphicScalarIn U (logDetNormalized M)) ∧
    ∀ w v : ComplexCoordinates N,
      scalarSecondDeriv (logDetNormalized M) 0 w v =
        Matrix.trace ((M 0)⁻¹ * secondDerivMatrix M w v) -
          Matrix.trace ((M 0)⁻¹ * derivMatrix M w * (M 0)⁻¹ *
            derivMatrix M v) := by
  have hdetM : IsUnit (M 0).det := (Matrix.isUnit_iff_isUnit_det _).1 hM0
  have hMc : ∀ z ∈ O, ∀ i j, DifferentiableAt ℂ (fun y => M y i j) z := fun z hz i j =>
    differentiableAt_of_isHolomorphic hS (hM i j) hz
  have hMr : ∀ z ∈ O, ∀ i j, DifferentiableAt ℝ (fun y => M y i j) z := fun z hz i j =>
    (hMc z hz i j).restrictScalars ℝ
  have hud : ∀ z ∈ O, DifferentiableAt ℂ (detNormalized M) z := fun z hz =>
    differentiableAt_matrix_det (A := fun y => (M 0)⁻¹ * M y)
      fun i j => differentiableAt_const_mul_entry _ (hMc z hz) i j
  have hu0 : detNormalized M 0 = 1 := by
    simp [detNormalized, Matrix.nonsing_inv_mul _ hdetM]
  have hcont : ContinuousOn (detNormalized M) O := fun z hz =>
    (hud z hz).continuousAt.continuousWithinAt
  let U : Set (ComplexCoordinates N) := O ∩ detNormalized M ⁻¹' Metric.ball 1 1
  have hU : IsOpen U := hcont.isOpen_inter_preimage hO Metric.isOpen_ball
  have hUO : U ⊆ O := Set.inter_subset_left
  have h0U : (0 : ComplexCoordinates N) ∈ U := ⟨h0, by simp [hu0]⟩
  have hnear : ∀ z ∈ U, ‖detNormalized M z - 1‖ < 1 := fun z hz => by
    simpa [dist_eq_norm] using hz.2
  have hfc : ∀ z ∈ U, DifferentiableAt ℂ (logDetNormalized M) z := by
    intro z hz
    have hfeq : logDetNormalized M =ᶠ[𝓝 z]
        fun y => Complex.log (detNormalized M y) := by
      filter_upwards [hU.mem_nhds hz] with y hy using seriesLog_eq_log (hnear y hy)
    exact ((hud z (hUO hz)).clog (mem_slitPlane_of_norm_sub_one_lt (hnear z hz))
      ).congr_of_eventuallyEq hfeq
  have hfr : ∀ z ∈ U, DifferentiableAt ℝ (logDetNormalized M) z := fun z hz =>
    (hfc z hz).restrictScalars ℝ
  have hfh : IsHolomorphicScalarIn U (logDetNormalized M) :=
    isHolomorphic_of_differentiableAt hU hfc
  refine ⟨⟨U, hU, h0U, hUO, hnear, hfh⟩, fun w v => ?_⟩
  have hc : Continuous fun s : ℝ => s • w := by fun_prop
  have hline : ∀ᶠ s : ℝ in 𝓝 0, s • w ∈ U :=
    hc.continuousAt.eventually_mem (by
      simp only [zero_smul]
      exact hU.mem_nhds h0U)
  have hX : ∀ i j, HasDerivAt (fun s : ℝ => M (s • w) i j) (derivMatrix M w i j) 0 := by
    intro i j
    have h1 := hasDerivAt_along_line (g := fun y => M y i j) (z := 0) (w := w) (t := 0)
      (by simpa using hMr 0 h0 i j)
    simpa [derivMatrix] using h1
  have hC : ∀ i j, HasDerivAt (fun s : ℝ => dirDerivMatrix M (s • w) v i j)
      (secondDerivMatrix M w v i j) 0 := by
    intro i j
    have h1 := hasDerivAt_scalarDeriv hD (hM i j) h0 w v
    simpa [dirDerivMatrix, secondDerivMatrix] using h1
  have hdet0 : (M ((0 : ℝ) • w)).det ≠ 0 := by simpa using hdetM.ne_zero
  have hBd := differentiableAt_inv_entry (𝕜 := ℝ) (A := fun s : ℝ => M (s • w)) (x := 0)
    (fun i j => (hX i j).differentiableAt) hdet0
  let B' : Matrix (Fin n) (Fin n) ℂ := Matrix.of fun i j => deriv (fun s : ℝ => (M (s • w))⁻¹ i j) 0
  have hB : ∀ i j, HasDerivAt (fun s : ℝ => (M (s • w))⁻¹ i j) (B' i j) 0 := fun i j =>
    (hBd i j).hasDerivAt
  have hdetU : ∀ y ∈ U, IsUnit (M y).det := by
    intro y hy
    have h1 : detNormalized M y ≠ 0 :=
      Complex.slitPlane_ne_zero (mem_slitPlane_of_norm_sub_one_lt (hnear y hy))
    rw [detNormalized, Matrix.det_mul] at h1
    exact isUnit_iff_ne_zero.2 (right_ne_zero_of_mul h1)
  have hone := hasDerivAt_mul_entry hX hB
  have hzero : derivMatrix M w * (M 0)⁻¹ + M 0 * B' = 0 := by
    ext i j
    have h1 := hone i j
    simp only [zero_smul] at h1
    have h2 : HasDerivAt (fun s : ℝ => (M (s • w) * (M (s • w))⁻¹) i j) 0 0 := by
      refine (hasDerivAt_const (0 : ℝ) ((1 : Matrix (Fin n) (Fin n) ℂ) i j)).congr_of_eventuallyEq ?_
      filter_upwards [hline] with s hs
      rw [Matrix.mul_nonsing_inv _ (hdetU _ hs)]
    exact h1.unique h2
  have hB' : B' = -((M 0)⁻¹ * derivMatrix M w * (M 0)⁻¹) := by
    have h1 := congrArg (fun Y => (M 0)⁻¹ * Y) hzero
    simp only [Matrix.mul_add, Matrix.mul_zero, ← Matrix.mul_assoc,
      Matrix.nonsing_inv_mul _ hdetM, Matrix.one_mul] at h1
    exact eq_neg_of_add_eq_zero_right h1
  have hfin := hasDerivAt_matrix_trace (hasDerivAt_mul_entry hB hC)
  have h2 := hasDerivAt_scalarDeriv hD hfh h0U w v
  simp only [zero_add] at h2
  have hev : (fun s : ℝ => scalarDeriv (logDetNormalized M) (s • w) v) =ᶠ[𝓝 0]
      fun s => ((M (s • w))⁻¹ * dirDerivMatrix M (s • w) v).trace := by
    filter_upwards [hline] with s hs
    exact scalarDeriv_logDet hJ hU hUO hMr hM0 hnear hfr hs v
  have heq := h2.unique (hfin.congr_of_eventuallyEq hev)
  have hdm : dirDerivMatrix M 0 v = derivMatrix M v := rfl
  simp only [zero_smul, hdm, hB', Matrix.trace_add, Matrix.neg_mul, Matrix.trace_neg] at heq
  rw [heq]
  ring
theorem claim_holds (hD : SeparatedFrame.HolomorphicDerivatives.Claim)
    (hS : ComplexCoordinates.PowerSeriesHolomorphy.Properties)
    (hJ : Matrices.JacobiDeterminantFormula) : Claim :=
  ⟨fun _ _ _ _ hO h0 hM hM0 => logDet_part hD hS hJ hO h0 hM hM0,
    fun _ _ _ hU h0 hg w v => real_line_derivs hD hS hU h0 hg w v⟩
end YangMills.Construction.Coordinates.ComplexCoordinates.LogDetSecondDeriv
