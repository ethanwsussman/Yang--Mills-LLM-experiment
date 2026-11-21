import YangMills.Construction.Lattice.MatricesBlocksAndGaugeTransformations
import YangMills.Construction.Matrices.ConjugationExpProducts
import YangMills.Construction.OneLoopLaw.PlaneWavesUnderMotionsOfTheLatticeProof
import YangMills.Construction.RunningCouplingSlope.CellsOfNeighbouringFineSites
import YangMills.Construction.RunningCouplingSlope.PlainAverageOfARealField
import YangMills.Construction.RunningCouplingSlope.TheFieldsOfTheChainReadNearCells
import YangMills.Construction.RunningCouplingSlope.TheHessianOfTheSoftActionReadsNearCells
import YangMills.Construction.RunningCouplingSlope.TopBondsAndTheirBlocks
import YangMills.Construction.Towers.ConfigurationsFormedLevelByLevelOnThePolydiscsProof
import Mathlib
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Filter Metric YangMills.Construction.Tower YangMills.Construction.Matrices
open scoped Topology Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction.RunningCouplingSlope.HessianLocality
section SecondDerivatives
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
private def secondDeriv (g : E → ℂ) (x u v : E) : ℂ := fderiv ℂ (fderiv ℂ g) x u v
private lemma secondDeriv_analyticOnNhd [CompleteSpace E] {g : E → ℂ} {s : Set E}
    (hg : AnalyticOnNhd ℂ g s) (u v : E) : AnalyticOnNhd ℂ (fun x => secondDeriv g x u v) s := by
  intro x hx
  have h2 : AnalyticAt ℂ (fderiv ℂ (fderiv ℂ g)) x := hg.fderiv.fderiv x hx
  have e : (fun x => secondDeriv g x u v) =
      ((ContinuousLinearMap.apply ℂ ℂ v).comp
        (ContinuousLinearMap.apply ℂ (E →L[ℂ] ℂ) u)) ∘ fderiv ℂ (fderiv ℂ g) := by
    funext y
    simp [secondDeriv]
  rw [e]
  exact ContinuousLinearMap.analyticAt _ _ |>.comp h2
private lemma hasDerivAt_line (y v : E) :
    HasDerivAt (fun t : ℝ => y + (t : ℂ) • v) v 0 := by
  have h : HasDerivAt (fun t : ℝ => (t : ℂ) • v) ((1 : ℂ) • v) 0 := by
    have h1 : HasDerivAt (fun t : ℝ => (t : ℂ)) 1 0 := Complex.ofRealCLM.hasDerivAt
    exact h1.smul_const v
  simpa using h.const_add y
abbrev _root_.YangMills.SharedProofs.p26497 := @hasDerivAt_line
private lemma hasDerivAt_comp_line {F : Type} [NormedAddCommGroup F] [NormedSpace ℂ F] {g : E → F}
    {y v : E} (hg : DifferentiableAt ℂ g y) :
    HasDerivAt (fun t : ℝ => g (y + (t : ℂ) • v)) (fderiv ℂ g y v) 0 := by
  have h1 : HasFDerivAt g ((fderiv ℂ g y).restrictScalars ℝ) (y + ((0 : ℝ) : ℂ) • v) := by
    simpa using hg.hasFDerivAt.restrictScalars ℝ
  exact h1.comp_hasDerivAt (0 : ℝ) (hasDerivAt_line y v)
private lemma eventually_hasDerivAt_inner {g : E → ℂ} {x u v : E} (hg : AnalyticAt ℂ g x) :
    ∀ᶠ s : ℝ in 𝓝 0, HasDerivAt (fun t : ℝ => g (x + (s : ℂ) • u + (t : ℂ) • v))
      (fderiv ℂ g (x + (s : ℂ) • u) v) 0 := by
  have ht : Tendsto (fun s : ℝ => x + (s : ℂ) • u) (𝓝 0) (𝓝 x) := by
    have := (hasDerivAt_line x u).continuousAt.tendsto
    simpa using this
  filter_upwards [ht.eventually hg.eventually_analyticAt] with s hs
  exact hasDerivAt_comp_line hs.differentiableAt
private lemma hasDerivAt_outer [CompleteSpace E] {g : E → ℂ} {x u v : E} (hg : AnalyticAt ℂ g x) :
    HasDerivAt (fun s : ℝ => fderiv ℂ g (x + (s : ℂ) • u) v) (secondDeriv g x u v) 0 := by
  have h1 : AnalyticAt ℂ (fderiv ℂ g) x := hg.fderiv
  have h2 := hasDerivAt_comp_line (v := u) h1.differentiableAt
  have h3 := ((ContinuousLinearMap.apply ℂ ℂ v).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt
    (0 : ℝ) h2
  exact h3
private lemma deriv_deriv_eq_secondDeriv [CompleteSpace E] {g : E → ℂ} {x u v : E}
    (hg : AnalyticAt ℂ g x) :
    deriv (fun s : ℝ => deriv (fun t : ℝ => g (x + (s : ℂ) • u + (t : ℂ) • v)) 0) 0 =
      secondDeriv g x u v := by
  have h : (fun s : ℝ => deriv (fun t : ℝ => g (x + (s : ℂ) • u + (t : ℂ) • v)) 0) =ᶠ[𝓝 0]
      fun s : ℝ => fderiv ℂ g (x + (s : ℂ) • u) v := by
    filter_upwards [eventually_hasDerivAt_inner (u := u) (v := v) hg] with s hs
    exact hs.deriv
  rw [h.deriv_eq]
  exact (hasDerivAt_outer hg).deriv
private lemma secondDeriv_congr [CompleteSpace E] {g g' : E → ℂ} {x x' u v u' v' : E}
    (hg : AnalyticAt ℂ g x) (hg' : AnalyticAt ℂ g' x')
    (h : ∀ᶠ p : ℝ × ℝ in 𝓝 0, g (x + (p.1 : ℂ) • u + (p.2 : ℂ) • v) =
      g' (x' + (p.1 : ℂ) • u' + (p.2 : ℂ) • v')) :
    secondDeriv g x u v = secondDeriv g' x' u' v' := by
  rw [← deriv_deriv_eq_secondDeriv hg, ← deriv_deriv_eq_secondDeriv hg']
  have h0 : ∀ᶠ p : ℝ × ℝ in 𝓝 ((0 : ℝ), (0 : ℝ)), g (x + (p.1 : ℂ) • u + (p.2 : ℂ) • v) =
      g' (x' + (p.1 : ℂ) • u' + (p.2 : ℂ) • v') := h
  rw [nhds_prod_eq] at h0
  have h1 := h0.curry
  have h2 : (fun s : ℝ => deriv (fun t : ℝ => g (x + (s : ℂ) • u + (t : ℂ) • v)) 0) =ᶠ[𝓝 0]
      fun s : ℝ => deriv (fun t : ℝ => g' (x' + (s : ℂ) • u' + (t : ℂ) • v')) 0 := by
    filter_upwards [h1] with s hs
    exact Filter.EventuallyEq.deriv_eq hs
  exact h2.deriv_eq
private lemma secondDeriv_zero_left (g : E → ℂ) (x v : E) : secondDeriv g x 0 v = 0 := by
  simp [secondDeriv]
private lemma secondDeriv_zero_right (g : E → ℂ) (x u : E) : secondDeriv g x u 0 = 0 := by
  simp [secondDeriv]
private lemma ofReal_deriv_eq {f : ℝ → ℝ} {c : ℝ → ℂ} {D : ℂ}
    (h : ∀ᶠ t in 𝓝 (0 : ℝ), (f t : ℂ) = c t) (hc : HasDerivAt c D 0) :
    ((deriv f 0 : ℝ) : ℂ) = D := by
  have hre : HasDerivAt (fun t => (c t).re) D.re 0 := Complex.reCLM.hasFDerivAt.comp_hasDerivAt (0 : ℝ) hc
  have him : HasDerivAt (fun t => (c t).im) D.im 0 := Complex.imCLM.hasFDerivAt.comp_hasDerivAt (0 : ℝ) hc
  have e1 : f =ᶠ[𝓝 0] fun t => (c t).re := by
    filter_upwards [h] with t ht
    rw [← ht]; simp
  have e2 : (fun t => (c t).im) =ᶠ[𝓝 0] fun _ => (0 : ℝ) := by
    filter_upwards [h] with t ht
    rw [← ht]; simp
  have h0 : D.im = 0 := by
    have := (him.congr_of_eventuallyEq e2.symm).unique (hasDerivAt_const (0 : ℝ) (0 : ℝ))
    have h' := him.unique ((hasDerivAt_const (0 : ℝ) (0 : ℝ)).congr_of_eventuallyEq e2)
    exact h'
  rw [e1.deriv_eq, hre.deriv]
  apply Complex.ext <;> simp [h0]
private lemma ofReal_deriv_deriv_eq_secondDeriv [CompleteSpace E] {g : E → ℂ} {x u v : E}
    (hg : AnalyticAt ℂ g x) {f : ℝ → ℝ → ℝ}
    (h : ∀ᶠ p : ℝ × ℝ in 𝓝 0, ((f p.1 p.2 : ℝ) : ℂ) = g (x + (p.1 : ℂ) • u + (p.2 : ℂ) • v)) :
    ((deriv (fun s => deriv (fun t => f s t) 0) 0 : ℝ) : ℂ) = secondDeriv g x u v := by
  have h0 : ∀ᶠ p : ℝ × ℝ in 𝓝 ((0 : ℝ), (0 : ℝ)), ((f p.1 p.2 : ℝ) : ℂ) =
      g (x + (p.1 : ℂ) • u + (p.2 : ℂ) • v) := h
  rw [nhds_prod_eq] at h0
  have h1 := h0.curry
  refine ofReal_deriv_eq (c := fun s : ℝ => fderiv ℂ g (x + (s : ℂ) • u) v) ?_ (hasDerivAt_outer hg)
  filter_upwards [h1, eventually_hasDerivAt_inner (u := u) (v := v) hg] with s hs hd
  exact ofReal_deriv_eq hs hd
private lemma norm_fderiv_apply_le_of_ball {g : E → ℂ} {x v : E} {R M r : ℝ}
    (hg : DifferentiableOn ℂ g (ball x R)) (hM : ∀ y ∈ ball x R, ‖g y‖ ≤ M) (hv : ‖v‖ ≤ 1)
    (hr : 0 < r) (hrR : r < R) : ‖fderiv ℂ g x v‖ ≤ M / r := by
  have hmaps : ∀ t : ℂ, t ∈ closedBall (0 : ℂ) r → x + t • v ∈ ball x R := by
    intro t ht
    have ht' : ‖t‖ ≤ r := by simpa using ht
    rw [mem_ball, dist_eq_norm]
    have : x + t • v - x = t • v := by abel
    rw [this, norm_smul]
    calc ‖t‖ * ‖v‖ ≤ r * 1 := mul_le_mul ht' hv (norm_nonneg _) hr.le
      _ < R := by linarith
  have hφ : DifferentiableOn ℂ (fun t : ℂ => g (x + t • v)) (closedBall 0 r) := by
    intro t ht
    have h1 : DifferentiableAt ℂ (fun t : ℂ => x + t • v) t := by fun_prop
    have h2 : DifferentiableAt ℂ g (x + t • v) :=
      (hg _ (hmaps t ht)).differentiableAt (isOpen_ball.mem_nhds (hmaps t ht))
    exact (h2.comp t h1).differentiableWithinAt
  have hc := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hr (hφ.diffContOnCl_ball subset_rfl)
    (C := M) (fun t ht => hM _ (hmaps t (sphere_subset_closedBall ht)))
  have hx : DifferentiableAt ℂ g x :=
    (hg x (mem_ball_self (hr.trans hrR))).differentiableAt
      (isOpen_ball.mem_nhds (mem_ball_self (hr.trans hrR)))
  have hd : HasDerivAt (fun t : ℂ => g (x + t • v)) (fderiv ℂ g x v) 0 := by
    have h1 : HasDerivAt (fun t : ℂ => x + t • v) v 0 := by
      simpa using ((hasDerivAt_id (0 : ℂ)).smul_const v).const_add x
    have h2 : HasFDerivAt g (fderiv ℂ g x) (x + (0 : ℂ) • v) := by simpa using hx.hasFDerivAt
    exact h2.comp_hasDerivAt (0 : ℂ) h1
  rwa [hd.deriv] at hc
private lemma norm_secondDeriv_le [CompleteSpace E] {g : E → ℂ} {x u v : E} {R M : ℝ} (hR : 0 < R)
    (hg : AnalyticOnNhd ℂ g (ball x R)) (hM : ∀ y ∈ ball x R, ‖g y‖ ≤ M)
    (hu : ‖u‖ ≤ 1) (hv : ‖v‖ ≤ 1) : ‖secondDeriv g x u v‖ ≤ 16 * M / R ^ 2 := by
  have hdg : DifferentiableOn ℂ g (ball x R) := hg.differentiableOn
  have hsub : ∀ y ∈ ball x (R / 2), ball y (R / 2) ⊆ ball x R := by
    intro y hy
    refine (ball_subset_ball' ?_)
    have : dist y x < R / 2 := hy
    linarith
  have h1 : ∀ y ∈ ball x (R / 2), ‖fderiv ℂ g y v‖ ≤ M / (R / 4) := by
    intro y hy
    exact norm_fderiv_apply_le_of_ball (R := R / 2) (hdg.mono (hsub y hy))
      (fun w hw => hM w (hsub y hy hw)) hv (by positivity) (by linarith)
  have hx : x ∈ ball x R := mem_ball_self hR
  have hd1 : DifferentiableOn ℂ (fun y => fderiv ℂ g y v) (ball x (R / 2)) := by
    intro y hy
    have hy' : y ∈ ball x R := ball_subset_ball (by linarith) hy
    have h2 : AnalyticAt ℂ (fderiv ℂ g) y := (hg y hy').fderiv
    exact (h2.differentiableAt.clm_apply (differentiableAt_const v)).differentiableWithinAt
  have h3 := norm_fderiv_apply_le_of_ball (R := R / 2) (r := R / 4) (x := x) (v := u) hd1 h1 hu
    (by positivity) (by linarith)
  have h4 : fderiv ℂ (fun y => fderiv ℂ g y v) x u = secondDeriv g x u v := by
    have h2 : AnalyticAt ℂ (fderiv ℂ g) x := (hg x hx).fderiv
    have := ((ContinuousLinearMap.apply ℂ ℂ v).hasFDerivAt.comp x
      h2.differentiableAt.hasFDerivAt).fderiv
    have e : (fun y => fderiv ℂ g y v) = (ContinuousLinearMap.apply ℂ ℂ v) ∘ fderiv ℂ g := rfl
    rw [e, this]
    simp [secondDeriv]
  rw [h4] at h3
  refine h3.trans (le_of_eq ?_)
  field_simp
  ring
end SecondDerivatives
section RowColumnSums
variable {m : Type} [Fintype m] [DecidableEq m]
private lemma opNorm_le_of_row_col_sums (A : Matrix m m ℂ) {K : ℝ} (hK : 0 ≤ K)
    (hr : ∀ p, ∑ q, ‖A p q‖ ≤ K) (hc : ∀ q, ∑ p, ‖A p q‖ ≤ K) : ‖A‖ ≤ K := by
  rw [Matrix.l2_opNorm_def]
  refine ContinuousLinearMap.opNorm_le_bound _ hK fun x => ?_
  have hx : ∀ p, ‖(A.mulVec (x : m → ℂ)) p‖ ^ 2 ≤ K * ∑ q, ‖A p q‖ * ‖x q‖ ^ 2 := by
    intro p
    have h1 : ‖(A.mulVec (x : m → ℂ)) p‖ ≤ ∑ q, ‖A p q‖ * ‖x q‖ := by
      simp only [Matrix.mulVec, dotProduct]
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun q _ => ?_)
      rw [norm_mul]
    have h2 : (∑ q, ‖A p q‖ * ‖x q‖) ^ 2 ≤
        (∑ q, ‖A p q‖) * ∑ q, ‖A p q‖ * ‖x q‖ ^ 2 := by
      have := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
        (fun q => Real.sqrt ‖A p q‖) (fun q => Real.sqrt ‖A p q‖ * ‖x q‖)
      have e1 : ∀ q, Real.sqrt ‖A p q‖ * (Real.sqrt ‖A p q‖ * ‖x q‖) = ‖A p q‖ * ‖x q‖ := by
        intro q
        rw [← mul_assoc, Real.mul_self_sqrt (norm_nonneg _)]
      have e2 : ∀ q, Real.sqrt ‖A p q‖ ^ 2 = ‖A p q‖ := fun q => Real.sq_sqrt (norm_nonneg _)
      have e3 : ∀ q, (Real.sqrt ‖A p q‖ * ‖x q‖) ^ 2 = ‖A p q‖ * ‖x q‖ ^ 2 := by
        intro q
        rw [mul_pow, e2]
      simpa only [e1, e2, e3] using this
    have h3 : 0 ≤ ∑ q, ‖A p q‖ * ‖x q‖ ^ 2 :=
      Finset.sum_nonneg fun q _ => by positivity
    calc ‖(A.mulVec (x : m → ℂ)) p‖ ^ 2 ≤ (∑ q, ‖A p q‖ * ‖x q‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
      _ ≤ (∑ q, ‖A p q‖) * ∑ q, ‖A p q‖ * ‖x q‖ ^ 2 := h2
      _ ≤ K * ∑ q, ‖A p q‖ * ‖x q‖ ^ 2 := mul_le_mul_of_nonneg_right (hr p) h3
  have hsq : ‖Matrix.toEuclideanCLM (n := m) (𝕜 := ℂ) A x‖ ^ 2 ≤ (K * ‖x‖) ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    have hn : ‖x‖ ^ 2 = ∑ q, ‖x q‖ ^ 2 := EuclideanSpace.norm_sq_eq x
    calc ∑ p, ‖(Matrix.toEuclideanCLM (n := m) (𝕜 := ℂ) A x) p‖ ^ 2
        = ∑ p, ‖(A.mulVec (x : m → ℂ)) p‖ ^ 2 := by
          refine Finset.sum_congr rfl fun p _ => ?_
          rfl
      _ ≤ ∑ p, K * ∑ q, ‖A p q‖ * ‖x q‖ ^ 2 := Finset.sum_le_sum fun p _ => hx p
      _ = K * ∑ q, (∑ p, ‖A p q‖) * ‖x q‖ ^ 2 := by
          rw [← Finset.mul_sum, Finset.sum_comm]
          simp only [Finset.sum_mul]
      _ ≤ K * ∑ q, K * ‖x q‖ ^ 2 := by
          refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun q _ => ?_) hK
          exact mul_le_mul_of_nonneg_right (hc q) (by positivity)
      _ = (K * ‖x‖) ^ 2 := by
          rw [← Finset.mul_sum, mul_pow, hn]
          ring
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 hsq
abbrev _root_.YangMills.SharedProofs.p42812 := @opNorm_le_of_row_col_sums
end RowColumnSums
private def pauliCoord (a : Fin 3) : ComplexMatrix2 →ₗ[ℂ] ℂ where
  toFun X := ![(X 0 1 + X 1 0) / 2, (X 1 0 - X 0 1) / (2 * Complex.I), X 0 0] a
  map_add' X Y := by fin_cases a <;> simp <;> ring
  map_smul' c X := by fin_cases a <;> simp <;> ring
private def pauliCoordCLM (a : Fin 3) : ComplexMatrix2 →L[ℂ] ℂ := (pauliCoord a).toContinuousLinearMap
private lemma trace_eq_zero_of_traceless {X : ComplexMatrix2} (hX : X ∈ ComplexMatrix2.traceless) :
    X 0 0 + X 1 1 = 0 := by
  have h : Matrix.trace X = 0 := hX
  simpa [Matrix.trace_fin_two] using h
private lemma sum_pauliCoord_smul {X : ComplexMatrix2} (hX : X ∈ ComplexMatrix2.traceless) :
    ∑ a, pauliCoordCLM a X • ComplexMatrix2.pauliFamily a = X := by
  have h := trace_eq_zero_of_traceless hX
  have e : ∑ a, pauliCoordCLM a X • ComplexMatrix2.pauliFamily a =
      !![pauliCoordCLM 2 X, pauliCoordCLM 0 X - Complex.I * pauliCoordCLM 1 X;
        pauliCoordCLM 0 X + Complex.I * pauliCoordCLM 1 X, -pauliCoordCLM 2 X] :=
    ComplexMatrix2.sum_smul_pauliFamily fun a => pauliCoordCLM a X
  rw [e]
  have hI : Complex.I ≠ 0 := Complex.I_ne_zero
  ext i j
  fin_cases i <;> fin_cases j <;> simp [pauliCoordCLM, pauliCoord] <;> (try field_simp) <;>
    first | ring1 | linear_combination (-1 : ℂ) * h
private lemma pauliCoeff_eq_pauliCoord {X : ComplexMatrix2} (hX : X ∈ ComplexMatrix2.traceless)
    (a : Fin 3) : pauliCoeff a X = pauliCoordCLM a X := by
  simp only [pauliCoeff, dif_pos hX]
  fin_cases a <;> rfl
private lemma pauliFamily_mem_traceless (a : Fin 3) :
    ComplexMatrix2.pauliFamily a ∈ ComplexMatrix2.traceless := by apply _root_.YangMills.Construction.OneLoopLaw.PlaneWaveSymmetries.pauliFamily_mem_traceless <;> assumption
private def expProd (A B : ComplexMatrix2) : ComplexMatrix2 :=
  ComplexMatrix2.matExp (Complex.I • A) * ComplexMatrix2.matExp (Complex.I • B)
private def expLogJoin (A B : ComplexMatrix2) : ComplexMatrix2 :=
  Complex.I⁻¹ • ComplexMatrix2.logSeries (expProd A B)
private lemma analyticAt_const_smul' {F : Type} [NormedAddCommGroup F] [NormedSpace ℂ F] (c : ℂ)
    {f : F → ComplexMatrix2} {x : F} (hf : AnalyticAt ℂ f x) : AnalyticAt ℂ (fun q => c • f q) x :=
  AnalyticAt.comp (g := c • ContinuousLinearMap.id ℂ ComplexMatrix2) (f := f)
    (ContinuousLinearMap.analyticAt _ _) hf
private lemma expProd_analyticAt (p : ComplexMatrix2 × ComplexMatrix2) :
    AnalyticAt ℂ (fun q : ComplexMatrix2 × ComplexMatrix2 => expProd q.1 q.2) p := by
  have e : ∀ A : ComplexMatrix2, AnalyticAt ℂ NormedSpace.exp A := fun A => NormedSpace.exp_analytic A
  have h1 : AnalyticAt ℂ (fun q : ComplexMatrix2 × ComplexMatrix2 =>
      ComplexMatrix2.matExp (Complex.I • q.1)) p :=
    (e _).comp (analyticAt_const_smul' _ analyticAt_fst)
  have h2 : AnalyticAt ℂ (fun q : ComplexMatrix2 × ComplexMatrix2 =>
      ComplexMatrix2.matExp (Complex.I • q.2)) p :=
    (e _).comp (analyticAt_const_smul' _ analyticAt_snd)
  exact h1.mul h2
abbrev _root_.YangMills.DeltaSharedProofs.p501919 := @expProd_analyticAt
private lemma expLogJoin_analyticAt (hS : PeriodicLattice.LogSeriesNearOne)
    {p : ComplexMatrix2 × ComplexMatrix2} (hp : ‖expProd p.1 p.2 - 1‖ < 1) :
    AnalyticAt ℂ (fun q : ComplexMatrix2 × ComplexMatrix2 => expLogJoin q.1 q.2) p := by
  have h1 : AnalyticAt ℂ ComplexMatrix2.logSeries (expProd p.1 p.2) := hS.1 _ hp
  have h2 : AnalyticAt ℂ (fun q : ComplexMatrix2 × ComplexMatrix2 =>
      ComplexMatrix2.logSeries (expProd q.1 q.2)) p :=
    AnalyticAt.comp (g := ComplexMatrix2.logSeries)
      (f := fun q : ComplexMatrix2 × ComplexMatrix2 => expProd q.1 q.2) h1 (expProd_analyticAt p)
  exact analyticAt_const_smul' _ h2
abbrev _root_.YangMills.DeltaSharedProofs.p502181 := @expLogJoin_analyticAt
private lemma expLogJoin_spec (hS : PeriodicLattice.LogSeriesNearOne)
    (hE : ComplexMatrix2.ExpLogEstimates) {A B : ComplexMatrix2} (hA : A ∈ ComplexMatrix2.traceless)
    (hB : B ∈ ComplexMatrix2.traceless) (h : ‖expProd A B - 1‖ < 9 / 10) :
    expLogJoin A B ∈ ComplexMatrix2.traceless ∧
      ComplexMatrix2.matExp (Complex.I • expLogJoin A B) = expProd A B := by
  have hdet : ∀ Z : ComplexMatrix2, Z ∈ ComplexMatrix2.traceless →
      (ComplexMatrix2.matExp (Complex.I • Z)).det = 1 := by
    intro Z hZ
    rw [hE.2.2.2.2.2.1]
    have : ComplexMatrix2.fullTrace (Complex.I • Z) = 0 := by
      have hz : Matrix.trace Z = 0 := hZ
      simp [ComplexMatrix2.fullTrace, Matrix.trace_smul, hz]
    rw [this, Complex.exp_zero]
  have hd : (expProd A B).det = 1 := by
    rw [expProd, Matrix.det_mul, hdet A hA, hdet B hB, one_mul]
  refine ⟨?_, ?_⟩
  · exact ComplexMatrix2.traceless.smul_mem _ (hE.2.2.2.2.2.2.1 _ hd h.le).2
  · have : Complex.I • expLogJoin A B = ComplexMatrix2.logSeries (expProd A B) := by
      simp [expLogJoin, smul_smul]
    rw [this]
    exact hS.2.2.2 _ (by
      change ‖expProd A B - 1‖ < 1
      linarith)
abbrev _root_.YangMills.DeltaSharedProofs.p502490 := @expLogJoin_spec
private lemma exists_expLogJoin_small (hS : PeriodicLattice.LogSeriesNearOne) {ρ : ℝ} (hρ : 0 < ρ) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ A B : ComplexMatrix2, ‖A‖ < δ → ‖B‖ < δ →
      ‖expProd A B - 1‖ < 9 / 10 ∧ ∀ a, ‖pauliCoordCLM a (expLogJoin A B)‖ < ρ := by
  have h0 : expProd 0 0 = 1 := by simp [expProd]
  have hc : ContinuousAt (fun q : ComplexMatrix2 × ComplexMatrix2 => expProd q.1 q.2) 0 :=
    (expProd_analyticAt 0).continuousAt
  have h1 : ∀ᶠ q : ComplexMatrix2 × ComplexMatrix2 in 𝓝 0, ‖expProd q.1 q.2 - 1‖ < 9 / 10 := by
    have : Tendsto (fun q : ComplexMatrix2 × ComplexMatrix2 => ‖expProd q.1 q.2 - 1‖) (𝓝 0)
        (𝓝 0) := by
      have h := (hc.tendsto.sub_const 1).norm
      simpa [h0] using h
    exact this.eventually (gt_mem_nhds (by norm_num))
  have hj0 : expLogJoin 0 0 = 0 := by
    simp [expLogJoin, h0, hS.2.1]
  have hja : AnalyticAt ℂ (fun q : ComplexMatrix2 × ComplexMatrix2 => expLogJoin q.1 q.2) 0 :=
    expLogJoin_analyticAt hS (by simp [h0])
  have h2 : ∀ a, ∀ᶠ q : ComplexMatrix2 × ComplexMatrix2 in 𝓝 0,
      ‖pauliCoordCLM a (expLogJoin q.1 q.2)‖ < ρ := by
    intro a
    have hc' : ContinuousAt (fun q : ComplexMatrix2 × ComplexMatrix2 =>
        pauliCoordCLM a (expLogJoin q.1 q.2)) 0 :=
      (pauliCoordCLM a).continuous.continuousAt.comp hja.continuousAt
    have : Tendsto (fun q : ComplexMatrix2 × ComplexMatrix2 =>
        ‖pauliCoordCLM a (expLogJoin q.1 q.2)‖) (𝓝 0) (𝓝 0) := by
      have h := hc'.tendsto.norm
      simpa [hj0] using h
    exact this.eventually (gt_mem_nhds hρ)
  have h3 : ∀ᶠ q : ComplexMatrix2 × ComplexMatrix2 in 𝓝 0, ‖expProd q.1 q.2 - 1‖ < 9 / 10 ∧
      ∀ a, ‖pauliCoordCLM a (expLogJoin q.1 q.2)‖ < ρ := h1.and (eventually_all.2 h2)
  obtain ⟨δ, hδ, hb⟩ := Metric.eventually_nhds_iff_ball.1 h3
  refine ⟨δ, hδ, fun A B hA hB => hb (A, B) ?_⟩
  rw [mem_ball_zero_iff, Prod.norm_def]
  exact max_lt hA hB
section Coordinates
variable {L n k : ℕ}
private def colourIndex : LevelFormIndex L n k → Fin 3
  | .inl p => p.1
  | .inr p => p.2.1
private def withColour (a : Fin 3) : LevelFormIndex L n k → LevelFormIndex L n k
  | .inl p => .inl (a, p.2)
  | .inr p => .inr ⟨p.1, (a, p.2.2)⟩
@[simp] private lemma withColour_withColour (a b : Fin 3) (p : LevelFormIndex L n k) :
    withColour a (withColour b p) = withColour a p := by
  rcases p with p | p <;> rfl
@[simp] private lemma colourIndex_withColour (a : Fin 3) (p : LevelFormIndex L n k) :
    colourIndex (withColour a p) = a := by
  rcases p with p | p <;> rfl
private lemma cell_withColour (a : Fin 3) (p : LevelFormIndex L n k) :
    levelFormIndexCell (withColour a p) = levelFormIndexCell p := by
  rcases p with p | p <;> rfl
private def bondMatrix (f : LevelFormIndex L n k → ℂ) (p : LevelFormIndex L n k) : ComplexMatrix2 :=
  ∑ a, f (withColour a p) • ComplexMatrix2.pauliFamily a
private lemma bondMatrix_mem (f : LevelFormIndex L n k → ℂ) (p : LevelFormIndex L n k) :
    bondMatrix f p ∈ ComplexMatrix2.traceless :=
  ComplexMatrix2.traceless.sum_mem fun a _ =>
    ComplexMatrix2.traceless.smul_mem _ (pauliFamily_mem_traceless a)
private def formPart (z : TripleCoordIndex L n k → ℂ) : LevelFormIndex L n k → ℂ := fun q => z (.inl q)
private def movedCoords (z : TripleCoordIndex L n k → ℂ) (ε : LevelFormIndex L n k → ℂ) :
    TripleCoordIndex L n k → ℂ :=
  Sum.elim (fun p => pauliCoordCLM (colourIndex p) (expLogJoin (bondMatrix ε p) (bondMatrix (formPart z) p)))
    fun r => z (.inr r)
private lemma bondMatrix_movedCoords (hS : PeriodicLattice.LogSeriesNearOne)
    (hE : ComplexMatrix2.ExpLogEstimates) {z : TripleCoordIndex L n k → ℂ}
    {ε : LevelFormIndex L n k → ℂ} (p : LevelFormIndex L n k)
    (h : ‖expProd (bondMatrix ε p) (bondMatrix (formPart z) p) - 1‖ < 9 / 10) :
    bondMatrix (formPart (movedCoords z ε)) p =
      expLogJoin (bondMatrix ε p) (bondMatrix (formPart z) p) := by
  have hj := (expLogJoin_spec hS hE (bondMatrix_mem ε p) (bondMatrix_mem _ p) h).1
  rw [← sum_pauliCoord_smul hj]
  simp [bondMatrix, formPart, movedCoords]
private lemma complexFineValues_positive (z : TripleCoordIndex L n k → ℂ) (b : PositiveEdge L n k 0) :
    complexFineValues z b.1 = bondMatrix (formPart z) (.inl (0, b)) := by
  simp only [complexFineValues, edgeFormOfPositiveValues, dif_pos b.2]
  rfl
private lemma complexLevelValues_eq (z : TripleCoordIndex L n k → ℂ) (i : Fin k)
    (c : PositiveEdge L n k (i + 1)) :
    complexLevelValues z i c = bondMatrix (formPart z) (.inr ⟨i, (0, c)⟩) := rfl
private lemma opposite_isPositive {j : ℕ} (b : Edge L n k j) (hb : ¬ b.IsPositivelyOriented) :
    b.opposite.IsPositivelyOriented := by apply _root_.YangMills.Construction.Tower.IteratedMeans.opposite_isPositivelyOriented_of_not <;> assumption
private lemma expMove_complexChainPoint (hS : PeriodicLattice.LogSeriesNearOne)
    (hE : ComplexMatrix2.ExpLogEstimates) {z : TripleCoordIndex L n k → ℂ}
    {ε : LevelFormIndex L n k → ℂ} (ξ : LevelForms L n k)
    (h1 : ∀ b : PositiveEdge L n k 0,
      (ξ.1 : Edge L n k 0 → ComplexMatrix2) b.1 = bondMatrix ε (.inl (0, b)))
    (h2 : ∀ (i : Fin k) (c : PositiveEdge L n k (i + 1)),
      (ξ.2 i : Edge L n k (i + 1) → ComplexMatrix2) c.1 = bondMatrix ε (.inr ⟨i, (0, c)⟩))
    (h : ∀ p, ‖expProd (bondMatrix ε p) (bondMatrix (formPart z) p) - 1‖ < 9 / 10) :
    expMove ξ (complexChainPoint z) = complexChainPoint (movedCoords z ε) := by
  have core : ∀ p : LevelFormIndex L n k,
      ComplexMatrix2.matExp (Complex.I • bondMatrix ε p) *
          ComplexMatrix2.matExp (Complex.I • bondMatrix (formPart z) p) =
        ComplexMatrix2.matExp (Complex.I • bondMatrix (formPart (movedCoords z ε)) p) := by
    intro p
    rw [bondMatrix_movedCoords hS hE p (h p),
      (expLogJoin_spec hS hE (bondMatrix_mem ε p) (bondMatrix_mem _ p) (h p)).2]
    rfl
  have base : ∀ b : PositiveEdge L n k 0,
      ComplexMatrix2.matExp (Complex.I • (ξ.1 : Edge L n k 0 → ComplexMatrix2) b.1) *
          (PeriodicLattice.expTwist (complexFineValues z) (unitPoint L n k).fine b.1) =
        PeriodicLattice.expTwist (complexFineValues (movedCoords z ε))
          (unitPoint L n k).fine b.1 := by
    intro b
    simp only [PeriodicLattice.expTwist, if_pos b.2, unitPoint, mul_one, complexFineValues_positive, h1]
    exact core _
  unfold expMove complexChainPoint
  congr 1
  · funext b
    by_cases hb : b.IsPositivelyOriented
    · have := base ⟨b, hb⟩
      simpa only [PeriodicLattice.expTwist, if_pos hb] using this
    · have hr := opposite_isPositive b hb
      have := base ⟨b.opposite, hr⟩
      simp only [PeriodicLattice.expTwist, if_pos hr] at this
      simp only [PeriodicLattice.expTwist, if_neg hb, if_pos hr]
      exact congrArg _ this
  · funext i c
    have := core (.inr ⟨i, (0, c)⟩)
    simp only [unitPoint, mul_one, complexLevelValues_eq, h2]
    exact this
end Coordinates
section Cells
variable {L n k : ℕ}
private lemma toSublattice_self {j : ℕ} (x : Vertex L n k j) :
    x.toSublattice (PeriodicLattice.levelDepth k j) = x := by
  apply Subtype.ext
  exact Classical.epsilon_spec
    (p := fun x' : PeriodicLattice.Site L n (PeriodicLattice.levelDepth k j) =>
      (x' : PeriodicLattice.FourTorus L n) = x) ⟨x, rfl⟩
private lemma levelVertexCell_zero (x : Vertex L n k 0) : levelVertexCell x = fineVertexCell x := by
  rw [levelVertexCell, toSublattice_self]
abbrev _root_.YangMills.SharedProofs.p6946 := @levelVertexCell_zero
private lemma refinedBlock_of_cell (hLat : PeriodicLattice.CoordinateDescription)
    (hCell : NeighbouringFineVertexCells) (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n)
    (y : Vertex L n k k) :
    (PeriodicLattice.refinedBlock k y).Finite ∧
      (PeriodicLattice.refinedBlock k y).ncard = L ^ (4 * k) ∧
      ∀ {j : ℕ} (_ : j ≤ k) (x : Vertex L n k j), levelVertexCell x = y →
        (x : PeriodicLattice.FourTorus L n) ∈ PeriodicLattice.refinedBlock k y := by
  have hj : -(n : ℤ) ≤ PeriodicLattice.levelDepth k k := by
    simp only [PeriodicLattice.levelDepth]
    omega
  have hb := ((hLat L n hL.1 hL.2 hn).2.2.1 (PeriodicLattice.levelDepth k k) k hj y).2.2.2.1
  have hL0 : 0 < L := by have := hL.2; omega
  refine ⟨Set.finite_of_ncard_pos ?_, hb, fun {j} hjk x h => ?_⟩
  · rw [hb]
    positivity
  · have hj' : -(n : ℤ) ≤ PeriodicLattice.levelDepth k j := by
      simp only [PeriodicLattice.levelDepth]
      omega
    have hle : PeriodicLattice.levelDepth k j ≤ PeriodicLattice.levelDepth k 0 := by
      simp only [PeriodicLattice.levelDepth]
      omega
    have hmem := ((hLat L n hL.1 hL.2 hn).1 _ hj').2.2.1 _ hle x.2
    have hcoe : ((x.toSublattice (PeriodicLattice.levelDepth k 0) : PeriodicLattice.Site L n _) :
        PeriodicLattice.FourTorus L n) = x :=
      Classical.epsilon_spec
        (p := fun x' : PeriodicLattice.Site L n (PeriodicLattice.levelDepth k 0) =>
          (x' : PeriodicLattice.FourTorus L n) = x) ⟨⟨x, hmem⟩, rfl⟩
    rw [← h, ← hcoe]
    exact (hCell L hL n k).2.2.1 (x.toSublattice _)
abbrev _root_.YangMills.SharedProofs.p41695 := @refinedBlock_of_cell
private def axisOf {j : ℕ} (b : PositiveEdge L n k j) : Fin 4 := b.2.choose
private lemma positiveEdge_eq {j : ℕ} (p q : PositiveEdge L n k j)
    (ht : (p.1.source : PeriodicLattice.FourTorus L n) = q.1.source) (hd : axisOf p = axisOf q) :
    p = q := by
  apply Subtype.ext
  have h1 := p.2.choose_spec
  have h2 := q.2.choose_spec
  have ht' : p.1.source = q.1.source := Subtype.ext ht
  have h3 : p.1.target = q.1.target := by
    have e1 : p.1.target = p.1.source + PeriodicLattice.unitStep L n _ (axisOf p) := by
      rw [← sub_eq_iff_eq_add']; exact h1
    have e2 : q.1.target = q.1.source + PeriodicLattice.unitStep L n _ (axisOf q) := by
      rw [← sub_eq_iff_eq_add']; exact h2
    rw [e1, e2, ht', hd]
  exact PeriodicLattice.Bond.ext ht' h3
private lemma card_filter_le_labels {ι κ Y P : Type} [Fintype ι] [Fintype κ] (c : ι → Y) (y : Y)
    [DecidablePred fun p => c p = y] (pt : ι → P) (lab : ι → κ) (B : Set P) (hB : B.Finite)
    (hmem : ∀ p, c p = y → pt p ∈ B)
    (hinj : ∀ p q, c p = y → c q = y → lab p = lab q → pt p = pt q → p = q) :
    (Finset.univ.filter fun p => c p = y).card ≤ Fintype.card κ * B.ncard := by
  classical
  have h := Finset.card_le_card_of_injOn (s := Finset.univ.filter fun p => c p = y)
    (t := (Finset.univ : Finset κ) ×ˢ hB.toFinset) (fun p => (lab p, pt p)) ?_ ?_
  · refine h.trans ?_
    rw [Finset.card_product, Finset.card_univ, Set.ncard_eq_toFinset_card B hB]
  · intro p hp
    have hp' : c p = y := (Finset.mem_filter.mp hp).2
    simp only [Finset.coe_product, Finset.coe_univ, Set.Finite.coe_toFinset, Set.mem_prod,
      Set.mem_univ, true_and]
    exact hmem p hp'
  · intro p hp q hq e
    have hp' : c p = y := (Finset.mem_filter.mp hp).2
    have hq' : c q = y := (Finset.mem_filter.mp hq).2
    exact hinj p q hp' hq' (congrArg Prod.fst e) (congrArg Prod.snd e)
abbrev _root_.YangMills.SharedProofs.p5765 := @card_filter_le_labels
private abbrev FormLabel (k : ℕ) : Type := Fin (k + 1) × Fin 3 × Fin 4
private def formPoint : LevelFormIndex L n k → PeriodicLattice.FourTorus L n
  | .inl p => p.2.1.source
  | .inr p => p.2.2.1.source
private def formLabel : LevelFormIndex L n k → FormLabel k
  | .inl p => (0, p.1, axisOf p.2)
  | .inr p => (⟨p.1 + 1, by have := p.1.2; omega⟩, p.2.1, axisOf p.2.2)
private lemma formLabel_injective (p q : LevelFormIndex L n k) (hl : formLabel p = formLabel q)
    (hp : formPoint p = formPoint q) : p = q := by
  rcases p with ⟨c, b⟩ | ⟨i, c, b⟩ <;> rcases q with ⟨c', b'⟩ | ⟨i', c', b'⟩
  · simp only [formLabel, Prod.mk.injEq, true_and] at hl
    simp only [formPoint] at hp
    obtain rfl := hl.1
    rw [positiveEdge_eq b b' hp hl.2]
  · simp only [formLabel, Prod.mk.injEq] at hl
    have := congrArg Fin.val hl.1
    simp at this
  · simp only [formLabel, Prod.mk.injEq] at hl
    have := congrArg Fin.val hl.1
    simp at this
  · simp only [formLabel, Prod.mk.injEq] at hl
    have h1 := congrArg Fin.val hl.1
    simp only [Nat.add_right_cancel_iff] at h1
    obtain rfl : i = i' := Fin.ext h1
    simp only [formPoint] at hp
    obtain rfl := hl.2.1
    rw [positiveEdge_eq b b' hp hl.2.2]
open Classical in
private lemma card_form_cell (hLat : PeriodicLattice.CoordinateDescription)
    (hCell : NeighbouringFineVertexCells) (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n)
    [Fintype (LevelFormIndex L n k)] (y : Vertex L n k k) :
    (Finset.univ.filter fun p : LevelFormIndex L n k => levelFormIndexCell p = y).card ≤
      Fintype.card (FormLabel k) * L ^ (4 * k) := by
  obtain ⟨hf, hc, hm⟩ := refinedBlock_of_cell (k := k) hLat hCell hL hn y
  rw [← hc]
  refine card_filter_le_labels (ι := LevelFormIndex L n k) levelFormIndexCell y formPoint formLabel _
    hf ?_ ?_
  · rintro (p | p) hp
    · exact hm (Nat.zero_le k) p.2.1.source hp
    · exact hm (by have := p.1.2; omega) p.2.2.1.source hp
  · exact fun p q _ _ => formLabel_injective p q
abbrev _root_.YangMills.DeltaSharedProofs.p502328 := @card_form_cell
private abbrev ActionTerm (L n k : ℕ) : Type :=
  Face L n k 0 ⊕ (Σ i : Fin k, PositiveEdge L n k (i + 1))
private def actionTermCell : ActionTerm L n k → Vertex L n k k
  | .inl p => levelVertexCell p.origin
  | .inr c => levelVertexCell c.2.1.source
private abbrev ActionTermLabel (k : ℕ) : Type := (Fin 4 × Fin 4) ⊕ (Fin k × Fin 4)
private def actionTermPoint : ActionTerm L n k → PeriodicLattice.FourTorus L n
  | .inl p => p.origin
  | .inr c => c.2.1.source
private def actionTermLabel : ActionTerm L n k → ActionTermLabel k
  | .inl p => .inl (p.firstAxis, p.secondAxis)
  | .inr c => .inr (c.1, axisOf c.2)
private lemma actionTermLabel_injective (p q : ActionTerm L n k)
    (hl : actionTermLabel p = actionTermLabel q) (hp : actionTermPoint p = actionTermPoint q) :
    p = q := by
  rcases p with p | ⟨i, b⟩ <;> rcases q with q | ⟨i', b'⟩
  · simp only [actionTermLabel, Sum.inl.injEq, Prod.mk.injEq] at hl
    simp only [actionTermPoint] at hp
    exact congrArg _ (PeriodicLattice.Plaquette.ext (Subtype.ext hp) hl.1 hl.2)
  · simp [actionTermLabel] at hl
  · simp [actionTermLabel] at hl
  · simp only [actionTermLabel, Sum.inr.injEq, Prod.mk.injEq] at hl
    simp only [actionTermPoint] at hp
    obtain rfl := hl.1
    rw [positiveEdge_eq b b' hp hl.2]
open Classical in
private lemma card_actionTerm_cell (hLat : PeriodicLattice.CoordinateDescription)
    (hCell : NeighbouringFineVertexCells) (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n)
    [Fintype (ActionTerm L n k)] (y : Vertex L n k k) :
    (Finset.univ.filter fun p : ActionTerm L n k => actionTermCell p = y).card ≤
      Fintype.card (ActionTermLabel k) * L ^ (4 * k) := by
  obtain ⟨hf, hc, hm⟩ := refinedBlock_of_cell (k := k) hLat hCell hL hn y
  rw [← hc]
  refine card_filter_le_labels (ι := ActionTerm L n k) actionTermCell y actionTermPoint actionTermLabel
    _ hf ?_ ?_
  · rintro (p | p) hp
    · exact hm (Nat.zero_le k) p.origin hp
    · exact hm (by have := p.1.2; omega) p.2.1.source hp
  · exact fun p q _ _ => actionTermLabel_injective p q
private def intBox (R : ℝ) : Finset (Fin 4 → ℤ) :=
  Fintype.piFinset fun _ => Finset.Icc (-((⌈R⌉₊ + 1 : ℕ) : ℤ)) ((⌈R⌉₊ + 1 : ℕ) : ℤ)
private lemma coe_offsetSite (y : Vertex L n k k) (m : Fin 4 → ℤ) (μ : Fin 4) :
    ((PeriodicLattice.offsetSite y m : Vertex L n k k) : PeriodicLattice.FourTorus L n) μ =
      (y : PeriodicLattice.FourTorus L n) μ +
        (((m μ : ℝ)) : AddCircle (PeriodicLattice.torusSide L n)) := by
  have hsp : PeriodicLattice.meshSize L 0 = 1 := by
    simp [PeriodicLattice.meshSize]
  simp only [PeriodicLattice.offsetSite]
  rw [AddSubgroup.coe_add, Pi.add_apply, AddSubgroup.val_finsetSum, Finset.sum_apply]
  congr 1
  rw [Finset.sum_eq_single μ]
  · have e : (((m μ : ℝ)) : AddCircle (PeriodicLattice.torusSide L n)) =
        (((m μ • (1 : ℝ) : ℝ)) : AddCircle (PeriodicLattice.torusSide L n)) := by simp
    rw [e]
    simp only [PeriodicLattice.unitStep, PeriodicLattice.pointOnAxis, PeriodicLattice.levelDepth,
      sub_self, hsp, AddSubgroup.coe_zsmul, Pi.smul_apply, Pi.single_eq_same]
    exact (QuotientAddGroup.mk_zsmul _ _ _).symm
  · intro ν _ hν
    simp [PeriodicLattice.unitStep, PeriodicLattice.pointOnAxis, Pi.single_eq_of_ne (Ne.symm hν)]
  · simp
abbrev _root_.YangMills.SharedProofs.p56430 := @coe_offsetSite
private lemma exists_offset_of_cellDist_le (hLat : PeriodicLattice.CoordinateDescription)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) (y y' : Vertex L n k k) {R : ℝ}
    (h : cellDist y' y ≤ R) :
    ∃ m ∈ intBox R, y' = PeriodicLattice.offsetSite y m := by
  have hj : -(n : ℤ) ≤ PeriodicLattice.levelDepth k k := by
    simp only [PeriodicLattice.levelDepth]
    omega
  obtain ⟨m₀, hm₀⟩ := ((hLat L n hL.1 hL.2 hn).1 _ hj).2.2.2.1 y y'
  have hL0 : 0 < L := by have := hL.2; omega
  have hlift : ∀ μ, ((y' : PeriodicLattice.FourTorus L n) - y) μ =
      (((m₀ μ : ℝ)) : AddCircle (PeriodicLattice.torusSide L n)) := by
    intro μ
    rw [hm₀, Pi.sub_apply, coe_offsetSite]
    abel
  have hne : (TorusMetric.euclidNormVec '' (TorusMetric.torusProj (PeriodicLattice.torusSide L n) ⁻¹'
      {(y' : PeriodicLattice.FourTorus L n) - y})).Nonempty := by
    refine ⟨_, fun μ => (m₀ μ : ℝ), ?_, rfl⟩
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    funext μ
    exact (hlift μ).symm
  have hlt : sInf (TorusMetric.euclidNormVec '' (TorusMetric.torusProj
      (PeriodicLattice.torusSide L n) ⁻¹' {(y' : PeriodicLattice.FourTorus L n) - y})) < R + 1 := by
    have : cellDist y' y < R + 1 := by linarith
    exact this
  obtain ⟨_, ⟨w, hw, rfl⟩, hwR⟩ := exists_lt_of_csInf_lt hne hlt
  have hw' : ∀ μ, ((w μ : ℝ) : AddCircle (PeriodicLattice.torusSide L n)) =
      (((m₀ μ : ℝ)) : AddCircle (PeriodicLattice.torusSide L n)) := by
    intro μ
    have := congrFun (Set.mem_singleton_iff.1 (Set.mem_preimage.1 hw)) μ
    rw [← hlift μ]
    exact this
  have hint : ∀ μ, ∃ m : ℤ, w μ = (m : ℝ) := by
    intro μ
    have e2 : (((w μ - m₀ μ : ℝ)) : AddCircle (PeriodicLattice.torusSide L n)) = 0 := by
      rw [AddCircle.coe_sub, hw', sub_self]
    obtain ⟨t, ht⟩ := (AddCircle.coe_eq_zero_iff _).1 e2
    refine ⟨m₀ μ + t * (2 * (L : ℤ) ^ n), ?_⟩
    simp only [PeriodicLattice.torusSide, zsmul_eq_mul] at ht
    push_cast
    linarith
  choose m hm using hint
  refine ⟨m, ?_, ?_⟩
  · simp only [intBox, Fintype.mem_piFinset, Finset.mem_Icc]
    intro μ
    have h1 : |w μ| ≤ TorusMetric.euclidNormVec w := by
      refine Real.abs_le_sqrt ?_
      exact Finset.single_le_sum (f := fun ν => w ν ^ 2) (fun _ _ => sq_nonneg _)
        (Finset.mem_univ μ)
    have h2 : |(m μ : ℝ)| < (⌈R⌉₊ + 1 : ℕ) := by
      rw [← hm μ]
      have h3 := Nat.le_ceil R
      push_cast
      linarith
    have h3 : |m μ| < ((⌈R⌉₊ + 1 : ℕ) : ℤ) := by exact_mod_cast h2
    have := abs_lt.1 h3
    omega
  · apply Subtype.ext
    funext μ
    rw [coe_offsetSite, ← hm μ, hw']
    have := hlift μ
    rw [Pi.sub_apply] at this
    rw [← this]
    abel
abbrev _root_.YangMills.DeltaSharedProofs.p502225 := @exists_offset_of_cellDist_le
open Classical in
private lemma card_cellDist_le (hLat : PeriodicLattice.CoordinateDescription)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) {ι : Type} [Fintype ι]
    (c : ι → Vertex L n k k) {D : ℕ}
    (hD : ∀ y, (Finset.univ.filter fun p => c p = y).card ≤ D) (y : Vertex L n k k) (R : ℝ) :
    (Finset.univ.filter fun p => cellDist (c p) y ≤ R).card ≤ D * (intBox R).card := by
  set s := Finset.univ.filter fun p => cellDist (c p) y ≤ R with hs
  have h1 : s.card ≤ D * (s.image c).card := by
    refine Finset.card_le_mul_card_image s D fun a _ => ?_
    exact (Finset.card_le_card fun p hp => by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
      exact hp.2).trans (hD a)
  have h2 : (s.image c).card ≤ (intBox R).card := by
    have : s.image c ⊆ (intBox R).image (PeriodicLattice.offsetSite y) := by
      intro y' hy'
      obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 hy'
      have hp' : cellDist (c p) y ≤ R := (Finset.mem_filter.1 hp).2
      obtain ⟨m, hm, e⟩ := exists_offset_of_cellDist_le hLat hL hn y (c p) hp'
      exact Finset.mem_image.2 ⟨m, hm, e.symm⟩
    exact (Finset.card_le_card this).trans Finset.card_image_le
  exact h1.trans (Nat.mul_le_mul_left _ h2)
abbrev _root_.YangMills.DeltaSharedProofs.p502568 := @card_cellDist_le
end Cells
private def traceL : ComplexMatrix2 →L[ℂ] ℂ :=
  (Matrix.traceLinearMap (Fin 2) ℂ ℂ).toContinuousLinearMap
private lemma traceL_apply (X : ComplexMatrix2) : traceL X = Matrix.trace X := rfl
private def pauliNormSum : ℝ := ∑ a, ‖ComplexMatrix2.pauliFamily a‖
private lemma pauliNormSum_nonneg : 0 ≤ pauliNormSum := Finset.sum_nonneg fun _ _ => norm_nonneg _
section Terms
variable {L n k : ℕ}
private lemma norm_bondMatrix_le [Fintype (LevelFormIndex L n k)] (f : LevelFormIndex L n k → ℂ)
    (p : LevelFormIndex L n k) : ‖bondMatrix f p‖ ≤ pauliNormSum * ‖f‖ := by
  unfold bondMatrix pauliNormSum
  refine (norm_sum_le _ _).trans ?_
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun a _ => ?_
  rw [norm_smul, mul_comm]
  exact mul_le_mul_of_nonneg_left (norm_le_pi_norm f _) (norm_nonneg _)
private lemma bondMatrix_analyticAt {F : Type} [NormedAddCommGroup F] [NormedSpace ℂ F]
    {φ : F → LevelFormIndex L n k → ℂ} {x : F} (hφ : ∀ q, AnalyticAt ℂ (fun y => φ y q) x)
    (p : LevelFormIndex L n k) : AnalyticAt ℂ (fun y => bondMatrix (φ y) p) x := by
  unfold bondMatrix
  have : AnalyticAt ℂ (∑ a : Fin 3, fun y => φ y (withColour a p) • ComplexMatrix2.pauliFamily a) x :=
    Finset.analyticAt_sum _ fun a _ => (hφ _).smul analyticAt_const
  convert this using 1
  funext y
  simp
variable [Fintype (LevelFormIndex L n k)] [Fintype (Fin 3 × PositiveEdge L n k k)]
private lemma formPart_analyticAt {z : TripleCoordIndex L n k → ℂ} (q : LevelFormIndex L n k) :
    AnalyticAt ℂ (fun z : TripleCoordIndex L n k → ℂ => formPart z q) z :=
  (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : TripleCoordIndex L n k => ℂ) (.inl q)).analyticAt z
private lemma norm_formPart_le (z : TripleCoordIndex L n k → ℂ) : ‖formPart z‖ ≤ ‖z‖ :=
  (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun q => norm_le_pi_norm z (.inl q)
private structure LevelFieldBounds (ρ C r : ℝ) : Prop where
  mem_fields : ∀ j ≤ k, ∀ z ∈ ball (0 : TripleCoordIndex L n k → ℂ) ρ,
    levelField (complexChainPoint z) j ∈ fieldsIn L n k j PeriodicLattice.complexGaugeGroup
  holo : ∀ j ≤ k, ∀ b : Edge L n k j,
    AnalyticOnNhd ℂ (fun z => levelField (complexChainPoint z) j b) (ball 0 ρ)
  close : ∀ j ≤ k, ∀ b : Edge L n k j, ∀ z ∈ ball (0 : TripleCoordIndex L n k → ℂ) ρ,
    ComplexMatrix2.operatorNorm (levelField (complexChainPoint z) j b - 1) ≤ C * ‖z‖
  local_dep : ∀ j ≤ k, ∀ b : Edge L n k j, ∀ z ∈ ball (0 : TripleCoordIndex L n k → ℂ) ρ,
    ∀ z' ∈ ball (0 : TripleCoordIndex L n k → ℂ) ρ,
    (∀ i, cellDist (tripleCoordIndexCell i) (levelVertexCell b.source) ≤ r → z i = z' i) →
      levelField (complexChainPoint z) j b = levelField (complexChainPoint z') j b
  radius_holo : ∀ (i : Fin k) (c : PositiveEdge L n k (i + 1)),
    AnalyticOnNhd ℂ (fun z => meanRadius (levelField (complexChainPoint z) i) c.1) (ball 0 ρ)
  radius_close : ∀ (i : Fin k) (c : PositiveEdge L n k (i + 1)),
    ∀ z ∈ ball (0 : TripleCoordIndex L n k → ℂ) ρ,
    ‖meanRadius (levelField (complexChainPoint z) i) c.1 - 1‖ ≤ C * ‖z‖
  radius_local : ∀ (i : Fin k) (c : PositiveEdge L n k (i + 1)),
    ∀ z ∈ ball (0 : TripleCoordIndex L n k → ℂ) ρ, ∀ z' ∈ ball (0 : TripleCoordIndex L n k → ℂ) ρ,
    (∀ i', cellDist (tripleCoordIndexCell i') (levelVertexCell c.1.source) ≤ r → z i' = z' i') →
      meanRadius (levelField (complexChainPoint z) i) c.1 =
        meanRadius (levelField (complexChainPoint z') i) c.1
end Terms
section TermValues
variable {L n k : ℕ}
private def faceBond (p : Face L n k 0) : Fin 4 → Edge L n k 0 :=
  ![PeriodicLattice.Bond.forwardFrom p.origin p.firstAxis,
    PeriodicLattice.Bond.forwardFrom (p.origin + PeriodicLattice.unitStep L n _ p.firstAxis) p.secondAxis,
    (PeriodicLattice.Bond.forwardFrom (p.origin + PeriodicLattice.unitStep L n _ p.secondAxis)
      p.firstAxis).opposite,
    (PeriodicLattice.Bond.forwardFrom p.origin p.secondAxis).opposite]
private def faceProduct (U : Edge L n k 0 → ComplexMatrix2) (p : Face L n k 0) : ComplexMatrix2 :=
  U (faceBond p 0) * U (faceBond p 1) * U (faceBond p 2) * U (faceBond p 3)
private def faceTerm (z : TripleCoordIndex L n k → ℂ) (p : Face L n k 0) : ℂ :=
  1 - (1 / 2) * traceL (faceProduct (levelField (complexChainPoint z) 0) p)
private lemma noise_eq_exp (z : TripleCoordIndex L n k → ℂ) (i : Fin k) (c : PositiveEdge L n k (i + 1)) :
    (complexChainPoint z).noise i c =
      ComplexMatrix2.matExp (Complex.I • bondMatrix (formPart z) (.inr ⟨i, (0, c)⟩)) := by
  simp only [complexChainPoint, unitPoint, mul_one, complexLevelValues_eq]
private def noiseWeightTerm (a : ℝ) (z : TripleCoordIndex L n k → ℂ)
    (c : Σ i : Fin k, PositiveEdge L n k (i + 1)) : ℂ :=
  (a : ℂ) * (meanRadius (levelField (complexChainPoint z) c.1) c.2.1 *
    (1 - (1 / 2) * traceL ((complexChainPoint z).noise c.1 c.2)))
private def termValue (a : ℝ) (z : TripleCoordIndex L n k → ℂ) : ActionTerm L n k → ℂ :=
  Sum.elim (faceTerm z) (noiseWeightTerm a z)
variable [Fintype (LevelFormIndex L n k)] [Fintype (Fin 3 × PositiveEdge L n k k)]
private lemma noise_analyticAt (i : Fin k) (c : PositiveEdge L n k (i + 1))
    (z : TripleCoordIndex L n k → ℂ) :
    AnalyticAt ℂ (fun z : TripleCoordIndex L n k → ℂ => (complexChainPoint z).noise i c) z := by
  simp only [noise_eq_exp]
  have h1 : AnalyticAt ℂ (fun z : TripleCoordIndex L n k → ℂ =>
      Complex.I • bondMatrix (formPart z) (.inr ⟨i, (0, c)⟩)) z :=
    analyticAt_const_smul' _ (bondMatrix_analyticAt formPart_analyticAt _)
  exact AnalyticAt.comp (g := NormedSpace.exp) (NormedSpace.exp_analytic _) h1
private lemma termValue_analyticOnNhd {ρ C r : ℝ}
    (hF : LevelFieldBounds (L := L) (n := n) (k := k) ρ C r) (a : ℝ)
    (α : ActionTerm L n k) : AnalyticOnNhd ℂ (fun z => termValue a z α) (ball 0 ρ) := by
  intro z hz
  rcases α with p | c
  · have hU : ∀ b : Edge L n k 0,
        AnalyticAt ℂ (fun z => levelField (complexChainPoint z) 0 b) z :=
      fun b => hF.holo 0 (Nat.zero_le k) b z hz
    have h1 : AnalyticAt ℂ (fun z : TripleCoordIndex L n k → ℂ =>
        faceProduct (levelField (complexChainPoint z) 0) p) z :=
      (((hU _).mul (hU _)).mul (hU _)).mul (hU _)
    have h2 : AnalyticAt ℂ (fun z : TripleCoordIndex L n k → ℂ =>
        traceL (faceProduct (levelField (complexChainPoint z) 0) p)) z :=
      AnalyticAt.comp (g := traceL) (traceL.analyticAt _) h1
    exact analyticAt_const.sub (analyticAt_const.mul h2)
  · have h1 : AnalyticAt ℂ (fun z : TripleCoordIndex L n k → ℂ =>
        traceL ((complexChainPoint z).noise c.1 c.2)) z :=
      AnalyticAt.comp (g := traceL) (traceL.analyticAt _) (noise_analyticAt c.1 c.2 z)
    have h2 := hF.radius_holo c.1 c.2 z hz
    exact analyticAt_const.mul (h2.mul (analyticAt_const.sub (analyticAt_const.mul h1)))
private def termValueBound (a ρ : ℝ) : ℝ :=
  1 + ‖traceL‖ * (1 + ‖(1 : ComplexMatrix2)‖) ^ 4 +
    |a| * ((1 + ‖(1 : ℂ)‖) * (1 + ‖traceL‖ * Real.exp (pauliNormSum * ρ)))
private lemma norm_termValue_le (hE : ComplexMatrix2.ExpLogEstimates) {ρ C r : ℝ}
    (hF : LevelFieldBounds (L := L) (n := n) (k := k) ρ C r) (hC : 0 ≤ C) (hρ : C * ρ ≤ 1) (a : ℝ)
    (α : ActionTerm L n k) {z : TripleCoordIndex L n k → ℂ} (hz : z ∈ ball 0 ρ) :
    ‖termValue a z α‖ ≤ termValueBound a ρ := by
  have hzn : ‖z‖ < ρ := by simpa using hz
  have hCz : C * ‖z‖ ≤ 1 := (mul_le_mul_of_nonneg_left hzn.le hC).trans hρ
  have hk := norm_nonneg traceL
  rcases α with p | c
  · have hU : ∀ b : Edge L n k 0,
        ‖levelField (complexChainPoint z) 0 b‖ ≤ 1 + ‖(1 : ComplexMatrix2)‖ := by
      intro b
      have h1 := hF.close 0 (Nat.zero_le k) b z hz
      have h2 : ‖levelField (complexChainPoint z) 0 b‖ ≤
          ‖levelField (complexChainPoint z) 0 b - 1‖ + ‖(1 : ComplexMatrix2)‖ := by
        simpa using norm_add_le (levelField (complexChainPoint z) 0 b - 1) 1
      have h3 : ‖levelField (complexChainPoint z) 0 b - 1‖ ≤ 1 := h1.trans hCz
      linarith
    have hP : ‖faceProduct (levelField (complexChainPoint z) 0) p‖ ≤
        (1 + ‖(1 : ComplexMatrix2)‖) ^ 4 := by
      unfold faceProduct
      calc _ ≤ ‖levelField (complexChainPoint z) 0 (faceBond p 0)‖ *
              ‖levelField (complexChainPoint z) 0 (faceBond p 1)‖ *
              ‖levelField (complexChainPoint z) 0 (faceBond p 2)‖ *
              ‖levelField (complexChainPoint z) 0 (faceBond p 3)‖ := by
            refine (norm_mul_le _ _).trans ?_
            refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
            refine (norm_mul_le _ _).trans ?_
            exact mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _)
        _ ≤ (1 + ‖(1 : ComplexMatrix2)‖) * (1 + ‖(1 : ComplexMatrix2)‖) *
              (1 + ‖(1 : ComplexMatrix2)‖) * (1 + ‖(1 : ComplexMatrix2)‖) := by
            gcongr <;> exact hU _
        _ = _ := by ring
    have h2 : ‖traceL (faceProduct (levelField (complexChainPoint z) 0) p)‖ ≤
        ‖traceL‖ * (1 + ‖(1 : ComplexMatrix2)‖) ^ 4 :=
      (traceL.le_opNorm _).trans (mul_le_mul_of_nonneg_left hP hk)
    have h3 : ‖faceTerm z p‖ ≤ 1 + ‖traceL‖ * (1 + ‖(1 : ComplexMatrix2)‖) ^ 4 := by
      unfold faceTerm
      refine (norm_sub_le _ _).trans ?_
      rw [norm_one, norm_mul]
      have : ‖(1 / 2 : ℂ)‖ ≤ 1 := by norm_num
      have h4 : ‖(1 / 2 : ℂ)‖ * ‖traceL (faceProduct (levelField (complexChainPoint z) 0) p)‖ ≤
          1 * ‖traceL‖ * (1 + ‖(1 : ComplexMatrix2)‖) ^ 4 := by
        rw [mul_assoc]
        exact mul_le_mul this h2 (norm_nonneg _) zero_le_one
      linarith
    have h5 : 0 ≤ |a| * ((1 + ‖(1 : ℂ)‖) * (1 + ‖traceL‖ * Real.exp (pauliNormSum * ρ))) := by
      positivity
    simp only [termValue, Sum.elim_inl, termValueBound]
    linarith
  · have hr : ‖meanRadius (levelField (complexChainPoint z) c.1) c.2.1‖ ≤ 1 + ‖(1 : ℂ)‖ := by
      have h1 := hF.radius_close c.1 c.2 z hz
      have h2 : ‖meanRadius (levelField (complexChainPoint z) c.1) c.2.1‖ ≤
          ‖meanRadius (levelField (complexChainPoint z) c.1) c.2.1 - 1‖ + ‖(1 : ℂ)‖ := by
        simpa using norm_add_le (meanRadius (levelField (complexChainPoint z) c.1) c.2.1 - 1) 1
      have h3 := h1.trans hCz
      linarith
    have hN : ‖(complexChainPoint z).noise c.1 c.2‖ ≤ Real.exp (pauliNormSum * ρ) := by
      rw [noise_eq_exp]
      refine (hE.1 _).1.trans (Real.exp_le_exp.2 ?_)
      have h1 := norm_bondMatrix_le (formPart z) (.inr ⟨c.1, (0, c.2)⟩)
      have h2 : ‖formPart z‖ ≤ ρ := (norm_formPart_le z).trans hzn.le
      rw [ComplexMatrix2.operatorNorm, norm_smul, Complex.norm_I, one_mul]
      exact h1.trans (mul_le_mul_of_nonneg_left h2 pauliNormSum_nonneg)
    have h2 : ‖traceL ((complexChainPoint z).noise c.1 c.2)‖ ≤
        ‖traceL‖ * Real.exp (pauliNormSum * ρ) :=
      (traceL.le_opNorm _).trans (mul_le_mul_of_nonneg_left hN hk)
    have h3 : ‖1 - (1 / 2) * traceL ((complexChainPoint z).noise c.1 c.2)‖ ≤
        1 + ‖traceL‖ * Real.exp (pauliNormSum * ρ) := by
      refine (norm_sub_le _ _).trans ?_
      rw [norm_one, norm_mul]
      have : ‖(1 / 2 : ℂ)‖ ≤ 1 := by norm_num
      have h4 := mul_le_mul this h2 (norm_nonneg _) zero_le_one
      linarith
    have h6 : ‖noiseWeightTerm a z c‖ ≤
        |a| * ((1 + ‖(1 : ℂ)‖) * (1 + ‖traceL‖ * Real.exp (pauliNormSum * ρ))) := by
      unfold noiseWeightTerm
      rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul hr h3 (norm_nonneg _) (by positivity)) (abs_nonneg _)
    have h7 : 0 ≤ ‖traceL‖ * (1 + ‖(1 : ComplexMatrix2)‖) ^ 4 := by positivity
    simp only [termValue, Sum.elim_inr, termValueBound]
    linarith
end TermValues
private lemma eventually_norm_lt_line {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {x : E}
    (u v : E) {δ : ℝ} (h : ‖x‖ < δ) :
    ∀ᶠ p : ℝ × ℝ in 𝓝 0, ‖x + (p.1 : ℂ) • u + (p.2 : ℂ) • v‖ < δ := by
  have hc : Continuous (fun p : ℝ × ℝ => ‖x + (p.1 : ℂ) • u + (p.2 : ℂ) • v‖) := by
    have h1 : Continuous (fun p : ℝ × ℝ => ((p.1 : ℝ) : ℂ)) :=
      Complex.continuous_ofReal.comp continuous_fst
    have h2 : Continuous (fun p : ℝ × ℝ => ((p.2 : ℝ) : ℂ)) :=
      Complex.continuous_ofReal.comp continuous_snd
    exact ((continuous_const.add (h1.smul continuous_const)).add
      (h2.smul continuous_const)).norm
  have := hc.tendsto 0
  simp only [Prod.fst_zero, Prod.snd_zero, Complex.ofReal_zero, zero_smul, add_zero] at this
  exact this.eventually (gt_mem_nhds h)
section Setup
variable {L n k : ℕ}
private abbrev PointForm (L n k : ℕ) : Type :=
  (TripleCoordIndex L n k → ℂ) × (LevelFormIndex L n k → ℂ)
private lemma movedCoords_congr {z z' : TripleCoordIndex L n k → ℂ} {ε ε' : LevelFormIndex L n k → ℂ}
    (i : TripleCoordIndex L n k)
    (hz : ∀ i', tripleCoordIndexCell i' = tripleCoordIndexCell i → z i' = z' i')
    (hε : ∀ q, levelFormIndexCell q = tripleCoordIndexCell i → ε q = ε' q) :
    movedCoords z ε i = movedCoords z' ε' i := by
  rcases i with p | r
  · have h1 : bondMatrix ε p = bondMatrix ε' p := by
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [hε _ (cell_withColour a p)]
    have h2 : bondMatrix (formPart z) p = bondMatrix (formPart z') p := by
      refine Finset.sum_congr rfl fun a _ => ?_
      have := hz (.inl (withColour a p)) (cell_withColour a p)
      simp only [formPart, this]
    simp only [movedCoords, Sum.elim_inl, h1, h2]
  · exact hz (.inr r) rfl
variable [Fintype (LevelFormIndex L n k)] [Fintype (Fin 3 × PositiveEdge L n k k)]
private structure Setup (L n k : ℕ) [Fintype (LevelFormIndex L n k)]
    [Fintype (Fin 3 × PositiveEdge L n k k)] (δ ρ C r : ℝ) : Prop where
  logSeries : PeriodicLattice.LogSeriesNearOne
  expLog : ComplexMatrix2.ExpLogEstimates
  dist_symm : ∀ y y' : Vertex L n k k, cellDist y y' = cellDist y' y
  dist_triangle : ∀ y y' y'' : Vertex L n k k,
    cellDist y y'' ≤ cellDist y y' + cellDist y' y''
  dist_refl : ∀ y : Vertex L n k k, cellDist y y = 0
  adjacent_le : ∀ (x : Vertex L n k 0) (μ : Fin 4), cellDist (levelVertexCell x)
    (levelVertexCell (x + PeriodicLattice.unitStep L n _ μ)) ≤ 4
  fields : LevelFieldBounds (L := L) (n := n) (k := k) ρ C r
  moved_small : ∀ (z : TripleCoordIndex L n k → ℂ) (ε : LevelFormIndex L n k → ℂ), ‖z‖ < δ → ‖ε‖ < δ →
    (∀ p, ‖expProd (bondMatrix ε p) (bondMatrix (formPart z) p) - 1‖ < 9 / 10) ∧
      ‖movedCoords z ε‖ < ρ
  C_nonneg : 0 ≤ C
  Cρ_le : C * ρ ≤ 1
  r_nonneg : 0 ≤ r
  δ_pos : 0 < δ
variable {δ ρ C r : ℝ}
private lemma faceBond_source_near (R : Setup L n k δ ρ C r) (p : Face L n k 0) (i : Fin 4) :
    cellDist (levelVertexCell (faceBond p i).source) (levelVertexCell p.origin) ≤ 8 := by
  have h1 := R.adjacent_le p.origin p.firstAxis
  have h2 := R.adjacent_le p.origin p.secondAxis
  have h3 := R.adjacent_le (p.origin + PeriodicLattice.unitStep L n _ p.secondAxis) p.firstAxis
  have s1 := R.dist_symm (levelVertexCell p.origin)
    (levelVertexCell (p.origin + PeriodicLattice.unitStep L n _ p.firstAxis))
  have s2 := R.dist_symm (levelVertexCell p.origin)
    (levelVertexCell (p.origin + PeriodicLattice.unitStep L n _ p.secondAxis))
  have s3 := R.dist_symm (levelVertexCell (p.origin + PeriodicLattice.unitStep L n _ p.secondAxis))
    (levelVertexCell (p.origin + PeriodicLattice.unitStep L n _ p.secondAxis +
      PeriodicLattice.unitStep L n _ p.firstAxis))
  have t := R.dist_triangle
    (levelVertexCell (p.origin + PeriodicLattice.unitStep L n _ p.secondAxis +
      PeriodicLattice.unitStep L n _ p.firstAxis))
    (levelVertexCell (p.origin + PeriodicLattice.unitStep L n _ p.secondAxis)) (levelVertexCell p.origin)
  fin_cases i
  · change cellDist (levelVertexCell p.origin) (levelVertexCell p.origin) ≤ 8
    rw [R.dist_refl]
    norm_num
  · change cellDist (levelVertexCell (p.origin + PeriodicLattice.unitStep L n _ p.firstAxis))
      (levelVertexCell p.origin) ≤ 8
    linarith
  · change cellDist (levelVertexCell (p.origin + PeriodicLattice.unitStep L n _ p.secondAxis +
      PeriodicLattice.unitStep L n _ p.firstAxis)) (levelVertexCell p.origin) ≤ 8
    linarith
  · change cellDist (levelVertexCell (p.origin + PeriodicLattice.unitStep L n _ p.secondAxis))
      (levelVertexCell p.origin) ≤ 8
    linarith
private lemma termValue_congr (R : Setup L n k δ ρ C r) (a : ℝ) (α : ActionTerm L n k)
    {z z' : TripleCoordIndex L n k → ℂ} (hz : z ∈ ball 0 ρ) (hz' : z' ∈ ball 0 ρ)
    (h : ∀ i, cellDist (tripleCoordIndexCell i) (actionTermCell α) ≤ r + 8 → z i = z' i) :
    termValue a z α = termValue a z' α := by
  rcases α with p | c
  · have hU : ∀ i : Fin 4, levelField (complexChainPoint z) 0 (faceBond p i) =
        levelField (complexChainPoint z') 0 (faceBond p i) := by
      intro i
      refine R.fields.local_dep 0 (Nat.zero_le k) _ z hz z' hz' fun i' hi' => h i' ?_
      have t := R.dist_triangle (tripleCoordIndexCell i')
        (levelVertexCell (faceBond p i).source) (levelVertexCell p.origin)
      have := faceBond_source_near R p i
      change cellDist (tripleCoordIndexCell i') (levelVertexCell p.origin) ≤ r + 8
      linarith
    simp only [termValue, Sum.elim_inl, faceTerm, faceProduct, hU]
  · have h1 := R.fields.radius_local c.1 c.2 z hz z' hz' fun i' hi' => h i' (by
      have hr := R.r_nonneg
      change cellDist (tripleCoordIndexCell i') (levelVertexCell c.2.1.source) ≤ r + 8
      linarith)
    have h2 : bondMatrix (formPart z) (.inr ⟨c.1, (0, c.2)⟩) =
        bondMatrix (formPart z') (.inr ⟨c.1, (0, c.2)⟩) := by
      refine Finset.sum_congr rfl fun b _ => ?_
      have := h (.inl (withColour b (.inr ⟨c.1, (0, c.2)⟩))) (by
        have hr := R.r_nonneg
        have h0 := R.dist_refl (levelVertexCell c.2.1.source)
        change cellDist (levelVertexCell c.2.1.source) (levelVertexCell c.2.1.source) ≤ r + 8
        linarith)
      simp only [formPart, this]
    simp only [termValue, Sum.elim_inr, noiseWeightTerm, h1, noise_eq_exp, h2]
private lemma movedCoords_analyticAt (hS : PeriodicLattice.LogSeriesNearOne)
    (x : PointForm L n k)
    (h : ∀ p, ‖expProd (bondMatrix x.2 p) (bondMatrix (formPart x.1) p) - 1‖ < 1) :
    AnalyticAt ℂ (fun y : PointForm L n k => movedCoords y.1 y.2) x := by
  refine AnalyticAt.pi ?_
  rintro (p | s)
  · have h1 : AnalyticAt ℂ (fun y : PointForm L n k => bondMatrix y.2 p) x := by
      refine bondMatrix_analyticAt (φ := fun y : PointForm L n k => y.2) (fun q => ?_) p
      exact AnalyticAt.comp (g := ContinuousLinearMap.proj (R := ℂ)
        (φ := fun _ : LevelFormIndex L n k => ℂ) q) (ContinuousLinearMap.analyticAt _ _)
        analyticAt_snd
    have h2 : AnalyticAt ℂ (fun y : PointForm L n k => bondMatrix (formPart y.1) p) x := by
      refine bondMatrix_analyticAt (φ := fun y : PointForm L n k => formPart y.1) (fun q => ?_) p
      exact AnalyticAt.comp (g := fun z : TripleCoordIndex L n k → ℂ => formPart z q)
        (formPart_analyticAt q) analyticAt_fst
    have hq : AnalyticAt ℂ (fun y : PointForm L n k =>
        (bondMatrix y.2 p, bondMatrix (formPart y.1) p)) x := h1.prod h2
    have hj : AnalyticAt ℂ (fun q : ComplexMatrix2 × ComplexMatrix2 => expLogJoin q.1 q.2)
        (bondMatrix x.2 p, bondMatrix (formPart x.1) p) := expLogJoin_analyticAt hS (h p)
    have h3 : AnalyticAt ℂ (fun y : PointForm L n k =>
        expLogJoin (bondMatrix y.2 p) (bondMatrix (formPart y.1) p)) x :=
      AnalyticAt.comp (g := fun q : ComplexMatrix2 × ComplexMatrix2 => expLogJoin q.1 q.2)
        (f := fun y : PointForm L n k => (bondMatrix y.2 p, bondMatrix (formPart y.1) p)) hj hq
    have h4 : AnalyticAt ℂ (pauliCoordCLM (colourIndex p)) (expLogJoin (bondMatrix x.2 p)
        (bondMatrix (formPart x.1) p)) := ContinuousLinearMap.analyticAt _ _
    exact AnalyticAt.comp (g := pauliCoordCLM (colourIndex p))
      (f := fun y : PointForm L n k => expLogJoin (bondMatrix y.2 p) (bondMatrix (formPart y.1) p))
      h4 h3
  · exact AnalyticAt.comp (g := ContinuousLinearMap.proj (R := ℂ)
      (φ := fun _ : TripleCoordIndex L n k => ℂ) (.inr s)) (ContinuousLinearMap.analyticAt _ _)
      analyticAt_fst
private def movedTerm (a : ℝ) (α : ActionTerm L n k) (x : PointForm L n k) : ℂ :=
  termValue a (movedCoords x.1 x.2) α
private lemma norm_lt_of_pair {x : PointForm L n k} (h : ‖x‖ < δ) :
    ‖x.1‖ < δ ∧ ‖x.2‖ < δ := by
  rw [Prod.norm_def] at h
  exact max_lt_iff.1 h
private lemma movedTerm_analyticOnNhd (R : Setup L n k δ ρ C r) (a : ℝ) (α : ActionTerm L n k) :
    AnalyticOnNhd ℂ (movedTerm a α) (ball 0 δ) := by
  intro x hx
  have hn := norm_lt_of_pair (mem_ball_zero_iff.1 hx)
  obtain ⟨h1, h2⟩ := R.moved_small x.1 x.2 hn.1 hn.2
  have h3 := movedCoords_analyticAt R.logSeries x fun p => (h1 p).trans (by norm_num)
  exact AnalyticAt.comp (g := fun z => termValue a z α)
    (termValue_analyticOnNhd R.fields a α _ (mem_ball_zero_iff.2 h2)) h3
private lemma norm_movedTerm_le (R : Setup L n k δ ρ C r) (a : ℝ) (α : ActionTerm L n k)
    {x : PointForm L n k} (hx : x ∈ ball 0 δ) :
    ‖movedTerm a α x‖ ≤ termValueBound a ρ := by
  have hn := norm_lt_of_pair (mem_ball_zero_iff.1 hx)
  exact norm_termValue_le R.expLog R.fields R.C_nonneg R.Cρ_le a α
    (mem_ball_zero_iff.2 (R.moved_small x.1 x.2 hn.1 hn.2).2)
private lemma movedTerm_congr (R : Setup L n k δ ρ C r) (a : ℝ) (α : ActionTerm L n k)
    {x x' : PointForm L n k} (hx : ‖x‖ < δ) (hx' : ‖x'‖ < δ)
    (h1 : ∀ i, cellDist (tripleCoordIndexCell i) (actionTermCell α) ≤ r + 8 → x.1 i = x'.1 i)
    (h2 : ∀ q, cellDist (levelFormIndexCell q) (actionTermCell α) ≤ r + 8 → x.2 q = x'.2 q) :
    movedTerm a α x = movedTerm a α x' := by
  have hn := norm_lt_of_pair hx
  have hn' := norm_lt_of_pair hx'
  refine termValue_congr R a α (mem_ball_zero_iff.2 (R.moved_small _ _ hn.1 hn.2).2)
    (mem_ball_zero_iff.2 (R.moved_small _ _ hn'.1 hn'.2).2) fun i hi => ?_
  refine movedCoords_congr i (fun i' e => h1 i' ?_) fun q e => h2 q ?_
  · rwa [e]
  · rwa [e]
variable [DecidableEq (LevelFormIndex L n k)]
private def coordDir (p : LevelFormIndex L n k) : PointForm L n k :=
  (0, Pi.single p 1)
private lemma norm_coordDir_le (p : LevelFormIndex L n k) : ‖coordDir p‖ ≤ 1 := by
  rw [coordDir, Prod.norm_def]
  refine max_le (by simp) ((pi_norm_le_iff_of_nonneg zero_le_one).2 fun q => ?_)
  by_cases h : q = p
  · subst h
    simp
  · simp [Pi.single_eq_of_ne h]
abbrev _root_.YangMills.DeltaSharedProofs.p501125 := @norm_coordDir_le
private lemma movedTerm_eq_of_far (R : Setup L n k δ ρ C r) (a : ℝ) (α : ActionTerm L n k)
    {p : LevelFormIndex L n k}
    (hp : r + 8 < cellDist (levelFormIndexCell p) (actionTermCell α))
    {y y' : PointForm L n k} (hy : ‖y‖ < δ)
    (hy' : ‖y'‖ < δ) (h1 : y.1 = y'.1) (h2 : ∀ q, q ≠ p → y.2 q = y'.2 q) :
    movedTerm a α y = movedTerm a α y' := by
  refine movedTerm_congr R a α hy hy' (fun i _ => congrFun h1 i) fun q hq => h2 q ?_
  rintro rfl
  exact absurd hq (not_le.2 hp)
private lemma secondDeriv_far_left (R : Setup L n k δ ρ C r) (a : ℝ) (α : ActionTerm L n k)
    {p : LevelFormIndex L n k}
    (hp : r + 8 < cellDist (levelFormIndexCell p) (actionTermCell α))
    {x v : PointForm L n k} (hx : ‖x‖ < δ) (hv : v.1 = 0) :
    secondDeriv (movedTerm a α) x (coordDir p) v = 0 := by
  have hb : x ∈ ball (0 : PointForm L n k) δ :=
    mem_ball_zero_iff.2 hx
  rw [← secondDeriv_zero_left (movedTerm a α) x v]
  refine secondDeriv_congr (movedTerm_analyticOnNhd R a α x hb) (movedTerm_analyticOnNhd R a α x hb) ?_
  filter_upwards [eventually_norm_lt_line (coordDir p) v hx, eventually_norm_lt_line 0 v hx] with s h1 h2
  refine movedTerm_eq_of_far R a α hp h1 h2 ?_ fun q hq => ?_
  · simp [coordDir, hv]
  · simp [coordDir, Pi.single_eq_of_ne hq]
private lemma secondDeriv_far_right (R : Setup L n k δ ρ C r) (a : ℝ) (α : ActionTerm L n k)
    {q : LevelFormIndex L n k}
    (hq : r + 8 < cellDist (levelFormIndexCell q) (actionTermCell α))
    {x u : PointForm L n k} (hx : ‖x‖ < δ) (hu : u.1 = 0) :
    secondDeriv (movedTerm a α) x u (coordDir q) = 0 := by
  have hb : x ∈ ball (0 : PointForm L n k) δ :=
    mem_ball_zero_iff.2 hx
  rw [← secondDeriv_zero_right (movedTerm a α) x u]
  refine secondDeriv_congr (movedTerm_analyticOnNhd R a α x hb) (movedTerm_analyticOnNhd R a α x hb) ?_
  filter_upwards [eventually_norm_lt_line u (coordDir q) hx, eventually_norm_lt_line u 0 hx] with s h1 h2
  refine movedTerm_eq_of_far R a α hq h1 h2 ?_ fun q' hq' => ?_
  · simp [coordDir, hu]
  · simp [coordDir, Pi.single_eq_of_ne hq']
private lemma norm_secondDeriv_movedTerm_le (R : Setup L n k δ ρ C r) (a : ℝ) (α : ActionTerm L n k)
    {x : PointForm L n k} (hx : ‖x‖ < δ / 2)
    (p q : LevelFormIndex L n k) :
    ‖secondDeriv (movedTerm a α) x (coordDir p) (coordDir q)‖ ≤
      16 * termValueBound a ρ / (δ / 2) ^ 2 := by
  have hsub : ball x (δ / 2) ⊆ ball (0 : PointForm L n k) δ := by
    refine ball_subset_ball' ?_
    rw [dist_zero_right]
    linarith
  have hδ := R.δ_pos
  exact norm_secondDeriv_le (by positivity) (fun y hy => movedTerm_analyticOnNhd R a α y (hsub hy))
    (fun y hy => norm_movedTerm_le R a α (hsub hy)) (norm_coordDir_le p) (norm_coordDir_le q)
end Setup
section SecondOfSums
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
private lemma secondDeriv_sum {κ : Type} [Fintype κ] {g : κ → E → ℂ} {x : E}
    (hg : ∀ α, AnalyticAt ℂ (g α) x) (u v : E) :
    secondDeriv (fun y => ∑ α, g α y) x u v = ∑ α, secondDeriv (g α) x u v := by
  have h1 : ∀ᶠ y in 𝓝 x, ∀ α, AnalyticAt ℂ (g α) y :=
    eventually_all.2 fun α => (hg α).eventually_analyticAt
  have h2 : fderiv ℂ (fun y => ∑ α, g α y) =ᶠ[𝓝 x] fun y => ∑ α, fderiv ℂ (g α) y := by
    filter_upwards [h1] with y hy
    exact fderiv_fun_sum fun α _ => (hy α).differentiableAt
  unfold secondDeriv
  rw [h2.fderiv_eq, fderiv_fun_sum fun α _ => (hg α).fderiv.differentiableAt]
  simp
private lemma secondDeriv_sum_smul {ι : Type} [Fintype ι] (g : E → ℂ) (x : E) (c : ι → ℂ) (d : ι → E) :
    secondDeriv g x (∑ p, c p • d p) (∑ q, c q • d q) =
      ∑ p, ∑ q, c p * (c q * secondDeriv g x (d p) (d q)) := by
  unfold secondDeriv
  simp only [map_sum, map_smul, sum_apply, smul_apply,
    smul_eq_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
  ring
end SecondOfSums
section Counting
variable {ι κ : Type} [Fintype ι] [Fintype κ]
open Classical in
private lemma sum_near_pairs_le (N : ι → κ → Prop) {B : ℝ} (hB : 0 ≤ B) {A Q : ℕ}
    (hA : ∀ p, (Finset.univ.filter (N p)).card ≤ A)
    (hQ : ∀ α, (Finset.univ.filter fun q => N q α).card ≤ Q) (p : ι) :
    ∑ q, ∑ α, (if N p α ∧ N q α then B else 0) ≤ B * Q * A := by
  rw [Finset.sum_comm]
  have h1 : ∀ α, ∑ q, (if N p α ∧ N q α then B else 0) ≤ if N p α then B * Q else 0 := by
    intro α
    by_cases h : N p α
    · simp only [h, true_and, if_true]
      rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_comm]
      exact mul_le_mul_of_nonneg_left (by exact_mod_cast hQ α) hB
    · simp [h]
  refine (Finset.sum_le_sum fun α _ => h1 α).trans ?_
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_comm]
  exact mul_le_mul_of_nonneg_left (by exact_mod_cast hA p) (by positivity)
end Counting
section HessianKernel
variable {L n k : ℕ} [Fintype (LevelFormIndex L n k)] [Fintype (Fin 3 × PositiveEdge L n k k)]
  [DecidableEq (LevelFormIndex L n k)] [Fintype (ActionTerm L n k)] {δ ρ C r : ℝ}
private def hessKernel (a : ℝ) (z : TripleCoordIndex L n k → ℂ) :
    Matrix (LevelFormIndex L n k) (LevelFormIndex L n k) ℂ :=
  fun p q => ∑ α : ActionTerm L n k, secondDeriv (movedTerm a α) (z, 0) (coordDir p) (coordDir q)
omit [DecidableEq (LevelFormIndex L n k)] [Fintype (ActionTerm L n k)] in
private lemma norm_pointForm (z : TripleCoordIndex L n k → ℂ) : ‖((z, 0) : PointForm L n k)‖ = ‖z‖ := by
  rw [Prod.norm_def]
  simp
private lemma hessKernel_analyticOnNhd (R : Setup L n k δ ρ C r) (a : ℝ) (p q : LevelFormIndex L n k) :
    AnalyticOnNhd ℂ (fun z => hessKernel a z p q) (ball 0 (δ / 2)) := by
  intro z hz
  have hδ := R.δ_pos
  have hz' : ((z, 0) : PointForm L n k) ∈ ball (0 : PointForm L n k) δ := by
    rw [mem_ball_zero_iff, norm_pointForm]
    have : ‖z‖ < δ / 2 := by simpa using hz
    linarith
  have hp : AnalyticAt ℂ (fun z : TripleCoordIndex L n k → ℂ => ((z, 0) : PointForm L n k)) z :=
    analyticAt_id.prod analyticAt_const
  have h1 : ∀ α : ActionTerm L n k, AnalyticAt ℂ
      (fun z : TripleCoordIndex L n k → ℂ =>
        secondDeriv (movedTerm a α) (z, 0) (coordDir p) (coordDir q)) z := by
    intro α
    exact AnalyticAt.comp (g := fun x => secondDeriv (movedTerm a α) x (coordDir p) (coordDir q))
      (f := fun z : TripleCoordIndex L n k → ℂ => ((z, 0) : PointForm L n k))
      (secondDeriv_analyticOnNhd (movedTerm_analyticOnNhd R a α) _ _ _ hz') hp
  have : AnalyticAt ℂ (∑ α : ActionTerm L n k, fun z : TripleCoordIndex L n k → ℂ =>
      secondDeriv (movedTerm a α) (z, 0) (coordDir p) (coordDir q)) z :=
    Finset.analyticAt_sum _ fun α _ => h1 α
  convert this using 1
  funext y
  simp [hessKernel]
private lemma secondDeriv_movedTerm_eq_zero_of_far (R : Setup L n k δ ρ C r) (a : ℝ)
    (z : TripleCoordIndex L n k → ℂ) (hz : ‖z‖ < δ)
    (α : ActionTerm L n k) (p q : LevelFormIndex L n k)
    (h : ¬ (cellDist (levelFormIndexCell p) (actionTermCell α) ≤ r + 8 ∧
      cellDist (levelFormIndexCell q) (actionTermCell α) ≤ r + 8)) :
    secondDeriv (movedTerm a α) (z, 0) (coordDir p) (coordDir q) = 0 := by
  have hx : ‖((z, 0) : PointForm L n k)‖ < δ := by rwa [norm_pointForm]
  by_cases hp : cellDist (levelFormIndexCell p) (actionTermCell α) ≤ r + 8
  · have hq : r + 8 < cellDist (levelFormIndexCell q) (actionTermCell α) :=
      not_le.1 fun hq => h ⟨hp, hq⟩
    exact secondDeriv_far_right R a α hq hx rfl
  · exact secondDeriv_far_left R a α (not_le.1 hp) hx rfl
open Classical in
private lemma norm_hessKernel_le (R : Setup L n k δ ρ C r) (a : ℝ) {z : TripleCoordIndex L n k → ℂ}
    (hz : ‖z‖ < δ / 2) (p q : LevelFormIndex L n k) :
    ‖hessKernel a z p q‖ ≤ ∑ α : ActionTerm L n k,
      if cellDist (levelFormIndexCell p) (actionTermCell α) ≤ r + 8 ∧
        cellDist (levelFormIndexCell q) (actionTermCell α) ≤ r + 8
      then 16 * termValueBound a ρ / (δ / 2) ^ 2 else 0 := by
  have hδ := R.δ_pos
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun α _ => ?_)
  split_ifs with h
  · exact norm_secondDeriv_movedTerm_le R a α (by rwa [norm_pointForm]) p q
  · rw [secondDeriv_movedTerm_eq_zero_of_far R a z (by linarith) α p q h, norm_zero]
open Classical in
private lemma hessKernel_isLocallyHolomorphic (R : Setup L n k δ ρ C r) (a : ℝ) {A Q : ℕ}
    (hA : ∀ p : LevelFormIndex L n k, (Finset.univ.filter fun α : ActionTerm L n k =>
      cellDist (levelFormIndexCell p) (actionTermCell α) ≤ r + 8).card ≤ A)
    (hQ : ∀ α : ActionTerm L n k, (Finset.univ.filter fun q : LevelFormIndex L n k =>
      cellDist (levelFormIndexCell q) (actionTermCell α) ≤ r + 8).card ≤ Q) :
    IsLocallyHolomorphicFamily tripleCoordIndexCell levelFormIndexCell levelFormIndexCell
      (hessKernel (L := L) (n := n) (k := k) a) (δ / 2)
      (16 * termValueBound a ρ / (δ / 2) ^ 2 * Q * A) (2 * (r + 8)) := by
  have hδ := R.δ_pos
  have hM : 0 ≤ termValueBound a ρ := by
    have h0 : 0 ≤ ‖traceL‖ := norm_nonneg _
    have h1 := norm_nonneg (1 : ComplexMatrix2)
    unfold termValueBound
    positivity
  have hB : 0 ≤ 16 * termValueBound a ρ / (δ / 2) ^ 2 := by positivity
  refine ⟨fun p q => hessKernel_analyticOnNhd R a p q, fun z hz => ?_, ?_, ?_⟩
  · have hz' : ‖z‖ < δ / 2 := by simpa using hz
    refine opNorm_le_of_row_col_sums _ (by positivity) (fun p => ?_) fun q => ?_
    · refine (Finset.sum_le_sum fun q _ => norm_hessKernel_le R a hz' p q).trans ?_
      exact sum_near_pairs_le (fun (p : LevelFormIndex L n k) (α : ActionTerm L n k) =>
        cellDist (levelFormIndexCell p) (actionTermCell α) ≤ r + 8) hB hA hQ p
    · refine (Finset.sum_le_sum fun p _ => norm_hessKernel_le R a hz' p q).trans ?_
      have := sum_near_pairs_le (fun (p : LevelFormIndex L n k) (α : ActionTerm L n k) =>
        cellDist (levelFormIndexCell p) (actionTermCell α) ≤ r + 8) hB hA hQ q
      refine le_trans (le_of_eq ?_) this
      refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun α _ => ?_
      simp only [and_comm]
  · intro p q z hz z' hz' h
    have hn : ‖z‖ < δ / 2 := by simpa using hz
    have hn' : ‖z'‖ < δ / 2 := by simpa using hz'
    have hx : ‖((z, 0) : PointForm L n k)‖ < δ := by rw [norm_pointForm]; linarith
    have hx' : ‖((z', 0) : PointForm L n k)‖ < δ := by rw [norm_pointForm]; linarith
    refine Finset.sum_congr rfl fun α _ => ?_
    by_cases hα : cellDist (levelFormIndexCell p) (actionTermCell α) ≤ r + 8
    · refine secondDeriv_congr (movedTerm_analyticOnNhd R a α _ (mem_ball_zero_iff.2 hx))
        (movedTerm_analyticOnNhd R a α _ (mem_ball_zero_iff.2 hx')) ?_
      filter_upwards [eventually_norm_lt_line (coordDir p) (coordDir q) hx,
        eventually_norm_lt_line (coordDir p) (coordDir q) hx'] with s h1 h2
      refine movedTerm_congr R a α h1 h2 (fun i hi => ?_) fun w _ => ?_
      · have t := R.dist_triangle (tripleCoordIndexCell i) (actionTermCell α) (levelFormIndexCell p)
        have c := R.dist_symm (actionTermCell α) (levelFormIndexCell p)
        have := h i (by linarith)
        simpa [coordDir] using this
      · simp [coordDir]
    · have e1 := secondDeriv_far_left R a α (not_le.1 hα) hx (v := coordDir q) rfl
      have e2 := secondDeriv_far_left R a α (not_le.1 hα) hx' (v := coordDir q) rfl
      rw [e1, e2]
  · intro z hz p q h
    have hn : ‖z‖ < δ / 2 := by simpa using hz
    refine Finset.sum_eq_zero fun α _ => secondDeriv_movedTerm_eq_zero_of_far R a z (by linarith) α p q ?_
    rintro ⟨h1, h2⟩
    have t := R.dist_triangle (levelFormIndexCell p) (actionTermCell α) (levelFormIndexCell q)
    have c := R.dist_symm (actionTermCell α) (levelFormIndexCell q)
    linarith
end HessianKernel
private lemma trace_eq_ofReal_re {g : ComplexMatrix2} (hg : g ∈ PeriodicLattice.compactGaugeGroup) :
    Matrix.trace g = (((Matrix.trace g).re : ℝ) : ℂ) := by
  obtain ⟨hu, hd⟩ := Matrix.mem_specialUnitaryGroup_iff.1 hg
  have h1 : g * star g = 1 := Matrix.mem_unitaryGroup_iff.1 hu
  have h2 : Matrix.adjugate g = star g := by
    calc Matrix.adjugate g = Matrix.adjugate g * (g * star g) := by rw [h1, mul_one]
      _ = star g := by rw [← mul_assoc, Matrix.adjugate_mul, hd, one_smul, one_mul]
  have h3 : g 1 1 = star (g 0 0) := by
    have := congrFun (congrFun h2 0) 0
    simpa [Matrix.adjugate_fin_two] using this
  rw [Matrix.trace_fin_two, h3]
  apply Complex.ext <;> simp
private lemma inv_mem_compactGaugeGroup {g : ComplexMatrix2} (hg : g ∈ PeriodicLattice.compactGaugeGroup) :
    g⁻¹ ∈ PeriodicLattice.compactGaugeGroup := by apply _root_.YangMills.Construction.PeriodicLattice.BlockAverageContinuity.inv_mem_compactGaugeGroup <;> assumption
section CompactValues
variable {L n k : ℕ}
private def CompactValued (X : ChainPoint L n k) : Prop :=
  (∀ b, X.fine b ∈ PeriodicLattice.compactGaugeGroup) ∧
    ∀ i c, X.noise i c ∈ PeriodicLattice.compactGaugeGroup
private lemma unitPoint_compactValued : CompactValued (unitPoint L n k) :=
  ⟨fun _ => ComplexMatrix2.specialUnitary.one_mem, fun _ _ => ComplexMatrix2.specialUnitary.one_mem⟩
private lemma expMove_compactValued
    (hc : ∀ Y ∈ ComplexMatrix2.hermitianTraceless,
      ComplexMatrix2.matExp (Complex.I • Y) ∈ ComplexMatrix2.specialUnitary)
    (η : LevelForms L n k) {X : ChainPoint L n k} (hX : CompactValued X) :
    CompactValued (expMove η X) := by
  refine ⟨fun b => ?_, fun i c => ?_⟩
  · simp only [expMove, PeriodicLattice.expTwist]
    split_ifs with hb
    · exact ComplexMatrix2.specialUnitary.mul_mem (hc _ (η.1.2.1 b hb)) (hX.1 b)
    · exact inv_mem_compactGaugeGroup (ComplexMatrix2.specialUnitary.mul_mem
        (hc _ (η.1.2.1 _ (opposite_isPositive b hb))) (hX.1 _))
  · exact ComplexMatrix2.specialUnitary.mul_mem (hc _ ((η.2 i).2.1 c.1 c.2)) (hX.2 i c)
variable [Fintype (LevelFormIndex L n k)] [Fintype (Fin 3 × PositiveEdge L n k k)] {δ ρ C r ρR : ℝ}
private lemma levelField_mem_fieldSpace (R : Setup L n k δ ρ C r)
    (hP : ∀ j : ℕ, j < k → ∀ V ∈ fieldSpace L n k j,
      (∀ b, ComplexMatrix2.operatorNorm (V b - 1) < ρR) →
      ∀ c : Edge L n k (j + 1), c.IsPositivelyOriented →
        meanRadius V c = (((meanRadius V c).re : ℝ) : ℂ) ∧ 0 < (meanRadius V c).re ∧
          normalizedMean V c ∈ PeriodicLattice.compactGaugeGroup)
    (hCR : C * ρ < ρR) {y : TripleCoordIndex L n k → ℂ} (hy : ‖y‖ < ρ)
    (hX : CompactValued (complexChainPoint y)) :
    ∀ j, j ≤ k → levelField (complexChainPoint y) j ∈ fieldSpace L n k j := by
  have hy' : y ∈ ball (0 : TripleCoordIndex L n k → ℂ) ρ := mem_ball_zero_iff.2 hy
  have hnear : ∀ j, j ≤ k → ∀ b : Edge L n k j,
      ComplexMatrix2.operatorNorm (levelField (complexChainPoint y) j b - 1) < ρR := fun j hj b =>
    (R.fields.close j hj b y hy').trans_lt
      ((mul_le_mul_of_nonneg_left hy.le R.C_nonneg).trans_lt hCR)
  intro j
  induction j with
  | zero =>
    intro _
    exact ⟨fun b _ => hX.1 b, (R.fields.mem_fields 0 (Nat.zero_le k) y hy').2⟩
  | succ j ih =>
    intro hj
    have hjk : j < k := hj
    have hV := ih hjk.le
    refine ⟨fun b _ => ?_, (R.fields.mem_fields (j + 1) hj y hy').2⟩
    have hw : ∀ c : PositiveEdge L n k (j + 1),
        (complexChainPoint y).noise ⟨j, hjk⟩ c * normalizedMean (levelField (complexChainPoint y) j) c.1 ∈
          PeriodicLattice.compactGaugeGroup := by
      intro c
      have h1 : normalizedMean (levelField (complexChainPoint y) j) c.1 ∈
          PeriodicLattice.compactGaugeGroup :=
        (hP j hjk (levelField (complexChainPoint y) j) hV (hnear j hjk.le) c.1 c.2).2.2
      have h2 : (complexChainPoint y).noise ⟨j, hjk⟩ c ∈ PeriodicLattice.compactGaugeGroup :=
        hX.2 ⟨j, hjk⟩ c
      exact ComplexMatrix2.specialUnitary.mul_mem h2 h1
    simp only [levelField, dif_pos hjk, fieldOfPositiveValues]
    split_ifs with h1 h2
    · exact hw ⟨b, h1⟩
    · exact inv_mem_compactGaugeGroup (hw ⟨b.opposite, h2⟩)
    · exact ComplexMatrix2.specialUnitary.one_mem
private lemma plaquetteHolonomy_eq_faceProduct (U : Edge L n k 0 → ComplexMatrix2) (p : Face L n k 0) :
    PeriodicLattice.plaquetteHolonomy U p = faceProduct U p := by
  simp only [PeriodicLattice.plaquetteHolonomy, PeriodicLattice.pathHolonomy,
    PeriodicLattice.Plaquette.boundaryBonds, List.map_cons, List.map_nil, List.prod_cons,
    List.prod_nil, mul_one, faceProduct, mul_assoc]
  rfl
private lemma faceTerm_ofReal {y : TripleCoordIndex L n k → ℂ}
    (hX : CompactValued (complexChainPoint y)) (p : Face L n k 0) :
    ((PeriodicLattice.plaquetteCost (levelField (complexChainPoint y) 0) p : ℝ) : ℂ) =
      faceTerm y p := by
  have hm : faceProduct (levelField (complexChainPoint y) 0) p ∈ PeriodicLattice.compactGaugeGroup :=
    ComplexMatrix2.specialUnitary.mul_mem (ComplexMatrix2.specialUnitary.mul_mem
      (ComplexMatrix2.specialUnitary.mul_mem (hX.1 _) (hX.1 _)) (hX.1 _)) (hX.1 _)
  rw [PeriodicLattice.plaquetteCost, plaquetteHolonomy_eq_faceProduct, faceTerm, traceL_apply]
  have ht := trace_eq_ofReal_re hm
  push_cast
  rw [ComplexMatrix2.fullTrace, ← ht]
private lemma noiseTerm_ofReal (R : Setup L n k δ ρ C r)
    (hP : ∀ j : ℕ, j < k → ∀ V ∈ fieldSpace L n k j,
      (∀ b, ComplexMatrix2.operatorNorm (V b - 1) < ρR) →
      ∀ c : Edge L n k (j + 1), c.IsPositivelyOriented →
        meanRadius V c = (((meanRadius V c).re : ℝ) : ℂ) ∧ 0 < (meanRadius V c).re ∧
          normalizedMean V c ∈ PeriodicLattice.compactGaugeGroup)
    (hCR : C * ρ < ρR) {y : TripleCoordIndex L n k → ℂ} (hy : ‖y‖ < ρ)
    (hX : CompactValued (complexChainPoint y)) (a : ℝ) (c : Σ i : Fin k, PositiveEdge L n k (i + 1)) :
    (((a * ((meanRadius (levelField (complexChainPoint y) c.1) c.2.1).re *
      traceDefect ((complexChainPoint y).noise c.1 c.2)) : ℝ)) : ℂ) = noiseWeightTerm a y c := by
  have hy' : y ∈ ball (0 : TripleCoordIndex L n k → ℂ) ρ := mem_ball_zero_iff.2 hy
  have hj : (c.1 : ℕ) < k := c.1.2
  have hV := levelField_mem_fieldSpace R hP hCR hy hX c.1 hj.le
  have hnear : ∀ b : Edge L n k c.1,
      ComplexMatrix2.operatorNorm (levelField (complexChainPoint y) c.1 b - 1) < ρR :=
    fun b => (R.fields.close c.1 hj.le b y hy').trans_lt
      ((mul_le_mul_of_nonneg_left hy.le R.C_nonneg).trans_lt hCR)
  have hr := (hP c.1 hj _ hV hnear c.2.1 c.2.2).1
  have ht := trace_eq_ofReal_re (hX.2 c.1 c.2)
  have he : ((traceDefect ((complexChainPoint y).noise c.1 c.2) : ℝ) : ℂ) =
      1 - (1 / 2) * traceL ((complexChainPoint y).noise c.1 c.2) := by
    rw [traceDefect, traceL_apply]
    have e : (ComplexMatrix2.halfTrace ((complexChainPoint y).noise c.1 c.2)).re =
        (1 / 2) * (Matrix.trace ((complexChainPoint y).noise c.1 c.2)).re := by
      simp [ComplexMatrix2.halfTrace, ComplexMatrix2.fullTrace]
    rw [e]
    push_cast
    rw [← ht]
  rw [noiseWeightTerm, ← he]
  push_cast
  rw [← hr]
private lemma chainAction_ofReal_eq_sum [Fintype (Face L n k 0)]
    [∀ i : Fin k, Fintype (PositiveEdge L n k (i + 1))]
    (R : Setup L n k δ ρ C r)
    (hP : ∀ j : ℕ, j < k → ∀ V ∈ fieldSpace L n k j,
      (∀ b, ComplexMatrix2.operatorNorm (V b - 1) < ρR) →
      ∀ c : Edge L n k (j + 1), c.IsPositivelyOriented →
        meanRadius V c = (((meanRadius V c).re : ℝ) : ℂ) ∧ 0 < (meanRadius V c).re ∧
          normalizedMean V c ∈ PeriodicLattice.compactGaugeGroup)
    (hCR : C * ρ < ρR) {y : TripleCoordIndex L n k → ℂ} (hy : ‖y‖ < ρ)
    (hX : CompactValued (complexChainPoint y)) (a : ℝ) :
    ((chainAction a (complexChainPoint y) : ℝ) : ℂ) = ∑ α : ActionTerm L n k, termValue a y α := by
  rw [Fintype.sum_sum_type, Fintype.sum_sigma]
  simp only [chainAction, Tower.plaquetteAction, PeriodicLattice.wilsonAction,
    finsum_eq_sum_of_fintype, termValue, Sum.elim_inl, Sum.elim_inr, Complex.ofReal_add,
    Complex.ofReal_sum]
  congr 1
  · exact Finset.sum_congr rfl fun p _ => faceTerm_ofReal hX p
  · rw [Complex.ofReal_mul, Complex.ofReal_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Complex.ofReal_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    have := noiseTerm_ofReal R hP hCR hy hX a ⟨i, c⟩
    rw [Complex.ofReal_mul] at this
    exact this
end CompactValues
section FormCoordinates
variable {L n k : ℕ} [Fintype (LevelFormIndex L n k)] [Fintype (Fin 3 × PositiveEdge L n k k)]
  [Fintype (GhostCoordIndex L n k)] [Fintype (Fin 3 × Vertex L n k 0)] [Fintype (Fin 3 × Vertex L n k k)]
private lemma traceless_of_hermitianTraceless {X : ComplexMatrix2}
    (h : X ∈ ComplexMatrix2.hermitianTraceless) : X ∈ ComplexMatrix2.traceless := h.2
private lemma formCoords_base_eq (P : PauliCoordinates L n k) (η : LevelForms L n k)
    (b : PositiveEdge L n k 0) :
    (η.1 : Edge L n k 0 → ComplexMatrix2) b.1 =
      bondMatrix (complexifyCoords (P.formCoords η)) (.inl (0, b)) := by
  have hm := traceless_of_hermitianTraceless (η.1.2.1 b.1 b.2)
  conv_lhs => rw [← sum_pauliCoord_smul hm]
  refine Finset.sum_congr rfl fun a _ => ?_
  have h := P.formCoords_base η (a, b)
  rw [← pauliCoeff_eq_pauliCoord hm]
  exact congrArg (· • ComplexMatrix2.pauliFamily a) h
private lemma formCoords_level_eq (P : PauliCoordinates L n k) (η : LevelForms L n k) (i : Fin k)
    (c : PositiveEdge L n k (i + 1)) :
    (η.2 i : Edge L n k (i + 1) → ComplexMatrix2) c.1 =
      bondMatrix (complexifyCoords (P.formCoords η)) (.inr ⟨i, (0, c)⟩) := by
  have hm := traceless_of_hermitianTraceless ((η.2 i).2.1 c.1 c.2)
  conv_lhs => rw [← sum_pauliCoord_smul hm]
  refine Finset.sum_congr rfl fun a _ => ?_
  have h := P.formCoords_level η i (a, c)
  rw [← pauliCoeff_eq_pauliCoord hm]
  exact congrArg (· • ComplexMatrix2.pauliFamily a) h
end FormCoordinates
private lemma exists_movedCoords_small (hS : PeriodicLattice.LogSeriesNearOne) {ρ : ℝ} (hρ : 0 < ρ) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ ρ ∧ ∀ {L n k : ℕ} [Fintype (LevelFormIndex L n k)]
      [Fintype (Fin 3 × PositiveEdge L n k k)] (z : TripleCoordIndex L n k → ℂ)
      (ε : LevelFormIndex L n k → ℂ), ‖z‖ < δ → ‖ε‖ < δ →
      (∀ p, ‖expProd (bondMatrix ε p) (bondMatrix (formPart z) p) - 1‖ < 9 / 10) ∧
        ‖movedCoords z ε‖ < ρ := by
  obtain ⟨δ₁, hδ₁, h⟩ := exists_expLogJoin_small hS hρ
  have hP := pauliNormSum_nonneg
  have hP1 : 0 < pauliNormSum + 1 := by linarith
  refine ⟨min ρ (δ₁ / (pauliNormSum + 1)), lt_min hρ (by positivity), min_le_left _ _, ?_⟩
  intro L n k _ _ z ε hz hε
  have hm : ∀ (f : LevelFormIndex L n k → ℂ) (p : LevelFormIndex L n k),
      ‖f‖ < min ρ (δ₁ / (pauliNormSum + 1)) → ‖bondMatrix f p‖ < δ₁ := by
    intro f p hf
    have h1 := lt_of_lt_of_le hf (min_le_right _ _)
    have h2 : pauliNormSum * ‖f‖ ≤ pauliNormSum * (δ₁ / (pauliNormSum + 1)) :=
      mul_le_mul_of_nonneg_left h1.le hP
    have h3 : pauliNormSum * (δ₁ / (pauliNormSum + 1)) < δ₁ := by
      rw [mul_div_assoc', div_lt_iff₀ hP1]
      nlinarith
    exact ((norm_bondMatrix_le f p).trans h2).trans_lt h3
  have hz' : ‖formPart z‖ < min ρ (δ₁ / (pauliNormSum + 1)) := (norm_formPart_le z).trans_lt hz
  refine ⟨fun p => (h _ _ (hm ε p hε) (hm _ p hz')).1, ?_⟩
  refine (pi_norm_lt_iff hρ).2 ?_
  rintro (p | s)
  · exact (h _ _ (hm ε p hε) (hm _ p hz')).2 _
  · exact (norm_le_pi_norm z (.inr s)).trans_lt (lt_of_lt_of_le hz (min_le_left _ _))
theorem chainActionHessianIsLocal_holds
    (hFields : LevelFieldsHolomorphicAndLocal)
    (hE : ComplexMatrix2.ExpLogEstimates)
    (hM : PeriodicLattice.ElementaryStepFacts)
    (hConj : ComplexMatrix2.ConjugationExpProductBounds)
    (hCell : NeighbouringFineVertexCells)
    (hTop : TopEdgesAndCubes)
    (hLat : PeriodicLattice.CoordinateDescription)
    (hReal : NormalizedMeanOfCompactField) :
    ChainActionHessianIsLocal := by
  intro a _ L hL k hk
  obtain ⟨ρ₀, C₀, r₀, hρ₀, hC₀, hr₀, hev⟩ := hFields L hL k hk
  obtain ⟨ρR, hρR, hP⟩ := hReal L hL
  have hS : PeriodicLattice.LogSeriesNearOne :=
    (hM L 1 1 0 hL one_pos one_pos).2.2.1
  have hc : ∀ Y ∈ ComplexMatrix2.hermitianTraceless,
      ComplexMatrix2.matExp (Complex.I • Y) ∈ ComplexMatrix2.specialUnitary := hConj.2.2.1
  have hC1 : 0 < C₀ + 1 := by linarith
  obtain ⟨ρ, hρdef⟩ : ∃ ρ : ℝ, ρ = min ρ₀ (min (1 / (C₀ + 1)) (ρR / (C₀ + 1))) := ⟨_, rfl⟩
  have hρ : 0 < ρ := by
    rw [hρdef]
    exact lt_min hρ₀ (lt_min (by positivity) (by positivity))
  have hρ₁ : ρ ≤ ρ₀ := by rw [hρdef]; exact min_le_left _ _
  have hρ₂ : ρ ≤ 1 / (C₀ + 1) := by
    rw [hρdef]; exact (min_le_right _ _).trans (min_le_left _ _)
  have hρ₃ : ρ ≤ ρR / (C₀ + 1) := by
    rw [hρdef]; exact (min_le_right _ _).trans (min_le_right _ _)
  have hρ1 : C₀ * ρ ≤ 1 := by
    have h1 : (C₀ + 1) * ρ ≤ 1 := by
      rw [le_div_iff₀ hC1] at hρ₂
      linarith
    nlinarith
  have hCR : C₀ * ρ < ρR := by
    have h1 : (C₀ + 1) * ρ ≤ ρR := by
      rw [le_div_iff₀ hC1] at hρ₃
      linarith
    nlinarith
  obtain ⟨δ, hδ, hδρ, hsm⟩ := exists_movedCoords_small hS hρ
  have hM0 : 0 ≤ termValueBound a ρ := by
    have h0 : 0 ≤ ‖traceL‖ := norm_nonneg _
    have h1 := norm_nonneg (1 : ComplexMatrix2)
    unfold termValueBound
    positivity
  refine ⟨δ / 2, 16 * termValueBound a ρ / (δ / 2) ^ 2 *
      (((Fintype.card (FormLabel k) * L ^ (4 * k)) * (intBox (r₀ + 8)).card : ℕ) : ℝ) *
      (((Fintype.card (ActionTermLabel k) * L ^ (4 * k)) * (intBox (r₀ + 8)).card : ℕ) : ℝ),
    2 * (r₀ + 8), by positivity, by positivity, by positivity, ?_⟩
  filter_upwards [hev, eventually_gt_atTop 0] with n hn hn0
  intro _ _ _ _ _ _ _ _ _ P
  obtain ⟨hfirst, hconf, hfields, hlen⟩ := hn P
  have h0 : Finite (Vertex L n k 0) := Finite.of_injective
    (fun x : Vertex L n k 0 => ((0 : Fin 3), x)) fun x y h => (Prod.mk.inj h).2
  have h1 : Finite (Face L n k 0) := Finite.of_injective
    (fun p : Face L n k 0 => (p.origin, p.firstAxis, p.secondAxis)) fun p q h => by
      simp only [Prod.mk.injEq] at h
      exact PeriodicLattice.Plaquette.ext h.1 h.2.1 h.2.2
  letI : Fintype (Face L n k 0) := Fintype.ofFinite _
  have h2 : ∀ i : Fin k, Finite (PositiveEdge L n k (i + 1)) := fun i => Finite.of_injective
    (fun c : PositiveEdge L n k (i + 1) => (.inr ⟨i, (0, c)⟩ : LevelFormIndex L n k))
    fun c c' h => by simpa using h
  letI : ∀ i : Fin k, Fintype (PositiveEdge L n k (i + 1)) := fun i => Fintype.ofFinite _
  have hsub : ball (0 : TripleCoordIndex L n k → ℂ) ρ ⊆ ball 0 ρ₀ := ball_subset_ball hρ₁
  have facts : LevelFieldBounds (L := L) (n := n) (k := k) ρ C₀ r₀ :=
    { mem_fields := fun j hj z hz => hconf j hj z (hsub hz)
      holo := fun j hj b => (hfields j hj b).1.mono hsub
      close := fun j hj b z hz => (hfields j hj b).2.1 z (hsub hz)
      local_dep := fun j hj b z hz z' hz' h => (hfields j hj b).2.2 z (hsub hz) z' (hsub hz') h
      radius_holo := fun i c => (hlen i c).1.mono hsub
      radius_close := fun i c z hz => (hlen i c).2.1 z (hsub hz)
      radius_local := fun i c z hz z' hz' h => (hlen i c).2.2 z (hsub hz) z' (hsub hz') h }
  have R : Setup L n k δ ρ C₀ r₀ :=
    { logSeries := hS
      expLog := hE
      dist_symm := (hCell L hL n k).1
      dist_triangle := (hCell L hL n k).2.1
      dist_refl := (hTop L hL n k hn0 hk).1
      adjacent_le := fun x μ => by
        rw [levelVertexCell_zero, levelVertexCell_zero]
        exact (hCell L hL n k).2.2.2 x μ
      fields := facts
      moved_small := fun z ε hz hε => hsm z ε hz hε
      C_nonneg := hC₀
      Cρ_le := hρ1
      r_nonneg := hr₀
      δ_pos := hδ }
  have hPj : ∀ j : ℕ, j < k → ∀ V ∈ fieldSpace L n k j,
      (∀ b, ComplexMatrix2.operatorNorm (V b - 1) < ρR) → ∀ c : Edge L n k (j + 1),
        c.IsPositivelyOriented →
        meanRadius V c = (((meanRadius V c).re : ℝ) : ℂ) ∧ 0 < (meanRadius V c).re ∧
          normalizedMean V c ∈ PeriodicLattice.compactGaugeGroup :=
    fun j hj V hV hb c hc' => hP n k j hn0 hj V hV hb c hc'
  refine ⟨hessKernel a, hessKernel_isLocallyHolomorphic R a (fun p => ?_) (fun α => ?_), ?_⟩
  · have h3 := card_cellDist_le hLat hL hn0 (actionTermCell (L := L) (n := n) (k := k))
      (card_actionTerm_cell hLat hCell hL hn0) (levelFormIndexCell p) (r₀ + 8)
    refine le_trans (Finset.card_le_card fun α hα => ?_) h3
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hα ⊢
    rwa [R.dist_symm]
  · exact card_cellDist_le hLat hL hn0 (levelFormIndexCell (L := L) (n := n) (k := k))
      (card_form_cell hLat hCell hL hn0) (actionTermCell α) (r₀ + 8)
  · filter_upwards [Metric.ball_mem_nhds (0 : TripleCoordIndex L n k → ℝ) (half_pos hδ)] with x hx ξ
    obtain ⟨cx, hcx⟩ : ∃ cx, cx = complexifyCoords x := ⟨_, rfl⟩
    obtain ⟨cv, hcv⟩ : ∃ cv, cv = complexifyCoords (P.formCoords ξ) := ⟨_, rfl⟩
    have hxn : ‖x‖ < δ / 2 := by simpa using hx
    have hcxn : ‖cx‖ < δ / 2 := by
      refine lt_of_le_of_lt ?_ hxn
      rw [hcx]
      refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun i => ?_
      simpa [complexifyCoords] using norm_le_pi_norm x i
    have hx0 : ‖((cx, 0) : PointForm L n k)‖ < δ := by
      rw [norm_pointForm]
      linarith
    have han : AnalyticAt ℂ (fun y : PointForm L n k => ∑ α : ActionTerm L n k, movedTerm a α y)
        (cx, 0) := by
      have : AnalyticAt ℂ (∑ α : ActionTerm L n k, movedTerm a α) (cx, 0) :=
        Finset.analyticAt_sum _ fun α _ => movedTerm_analyticOnNhd R a α _ (mem_ball_zero_iff.2 hx0)
      convert this using 1
      funext y
      simp
    have hb := ofReal_deriv_deriv_eq_secondDeriv
      (g := fun y : PointForm L n k => ∑ α : ActionTerm L n k, movedTerm a α y)
      (x := (cx, 0)) (u := ((0, cv) : PointForm L n k)) (v := ((0, cv) : PointForm L n k)) han
      (f := fun s t => chainAction a (expMove (s • ξ + t • ξ) (pointOfCoords P x))) (by
        filter_upwards [eventually_norm_lt_line ((0, cv) : PointForm L n k)
          ((0, cv) : PointForm L n k) hx0] with s hs
        obtain ⟨η, hη⟩ : ∃ η, η = s.1 • ξ + s.2 • ξ := ⟨_, rfl⟩
        have hcoord : complexifyCoords (P.formCoords η) = (s.1 : ℂ) • cv + (s.2 : ℂ) • cv := by
          funext i
          simp [hη, hcv, complexifyCoords, map_add, map_smul]
        have hpt : ((cx, 0) : PointForm L n k) + (s.1 : ℂ) • ((0, cv) : PointForm L n k) +
            (s.2 : ℂ) • ((0, cv) : PointForm L n k) = (cx, complexifyCoords (P.formCoords η)) := by
          rw [hcoord]
          refine Prod.ext ?_ ?_ <;> simp
        rw [hpt] at hs
        rw [hpt, ← hη]
        have hn2 := norm_lt_of_pair hs
        obtain ⟨h3, h4⟩ := R.moved_small _ _ hn2.1 hn2.2
        have hmv := expMove_complexChainPoint hS hE η (formCoords_base_eq P η)
          (formCoords_level_eq P η) h3
        have hXr : CompactValued (complexChainPoint (movedCoords cx
            (complexifyCoords (P.formCoords η)))) := by
          rw [← hmv, hcx, hfirst x]
          exact expMove_compactValued hc η (expMove_compactValued hc _ unitPoint_compactValued)
        rw [← hfirst x, ← hcx, hmv]
        exact chainAction_ofReal_eq_sum R hPj hCR h4 hXr a)
    have hdir : ((0, cv) : PointForm L n k) = ∑ p, cv p • coordDir p := by
      refine Prod.ext ?_ ?_
      · simp [Prod.fst_sum, coordDir]
      · funext q
        simp [Prod.snd_sum, coordDir, Finset.sum_apply, Pi.single_apply]
    have hfin : secondDeriv (fun y : PointForm L n k => ∑ α : ActionTerm L n k, movedTerm a α y)
        (cx, 0) (0, cv) (0, cv) = cv ⬝ᵥ (hessKernel a cx).mulVec cv := by
      rw [secondDeriv_sum fun α => movedTerm_analyticOnNhd R a α _ (mem_ball_zero_iff.2 hx0), hdir]
      simp only [secondDeriv_sum_smul]
      simp only [dotProduct, Matrix.mulVec, hessKernel, Finset.sum_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun p _ => ?_
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun q _ => Finset.sum_congr rfl fun α _ => ?_
      ring
    rw [← hcx, ← hcv, ← hfin, ← hb]
    rfl
end YangMills.Construction.RunningCouplingSlope.HessianLocality
end
