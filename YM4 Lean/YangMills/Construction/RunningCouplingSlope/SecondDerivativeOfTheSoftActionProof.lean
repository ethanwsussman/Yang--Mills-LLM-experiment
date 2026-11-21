import YangMills.Construction.ColdChainAtEveryLevel.TotalUnderATurnedTopProof
import YangMills.Construction.Lattice.PeriodicLattices
import YangMills.Construction.RunningCouplingSlope.GradientAndMultiplierAtALeastPointProof
import YangMills.Construction.RunningCouplingSlope.PlainAverageIsAnalytic
import YangMills.Construction.RunningCouplingSlope.PlainIteratesNearOne
import YangMills.Construction.RunningCouplingSlope.PlainStepOnTheForms
import YangMills.Construction.RunningCouplingSlope.SecondDerivativeOfTheSoftAction
import Mathlib
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
open Filter
open scoped Topology Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction.RunningCouplingSlope
namespace ChainActionHessian
open Matrices
private theorem secondDeriv_add {f g : ℝ → ℝ} (hf : AnalyticAt ℝ f 0) (hg : AnalyticAt ℝ g 0) :
    deriv (deriv fun u => f u + g u) 0 = deriv (deriv f) 0 + deriv (deriv g) 0 := by apply _root_.YangMills.SharedProofs.p79864 <;> assumption
private theorem secondDeriv_const_mul (c : ℝ) (f : ℝ → ℝ) :
    deriv (deriv fun u => c * f u) 0 = c * deriv (deriv f) 0 := by
  have hcf : deriv (fun u => c * f u) = fun u => c * deriv f u := by
    funext u
    exact deriv_const_mul_field c
  rw [hcf]
  exact deriv_const_mul_field c
private theorem secondDeriv_sum {ι : Type*} (s : Finset ι) (f : ι → ℝ → ℝ)
    (h : ∀ i ∈ s, AnalyticAt ℝ (f i) 0) :
    deriv (deriv fun u => ∑ i ∈ s, f i u) 0 = ∑ i ∈ s, deriv (deriv (f i)) 0 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    have hs : AnalyticAt ℝ (fun u => ∑ i ∈ s, f i u) 0 :=
      Finset.analyticAt_fun_sum _ fun i hi => h i (Finset.mem_insert_of_mem hi)
    simp only [Finset.sum_insert ha]
    rw [secondDeriv_add (h a (Finset.mem_insert_self a s)) hs,
      ih fun i hi => h i (Finset.mem_insert_of_mem hi)]
private theorem secondDeriv_mul_of_vanishing {r e : ℝ → ℝ} (hr : AnalyticAt ℝ r 0)
    (he : AnalyticAt ℝ e 0) (h0 : e 0 = 0) (h1 : deriv e 0 = 0) :
    deriv (deriv fun u => r u * e u) 0 = r 0 * deriv (deriv e) 0 := by
  have hre : deriv (fun u => r u * e u) =ᶠ[𝓝 0] fun u => deriv r u * e u + r u * deriv e u := by
    filter_upwards [hr.eventually_analyticAt, he.eventually_analyticAt] with u hru heu
    exact deriv_fun_mul hru.differentiableAt heu.differentiableAt
  rw [hre.deriv_eq]
  have d1 := hr.deriv.differentiableAt.hasDerivAt
  have d2 := he.differentiableAt.hasDerivAt
  have d3 := hr.differentiableAt.hasDerivAt
  have d4 := he.deriv.differentiableAt.hasDerivAt
  have hsum : HasDerivAt (fun u => deriv r u * e u + r u * deriv e u)
      (deriv (deriv r) 0 * e 0 + deriv r 0 * deriv e 0 +
        (deriv r 0 * deriv e 0 + r 0 * deriv (deriv e) 0)) 0 := (d1.mul d2).add (d3.mul d4)
  rw [hsum.deriv, h0, h1]
  ring
private theorem deriv_comp_add_left_zero (g : ℝ → ℝ) (s : ℝ) :
    deriv (fun t => g (s + t)) 0 = deriv g s :=
  (deriv_comp_const_add g s 0).trans (by simp)
private theorem matExp_eq (Z : ComplexMatrix2) : ComplexMatrix2.matExp Z = NormedSpace.exp Z := rfl
private theorem analyticAt_expLine (X : ComplexMatrix2) :
    AnalyticAt ℝ (fun u : ℝ => ComplexMatrix2.matExp (Complex.I • (u • X))) 0 := by
  have h1 : AnalyticAt ℝ (fun u : ℝ => u • (Complex.I • X)) 0 :=
    analyticAt_id.smul analyticAt_const
  have h2 := AnalyticAt.comp_of_eq (NormedSpace.exp_analytic (𝕂 := ℝ) (0 : ComplexMatrix2)) h1
    (by simp)
  have hfun : (fun u : ℝ => ComplexMatrix2.matExp (Complex.I • (u • X))) =
      NormedSpace.exp ∘ fun u : ℝ => u • (Complex.I • X) := by
    funext u
    simp only [Function.comp, matExp_eq]
    rw [smul_comm]
  rw [hfun]
  exact h2
private theorem analyticAt_inv_of_det {f : ℝ → ComplexMatrix2} (hf : AnalyticAt ℝ f 0)
    (hu : IsUnit (Matrix.det (f 0))) : AnalyticAt ℝ (fun y => (f y)⁻¹) 0 := by
  have hfun : (fun y => (f y)⁻¹) = Ring.inverse ∘ f := by
    funext y
    simp [Matrix.nonsing_inv_eq_ringInverse]
  have hunit : IsUnit (f 0) := (Matrix.isUnit_iff_isUnit_det _).2 hu
  obtain ⟨w, hw⟩ := hunit
  rw [hfun]
  exact AnalyticAt.comp (by rw [← hw]; exact analyticAt_inverse (𝕜 := ℝ) w) hf
private theorem expLine_zero (X : ComplexMatrix2) :
    ComplexMatrix2.matExp (Complex.I • ((0 : ℝ) • X)) = 1 := by apply _root_.YangMills.SharedProofs.p11429 <;> assumption
variable {L n k : ℕ}
private abbrev chainLine (U : Tower.Edge L n k 0 → ComplexMatrix2) (ξ : LevelForms L n k) (u : ℝ) :
    ChainPoint L n k :=
  expMove (u • ξ) (quietPoint U)
private theorem chainLine_zero {U : Tower.Edge L n k 0 → ComplexMatrix2}
    (hU : ∀ b, (U b.opposite)⁻¹ = U b) (ξ : LevelForms L n k) :
    chainLine U ξ 0 = quietPoint U := by
  classical
  have hb : (chainLine U ξ 0).fine = U := by
    funext b
    by_cases h : b.IsPositivelyOriented
    · change PeriodicLattice.expTwist _ U b = _
      simp only [PeriodicLattice.expTwist, if_pos h]
      have hz : Complex.I • (((0 : ℝ) • ξ).1 : Tower.Edge L n k 0 → ComplexMatrix2) b = 0 := by
        simp
      rw [hz]
      simp [ComplexMatrix2.matExp, NormedSpace.exp_zero]
    · change PeriodicLattice.expTwist _ U b = _
      simp only [PeriodicLattice.expTwist, if_neg h]
      have hz : Complex.I • (((0 : ℝ) • ξ).1 : Tower.Edge L n k 0 → ComplexMatrix2) b.opposite = 0 := by
        simp
      rw [hz]
      simp only [ComplexMatrix2.matExp, NormedSpace.exp_zero, one_mul]
      exact hU b
  have hn : (chainLine U ξ 0).noise = fun _ _ => 1 := by
    funext i c
    change ComplexMatrix2.matExp
      (Complex.I • (((0 : ℝ) • ξ).2 i : Tower.Edge L n k (i + 1) → ComplexMatrix2) c) * 1 = 1
    have hz : Complex.I • (((0 : ℝ) • ξ).2 i : Tower.Edge L n k (i + 1) → ComplexMatrix2) c = 0 := by
      simp
    rw [hz]
    simp [ComplexMatrix2.matExp, NormedSpace.exp_zero]
  change ChainPoint.mk (chainLine U ξ 0).fine (chainLine U ξ 0).noise = ChainPoint.mk U fun _ _ => 1
  rw [hb, hn]
private theorem analyticAt_chainLine_fine {U : Tower.Edge L n k 0 → ComplexMatrix2}
    (ξ : LevelForms L n k) (hdet : ∀ b, Matrix.det (U b) = 1) (b : Tower.Edge L n k 0) :
    AnalyticAt ℝ (fun u => (chainLine U ξ u).fine b) 0 := by
  classical
  by_cases h : b.IsPositivelyOriented
  · have hfun : (fun u => (chainLine U ξ u).fine b) =
        fun u : ℝ => ComplexMatrix2.matExp
          (Complex.I • (u • (ξ.1 : Tower.Edge L n k 0 → ComplexMatrix2) b)) * U b := by
      funext u
      change PeriodicLattice.expTwist _ U b = _
      simp only [PeriodicLattice.expTwist, if_pos h]
      rfl
    rw [hfun]
    exact (analyticAt_expLine _).mul analyticAt_const
  · have hfun : (fun u => (chainLine U ξ u).fine b) =
        fun u : ℝ => (ComplexMatrix2.matExp
          (Complex.I • (u • (ξ.1 : Tower.Edge L n k 0 → ComplexMatrix2) b.opposite)) *
          U b.opposite)⁻¹ := by
      funext u
      change PeriodicLattice.expTwist _ U b = _
      simp only [PeriodicLattice.expTwist, if_neg h]
      rfl
    rw [hfun]
    refine analyticAt_inv_of_det ((analyticAt_expLine _).mul analyticAt_const) ?_
    simp only [expLine_zero, one_mul, hdet]
    exact isUnit_one
private theorem analyticAt_levelField [∀ i, Fintype (Tower.Edge L n k i)]
    {U : Tower.Edge L n k 0 → ComplexMatrix2}
    (ξ : LevelForms L n k) (hdet : ∀ b, Matrix.det (U b) = 1)
    (hU : ∀ b, (U b.opposite)⁻¹ = U b)
    (hX : ∀ i, i ≤ k → ∀ b : Tower.Edge L n k i,
      Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented)
    (hΦ : ∀ i, i < k → ∀ c : Tower.Edge L n k (i + 1), c.IsPositivelyOriented →
      AnalyticAt ℂ (fun V' : Tower.Edge L n k i → ComplexMatrix2 => normalizedMean V' c)
        (meanIterate U i))
    (hd1 : ∀ i, i < k → ∀ c : Tower.Edge L n k (i + 1), c.IsPositivelyOriented →
      Matrix.det (normalizedMean (meanIterate U i) c) = 1) :
    ∀ i, i ≤ k → ∀ b, AnalyticAt ℝ (fun u => levelField (chainLine U ξ u) i b) 0 := by
  classical
  intro i
  induction i with
  | zero =>
    intro _ b
    exact analyticAt_chainLine_fine ξ hdet b
  | succ i ih =>
    intro hi b
    have hlt : i < k := by omega
    have hγ : AnalyticAt ℝ (fun u => levelField (chainLine U ξ u) i) 0 :=
      AnalyticAt.pi fun b => ih (by omega) b
    have h0 : levelField (chainLine U ξ 0) i = meanIterate U i := by
      rw [chainLine_zero hU]
    have hφ : ∀ c : Tower.Edge L n k (i + 1), c.IsPositivelyOriented →
        AnalyticAt ℝ (fun u => normalizedMean (levelField (chainLine U ξ u) i) c) 0 := fun c hc =>
      ((hΦ i hlt c hc).restrictScalars (𝕜 := ℝ)).comp_of_eq hγ h0
    have hpos : ∀ c : Tower.Edge L n k (i + 1), ∀ hc : c.IsPositivelyOriented,
        (fun u => levelField (chainLine U ξ u) (i + 1) c) = fun u : ℝ =>
          (ComplexMatrix2.matExp (Complex.I •
            (u • (ξ.2 ⟨i, hlt⟩ : Tower.Edge L n k (i + 1) → ComplexMatrix2) c)) * 1) *
            normalizedMean (levelField (chainLine U ξ u) i) c := by
      intro c hc
      funext u
      simp only [levelField, dif_pos hlt, Tower.fieldOfPositiveValues, dif_pos hc]
      rfl
    have hanal : ∀ c : Tower.Edge L n k (i + 1), c.IsPositivelyOriented →
        AnalyticAt ℝ (fun u => levelField (chainLine U ξ u) (i + 1) c) 0 := by
      intro c hc
      rw [hpos c hc]
      exact ((analyticAt_expLine _).mul analyticAt_const).mul (hφ c hc)
    rcases hX (i + 1) hi b with ⟨hp, hn⟩ | ⟨hp, hn⟩
    · exact hanal b hp
    · have hfun : (fun u => levelField (chainLine U ξ u) (i + 1) b) = fun u =>
          (levelField (chainLine U ξ u) (i + 1) b.opposite)⁻¹ := by
        funext u
        simp only [levelField, dif_pos hlt, Tower.fieldOfPositiveValues, dif_neg hn, dif_pos hp]
      rw [hfun]
      refine analyticAt_inv_of_det (hanal _ hp) ?_
      have hv : levelField (chainLine U ξ 0) (i + 1) b.opposite =
          normalizedMean (meanIterate U i) b.opposite := by
        refine (congrFun (hpos _ hp) 0).trans ?_
        change (ComplexMatrix2.matExp (Complex.I • ((0 : ℝ) • _)) * 1) *
          normalizedMean (levelField (chainLine U ξ 0) i) _ = _
        rw [expLine_zero, h0]
        simp
      rw [hv, hd1 i hlt _ hp]
      exact isUnit_one
private theorem analyticAt_pathHolonomy {γ : ℝ → Tower.Edge L n k 0 → ComplexMatrix2}
    (h : ∀ b, AnalyticAt ℝ (fun u => γ u b) 0) (l : List (Tower.Edge L n k 0)) :
    AnalyticAt ℝ (fun u => PeriodicLattice.pathHolonomy (γ u) l) 0 := by
  induction l with
  | nil => simpa [PeriodicLattice.pathHolonomy] using analyticAt_const
  | cons b l ih =>
    have hfun : (fun u => PeriodicLattice.pathHolonomy (γ u) (b :: l)) =
        fun u => γ u b * PeriodicLattice.pathHolonomy (γ u) l := by
      funext u
      simp [PeriodicLattice.pathHolonomy]
    rw [hfun]
    exact (h b).mul ih
private def realTrace : ComplexMatrix2 →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap (Complex.reLm ∘ₗ Matrix.traceLinearMap (Fin 2) ℝ ℂ)
private theorem realTrace_apply (g : ComplexMatrix2) : realTrace g = (Matrix.trace g).re := rfl
private theorem halfTrace_re (g : ComplexMatrix2) :
    (ComplexMatrix2.halfTrace g).re = 1 / 2 * realTrace g := by
  have h : Matrix.trace g = g 0 0 + g 1 1 := Matrix.trace_fin_two g
  have hg : ComplexMatrix2.halfTrace g = (((1 / 2 : ℝ)) : ℂ) * Matrix.trace g := by
    rw [h]
    simp [ComplexMatrix2.halfTrace, Fin.sum_univ_two]
    exact h
  rw [hg, Complex.re_ofReal_mul, realTrace_apply]
private theorem analyticAt_plaquetteAction [Finite (Tower.Face L n k 0)]
    {γ : ℝ → Tower.Edge L n k 0 → ComplexMatrix2}
    (h : ∀ b, AnalyticAt ℝ (fun u => γ u b) 0) :
    AnalyticAt ℝ (fun u => Tower.plaquetteAction L n k (γ u)) 0 := by
  let _ : Fintype (Tower.Face L n k 0) := Fintype.ofFinite _
  have hfun : (fun u => Tower.plaquetteAction L n k (γ u)) = fun u => ∑ p : Tower.Face L n k 0,
      (1 - 1 / 2 * realTrace (PeriodicLattice.pathHolonomy (γ u) p.boundaryBonds)) := by
    funext u
    simp only [Tower.plaquetteAction, PeriodicLattice.wilsonAction]
    rw [finsum_eq_sum_of_fintype]
    rfl
  rw [hfun]
  refine Finset.analyticAt_fun_sum _ fun p _ => ?_
  exact analyticAt_const.sub (analyticAt_const.mul
    ((realTrace.analyticAt _).comp (analyticAt_pathHolonomy h _)))
private theorem traceDefect_expLine {X : ComplexMatrix2} (hX : X ∈ ComplexMatrix2.hermitianTraceless) :
    AnalyticAt ℝ (fun u : ℝ => traceDefect (ComplexMatrix2.matExp (Complex.I • (u • X)) * 1)) 0 ∧
      traceDefect (ComplexMatrix2.matExp (Complex.I • ((0 : ℝ) • X)) * 1) = 0 ∧
      deriv (fun u : ℝ => traceDefect (ComplexMatrix2.matExp (Complex.I • (u • X)) * 1)) 0 = 0 ∧
      deriv (deriv fun u : ℝ => traceDefect (ComplexMatrix2.matExp (Complex.I • (u • X)) * 1)) 0 =
        (ComplexMatrix2.halfTrace (X * X)).re := by
  set A : ComplexMatrix2 := Complex.I • X with hA
  have hfun : (fun u : ℝ => traceDefect (ComplexMatrix2.matExp (Complex.I • (u • X)) * 1)) =
      fun u : ℝ => 1 - 1 / 2 * realTrace (NormedSpace.exp (u • A)) := by
    funext u
    rw [traceDefect, mul_one, halfTrace_re, matExp_eq, hA, smul_comm]
  have hh : ∀ u : ℝ, HasDerivAt (fun u : ℝ => NormedSpace.exp (u • A))
      (NormedSpace.exp (u • A) * A) u := fun u => hasDerivAt_exp_smul_const (𝕂 := ℝ) A u
  have hd : ∀ u : ℝ, HasDerivAt (fun u : ℝ => 1 - 1 / 2 * realTrace (NormedSpace.exp (u • A)))
      (-(1 / 2 * realTrace (NormedSpace.exp (u • A) * A))) u := by
    intro u
    have h1 := realTrace.hasFDerivAt.comp_hasDerivAt u (hh u)
    exact ((h1.const_mul (1 / 2 : ℝ)).const_sub 1)
  have hd' : deriv (fun u : ℝ => 1 - 1 / 2 * realTrace (NormedSpace.exp (u • A))) =
      fun u => -(1 / 2 * realTrace (NormedSpace.exp (u • A) * A)) := by
    funext u
    exact (hd u).deriv
  have hd2 : HasDerivAt (fun u : ℝ => -(1 / 2 * realTrace (NormedSpace.exp (u • A) * A)))
      (-(1 / 2 * realTrace (NormedSpace.exp ((0 : ℝ) • A) * A * A))) 0 := by
    have h1 := realTrace.hasFDerivAt.comp_hasDerivAt (0 : ℝ) ((hh 0).mul_const A)
    exact (h1.const_mul (1 / 2 : ℝ)).neg
  have hexp0 : NormedSpace.exp ((0 : ℝ) • A) = 1 := by
    rw [zero_smul]
    exact NormedSpace.exp_zero
  have htr : realTrace A = 0 := by
    have h0 : Matrix.trace X = 0 := hX.2
    rw [realTrace_apply, hA, Matrix.trace_smul, h0]
    simp
  have hAA : realTrace (A * A) = -(2 * (ComplexMatrix2.halfTrace (X * X)).re) := by
    have hsq : A * A = -(X * X) := by
      rw [hA, Matrix.smul_mul, Matrix.mul_smul, smul_smul, Complex.I_mul_I]
      simp
    rw [hsq, map_neg, halfTrace_re]
    ring
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hfun]
    have h1 : AnalyticAt ℝ (fun u : ℝ => u • A) 0 := analyticAt_id.smul analyticAt_const
    have h2 := AnalyticAt.comp_of_eq (NormedSpace.exp_analytic (𝕂 := ℝ) (0 : ComplexMatrix2)) h1
      (by simp)
    exact analyticAt_const.sub (analyticAt_const.mul ((realTrace.analyticAt _).comp h2))
  · have h0 : traceDefect (ComplexMatrix2.matExp (Complex.I • ((0 : ℝ) • X)) * 1) =
        1 - 1 / 2 * realTrace (NormedSpace.exp ((0 : ℝ) • A)) := congrFun hfun 0
    rw [h0, hexp0, realTrace_apply]
    simp [Matrix.trace_one]
  · rw [hfun, (hd 0).deriv, hexp0, one_mul, htr]
    simp
  · rw [hfun, hd', hd2.deriv, hexp0, one_mul, hAA]
    ring
end ChainActionHessian
open ChainActionHessian Matrices in
theorem chainActionHessianAtQuiet_holds (hA : NormalizedMeanAnalytic)
    (hI : MeanIteratesTendToOne) (hS : MeanDerivOnForms.Claim) :
    ChainActionHessianAtQuiet := by
  intro a L hL k n hn
  classical
  obtain ⟨ρ, hρ, HA⟩ := hA L hL
  have hL2 : 2 ≤ L := by
    have := hL.2
    omega
  haveI : NeZero L := ⟨by omega⟩
  have hfinB : ∀ i, Finite (Tower.Edge L n k i) := fun i => PeriodicLattice.instFiniteBond _
  let _ : ∀ i, Fintype (Tower.Edge L n k i) := fun i =>
    have := hfinB i
    Fintype.ofFinite _
  have hX : ∀ i, i ≤ k → ∀ b : Tower.Edge L n k i,
      Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented := fun i hi b =>
    PeriodicLattice.MatrixValued.xor_isPositivelyOriented_opposite hL2
      (by simp only [PeriodicLattice.levelDepth]; omega) b
  have hnear : ∀ i, ∀ᶠ V : Tower.Edge L n k i → ComplexMatrix2 in
      𝓝[Tower.fieldSpace L n k i] (fun _ => (1 : ComplexMatrix2)),
      ∀ b, ComplexMatrix2.operatorNorm (V b - 1) < ρ := by
    intro i
    have := hfinB i
    rw [Filter.eventually_all]
    intro b
    have h1 : Tendsto (fun V : Tower.Edge L n k i → ComplexMatrix2 => V b)
        (𝓝[Tower.fieldSpace L n k i] fun _ => (1 : ComplexMatrix2)) (𝓝 1) :=
      ((continuous_apply b).tendsto _).mono_left nhdsWithin_le_nhds
    have := Metric.tendsto_nhds.1 h1 ρ hρ
    filter_upwards [this] with V hV
    simpa [dist_eq_norm] using hV
  have hev : ∀ᶠ U in 𝓝[Tower.fieldSpace L n k 0] (fun _ => (1 : ComplexMatrix2)),
      ∀ i ∈ Finset.range k,
      meanIterate U i ∈ Tower.fieldSpace L n k i ∧
        (∀ b, ComplexMatrix2.operatorNorm (meanIterate U i b - 1) < ρ) ∧
        ∀ c : Tower.Edge L n k (i + 1), c.IsPositivelyOriented →
          normalizedMean (meanIterate U i) c ∈ ComplexMatrix2.specialUnitary := by
    rw [Filter.eventually_all_finset]
    intro i hi
    have hik : i < k := Finset.mem_range.1 hi
    have hT := hI L hL k n hn i hik.le
    have h1 := hT.eventually (hnear i)
    have h2 := hT.eventually self_mem_nhdsWithin
    have h3 := hT.eventually (hS L hL n k i hn hik)
    filter_upwards [h1, h2, h3] with U f₁ f₂ f₃
    exact ⟨f₂, f₁, fun c hc => (f₃.2.1 c hc).2.2⟩
  unfold Tower.EventuallyNearIdentity
  filter_upwards [hev, self_mem_nhdsWithin] with U hU hU0 ξ
  have hUs : ∀ b, U b ∈ ComplexMatrix2.specialUnitary := fun b => hU0.1 b (Set.mem_univ b)
  have hdet : ∀ b, Matrix.det (U b) = 1 := fun b =>
    (Matrix.mem_specialUnitaryGroup_iff.1 (hUs b)).2
  have hinvU : ∀ b, (U b.opposite)⁻¹ = U b := by
    intro b
    rw [hU0.2 b (Set.mem_univ b)]
    exact Matrix.nonsing_inv_nonsing_inv _ (by rw [hdet b]; exact isUnit_one)
  have hcfg : ∀ i, i < k →
      meanIterate U i ∈ Tower.fieldsIn L n k i PeriodicLattice.complexGaugeGroup := by
    intro i hi
    have h := (hU i (Finset.mem_range.2 hi)).1
    exact ⟨fun b _ => (Matrix.mem_specialUnitaryGroup_iff.1 (h.1 b (Set.mem_univ b))).2, h.2⟩
  have hΦ : ∀ i, i < k → ∀ c : Tower.Edge L n k (i + 1), c.IsPositivelyOriented →
      AnalyticAt ℂ (fun V' : Tower.Edge L n k i → ComplexMatrix2 => normalizedMean V' c)
        (meanIterate U i) :=
    fun i hi c hc => (HA n k i hn hi _ (hcfg i hi) (hU i (Finset.mem_range.2 hi)).2.1 c hc).2
  have hΛ : ∀ i, i < k → ∀ c : Tower.Edge L n k (i + 1), c.IsPositivelyOriented →
      AnalyticAt ℂ (fun V' : Tower.Edge L n k i → ComplexMatrix2 => meanRadius V' c)
        (meanIterate U i) :=
    fun i hi c hc => (HA n k i hn hi _ (hcfg i hi) (hU i (Finset.mem_range.2 hi)).2.1 c hc).1
  have hd1 : ∀ i, i < k → ∀ c : Tower.Edge L n k (i + 1), c.IsPositivelyOriented →
      Matrix.det (normalizedMean (meanIterate U i) c) = 1 := fun i hi c hc =>
    (Matrix.mem_specialUnitaryGroup_iff.1 ((hU i (Finset.mem_range.2 hi)).2.2 c hc)).2
  have hfield := analyticAt_levelField ξ hdet hinvU hX hΦ hd1
  have hzero : ∀ i : ℕ, levelField (chainLine U ξ 0) i = meanIterate U i := fun i => by
    rw [chainLine_zero hinvU]
  have hchain : leftSecondDeriv (chainAction a) (quietPoint U) ξ ξ =
      deriv (deriv fun u => chainAction a (chainLine U ξ u)) 0 := by
    unfold leftSecondDeriv
    have hfun : (fun s : ℝ => deriv (fun t : ℝ =>
        chainAction a (expMove (s • ξ + t • ξ) (quietPoint U))) 0) =
        deriv fun u => chainAction a (chainLine U ξ u) := by
      funext s
      have hshift : (fun t : ℝ => chainAction a (expMove (s • ξ + t • ξ) (quietPoint U))) =
          fun t => (fun u => chainAction a (chainLine U ξ u)) (s + t) := by
        funext t
        simp only [chainLine, add_smul]
      rw [hshift]
      exact deriv_comp_add_left_zero (fun u => chainAction a (chainLine U ξ u)) s
    rw [hfun]
  have hact : Tower.leftSecondDeriv (Tower.plaquetteAction L n k) U
      (ξ.1 : Tower.Edge L n k 0 → ComplexMatrix2) (ξ.1 : Tower.Edge L n k 0 → ComplexMatrix2) =
      deriv (deriv fun u => Tower.plaquetteAction L n k (chainLine U ξ u).fine) 0 := by
    unfold Tower.leftSecondDeriv Tower.mixedDirectionalDeriv
    have hfun : (fun s : ℝ => deriv (fun t : ℝ => Tower.plaquetteAction L n k
        (PeriodicLattice.expTwist
          (algebraMap ℝ ℂ s • (ξ.1 : Tower.Edge L n k 0 → ComplexMatrix2) +
            algebraMap ℝ ℂ t • (ξ.1 : Tower.Edge L n k 0 → ComplexMatrix2)) U)) 0) =
        deriv fun u => Tower.plaquetteAction L n k (chainLine U ξ u).fine := by
      funext s
      have hshift : (fun t : ℝ => Tower.plaquetteAction L n k (PeriodicLattice.expTwist
          (algebraMap ℝ ℂ s • (ξ.1 : Tower.Edge L n k 0 → ComplexMatrix2) +
            algebraMap ℝ ℂ t • (ξ.1 : Tower.Edge L n k 0 → ComplexMatrix2)) U)) =
          fun t => (fun u => Tower.plaquetteAction L n k (chainLine U ξ u).fine) (s + t) := by
        funext t
        have hsum : algebraMap ℝ ℂ s • (ξ.1 : Tower.Edge L n k 0 → ComplexMatrix2) +
            algebraMap ℝ ℂ t • (ξ.1 : Tower.Edge L n k 0 → ComplexMatrix2) =
            (((s + t) • ξ).1 : Tower.Edge L n k 0 → ComplexMatrix2) := by
          funext b
          change (algebraMap ℝ ℂ s) • (ξ.1 : Tower.Edge L n k 0 → ComplexMatrix2) b +
            (algebraMap ℝ ℂ t) • (ξ.1 : Tower.Edge L n k 0 → ComplexMatrix2) b =
            (s + t) • (ξ.1 : Tower.Edge L n k 0 → ComplexMatrix2) b
          rw [add_smul]
          simp only [Complex.coe_algebraMap, Complex.coe_smul]
        simp only [hsum]
        rfl
      rw [hshift]
      exact deriv_comp_add_left_zero (fun u => Tower.plaquetteAction L n k (chainLine U ξ u).fine) s
    exact congrArg (fun f : ℝ → ℝ => deriv f 0) hfun
  have hfinP : ∀ i, Finite (Tower.PositiveEdge L n k i) := fun i => by
    have := hfinB i
    exact Subtype.finite
  let _ : ∀ i, Fintype (Tower.PositiveEdge L n k i) := fun i =>
    have := hfinP i
    Fintype.ofFinite _
  have hfinPl : Finite (Tower.Face L n k 0) := by
    have : Finite (PeriodicLattice.Site L n (PeriodicLattice.levelDepth k 0)) :=
      PeriodicLattice.instFiniteSite _
    exact PeriodicLattice.ConjugationReality.finite_plaquette _ _ _
  set r : (i : Fin k) → Tower.PositiveEdge L n k (i + 1) → ℝ → ℝ := fun i c u =>
    (meanRadius (levelField (chainLine U ξ u) i) c.1).re with hr
  set e : (i : Fin k) → Tower.PositiveEdge L n k (i + 1) → ℝ → ℝ := fun i c u =>
    traceDefect ((chainLine U ξ u).noise i c) with he
  have hg : (fun u => chainAction a (chainLine U ξ u)) = fun u =>
      Tower.plaquetteAction L n k (chainLine U ξ u).fine +
      a * ∑ i : Fin k, ∑ c : Tower.PositiveEdge L n k (i + 1), r i c u * e i c u := by
    funext u
    simp only [chainAction]
    congr 2
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [finsum_eq_sum_of_fintype]
  have hrA : ∀ i c, AnalyticAt ℝ (r i c) 0 := by
    intro i c
    have hγ : AnalyticAt ℝ (fun u => levelField (chainLine U ξ u) i) 0 :=
      AnalyticAt.pi fun b => hfield i i.2.le b
    have h1 := ((hΛ i i.2 c.1 c.2).restrictScalars (𝕜 := ℝ)).comp_of_eq hγ (hzero i)
    exact (Complex.reCLM.analyticAt _).comp h1
  have hsu : ∀ (i : Fin k) (c : Tower.PositiveEdge L n k (i + 1)),
      ((ξ.2 i : Tower.edgeFormSpace L n k (i + 1)) : Tower.Edge L n k (i + 1) → ComplexMatrix2) c.1 ∈
        ComplexMatrix2.hermitianTraceless := fun i c =>
    (ξ.2 i).2.1 c.1 c.2
  have heA : ∀ i c, AnalyticAt ℝ (e i c) 0 := fun i c => (traceDefect_expLine (hsu i c)).1
  have he0 : ∀ i c, e i c 0 = 0 := fun i c => (traceDefect_expLine (hsu i c)).2.1
  have he1 : ∀ i c, deriv (e i c) 0 = 0 := fun i c => (traceDefect_expLine (hsu i c)).2.2.1
  have he2 : ∀ i c, deriv (deriv (e i c)) 0 =
      (ComplexMatrix2.halfTrace
        (((ξ.2 i : Tower.edgeFormSpace L n k (i + 1)) : Tower.Edge L n k (i + 1) → ComplexMatrix2) c.1 *
        ((ξ.2 i : Tower.edgeFormSpace L n k (i + 1)) : Tower.Edge L n k (i + 1) → ComplexMatrix2) c.1)).re :=
    fun i c => (traceDefect_expLine (hsu i c)).2.2.2
  have hrc : ∀ i c, AnalyticAt ℝ (fun u => r i c u * e i c u) 0 := fun i c =>
    (hrA i c).mul (heA i c)
  have hsumc : ∀ i : Fin k,
      AnalyticAt ℝ (fun u => ∑ c : Tower.PositiveEdge L n k (i + 1), r i c u * e i c u) 0 :=
    fun i => Finset.analyticAt_fun_sum _ fun c _ => hrc i c
  have hsumi : AnalyticAt ℝ (fun u => ∑ i : Fin k, ∑ c : Tower.PositiveEdge L n k (i + 1),
      r i c u * e i c u) 0 := Finset.analyticAt_fun_sum _ fun i _ => hsumc i
  have h₁ : AnalyticAt ℝ (fun u => Tower.plaquetteAction L n k (chainLine U ξ u).fine) 0 :=
    analyticAt_plaquetteAction fun b => analyticAt_chainLine_fine ξ hdet b
  have h₂ : AnalyticAt ℝ (fun u => a * ∑ i : Fin k, ∑ c : Tower.PositiveEdge L n k (i + 1),
      r i c u * e i c u) 0 := analyticAt_const.mul hsumi
  rw [hchain, hg, secondDeriv_add h₁ h₂, secondDeriv_const_mul, ← hact,
    secondDeriv_sum Finset.univ
      (fun (i : Fin k) u => ∑ c : Tower.PositiveEdge L n k (i + 1), r i c u * e i c u)
      fun i _ => hsumc i]
  congr 2
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [secondDeriv_sum Finset.univ (fun (c : Tower.PositiveEdge L n k (i + 1)) u => r i c u * e i c u)
    fun c _ => hrc i c, finsum_eq_sum_of_fintype]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [secondDeriv_mul_of_vanishing (hrA i c) (heA i c) (he0 i c) (he1 i c), he2]
  simp only [hr, hzero]
end YangMills.Construction.RunningCouplingSlope
end
