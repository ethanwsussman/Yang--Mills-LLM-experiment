import YangMills.Construction.Towers.CriticalPointsAndHessiansThroughAChart
import Mathlib
set_option autoImplicit false
open Set Filter Topology
noncomputable section
namespace YangMills.Construction.Geometry.ChartedCriticalPoints
variable {X T K : Type} [AddCommGroup T] [Module ℝ T] [NormedAddCommGroup K] [NormedSpace ℝ K]
theorem exists_openInterval_mapsTo_line {O : Set K} (hO : IsOpen O) {x : K} (hx : x ∈ O) (v : K) :
    ∃ I : Set ℝ, Tower.IsOpenIntervalAroundZero I ∧ MapsTo (fun t : ℝ => x + t • v) I O := by
  have hcont : Continuous fun t : ℝ => x + t • v := by fun_prop
  have hpre : (fun t : ℝ => x + t • v) ⁻¹' O ∈ 𝓝 (0 : ℝ) :=
    hcont.continuousAt.preimage_mem_nhds (by simpa using hO.mem_nhds hx)
  obtain ⟨ε, hε, hsub⟩ := Metric.mem_nhds_iff.1 hpre
  exact ⟨Metric.ball 0 ε, ⟨Metric.isOpen_ball, (convex_ball 0 ε).ordConnected,
    Metric.mem_ball_self hε⟩, fun t ht => hsub ht⟩
theorem hasDerivAt_comp_curve {O : Set K} (hO : IsOpen O) {G : K → ℝ} (hG : ContDiffOn ℝ 2 G O)
    {I : Set ℝ} (hI : IsOpen I) {c : ℝ → K} (hc : DifferentiableOn ℝ c I) (hmaps : MapsTo c I O)
    {t : ℝ} (ht : t ∈ I) :
    HasDerivAt (fun s => G (c s)) (fderiv ℝ G (c t) (deriv c t)) t := by
  have hf : HasFDerivAt G (fderiv ℝ G (c t)) (c t) :=
    ((hG.differentiableOn (by norm_num)).differentiableAt (hO.mem_nhds (hmaps ht))).hasFDerivAt
  exact hf.comp_hasDerivAt t (hc.differentiableAt (hI.mem_nhds ht)).hasDerivAt
theorem deriv_deriv_comp_curve_of_fderiv_eq_zero {O : Set K} (hO : IsOpen O) {G : K → ℝ}
    (hG : ContDiffOn ℝ 2 G O) {I : Set ℝ} (hI : IsOpen I) (hzero : (0 : ℝ) ∈ I) {c : ℝ → K}
    (hc : DifferentiableOn ℝ c I) (hc' : DifferentiableOn ℝ (deriv c) I) (hmaps : MapsTo c I O)
    (hcrit : fderiv ℝ G (c 0) = 0) :
    deriv (deriv fun t => G (c t)) 0 = fderiv ℝ (fderiv ℝ G) (c 0) (deriv c 0) (deriv c 0) := by
  have heq : deriv (fun t => G (c t)) =ᶠ[𝓝 0] fun t => fderiv ℝ G (c t) (deriv c t) :=
    eventually_of_mem (hI.mem_nhds hzero) fun t ht => (hasDerivAt_comp_curve hO hG hI hc hmaps ht).deriv
  have hat : ContDiffAt ℝ 2 G (c 0) := hG.contDiffAt (hO.mem_nhds (hmaps hzero))
  have hf : HasFDerivAt (fderiv ℝ G) (fderiv ℝ (fderiv ℝ G) (c 0)) (c 0) :=
    ((hat.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)).hasFDerivAt
  have hcomp : HasDerivAt (fun t => fderiv ℝ G (c t))
      (fderiv ℝ (fderiv ℝ G) (c 0) (deriv c 0)) 0 :=
    hf.comp_hasDerivAt 0 (hc.differentiableAt (hI.mem_nhds hzero)).hasDerivAt
  have hvel : HasDerivAt (deriv c) (deriv (deriv c) 0) 0 :=
    (hc'.differentiableAt (hI.mem_nhds hzero)).hasDerivAt
  rw [heq.deriv_eq, (hcomp.clm_apply hvel).deriv, hcrit]
  simp
variable {R : CurveData X T} {N : Set X} {O : Set K} {φ : K → X} {r : X → K}
  {D : K → K →ₗ[ℝ] T} {F : X → ℝ}
theorem comp_eventuallyEq_comp_coord (hR : R.IsChartedBy N O φ r D) {I : Set ℝ} (hI : IsOpen I)
    (hzero : (0 : ℝ) ∈ I) {γ : ℝ → X} (hmaps : MapsTo γ I N) :
    (fun t => F (γ t)) =ᶠ[𝓝 0] fun t => F (φ (r (γ t))) :=
  eventually_of_mem (hI.mem_nhds hzero) fun t ht => by
    show F (γ t) = F (φ (r (γ t)))
    rw [hR.param_coord _ (hmaps ht)]
theorem mapsTo_coord_comp (hR : R.IsChartedBy N O φ r D) {I : Set ℝ} {γ : ℝ → X}
    (hmaps : MapsTo γ I N) : MapsTo (fun t => r (γ t)) I O :=
  fun _ ht => hR.coord_mem _ (hmaps ht)
theorem deriv_comp_curve_eq (hR : R.IsChartedBy N O φ r D)
    (hG : ContDiffOn ℝ 2 (fun x => F (φ x)) O) {x : K} (hx : x ∈ O) {I : Set ℝ} {γ : ℝ → X}
    (hγ : R.IsCurve I γ) (hmaps : MapsTo γ I N) (hstart : γ 0 = φ x) :
    deriv (fun t => F (γ t)) 0 =
      fderiv ℝ (fun x => F (φ x)) x (deriv (fun t => r (γ t)) 0) := by
  have hI := hR.isInterval I γ hγ
  have hr : r (γ 0) = x := by rw [hstart, hR.coord_param x hx]
  rw [(comp_eventuallyEq_comp_coord hR hI.1 hI.2.2 hmaps).deriv_eq,
    (hasDerivAt_comp_curve hR.isOpen_domain hG hI.1 (hR.coord_differentiableOn I γ hγ hmaps)
      (mapsTo_coord_comp hR hmaps) hI.2.2).deriv, hr]
theorem deriv_deriv_comp_curve_eq (hR : R.IsChartedBy N O φ r D)
    (hG : ContDiffOn ℝ 2 (fun x => F (φ x)) O) {x : K} (hx : x ∈ O)
    (hcrit : fderiv ℝ (fun x => F (φ x)) x = 0) {I : Set ℝ} {γ : ℝ → X}
    (hγ : R.IsTwiceDiffCurve I γ) (hmaps : MapsTo γ I N) (hstart : γ 0 = φ x) :
    deriv (deriv fun t => F (γ t)) 0 =
      fderiv ℝ (fderiv ℝ fun x => F (φ x)) x (deriv (fun t => r (γ t)) 0)
        (deriv (fun t => r (γ t)) 0) := by
  have hcurve := (hR.twice_coord I γ hγ).1
  have hI := hR.isInterval I γ hcurve
  have hr : r (γ 0) = x := by rw [hstart, hR.coord_param x hx]
  have key := deriv_deriv_comp_curve_of_fderiv_eq_zero (G := fun x => F (φ x))
    (c := fun t => r (γ t)) hR.isOpen_domain hG hI.1 hI.2.2
    (hR.coord_differentiableOn I γ hcurve hmaps) ((hR.twice_coord I γ hγ).2 hmaps)
    (mapsTo_coord_comp hR hmaps) (by simpa only [hr] using hcrit)
  rw [(comp_eventuallyEq_comp_coord hR hI.1 hI.2.2 hmaps).deriv.deriv_eq]
  simpa only [hr] using key
theorem exists_curve_with_velocity (hR : R.IsChartedBy N O φ r D) {x : K} (hx : x ∈ O) (v : K) :
    ∃ (I : Set ℝ) (γ : ℝ → X), R.IsTwiceDiffCurve I γ ∧ MapsTo γ I N ∧ γ 0 = φ x ∧
      deriv (fun t => r (γ t)) 0 = v ∧ R.tangent γ = D x v := by
  obtain ⟨I, hI, hline⟩ := exists_openInterval_mapsTo_line hR.isOpen_domain hx v
  have hd : ∀ t : ℝ, HasDerivAt (fun t : ℝ => x + t • v) v t := fun t => by
    simpa using ((hasDerivAt_id t).smul_const v).const_add x
  have hderiv : deriv (fun t : ℝ => x + t • v) = fun _ => v := funext fun t => (hd t).deriv
  have hdiff : DifferentiableOn ℝ (fun t : ℝ => x + t • v) I :=
    fun t _ => (hd t).differentiableAt.differentiableWithinAt
  have hdiff' : DifferentiableOn ℝ (deriv fun t : ℝ => x + t • v) I := by
    rw [hderiv]
    exact differentiableOn_const v
  have htwice := hR.param_isTwiceDiffCurve I _ hI hdiff hdiff' hline
  have hmaps : MapsTo (fun t : ℝ => φ (x + t • v)) I N := fun t ht => hR.mapsTo_param (hline ht)
  have hstart : (fun t : ℝ => φ (x + t • v)) 0 = φ x := by simp
  have heq : (fun t : ℝ => r (φ (x + t • v))) =ᶠ[𝓝 0] fun t : ℝ => x + t • v :=
    eventually_of_mem (hI.1.mem_nhds hI.2.2) fun t ht => hR.coord_param _ (hline ht)
  have hvel : deriv (fun t : ℝ => r (φ (x + t • v))) 0 = v := by
    rw [heq.deriv_eq, (hd 0).deriv]
  refine ⟨I, _, htwice, hmaps, hstart, hvel, ?_⟩
  have htan := hR.tangent_eq I _ (hR.twice_coord I _ htwice).1 hmaps
  have hr : r (φ (x + (0 : ℝ) • v)) = x := by simp [hR.coord_param x hx]
  rw [htan, hr, hvel]
theorem tangentSpan_le_range (hR : R.IsChartedBy N O φ r D) {x : K} (hx : x ∈ O) :
    R.tangentSpan N (φ x) ≤ LinearMap.range (D x) := by
  refine Submodule.span_le.2 ?_
  rintro w ⟨I, γ, hγ, hmaps, hstart, rfl⟩
  refine ⟨deriv (fun t => r (γ t)) 0, ?_⟩
  rw [hR.tangent_eq I γ hγ hmaps, hstart, hR.coord_param x hx]
theorem exists_isHessianFormAt (hR : R.IsChartedBy N O φ r D)
    (hG : ContDiffOn ℝ 2 (fun x => F (φ x)) O) {x : K} (hx : x ∈ O)
    (hcrit : fderiv ℝ (fun x => F (φ x)) x = 0) :
    ∃ Q : QuadraticForm ℝ (R.tangentSpan N (φ x)),
      R.IsHessianFormAt Subtype.val N F (φ x) Q := by
  obtain ⟨g, hg⟩ := (D x).exists_leftInverse_of_injective
    (LinearMap.ker_eq_bot.2 (hR.injective_diff x hx))
  have hgD : ∀ v, g (D x v) = v := fun v => LinearMap.congr_fun hg v
  let L := fderiv ℝ (fderiv ℝ fun x => F (φ x)) x
  let B : K →ₗ[ℝ] K →ₗ[ℝ] ℝ := (ContinuousLinearMap.coeLM ℝ) ∘ₗ (L : K →ₗ[ℝ] (K →L[ℝ] ℝ))
  refine ⟨(LinearMap.BilinMap.toQuadraticMap B).comp
    (g ∘ₗ (R.tangentSpan N (φ x)).subtype), ?_⟩
  intro I γ w hγ hmaps hstart htan
  have hcurve := (hR.twice_coord I γ hγ).1
  have hw : g w.1 = deriv (fun t => r (γ t)) 0 := by
    rw [← htan, hR.tangent_eq I γ hcurve hmaps, hstart, hR.coord_param x hx, hgD]
  rw [deriv_deriv_comp_curve_eq hR hG hx hcrit hγ hmaps hstart]
  simp [B, L, hw]
theorem hessianForm_posDef (hR : R.IsChartedBy N O φ r D)
    (hG : ContDiffOn ℝ 2 (fun x => F (φ x)) O) {x : K} (hx : x ∈ O)
    (hcrit : fderiv ℝ (fun x => F (φ x)) x = 0)
    (hpos : ∀ v : K, v ≠ 0 → 0 < fderiv ℝ (fderiv ℝ fun x => F (φ x)) x v v) :
    (R.hessianForm (S := R.tangentSpan N (φ x)) Subtype.val N F (φ x)).PosDef := by
  have hspec : R.IsHessianFormAt Subtype.val N F (φ x)
      (R.hessianForm (S := R.tangentSpan N (φ x)) Subtype.val N F (φ x)) :=
    Classical.epsilon_spec (exists_isHessianFormAt hR hG hx hcrit)
  intro w hw
  obtain ⟨v, hv⟩ := tangentSpan_le_range hR hx w.2
  have hne : v ≠ 0 := by
    rintro rfl
    exact hw (Subtype.ext (by simpa using hv.symm))
  obtain ⟨I, γ, hγ, hmaps, hstart, hvel, htan⟩ := exists_curve_with_velocity hR hx v
  rw [hspec I γ w hγ hmaps hstart (htan.trans hv),
    deriv_deriv_comp_curve_eq hR hG hx hcrit hγ hmaps hstart, hvel]
  exact hpos v hne
theorem statement_holds : ChartedCriticalPoints.Statement := by
  intro X T K _ _ _ _ R N O φ r D F hR hG x hx
  refine ⟨⟨fun hc => ?_, fun hcrit => ⟨hR.mapsTo_param hx, fun I γ hγ hmaps hstart => ?_⟩⟩,
    fun hcrit hpos => hessianForm_posDef hR hG hx hcrit hpos⟩
  · refine ContinuousLinearMap.ext fun v => ?_
    obtain ⟨I, γ, hγ, hmaps, hstart, hvel, -⟩ := exists_curve_with_velocity hR hx v
    have hcurve := (hR.twice_coord I γ hγ).1
    have key := hc.2 I γ hcurve hmaps hstart
    rw [deriv_comp_curve_eq hR hG hx hcurve hmaps hstart, hvel] at key
    simpa using key
  · rw [deriv_comp_curve_eq hR hG hx hγ hmaps hstart, hcrit]
    simp
end YangMills.Construction.Geometry.ChartedCriticalPoints
end
