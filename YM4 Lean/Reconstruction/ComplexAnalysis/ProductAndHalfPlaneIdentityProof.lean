import Reconstruction.ComplexAnalysis.ProductAndHalfPlaneIdentity
import YangMills.Construction.Coordinates.PowerSeriesHolomorphy
import Mathlib
set_option autoImplicit false
open Set Filter
open scoped Topology
open YangMills.Construction.Coordinates YangMills.Construction.Coordinates.ComplexCoordinates YangMills.Construction.ComplexManifolds
noncomputable section
namespace YangMills.Construction.ComplexAnalysis
theorem coordinatesProdHomeomorph_apply_finSumFinEquiv (n m : ℕ)
    (z : ComplexCoordinates n × ComplexCoordinates m) (k : Fin n ⊕ Fin m) :
    coordinatesProdHomeomorph n m z (finSumFinEquiv k) = Sum.elim z.1 z.2 k := by
  have hk := Equiv.piCongrLeft_apply_apply (fun _ : Fin (n + m) => ℂ) finSumFinEquiv
    (Sum.elim z.1 z.2) k
  exact hk
def coordinatesProdCLM (n m : ℕ) :
    (ComplexCoordinates n × ComplexCoordinates m) →L[ℂ] ComplexCoordinates (n + m) :=
  LinearMap.toContinuousLinearMap
    { toFun := coordinatesProdHomeomorph n m
      map_add' := by
        intro z w
        funext j
        obtain ⟨k, rfl⟩ := finSumFinEquiv.surjective j
        rw [Pi.add_apply, coordinatesProdHomeomorph_apply_finSumFinEquiv,
          coordinatesProdHomeomorph_apply_finSumFinEquiv,
          coordinatesProdHomeomorph_apply_finSumFinEquiv]
        cases k <;> simp
      map_smul' := by
        intro c z
        funext j
        obtain ⟨k, rfl⟩ := finSumFinEquiv.surjective j
        rw [Pi.smul_apply, coordinatesProdHomeomorph_apply_finSumFinEquiv,
          coordinatesProdHomeomorph_apply_finSumFinEquiv]
        cases k <;> simp }
theorem coordinatesProdCLM_apply (n m : ℕ) (z : ComplexCoordinates n × ComplexCoordinates m) :
    coordinatesProdCLM n m z = coordinatesProdHomeomorph n m z := rfl
theorem eq_zero_on_ball_of_eventually_zero {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {f : E → ℂ} {c : E} {ρ : ℝ} (hf : DifferentiableOn ℂ f (Metric.ball c ρ)) (hρ : 0 < ρ)
    (hzero : ∀ᶠ q in 𝓝 c, f q = 0) : ∀ w ∈ Metric.ball c ρ, f w = 0 := by
  intro w hw
  let γ : ℂ → E := fun ζ => c + ζ • (w - c)
  have hγ : Continuous γ := by fun_prop
  let V : Set ℂ := γ ⁻¹' Metric.ball c ρ
  have hVo : IsOpen V := Metric.isOpen_ball.preimage hγ
  have hVc : Convex ℝ V := by
    intro x hx y hy s t hs ht hst
    have hmem := (convex_ball c ρ) hx hy hs ht hst
    have hlin : γ (s • x + t • y) = s • γ x + t • γ y := by
      have hc' : c = s • c + t • c := by rw [← add_smul, hst, one_smul]
      simp only [γ, add_smul, smul_add, smul_assoc]
      nth_rw 1 [hc']
      abel
    change γ (s • x + t • y) ∈ Metric.ball c ρ
    rw [hlin]
    exact hmem
  have hV0 : (0 : ℂ) ∈ V := by simp [V, γ, hρ]
  have hV1 : (1 : ℂ) ∈ V := by simpa [V, γ] using hw
  have hcomp : DifferentiableOn ℂ (f ∘ γ) V := by
    apply hf.comp
    · exact (by fun_prop : Differentiable ℂ γ).differentiableOn
    · exact fun _ hx => hx
  have hana := hcomp.analyticOnNhd hVo
  have hev : (f ∘ γ) =ᶠ[𝓝 0] 0 := by
    have htend : Tendsto γ (𝓝 0) (𝓝 c) := by
      have := hγ.tendsto 0
      simpa [γ] using this
    exact htend.eventually hzero
  have := hana.eqOn_zero_of_preconnected_of_eventuallyEq_zero hVc.isPreconnected hV0 hev hV1
  simpa [γ] using this
theorem differentiableOn_of_holomorphicOnCoordinatesProd
    (hps : PowerSeriesHolomorphy.Properties)
    {n m : ℕ} {U : Set (ComplexCoordinates n × ComplexCoordinates m)}
    {f : ComplexCoordinates n × ComplexCoordinates m → ℂ} (hf : HolomorphicOnCoordinatesProd U f) :
    DifferentiableOn ℂ f U := by
  intro z hz
  have hO := hf.1
  obtain ⟨L, hL⟩ := ((hps.1 (n + m) _ hO).1 1 _ hf).2.2.1 (coordinatesProdHomeomorph n m z)
    ⟨z, hz, rfl⟩
  have hv := (hasFDerivAt_of_restrictScalars ℝ hL rfl).differentiableAt
  have hlin : DifferentiableAt ℂ (fun q => coordinatesProdCLM n m q) z :=
    (coordinatesProdCLM n m).differentiableAt
  have hcomp := (DifferentiableAt.comp z (f := fun q => coordinatesProdCLM n m q) hv hlin)
  have hcoord : DifferentiableAt ℂ (fun q => (((fun w (_ : Fin 1) =>
      f ((coordinatesProdHomeomorph n m).symm w)) ∘
      fun q => coordinatesProdCLM n m q) q) 0) z :=
    (differentiableAt_pi.1 hcomp) 0
  have heq : (fun q => (((fun w (_ : Fin 1) => f ((coordinatesProdHomeomorph n m).symm w)) ∘
      fun q => coordinatesProdCLM n m q) q) 0) = f := by
    funext q
    simp [coordinatesProdCLM_apply]
  rw [heq] at hcoord
  exact hcoord.differentiableWithinAt
theorem eq_zero_of_eventually_zero_on_realLocus (hps : PowerSeriesHolomorphy.Properties)
    (n m : ℕ) (U : Set (ComplexCoordinates n × ComplexCoordinates m))
    (f : ComplexCoordinates n × ComplexCoordinates m → ℂ)
    (x₀ : ComplexCoordinates n) (y₀ : ComplexCoordinates m)
    (hU : IsOpen U) (hconn : IsConnected U) (hf : HolomorphicOnCoordinatesProd U f)
    (hmem₀ : (x₀, y₀) ∈ U) (hx₀ : x₀ ∈ realLocus n)
    (hvanish : ∀ᶠ z in 𝓝 (x₀, y₀), z.1 ∈ realLocus n → f z = 0) :
    ∀ z ∈ U, f z = 0 := by
  have hdiff := differentiableOn_of_holomorphicOnCoordinatesProd hps hf
  let W : Set (ComplexCoordinates n × ComplexCoordinates m) := {z | ∀ᶠ q in 𝓝 z, f q = 0}
  have hWo : IsOpen W := isOpen_setOfPred_eventually_nhds
  have hbase : (x₀, y₀) ∈ W := by
    obtain ⟨ρ, hρ, hball⟩ := Metric.eventually_nhds_iff_ball.1 (hvanish.and (hU.mem_nhds hmem₀))
    have hsmall : ∀ z ∈ Metric.ball ((x₀, y₀) : ComplexCoordinates n × ComplexCoordinates m)
        (ρ / 3), f z = 0 := by
      rintro ⟨x, y⟩ hz
      rw [← ball_prod_same, Set.mem_prod] at hz
      obtain ⟨hx, hy⟩ := hz
      let a : ComplexCoordinates n := fun j => ((x j).re : ℂ)
      let b : ComplexCoordinates n := fun j => ((x j).im : ℂ)
      let γ : ℂ → ComplexCoordinates n × ComplexCoordinates m := fun ζ => (a + ζ • b, y)
      have hγ : Differentiable ℂ γ := by fun_prop
      have hγball : ∀ ζ ∈ Metric.ball (0 : ℂ) 2, γ ζ ∈ Metric.ball (x₀, y₀) ρ := by
        intro ζ hζ
        rw [← ball_prod_same, Set.mem_prod]
        have hζ' : ‖ζ‖ < 2 := by simpa using hζ
        refine ⟨?_, Metric.ball_subset_ball (by linarith) hy⟩
        rw [mem_ball_iff_norm, pi_norm_lt_iff hρ]
        intro j
        have hxj : ‖x j - x₀ j‖ < ρ / 3 := by
          rw [mem_ball_iff_norm] at hx
          exact lt_of_le_of_lt (norm_le_pi_norm (x - x₀) j) hx
        have him : (x₀ j).im = 0 := hx₀ j
        have hsplit : (a + ζ • b - x₀) j =
            (((x j - x₀ j).re : ℝ) : ℂ) + ζ * (((x j - x₀ j).im : ℝ) : ℂ) - 0 := by
          have hre : (((x₀ j).re : ℝ) : ℂ) = x₀ j := by
            apply Complex.ext <;> simp [him]
          simp only [a, b, Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
            Complex.sub_re, Complex.sub_im, him, sub_zero]
          push_cast
          rw [hre]
          ring
        rw [hsplit, sub_zero]
        calc ‖(((x j - x₀ j).re : ℝ) : ℂ) + ζ * (((x j - x₀ j).im : ℝ) : ℂ)‖
            ≤ ‖(((x j - x₀ j).re : ℝ) : ℂ)‖ + ‖ζ‖ * ‖(((x j - x₀ j).im : ℝ) : ℂ)‖ := by
              refine (norm_add_le _ _).trans ?_
              rw [norm_mul]
          _ ≤ ‖x j - x₀ j‖ + 2 * ‖x j - x₀ j‖ := by
              have hr1 : ‖(((x j - x₀ j).re : ℝ) : ℂ)‖ ≤ ‖x j - x₀ j‖ := by
                rw [Complex.norm_real]
                exact Complex.abs_re_le_norm _
              have hr2 : ‖(((x j - x₀ j).im : ℝ) : ℂ)‖ ≤ ‖x j - x₀ j‖ := by
                rw [Complex.norm_real]
                exact Complex.abs_im_le_norm _
              have hr3 := norm_nonneg (((x j - x₀ j).im : ℝ) : ℂ)
              nlinarith
          _ < ρ := by linarith
      let V : Set ℂ := Metric.ball 0 2
      have hcomp : DifferentiableOn ℂ (f ∘ γ) V := by
        apply hdiff.comp hγ.differentiableOn
        intro ζ hζ
        exact (hball _ (hγball ζ hζ)).2
      have hana := hcomp.analyticOnNhd Metric.isOpen_ball
      have hfreq : ∃ᶠ ζ in 𝓝[≠] (0 : ℂ), (f ∘ γ) ζ = 0 := by
        have hseq : Tendsto (fun k : ℕ => (((1 / ((k : ℝ) + 1) : ℝ)) : ℂ)) atTop (𝓝[≠] 0) := by
          refine tendsto_nhdsWithin_iff.2 ⟨?_, Eventually.of_forall fun k => ?_⟩
          · have ht : Tendsto (fun k : ℕ => (((1 / ((k : ℝ) + 1) : ℝ)) : ℂ)) atTop
                (𝓝 ((0 : ℝ) : ℂ)) :=
              (Complex.continuous_ofReal.tendsto 0).comp
                (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
            simpa only [Complex.ofReal_zero] using ht
          · have hne : (1 / ((k : ℝ) + 1)) ≠ 0 := by positivity
            simp only [mem_compl_iff, mem_singleton_iff, Complex.ofReal_eq_zero]
            exact hne
        refine hseq.frequently (Frequently.of_forall fun k => ?_)
        have hk0 : (0 : ℝ) < (k : ℝ) + 1 := by positivity
        have hkV : (((1 / ((k : ℝ) + 1) : ℝ)) : ℂ) ∈ V := by
          have hle : 1 / ((k : ℝ) + 1) ≤ 1 := by
            rw [div_le_one hk0]
            linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
          have hpos : 0 < 1 / ((k : ℝ) + 1) := by positivity
          simp only [V, mem_ball_zero_iff, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hpos]
          linarith
        refine (hball _ (hγball _ hkV)).1 ?_
        intro j
        simp [γ, a, b]
      have hIV : Complex.I ∈ V := by simp [V]
      have h0V : (0 : ℂ) ∈ V := by simp [V]
      have := hana.eqOn_zero_of_preconnected_of_frequently_eq_zero
        (convex_ball (0 : ℂ) 2).isPreconnected h0V hfreq hIV
      have hγI : γ Complex.I = (x, y) := by
        refine Prod.ext ?_ rfl
        funext j
        simp only [γ, a, b, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
        rw [mul_comm]
        exact Complex.re_add_im (x j)
      simpa [hγI] using this
    exact Metric.eventually_nhds_iff_ball.2 ⟨ρ / 3, by positivity, hsmall⟩
  have hclosed : closure W ∩ U ⊆ W := by
    rintro z ⟨hcl, hzU⟩
    obtain ⟨ρ, hρ, hball⟩ := Metric.isOpen_iff.1 hU z hzU
    obtain ⟨c, hcW, hdist⟩ := Metric.mem_closure_iff.1 hcl (ρ / 2) (by positivity)
    have hsub : Metric.ball c (ρ / 2) ⊆ U := by
      intro w hw
      apply hball
      rw [Metric.mem_ball] at hw ⊢
      have := dist_triangle w c z
      rw [dist_comm c z] at this
      linarith
    have hz := eq_zero_on_ball_of_eventually_zero (hdiff.mono hsub) (by positivity) hcW
    have hzc : z ∈ Metric.ball c (ρ / 2) := by
      rw [Metric.mem_ball]
      exact hdist
    exact Filter.eventually_of_mem (Metric.isOpen_ball.mem_nhds hzc) hz
  intro z hz
  have hsub : U ⊆ W :=
    hconn.isPreconnected.subset_of_closure_inter_subset hWo ⟨_, hmem₀, hbase⟩ hclosed
  exact (hsub hz).self_of_nhds
theorem differentiableOn_upperHalfPlane_of_isHolomorphicIn {f : ℂ → ℂ}
    (hf : IsHolomorphicIn (N' := 1) upperHalfPlaneCoords (fun z _ => f (z 0))) :
    DifferentiableOn ℂ f {z | 0 < z.im} := by
  intro w hw
  have hmem : (fun _ : Fin 1 => w) ∈ upperHalfPlaneCoords := hw
  have hd := (hf.2.2 _ hmem 0).self_of_nhds
  have hd0 := (differentiableAt_pi.1 hd) 0
  have heq : (fun ζ : ℂ => ((fun z (_ : Fin 1) => f (z 0))
      ((fun _ : Fin 1 => w) + ζ • stdBasisVector (0 : Fin 1))) 0) = fun ζ => f (w + ζ) := by
    funext ζ
    simp [stdBasisVector]
  rw [heq] at hd0
  have hshift : DifferentiableAt ℂ (fun z : ℂ => z - w) w := by fun_prop
  have hcomp : DifferentiableAt ℂ ((fun ζ => f (w + ζ)) ∘ fun z : ℂ => z - w) w :=
    DifferentiableAt.comp w (by simpa using hd0) hshift
  have heq2 : ((fun ζ => f (w + ζ)) ∘ fun z : ℂ => z - w) = f := by
    funext z
    simp
  rw [heq2] at hcomp
  exact hcomp.differentiableWithinAt
theorem eq_zero_of_eq_zero_on_real_axis {f : ℂ → ℂ} (hcont : ContinuousOn f {z | 0 ≤ z.im})
    (hdiff : DifferentiableOn ℂ f {z | 0 < z.im}) (hreal : ∀ z : ℂ, z.im = 0 → f z = 0)
    (w : ℂ) (hw : 0 < w.im) : f w = 0 := by
  set a : ℝ := w.re with ha
  set b : ℝ := w.im with hb
  set A : ℝ := 2 * b + 1 with hA
  set C : ℝ := 4 * b + 3 with hC
  let g : ℂ → ℝ := fun z => A ^ 2 - (z.re - a) ^ 2 + z.im ^ 2 - C * z.im
  let ψ : ℂ → ℂ := fun z =>
    ((A : ℂ)) ^ 2 - (z - (a : ℂ)) ^ 2 + Complex.I * (C : ℂ) * (z - (a : ℂ))
  have hψre : ∀ z, (ψ z).re = g z := by
    intro z
    simp only [ψ, g, pow_two, Complex.add_re, Complex.sub_re, Complex.mul_re, Complex.I_re,
      Complex.I_im, Complex.ofReal_re, Complex.ofReal_im, Complex.mul_im, Complex.sub_im]
    ring
  have hgc : Continuous g := by
    simp only [g]
    fun_prop
  have hψd : Differentiable ℂ ψ := by
    simp only [ψ]
    fun_prop
  let Ω : Set ℂ := {z | 0 < z.im ∧ 0 < g z ∧ z.im < C / 2}
  let T : Set ℂ := {z | 0 ≤ z.im ∧ 0 ≤ g z ∧ z.im ≤ C / 2}
  let S : Set ℂ := Icc (a - A) (a + A) ×ℂ Icc 0 (C / 2)
  have hΩo : IsOpen Ω := by
    have h1 : IsOpen {z : ℂ | 0 < z.im} := isOpen_lt continuous_const Complex.continuous_im
    have h2 : IsOpen {z : ℂ | 0 < g z} := isOpen_lt continuous_const hgc
    have h3 : IsOpen {z : ℂ | z.im < C / 2} := isOpen_lt Complex.continuous_im continuous_const
    exact h1.inter (h2.inter h3)
  have hTc : IsClosed T := by
    have h1 : IsClosed {z : ℂ | 0 ≤ z.im} := isClosed_le continuous_const Complex.continuous_im
    have h2 : IsClosed {z : ℂ | 0 ≤ g z} := isClosed_le continuous_const hgc
    have h3 : IsClosed {z : ℂ | z.im ≤ C / 2} := isClosed_le Complex.continuous_im continuous_const
    exact h1.inter (h2.inter h3)
  have hΩT : Ω ⊆ T := fun z hz => ⟨hz.1.le, hz.2.1.le, hz.2.2.le⟩
  have hApos : 0 < A := by positivity
  have hTS : T ⊆ S := by
    rintro z ⟨h1, h2, h3⟩
    have hsq : (z.re - a) ^ 2 ≤ A ^ 2 := by
      simp only [g] at h2
      nlinarith
    have habs := abs_le_of_sq_le_sq' hsq hApos.le
    refine ⟨⟨?_, ?_⟩, ⟨h1, h3⟩⟩
    · linarith [habs.1]
    · linarith [habs.2]
  have hScpt : IsCompact S := isCompact_Icc.reProdIm isCompact_Icc
  have hSup : S ⊆ {z | 0 ≤ z.im} := fun z hz => hz.2.1
  have hclT : closure Ω ⊆ T := closure_minimal hΩT hTc
  have hwΩ : w ∈ Ω := by
    refine ⟨hw, ?_, ?_⟩
    · simp only [g, ← ha, ← hb, sub_self]
      rw [hA, hC]
      nlinarith
    · rw [hC, ← hb]
      linarith
  obtain ⟨M, hM⟩ := hScpt.exists_bound_of_continuousOn (hcont.mono hSup)
  have hMnn : 0 ≤ M := (norm_nonneg _).trans (hM w (hTS (hΩT hwΩ)))
  have hbound : ∀ K : ℕ, ‖f w‖ * Real.exp (K * g w) ≤ M := by
    intro K
    let F : ℂ → ℂ := fun z => f z * Complex.exp (K * ψ z)
    have hΩb : Bornology.IsBounded Ω := hScpt.isBounded.subset (hΩT.trans hTS)
    have hexp : Differentiable ℂ fun z => Complex.exp (K * ψ z) := by fun_prop
    have hdc : DiffContOnCl ℂ F Ω := by
      refine ⟨?_, ?_⟩
      · exact (hdiff.mono fun z hz => hz.1).mul hexp.differentiableOn
      · exact (hcont.mono ((hclT.trans hTS).trans hSup)).mul hexp.continuous.continuousOn
    have hfr : ∀ z ∈ frontier Ω, ‖F z‖ ≤ M := by
      intro z hz
      rw [hΩo.frontier_eq] at hz
      obtain ⟨hzc, hzn⟩ := hz
      obtain ⟨t1, t2, t3⟩ := hclT hzc
      rcases t1.eq_or_lt with hy | hy
      · simp [F, hreal z hy.symm, hMnn]
      · have hg : g z ≤ 0 := by
          by_contra hpos
          have hpos' : 0 < g z := not_le.1 hpos
          have htop : z.im = C / 2 := by
            by_contra hne
            exact hzn ⟨hy, hpos', lt_of_le_of_ne t3 hne⟩
          have hsq : 0 ≤ (z.re - a) ^ 2 := sq_nonneg _
          simp only [g] at hpos'
          rw [htop] at hpos'
          rw [hA, hC] at hpos'
          nlinarith
        have hn : ‖Complex.exp (K * ψ z)‖ ≤ 1 := by
          rw [Complex.norm_exp]
          have : ((K : ℂ) * ψ z).re = K * g z := by
            simp [hψre]
          rw [this]
          apply Real.exp_le_one_iff.2
          exact mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg K) hg
        calc ‖F z‖ = ‖f z‖ * ‖Complex.exp (K * ψ z)‖ := norm_mul _ _
          _ ≤ M * 1 := mul_le_mul (hM z (hTS (hclT hzc))) hn (norm_nonneg _) hMnn
          _ = M := mul_one M
    have hmain := Complex.norm_le_of_forall_mem_frontier_norm_le hΩb hdc hfr
      (subset_closure hwΩ)
    have heq : ‖F w‖ = ‖f w‖ * Real.exp (K * g w) := by
      simp only [F, norm_mul, Complex.norm_exp]
      congr 2
      simp [hψre]
    rwa [heq] at hmain
  by_contra hne
  have hn : 0 < ‖f w‖ := norm_pos_iff.2 hne
  have hδ : 0 < g w := hwΩ.2.1
  obtain ⟨K, hK⟩ := exists_nat_gt (M / (‖f w‖ * g w))
  have h1 := hbound K
  have h2 : (K : ℝ) * g w + 1 ≤ Real.exp (K * g w) := Real.add_one_le_exp _
  rw [div_lt_iff₀ (by positivity)] at hK
  have h3 : ‖f w‖ * ((K : ℝ) * g w + 1) ≤ ‖f w‖ * Real.exp (K * g w) :=
    mul_le_mul_of_nonneg_left h2 hn.le
  nlinarith
theorem identityTheoremsProdAndUpperHalfPlane_of_powerSeriesHolomorphy
    (hps : PowerSeriesHolomorphy.Properties) : IdentityTheoremsProdAndUpperHalfPlane := by
  refine ⟨?_, ?_⟩
  · intro n m _ U f x₀ y₀ hU hconn hf hmem₀ hx₀ hvanish
    exact eq_zero_of_eventually_zero_on_realLocus hps n m U f x₀ y₀ hU hconn hf hmem₀ hx₀ hvanish
  · intro f hcont hf hreal z hz
    rcases hz.eq_or_lt with hy | hy
    · exact hreal z hy.symm
    · exact eq_zero_of_eq_zero_on_real_axis hcont
        (differentiableOn_upperHalfPlane_of_isHolomorphicIn hf) hreal z hy
end YangMills.Construction.ComplexAnalysis
