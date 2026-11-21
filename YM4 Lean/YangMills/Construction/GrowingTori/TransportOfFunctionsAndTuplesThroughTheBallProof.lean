import YangMills.Construction.GrowingTori.TransportOfFunctionsAndTuplesThroughTheBall
import YangMills.Construction.SourcesAndGluing.TransportToATorus
import YangMills.Construction.Torus.CoveringMapOnSmallBalls
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open Set TorusMetric TestFunctions TorusPeriodization
open SourcesAndGluing (ballR4)
open BallPeriodization (IsPeriodizableInBall)
open scoped ENNReal Topology
namespace PeriodizationThroughBall
def gluingSetupOf (D : PeriodicSpace.Params) : SourcesAndGluing.GluingSetup :=
  ⟨⟨D.L, D.isAdmissible, 1, D.m⟩, 1, one_pos, 0⟩
variable {D : PeriodicSpace.Params} {ρ : ℝ}
theorem two_mul_add_two_le_pow (hr : ρ ≤ BallPeriodization.ballRadius D) :
    2 * ρ + 2 ≤ (D.L : ℝ) ^ (D.m : ℕ) := by
  have h₁ : BallPeriodization.ballRadius D = D.side / 4 - 1 := rfl
  have hs : D.side = 2 * (D.L : ℝ) ^ (D.m : ℕ) := rfl
  rw [h₁, hs] at hr
  linarith
theorem lt_side_div_two (hρ : 0 < ρ) (hr : ρ ≤ BallPeriodization.ballRadius D) :
    ρ < D.side / 2 := by
  have h₁ : BallPeriodization.ballRadius D = D.side / 4 - 1 := rfl
  rw [h₁] at hr
  linarith
theorem lt_side_div_four (hr : ρ ≤ BallPeriodization.ballRadius D) : ρ < D.side / 4 := by
  have h₁ : BallPeriodization.ballRadius D = D.side / 4 - 1 := rfl
  rw [h₁] at hr
  linarith
theorem ballPeriodization_facts (hg : SourcesAndGluing.TorusPeriodizationOfBall.Statement)
    (hρ : 0 < ρ) (hr : ρ ≤ BallPeriodization.ballRadius D) :
    SourcesAndGluing.TorusPeriodizationOfBall.ProjIsometricOnBall (gluingSetupOf D) D.m ρ ∧
      (∀ (𝕜 : Type) [RCLike 𝕜],
        SourcesAndGluing.TorusPeriodizationOfBall.BallPeriodizeValues (gluingSetupOf D) D.m ρ 𝕜 ∧
        SourcesAndGluing.TorusPeriodizationOfBall.BallPeriodizeLinear (gluingSetupOf D) D.m ρ 𝕜 ∧
        SourcesAndGluing.TorusPeriodizationOfBall.BallPeriodizeNormsAndRegularity (gluingSetupOf D)
          D.m ρ 𝕜 ∧
        SourcesAndGluing.TorusPeriodizationOfBall.BallPeriodizeSuppNear (gluingSetupOf D) D.m ρ 𝕜 ∧
        SourcesAndGluing.TorusPeriodizationOfBall.BallPeriodizeComp (gluingSetupOf D) D.m ρ 𝕜) ∧
      (∀ (𝕜 𝕜' : Type) [RCLike 𝕜] [RCLike 𝕜'],
        SourcesAndGluing.TorusPeriodizationOfBall.BallPeriodizeSuppDist (gluingSetupOf D) D.m ρ
          𝕜 𝕜') := by
  have h := hg (gluingSetupOf D) D.m ρ hρ (two_mul_add_two_le_pow hr)
  exact ⟨h.1, h.2.1, h.2.2.1⟩
section Functions
variable {𝕜 : Type} [RCLike 𝕜] {f : (Fin 4 → ℝ) → 𝕜}
theorem ballPeriodize_eq_periodize (hg : SourcesAndGluing.TorusPeriodizationOfBall.Statement)
    (hf : IsPeriodizableInBall D ρ f) :
    (gluingSetupOf D).ballPeriodize D.m ρ f = periodize D.side f := by
  have hv := ((ballPeriodization_facts hg hf.1 hf.2.1).2.1 𝕜).1 f hf.2.2
  funext u
  obtain ⟨x, rfl⟩ := torusProj_surjective D.side u
  exact (hv.2.1 x).trans (periodize_torusProj D.side f x).symm
end Functions
theorem torusDist_eq_ofReal (u v : D.Torus) :
    torusDist D u v = ENNReal.ofReal (torusEuclidNorm (u - v)) :=
  (BallPeriodization.ptInfDist_eq D .torus u v).trans
    (congrArg ENNReal.ofReal (BallPeriodization.quotDist_torus D u v))
theorem projectionOnBall (hg : SourcesAndGluing.TorusPeriodizationOfBall.Statement)
    (hs : TestFunctions.SmallBalls.CoveringOnSmallBalls) (hρ : 0 < ρ)
    (hr : ρ ≤ BallPeriodization.ballRadius D) : ProjectionOnBall D ρ := by
  obtain ⟨h₁, h₂, h₃, h₄⟩ := (ballPeriodization_facts hg hρ hr).1
  have hd := (hs D.side (BallPeriodization.side_pos D)).1
  refine ⟨fun x y => ?_, h₁, fun x hx y hy => ?_, h₃, h₄⟩
  · obtain ⟨⟨⟨k, hk⟩, hl⟩, hle, -⟩ := hd x y
    rw [torusDist_eq_ofReal]
    refine ⟨⟨⟨k, congrArg ENNReal.ofReal hk⟩, ?_⟩, ENNReal.ofReal_le_ofReal hle⟩
    rintro _ ⟨k', rfl⟩
    exact ENNReal.ofReal_le_ofReal (hl ⟨k', rfl⟩)
  · rw [torusDist_eq_ofReal]
    refine congrArg ENNReal.ofReal ?_
    exact ((gluingSetupOf D).torusDist_eq_torusEuclidNorm D.m _ _).symm.trans (h₂ x hx y hy)
theorem exists_mem_fundamentalCube_torusProj_eq (u : D.Torus) :
    ∃ y ∈ fundamentalCube D, torusProj D.side y = u := by
  have hp := BallPeriodization.side_pos D
  obtain ⟨x, rfl⟩ := torusProj_surjective D.side u
  refine ⟨x + latticeTranslate D.side (fun μ => -toIcoDiv hp (-D.side / 2) (x μ)), ?_,
    torusProj_add_latticeTranslate _ _ _⟩
  intro μ _
  have h := toIcoMod_mem_Ico hp (-D.side / 2) (x μ)
  have e : (x + latticeTranslate D.side (fun μ => -toIcoDiv hp (-D.side / 2) (x μ))) μ =
      toIcoMod hp (-D.side / 2) (x μ) := by
    simp only [Pi.add_apply, latticeTranslate, toIcoMod, zsmul_eq_mul]
    push_cast
    ring
  rw [e]
  refine ⟨h.1, h.2.trans_eq ?_⟩
  ring
theorem eq_of_mem_fundamentalCube_of_mem_ball (hρ : 0 < ρ)
    (hr : ρ ≤ BallPeriodization.ballRadius D)
    {y w : Fin 4 → ℝ} (hy : y ∈ fundamentalCube D) (hw : w ∈ ballR4 ρ)
    (h : torusProj D.side w = torusProj D.side y) : y = w := by
  have hp := BallPeriodization.side_pos D
  have hq := lt_side_div_four hr
  obtain ⟨k, rfl⟩ := exists_latticeTranslate_of_torusProj_eq h
  have hk : k = 0 := by
    funext μ
    have hb : |(y + latticeTranslate D.side k) μ| < ρ :=
      lt_of_le_of_lt (abs_apply_le_euclidNormVec _ μ) hw
    have hyμ := hy μ (mem_univ _)
    simp only [Pi.add_apply, latticeTranslate] at hb
    obtain ⟨hb₁, hb₂⟩ := abs_lt.1 hb
    by_contra hne
    have hne' : k μ ≠ 0 := hne
    rcases lt_or_gt_of_ne hne' with hlt | hgt
    · have h1 : (k μ : ℝ) ≤ -1 := by exact_mod_cast Int.le_sub_one_of_lt hlt
      nlinarith [hyμ.1, hyμ.2]
    · have h1 : (1 : ℝ) ≤ k μ := by exact_mod_cast hgt
      nlinarith [hyμ.1, hyμ.2]
  subst hk
  funext μ
  simp [latticeTranslate]
section Functions
variable {𝕜 : Type} [RCLike 𝕜] {f : (Fin 4 → ℝ) → 𝕜}
theorem periodize_torusProj_of_mem_fundamentalCube (hf : IsPeriodizableInBall D ρ f)
    {y : Fin 4 → ℝ} (hy : y ∈ fundamentalCube D) :
    periodize D.side f (torusProj D.side y) = f y := by
  by_cases hb : y ∈ ballR4 ρ
  · exact hf.periodize_torusProj_of_mem hb
  · have h0 : f y = 0 := by
      by_contra hne
      exact hb (hf.support_subset hne)
    rw [h0]
    refine hf.periodize_eq_zero ?_
    rintro ⟨w, hw, hwy⟩
    exact hb ((eq_of_mem_fundamentalCube_of_mem_ball hf.1 hf.2.1 hy hw hwy) ▸ hw)
theorem periodizeValues (hg : SourcesAndGluing.TorusPeriodizationOfBall.Statement) (hρ : 0 < ρ)
    (hr : ρ ≤ BallPeriodization.ballRadius D) : PeriodizeValues D ρ 𝕜 := by
  intro f hf
  obtain ⟨hv₁, -, hv₃, -, -⟩ := ((ballPeriodization_facts hg hρ hr).2.1 𝕜).1 f hf.2.2
  have hbt := ballPeriodize_eq_periodize hg hf
  refine ⟨fun x k hk k' hk' => hv₃ x k k' hk hk', fun x x' hxx => ?_,
    fun x => periodize_torusProj D.side f x, fun g => ?_, fun ρ' hf' =>
      ⟨fun x hx => hf'.periodize_torusProj_of_mem hx, fun u hu => hf'.periodize_eq_zero hu⟩,
    fun S hS hd => ?_, fun g => ?_⟩
  · exact (periodize_torusProj D.side f x).symm.trans
      ((congrArg _ hxx).trans (periodize_torusProj D.side f x'))
  · exact (hv₁ g).trans (by rw [hbt]; exact Iff.rfl)
  · have hsup : Function.support f ⊆ S := subset_closure.trans hS
    have hz : ∀ x ∈ S, ∀ k : Fin 4 → ℤ, k ≠ 0 → f (x + latticeTranslate D.side k) = 0 := by
      intro x hx k hk
      by_contra hne
      have hd' := hd _ (hsup hne) _ hx
      rw [add_sub_cancel_left] at hd'
      have hpos := BallPeriodization.side_pos D
      obtain ⟨μ, hμ⟩ := Function.ne_iff.mp hk
      have h1 : (1 : ℝ) ≤ |(k μ : ℝ)| := by
        have hμ' : k μ ≠ 0 := hμ
        exact_mod_cast Int.one_le_abs hμ'
      have h2 := abs_apply_le_euclidNormVec (latticeTranslate D.side k) μ
      simp only [latticeTranslate, abs_mul, abs_of_pos hpos] at h2
      nlinarith
    refine ⟨⟨hd, hsup⟩, fun x hx => ?_, fun u hu => ?_⟩
    · rw [periodize_torusProj, periodicSum, tsum_eq_single 0 (fun k hk => hz x hx k hk)]
      have h0 : latticeTranslate D.side 0 = 0 := by
        funext μ
        simp [latticeTranslate]
      rw [h0, add_zero]
    · obtain ⟨x, rfl⟩ := torusProj_surjective D.side u
      have hz' : ∀ k, f (x + latticeTranslate D.side k) = 0 := by
        intro k
        by_contra hne
        exact hu ⟨_, hsup hne, torusProj_add_latticeTranslate D.side x k⟩
      rw [periodize_torusProj, periodicSum]
      simp [hz']
  · constructor
    · intro h
      funext u
      obtain ⟨y, hy, rfl⟩ := exists_mem_fundamentalCube_torusProj_eq u
      rw [h y hy, periodize_torusProj_of_mem_fundamentalCube hf hy]
    · rintro rfl y hy
      exact periodize_torusProj_of_mem_fundamentalCube hf hy
theorem periodizeLinear (hg : SourcesAndGluing.TorusPeriodizationOfBall.Statement) (hρ : 0 < ρ)
    (hr : ρ ≤ BallPeriodization.ballRadius D) : PeriodizeLinear D ρ 𝕜 := by
  intro f h c' c'' hf hh
  have h₁ := ((ballPeriodization_facts hg hρ hr).2.1 𝕜).2.1 f h c' c'' hf.2.2 hh.2.2
  have hc : IsPeriodizableInBall D ρ (c' • f + c'' • h) := ⟨hρ, hr, h₁.1⟩
  refine ⟨hc, ?_⟩
  rw [← ballPeriodize_eq_periodize hg hc, ← ballPeriodize_eq_periodize hg hf,
    ← ballPeriodize_eq_periodize hg hh]
  exact h₁.2
theorem periodizeNorms (hg : SourcesAndGluing.TorusPeriodizationOfBall.Statement) (hρ : 0 < ρ)
    (hr : ρ ≤ BallPeriodization.ballRadius D) : PeriodizeNorms D ρ 𝕜 := by
  intro f hf hl
  have h₁ := (((ballPeriodization_facts hg hρ hr).2.1 𝕜).2.2.1 f hf.2.2).1 hl
  rw [ballPeriodize_eq_periodize hg hf] at h₁
  obtain ⟨a, b, c, -⟩ := h₁
  have c' : lipConstTorus (periodize D.side f) = lipConstR4 f := c
  refine ⟨a, b, c', ?_⟩
  exact congrArg₂ max b (congrArg (fun t => 40 * D.M * t) c')
theorem periodizeComp (hg : SourcesAndGluing.TorusPeriodizationOfBall.Statement) (hρ : 0 < ρ)
    (hr : ρ ≤ BallPeriodization.ballRadius D) : PeriodizeComp D ρ 𝕜 := by
  intro f s hf hfs
  have h₁ := ((ballPeriodization_facts hg hρ hr).2.1 𝕜).2.2.2.2 f s hf.2.2 hfs.2.2
  rw [ballPeriodize_eq_periodize hg hf, ballPeriodize_eq_periodize hg hfs] at h₁
  exact h₁
end Functions
theorem torusEuclidNorm_sub_le (x y : Fin 4 → ℝ) :
    torusEuclidNorm (torusProj D.side x - torusProj D.side y) ≤ euclidNormVec (x - y) := by
  have hsub : torusProj D.side x - torusProj D.side y = torusProj D.side (x - y) := by
    funext μ
    simp [torusProj]
  rw [hsub]
  exact AmbientPoints.torusEuclidNorm_torusProj_le _
def projToPt (D : PeriodicSpace.Params) (x : Fin 4 → ℝ) :
    AmbientPoints.Pt (BallTuples.cutoffOneParams D) .torus := torusProj D.side x
theorem continuous_projToPt : Continuous (projToPt D) := by
  have hv : Continuous euclidNormVec := by
    unfold euclidNormVec
    fun_prop
  rw [continuous_iff_continuousAt]
  intro x
  refine tendsto_iff_dist_tendsto_zero.2 (squeeze_zero (g := fun y => euclidNormVec (y - x))
    (fun _ => dist_nonneg) (fun y => torusEuclidNorm_sub_le (D := D) y x) ?_)
  have h := (hv.comp (continuous_id.sub (continuous_const (y := x)))).tendsto x
  have h0 : euclidNormVec 0 = 0 := by simp [euclidNormVec]
  simpa [Function.comp_def, h0] using h
theorem isCompact_projToPt_image {Z : Set (Fin 4 → ℝ)} (hZ : IsCompact Z) :
    IsCompact (projToPt D '' Z) :=
  hZ.image continuous_projToPt
section Functions
variable {𝕜 : Type} [RCLike 𝕜] {f : (Fin 4 → ℝ) → 𝕜}
theorem torusSupp_periodize (hg : SourcesAndGluing.TorusPeriodizationOfBall.Statement)
    (hf : IsPeriodizableInBall D ρ f) :
    torusSupp D (periodize D.side f) = torusProj D.side '' euclidSupp f := by
  have h := (((ballPeriodization_facts hg hf.1 hf.2.1).2.1 𝕜).1 f hf.2.2).2.2.2.2
  rw [ballPeriodize_eq_periodize hg hf] at h
  exact h
theorem isCompactSubset_torusSupp (hg : SourcesAndGluing.TorusPeriodizationOfBall.Statement)
    (hf : IsPeriodizableInBall D ρ f) :
    (unitCutoffData D).IsCompactSubset (torusSupp D (periodize D.side f)) := by
  rw [torusSupp_periodize hg hf]
  exact (AmbientPoints.isCompact_iff_isCompactWrt _).1 (isCompact_projToPt_image hf.2.2.1)
theorem periodizeSupport (hg : SourcesAndGluing.TorusPeriodizationOfBall.Statement) (hρ : 0 < ρ)
    (hr : ρ ≤ BallPeriodization.ballRadius D) : PeriodizeSupport D ρ 𝕜 := by
  intro f hf
  have hs := torusSupp_periodize hg hf
  refine ⟨hs, isCompactSubset_torusSupp hg hf, lt_side_div_two hρ hr, ?_, fun R x hR hx => ?_⟩
  · rw [hs]
    rintro _ ⟨y, hy, rfl⟩
    have hy' : euclidNormVec y < ρ := hf.2.2.2 hy
    have h := torusEuclidNorm_sub_le (D := D) y 0
    rw [sub_zero] at h
    exact h.trans hy'.le
  · rw [hs]
    rintro _ ⟨y, hy, rfl⟩
    have hy' : euclidNormVec (y - x) ≤ R := hx hy
    change torusDist D (torusProj D.side y) (torusProj D.side x) ≤ ENNReal.ofReal R
    rw [torusDist_eq_ofReal]
    exact ENNReal.ofReal_le_ofReal ((torusEuclidNorm_sub_le y x).trans hy')
theorem periodizeSuppDist (hg : SourcesAndGluing.TorusPeriodizationOfBall.Statement) (hρ : 0 < ρ)
    (hr : ρ ≤ BallPeriodization.ballRadius D) (𝕜' : Type) [RCLike 𝕜'] :
    PeriodizeSuppDist D ρ 𝕜 𝕜' := by
  intro f h hf hh
  have hd := (ballPeriodization_facts hg hρ hr).2.2 𝕜 𝕜' f h hf.2.2 hh.2.2
  rw [ballPeriodize_eq_periodize hg hf, ballPeriodize_eq_periodize hg hh] at hd
  have hsf := torusSupp_periodize hg hf
  have hsh := torusSupp_periodize hg hh
  have hinj := (ballPeriodization_facts hg hρ hr).1.2.2.1
  refine ⟨hd, fun he => ?_, fun hdis => ?_⟩
  · rw [hsf, hsh]
    rcases he with he | he <;> simp [he, setEuclidDist, setDistR4]
  · rw [hsf, hsh, Set.disjoint_left]
    rintro _ ⟨x, hx, rfl⟩ ⟨y, hy, hxy⟩
    have hyx : y = x := hinj (hh.2.2.2 hy) (hf.2.2.2 hx) hxy
    exact Set.disjoint_left.1 hdis hx (hyx ▸ hy)
theorem partialDerivR4_eq_zero_of_notMem (μ : Fin 4) {x : Fin 4 → ℝ} (hx : x ∉ euclidSupp f) :
    partialDerivR4 μ f x = 0 := by
  have hopen : (euclidSupp f)ᶜ ∈ 𝓝 x := isClosed_closure.isOpen_compl.mem_nhds hx
  have hc : Filter.Tendsto (fun t : ℝ => x + t • Pi.single μ (1 : ℝ)) (𝓝 0) (𝓝 x) := by
    have h : Continuous fun t : ℝ => x + t • (Pi.single μ (1 : ℝ) : Fin 4 → ℝ) := by fun_prop
    simpa using h.tendsto 0
  have he : (fun t : ℝ => f (x + t • Pi.single μ (1 : ℝ))) =ᶠ[𝓝 0] fun _ => 0 := by
    refine (hc.eventually hopen).mono fun t ht => ?_
    by_contra hne
    exact ht (subset_closure hne)
  rw [partialDerivR4, he.deriv_eq, deriv_const]
theorem isPeriodizableInBall_partialDerivR4 (hf : IsPeriodizableInBall D ρ f) (μ : Fin 4) :
    IsPeriodizableInBall D ρ (partialDerivR4 μ f) := by
  have hsub : SourcesAndGluing.GluingSetup.suppR4 (partialDerivR4 μ f) ⊆
      SourcesAndGluing.GluingSetup.suppR4 f :=
    closure_minimal (fun x hx => by
      by_contra h
      exact hx (partialDerivR4_eq_zero_of_notMem μ h)) isClosed_closure
  exact ⟨hf.1, hf.2.1, hf.2.2.1.of_isClosed_subset isClosed_closure hsub, hsub.trans hf.2.2.2⟩
theorem partialDerivTorus_periodize (hf : IsPeriodizableInBall D ρ f) (μ : Fin 4) :
    BallPeriodization.partialDerivTorus D μ (periodize D.side f) =
      periodize D.side (partialDerivR4 μ f) := by
  funext u
  obtain ⟨x, rfl⟩ := torusProj_surjective D.side u
  have h₁ := congrFun (BallPeriodization.partialDerivTorus_comp_torusProj D μ
    (periodize D.side f)) x
  simp only [Function.comp_apply] at h₁
  rw [h₁]
  by_cases hx : torusProj D.side x ∈ torusProj D.side '' ballR4 ρ
  · obtain ⟨y, hy, hyx⟩ := hx
    have hyx' : torusProj D.side y = torusProj D.side x := hyx
    obtain ⟨k, hk⟩ := exists_latticeTranslate_of_torusProj_eq hyx'
    have hball : IsOpen (ballR4 ρ) := by
      have hv : Continuous euclidNormVec := by
        unfold euclidNormVec
        fun_prop
      exact isOpen_lt hv continuous_const
    have hc : Filter.Tendsto (fun t : ℝ => y + t • Pi.single μ (1 : ℝ)) (𝓝 0) (𝓝 y) := by
      have h : Continuous fun t : ℝ => y + t • (Pi.single μ (1 : ℝ) : Fin 4 → ℝ) := by fun_prop
      simpa using h.tendsto 0
    have he : (fun t : ℝ => (periodize D.side f ∘ torusProj D.side) (x + t • Pi.single μ (1 : ℝ)))
        =ᶠ[𝓝 0] fun t => f (y + t • Pi.single μ (1 : ℝ)) := by
      refine (hc.eventually (hball.mem_nhds hy)).mono fun t ht => ?_
      have hcov : torusProj D.side (x + t • Pi.single μ (1 : ℝ)) =
          torusProj D.side (y + t • Pi.single μ (1 : ℝ)) := by
        rw [hk, add_right_comm, torusProj_add_latticeTranslate]
      simp only [Function.comp_apply]
      rw [hcov]
      exact hf.periodize_torusProj_of_mem ht
    rw [← hyx', (isPeriodizableInBall_partialDerivR4 hf μ).periodize_torusProj_of_mem hy,
      partialDerivR4, he.deriv_eq, partialDerivR4]
  · rw [(isPeriodizableInBall_partialDerivR4 hf μ).periodize_eq_zero hx]
    have hcl : IsClosed (projToPt D '' euclidSupp f) :=
      (isCompact_projToPt_image hf.2.2.1).isClosed
    have hW : {z : Fin 4 → ℝ | torusProj D.side z ∉ torusProj D.side '' euclidSupp f} ∈ 𝓝 x := by
      refine (hcl.preimage continuous_projToPt).isOpen_compl.mem_nhds ?_
      rintro ⟨w, hw, hwx⟩
      exact hx ⟨w, hf.2.2.2 hw, hwx⟩
    have hc : Filter.Tendsto (fun t : ℝ => x + t • Pi.single μ (1 : ℝ)) (𝓝 0) (𝓝 x) := by
      have h : Continuous fun t : ℝ => x + t • (Pi.single μ (1 : ℝ) : Fin 4 → ℝ) := by fun_prop
      simpa using h.tendsto 0
    have he : (fun t : ℝ => (periodize D.side f ∘ torusProj D.side) (x + t • Pi.single μ (1 : ℝ)))
        =ᶠ[𝓝 0] fun _ => 0 := by
      refine (hc.eventually hW).mono fun t ht => ?_
      have hz : ∀ k, f (x + t • Pi.single μ (1 : ℝ) + latticeTranslate D.side k) = 0 := by
        intro k
        by_contra hne
        exact ht ⟨_, subset_closure hne, torusProj_add_latticeTranslate D.side _ k⟩
      simp only [Function.comp_apply]
      rw [periodize_torusProj, periodicSum]
      simp [hz]
    rw [partialDerivR4, he.deriv_eq, deriv_const]
theorem periodizeDeriv (hg : SourcesAndGluing.TorusPeriodizationOfBall.Statement) (hρ : 0 < ρ)
    (hr : ρ ≤ BallPeriodization.ballRadius D) : PeriodizeDeriv D ρ 𝕜 := by
  intro f hf hc
  have h₁ := (((ballPeriodization_facts hg hρ hr).2.1 𝕜).2.2.1 f hf.2.2).2.1 hc
  rw [ballPeriodize_eq_periodize hg hf] at h₁
  exact ⟨(BallPeriodization.isC1Torus_iff D _).2 h₁, fun μ =>
    ⟨isPeriodizableInBall_partialDerivR4 hf μ, partialDerivTorus_periodize hf μ⟩⟩
end Functions
theorem euclidNormVec_signedPermEuclidean (π : Equiv.Perm (Fin 4)) (σ : Fin 4 → ℤˣ)
    (v : Fin 4 → ℝ) :
    euclidNormVec (PeriodicLattice.CutoffTorus.signedPermEuclidean π σ v) = euclidNormVec v := by
  unfold euclidNormVec
  congr 1
  have h : ∀ μ, (PeriodicLattice.CutoffTorus.signedPermEuclidean π σ v μ) ^ 2 = v (π μ) ^ 2 := by
    intro μ
    simp only [PeriodicLattice.CutoffTorus.signedPermEuclidean]
    rcases Int.units_eq_one_or (σ μ) with h | h <;> simp [h]
  simp_rw [h]
  exact Equiv.sum_comp π fun ν => v ν ^ 2
theorem torusEuclidNorm_motion_le (hd : TestFunctions.SmallBalls.ProjDistFormula D.side)
    (s : euclideanMotions) (x y : Fin 4 → ℝ) :
    torusEuclidNorm (torusProj D.side ((s : Equiv.Perm (Fin 4 → ℝ)) x) -
        torusProj D.side ((s : Equiv.Perm (Fin 4 → ℝ)) y)) ≤
      torusEuclidNorm (torusProj D.side x - torusProj D.side y) := by
  obtain ⟨π, σ, v, h⟩ := s.2
  obtain ⟨⟨k, hk⟩, -⟩ := (hd x y).1
  have hw := (hd ((s : Equiv.Perm (Fin 4 → ℝ)) x) ((s : Equiv.Perm (Fin 4 → ℝ)) y)).1.2
    ⟨fun μ => (σ μ : ℤ) * k (π μ), rfl⟩
  refine hw.trans_eq ?_
  have e : (s : Equiv.Perm (Fin 4 → ℝ)) x - (s : Equiv.Perm (Fin 4 → ℝ)) y -
        latticeTranslate D.side (fun μ => (σ μ : ℤ) * k (π μ)) =
      PeriodicLattice.CutoffTorus.signedPermEuclidean π σ (x - y - latticeTranslate D.side k) := by
    funext μ
    simp only [h x, h y, Pi.sub_apply, Pi.add_apply,
      PeriodicLattice.CutoffTorus.signedPermEuclidean, latticeTranslate]
    push_cast
    ring
  simp only [e, euclidNormVec_signedPermEuclidean]
  exact hk
theorem descendedMotions (hs : TestFunctions.SmallBalls.CoveringOnSmallBalls) :
    DescendedMotions D := by
  have hd := (hs D.side (BallPeriodization.side_pos D)).1
  intro s
  have huniq : ∀ t : D.Torus → D.Torus,
      t ∘ torusProj D.side = torusProj D.side ∘ (s : Equiv.Perm (Fin 4 → ℝ)) →
        t = BallPeriodization.torusMap D s := by
    intro t ht
    funext u
    obtain ⟨x, rfl⟩ := torusProj_surjective D.side u
    exact (congrFun ht x).trans
      (congrFun (BallPeriodization.torusMap_comp_torusProj D s) x).symm
  refine ⟨⟨BallPeriodization.torusMap D s,
    BallPeriodization.torusMap_comp_torusProj D s, huniq⟩, fun t ht => ?_⟩
  obtain rfl := huniq t ht
  refine ⟨(BallPeriodization.torusMap D s).bijective, fun u v => ?_⟩
  obtain ⟨x, rfl⟩ := torusProj_surjective D.side u
  obtain ⟨y, rfl⟩ := torusProj_surjective D.side v
  rw [torusDist_eq_ofReal, torusDist_eq_ofReal]
  refine congrArg ENNReal.ofReal ?_
  have e : ∀ z, BallPeriodization.torusMap D s (torusProj D.side z) =
      torusProj D.side ((s : Equiv.Perm (Fin 4 → ℝ)) z) := torusMotion_torusProj D.side s
  rw [e, e]
  refine le_antisymm (torusEuclidNorm_motion_le hd s x y) ?_
  have h := torusEuclidNorm_motion_le hd s⁻¹ ((s : Equiv.Perm (Fin 4 → ℝ)) x)
    ((s : Equiv.Perm (Fin 4 → ℝ)) y)
  simpa using h
theorem periodizeTuples (hg : SourcesAndGluing.TorusPeriodizationOfBall.Statement) (hρ : 0 < ρ)
    (hr : ρ ≤ BallPeriodization.ballRadius D) (n : ℕ) : PeriodizeTuples D ρ n := by
  intro X hX
  have hent := hX.apply
  have hN := periodizeNorms (𝕜 := ℝ) hg hρ hr
  have hD := periodizeSuppDist (𝕜 := ℝ) hg hρ hr ℝ
  have hL := periodizeLinear (𝕜 := ℝ) hg hρ hr
  refine ⟨fun l => (hN _ (hent l) (hX.2.2.1.1 l)).1, fun l => isCompactSubset_torusSupp hg (hent l),
    fun l l' hl => (hD _ _ (hent l) (hent l')).2.2 (hX.2.2.1.2.2 l l' hl), ?_, fun J => rfl,
    fun _ => ?_, fun R hR hX' l => ?_, fun hm => ?_⟩
  · intro l g g' a b h₁ h₂ _
    have hg₁ : IsPeriodizableInBall D ρ g := by
      simpa using h₁.apply l
    have hg₂ : IsPeriodizableInBall D ρ g' := by
      simpa using h₂.apply l
    funext i
    by_cases hi : i = l
    · subst hi
      rw [BallTuples.periodize_apply, Function.update_self, Function.update_self]
      exact (hL g g' a b hg₁ hg₂).2
    · rw [BallTuples.periodize_apply, Function.update_of_ne hi, Function.update_of_ne hi,
        BallTuples.periodize_apply]
  · exact iInf_congr fun l => iInf_congr fun l' => iInf_congr fun _ =>
      (hD _ _ (hent l) (hent l')).1
  · obtain ⟨B, ⟨-, x, rfl⟩, hB⟩ := hX'.2 l
    refine ⟨torusProj D.side x, ?_⟩
    have hB' : euclidSupp (X l) ⊆ closedBallR4 x R := by
      have e := BallTuples.ambient_supp_euclidean D.L (X l)
      rw [e] at hB
      exact hB
    exact (periodizeSupport (𝕜 := ℝ) hg hρ hr (X l) (hent l)).2.2.2.2 R x hR hB'
  · obtain ⟨h₁, -, -⟩ := (BallTuples.mem_sepTuplesR4_iff X).1 hm.1
    have hts : ∀ l, tsupport (X := AmbientPoints.Pt (BallTuples.cutoffOneParams D) .torus)
        (BallTuples.periodize D X l) = torusSupp D (periodize D.side (X l)) :=
      fun l => AmbientPoints.closure_eq_closureWrt _
    refine ⟨fun i => ⟨?_, ?_⟩, fun i j hij => ?_⟩
    · have h := (periodizeDeriv (𝕜 := ℝ) hg hρ hr (X i) (hent i) (h₁ i)).1
      exact h
    · rw [hts i]
      exact (AmbientPoints.isCompact_iff_isCompactWrt _).2 (isCompactSubset_torusSupp hg (hent i))
    · exact (congrArg₂ Disjoint (hts i) (hts j)).mpr
        ((hD _ _ (hent i) (hent j)).2.2 (hX.2.2.1.2.2 i j hij))
theorem periodizationLemma_holds (hg : SourcesAndGluing.TorusPeriodizationOfBall.Statement)
    (hs : TestFunctions.SmallBalls.CoveringOnSmallBalls) : PeriodizationLemma := by
  intro D ρ hρ hr
  exact ⟨projectionOnBall hg hs hρ hr, fun 𝕜 _ =>
    ⟨periodizeValues hg hρ hr, periodizeLinear hg hρ hr, periodizeNorms hg hρ hr,
      periodizeSupport hg hρ hr, periodizeDeriv hg hρ hr,
      periodizeComp hg hρ hr⟩,
    fun 𝕜 𝕜' _ _ => periodizeSuppDist hg hρ hr 𝕜', descendedMotions hs,
    fun n _ => periodizeTuples hg hρ hr n⟩
end PeriodizationThroughBall
end YangMills.Construction
end
