import YangMills.Construction.Coordinates.PowerSeriesHolomorphy
import YangMills.Construction.OneLoopLaw.HolomorphicFunctionsWithACubicDifference
import Mathlib
set_option autoImplicit false
open Filter Asymptotics
open scoped Topology ContDiff
noncomputable section
namespace YangMills.Construction.OneLoopLaw.CubicAgreement
open YangMills.Construction.Coordinates.ConstancyOnConnected (IsHolomorphicScalarIn)
open YangMills.Construction.OneLoopLaw.TemperedStiffness (secondPartialAtZero)
open YangMills.Construction.PeriodicOperators (toComplexVec)
open YangMills.Construction.InfiniteLattice (AmbientSpace)
open YangMills.Construction.TorusMetric (euclidNormVec)
section Calculus
variable {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F]
theorem eventually_differentiableAt_of_contDiffAt_two {φ : E → F} (hφ : ContDiffAt ℝ 2 φ 0) :
    ∀ᶠ x in 𝓝 (0 : E), DifferentiableAt ℝ φ x :=
  (hφ.eventually (by simp)).mono fun _ hx => hx.differentiableAt (by norm_num)
theorem eventually_hasDerivAt_along_line {φ : E → F} (hφ : ContDiffAt ℝ 2 φ 0) (a b : E) :
    ∀ᶠ s : ℝ in 𝓝 0, HasDerivAt (fun t : ℝ => φ (s • a + t • b)) (fderiv ℝ φ (s • a) b) 0 := by
  have hc : Tendsto (fun s : ℝ => s • a) (𝓝 0) (𝓝 (0 : E)) := by
    have : Continuous fun s : ℝ => s • a := by fun_prop
    simpa using this.tendsto 0
  refine (hc.eventually (eventually_differentiableAt_of_contDiffAt_two hφ)).mono fun s hs => ?_
  have h1 : HasFDerivAt φ (fderiv ℝ φ (s • a)) (s • a + (0 : ℝ) • b) := by
    simpa using hs.hasFDerivAt
  have h2 : HasDerivAt (fun t : ℝ => s • a + t • b) b 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const b).const_add (s • a)
  exact h1.comp_hasDerivAt (0 : ℝ) h2
theorem hasDerivAt_iterated_directional {φ : E → F} (hφ : ContDiffAt ℝ 2 φ 0) (a b : E) :
    HasDerivAt (fun s : ℝ => deriv (fun t : ℝ => φ (s • a + t • b)) 0)
      (fderiv ℝ (fderiv ℝ φ) 0 a b) 0 := by
  have hd : DifferentiableAt ℝ (fderiv ℝ φ) 0 :=
    (hφ.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have h1 : HasFDerivAt (fderiv ℝ φ) (fderiv ℝ (fderiv ℝ φ) 0) ((0 : ℝ) • a) := by
    simpa using hd.hasFDerivAt
  have h2 : HasDerivAt (fun s : ℝ => s • a) a 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).smul_const a
  have h3 : HasDerivAt (fun s : ℝ => fderiv ℝ φ (s • a)) (fderiv ℝ (fderiv ℝ φ) 0 a) 0 :=
    h1.comp_hasDerivAt (0 : ℝ) h2
  have h4 : HasDerivAt (fun s : ℝ => fderiv ℝ φ (s • a) b) (fderiv ℝ (fderiv ℝ φ) 0 a b) 0 :=
    h3.clm_apply (hasDerivAt_const (0 : ℝ) b) |>.congr_deriv (by simp)
  exact h4.congr_of_eventuallyEq
    ((eventually_hasDerivAt_along_line hφ a b).mono fun s hs => hs.deriv)
end Calculus
theorem deriv_deriv_eq_zero_of_isBigO_cube {w : ℝ → ℂ} (hw : ContDiffAt ℝ 2 w 0)
    (hO : w =O[𝓝 0] fun r : ℝ => r ^ 3) : deriv (deriv w) 0 = 0 := by
  obtain ⟨U, hU, hUc⟩ := hw.contDiffOn (m := 2) le_rfl (by simp)
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 hU
  have hs : Convex ℝ (Metric.ball (0 : ℝ) ε) := convex_ball _ _
  have h0 : (0 : ℝ) ∈ Metric.ball (0 : ℝ) ε := Metric.mem_ball_self hε
  have hopen : IsOpen (Metric.ball (0 : ℝ) ε) := Metric.isOpen_ball
  have hT := taylor_isLittleO hs h0 (hUc.mono hball)
  rw [hopen.nhdsWithin_eq h0] at hT
  set B := Metric.ball (0 : ℝ) ε with hB
  have hc : iteratedDerivWithin 2 w B 0 = deriv (deriv w) 0 := by
    rw [iteratedDerivWithin_of_isOpen hopen h0, show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ,
      iteratedDeriv_one]
  rw [← hc]
  set c₂ := iteratedDerivWithin 2 w B 0 with hc₂
  set c₁ := iteratedDerivWithin 1 w B 0 with hc₁
  have hw0 : w 0 = 0 := by
    obtain ⟨C, hC⟩ := hO.bound
    simpa using hC.self_of_nhds
  have hval : ∀ x : ℝ, taylorWithinEval w 2 B 0 x = x • c₁ + (x ^ 2 / 2) • c₂ := by
    intro x
    simp [taylor_within_apply, hw0, ← hc₁, ← hc₂, div_eq_inv_mul]
    exact Or.inl (Or.inl (by norm_num))
  simp only [sub_zero] at hT
  have hA : (fun x : ℝ => w x - (x • c₁ + (x ^ 2 / 2) • c₂)) =o[𝓝 0] fun x : ℝ => x ^ 2 := by
    simpa only [hval] using hT
  have hneg : Tendsto (fun x : ℝ => -x) (𝓝 0) (𝓝 0) := by
    simpa using (continuous_neg (G := ℝ)).tendsto 0
  have hA' : (fun x : ℝ => w (-x) - ((-x) • c₁ + ((-x) ^ 2 / 2) • c₂)) =o[𝓝 0]
      fun x : ℝ => x ^ 2 := by
    simpa [Function.comp_def] using hA.comp_tendsto hneg
  have hW : w =o[𝓝 0] fun x : ℝ => x ^ 2 :=
    hO.trans_isLittleO (isLittleO_pow_pow (by norm_num))
  have hW' : (fun x : ℝ => w (-x)) =o[𝓝 0] fun x : ℝ => x ^ 2 := by
    simpa [Function.comp_def] using hW.comp_tendsto hneg
  have hsq : (fun x : ℝ => (x ^ 2) • c₂) =o[𝓝 0] fun x : ℝ => x ^ 2 := by
    refine ((hW.add hW').sub (hA.add hA')).congr_left fun x => ?_
    simp only [neg_smul, even_two, Even.neg_pow]
    have : (x ^ 2) • c₂ = (x ^ 2 / 2) • c₂ + (x ^ 2 / 2) • c₂ := by
      rw [← add_smul]; congr 1; ring
    rw [this]
    abel
  by_contra hne
  have hpos : 0 < ‖c₂‖ := norm_pos_iff.2 hne
  have hev := (isLittleO_iff.1 hsq) (c := ‖c₂‖ / 2) (by positivity)
  have hev' : ∀ᶠ x : ℝ in 𝓝[≠] 0, ‖(x ^ 2) • c₂‖ ≤ ‖c₂‖ / 2 * ‖x ^ 2‖ :=
    hev.filter_mono nhdsWithin_le_nhds
  obtain ⟨x, hx, hx0⟩ := (hev'.and self_mem_nhdsWithin).exists
  have hxp : 0 < ‖x ^ 2‖ := norm_pos_iff.2 (pow_ne_zero 2 hx0)
  rw [norm_smul] at hx
  nlinarith
theorem contDiffAt_two_realRestriction
    (H : YangMills.Construction.Coordinates.ComplexCoordinates.PowerSeriesHolomorphy.Properties)
    {U : Set (Fin 4 → ℂ)} {f : (Fin 4 → ℂ) → ℂ} (hU : IsOpen U) (h0 : 0 ∈ U)
    (hf : IsHolomorphicScalarIn U f) :
    ContDiffAt ℝ 2 (fun p : AmbientSpace => f (toComplexVec p)) 0 := by
  have h1 : ContDiffOn ℝ ∞ (fun z => (Equiv.funUnique (Fin 1) ℂ).symm (f z)) U :=
    ((H.1 4 U hU).1 1 _ hf).2.1
  have h2 : ContDiffOn ℝ ∞ f U := by
    have hp : ContDiff ℝ ∞ (fun v : Fin 1 → ℂ => v 0) := contDiff_apply ℝ ℂ (0 : Fin 1)
    exact (hp.comp_contDiffOn h1).congr fun z _ => by simp
  have hz : toComplexVec (0 : AmbientSpace) = 0 := by
    funext μ
    simp [toComplexVec]
  have h3 : ContDiffAt ℝ ∞ f (toComplexVec (0 : AmbientSpace)) :=
    h2.contDiffAt (hU.mem_nhds (by rwa [hz]))
  have h4 : ContDiff ℝ ∞ (toComplexVec : AmbientSpace → Fin 4 → ℂ) :=
    contDiff_pi.2 fun μ => Complex.ofRealCLM.contDiff.comp (contDiff_apply ℝ ℝ μ)
  exact (h3.comp (0 : AmbientSpace) h4.contDiffAt).of_le ENat.LEInfty.out
theorem secondPartialExists_and_eq_fderiv {g : (Fin 4 → ℂ) → ℂ}
    (hg : ContDiffAt ℝ 2 (fun p : AmbientSpace => g (toComplexVec p)) 0) (μ ν : Fin 4) :
    SecondPartialExists g μ ν ∧
      secondPartialAtZero g μ ν =
        fderiv ℝ (fderiv ℝ fun p : AmbientSpace => g (toComplexVec p)) 0
          (Pi.single μ 1) (Pi.single ν 1) := by
  have e : ∀ s t : ℝ, (Pi.single μ s + Pi.single ν t : AmbientSpace) =
      s • (Pi.single μ 1 : AmbientSpace) + t • (Pi.single ν 1 : AmbientSpace) := by
    intro s t
    funext i
    simp [Pi.single_apply]
  have hin := eventually_hasDerivAt_along_line hg (Pi.single μ 1) (Pi.single ν 1)
  have hout := hasDerivAt_iterated_directional hg (Pi.single μ 1) (Pi.single ν 1)
  refine ⟨⟨hin.mono fun s hs => ?_, ?_⟩, ?_⟩
  · simp only [e]
    exact hs.differentiableAt
  · simp only [e]
    exact hout.differentiableAt
  · simp only [secondPartialAtZero, e]
    exact hout.deriv
theorem fderiv_fderiv_eq_zero_of_isBigO_cube {φ : AmbientSpace → ℂ} (hφ : ContDiffAt ℝ 2 φ 0)
    (hO : φ =O[𝓝 0] fun p : AmbientSpace => euclidNormVec p ^ 3) (a b : AmbientSpace) :
    fderiv ℝ (fderiv ℝ φ) 0 a b = 0 := by
  have diag : ∀ v : AmbientSpace, fderiv ℝ (fderiv ℝ φ) 0 v v = 0 := by
    intro v
    have hw : ContDiffAt ℝ 2 (fun r : ℝ => φ (r • v)) 0 := by
      have h1 : ContDiffAt ℝ 2 φ ((0 : ℝ) • v) := by simpa using hφ
      have h2 : ContDiffAt ℝ 2 (fun r : ℝ => r • v) 0 := by fun_prop
      exact h1.comp (0 : ℝ) h2
    have hline : Tendsto (fun r : ℝ => r • v) (𝓝 0) (𝓝 (0 : AmbientSpace)) := by
      have : Continuous fun r : ℝ => r • v := by fun_prop
      simpa using this.tendsto 0
    have hscale : ∀ r : ℝ, euclidNormVec (r • v) = |r| * euclidNormVec v := by
      intro r
      have : ∑ μ, (r • v) μ ^ 2 = r ^ 2 * ∑ μ, v μ ^ 2 := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun μ _ => by simp [mul_pow]
      rw [euclidNormVec, euclidNormVec, this, Real.sqrt_mul (by positivity), Real.sqrt_sq_eq_abs]
    have hbig : (fun r : ℝ => φ (r • v)) =O[𝓝 0] fun r : ℝ => r ^ 3 := by
      refine (hO.comp_tendsto hline).trans (IsBigO.of_bound (euclidNormVec v ^ 3) ?_)
      refine Eventually.of_forall fun r => ?_
      simp only [Function.comp_apply, hscale, mul_pow, norm_mul, norm_pow, Real.norm_eq_abs,
        abs_abs]
      have hnn : 0 ≤ euclidNormVec v := Real.sqrt_nonneg _
      rw [abs_of_nonneg hnn, mul_comm]
    have hz := deriv_deriv_eq_zero_of_isBigO_cube hw hbig
    have hE : deriv (fun r : ℝ => φ (r • v)) =
        fun s : ℝ => deriv (fun t : ℝ => φ (s • v + t • v)) 0 := by
      funext s
      have h1 : (fun t : ℝ => φ (s • v + t • v)) =
          fun t : ℝ => (fun r : ℝ => φ (r • v)) (s + t) := by
        funext t
        simp only [add_smul]
      rw [h1]
      have h2 := deriv_comp_const_add (f := fun r : ℝ => φ (r • v)) (a := s) (x := 0)
      simpa using h2.symm
    rw [hE] at hz
    rw [← (hasDerivAt_iterated_directional hφ v v).deriv]
    exact hz
  have hs : IsSymmSndFDerivAt ℝ φ 0 := hφ.isSymmSndFDerivAt (by simp)
  have h1 := diag (a + b)
  simp only [map_add, add_apply, diag a, diag b, zero_add, add_zero] at h1
  rw [hs.eq b a] at h1
  have h2 : (2 : ℂ) * fderiv ℝ (fderiv ℝ φ) 0 a b = 0 := by
    rw [two_mul]
    exact h1
  simpa using h2
theorem secondPartialsAgree_of_powerSeries
    (H : YangMills.Construction.Coordinates.ComplexCoordinates.PowerSeriesHolomorphy.Properties) :
    SecondPartialsAgree := by
  intro U f g hU h0 hf hg hb μ ν
  have cf := contDiffAt_two_realRestriction H hU h0 hf
  have cg := contDiffAt_two_realRestriction H hU h0 hg
  obtain ⟨ff, ef⟩ := secondPartialExists_and_eq_fderiv cf μ ν
  obtain ⟨fg, eg⟩ := secondPartialExists_and_eq_fderiv cg μ ν
  refine ⟨ff, fg, ?_⟩
  rw [ef, eg]
  have ch : ContDiffAt ℝ 2
      (fun p : AmbientSpace => f (toComplexVec p) - g (toComplexVec p)) 0 :=
    cf.sub cg
  have hv := fderiv_fderiv_eq_zero_of_isBigO_cube ch hb (Pi.single μ 1) (Pi.single ν 1)
  have e : fderiv ℝ (fun p : AmbientSpace => f (toComplexVec p) - g (toComplexVec p)) =ᶠ[𝓝 0]
      fderiv ℝ (fun p : AmbientSpace => f (toComplexVec p)) -
        fderiv ℝ (fun p : AmbientSpace => g (toComplexVec p)) :=
    ((eventually_differentiableAt_of_contDiffAt_two cf).and
      (eventually_differentiableAt_of_contDiffAt_two cg)).mono
      fun x hx => fderiv_fun_sub hx.1 hx.2
  have dF : DifferentiableAt ℝ (fderiv ℝ fun p : AmbientSpace => f (toComplexVec p)) 0 :=
    (cf.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have dG : DifferentiableAt ℝ (fderiv ℝ fun p : AmbientSpace => g (toComplexVec p)) 0 :=
    (cg.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  rw [e.fderiv_eq, fderiv_sub dF dG] at hv
  simpa [sub_eq_zero] using hv
end YangMills.Construction.OneLoopLaw.CubicAgreement
end
