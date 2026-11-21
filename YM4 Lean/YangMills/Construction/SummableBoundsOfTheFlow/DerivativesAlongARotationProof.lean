import YangMills.Construction.ClusterExpansionOfAStep.LogarithmOfAMove
import YangMills.Construction.SummableBoundsOfTheFlow.DerivativesAlongAList
import YangMills.Construction.SummableBoundsOfTheFlow.DerivativesAlongARotation
import YangMills.Construction.SummableBoundsOfTheFlow.ExpansionAlongAMotion
import YangMills.Construction.SummableBoundsOfTheFlow.SmoothAlongAMotion
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion Topology
namespace YangMills.Construction.Estimates
open BlockAverages ColdStepAtMirrorFrames QuaternionLogarithm IteratedDerivative
variable {F : BlockFrame} {j k : ℕ}
private def toImaginaryCLM : ImaginaryCoord →L[ℝ] imaginaryQuaternions :=
  LinearMap.toContinuousLinearMap
    { toFun := toImaginary
      map_add' := fun v w => Subtype.ext (by
        rw [Submodule.coe_add]
        simp only [coe_toImaginary, map_add])
      map_smul' := fun a v => Subtype.ext (by
        rw [Submodule.coe_smul]
        simp only [coe_toImaginary, map_smul, RingHom.id_apply]) }
private theorem coe_toImaginaryCLM (v : ImaginaryCoord) :
    ((toImaginaryCLM v : imaginaryQuaternions) : ℍ[ℝ]) = imaginaryCLM v := rfl
private def bondGenerator (c : Fin k → F.Site j × Fin 4) (X : Fin k → imaginaryQuaternions)
    (q : F.Site j × Fin 4) (τ : Fin k → ℝ) : imaginaryQuaternions :=
  ColdStepAtMirrorFrames.bondSpread c X τ q.1 q.2
private theorem contDiff_bondGenerator (c : Fin k → F.Site j × Fin 4) (X : Fin k → imaginaryQuaternions)
    (q : F.Site j × Fin 4) : ContDiff ℝ 3 (bondGenerator c X q) := by
  unfold bondGenerator ColdStepAtMirrorFrames.bondSpread
  refine ContDiff.sum fun l _ => ?_
  split_ifs
  · exact (contDiff_apply ℝ ℝ l).smul contDiff_const
  · exact contDiff_const
private def relativeMove (c : Fin k → F.Site j × Fin 4) (X : Fin k → imaginaryQuaternions) (q : F.Site j × Fin 4)
    (z : (Fin k → ℝ) × (Fin k → ℝ)) : ℍ[ℝ] :=
  NormedSpace.exp ((bondGenerator c X q (z.1 + z.2) : imaginaryQuaternions) : ℍ[ℝ]) *
    NormedSpace.exp (-((bondGenerator c X q z.1 : imaginaryQuaternions) : ℍ[ℝ]))
private theorem contDiff_relativeMove (c : Fin k → F.Site j × Fin 4) (X : Fin k → imaginaryQuaternions)
    (q : F.Site j × Fin 4) : ContDiff ℝ 3 (relativeMove c X q) := by
  unfold relativeMove
  have he : ContDiff ℝ 3 (NormedSpace.exp : ℍ[ℝ] → ℍ[ℝ]) :=
    AnalyticOnNhd.contDiff fun x (_ : x ∈ Set.univ) => NormedSpace.exp_analytic x
  have hA := contDiff_bondGenerator c X q
  refine (he.comp (imaginaryQuaternions.subtypeL.contDiff.comp (hA.comp (contDiff_fst.add contDiff_snd)))).mul
    (he.comp (imaginaryQuaternions.subtypeL.contDiff.comp (hA.comp contDiff_fst)).neg)
private theorem relativeMove_zero (c : Fin k → F.Site j × Fin 4) (X : Fin k → imaginaryQuaternions)
    (q : F.Site j × Fin 4) (τ : Fin k → ℝ) : relativeMove c X q (τ, 0) = 1 := by
  simp only [relativeMove, add_zero]
  exact exp_mul_exp_neg _
private theorem relativeMove_mem_unitary (c : Fin k → F.Site j × Fin 4) (X : Fin k → imaginaryQuaternions)
    (q : F.Site j × Fin 4) (z : (Fin k → ℝ) × (Fin k → ℝ)) : relativeMove c X q z ∈ unitary ℍ[ℝ] :=
  (unitary ℍ[ℝ]).mul_mem (exp_imaginary_mem_unitary _) (exp_imaginary_mem_unitary (-(bondGenerator c X q z.1)))
private def moveLog (c : Fin k → F.Site j × Fin 4) (X : Fin k → imaginaryQuaternions) (q : F.Site j × Fin 4)
    (z : (Fin k → ℝ) × (Fin k → ℝ)) : imaginaryQuaternions :=
  toImaginaryCLM (localLog (relativeMove c X q z))
private theorem moveLog_zero (c : Fin k → F.Site j × Fin 4) (X : Fin k → imaginaryQuaternions)
    (q : F.Site j × Fin 4) (τ : Fin k → ℝ) : moveLog c X q (τ, 0) = 0 := by
  simp [moveLog, relativeMove_zero, localLog_one]
private theorem contDiffAt_moveLog (c : Fin k → F.Site j × Fin 4) (X : Fin k → imaginaryQuaternions)
    (q : F.Site j × Fin 4) (τ : Fin k → ℝ) : ContDiffAt ℝ 3 (moveLog c X q) (τ, 0) := by
  have h : ContDiffAt ℝ 3 localLog (relativeMove c X q (τ, 0)) := by
    rw [relativeMove_zero]
    exact contDiffAt_localLog
  exact toImaginaryCLM.contDiff.contDiffAt.comp _ (h.comp _ (contDiff_relativeMove c X q).contDiffAt)
private theorem expUnit_moveLog_mul (c : Fin k → F.Site j × Fin 4) (X : Fin k → imaginaryQuaternions)
    (q : F.Site j × Fin 4) (τ : Fin k → ℝ) :
    ∀ᶠ u in 𝓝 (0 : Fin k → ℝ),
      expUnit (moveLog c X q (τ, u)) * expUnit (bondGenerator c X q τ) = expUnit (bondGenerator c X q (τ + u)) := by
  have hz : Filter.Tendsto (fun u : Fin k → ℝ => (τ, u)) (𝓝 0) (𝓝 (τ, 0)) :=
    (Continuous.prodMk continuous_const continuous_id).tendsto' _ _ rfl
  have hc : Filter.Tendsto (fun u : Fin k → ℝ => relativeMove c X q (τ, u)) (𝓝 0) (𝓝 1) := by
    have := (contDiff_relativeMove c X q).continuous.continuousAt.tendsto.comp hz
    rwa [relativeMove_zero] at this
  filter_upwards [hc.eventually eventually_exp_localLog] with u hu
  apply Subtype.ext
  have h2 := hu (relativeMove_mem_unitary c X q (τ, u))
  show NormedSpace.exp (((moveLog c X q (τ, u) : imaginaryQuaternions)) : ℍ[ℝ]) *
    NormedSpace.exp ((bondGenerator c X q τ : imaginaryQuaternions) : ℍ[ℝ]) =
      NormedSpace.exp ((bondGenerator c X q (τ + u) : imaginaryQuaternions) : ℍ[ℝ])
  rw [moveLog, coe_toImaginaryCLM, h2, relativeMove, mul_assoc]
  have h3 : NormedSpace.exp (-((bondGenerator c X q τ : imaginaryQuaternions) : ℍ[ℝ])) *
      NormedSpace.exp ((bondGenerator c X q τ : imaginaryQuaternions) : ℍ[ℝ]) = 1 := by
    simpa using exp_mul_exp_neg (-((bondGenerator c X q τ : imaginaryQuaternions) : ℍ[ℝ]))
  simp only
  rw [h3, mul_one]
private def coordEmbedding {p : ℕ} (m : Fin p → Fin k) : (Fin p → ℝ) →L[ℝ] (Fin k → ℝ) :=
  ∑ i, (ContinuousLinearMap.proj i : (Fin p → ℝ) →L[ℝ] ℝ).smulRight (Pi.single (m i) (1 : ℝ))
private theorem coordEmbedding_single {p : ℕ} (m : Fin p → Fin k) (q : Fin p) :
    coordEmbedding m (Pi.single q 1) = Pi.single (m q) 1 := by
  simp [coordEmbedding, Pi.single_apply]
private theorem coordEmbedding_id (u : Fin k → ℝ) : coordEmbedding (fun i : Fin k => i) u = u := by
  funext a
  simp [coordEmbedding, Finset.sum_apply, Pi.single_apply]
private def motionAt (c : Fin k → F.Site j × Fin 4) (X : Fin k → imaginaryQuaternions) (τ : Fin k → ℝ) {p : ℕ}
    (m : Fin p → Fin k) (u : Fin p → ℝ) : F.Site j → Fin 4 → imaginaryQuaternions :=
  fun x b => moveLog c X (x, b) (τ, coordEmbedding m u)
private theorem motionAt_zero (c : Fin k → F.Site j × Fin 4) (X : Fin k → imaginaryQuaternions) (τ : Fin k → ℝ)
    {p : ℕ} (m : Fin p → Fin k) (x : F.Site j) (b : Fin 4) : motionAt c X τ m 0 x b = 0 := by
  simp [motionAt, moveLog_zero]
private theorem contDiffAt_motionAt (c : Fin k → F.Site j × Fin 4) (X : Fin k → imaginaryQuaternions)
    (τ : Fin k → ℝ) {p : ℕ} (m : Fin p → Fin k) (x : F.Site j) (b : Fin 4) :
    ContDiffAt ℝ 3 (fun u => motionAt c X τ m u x b) 0 := by
  have h := contDiffAt_moveLog c X (x, b) τ
  have hi : ContDiffAt ℝ 3 (fun u : Fin p → ℝ => (τ, coordEmbedding m u)) 0 :=
    (contDiff_const.prodMk (coordEmbedding m).contDiff).contDiffAt
  have e : (τ, coordEmbedding m (0 : Fin p → ℝ)) = (τ, 0) := by simp
  exact ContDiffAt.comp (0 : Fin p → ℝ) (e ▸ h) hi
private theorem leftTranslate_eq_motionAt (c : Fin k → F.Site j × Fin 4) (X : Fin k → imaginaryQuaternions)
    (W : F.GaugeField j) (τ : Fin k → ℝ) {p : ℕ} (m : Fin p → Fin k) (hfin : Finite (F.Site j)) :
    ∀ᶠ u in 𝓝 (0 : Fin p → ℝ), leftTranslate (bondSpread c X (τ + coordEmbedding m u)) W =
      leftTranslate (motionAt c X τ m u) (leftTranslate (bondSpread c X τ) W) := by
  have hz : Filter.Tendsto (coordEmbedding m) (𝓝 0) (𝓝 0) :=
    (coordEmbedding m).continuous.tendsto' _ _ (map_zero _)
  have hall : ∀ᶠ u in 𝓝 (0 : Fin p → ℝ), ∀ (x : F.Site j) (b : Fin 4),
      expUnit (moveLog c X (x, b) (τ, coordEmbedding m u)) * expUnit (bondGenerator c X (x, b) τ) =
        expUnit (bondGenerator c X (x, b) (τ + coordEmbedding m u)) := by
    rw [Filter.eventually_all]
    intro x
    rw [Filter.eventually_all]
    intro b
    exact hz.eventually (expUnit_moveLog_mul c X (x, b) τ)
  filter_upwards [hall] with u hu
  funext x b
  show expUnit (bondSpread c X (τ + coordEmbedding m u) x b) * W x b =
    expUnit (moveLog c X (x, b) (τ, coordEmbedding m u)) * (expUnit (bondSpread c X τ x b) * W x b)
  rw [← mul_assoc]
  exact congrArg (· * W x b) (hu x b).symm
private theorem norm_motionComponent_le (hA : DerivAlongRulesHold) (c : Fin k → F.Site j × Fin 4)
    (X : Fin k → imaginaryQuaternions) (τ : Fin k → ℝ) {p r : ℕ} (m : Fin p → Fin k) (e : Fin r → Fin p)
    (x : F.Site j) (b : Fin 4) {D : ℝ} (hr : r ≤ 3)
    (hD : ‖iteratedFDeriv ℝ r (moveLog c X (x, b)) (τ, 0)‖ ≤ D) :
    ‖motionComponent (motionAt c X τ m) e x b‖ ≤ D := by
  let Li : (Fin p → ℝ) →L[ℝ] (Fin k → ℝ) × (Fin k → ℝ) := (ContinuousLinearMap.inr ℝ _ _).comp (coordEmbedding m)
  have hr' : ((r : ℕ) : WithTop ℕ∞) ≤ 3 := by exact_mod_cast hr
  have hc : ContDiffAt ℝ r (moveLog c X (x, b)) (τ, 0) := (contDiffAt_moveLog c X _ τ).of_le hr'
  have hc' : ContDiffAt ℝ r (fun u => motionAt c X τ m u x b) 0 := (contDiffAt_motionAt c X τ m x b).of_le hr'
  let un : Fin r → (Fin p → ℝ) := fun l => Pi.single (e l) 1
  have e0 : ((τ, 0) : (Fin k → ℝ) × (Fin k → ℝ)) + Li 0 = (τ, 0) := by simp
  have h1 : motionComponent (motionAt c X τ m) e x b =
      iteratedFDeriv ℝ r (moveLog c X (x, b)) (τ, 0) fun l => Li (un l) := by
    have e1 : (fun u => motionAt c X τ m u x b) =
        fun t' => moveLog c X (x, b) (((τ, 0) : (Fin k → ℝ) × (Fin k → ℝ)) + Li t') := by
      funext u
      simp [motionAt, Li]
    have h2 := hA.2 ((Fin k → ℝ) × (Fin k → ℝ)) (Fin p → ℝ) imaginaryQuaternions (moveLog c X (x, b)) Li (τ, 0) 0
      (List.ofFn un) (by rw [e0, List.length_ofFn]; exact hc)
    unfold motionComponent
    rw [(hA.1 _ _).iteratedFDeriv_eq _ _ r un hc', e1, h2, e0, (hA.1 _ _).iteratedFDeriv_eq _ _ r _ hc,
      List.map_ofFn]
    rfl
  rw [h1]
  refine ((iteratedFDeriv ℝ r (moveLog c X (x, b)) (τ, 0)).le_opNorm _).trans ?_
  have hp : ∏ l, ‖Li (un l)‖ ≤ 1 := by
    refine Finset.prod_le_one (fun _ _ => norm_nonneg _) fun l _ => ?_
    have h3 : ‖(Pi.single (m (e l)) (1 : ℝ) : Fin k → ℝ)‖ ≤ 1 := by
      rw [Pi.norm_single]
      simp
    simpa [Li, un, coordEmbedding_single, Prod.norm_def] using h3
  calc ‖iteratedFDeriv ℝ r (moveLog c X (x, b)) (τ, 0)‖ * ∏ l, ‖Li (un l)‖
      ≤ ‖iteratedFDeriv ℝ r (moveLog c X (x, b)) (τ, 0)‖ * 1 := mul_le_mul_of_nonneg_left hp (norm_nonneg _)
    _ ≤ D := by simpa using hD
theorem contDiffBoundAlongTranslation_of_expansion (hE : expansionAlongMotionStatement) (hS : SmoothAlongMotion)
    (hA : DerivAlongRulesHold) : ContDiffBoundAlongTranslation := by
  intro F j k c X W hper
  have hne : ∀ i, NeZero (F.period j i) := fun i => ⟨hper i⟩
  have hfin : Finite (F.Site j) := Pi.finite
  let : Fintype (F.Site j × Fin 4) := Fintype.ofFinite _
  let T : Finset (F.Site j × Fin 4) := Finset.univ
  let D : ℝ := 1 + ∑ n : Fin 4, ∑ q : F.Site j × Fin 4, ‖iteratedFDeriv ℝ n (moveLog c X q) (0, 0)‖
  have hD1 : 0 ≤ D := by positivity
  have hev : ∀ᶠ τ in 𝓝 (0 : Fin k → ℝ), ∀ (n : Fin 4) (q : F.Site j × Fin 4),
      ‖iteratedFDeriv ℝ n (moveLog c X q) (τ, 0)‖ ≤ D := by
    rw [Filter.eventually_all]
    intro n
    rw [Filter.eventually_all]
    intro q
    have hn : (0 : WithTop ℕ∞) + ((n : ℕ) : WithTop ℕ∞) ≤ 3 := by
      rw [zero_add]
      exact_mod_cast Nat.le_of_lt_succ n.2
    have hc : ContinuousAt (iteratedFDeriv ℝ n (moveLog c X q)) ((0 : Fin k → ℝ), (0 : Fin k → ℝ)) :=
      ((contDiffAt_moveLog c X q 0).iteratedFDeriv_right (m := 0) hn).continuousAt
    have hz : ContinuousAt (fun τ : Fin k → ℝ => (τ, (0 : Fin k → ℝ))) 0 :=
      (Continuous.prodMk continuous_id continuous_const).continuousAt
    have h1 : ContinuousAt (fun τ : Fin k → ℝ => ‖iteratedFDeriv ℝ n (moveLog c X q) (τ, 0)‖) 0 :=
      (ContinuousAt.comp (f := fun τ : Fin k → ℝ => (τ, (0 : Fin k → ℝ))) hc hz).norm
    have hlt : ‖iteratedFDeriv ℝ n (moveLog c X q) ((0 : Fin k → ℝ), (0 : Fin k → ℝ))‖ < D := by
      have a1 : ‖iteratedFDeriv ℝ n (moveLog c X q) ((0 : Fin k → ℝ), (0 : Fin k → ℝ))‖ ≤
          ∑ q : F.Site j × Fin 4, ‖iteratedFDeriv ℝ n (moveLog c X q) (0, 0)‖ :=
        Finset.single_le_sum (f := fun q : F.Site j × Fin 4 => ‖iteratedFDeriv ℝ n (moveLog c X q) (0, 0)‖)
          (fun _ _ => norm_nonneg _) (Finset.mem_univ q)
      have a2 : ∑ q : F.Site j × Fin 4, ‖iteratedFDeriv ℝ n (moveLog c X q) (0, 0)‖ ≤
          ∑ n : Fin 4, ∑ q : F.Site j × Fin 4, ‖iteratedFDeriv ℝ n (moveLog c X q) (0, 0)‖ :=
        Finset.single_le_sum (f := fun n : Fin 4 => ∑ q : F.Site j × Fin 4,
          ‖iteratedFDeriv ℝ n (moveLog c X q) (0, 0)‖)
          (fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _) (Finset.mem_univ n)
      show _ < 1 + _
      linarith
    filter_upwards [h1.tendsto.eventually_lt_const hlt] with τ hτ using hτ.le
  obtain ⟨r₀, hr₀, hrb₀⟩ := Metric.eventually_nhds_iff_ball.1 hev
  let M : ℝ := ∑ p : Fin 4, ∑ cc : OrderedFinpartition (p : ℕ), ((T.card : ℝ) * D) ^ cc.length
  have hterm0 : ∀ (p : Fin 4) (cc : OrderedFinpartition (p : ℕ)), 0 ≤ ((T.card : ℝ) * D) ^ cc.length :=
    fun _ _ => pow_nonneg (mul_nonneg (Nat.cast_nonneg _) hD1) _
  have hM : 0 ≤ M := Finset.sum_nonneg fun p _ => Finset.sum_nonneg fun cc _ => hterm0 p cc
  refine ⟨r₀, M, hr₀, hM, fun r G R hr hR hG => ?_⟩
  have hrb : ∀ y ∈ Metric.ball (0 : Fin k → ℝ) r, ∀ (n : Fin 4) (q : F.Site j × Fin 4),
      ‖iteratedFDeriv ℝ n (moveLog c X q) (y, 0)‖ ≤ D := fun y hy =>
    hrb₀ y (Metric.ball_subset_ball hr hy)
  let g : (Fin k → ℝ) → ℝ := fun τ => G (leftTranslate (bondSpread c X τ) W)
  have hsmooth : ∀ τ ∈ Metric.ball (0 : Fin k → ℝ) r, ContDiffAt ℝ 3 g τ := by
    intro τ hτ
    have hm : ContDiffAt ℝ ((3 : ℕ) : WithTop ℕ∞)
        (fun u => G (leftTranslate (motionAt c X τ (fun i : Fin k => i) u) (leftTranslate (bondSpread c X τ) W))) 0 :=
      hS F j 3 k G _ _ hper (fun q c' X' => by exact_mod_cast (hG τ hτ).1 q c' X')
        (fun x b => by exact_mod_cast contDiffAt_motionAt c X τ (fun i : Fin k => i) x b)
        (fun x b => motionAt_zero c X τ _ x b)
    have he : (fun u => g (τ + u)) =ᶠ[𝓝 0]
        fun u => G (leftTranslate (motionAt c X τ (fun i : Fin k => i) u) (leftTranslate (bondSpread c X τ) W)) := by
      filter_upwards [leftTranslate_eq_motionAt c X W τ (fun i : Fin k => i) hfin] with u hu
      have e := coordEmbedding_id u
      simp only [g]
      rw [← hu, e]
    have h1 : ContDiffAt ℝ 3 (fun u => g (τ + u)) 0 := by
      have : ContDiffAt ℝ 3 (fun u => G (leftTranslate (motionAt c X τ (fun i : Fin k => i) u)
          (leftTranslate (bondSpread c X τ) W))) 0 := by exact_mod_cast hm
      exact this.congr_of_eventuallyEq he
    have h2 : ContDiffAt ℝ 3 (fun v => g (τ + (v - τ))) τ :=
      ContDiffAt.comp (g := fun u => g (τ + u)) (f := fun v => v - τ) τ
        (by show ContDiffAt ℝ 3 _ (τ - τ); rw [sub_self]; exact h1) (contDiff_id.sub contDiff_const).contDiffAt
    have e : (fun v => g (τ + (v - τ))) = g := by
      funext v
      rw [add_sub_cancel]
    rwa [e] at h2
  refine ⟨fun τ hτ => (hsmooth τ hτ).contDiffWithinAt, fun τ hτ n m hn => ?_⟩
  have hn' : ((n : ℕ) : WithTop ℕ∞) ≤ 3 := by exact_mod_cast hn
  have hg : ContDiffAt ℝ n g τ := (hsmooth τ hτ).of_le hn'
  let un : Fin n → (Fin n → ℝ) := fun l => Pi.single l 1
  have e0 : τ + coordEmbedding m 0 = τ := by simp
  have v1 : iteratedFDeriv ℝ n g τ (fun i => Pi.single (m i) 1) =
      iteratedFDeriv ℝ n (fun u => g (τ + coordEmbedding m u)) 0 un := by
    have hgc : ContDiffAt ℝ n (fun u => g (τ + coordEmbedding m u)) 0 :=
      ContDiffAt.comp (g := g) (f := fun u => τ + coordEmbedding m u) (0 : Fin n → ℝ)
        (by show ContDiffAt ℝ n g (τ + coordEmbedding m 0); rw [e0]; exact hg)
        (contDiff_const.add (coordEmbedding m).contDiff).contDiffAt
    have h2 := hA.2 (Fin k → ℝ) (Fin n → ℝ) ℝ g (coordEmbedding m) τ 0 (List.ofFn un)
      (by rw [e0, List.length_ofFn]; exact hg)
    rw [(hA.1 _ _).iteratedFDeriv_eq _ _ n un hgc, h2, e0, List.map_ofFn, (hA.1 _ _).iteratedFDeriv_eq _ _ n _ hg]
    congr 2
    funext q
    simp [un, coordEmbedding_single]
  have he : (fun u => g (τ + coordEmbedding m u)) =ᶠ[𝓝 0]
      fun u => G (leftTranslate (motionAt c X τ m u) (leftTranslate (bondSpread c X τ) W)) := by
    filter_upwards [leftTranslate_eq_motionAt c X W τ m hfin] with u hu
    simp only [g]
    rw [hu]
  obtain ⟨-, hform⟩ := hE.1 F j n G (leftTranslate (bondSpread c X τ) W) (motionAt c X τ m) hper
    (fun q c' X' => ((hG τ hτ).1 q c' X').of_le hn') (fun x b => (contDiffAt_motionAt c X τ m x b).of_le hn')
    (fun x b => motionAt_zero c X τ m x b)
  rw [v1, (Filter.EventuallyEq.iteratedFDeriv (𝕜 := ℝ) he n).eq_of_nhds]
  have hform' : iteratedFDeriv ℝ n
      (fun u => G (leftTranslate (motionAt c X τ m u) (leftTranslate (bondSpread c X τ) W))) 0 un =
      ∑ cc : OrderedFinpartition n, mixedDerivAlong G (leftTranslate (bondSpread c X τ) W)
        fun q => motionComponent (motionAt c X τ m) (cc.emb q) := hform
  rw [hform']
  have hterm : ∀ cc : OrderedFinpartition n,
      |mixedDerivAlong G (leftTranslate (bondSpread c X τ) W)
          fun q => motionComponent (motionAt c X τ m) (cc.emb q)| ≤
        R * ((T.card : ℝ) * D) ^ cc.length := by
    intro cc
    have hlen : cc.length ≤ 3 := cc.length_le.trans hn
    have hlen' : ((cc.length : ℕ) : WithTop ℕ∞) ≤ 3 := by exact_mod_cast hlen
    have hs := hE.2 F j cc.length G (leftTranslate (bondSpread c X τ) W)
      (fun q => motionComponent (motionAt c X τ m) (cc.emb q)) T (fun _ => R) hper (fun b => Finset.mem_univ b)
      (fun q c' X' => ((hG τ hτ).1 q c' X').of_le hlen') (fun b X' hX => (hG τ hτ).2 _ b X' hlen hX)
    refine hs.trans ?_
    have hp : ∀ b ∈ Fintype.piFinset fun _ : Fin cc.length => T,
        R * ∏ l, ‖motionComponent (motionAt c X τ m) (cc.emb l) (b l).1 (b l).2‖ ≤ R * D ^ cc.length := by
      intro b _
      refine mul_le_mul_of_nonneg_left ?_ hR
      calc ∏ l, ‖motionComponent (motionAt c X τ m) (cc.emb l) (b l).1 (b l).2‖ ≤ ∏ _l : Fin cc.length, D := by
            refine Finset.prod_le_prod (fun _ _ => norm_nonneg _) fun l _ => ?_
            have hps : cc.partSize l ≤ n := by
              have := Fintype.card_le_of_injective _ (cc.emb_strictMono l).injective
              simpa using this
            have hps3 : cc.partSize l < 4 := by omega
            exact norm_motionComponent_le hA c X τ m (cc.emb l) _ _ (by omega)
              (hrb τ hτ ⟨cc.partSize l, hps3⟩ (b l))
        _ = D ^ cc.length := by simp
    refine (Finset.sum_le_card_nsmul _ _ _ hp).trans (le_of_eq ?_)
    rw [Fintype.card_piFinset_const, nsmul_eq_mul, mul_pow]
    push_cast
    ring
  have hsum : (∑ cc : OrderedFinpartition n, ((T.card : ℝ) * D) ^ cc.length) ≤ M := by
    have hn4 : n < 4 := by omega
    exact Finset.single_le_sum
      (f := fun p : Fin 4 => ∑ cc : OrderedFinpartition (p : ℕ), ((T.card : ℝ) * D) ^ cc.length)
      (fun p _ => Finset.sum_nonneg fun cc _ => hterm0 p cc) (Finset.mem_univ (⟨n, hn4⟩ : Fin 4))
  calc |∑ cc : OrderedFinpartition n, mixedDerivAlong G (leftTranslate (bondSpread c X τ) W)
        fun q => motionComponent (motionAt c X τ m) (cc.emb q)|
      ≤ ∑ cc : OrderedFinpartition n, R * ((T.card : ℝ) * D) ^ cc.length :=
        (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun cc _ => hterm cc)
    _ = R * ∑ cc : OrderedFinpartition n, ((T.card : ℝ) * D) ^ cc.length := by rw [Finset.mul_sum]
    _ ≤ R * M := mul_le_mul_of_nonneg_left hsum hR
    _ = M * R := mul_comm _ _
end YangMills.Construction.Estimates
end
