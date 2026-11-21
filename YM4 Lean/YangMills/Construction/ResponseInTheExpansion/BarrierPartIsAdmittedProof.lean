import YangMills.Construction.ColdStepAtMirrorFrames.CompatibleLocalFamiliesGlue
import YangMills.Construction.ResponseInTheExpansion.BarrierPartIsAdmitted
import YangMills.Construction.ResponseInTheExpansion.MajorisedObservablesAreAdmitted
import Mathlib
set_option autoImplicit false
noncomputable section
open YangMills.Construction.BlockAverages YangMills.Construction.ColdStepAtMirrorFrames
open YangMills.Construction.TorusComparison YangMills.Construction.Interpolation
open YangMills.Construction.WeightedResponses Topology
namespace YangMills.Construction.ResponseInTheExpansion
variable {F : BlockFrame} {ι : Type} [Fintype ι] [DecidableEq ι]
private def radialDeriv (p : ℝ → ℝ) (e : BondVector) : ℝ := ‖e‖ * deriv p ‖e‖
private theorem radialDeriv_eq_zero_of_lt {ρ : ℝ} {p : ℝ → ℝ} (hρ : 0 < ρ) (hp : IsCutoff ρ p) {e : BondVector}
    (he : ‖e‖ < 5 * ρ / 8) : radialDeriv p e = 0 := by
  unfold radialDeriv
  rcases (norm_nonneg e).eq_or_lt with h | h
  · rw [← h, zero_mul]
  · have hz : p =ᶠ[𝓝 ‖e‖] fun _ => 0 := by
      filter_upwards [Ioo_mem_nhds h he] with u hu
      exact hp.vanish_small u hu.1.le hu.2.le
    rw [hz.deriv_eq]
    simp
private theorem radialDeriv_eventuallyEq_zero {ρ : ℝ} {p : ℝ → ℝ} (hρ : 0 < ρ) (hp : IsCutoff ρ p) :
    radialDeriv p =ᶠ[𝓝 (0 : BondVector)] fun _ => 0 := by
  have : Metric.ball (0 : BondVector) (5 * ρ / 8) ∈ 𝓝 (0 : BondVector) := Metric.ball_mem_nhds _ (by positivity)
  filter_upwards [this] with e he
  exact radialDeriv_eq_zero_of_lt hρ hp (by simpa using he)
private theorem contDiffAt_deriv_cutoff {ρ : ℝ} {p : ℝ → ℝ} (hp : IsCutoff ρ p) {u : ℝ} (h0 : 0 < u) (h1 : u < ρ) :
    ContDiffAt ℝ 2 (deriv p) u := by
  have hs : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) p (Set.Ioo 0 ρ) := hp.smooth.mono Set.Ioo_subset_Ico_self
  have hd : ContDiffOn ℝ 2 (deriv p) (Set.Ioo 0 ρ) := hs.deriv_of_isOpen isOpen_Ioo (by
    show ((3 : ℕ∞) : WithTop ℕ∞) ≤ _
    exact WithTop.coe_le_coe.2 le_top)
  exact hd.contDiffAt (Ioo_mem_nhds h0 h1)
private theorem radialDeriv_contDiffAt {ρ : ℝ} {p : ℝ → ℝ} (hρ : 0 < ρ) (hp : IsCutoff ρ p) {e : BondVector}
    (he : ‖e‖ < ρ) : ContDiffAt ℝ 1 (radialDeriv p) e := by
  by_cases h0 : e = 0
  · subst h0
    exact contDiffAt_const.congr_of_eventuallyEq (radialDeriv_eventuallyEq_zero hρ hp)
  · have hu : 0 < ‖e‖ := norm_pos_iff.2 h0
    have h1 : ContDiffAt ℝ 1 (fun u : ℝ => u * deriv p u) ‖e‖ :=
      contDiffAt_id.mul ((contDiffAt_deriv_cutoff hp hu he).of_le (by norm_num))
    exact h1.comp e (contDiffAt_norm ℝ h0)
private theorem norm_fderiv_radialDeriv_le {ρ : ℝ} {p : ℝ → ℝ} (hρ : 0 < ρ) (hp : IsCutoff ρ p) {e : BondVector}
    (he : ‖e‖ < ρ) :
    ‖fderiv ℝ (radialDeriv p) e‖ ≤ (1 + ρ) * (|deriv p ‖e‖| + |deriv (deriv p) ‖e‖|) := by
  have hr : 0 ≤ (1 + ρ) * (|deriv p ‖e‖| + |deriv (deriv p) ‖e‖|) := by positivity
  by_cases h0 : e = 0
  · subst h0
    rw [(radialDeriv_eventuallyEq_zero hρ hp).fderiv_eq]
    simpa using hr
  · have hu : 0 < ‖e‖ := norm_pos_iff.2 h0
    have hc := contDiffAt_deriv_cutoff hp hu he
    have hd1 : DifferentiableAt ℝ (deriv p) ‖e‖ := hc.differentiableAt (by norm_num)
    have hd2 : HasDerivAt (fun u : ℝ => u * deriv p u) (1 * deriv p ‖e‖ + ‖e‖ * deriv (deriv p) ‖e‖) ‖e‖ :=
      (hasDerivAt_id _).mul hd1.hasDerivAt
    have hn : HasFDerivAt (fun v : BondVector => ‖v‖) (fderiv ℝ (fun v : BondVector => ‖v‖) e) e :=
      ((contDiffAt_norm ℝ h0 : ContDiffAt ℝ 1 (fun v : BondVector => ‖v‖) e).differentiableAt (by norm_num)).hasFDerivAt
    have hf : HasFDerivAt (radialDeriv p)
        ((1 * deriv p ‖e‖ + ‖e‖ * deriv (deriv p) ‖e‖) • fderiv ℝ (fun v : BondVector => ‖v‖) e) e :=
      hd2.comp_hasFDerivAt e hn
    rw [hf.fderiv, norm_smul, Real.norm_eq_abs]
    have h1 : ‖fderiv ℝ (fun v : BondVector => ‖v‖) e‖ ≤ 1 := by
      have := norm_fderiv_le_of_lipschitz ℝ (x₀ := e) (lipschitzWith_one_norm (E := BondVector))
      simpa using this
    have h2 : |1 * deriv p ‖e‖ + ‖e‖ * deriv (deriv p) ‖e‖| ≤ (1 + ρ) * (|deriv p ‖e‖| + |deriv (deriv p) ‖e‖|) := by
      have a1 : |‖e‖ * deriv (deriv p) ‖e‖| ≤ ρ * |deriv (deriv p) ‖e‖| := by
        rw [abs_mul, abs_of_nonneg (norm_nonneg e)]
        exact mul_le_mul_of_nonneg_right he.le (abs_nonneg _)
      have a2 := abs_add_le (1 * deriv p ‖e‖) (‖e‖ * deriv (deriv p) ‖e‖)
      rw [one_mul] at a2 ⊢
      nlinarith [abs_nonneg (deriv p ‖e‖), abs_nonneg (deriv (deriv p) ‖e‖)]
    calc _ ≤ ((1 + ρ) * (|deriv p ‖e‖| + |deriv (deriv p) ‖e‖|)) * 1 := mul_le_mul h2 h1 (norm_nonneg _) hr
      _ = _ := mul_one _
private theorem bondGradNorm_finset_sum_le (S : Finset ι) (φ : BondVector → ℝ) (η : BondField ι)
    (hd : ∀ b ∈ S, DifferentiableAt ℝ φ (η b)) (b₀ : ι) {B : ℝ} (hB : 0 ≤ B)
    (h : b₀ ∈ S → ‖fderiv ℝ φ (η b₀)‖ ≤ B) :
    bondGradNorm (fun ζ : BondField ι => ∑ b ∈ S, φ (ζ b)) b₀ η ≤ B := by
  have hf : HasFDerivAt (fun ζ : BondField ι => ∑ b ∈ S, φ (ζ b))
      (∑ b ∈ S, (fderiv ℝ φ (η b)).comp (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι => BondVector) b)) η := by
    refine HasFDerivAt.fun_sum fun b hb => ?_
    exact (hd b hb).hasFDerivAt.comp η (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι => BondVector) b).hasFDerivAt
  unfold bondGradNorm
  rw [hf.fderiv]
  by_cases hb : b₀ ∈ S
  · have : (∑ b ∈ S, (fderiv ℝ φ (η b)).comp (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι => BondVector) b)).comp
        (ContinuousLinearMap.single ℝ (fun _ : ι => BondVector) b₀) = fderiv ℝ φ (η b₀) := by
      refine ContinuousLinearMap.ext fun v => ?_
      simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.sum_apply, ContinuousLinearMap.proj_apply,
        ContinuousLinearMap.single_apply]
      rw [Finset.sum_eq_single b₀]
      · simp
      · intro b _ hne
        simp [Pi.single_apply, hne]
      · exact fun h' => absurd hb h'
    rw [this]
    exact h hb
  · have : (∑ b ∈ S, (fderiv ℝ φ (η b)).comp (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι => BondVector) b)).comp
        (ContinuousLinearMap.single ℝ (fun _ : ι => BondVector) b₀) = 0 := by
      refine ContinuousLinearMap.ext fun v => ?_
      simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.sum_apply, ContinuousLinearMap.proj_apply,
        ContinuousLinearMap.single_apply, ContinuousLinearMap.zero_apply]
      refine Finset.sum_eq_zero fun b hb' => ?_
      have hne : b ≠ b₀ := fun e => hb (e ▸ hb')
      simp [Pi.single_apply, hne]
    rw [this]
    simpa using hB
private theorem cutoffTerm_eq_sum {Q : ColdHalfLaw} (Y : F.Cell) (η : StepVariable (finiteCells F)) (V : F.GaugeField F.top) :
    Q.cutoffTerm Y η V = open Classical in
      ∑ b ∈ Finset.univ.filter (fun b : ↥(chordBonds (finiteCells F)) => enclosingCell b.1.1 = Y), radialDeriv Q.cutoff (η b) := by
  classical
  unfold ColdHalfLaw.cutoffTerm ColdHalfLaw.sumOverBlock
  rw [← Finset.sum_filter]
  rfl
private theorem freezeOutside_apply_of_cell {q : ℕ} {Y : F.Cell} (η : StepVariable (finiteCells F))
    {b : ↥(chordBonds (finiteCells F))} (hb : enclosingCell b.1.1 = Y) : freezeOutside (bondsNearCell Y q) η b = η b := by
  have hz : cellSupDist Y Y = 0 := Nat.le_zero.1 (Finset.sup_le fun i _ => by simp)
  have hm : b ∈ bondsNearCell Y q := by
    unfold bondsNearCell
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    rw [hb, hz]
    simp
  unfold freezeOutside extendByZero
  rw [Finset.sum_eq_single b]
  · simp
  · intro b' _ hne
    simp [hne]
  · exact fun h => absurd hm h
private theorem cutoffTerm_isCutoffDominated {T : StepParameters} (hDr : T.IsOrdered) (x : ℝ) (f : LocalFamily) (q : ℕ)
    (Y : F.Cell) (V : F.GaugeField F.top) :
    IsCutoffDominated T.ballRadius T.κ (1 + T.ballRadius) T.p q Y (fun η => (coldHalfLawAt T x f).cutoffTerm Y η V) := by
  classical
  have hρ : 0 < T.ballRadius := by
    have := hDr.σ_pos
    show 0 < T.σ / 64
    positivity
  have hp : IsCutoff T.ballRadius T.p := hDr.cutoff
  set S := Finset.univ.filter (fun b : ↥(chordBonds (finiteCells F)) => enclosingCell b.1.1 = Y) with hS
  have e : (fun η => (coldHalfLawAt T x f).cutoffTerm Y η V) =
      fun η : StepVariable (finiteCells F) => ∑ b ∈ S, radialDeriv T.p (η b) := by
    funext η
    rw [cutoffTerm_eq_sum]
    exact Finset.sum_congr (by rw [hS]) fun _ _ => rfl
  have emaj : ∀ η : StepVariable (finiteCells F), cutoffMajorant T.p Y η =
      1 + ∑ b ∈ S, (|deriv T.p ‖η b‖| + |deriv (deriv T.p) ‖η b‖|) := fun η => by
    unfold cutoffMajorant ColdHalfLaw.sumOverBlock
    rw [← Finset.sum_filter]
  have hsn : ∀ η : StepVariable (finiteCells F), 0 ≤ ∑ b ∈ S, (|deriv T.p ‖η b‖| + |deriv (deriv T.p) ‖η b‖|) :=
    fun η => Finset.sum_nonneg fun b _ => by positivity
  rw [e]
  refine ⟨?_, fun η hη => ?_, fun η hη b => ?_, fun η hη => ?_⟩
  · refine ContDiffOn.sum fun b _ => ?_
    intro η hη
    have hpr : ContDiffAt ℝ 1 (fun ζ : StepVariable (finiteCells F) => ζ b) η :=
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ↥(chordBonds (finiteCells F)) => BondVector) b).contDiff.contDiffAt
    exact (ContDiffAt.comp (g := radialDeriv T.p) (f := fun ζ : StepVariable (finiteCells F) => ζ b) η
      (radialDeriv_contDiffAt hρ hp (hη b)) hpr).contDiffWithinAt
  · have h1 : ∀ b ∈ S, |radialDeriv T.p (η b)| ≤
        (1 + T.ballRadius) * (|deriv T.p ‖η b‖| + |deriv (deriv T.p) ‖η b‖|) := fun b _ => by
      unfold radialDeriv
      rw [abs_mul, abs_of_nonneg (norm_nonneg _)]
      have h2 := (hη b).le
      have h3 := abs_nonneg (deriv T.p ‖η b‖)
      have h4 := abs_nonneg (deriv (deriv T.p) ‖η b‖)
      have h5 := norm_nonneg (η b)
      nlinarith
    calc |∑ b ∈ S, radialDeriv T.p (η b)| ≤ ∑ b ∈ S, |radialDeriv T.p (η b)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ b ∈ S, (1 + T.ballRadius) * (|deriv T.p ‖η b‖| + |deriv (deriv T.p) ‖η b‖|) := Finset.sum_le_sum h1
      _ = (1 + T.ballRadius) * ∑ b ∈ S, (|deriv T.p ‖η b‖| + |deriv (deriv T.p) ‖η b‖|) := by rw [Finset.mul_sum]
      _ ≤ _ := by
        rw [emaj]
        exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  · have hB : 0 ≤ (1 + T.ballRadius) * Real.exp (-(2 * T.κ * bondDistToCell Y b)) * cutoffMajorant T.p Y η := by
      rw [emaj]
      have := hsn η
      positivity
    refine bondGradNorm_finset_sum_le S (radialDeriv T.p) η
      (fun b _ => (radialDeriv_contDiffAt hρ hp (hη b)).differentiableAt (by norm_num)) b hB fun hb => ?_
    have hcell : enclosingCell b.1.1 = Y := by simpa [hS] using hb
    have hz : cellSupDist Y Y = 0 := Nat.le_zero.1 (Finset.sup_le fun i _ => by simp)
    have hd : bondDistToCell Y b = 0 := by
      unfold bondDistToCell
      rw [hcell, hz]
      simp
    rw [hd]
    simp only [mul_zero, neg_zero, Real.exp_zero, mul_one]
    refine (norm_fderiv_radialDeriv_le hρ hp (hη b)).trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
    rw [emaj]
    have := Finset.single_le_sum (f := fun b => |deriv T.p ‖η b‖| + |deriv (deriv T.p) ‖η b‖|)
      (fun b _ => by positivity) hb
    linarith
  · have : ∑ b ∈ S, radialDeriv T.p (freezeOutside (bondsNearCell Y q) η b) = ∑ b ∈ S, radialDeriv T.p (η b) :=
      Finset.sum_congr rfl fun b hb => by
        rw [freezeOutside_apply_of_cell η (by simpa [hS] using hb)]
    rw [this, sub_self, abs_zero]
    positivity
theorem cutoffTermComparable_of_dominated (hJ : EventuallyInParametersCombines)
    (hM : DominatedObservablesComparable) : CutoffTermComparable := by
  obtain ⟨-, weaken⟩ := hJ
  refine weaken _ _ ?_ hM
  rintro T hDr ⟨C, hC, hT⟩
  intro t x f hfl hrow
  have hρ : 0 < T.ballRadius := by
    have := hDr.σ_pos
    show 0 < T.σ / 64
    positivity
  refine ⟨C * (1 + T.ballRadius), by positivity, ?_⟩
  intro F V V' Y q ι _ _ j htop hV hV' hag hpair
  exact hT t x f F V V' Y q ι j ((coldHalfLawAt T x f).cutoffTerm Y) (1 + T.ballRadius) hfl hrow htop hV hV' hpair
    (by positivity) (cutoffTerm_isCutoffDominated hDr x f q Y V) (cutoffTerm_isCutoffDominated hDr x f q Y V')
    fun _ ζ _ => by
      have : (coldHalfLawAt T x f).cutoffTerm Y (toTorus j ζ) V = (coldHalfLawAt T x f).cutoffTerm Y (toTorus j ζ) V' := rfl
      rw [this, sub_self, abs_zero]
      positivity
end YangMills.Construction.ResponseInTheExpansion
end
