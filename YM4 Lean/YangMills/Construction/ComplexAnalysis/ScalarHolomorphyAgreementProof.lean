import YangMills.Construction.ComplexAnalysis.ScalarHolomorphyAgreement
import YangMills.Construction.Coordinates.PowerSeriesHolomorphy
import Mathlib
open Filter Set
open scoped Topology
noncomputable section
namespace YangMills.Construction.BanachValued.ScalarAgreement
variable {n : ℕ}
theorem norm_monomial_le {ρ : ℝ} {w : Coordinates.ComplexCoordinates n} (hw : ‖w‖ ≤ ρ)
    (γ : YangMills.Construction.PowerSeries.MultiIndex n) :
    ‖YangMills.Construction.PowerSeries.MultiIndex.monomial w γ‖ ≤
      ρ ^ YangMills.Construction.PowerSeries.MultiIndex.order γ := by
  unfold YangMills.Construction.PowerSeries.MultiIndex.monomial
    YangMills.Construction.PowerSeries.MultiIndex.order
  rw [norm_prod, ← Finset.prod_pow_eq_pow_sum]
  refine Finset.prod_le_prod (fun i _ => norm_nonneg _) fun i _ => ?_
  rw [norm_pow]
  exact pow_le_pow_left₀ (norm_nonneg _) ((norm_le_pi_norm w i).trans hw) _
theorem norm_monomial_smul_le {ρ : ℝ} {a : YangMills.Construction.PowerSeries.MultiIndex n → ℂ}
    {w : Coordinates.ComplexCoordinates n} (hw : ‖w‖ ≤ ρ)
    (γ : YangMills.Construction.PowerSeries.MultiIndex n) :
    ‖YangMills.Construction.PowerSeries.MultiIndex.monomial w γ • a γ‖ ≤
      ‖a γ‖ * ρ ^ YangMills.Construction.PowerSeries.MultiIndex.order γ := by
  rw [norm_smul, mul_comm]
  exact mul_le_mul_of_nonneg_left (norm_monomial_le hw γ) (norm_nonneg _)
theorem continuous_monomial (γ : YangMills.Construction.PowerSeries.MultiIndex n) :
    Continuous fun w : Coordinates.ComplexCoordinates n =>
      YangMills.Construction.PowerSeries.MultiIndex.monomial w γ := by
  unfold YangMills.Construction.PowerSeries.MultiIndex.monomial
  fun_prop
theorem continuousAt_of_powerSeriesData {O : Set (Coordinates.ComplexCoordinates n)}
    {f : Coordinates.ComplexCoordinates n → ℂ} {c : Coordinates.ComplexCoordinates n} {ρ : ℝ}
    {a : YangMills.Construction.PowerSeries.MultiIndex n → ℂ}
    (h : YangMills.Construction.BanachValued.IsPowerSeriesDataAt O f c ρ a) :
    ContinuousAt f c := by
  have hsum : ContinuousOn (fun w : Coordinates.ComplexCoordinates n =>
      ∑' γ, YangMills.Construction.PowerSeries.MultiIndex.monomial w γ • a γ)
      (Metric.closedBall 0 ρ) := by
    refine continuousOn_tsum (fun γ => ((continuous_monomial γ).smul
      continuous_const).continuousOn) h.summable fun γ w hw => ?_
    exact norm_monomial_smul_le (by simpa using hw) γ
  have hnear : ContinuousAt (fun w : Coordinates.ComplexCoordinates n =>
      ∑' γ, YangMills.Construction.PowerSeries.MultiIndex.monomial w γ • a γ) 0 :=
    hsum.continuousAt (Metric.closedBall_mem_nhds _ h.pos)
  have heq : (fun w : Coordinates.ComplexCoordinates n =>
      ∑' γ, YangMills.Construction.PowerSeries.MultiIndex.monomial w γ • a γ) =ᶠ[𝓝 0]
      fun w => f (c + w) := by
    filter_upwards [Metric.closedBall_mem_nhds (0 : Coordinates.ComplexCoordinates n) h.pos]
      with w hw
    exact (h.hasSum w (by simpa using hw)).tsum_eq
  have hshift : ContinuousAt (fun w : Coordinates.ComplexCoordinates n => f (c + w)) 0 :=
    hnear.congr heq
  have hback : ContinuousAt (fun z : Coordinates.ComplexCoordinates n => z - c) c :=
    (continuous_id.sub continuous_const).continuousAt
  have hcomp : ContinuousAt
      ((fun w : Coordinates.ComplexCoordinates n => f (c + w)) ∘ fun z => z - c) c := by
    refine ContinuousAt.comp ?_ hback
    simpa using hshift
  simpa [Function.comp_def] using hcomp
theorem eventually_differentiableAt_line_of_powerSeriesData
    {O : Set (Coordinates.ComplexCoordinates n)}
    {f : Coordinates.ComplexCoordinates n → ℂ} {c : Coordinates.ComplexCoordinates n} {ρ : ℝ}
    {a : YangMills.Construction.PowerSeries.MultiIndex n → ℂ}
    (h : YangMills.Construction.BanachValued.IsPowerSeriesDataAt O f c ρ a) (j : Fin n) :
    ∀ᶠ ζ in 𝓝 (0 : ℂ), DifferentiableAt ℂ
      (fun ζ : ℂ => f (c + ζ • Coordinates.ComplexCoordinates.stdBasisVector j)) ζ := by
  have hbasis : ‖Coordinates.ComplexCoordinates.stdBasisVector j‖ ≤ 1 := by
    refine (pi_norm_le_iff_of_nonneg zero_le_one).2 fun i => ?_
    by_cases hij : i = j
    · subst hij
      simp [YangMills.Construction.Coordinates.ComplexCoordinates.stdBasisVector]
    · simp [YangMills.Construction.Coordinates.ComplexCoordinates.stdBasisVector,
        Pi.single_eq_of_ne hij]
  have hnorm : ∀ ζ : ℂ, ζ ∈ Metric.ball (0 : ℂ) ρ →
      ‖ζ • Coordinates.ComplexCoordinates.stdBasisVector j‖ ≤ ρ := by
    intro ζ hζ
    have hζ' : ‖ζ‖ < ρ := by simpa using hζ
    rw [norm_smul]
    calc ‖ζ‖ * ‖Coordinates.ComplexCoordinates.stdBasisVector j‖ ≤ ‖ζ‖ * 1 :=
          mul_le_mul_of_nonneg_left hbasis (norm_nonneg _)
      _ ≤ ρ := by simpa using hζ'.le
  have hterm : ∀ γ : YangMills.Construction.PowerSeries.MultiIndex n, DifferentiableOn ℂ
      (fun ζ : ℂ => YangMills.Construction.PowerSeries.MultiIndex.monomial
        (ζ • Coordinates.ComplexCoordinates.stdBasisVector j) γ • a γ)
      (Metric.ball (0 : ℂ) ρ) := by
    intro γ
    have hdiff : Differentiable ℂ
        (fun ζ : ℂ => YangMills.Construction.PowerSeries.MultiIndex.monomial
          (ζ • Coordinates.ComplexCoordinates.stdBasisVector j) γ • a γ) := by
      unfold YangMills.Construction.PowerSeries.MultiIndex.monomial
      simp only [Pi.smul_apply, smul_eq_mul]
      fun_prop
    exact hdiff.differentiableOn
  have hsum : DifferentiableOn ℂ
      (fun ζ : ℂ => ∑' γ, YangMills.Construction.PowerSeries.MultiIndex.monomial
        (ζ • Coordinates.ComplexCoordinates.stdBasisVector j) γ • a γ)
      (Metric.ball (0 : ℂ) ρ) :=
    Complex.differentiableOn_tsum_of_summable_norm h.summable hterm
      Metric.isOpen_ball fun γ ζ hζ => norm_monomial_smul_le (hnorm ζ hζ) γ
  filter_upwards [Metric.ball_mem_nhds (0 : ℂ) h.pos] with ζ hζ
  refine (hsum.differentiableAt (Metric.isOpen_ball.mem_nhds hζ)).congr_of_eventuallyEq ?_
  filter_upwards [Metric.isOpen_ball.mem_nhds hζ] with ξ hξ
  exact ((h.hasSum _ (hnorm ξ hξ)).tsum_eq).symm
theorem isHolomorphicIn_of_powerSeriesData {O : Set (Coordinates.ComplexCoordinates n)}
    {f : Coordinates.ComplexCoordinates n → ℂ} (hO : IsOpen O)
    (h : ∀ c ∈ O, ∃ (ρ : ℝ) (a : YangMills.Construction.PowerSeries.MultiIndex n → ℂ),
      YangMills.Construction.BanachValued.IsPowerSeriesDataAt O f c ρ a) :
    Coordinates.ComplexCoordinates.IsHolomorphicIn O ((Equiv.funUnique (Fin 1) ℂ).symm ∘ f) := by
  refine ⟨hO, ?_, fun c hc j => ?_⟩
  · intro c hc
    obtain ⟨ρ, a, hd⟩ := h c hc
    refine ContinuousAt.continuousWithinAt ?_
    exact continuousAt_pi.2 fun _ => continuousAt_of_powerSeriesData hd
  · obtain ⟨ρ, a, hd⟩ := h c hc
    filter_upwards [eventually_differentiableAt_line_of_powerSeriesData hd j] with ζ hζ
    exact differentiableAt_pi.2 fun _ => hζ
theorem exists_powerSeriesData_of_isHolomorphicIn
    (hseries : Coordinates.ComplexCoordinates.PowerSeriesHolomorphy.Properties)
    {O : Set (Coordinates.ComplexCoordinates n)} {f : Coordinates.ComplexCoordinates n → ℂ}
    (hO : IsOpen O)
    (h : Coordinates.ComplexCoordinates.IsHolomorphicIn O ((Equiv.funUnique (Fin 1) ℂ).symm ∘ f))
    (c : Coordinates.ComplexCoordinates n) (hc : c ∈ O) :
    ∃ (ρ : ℝ) (a : YangMills.Construction.PowerSeries.MultiIndex n → ℂ),
      YangMills.Construction.BanachValued.IsPowerSeriesDataAt O f c ρ a := by
  obtain ⟨ρ₀, hρ₀, hball⟩ := Metric.nhds_basis_closedBall.mem_iff.1 (hO.mem_nhds hc)
  have hpoly : Coordinates.ComplexCoordinates.PowerSeriesHolomorphy.closedPolydisk c ρ₀ ⊆ O := by
    intro z hz
    refine hball (Metric.mem_closedBall.2 ?_)
    rw [dist_eq_norm]
    exact (pi_norm_le_iff_of_nonneg hρ₀.le).2 fun j => hz j
  obtain ⟨b, hb, habs⟩ := ((hseries.1 n O hO).1 1 _ h).1 c hc ρ₀ hρ₀ hpoly
  have hρ : 0 < ρ₀ / 2 := half_pos hρ₀
  have hlt : ρ₀ / 2 < ρ₀ := half_lt_self hρ₀
  refine ⟨ρ₀ / 2, fun γ => b γ 0, hρ, ?_, ?_, ?_⟩
  · intro z hz
    refine hball (Metric.mem_closedBall.2 ?_)
    rw [dist_eq_norm]
    exact le_trans hz hlt.le
  · have hcorner : c + (fun _ => ((ρ₀ / 2 : ℝ) : ℂ)) ∈
        Coordinates.ComplexCoordinates.PowerSeriesHolomorphy.closedPolydisk c (ρ₀ / 2) := by
      intro j
      simp [abs_of_pos hρ₀]
    have hsummable := (habs (ρ₀ / 2) hlt).1 _ hcorner
    refine Summable.of_nonneg_of_le (fun γ => by positivity) (fun γ => ?_) hsummable
    have hterm : ‖Coordinates.ComplexCoordinates.PowerSeriesHolomorphy.monomialTerm b c
        (c + fun _ => ((ρ₀ / 2 : ℝ) : ℂ)) γ‖ =
          (ρ₀ / 2) ^ YangMills.Construction.PowerSeries.MultiIndex.order γ * ‖b γ‖ := by
      unfold YangMills.Construction.Coordinates.ComplexCoordinates.PowerSeriesHolomorphy.monomialTerm
        YangMills.Construction.PowerSeries.MultiIndex.order
      rw [norm_smul, norm_prod, ← Finset.prod_pow_eq_pow_sum]
      congr 1
      refine Finset.prod_congr rfl fun i _ => ?_
      simp [abs_of_pos hρ₀]
    rw [hterm, mul_comm]
    exact mul_le_mul_of_nonneg_left (norm_le_pi_norm (b γ) 0) (by positivity)
  · intro w hw
    have hmem : c + w ∈
        Coordinates.ComplexCoordinates.PowerSeriesHolomorphy.openPolydisk c ρ₀ := by
      intro j
      have : ‖w j‖ < ρ₀ := ((norm_le_pi_norm w j).trans hw).trans_lt hlt
      simpa using this
    have hsum := Pi.hasSum.1 (hb (c + w) hmem) 0
    simpa [YangMills.Construction.Coordinates.ComplexCoordinates.PowerSeriesHolomorphy.monomialTerm,
      YangMills.Construction.PowerSeries.MultiIndex.monomial, Function.comp_def] using hsum
theorem agreement_holds
    (hseries : Coordinates.ComplexCoordinates.PowerSeriesHolomorphy.Properties) :
    YangMills.Construction.BanachValued.ScalarAgreement.Agreement := by
  intro n hn O hO f
  constructor
  · intro h
    exact ⟨hO, Or.inl ⟨hn, exists_powerSeriesData_of_isHolomorphicIn hseries hO h⟩⟩
  · rintro ⟨-, ⟨-, h⟩ | ⟨h0, -⟩⟩
    · exact isHolomorphicIn_of_powerSeriesData hO h
    · omega
end YangMills.Construction.BanachValued.ScalarAgreement
