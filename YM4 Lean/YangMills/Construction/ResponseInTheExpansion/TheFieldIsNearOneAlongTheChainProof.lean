import YangMills.Construction.ResponseInTheExpansion.SizeOfTheLocalChainProof
import YangMills.Construction.ResponseInTheExpansion.TheFieldIsNearOneAlongTheChain
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ResponseInTheExpansion
open WeightedResponses TorusFields TorusLumps RenormalizationStepParameters
open Classical
open MeasureTheory
variable {ℓ : TorusLumps.StepParameters}
private theorem finsetSupNonneg_nonneg {α : Type} (S : Finset α) (f : α → ℝ) : 0 ≤ finsetSupNonneg S f :=
  Finset.le_fold_max 0 |>.mpr (Or.inl le_rfl)
private theorem maxCurvatureOnBall_nonneg {n : ℕ} [NeZero n] (W : TorusField n) (o : TorusSite n) (r : ℝ) :
    0 ≤ maxCurvatureOnBall W o r := finsetSupNonneg_nonneg _ _
private theorem widenedStageSum_nonneg (T : StageTower ℓ) (t : ℕ) (nn ρ₀ : ℝ) (d : ℕ) :
    ∀ (n : ℕ) [NeZero n] (u : MarkedSample ℓ (t + d) n) (o : TorusSite (fineSide ℓ.side d n)),
      0 ≤ widenedStageSum T t nn ρ₀ d n u o := by apply _root_.YangMills.SharedProofs.p61945 <;> assumption
private theorem widenedStageMax_nonneg (t : ℕ) (nn ρ₀ : ℝ) (d : ℕ) :
    ∀ (n : ℕ) [NeZero n] (u : MarkedSample ℓ (t + d) n) (o : TorusSite (fineSide ℓ.side d n)),
      0 ≤ widenedStageMax t nn ρ₀ d n u o := by apply _root_.YangMills.SharedProofs.p78364 <;> assumption
private theorem widenedChainSize_nonneg (T : StageTower ℓ) {C₁ ρ₀ : ℝ} (c : ℝ) (M t : ℕ) (nn : ℝ) (d n : ℕ)
    [NeZero n] (u : MarkedSample ℓ (t + d) n) (o : TorusSite (fineSide ℓ.side d n)) (hC : 0 ≤ C₁) (hρ : 0 ≤ ρ₀) :
    0 ≤ widenedChainSize T C₁ c M t nn ρ₀ d n u o := by
  unfold widenedChainSize
  refine le_min zero_le_one (mul_nonneg hC ?_)
  have h1 := mul_nonneg hρ (maxCurvatureOnBall_nonneg (topField ℓ (t + d) n u) (siteAbove ℓ.side d n o)
    (ballRadius ℓ.side nn ρ₀ d + 1))
  have h2 := widenedStageSum_nonneg T t nn ρ₀ d n u o
  have h3 := widenedStageMax_nonneg (ℓ := ℓ) t nn ρ₀ d n u o
  have h4 : 0 ≤ (M : ℝ) * Real.exp (-(c * ρ₀)) := mul_nonneg (Nat.cast_nonneg _) (Real.exp_pos _).le
  linarith
private theorem measureReal_le_of_indicator_moment {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) (A B : Set Ω)
    (f : Ω → ℝ) {s K : ℝ} (q : ℕ)
    (hs : 0 < s) (hf : ∀ u, 0 ≤ f u) (hB : ∀ᵐ u ∂μ, u ∈ B → u ∈ A ∧ s < f u)
    (hint : Integrable (A.indicator fun u => f u ^ q) μ)
    (hK : ∫ u, A.indicator (fun u => f u ^ q) u ∂μ ≤ K) : μ.real B ≤ K / s ^ q := by
  have hsq : 0 < s ^ q := pow_pos hs q
  set g : Ω → ℝ := A.indicator fun u => f u ^ q with hg
  have hg0 : ∀ u, 0 ≤ g u := fun u => Set.indicator_nonneg (fun v _ => pow_nonneg (hf v) q) u
  have hcheb := mul_meas_ge_le_integral_of_nonneg (μ := μ) (f := g)
    (Filter.Eventually.of_forall hg0) hint (s ^ q)
  have hfin : μ {u | s ^ q ≤ g u} < ⊤ := hint.measure_ge_lt_top hsq
  have hsub : B ≤ᵐ[μ] {u | s ^ q ≤ g u} := by
    filter_upwards [hB] with u hu hmem
    obtain ⟨hA, hlt⟩ := hu hmem
    show s ^ q ≤ g u
    rw [hg, Set.indicator_of_mem hA]
    exact pow_le_pow_left₀ hs.le hlt.le q
  have hmono : μ.real B ≤ μ.real {u | s ^ q ≤ g u} :=
    ENNReal.toReal_mono hfin.ne (measure_mono_ae hsub)
  rw [le_div_iff₀ hsq]
  calc μ.real B * s ^ q ≤ μ.real {u | s ^ q ≤ g u} * s ^ q := by gcongr
    _ = s ^ q * μ.real {u | s ^ q ≤ g u} := mul_comm _ _
    _ ≤ ∫ u, g u ∂μ := hcheb
    _ ≤ K := hK
private theorem rpow_moment_ratio_le {x C p : ℝ} {q : ℕ} (hx : 1 ≤ x) (hq : 5 * |p| ≤ q) :
    (C * x ^ (-(1 / 2 : ℝ) + 2 / 1000)) ^ q / (x ^ (-(1 / 4 : ℝ))) ^ q ≤ |C| ^ q * x ^ (-p) := by
  have hx0 : 0 < x := by linarith
  have hpow : x ^ (-(1 / 2 : ℝ) + 2 / 1000) / x ^ (-(1 / 4 : ℝ)) = x ^ (-(1 / 4 : ℝ) + 2 / 1000) := by
    rw [← Real.rpow_sub hx0]; norm_num
  rw [← div_pow, mul_div_assoc, hpow, mul_pow]
  have h1 : C ^ q ≤ |C| ^ q := by
    have := pow_le_pow_left₀ (abs_nonneg C) le_rfl q
    calc C ^ q ≤ |C ^ q| := le_abs_self _
      _ = |C| ^ q := abs_pow C q
  have h2 : (x ^ (-(1 / 4 : ℝ) + 2 / 1000)) ^ q ≤ x ^ (-p) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hx0.le]
    apply Real.rpow_le_rpow_of_exponent_le hx
    have hqp : p ≤ |p| := le_abs_self p
    nlinarith [abs_nonneg p]
  have h3 : 0 ≤ (x ^ (-(1 / 4 : ℝ) + 2 / 1000)) ^ q := pow_nonneg (Real.rpow_nonneg hx0.le _) q
  calc C ^ q * (x ^ (-(1 / 4 : ℝ) + 2 / 1000)) ^ q ≤ |C| ^ q * (x ^ (-(1 / 4 : ℝ) + 2 / 1000)) ^ q :=
        mul_le_mul_of_nonneg_right h1 h3
    _ ≤ |C| ^ q * x ^ (-p) := mul_le_mul_of_nonneg_left h2 (pow_nonneg (abs_nonneg C) q)
private theorem nearIdentityAlongChainAt_of_localChainSizeAt (Tb : ParameterAssignment) (y : ℝ)
    (h : localChainSizeAt Tb y) : nearIdentityAlongChainAt Tb y := by
  obtain ⟨C₁, c, hC₁, -, hq⟩ := h
  intro p
  obtain ⟨Cq, x₀, hb⟩ := hq ⌈5 * |p|⌉₊
  refine ⟨|Cq| ^ ⌈5 * |p|⌉₊, max x₀ 2, ?_⟩
  intro T β k N _ nn o hOn hdvd
  have hx2 : 2 ≤ flowCouplings (Tb.stepParameters y) β k := le_trans (le_max_right _ _) hOn.floor_le
  have hOn' : IsLocalChainAbove Tb y T β k N nn x₀ :=
    { hOn with floor_le := le_trans (le_max_left _ _) hOn.floor_le }
  obtain ⟨h1, ⟨hint, hmom⟩, -⟩ := hb T β k N nn k (localChainDepth (Tb.stepParameters y) β k)
    (localChainDepth (Tb.stepParameters y) β k) o hOn' hdvd le_rfl rfl rfl
  simp only [Nat.sub_self, pow_zero, div_one] at h1 hmom hint
  have hx1 : 1 < flowCouplings (Tb.stepParameters y) β k := by linarith
  have hs1 : flowCouplings (Tb.stepParameters y) β k ^ (-(1 / 4 : ℝ)) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg hx1 (by norm_num)
  have hs0 : 0 < flowCouplings (Tb.stepParameters y) β k ^ (-(1 / 4 : ℝ)) := Real.rpow_pos_of_pos (by linarith) _
  have hρ : 0 ≤ localLogScale (Tb.stepParameters y) β k := Nat.cast_nonneg _
  refine le_trans (measureReal_le_of_indicator_moment _ _ _ _ ⌈5 * |p|⌉₊ hs0
    (fun u => widenedChainSize_nonneg T c _ k nn _ _ _ _ hC₁.le hρ) ?_ hint hmom)
    (rpow_moment_ratio_le hx1.le (Nat.le_ceil _))
  filter_upwards [h1 _ hs1] with u hu hmem
  obtain ⟨hl, hn⟩ := hmem
  refine ⟨hl, lt_of_not_ge fun hle => hn (hu hl hle)⟩
theorem nearIdentityAlongChain_of_localChainSize (h : localChainSizeStatement) :
    nearIdentityAlongChainStatement := by
  intro a ha
  obtain ⟨L₀, rt₀, C₀, hrt, H⟩ := h a ha
  refine ⟨L₀, rt₀, C₀, hrt, fun L hL hL₀ T hTa hTL hD hC hO hr hC₀ => ?_⟩
  obtain ⟨y₀, Hy⟩ := H L hL hL₀ T hTa hTL hD hC hO hr hC₀
  exact ⟨y₀, fun y hy hR hW => nearIdentityAlongChainAt_of_localChainSizeAt T y (Hy y hy hR hW)⟩
end YangMills.Construction.ResponseInTheExpansion
end
