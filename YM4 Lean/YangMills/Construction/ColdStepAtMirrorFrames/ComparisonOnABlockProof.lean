import YangMills.Construction.ColdStepAtMirrorFrames.CalculusOfLocalTerms
import YangMills.Construction.ColdStepAtMirrorFrames.ComparisonOnABlock
import YangMills.Construction.ColdStepAtMirrorFrames.ExponentsStayGood
import YangMills.Construction.ColdStepAtMirrorFrames.RimOfACut
import Mathlib
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YangMills.Construction.ColdStepAtMirrorFrames
namespace BlockComparison
open LocalCalculus
variable {ι κ P : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] [Fintype P]
  {ρ r c x : ℝ} {pos : ι → P} {D : P → P → ℝ} {z : P} {θ : BondField ι → ℝ}
theorem weightedSqNormNear_pushforwardField (j : κ → ι) (hj : Function.Injective j) (ξ : BondField κ) :
    weightedSqNormNear r pos D z (pushforwardField j ξ) = weightedSqNormNear r (fun k => pos (j k)) D z ξ := by
  classical
  unfold weightedSqNormNear
  rw [← Finset.sum_subset (Finset.subset_univ (Finset.univ.image j))]
  · rw [Finset.sum_image (fun a _ b _ h => hj h)]
    exact Finset.sum_congr rfl fun k _ => by rw [pushforwardField_apply_image j hj]
  · intro b _ hb
    have : ∀ k, j k ≠ b := fun k e => hb (by simp [← e])
    simp [pushforwardField_apply_of_not_mem_range j _ b this]
theorem sum_comp_le_sum_of_injective (j : κ → ι) (hj : Function.Injective j) (w : ι → ℝ) (hw : ∀ b, 0 ≤ w b) :
    ∑ k, w (j k) ≤ ∑ b, w b := by
  classical
  rw [← Finset.sum_image (s := Finset.univ) (g := j) (f := w) (fun a _ b _ h => hj h)]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun b _ _ => hw b
def restrictToBlock (j : κ → ι) (θ : BondField ι → ℝ) (ξ : BondField κ) : ℝ := θ (pushforwardField j ξ)
theorem restrictToBlock_eq (j : κ → ι) (θ : BondField ι → ℝ) :
    restrictToBlock j θ = fun ζ => θ (pushforwardFieldCLM j ζ) := by
  funext ζ
  simp [restrictToBlock, pushforwardFieldCLM_apply]
theorem contDiffOn_restrictToBlock (hρ : 0 < ρ) (j : κ → ι) (hj : Function.Injective j) {n : WithTop ℕ∞}
    (hθ : ContDiffOn ℝ n θ (openPolyball ι ρ)) : ContDiffOn ℝ n (restrictToBlock j θ) (openPolyball κ ρ) := by
  rw [restrictToBlock_eq]
  exact hθ.comp (pushforwardFieldCLM j).contDiff.contDiffOn (fun ξ hξ => by
    rw [pushforwardFieldCLM_apply]
    exact pushforwardField_mem_openPolyball hρ j hj hξ)
theorem bondGradNorm_restrictToBlock_le (hρ : 0 < ρ) (j : κ → ι) (hj : Function.Injective j)
    (hθ : ContDiffOn ℝ 1 θ (openPolyball ι ρ)) {ξ : BondField κ} (hξ : ξ ∈ openPolyball κ ρ) (k : κ) :
    bondGradNorm (restrictToBlock j θ) k ξ ≤ bondGradNorm θ (j k) (pushforwardField j ξ) := by
  rw [restrictToBlock_eq]
  have := bondGradNorm_comp_clm_le hρ hθ (pushforwardFieldCLM j)
    (by rw [pushforwardFieldCLM_apply]; exact pushforwardField_mem_openPolyball hρ j hj hξ)
    (k := k) (b := j k) (fun e => by rw [pushforwardFieldCLM_apply, pushforwardField_bondVariation j hj])
  rwa [pushforwardFieldCLM_apply] at this
theorem bondGradNorm_restrictToBlock_le_decay (hρ : 0 < ρ) (j : κ → ι) (hj : Function.Injective j)
    (hT : IsLocalTermAt ρ r c x pos D z θ) {ξ : BondField κ} (hξ : ξ ∈ openPolyball κ ρ) (k : κ) :
    bondGradNorm (restrictToBlock j θ) k ξ ≤
      c * (x * Real.sqrt (weightedSqNormNear r (fun k => pos (j k)) D z ξ) + 1) *
        Real.exp (-(2 ^ 5 * r * D (pos (j k)) z)) := by
  refine (bondGradNorm_restrictToBlock_le hρ j hj (contDiffOn_one_of_two hT.smooth) hξ k).trans ?_
  have := hT.slope _ (pushforwardField_mem_openPolyball hρ j hj hξ) (j k)
  rwa [weightedSqNormNear_pushforwardField j hj] at this
theorem exists_bondGradNorm_restrictToBlock_bound (hρ : 0 < ρ) (hr : 0 < r) (hc : 0 ≤ c) (hx : 0 ≤ x)
    (hD : IsPseudoMetricOnBonds D) (j : κ → ι) (hj : Function.Injective j) (hT : IsLocalTermAt ρ r c x pos D z θ) :
    ∃ M, 0 ≤ M ∧ ∀ ξ ∈ openPolyball κ ρ, ∀ k, bondGradNorm (restrictToBlock j θ) k ξ ≤ M := by
  obtain ⟨M, hM0, hM⟩ := exists_bondGradNorm_bound_of_localTerm hρ hr.le hc hx hD hT
  exact ⟨M, hM0, fun ξ hξ k => (bondGradNorm_restrictToBlock_le hρ j hj (contDiffOn_one_of_two hT.smooth) hξ k).trans
    (hM _ (pushforwardField_mem_openPolyball hρ j hj hξ) _)⟩
section Measure
variable {m S : ℝ} {p : ℝ → ℝ} {T : BondField κ → ℝ}
theorem ballL2Norm_bondGradNorm_le (hρ : 0 < ρ) {posκ : κ → P} (hx : 0 ≤ x)
    (F : IsPositiveUnitalForm ρ p T) (Sz : AdmissibleMomentBounds ρ m r S p posκ D T)
    {G : BondField κ → ℝ} (hG : ContDiffOn ℝ 1 G (openPolyball κ ρ)) {M a : ℝ} (ha : 0 ≤ a)
    (hM : ∀ ξ ∈ openPolyball κ ρ, ∀ k, bondGradNorm G k ξ ≤ M) (z : P) {k : κ} {w : ℝ} (hw : 0 ≤ w)
    (h : ∀ ξ ∈ openPolyball κ ρ, bondGradNorm G k ξ ≤
      a * (x * Real.sqrt (weightedSqNormNear r posκ D z ξ) + 1) * w) :
    ballL2Norm (cutoffFactor ρ p) T (bondGradNorm G k) ≤
      a * w * Real.sqrt (2 * x ^ 2 * (8 * S ^ 2 / m) + 2) := by
  apply ballL2Norm_le_of_near_majorant hρ F Sz (isBoundedContinuousOn_bondGradNorm hρ hG hM k) (by positivity) hx z
  intro ξ hξ
  rw [abs_of_nonneg (bondGradNorm_nonneg G k ξ)]
  refine (h ξ hξ).trans (le_of_eq ?_)
  ring
theorem ballCovariance_add_right (F : IsPositiveUnitalForm ρ p T) {f g h : BondField κ → ℝ}
    (hf : IsBoundedContinuousOn κ ρ f) (hg : IsBoundedContinuousOn κ ρ g) (hh : IsBoundedContinuousOn κ ρ h) :
    ballCovariance (cutoffFactor ρ p) T f (fun η => g η + h η) =
      ballCovariance (cutoffFactor ρ p) T f g + ballCovariance (cutoffFactor ρ p) T f h := by
  unfold ballCovariance
  have e : (fun η => f η * (g η + h η)) = fun η => f η * g η + f η * h η := by
    funext η
    ring
  rw [e, F.map_add _ _ (hf.mul hg) (hf.mul hh), F.map_add _ _ hg hh]
  ring
end Measure
theorem exp_neg_mul_le_of_le {a b d : ℝ} (hab : a ≤ b) (hd : 0 ≤ d) : Real.exp (-(b * d)) ≤ Real.exp (-(a * d)) :=
  Real.exp_le_exp.mpr (by
    have := mul_le_mul_of_nonneg_right hab hd
    linarith)
theorem exp_neg_half_le_of_far {r R d : ℝ} (hr : 0 < r) (hd : R / 8 ≤ d) :
    Real.exp (-(r / 2 * d)) ≤ Real.exp (-(r / 4 * d)) * Real.exp (-(r * R / 32)) := by
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have h3 : (R / 8) * r ≤ d * r := mul_le_mul_of_nonneg_right hd hr.le
  nlinarith
theorem convex_combination_le {v a b c : ℝ} (h0 : 0 ≤ v) (h1 : v ≤ 1) (ha : a ≤ c) (hb : b ≤ c) :
    v * a + (1 - v) * b ≤ c := by
  have h2 : 0 ≤ 1 - v := by linarith
  have h3 := mul_le_mul_of_nonneg_left ha h0
  have h4 := mul_le_mul_of_nonneg_left hb h2
  nlinarith
theorem comparison_constants_le {lam S x c ε e : ℝ} (hlam : 0 < lam) (hSn : 0 ≤ S) (hx : 1 ≤ x) (hc : 1 ≤ c)
    (hε : 0 ≤ ε) (he : 0 < e) :
    c * ε * (x * (8 * S ^ 2 / (x * lam / 4)) + 1) +
      ((x * lam / 4)⁻¹ * (c * Real.sqrt (2 * x ^ 2 * (8 * S ^ 2 / (x * lam / 4)) + 2)) * S *
          (c * ε * Real.sqrt (2 * x ^ 2 * (8 * S ^ 2 / (x * lam / 4)) + 2) * S * S) +
        (x * lam / 4)⁻¹ * (c * Real.sqrt (2 * x ^ 2 * (8 * S ^ 2 / (x * lam / 4)) + 2)) * S *
          (c * Real.sqrt (2 * x ^ 2 * (8 * S ^ 2 / (x * lam / 4)) + 2) * S * (S * e)) +
        (x * lam / 4)⁻¹ * (c * Real.sqrt (2 * x ^ 2 * (8 * S ^ 2 / (x * lam / 4)) + 2)) * S *
          (c * Real.sqrt (2 * x ^ 2 * (8 * S ^ 2 / (x * lam / 4)) + 2) * S * (S * e))) ≤
      c ^ 2 * blockComparisonConstant lam S * (ε + e) := by
  have hx0 : 0 < x := by linarith
  set m := x * lam / 4 with hm
  have hG2 : 0 ≤ 2 * x ^ 2 * (8 * S ^ 2 / m) + 2 := by positivity
  set G := Real.sqrt (2 * x ^ 2 * (8 * S ^ 2 / m) + 2) with hG
  have hGs : G ^ 2 = 2 * x ^ 2 * (8 * S ^ 2 / m) + 2 := Real.sq_sqrt hG2
  set N₃ := (4 / lam) * (64 * S ^ 2 / lam + 2) with hN₃
  have a1 : m⁻¹ * G ^ 2 ≤ N₃ := by
    rw [hGs, hm, hN₃]
    have e1 : (x * lam / 4)⁻¹ * (2 * x ^ 2 * (8 * S ^ 2 / (x * lam / 4)) + 2) =
        (4 / lam) * (64 * S ^ 2 / lam + 2 / x) := by
      field_simp
      ring
    rw [e1]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    have : 2 / x ≤ 2 := by
      rw [div_le_iff₀ hx0]
      linarith
    linarith
  have e2 : x * (8 * S ^ 2 / m) = 32 * S ^ 2 / lam := by
    rw [hm]
    field_simp
    ring
  rw [e2]
  have t : m⁻¹ * (c * G) * S * (c * ε * G * S * S) + m⁻¹ * (c * G) * S * (c * G * S * (S * e)) +
      m⁻¹ * (c * G) * S * (c * G * S * (S * e)) =
      (m⁻¹ * G ^ 2) * (c ^ 2 * S ^ 3 * (ε + 2 * e)) := by ring
  rw [t]
  unfold blockComparisonConstant
  rw [← hN₃]
  have hcc : c ≤ c ^ 2 := by nlinarith
  have hq : 0 ≤ 32 * S ^ 2 / lam + 1 := by positivity
  have b1 : (m⁻¹ * G ^ 2) * (c ^ 2 * S ^ 3 * (ε + 2 * e)) ≤ N₃ * (c ^ 2 * S ^ 3 * (ε + 2 * e)) :=
    mul_le_mul_of_nonneg_right a1 (by positivity)
  have b2 : c * ε * (32 * S ^ 2 / lam + 1) ≤ c ^ 2 * ε * (32 * S ^ 2 / lam + 1) := by
    apply mul_le_mul_of_nonneg_right _ hq
    exact mul_le_mul_of_nonneg_right hcc hε
  have b3 : 0 ≤ c ^ 2 * e * (32 * S ^ 2 / lam + 1) := by positivity
  have b4 : 0 ≤ N₃ * c ^ 2 * S ^ 3 * ε := by positivity
  nlinarith
end BlockComparison
set_option maxHeartbeats 3200000 in
open BlockComparison LocalCalculus in
theorem blockComparisonBound_holds (hseg : MeanDifferenceBoundAlongSegment)
    (hgood : AdmissiblePotentialStability) (hsz : AdmissibleMomentBoundsHold)
    (hmc : CutoffExpectationIsPositiveForm) (hrim : CutoffFactorIsRadialCutoff) :
    BlockComparisonBound := by
  intro ι ι' κ P P' _ _ _ _ _ _ _ _ _ _ ρ r S lam x c ε R p pos D Ψ H θ Y pos' D' Ψ' H' θ' Y' j j' M M' φ
    hρ hr hlam hx hc hε hR hp hD hD' hΨ hΨ' hS hSp hS2 hSp2 hθ hsum hθ' hsum' hH hH' hj hj' hdist hY
    hfar hfar' hcomp hval
  have hx0 : 0 < x := by linarith
  have hc0 : 0 ≤ c := by linarith
  have hm0 : 0 < x * lam / 4 := by positivity
  have h2m : 2 * (x * lam / 4) ≤ x * lam := by linarith [mul_pos hx0 hlam]
  have hd : IsPseudoMetricOnBonds (fun b b' => D (pos b) (pos b')) :=
    ⟨fun b => hD.self _, fun b b' => hD.symm _ _, fun b b' b'' => hD.triangle _ _ _⟩
  have hd' : IsPseudoMetricOnBonds (fun b b' => D' (pos' b) (pos' b')) :=
    ⟨fun b => hD'.self _, fun b b' => hD'.symm _ _, fun b b' b'' => hD'.triangle _ _ _⟩
  have hdk : IsPseudoMetricOnBonds (fun k k' => D (pos (j k)) (pos (j k'))) :=
    ⟨fun b => hD.self _, fun b b' => hD.symm _ _, fun b b' b'' => hD.triangle _ _ _⟩
  have hSn : 0 ≤ S := (Finset.sum_nonneg fun b _ => (Real.exp_pos _).le).trans (hS Y)
  have gA := (hgood ι ρ (x * lam / 4) r (x * lam) _ hρ hm0 hr.le hd h2m).2.2.2 κ j Ψ hj hΨ
  have gB := (hgood ι' ρ (x * lam / 4) r (x * lam) _ hρ hm0 hr.le hd' h2m).2.2.2 κ j' Ψ' hj' hΨ'
  have ed : (fun k k' => D' (pos' (j' k)) (pos' (j' k'))) = fun k k' => D (pos (j k)) (pos (j k')) := by
    funext k k'
    exact (hdist k k').symm
  simp only [ed] at gB
  have hsg := (hgood κ ρ (x * lam / 4) r (x * lam) _ hρ hm0 hr.le hdk h2m).1
  have cA : Continuous (fun ξ => Ψ (pushforwardField j ξ)) := by
    obtain ⟨K, hK, _⟩ := gA
    exact hK.smooth.continuous
  have cB : Continuous (fun ξ => Ψ' (pushforwardField j' ξ)) := by
    obtain ⟨K, hK, _⟩ := gB
    exact hK.smooth.continuous
  set A := fun ξ => Ψ (pushforwardField j ξ) with hA
  set B := fun ξ => Ψ' (pushforwardField j' ξ) with hB
  have hSk : ∀ z, ∑ k, Real.exp (-(r / 4 * D (pos (j k)) z)) ≤ S := fun z =>
    (sum_comp_le_sum_of_injective j hj (fun b => Real.exp (-(r / 4 * D (pos b) z)))
      fun b => (Real.exp_pos _).le).trans (hS z)
  have hSk' : ∀ z, ∑ k, Real.exp (-(r / 4 * D' (pos' (j' k)) z)) ≤ S := fun z =>
    (sum_comp_le_sum_of_injective j' hj' (fun b => Real.exp (-(r / 4 * D' (pos' b) z)))
      fun b => (Real.exp_pos _).le).trans (hS2 z)
  have hH1 := contDiffOn_one_of_two hH.smooth
  have hH1' := contDiffOn_one_of_two hH'.smooth
  have hb₀ := contDiffOn_restrictToBlock hρ j hj hH1
  have hb₁ := contDiffOn_restrictToBlock hρ j' hj' hH1'
  obtain ⟨M₀, hM₀0, hM₀⟩ := exists_bondGradNorm_restrictToBlock_bound hρ hr hc0 hx0.le hD j hj hH
  obtain ⟨M₁, hM₁0, hM₁⟩ := exists_bondGradNorm_restrictToBlock_bound hρ hr hc0 hx0.le hD' j' hj' hH'
  obtain ⟨_, N₀, hN₀⟩ := isBoundedContinuousOn_of_bondGradNorm_le hρ hb₀ hM₀0 hM₀
  obtain ⟨_, N₁, hN₁⟩ := isBoundedContinuousOn_of_bondGradNorm_le hρ hb₁ hM₁0 hM₁
  have hbdd : ∀ f : BondField κ → ℝ, Continuous f → ∃ M, ∀ η ∈ openPolyball κ ρ, |f η| ≤ M := by
    intro f hf
    obtain ⟨M, hM⟩ := (isCompact_closedBall (0 : BondField κ) ρ).exists_bound_of_continuousOn
      hf.continuousOn
    refine ⟨M, fun η hη => ?_⟩
    have : η ∈ Metric.closedBall (0 : BondField κ) ρ := by
      rw [openPolyball_eq_ball hρ] at hη
      exact Metric.ball_subset_closedBall hη
    simpa using hM η this
  obtain ⟨N₂, hN₂⟩ := hbdd A cA
  obtain ⟨N₃, hN₃⟩ := hbdd B cB
  have hr' := hrim ρ p hρ hp
  have hfin := hseg κ ρ _ A B (restrictToBlock j H) (restrictToBlock j' H') (|N₀| + |N₁| + |N₂| + |N₃|)
    (c ^ 2 * blockComparisonConstant lam S * (ε + Real.exp (-(r * R / 32)))) hρ hr' cA.continuousOn
    cB.continuousOn hb₀.continuousOn hb₁.continuousOn
    (fun η hη => by
      have h1 := hN₀ η hη
      have h2 := hN₁ η hη
      have h3 := hN₂ η hη
      have h4 := hN₃ η hη
      have a1 := le_abs_self N₀
      have a2 := le_abs_self N₁
      have a3 := le_abs_self N₂
      have a4 := le_abs_self N₃
      have b1 := abs_nonneg N₀
      have b2 := abs_nonneg N₁
      have b3 := abs_nonneg N₂
      have b4 := abs_nonneg N₃
      exact ⟨by linarith, by linarith, by linarith, by linarith⟩)
  have conv : ∀ (Φ f : BondField κ → ℝ),
      ballExpectation (fun u => cutoffFactor ρ p (max u 0)) Φ f = ballExpectation (cutoffFactor ρ p) Φ f := by
    intro Φ f
    unfold ballExpectation ballDensity radialWeightProd
    simp only [max_eq_left (norm_nonneg _)]
  have convc : ∀ (Φ f g : BondField κ → ℝ),
      ballCovariance (fun u => cutoffFactor ρ p (max u 0)) Φ f g = ballCovariance (cutoffFactor ρ p) Φ f g := by
    intro Φ f g
    unfold ballCovariance
    simp only [conv]
  simp only [conv, convc] at hfin
  refine hfin ?_
  intro v hv0 hv1
  have hv1' : 0 ≤ 1 - v := by linarith
  set T := segmentInterpolant A B v with hT
  have gT := hsg A B v gA gB hv0 hv1
  have cT : Continuous T := by
    obtain ⟨K, hK, _⟩ := gT
    exact hK.smooth.continuous
  have F := hmc κ ρ p T hρ hp cT
  have Sz := hsz κ P ρ (x * lam / 4) r S p (fun k => pos (j k)) D T hρ hm0 hr hp hD gT hSk
  have gT' : IsAdmissiblePotential ρ (x * lam / 4) r
      (fun k k' => D' (pos' (j' k)) (pos' (j' k'))) T := by
    rw [ed]
    exact gT
  have Sz' := hsz κ P' ρ (x * lam / 4) r S p (fun k => pos' (j' k)) D' T hρ hm0 hr hp hD' gT' hSk'
  set G := Real.sqrt (2 * x ^ 2 * (8 * S ^ 2 / (x * lam / 4)) + 2) with hGd
  have hG0 : 0 ≤ G := Real.sqrt_nonneg _
  set e := Real.exp (-(r * R / 32)) with hed
  have he : 0 < e := Real.exp_pos _
  have nearY : ∀ ξ, weightedSqNormNear r (fun k => pos' (j' k)) D' Y' ξ =
      weightedSqNormNear r (fun k => pos (j k)) D Y ξ := by
    intro ξ
    unfold weightedSqNormNear
    exact Finset.sum_congr rfl fun k _ => by rw [hY k]
  set Hv := segmentInterpolant (restrictToBlock j H) (restrictToBlock j' H') v with hHvd
  have hHv : ContDiffOn ℝ 1 Hv (openPolyball κ ρ) :=
    (contDiffOn_const.mul hb₁).add (contDiffOn_const.mul hb₀)
  have hlin : ∀ ξ ∈ openPolyball κ ρ, ∀ k, bondGradNorm Hv k ξ ≤ v * bondGradNorm (restrictToBlock j' H') k ξ +
      (1 - v) * bondGradNorm (restrictToBlock j H) k ξ := by
    intro ξ hξ k
    have := bondGradNorm_linear_combination_le hρ hb₁ hb₀ v (1 - v) hξ k
    rwa [abs_of_nonneg hv0, abs_of_nonneg hv1'] at this
  have hMv0 : 0 ≤ M₀ + M₁ := by positivity
  have hMv : ∀ ξ ∈ openPolyball κ ρ, ∀ k, bondGradNorm Hv k ξ ≤ M₀ + M₁ := by
    intro ξ hξ k
    refine (hlin ξ hξ k).trans ?_
    exact convex_combination_le hv0 hv1 ((hM₁ ξ hξ k).trans (by linarith)) ((hM₀ ξ hξ k).trans (by linarith))
  have hmaj : ∀ ξ ∈ openPolyball κ ρ, ∀ k, bondGradNorm Hv k ξ ≤
      c * (x * Real.sqrt (weightedSqNormNear r (fun k => pos (j k)) D Y ξ) + 1) *
        Real.exp (-(2 ^ 5 * r * D (pos (j k)) Y)) := by
    intro ξ hξ k
    refine (hlin ξ hξ k).trans ?_
    have h1 := bondGradNorm_restrictToBlock_le_decay hρ j' hj' hH' hξ k
    rw [nearY, ← hY k] at h1
    have h2 := bondGradNorm_restrictToBlock_le_decay hρ j hj hH hξ k
    exact convex_combination_le hv0 hv1 h1 h2
  have hnn := fun y w => pseudoMetric_nonneg hD y w
  have hnn' := fun y w => pseudoMetric_nonneg hD' y w
  have hHn : ∀ k, ballL2Norm (cutoffFactor ρ p) T (bondGradNorm Hv k) ≤
      c * G * Real.exp (-(2 * r * D (pos (j k)) Y)) := by
    intro k
    have key := ballL2Norm_bondGradNorm_le (a := c) (w := Real.exp (-(2 ^ 5 * r * D (pos (j k)) Y))) hρ hx0.le
      F Sz hHv hc0 hMv Y (Real.exp_pos _).le (fun ξ hξ => hmaj ξ hξ k)
    refine key.trans ?_
    have hw : Real.exp (-(2 ^ 5 * r * D (pos (j k)) Y)) ≤ Real.exp (-(2 * r * D (pos (j k)) Y)) :=
      exp_neg_mul_le_of_le (by linarith) (hnn _ _)
    calc c * Real.exp (-(2 ^ 5 * r * D (pos (j k)) Y)) * G
        = c * G * Real.exp (-(2 ^ 5 * r * D (pos (j k)) Y)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hw (by positivity)
  have hHn' : ∀ k, ballL2Norm (cutoffFactor ρ p) T (bondGradNorm Hv k) ≤
      c * G * Real.exp (-(2 * r * D' (pos' (j' k)) Y')) := by
    intro k
    rw [← hY k]
    exact hHn k
  have hvn := isBoundedContinuousOn_of_bondGradNorm_le hρ hHv hMv0 hMv
  have hq := isBoundedContinuousOn_weightedSqNormNear (r := r) (pos := fun k => pos (j k)) (D := D) (ι := κ) hρ Y
  have nDiff : IsBoundedContinuousOn κ ρ (fun ξ => restrictToBlock j' H' ξ - restrictToBlock j H ξ) :=
    (isBoundedContinuousOn_of_bondGradNorm_le hρ hb₁ hM₁0 hM₁).sub
      (isBoundedContinuousOn_of_bondGradNorm_le hρ hb₀ hM₀0 hM₀)
  have t1 : |ballExpectation (cutoffFactor ρ p) T (fun ξ => restrictToBlock j' H' ξ - restrictToBlock j H ξ)| ≤
      c * ε * (x * (8 * S ^ 2 / (x * lam / 4)) + 1) := by
    have hmj : IsBoundedContinuousOn κ ρ
        (fun ξ => c * ε * (x * weightedSqNormNear r (fun k => pos (j k)) D Y ξ + 1)) :=
      (IsBoundedContinuousOn.const _).mul
        (((IsBoundedContinuousOn.const _).mul hq).add (IsBoundedContinuousOn.const _))
    refine (abs_ballExpectation_le F nDiff hmj hval).trans ?_
    rw [F.map_smul, F.map_add _ _ ((IsBoundedContinuousOn.const _).mul hq) (IsBoundedContinuousOn.const _),
      F.map_smul, F.map_one]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    have := mul_le_mul_of_nonneg_left (Sz.near_moment_le Y) hx0.le
    linarith
  set Δ : {z // z ∈ M} → BondField κ → ℝ := fun z ζ =>
    θ' (φ z).1 (pushforwardField j' ζ) - θ z.1 (pushforwardField j ζ) with hΔ
  have hΔs : ∀ z, ContDiffOn ℝ 1 (Δ z) (openPolyball κ ρ) := fun z =>
    (contDiffOn_restrictToBlock hρ j' hj' (contDiffOn_one_of_two (hθ' (φ z).1).smooth)).sub
      (contDiffOn_restrictToBlock hρ j hj (contDiffOn_one_of_two (hθ z.1).smooth))
  have hΔb : ∀ z, ∃ Mz, 0 ≤ Mz ∧ ∀ ξ ∈ openPolyball κ ρ, ∀ k, bondGradNorm (Δ z) k ξ ≤ Mz := by
    intro z
    obtain ⟨A₁, hA₁0, hA₁⟩ := exists_bondGradNorm_restrictToBlock_bound hρ hr hc0 hx0.le hD' j' hj' (hθ' (φ z).1)
    obtain ⟨A₂, hA₂0, hA₂⟩ := exists_bondGradNorm_restrictToBlock_bound hρ hr hc0 hx0.le hD j hj (hθ z.1)
    refine ⟨A₁ + A₂, by positivity, fun ξ hξ k => ?_⟩
    have e1 : Δ z = fun ζ => 1 * restrictToBlock j' (θ' (φ z).1) ζ + (-1) * restrictToBlock j (θ z.1) ζ := by
      funext ζ
      simp only [hΔ, restrictToBlock]
      ring
    rw [e1]
    have := bondGradNorm_linear_combination_le hρ
      (contDiffOn_restrictToBlock hρ j' hj' (contDiffOn_one_of_two (hθ' (φ z).1).smooth))
      (contDiffOn_restrictToBlock hρ j hj (contDiffOn_one_of_two (hθ z.1).smooth)) 1 (-1) hξ k
    have h1 := hA₁ ξ hξ k
    have h2 := hA₂ ξ hξ k
    simp only [abs_one, abs_neg, one_mul] at this
    simp only [one_mul]
    linarith
  have hΔn : ∀ z, IsBoundedContinuousOn κ ρ (Δ z) := fun z => by
    obtain ⟨Mz, h0, hMz⟩ := hΔb z
    exact isBoundedContinuousOn_of_bondGradNorm_le hρ (hΔs z) h0 hMz
  have hgs : ∀ z, ContDiffOn ℝ 1 (restrictToBlock j (θ z)) (openPolyball κ ρ) := fun z =>
    contDiffOn_restrictToBlock hρ j hj (contDiffOn_one_of_two (hθ z).smooth)
  have hgs' : ∀ z, ContDiffOn ℝ 1 (restrictToBlock j' (θ' z)) (openPolyball κ ρ) := fun z =>
    contDiffOn_restrictToBlock hρ j' hj' (contDiffOn_one_of_two (hθ' z).smooth)
  have hgb := fun z => exists_bondGradNorm_restrictToBlock_bound hρ hr hc0 hx0.le hD j hj (hθ z)
  have hgb' := fun z => exists_bondGradNorm_restrictToBlock_bound hρ hr hc0 hx0.le hD' j' hj' (hθ' z)
  have hgn : ∀ z, IsBoundedContinuousOn κ ρ (restrictToBlock j (θ z)) := fun z => by
    obtain ⟨Mz, h0, hMz⟩ := hgb z
    exact isBoundedContinuousOn_of_bondGradNorm_le hρ (hgs z) h0 hMz
  have hgn' : ∀ z, IsBoundedContinuousOn κ ρ (restrictToBlock j' (θ' z)) := fun z => by
    obtain ⟨Mz, h0, hMz⟩ := hgb' z
    exact isBoundedContinuousOn_of_bondGradNorm_le hρ (hgs' z) h0 hMz
  have hsplit : ∀ ξ ∈ openPolyball κ ρ, B ξ - A ξ =
      ((∑ z, Δ z ξ) + ∑ z ∈ M'ᶜ, restrictToBlock j' (θ' z) ξ) - ∑ z ∈ Mᶜ, restrictToBlock j (θ z) ξ := by
    intro ξ hξ
    have h1 := hsum _ (pushforwardField_mem_openPolyball hρ j hj hξ)
    have h2 := hsum' _ (pushforwardField_mem_openPolyball hρ j' hj' hξ)
    simp only [hA, hB, h1, h2, hΔ, restrictToBlock, Finset.sum_sub_distrib]
    have s1 := Finset.sum_add_sum_compl M (fun z => θ z (pushforwardField j ξ))
    have s2 := Finset.sum_add_sum_compl M' (fun z => θ' z (pushforwardField j' ξ))
    have s3 : ∑ z : {z // z ∈ M}, θ z.1 (pushforwardField j ξ) = ∑ z ∈ M, θ z (pushforwardField j ξ) :=
      Finset.sum_coe_sort M (fun z => θ z (pushforwardField j ξ))
    have s4 : ∑ z : {z // z ∈ M}, θ' (φ z).1 (pushforwardField j' ξ) = ∑ z ∈ M', θ' z (pushforwardField j' ξ) := by
      rw [Equiv.sum_comp φ (fun z : {z // z ∈ M'} => θ' z.1 (pushforwardField j' ξ))]
      exact Finset.sum_coe_sort M' (fun z => θ' z (pushforwardField j' ξ))
    rw [s3, s4, ← s1, ← s2]
    ring
  have e1 : ballCovariance (cutoffFactor ρ p) T Hv (fun ξ => B ξ - A ξ) =
      ((∑ z, ballCovariance (cutoffFactor ρ p) T Hv (Δ z)) +
        ∑ z ∈ M'ᶜ, ballCovariance (cutoffFactor ρ p) T Hv (restrictToBlock j' (θ' z))) -
        ∑ z ∈ Mᶜ, ballCovariance (cutoffFactor ρ p) T Hv (restrictToBlock j (θ z)) := by
    have n1 : IsBoundedContinuousOn κ ρ (fun ξ => ∑ z, Δ z ξ) :=
      IsBoundedContinuousOn.sum _ _ fun z _ => hΔn z
    have n2 : IsBoundedContinuousOn κ ρ (fun ξ => ∑ z ∈ M'ᶜ, restrictToBlock j' (θ' z) ξ) :=
      IsBoundedContinuousOn.sum _ _ fun z _ => hgn' z
    have n3 : IsBoundedContinuousOn κ ρ (fun ξ => ∑ z ∈ Mᶜ, restrictToBlock j (θ z) ξ) :=
      IsBoundedContinuousOn.sum _ _ fun z _ => hgn z
    rw [ballCovariance_congr F (fun _ _ => rfl) hsplit, ballCovariance_sub_right F hvn (n1.add n2) n3,
      ballCovariance_add_right F hvn n1 n2,
      ballCovariance_sum_right F hvn _ _ fun z _ => hΔn z, ballCovariance_sum_right F hvn _ _ fun z _ => hgn' z,
      ballCovariance_sum_right F hvn _ _ fun z _ => hgn z]
  have c1 : ∀ z : {z // z ∈ M}, |ballCovariance (cutoffFactor ρ p) T Hv (Δ z)| ≤
      (x * lam / 4)⁻¹ * (c * G) * S * (c * ε * G * S * Real.exp (-(r / 4 * D z.1 Y))) := by
    intro z
    obtain ⟨Mz, h0, hMz⟩ := hΔb z
    have hM0 : 0 ≤ M₀ + M₁ := hMv0
    obtain ⟨Mc, hMc⟩ := exists_common_bound hρ hHv (hΔs z) hM0 h0 hMv hMz
    have h1 := abs_ballCovariance_le_of_decay (B := c * ε * G) (z := Y) (z' := z.1) hρ hr hD Sz hm0 hSk hHv
      (hΔs z) hMc (by positivity) (by positivity) hHn (fun k => by
        have := ballL2Norm_le_of_near_majorant (a := c * ε * Real.exp (-(2 * r * D (pos (j k)) z.1))) hρ F Sz
          (isBoundedContinuousOn_bondGradNorm hρ (hΔs z) hMz k) (by positivity) hx0.le z.1 (fun ξ hξ => by
            rw [abs_of_nonneg (bondGradNorm_nonneg _ k ξ)]
            refine (hcomp z ξ hξ k).trans (le_of_eq ?_)
            ring)
        refine this.trans (le_of_eq ?_)
        ring)
    refine h1.trans ?_
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact exp_neg_mul_le_of_le (by linarith) (hnn _ _)
  have far : ∀ {d : ℝ}, R / 8 ≤ d → Real.exp (-(r / 2 * d)) ≤ Real.exp (-(r / 4 * d)) * e :=
    fun hd => exp_neg_half_le_of_far hr hd
  have c2 : ∀ z ∈ Mᶜ, |ballCovariance (cutoffFactor ρ p) T Hv (restrictToBlock j (θ z))| ≤
      (x * lam / 4)⁻¹ * (c * G) * S * (c * G * S * (Real.exp (-(r / 4 * D z Y)) * e)) := by
    intro z hz
    obtain ⟨Mz, h0, hMz⟩ := hgb z
    obtain ⟨Mc, hMc⟩ := exists_common_bound hρ hHv (hgs z) hMv0 h0 hMv hMz
    have h1 := abs_ballCovariance_le_of_decay (B := c * G) (z := Y) (z' := z) hρ hr hD Sz hm0 hSk hHv (hgs z)
      hMc (by positivity) (by positivity) hHn (fun k => by
        have key := ballL2Norm_bondGradNorm_le (a := c) (w := Real.exp (-(2 ^ 5 * r * D (pos (j k)) z))) hρ
          hx0.le F Sz (hgs z) hc0 hMz z (Real.exp_pos _).le
          (fun ξ hξ => bondGradNorm_restrictToBlock_le_decay hρ j hj (hθ z) hξ k)
        refine key.trans ?_
        have hw : Real.exp (-(2 ^ 5 * r * D (pos (j k)) z)) ≤ Real.exp (-(2 * r * D (pos (j k)) z)) :=
          exp_neg_mul_le_of_le (by linarith) (hnn _ _)
        calc c * Real.exp (-(2 ^ 5 * r * D (pos (j k)) z)) * G
            = c * G * Real.exp (-(2 ^ 5 * r * D (pos (j k)) z)) := by ring
          _ ≤ _ := mul_le_mul_of_nonneg_left hw (by positivity))
    refine h1.trans ?_
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact far (hfar z (by simpa using hz))
  have c3 : ∀ z ∈ M'ᶜ, |ballCovariance (cutoffFactor ρ p) T Hv (restrictToBlock j' (θ' z))| ≤
      (x * lam / 4)⁻¹ * (c * G) * S * (c * G * S * (Real.exp (-(r / 4 * D' z Y')) * e)) := by
    intro z hz
    obtain ⟨Mz, h0, hMz⟩ := hgb' z
    obtain ⟨Mc, hMc⟩ := exists_common_bound hρ hHv (hgs' z) hMv0 h0 hMv hMz
    have h1 := abs_ballCovariance_le_of_decay (B := c * G) (z := Y') (z' := z) hρ hr hD' Sz' hm0 hSk' hHv
      (hgs' z) hMc (by positivity) (by positivity) hHn' (fun k => by
        have key := ballL2Norm_bondGradNorm_le (a := c) (w := Real.exp (-(2 ^ 5 * r * D' (pos' (j' k)) z))) hρ
          hx0.le F Sz' (hgs' z) hc0 hMz z (Real.exp_pos _).le
          (fun ξ hξ => bondGradNorm_restrictToBlock_le_decay hρ j' hj' (hθ' z) hξ k)
        refine key.trans ?_
        have hw : Real.exp (-(2 ^ 5 * r * D' (pos' (j' k)) z)) ≤
            Real.exp (-(2 * r * D' (pos' (j' k)) z)) :=
          exp_neg_mul_le_of_le (by linarith) (hnn' _ _)
        calc c * Real.exp (-(2 ^ 5 * r * D' (pos' (j' k)) z)) * G
            = c * G * Real.exp (-(2 ^ 5 * r * D' (pos' (j' k)) z)) := by ring
          _ ≤ _ := mul_le_mul_of_nonneg_left hw (by positivity))
    refine h1.trans ?_
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact far (hfar' z (by simpa using hz))
  have s1 : ∑ z : {z // z ∈ M}, |ballCovariance (cutoffFactor ρ p) T Hv (Δ z)| ≤
      (x * lam / 4)⁻¹ * (c * G) * S * (c * ε * G * S * S) := by
    refine (Finset.sum_le_sum fun z _ => c1 z).trans ?_
    rw [← Finset.mul_sum, ← Finset.mul_sum]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    have h1 : ∑ z : {z // z ∈ M}, Real.exp (-(r / 4 * D z.1 Y)) =
        ∑ z ∈ M, Real.exp (-(r / 4 * D z Y)) :=
      Finset.sum_coe_sort M (fun z => Real.exp (-(r / 4 * D z Y)))
    rw [h1]
    exact (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ M)
      fun z _ _ => (Real.exp_pos _).le).trans (hSp Y)
  have s2 : ∑ z ∈ Mᶜ, |ballCovariance (cutoffFactor ρ p) T Hv (restrictToBlock j (θ z))| ≤
      (x * lam / 4)⁻¹ * (c * G) * S * (c * G * S * (S * e)) := by
    refine (Finset.sum_le_sum c2).trans ?_
    rw [← Finset.mul_sum, ← Finset.mul_sum, ← Finset.sum_mul]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply mul_le_mul_of_nonneg_right _ he.le
    exact (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ Mᶜ)
      fun z _ _ => (Real.exp_pos _).le).trans (hSp Y)
  have s3 : ∑ z ∈ M'ᶜ, |ballCovariance (cutoffFactor ρ p) T Hv (restrictToBlock j' (θ' z))| ≤
      (x * lam / 4)⁻¹ * (c * G) * S * (c * G * S * (S * e)) := by
    refine (Finset.sum_le_sum c3).trans ?_
    rw [← Finset.mul_sum, ← Finset.mul_sum, ← Finset.sum_mul]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply mul_le_mul_of_nonneg_right _ he.le
    exact (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ M'ᶜ)
      fun z _ _ => (Real.exp_pos _).le).trans (hSp2 Y')
  have t2 : |ballCovariance (cutoffFactor ρ p) T Hv (fun ξ => B ξ - A ξ)| ≤
      (x * lam / 4)⁻¹ * (c * G) * S * (c * ε * G * S * S) +
        (x * lam / 4)⁻¹ * (c * G) * S * (c * G * S * (S * e)) +
        (x * lam / 4)⁻¹ * (c * G) * S * (c * G * S * (S * e)) := by
    rw [e1]
    refine (abs_sub _ _).trans ?_
    refine add_le_add ((abs_add_le _ _).trans (add_le_add ?_ ?_)) ?_
    · exact (Finset.abs_sum_le_sum_abs _ _).trans s1
    · exact (Finset.abs_sum_le_sum_abs _ _).trans s3
    · exact (Finset.abs_sum_le_sum_abs _ _).trans s2
  have tt : |ballExpectation (cutoffFactor ρ p) T (fun ξ => restrictToBlock j' H' ξ - restrictToBlock j H ξ) -
      ballCovariance (cutoffFactor ρ p) T Hv (fun ξ => B ξ - A ξ)| ≤ _ :=
    (abs_sub _ _).trans (add_le_add t1 t2)
  exact tt.trans (comparison_constants_le hlam hSn hx hc hε (Real.exp_pos _))
end YangMills.Construction.ColdStepAtMirrorFrames
end
