import YangMills.Construction.ColdChainAtEveryLevel.FractionalIntegrationOnTheLatticeProof
import YangMills.Construction.ClusterExpansionOfAStep.ConvexityOfASetting
import YangMills.Construction.ClusterExpansionOfAStep.CostsOfTwoSettings
import YangMills.Construction.ClusterExpansionOfAStep.GradientsOfTwoSettings
import YangMills.Construction.ClusterExpansionOfAStep.PowersAgainstAnExponential
import YangMills.Construction.ClusterExpansionOfAStep.ShiftsOfTwoSettings
import YangMills.Construction.ClusterExpansionOfAStep.StateDensitiesOfTwoSettings
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
open MeasureTheory
namespace YangMills.Construction
open BlockAverages LumpContours ColdStepAtMirrorFrames StepSettings TorusFields TorusLumps RenormalizationStepParameters BlockOffsets
  TorusBalls SettingShifts
namespace ClusterExpansionOfAStep
namespace SettingGradients
set_option linter.unusedSectionVars false
section Calculus
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
theorem abs_line_remainder_le {g g' g'' : ℝ → ℝ} {M l : ℝ} (hl : 0 ≤ l)
    (h1 : ∀ t ∈ Set.Icc 0 l, HasDerivAt g (g' t) t) (h2 : ∀ t ∈ Set.Icc 0 l, HasDerivAt g' (g'' t) t)
    (hM : ∀ t ∈ Set.Icc 0 l, |g'' t| ≤ M) : |g l - g 0 - l * g' 0| ≤ M * l ^ 2 := by
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0 ⟨le_rfl, hl⟩)
  have a : ∀ t ∈ Set.Icc 0 l, |g' t - g' 0| ≤ M * l := by
    intro t ht
    have := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (f := g') (f' := g'')
      (s := Set.Icc 0 l) (C := M) (x := 0) (y := t)
      (fun u hu => (h2 u hu).hasDerivWithinAt) (fun u hu => by rw [Real.norm_eq_abs]; exact hM u hu)
      (convex_Icc 0 l) ⟨le_rfl, hl⟩ ht
    simp only [Real.norm_eq_abs, sub_zero] at this
    have h3 : |t| ≤ l := by rw [abs_of_nonneg ht.1]; exact ht.2
    exact this.trans (by gcongr)
  have b := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (f := fun t => g t - t * g' 0)
    (f' := fun t => g' t - g' 0) (s := Set.Icc 0 l) (C := M * l) (x := 0) (y := l)
    (fun u hu => by
      have h3 : HasDerivAt (fun t : ℝ => t * g' 0) (1 * g' 0) u := (hasDerivAt_id' u).mul_const _
      have h5 : HasDerivAt (fun t => g t - t * g' 0) (g' u - 1 * g' 0) u := (h1 u hu).sub h3
      exact (h5.congr_deriv (by ring)).hasDerivWithinAt)
    (fun u hu => by rw [Real.norm_eq_abs]; exact a u hu)
    (convex_Icc 0 l) ⟨le_rfl, hl⟩ ⟨hl, le_rfl⟩
  simp only [Real.norm_eq_abs, sub_zero, zero_mul] at b
  have e : g l - l * g' 0 - g 0 = g l - g 0 - l * g' 0 := by ring
  rw [e, abs_of_nonneg hl] at b
  calc _ ≤ M * l * l := b
    _ = M * l ^ 2 := by ring
theorem abs_fderiv_le_of_oscillation {D : E → ℝ} {U : Set E} {ρ M Q : ℝ} (hρ : 0 < ρ) (hM : 0 < M) (hQ : 0 < Q)
    (hQM : Q ≤ M * ρ ^ 2) (hU : IsOpen U) (hsub : Metric.closedBall (0 : E) ρ ⊆ U) (hD : ContDiffOn ℝ 2 D U)
    (h2 : ∀ v ∈ Metric.closedBall (0 : E) ρ, ∀ X : E, ‖X‖ = 1 → |deriv (deriv fun t : ℝ => D (v + t • X)) 0| ≤ M)
    (hosc : ∀ v ∈ Metric.closedBall (0 : E) ρ, ∀ v' ∈ Metric.closedBall (0 : E) ρ, |D v' - D v| ≤ Q)
    {v : E} (hv : v ∈ Metric.closedBall (0 : E) ρ) {X : E} (hX : ‖X‖ = 1) :
    |fderiv ℝ D v X| ≤ 5 * Real.sqrt (Q * M) := by
  have hdiff : ∀ z ∈ U, DifferentiableAt ℝ D z := fun z hz =>
    (hD.contDiffAt (hU.mem_nhds hz)).differentiableAt (by norm_num)
  have taylor : ∀ w : E, v + w ∈ Metric.closedBall (0 : E) ρ → |D (v + w) - D v - fderiv ℝ D v w| ≤ M * ‖w‖ ^ 2 := by
    intro w hw
    by_cases hw0 : w = 0
    · subst hw0
      simp
    have hl : 0 < ‖w‖ := norm_pos_iff.mpr hw0
    set Y : E := (‖w‖)⁻¹ • w with hY
    have hYn : ‖Y‖ = 1 := by
      rw [hY, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hl.ne']
    have hline : ∀ t ∈ Set.Icc 0 ‖w‖, v + t • Y ∈ Metric.closedBall (0 : E) ρ := by
      intro t ht
      have e : v + t • Y = (1 - t / ‖w‖) • v + (t / ‖w‖) • (v + w) := by
        rw [hY, smul_smul, smul_add]
        have : t * (‖w‖)⁻¹ = t / ‖w‖ := by ring
        rw [this, sub_smul, one_smul]
        abel
      rw [e]
      have c := convex_closedBall (0 : E) ρ
      refine c hv hw ?_ ?_ (by ring)
      · rw [sub_nonneg, div_le_one hl]; exact ht.2
      · exact div_nonneg ht.1 hl.le
    have hcd : ∀ z ∈ U, ContDiffAt ℝ 2 D z := fun z hz => hD.contDiffAt (hU.mem_nhds hz)
    have hlin : ∀ t : ℝ, HasDerivAt (fun t : ℝ => v + t • Y) Y t := fun t => by
      simpa using ((hasDerivAt_id t).smul_const Y).const_add v
    have d1 : ∀ t ∈ Set.Icc 0 ‖w‖, HasDerivAt (fun t : ℝ => D (v + t • Y)) (fderiv ℝ D (v + t • Y) Y) t := by
      intro t ht
      exact (hdiff _ (hsub (hline t ht))).hasFDerivAt.comp_hasDerivAt t (hlin t)
    have d2 : ∀ t ∈ Set.Icc 0 ‖w‖, HasDerivAt (fun t : ℝ => fderiv ℝ D (v + t • Y) Y)
        (deriv (deriv fun τ : ℝ => D ((v + t • Y) + τ • Y)) 0) t := by
      intro t ht
      have hz := hsub (hline t ht)
      have hdf : DifferentiableAt ℝ (fun z => fderiv ℝ D z Y) (v + t • Y) := by
        have hc := (hcd _ hz).fderiv_right (m := 1) (by norm_num)
        exact (hc.clm_apply contDiffAt_const).differentiableAt (by norm_num)
      have h := hdf.hasFDerivAt.comp_hasDerivAt t (hlin t)
      have ev : (deriv fun τ : ℝ => D ((v + t • Y) + τ • Y)) =ᶠ[nhds 0]
          fun τ => fderiv ℝ D ((v + t • Y) + τ • Y) Y := by
        have hopen : ∀ᶠ τ : ℝ in nhds 0, (v + t • Y) + τ • Y ∈ U := by
          have hc : ContinuousAt (fun τ : ℝ => (v + t • Y) + τ • Y) 0 := by fun_prop
          exact hc.eventually_mem (by simpa using hU.mem_nhds hz)
        filter_upwards [hopen] with τ hτ
        have h3 : HasDerivAt (fun τ : ℝ => (v + t • Y) + τ • Y) Y τ := by
          simpa using ((hasDerivAt_id τ).smul_const Y).const_add (v + t • Y)
        exact ((hdiff _ hτ).hasFDerivAt.comp_hasDerivAt τ h3).deriv
      rw [ev.deriv_eq]
      have h4 : HasDerivAt (fun τ : ℝ => fderiv ℝ D ((v + t • Y) + τ • Y) Y) (fderiv ℝ (fun z => fderiv ℝ D z Y) (v + t • Y) Y) 0 := by
        have h3 : HasDerivAt (fun τ : ℝ => (v + t • Y) + τ • Y) Y 0 := by
          simpa using ((hasDerivAt_id (0 : ℝ)).smul_const Y).const_add (v + t • Y)
        have hdf' : HasFDerivAt (fun z => fderiv ℝ D z Y) (fderiv ℝ (fun z => fderiv ℝ D z Y) (v + t • Y)) ((v + t • Y) + (0 : ℝ) • Y) := by
          simpa using hdf.hasFDerivAt
        exact hdf'.comp_hasDerivAt (0 : ℝ) h3
      rw [h4.deriv]
      exact h
    have rem := abs_line_remainder_le hl.le d1 d2 (fun t ht => h2 _ (hline t ht) Y hYn)
    have e1 : v + ‖w‖ • Y = v + w := by
      rw [hY, smul_smul, mul_inv_cancel₀ hl.ne', one_smul]
    have e2 : ‖w‖ * fderiv ℝ D v Y = fderiv ℝ D v w := by
      rw [← smul_eq_mul, ← map_smul, hY, smul_smul, mul_inv_cancel₀ hl.ne', one_smul]
    simp only [e1, zero_smul, add_zero] at rem
    rw [e2] at rem
    exact rem
  set r₀ := Real.sqrt (Q / M) with hr₀
  have hr₀pos : 0 < r₀ := Real.sqrt_pos.mpr (div_pos hQ hM)
  have hr₀sq : r₀ ^ 2 = Q / M := Real.sq_sqrt (div_pos hQ hM).le
  have hr₀le : r₀ ≤ ρ := by
    rw [hr₀]
    refine Real.sqrt_le_iff.mpr ⟨hρ.le, ?_⟩
    rw [div_le_iff₀ hM]
    linarith [mul_comm M (ρ ^ 2)]
  have hvn : ‖v‖ ≤ ρ := by simpa using hv
  set vb : E := (1 - r₀ / ρ) • v with hvb
  have h1r : 0 ≤ 1 - r₀ / ρ := by rw [sub_nonneg, div_le_one hρ]; exact hr₀le
  have hvbn : ‖vb‖ ≤ ρ - r₀ := by
    rw [hvb, norm_smul, Real.norm_eq_abs, abs_of_nonneg h1r]
    calc (1 - r₀ / ρ) * ‖v‖ ≤ (1 - r₀ / ρ) * ρ := by gcongr
      _ = ρ - r₀ := by field_simp
  have hvd : ‖vb - v‖ ≤ r₀ := by
    have : vb - v = (-(r₀ / ρ)) • v := by
      rw [hvb, sub_smul, one_smul, neg_smul]
      abel
    rw [this, norm_smul, norm_neg, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    calc r₀ / ρ * ‖v‖ ≤ r₀ / ρ * ρ := by gcongr
      _ = r₀ := by field_simp
  have hp : ∀ σ : ℝ, |σ| = 1 → v + (vb - v + (σ * r₀) • X) ∈ Metric.closedBall (0 : E) ρ ∧
      ‖vb - v + (σ * r₀) • X‖ ≤ 2 * r₀ := by
    intro σ hσ
    have hn : ‖(σ * r₀) • X‖ = r₀ := by
      rw [norm_smul, hX, mul_one, Real.norm_eq_abs, abs_mul, hσ, one_mul, abs_of_pos hr₀pos]
    constructor
    · have e : v + (vb - v + (σ * r₀) • X) = vb + (σ * r₀) • X := by abel
      rw [e, mem_closedBall_zero_iff]
      calc ‖vb + (σ * r₀) • X‖ ≤ ‖vb‖ + ‖(σ * r₀) • X‖ := norm_add_le _ _
        _ ≤ ρ := by rw [hn]; linarith
    · calc _ ≤ ‖vb - v‖ + ‖(σ * r₀) • X‖ := norm_add_le _ _
        _ ≤ 2 * r₀ := by rw [hn]; linarith
  have bound : ∀ σ : ℝ, |σ| = 1 → |fderiv ℝ D v (vb - v + (σ * r₀) • X)| ≤ Q + M * (2 * r₀) ^ 2 := by
    intro σ hσ
    obtain ⟨h3, h4⟩ := hp σ hσ
    have t := taylor _ h3
    have o := hosc v hv _ h3
    have e : fderiv ℝ D v (vb - v + (σ * r₀) • X) =
        (D (v + (vb - v + (σ * r₀) • X)) - D v) -
          (D (v + (vb - v + (σ * r₀) • X)) - D v - fderiv ℝ D v (vb - v + (σ * r₀) • X)) := by ring
    rw [e]
    refine (abs_sub _ _).trans ?_
    have : M * ‖vb - v + (σ * r₀) • X‖ ^ 2 ≤ M * (2 * r₀) ^ 2 := by gcongr
    linarith
  have b1 := bound 1 (by simp)
  have b2 := bound (-1) (by simp)
  have e : (2 * r₀) * fderiv ℝ D v X = fderiv ℝ D v (vb - v + (1 * r₀) • X) -
      fderiv ℝ D v (vb - v + (-1 * r₀) • X) := by
    simp only [map_add, map_smul, smul_eq_mul]
    ring
  have h5 : (2 * r₀) * |fderiv ℝ D v X| ≤ 2 * (Q + M * (2 * r₀) ^ 2) := by
    have : |(2 * r₀) * fderiv ℝ D v X| = (2 * r₀) * |fderiv ℝ D v X| := by
      rw [abs_mul, abs_of_pos (by positivity)]
    rw [← this, e]
    refine (abs_sub _ _).trans ?_
    linarith
  have h6 : |fderiv ℝ D v X| ≤ Q / r₀ + 4 * M * r₀ := by
    have : Q / r₀ + 4 * M * r₀ = (2 * (Q + M * (2 * r₀) ^ 2)) / (2 * r₀) := by
      field_simp
      ring
    rw [this, le_div_iff₀ (by positivity)]
    linarith
  have hs : Real.sqrt (Q * M) = M * r₀ := by
    have hnn : 0 ≤ M * r₀ := by positivity
    rw [show Q * M = (M * r₀) ^ 2 by rw [mul_pow, hr₀sq]; field_simp]
    exact Real.sqrt_sq hnn
  have hq : Q / r₀ = M * r₀ := by
    have : Q = M * r₀ ^ 2 := by rw [hr₀sq]; field_simp
    rw [this]
    field_simp
  rw [hs]
  rw [hq] at h6
  linarith
end Calculus
section Sums
variable {R : StepSetup} {n n' : ℕ} [NeZero n] [NeZero n']
def LocallyClosePair (s : ChartSetting R n) (s' : ChartSetting R n') (A : TorusSite n → FreeCoords s.free → ℝ)
    (A' : TorusSite n' → FreeCoords s'.free → ℝ) (J : ℕ) (e : ℕ → ℝ) : Prop :=
  ∀ (Z : TorusSite n) (Z' : TorusSite n') (m' j : ℕ) (ζ : FreeCoords s.free) (ζ' : FreeCoords s'.free),
    SettingsAgreeNear s s' Z Z' m' → j ≤ m' → J ≤ j → CoordsAgreeNear s s' Z Z' j ζ ζ' → s.InBalls ζ → s'.InBalls ζ' →
    |A Z ζ - A' Z' ζ'| ≤ e j
theorem coordsAgreeNear_update_far (s : ChartSetting R n) {Z : TorusSite n} {j : ℕ} {η : FreeCoords s.free} (b : s.free)
    (v v₂ : EuclideanSpace ℝ (Fin 3)) (hb : ∀ q, IsNearIndex R.params.side j q → nearBond R.params.side Z q ≠ b.1) :
    CoordsAgreeNear s s Z Z j (Function.update η b v) (Function.update η b v₂) := by
  intro q hq
  simp only [ChartSetting.coordsByIndex]
  by_cases hf : nearBond R.params.side Z q ∈ s.free
  · rw [dif_pos hf, dif_pos hf, Function.update_of_ne (fun e => hb q hq (congrArg Subtype.val e)),
      Function.update_of_ne (fun e => hb q hq (congrArg Subtype.val e))]
  · rw [dif_neg hf, dif_neg hf]
theorem sum_far_update_le (hodd : Odd R.params.side) (s : ChartSetting R n) (hs : s.IsAdmissible)
    {A : TorusSite n → FreeCoords s.free → ℝ}
    {J : ℕ} {E₀ c A₀ : ℝ} (hE : 0 ≤ E₀) (_hc : 0 < c)
    (hA₀ : ∀ (n : ℕ) [NeZero n] (y : TorusSite n) (D : ℕ),
      ∑ Y ∈ Finset.univ.filter (fun Y : TorusSite n => D ≤ _root_.YangMills.Construction.TorusFields.supDist Y y), Real.exp (-(c * _root_.YangMills.Construction.TorusFields.supDist Y y)) ≤
        A₀ * Real.exp (-(c * D / 2)))
    (h11 : LocallyClosePair s s A A J fun j => E₀ * Real.exp (-(c * j))) {Y : TorusSite n} {q₀ : NearBondIndex}
    (hb : nearBond R.params.side Y q₀ ∈ s.free) (hq₀ : q₀.2.1 ∈ centredCube R.params.side) {η : FreeCoords s.free}
    (hη : s.InBalls η)
    {v v₂ : EuclideanSpace ℝ (Fin 3)} (hv : coordNorm v ≤ R.ballRadius) (hv₂ : coordNorm v₂ ≤ R.ballRadius) {k₁ : ℕ}
    (hk : J + 1 ≤ k₁) (hn : 3 ≤ n) (S : Finset (TorusSite n))
    (hS : ∀ Z, Z ∉ S → k₁ + 1 ≤ _root_.YangMills.Construction.TorusFields.supDist Z (Y + siteOfInt q₀.1)) :
    ∑ Z ∈ Finset.univ \ S, |A Z (Function.update η ⟨_, hb⟩ v₂) - A Z (Function.update η ⟨_, hb⟩ v)| ≤
      E₀ * Real.exp (2 * c) * (A₀ * Real.exp (-(c * (k₁ + 1 : ℕ) / 2))) := by
  have point : ∀ Z ∈ Finset.univ \ S,
      |A Z (Function.update η ⟨_, hb⟩ v₂) - A Z (Function.update η ⟨_, hb⟩ v)| ≤
        E₀ * Real.exp (2 * c) * Real.exp (-(c * _root_.YangMills.Construction.TorusFields.supDist Z (Y + siteOfInt q₀.1))) := by
    intro Z hZ
    have hD := hS Z (Finset.mem_sdiff.mp hZ).2
    set D := _root_.YangMills.Construction.TorusFields.supDist Z (Y + siteOfInt q₀.1) with hDdef
    have hhalf := two_mul_supDist_le Z (Y + siteOfInt q₀.1)
    rw [← hDdef] at hhalf
    have hag : SettingsAgreeNear s s Z Z (D - 2) := settingsAgreeNear_refl s hs Z (D - 2) (by omega)
    have hnear : ∀ q, IsNearIndex R.params.side (D - 2) q → nearBond R.params.side Z q ≠ (⟨_, hb⟩ : s.free).1 := by
      rintro ⟨h, o, i⟩ hq e
      simp only [nearBond, Prod.mk.injEq] at e
      have b1 := parentBlock_fineSite hodd Z h o hq.2
      have b2 := parentBlock_fineSite hodd Y q₀.1 q₀.2.1 hq₀
      rw [e.1, b2] at b1
      have : _root_.YangMills.Construction.TorusFields.supDist Z (Y + siteOfInt q₀.1) ≤ D - 2 := by
        rw [b1]
        refine _root_.YangMills.Construction.TorusFields.supDist_add_siteOfInt_le Z h (D - 2) fun l => ?_
        have hh : |h l| ≤ ((D - 2 : ℕ) : ℤ) := hq.1 l
        rw [Int.abs_eq_natAbs] at hh
        omega
      omega
    have key := h11 Z Z (D - 2) (D - 2) _ _ hag le_rfl (by omega)
      (coordsAgreeNear_update_far s ⟨_, hb⟩ v₂ v hnear)
      (inBalls_update s hη _ hv₂) (inBalls_update s hη _ hv)
    refine key.trans (le_of_eq ?_)
    have e : ((D - 2 : ℕ) : ℝ) = (D : ℝ) - 2 := by
      rw [Nat.cast_sub (by omega)]
      norm_num
    simp only [e]
    rw [mul_assoc, ← Real.exp_add]
    congr 2
    ring
  refine (Finset.sum_le_sum point).trans ?_
  rw [← Finset.mul_sum]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  refine le_trans ?_ (hA₀ n (Y + siteOfInt q₀.1) (k₁ + 1))
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun _ _ _ => (Real.exp_pos _).le
  intro Z hZ
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hS Z (Finset.mem_sdiff.mp hZ).2⟩
def offsetBox (h₀ : Fin 4 → ℤ) (k₁ : ℕ) : Finset (Fin 4 → ℤ) :=
  Fintype.piFinset fun i => Finset.Icc (h₀ i - k₁) (h₀ i + k₁)
theorem card_offsetBox (h₀ : Fin 4 → ℤ) (k₁ : ℕ) : (offsetBox h₀ k₁).card = (2 * k₁ + 1) ^ 4 := by
  simp only [offsetBox, Fintype.card_piFinset, Int.card_Icc]
  have : ∀ i, (h₀ i + (k₁ : ℤ) + 1 - (h₀ i - k₁)).toNat = 2 * k₁ + 1 := fun i => by omega
  simp [this]
theorem mem_offsetBox {h₀ h : Fin 4 → ℤ} {k₁ : ℕ} : h ∈ offsetBox h₀ k₁ ↔ ∀ i, |h i - h₀ i| ≤ k₁ := by apply _root_.YangMills.Construction.LatticeFractionalIntegration.mem_cube <;> assumption
theorem abs_sum_update_sub_le (hodd : Odd R.params.side) {s : ChartSetting R n} {s' : ChartSetting R n'}
    (hs : s.IsAdmissible) (hs' : s'.IsAdmissible)
    {A : TorusSite n → FreeCoords s.free → ℝ} {A' : TorusSite n' → FreeCoords s'.free → ℝ} {J : ℕ} {E₀ c A₀ : ℝ}
    (hE : 0 ≤ E₀) (hc : 0 < c)
    (hA₀ : ∀ (n : ℕ) [NeZero n] (y : TorusSite n) (D : ℕ),
      ∑ Y ∈ Finset.univ.filter (fun Y : TorusSite n => D ≤ _root_.YangMills.Construction.TorusFields.supDist Y y), Real.exp (-(c * _root_.YangMills.Construction.TorusFields.supDist Y y)) ≤
        A₀ * Real.exp (-(c * D / 2)))
    (h12 : LocallyClosePair s s' A A' J fun j => E₀ * Real.exp (-(c * j)))
    (h11 : LocallyClosePair s s A A J fun j => E₀ * Real.exp (-(c * j)))
    (h22 : LocallyClosePair s' s' A' A' J fun j => E₀ * Real.exp (-(c * j)))
    {Y : TorusSite n} {Y' : TorusSite n'} {m k : ℕ} (hag : SettingsAgreeNear s s' Y Y' m) (hkm : k ≤ m)
    {η : FreeCoords s.free} {η' : FreeCoords s'.free} (hη : s.InBalls η) (hη' : s'.InBalls η')
    (hn : CoordsAgreeNear s s' Y Y' k η η') {q₀ : NearBondIndex} (hb : nearBond R.params.side Y q₀ ∈ s.free)
    (hb' : nearBond R.params.side Y' q₀ ∈ s'.free) (hq₀ : IsNearIndex R.params.side (k / 2) q₀)
    {v v₂ : EuclideanSpace ℝ (Fin 3)} (hv : coordNorm v ≤ R.ballRadius) (hv₂ : coordNorm v₂ ≤ R.ballRadius)
    (hk : J + 1 ≤ k / 4) :
    |(∑ Z, A Z (Function.update η ⟨_, hb⟩ v₂) - ∑ Z, A Z (Function.update η ⟨_, hb⟩ v)) -
        (∑ Z, A' Z (Function.update η' ⟨_, hb'⟩ v₂) - ∑ Z, A' Z (Function.update η' ⟨_, hb'⟩ v))| ≤
      ((2 * (k / 4 : ℕ) + 1 : ℕ) : ℝ) ^ 4 * (2 * (E₀ * Real.exp (-(c * (k / 4 : ℕ))))) +
        2 * (E₀ * Real.exp (2 * c) * (A₀ * Real.exp (-(c * (k / 4 + 1 : ℕ) / 2)))) := by
  classical
  set k₁ := k / 4 with hk₁
  have side := hag.lt_extent
  have side' := hag.lt_extent'
  have hq₀k : IsNearIndex R.params.side k q₀ := ⟨fun l => by
    have := hq₀.1 l
    omega, hq₀.2⟩
  have hfree : ∀ q, IsNearIndex R.params.side k q →
      (nearBond R.params.side Y q ∈ s.free ↔ nearBond R.params.side Y' q ∈ s'.free) :=
    fun q hq => hag.free_iff q ⟨fun l => by
      have := hq.1 l
      omega, hq.2⟩
  have nearv : ∀ w, CoordsAgreeNear s s' Y Y' k (Function.update η ⟨_, hb⟩ w)
      (Function.update η' ⟨_, hb'⟩ w) := fun w =>
    coordsAgreeNear_update hodd (by omega) (by omega) hfree hn hq₀k w
  set Bx := offsetBox q₀.1 k₁ with hBx
  have bound : ∀ h ∈ Bx, ∀ l, |h l| + k₁ ≤ k := by
    intro h hh l
    have a := mem_offsetBox.mp hh l
    have b := hq₀.1 l
    have c1 : |h l| ≤ |h l - q₀.1 l| + |q₀.1 l| := by
      have := abs_add_le (h l - q₀.1 l) (q₀.1 l)
      simpa using this
    omega
  have inj : Set.InjOn (fun h : Fin 4 → ℤ => Y + siteOfInt h) Bx := by
    intro h hh h₂ hh₂ e
    refine eq_of_siteOfInt_eq (k := k) (by omega) (fun l => ?_) (fun l => ?_) (add_left_cancel e)
    · have := bound h hh l
      omega
    · have := bound h₂ hh₂ l
      omega
  have inj' : Set.InjOn (fun h : Fin 4 → ℤ => Y' + siteOfInt h) Bx := by
    intro h hh h₂ hh₂ e
    refine eq_of_siteOfInt_eq (k := k) (by omega) (fun l => ?_) (fun l => ?_) (add_left_cancel e)
    · have := bound h hh l
      omega
    · have := bound h₂ hh₂ l
      omega
  set S := Bx.image fun h : Fin 4 → ℤ => Y + siteOfInt h with hS
  set S' := Bx.image fun h : Fin 4 → ℤ => Y' + siteOfInt h with hS'
  have farS : ∀ (N : ℕ) [NeZero N] (U : TorusSite N), ∀ Z, Z ∉ Bx.image (fun h : Fin 4 → ℤ => U + siteOfInt h) →
      k₁ + 1 ≤ _root_.YangMills.Construction.TorusFields.supDist Z (U + siteOfInt q₀.1) := by
    intro N _ U Z hZ
    by_contra hlt
    apply hZ
    have hlt : _root_.YangMills.Construction.TorusFields.supDist (U + siteOfInt q₀.1) Z ≤ k₁ := by
      rw [_root_.YangMills.Construction.TorusFields.supDist_comm]
      omega
    obtain ⟨e, he, hb₂⟩ := exists_offset_of_supDist (U + siteOfInt q₀.1) Z
    refine Finset.mem_image.mpr ⟨q₀.1 + e, mem_offsetBox.mpr fun l => ?_, ?_⟩
    · have := hb₂ l
      simp only [Pi.add_apply, add_sub_cancel_left]
      rw [Int.abs_eq_natAbs]
      omega
    · rw [_root_.YangMills.Construction.BlockOffsets.siteOfInt_add, ← add_assoc, ← he]
  set f : TorusSite n → ℝ := fun Z => A Z (Function.update η ⟨_, hb⟩ v₂) - A Z (Function.update η ⟨_, hb⟩ v) with hf
  set f' : TorusSite n' → ℝ := fun Z => A' Z (Function.update η' ⟨_, hb'⟩ v₂) - A' Z (Function.update η' ⟨_, hb'⟩ v)
    with hf'
  have e1 : ∑ Z, A Z (Function.update η ⟨_, hb⟩ v₂) - ∑ Z, A Z (Function.update η ⟨_, hb⟩ v) =
      ∑ h ∈ Bx, f (Y + siteOfInt h) + ∑ Z ∈ Finset.univ \ S, f Z := by
    rw [← Finset.sum_sub_distrib]
    have h3 := Finset.sum_sdiff (Finset.subset_univ S) (f := f)
    rw [Finset.sum_image inj] at h3
    rw [← h3, add_comm]
  have e2 : ∑ Z, A' Z (Function.update η' ⟨_, hb'⟩ v₂) - ∑ Z, A' Z (Function.update η' ⟨_, hb'⟩ v) =
      ∑ h ∈ Bx, f' (Y' + siteOfInt h) + ∑ Z ∈ Finset.univ \ S', f' Z := by
    rw [← Finset.sum_sub_distrib]
    have h3 := Finset.sum_sdiff (Finset.subset_univ S') (f := f')
    rw [Finset.sum_image inj'] at h3
    rw [← h3, add_comm]
  have hJ : J ≤ k₁ := by omega
  have near : ∀ h ∈ Bx, |f (Y + siteOfInt h) - f' (Y' + siteOfInt h)| ≤ 2 * (E₀ * Real.exp (-(c * k₁))) := by
    intro h hh
    have hsh : SettingsAgreeNear s s' (Y + siteOfInt h) (Y' + siteOfInt h) k₁ :=
      settingsAgreeNear_shift hag fun l => by
        have := bound h hh l
        omega
    have n1 := coordsAgreeNear_shift (nearv v₂) (bound h hh)
    have n2 := coordsAgreeNear_shift (nearv v) (bound h hh)
    have a := h12 _ _ k₁ k₁ _ _ hsh le_rfl hJ n1 (inBalls_update s hη _ hv₂) (inBalls_update s' hη' _ hv₂)
    have b := h12 _ _ k₁ k₁ _ _ hsh le_rfl hJ n2 (inBalls_update s hη _ hv) (inBalls_update s' hη' _ hv)
    simp only [hf, hf']
    have t : ∀ p p' r r' : ℝ, |p - p'| ≤ E₀ * Real.exp (-(c * k₁)) → |r - r'| ≤ E₀ * Real.exp (-(c * k₁)) →
        |(p - r) - (p' - r')| ≤ 2 * (E₀ * Real.exp (-(c * k₁))) := by
      intro p p' r r' h1 h2
      have e : (p - r) - (p' - r') = (p - p') - (r - r') := by ring
      rw [e]
      have := abs_sub (p - p') (r - r')
      linarith
    exact t _ _ _ _ a b
  have sumnear : |∑ h ∈ Bx, f (Y + siteOfInt h) - ∑ h ∈ Bx, f' (Y' + siteOfInt h)| ≤
      ((2 * k₁ + 1 : ℕ) : ℝ) ^ 4 * (2 * (E₀ * Real.exp (-(c * k₁)))) := by
    rw [← Finset.sum_sub_distrib]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    refine (Finset.sum_le_card_nsmul _ _ _ near).trans (le_of_eq ?_)
    rw [hBx, card_offsetBox, nsmul_eq_mul]
    push_cast
    ring
  have far1 := sum_far_update_le hodd s hs hE hc hA₀ h11 hb hq₀.2 hη hv hv₂ hk (by omega) S (farS n Y)
  have far2 := sum_far_update_le hodd s' hs' hE hc hA₀ h22 hb' hq₀.2 hη' hv hv₂ hk (by omega) S' (farS n' Y')
  have a1 : |∑ Z ∈ Finset.univ \ S, f Z| ≤ _ := (Finset.abs_sum_le_sum_abs _ _).trans far1
  have a2 : |∑ Z ∈ Finset.univ \ S', f' Z| ≤ _ := (Finset.abs_sum_le_sum_abs _ _).trans far2
  rw [e1, e2]
  have e3 : (∑ h ∈ Bx, f (Y + siteOfInt h) + ∑ Z ∈ Finset.univ \ S, f Z) -
      (∑ h ∈ Bx, f' (Y' + siteOfInt h) + ∑ Z ∈ Finset.univ \ S', f' Z) =
      (∑ h ∈ Bx, f (Y + siteOfInt h) - ∑ h ∈ Bx, f' (Y' + siteOfInt h)) + ∑ Z ∈ Finset.univ \ S, f Z -
        ∑ Z ∈ Finset.univ \ S', f' Z := by ring
  rw [e3]
  have t1 := abs_sub ((∑ h ∈ Bx, f (Y + siteOfInt h) - ∑ h ∈ Bx, f' (Y' + siteOfInt h)) + ∑ Z ∈ Finset.univ \ S, f Z)
    (∑ Z ∈ Finset.univ \ S', f' Z)
  have t2 := abs_add_le (∑ h ∈ Bx, f (Y + siteOfInt h) - ∑ h ∈ Bx, f' (Y' + siteOfInt h)) (∑ Z ∈ Finset.univ \ S, f Z)
  linarith
end Sums
section Derivative
variable {n n' : ℕ}
theorem mixedSecondDeriv_self_eq {free : Finset (TorusBond n)} (u : FreeCoords free → ℝ) (ζ : FreeCoords free)
    (b : free) (X : EuclideanSpace ℝ (Fin 3)) :
    mixedSecondDeriv u ζ b b X X = deriv (deriv fun t : ℝ => u (Function.update ζ b (ζ b + t • X))) 0 := by
  unfold mixedSecondDeriv
  set G : ℝ → ℝ := fun t => u (Function.update ζ b (ζ b + t • X)) with hG
  have inner : ∀ τ : ℝ, deriv (fun τ' : ℝ => u (Function.update (Function.update ζ b (ζ b + τ • X)) b
      ((Function.update ζ b (ζ b + τ • X)) b + τ' • X))) 0 = deriv G τ := by
    intro τ
    have e : (fun τ' : ℝ => u (Function.update (Function.update ζ b (ζ b + τ • X)) b
        ((Function.update ζ b (ζ b + τ • X)) b + τ' • X))) = fun τ' => G (τ + τ') := by
      funext τ'
      simp only [hG, Function.update_self, Function.update_idem, add_smul, add_assoc]
    rw [e, deriv_comp_const_add]
    simp
  simp only [inner]
theorem deriv_deriv_fun_sub {g g' : ℝ → ℝ} (h : ContDiffAt ℝ 2 g 0) (h' : ContDiffAt ℝ 2 g' 0) :
    deriv (deriv fun t => g t - g' t) 0 = deriv (deriv g) 0 - deriv (deriv g') 0 := by
  have ev : (deriv fun t => g t - g' t) =ᶠ[nhds 0] fun t => deriv g t - deriv g' t := by
    have e1 := h.eventually (by simp)
    have e2 := h'.eventually (by simp)
    filter_upwards [e1, e2] with t a b
    exact deriv_fun_sub (a.differentiableAt (by norm_num)) (b.differentiableAt (by norm_num))
  rw [ev.deriv_eq]
  have dd : ∀ {k : ℝ → ℝ}, ContDiffAt ℝ 2 k 0 → DifferentiableAt ℝ (deriv k) 0 := by
    intro k hk
    have e : deriv k = fun t => fderiv ℝ k t 1 := by
      funext t
      rfl
    rw [e]
    have hc := hk.fderiv_right (m := 1) (by norm_num)
    exact (hc.clm_apply contDiffAt_const).differentiableAt (by norm_num)
  exact deriv_fun_sub (dd h) (dd h')
theorem abs_directionalDeriv_sub_le {free : Finset (TorusBond n)} {free' : Finset (TorusBond n')}
    {f : FreeCoords free → ℝ}
    {f' : FreeCoords free' → ℝ} {U : Set (FreeCoords free)} {U' : Set (FreeCoords free')}
    {η : FreeCoords free} {η' : FreeCoords free'} {b : free} {b' : free'} {ρ M Q : ℝ} (hρ : 0 < ρ) (hM : 0 < M)
    (hQ : 0 < Q) (hQM : Q ≤ 2 * M * ρ ^ 2) (hU : IsOpen U) (hU' : IsOpen U') (hf : ContDiffOn ℝ 3 f U)
    (hf' : ContDiffOn ℝ 3 f' U') (hsub : ∀ v : EuclideanSpace ℝ (Fin 3), ‖v‖ ≤ ρ → Function.update η b v ∈ U)
    (hsub' : ∀ v : EuclideanSpace ℝ (Fin 3), ‖v‖ ≤ ρ → Function.update η' b' v ∈ U')
    (he : ∀ v : EuclideanSpace ℝ (Fin 3), ‖v‖ ≤ ρ → ∀ X : EuclideanSpace ℝ (Fin 3), ‖X‖ = 1 →
      |mixedSecondDeriv f (Function.update η b v) b b X X| ≤ M)
    (he' : ∀ v : EuclideanSpace ℝ (Fin 3), ‖v‖ ≤ ρ → ∀ X : EuclideanSpace ℝ (Fin 3), ‖X‖ = 1 →
      |mixedSecondDeriv f' (Function.update η' b' v) b' b' X X| ≤ M)
    (ho : ∀ v v₂ : EuclideanSpace ℝ (Fin 3), ‖v‖ ≤ ρ → ‖v₂‖ ≤ ρ →
      |(f (Function.update η b v₂) - f (Function.update η b v)) -
        (f' (Function.update η' b' v₂) - f' (Function.update η' b' v))| ≤ Q)
    (hb : η b = η' b') (hn : ‖η b‖ ≤ ρ) {X : EuclideanSpace ℝ (Fin 3)} (hX : ‖X‖ = 1) :
    |directionalDeriv f η b X - directionalDeriv f' η' b' X| ≤ 5 * Real.sqrt (Q * (2 * M)) := by
  set G : EuclideanSpace ℝ (Fin 3) → ℝ := fun v => f (Function.update η b v) with hG
  set G' : EuclideanSpace ℝ (Fin 3) → ℝ := fun v => f' (Function.update η' b' v) with hG'
  have cu : Continuous (Function.update η b) := continuous_const.update b continuous_id
  have cu' : Continuous (Function.update η' b') := continuous_const.update b' continuous_id
  set W : Set (EuclideanSpace ℝ (Fin 3)) := (Function.update η b) ⁻¹' U ∩ (Function.update η' b') ⁻¹' U' with hW
  have hWo : IsOpen W := (hU.preimage cu).inter (hU'.preimage cu')
  have sW : Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) ρ ⊆ W := fun v hv =>
    ⟨hsub v (by simpa using hv), hsub' v (by simpa using hv)⟩
  have cG : ContDiffOn ℝ 3 G W :=
    hf.comp (contDiff_update 3 η b).contDiffOn fun v hv => hv.1
  have cG' : ContDiffOn ℝ 3 G' W :=
    hf'.comp (contDiff_update 3 η' b').contDiffOn fun v hv => hv.2
  have atW : ∀ v ∈ W, ContDiffAt ℝ 3 G v ∧ ContDiffAt ℝ 3 G' v := fun v hv =>
    ⟨cG.contDiffAt (hWo.mem_nhds hv), cG'.contDiffAt (hWo.mem_nhds hv)⟩
  set D : EuclideanSpace ℝ (Fin 3) → ℝ := fun v => G v - G' v with hD
  have cD : ContDiffOn ℝ 2 D W := (cG.of_le (by norm_num)).sub (cG'.of_le (by norm_num))
  have h2 : ∀ v ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) ρ, ∀ Y : EuclideanSpace ℝ (Fin 3), ‖Y‖ = 1 →
      |deriv (deriv fun t : ℝ => D (v + t • Y)) 0| ≤ 2 * M := by
    intro v hv Y hY
    have hline : ContDiffAt ℝ 2 (fun t : ℝ => v + t • Y) 0 := by fun_prop
    have hl0 : v + (0 : ℝ) • Y = v := by simp
    have a1 : ContDiffAt ℝ 2 (fun t : ℝ => G (v + t • Y)) 0 := by
      have hh := ((atW v (sW hv)).1.of_le (by norm_num : (2 : WithTop ℕ∞) ≤ 3))
      rw [← hl0] at hh
      exact ContDiffAt.comp (g := G) (f := fun t : ℝ => v + t • Y) (0 : ℝ) hh hline
    have a2 : ContDiffAt ℝ 2 (fun t : ℝ => G' (v + t • Y)) 0 := by
      have hh := ((atW v (sW hv)).2.of_le (by norm_num : (2 : WithTop ℕ∞) ≤ 3))
      rw [← hl0] at hh
      exact ContDiffAt.comp (g := G') (f := fun t : ℝ => v + t • Y) (0 : ℝ) hh hline
    rw [show (fun t : ℝ => D (v + t • Y)) = fun t => G (v + t • Y) - G' (v + t • Y) from rfl,
      deriv_deriv_fun_sub a1 a2]
    have hvn : ‖v‖ ≤ ρ := by simpa using hv
    have e1 := he v hvn Y hY
    have e2 := he' v hvn Y hY
    rw [mixedSecondDeriv_self_eq] at e1 e2
    simp only [Function.update_self, Function.update_idem] at e1 e2
    have := abs_sub (deriv (deriv fun t : ℝ => G (v + t • Y)) 0) (deriv (deriv fun t : ℝ => G' (v + t • Y)) 0)
    linarith
  have hosc : ∀ v ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) ρ,
      ∀ v' ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) ρ, |D v' - D v| ≤ Q := by
    intro v hv v' hv'
    have := ho v v' (by simpa using hv) (by simpa using hv')
    have e : D v' - D v = (G v' - G v) - (G' v' - G' v) := by
      simp only [hD]
      ring
    rw [e]
    exact this
  have hv0 : η b ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) ρ := by simpa using hn
  have key := abs_fderiv_le_of_oscillation hρ (by positivity : 0 < 2 * M) hQ hQM hWo sW cD h2 hosc hv0 hX
  have dG : DifferentiableAt ℝ G (η b) := (atW _ (sW hv0)).1.differentiableAt (by norm_num)
  have dG' : DifferentiableAt ℝ G' (η b) := (atW _ (sW hv0)).2.differentiableAt (by norm_num)
  have hline : ∀ τ : ℝ, HasDerivAt (fun τ : ℝ => η b + τ • X) X τ := fun τ => by
    simpa using ((hasDerivAt_id τ).smul_const X).const_add (η b)
  have f1 : directionalDeriv f η b X = fderiv ℝ G (η b) X := by
    have h3 : HasFDerivAt G (fderiv ℝ G (η b)) (η b + (0 : ℝ) • X) := by simpa using dG.hasFDerivAt
    exact (h3.comp_hasDerivAt (0 : ℝ) (hline 0)).deriv
  have f2 : directionalDeriv f' η' b' X = fderiv ℝ G' (η b) X := by
    have h3 : HasFDerivAt G' (fderiv ℝ G' (η b)) (η b + (0 : ℝ) • X) := by simpa using dG'.hasFDerivAt
    have h4 := (h3.comp_hasDerivAt (0 : ℝ) (hline 0)).deriv
    unfold directionalDeriv
    rw [← hb]
    exact h4
  have f3 : fderiv ℝ D (η b) X = fderiv ℝ G (η b) X - fderiv ℝ G' (η b) X := by
    have := (dG.hasFDerivAt.sub dG'.hasFDerivAt).fderiv
    erw [this]
    rfl
  rw [f1, f2, ← f3]
  exact key
end Derivative
section Main
variable {R : StepSetup} {n n' : ℕ} [NeZero n] [NeZero n']
theorem le_mul_sub_sub_of_large {L j : ℕ} (hL : 2 ^ 40 ≤ L) (hj : 4 ≤ j) : j ≤ L * j - L - 2 ^ 16 := by
  obtain ⟨i, rfl⟩ : ∃ i, j = i + 4 := ⟨j - 4, by omega⟩
  have : (i + 4) + L + 2 ^ 16 ≤ L * (i + 4) := by nlinarith
  omega
theorem pow_mul_le_mul_sub_of_large {L j : ℕ} (hL : 2 ^ 40 ≤ L) (hj : 4 ≤ j) : 2 ^ 32 * j ≤ L * j - 2 * L := by
  obtain ⟨i, rfl⟩ : ∃ i, j = i + 4 := ⟨j - 4, by omega⟩
  have : 2 ^ 32 * (i + 4) + 2 * L ≤ L * (i + 4) := by nlinarith
  omega
theorem pow_mul_rt_le_δ₁ {T : ParameterAssignment} (hT : T.Admissible) : 2 ^ 20 * T.rt ≤ T.δ₁ := by
  have a := hT.rt_le
  have b := hT.δc_le
  linarith
theorem N_zero_pos {T : ParameterAssignment} (hT : T.Admissible) : 0 < T.N 0 := hT.chain.2.2.2.2.2.2.2.1 0
theorem blockCost_locallyClose (hc2 : BlockCostsAgree) {T : ParameterAssignment} (hT : T.Admissible) {y : ℝ}
    (hy : T.floorMin ≤ y)
    (hR : R.params = T.stepParameters y) (hn : T.n₀ ≤ n) (hn' : T.n₀ ≤ n') {s : ChartSetting R n}
    {s' : ChartSetting R n'}
    (hs : s.IsAdmissible) (hs' : s'.IsAdmissible) {J : ℕ} (hJ : 4 ≤ J) :
    LocallyClosePair s s' s.blockCostAt s'.blockCostAt J fun j =>
      ((T.side : ℝ) ^ 4 * T.threshold ^ 2 * T.N 0) * Real.exp (-((2 ^ 20 * T.rt) * j)) := by
  intro Z Z' m' j ζ ζ' hag hjm hJj near hζ hζ'
  have h := (hc2 T hT y R hy hR n n' hn hn' s s' Z Z' m' j ζ ζ' hs hs' hag (by omega) hjm near hζ hζ').1
  refine h.trans ?_
  have hN := N_zero_pos hT
  have hc : 0 ≤ (T.side : ℝ) ^ 4 * T.threshold ^ 2 * T.N 0 := by positivity
  refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hc
  have h1 : (j : ℝ) ≤ ((T.side * j - T.side - 2 ^ 16 : ℕ) : ℝ) :=
    Nat.cast_le.mpr (le_mul_sub_sub_of_large hT.L_ge (by omega))
  have h2 := pow_mul_rt_le_δ₁ hT
  have h3 : 0 ≤ 2 ^ 20 * T.rt := mul_nonneg (by norm_num) hT.rt_pos.le
  have h4 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  have h5 : 2 ^ 20 * T.rt * (j : ℝ) ≤ T.δ₁ * ((T.side * j - T.side - 2 ^ 16 : ℕ) : ℝ) :=
    mul_le_mul h2 h1 h4 (h3.trans h2)
  linarith
theorem potentialPart_locallyClose (hc2 : BlockCostsAgree) (hphi : BlockDensitiesClose)
    {T : ParameterAssignment} (hT : T.Admissible) {y : ℝ} (hy : T.floorMin ≤ y) (hR : R.params = T.stepParameters y)
    (hrow : R.HasExpansions) (hx : 0 ≤ R.coupling)
    (hn : T.n₀ ≤ n) (hn' : T.n₀ ≤ n') {s : ChartSetting R n} {s' : ChartSetting R n'} (hs : s.IsAdmissible)
    (hs' : s'.IsAdmissible)
    {J : ℕ} (hJ : 4 ≤ J) (hr : (R.range : ℝ) / 64 ≤ ((T.side * J - 2 * T.side : ℕ) : ℝ)) {ν : ℝ} (h0 : 0 ≤ ν)
    (h1 : ν ≤ 1) :
    LocallyClosePair s s' (fun Z ζ => R.coupling * s.blockCostAt Z ζ - ν * s.blockDensityAt Z ζ - s.logJacobianAt Z ζ)
      (fun Z ζ => R.coupling * s'.blockCostAt Z ζ - ν * s'.blockDensityAt Z ζ - s'.logJacobianAt Z ζ) J fun j =>
      (R.coupling * ((T.side : ℝ) ^ 4 * T.threshold ^ 2 * T.N 0) + (T.side : ℝ) ^ 4) *
        Real.exp (-((2 ^ 20 * T.rt) * j)) := by
  intro Z Z' m' j ζ ζ' hag hjm hJj near hζ hζ'
  have hL : R.params.side = T.side := by rw [hR]; rfl
  have hrt : R.params.rt = T.rt := by rw [hR]; rfl
  have hn0 : R.params.n₀ = T.n₀ := by rw [hR]; rfl
  have hfit : R.params.Admissible := by rw [hR]; exact hT.fits y hy
  have hc := blockCost_locallyClose hc2 hT hy hR hn hn' hs hs' hJ Z Z' m' j ζ ζ' hag hjm hJj near hζ hζ'
  obtain ⟨-, hj, -⟩ := hc2 T hT y R hy hR n n' hn hn' s s' Z Z' m' j ζ ζ' hs hs' hag (by omega) hjm near hζ hζ'
  have hmono : ((T.side * J - 2 * T.side : ℕ) : ℝ) ≤ ((T.side * j - 2 * T.side : ℕ) : ℝ) := by
    have : T.side * J ≤ T.side * j := Nat.mul_le_mul_left _ hJj
    exact_mod_cast Nat.sub_le_sub_right this _
  have hp := hphi R n n' s s' Z Z' m' j ζ ζ' hfit hrow (by rw [hn0]; exact hn) (by rw [hn0]; exact hn') hs hs' hag
    (by omega) hjm (by rw [hL]; exact hr.trans hmono) near hζ hζ'
  rw [hL] at hp
  have hp2 : |s.blockDensityAt Z ζ - s'.blockDensityAt Z' ζ'| ≤
      (T.side : ℝ) ^ 4 * Real.exp (-((2 ^ 20 * T.rt) * j)) := by
    refine hp.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by positivity))
    have h2 : (2 : ℝ) ^ 32 * j ≤ ((T.side * j - 2 * T.side : ℕ) : ℝ) := by
      have := Nat.cast_le (α := ℝ).mpr (pow_mul_le_mul_sub_of_large hT.L_ge (show 4 ≤ j by omega))
      rw [Nat.cast_mul, show ((2 ^ 32 : ℕ) : ℝ) = (2 : ℝ) ^ 32 by norm_num] at this
      exact this
    have h3 := hT.rt_pos
    simp only [StepParameters.decayRate, hrt]
    have h4 : (T.rt / 2 ^ 12) * (2 ^ 32 * j) ≤ (T.rt / 2 ^ 12) * ((T.side * j - 2 * T.side : ℕ) : ℝ) := by
      gcongr
    have h5 : (T.rt / 2 ^ 12) * (2 ^ 32 * j) = 2 ^ 20 * T.rt * j := by ring
    linarith
  have e : (R.coupling * s.blockCostAt Z ζ - ν * s.blockDensityAt Z ζ - s.logJacobianAt Z ζ) -
      (R.coupling * s'.blockCostAt Z' ζ' - ν * s'.blockDensityAt Z' ζ' - s'.logJacobianAt Z' ζ') =
      R.coupling * (s.blockCostAt Z ζ - s'.blockCostAt Z' ζ') - ν * (s.blockDensityAt Z ζ - s'.blockDensityAt Z' ζ') := by
    rw [hj]
    ring
  simp only []
  rw [e]
  refine (abs_sub _ _).trans ?_
  rw [abs_mul, abs_mul, abs_of_nonneg hx, abs_of_nonneg h0, add_mul, mul_assoc]
  have h6 : ν * |s.blockDensityAt Z ζ - s'.blockDensityAt Z' ζ'| ≤ 1 * |s.blockDensityAt Z ζ - s'.blockDensityAt Z' ζ'| := by
    gcongr
  have h7 : R.coupling * |s.blockCostAt Z ζ - s'.blockCostAt Z' ζ'| ≤
      R.coupling * (((T.side : ℝ) ^ 4 * T.threshold ^ 2 * T.N 0) * Real.exp (-((2 ^ 20 * T.rt) * j))) := by gcongr
  linarith
theorem sum_error_le {k : ℕ} {E₀ c A₀ : ℝ} (hE : 0 ≤ E₀) (hc : 0 < c) (hA : 0 ≤ A₀) :
    ((2 * (k / 4 : ℕ) + 1 : ℕ) : ℝ) ^ 4 * (2 * (E₀ * Real.exp (-(c * (k / 4 : ℕ))))) +
        2 * (E₀ * Real.exp (2 * c) * (A₀ * Real.exp (-(c * (k / 4 + 1 : ℕ) / 2)))) ≤
      E₀ * (2 * Real.exp c + 2 * Real.exp (2 * c) * A₀) * ((k : ℝ) + 1) ^ 4 * Real.exp (-(c * k / 8)) := by
  set k₁ := k / 4 with hk₁
  have hlo : 4 * k₁ ≤ k := Nat.mul_div_le k 4
  have hhi : k < 4 * k₁ + 4 := by omega
  have hloR : 4 * (k₁ : ℝ) ≤ k := by exact_mod_cast hlo
  have hhiR : (k : ℝ) ≤ 4 * k₁ + 4 := by exact_mod_cast hhi.le
  have p1 : (((2 * k₁ + 1 : ℕ) : ℝ)) ^ 4 ≤ ((k : ℝ) + 1) ^ 4 := by
    push_cast
    gcongr
    have : (0 : ℝ) ≤ k₁ := by positivity
    linarith
  have p2 : (1 : ℝ) ≤ ((k : ℝ) + 1) ^ 4 := by
    have : (1 : ℝ) ≤ (k : ℝ) + 1 := by
      have : (0 : ℝ) ≤ k := by positivity
      linarith
    exact one_le_pow₀ this
  have e1 : Real.exp (-(c * k₁)) ≤ Real.exp c * Real.exp (-(c * k / 8)) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    nlinarith
  have e2 : Real.exp (-(c * (k₁ + 1 : ℕ) / 2)) ≤ Real.exp (-(c * k / 8)) := by
    apply Real.exp_le_exp.mpr
    push_cast
    nlinarith
  set Ex := Real.exp (-(c * k / 8)) with hEx
  have a1 : ((2 * k₁ + 1 : ℕ) : ℝ) ^ 4 * (2 * (E₀ * Real.exp (-(c * k₁)))) ≤
      ((k : ℝ) + 1) ^ 4 * (2 * (E₀ * (Real.exp c * Ex))) := by gcongr
  have a2 : 2 * (E₀ * Real.exp (2 * c) * (A₀ * Real.exp (-(c * (k₁ + 1 : ℕ) / 2)))) ≤
      ((k : ℝ) + 1) ^ 4 * (2 * (E₀ * Real.exp (2 * c) * (A₀ * Ex))) := by
    have h3 : 2 * (E₀ * Real.exp (2 * c) * (A₀ * Real.exp (-(c * (k₁ + 1 : ℕ) / 2)))) ≤
        2 * (E₀ * Real.exp (2 * c) * (A₀ * Ex)) := by gcongr
    have h4 : 0 ≤ 2 * (E₀ * Real.exp (2 * c) * (A₀ * Ex)) := by positivity
    nlinarith
  calc _ ≤ ((k : ℝ) + 1) ^ 4 * (2 * (E₀ * (Real.exp c * Ex))) +
        ((k : ℝ) + 1) ^ 4 * (2 * (E₀ * Real.exp (2 * c) * (A₀ * Ex))) := add_le_add a1 a2
    _ = _ := by ring
theorem directionalDeriv_close_of_locallyClose (hodd : Odd R.params.side) {s : ChartSetting R n}
    {s' : ChartSetting R n'} (hs : s.IsAdmissible) (hs' : s'.IsAdmissible)
    {A : TorusSite n → FreeCoords s.free → ℝ} {A' : TorusSite n' → FreeCoords s'.free → ℝ} {J : ℕ}
    {E₀ c A₀ M Q : ℝ}
    (hE : 0 ≤ E₀) (hc : 0 < c) (hA : 0 ≤ A₀)
    (hA₀ : ∀ (n : ℕ) [NeZero n] (y : TorusSite n) (D : ℕ),
      ∑ Y ∈ Finset.univ.filter (fun Y : TorusSite n => D ≤ _root_.YangMills.Construction.TorusFields.supDist Y y), Real.exp (-(c * _root_.YangMills.Construction.TorusFields.supDist Y y)) ≤
        A₀ * Real.exp (-(c * D / 2)))
    (h12 : LocallyClosePair s s' A A' J fun j => E₀ * Real.exp (-(c * j)))
    (h11 : LocallyClosePair s s A A J fun j => E₀ * Real.exp (-(c * j)))
    (h22 : LocallyClosePair s' s' A' A' J fun j => E₀ * Real.exp (-(c * j)))
    {Y : TorusSite n} {Y' : TorusSite n'} {m k : ℕ} (hag : SettingsAgreeNear s s' Y Y' m) (hkm : k ≤ m)
    {η : FreeCoords s.free} {η' : FreeCoords s'.free} (hη : s.InBalls η) (hη' : s'.InBalls η')
    (hn : CoordsAgreeNear s s' Y Y' k η η') {q₀ : NearBondIndex} (hb : nearBond R.params.side Y q₀ ∈ s.free)
    (hb' : nearBond R.params.side Y' q₀ ∈ s'.free) (hq₀ : IsNearIndex R.params.side (k / 2) q₀)
    (hk : J + 1 ≤ k / 4)
    (hρ : 0 < R.ballRadius) (hM : 0 < M) (hQ : 0 < Q)
    (hQ₁ : E₀ * (2 * Real.exp c + 2 * Real.exp (2 * c) * A₀) * ((k : ℝ) + 1) ^ 4 * Real.exp (-(c * k / 8)) ≤ Q)
    (hQ₂ : Q ≤ 2 * M * R.ballRadius ^ 2)
    (hU : ∃ U : Set (FreeCoords s.free), IsOpen U ∧ (∀ ζ, s.InBalls ζ → ζ ∈ U) ∧
      ContDiffOn ℝ 3 (fun ζ => ∑ Z, A Z ζ) U)
    (hU' : ∃ U : Set (FreeCoords s'.free), IsOpen U ∧ (∀ ζ, s'.InBalls ζ → ζ ∈ U) ∧
      ContDiffOn ℝ 3 (fun ζ => ∑ Z, A' Z ζ) U)
    (he : ∀ ζ, s.InBalls ζ → ∀ b X, ‖X‖ = 1 → |mixedSecondDeriv (fun ζ => ∑ Z, A Z ζ) ζ b b X X| ≤ M)
    (he' : ∀ ζ, s'.InBalls ζ → ∀ b X, ‖X‖ = 1 → |mixedSecondDeriv (fun ζ => ∑ Z, A' Z ζ) ζ b b X X| ≤ M)
    {X : EuclideanSpace ℝ (Fin 3)} (hX : ‖X‖ = 1) :
    |directionalDeriv (fun ζ => ∑ Z, A Z ζ) η ⟨_, hb⟩ X - directionalDeriv (fun ζ => ∑ Z, A' Z ζ) η' ⟨_, hb'⟩ X| ≤
      5 * Real.sqrt (Q * (2 * M)) := by
  obtain ⟨U, oU, sU, cU⟩ := hU
  obtain ⟨U', oU', sU', cU'⟩ := hU'
  have ball : ∀ v : EuclideanSpace ℝ (Fin 3), ‖v‖ ≤ R.ballRadius → coordNorm v ≤ R.ballRadius := fun v hv => by
    rwa [coordNorm_eq_norm]
  have hq₀k : IsNearIndex R.params.side k q₀ := ⟨fun l => by
    have := hq₀.1 l
    omega, hq₀.2⟩
  have hval : η ⟨_, hb⟩ = η' ⟨_, hb'⟩ := by
    have := hn q₀ hq₀k
    simpa only [ChartSetting.coordsByIndex, dif_pos hb, dif_pos hb'] using this
  have hnorm : ‖η ⟨_, hb⟩‖ ≤ R.ballRadius := by
    have := hη ⟨_, hb⟩
    rwa [coordNorm_eq_norm] at this
  refine abs_directionalDeriv_sub_le hρ hM hQ hQ₂ oU oU' cU cU'
    (fun v hv => sU _ (inBalls_update s hη _ (ball v hv))) (fun v hv => sU' _ (inBalls_update s' hη' _ (ball v hv)))
    (fun v hv X hX => he _ (inBalls_update s hη _ (ball v hv)) _ X hX)
    (fun v hv X hX => he' _ (inBalls_update s' hη' _ (ball v hv)) _ X hX)
    (fun v v₂ hv hv₂ => ?_) hval hnorm hX
  have hsum := abs_sum_update_sub_le hodd hs hs' hE hc hA₀ h12 h11 h22 hag hkm hη hη' hn hb hb' hq₀
    (ball v hv) (ball v₂ hv₂) hk
  exact hsum.trans ((sum_error_le hE hc hA).trans hQ₁)
end Main
section Numbers
theorem le_clusterRange_of_pow_le {B x : ℝ} (hB : 0 ≤ B) (hx : B ^ 100 ≤ x) : B ≤ clusterRange x := by
  have h1 := Real.rpow_le_rpow (by positivity) hx (show (0 : ℝ) ≤ 1 / 100 by norm_num)
  rw [← Real.rpow_natCast, ← Real.rpow_mul hB] at h1
  norm_num at h1
  exact h1.trans (Nat.le_ceil _)
theorem constants_fit {x E C₃ M₀ ρ W Wq e₃ : ℝ} (hx : 1 ≤ x) (hE : 0 < E) (hC : 0 < C₃) (hM : 0 < M₀) (hρ : 0 < ρ)
    (hW : 0 ≤ W) (he₃ : 0 < e₃) (he₁ : e₃ ≤ 1) (hWq0 : 0 ≤ Wq) (hWq : Wq ≤ W * e₃ ^ 2)
    (hN : (50 * E * C₃ * M₀ + E * C₃ / (2 * M₀ * ρ ^ 2)) * x ^ 4 * W ≤ 1) :
    x * E * C₃ * Wq ≤ 2 * (M₀ * x) * ρ ^ 2 ∧
      x * (5 * Real.sqrt (x * E * C₃ * Wq * (2 * (M₀ * x)))) ≤ e₃ := by
  have hx4 : 1 ≤ x ^ 4 := one_le_pow₀ hx
  have hP : 0 ≤ x ^ 4 * W := by positivity
  set b := E * C₃ / (2 * M₀ * ρ ^ 2) with hb
  have hb0 : 0 < b := by positivity
  have ha : 0 < 50 * E * C₃ * M₀ := by positivity
  have h1 : 50 * E * C₃ * M₀ * (x ^ 4 * W) ≤ 1 := by nlinarith [mul_nonneg hb0.le hP]
  have h2 : b * (x ^ 4 * W) ≤ 1 := by nlinarith [mul_nonneg ha.le hP]
  have h3 : b * W ≤ 1 := by nlinarith [mul_nonneg hb0.le hW, mul_nonneg (mul_nonneg hb0.le hW) (sub_nonneg.mpr hx4)]
  have h4 : E * C₃ * W ≤ 2 * M₀ * ρ ^ 2 := by
    have hd : 0 < 2 * M₀ * ρ ^ 2 := by positivity
    have e : b * W = E * C₃ * W / (2 * M₀ * ρ ^ 2) := by rw [hb]; ring
    rw [e, div_le_one hd] at h3
    exact h3
  have he2 : e₃ ^ 2 ≤ 1 := by nlinarith
  have hWq1 : Wq ≤ W := hWq.trans (by nlinarith)
  constructor
  · have : x * E * C₃ * Wq ≤ x * (E * C₃ * W) := by
      have : E * C₃ * Wq ≤ E * C₃ * W := by gcongr
      nlinarith
    nlinarith
  · have hy : 0 ≤ e₃ / (5 * x) := by positivity
    have hs : Real.sqrt (x * E * C₃ * Wq * (2 * (M₀ * x))) ≤ e₃ / (5 * x) := by
      refine Real.sqrt_le_iff.mpr ⟨hy, ?_⟩
      have e : (e₃ / (5 * x)) ^ 2 = e₃ ^ 2 / (25 * x ^ 2) := by
        field_simp
        ring
      rw [e, le_div_iff₀ (by positivity)]
      have h5 : 50 * E * C₃ * M₀ * x ^ 4 * Wq ≤ 50 * E * C₃ * M₀ * x ^ 4 * (W * e₃ ^ 2) := by gcongr
      have h7 : (50 * E * C₃ * M₀ * (x ^ 4 * W)) * e₃ ^ 2 ≤ 1 * e₃ ^ 2 := by gcongr
      nlinarith
    calc x * (5 * Real.sqrt (x * E * C₃ * Wq * (2 * (M₀ * x)))) ≤ x * (5 * (e₃ / (5 * x))) := by gcongr
      _ = e₃ := by field_simp
end Numbers
theorem range_div_le {r L : ℝ} {J : ℕ} {k : ℕ} (hL : 0 < L) (hr : 2 ^ 14 * L ≤ r) (h1 : r ≤ k * (4 * L))
    (h2 : (k : ℝ) ≤ 4 * ((J : ℝ) + 1) + 4) : r / 64 ≤ L * J - 2 * L := by
  have h4 : r ≤ (4 * (J : ℝ) + 8) * (4 * L) := h1.trans (by gcongr; linarith)
  linarith
theorem settingGradientsClose_of (hconv : SettingsUniformlyConvex) (hcost : CostHessianFloor)
    (hc2 : BlockCostsAgree) (hphi : BlockDensitiesClose)
    (hnum : PolynomialBelowExponential) : SettingGradientsClose := by
  obtain ⟨r₁, p₁, H1⟩ := hconv
  obtain ⟨r₂, p₂, H2⟩ := hcost
  refine ⟨fun c => min (r₁ c) (r₂ c), fun c => lt_min (p₁ c) (p₂ c), fun T hT hrt => ?_⟩
  obtain ⟨C₁, y₁, hC₁, H1⟩ := H1 T hT (hrt.trans (min_le_left _ _))
  obtain ⟨C₂, y₂, hC₂, H2⟩ := H2 T hT (hrt.trans (min_le_right _ _))
  have hrt0 := hT.rt_pos
  have hσ := hT.σ_pos
  have hL40 : (2 : ℝ) ^ 40 ≤ T.side := by
    have := Nat.cast_le (α := ℝ).mpr hT.L_ge
    rwa [show ((2 ^ 40 : ℕ) : ℝ) = (2 : ℝ) ^ 40 by norm_num] at this
  have hLpos : (0 : ℝ) < T.side := by linarith [show (0 : ℝ) < 2 ^ 40 by norm_num]
  set c : ℝ := 2 ^ 20 * T.rt with hc
  have hc0 : 0 < c := by positivity
  obtain ⟨A₀, hA, hA₀⟩ := exists_sum_exp_supDist_le c hc0
  set Ec : ℝ := (T.side : ℝ) ^ 4 * T.threshold ^ 2 * T.N 0 with hEc
  have hN0 := N_zero_pos hT
  have hEc0 : 0 ≤ Ec := by positivity
  set E : ℝ := Ec + (T.side : ℝ) ^ 4 with hE
  have hE0 : 0 < E := by positivity
  set C₃ : ℝ := 2 * Real.exp c + 2 * Real.exp (2 * c) * A₀ with hC₃
  have hC₃0 : 0 < C₃ := by positivity
  set M₀ : ℝ := C₁ + C₂ + 1 with hM₀
  have hM₀0 : 0 < M₀ := by positivity
  set ρ : ℝ := T.threshold / 64 with hρ
  have hρ0 : 0 < ρ := by positivity
  obtain ⟨y₃, hy₃, N⟩ :=
    hnum (50 * E * C₃ * M₀ + E * C₃ / (2 * M₀ * ρ ^ 2)) T.rt (2 ^ 8 * T.side) 4 4 hrt0 (by positivity)
  refine ⟨max T.floorMin (max y₁ (max y₂ (max y₃ ((2 ^ 14 * (T.side : ℝ)) ^ 100)))), fun y hy R hOT n n' _ _ hn hn'
    s s' Y Y' m k η η' hs hs' hag hkm hkr near hη hη' q h h' X hq hX => ?_⟩
  obtain ⟨hR, hρA, hp, hyx, hstep⟩ := id hOT
  have hyT : T.floorMin ≤ y := (le_max_left _ _).trans hy
  have hy1 : y₁ ≤ y := (le_max_left _ _).trans ((le_max_right _ _).trans hy)
  have hy2 : y₂ ≤ y :=
    (le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hy))
  have hy3 : y₃ ≤ R.coupling := ((le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans
    ((le_max_right _ _).trans hy)))).trans hyx
  have hy4 : (2 ^ 14 * (T.side : ℝ)) ^ 100 ≤ R.coupling := ((le_max_right _ _).trans ((le_max_right _ _).trans
    ((le_max_right _ _).trans ((le_max_right _ _).trans hy)))).trans hyx
  have hx1 : 1 ≤ R.coupling := hy₃.trans hy3
  have hL : R.params.side = T.side := by rw [hR]; rfl
  have hodd : Odd R.params.side := by rw [hL]; exact hT.L_odd
  have hRρ : R.ballRadius = ρ := by
    show R.params.threshold / 64 = _
    rw [hR]
    rfl
  have hrfloor : 2 ^ 14 * (T.side : ℝ) ≤ R.range := le_clusterRange_of_pow_le (by positivity) hy4
  have hk32 : (2 : ℝ) ^ 6 ≤ k := by
    have h1 : (R.range : ℝ) / (2 ^ 8 * T.side) ≤ k := hkr
    have h2 : (2 : ℝ) ^ 6 ≤ (R.range : ℝ) / (2 ^ 8 * T.side) := by
      rw [le_div_iff₀ (by positivity)]
      have : (2 : ℝ) ^ 6 * (2 ^ 8 * T.side) = 2 ^ 14 * T.side := by ring
      linarith
    linarith
  have hk64 : 64 ≤ k := by
    have : ((64 : ℕ) : ℝ) ≤ k := by
      norm_num
      norm_num at hk32
      exact hk32
    exact_mod_cast this
  set J : ℕ := k / 4 - 1 with hJ
  have hJ4 : 4 ≤ J := by omega
  have hJk : J + 1 ≤ k / 4 := by omega
  have hnum' := N R.coupling hy3 k hkr
  set W : ℝ := ((k : ℝ) + 1) ^ 4 * Real.exp (-(T.rt * k)) with hW
  have hW0 : 0 ≤ W := by positivity
  set e₃ : ℝ := Real.exp (-(4 * T.rt * k)) with he₃
  have he₃0 : 0 < e₃ := Real.exp_pos _
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hrk : 0 ≤ T.rt * k := mul_nonneg hrt0.le hk0
  have he₃1 : e₃ ≤ 1 := Real.exp_le_one_iff.mpr (by
    have : 4 * T.rt * k = 4 * (T.rt * k) := by ring
    linarith)
  set Wq : ℝ := ((k : ℝ) + 1) ^ 4 * Real.exp (-(c * k / 8)) with hWq
  have hWq0 : 0 ≤ Wq := by positivity
  have hWqle : Wq ≤ W * e₃ ^ 2 := by
    have hpk : (0 : ℝ) ≤ ((k : ℝ) + 1) ^ 4 := by positivity
    have e0 : W * e₃ ^ 2 = ((k : ℝ) + 1) ^ 4 * (Real.exp (-(T.rt * k)) * e₃ ^ 2) := by rw [hW]; ring
    rw [e0, hWq]
    refine mul_le_mul_of_nonneg_left ?_ hpk
    rw [he₃, ← Real.exp_nat_mul, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have e1 : c * k / 8 = 2 ^ 17 * (T.rt * k) := by simp only [hc]; ring
    have e2 : (((2 : ℕ) : ℝ)) * -(4 * T.rt * k) = -(8 * (T.rt * k)) := by push_cast; ring
    rw [e1, e2]
    linarith
  obtain ⟨hQ₂, hF⟩ := constants_fit hx1 hE0 hC₃0 hM₀0 hρ0 hW0 he₃0 he₃1 hWq0 hWqle
    (by
      have e : (50 * E * C₃ * M₀ + E * C₃ / (2 * M₀ * ρ ^ 2)) * R.coupling ^ 4 * W =
          (50 * E * C₃ * M₀ + E * C₃ / (2 * M₀ * ρ ^ 2)) * R.coupling ^ 4 * ((k : ℝ) + 1) ^ 4 *
            Real.exp (-(T.rt * k)) := by
        rw [hW]
        ring
      rw [e]
      exact hnum')
  have hQ0 : 0 < R.coupling * E * C₃ * Wq := by
    have : 0 < Wq := by positivity
    positivity
  have hM0 : 0 < M₀ * R.coupling := by positivity
  have hρR : 0 < R.ballRadius := by rw [hRρ]; exact hρ0
  have hQ₂' : R.coupling * E * C₃ * Wq ≤ 2 * (M₀ * R.coupling) * R.ballRadius ^ 2 := by rw [hRρ]; exact hQ₂
  have hC₁x : C₁ * R.coupling ≤ M₀ * R.coupling := by
    have : C₁ ≤ M₀ := by simp only [hM₀]; linarith
    gcongr
  have hC₂x : C₂ ≤ M₀ * R.coupling := by
    have h3 : C₂ ≤ M₀ := by simp only [hM₀]; linarith
    exact h3.trans (le_mul_of_one_le_right hM₀0.le hx1)
  refine ⟨?_, fun hkr4 ν h0 h1 => ?_⟩
  · have standingConstraints := H2 y hy2 R hOT
    have cs := standingConstraints n hn s hs
    have cs' := standingConstraints n' hn' s' hs'
    have entry : ∀ {N : ℕ} [NeZero N] (u : ChartSetting R N), u.HasCostDecay T.lam C₂ → ∀ ζ, u.InBalls ζ →
        ∀ b X, ‖X‖ = 1 → |mixedSecondDeriv (fun ζ => ∑ Z, u.blockCostAt Z ζ) ζ b b X X| ≤ M₀ * R.coupling := by
      intro N _ u hu ζ hζ b X hX
      obtain ⟨Mb, h1, h2, -⟩ := hu.decay
      exact (h1 ζ hζ b b X X hX hX).trans ((h2 b b).trans hC₂x)
    have key := directionalDeriv_close_of_locallyClose (A := s.blockCostAt) (A' := s'.blockCostAt) (J := J)
      (E₀ := Ec) (c := c) (A₀ := A₀)
      (M := M₀ * R.coupling) (Q := R.coupling * E * C₃ * Wq) hodd hs hs' hEc0 hc0 hA hA₀
      (blockCost_locallyClose hc2 hT hyT hR hn hn' hs hs' hJ4) (blockCost_locallyClose hc2 hT hyT hR hn hn hs hs hJ4)
      (blockCost_locallyClose hc2 hT hyT hR hn' hn' hs' hs' hJ4) hag hkm hη hη' near h h' hq hJk hρR hM0 hQ0
      (by
        have h3 : Ec ≤ R.coupling * E := by
          have h4 : Ec ≤ E := by
            simp only [hE]
            have : (0 : ℝ) ≤ (T.side : ℝ) ^ 4 := by positivity
            linarith
          exact h4.trans (le_mul_of_one_le_left hE0.le hx1)
        calc Ec * C₃ * ((k : ℝ) + 1) ^ 4 * Real.exp (-(c * k / 8)) = Ec * C₃ * Wq := by rw [hWq]; ring
          _ ≤ R.coupling * E * C₃ * Wq := by gcongr)
      hQ₂' cs.contDiffOn cs'.contDiffOn (entry s cs) (entry s' cs') hX
    have hxnn : 0 ≤ R.coupling := by linarith
    calc R.coupling * |directionalDeriv s.costSum η ⟨_, h⟩ X - directionalDeriv s'.costSum η' ⟨_, h'⟩ X|
        ≤ R.coupling * (5 * Real.sqrt (R.coupling * E * C₃ * Wq * (2 * (M₀ * R.coupling)))) := by
          gcongr
          exact key
      _ ≤ e₃ := hF
  · have standingConstraints := H1 y hy1 R hOT
    have cs := (standingConstraints n hn s hs).2.1 ν h0 h1
    have cs' := (standingConstraints n' hn' s' hs').2.1 ν h0 h1
    have hxnn : 0 ≤ R.coupling := by linarith
    have hr : (R.range : ℝ) / 64 ≤ ((T.side * J - 2 * T.side : ℕ) : ℝ) := by
      have hJ2 : 2 * T.side ≤ T.side * J := by
        rw [mul_comm 2]
        exact Nat.mul_le_mul_left _ (by omega)
      rw [Nat.cast_sub hJ2]
      push_cast
      have h1 : (R.range : ℝ) / (4 * T.side) ≤ k := hkr4
      rw [div_le_iff₀ (by positivity)] at h1
      have h2 : (k : ℝ) ≤ 4 * ((k / 4 : ℕ) : ℝ) + 4 := by
        have : k < 4 * (k / 4) + 4 := by omega
        exact_mod_cast this.le
      have h3 : ((k / 4 : ℕ) : ℝ) = (J : ℝ) + 1 := by
        have : k / 4 = J + 1 := by omega
        exact_mod_cast this
      rw [h3] at h2
      exact range_div_le hLpos hrfloor h1 h2
    have key := directionalDeriv_close_of_locallyClose
      (A := fun Z ζ => R.coupling * s.blockCostAt Z ζ - ν * s.blockDensityAt Z ζ - s.logJacobianAt Z ζ)
      (A' := fun Z ζ => R.coupling * s'.blockCostAt Z ζ - ν * s'.blockDensityAt Z ζ - s'.logJacobianAt Z ζ) (J := J)
      (E₀ := R.coupling * Ec + (T.side : ℝ) ^ 4) (c := c) (A₀ := A₀)
      (M := M₀ * R.coupling) (Q := R.coupling * E * C₃ * Wq) hodd hs hs' (by positivity) hc0 hA hA₀
      (potentialPart_locallyClose hc2 hphi hT hyT hR hstep.1 hxnn hn hn' hs hs' hJ4 hr h0 h1)
      (potentialPart_locallyClose hc2 hphi hT hyT hR hstep.1 hxnn hn hn hs hs hJ4 hr h0 h1)
      (potentialPart_locallyClose hc2 hphi hT hyT hR hstep.1 hxnn hn' hn' hs' hs' hJ4 hr h0 h1)
      hag hkm hη hη' near h h' hq hJk hρR hM0 hQ0
      (by
        have h3 : R.coupling * Ec + (T.side : ℝ) ^ 4 ≤ R.coupling * E := by
          simp only [hE]
          have h5 : (0 : ℝ) ≤ (T.side : ℝ) ^ 4 := by positivity
          have h6 := le_mul_of_one_le_left h5 hx1
          rw [mul_add]
          linarith
        calc (R.coupling * Ec + (T.side : ℝ) ^ 4) * C₃ * ((k : ℝ) + 1) ^ 4 * Real.exp (-(c * k / 8)) =
            (R.coupling * Ec + (T.side : ℝ) ^ 4) * C₃ * Wq := by rw [hWq]; ring
          _ ≤ R.coupling * E * C₃ * Wq := by gcongr)
      hQ₂' cs.contDiffOn_nhds cs'.contDiffOn_nhds
      (fun ζ hζ b X hX => (cs.mixedSecondDeriv_le ζ hζ b b X X hX hX).trans hC₁x)
      (fun ζ hζ b X hX => (cs'.mixedSecondDeriv_le ζ hζ b b X X hX hX).trans hC₁x) hX
    have hx5 : 5 * Real.sqrt (R.coupling * E * C₃ * Wq * (2 * (M₀ * R.coupling))) ≤
        R.coupling * (5 * Real.sqrt (R.coupling * E * C₃ * Wq * (2 * (M₀ * R.coupling)))) := by
      exact le_mul_of_one_le_left (by positivity) hx1
    exact key.trans (hx5.trans hF)
end SettingGradients
theorem settingGradientsClose_holds (hconv : SettingsUniformlyConvex) (hcost : CostHessianFloor)
    (hc2 : BlockCostsAgree) (hphi : BlockDensitiesClose)
    (hnum : PolynomialBelowExponential) : SettingGradientsClose := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.SettingGradients.settingGradientsClose_of <;> assumption
end ClusterExpansionOfAStep
end YangMills.Construction
end
