import YangMills.Construction.ClusterExpansionOfAStep.BondInCoordinates
import YangMills.Construction.ClusterExpansionOfAStep.MovesOfAField
import YangMills.Construction.ClusterExpansionOfAStep.PartsOfAPotential
import YangMills.Construction.ClusterExpansionOfAStep.PriceOfTheHotLumps
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction
namespace StepSettings
open BlockAverages LumpContours ColdStepAtMirrorFrames TorusFields TorusLumps FieldMoves
variable {R : StepSetup} {n : ℕ} [NeZero n]
def ChartSetting.densityAt (s : ChartSetting R n) (W : TorusField (n * R.params.side)) : ℝ :=
  ∑ y, R.siteDensity (n * R.params.side) y W s.support s.labelling
theorem ChartSetting.totalDensity_eq_densityAt (s : ChartSetting R n) (η : FreeCoords s.free) :
    s.totalDensity η = s.densityAt (s.field η) := by
  classical
  unfold ChartSetting.totalDensity ChartSetting.densityAt ChartSetting.blockDensity
  have e : ∀ Y : TorusSite n, sitesInBlocks R.params.side {Y} =
      (Finset.univ : Finset (TorusSite (n * R.params.side))).filter fun x => parentBlock R.params.side x = Y := by
    intro Y
    simp [sitesInBlocks]
  simp only [e]
  exact Finset.sum_fiberwise _ _ _
structure ChartSetting.IsNear (s : ChartSetting R n) (θ : ℝ) (W : TorusField (n * R.params.side)) : Prop where
  torusHotLumps_eq : torusHotLumps R.params W = torusHotLumps R.params s.fine
  eq_off_free : ∀ x i, (x, i) ∉ s.free → W x i = s.fine x i
  curvature_lt : ∀ b ∈ s.free, ∀ (x : TorusSite (n * R.params.side)) (μ ν : Fin 4), μ < ν →
    supDist x b.1 ≤ 3 * R.range → curvature W x μ ν < θ
structure ChartSetting.Hypotheses (s : ChartSetting R n) : Prop where
  admissible : R.params.Admissible
  coldExpansion : ColdExpansion R.params R.depth R.coupling R.functional R.density
  hullExpansion : HullExpansion R.params R.depth R.coupling R.functional R.density R.labels R.labelWeight
    R.clusterFactor R.siteDensity
  isAdmissible : s.IsAdmissible
  range_large : 2 ^ 20 * (R.params.side + R.params.n₀ + 1) ≤ R.range
  n₀_le : R.params.n₀ ≤ n
variable {s : ChartSetting R n}
theorem isHullState_of_torusHotLumps_eq {m : ℕ} {ℓ : StepParameters} {r : ℕ} {W W' : TorusField m}
    {Y : Finset (TorusSite m)} [NeZero m]
    (h : torusHotLumps ℓ W = torusHotLumps ℓ W') (hY : IsHullState ℓ r W Y) : IsHullState ℓ r W' Y := by
  unfold IsHullState torusHotSites at *
  rwa [← h]
theorem ChartSetting.Hypotheses.isBlockTorusSide (h : s.Hypotheses) :
    IsBlockTorusSide R.params (n * R.params.side) :=
  ⟨Dvd.intro_left n rfl, by rw [mul_comm]; exact Nat.mul_le_mul_right _ h.n₀_le⟩
theorem ChartSetting.Hypotheses.side_dvd (_h : s.Hypotheses) : R.params.side ∣ n * R.params.side :=
  Dvd.intro_left n rfl
theorem ChartSetting.Hypotheses.threshold_pos (h : s.Hypotheses) : 0 < R.params.threshold :=
  h.admissible.σ_pos
theorem ChartSetting.Hypotheses.side_pos (h : s.Hypotheses) : 0 < R.params.side := by
  have := h.admissible.L_ge
  omega
theorem toImaginary_zero : toImaginary 0 = 0 := by apply _root_.YangMills.Construction.BondCoordinates.toImaginary_zero <;> assumption
theorem ChartSetting.Hypotheses.inBalls_zero (h : s.Hypotheses) : s.InBalls (0 : FreeCoords s.free) := by
  intro b
  have e : coordNorm (0 : EuclideanSpace ℝ (Fin 3)) = 0 := by
    simp [coordNorm, toImaginary_zero]
  simp only [Pi.zero_apply, e, StepSetup.ballRadius]
  have := h.threshold_pos
  positivity
theorem ChartSetting.Hypotheses.isHullState_fine (h : s.Hypotheses) :
    IsHullState R.params R.range s.fine s.support :=
  isHullState_of_torusHotLumps_eq (h.isAdmissible.hotLumps_eq 0 h.inBalls_zero)
    (h.isAdmissible.isHull 0 h.inBalls_zero)
theorem ChartSetting.IsNear.isHullState {θ : ℝ} {W : TorusField (n * R.params.side)} (hg : s.IsNear θ W)
    (h : s.Hypotheses) : IsHullState R.params R.range W s.support :=
  isHullState_of_torusHotLumps_eq hg.torusHotLumps_eq.symm h.isHullState_fine
theorem ChartSetting.Hypotheses.not_mem_free_of_mem_support (h : s.Hypotheses)
    {x : TorusSite (n * R.params.side)} (hx : x ∈ s.support) (i : Fin 4) : (x, i) ∉ s.free := by
  intro hb
  have h1 := h.isAdmissible.far_from_support (x, i) hb x (Finset.mem_union_left _ hx)
  have h2 := h.range_large
  simp only [supDist_self] at h1
  omega
theorem ChartSetting.IsNear.clusterFactor_eq {θ : ℝ} {W : TorusField (n * R.params.side)} (hg : s.IsNear θ W)
    (h : s.Hypotheses) {X : Finset (TorusSite (n * R.params.side))} (hX : X ∈ chainComponents R.range s.support) :
    R.clusterFactor (n * R.params.side) W s.support s.labelling X =
      R.clusterFactor (n * R.params.side) s.fine s.support s.labelling X :=
  h.hullExpansion.reads_class (n * R.params.side) h.isBlockTorusSide W s.fine s.support s.support s.labelling
    s.labelling X (subset_of_mem_chainComponents hX) (subset_of_mem_chainComponents hX)
    (fun b hb _ => hg.eq_off_free b.1 b.2
      (h.not_mem_free_of_mem_support (subset_of_mem_chainComponents hX hb) b.2))
    (fun _ _ _ _ => rfl)
def ChartSetting.fineFactorProd (s : ChartSetting R n) : ℝ :=
  ∏ X ∈ chainComponents R.range s.support, R.clusterFactor (n * R.params.side) s.fine s.support s.labelling X
def ChartSetting.outsideHot (s : ChartSetting R n) : Finset (TorusSite (n * R.params.side)) :=
  Finset.univ \ thickening lumpRange (torusHotSites R.params s.fine)
omit [NeZero n] in
theorem ChartSetting.field_apply_of_not_mem (s : ChartSetting R n) (η : FreeCoords s.free)
    (x : TorusSite (n * R.params.side)) (i : Fin 4) (hx : (x, i) ∉ s.free) : s.field η x i = s.fine x i := by
  unfold ChartSetting.field
  rw [dif_neg hx]
theorem ChartSetting.Hypotheses.clusterFactor_fine_ne_zero (h : s.Hypotheses)
    {X : Finset (TorusSite (n * R.params.side))} (hX : X ∈ chainComponents R.range s.support) :
    R.clusterFactor (n * R.params.side) s.fine s.support s.labelling X ≠ 0 := by
  have e : R.clusterFactor (n * R.params.side) (s.field 0) s.support s.labelling X =
      R.clusterFactor (n * R.params.side) s.fine s.support s.labelling X :=
    h.hullExpansion.reads_class (n * R.params.side) h.isBlockTorusSide _ _ s.support s.support s.labelling
      s.labelling X (subset_of_mem_chainComponents hX) (subset_of_mem_chainComponents hX)
      (fun b hb _ => s.field_apply_of_not_mem 0 b.1 b.2
        (h.not_mem_free_of_mem_support (subset_of_mem_chainComponents hX hb) b.2))
      (fun _ _ _ _ => rfl)
  rw [← e]
  exact h.isAdmissible.factor_ne_zero 0 h.inBalls_zero X hX
theorem ChartSetting.Hypotheses.fineFactorProd_pos (h : s.Hypotheses) : 0 < s.fineFactorProd := by
  refine Finset.prod_pos fun X hX => ?_
  exact lt_of_le_of_ne
    (h.hullExpansion.factor_nonneg (n * R.params.side) h.isBlockTorusSide s.fine s.support s.labelling X)
    (h.clusterFactor_fine_ne_zero hX).symm
theorem ChartSetting.Hypotheses.functional_trivialField_pos (h : s.Hypotheses) :
    0 < R.functional (n * R.params.side) (trivialField (n * R.params.side)) := by
  refine h.coldExpansion.positive (n * R.params.side) ?_ _ ?_
  · exact h.n₀_le.trans (Nat.le_mul_of_pos_right _ h.side_pos)
  · intro x μ ν _
    simp [curvature, holonomy_trivialField, h.threshold_pos]
theorem ChartSetting.IsNear.labelWeight_pos_and_densityAt_eq {θ : ℝ} {W : TorusField (n * R.params.side)}
    (hg : s.IsNear θ W) (h : s.Hypotheses) :
    0 < R.labelWeight (n * R.params.side) W s.support s.labelling ∧
      s.densityAt W = Real.log (R.labelWeight (n * R.params.side) W s.support s.labelling) -
          (Real.log (R.functional (n * R.params.side) (trivialField (n * R.params.side))) +
            Real.log s.fineFactorProd) +
        R.coupling * actionAtLevel R.params.coupling R.params.side R.depth s.outsideHot W := by
  have hf := h.hullExpansion.form (n * R.params.side) h.isBlockTorusSide W s.support s.labelling (hg.isHullState h)
  have e1 : ∏ X ∈ chainComponents (clusterRange R.coupling) s.support,
      R.clusterFactor (n * R.params.side) W s.support s.labelling X = s.fineFactorProd :=
    Finset.prod_congr rfl fun X hX => hg.clusterFactor_eq h hX
  have e2 : torusHotSites R.params W = torusHotSites R.params s.fine := by
    unfold torusHotSites
    rw [hg.torusHotLumps_eq]
  rw [e1, e2] at hf
  have hD := h.functional_trivialField_pos
  have hP := h.fineFactorProd_pos
  have hpos : 0 < R.labelWeight (n * R.params.side) W s.support s.labelling := by
    rw [hf]
    positivity
  refine ⟨hpos, ?_⟩
  rw [hf, Real.log_mul (by positivity) hP.ne', Real.log_mul hD.ne' (Real.exp_pos _).ne', Real.log_exp]
  unfold ChartSetting.densityAt ChartSetting.outsideHot
  ring
theorem ChartSetting.IsNear.of_close (h : s.Hypotheses) {θ ε : ℝ} {W W' : TorusField (n * R.params.side)}
    (hg : s.IsNear θ W) (hoff : ∀ x i, (x, i) ∉ s.free → W' x i = W x i)
    (hc : ∀ x i, ‖((W' x i : UnitQuaternion) : ℍ[ℝ]) - W x i‖ ≤ ε) (hθ : θ + 4 * ε ≤ R.params.threshold) :
    s.IsNear (θ + 4 * ε) W' := by
  have hcurv := curvature_le_add_of_close hc
  have hε : 0 ≤ ε := (norm_nonneg _).trans (hc 0 0)
  refine ⟨?_, fun x i hx => (hoff x i hx).trans (hg.eq_off_free x i hx), ?_⟩
  · rw [← hg.torusHotLumps_eq]
    apply torusHotLumps_eq_of_hotPlaquettes_eq h.admissible h.side_dvd
    ext ⟨x, μ, ν⟩
    simp only [hotPlaquettes, Finset.mem_filter, Finset.mem_univ, true_and]
    refine and_congr_right fun hlt => ?_
    by_cases he : (x, μ) ∈ s.free ∨ (x + TorusFields.unitStep (n * R.params.side) μ, ν) ∈ s.free ∨
        (x + TorusFields.unitStep (n * R.params.side) ν, μ) ∈ s.free ∨ (x, ν) ∈ s.free
    · have hex : ∃ b ∈ s.free, supDist x b.1 ≤ 3 * R.range := by
        have hr : 1 ≤ 3 * R.range := by
          have := h.range_large
          omega
        rcases he with e | e | e | e
        · exact ⟨_, e, by simp [supDist_self]⟩
        · exact ⟨_, e, (supDist_add_unitStep_le x μ).trans hr⟩
        · exact ⟨_, e, (supDist_add_unitStep_le x ν).trans hr⟩
        · exact ⟨_, e, by simp [supDist_self]⟩
      obtain ⟨b, hb, hd⟩ := hex
      have c1 := hg.curvature_lt b hb x μ ν hlt hd
      have c2 := hcurv x μ ν
      constructor
      · intro h1
        linarith
      · intro h1
        linarith
    · push Not at he
      obtain ⟨e1, e2, e3, e4⟩ := he
      have : holonomy W' x μ ν = holonomy W x μ ν := by
        unfold holonomy
        rw [hoff _ _ e1, hoff _ _ e2, hoff _ _ e3, hoff _ _ e4]
      unfold curvature
      rw [this]
  · intro b hb x μ ν hlt hd
    have c1 := hg.curvature_lt b hb x μ ν hlt hd
    have c2 := hcurv x μ ν
    linarith
theorem eventually_norm_perturb_sub_le {m k : ℕ} [NeZero m] (c : Fin k → TorusBond m)
    (X : Fin k → imaginaryQuaternions) (W : TorusField m) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ σ in nhds (0 : Fin k → ℝ), ∀ x i, ‖((perturb c X σ W x i : UnitQuaternion) : ℍ[ℝ]) - W x i‖ ≤ ε := by
  refine Filter.eventually_all.mpr fun x => Filter.eventually_all.mpr fun i => ?_
  have hc : Continuous fun σ : Fin k → ℝ => ‖((perturb c X σ W x i : UnitQuaternion) : ℍ[ℝ]) - W x i‖ := by
    have h1 : Continuous fun σ : Fin k → ℝ => perturb c X σ W x i :=
      (continuous_apply i).comp ((continuous_apply x).comp (continuous_perturb c X W))
    exact ((continuous_subtype_val.comp h1).sub continuous_const).norm
  have h0 : ‖((perturb c X (0 : Fin k → ℝ) W x i : UnitQuaternion) : ℍ[ℝ]) - W x i‖ = 0 := by
    rw [perturb_zero]
    simp
  have := hc.tendsto (0 : Fin k → ℝ)
  rw [h0] at this
  exact (this.eventually (gt_mem_nhds hε)).mono fun σ hσ => le_of_lt hσ
omit [NeZero n] in
theorem perturb_apply_of_not_mem_free {k : ℕ} {c : Fin k → TorusBond (n * R.params.side)}
    (hc : ∀ l, c l ∈ s.free) (X : Fin k → imaginaryQuaternions) (σ : Fin k → ℝ)
    (W : TorusField (n * R.params.side)) (x : TorusSite (n * R.params.side)) (i : Fin 4)
    (hx : (x, i) ∉ s.free) : perturb c X σ W x i = W x i :=
  perturb_apply_of_ne c X σ W (x, i) fun l e => hx (e ▸ hc l)
theorem ChartSetting.IsNear.eventually_perturb (h : s.Hypotheses) {θ : ℝ} {W : TorusField (n * R.params.side)}
    (hg : s.IsNear θ W) (hθ : θ < R.params.threshold) {k : ℕ} {c : Fin k → TorusBond (n * R.params.side)}
    (hc : ∀ l, c l ∈ s.free) (X : Fin k → imaginaryQuaternions) :
    ∀ᶠ σ in nhds (0 : Fin k → ℝ), s.IsNear ((θ + R.params.threshold) / 2) (perturb c X σ W) := by
  have hε : 0 < (R.params.threshold - θ) / 8 := by linarith
  filter_upwards [eventually_norm_perturb_sub_le c X W hε] with σ hσ
  have := ChartSetting.IsNear.of_close h hg
    (fun x i hx => perturb_apply_of_not_mem_free hc X σ W x i hx) hσ (by linarith)
  have e : θ + 4 * ((R.params.threshold - θ) / 8) = (θ + R.params.threshold) / 2 := by ring
  rwa [e] at this
def ChartSetting.ActionSmooth (s : ChartSetting R n) (N₃ : ℝ) : Prop :=
  ∀ (θ : ℝ) (W : TorusField (n * R.params.side)), θ < R.params.threshold → s.IsNear θ W →
    ∀ (k : ℕ) (c : Fin k → TorusBond (n * R.params.side)) (X : Fin k → imaginaryQuaternions),
    (∀ l, c l ∈ s.free) →
    ContDiffAt ℝ 3 (fun σ : Fin k → ℝ =>
        actionAtLevel R.params.coupling R.params.side R.depth s.outsideHot (perturb c X σ W)) 0 ∧
      (2 ≤ k → k ≤ 3 → AreUnitVectors X →
        |mixedDeriv (actionAtLevel R.params.coupling R.params.side R.depth s.outsideHot) W c X| ≤ N₃)
theorem iteratedFDeriv_sub_const_add_mul {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {k : ℕ}
    (hk : k ≠ 0) {p : E} {G₁ G₂ : E → ℝ} (h₁ : ContDiffAt ℝ k G₁ p) (h₂ : ContDiffAt ℝ k G₂ p) (a c : ℝ) :
    iteratedFDeriv ℝ k (fun σ => G₁ σ - c + a * G₂ σ) p =
      iteratedFDeriv ℝ k G₁ p + a • iteratedFDeriv ℝ k G₂ p := by
  have e : (fun σ => G₁ σ - c + a * G₂ σ) = G₁ + ((fun _ => -c) + a • G₂) := by
    funext σ
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have hc : ContDiffAt ℝ k (fun _ : E => -c) p := contDiffAt_const
  have hs : ContDiffAt ℝ k (a • G₂) p := h₂.const_smul a
  have hcs : ContDiffAt ℝ k ((fun _ : E => -c) + a • G₂) p := hc.add hs
  ext m
  rw [e, iteratedFDeriv_add_apply h₁ hcs, iteratedFDeriv_add_apply hc hs,
    iteratedFDeriv_const_smul_apply h₂, iteratedFDeriv_const_of_ne hk]
  simp
theorem ChartSetting.IsNear.densityAt_smooth (h : s.Hypotheses) {N₃ : ℝ} (hA : s.ActionSmooth N₃) {θ : ℝ}
    {W : TorusField (n * R.params.side)} (hg : s.IsNear θ W) (hθ : θ < R.params.threshold) {k : ℕ}
    {c : Fin k → TorusBond (n * R.params.side)} (hc : ∀ l, c l ∈ s.free) (X : Fin k → imaginaryQuaternions) :
    ContDiffAt ℝ 3 (fun σ : Fin k → ℝ => s.densityAt (perturb c X σ W)) 0 ∧
      (2 ≤ k → k ≤ 3 → AreUnitVectors X → 0 ≤ R.coupling →
        |mixedDeriv s.densityAt W c X| ≤ (R.params.derivBound * R.coupling) ^ k + R.coupling * N₃) := by
  obtain ⟨hpos, -⟩ := hg.labelWeight_pos_and_densityAt_eq h
  have haway : ∀ l, ∀ z ∈ s.support, clusterRange R.coupling ≤ supDist (c l).1 z := by
    intro l z hz
    have h1 := h.isAdmissible.far_from_support (c l) (hc l) z (Finset.mem_union_left _ hz)
    have h2 := h.range_large
    have h3 : R.range = clusterRange R.coupling := rfl
    omega
  obtain ⟨hD, hb⟩ := h.hullExpansion.smooth (n * R.params.side) h.isBlockTorusSide W s.support s.labelling
    (hg.isHullState h) hpos k c X haway
  obtain ⟨hAC, hAb⟩ := hA θ W hθ hg k c X hc
  have hne : R.labelWeight (n * R.params.side) (perturb c X (0 : Fin k → ℝ) W) s.support s.labelling ≠ 0 := by
    rw [perturb_zero]
    exact hpos.ne'
  have hL : ContDiffAt ℝ 3 (fun σ : Fin k → ℝ =>
      Real.log (R.labelWeight (n * R.params.side) (perturb c X σ W) s.support s.labelling)) 0 := hD.log hne
  set cst := Real.log (R.functional (n * R.params.side) (trivialField (n * R.params.side))) +
    Real.log s.fineFactorProd with hcst
  have hev : (fun σ : Fin k → ℝ => s.densityAt (perturb c X σ W)) =ᶠ[nhds 0]
      fun σ => Real.log (R.labelWeight (n * R.params.side) (perturb c X σ W) s.support s.labelling) - cst +
        R.coupling * actionAtLevel R.params.coupling R.params.side R.depth s.outsideHot (perturb c X σ W) := by
    filter_upwards [hg.eventually_perturb h hθ hc X] with σ hσ
    exact (hσ.labelWeight_pos_and_densityAt_eq h).2
  refine ⟨((hL.sub contDiffAt_const).add (contDiffAt_const.mul hAC)).congr_of_eventuallyEq hev, ?_⟩
  intro k2 k3 hu hx
  have hk : k ≠ 0 := by omega
  have hC₁ : ContDiffAt ℝ k (fun σ : Fin k → ℝ =>
      Real.log (R.labelWeight (n * R.params.side) (perturb c X σ W) s.support s.labelling)) 0 :=
    hL.of_le (by exact_mod_cast k3)
  have hC₂ : ContDiffAt ℝ k (fun σ : Fin k → ℝ =>
      actionAtLevel R.params.coupling R.params.side R.depth s.outsideHot (perturb c X σ W)) 0 :=
    hAC.of_le (by exact_mod_cast k3)
  have e1 : mixedDeriv s.densityAt W c X =
      mixedDeriv (fun W' => Real.log (R.labelWeight (n * R.params.side) W' s.support s.labelling)) W c X +
        R.coupling * mixedDeriv (actionAtLevel R.params.coupling R.params.side R.depth s.outsideHot) W c X := by
    unfold mixedDeriv
    rw [(Filter.EventuallyEq.iteratedFDeriv ℝ hev k).eq_of_nhds, iteratedFDeriv_sub_const_add_mul hk hC₁ hC₂]
    simp
  rw [e1]
  have b1 := hb (by omega) k3 hu
  have b2 := hAb k2 k3 hu
  calc _ ≤ |mixedDeriv (fun W' => Real.log (R.labelWeight (n * R.params.side) W' s.support s.labelling)) W c X| +
        |R.coupling * mixedDeriv (actionAtLevel R.params.coupling R.params.side R.depth s.outsideHot) W c X| :=
        abs_add_le _ _
    _ ≤ (R.params.derivBound * R.coupling) ^ k + R.coupling * N₃ := by
      refine add_le_add b1 ?_
      rw [abs_mul, abs_of_nonneg hx]
      exact mul_le_mul_of_nonneg_left b2 hx
end StepSettings
end YangMills.Construction
end
