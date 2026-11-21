import YangMills.Construction.ClusterExpansionOfAStep.DensitiesAgainstAMirror
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction.StepSettings
open BlockAverages LumpContours ColdStepAtMirrorFrames TorusFields TorusLumps FieldMoves MirrorDensities
  ExponentialSums
variable {R : StepSetup} {n : ℕ} [NeZero n] {s : ChartSetting R n}
variable {τ ε θ : ℝ} {W : TorusField (n * R.params.side)} {c : Fin 2 → TorusBond (n * R.params.side)}
  {X : Fin 2 → imaginaryQuaternions}
theorem ChartSetting.NearFreePair.supDist_le_mirror_offset (p : s.NearFreePair τ ε θ W c X) (h : s.Hypotheses)
    {u v : TorusSite (n * R.params.side)}
    (hu : _root_.YangMills.Construction.TorusFields.supDist u (c 0).1 ≤ R.range / 2) (hv : _root_.YangMills.Construction.TorusFields.supDist v (c 0).1 ≤ R.range / 2) :
    _root_.YangMills.Construction.TorusFields.supDist u v ≤ _root_.YangMills.Construction.TorusFields.supDist (siteOfInt (offset (c 0).1 u) : TorusSite (4 * R.range)) (siteOfInt (offset (c 0).1 v)) := by
  have hr := p.range_large h
  have : NeZero (4 * R.range) := ⟨by omega⟩
  have key := _root_.YangMills.Construction.MirrorDensities.supDist_le_supDist_mirror (r := R.range) (c 0).1 (g := offset (c 0).1 u) (g' := offset (c 0).1 v)
    (fun i => by
    have h1 := (abs_offset_le (c 0).1 u i).trans
      (by exact_mod_cast hu : (supDist u (c 0).1 : ℤ) ≤ ((R.range / 2 : ℕ) : ℤ))
    have h2 := (abs_offset_le (c 0).1 v i).trans
      (by exact_mod_cast hv : (supDist v (c 0).1 : ℤ) ≤ ((R.range / 2 : ℕ) : ℤ))
    have h3 : ((R.range / 2 : ℕ) : ℤ) + ((R.range / 2 : ℕ) : ℤ) ≤ R.range := by
      have : R.range / 2 + R.range / 2 ≤ R.range := by omega
      exact_mod_cast this
    have h4 := abs_sub (offset (c 0).1 u i) (offset (c 0).1 v i)
    linarith)
  rwa [add_siteOfInt_offset, add_siteOfInt_offset] at key
theorem ChartSetting.NearFreePair.mirrorCentered_bounds (p : s.NearFreePair τ ε θ W c X) (h : s.Hypotheses)
    {σ : Fin 2 → ℝ} (hτ : ∀ l, |σ l| ≤ τ) (y : TorusSite (n * R.params.side)) :
    ContDiffAt ℝ 3 (mirrorCentered R (c 0).1 c X W y) σ ∧ ∀ (k : ℕ) (ι : Fin k → Fin 2), 1 ≤ k → k ≤ 3 →
      |iteratedFDeriv ℝ k (mirrorCentered R (c 0).1 c X W y) σ fun l => Pi.single (ι l) 1| ≤
        (if k = 3 then R.params.E₃ else R.params.E) / R.params.weight
          (supportDiam (siteOfInt (offset (c 0).1 y) : TorusSite (4 * R.range))
            ((fun l => mirrorBond R.range (c 0).1 (c l)) ∘ ι)) := by
  have hr := p.range_large h
  have hbig := h.range_large
  have : NeZero (4 * R.range) := ⟨by omega⟩
  have hb := centered_alongPair_bounds h.coldExpansion (M := 4 * R.range) (by omega)
    (siteOfInt (offset (c 0).1 y)) (p.commutingPair_mirror h) (p.isCold_perturb_mirror h hτ)
  exact ⟨hb.1, fun k ι k1 k3 => hb.2 k ι k1 k3 p.areUnitVectors⟩
theorem componentBound_nonneg (h : s.Hypotheses) (k : ℕ) : 0 ≤ (if k = 3 then R.params.E₃ else R.params.E) := by
  split_ifs
  · exact h.admissible.E₃_pos.le
  · exact h.admissible.E_pos.le
theorem weightRate_pos (h : s.Hypotheses) : 0 < R.params.weightRate := by
  have := h.admissible.rt_pos
  unfold TorusLumps.StepParameters.weightRate
  positivity
theorem ChartSetting.NearFreePair.sum_mirrorCentered_le (p : s.NearFreePair τ ε θ W c X) (h : s.Hypotheses)
    {σ : Fin 2 → ℝ} (hτ : ∀ l, |σ l| ≤ τ) (k : ℕ) (ι : Fin k → Fin 2) (k1 : 1 ≤ k) (k3 : k ≤ 3) :
    ∑ y ∈ nearBall R (c 0).1, |iteratedFDeriv ℝ k (mirrorCentered R (c 0).1 c X W y) σ fun l => Pi.single (ι l) 1| ≤
      (if k = 3 then R.params.E₃ else R.params.E) * expLatticeSum R.params.weightRate := by
  have hδ := weightRate_pos h
  set l₀ : Fin k := ⟨0, by omega⟩
  set w := (c (ι l₀)).1 with hw
  have hE := componentBound_nonneg h k
  calc _ ≤ ∑ y ∈ nearBall R (c 0).1, (if k = 3 then R.params.E₃ else R.params.E) *
        Real.exp (-R.params.weightRate * _root_.YangMills.Construction.TorusFields.supDist y w) := by
        refine Finset.sum_le_sum fun y hy => ?_
        have hy' : _root_.YangMills.Construction.TorusFields.supDist y (c 0).1 ≤ R.range / 2 := (Finset.mem_filter.mp hy).2
        refine ((p.mirrorCentered_bounds h hτ y).2 k ι k1 k3).trans ?_
        refine (div_weight_le_mul_exp R.params hE _).trans ?_
        refine mul_le_mul_of_nonneg_left ?_ hE
        apply Real.exp_le_exp.mpr
        have h1 := p.supDist_le_mirror_offset h hy' (p.supDist_le (ι l₀))
        have h2 := _root_.YangMills.Construction.MirrorDensities.supDist_le_supportDiam (siteOfInt (offset (c 0).1 y) : TorusSite (4 * R.range))
          ((fun l => mirrorBond R.range (c 0).1 (c l)) ∘ ι) l₀
        have h3 : _root_.YangMills.Construction.TorusFields.supDist y w ≤ supportDiam (siteOfInt (offset (c 0).1 y) : TorusSite (4 * R.range))
            ((fun l => mirrorBond R.range (c 0).1 (c l)) ∘ ι) := h1.trans h2
        have h4 : (_root_.YangMills.Construction.TorusFields.supDist y w : ℝ) ≤ (supportDiam (siteOfInt (offset (c 0).1 y) : TorusSite (4 * R.range))
            ((fun l => mirrorBond R.range (c 0).1 (c l)) ∘ ι) : ℝ) := by exact_mod_cast h3
        nlinarith
    _ ≤ ∑ y : TorusSite (n * R.params.side), (if k = 3 then R.params.E₃ else R.params.E) *
          Real.exp (-R.params.weightRate * _root_.YangMills.Construction.TorusFields.supDist y w) :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun _ _ _ => by positivity
    _ = (if k = 3 then R.params.E₃ else R.params.E) *
          ∑ y : TorusSite (n * R.params.side), Real.exp (-R.params.weightRate * _root_.YangMills.Construction.TorusFields.supDist y w) := by
        rw [Finset.mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left (sum_torus_exp_le hδ w) hE
theorem ChartSetting.NearFreePair.nearSum_bounds (p : s.NearFreePair τ ε θ W c X) (h : s.Hypotheses) {N₃ : ℝ}
    (hA : s.ActionSmooth N₃) (hx : 0 ≤ R.coupling) {σ : Fin 2 → ℝ} (hτ : ∀ l, |σ l| ≤ τ) :
    ContDiffAt ℝ 3 (s.nearSum (c 0).1 c X W) σ ∧ ∀ (k : ℕ) (ι : Fin k → Fin 2), 2 ≤ k → k ≤ 3 →
      |iteratedFDeriv ℝ k (s.nearSum (c 0).1 c X W) σ fun l => Pi.single (ι l) 1| ≤
        (R.params.derivBound * R.coupling) ^ k + R.coupling * N₃ +
          (if k = 3 then R.params.E₃ else R.params.E) * expLatticeSum R.params.weightRate := by
  have hAb := h.alongPair_bounds hA p.norm_exp_sub_one_le p.θ_lt p.isNear p.mem_free p.areUnitVectors
    p.commuting hx hτ
  have hG := fun y => (p.mirrorCentered_bounds h hτ y).1
  have hΨ : ContDiffAt ℝ 3 (fun σ' => ∑ y ∈ nearBall R (c 0).1, mirrorCentered R (c 0).1 c X W y σ') σ :=
    ContDiffAt.sum fun y _ => hG y
  refine ⟨hAb.1.sub hΨ, fun k ι k2 k3 => ?_⟩
  have hle : ((k : ℕ) : WithTop ℕ∞) ≤ 3 := by exact_mod_cast k3
  have e : iteratedFDeriv ℝ k (s.nearSum (c 0).1 c X W) σ =
      iteratedFDeriv ℝ k (alongPair s.densityAt c X W) σ -
        ∑ y ∈ nearBall R (c 0).1, iteratedFDeriv ℝ k (mirrorCentered R (c 0).1 c X W y) σ := by
    unfold ChartSetting.nearSum
    rw [iteratedFDeriv_sub_apply (hAb.1.of_le hle) (hΨ.of_le hle),
      iteratedFDeriv_fun_sum_apply fun y _ => (hG y).of_le hle]
  rw [e]
  simp only [sub_apply, sum_apply]
  have b1 := hAb.2 k ι k2 k3
  have b2 := p.sum_mirrorCentered_le h hτ k ι (by omega) k3
  have b3 := Finset.abs_sum_le_sum_abs (fun y => iteratedFDeriv ℝ k (mirrorCentered R (c 0).1 c X W y) σ
    fun l => Pi.single (ι l) 1) (nearBall R (c 0).1)
  calc _ ≤ _ + _ := abs_sub _ _
    _ ≤ _ := add_le_add b1 (b3.trans b2)
theorem ChartSetting.NearFreePair.abs_mixedDeriv_le (p : s.NearFreePair τ ε θ W c X) (h : s.Hypotheses) {N₃ : ℝ}
    (hA : s.ActionSmooth N₃) (hx : 0 ≤ R.coupling) (hδ : 0 < R.params.decayRate) {t : ℝ} (ht0 : 0 < t)
    (ht : t ≤ τ) :
    |iteratedFDeriv ℝ 2 (alongPair s.densityAt c X W) 0 fun l => Pi.single l 1| ≤
      R.differenceConstant * Real.exp (-R.params.decayRate * R.range / 4) / t ^ 2 +
        2 * ((R.params.derivBound * R.coupling) ^ 3 + R.coupling * N₃ +
          R.params.E₃ * expLatticeSum R.params.weightRate) * t +
        R.params.E * expLatticeSum (R.params.weightRate / 2) *
          Real.exp (-(R.params.weightRate / 2) * _root_.YangMills.Construction.TorusFields.supDist (c 0).1 (c 1).1) := by
  have sq : ∀ σ : Fin 2 → ℝ, (∀ i, 0 ≤ σ i ∧ σ i ≤ t) → ∀ l, |σ l| ≤ τ := fun σ hσ l => by
    rw [abs_of_nonneg (hσ l).1]
    exact (hσ l).2.trans ht
  have h0 : ∀ l : Fin 2, |(0 : Fin 2 → ℝ) l| ≤ τ := fun l => by
    simpa using ht0.le.trans ht
  have hU := abs_iteratedFDeriv_two_le_of_mixed_difference (U := s.nearSum (c 0).1 c X W) ht0
    (fun σ hσ => (p.nearSum_bounds h hA hx (sq σ hσ)).1)
    (fun σ hσ ι => by
      have := (p.nearSum_bounds h hA hx (sq σ hσ)).2 3 ι (by norm_num) le_rfl
      rwa [if_pos rfl] at this)
    (p.abs_second_difference_nearSum_le h hδ ht0.le ht)
  have hAb := h.alongPair_bounds hA p.norm_exp_sub_one_le p.θ_lt p.isNear p.mem_free p.areUnitVectors
    p.commuting hx h0
  have hG := fun y => (p.mirrorCentered_bounds h h0 y).1
  have hle : ((2 : ℕ) : WithTop ℕ∞) ≤ 3 := by norm_num
  have hΨ : ContDiffAt ℝ 3 (fun σ' => ∑ y ∈ nearBall R (c 0).1, mirrorCentered R (c 0).1 c X W y σ') 0 :=
    ContDiffAt.sum fun y _ => hG y
  have e : iteratedFDeriv ℝ 2 (s.nearSum (c 0).1 c X W) 0 =
      iteratedFDeriv ℝ 2 (alongPair s.densityAt c X W) 0 -
        ∑ y ∈ nearBall R (c 0).1, iteratedFDeriv ℝ 2 (mirrorCentered R (c 0).1 c X W y) 0 := by
    unfold ChartSetting.nearSum
    rw [iteratedFDeriv_sub_apply (hAb.1.of_le hle) (hΨ.of_le hle),
      iteratedFDeriv_fun_sum_apply fun y _ => (hG y).of_le hle]
  rw [e] at hU
  simp only [sub_apply, sum_apply] at hU
  have hrate := weightRate_pos h
  have hE := h.admissible.E_pos
  have hsum : ∑ y ∈ nearBall R (c 0).1,
      |iteratedFDeriv ℝ 2 (mirrorCentered R (c 0).1 c X W y) 0 fun l => Pi.single l 1| ≤
      R.params.E * expLatticeSum (R.params.weightRate / 2) *
        Real.exp (-(R.params.weightRate / 2) * _root_.YangMills.Construction.TorusFields.supDist (c 0).1 (c 1).1) := by
    calc _ ≤ ∑ y ∈ nearBall R (c 0).1, R.params.E *
          Real.exp (-(R.params.weightRate / 2) * supDist (c 0).1 (c 1).1) *
          Real.exp (-(R.params.weightRate / 2) * _root_.YangMills.Construction.TorusFields.supDist y (c 0).1) := by
          refine Finset.sum_le_sum fun y hy => ?_
          have hy' : _root_.YangMills.Construction.TorusFields.supDist y (c 0).1 ≤ R.range / 2 := (Finset.mem_filter.mp hy).2
          have b := (p.mirrorCentered_bounds h h0 y).2 2 id (by norm_num) (by norm_num)
          rw [if_neg (by norm_num)] at b
          refine b.trans ((div_weight_le_mul_exp R.params hE.le _).trans ?_)
          rw [mul_assoc, ← Real.exp_add]
          refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hE.le
          set sp := supportDiam (siteOfInt (offset (c 0).1 y) : TorusSite (4 * R.range))
            ((fun l => mirrorBond R.range (c 0).1 (c l)) ∘ id) with hsp
          have m1 : _root_.YangMills.Construction.TorusFields.supDist y (c 0).1 ≤ sp := (p.supDist_le_mirror_offset h hy' (p.supDist_le 0)).trans
            (_root_.YangMills.Construction.MirrorDensities.supDist_le_supportDiam _ ((fun l => mirrorBond R.range (c 0).1 (c l)) ∘ id) 0)
          have m2 : _root_.YangMills.Construction.TorusFields.supDist (c 0).1 (c 1).1 ≤ sp :=
            (p.supDist_le_mirror_offset h (p.supDist_le 0) (p.supDist_le 1)).trans
              (_root_.YangMills.Construction.MirrorDensities.supDist_bonds_le_supportDiam _ ((fun l => mirrorBond R.range (c 0).1 (c l)) ∘ id) 0 1)
          have m1' : (_root_.YangMills.Construction.TorusFields.supDist y (c 0).1 : ℝ) ≤ sp := by exact_mod_cast m1
          have m2' : (_root_.YangMills.Construction.TorusFields.supDist (c 0).1 (c 1).1 : ℝ) ≤ sp := by exact_mod_cast m2
          nlinarith
      _ ≤ ∑ y : TorusSite (n * R.params.side), R.params.E *
          Real.exp (-(R.params.weightRate / 2) * supDist (c 0).1 (c 1).1) *
          Real.exp (-(R.params.weightRate / 2) * _root_.YangMills.Construction.TorusFields.supDist y (c 0).1) :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun _ _ _ => by positivity
      _ = R.params.E * Real.exp (-(R.params.weightRate / 2) * _root_.YangMills.Construction.TorusFields.supDist (c 0).1 (c 1).1) *
          ∑ y : TorusSite (n * R.params.side), Real.exp (-(R.params.weightRate / 2) * _root_.YangMills.Construction.TorusFields.supDist y (c 0).1) := by
          rw [Finset.mul_sum]
      _ ≤ R.params.E * Real.exp (-(R.params.weightRate / 2) * _root_.YangMills.Construction.TorusFields.supDist (c 0).1 (c 1).1) *
          expLatticeSum (R.params.weightRate / 2) :=
          mul_le_mul_of_nonneg_left (sum_torus_exp_le (by linarith) _) (by positivity)
      _ = _ := by ring
  have b3 := Finset.abs_sum_le_sum_abs (fun y => iteratedFDeriv ℝ 2 (mirrorCentered R (c 0).1 c X W y) 0
    fun l => Pi.single l 1) (nearBall R (c 0).1)
  set a := iteratedFDeriv ℝ 2 (alongPair s.densityAt c X W) 0 fun l => Pi.single l 1
  set b := ∑ y ∈ nearBall R (c 0).1, iteratedFDeriv ℝ 2 (mirrorCentered R (c 0).1 c X W y) 0
    fun l => Pi.single l 1
  have : |a| ≤ |a - b| + |b| := by
    have := abs_add_le (a - b) b
    simpa using this
  linarith
theorem ChartSetting.NearFreePair.abs_firstDeriv_le (p : s.NearFreePair τ ε θ W c X) (h : s.Hypotheses) {N₃ : ℝ}
    (hA : s.ActionSmooth N₃) (hx : 0 ≤ R.coupling) (hδ : 0 < R.params.decayRate) {t : ℝ} (ht0 : 0 < t)
    (ht : t ≤ τ) :
    |iteratedFDeriv ℝ 1 (alongPair s.densityAt c X W) 0 fun _ => Pi.single 0 1| ≤
      R.differenceConstant * Real.exp (-R.params.decayRate * R.range / 4) / t +
        ((R.params.derivBound * R.coupling) ^ 2 + R.coupling * N₃ +
          R.params.E * expLatticeSum R.params.weightRate) * t +
        R.params.E * expLatticeSum R.params.weightRate := by
  have sq : ∀ u : ℝ, 0 ≤ u → u ≤ t → ∀ l, |(![u, 0] : Fin 2 → ℝ) l| ≤ τ := by
    intro u a b l
    have hτ : 0 ≤ τ := ht0.le.trans ht
    fin_cases l
    · simpa [abs_of_nonneg a] using b.trans ht
    · simpa using hτ
  have h0 : ∀ l : Fin 2, |(0 : Fin 2 → ℝ) l| ≤ τ := fun l => by
    simpa using ht0.le.trans ht
  have hU := abs_iteratedFDeriv_one_le_of_difference (U := s.nearSum (c 0).1 c X W) ht0
    (fun u a b => (p.nearSum_bounds h hA hx (sq u a b)).1.of_le (by norm_num))
    (fun u a b => by
      have := (p.nearSum_bounds h hA hx (sq u a b)).2 2 (fun _ => 0) (by norm_num) (by norm_num)
      rwa [if_neg (by norm_num)] at this)
    (p.abs_first_difference_nearSum_le h hδ ht0.le ht)
  have hAb := h.alongPair_bounds hA p.norm_exp_sub_one_le p.θ_lt p.isNear p.mem_free p.areUnitVectors
    p.commuting hx h0
  have hG := fun y => (p.mirrorCentered_bounds h h0 y).1
  have hle : ((1 : ℕ) : WithTop ℕ∞) ≤ 3 := by norm_num
  have hΨ : ContDiffAt ℝ 3 (fun σ' => ∑ y ∈ nearBall R (c 0).1, mirrorCentered R (c 0).1 c X W y σ') 0 :=
    ContDiffAt.sum fun y _ => hG y
  have e : iteratedFDeriv ℝ 1 (s.nearSum (c 0).1 c X W) 0 =
      iteratedFDeriv ℝ 1 (alongPair s.densityAt c X W) 0 -
        ∑ y ∈ nearBall R (c 0).1, iteratedFDeriv ℝ 1 (mirrorCentered R (c 0).1 c X W y) 0 := by
    unfold ChartSetting.nearSum
    rw [iteratedFDeriv_sub_apply (hAb.1.of_le hle) (hΨ.of_le hle),
      iteratedFDeriv_fun_sum_apply fun y _ => (hG y).of_le hle]
  rw [e] at hU
  simp only [sub_apply, sum_apply] at hU
  have hsum := p.sum_mirrorCentered_le h h0 1 (fun _ => 0) le_rfl (by norm_num)
  rw [if_neg (by norm_num)] at hsum
  have b3 := Finset.abs_sum_le_sum_abs (fun y => iteratedFDeriv ℝ 1 (mirrorCentered R (c 0).1 c X W y) 0
    fun _ => Pi.single 0 1) (nearBall R (c 0).1)
  set a := iteratedFDeriv ℝ 1 (alongPair s.densityAt c X W) 0 fun _ => Pi.single 0 1
  set b := ∑ y ∈ nearBall R (c 0).1, iteratedFDeriv ℝ 1 (mirrorCentered R (c 0).1 c X W y) 0
    fun _ => Pi.single 0 1
  have : |a| ≤ |a - b| + |b| := by
    have := abs_add_le (a - b) b
    simpa using this
  linarith
theorem isCold_of_isHullState_empty (h : s.Hypotheses) {W' : TorusField (n * R.params.side)}
    (hh : IsHullState R.params R.range W' ∅) : IsCold R.params.threshold W' := by
  intro x μ ν hlt
  by_contra hcon
  have hcon' : R.params.threshold ≤ curvature W' x μ ν := not_lt.mp hcon
  have hl := (mem_torusHotLumps_iff R.params h.admissible h.side_dvd W' (torusLumpOf R.params x)).mpr
    ⟨x, μ, ν, hlt, hcon', x, by simp [plaquetteVertices], rfl⟩
  have hz : x ∈ torusHotSites R.params W' := mem_torusHotSites_iff.mpr ⟨_, hl, mem_torusLumpOf_self x⟩
  exact Finset.notMem_empty _ (hh.1 (subset_thickening_self _ _ hz))
theorem ChartSetting.Hypotheses.densityAt_eq_of_support_empty (h : s.Hypotheses) (he : s.support = ∅) {θ' : ℝ}
    {W' : TorusField (n * R.params.side)} (hg' : s.IsNear θ' W') :
    s.densityAt W' = ∑ y, centered R.density (n * R.params.side) y W' := by
  have key : ∀ (Y : Finset (TorusSite (n * R.params.side))) (ω : Y → R.labels.Ω), Y = ∅ →
      IsHullState R.params R.range W' Y → ∀ y,
      R.siteDensity (n * R.params.side) y W' Y ω = centered R.density (n * R.params.side) y W' := by
    rintro Y ω rfl hh y
    exact h.hullExpansion.empty (n * R.params.side) h.isBlockTorusSide W' ω y hh
  unfold ChartSetting.densityAt
  exact Finset.sum_congr rfl fun y _ => key _ _ he (hg'.isHullState h) y
theorem ChartSetting.Hypotheses.abs_iteratedFDeriv_le_of_support_empty (h : s.Hypotheses) (he : s.support = ∅)
    (hg : s.IsNear θ W) (hθ : θ < R.params.threshold) (hc : ∀ l, c l ∈ s.free) (hcomm : CommutingPair c X)
    (hu : AreUnitVectors X) (k : ℕ) (ι : Fin k → Fin 2) (k1 : 1 ≤ k) (k3 : k ≤ 3) :
    |iteratedFDeriv ℝ k (alongPair s.densityAt c X W) 0 fun l => Pi.single (ι l) 1| ≤
      ∑ y, (if k = 3 then R.params.E₃ else R.params.E) / R.params.weight (supportDiam y (c ∘ ι)) := by
  have hN : R.params.n₀ ≤ n * R.params.side := h.n₀_le.trans (Nat.le_mul_of_pos_right _ h.side_pos)
  have hcold : IsCold R.params.threshold (perturb c X (0 : Fin 2 → ℝ) W) := by
    rw [perturb_zero]
    have hh := hg.isHullState h
    rw [he] at hh
    exact isCold_of_isHullState_empty h hh
  have hG := fun y => centered_alongPair_bounds h.coldExpansion hN y hcomm hcold
  have hev : alongPair s.densityAt c X W =ᶠ[nhds 0]
      fun σ => ∑ y, alongPair (centered R.density (n * R.params.side) y) c X W σ := by
    filter_upwards [hg.eventually_perturb h hθ hc X] with σ hσ
    exact h.densityAt_eq_of_support_empty he hσ
  have hle : ((k : ℕ) : WithTop ℕ∞) ≤ 3 := by exact_mod_cast k3
  rw [(Filter.EventuallyEq.iteratedFDeriv ℝ hev k).eq_of_nhds,
    iteratedFDeriv_fun_sum_apply fun y _ => (hG y).1.of_le hle]
  simp only [sum_apply]
  exact (Finset.abs_sum_le_sum_abs _ _).trans
    (Finset.sum_le_sum fun y _ => (hG y).2 k ι k1 k3 hu)
theorem exp_interpolate_two {D M τ w : ℝ} (hD : 0 ≤ D) (_hM : 0 ≤ M) (hτ : 0 < τ) (hw : 0 ≤ w) :
    D * Real.exp (-w) / (τ * Real.exp (-(w / 4))) ^ 2 + 2 * M * (τ * Real.exp (-(w / 4))) ≤
      (D / τ ^ 2 + 2 * M * τ) * Real.exp (-(w / 4)) := by
  have e1 : (τ * Real.exp (-(w / 4))) ^ 2 = τ ^ 2 * Real.exp (-(w / 2)) := by
    rw [mul_pow, ← Real.exp_nat_mul]
    congr 2
    push_cast
    ring
  have e2 : Real.exp (-w) = Real.exp (-(w / 2)) * Real.exp (-(w / 2)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have e3 : D * Real.exp (-w) / (τ * Real.exp (-(w / 4))) ^ 2 = D / τ ^ 2 * Real.exp (-(w / 2)) := by
    rw [e1, e2]
    have := Real.exp_pos (-(w / 2))
    field_simp
  have e4 : Real.exp (-(w / 2)) ≤ Real.exp (-(w / 4)) := Real.exp_le_exp.mpr (by linarith)
  rw [e3]
  have h1 : D / τ ^ 2 * Real.exp (-(w / 2)) ≤ D / τ ^ 2 * Real.exp (-(w / 4)) :=
    mul_le_mul_of_nonneg_left e4 (by positivity)
  nlinarith
theorem exp_interpolate_one {D M τ w : ℝ} (hτ : 0 < τ) :
    D * Real.exp (-w) / (τ * Real.exp (-(w / 2))) + M * (τ * Real.exp (-(w / 2))) =
      (D / τ + M * τ) * Real.exp (-(w / 2)) := by
  have e2 : Real.exp (-w) = Real.exp (-(w / 2)) * Real.exp (-(w / 2)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have := Real.exp_pos (-(w / 2))
  rw [e2]
  field_simp
def StepSetup.mainConstant (R : StepSetup) : ℝ := R.params.E * expLatticeSum (R.params.weightRate / 2)
def StepSetup.tailConstant (R : StepSetup) (τ N₃ : ℝ) : ℝ :=
  R.differenceConstant / τ ^ 2 + 2 * ((R.params.derivBound * R.coupling) ^ 3 + R.coupling * N₃ +
    R.params.E₃ * expLatticeSum R.params.weightRate) * τ
def StepSetup.firstTailConstant (R : StepSetup) (τ N₃ : ℝ) : ℝ :=
  R.differenceConstant / τ + ((R.params.derivBound * R.coupling) ^ 2 + R.coupling * N₃ +
    R.params.E * expLatticeSum R.params.weightRate) * τ
theorem decayRate_pos (h : s.Hypotheses) : 0 < R.params.decayRate := by
  have := h.admissible.rt_pos
  unfold TorusLumps.StepParameters.decayRate
  positivity
theorem differenceConstant_nonneg (h : s.Hypotheses) : 0 ≤ R.differenceConstant := by
  have := decayRate_pos h
  have hL : 0 < expLatticeSum (R.params.decayRate / 2) := expLatticeSum_pos (by linarith)
  unfold StepSetup.differenceConstant
  positivity
theorem neg_mul_le_of_le_of_le {ρ sp a b : ℝ} (hρ : 0 ≤ ρ) (ha : a ≤ sp) (hb : b ≤ sp) :
    -ρ * sp ≤ -(ρ / 2) * a + -(ρ / 2) * b := by
  nlinarith
theorem mul_exp_neg_le_self {τ a : ℝ} (hτ : 0 < τ) (ha : 0 ≤ a) : τ * Real.exp (-a) ≤ τ := by
  have : Real.exp (-a) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  nlinarith
theorem bound_of_far {v D M M' τ δ d rr main t : ℝ} (hD : 0 ≤ D) (hM' : 0 ≤ M') (hMM : M' ≤ M) (hτ : 0 < τ)
    (hδ : 0 < δ) (hd : 0 ≤ d) (hfar : rr / 2 < d) (hmain : 0 ≤ main)
    (ht : t = τ * Real.exp (-(δ * d / 4 / 4)))
    (hb : v ≤ D * Real.exp (-δ * d / 4) / t ^ 2 + 2 * M' * t) :
    v ≤ (main + (D / τ ^ 2 + 2 * M * τ) * Real.exp (-δ * rr / 64)) * Real.exp (-(δ / 32) * d) := by
  have hw0 : 0 ≤ δ * d / 4 := by positivity
  have hM : 0 ≤ M := hM'.trans hMM
  have i1 := exp_interpolate_two (D := D) (M := M) hD hM hτ hw0
  rw [← ht] at i1
  have e0 : Real.exp (-δ * d / 4) = Real.exp (-(δ * d / 4)) := by
    congr 1
    ring
  rw [e0] at hb
  have ht0 : 0 < t := by
    rw [ht]
    positivity
  have h2 : 2 * M' * t ≤ 2 * M * t := by nlinarith
  have hT : 0 ≤ D / τ ^ 2 + 2 * M * τ := by positivity
  have e3 : Real.exp (-(δ * d / 4 / 4)) ≤ Real.exp (-δ * rr / 64) * Real.exp (-(δ / 32) * d) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    nlinarith
  have e4 : (D / τ ^ 2 + 2 * M * τ) * Real.exp (-(δ * d / 4 / 4)) ≤
      (D / τ ^ 2 + 2 * M * τ) * (Real.exp (-δ * rr / 64) * Real.exp (-(δ / 32) * d)) :=
    mul_le_mul_of_nonneg_left e3 hT
  have e5 : 0 ≤ main * Real.exp (-(δ / 32) * d) := by positivity
  have e6 : (main + (D / τ ^ 2 + 2 * M * τ) * Real.exp (-δ * rr / 64)) * Real.exp (-(δ / 32) * d) =
      main * Real.exp (-(δ / 32) * d) +
        (D / τ ^ 2 + 2 * M * τ) * (Real.exp (-δ * rr / 64) * Real.exp (-(δ / 32) * d)) := by ring
  rw [e6]
  linarith
theorem bound_of_near {v D M τ δ ρ d rr main t : ℝ} (hD : 0 ≤ D) (hM : 0 ≤ M) (hτ : 0 < τ) (hδ : 0 < δ)
    (hρ : δ / 32 ≤ ρ) (hd : 0 ≤ d) (hnear : d ≤ rr / 2) (hr : 0 ≤ rr) (hmain : 0 ≤ main)
    (ht : t = τ * Real.exp (-(δ * rr / 4 / 4)))
    (hb : v ≤ D * Real.exp (-δ * rr / 4) / t ^ 2 + 2 * M * t + main * Real.exp (-ρ * d)) :
    v ≤ (main + (D / τ ^ 2 + 2 * M * τ) * Real.exp (-δ * rr / 64)) * Real.exp (-(δ / 32) * d) := by
  have hw0 : 0 ≤ δ * rr / 4 := by positivity
  have i1 := exp_interpolate_two (D := D) (M := M) hD hM hτ hw0
  rw [← ht] at i1
  have e0 : Real.exp (-δ * rr / 4) = Real.exp (-(δ * rr / 4)) := by
    congr 1
    ring
  rw [e0] at hb
  have hT : 0 ≤ D / τ ^ 2 + 2 * M * τ := by positivity
  have e3 : Real.exp (-(δ * rr / 4 / 4)) ≤ Real.exp (-δ * rr / 64) * Real.exp (-(δ / 32) * d) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    nlinarith
  have e4 : (D / τ ^ 2 + 2 * M * τ) * Real.exp (-(δ * rr / 4 / 4)) ≤
      (D / τ ^ 2 + 2 * M * τ) * (Real.exp (-δ * rr / 64) * Real.exp (-(δ / 32) * d)) :=
    mul_le_mul_of_nonneg_left e3 hT
  have e5 : main * Real.exp (-ρ * d) ≤ main * Real.exp (-(δ / 32) * d) :=
    mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by nlinarith)) hmain
  have e6 : (main + (D / τ ^ 2 + 2 * M * τ) * Real.exp (-δ * rr / 64)) * Real.exp (-(δ / 32) * d) =
      main * Real.exp (-(δ / 32) * d) +
        (D / τ ^ 2 + 2 * M * τ) * (Real.exp (-δ * rr / 64) * Real.exp (-(δ / 32) * d)) := by ring
  rw [e6]
  linarith
theorem bound_of_empty {v main T δ ρ d rr : ℝ} (hT : 0 ≤ T) (hmain : 0 ≤ main) (hρ : δ / 32 ≤ ρ) (hd : 0 ≤ d)
    (hb : v ≤ main * Real.exp (-ρ * d)) :
    v ≤ (main + T * Real.exp (-δ * rr / 64)) * Real.exp (-(δ / 32) * d) := by
  have e5 : main * Real.exp (-ρ * d) ≤ main * Real.exp (-(δ / 32) * d) :=
    mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by nlinarith)) hmain
  have e6 : 0 ≤ T * Real.exp (-δ * rr / 64) * Real.exp (-(δ / 32) * d) := by positivity
  have e7 : (main + T * Real.exp (-δ * rr / 64)) * Real.exp (-(δ / 32) * d) =
      main * Real.exp (-(δ / 32) * d) + T * Real.exp (-δ * rr / 64) * Real.exp (-(δ / 32) * d) := by ring
  rw [e7]
  linarith
theorem decayRate_div_le_weightRate (h : s.Hypotheses) : R.params.decayRate / 32 ≤ R.params.weightRate / 2 := by
  have := h.admissible.rt_pos
  unfold TorusLumps.StepParameters.decayRate TorusLumps.StepParameters.weightRate
  linarith
theorem tailConstant_nonneg (h : s.Hypotheses) {τ N₃ : ℝ} (hτ : 0 < τ) (hN₃ : 0 ≤ N₃) (hx : 0 ≤ R.coupling)
    (hCd : 0 ≤ R.params.derivBound) : 0 ≤ R.tailConstant τ N₃ := by
  have hD := differenceConstant_nonneg h
  have hL := expLatticeSum_pos (weightRate_pos h)
  have hE₃ := h.admissible.E₃_pos
  unfold StepSetup.tailConstant
  positivity
theorem mainConstant_nonneg (h : s.Hypotheses) : 0 ≤ R.mainConstant := by
  have hrate := weightRate_pos h
  have hL : 0 < expLatticeSum (R.params.weightRate / 2) := expLatticeSum_pos (by linarith)
  have hE := h.admissible.E_pos
  unfold StepSetup.mainConstant
  positivity
theorem ChartSetting.Hypotheses.abs_mixedDeriv_le_of_support_empty (h : s.Hypotheses) (he : s.support = ∅)
    (hg : s.IsNear (R.params.threshold / 4) W) (hc : ∀ l, c l ∈ s.free) (hu : AreUnitVectors X)
    (hcomm : CommutingPair c X) :
    |iteratedFDeriv ℝ 2 (alongPair s.densityAt c X W) 0 fun l => Pi.single l 1| ≤
      R.mainConstant * Real.exp (-(R.params.weightRate / 2) * _root_.YangMills.Construction.TorusFields.supDist (c 0).1 (c 1).1) := by
  have hrate := weightRate_pos h
  have hE := h.admissible.E_pos
  have hσ := h.threshold_pos
  have b := h.abs_iteratedFDeriv_le_of_support_empty he hg (by linarith) hc hcomm hu 2 id (by norm_num)
    (by norm_num)
  refine b.trans ?_
  unfold StepSetup.mainConstant
  calc _ ≤ ∑ y : TorusSite (n * R.params.side), R.params.E *
        Real.exp (-(R.params.weightRate / 2) * _root_.YangMills.Construction.TorusFields.supDist (c 0).1 (c 1).1) *
        Real.exp (-(R.params.weightRate / 2) * _root_.YangMills.Construction.TorusFields.supDist y (c 0).1) := by
        refine Finset.sum_le_sum fun y _ => ?_
        rw [if_neg (by norm_num)]
        refine (div_weight_le_mul_exp R.params hE.le _).trans ?_
        rw [mul_assoc, ← Real.exp_add]
        refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hE.le
        have m1 : _root_.YangMills.Construction.TorusFields.supDist y (c 0).1 ≤ supportDiam y (c ∘ id) := _root_.YangMills.Construction.MirrorDensities.supDist_le_supportDiam y (c ∘ id) 0
        have m2 : _root_.YangMills.Construction.TorusFields.supDist (c 0).1 (c 1).1 ≤ supportDiam y (c ∘ id) :=
          _root_.YangMills.Construction.MirrorDensities.supDist_bonds_le_supportDiam y (c ∘ id) 0 1
        exact neg_mul_le_of_le_of_le hrate.le (by exact_mod_cast m2) (by exact_mod_cast m1)
    _ = R.params.E * Real.exp (-(R.params.weightRate / 2) * _root_.YangMills.Construction.TorusFields.supDist (c 0).1 (c 1).1) *
        ∑ y : TorusSite (n * R.params.side), Real.exp (-(R.params.weightRate / 2) * _root_.YangMills.Construction.TorusFields.supDist y (c 0).1) := by
        rw [Finset.mul_sum]
    _ ≤ R.params.E * Real.exp (-(R.params.weightRate / 2) * _root_.YangMills.Construction.TorusFields.supDist (c 0).1 (c 1).1) *
        expLatticeSum (R.params.weightRate / 2) :=
        mul_le_mul_of_nonneg_left (sum_torus_exp_le (by linarith) _) (by positivity)
    _ = _ := by ring
theorem ChartSetting.Hypotheses.abs_mixedDeriv_le_exp (h : s.Hypotheses) {N₃ : ℝ} (hA : s.ActionSmooth N₃)
    (hN₃ : 0 ≤ N₃) {τ : ℝ} (hτ : 0 < τ)
    (hstep : ∀ a : imaginaryQuaternions, ‖a‖ ≤ 2 * τ →
      ‖((expUnit a : UnitQuaternion) : ℍ[ℝ]) - 1‖ ≤ R.params.threshold / 64)
    (hx : 0 ≤ R.coupling) (hCd : 0 ≤ R.params.derivBound) (hg : s.IsNear (R.params.threshold / 4) W)
    (hc : ∀ l, c l ∈ s.free) (hu : AreUnitVectors X) (hcomm : CommutingPair c X) :
    |iteratedFDeriv ℝ 2 (alongPair s.densityAt c X W) 0 fun l => Pi.single l 1| ≤
      (R.mainConstant + R.tailConstant τ N₃ * Real.exp (-R.params.decayRate * R.range / 64)) *
        Real.exp (-(R.params.decayRate / 32) * _root_.YangMills.Construction.TorusFields.supDist (c 0).1 (c 1).1) := by
  have hδ := decayRate_pos h
  have hσ := h.threshold_pos
  have hD := differenceConstant_nonneg h
  have hLr : 0 < expLatticeSum R.params.weightRate := expLatticeSum_pos (weightRate_pos h)
  have hE₃ := h.admissible.E₃_pos
  have hθ : R.params.threshold / 4 + 4 * (R.params.threshold / 64) < R.params.threshold := by linarith
  have hM' : 0 ≤ (R.params.derivBound * R.coupling) ^ 3 + R.coupling * N₃ := by positivity
  have hM : 0 ≤ (R.params.derivBound * R.coupling) ^ 3 + R.coupling * N₃ +
      R.params.E₃ * expLatticeSum R.params.weightRate := by positivity
  have hd0 : (0 : ℝ) ≤ ((_root_.YangMills.Construction.TorusFields.supDist (c 0).1 (c 1).1 : ℕ) : ℝ) := by positivity
  by_cases he : s.support = ∅
  · exact bound_of_empty (tailConstant_nonneg h hτ hN₃ hx hCd) (mainConstant_nonneg h)
      (decayRate_div_le_weightRate h) hd0 (h.abs_mixedDeriv_le_of_support_empty he hg hc hu hcomm)
  · have hne : s.support.Nonempty := Finset.nonempty_iff_ne_empty.mpr he
    by_cases hfar : (R.range : ℝ) / 2 < ((_root_.YangMills.Construction.TorusFields.supDist (c 0).1 (c 1).1 : ℕ) : ℝ)
    · have hw : 0 ≤ R.params.decayRate * ((_root_.YangMills.Construction.TorusFields.supDist (c 0).1 (c 1).1 : ℕ) : ℝ) / 4 / 4 := by positivity
      have b := h.abs_mixedDeriv_le hA hstep hθ hg hc hu hcomm hfar hx hδ
        (t := τ * Real.exp (-(R.params.decayRate * ((_root_.YangMills.Construction.TorusFields.supDist (c 0).1 (c 1).1 : ℕ) : ℝ) / 4 / 4)))
        (by positivity) (mul_exp_neg_le_self hτ hw)
      rw [mixedDeriv_eq_iteratedFDeriv_two] at b
      exact bound_of_far hD hM' (le_add_of_nonneg_right (by positivity)) hτ hδ hd0 hfar
        (mainConstant_nonneg h) rfl b
    · have hd3 : ((_root_.YangMills.Construction.TorusFields.supDist (c 0).1 (c 1).1 : ℕ) : ℝ) ≤ (R.range : ℝ) / 2 := not_lt.mp hfar
      have hd2 : _root_.YangMills.Construction.TorusFields.supDist (c 0).1 (c 1).1 ≤ R.range / 2 := by
        have h2 : (2 * _root_.YangMills.Construction.TorusFields.supDist (c 0).1 (c 1).1 : ℝ) ≤ R.range := by linarith
        have h3 : 2 * _root_.YangMills.Construction.TorusFields.supDist (c 0).1 (c 1).1 ≤ R.range := by exact_mod_cast h2
        omega
      have p : s.NearFreePair τ (R.params.threshold / 64) (R.params.threshold / 4) W c X :=
        { norm_exp_sub_one_le := hstep
          θ_pos := by positivity
          θ_lt := hθ
          isNear := hg
          mem_free := hc
          areUnitVectors := hu
          commuting := hcomm
          supDist_le := fun l => by
            fin_cases l
            · simp [_root_.YangMills.Construction.TorusFields.supDist_self]
            · simpa [_root_.YangMills.Construction.TorusFields.supDist_comm] using hd2
          support_nonempty := hne }
      have hr0 : (0 : ℝ) ≤ (R.range : ℝ) := by positivity
      have hw : 0 ≤ R.params.decayRate * (R.range : ℝ) / 4 / 4 := by positivity
      have b := p.abs_mixedDeriv_le h hA hx hδ
        (t := τ * Real.exp (-(R.params.decayRate * (R.range : ℝ) / 4 / 4))) (by positivity)
        (mul_exp_neg_le_self hτ hw)
      exact bound_of_near hD hM hτ hδ (decayRate_div_le_weightRate h) hd0 hd3 hr0 (mainConstant_nonneg h) rfl b
theorem bound_first {v D M τ δ rr main t : ℝ} (hτ : 0 < τ)
    (ht : t = τ * Real.exp (-(δ * rr / 4 / 2)))
    (hb : v ≤ D * Real.exp (-δ * rr / 4) / t + M * t + main) :
    v ≤ main + (D / τ + M * τ) * Real.exp (-δ * rr / 8) := by
  have e0 : Real.exp (-δ * rr / 4) = Real.exp (-(δ * rr / 4)) := by
    congr 1
    ring
  have e1 : Real.exp (-δ * rr / 8) = Real.exp (-(δ * rr / 4 / 2)) := by
    congr 1
    ring
  rw [e0, ht, exp_interpolate_one hτ] at hb
  rw [e1]
  linarith
theorem ChartSetting.Hypotheses.abs_firstDeriv_le (h : s.Hypotheses) {N₃ : ℝ} (hA : s.ActionSmooth N₃)
    (hN₃ : 0 ≤ N₃) {τ : ℝ} (hτ : 0 < τ)
    (hstep : ∀ a : imaginaryQuaternions, ‖a‖ ≤ 2 * τ →
      ‖((expUnit a : UnitQuaternion) : ℍ[ℝ]) - 1‖ ≤ R.params.threshold / 64)
    (hx : 0 ≤ R.coupling) (_hCd : 0 ≤ R.params.derivBound) (hg : s.IsNear (R.params.threshold / 4) W)
    (hc : ∀ l, c l ∈ s.free) (hu : AreUnitVectors X) (hcomm : CommutingPair c X) (hcc : c 1 = c 0) :
    |iteratedFDeriv ℝ 1 (alongPair s.densityAt c X W) 0 fun _ => Pi.single 0 1| ≤
      R.params.E * expLatticeSum R.params.weightRate +
        R.firstTailConstant τ N₃ * Real.exp (-R.params.decayRate * R.range / 8) := by
  have hδ := decayRate_pos h
  have hrate := weightRate_pos h
  have hσ := h.threshold_pos
  have hE := h.admissible.E_pos
  have hD := differenceConstant_nonneg h
  have hLr : 0 < expLatticeSum R.params.weightRate := expLatticeSum_pos hrate
  have hθ : R.params.threshold / 4 + 4 * (R.params.threshold / 64) < R.params.threshold := by linarith
  have htail : 0 ≤ R.firstTailConstant τ N₃ := by
    unfold StepSetup.firstTailConstant
    positivity
  by_cases he : s.support = ∅
  · have b := h.abs_iteratedFDeriv_le_of_support_empty he hg (by linarith) hc hcomm hu 1 (fun _ => 0) le_rfl
      (by norm_num)
    have h1 : ∑ y : TorusSite (n * R.params.side), (if (1 : ℕ) = 3 then R.params.E₃ else R.params.E) /
        R.params.weight (supportDiam y (c ∘ fun _ : Fin 1 => (0 : Fin 2))) ≤
          R.params.E * expLatticeSum R.params.weightRate := by
      calc _ ≤ ∑ y : TorusSite (n * R.params.side), R.params.E *
            Real.exp (-R.params.weightRate * _root_.YangMills.Construction.TorusFields.supDist y (c 0).1) := by
            refine Finset.sum_le_sum fun y _ => ?_
            rw [if_neg (by norm_num)]
            refine (div_weight_le_mul_exp R.params hE.le _).trans ?_
            refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hE.le
            have m1 : _root_.YangMills.Construction.TorusFields.supDist y (c 0).1 ≤ supportDiam y (c ∘ fun _ : Fin 1 => (0 : Fin 2)) :=
              _root_.YangMills.Construction.MirrorDensities.supDist_le_supportDiam y (c ∘ fun _ : Fin 1 => (0 : Fin 2)) 0
            have m1' : (_root_.YangMills.Construction.TorusFields.supDist y (c 0).1 : ℝ) ≤ supportDiam y (c ∘ fun _ : Fin 1 => (0 : Fin 2)) := by
              exact_mod_cast m1
            exact mul_le_mul_of_nonpos_left m1' (by linarith)
        _ = R.params.E * ∑ y : TorusSite (n * R.params.side),
              Real.exp (-R.params.weightRate * _root_.YangMills.Construction.TorusFields.supDist y (c 0).1) := by
            rw [Finset.mul_sum]
        _ ≤ _ := mul_le_mul_of_nonneg_left (sum_torus_exp_le hrate _) hE.le
    have h2 : 0 ≤ R.firstTailConstant τ N₃ * Real.exp (-R.params.decayRate * R.range / 8) := by positivity
    exact b.trans (h1.trans (le_add_of_nonneg_right h2))
  · have hne : s.support.Nonempty := Finset.nonempty_iff_ne_empty.mpr he
    have p : s.NearFreePair τ (R.params.threshold / 64) (R.params.threshold / 4) W c X :=
      { norm_exp_sub_one_le := hstep
        θ_pos := by positivity
        θ_lt := hθ
        isNear := hg
        mem_free := hc
        areUnitVectors := hu
        commuting := hcomm
        supDist_le := fun l => by
          fin_cases l
          · simp [_root_.YangMills.Construction.TorusFields.supDist_self]
          · simp [hcc, _root_.YangMills.Construction.TorusFields.supDist_self]
        support_nonempty := hne }
    have hr0 : (0 : ℝ) ≤ (R.range : ℝ) := by positivity
    have hw : 0 ≤ R.params.decayRate * (R.range : ℝ) / 4 / 2 := by positivity
    have b := p.abs_firstDeriv_le h hA hx hδ
      (t := τ * Real.exp (-(R.params.decayRate * (R.range : ℝ) / 4 / 2))) (by positivity)
      (mul_exp_neg_le_self hτ hw)
    exact bound_first hτ rfl b
end YangMills.Construction.StepSettings
end
