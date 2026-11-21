import YangMills.Construction.ClusterExpansionOfAStep.AdmissionReadsVOnItsHullProof
import YangMills.Construction.ClusterExpansionOfAStep.MeanOfTheGainProof
import YangMills.Construction.ClusterExpansionOfAStep.NearPotentialAgainstTheCost
import YangMills.Construction.ClusterExpansionOfAStep.OffNearDensitiesMoveLittle
import YangMills.Construction.ClusterExpansionOfAStep.SizeOfJOfASettingForm
import YangMills.Construction.ClusterExpansionOfAStep.ThreeFactsOfAnExpansion
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.ClusterExpansionOfAStep
open BlockAverages ColdStepAtMirrorFrames TorusFields TorusLumps StepSettings RenormalizationStepParameters BlockOffsets
namespace NearPotentialBound
variable {R : StepSetup} {n : ℕ} [NeZero n]
theorem two_mul_supDist_le {N : ℕ} [NeZero N] (x y : TorusSite N) : 2 * supDist x y ≤ N := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.HullLocality.two_mul_supDist_le <;> assumption
theorem supDist_add_siteOfInt_le_of_inBox {N : ℕ} [NeZero N] (y : TorusSite N) (h : Fin 4 → ℤ) (m : ℕ)
    (hm : OffsetInBox m h) : supDist y (y + siteOfInt h) ≤ m := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.HullLocality.supDist_add_le_of_inBox <;> assumption
theorem coordNorm_eq_norm (v : EuclideanSpace ℝ (Fin 3)) : coordNorm v = ‖v‖ := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.coordNorm_eq_norm <;> assumption
theorem inBalls_zero (s : ChartSetting R n) (hρ : 0 ≤ R.ballRadius) : s.InBalls 0 := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.GainMean.inBalls_zero <;> assumption
theorem field_apply_of_not_mem_free (s : ChartSetting R n) (η : FreeCoords s.free)
    (x : TorusSite (n * R.params.side)) (i : Fin 4)
    (h : (x, i) ∉ s.free) : s.field η x i = s.fine x i := by
  unfold ChartSetting.field
  rw [dif_neg h]
theorem fieldsAgreeNear_of_close (s : ChartSetting R n) (hs : s.IsAdmissible) (η η' : FreeCoords s.free)
    (y z : TorusSite (n * R.params.side)) (hz : z ∈ s.support) (m : ℕ)
    (hm : m + supDist y z + R.params.side + 1 < 4 * R.range) :
    FieldsAgreeNear (s.field η) (s.field η') y y m := by
  intro b hb
  have hx : ((bondFrom y b).1, (bondFrom y b).2) ∉ s.free := by
    intro hf
    have h1 := hs.far_from_support _ hf z (Finset.mem_union_left _ hz)
    have h2 : supDist (bondFrom y b).1 z ≤ m + supDist y z := by
      have h3 := supDist_add_siteOfInt_le_of_inBox y b.1 m hb.1
      have h4 := supDist_triangle (bondFrom y b).1 y z
      rw [supDist_comm (bondFrom y b).1 y] at h4
      have : (bondFrom y b).1 = y + siteOfInt b.1 := rfl
      rw [this] at h4 ⊢
      omega
    simp only at h1
    omega
  rw [field_apply_of_not_mem_free s η _ _ hx, field_apply_of_not_mem_free s η' _ _ hx]
theorem isBlockTorusSide_fine (hn : R.params.n₀ ≤ n) (hn0 : 0 < n) :
    IsBlockTorusSide R.params (n * R.params.side) :=
  ⟨Dvd.intro_left n rfl, by
    have : R.params.side * R.params.n₀ ≤ R.params.side * n := Nat.mul_le_mul_left _ hn
    linarith [Nat.mul_comm n R.params.side]⟩
theorem abs_siteDensity_sub_le_one (s : ChartSetting R n) (hs : s.IsAdmissible)
    (hfit : R.params.Admissible) (hrow : R.HasExpansions)
    (hn : R.params.n₀ ≤ n) (hr : 4 * (R.params.side + 2) ≤ R.range) (η : FreeCoords s.free)
    (hη : s.InBalls η) (y z : TorusSite (n * R.params.side)) (hz : z ∈ s.support)
    (hy : (supDist y z : ℝ) < (R.range : ℝ) / 4) :
    |R.siteDensity (n * R.params.side) y (s.field η) s.support s.labelling -
      R.siteDensity (n * R.params.side) y (s.field 0) s.support s.labelling| ≤ 1 := by
  have hρ : 0 ≤ R.ballRadius := by
    have := hfit.σ_pos
    unfold StepSetup.ballRadius
    positivity
  have h0 := inBalls_zero s hρ
  by_cases hfree : ∃ b, b ∈ s.free
  · obtain ⟨b, hb⟩ := hfree
    have h1 := hs.far_from_support b hb z (Finset.mem_union_left _ hz)
    have h2 := two_mul_supDist_le b.1 z
    have hy' : 4 * supDist y z < R.range := by
      have : (4 * supDist y z : ℝ) < R.range := by linarith
      exact_mod_cast this
    have hm : 3 * R.range + supDist y z + R.params.side + 1 < 4 * R.range := by omega
    have hside : 2 * (3 * R.range) + 2 < n * R.params.side := by
      linarith
    have hagree : StatesAgreeNear R.params (s.field η) (s.field 0) s.support s.support s.labelling s.labelling
        y y (3 * R.range) :=
      ⟨hside, hside, fieldsAgreeNear_of_close s hs η 0 y z hz _ hm, fun _ _ => Iff.rfl,
        fun _ _ _ _ _ => rfl, fun _ i => by simp⟩
    have hb' := isBlockTorusSide_fine (R := R) hn (Nat.pos_of_ne_zero (NeZero.ne n))
    have hf := hrow.2.forget (n * R.params.side) (n * R.params.side) hb' hb' (s.field η) (s.field 0)
      s.support s.support s.labelling s.labelling
      y y (3 * R.range) (hs.isHull η hη) (hs.isHull 0 h0) (hs.factor_ne_zero η hη) (hs.factor_ne_zero 0 h0)
      (by
        have : (0 : ℝ) ≤ clusterRange R.coupling := by positivity
        show (clusterRange R.coupling : ℝ) / 64 ≤ ((3 * clusterRange R.coupling : ℕ) : ℝ)
        push_cast
        linarith) hagree
    refine hf.trans (Real.exp_le_one_iff.mpr ?_)
    have : 0 ≤ R.params.decayRate := by
      have := hfit.rt_pos
      unfold StepParameters.decayRate
      positivity
    nlinarith
  · push Not at hfree
    have : s.field η = s.field 0 := by
      funext x i
      rw [field_apply_of_not_mem_free s η x i (hfree _), field_apply_of_not_mem_free s 0 x i (hfree _)]
    rw [this]
    simp
theorem sum_sum_sitesInBlocks_singleton {L : ℕ} [NeZero L] (N : Finset (TorusSite n))
    (g : TorusSite (n * L) → ℝ) :
    ∑ Y ∈ N, ∑ y ∈ sitesInBlocks L {Y}, g y = ∑ y ∈ sitesInBlocks L N, g y := by
  classical
  rw [← Finset.sum_fiberwise_of_maps_to (s := sitesInBlocks L N) (t := N) (g := parentBlock L)
    (fun x hx => by simpa [sitesInBlocks] using hx)]
  refine Finset.sum_congr rfl fun Y hY => ?_
  refine Finset.sum_congr ?_ fun _ _ => rfl
  ext x
  simp only [sitesInBlocks, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
  constructor
  · intro h
    exact ⟨h ▸ hY, h⟩
  · exact fun h => h.2
theorem sum_blockDensity_le (s : ChartSetting R n) (hs : s.IsAdmissible) (hfit : R.params.Admissible)
    (hrow : R.HasExpansions)
    (hn : R.params.n₀ ≤ n) (hr : 4 * (R.params.side + 2) ≤ R.range) (hx : 0 < R.coupling)
    (hfl : 4 * R.params.n₀ + 2 ^ 16 ≤ R.range) (h3 : ExpansionBasicBounds)
    (N : Finset (TorusSite n)) (Yk : Finset (TorusSite (n * R.params.side))) (hYk : Yk ⊆ s.support)
    (hA : nearSites R.range Yk ⊆ sitesInBlocks R.params.side N)
    (hfar : ∀ z ∈ s.support \ Yk, ∀ y ∈ sitesInBlocks R.params.side N, (R.range : ℝ) / 4 ≤ supDist y z)
    (η : FreeCoords s.free) (hη : s.InBalls η) :
    ∑ Y ∈ N, s.blockDensity (s.field η) Y ≤
      ∑ y ∈ nearSites R.range Yk, R.siteDensity (n * R.params.side) y (s.field 0) s.support s.labelling +
        (1 + 2 * R.params.E) * (R.params.side : ℝ) ^ 4 * (N.card : ℝ) := by
  classical
  have hb' := isBlockTorusSide_fine (R := R) hn (Nat.pos_of_ne_zero (NeZero.ne n))
  have hodd := hfit.L_odd
  set f : TorusSite (n * R.params.side) → ℝ :=
    fun y => R.siteDensity (n * R.params.side) y (s.field η) s.support s.labelling with hf
  have hsum : ∑ Y ∈ N, s.blockDensity (s.field η) Y = ∑ y ∈ sitesInBlocks R.params.side N, f y :=
    sum_sum_sitesInBlocks_singleton N f
  have hcard : ((sitesInBlocks R.params.side N).card : ℝ) = (R.params.side : ℝ) ^ 4 * (N.card : ℝ) := by
    have h1 := sum_sum_sitesInBlocks_singleton (L := R.params.side) N (fun _ => (1 : ℝ))
    simp only [Finset.sum_const, nsmul_eq_mul, mul_one] at h1
    rw [← h1]
    have h2 : ∀ Y ∈ N, ((sitesInBlocks R.params.side {Y}).card : ℝ) = (R.params.side : ℝ) ^ 4 :=
      fun Y _ => by
        have := sum_sitesInBlocks (L := R.params.side) hodd Y (fun _ => (1 : ℝ))
        simp only [Finset.sum_const, nsmul_eq_mul, mul_one] at this
        rw [this, card_centredCube hodd]
        push_cast
        ring
    rw [Finset.sum_congr rfl h2]
    simp [mul_comm]
  have hE := hfit.E_ge
  have hnearBound : ∑ y ∈ nearSites R.range Yk, f y ≤
      ∑ y ∈ nearSites R.range Yk,
        (R.siteDensity (n * R.params.side) y (s.field 0) s.support s.labelling + 1) := by
    refine Finset.sum_le_sum fun y hy => ?_
    obtain ⟨z, hz, hyz⟩ : ∃ z ∈ Yk, (supDist y z : ℝ) < (R.range : ℝ) / 4 := by
      simpa [nearSites] using hy
    have := abs_siteDensity_sub_le_one s hs hfit hrow hn hr η hη y z (hYk hz) hyz
    have := (abs_le.mp this).2
    simp only [hf]
    linarith
  have hfarBound : ∑ y ∈ sitesInBlocks R.params.side N \ nearSites R.range Yk, f y ≤
      ∑ _y ∈ sitesInBlocks R.params.side N \ nearSites R.range Yk, 2 * R.params.E := by
    refine Finset.sum_le_sum fun y hy => ?_
    obtain ⟨hyN, hyA⟩ := Finset.mem_sdiff.mp hy
    have hfacts := h3 R.params R.depth R.coupling R.functional R.density R.labels R.labelWeight
      R.clusterFactor R.siteDensity hfit hE hx
      (by
        have h4 : 4 * R.params.n₀ + 2 ^ 16 ≤ R.range := hfl
        exact h4) hrow.1 hrow.2
    have := hfacts.2.1 (n * R.params.side) hb' (s.field η) s.support s.labelling y (hs.isHull η hη)
      (hs.factor_ne_zero η hη)
      (fun z hz => by
        by_cases hzk : z ∈ Yk
        · by_contra hlt
          push Not at hlt
          exact hyA (by
            simp only [nearSites, Finset.mem_filter, Finset.mem_univ, true_and]
            exact ⟨z, hzk, hlt⟩)
        · exact hfar z (Finset.mem_sdiff.mpr ⟨hz, hzk⟩) y hyN)
    exact (abs_le.mp this).2
  have hsplit := Finset.sum_sdiff (f := f) hA
  have hcards : ((sitesInBlocks R.params.side N \ nearSites R.range Yk).card : ℝ) +
      ((nearSites R.range Yk).card : ℝ) = ((sitesInBlocks R.params.side N).card : ℝ) := by
    exact_mod_cast Finset.card_sdiff_add_card_eq_card hA
  rw [hsum, ← hsplit]
  simp only [Finset.sum_const, nsmul_eq_mul, Finset.sum_add_distrib, mul_one] at hfarBound hnearBound
  have hfin : (1 + 2 * R.params.E) * (R.params.side : ℝ) ^ 4 * (N.card : ℝ) =
      (1 + 2 * R.params.E) * (((sitesInBlocks R.params.side N \ nearSites R.range Yk).card : ℝ) +
        ((nearSites R.range Yk).card : ℝ)) := by
    rw [hcards, hcard]
    ring
  rw [hfin]
  nlinarith
theorem neg_localPotential_eq (s : ChartSetting R n) (N : Finset (TorusSite n)) (η : FreeCoords s.free) :
    -(s.localPotential N fun b => η b.1) =
      -(R.coupling * s.energyNear N η) +
      ∑ Y ∈ N, s.blockDensity (s.field (s.extendByZero N fun b => η b.1)) Y +
      (∑ Y ∈ Finset.univ \ N, (s.blockDensity (s.field (s.extendByZero N fun b => η b.1)) Y -
        s.blockDensity (s.field 0) Y)) +
      ∑ Y ∈ N, s.logJacobian (s.field (s.extendByZero N fun b => η b.1)) (s.extendByZero N fun b => η b.1) Y +
      ∑ Y ∈ Finset.univ \ N, (s.logJacobian (s.field (s.extendByZero N fun b => η b.1))
        (s.extendByZero N fun b => η b.1) Y - s.logJacobian (s.field 0) 0 Y) := by
  classical
  unfold ChartSetting.localPotential ChartSetting.farEnergy ChartSetting.energyNear ChartSetting.potential
    ChartSetting.blockCostAt
  have hs : ∀ f : TorusSite n → ℝ, ∑ Y, f Y = ∑ Y ∈ Finset.univ \ N, f Y + ∑ Y ∈ N, f Y := fun f =>
    (Finset.sum_sdiff (Finset.subset_univ N)).symm
  rw [hs]
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, mul_add, mul_sub]
  ring
theorem le_clusterRange_of_pow_le {x : ℝ} (A : ℕ) (hx : (A : ℝ) ^ 100 ≤ x) : A ≤ clusterRange x := by
  have hA : (0 : ℝ) ≤ (A : ℝ) := by positivity
  have h1 : (A : ℝ) ≤ x ^ ((1 : ℝ) / 100) := by
    calc (A : ℝ) = ((A : ℝ) ^ (100 : ℕ)) ^ ((1 : ℝ) / 100) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul hA]
          norm_num
      _ ≤ x ^ ((1 : ℝ) / 100) := Real.rpow_le_rpow (by positivity) hx (by norm_num)
  have h2 : x ^ ((1 : ℝ) / 100) ≤ (clusterRange x : ℝ) := Nat.le_ceil _
  exact_mod_cast h1.trans h2
end NearPotentialBound
open NearPotentialBound in
theorem nearPotentialLeEnergy_of_bounds (h₁ : farBlockDensityVariationBound)
    (h₂ : LogJacobianLeLog) (h₃ : ExpansionBasicBounds) :
    NearPotentialLeEnergy := by
  intro T hT
  obtain ⟨C1, y1, hC1, H1⟩ := h₁ T hT
  obtain ⟨C2, y2, hC2, H2⟩ := h₂ T hT
  have hEpos : 0 ≤ T.E := by
    have := hT.B_ge
    unfold ParameterAssignment.E
    linarith
  refine ⟨C1 + C2 + (T.side : ℝ) ^ 4 * (1 + 2 * T.E), max (max y1 y2)
      (max T.floorMin (max 3 (((4 * T.n₀ + 2 ^ 16 + 4 * (T.side + 2) : ℕ) : ℝ) ^ 100))), by positivity, ?_⟩
  intro y hy R hR n _ hn s c hs hc K hK Yk hYk hYkK hfar η hη
  have hy1 : y1 ≤ y := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hy
  have hy2 : y2 ≤ y := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hy
  have hy3 : T.floorMin ≤ y := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hy
  have hy4 : (3 : ℝ) ≤ y :=
    le_trans (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_max_right _ _)) hy
  have hy5 : ((4 * T.n₀ + 2 ^ 16 + 4 * (T.side + 2) : ℕ) : ℝ) ^ 100 ≤ y :=
    le_trans (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) (le_max_right _ _)) hy
  have hrow := hR.isStep.1
  have hlet := hR.params_eq
  have hfit : R.params.Admissible := hlet ▸ hT.fits y hy3
  have hxy := hR.le_coupling
  have hx3 : (3 : ℝ) ≤ R.coupling := hy4.trans hxy
  have hLe : R.params.side = T.side := by rw [hlet]; rfl
  have hEe : R.params.E = T.E := by rw [hlet]; rfl
  have hne : T.n₀ = R.params.n₀ := by rw [hlet]; rfl
  have hbig : 4 * T.n₀ + 2 ^ 16 + 4 * (T.side + 2) ≤ R.range := le_clusterRange_of_pow_le _ (hy5.trans hxy)
  have hr : 4 * (R.params.side + 2) ≤ R.range := by
    rw [hLe]
    omega
  have hfl : 4 * R.params.n₀ + 2 ^ 16 ≤ R.range := by
    rw [← hne]
    omega
  have hrpos : (1 : ℝ) ≤ (R.range : ℝ) := by
    have : 1 ≤ R.range := by omega
    exact_mod_cast this
  have hlog : 1 ≤ Real.log R.coupling := by
    rw [Real.le_log_iff_exp_le (by linarith)]
    have := Real.exp_one_lt_d9
    linarith
  set N := blocksNear R.params.side R.range (K.biUnion id) with hN
  set ζ : s.freeNear N → EuclideanSpace ℝ (Fin 3) := fun b => η b.1 with hζ
  have hρ : 0 ≤ R.ballRadius := by
    have := hfit.σ_pos
    unfold StepSetup.ballRadius
    positivity
  have hin : s.InBalls (s.extendByZero N ζ) := by
    intro b
    unfold ChartSetting.extendByZero
    by_cases hb : b ∈ s.freeNear N
    · simp only [hb, dite_true]
      exact hη b
    · simp only [hb, dite_false]
      rw [coordNorm_eq_norm]
      simpa using hρ
  have hoff := H1 y hy1 R hR n hn s c hs hc K hK ζ hin
  have hA : nearSites R.range Yk ⊆ sitesInBlocks R.params.side N := by
    classical
    intro z hz
    obtain ⟨u, hu, hzu⟩ : ∃ u ∈ Yk, (supDist z u : ℝ) < (R.range : ℝ) / 4 := by
      simpa [nearSites] using hz
    simp only [sitesInBlocks, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [hN]
    unfold blocksNear
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨z, Finset.mem_inter.mpr ⟨?_, (mem_thickening _ _ _).mpr ⟨u, hYkK hu, ?_⟩⟩⟩
    · simp [sitesInBlocks]
    · have h1 : (supDist z u : ℝ) ≤ ((5 * R.range : ℕ) : ℝ) := by
        push_cast
        have : (0 : ℝ) ≤ (R.range : ℝ) := by positivity
        linarith
      exact_mod_cast h1
  have hphi := sum_blockDensity_le s hs hfit hrow (by omega) hr (by linarith) hfl h₃ N Yk hYk hA hfar _ hin
  have hj : ∑ Y ∈ N, s.logJacobian (s.field (s.extendByZero N ζ)) (s.extendByZero N ζ) Y ≤
      C2 * Real.log R.coupling * (N.card : ℝ) := by
    calc _ ≤ ∑ _Y ∈ N, C2 * Real.log R.coupling := Finset.sum_le_sum fun Y _ =>
          (abs_le.mp (H2 y hy2 R hR n hn s hs _ hin Y)).2
      _ = _ := by simp [Finset.sum_const, mul_comm]
  have hd1 : ∑ Y ∈ Finset.univ \ N,
      (s.blockDensity (s.field (s.extendByZero N ζ)) Y - s.blockDensity (s.field 0) Y) ≤
      ∑ Y ∈ Finset.univ \ N, |s.blockDensity (s.field (s.extendByZero N ζ)) Y - s.blockDensity (s.field 0) Y| :=
    Finset.sum_le_sum fun _ _ => le_abs_self _
  have hd2 : ∑ Y ∈ Finset.univ \ N, (s.logJacobian (s.field (s.extendByZero N ζ)) (s.extendByZero N ζ) Y -
      s.logJacobian (s.field 0) 0 Y) ≤
      ∑ Y ∈ Finset.univ \ N, |s.logJacobian (s.field (s.extendByZero N ζ)) (s.extendByZero N ζ) Y -
        s.logJacobian (s.field 0) 0 Y| :=
    Finset.sum_le_sum fun _ _ => le_abs_self _
  rw [neg_localPotential_eq s N η]
  have hLr : (R.params.side : ℝ) = T.side := by rw [hLe]
  have hEr : R.params.E = T.E := hEe
  rw [hLr, hEr] at hphi
  have hcard : (0 : ℝ) ≤ (N.card : ℝ) := by positivity
  have hr4 : (1 : ℝ) ≤ (R.range : ℝ) ^ 4 := one_le_pow₀ hrpos
  have hclasscost : (1 : ℝ) ≤ (R.range : ℝ) ^ 4 * Real.log R.coupling := by nlinarith
  have hlogb : Real.log R.coupling ≤ (R.range : ℝ) ^ 4 * Real.log R.coupling := by nlinarith
  have e1 : (T.side : ℝ) ^ 4 * (1 + 2 * T.E) * (N.card : ℝ) ≤
      (T.side : ℝ) ^ 4 * (1 + 2 * T.E) * ((R.range : ℝ) ^ 4 * Real.log R.coupling) * (N.card : ℝ) := by
    have : (0 : ℝ) ≤ (T.side : ℝ) ^ 4 * (1 + 2 * T.E) := by positivity
    have h2 : (T.side : ℝ) ^ 4 * (1 + 2 * T.E) * 1 ≤
        (T.side : ℝ) ^ 4 * (1 + 2 * T.E) * ((R.range : ℝ) ^ 4 * Real.log R.coupling) :=
      mul_le_mul_of_nonneg_left hclasscost this
    nlinarith
  have e2 : C2 * Real.log R.coupling * (N.card : ℝ) ≤
      C2 * ((R.range : ℝ) ^ 4 * Real.log R.coupling) * (N.card : ℝ) := by
    have h2 : C2 * Real.log R.coupling ≤ C2 * ((R.range : ℝ) ^ 4 * Real.log R.coupling) :=
      mul_le_mul_of_nonneg_left hlogb hC2.le
    nlinarith
  have hζrfl : (fun b : s.freeNear N => η b.1) = ζ := rfl
  simp only [hζrfl] at *
  nlinarith
end YangMills.Construction.ClusterExpansionOfAStep
