import YangMills.Construction.ClusterExpansionOfAStep.AllowedStatesReadTheirBoxProof
import YangMills.Construction.ClusterExpansionOfAStep.DeepDensitiesAgainstTheCutProof
import Mathlib
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
open MeasureTheory Set
namespace YangMills.Construction.ClusterExpansionOfAStep
open BlockAverages TorusFields TorusLumps StepSettings RenormalizationStepParameters BlockOffsets StepCosts ColdStepAtMirrorFrames
  Interpolation StepLocality StepFloors FrameLocality
section Extension
variable {R : StepSetup} {n n' : ℕ} [NeZero n] [NeZero n']
theorem isNearIndex_mono {L k m : ℕ} {q : NearBondIndex} (hq : IsNearIndex L k q) (h : k ≤ m) :
    IsNearIndex L m q :=
  ⟨fun i => (hq.1 i).trans (by exact_mod_cast h), hq.2⟩
theorem nearBond_injective_of_near (hodd : Odd R.params.side) {Y : TorusSite n} {k : ℕ} (hk : 2 * k + 2 < n)
    {q q' : NearBondIndex} (hq : IsNearIndex R.params.side k q) (hq' : IsNearIndex R.params.side k q')
    (e : nearBond R.params.side Y q = nearBond R.params.side Y q') : q = q' := by exact _root_.YangMills.Construction.ClusterExpansionOfAStep.DeepCutoff.nearBond_inj_of_isNearIndex (R := R) (n := n) (Y := Y) hodd hk hq hq' e
open Classical in
def _root_.YangMills.Construction.StepSettings.ChartSetting.extendByIndex (s : ChartSetting R n)
    (Y : TorusSite n) (k : ℕ) (z : NearBondIndex → EuclideanSpace ℝ (Fin 3)) : FreeCoords s.free :=
  fun b => if h : ∃ q, IsNearIndex R.params.side k q ∧ nearBond R.params.side Y q = b.1 then z h.choose else 0
theorem extendByIndex_apply_near (hodd : Odd R.params.side) (s : ChartSetting R n) {Y : TorusSite n} {k : ℕ}
    (hk : 2 * k + 2 < n) (z : NearBondIndex → EuclideanSpace ℝ (Fin 3)) {q : NearBondIndex}
    (hq : IsNearIndex R.params.side k q) (h : nearBond R.params.side Y q ∈ s.free) :
    s.extendByIndex Y k z ⟨_, h⟩ = z q := by
  classical
  have hex : ∃ q', IsNearIndex R.params.side k q' ∧ nearBond R.params.side Y q' = (⟨_, h⟩ : s.free).1 :=
    ⟨q, hq, rfl⟩
  unfold ChartSetting.extendByIndex
  rw [dif_pos hex]
  rw [nearBond_injective_of_near hodd hk hex.choose_spec.1 hq hex.choose_spec.2]
theorem coordsAgreeNear_extendByIndex (hodd : Odd R.params.side) {s : ChartSetting R n} {s' : ChartSetting R n'}
    {Y : TorusSite n} {Y' : TorusSite n'} {m k : ℕ} (hag : SettingsAgreeNear s s' Y Y' m) (hkm : k ≤ m)
    (η' : FreeCoords s'.free) :
    CoordsAgreeNear s s' Y Y' k (s.extendByIndex Y k (s'.coordsByIndex Y' η')) η' := by
  classical
  have hk : 2 * k + 2 < n := by have := hag.lt_extent; omega
  intro q hq
  by_cases h : nearBond R.params.side Y q ∈ s.free
  · have e : s.coordsByIndex Y (s.extendByIndex Y k (s'.coordsByIndex Y' η')) q =
        s.extendByIndex Y k (s'.coordsByIndex Y' η') ⟨_, h⟩ := dif_pos h
    rw [e, extendByIndex_apply_near hodd s hk _ hq h]
  · have h' : nearBond R.params.side Y' q ∉ s'.free :=
      fun hh => h ((hag.free_iff q (isNearIndex_mono hq hkm)).mpr hh)
    have e : s.coordsByIndex Y (s.extendByIndex Y k (s'.coordsByIndex Y' η')) q = 0 := dif_neg h
    have e' : s'.coordsByIndex Y' η' q = 0 := dif_neg h'
    rw [e, e']
theorem settingsAgreeNear_self {s : ChartSetting R n} {s' : ChartSetting R n'} {Y : TorusSite n}
    {Y' : TorusSite n'} {m : ℕ} (hag : SettingsAgreeNear s s' Y Y' m) : SettingsAgreeNear s s Y Y m :=
  ⟨hag.lt_extent, hag.lt_extent, fun _ _ => rfl, fun _ _ => Iff.rfl, fun _ _ _ => rfl, fun _ _ _ => rfl,
    fun _ _ _ _ => Iff.rfl, fun _ _ _ _ _ _ => rfl, fun h hh => by
      obtain ⟨o, ho, e, _⟩ := hag.bases_match h hh
      exact ⟨o, ho, e, e⟩⟩
theorem coordNorm_zero : coordNorm 0 = 0 := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.DeepCutoff.coordNorm_zero <;> assumption
theorem inBalls_extendByIndex (s : ChartSetting R n) (Y : TorusSite n) (k : ℕ)
    {z : NearBondIndex → EuclideanSpace ℝ (Fin 3)} (hρ : 0 ≤ R.ballRadius) (hz : CoordsInBalls R z) :
    s.InBalls (s.extendByIndex Y k z) := by
  classical
  intro b
  unfold ChartSetting.extendByIndex
  by_cases h : ∃ q, IsNearIndex R.params.side k q ∧ nearBond R.params.side Y q = b.1
  · rw [dif_pos h]
    exact hz _
  · rw [dif_neg h, coordNorm_zero]
    exact hρ
theorem extendByIndex_mem_openBallsIn (s : ChartSetting R n) (Y : TorusSite n) (k : ℕ)
    {z : NearBondIndex → EuclideanSpace ℝ (Fin 3)} (hρ : 0 < R.ballRadius)
    (hz : ∀ q, coordNorm (z q) < R.ballRadius) : s.extendByIndex Y k z ∈ openBallsIn R s.free := by
  classical
  intro b
  unfold ChartSetting.extendByIndex
  by_cases h : ∃ q, IsNearIndex R.params.side k q ∧ nearBond R.params.side Y q = b.1
  · rw [dif_pos h]
    exact hz _
  · rw [dif_neg h, coordNorm_zero]
    exact hρ
theorem coordsInBalls_coordsByIndex (s : ChartSetting R n) (Y : TorusSite n) {η : FreeCoords s.free}
    (hρ : 0 ≤ R.ballRadius) (hη : s.InBalls η) : CoordsInBalls R (s.coordsByIndex Y η) := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.DeepCutoff.coordsByIndex_inBalls <;> assumption
theorem coordNorm_coordsByIndex_lt (s : ChartSetting R n) (Y : TorusSite n) {η : FreeCoords s.free}
    (hρ : 0 < R.ballRadius) (hη : η ∈ openBallsIn R s.free) (q : NearBondIndex) :
    coordNorm (s.coordsByIndex Y η q) < R.ballRadius := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.DeepCutoff.coordNorm_coordsByIndex_lt <;> assumption
theorem measurable_coordsByIndex (s : ChartSetting R n) (Y : TorusSite n) : Measurable (s.coordsByIndex Y) := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.DeepCutoff.measurable_coordsByIndex <;> assumption
theorem measurable_extendByIndex (s : ChartSetting R n) (Y : TorusSite n) (k : ℕ) :
    Measurable (s.extendByIndex Y k) := by
  classical
  refine measurable_pi_iff.mpr fun b => ?_
  unfold ChartSetting.extendByIndex
  by_cases h : ∃ q, IsNearIndex R.params.side k q ∧ nearBond R.params.side Y q = b.1
  · simp only [dif_pos h]
    exact measurable_pi_apply _
  · simp only [dif_neg h]
    exact measurable_const
theorem extendByIndex_congr (s : ChartSetting R n) (Y : TorusSite n) {k m : ℕ} (hkm : k ≤ m)
    {z z' : NearBondIndex → EuclideanSpace ℝ (Fin 3)} (h : ∀ q, IsNearIndex R.params.side m q → z q = z' q) :
    s.extendByIndex Y k z = s.extendByIndex Y k z' := by
  classical
  funext b
  unfold ChartSetting.extendByIndex
  by_cases he : ∃ q, IsNearIndex R.params.side k q ∧ nearBond R.params.side Y q = b.1
  · rw [dif_pos he, dif_pos he]
    exact h _ (isNearIndex_mono he.choose_spec.1 hkm)
  · rw [dif_neg he, dif_neg he]
end Extension
section Laws
variable {R : StepSetup} {n : ℕ} [NeZero n] {free : Finset (TorusBond (n * R.params.side))}
theorem weightedMean_interpolatedDensity_eq_lawDensity (s : ChartSetting R n) (hreg : s.densitySplit.IsRegular)
    (lam τ : ℝ) (G : FreeCoords s.free → ℝ) :
    weightedMean (s.interpolatedDensity lam τ) G = weightedMean (s.lawDensity fun η => τ * s.partPotential 0 η +
      (1 - τ) * s.restrictedPotential lam 0 ∅ (s.partPotential 0) η) G := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.DeepCutoff.weightedMean_interpolatedDensity_eq_lawDensity <;> assumption
theorem weightedMean_perturbedDensity_eq_lawDensity (s : ChartSetting R n) (hreg : s.densitySplit.IsRegular)
    (ν : ℝ) (G : FreeCoords s.free → ℝ) :
    weightedMean (s.perturbedDensity ν) G = weightedMean (s.lawDensity (s.partPotential ν)) G := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.DeepCutoff.weightedMean_perturbedDensity_eq_lawDensity <;> assumption
theorem abs_sub_weightedMean_interpolatedDensity_le (hcore : LogIntegralExpInterpolationStatement)
    (hρ : 0 < R.ballRadius) (hp : IsCutoff R.ballRadius R.barrierFn)
    {D : BlockDensitySplit R n free} (hreg : D.IsRegular) (lam τ : ℝ) {G H : FreeCoords free → ℝ} {ε : ℝ}
    (hG : AEBounded (volume.restrict (openBallsIn R free)) G)
    (hH : AEBounded (volume.restrict (openBallsIn R free)) H)
    (hc : ∀ η ∈ openBallsIn R free, |G η - H η| ≤ ε) :
    |weightedMean (D.interpolatedDensity lam τ) G - weightedMean (D.interpolatedDensity lam τ) H| ≤ ε := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.DeepCutoff.abs_weightedMean_interpolatedDensity_sub_le <;> assumption
theorem abs_sub_weightedMean_perturbedDensity_le (hcore : LogIntegralExpInterpolationStatement)
    (hρ : 0 < R.ballRadius) (hp : IsCutoff R.ballRadius R.barrierFn)
    {D : BlockDensitySplit R n free} (hreg : D.IsRegular) (ν : ℝ) {G H : FreeCoords free → ℝ} {ε : ℝ}
    (hG : AEBounded (volume.restrict (openBallsIn R free)) G)
    (hH : AEBounded (volume.restrict (openBallsIn R free)) H)
    (hc : ∀ η ∈ openBallsIn R free, |G η - H η| ≤ ε) :
    |weightedMean (D.perturbedDensity ν) G - weightedMean (D.perturbedDensity ν) H| ≤ ε := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.DeepCutoff.abs_weightedMean_perturbedDensity_sub_le <;> assumption
end Laws
section Main
theorem cellOffset_torusFrame {L n : ℕ} [NeZero L] [NeZero n] (t : ℕ) (hodd : Odd L) (A o : Fin 4 → ℤ)
    (ho : o ∈ centredCube L) :
    cellOffset (F := torusFrame L t n)
      (torusSiteInFrame (torusFrame L t n) (torusFrame L t n).depth
        (siteOfInt (blockPoint L A o) : TorusSite (n * L))) = o := by apply _root_.YangMills.Construction.InBoxTransfer.cellOffset_torusFrame <;> assumption
theorem density_locality_arith {rt δ L k m x K₀ Cψ E W W₂ f c r C₀ : ℝ} (hrt : 0 < rt) (hrtδ : rt ≤ δ)
    (hδ : 0 < δ) (hL : (2 : ℝ) ^ 15 ≤ L) (hk : 4 ≤ k) (hm : 0 ≤ m) (hm16 : m ≤ 16 * k) (hWR : L * k / 2 ≤ W)
    (hW₂ : W₂ = L * k - 2 * L) (hf : f = rt / 2 ^ 12) (hx1 : 1 ≤ x) (hK₀ : 0 ≤ K₀) (hCψ : 0 ≤ Cψ) (hE : 0 ≤ E)
    (hKC : K₀ + 4 * Cψ + 2 * L ^ 4 + L ^ 4 * (4 * E + 2) ≤ C₀) (hC₁ : 1 ≤ C₀)
    (hy7 : C₀ * x ^ C₀ * Real.exp (-(c * r)) ≤ Real.exp (-(x ^ (1 / 200 : ℝ))))
    (hc : c = 3 * rt / (128 * L)) (hr : r ≤ 4 * L * m) :
    x * (K₀ * Real.exp (-δ * W)) + (2 * (Cψ * Real.exp (-(4 * rt * k))) +
      2 * (Cψ * x) * Real.exp (-(rt * m / 2 ^ 3))) +
      (2 * (L ^ 4 * Real.exp (-f * W₂)) + L ^ 4 * (4 * E + 2) * Real.exp (-(rt * m / 2 ^ 3))) ≤
      Real.exp (-(rt * m / 2 ^ 5)) := by
  have hx : 0 < x := by linarith
  have hk0 : 0 ≤ k := by linarith
  set E₁ : ℝ := Real.exp (-(rt * m / 2 ^ 3)) with hE₁
  have hE₁pos : 0 < E₁ := Real.exp_pos _
  have hrt8 : rt * m / 2 ^ 3 ≤ rt * (2 * k) := by
    have : m / 8 ≤ 2 * k := by linarith
    calc rt * m / 2 ^ 3 = rt * (m / 8) := by ring
      _ ≤ rt * (2 * k) := mul_le_mul_of_nonneg_left this hrt.le
  have hLk : 2 ^ 15 * k ≤ L * k := mul_le_mul_of_nonneg_right hL hk0
  have B1 : Real.exp (-δ * W) ≤ E₁ := by
    apply Real.exp_le_exp.mpr
    have h1 : rt * (2 * k) ≤ δ * (2 * k) := mul_le_mul_of_nonneg_right hrtδ (by positivity)
    have h2 : 2 * k ≤ W := by linarith
    have h3 : δ * (2 * k) ≤ δ * W := mul_le_mul_of_nonneg_left h2 hδ.le
    linarith
  have B2 : Real.exp (-(4 * rt * k)) ≤ E₁ := by
    apply Real.exp_le_exp.mpr
    have : rt * (2 * k) ≤ 4 * rt * k := by nlinarith
    linarith
  have B3 : Real.exp (-f * W₂) ≤ E₁ := by
    apply Real.exp_le_exp.mpr
    rw [hW₂, hf]
    have h0 : L ≤ L * k / 4 := by nlinarith
    have h1 : 2 ^ 13 * (2 * k) ≤ L * k - 2 * L := by nlinarith
    have h2 : rt / 2 ^ 12 * (2 ^ 13 * (2 * k)) ≤ rt / 2 ^ 12 * (L * k - 2 * L) :=
      mul_le_mul_of_nonneg_left h1 (by positivity)
    have h3 : rt * (2 * k) ≤ rt / 2 ^ 12 * (2 ^ 13 * (2 * k)) := by
      have e : rt / 2 ^ 12 * (2 ^ 13 * (2 * k)) = 2 * (rt * (2 * k)) := by ring
      have : 0 ≤ rt * (2 * k) := by positivity
      linarith
    linarith
  have t1 : x * (K₀ * Real.exp (-δ * W)) ≤ K₀ * x * E₁ := by
    have := mul_le_mul_of_nonneg_left B1 (mul_nonneg hK₀ hx.le)
    calc x * (K₀ * Real.exp (-δ * W)) = K₀ * x * Real.exp (-δ * W) := by ring
      _ ≤ _ := this
  have t2 : 2 * (Cψ * Real.exp (-(4 * rt * k))) ≤ 2 * Cψ * x * E₁ := by
    have h1 := mul_le_mul_of_nonneg_left B2 (by positivity : (0 : ℝ) ≤ 2 * Cψ)
    have h2 : 2 * Cψ * E₁ ≤ 2 * Cψ * x * E₁ := by
      have : (0 : ℝ) ≤ 2 * Cψ * E₁ := by positivity
      nlinarith
    calc 2 * (Cψ * Real.exp (-(4 * rt * k))) = 2 * Cψ * Real.exp (-(4 * rt * k)) := by ring
      _ ≤ _ := h1.trans h2
  have t3 : 2 * (L ^ 4 * Real.exp (-f * W₂)) ≤ 2 * L ^ 4 * x * E₁ := by
    have h1 := mul_le_mul_of_nonneg_left B3 (by positivity : (0 : ℝ) ≤ 2 * L ^ 4)
    have h2 : 2 * L ^ 4 * E₁ ≤ 2 * L ^ 4 * x * E₁ := by
      have : (0 : ℝ) ≤ 2 * L ^ 4 * E₁ := by positivity
      nlinarith
    calc 2 * (L ^ 4 * Real.exp (-f * W₂)) = 2 * L ^ 4 * Real.exp (-f * W₂) := by ring
      _ ≤ _ := h1.trans h2
  have t4 : L ^ 4 * (4 * E + 2) * E₁ ≤ L ^ 4 * (4 * E + 2) * x * E₁ := by
    have : (0 : ℝ) ≤ L ^ 4 * (4 * E + 2) * E₁ := by positivity
    nlinarith
  set Kf := K₀ + 4 * Cψ + 2 * L ^ 4 + L ^ 4 * (4 * E + 2) with hKf
  have hsum : x * (K₀ * Real.exp (-δ * W)) + (2 * (Cψ * Real.exp (-(4 * rt * k))) + 2 * (Cψ * x) * E₁) +
      (2 * (L ^ 4 * Real.exp (-f * W₂)) + L ^ 4 * (4 * E + 2) * E₁) ≤ Kf * x * E₁ := by
    have e : Kf * x * E₁ = K₀ * x * E₁ + 2 * Cψ * x * E₁ + 2 * (Cψ * x) * E₁ +
        2 * L ^ 4 * x * E₁ + L ^ 4 * (4 * E + 2) * x * E₁ := by
      rw [hKf]
      ring
    rw [e]
    linarith
  refine hsum.trans ?_
  have hxC : x ≤ x ^ C₀ := Real.self_le_rpow_of_one_le hx1 hC₁
  have hone : Real.exp (-(x ^ (1 / 200 : ℝ))) ≤ 1 := by
    apply Real.exp_le_one_iff.mpr
    have := Real.rpow_nonneg hx.le (1 / 200 : ℝ)
    linarith
  have hbig : C₀ * x ^ C₀ ≤ Real.exp (c * r) := by
    have h1 := hy7.trans hone
    rw [Real.exp_neg, ← div_eq_mul_inv, div_le_one (Real.exp_pos _)] at h1
    exact h1
  have hC₀pos : 0 < C₀ := by linarith
  have hKx : Kf * x ≤ Real.exp (c * r) := by
    refine le_trans ?_ hbig
    exact mul_le_mul hKC hxC hx.le hC₀pos.le
  have hcr : c * r ≤ 3 / 32 * (rt * m) := by
    have hc0 : 0 ≤ c := by
      rw [hc]
      positivity
    have h1 : c * r ≤ c * (4 * L * m) := mul_le_mul_of_nonneg_left hr hc0
    have e : c * (4 * L * m) = 3 / 32 * (rt * m) := by
      rw [hc]
      field_simp
      ring
    linarith
  calc Kf * x * E₁ ≤ Real.exp (c * r) * E₁ := mul_le_mul_of_nonneg_right hKx hE₁pos.le
    _ = Real.exp (c * r + -(rt * m / 2 ^ 3)) := by rw [Real.exp_add]
    _ ≤ Real.exp (-(rt * m / 2 ^ 5)) := by
        apply Real.exp_le_exp.mpr
        have : 0 ≤ rt * m := by positivity
        linarith
set_option maxHeartbeats 4000000 in
theorem densityLocality_holds (hcore : LogIntegralExpInterpolationStatement)
    (hpsi : blockInteractionLocalityBound) (hstate : BlockDensitiesClose)
    (hosc : BlockDensityOscillationBound) (hsd : BlockDensitiesMeasurableBounded)
    (h3 : LocalMeansClose) (hcost : BlockCostsAgree)
    (hreg : DensitySplitRegular) (hfr : FrameCoordLocal)
    (hfl : EventuallyFloorConditions) : DensityLocality := by
  obtain ⟨r₁, p₁, g₁⟩ := h3
  obtain ⟨r₂, p₂, g₂⟩ := hreg
  obtain ⟨r₃, p₃, g₃⟩ := hpsi
  refine ⟨fun c => min (r₁ c) (min (r₂ c) (r₃ c)), fun c => lt_min (p₁ c) (lt_min (p₂ c) (p₃ c)),
    fun T hD hrt => ?_⟩
  have a₁ : T.rt ≤ r₁ T.toChainParameters := hrt.trans (min_le_left _ _)
  have a₂ : T.rt ≤ r₂ T.toChainParameters := hrt.trans ((min_le_right _ _).trans (min_le_left _ _))
  have a₃ : T.rt ≤ r₃ T.toChainParameters := hrt.trans ((min_le_right _ _).trans (min_le_right _ _))
  obtain ⟨y₁, L3⟩ := g₁ T hD a₁
  obtain ⟨y₂, Rg⟩ := g₂ T hD a₂
  obtain ⟨Cψ, y₃, hCψ, Ps⟩ := g₃ T hD a₃
  have hσ := hD.σ_pos
  have hrtpos := hD.rt_pos
  have hL40 : (2 : ℝ) ^ 40 ≤ T.side := by exact_mod_cast hD.L_ge
  have hL0 : (0 : ℝ) < T.side := by linarith [show (0 : ℝ) < 2 ^ 40 by positivity]
  have hN0 : 0 < T.N 0 := hD.chain.2.2.2.2.2.2.2.1 0
  have hEpos : 1 ≤ T.E := by
    have := hD.B_ge
    unfold ParameterAssignment.E
    linarith
  set K₀ : ℝ := (T.side : ℝ) ^ 4 * T.threshold ^ 2 * T.N 0 with hK₀
  have hK₀pos : 0 < K₀ := by positivity
  set Kf : ℝ := K₀ + 4 * Cψ + 2 * (T.side : ℝ) ^ 4 + (T.side : ℝ) ^ 4 * (4 * T.E + 2) with hKf
  have hKfpos : 0 < Kf := by positivity
  set C₀ : ℝ := Kf + 2 ^ 21 * T.side + 4 * T.n₀ + 2 ^ 17 + 2 with hC₀
  have hC₀pos : 0 < C₀ := by positivity
  have hKC : K₀ + 4 * Cψ + 2 * (T.side : ℝ) ^ 4 + (T.side : ℝ) ^ 4 * (4 * T.E + 2) ≤ C₀ := by
    have h1 : 0 ≤ 2 ^ 21 * (T.side : ℝ) := by positivity
    have h2 : 0 ≤ 4 * (T.n₀ : ℝ) := by positivity
    have h3 : (0 : ℝ) ≤ 2 ^ 17 := by positivity
    linarith
  have hC₁ : 1 ≤ C₀ := by
    have h1 : 0 ≤ 2 ^ 21 * (T.side : ℝ) := by positivity
    have h2 : 0 ≤ 4 * (T.n₀ : ℝ) := by positivity
    have h3 : (2 : ℝ) ^ 17 ≥ 1 := by norm_num
    linarith [hKfpos]
  have hL15 : (2 : ℝ) ^ 15 ≤ T.side := le_trans (by norm_num) hL40
  have hE0 : 0 ≤ T.E := by linarith
  set c₀ : ℝ := 3 * T.rt / (128 * T.side) with hc₀
  have hc₀pos : 0 < c₀ := by positivity
  obtain ⟨yF, hF⟩ := hfl T hD C₀ c₀ hC₀pos hc₀pos
  refine ⟨max (max T.floorMin (max y₁ y₂)) (max (max y₃ yF) 1),
    fun y hy R hR n n' _ _ hn hn' s s' Y Y' m hs hs' => ?_⟩
  have hy0 : T.floorMin ≤ y := (le_max_left _ _).trans ((le_max_left _ _).trans hy)
  have hyL : y₁ ≤ y := (le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_left _ _).trans hy))
  have hyR : y₂ ≤ y := (le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_left _ _).trans hy))
  have hyP : y₃ ≤ y := (le_max_left _ _).trans ((le_max_left _ _).trans ((le_max_right _ _).trans hy))
  have hyF : yF ≤ y := (le_max_right _ _).trans ((le_max_left _ _).trans ((le_max_right _ _).trans hy))
  have hy1 : (1 : ℝ) ≤ y := (le_max_right _ _).trans ((le_max_right _ _).trans hy)
  have hxy := hR.le_coupling
  have hx1 : 1 ≤ R.coupling := hy1.trans hxy
  have hx : 0 < R.coupling := by linarith
  have hfit : R.params.Admissible := hR.params_eq ▸ hD.fits y hy0
  have hodd : Odd R.params.side := hfit.L_odd
  have hLq : R.params.side = T.side := by rw [hR.params_eq]; rfl
  have hσq : R.params.threshold = T.threshold := by rw [hR.params_eq]; rfl
  have hEq : R.params.E = T.E := by rw [hR.params_eq]; rfl
  have hn₀q : R.params.n₀ = T.n₀ := by rw [hR.params_eq]; rfl
  have hrtq : R.params.rt = T.rt := by rw [hR.params_eq]; rfl
  have hρq : R.ballRadius = T.ballRadius := by
    unfold StepSetup.ballRadius ParameterAssignment.ballRadius
    rw [hσq]
  have hρ : 0 < R.ballRadius := by
    rw [hρq]
    unfold ParameterAssignment.ballRadius
    positivity
  have hp : IsCutoff R.ballRadius R.barrierFn := by
    rw [hρq, hR.barrierFn_eq]
    exact hD.cut
  have hFl := hF R.coupling (hyF.trans hxy)
  have hrC : C₀ ≤ R.range := hFl.range_ge
  have hr2 : (2 : ℝ) ^ 21 * T.side ≤ R.range := by
    have h1 : 0 ≤ 4 * (T.n₀ : ℝ) := by positivity
    linarith
  have hrn : 4 * R.params.n₀ + 2 ^ 16 ≤ R.range := by
    have : ((4 * T.n₀ + 2 ^ 16 : ℕ) : ℝ) ≤ R.range := by
      push_cast
      have h2 : 0 ≤ 2 ^ 21 * (T.side : ℝ) := by positivity
      linarith
    rw [hn₀q]
    exact_mod_cast this
  have hrL : R.params.side + 2 ≤ R.range := by
    have : ((T.side + 2 : ℕ) : ℝ) ≤ R.range := by
      push_cast
      nlinarith
    rw [hLq]
    exact_mod_cast this
  have hE1 : 1 ≤ R.params.E := by rw [hEq]; exact hEpos
  have hnq : R.params.n₀ ≤ n := by rw [hn₀q]; exact hn
  have hnq' : R.params.n₀ ≤ n' := by rw [hn₀q]; exact hn'
  have hregs : s.densitySplit.IsRegular := Rg y hyR R hR n hn s hs
  have hregs' : s'.densitySplit.IsRegular := Rg y hyR R hR n' hn' s' hs'
  have key : ∀ m : ℕ, (R.range : ℝ) / (4 * R.params.side) ≤ m → SettingsAgreeNear s s' Y Y' m →
      |s.blockActivity T.lam Y - s'.blockActivity T.lam Y'| ≤ Real.exp (-(T.rt * m / 2 ^ 5)) := by
    intro m hrm hag
    have hLr : (R.params.side : ℝ) = T.side := by exact_mod_cast hLq
    rw [hLr] at hrm
    have hMbig : (2 : ℝ) ^ 19 ≤ m := by
      refine le_trans ?_ hrm
      rw [le_div_iff₀ (by positivity)]
      linarith
    have hmN : 2 ^ 19 ≤ m := by exact_mod_cast hMbig
    obtain ⟨k, hkdef⟩ : ∃ k, k = m / 8 := ⟨_, rfl⟩
    have hk8 : m ≤ 8 * k + 7 := by omega
    have hk4 : 4 ≤ k := by omega
    have hkm : k ≤ m := by omega
    have hkq : k ≤ m / 4 := by omega
    clear hmN
    have hk8R : (m : ℝ) ≤ 8 * k + 7 := by exact_mod_cast hk8
    have hkR : (m : ℝ) / 16 ≤ k := by linarith
    have hrk : (R.range : ℝ) / (2 ^ 8 * T.side) ≤ k := by
      have e : (R.range : ℝ) / (2 ^ 8 * T.side) = (R.range : ℝ) / (4 * T.side) / 2 ^ 6 := by
        field_simp
        ring
      rw [e]
      have h0 : (0 : ℝ) ≤ k := by positivity
      linarith
    have hLk2 : 2 * R.params.side ≤ R.params.side * k := by
      rw [mul_comm 2]
      exact Nat.mul_le_mul_left _ (by omega)
    have hW₂cast : ((R.params.side * k - 2 * R.params.side : ℕ) : ℝ) = T.side * k - 2 * T.side := by
      rw [Nat.cast_sub hLk2, hLq]
      push_cast
      ring
    have hrM : (R.range : ℝ) ≤ 4 * T.side * m := by
      rwa [div_le_iff₀ (by positivity), mul_comm] at hrm
    have hLk : (T.side : ℝ) * ((m : ℝ) - 7) / 8 ≤ T.side * k := by
      have : ((m : ℝ) - 7) / 8 ≤ k := by linarith
      calc (T.side : ℝ) * ((m : ℝ) - 7) / 8 = T.side * (((m : ℝ) - 7) / 8) := by ring
        _ ≤ T.side * k := mul_le_mul_of_nonneg_left this hL0.le
    have hW₂ : (R.range : ℝ) / 64 ≤ ((R.params.side * k - 2 * R.params.side : ℕ) : ℝ) := by
      rw [hW₂cast]
      have h1 : (m : ℝ) / 16 + 3 ≤ ((m : ℝ) - 7) / 8 := by linarith
      have h2 : (T.side : ℝ) * ((m : ℝ) / 16 + 3) ≤ T.side * (((m : ℝ) - 7) / 8) :=
        mul_le_mul_of_nonneg_left h1 hL0.le
      have e1 : (T.side : ℝ) * ((m : ℝ) / 16 + 3) = T.side * m / 16 + 3 * T.side := by ring
      have e2 : (T.side : ℝ) * (((m : ℝ) - 7) / 8) = T.side * ((m : ℝ) - 7) / 8 := by ring
      linarith
    have hbz : s.InBalls 0 := fun b => by
      show coordNorm 0 ≤ R.ballRadius
      rw [coordNorm_zero]
      exact hρ.le
    have hbz' : s'.InBalls 0 := fun b => by
      show coordNorm 0 ≤ R.ballRadius
      rw [coordNorm_zero]
      exact hρ.le
    have hself := settingsAgreeNear_self hag
    have hopen : ∀ η ∈ openBallsIn R s.free, s.InBalls η := fun η h b => (h b).le
    have hopen' : ∀ η ∈ openBallsIn R s'.free, s'.InBalls η := fun η h b => (h b).le
    have hBm : MeasurableSet (openBallsIn R s.free) := measurableSet_openBallsIn
    have hBm' : MeasurableSet (openBallsIn R s'.free) := measurableSet_openBallsIn
    have Pss : ∀ η ζ : FreeCoords s.free, s.InBalls η → s.InBalls ζ → CoordsAgreeNear s s Y Y k η ζ →
        |(s.blockInteraction Y η - s.blockGaussian T.lam Y η) - (s.blockInteraction Y ζ - s.blockGaussian T.lam Y ζ)| ≤
          Cψ * Real.exp (-(4 * T.rt * k)) ∧
          |s.blockInteraction Y η - s.blockGaussian T.lam Y η| ≤ Cψ * R.coupling := fun η ζ hη hζ hnr =>
      Ps y hyP R hR n n hn hn s s Y Y m k η ζ hs hs hself hk4 hkm hrk hnr hη hζ
    have Pst : ∀ (η : FreeCoords s.free) (ζ : FreeCoords s'.free), s.InBalls η → s'.InBalls ζ →
        CoordsAgreeNear s s' Y Y' k η ζ →
        |(s.blockInteraction Y η - s.blockGaussian T.lam Y η) -
          (s'.blockInteraction Y' ζ - s'.blockGaussian T.lam Y' ζ)| ≤ Cψ * Real.exp (-(4 * T.rt * k)) :=
      fun η ζ hη hζ hnr => (Ps y hyP R hR n n' hn hn' s s' Y Y' m k η ζ hs hs' hag hk4 hkm hrk hnr hη hζ).1
    set g : FreeCoords s.free → ℝ := fun η => s.blockInteraction Y η - s.blockGaussian T.lam Y η with hg
    set g' : FreeCoords s'.free → ℝ := fun η => s'.blockInteraction Y' η - s'.blockGaussian T.lam Y' η with hg'
    have hgB : AEBounded (volume.restrict (openBallsIn R s.free)) g :=
      (aeBounded_interaction hregs Y).sub (aeBounded_gaussianPart T.lam Y)
    have hgB' : AEBounded (volume.restrict (openBallsIn R s'.free)) g' :=
      (aeBounded_interaction hregs' Y').sub (aeBounded_gaussianPart T.lam Y')
    have hgm : Measurable ((openBallsIn R s.free).indicator g) := by
      classical
      have hc : ContinuousOn (fun η => R.coupling * ∑ b ∈ freeBondsAt s.free Y, s.densitySplit.segmentIntegral b η)
          (openBallsIn R s.free) :=
        (continuousOn_const.mul (continuousOn_finsetSum _ fun b _ =>
          continuousOn_segmentIntegral hregs b)).mono openBallsIn_subset_closedBallsIn
      have h1 : Measurable ((openBallsIn R s.free).indicator
          fun η => R.coupling * ∑ b ∈ freeBondsAt s.free Y, s.densitySplit.segmentIntegral b η) := by
        have := hc.measurable_piecewise (g := fun _ => (0 : ℝ)) continuousOn_const hBm
        rwa [show (openBallsIn R s.free).piecewise
          (fun η => R.coupling * ∑ b ∈ freeBondsAt s.free Y, s.densitySplit.segmentIntegral b η)
            (fun _ => (0 : ℝ)) =
            (openBallsIn R s.free).indicator
              (fun η => R.coupling * ∑ b ∈ freeBondsAt s.free Y, s.densitySplit.segmentIntegral b η) from
          Set.piecewise_eq_indicator] at this
      have h2 : Measurable ((openBallsIn R s.free).indicator (s.logJacobianAt Y)) :=
        hregs.measurable_logJacobian Y
      have h3 : Measurable ((openBallsIn R s.free).indicator fun _ : FreeCoords s.free => s.logJacobianAt Y 0) :=
        measurable_const.indicator hBm
      have h4 : Measurable ((openBallsIn R s.free).indicator (s.blockGaussian T.lam Y)) :=
        (continuous_gaussianPart (R := R) (free := s.free) T.lam Y).measurable.indicator hBm
      have e : (openBallsIn R s.free).indicator g = fun η =>
          (openBallsIn R s.free).indicator
            (fun η => R.coupling * ∑ b ∈ freeBondsAt s.free Y, s.densitySplit.segmentIntegral b η) η -
          (openBallsIn R s.free).indicator (s.logJacobianAt Y) η +
          (openBallsIn R s.free).indicator (fun _ => s.logJacobianAt Y 0) η -
          (openBallsIn R s.free).indicator (s.blockGaussian T.lam Y) η := by
        funext η
        by_cases h : η ∈ openBallsIn R s.free
        · simp only [Set.indicator_of_mem h, hg]
          have := interaction_eq hregs (openBallsIn_subset_closedBallsIn h) Y
          show s.densitySplit.interaction Y η - s.blockGaussian T.lam Y η = _
          rw [this]
          rfl
        · simp only [Set.indicator_of_notMem h]
          ring
      rw [e]
      exact ((h1.sub h2).add h3).sub h4
    set Fψ : (NearBondIndex → EuclideanSpace ℝ (Fin 3)) → ℝ := fun z =>
      (openBallsIn R s.free).indicator g (s.extendByIndex Y k z) with hFψ
    have hFψm : Measurable Fψ := hgm.comp (measurable_extendByIndex s Y k)
    have hFψb : ∀ z, |Fψ z| ≤ Cψ * R.coupling := by
      intro z
      by_cases h : s.extendByIndex Y k z ∈ openBallsIn R s.free
      · simp only [hFψ, Set.indicator_of_mem h]
        exact (Pss _ _ (hopen _ h) (hopen _ h) (fun _ _ => rfl)).2
      · simp only [hFψ, Set.indicator_of_notMem h, abs_zero]
        positivity
    have hFψr : DependsWithin T.side (m / 4) Fψ := by
      intro z z' h
      simp only [hFψ]
      rw [extendByIndex_congr s Y hkq (R := R) (fun q hq => h q (by rw [← hLq] at *; exact hq))]
    have hFψo : ∀ z z', CoordsInBalls R z → CoordsInBalls R z' → |Fψ z - Fψ z'| ≤ 2 * (Cψ * R.coupling) := by
      intro z z' _ _
      have h1 := hFψb z
      have h2 := hFψb z'
      have h3 := abs_sub (Fψ z) (Fψ z')
      linarith
    have hHB : AEBounded (volume.restrict (openBallsIn R s.free)) fun η => Fψ (s.coordsByIndex Y η) :=
      ⟨(hFψm.comp (measurable_coordsByIndex s Y)).aestronglyMeasurable, Cψ * R.coupling,
        Filter.Eventually.of_forall fun η => hFψb _⟩
    have hHB' : AEBounded (volume.restrict (openBallsIn R s'.free)) fun η => Fψ (s'.coordsByIndex Y' η) :=
      ⟨(hFψm.comp (measurable_coordsByIndex s' Y')).aestronglyMeasurable, Cψ * R.coupling,
        Filter.Eventually.of_forall fun η => hFψb _⟩
    have hcl : ∀ η ∈ openBallsIn R s.free, |g η - Fψ (s.coordsByIndex Y η)| ≤ Cψ * Real.exp (-(4 * T.rt * k)) := by
      intro η h
      have hz := extendByIndex_mem_openBallsIn s Y k hρ (coordNorm_coordsByIndex_lt s Y hρ h)
      simp only [hFψ, Set.indicator_of_mem hz]
      have hn := coordsAgreeNear_extendByIndex hodd hself hkm η
      have := (Pss _ _ (hopen _ hz) (hopen _ h) hn).1
      rwa [abs_sub_comm] at this
    have hcl' : ∀ η ∈ openBallsIn R s'.free,
        |g' η - Fψ (s'.coordsByIndex Y' η)| ≤ Cψ * Real.exp (-(4 * T.rt * k)) := by
      intro η h
      have hz := extendByIndex_mem_openBallsIn s Y k hρ (coordNorm_coordsByIndex_lt s' Y' hρ h)
      simp only [hFψ, Set.indicator_of_mem hz]
      have hn := coordsAgreeNear_extendByIndex hodd hag hkm η
      have := Pst _ _ (hopen _ hz) (hopen' _ h) hn
      rwa [abs_sub_comm] at this
    have hτ : ∀ τ ∈ Set.Icc (0 : ℝ) 1,
        |weightedMean (s.densitySplit.interpolatedDensity T.lam τ) g -
          weightedMean (s'.densitySplit.interpolatedDensity T.lam τ) g'| ≤
          2 * (Cψ * Real.exp (-(4 * T.rt * k))) + 2 * (Cψ * R.coupling) * Real.exp (-(T.rt * m / 2 ^ 3)) := by
      intro τ hτ'
      have hA : AlikePotentials s s' T.lam Y Y' m
          (fun η => τ * s.partPotential 0 η + (1 - τ) * s.restrictedPotential T.lam 0 ∅ (s.partPotential 0) η)
          (fun η => τ * s'.partPotential 0 η + (1 - τ) * s'.restrictedPotential T.lam 0 ∅ (s'.partPotential 0) η) :=
        AlikePotentials.convex τ _ _ _ _ hτ'.1 hτ'.2 (AlikePotentials.part_potential 0 le_rfl zero_le_one)
          (AlikePotentials.restrict 0 ∅ ∅ _ _ le_rfl zero_le_one (fun q h h' _ => by simp)
            (AlikePotentials.part_potential 0 le_rfl zero_le_one))
      have h2 := L3 y hyL R hR n n' hn hn' s s' Y Y' m hs hs' hag hrm
        _ _ hA Fψ _ hFψm hFψr hFψo
      rw [← weightedMean_interpolatedDensity_eq_lawDensity s hregs,
        ← weightedMean_interpolatedDensity_eq_lawDensity s' hregs'] at h2
      have h1 := abs_sub_weightedMean_interpolatedDensity_le hcore hρ hp hregs T.lam τ hgB hHB hcl
      have h3 := abs_sub_weightedMean_interpolatedDensity_le hcore hρ hp hregs' T.lam τ hgB' hHB' hcl'
      have e := abs_sub_le (weightedMean (s.densitySplit.interpolatedDensity T.lam τ) g)
        (weightedMean (s.densitySplit.interpolatedDensity T.lam τ) fun η => Fψ (s.coordsByIndex Y η))
        (weightedMean (s'.densitySplit.interpolatedDensity T.lam τ) g')
      have e2 := abs_sub_le (weightedMean (s.densitySplit.interpolatedDensity T.lam τ)
          fun η => Fψ (s.coordsByIndex Y η))
        (weightedMean (s'.densitySplit.interpolatedDensity T.lam τ) fun η => Fψ (s'.coordsByIndex Y' η))
        (weightedMean (s'.densitySplit.interpolatedDensity T.lam τ) g')
      rw [abs_sub_comm (weightedMean (s'.densitySplit.interpolatedDensity T.lam τ)
        fun η => Fψ (s'.coordsByIndex Y' η))] at e2
      have h2' : |weightedMean (s.densitySplit.interpolatedDensity T.lam τ) (fun η => Fψ (s.coordsByIndex Y η)) -
          weightedMean (s'.densitySplit.interpolatedDensity T.lam τ) fun η => Fψ (s'.coordsByIndex Y' η)| ≤
          2 * (Cψ * R.coupling) * Real.exp (-(T.rt * m / 2 ^ 3)) := h2
      linarith
    obtain ⟨hGφ, Mφ, hMφ⟩ := hsd R n s hfit hE1 hx hrn hrL hR.isStep.1 hnq hs
    obtain ⟨G, hGm, hGe⟩ := hGφ Y
    set Fφ : (NearBondIndex → EuclideanSpace ℝ (Fin 3)) → ℝ := fun z => G (s.extendByIndex Y k z) with hFφ
    have hFφm : Measurable Fφ := hGm.comp (measurable_extendByIndex s Y k)
    have hFφr : DependsWithin T.side (m / 4) Fφ := by
      intro z z' h
      simp only [hFφ]
      rw [extendByIndex_congr s Y hkq (R := R) (fun q hq => h q (by rw [← hLq] at *; exact hq))]
    have hFφo : ∀ z z', CoordsInBalls R z → CoordsInBalls R z' →
        |Fφ z - Fφ z'| ≤ (R.params.side : ℝ) ^ 4 * (4 * R.params.E + 2) := by
      intro z z' hz hz'
      have a := inBalls_extendByIndex s Y k hρ.le hz
      have b := inBalls_extendByIndex s Y k hρ.le hz'
      simp only [hFφ]
      rw [hGe _ a, hGe _ b]
      exact hosc R n s hfit hE1 hx hrn hrL hR.isStep.1 hnq hs Y _ _ a b
    set eφ : ℝ := (R.params.side : ℝ) ^ 4 *
      Real.exp (-R.params.decayRate * ((R.params.side * k - 2 * R.params.side : ℕ) : ℝ)) with heφ
    have Sss : ∀ η ζ : FreeCoords s.free, s.InBalls η → s.InBalls ζ → CoordsAgreeNear s s Y Y k η ζ →
        |s.blockDensityAt Y η - s.blockDensityAt Y ζ| ≤ eφ := fun η ζ hη hζ hnr =>
      hstate R n n s s Y Y m k η ζ hfit hR.isStep.1 hnq hnq hs hs hself (by omega) hkm hW₂ hnr hη hζ
    have Sst : ∀ (η : FreeCoords s.free) (ζ : FreeCoords s'.free), s.InBalls η → s'.InBalls ζ →
        CoordsAgreeNear s s' Y Y' k η ζ → |s.blockDensityAt Y η - s'.blockDensityAt Y' ζ| ≤ eφ :=
      fun η ζ hη hζ hnr =>
      hstate R n n' s s' Y Y' m k η ζ hfit hR.isStep.1 hnq hnq' hs hs' hag (by omega) hkm hW₂ hnr hη hζ
    have hφB : AEBounded (volume.restrict (openBallsIn R s.free)) (s.densitySplit.density Y) :=
      aeBounded_density hregs Y
    have hφB' : AEBounded (volume.restrict (openBallsIn R s'.free)) (s'.densitySplit.density Y') :=
      aeBounded_density hregs' Y'
    have hKB : AEBounded (volume.restrict (openBallsIn R s.free)) fun η => Fφ (s.coordsByIndex Y η) := by
      refine ⟨(hFφm.comp (measurable_coordsByIndex s Y)).aestronglyMeasurable, Mφ,
        ae_restrict_of_forall_mem hBm fun η h => ?_⟩
      have hz := inBalls_extendByIndex s Y k hρ.le (coordsInBalls_coordsByIndex s Y hρ.le (hopen η h))
      simp only [hFφ]
      rw [hGe _ hz]
      exact hMφ _ hz Y
    have hKB' : AEBounded (volume.restrict (openBallsIn R s'.free)) fun η => Fφ (s'.coordsByIndex Y' η) := by
      refine ⟨(hFφm.comp (measurable_coordsByIndex s' Y')).aestronglyMeasurable, Mφ,
        ae_restrict_of_forall_mem hBm' fun η h => ?_⟩
      have hz := inBalls_extendByIndex s Y k hρ.le (coordsInBalls_coordsByIndex s' Y' hρ.le (hopen' η h))
      simp only [hFφ]
      rw [hGe _ hz]
      exact hMφ _ hz Y
    have hcφ : ∀ η ∈ openBallsIn R s.free, |s.densitySplit.density Y η - Fφ (s.coordsByIndex Y η)| ≤ eφ := by
      intro η h
      have hz := inBalls_extendByIndex s Y k hρ.le (coordsInBalls_coordsByIndex s Y hρ.le (hopen η h))
      simp only [hFφ]
      rw [hGe _ hz]
      have hn := coordsAgreeNear_extendByIndex hodd hself hkm η
      have := Sss _ _ hz (hopen η h) hn
      rwa [abs_sub_comm] at this
    have hcφ' : ∀ η ∈ openBallsIn R s'.free,
        |s'.densitySplit.density Y' η - Fφ (s'.coordsByIndex Y' η)| ≤ eφ := by
      intro η h
      have hz := inBalls_extendByIndex s Y k hρ.le (coordsInBalls_coordsByIndex s' Y' hρ.le (hopen' η h))
      simp only [hFφ]
      rw [hGe _ hz]
      have hn := coordsAgreeNear_extendByIndex hodd hag hkm η
      have := Sst _ _ hz (hopen' η h) hn
      rwa [abs_sub_comm] at this
    have hν : ∀ ν ∈ Set.Icc (0 : ℝ) 1,
        |weightedMean (s.densitySplit.perturbedDensity ν) (s.densitySplit.density Y) -
          weightedMean (s'.densitySplit.perturbedDensity ν) (s'.densitySplit.density Y')| ≤
          2 * eφ + (R.params.side : ℝ) ^ 4 * (4 * R.params.E + 2) * Real.exp (-(T.rt * m / 2 ^ 3)) := by
      intro ν hν'
      have hA : AlikePotentials s s' T.lam Y Y' m (s.partPotential ν) (s'.partPotential ν) :=
        AlikePotentials.part_potential ν hν'.1 hν'.2
      have h2 := L3 y hyL R hR n n' hn hn' s s' Y Y' m hs hs' hag hrm
        _ _ hA Fφ _ hFφm hFφr hFφo
      rw [← weightedMean_perturbedDensity_eq_lawDensity s hregs,
        ← weightedMean_perturbedDensity_eq_lawDensity s' hregs'] at h2
      have h1 := abs_sub_weightedMean_perturbedDensity_le hcore hρ hp hregs ν hφB hKB hcφ
      have h3 := abs_sub_weightedMean_perturbedDensity_le hcore hρ hp hregs' ν hφB' hKB' hcφ'
      have e := abs_sub_le (weightedMean (s.densitySplit.perturbedDensity ν) (s.densitySplit.density Y))
        (weightedMean (s.densitySplit.perturbedDensity ν) fun η => Fφ (s.coordsByIndex Y η))
        (weightedMean (s'.densitySplit.perturbedDensity ν) (s'.densitySplit.density Y'))
      have e2 := abs_sub_le (weightedMean (s.densitySplit.perturbedDensity ν) fun η => Fφ (s.coordsByIndex Y η))
        (weightedMean (s'.densitySplit.perturbedDensity ν) fun η => Fφ (s'.coordsByIndex Y' η))
        (weightedMean (s'.densitySplit.perturbedDensity ν) (s'.densitySplit.density Y'))
      rw [abs_sub_comm (weightedMean (s'.densitySplit.perturbedDensity ν)
        fun η => Fφ (s'.coordsByIndex Y' η))] at e2
      have h2' : |weightedMean (s.densitySplit.perturbedDensity ν) (fun η => Fφ (s.coordsByIndex Y η)) -
          weightedMean (s'.densitySplit.perturbedDensity ν) fun η => Fφ (s'.coordsByIndex Y' η)| ≤
          (R.params.side : ℝ) ^ 4 * (4 * R.params.E + 2) * Real.exp (-(T.rt * m / 2 ^ 3)) := h2
      linarith
    have h00 : CoordsAgreeNear s s' Y Y' k 0 0 := by
      classical
      intro q _
      have a : s.coordsByIndex Y 0 q = 0 := by
        unfold ChartSetting.coordsByIndex
        split_ifs <;> rfl
      have b : s'.coordsByIndex Y' 0 q = 0 := by
        unfold ChartSetting.coordsByIndex
        split_ifs <;> rfl
      rw [a, b]
    have hcz := hcost T hD y R hy0 hR.params_eq n n' hn hn' s s' Y Y' m k 0 0 hs hs' hag hk4 hkm h00 hbz hbz'
    set W : ℕ := T.side * k - T.side - 2 ^ 16 with hW
    have h0' : |R.coupling * s.densitySplit.cost Y 0 - R.coupling * s'.densitySplit.cost Y' 0| ≤
        R.coupling * (K₀ * Real.exp (-T.δ₁ * (W : ℝ))) := by
      rw [← mul_sub, abs_mul, abs_of_pos hx]
      exact mul_le_mul_of_nonneg_left hcz.1 hx.le
    have hz := abs_activity_sub_le (D := s.densitySplit) (D' := s'.densitySplit) (lam := T.lam) (Y := Y) (Y' := Y')
      h0' hcz.2.1 hcz.2.2 hτ hν
      (continuous_weightedMean_interpolatedDensity hcore hρ hp hregs T.lam hgB)
      (continuous_weightedMean_interpolatedDensity hcore hρ hp hregs' T.lam hgB')
      (continuous_weightedMean_perturbedDensity hcore hρ hp hregs hφB)
      (continuous_weightedMean_perturbedDensity hcore hρ hp hregs' hφB')
    refine le_trans hz ?_
    have hrtδ : T.rt ≤ T.δ₁ := by
      have h1 := hD.rt_le
      have h2 := hD.δc_le
      have h3 := hD.δ₁_pos
      have h4 := hD.δc_pos
      linarith
    have hm16 : (m : ℝ) ≤ 16 * k := by linarith
    have hk4R : (4 : ℝ) ≤ k := by exact_mod_cast hk4
    have hWR : (T.side : ℝ) * k / 2 ≤ W := by
      have hP : 4 * T.side ≤ T.side * k := by
        rw [mul_comm 4]
        exact Nat.mul_le_mul_left _ hk4
      have hLn := hD.L_ge
      have hWn : T.side * k ≤ 2 * W := by
        rw [hW]
        generalize T.side * k = P at *
        omega
      have : ((T.side * k : ℕ) : ℝ) ≤ ((2 * W : ℕ) : ℝ) := by exact_mod_cast hWn
      push_cast at this
      linarith
    have hf : R.params.decayRate = T.rt / 2 ^ 12 := by
      unfold StepParameters.decayRate
      rw [hrtq]
    have hfin := density_locality_arith (rt := T.rt) (δ := T.δ₁) (L := T.side) (k := k) (m := m)
      (x := R.coupling) (K₀ := K₀) (Cψ := Cψ) (E := T.E) (W := W)
      (W₂ := ((R.params.side * k - 2 * R.params.side : ℕ) : ℝ)) (f := R.params.decayRate) (c := c₀)
      (r := R.range) (C₀ := C₀) hrtpos hrtδ hD.δ₁_pos hL15 hk4R (Nat.cast_nonneg _) hm16 hWR hW₂cast hf hx1
      hK₀pos.le hCψ.le hE0 hKC hC₁ hFl.stretched_tail.1 rfl hrM
    have hEr : (R.params.E : ℝ) = T.E := hEq
    rw [heφ, hLr, hEr]
    exact hfin
  refine ⟨key m, fun hm₀ hoff => ?_⟩
  have hm0le : R.frameReach ≤ m := by omega
  obtain ⟨m', hm'⟩ : ∃ m', m' = m - R.frameReach := ⟨_, rfl⟩
  have hm'm : m' ≤ m := by omega
  have hcast : (m' : ℝ) = (m : ℝ) - R.frameReach := by
    rw [hm', Nat.cast_sub hm0le]
  have hrlarge : 2 ^ 11 ≤ R.range := by
    have hb : (2 : ℝ) ^ 11 ≤ R.range := by nlinarith [show (2 : ℝ) ^ 21 * 1 ≤ 2 ^ 21 * T.side by nlinarith]
    exact_mod_cast hb
  have hm₀pos : 0 < R.frameReach := by
    unfold StepSetup.frameReach
    exact Nat.div_pos hrlarge (by norm_num)
  have hside : 4 * R.frameReach + 5 < n := by have := hoff.lt_extent; omega
  have hside' : 4 * R.frameReach + 5 < n' := by have := hoff.lt_extent'; omega
  have hag' : SettingsAgreeNear s s' Y Y' m' := by
    refine ⟨by have := hoff.lt_extent; omega, by have := hoff.lt_extent'; omega, ?_,
      fun q hq => hoff.free_iff q (isNearIndex_mono hq hm'm),
      fun q hq => hoff.fine_eq q (isNearIndex_mono hq hm'm), ?_,
      fun h o hh ho => hoff.support_iff h o (fun i => (hh i).trans (by exact_mod_cast hm'm)) ho,
      fun h o hz hz' hh ho => hoff.labelling_eq h o hz hz' (fun i => (hh i).trans (by exact_mod_cast hm'm)) ho,
      fun h hh => hoff.bases_match h (fun i => (hh i).trans (by exact_mod_cast hm'm))⟩
    · intro b hb
      exact hoff.coarse_agree b ⟨fun i => (hb.1 i).trans (by exact_mod_cast hm'm),
        fun i => (hb.2 i).trans (by exact_mod_cast hm'm)⟩
    · rintro ⟨h, o, i⟩ hq _
      have ho : o ∈ centredCube R.params.side := hq.2
      have hoff₁ := cellOffset_torusFrame (L := R.params.side) (n := n) R.depth hodd
        (fun i => ((Y i).cast : ℤ) + h i) o ho
      have hoff₂ := cellOffset_torusFrame (L := R.params.side) (n := n') R.depth hodd
        (fun i => ((Y' i).cast : ℤ) + h i) o ho
      refine hfr R.params R.anchorRadius R.depth R.frameReach n n' s.coarse s'.coarse _ _ hfit hm₀pos hside hside'
        rfl (hoff₁.trans hoff₂.symm) ?_
      show FieldsAgreeNear s.coarse s'.coarse (parentBlock R.params.side (fineSite R.params.side Y h o))
        (parentBlock R.params.side (fineSite R.params.side Y' h o)) R.frameReach
      rw [parentBlock_fineSite hodd Y h o ho, parentBlock_fineSite hodd Y' h o ho]
      intro b hb
      have hbox : BondWithinRadius m (h + b.1, b.2) := by
        constructor
        · intro i
          have h1 : |h i| ≤ (m' : ℤ) := hq.1 i
          have h2 : |b.1 i| ≤ (R.frameReach : ℤ) := hb.1 i
          have : ((m' : ℤ) + R.frameReach) ≤ m := by omega
          show |h i + b.1 i| ≤ (m : ℤ)
          rw [abs_le] at h1 h2 ⊢
          constructor <;> omega
        · intro i
          have h1 : |h i| ≤ (m' : ℤ) := hq.1 i
          have h2 : |(b.1 + Pi.single b.2 1 : Fin 4 → ℤ) i| ≤ (R.frameReach : ℤ) := hb.2 i
          have : ((m' : ℤ) + R.frameReach) ≤ m := by omega
          have e : ((h + b.1) + Pi.single b.2 1 : Fin 4 → ℤ) i = h i + (b.1 + Pi.single b.2 1 : Fin 4 → ℤ) i := by
            simp only [Pi.add_apply]
            ring
          show |((h + b.1) + Pi.single b.2 1 : Fin 4 → ℤ) i| ≤ (m : ℤ)
          rw [e]
          rw [abs_le] at h1 h2 ⊢
          constructor <;> omega
      have hh := hoff.coarse_agree (h + b.1, b.2) hbox
      have e1 : ∀ (N : ℕ) [NeZero N] (Z : TorusSite N), (bondFrom (Z + siteOfInt h) b).1 = (bondFrom Z (h + b.1, b.2)).1 := by
        intro N _ Z
        simp only [bondFrom]
        rw [add_assoc, ← BlockOffsets.siteOfInt_add]
      show s.coarse (bondFrom (Y + siteOfInt h) b).1 b.2 = s'.coarse (bondFrom (Y' + siteOfInt h) b).1 b.2
      rw [e1, e1]
      exact hh
  have hLr : (R.params.side : ℝ) = T.side := by exact_mod_cast hLq
  have hm₀R : (R.range : ℝ) / 2 ^ 11 - 1 ≤ R.frameReach := by
    have h1 : R.range < 2 ^ 11 * (R.frameReach + 1) := by
      unfold StepSetup.frameReach
      have := Nat.lt_mul_div_succ R.range (show 0 < 2 ^ 11 by norm_num)
      simpa using this
    have h2 : (R.range : ℝ) < 2 ^ 11 * ((R.frameReach : ℝ) + 1) := by exact_mod_cast h1
    have : (R.range : ℝ) / 2 ^ 11 < (R.frameReach : ℝ) + 1 := by
      rw [div_lt_iff₀ (by norm_num)]
      linarith
    linarith
  have hm₀m : (16 : ℝ) * R.frameReach ≤ m := by exact_mod_cast hm₀
  have hrm' : (R.range : ℝ) / (4 * R.params.side) ≤ m' := by
    rw [hcast, hLr, div_le_iff₀ (by positivity)]
    have hr0 : (0 : ℝ) ≤ R.range := by positivity
    have h15 : 15 * (R.frameReach : ℝ) ≤ (m : ℝ) - R.frameReach := by linarith
    have h1 : (2 : ℝ) ^ 21 * T.side ≤ R.range := hr2
    have h2 : (R.range : ℝ) ≤ ((m : ℝ) - R.frameReach) * (4 * T.side) := by
      have h3 : 15 * ((R.range : ℝ) / 2 ^ 11 - 1) ≤ (m : ℝ) - R.frameReach := by linarith
      have h4 : (R.range : ℝ) / 2 ^ 12 ≤ 15 * ((R.range : ℝ) / 2 ^ 11 - 1) := by
        have : (2 : ℝ) ^ 21 ≤ R.range := by nlinarith
        nlinarith
      have h5 : (R.range : ℝ) / 2 ^ 12 ≤ (m : ℝ) - R.frameReach := h4.trans h3
      have h6 : (R.range : ℝ) / 2 ^ 12 * (4 * T.side) ≤ ((m : ℝ) - R.frameReach) * (4 * T.side) :=
        mul_le_mul_of_nonneg_right h5 (by positivity)
      have h7 : (R.range : ℝ) ≤ (R.range : ℝ) / 2 ^ 12 * (4 * T.side) := by nlinarith
      linarith
    linarith
  have hfirst := key m' hrm' hag'
  rw [hcast] at hfirst
  refine ⟨hfirst, ?_⟩
  apply Real.exp_le_exp.mpr
  have : 15 / 16 * (m : ℝ) ≤ (m : ℝ) - R.frameReach := by linarith
  have h2 := mul_le_mul_of_nonneg_left this hrtpos.le
  have e : 15 / 16 * T.rt * (m : ℝ) / 2 ^ 5 = T.rt * (15 / 16 * (m : ℝ)) / 2 ^ 5 := by ring
  rw [e]
  have h3 : T.rt * (15 / 16 * (m : ℝ)) / 2 ^ 5 ≤ T.rt * ((m : ℝ) - R.frameReach) / 2 ^ 5 := by
    exact div_le_div_of_nonneg_right h2 (by norm_num)
  linarith
end Main
end YangMills.Construction.ClusterExpansionOfAStep
end
