import YangMills.Construction.ClusterExpansionOfAStep.AdmissionEqualInBoxes
import YangMills.Construction.ClusterExpansionOfAStep.MovesOfFreeBondsForm
import YangMills.Construction.ClusterExpansionOfAStep.FitsOfASetting
import YangMills.Construction.ColdStepAtMirrorFrames.ChartUnderGaugesAndShiftsProof
import YangMills.Construction.ColdStepAtMirrorFrames.SecondOrderOfADensityAtConstantCurvatureProof
import YangMills.Construction.HoleBesideASecondHole.EnergyInTheChart
import YangMills.Construction.RunningCouplingSlope.LeastFieldIsABlockMap
import YangMills.Construction.RunningCouplingSlope.LeastFieldIsOneOnLargeTori
import YangMills.Construction.RunningCouplingSlope.TotalAtTheLeastField
import YangMills.Construction.RunningCouplingSlope.TotalOfAStepReadsNoBoundProof
import YangMills.Construction.SummableBoundsOfTheFlow.EnergyUnderAnIsometry
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Topology Quaternion
open Filter
namespace YangMills.Construction
open BlockAverages ColdStepAtMirrorFrames TorusFields TorusLumps QuaternionLogarithm StepCosts EnergySymmetry GaugeFixing
  SlopeCoefficient
namespace RunningCouplingSlope
namespace MinimizerTotal
section Units
private theorem norm_inv_sub_one (g : UnitQuaternion) :
    ‖((g⁻¹ : UnitQuaternion) : ℍ[ℝ]) - 1‖ = ‖(g : ℍ[ℝ]) - 1‖ := by apply _root_.YangMills.Construction.BlockAverages.norm_coe_inv_sub_one <;> assumption
private theorem norm_mul_sub_one_le (g h : UnitQuaternion) :
    ‖((g * h : UnitQuaternion) : ℍ[ℝ]) - 1‖ ≤ ‖(g : ℍ[ℝ]) - 1‖ + ‖(h : ℍ[ℝ]) - 1‖ := by apply _root_.YangMills.Construction.BlockAverages.norm_coe_mul_sub_one_le <;> assumption
private theorem continuous_unitInv : Continuous fun g : UnitQuaternion => g⁻¹ := by
  refine Continuous.subtype_mk (f := fun g : UnitQuaternion => star (g : ℍ[ℝ])) ?_ _
  exact continuous_star.comp continuous_subtype_val
private theorem continuous_unitMul : Continuous fun p : UnitQuaternion × UnitQuaternion => p.1 * p.2 := by
  refine Continuous.subtype_mk (f := fun p : UnitQuaternion × UnitQuaternion => (p.1 : ℍ[ℝ]) * (p.2 : ℍ[ℝ])) ?_ _
  exact (continuous_subtype_val.comp continuous_fst).mul (continuous_subtype_val.comp continuous_snd)
end Units
section Near
variable {m : ℕ} [NeZero m]
private theorem gauge_mem_of_near_one {U : Set (TorusSite m → UnitQuaternion)} (hU : U ∈ 𝓝 (1 : TorusSite m → UnitQuaternion)) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ γ : TorusSite m → UnitQuaternion, (∀ x, ‖(γ x : ℍ[ℝ]) - 1‖ < ε) → γ ∈ U := by
  obtain ⟨ε, hε, h⟩ := Metric.mem_nhds_iff.mp hU
  refine ⟨ε, hε, fun γ hγ => h ?_⟩
  rw [Metric.mem_ball, dist_pi_lt_iff hε]
  intro x
  have := hγ x
  rw [Subtype.dist_eq, dist_eq_norm]
  simpa using this
private theorem field_mem_of_near_trivial {U : Set (TorusField m)} (hU : U ∈ 𝓝 (trivialField m)) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ W : TorusField m, (∀ x i, ‖(W x i : ℍ[ℝ]) - 1‖ < ε) → W ∈ U := by
  obtain ⟨ε, hε, h⟩ := Metric.mem_nhds_iff.mp hU
  refine ⟨ε, hε, fun W hW => h ?_⟩
  rw [Metric.mem_ball, dist_pi_lt_iff hε]
  intro x
  rw [dist_pi_lt_iff hε]
  intro i
  have := hW x i
  rw [Subtype.dist_eq, dist_eq_norm]
  simpa [trivialField] using this
private theorem eventually_links_near_one {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ W in 𝓝 (trivialField m), ∀ x i, ‖((W x i : UnitQuaternion) : ℍ[ℝ]) - 1‖ < ε := by
  rw [eventually_all]
  intro x
  rw [eventually_all]
  intro i
  have hc : Continuous fun W : TorusField m => ‖((W x i : UnitQuaternion) : ℍ[ℝ]) - 1‖ :=
    (((continuous_subtype_val.comp ((continuous_apply i).comp (continuous_apply x))).sub
      continuous_const)).norm
  have h0 : ‖((trivialField m x i : UnitQuaternion) : ℍ[ℝ]) - 1‖ < ε := by
    simpa [trivialField] using hε
  exact hc.continuousAt.eventually (gt_mem_nhds h0)
abbrev _root_.YangMills.SharedProofs.p18107 := @eventually_links_near_one
private theorem gauge_step_bound {γ : TorusSite m → UnitQuaternion} {Y q : TorusField m} {δ : ℝ}
    (hY : ∀ x i, ‖(Y x i : ℍ[ℝ]) - 1‖ < δ)
    (hq : ∀ x i, ‖(q x i : ℍ[ℝ]) - 1‖ < δ) (e : Y = TorusFields.gaugeTransform γ q) (x : TorusSite m) (i : Fin 4) :
    ‖(γ (x + TorusFields.unitStep m i) : ℍ[ℝ]) - 1‖ ≤ ‖(γ x : ℍ[ℝ]) - 1‖ + 2 * δ := by
  have h : γ (x + TorusFields.unitStep m i) = (Y x i)⁻¹ * γ x * q x i := by
    rw [e]
    simp only [TorusFields.gaugeTransform]
    group
  rw [h]
  have a1 := norm_mul_sub_one_le ((Y x i)⁻¹ * γ x) (q x i)
  have a2 := norm_mul_sub_one_le (Y x i)⁻¹ (γ x)
  rw [norm_inv_sub_one] at a2
  have b1 := hY x i
  have b2 := hq x i
  linarith
private theorem gauge_line_bound {γ : TorusSite m → UnitQuaternion} {Y q : TorusField m} {δ : ℝ}
    (hY : ∀ x i, ‖(Y x i : ℍ[ℝ]) - 1‖ < δ)
    (hq : ∀ x i, ‖(q x i : ℍ[ℝ]) - 1‖ < δ) (e : Y = TorusFields.gaugeTransform γ q) (x : TorusSite m) (i : Fin 4)
    (k : ℕ) :
    ‖(γ (x + k • TorusFields.unitStep m i) : ℍ[ℝ]) - 1‖ ≤ ‖(γ x : ℍ[ℝ]) - 1‖ + k * (2 * δ) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have h := gauge_step_bound hY hq e (x + k • TorusFields.unitStep m i) i
    have e2 : x + (k + 1) • TorusFields.unitStep m i = x + k • TorusFields.unitStep m i + TorusFields.unitStep m i := by
      rw [succ_nsmul, add_assoc]
    rw [e2]
    push_cast
    linarith
private theorem site_eq_sum_steps (x : TorusSite m) :
    x = (((0 + (x 0).val • TorusFields.unitStep m 0) + (x 1).val • TorusFields.unitStep m 1) +
      (x 2).val • TorusFields.unitStep m 2) + (x 3).val • TorusFields.unitStep m 3 := by
  have key : ∀ (v : ℕ) (i j : Fin 4), (v • TorusFields.unitStep m i) j = if j = i then (v : ZMod m) else 0 := by
    intro v i j
    by_cases h : j = i
    · subst h
      simp [TorusFields.unitStep]
    · simp [TorusFields.unitStep, h]
  funext i
  simp only [Pi.add_apply, Pi.zero_apply, key, zero_add]
  fin_cases i <;> simp
private theorem gauge_near_one {γ : TorusSite m → UnitQuaternion} {Y q : TorusField m} {δ : ℝ} (hδ : 0 < δ)
    (hY : ∀ x i, ‖(Y x i : ℍ[ℝ]) - 1‖ < δ)
    (hq : ∀ x i, ‖(q x i : ℍ[ℝ]) - 1‖ < δ) (e : Y = TorusFields.gaugeTransform γ q) (h0 : γ 0 = 1) (x : TorusSite m) :
    ‖(γ x : ℍ[ℝ]) - 1‖ ≤ 8 * m * δ := by
  have l := fun (y : TorusSite m) (i : Fin 4) (k : ℕ) => gauge_line_bound hY hq e y i k
  have v : ∀ i, (((x i).val : ℕ) : ℝ) ≤ m := fun i => by
    exact_mod_cast (ZMod.val_lt (x i)).le
  have c0 := l 0 0 (x 0).val
  have c1 := l (0 + (x 0).val • TorusFields.unitStep m 0) 1 (x 1).val
  have c2 := l ((0 + (x 0).val • TorusFields.unitStep m 0) + (x 1).val • TorusFields.unitStep m 1) 2 (x 2).val
  have c3 := l (((0 + (x 0).val • TorusFields.unitStep m 0) + (x 1).val • TorusFields.unitStep m 1) +
    (x 2).val • TorusFields.unitStep m 2) 3 (x 3).val
  rw [← site_eq_sum_steps x] at c3
  have hz : ‖(γ 0 : ℍ[ℝ]) - 1‖ = 0 := by
    rw [h0]
    simp
  rw [hz] at c0
  have w0 := mul_le_mul_of_nonneg_right (v 0) (by positivity : (0 : ℝ) ≤ 2 * δ)
  have w1 := mul_le_mul_of_nonneg_right (v 1) (by positivity : (0 : ℝ) ≤ 2 * δ)
  have w2 := mul_le_mul_of_nonneg_right (v 2) (by positivity : (0 : ℝ) ≤ 2 * δ)
  have w3 := mul_le_mul_of_nonneg_right (v 3) (by positivity : (0 : ℝ) ≤ 2 * δ)
  nlinarith
private theorem eventually_gauge_between {P : (TorusSite m → UnitQuaternion) × TorusField m → Prop}
    (h : ∀ᶠ p in 𝓝 (((1 : TorusSite m → UnitQuaternion), trivialField m)), P p) :
    ∃ U ∈ 𝓝 (trivialField m), ∀ Y ∈ U, ∀ q ∈ U, ∀ γ : TorusSite m → UnitQuaternion, γ 0 = 1 →
      Y = TorusFields.gaugeTransform γ q → P (γ, q) := by
  obtain ⟨A, hA, B, hB, hAB⟩ := mem_nhds_prod_iff.mp h
  obtain ⟨ε₁, hε₁, h₁⟩ := gauge_mem_of_near_one hA
  obtain ⟨ε₂, hε₂, h₂⟩ := field_mem_of_near_trivial hB
  have hm : (0 : ℝ) < m := by
    exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne m)
  set δ : ℝ := min ε₂ (ε₁ / (16 * m)) with hδ
  have hδ0 : 0 < δ := lt_min hε₂ (by positivity)
  have hδ1 : 8 * m * δ < ε₁ := by
    have : δ ≤ ε₁ / (16 * m) := min_le_right _ _
    rw [le_div_iff₀ (by positivity)] at this
    nlinarith
  refine ⟨{W | ∀ x i, ‖((W x i : UnitQuaternion) : ℍ[ℝ]) - 1‖ < δ}, eventually_links_near_one hδ0,
    fun Y hY q hq γ h0 e => ?_⟩
  refine hAB (Set.mk_mem_prod (h₁ γ fun x => ?_) (h₂ q fun x i => ?_))
  · exact (gauge_near_one hδ0 hY hq e h0 x).trans_lt hδ1
  · exact (hq x i).trans_le (min_le_left _ _)
end Near
section Read
variable {F : BlockFrame} {j N : ℕ} [NeZero N]
private theorem restrictToTorus_gaugeTransform (hp : ∀ i, F.period j i = N) (γ : F.Site j → UnitQuaternion)
    (W : F.GaugeField j) :
    restrictToTorus N (BlockAverages.gaugeTransform γ W) =
      TorusFields.gaugeTransform (fun x => γ (torusSiteInFrame F j x)) (restrictToTorus N W) := by
  funext x i
  have e : torusSiteInFrame F j (x + TorusFields.unitStep N i) =
      torusSiteInFrame F j x + BlockAverages.unitStep j i := by
    apply TopLevelSites.toTorusSite_injective hp
    rw [TopLevelSites.toTorusSite_add hp, TopLevelSites.toTorusSite_torusSiteInFrame hp,
      TopLevelSites.toTorusSite_torusSiteInFrame hp, TopLevelSites.toTorusSite_unitStep hp]
  show γ (torusSiteInFrame F j x) * W (torusSiteInFrame F j x) i *
      (γ (torusSiteInFrame F j x + BlockAverages.unitStep j i))⁻¹ =
    γ (torusSiteInFrame F j x) * W (torusSiteInFrame F j x) i *
      (γ (torusSiteInFrame F j (x + TorusFields.unitStep N i)))⁻¹
  rw [e]
private theorem readAtLevel_gaugeTransform (hp : ∀ i, F.period j i = N) (u : TorusSite N → UnitQuaternion)
    (V : TorusField N) :
    readAtLevel F j (TorusFields.gaugeTransform u V) =
      BlockAverages.gaugeTransform (fun z => u (toTorusSite N z)) (readAtLevel F j V) := by apply _root_.YangMills.Construction.SettingFits.readAtLevel_gaugeTransform <;> assumption
private theorem restrictToTorus_apply (hp : ∀ i, F.period j i = N) (W : F.GaugeField j) (y : F.Site j) (i : Fin 4) :
    restrictToTorus N W (toTorusSite N y) i = W y i := by
  show W (torusSiteInFrame F j (toTorusSite N y)) i = W y i
  rw [TopLevelSites.torusSiteInFrame_toTorusSite hp]
end Read
section Energy
variable {F : BlockFrame}
private theorem enclosingCell_refineSite (hL : Odd F.blockSide) (hs : ∀ i, 2 ≤ F.extent i) (y : F.Cell) :
    enclosingCell (refineSite (j := F.depth) y : F.Site F.depth) = y := by apply _root_.YangMills.Construction.ChartSymmetries.enclosingCell_refineSite <;> assumption
private theorem blockEnergy_blockGauge (hcov : gaugeCovarianceStatement) (hL : Odd F.blockSide)
    (hs : ∀ i, 2 ≤ F.extent i) (a : ℝ)
    (S : Finset F.Cell) (γ : F.Cell → UnitQuaternion) (W : F.GaugeField F.depth) (V : F.GaugeField F.top) :
    blockEnergy a S F.depth (BlockAverages.gaugeTransform (fun x => γ (enclosingCell x)) W)
      (BlockAverages.gaugeTransform γ V) = blockEnergy a S F.depth W V := by
  unfold blockEnergy
  rw [minimalAction_gaugeTransform hcov hL.pos a S F.depth (Nat.le_succ _)]
  congr 2
  refine Finset.sum_congr rfl fun c _ => ?_
  exact (hcov F F.depth (Nat.lt_succ_self _) hL.pos).2.2.2 _ γ W V c (by simp only [enclosingCell_refineSite hL hs])
    (by simp only [enclosingCell_refineSite hL hs])
private theorem fieldAboveFrame_zero (a ρ : ℝ) (V : F.GaugeField F.top) :
    fieldAboveFrame true a ρ 0 V 0 = chartedField (minimizingCoordinates a (finiteCells F) V ρ) V := by apply _root_.YangMills.SharedProofs.p22006 <;> assumption
end Energy
section Top
variable {L t n : ℕ}
private theorem top_period (i : Fin 4) : (torusFrame L t n).period (torusFrame L t n).top i = n := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.SecondOrderAtConstantCurvature.torusFrame_period_top <;> assumption
private theorem depth_period (i : Fin 4) : (torusFrame L t n).period (torusFrame L t n).depth i = n * L := by apply _root_.YangMills.Construction.CongruentAdmission.torusFrame_period_depth <;> assumption
private def frameMinimizer (a ρ : ℝ) (L t n : ℕ) (V : TorusField n) :
    (torusFrame L t n).GaugeField (torusFrame L t n).depth :=
  fieldAboveFrame (F := torusFrame L t n) true a ρ 0 (readAtLevel (torusFrame L t n) (torusFrame L t n).top V) 0
private theorem frameMinimizer_isMinimizer {a ρ : ℝ} {V : TorusField n}
    (h : ∃ w, IsMinimizingChart a (finiteCells (torusFrame L t n))
      (readAtLevel (torusFrame L t n) (torusFrame L t n).top V) ρ w) :
    IsEnergyMinimizerOver a L t n V (frameMinimizer a ρ L t n V) := by
  have hl : IsMinimizingChart a (finiteCells (torusFrame L t n))
      (readAtLevel (torusFrame L t n) (torusFrame L t n).top V) ρ
      (minimizingCoordinates a (finiteCells (torusFrame L t n))
        (readAtLevel (torusFrame L t n) (torusFrame L t n).top V) ρ) := by
    unfold minimizingCoordinates
    rw [dif_pos h]
    exact h.choose_spec
  intro W'
  unfold frameMinimizer
  rw [fieldAboveFrame_zero]
  exact hl.2.2 W'
private def blockGauge (L t : ℕ) {n : ℕ} (u : TorusSite n → UnitQuaternion) :
    (torusFrame L t n).Site (torusFrame L t n).depth → UnitQuaternion :=
  fun x => u (toTorusSite n (enclosingCell x))
private theorem isMinimizer_gaugeTransform [NeZero n] (hcov : gaugeCovarianceStatement) (hL : Odd L) (h2 : 2 ≤ n)
    {a : ℝ} (u : TorusSite n → UnitQuaternion) {V : TorusField n}
    {W : (torusFrame L t n).GaugeField (torusFrame L t n).depth} (h : IsEnergyMinimizerOver a L t n V W) :
    IsEnergyMinimizerOver a L t n (TorusFields.gaugeTransform u V)
      (BlockAverages.gaugeTransform (blockGauge L t u) W) := by
  intro W'
  have hs : ∀ i, 2 ≤ (torusFrame L t n).extent i := fun _ => h2
  have hr := readAtLevel_gaugeTransform (F := torusFrame L t n) (j := (torusFrame L t n).top) top_period u V
  have key := fun X => blockEnergy_blockGauge (F := torusFrame L t n) hcov hL hs a (finiteCells (torusFrame L t n))
    (fun z => u (toTorusSite n z)) X (readAtLevel (torusFrame L t n) (torusFrame L t n).top V)
  obtain ⟨X, rfl⟩ : ∃ X, W' = BlockAverages.gaugeTransform (blockGauge L t u) X :=
    ⟨BlockAverages.gaugeTransform (fun x => (blockGauge L t u x)⁻¹) W', (gaugeTransform_gaugeTransform_inv _ _).symm⟩
  rw [hr]
  have k1 := key W
  have k2 := key X
  unfold blockGauge
  rw [k1, k2]
  exact h X
private def ambientSymmetry (g : TorusIsometry) : CubicSymmetry := ⟨g.axisPerm, g.axisSign, g.offset⟩
private def liftedIsometry (L : ℕ) (g : TorusIsometry) : TorusIsometry :=
  ⟨g.axisPerm, g.axisSign, fun i => (L : ℤ) * g.offset i, g.axisSign_unit⟩
private theorem toTorusSite_actSite [NeZero n] (g : TorusIsometry) (x : (torusFrame L t n).Cell) :
    toTorusSite n (CubicSymmetry.actSite (ambientSymmetry g) (torusFrame L t n).top x) =
      g.mapSite (toTorusSite n x) := by
  unfold CubicSymmetry.actSite
  rw [TopLevelSites.toTorusSite_siteOfCoords top_period]
  funext i
  simp [siteOfInt, TorusIsometry.mapSite, toTorusSite, ambientSymmetry, TopLevelSites.top_sub_depth]
abbrev _root_.YangMills.DeltaSharedProofs.p501220 := @toTorusSite_actSite
private theorem ambient_transports [NeZero n] (g : TorusIsometry) {W W' : TorusField n} (h : g.Transports W W') :
    CubicSymmetry.TransportsField (F := torusFrame L t n) (ambientSymmetry g)
      (readAtLevel (torusFrame L t n) (torusFrame L t n).top W)
      (readAtLevel (torusFrame L t n) (torusFrame L t n).top W') := by
  intro x k
  have hc := h (toTorusSite n x) k
  have hr : ∀ (V : TorusField n) (z : (torusFrame L t n).Cell) (i : Fin 4),
      readAtLevel (torusFrame L t n) (torusFrame L t n).top V z i = V (toTorusSite n z) i := fun _ _ _ => rfl
  unfold linkValue CubicSymmetry.actStep
  by_cases hs : g.axisSign (g.axisPerm.symm k) = 1
  · simp only [ambientSymmetry, hs, decide_true, if_true] at hc ⊢
    rw [hr, hr]
    have := toTorusSite_actSite (L := L) (t := t) g x
    simp only [ambientSymmetry] at this
    rw [this]
    exact hc
  · simp only [ambientSymmetry, hs, decide_false, if_false, Bool.false_eq_true] at hc ⊢
    rw [hr, hr, sub_eq_add_neg, TopLevelSites.toTorusSite_add top_period, TopLevelSites.toTorusSite_neg top_period,
      TopLevelSites.toTorusSite_unitStep top_period]
    have := toTorusSite_actSite (L := L) (t := t) g x
    simp only [ambientSymmetry] at this
    rw [this, ← sub_eq_add_neg]
    exact hc
abbrev _root_.YangMills.DeltaSharedProofs.p501285 := @ambient_transports
private theorem toTorusSite_actSite_depth [NeZero (n * L)] (g : TorusIsometry)
    (x : (torusFrame L t n).Site (torusFrame L t n).depth) :
    toTorusSite (n * L) (CubicSymmetry.actSite (ambientSymmetry g) (torusFrame L t n).depth x) =
      (liftedIsometry L g).mapSite (toTorusSite (n * L) x) := by
  have hpow : (((torusFrame L t n).blockSide : ℕ) : ℤ) ^ ((torusFrame L t n).top - (torusFrame L t n).depth) =
      (L : ℤ) := by
    rw [TopLevelSites.top_sub_depth]
    simp [torusFrame]
  unfold CubicSymmetry.actSite
  rw [TopLevelSites.toTorusSite_siteOfCoords depth_period, hpow]
  funext i
  simp [siteOfInt, TorusIsometry.mapSite, liftedIsometry, toTorusSite, ambientSymmetry]
private theorem lifted_transports [NeZero (n * L)] (g : TorusIsometry)
    (Wl Wi : (torusFrame L t n).GaugeField (torusFrame L t n).depth)
    (hst : ∀ (x : (torusFrame L t n).Site (torusFrame L t n).depth) (k : Fin 4),
      linkValue Wi (CubicSymmetry.actSite (ambientSymmetry g) (torusFrame L t n).depth x)
        (CubicSymmetry.actStep (ambientSymmetry g) k) = Wl x k) :
    (liftedIsometry L g).Transports (restrictToTorus (n * L) Wl) (restrictToTorus (n * L) Wi) := by
  intro x k
  set y : (torusFrame L t n).Site (torusFrame L t n).depth :=
    torusSiteInFrame (torusFrame L t n) (torusFrame L t n).depth x with hy
  have hyx : toTorusSite (n * L) y = x := TopLevelSites.toTorusSite_torusSiteInFrame depth_period x
  have hc := hst y k
  have hs := toTorusSite_actSite_depth (L := L) (t := t) (n := n) g y
  rw [hyx] at hs
  have hv : restrictToTorus (n * L) Wl x k = Wl y k := rfl
  unfold linkValue CubicSymmetry.actStep at hc
  show if (liftedIsometry L g).axisSign ((liftedIsometry L g).axisPerm.symm k) = 1 then
      restrictToTorus (n * L) Wi ((liftedIsometry L g).mapSite x) ((liftedIsometry L g).axisPerm.symm k) =
        restrictToTorus (n * L) Wl x k
    else (restrictToTorus (n * L) Wi ((liftedIsometry L g).mapSite x -
        TorusFields.unitStep (n * L) ((liftedIsometry L g).axisPerm.symm k))
      ((liftedIsometry L g).axisPerm.symm k))⁻¹ = restrictToTorus (n * L) Wl x k
  have hperm : (liftedIsometry L g).axisPerm = g.axisPerm := rfl
  have hsign : (liftedIsometry L g).axisSign = g.axisSign := rfl
  have hap : (ambientSymmetry g).perm = g.axisPerm := rfl
  have has : (ambientSymmetry g).sign = g.axisSign := rfl
  rw [hperm, hsign]
  rw [hap, has] at hc
  by_cases hg : g.axisSign (g.axisPerm.symm k) = 1
  · simp only [hg, decide_true, if_true] at hc ⊢
    rw [← hs, restrictToTorus_apply depth_period, hv]
    exact hc
  · simp only [hg, decide_false, if_false, Bool.false_eq_true] at hc ⊢
    have e : (liftedIsometry L g).mapSite x - TorusFields.unitStep (n * L) (g.axisPerm.symm k) =
        toTorusSite (n * L) (CubicSymmetry.actSite (ambientSymmetry g) (torusFrame L t n).depth y -
          BlockAverages.unitStep (torusFrame L t n).depth (g.axisPerm.symm k)) := by
      rw [sub_eq_add_neg (CubicSymmetry.actSite (ambientSymmetry g) (torusFrame L t n).depth y),
        TopLevelSites.toTorusSite_add depth_period, TopLevelSites.toTorusSite_neg depth_period,
        TopLevelSites.toTorusSite_unitStep depth_period, hs, ← sub_eq_add_neg]
    rw [e, restrictToTorus_apply depth_period, hv]
    exact hc
private theorem isMinimizer_transport [NeZero n] (hEn : BlockEnergySymmetric) (hL : Odd L) {a : ℝ}
    (g : TorusIsometry) {V V' : TorusField n} (hC : g.Transports V V')
    {W : (torusFrame L t n).GaugeField (torusFrame L t n).depth} (h : IsEnergyMinimizerOver a L t n V W) :
    IsEnergyMinimizerOver a L t n V' (transportField (ambientSymmetry g) W) := by
  have hall : ∀ z : (torusFrame L t n).Cell, z ∈ finiteCells (torusFrame L t n) :=
    TopLevelSites.mem_finiteCells fun _ => Nat.pos_of_ne_zero (NeZero.ne n)
  obtain ⟨he, hon, -⟩ := hEn (torusFrame L t n) a _ _ _ _ (ambientSymmetry g) hL ⟨g.axisSign_unit, fun _ _ => rfl⟩
    (fun _ => ⟨fun _ => hall _, fun _ => hall _⟩) (ambient_transports g hC)
  intro W'
  obtain ⟨X, rfl⟩ := hon W'
  rw [he, he]
  exact h X
end Top
section Carried
variable {n : ℕ} [NeZero n]
private theorem transported_link (g : TorusIsometry) {W W' : TorusField n} (h : g.Transports W W') (y : TorusSite n)
    (j : Fin 4) :
    ∃ (x : TorusSite n) (k : Fin 4), W' y j = W x k ∨ (W' y j)⁻¹ = W x k := by
  have surj : ∀ y : TorusSite n, ∃ x, g.mapSite x = y := by
    intro y
    refine ⟨fun m => ((g.axisSign (g.axisPerm.symm m) : ℤ) : ZMod n) *
      (y (g.axisPerm.symm m) - ((g.offset (g.axisPerm.symm m) : ℤ) : ZMod n)), ?_⟩
    funext i
    simp only [TorusIsometry.mapSite, Equiv.symm_apply_apply]
    have : ((g.axisSign i : ℤ) : ZMod n) * ((g.axisSign i : ℤ) : ZMod n) = 1 := by
      rcases g.axisSign_unit i with e | e <;> simp [e]
    rw [← mul_assoc, this]
    ring
  by_cases hs : g.axisSign j = 1
  · obtain ⟨x, hx⟩ := surj y
    have := h x (g.axisPerm j)
    simp only [Equiv.symm_apply_apply, hs, if_true, hx] at this
    exact ⟨x, g.axisPerm j, Or.inl this⟩
  · obtain ⟨x, hx⟩ := surj (y + TorusFields.unitStep n j)
    have := h x (g.axisPerm j)
    simp only [Equiv.symm_apply_apply, hs, if_false, hx, add_sub_cancel_right] at this
    exact ⟨x, g.axisPerm j, Or.inr this⟩
abbrev _root_.YangMills.SharedProofs.p7027 := @transported_link
private theorem transported_near_one (g : TorusIsometry) {W W' : TorusField n} (h : g.Transports W W') {ε : ℝ}
    (hW : ∀ x i, ‖((W x i : UnitQuaternion) : ℍ[ℝ]) - 1‖ < ε) (y : TorusSite n) (j : Fin 4) :
    ‖((W' y j : UnitQuaternion) : ℍ[ℝ]) - 1‖ < ε := by
  obtain ⟨x, k, e | e⟩ := transported_link g h y j
  · rw [e]
    exact hW x k
  · have := hW x k
    rwa [← e, norm_inv_sub_one] at this
end Carried
section Chart
variable {m : ℕ} [NeZero m]
private abbrev LinkIndex (m : ℕ) : Type := TorusBond m × Fin 3
private def linkIndexEquiv (m : ℕ) [NeZero m] : LinkIndex m ≃ Fin (Fintype.card (LinkIndex m)) := Fintype.equivFin _
private def imaginaryUnit (k : Fin 3) : imaginaryQuaternions := toImaginary (EuclideanSpace.single k 1)
private def allLinks (m : ℕ) [NeZero m] (l : Fin (Fintype.card (LinkIndex m))) : TorusBond m :=
  ((linkIndexEquiv m).symm l).1
private def allDirections (m : ℕ) [NeZero m] (l : Fin (Fintype.card (LinkIndex m))) : imaginaryQuaternions :=
  imaginaryUnit ((linkIndexEquiv m).symm l).2
private def logCoords (W : TorusField m) (l : Fin (Fintype.card (LinkIndex m))) : ℝ :=
  localLog ((W ((linkIndexEquiv m).symm l).1.1 ((linkIndexEquiv m).symm l).1.2 : UnitQuaternion) : ℍ[ℝ])
    ((linkIndexEquiv m).symm l).2
private theorem sum_imaginaryUnit (v : ImaginaryCoord) : ∑ k, v k • imaginaryUnit k = toImaginary v := by apply _root_.YangMills.Construction.FreeBondMoves.sum_smul_toImaginary_coordUnit <;> assumption
private theorem sum_allLinks (w : TorusBond m → ImaginaryCoord) (b : TorusBond m) :
    (∑ l, if allLinks m l = b then (w (allLinks m l) ((linkIndexEquiv m).symm l).2) • allDirections m l else 0) =
      toImaginary (w b) := by
  classical
  have h1 := Equiv.sum_comp (linkIndexEquiv m).symm
    (fun q : LinkIndex m => if q.1 = b then (w q.1 q.2) • imaginaryUnit q.2 else 0)
  have h2 : (∑ l, if allLinks m l = b then (w (allLinks m l) ((linkIndexEquiv m).symm l).2) • allDirections m l else 0) =
      ∑ l, (fun q : LinkIndex m => if q.1 = b then (w q.1 q.2) • imaginaryUnit q.2 else 0)
        ((linkIndexEquiv m).symm l) := rfl
  rw [h2, h1, Fintype.sum_prod_type, Finset.sum_eq_single b]
  · simp only [if_true]
    exact sum_imaginaryUnit (w b)
  · intro b' _ hb
    simp [hb]
  · simp
private theorem tendsto_link (x : TorusSite m) (i : Fin 4) :
    Tendsto (fun W : TorusField m => ((W x i : UnitQuaternion) : ℍ[ℝ])) (𝓝 (trivialField m)) (𝓝 1) := by
  have hc : Continuous fun W : TorusField m => ((W x i : UnitQuaternion) : ℍ[ℝ]) :=
    continuous_subtype_val.comp ((continuous_apply i).comp (continuous_apply x))
  have := hc.tendsto (trivialField m)
  simpa [trivialField] using this
private theorem tendsto_of_links {α : Type*} {l : Filter α} {f : α → TorusField m}
    (h : ∀ x i, Tendsto (fun a => ((f a x i : UnitQuaternion) : ℍ[ℝ])) l (𝓝 1)) :
    Tendsto f l (𝓝 (trivialField m)) := by
  refine tendsto_pi_nhds.mpr fun x => tendsto_pi_nhds.mpr fun i => ?_
  rw [tendsto_subtype_rng]
  simpa [trivialField] using h x i
private theorem perturb_logCoords :
    ∀ᶠ W in 𝓝 (trivialField m), perturb (allLinks m) (allDirections m) (logCoords W) (trivialField m) = W := by
  have hb : ∀ᶠ W in 𝓝 (trivialField m), ∀ (x : TorusSite m) (i : Fin 4),
      NormedSpace.exp (imaginaryCLM (localLog ((W x i : UnitQuaternion) : ℍ[ℝ]))) =
        ((W x i : UnitQuaternion) : ℍ[ℝ]) := by
    rw [eventually_all]
    intro x
    rw [eventually_all]
    intro i
    filter_upwards [(tendsto_link x i).eventually eventually_exp_localLog] with W hW
    exact hW (W x i).2
  filter_upwards [hb] with W hW
  funext x i
  have hs := sum_allLinks (m := m) (fun b => localLog ((W b.1 b.2 : UnitQuaternion) : ℍ[ℝ])) (x, i)
  have e : perturb (allLinks m) (allDirections m) (logCoords W) (trivialField m) x i =
      expUnit (∑ l, if allLinks m l = (x, i) then (logCoords W l) • allDirections m l else 0) * 1 := rfl
  rw [e, mul_one]
  have e2 : (∑ l, if allLinks m l = (x, i) then (logCoords W l) • allDirections m l else 0) =
      toImaginary (localLog ((W x i : UnitQuaternion) : ℍ[ℝ])) := hs
  rw [e2]
  apply Subtype.ext
  exact hW x i
private theorem logCoords_trivial : logCoords (trivialField m) = 0 := by
  funext l
  simp [logCoords, trivialField, localLog_one]
private theorem tendsto_logCoords : Tendsto (logCoords (m := m)) (𝓝 (trivialField m)) (𝓝 0) := by
  refine tendsto_pi_nhds.mpr fun l => ?_
  have hc : Tendsto localLog (𝓝 (1 : ℍ[ℝ])) (𝓝 0) := by
    have := contDiffAt_localLog.continuousAt.tendsto
    rwa [localLog_one] at this
  have h2 := hc.comp (tendsto_link ((linkIndexEquiv m).symm l).1.1 ((linkIndexEquiv m).symm l).1.2)
  have h3 := ((EuclideanSpace.proj (𝕜 := ℝ) ((linkIndexEquiv m).symm l).2 : ImaginaryCoord →L[ℝ] ℝ).continuous.tendsto
    0).comp h2
  rw [map_zero] at h3
  exact h3
private theorem perturb_zero_trivial {k : ℕ} (c : Fin k → TorusBond m) (X : Fin k → imaginaryQuaternions) :
    perturb c X 0 (trivialField m) = trivialField m := by
  funext x i
  have e : expUnit (0 : imaginaryQuaternions) = 1 := by
    apply Subtype.ext
    simp [expUnit]
  simp [perturb, trivialField, e]
end Chart
section Through
variable {L n : ℕ} [NeZero n] [NeZero (n * L)] {p : (n : ℕ) → TorusField n → TorusField (n * L)}
private theorem tendsto_through (H₀ : p n (trivialField n) = trivialField (n * L))
    (hsm : ∀ (k : ℕ) (c : Fin k → TorusBond n) (X : Fin k → imaginaryQuaternions) (b : TorusBond (n * L)),
      ContDiffAt ℝ 2 (fun σ : Fin k → ℝ => ((p n (perturb c X σ (trivialField n)) b.1 b.2 : UnitQuaternion) : ℍ[ℝ])) 0) :
    Tendsto (p n) (𝓝 (trivialField n)) (𝓝 (trivialField (n * L))) := by
  refine tendsto_of_links fun x i => ?_
  have hc := (hsm _ (allLinks n) (allDirections n) (x, i)).continuousAt.tendsto
  have h1 := hc.comp tendsto_logCoords
  have e0 : ((p n (perturb (allLinks n) (allDirections n) 0 (trivialField n)) x i : UnitQuaternion) : ℍ[ℝ]) = 1 := by
    rw [perturb_zero_trivial, H₀]
    simp [trivialField]
  rw [e0] at h1
  refine h1.congr' ?_
  filter_upwards [perturb_logCoords (m := n)] with V hV
  simp only [Function.comp]
  rw [hV]
private theorem contDiffAt_through {H : GaugeTotal} (ht : IsGaugeTotalAt H (n * L))
    (H₀ : p n (trivialField n) = trivialField (n * L))
    {k : ℕ} (c : Fin k → TorusBond n) (X : Fin k → imaginaryQuaternions)
    (hsm : ∀ b : TorusBond (n * L),
      ContDiffAt ℝ 2 (fun σ : Fin k → ℝ => ((p n (perturb c X σ (trivialField n)) b.1 b.2 : UnitQuaternion) : ℍ[ℝ])) 0) :
    ContDiffAt ℝ 2 (fun σ : Fin k → ℝ => H (n * L) (p n (perturb c X σ (trivialField n)))) 0 := by
  have hq0 : p n (perturb c X 0 (trivialField n)) = trivialField (n * L) := by
    rw [perturb_zero_trivial, H₀]
  have hτ : ContDiffAt ℝ 2 (fun σ : Fin k → ℝ => logCoords (p n (perturb c X σ (trivialField n)))) 0 := by
    rw [contDiffAt_pi]
    intro l
    have hb := hsm (allLinks (n * L) l)
    have hlog : ContDiffAt ℝ 2 localLog
        ((p n (perturb c X 0 (trivialField n)) (allLinks (n * L) l).1 (allLinks (n * L) l).2 : UnitQuaternion) :
          ℍ[ℝ]) := by
      rw [hq0]
      simpa [trivialField] using contDiffAt_localLog.of_le (by norm_num)
    have h1 : ContDiffAt ℝ 2 (fun σ : Fin k → ℝ => localLog
        ((p n (perturb c X σ (trivialField n)) (allLinks (n * L) l).1 (allLinks (n * L) l).2 : UnitQuaternion) :
          ℍ[ℝ])) 0 :=
      ContDiffAt.comp (g := localLog) 0 hlog hb
    have hpj : ContDiff ℝ 2 (fun v : ImaginaryCoord => v ((linkIndexEquiv (n * L)).symm l).2) :=
      (EuclideanSpace.proj (𝕜 := ℝ) ((linkIndexEquiv (n * L)).symm l).2 : ImaginaryCoord →L[ℝ] ℝ).contDiff
    exact ContDiffAt.comp (g := fun v : ImaginaryCoord => v ((linkIndexEquiv (n * L)).symm l).2) 0 hpj.contDiffAt h1
  have hc := ht.contDiffAt_perturb _ (allLinks (n * L)) (allDirections (n * L))
  have h00 : logCoords (p n (perturb c X 0 (trivialField n))) = 0 := by
    rw [hq0, logCoords_trivial]
  have hcomp : ContDiffAt ℝ 2 (fun σ : Fin k → ℝ => H (n * L) (perturb (allLinks (n * L)) (allDirections (n * L))
      (logCoords (p n (perturb c X σ (trivialField n)))) (trivialField (n * L)))) 0 :=
    ContDiffAt.comp
      (g := fun σ' => H (n * L) (perturb (allLinks (n * L)) (allDirections (n * L)) σ' (trivialField (n * L)))) 0
      (by rw [h00]; exact hc) hτ
  refine hcomp.congr_of_eventuallyEq ?_
  have hqt : Tendsto (fun σ : Fin k → ℝ => p n (perturb c X σ (trivialField n))) (𝓝 0) (𝓝 (trivialField (n * L))) := by
    refine tendsto_of_links fun x i => ?_
    have := (hsm (x, i)).continuousAt.tendsto
    rw [hq0] at this
    simpa [trivialField] using this
  filter_upwards [hqt.eventually perturb_logCoords] with σ hσ
  rw [hσ]
end Through
section Main
variable {a ρ : ℝ} {L t n : ℕ} [NeZero n] [NeZero (n * L)] {H : GaugeTotal}
private def MinimizerUnique (a ρ : ℝ) (L t n : ℕ) (V : TorusField n) : Prop :=
  (∃ w, IsMinimizingChart a (finiteCells (torusFrame L t n))
    (readAtLevel (torusFrame L t n) (torusFrame L t n).top V) ρ w) ∧
  ∀ W, IsEnergyMinimizerOver a L t n V W → ∃ γ : (torusFrame L t n).Site (torusFrame L t n).depth → UnitQuaternion,
    (∀ z : (torusFrame L t n).Cell, γ (cellCentre _ z) = 1) ∧
    W = BlockAverages.gaugeTransform γ (fieldAboveFrame (F := torusFrame L t n) true a ρ 0
      (readAtLevel (torusFrame L t n) (torusFrame L t n).top V) 0)
private theorem torusSiteInFrame_zero :
    torusSiteInFrame (torusFrame L t n) (torusFrame L t n).depth (0 : TorusSite (n * L)) =
      cellCentre (F := torusFrame L t n) (torusFrame L t n).depth 0 := by
  funext i
  simp [torusSiteInFrame, cellCentre, siteOfCoords, siteCoords]
private theorem eventually_total_minimizer (ht : IsGaugeTotalAt H (n * L))
    (hp : Tendsto (minimizerOnFinerTorus a ρ L t n) (𝓝 (trivialField n)) (𝓝 (trivialField (n * L))))
    (hOne : ∀ᶠ V in 𝓝 (trivialField n), MinimizerUnique a ρ L t n V) :
    ∃ U ∈ 𝓝 (trivialField (n * L)), ∀ᶠ V in 𝓝 (trivialField n), ∀ W, IsEnergyMinimizerOver a L t n V W →
      restrictToTorus (n * L) W ∈ U →
      H (n * L) (minimizerOnFinerTorus a ρ L t n V) = H (n * L) (restrictToTorus (n * L) W) := by
  obtain ⟨U, hU, hUp⟩ := eventually_gauge_between ht.gauge_invariant_near
  refine ⟨U, hU, ?_⟩
  filter_upwards [hOne, hp.eventually hU] with V h1 h2 W hW hWU
  obtain ⟨γ, hγ, e⟩ := h1.2 W hW
  have hY : restrictToTorus (n * L) W =
      TorusFields.gaugeTransform (fun x => γ (torusSiteInFrame (torusFrame L t n) (torusFrame L t n).depth x))
        (minimizerOnFinerTorus a ρ L t n V) := by
    rw [e]
    exact restrictToTorus_gaugeTransform depth_period γ _
  have h0 : (fun x => γ (torusSiteInFrame (torusFrame L t n) (torusFrame L t n).depth x)) (0 : TorusSite (n * L)) = 1 := by
    show γ (torusSiteInFrame (torusFrame L t n) (torusFrame L t n).depth 0) = 1
    rw [torusSiteInFrame_zero]
    exact hγ 0
  have h3 : H (n * L) (TorusFields.gaugeTransform
      (fun x => γ (torusSiteInFrame (torusFrame L t n) (torusFrame L t n).depth x))
      (minimizerOnFinerTorus a ρ L t n V)) = H (n * L) (minimizerOnFinerTorus a ρ L t n V) := hUp _ hWU _ h2 _ h0 hY
  rw [hY]
  exact h3.symm
private theorem continuous_torusGauge {m : ℕ} :
    Continuous fun p : (TorusSite m → UnitQuaternion) × TorusField m => TorusFields.gaugeTransform p.1 p.2 := by
  refine continuous_pi fun x => continuous_pi fun i => ?_
  show Continuous fun p : (TorusSite m → UnitQuaternion) × TorusField m =>
    p.1 x * p.2 x i * (p.1 (x + TorusFields.unitStep m i))⁻¹
  have c1 : Continuous fun p : (TorusSite m → UnitQuaternion) × TorusField m => p.1 x :=
    (continuous_apply x).comp continuous_fst
  have c2 : Continuous fun p : (TorusSite m → UnitQuaternion) × TorusField m => p.2 x i :=
    (continuous_apply i).comp ((continuous_apply x).comp continuous_snd)
  have c3 : Continuous fun p : (TorusSite m → UnitQuaternion) × TorusField m => p.1 (x + TorusFields.unitStep m i) :=
    (continuous_apply (x + TorusFields.unitStep m i)).comp continuous_fst
  exact continuous_unitMul.comp ((continuous_unitMul.comp (c1.prodMk c2)).prodMk (continuous_unitInv.comp c3))
abbrev _root_.YangMills.SharedProofs.p21641 := @continuous_torusGauge
private theorem tendsto_torusGauge {m : ℕ} :
    Tendsto (fun p : (TorusSite m → UnitQuaternion) × TorusField m => TorusFields.gaugeTransform p.1 p.2)
      (𝓝 ((1 : TorusSite m → UnitQuaternion), trivialField m)) (𝓝 (trivialField m)) := by
  have h := (continuous_torusGauge (m := m)).tendsto ((1 : TorusSite m → UnitQuaternion), trivialField m)
  have e : TorusFields.gaugeTransform (1 : TorusSite m → UnitQuaternion) (trivialField m) = trivialField m := by
    funext x i
    simp [TorusFields.gaugeTransform, trivialField]
  simpa only [e] using h
abbrev _root_.YangMills.SharedProofs.p29867 := @tendsto_torusGauge
private theorem tendsto_constGauge {m : ℕ} (g : UnitQuaternion) :
    Tendsto (fun V : TorusField m => TorusFields.gaugeTransform (fun _ => g) V) (𝓝 (trivialField m))
      (𝓝 (trivialField m)) := by
  have hc : Continuous fun V : TorusField m => TorusFields.gaugeTransform (fun _ => g) V := by
    refine continuous_pi fun x => continuous_pi fun i => ?_
    show Continuous fun V : TorusField m => g * V x i * g⁻¹
    have c2 : Continuous fun V : TorusField m => V x i := (continuous_apply i).comp (continuous_apply x)
    exact continuous_unitMul.comp ((continuous_unitMul.comp (continuous_const.prodMk c2)).prodMk continuous_const)
  have h : Tendsto (fun V : TorusField m => TorusFields.gaugeTransform (fun _ => g) V) (𝓝 (trivialField m))
      (𝓝 (TorusFields.gaugeTransform (fun _ => g) (trivialField m))) :=
    hc.tendsto (trivialField m)
  have e : TorusFields.gaugeTransform (fun _ : TorusSite m => g) (trivialField m) = trivialField m := by
    funext x i
    simp [TorusFields.gaugeTransform, trivialField]
  rwa [e] at h
abbrev _root_.YangMills.SharedProofs.p78957 := @tendsto_constGauge
private def liftedGauge (L t : ℕ) {n : ℕ} (u : TorusSite n → UnitQuaternion) : TorusSite (n * L) → UnitQuaternion :=
  fun x => blockGauge L t u (torusSiteInFrame (torusFrame L t n) (torusFrame L t n).depth x)
private theorem tendsto_liftedGauge :
    Tendsto (liftedGauge L t (n := n)) (𝓝 (1 : TorusSite n → UnitQuaternion)) (𝓝 (1 : TorusSite (n * L) → UnitQuaternion)) := by
  have hc : Continuous (liftedGauge L t (n := n)) := continuous_pi fun x => continuous_apply _
  exact hc.tendsto 1
private theorem total_gauge_invariant (hcov : gaugeCovarianceStatement) (hL : Odd L) (h2 : 2 ≤ n)
    (ht : IsGaugeTotalAt H (n * L))
    (hp : Tendsto (minimizerOnFinerTorus a ρ L t n) (𝓝 (trivialField n)) (𝓝 (trivialField (n * L))))
    (hOne : ∀ᶠ V in 𝓝 (trivialField n), MinimizerUnique a ρ L t n V) :
    ∀ᶠ p : (TorusSite n → UnitQuaternion) × TorusField n in 𝓝 ((1 : TorusSite n → UnitQuaternion), trivialField n),
      H (n * L) (minimizerOnFinerTorus a ρ L t n (TorusFields.gaugeTransform p.1 p.2)) =
        H (n * L) (minimizerOnFinerTorus a ρ L t n p.2) := by
  obtain ⟨U, hU, hR⟩ := eventually_total_minimizer ht hp hOne
  have hfst : Tendsto (fun p : (TorusSite n → UnitQuaternion) × TorusField n => p.1)
      (𝓝 ((1 : TorusSite n → UnitQuaternion), trivialField n)) (𝓝 1) :=
    continuous_fst.tendsto _
  have hsnd : Tendsto (fun p : (TorusSite n → UnitQuaternion) × TorusField n => p.2)
      (𝓝 ((1 : TorusSite n → UnitQuaternion), trivialField n)) (𝓝 (trivialField n)) :=
    continuous_snd.tendsto _
  have hT2 : Tendsto (fun p : (TorusSite n → UnitQuaternion) × TorusField n =>
        (liftedGauge L t p.1, minimizerOnFinerTorus a ρ L t n p.2))
      (𝓝 ((1 : TorusSite n → UnitQuaternion), trivialField n))
      (𝓝 ((1 : TorusSite (n * L) → UnitQuaternion), trivialField (n * L))) :=
    (tendsto_liftedGauge.comp hfst).prodMk_nhds (hp.comp hsnd)
  have hT3 := tendsto_torusGauge.comp hT2
  filter_upwards [tendsto_torusGauge.eventually hR, hT2.eventually ht.gauge_invariant_near, hT3.eventually hU,
    hsnd.eventually hOne] with p r1 r2 r3 r4
  have hl := isMinimizer_gaugeTransform hcov hL h2 p.1 (frameMinimizer_isMinimizer r4.1)
  have hf : restrictToTorus (n * L) (BlockAverages.gaugeTransform (blockGauge L t p.1) (frameMinimizer a ρ L t n p.2)) =
      TorusFields.gaugeTransform (liftedGauge L t p.1) (minimizerOnFinerTorus a ρ L t n p.2) :=
    restrictToTorus_gaugeTransform depth_period _ _
  have h3 : restrictToTorus (n * L) (BlockAverages.gaugeTransform (blockGauge L t p.1) (frameMinimizer a ρ L t n p.2)) ∈
      U := by
    rw [hf]
    exact r3
  rw [r1 _ hl h3, hf]
  exact r2
private theorem total_constant_invariant (hcov : gaugeCovarianceStatement) (hL : Odd L) (h2 : 2 ≤ n)
    (ht : IsGaugeTotalAt H (n * L))
    (hp : Tendsto (minimizerOnFinerTorus a ρ L t n) (𝓝 (trivialField n)) (𝓝 (trivialField (n * L))))
    (hOne : ∀ᶠ V in 𝓝 (trivialField n), MinimizerUnique a ρ L t n V) (g : UnitQuaternion) :
    ∀ᶠ V in 𝓝 (trivialField n), H (n * L) (minimizerOnFinerTorus a ρ L t n (TorusFields.gaugeTransform (fun _ => g) V)) =
      H (n * L) (minimizerOnFinerTorus a ρ L t n V) := by
  obtain ⟨U, hU, hR⟩ := eventually_total_minimizer ht hp hOne
  have hT3 := (tendsto_constGauge (m := n * L) g).comp hp
  filter_upwards [(tendsto_constGauge (m := n) g).eventually hR, hp.eventually (ht.constant_gauge_invariant g),
    hT3.eventually hU, hOne] with V r1 r2 r3 r4
  have hl := isMinimizer_gaugeTransform hcov hL h2 (fun _ => g) (frameMinimizer_isMinimizer r4.1)
  have hf : restrictToTorus (n * L)
      (BlockAverages.gaugeTransform (blockGauge L t fun _ : TorusSite n => g) (frameMinimizer a ρ L t n V)) =
      TorusFields.gaugeTransform (fun _ => g) (minimizerOnFinerTorus a ρ L t n V) :=
    restrictToTorus_gaugeTransform depth_period _ _
  have h3 : restrictToTorus (n * L)
      (BlockAverages.gaugeTransform (blockGauge L t fun _ : TorusSite n => g) (frameMinimizer a ρ L t n V)) ∈ U := by
    rw [hf]
    exact r3
  rw [r1 _ hl h3, hf]
  exact r2
private theorem total_isometry_invariant (hEn : BlockEnergySymmetric) (hL : Odd L)
    (ht : IsGaugeTotalAt H (n * L))
    (hp : Tendsto (minimizerOnFinerTorus a ρ L t n) (𝓝 (trivialField n)) (𝓝 (trivialField (n * L))))
    (hOne : ∀ᶠ V in 𝓝 (trivialField n), MinimizerUnique a ρ L t n V) (g : TorusIsometry) :
    ∀ᶠ V in 𝓝 (trivialField n), ∀ V' : TorusField n, g.Transports V V' →
      H (n * L) (minimizerOnFinerTorus a ρ L t n V') = H (n * L) (minimizerOnFinerTorus a ρ L t n V) := by
  obtain ⟨U, hU, hR⟩ := eventually_total_minimizer ht hp hOne
  obtain ⟨ε, hε, hε'⟩ := field_mem_of_near_trivial hR
  obtain ⟨δ, hδ, hδ'⟩ := field_mem_of_near_trivial hU
  filter_upwards [eventually_links_near_one hε, hp.eventually (eventually_links_near_one hδ),
    hp.eventually (ht.isometry_invariant (liftedIsometry L g)), hOne]
    with V v1 v2 v3 v4 V' hC
  have hall : ∀ z : (torusFrame L t n).Cell, z ∈ finiteCells (torusFrame L t n) :=
    TopLevelSites.mem_finiteCells fun _ => Nat.pos_of_ne_zero (NeZero.ne n)
  have r := hε' V' (transported_near_one g hC v1)
  have hl := isMinimizer_transport hEn hL g hC (frameMinimizer_isMinimizer v4.1)
  obtain ⟨-, -, hst⟩ := hEn (torusFrame L t n) a _ _ _ _ (ambientSymmetry g) hL ⟨g.axisSign_unit, fun _ _ => rfl⟩
    (fun _ => ⟨fun _ => hall _, fun _ => hall _⟩) (ambient_transports g hC)
  have hcar := lifted_transports g (frameMinimizer a ρ L t n V) _ (hst (frameMinimizer a ρ L t n V))
  rw [r _ hl (hδ' _ (transported_near_one (liftedIsometry L g) hcar v2))]
  exact v3 _ hcar
end Main
end MinimizerTotal
open MinimizerTotal in
theorem gaugeTotalAtMinimizer_of_blockMap (hBlock : MinimizerIsBlockMap) (hOne : MinimizerUniqueUpToGauge)
    (hEn : BlockEnergySymmetric) (hcov : gaugeCovarianceStatement) :
    GaugeTotalAtMinimizer := by
  intro a ha L hL t ρ h0 h1 H hH
  obtain ⟨P, Pl, hM⟩ := hBlock a ha L hL t ρ h0 h1
  have hLpos : 0 < L := hL.1.pos
  have hTend : Tendsto (fun n : ℕ => n * L) atTop atTop :=
    tendsto_atTop_mono (fun n => Nat.le_mul_of_pos_right n hLpos) tendsto_id
  filter_upwards [hM.map_trivial, hM.contDiffAt_perturb, hOne a ha L hL t ρ h0 h1, hTend.eventually hH,
    eventually_ge_atTop 2] with n f1 f2 f3 f4 f5
  have : NeZero n := ⟨by omega⟩
  have : NeZero (n * L) := ⟨Nat.mul_ne_zero (by omega) hLpos.ne'⟩
  have hp : Tendsto (minimizerOnFinerTorus a ρ L t n) (𝓝 (trivialField n)) (𝓝 (trivialField (n * L))) :=
    tendsto_through (p := minimizerOnFinerTorus a ρ L t) f1 f2
  exact
    { contDiffAt_perturb := fun k c X => contDiffAt_through (p := minimizerOnFinerTorus a ρ L t) f4 f1 c X (f2 k c X)
      gauge_invariant_near := total_gauge_invariant hcov hL.1 f5 f4 hp f3
      constant_gauge_invariant := total_constant_invariant hcov hL.1 f5 f4 hp f3
      isometry_invariant := total_isometry_invariant hEn hL.1 f4 hp f3 }
end RunningCouplingSlope
end YangMills.Construction
end
