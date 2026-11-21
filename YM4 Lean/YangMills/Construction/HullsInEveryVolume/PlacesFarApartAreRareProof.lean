import YangMills.Construction.ClusterExpansionOfAStep.ImageStateIsSmoothOffItsHullProof
import YangMills.Construction.ClusterExpansionOfAStep.OmGrowsLikeALogarithm
import YangMills.Construction.ClusterExpansionOfAStep.ZetaOfAGroundIsBorelProof
import YangMills.Construction.FreeEnergiesOfTheFlow.MassOfTheFlow
import YangMills.Construction.FreeEnergiesOfTheFlow.ThePastIsFreeGivenTheStateProof
import YangMills.Construction.HullsInEveryVolume.BadBlocksArePaid
import YangMills.Construction.HullsInEveryVolume.FreeEnergyBeforeTheFloor
import YangMills.Construction.HullsInEveryVolume.PlacesFarApartAreRare
import YangMills.Construction.HullsInEveryVolume.TheArrayPaysItsLumps
import YangMills.Construction.HullsInEveryVolume.TheStatesOfTheChainHaveTheirDensities
import YangMills.Construction.ResponseInTheExpansion.SizeOfTheMeanOfABond
import YangMills.Construction.ResponseInTheExpansion.WhatTheChainReadsIsBorel
import Mathlib
set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped Quaternion
namespace YangMills.Construction.HullsInEveryVolume
open TorusFields TorusLumps StepSettings RenormalizationStepParameters StepCosts StepReturn StepMarks WeightedResponses BlockAverages
  LumpContours ColdStepAtMirrorFrames FreeEnergies HullTrees TopLevelSites ClusterExpansionOfAStep ResponseInTheExpansion
section Action
private theorem minimalAction_nonneg {F : BlockFrame} {a : ℝ} (ha : 0 ≤ a) (S : Finset F.Cell) :
    ∀ (j : ℕ) (X : F.GaugeField j), 0 ≤ minimalAction a S j X
  | 0, U => by
    unfold minimalAction BlockAverages.wilsonAction
    refine Finset.sum_nonneg fun p _ => ?_
    have h := sq_norm_unitQuaternion_sub_one (plaquetteHolonomy U p)
    nlinarith [sq_nonneg ‖((plaquetteHolonomy U p : UnitQuaternion) : ℍ[ℝ]) - 1‖]
  | j + 1, V => by
    refine Real.iInf_nonneg fun W => ?_
    refine add_nonneg (minimalAction_nonneg ha S j W)
      (mul_nonneg ha (Finset.sum_nonneg fun c _ => ?_))
    unfold blockFit
    have h1 : (contourAverage W c * ((V c.1 c.2)⁻¹ : UnitQuaternion)).re ≤
        ‖contourAverage W c * ((V c.1 c.2)⁻¹ : UnitQuaternion)‖ := by
      have h2 : (contourAverage W c * ((V c.1 c.2)⁻¹ : UnitQuaternion)).re ^ 2 ≤
          ‖contourAverage W c * ((V c.1 c.2)⁻¹ : UnitQuaternion)‖ ^ 2 := by
        rw [sq ‖_‖, ← Quaternion.normSq_eq_norm_mul_self, Quaternion.normSq_def']
        nlinarith [sq_nonneg (contourAverage W c * ((V c.1 c.2)⁻¹ : UnitQuaternion)).imI,
          sq_nonneg (contourAverage W c * ((V c.1 c.2)⁻¹ : UnitQuaternion)).imJ,
          sq_nonneg (contourAverage W c * ((V c.1 c.2)⁻¹ : UnitQuaternion)).imK]
      exact (abs_le_of_sq_le_sq' h2 (norm_nonneg _)).2
    rw [norm_mul, WeightedResponses.norm_unitQuaternion, mul_one] at h1
    linarith
private theorem actionAtLevel_nonneg {n : ℕ} [NeZero n] {a : ℝ} (ha : 0 ≤ a) (L : ℕ) :
    ∀ (t : ℕ) (S : Finset (TorusSite n)) (W : TorusField n), 0 ≤ actionAtLevel a L t S W
  | 0, S, W => Finset.sum_nonneg fun p _ => plaquetteEnergy_nonneg W _ _ _
  | t + 1, S, W => minimalAction_nonneg ha _ _ _
end Action
section Hull
variable {ℓ : TorusLumps.StepParameters} {t : ℕ} {x : ℝ} {D : TorusFunctional} {f : LocalDensity} {n : ℕ} [NeZero n]
  {Λ : LabelSpace} {Dq : (n : ℕ) → TorusField n → (Y : Finset (TorusSite n)) → (Y → Λ.Ω) → ℝ}
  {Φ : (n : ℕ) → TorusField n → (Y : Finset (TorusSite n)) → (Y → Λ.Ω) → Finset (TorusSite n) → ℝ}
  {φ : (n : ℕ) → TorusSite n → TorusField n → (Y : Finset (TorusSite n)) → (Y → Λ.Ω) → ℝ}
open Classical in
private theorem sum_integral_labelWeight (hh : HullExpansion ℓ t x D f Λ Dq Φ φ) (hs : IsBlockTorusSide ℓ n)
    (W : TorusField n) (hD0 : 0 ≤ D n W) :
    ∑ Y ∈ Finset.univ.filter (IsHullState ℓ (clusterRange x) W),
      ∫ ω, Dq n W Y ω ∂(Measure.pi fun _ : Y => Λ.μ) = D n W := by
  have hsum := hh.sum n hs W
  have hone : ∀ Y ∈ Finset.univ.filter (IsHullState ℓ (clusterRange x) W),
      ∫ ω, Dq n W Y ω ∂(Measure.pi fun _ : Y => Λ.μ) =
        (∫⁻ ω, ENNReal.ofReal (Dq n W Y ω) ∂(Measure.pi fun _ : Y => Λ.μ)).toReal := by
    intro Y hY
    have hYh : IsHullState ℓ (clusterRange x) W Y := (Finset.mem_filter.mp hY).2
    have hm : Measurable fun ω : Y → Λ.Ω => Dq n W Y ω := by
      have h2 := ((hh.borel n hs Y).1).comp (measurable_prodMk_left (x := W))
      have e : (fun ω : Y → Λ.Ω => Dq n W Y ω) = (fun p : TorusField n × (Y → Λ.Ω) =>
          if IsHullState ℓ (clusterRange x) p.1 Y then Dq n p.1 Y p.2 else 0) ∘ Prod.mk W := by
        funext ω
        show _ = if IsHullState ℓ (clusterRange x) W Y then Dq n W Y ω else 0
        rw [if_pos hYh]
      rw [e]
      exact h2
    exact integral_eq_lintegral_of_nonneg_ae
      (Filter.Eventually.of_forall fun ω => hh.nonneg n hs W Y ω hYh) hm.aestronglyMeasurable
  rw [Finset.sum_congr rfl hone, ← ENNReal.toReal_sum, hsum, ENNReal.toReal_ofReal hD0]
  intro Y hY
  have h1 := Finset.single_le_sum (f := fun Y : Finset (TorusSite n) =>
    ∫⁻ ω, ENNReal.ofReal (Dq n W Y ω) ∂(Measure.pi fun _ : Y => Λ.μ))
    (fun _ _ => zero_le) hY
  rw [hsum] at h1
  exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top h1
end Hull
section Field
variable {ℓ : TorusLumps.StepParameters}
private theorem stageState_fst (T : StageTower ℓ) : ∀ (u n : ℕ) [NeZero n] (w : MarkedSample ℓ u n),
    (stageState T u n w).1 = topField ℓ u n w
  | 0, _, _, _ => rfl
  | _ + 1, _, _, _ => rfl
private theorem measurable_topField (s n : ℕ) : Measurable (topField ℓ s n) := by apply _root_.YangMills.SharedProofs.p12845 <;> assumption
private structure StageFacts (T : StageTower ℓ) (β Z Cm : ℝ) (u n : ℕ) [NeZero n] : Prop where
  admissible : ℓ.Admissible
  blockSide : IsBlockTorusSide ℓ n
  expansions : (T.stage u).toStepSetup.HasExpansions
  one_le_coupling : 1 ≤ (T.stage u).coupling
  range_ge : 4 * ℓ.n₀ + 2 ^ 16 ≤ clusterRange (T.stage u).coupling
  functional_nonneg : ∀ W : TorusField n, 0 ≤ (T.stage u).functional n W
  partition_pos : 0 < Z
  partition_lower : Real.log ((T.stage u).functional n (trivialField n)) - Cm * (n : ℝ) ^ 4 ≤ Real.log Z
  states : ∀ F : StageState T u n → ℝ, Measurable F → (∃ C : ℝ, ∀ q, |F q| ≤ C) →
    ∫ w, F (stageState T u n w) ∂(markedSampleLaw T β u n) =
      (∫ W, (open Classical in ∑ Y ∈ Finset.univ.filter (IsHullState ℓ (stageRange T u) W),
          ∫ ω, F (W, ⟨Y, ω⟩) * (T.stage u).labelWeight n W Y ω
            ∂(Measure.pi fun _ : Y => (T.stage u).labels.μ)) ∂(fieldHaar n)) / Z
variable {T : StageTower ℓ} {β Z Cm : ℝ} {u n : ℕ} [NeZero n]
open Classical in
private theorem integral_topField (hL : StageFacts T β Z Cm u n) (G : TorusField n → ℝ) (hG : Measurable G)
    (hb : ∃ C : ℝ, ∀ W, |G W| ≤ C) :
    ∫ w, G (topField ℓ u n w) ∂(markedSampleLaw T β u n) =
      (∫ W, G W * (T.stage u).functional n W ∂(fieldHaar n)) / Z := by
  obtain ⟨C, hC⟩ := hb
  have h := hL.states (fun q => G q.1) (hG.comp measurable_fst) ⟨C, fun q => hC _⟩
  simp only [stageState_fst] at h
  rw [h]
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall fun W => ?_)
  have hH := hL.expansions.2
  have hs := hL.blockSide
  show ∑ Y ∈ Finset.univ.filter (IsHullState ℓ (stageRange T u) W),
      ∫ ω, G W * (T.stage u).labelWeight n W Y ω ∂(Measure.pi fun _ : Y => (T.stage u).labels.μ) =
        G W * (T.stage u).functional n W
  simp only [integral_const_mul]
  rw [← Finset.mul_sum]
  congr 1
  exact sum_integral_labelWeight hH hs W (hL.functional_nonneg W)
private theorem card_torusSite (n : ℕ) [NeZero n] : (Fintype.card (TorusSite n) : ℝ) = (n : ℝ) ^ 4 := by
  simp [ZMod.card]
open Classical in
private theorem integral_topField_le (hPay : functionalBoundByLumpPrice) (hL : StageFacts T β Z Cm u n)
    (G : TorusField n → ℝ) (hG : Measurable G) (hb : ∃ C : ℝ, ∀ W, |G W| ≤ C) (h0 : ∀ W, 0 ≤ G W) (Kb : ℝ)
    (hKb : 0 ≤ Kb)
    (he : ∀ W, G W * Real.exp (-((T.stage u).coupling * actionAtLevel ℓ.coupling ℓ.side (T.stage u).depth
        (Finset.univ \ thickening lumpRange (torusHotSites ℓ W)) W) -
        (T.stage u).coupling * ℓ.κ * ℓ.threshold ^ 2 * ((torusHotLumps ℓ W).card : ℝ)) ≤ Kb) :
    ∫ w, G (topField ℓ u n w) ∂(markedSampleLaw T β u n) ≤
      Real.exp ((Real.log 2 + 2 * ℓ.E + Cm) * (n : ℝ) ^ 4) * Kb := by
  have hfit := hL.admissible
  have hC := hL.expansions.1
  have hH := hL.expansions.2
  have hx0 : 0 < (T.stage u).coupling := by linarith [hL.one_le_coupling]
  have hE := hfit.E_ge
  have hs := hL.blockSide
  have hflat : IsCold ℓ.threshold (trivialField n) := fun z μ ν _ => by
    simp only [curvature, holonomy_trivialField]
    simpa using hfit.σ_pos
  have hn₀ : ℓ.n₀ ≤ n := by
    have h1 := hs.2
    have h2 : 1 * ℓ.n₀ ≤ ℓ.side * ℓ.n₀ := Nat.mul_le_mul_right _ (by have := hfit.L_ge; omega)
    omega
  have hD1 : 0 < (T.stage u).functional n (trivialField n) := hC.positive n hn₀ _ hflat
  rw [integral_topField hL G hG hb]
  set D1 := (T.stage u).functional n (trivialField n) with hD1def
  set N : ℝ := (Fintype.card (TorusSite n) : ℝ) with hN
  have hNn : N = (n : ℝ) ^ 4 := card_torusSite n
  set c₁ : ℝ := (2 : ℝ) ^ Fintype.card (TorusSite n) * (D1 * Real.exp (2 * ℓ.E * N)) with hc₁
  have hc₁0 : 0 ≤ c₁ := by positivity
  have hpt : ∀ W, G W * (T.stage u).functional n W ≤ c₁ * Kb := by
    intro W
    have hbd := hPay _ _ _ _ _ _ _ _ _ hfit hE hx0 hL.range_ge hC hH n hs W
    set e : ℝ := Real.exp (-((T.stage u).coupling * actionAtLevel ℓ.coupling ℓ.side (T.stage u).depth
        (Finset.univ \ thickening lumpRange (torusHotSites ℓ W)) W) -
        (T.stage u).coupling * ℓ.κ * ℓ.threshold ^ 2 * ((torusHotLumps ℓ W).card : ℝ)) with hedef
    have e1 : (2 : ℝ) ^ Fintype.card (TorusSite n) * (D1 * Real.exp (2 * ℓ.E * N -
        (T.stage u).coupling * actionAtLevel ℓ.coupling ℓ.side (T.stage u).depth
          (Finset.univ \ thickening lumpRange (torusHotSites ℓ W)) W -
        (T.stage u).coupling * ℓ.κ * ℓ.threshold ^ 2 * ((torusHotLumps ℓ W).card : ℝ))) = c₁ * e := by
      have e0 : Real.exp (2 * ℓ.E * N -
          (T.stage u).coupling * actionAtLevel ℓ.coupling ℓ.side (T.stage u).depth
            (Finset.univ \ thickening lumpRange (torusHotSites ℓ W)) W -
          (T.stage u).coupling * ℓ.κ * ℓ.threshold ^ 2 * ((torusHotLumps ℓ W).card : ℝ)) =
            Real.exp (2 * ℓ.E * N) * e := by
        rw [hedef, ← Real.exp_add]
        congr 1
        ring
      rw [e0, hc₁]
      ring
    rw [e1] at hbd
    calc G W * (T.stage u).functional n W ≤ G W * (c₁ * e) := mul_le_mul_of_nonneg_left hbd (h0 W)
      _ = c₁ * (G W * e) := by ring
      _ ≤ c₁ * Kb := mul_le_mul_of_nonneg_left (he W) hc₁0
  have hint : ∫ W, G W * (T.stage u).functional n W ∂(fieldHaar n) ≤ c₁ * Kb := by
    have h1 := integral_mono_of_nonneg (μ := fieldHaar n) (f := fun W => G W * (T.stage u).functional n W)
      (g := fun _ => c₁ * Kb)
      (Filter.Eventually.of_forall fun W => mul_nonneg (h0 W) (hL.functional_nonneg W))
      (integrable_const _) (Filter.Eventually.of_forall hpt)
    simpa using h1
  have hZl : D1 * Real.exp (-(Cm * (n : ℝ) ^ 4)) ≤ Z := by
    have h1 := Real.exp_le_exp.mpr hL.partition_lower
    rw [Real.exp_log hL.partition_pos, Real.exp_sub, Real.exp_log hD1, div_eq_mul_inv, ← Real.exp_neg] at h1
    exact h1
  have hden : 0 < D1 * Real.exp (-(Cm * (n : ℝ) ^ 4)) := by positivity
  have hpow2 : (2 : ℝ) ^ Fintype.card (TorusSite n) = Real.exp (N * Real.log 2) := by
    rw [← Real.rpow_natCast, Real.rpow_def_of_pos (by norm_num), mul_comm]
  calc (∫ W, G W * (T.stage u).functional n W ∂(fieldHaar n)) / Z ≤ (c₁ * Kb) / Z :=
        div_le_div_of_nonneg_right hint hL.partition_pos.le
    _ ≤ (c₁ * Kb) / (D1 * Real.exp (-(Cm * (n : ℝ) ^ 4))) :=
        div_le_div_of_nonneg_left (by positivity) hden hZl
    _ = Real.exp ((Real.log 2 + 2 * ℓ.E + Cm) * (n : ℝ) ^ 4) * Kb := by
        rw [div_eq_iff hden.ne']
        have e2 : Real.exp ((Real.log 2 + 2 * ℓ.E + Cm) * (n : ℝ) ^ 4) * Real.exp (-(Cm * (n : ℝ) ^ 4)) =
            Real.exp (N * Real.log 2) * Real.exp (2 * ℓ.E * N) := by
          rw [← Real.exp_add, ← Real.exp_add]
          congr 1
          rw [hNn]
          ring
        rw [hc₁, hpow2]
        linear_combination (-(D1 * Kb)) * e2
end Field
section Count
variable {ℓ : TorusLumps.StepParameters} {n : ℕ} [NeZero n]
open Classical in
private theorem card_le_card_torusHotLumps (hfit : ℓ.Admissible) (hLn : ℓ.side ∣ n) {W : TorusField n} {r : ℕ}
    {A : Finset (TorusSite n)} (hA : Separated (2 ^ 17 + 8 * r) A)
    (hh : ∀ z ∈ A, ContainsHotPlaquette ℓ W (box z (4 * r))) :
    A.card ≤ (torusHotLumps ℓ W).card := by
  have hch : ∀ z ∈ A, ∃ v : TorusSite n, supDist v z ≤ 4 * r ∧ torusLumpOf ℓ v ∈ torusHotLumps ℓ W := by
    intro z hz
    obtain ⟨p, hp, hs⟩ := hh z hz
    simp only [TorusFields.plaquettesIn, Finset.mem_filter, Finset.mem_univ, true_and] at hp
    obtain ⟨h1, h2⟩ := hp
    refine ⟨p.1, ?_, (mem_torusHotLumps_iff ℓ hfit hLn W _).mpr
      ⟨p.1, p.2.1, p.2.2, h1, hs, p.1, base_mem_plaquetteVertices _ _ _, rfl⟩⟩
    obtain ⟨x, hx, hd⟩ := (mem_thickening _ _ _).mp (h2 _ (base_mem_plaquetteVertices _ _ _))
    rw [Finset.mem_singleton.mp hx] at hd
    exact hd
  choose! v hv1 hv2 using hch
  refine Finset.card_le_card_of_injOn (fun z => torusLumpOf ℓ (v z)) hv2 ?_
  intro z hz z' hz' he
  by_contra hne
  have h1 := hA z hz z' hz' hne
  obtain ⟨mid, hmid⟩ := exists_centre_of_torusLumpOf hfit hLn (v z)
  have ha : v z ∈ torusLumpOf ℓ (v z) := mem_torusLumpOf_self _
  have hb : v z' ∈ torusLumpOf ℓ (v z) := by
    have : torusLumpOf ℓ (v z) = torusLumpOf ℓ (v z') := he
    rw [this]
    exact mem_torusLumpOf_self _
  have h2 := hmid _ ha
  have h3 := hmid _ hb
  have h4 := hv1 z hz
  have h5 := hv1 z' hz'
  have t1 := supDist_triangle z (v z) z'
  have t2 := supDist_triangle (v z) mid z'
  have t3 := supDist_triangle mid (v z') z'
  have e1 := supDist_comm z (v z)
  have e2 := supDist_comm mid (v z')
  have e3 := supDist_comm (v z') z'
  omega
open Classical in
private theorem card_le_card_blocks {m : ℕ} (L : ℕ) {bad : Finset (TorusSite m × Fin 4)} (blk : TorusSite m → TorusSite n)
    {r : ℕ} {A : Finset (TorusSite n)} (hA : Separated (2 ^ 17 + 8 * r) A)
    (hh : ∀ z ∈ A, ∃ b ∈ bad, blk b.1 ∈ box z (4 * r)) :
    A.card ≤ (bad.image fun e => blk e.1).card := by
  have hch : ∀ z ∈ A, ∃ v ∈ bad.image (fun e => blk e.1), supDist v z ≤ 4 * r := by
    intro z hz
    obtain ⟨b, hb, hin⟩ := hh z hz
    refine ⟨blk b.1, Finset.mem_image.mpr ⟨b, hb, rfl⟩, ?_⟩
    obtain ⟨x, hx, hd⟩ := (mem_thickening _ _ _).mp hin
    rw [Finset.mem_singleton.mp hx] at hd
    exact hd
  choose! v hv1 hv2 using hch
  refine Finset.card_le_card_of_injOn v hv1 ?_
  intro z hz z' hz' he
  by_contra hne
  have h1 := hA z hz z' hz' hne
  have h4 := hv2 z hz
  have h5 := hv2 z' hz'
  have he' : v z = v z' := he
  rw [← he'] at h5
  have t1 := supDist_triangle z (v z) z'
  have e1 := supDist_comm z (v z)
  omega
end Count
section Later
variable {A D : Type} [MeasurableSpace A] [MeasurableSpace D] {μ : Measure A} {ρ : Measure D}
  [SFinite ρ] {w : A × D → ℝ}
private theorem withDensity_snd_preimage (hw : Measurable w) {B : Set D} (hB : MeasurableSet B) :
    ((μ.prod ρ).withDensity fun u => ENNReal.ofReal (w u)) (Prod.snd ⁻¹' B) =
      ∫⁻ a, ∫⁻ d in B, ENNReal.ofReal (w (a, d)) ∂ρ ∂μ := by
  have hS : MeasurableSet ((Prod.snd : A × D → D) ⁻¹' B) := measurable_snd hB
  rw [withDensity_apply _ hS, ← lintegral_indicator hS,
    lintegral_prod _ (hw.ennreal_ofReal.indicator hS).aemeasurable]
  refine lintegral_congr fun a => ?_
  rw [← lintegral_indicator hB]
  refine lintegral_congr fun d => ?_
  by_cases hd : d ∈ B
  · rw [Set.indicator_of_mem hd, Set.indicator_of_mem (show (a, d) ∈ (Prod.snd : A × D → D) ⁻¹' B from hd)]
  · rw [Set.indicator_of_notMem hd,
      Set.indicator_of_notMem (show (a, d) ∉ (Prod.snd : A × D → D) ⁻¹' B from hd)]
end Later
section Marks
variable (R : StepSetup) {n : ℕ} [NeZero n]
private theorem markLaw_nonneg (hc : IsCutoff R.ballRadius R.barrierFn) (W : TorusField (n * R.params.side))
    (V : TorusField n) (bad : Finset (TorusBond (n * R.params.side))) :
    0 ≤ markLaw R W V bad := by apply _root_.YangMills.SharedProofs.p19776 <;> assumption
private theorem sum_markLaw (W : TorusField (n * R.params.side)) (V : TorusField n) :
    ∑ bad : Finset (TorusBond (n * R.params.side)), markLaw R W V bad = 1 := by apply _root_.YangMills.SharedProofs.p2142 <;> assumption
private theorem markLaw_le_one (hc : IsCutoff R.ballRadius R.barrierFn) (W : TorusField (n * R.params.side))
    (V : TorusField n) (bad : Finset (TorusBond (n * R.params.side))) :
    markLaw R W V bad ≤ 1 := by apply _root_.YangMills.SharedProofs.p42074 <;> assumption
end Marks
section Outcomes
variable {ℓ : TorusLumps.StepParameters}
private instance (L n : ℕ) : DiscreteMeasurableSpace (BaseChoice L n) :=
  ⟨fun _ => MeasurableSpace.measurableSet_top⟩
private instance (m : ℕ) : DiscreteMeasurableSpace (BondSet m) :=
  ⟨fun _ => MeasurableSpace.measurableSet_top⟩
private instance (m : ℕ) [NeZero m] : Fintype (BondSet m) := inferInstanceAs (Fintype (Finset (TorusBond m)))
private theorem measurable_of_stepOutcome {X : Type} [MeasurableSpace X] {n : ℕ} [NeZero n]
    {f : X × StepOutcome ℓ n → ℝ}
    (h : ∀ (b : BaseChoice ℓ.side n) (bad : BondSet (n * ℓ.side)),
      Measurable fun p : X × TorusField n => f (p.1, (b, p.2, bad))) : Measurable f := by apply _root_.YangMills.SharedProofs.p21057 <;> assumption
private instance (ℓ : TorusLumps.StepParameters) (n : ℕ) [NeZero n] :
    IsFiniteMeasure (stepReferenceMeasure ℓ n) := by
  unfold stepReferenceMeasure
  infer_instance
private theorem integral_stepReferenceMeasure {n : ℕ} [NeZero n] {g : StepOutcome ℓ n → ℝ} (hg : Measurable g)
    {C : ℝ} (hC : ∀ d, |g d| ≤ C) :
    ∫ d, g d ∂(stepReferenceMeasure ℓ n) =
      ∑ b : BaseChoice ℓ.side n, ∫ V : TorusField n, ∑ bad : BondSet (n * ℓ.side), g (b, V, bad) ∂(fieldHaar n) := by
  have hI : Integrable g (stepReferenceMeasure ℓ n) :=
    Integrable.of_bound hg.aestronglyMeasurable C
      (Filter.Eventually.of_forall fun d => by rw [Real.norm_eq_abs]; exact hC d)
  unfold stepReferenceMeasure at hI ⊢
  rw [integral_prod _ hI, integral_count]
  refine Finset.sum_congr rfl fun b _ => ?_
  have hIb : Integrable (fun y : TorusField n × BondSet (n * ℓ.side) => g (b, y))
      ((fieldHaar n).prod (Measure.count : Measure (BondSet (n * ℓ.side)))) :=
    Integrable.of_bound (hg.comp measurable_prodMk_left).aestronglyMeasurable C
      (Filter.Eventually.of_forall fun d => by rw [Real.norm_eq_abs]; exact hC _)
  rw [integral_prod _ hIb]
  refine integral_congr_ae (Filter.Eventually.of_forall fun V => ?_)
  exact integral_count _
end Outcomes
section OneStep
variable (R : StepSetup) {n : ℕ} [NeZero n]
private theorem measurable_stepOutcomeDensity (hS : StepTransitionDensityBounds)
    (hB : ∀ bad : Finset (TorusBond (n * R.params.side)),
      Measurable fun p : TorusField (n * R.params.side) × TorusField n => markLaw R p.1 p.2 bad) :
    Measurable fun p : TorusField (n * R.params.side) × StepOutcome R.params n => stepOutcomeDensity R p.1 p.2 :=
  measurable_of_stepOutcome fun b bad => ((hS R.params R.coupling n).1 b).mul (hB bad)
end OneStep
section Mass
variable (R : StepSetup) {n : ℕ} [NeZero n]
private theorem stepBaseLaw_nonneg (W : TorusField (n * R.params.side)) (b : BaseChoice R.params.side n) :
    0 ≤ baseLaw (R := R) W b := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.SmoothOffHull.baseLaw_nonneg_of_field <;> assumption
private theorem sum_stepBaseLaw_le (W : TorusField (n * R.params.side)) :
    ∑ b : BaseChoice R.params.side n, baseLaw (R := R) W b ≤ 1 := by
  classical
  unfold baseLaw
  rw [Finset.sum_ite_mem Finset.univ, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul]
  by_cases h0 : ((baseChoices R.params (readAtLevel (stepBlockFrame R.params.side n) 0 W)).card : ℝ) = 0
  · simp [h0]
  · rw [mul_one_div, div_self h0]
private theorem stepBaseLaw_le_one (W : TorusField (n * R.params.side)) (b : BaseChoice R.params.side n) :
    baseLaw (R := R) W b ≤ 1 :=
  (Finset.single_le_sum (f := fun b => baseLaw (R := R) W b) (fun b _ => stepBaseLaw_nonneg R W b)
    (Finset.mem_univ b)).trans (sum_stepBaseLaw_le R W)
private theorem measurable_curry_slice {X Y : Type} [MeasurableSpace X] [MeasurableSpace Y] {f : X → Y → ℝ}
    (h : Measurable fun p : X × Y => f p.1 p.2) (x : X) : Measurable (f x) :=
  h.comp measurable_prodMk_left
private theorem measurable_of_unit_prod {Y : Type} [MeasurableSpace Y] {f : Y → ℝ}
    (h : Measurable fun p : Unit × Y => f p.2) : Measurable f :=
  h.comp (Measurable.prodMk (measurable_const (a := ())) measurable_id)
private def baseMarkWeight (W : TorusField (n * R.params.side)) (d : StepOutcome R.params n) : ℝ :=
  baseLaw (R := R) W d.1 * markLaw R W d.2.1 d.2.2
private theorem lintegral_baseMarkWeight_le (hc : IsCutoff R.ballRadius R.barrierFn)
    (hB : ∀ bad : Finset (TorusBond (n * R.params.side)),
      Measurable fun p : TorusField (n * R.params.side) × TorusField n => markLaw R p.1 p.2 bad)
    (W : TorusField (n * R.params.side)) :
    ∫⁻ d, ENNReal.ofReal (baseLaw (R := R) W d.1 * markLaw R W d.2.1 d.2.2) ∂(stepReferenceMeasure R.params n) ≤ 1 := by
  have hq0 : ∀ d, 0 ≤ baseMarkWeight R W d := fun d =>
    mul_nonneg (stepBaseLaw_nonneg R W _) (markLaw_nonneg R hc _ _ _)
  have hq1 : ∀ d, |baseMarkWeight R W d| ≤ 1 := fun d => by
    rw [abs_of_nonneg (hq0 d)]
    exact mul_le_one₀ (stepBaseLaw_le_one R W _) (markLaw_nonneg R hc _ _ _) (markLaw_le_one R hc _ _ _)
  have hslice : ∀ (b : BaseChoice R.params.side n) (bad : BondSet (n * R.params.side)),
      Measurable fun p : Unit × TorusField n => baseMarkWeight R W (b, p.2, bad) := by
    intro b bad
    have h1 : Measurable (fun V : TorusField n => markLaw R W V bad) :=
      measurable_curry_slice (f := fun W V => markLaw R W V bad) (hB bad) W
    exact (h1.comp measurable_snd).const_mul (baseLaw (R := R) W b)
  have hqm : Measurable (baseMarkWeight R W) := by
    have h1 := measurable_of_stepOutcome (ℓ := R.params) (n := n) (X := Unit)
      (f := fun p => baseMarkWeight R W p.2) hslice
    exact measurable_of_unit_prod h1
  have hI : Integrable (baseMarkWeight R W) (stepReferenceMeasure R.params n) :=
    Integrable.of_bound hqm.aestronglyMeasurable 1
      (Filter.Eventually.of_forall fun d => by rw [Real.norm_eq_abs]; exact hq1 d)
  have hl : ∫⁻ d, ENNReal.ofReal (baseLaw (R := R) W d.1 * markLaw R W d.2.1 d.2.2) ∂(stepReferenceMeasure R.params n) =
      ∫⁻ d, ENNReal.ofReal (baseMarkWeight R W d) ∂(stepReferenceMeasure R.params n) := rfl
  rw [hl, ← ofReal_integral_eq_lintegral_ofReal hI (Filter.Eventually.of_forall hq0),
    integral_stepReferenceMeasure hqm hq1]
  have e : ∀ (b : BaseChoice R.params.side n) (V : TorusField n),
      ∑ bad : BondSet (n * R.params.side), baseMarkWeight R W (b, V, bad) = baseLaw (R := R) W b := by
    intro b V
    have hs : ∑ bad : BondSet (n * R.params.side), markLaw R W V bad = 1 := sum_markLaw R W V
    show ∑ bad : BondSet (n * R.params.side), baseLaw (R := R) W b * markLaw R W V bad = _
    exact (Finset.mul_sum _ _ _).symm.trans (by rw [hs, mul_one])
  simp only [e, integral_const, probReal_univ, one_smul]
  exact ENNReal.ofReal_le_one.mpr (sum_stepBaseLaw_le R W)
end Mass
section Kernels
variable {ℓ : TorusLumps.StepParameters} {n : ℕ} [NeZero n]
private theorem prod_bondKernel_le (hK : BondKernelProperties) (x Cl : ℝ) (W : TorusField (n * ℓ.side))
    (V : TorusField n) (b : BaseChoice ℓ.side n)
    (hom : ∀ e : TorusBond n, logPartitionGap (ℓ.coupling * x * meanNorm ℓ W b e) ≤ Cl) :
    ∏ c : (stepBlockFrame ℓ.side n).Cell × Fin 4,
        bondKernel ℓ x (readAtLevel (stepBlockFrame ℓ.side n) 0 W) (readAtLevel (stepBlockFrame ℓ.side n) 1 V) b c ≤
      Real.exp (-(ℓ.coupling * x) * ∑ e : TorusBond n, bondFit ℓ W V b e + 4 * (n : ℝ) ^ 4 * Cl) := by
  have hk := fun c =>
    hK.2 ℓ x n (readAtLevel (stepBlockFrame ℓ.side n) 0 W) (readAtLevel (stepBlockFrame ℓ.side n) 1 V) b c
  have hexp : ∏ c : (stepBlockFrame ℓ.side n).Cell × Fin 4,
        bondKernel ℓ x (readAtLevel (stepBlockFrame ℓ.side n) 0 W) (readAtLevel (stepBlockFrame ℓ.side n) 1 V) b c =
      Real.exp (∑ c : (stepBlockFrame ℓ.side n).Cell × Fin 4,
        Real.log (bondKernel ℓ x (readAtLevel (stepBlockFrame ℓ.side n) 0 W)
          (readAtLevel (stepBlockFrame ℓ.side n) 1 V) b c)) := by
    rw [Real.exp_sum]
    exact Finset.prod_congr rfl fun c _ => (Real.exp_log (hk c).1).symm
  have hper : ∀ i, (stepBlockFrame ℓ.side n).period 1 i = n :=
    period_top_of_extent (F := stepBlockFrame ℓ.side n) (fun _ => rfl)
  have hb : Function.Bijective (torusSiteInFrame (n := n) (stepBlockFrame ℓ.side n) 1) :=
    Function.bijective_iff_has_inverse.mpr ⟨toTorusSite n, fun u => toTorusSite_torusSiteInFrame hper u,
      fun z => torusSiteInFrame_toTorusSite hper z⟩
  have hbp : Function.Bijective
      (Prod.map (torusSiteInFrame (n := n) (stepBlockFrame ℓ.side n) 1) (id : Fin 4 → Fin 4)) :=
    hb.prodMap Function.bijective_id
  have hlog : ∑ c : (stepBlockFrame ℓ.side n).Cell × Fin 4,
        Real.log (bondKernel ℓ x (readAtLevel (stepBlockFrame ℓ.side n) 0 W)
          (readAtLevel (stepBlockFrame ℓ.side n) 1 V) b c) =
      ∑ e : TorusBond n, (-(ℓ.coupling * x) * bondFit ℓ W V b e +
        logPartitionGap (ℓ.coupling * x * meanNorm ℓ W b e)) := by
    symm
    refine Fintype.sum_bijective _ hbp _ _ fun e => ?_
    exact (hk _).2.1.symm
  rw [hexp, hlog]
  apply Real.exp_le_exp.mpr
  rw [Finset.sum_add_distrib, ← Finset.mul_sum]
  have h2 := Finset.sum_le_card_nsmul Finset.univ
    (fun e : TorusBond n => logPartitionGap (ℓ.coupling * x * meanNorm ℓ W b e)) Cl (fun e _ => hom e)
  rw [nsmul_eq_mul, Finset.card_univ, Fintype.card_prod, Nat.cast_mul, card_torusSite] at h2
  have h3 : ((Fintype.card (Fin 4) : ℕ) : ℝ) = 4 := by simp
  rw [h3] at h2
  linarith
end Kernels
section BadMass
variable (R : StepSetup) {n : ℕ} [NeZero n]
open Classical in
private def badOutcomes (k : ℕ) : Set (StepOutcome R.params n) :=
  {d | k ≤ (((d.2.2 : Finset (TorusBond (n * R.params.side)))).image fun e => parentBlock R.params.side e.1).card}
private def badOutcomeMass (k : ℕ) (W : TorusField (n * R.params.side)) : ENNReal :=
  ∫⁻ d in badOutcomes R (n := n) k, ENNReal.ofReal (stepOutcomeDensity R W d) ∂(stepReferenceMeasure R.params n)
private theorem measurableSet_badOutcomes (k : ℕ) : MeasurableSet (badOutcomes R (n := n) k) := by
  have h : MeasurableSet {bad : BondSet (n * R.params.side) | k ≤ (by classical exact
      ((bad : Finset (TorusBond (n * R.params.side))).image fun e => parentBlock R.params.side e.1).card)} :=
    MeasurableSpace.measurableSet_top
  exact (measurable_snd.comp measurable_snd) h
open Classical in
private theorem badOutcomeMass_mul_le (hc : IsCutoff R.ballRadius R.barrierFn)
    (hB : ∀ bad : Finset (TorusBond (n * R.params.side)),
      Measurable fun p : TorusField (n * R.params.side) × TorusField n => markLaw R p.1 p.2 bad)
    (k : ℕ) (W : TorusField (n * R.params.side)) (e Kk : ℝ) (he : 0 ≤ e) (hKk : 0 ≤ Kk)
    (hpt : ∀ (b : BaseChoice R.params.side n) (V : TorusField n) (bad : Finset (TorusBond (n * R.params.side))),
      b ∈ baseChoices R.params (readAtLevel (stepBlockFrame R.params.side n) 0 W) → markLaw R W V bad ≠ 0 →
      k ≤ (bad.image fun e => parentBlock R.params.side e.1).card →
      (∏ c : (stepBlockFrame R.params.side n).Cell × Fin 4,
        bondKernel R.params R.coupling (readAtLevel (stepBlockFrame R.params.side n) 0 W)
          (readAtLevel (stepBlockFrame R.params.side n) 1 V) b c) * e ≤ Kk) :
    badOutcomeMass R k W * ENNReal.ofReal e ≤ ENNReal.ofReal Kk := by
  have hbm := measurableSet_badOutcomes R (n := n) k
  have h1 : badOutcomeMass R k W * ENNReal.ofReal e =
      ∫⁻ d in badOutcomes R (n := n) k, ENNReal.ofReal (stepOutcomeDensity R W d) * ENNReal.ofReal e
        ∂(stepReferenceMeasure R.params n) := by
    unfold badOutcomeMass
    exact (lintegral_mul_const' _ _ ENNReal.ofReal_ne_top).symm
  rw [h1]
  have hpw : ∀ d ∈ badOutcomes R (n := n) k, ENNReal.ofReal (stepOutcomeDensity R W d) * ENNReal.ofReal e ≤
      ENNReal.ofReal Kk * ENNReal.ofReal (baseLaw (R := R) W d.1 * markLaw R W d.2.1 d.2.2) := by
    intro d hd
    have hq0 : 0 ≤ baseLaw (R := R) W d.1 * markLaw R W d.2.1 d.2.2 :=
      mul_nonneg (stepBaseLaw_nonneg R W _) (markLaw_nonneg R hc _ _ _)
    have hc0 := markLaw_nonneg R hc W d.2.1 d.2.2
    rw [← ENNReal.ofReal_mul' he, ← ENNReal.ofReal_mul hKk]
    apply ENNReal.ofReal_le_ofReal
    show WeightedResponses.stepTransitionDensity R.params R.coupling W d.1 d.2.1 * markLaw R W d.2.1 d.2.2 * e ≤ _
    by_cases hb : d.1 ∈ baseChoices R.params (readAtLevel (stepBlockFrame R.params.side n) 0 W)
    · unfold WeightedResponses.stepTransitionDensity baseLaw
      rw [if_pos hb, if_pos hb]
      by_cases hz : markLaw R W d.2.1 d.2.2 = 0
      · simp [hz]
      · have hp := hpt d.1 d.2.1 d.2.2 hb hz hd
        have hcard : 0 ≤ 1 / ((baseChoices R.params (readAtLevel (stepBlockFrame R.params.side n) 0 W)).card : ℝ) := by
          positivity
        have hm := mul_le_mul_of_nonneg_left hp (mul_nonneg hcard hc0)
        calc _ = 1 / ((baseChoices R.params (readAtLevel (stepBlockFrame R.params.side n) 0 W)).card : ℝ) *
              markLaw R W d.2.1 d.2.2 *
              ((∏ c : (stepBlockFrame R.params.side n).Cell × Fin 4,
                bondKernel R.params R.coupling (readAtLevel (stepBlockFrame R.params.side n) 0 W)
                  (readAtLevel (stepBlockFrame R.params.side n) 1 d.2.1) d.1 c) * e) := by
              ring
          _ ≤ _ := hm
          _ = _ := by ring
    · have h0 : WeightedResponses.stepTransitionDensity R.params R.coupling W d.1 d.2.1 = 0 := by
        unfold WeightedResponses.stepTransitionDensity
        rw [if_neg hb]
      rw [h0]
      simpa using mul_nonneg hKk hq0
  calc ∫⁻ d in badOutcomes R (n := n) k, ENNReal.ofReal (stepOutcomeDensity R W d) * ENNReal.ofReal e
        ∂(stepReferenceMeasure R.params n)
      ≤ ∫⁻ d in badOutcomes R (n := n) k, ENNReal.ofReal Kk *
          ENNReal.ofReal (baseLaw (R := R) W d.1 * markLaw R W d.2.1 d.2.2) ∂(stepReferenceMeasure R.params n) :=
        setLIntegral_mono' hbm hpw
    _ ≤ ∫⁻ d, ENNReal.ofReal Kk *
          ENNReal.ofReal (baseLaw (R := R) W d.1 * markLaw R W d.2.1 d.2.2) ∂(stepReferenceMeasure R.params n) :=
        setLIntegral_le_lintegral _ _
    _ = ENNReal.ofReal Kk * ∫⁻ d, ENNReal.ofReal (baseLaw (R := R) W d.1 * markLaw R W d.2.1 d.2.2)
          ∂(stepReferenceMeasure R.params n) := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal Kk * 1 := by
        gcongr
        exact lintegral_baseMarkWeight_le R hc hB W
    _ = _ := mul_one _
private theorem measurable_badOutcomeMass (hS : StepTransitionDensityBounds)
    (hB : ∀ bad : Finset (TorusBond (n * R.params.side)),
      Measurable fun p : TorusField (n * R.params.side) × TorusField n => markLaw R p.1 p.2 bad)
    (k : ℕ) : Measurable (badOutcomeMass R (n := n) k) := by
  have h1 := (measurable_stepOutcomeDensity R (n := n) hS hB).ennreal_ofReal
  exact h1.lintegral_prod_right'
private theorem badOutcomeMass_bounded (hS : StepTransitionDensityBounds) (hc : IsCutoff R.ballRadius R.barrierFn)
    (k : ℕ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ W, badOutcomeMass R (n := n) k W ≤ ENNReal.ofReal C := by
  obtain ⟨C₀, hC₀⟩ := (hS R.params R.coupling n).2
  refine ⟨max C₀ 0 * (stepReferenceMeasure R.params n Set.univ).toReal, by positivity, fun W => ?_⟩
  have hw : ∀ d, ENNReal.ofReal (stepOutcomeDensity R W d) ≤ ENNReal.ofReal (max C₀ 0) := by
    intro d
    apply ENNReal.ofReal_le_ofReal
    have hs := hC₀ W d.1 d.2.1
    have hk := markLaw_le_one R hc W d.2.1 d.2.2
    calc stepOutcomeDensity R W d ≤ WeightedResponses.stepTransitionDensity R.params R.coupling W d.1 d.2.1 * 1 :=
          mul_le_mul_of_nonneg_left hk hs.1
      _ ≤ C₀ := by rw [mul_one]; exact hs.2
      _ ≤ _ := le_max_left _ _
  calc badOutcomeMass R (n := n) k W
        ≤ ∫⁻ d, ENNReal.ofReal (stepOutcomeDensity R W d) ∂(stepReferenceMeasure R.params n) :=
        setLIntegral_le_lintegral _ _
    _ ≤ ∫⁻ _, ENNReal.ofReal (max C₀ 0) ∂(stepReferenceMeasure R.params n) := lintegral_mono hw
    _ = ENNReal.ofReal (max C₀ 0) * stepReferenceMeasure R.params n Set.univ := lintegral_const _
    _ = _ := by
      rw [ENNReal.ofReal_mul (le_max_right _ _), ENNReal.ofReal_toReal (measure_ne_top _ _)]
end BadMass
section Chances
variable {ℓ : TorusLumps.StepParameters} {T : StageTower ℓ} {β Z Cm : ℝ}
open Classical in
private theorem hotLumps_probability_le {u n : ℕ} [NeZero n] (hPay : functionalBoundByLumpPrice)
    (hL : StageFacts T β Z Cm u n) (hP : IsProbabilityMeasure (markedSampleLaw T β u n)) (k : ℕ) :
    (markedSampleLaw T β u n).real {w | k ≤ (torusHotLumps ℓ (topField ℓ u n w)).card} ≤
      Real.exp ((Real.log 2 + 2 * ℓ.E + Cm) * (n : ℝ) ^ 4) *
        Real.exp (-((T.stage u).coupling * ℓ.κ * ℓ.threshold ^ 2 * (k : ℝ))) := by
  have hfit := hL.admissible
  have hLn : ℓ.side ∣ n := hL.blockSide.1
  set S : Set (TorusField n) := {W | k ≤ (torusHotLumps ℓ W).card} with hS
  have hSm : MeasurableSet S := by
    have e : S = ⋃ H ∈ {H : Finset (Finset (TorusSite n)) | k ≤ H.card}, {W : TorusField n | torusHotLumps ℓ W = H} := by
      ext W
      simp [hS]
    rw [e]
    exact MeasurableSet.biUnion (Set.to_countable _) fun H _ => measurableSet_torusHotLumps_eq hfit hLn H
  have hx0 : 0 ≤ (T.stage u).coupling := by linarith [hL.one_le_coupling]
  have ha : 0 ≤ ℓ.coupling := by have := hfit.a_ge; linarith
  have hG : Measurable (S.indicator fun _ : TorusField n => (1 : ℝ)) := measurable_const.indicator hSm
  have h1 := integral_topField_le hPay hL (S.indicator fun _ => (1 : ℝ)) hG ⟨1, fun W => by
      by_cases hW : W ∈ S <;> simp [hW]⟩ (fun W => by
      by_cases hW : W ∈ S <;> simp [hW])
    (Real.exp (-((T.stage u).coupling * ℓ.κ * ℓ.threshold ^ 2 * (k : ℝ)))) (Real.exp_pos _).le
    (fun W => by
      by_cases hW : W ∈ S
      · rw [Set.indicator_of_mem hW, one_mul]
        apply Real.exp_le_exp.mpr
        have h2 : 0 ≤ (T.stage u).coupling * actionAtLevel ℓ.coupling ℓ.side (T.stage u).depth
            (Finset.univ \ thickening lumpRange (torusHotSites ℓ W)) W :=
          mul_nonneg hx0 (actionAtLevel_nonneg ha _ _ _ _)
        have hk : (k : ℝ) ≤ ((torusHotLumps ℓ W).card : ℝ) := by exact_mod_cast hW
        have h3 : 0 ≤ (T.stage u).coupling * ℓ.κ * ℓ.threshold ^ 2 := by
          have := hfit.κ_pos
          positivity
        have h4 := mul_le_mul_of_nonneg_left hk h3
        linarith
      · rw [Set.indicator_of_notMem hW, zero_mul]
        exact (Real.exp_pos _).le)
  have e1 : (fun w => S.indicator (fun _ : TorusField n => (1 : ℝ)) (topField ℓ u n w)) =
      (topField ℓ u n ⁻¹' S).indicator fun _ => (1 : ℝ) := rfl
  have hmeas : MeasurableSet (topField ℓ u n ⁻¹' S) := measurable_topField u n hSm
  rw [e1, integral_indicator_const _ hmeas] at h1
  simp only [smul_eq_mul, mul_one] at h1
  exact h1
private theorem badBlocks_measure_le {s n : ℕ} [NeZero n] (hPay : functionalBoundByLumpPrice)
    (hS : StepTransitionDensityBounds) (hL : StageFacts T β Z Cm s (n * ℓ.side))
    (hP : IsProbabilityMeasure (markedSampleLaw T β s (n * ℓ.side)))
    (hc : IsCutoff (T.stage s).toStepSetup.ballRadius (T.stage s).toStepSetup.barrierFn) (hcoin : T.MarksMeasurable)
    (k : ℕ) (Kk : ℝ) (hKk : 0 ≤ Kk)
    (hpt : ∀ (W : TorusField (n * ℓ.side)) (b : BaseChoice ℓ.side n) (V : TorusField n)
      (bad : Finset (TorusBond (n * ℓ.side))),
      b ∈ baseChoices ℓ (readAtLevel (stepBlockFrame ℓ.side n) 0 W) → markLaw (T.stage s).toStepSetup W V bad ≠ 0 →
      (k ≤ (by classical exact (bad.image fun e => parentBlock ℓ.side e.1).card)) →
      (∏ c : (stepBlockFrame ℓ.side n).Cell × Fin 4,
        bondKernel ℓ (T.stage s).coupling (readAtLevel (stepBlockFrame ℓ.side n) 0 W)
          (readAtLevel (stepBlockFrame ℓ.side n) 1 V) b c) *
        Real.exp (-((T.stage s).coupling * actionAtLevel ℓ.coupling ℓ.side (T.stage s).depth
          (Finset.univ \ thickening lumpRange (torusHotSites ℓ W)) W) -
          (T.stage s).coupling * ℓ.κ * ℓ.threshold ^ 2 * ((torusHotLumps ℓ W).card : ℝ)) ≤ Kk) :
    (markedSampleLaw T β (s + 1) n) (Prod.snd ⁻¹' badOutcomes (T.stage s).toStepSetup (n := n) k) ≤
      ENNReal.ofReal (Real.exp ((Real.log 2 + 2 * ℓ.E + Cm) * ((n * ℓ.side : ℕ) : ℝ) ^ 4) * Kk) := by
  have hB : ∀ bad : Finset (TorusBond (n * ℓ.side)),
      Measurable fun p : TorusField (n * ℓ.side) × TorusField n => markLaw (T.stage s).toStepSetup p.1 p.2 bad :=
    fun bad => hcoin s n bad
  have hw1 := measurable_stepOutcomeDensity (T.stage s).toStepSetup (n := n) hS hB
  have hw2 : Measurable fun u : MarkedSample ℓ s (n * ℓ.side) × StepOutcome ℓ n =>
      ((topField ℓ s (n * ℓ.side) u.1, u.2) : TorusField (n * ℓ.side) × StepOutcome ℓ n) :=
    ((measurable_topField s (n * ℓ.side)).comp measurable_fst).prodMk measurable_snd
  have hw := hw1.comp hw2
  have hset := withDensity_snd_preimage (μ := markedSampleLaw T β s (n * ℓ.side)) (ρ := stepReferenceMeasure ℓ n) hw
    (measurableSet_badOutcomes (T.stage s).toStepSetup (n := n) k)
  have hgm := measurable_badOutcomeMass (T.stage s).toStepSetup (n := n) hS hB k
  obtain ⟨Cg, hCg0, hCg⟩ := badOutcomeMass_bounded (T.stage s).toStepSetup (n := n) hS hc k
  set g := badOutcomeMass (T.stage s).toStepSetup (n := n) k with hg
  have hfin : ∀ W, g W ≠ ⊤ := fun W => ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hCg W)
  have hGm : Measurable fun W => (g W).toReal := hgm.ennreal_toReal
  have hGb : ∀ W, |(g W).toReal| ≤ Cg := fun W => by
    rw [abs_of_nonneg ENNReal.toReal_nonneg]
    exact ENNReal.toReal_le_of_le_ofReal hCg0 (hCg W)
  have hchance := integral_topField_le hPay hL (fun W => (g W).toReal) hGm ⟨Cg, hGb⟩
    (fun W => ENNReal.toReal_nonneg) Kk hKk
    (fun W => by
      have he0 := (Real.exp_pos (-((T.stage s).coupling * actionAtLevel ℓ.coupling ℓ.side (T.stage s).depth
        (Finset.univ \ thickening lumpRange (torusHotSites ℓ W)) W) -
        (T.stage s).coupling * ℓ.κ * ℓ.threshold ^ 2 * ((torusHotLumps ℓ W).card : ℝ)))
      have h1 := badOutcomeMass_mul_le (T.stage s).toStepSetup (n := n) hc hB k W _ Kk he0.le hKk (hpt W)
      have h2 := ENNReal.toReal_mono ENNReal.ofReal_ne_top h1
      rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal he0.le, ENNReal.toReal_ofReal hKk] at h2
      exact h2)
  have hI : Integrable (fun a => (g (topField ℓ s (n * ℓ.side) a)).toReal) (markedSampleLaw T β s (n * ℓ.side)) :=
    Integrable.of_bound (hGm.comp (measurable_topField s (n * ℓ.side))).aestronglyMeasurable Cg
      (Filter.Eventually.of_forall fun a => by rw [Real.norm_eq_abs]; exact hGb _)
  have hlint : ∫⁻ a, g (topField ℓ s (n * ℓ.side) a) ∂(markedSampleLaw T β s (n * ℓ.side)) =
      ENNReal.ofReal (∫ a, (g (topField ℓ s (n * ℓ.side) a)).toReal ∂(markedSampleLaw T β s (n * ℓ.side))) := by
    rw [ofReal_integral_eq_lintegral_ofReal hI (Filter.Eventually.of_forall fun a => ENNReal.toReal_nonneg)]
    refine lintegral_congr fun a => ?_
    rw [ENNReal.ofReal_toReal (hfin _)]
  have hmain : (markedSampleLaw T β (s + 1) n) (Prod.snd ⁻¹' badOutcomes (T.stage s).toStepSetup (n := n) k) =
      ∫⁻ a, g (topField ℓ s (n * ℓ.side) a) ∂(markedSampleLaw T β s (n * ℓ.side)) := hset
  rw [hmain, hlint]
  exact ENNReal.ofReal_le_ofReal hchance
end Chances
section Flow
variable {ℓ : TorusLumps.StepParameters}
private theorem clusterRange_mono {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) : clusterRange x ≤ clusterRange y := by apply _root_.YangMills.Construction.WilsonExpansion.clusterRange_mono <;> assumption
private theorem le_clusterRange {k : ℕ} {y : ℝ} (hy : (k : ℝ) ^ 100 ≤ y) : k ≤ clusterRange y := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.BlockActivityMeasurability.le_clusterRange <;> assumption
private theorem clusterRange_le_succ {x x' B : ℝ} (hB : 0 ≤ B) (hx : 0 ≤ x) (hd : x ≤ x' + 2 * B)
    (hx' : (2 * B + 1) ^ 100 ≤ x') : clusterRange x ≤ clusterRange x' + 1 := by
  have hp0 : 0 ≤ x' := le_trans (by positivity) hx'
  set u : ℝ := x' ^ ((1 : ℝ) / 100) with hu
  have hu100 : u ^ 100 = x' := by
    rw [hu, ← Real.rpow_natCast, ← Real.rpow_mul hp0]
    norm_num
  have hu1 : 2 * B + 1 ≤ u := by
    have h1 : ((2 * B + 1) ^ 100) ^ ((1 : ℝ) / 100) = 2 * B + 1 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
      norm_num
    rw [← h1]
    exact Real.rpow_le_rpow (by positivity) hx' (by norm_num)
  have hu0 : 1 ≤ u := by linarith
  have h99 : u ≤ u ^ 99 := le_self_pow₀ hu0 (by norm_num)
  have hpow : u ^ 100 + u ≤ (u + 1) ^ 100 := by
    have h1 : u ^ 99 ≤ (u + 1) ^ 99 := pow_le_pow_left₀ (by linarith) (by linarith) _
    have e : (u + 1) ^ 100 = (u + 1) * (u + 1) ^ 99 := by ring
    have e2 : u ^ 100 = u * u ^ 99 := by ring
    rw [e, e2]
    nlinarith [pow_pos (show 0 < u by linarith) 99]
  have hxu : x ≤ (u + 1) ^ 100 := by
    rw [hu100] at hpow
    linarith
  have h2 : x ^ ((1 : ℝ) / 100) ≤ u + 1 := by
    have h1 : ((u + 1) ^ 100) ^ ((1 : ℝ) / 100) = u + 1 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by linarith)]
      norm_num
    rw [← h1]
    exact Real.rpow_le_rpow hx hxu (by norm_num)
  calc clusterRange x ≤ ⌈u + 1⌉₊ := Nat.ceil_mono h2
    _ = clusterRange x' + 1 := Nat.ceil_add_one (by linarith)
private theorem stage_functional_eq (T : StageTower ℓ) {β : ℝ} {K : ℕ} (hst : TowerFollowsFlow T β K)
    (h0 : T.base.functional = wilsonWeight β) :
    ∀ j, j ≤ K + 1 → (T.stage j).functional = flowFunctional ℓ β j
  | 0, _ => h0
  | j + 1, h => by
    have ih := stage_functional_eq T hst h0 j (by omega)
    have hx := hst j (by omega)
    show kernelImage ℓ (T.stage j).coupling (T.stage j).functional =
      kernelImage ℓ (couplingFlow ℓ β j).1 (couplingFlow ℓ β j).2
    rw [ih, hx]
    rfl
private theorem stage_anchorRadius (T : StageTower ℓ) : ∀ t, (T.stage t).anchorRadius = T.base.anchorRadius
  | 0 => rfl
  | t + 1 => stage_anchorRadius T t
private theorem stage_barrierFn (T : StageTower ℓ) : ∀ t, (T.stage t).barrierFn = T.base.barrierFn
  | 0 => rfl
  | t + 1 => stage_barrierFn T t
private theorem abs_expansionCoupling_sub_le (hret : ExpansionReturnsAt ℓ) {t : ℕ} {x : ℝ} {D : TorusFunctional}
    (hx : ℓ.y₁ ≤ x) (hr : HasExpansion ℓ t x D) : |expansionCoupling ℓ t x D - x| ≤ 2 * ℓ.B := by
  classical
  obtain ⟨x', ⟨h1, h2⟩, h3⟩ := hret t x D hx hr
  have hex : ∃ x' : ℝ, HasExpansion ℓ (t + 1) x' (kernelImage ℓ x D) := ⟨x', h1⟩
  have e : expansionCoupling ℓ t x D = hex.choose := by
    unfold expansionCoupling
    rw [dif_pos hex]
  obtain ⟨-, f, hf, -⟩ := hex.choose_spec
  rw [e, h3 _ f hf]
  exact h2
end Flow
section Numbers
private theorem hot_exponent_le {N X C b L4 Cd : ℝ} (hN : 0 ≤ N) (hX : 1 ≤ X) (hb : 0 ≤ b) (hL4 : 1 ≤ L4)
    (hCd : 0 ≤ Cd) : (b + (C + 6 * X)) * N ≤ (L4 * (b + |C| + 12) + Cd) * X * N := by
  have h0 : 0 ≤ b + |C| := add_nonneg hb (abs_nonneg _)
  have h1 : b + (C + 6 * X) ≤ (b + |C| + 12) * X := by
    have := le_abs_self C
    nlinarith
  have h2 : (b + |C| + 12) * X ≤ L4 * (b + |C| + 12) * X := by
    have h3 : 0 ≤ (b + |C| + 12) * X := by positivity
    nlinarith
  have h3 : 0 ≤ Cd * X := by positivity
  have h4 : b + (C + 6 * X) ≤ (L4 * (b + |C| + 12) + Cd) * X := by nlinarith
  exact mul_le_mul_of_nonneg_right h4 hN
private theorem bad_exponent_le {N X Y C b L4 Cl Cd : ℝ} (hN : 0 ≤ N) (hX : 1 ≤ X) (hb : 0 ≤ b) (hL4 : 1 ≤ L4)
    (hY : Y ≤ 2 * X) (hCl : 4 * Cl ≤ Cd * X) :
    (b + (C + 6 * Y)) * (N * L4) + 4 * N * Cl ≤ (L4 * (b + |C| + 12) + Cd) * X * N := by
  have h0 : 0 ≤ b + |C| := add_nonneg hb (abs_nonneg _)
  have h1 : b + (C + 6 * Y) ≤ (b + |C| + 12) * X := by
    have := le_abs_self C
    nlinarith
  have hNL : 0 ≤ N * L4 := by positivity
  have h2 := mul_le_mul_of_nonneg_right h1 hNL
  have h3 := mul_le_mul_of_nonneg_left hCl hN
  nlinarith
private theorem decay_gap_le {N σ δ t M : ℝ} (hN : 0 ≤ N) (hσ : 0 ≤ σ) (hδ : 0 ≤ δ) (hM : 512 * N ≤ δ * M)
    (ht : M ≤ t) : N * σ * Real.exp (-(δ * t)) ≤ σ / 512 := by
  have h1 : 512 * N ≤ δ * t := hM.trans (mul_le_mul_of_nonneg_left ht hδ)
  have h2 : δ * t + 1 ≤ Real.exp (δ * t) := Real.add_one_le_exp _
  rw [Real.exp_neg]
  have hp := Real.exp_pos (δ * t)
  have h4 : N * (Real.exp (δ * t))⁻¹ ≤ 1 / 512 := by
    rw [← div_eq_mul_inv, div_le_iff₀ hp]
    linarith
  have := mul_le_mul_of_nonneg_left h4 hσ
  nlinarith
private theorem range_floor_facts (n₀ M : ℕ) : 2 ^ 16 ≤ 4 * n₀ + 2 ^ 16 + 2 ^ 11 * (M + 16) ∧
    16 * 2 ^ 11 ≤ 4 * n₀ + 2 ^ 16 + 2 ^ 11 * (M + 16) ∧ M * 2 ^ 11 ≤ 4 * n₀ + 2 ^ 16 + 2 ^ 11 * (M + 16) := by
  norm_num
  omega
private theorem le_sq_of_le_two_mul {a b : ℝ} (hb : 2 ≤ b) (h : a ≤ 2 * b) : a ≤ b ^ 2 := by nlinarith
private theorem two_add_mul_le {a u v : ℝ} (ha : 0 ≤ a) (hv : 1 ≤ v) (h : u ≤ 2 * v) :
    2 + a * u ≤ (2 + 2 * a) * v := by
  have := mul_le_mul_of_nonneg_left h ha
  nlinarith
private theorem le_add_one_mul {l g X : ℝ} (hX : 1 ≤ X) (hg : 0 ≤ g) (h : l ≤ g + X) : l ≤ (g + 1) * X := by
  nlinarith
end Numbers
section Main
variable {Tb : ParameterAssignment} {y : ℝ}
private theorem flow_above_floor (hfit : (Tb.stepParameters y).Admissible) (hR : ExpansionHolds (Tb.stepParameters y))
    (hA : expansionAlongFlow) {g β : ℝ} {K : ℕ} (hp : FlowCrossing Tb y g β K) :
    ∀ j ≤ K, y ≤ (couplingFlow (Tb.stepParameters y) β j).1 := by
  have hB : 0 < (Tb.stepParameters y).B := hfit.B_pos
  have hfl := hp.le_inv_sq
  have hlt : ∀ j, j < K → y ≤ (couplingFlow (Tb.stepParameters y) β j).1 := by
    intro j hj
    have h1 := hp.isFirst.2 j hj
    unfold windowUpper at h1
    linarith
  intro j hj
  rcases Nat.lt_or_eq_of_le hj with h | rfl
  · exact hlt j h
  · cases j with
    | zero =>
      have h1 := hp.upper_le
      unfold windowUpper at h1
      show y ≤ β
      linarith
    | succ k =>
      have hk : y ≤ (couplingFlow (Tb.stepParameters y) β k).1 := hlt k (by omega)
      have hreach : CouplingsAboveFloor (Tb.stepParameters y) β k := fun i hi => hlt i (by omega)
      have hrow := (hA _ hR β k hreach).1
      have hs := abs_expansionCoupling_sub_le hR.returns_at hk hrow
      have h1 := hp.isFirst.2 k (by omega)
      unfold windowUpper at h1
      have h2 := (abs_le.mp hs).1
      have h3 : (couplingFlow (Tb.stepParameters y) β (k + 1)).1 =
          expansionCoupling (Tb.stepParameters y) k (couplingFlow (Tb.stepParameters y) β k).1
            (couplingFlow (Tb.stepParameters y) β k).2 := rfl
      have h4 : flowCoupling (Tb.stepParameters y) β k = (couplingFlow (Tb.stepParameters y) β k).1 := rfl
      rw [h3]
      have h6 : -(2 * (Tb.stepParameters y).B) ≤ expansionCoupling (Tb.stepParameters y) k
          (couplingFlow (Tb.stepParameters y) β k).1 (couplingFlow (Tb.stepParameters y) β k).2 -
            (couplingFlow (Tb.stepParameters y) β k).1 := (abs_le.mp hs).1
      linarith
private theorem isBlockTorusSide_torusSideAtLevel {g β : ℝ} {K m j : ℕ} (hfit : (Tb.stepParameters y).Admissible)
    (hv : CrossingVolume Tb y g β K m) : IsBlockTorusSide (Tb.stepParameters y) (torusSideAtLevel Tb.side K m j) := by
  have hvol := hv.volume_le
  have hL1 : 2 ^ 16 ≤ Tb.side := hfit.L_ge
  have hn₀ : 4096 ≤ Tb.n₀ := hfit.n₀_ge
  have hm : m ≠ 0 := by
    rintro rfl
    simp only [pow_zero, mul_one] at hvol
    nlinarith
  have e : torusSideAtLevel Tb.side K m j = 2 * Tb.side ^ m * Tb.side ^ (K - j) := by
    unfold torusSideAtLevel
    rw [fineSide_eq]
  refine ⟨?_, ?_⟩
  · show Tb.side ∣ torusSideAtLevel Tb.side K m j
    rw [e]
    exact Dvd.dvd.mul_right (Dvd.dvd.mul_left (dvd_pow_self _ hm) 2) _
  · show Tb.side * Tb.n₀ ≤ torusSideAtLevel Tb.side K m j
    rw [e]
    have h1 : 1 ≤ Tb.side ^ (K - j) := Nat.one_le_pow _ _ (by omega)
    calc Tb.side * Tb.n₀ ≤ 2 * Tb.side ^ m := hvol
      _ = 2 * Tb.side ^ m * 1 := (mul_one _).symm
      _ ≤ _ := Nat.mul_le_mul_left _ h1
private theorem stageFacts_of {C g β : ℝ} {K m j n : ℕ} [NeZero n] {T : StageTower (Tb.stepParameters y)}
    (hfit : (Tb.stepParameters y).Admissible) (hM : flowFunctionalIntegral)
    (hAt : HullChainAtLevel Tb y g β K m T j n)
    (hside : IsBlockTorusSide (Tb.stepParameters y) n)
    (hreach : ∀ i ≤ K, y ≤ (couplingFlow (Tb.stepParameters y) β i).1) (hy : 1 ≤ y)
    (hfl : 4 * Tb.n₀ + 2 ^ 16 ≤ clusterRange y)
    (hmass : ∀ (t : ℕ), CouplingsAboveFloor (Tb.stepParameters y) β t → ∀ (n : ℕ) [NeZero n],
      IsBlockTorusSide (Tb.stepParameters y) n →
      Real.log (flowFunctionalAtTrivial (Tb.stepParameters y) β t n) -
          (C + 6 * Real.log (flowCoupling (Tb.stepParameters y) β t)) * (n : ℝ) ^ 4 ≤
        Real.log (torusPartition (Tb.stepParameters y) β t n))
    (hst : ∀ F : StageState T j n → ℝ, Measurable F → (∃ C : ℝ, ∀ q, |F q| ≤ C) →
      ∫ w, F (stageState T j n w) ∂(markedSampleLaw T β j n) =
        (∫ W, (open Classical in ∑ Y ∈ Finset.univ.filter (IsHullState (Tb.stepParameters y) (stageRange T j) W),
            ∫ ω, F (W, ⟨Y, ω⟩) * (T.stage j).labelWeight n W Y ω
              ∂(Measure.pi fun _ : Y => (T.stage j).labels.μ)) ∂(fieldHaar n)) /
          ∫ W, wilsonWeight β (fineSide (Tb.stepParameters y).side j n) W
            ∂(fieldHaar (fineSide (Tb.stepParameters y).side j n))) :
    StageFacts T β (∫ W, wilsonWeight β (fineSide (Tb.stepParameters y).side j n) W
        ∂(fieldHaar (fineSide (Tb.stepParameters y).side j n)))
      (C + 6 * Real.log (T.stage j).coupling) j n := by
  have hj := hAt.le
  have hrun := hAt.chain
  have hx : (T.stage j).coupling = (couplingFlow (Tb.stepParameters y) β j).1 := hrun.follows j (by omega)
  have hD : (T.stage j).functional = flowFunctional (Tb.stepParameters y) β j :=
    stage_functional_eq T hrun.follows hrun.functional_bottom j (by omega)
  have hyx := hreach j hj
  obtain ⟨-, hpos, -, -, hZ⟩ := hM _ hfit β j n
  refine ⟨hfit, hside, hrun.expansions j hj, ?_, ?_, ?_, hZ, ?_, hst⟩
  · rw [hx]
    linarith
  · rw [hx]
    exact hfl.trans (clusterRange_mono (by linarith) hyx)
  · intro W
    rw [hD]
    exact (hpos W).le
  · have h1 := hmass j (fun i hi => hreach i (hi.trans hj)) n hside
    rw [hx, hD]
    exact h1
end Main
section Proof
open Classical in
theorem separatedUnitsRare (hS : stageStateDensityStatement)
    (hMass : freeEnergyLowerBoundStatement) (hBad : badBlocksPaidByEnergy)
    (hM : flowFunctionalIntegral) (hA : expansionAlongFlow) (hPay : functionalBoundByLumpPrice)
    (hK : BondKernelProperties) (hOm : LogPartitionGapLogGrowth)
    (hSD : StepTransitionDensityBounds) (hWB : chainMeasurabilityStatement) :
    separatedUnitsRareStatement := by
  have hMass' : ∀ Tb : ParameterAssignment, ∃ C y₀ : ℝ, Tb.Admissible → ∀ y : ℝ, y₀ ≤ y →
      ExpansionHolds (Tb.stepParameters y) →
      ∀ (β : ℝ) (t : ℕ), CouplingsAboveFloor (Tb.stepParameters y) β t → ∀ (n : ℕ) [NeZero n],
        IsBlockTorusSide (Tb.stepParameters y) n →
        Real.log (flowFunctionalAtTrivial (Tb.stepParameters y) β t n) -
            (C + 6 * Real.log (flowCoupling (Tb.stepParameters y) β t)) * (n : ℝ) ^ 4 ≤
          Real.log (torusPartition (Tb.stepParameters y) β t n) := fun Tb => by
    by_cases h : Tb.Admissible
    · obtain ⟨C, y₀, h1⟩ := hMass Tb h
      exact ⟨C, y₀, fun _ => h1⟩
    · exact ⟨0, 0, fun h' => absurd h' h⟩
  choose Cm yM HM using hMass'
  obtain ⟨Co, hCo, hom⟩ := hOm
  refine ⟨fun Tb => (Tb.side : ℝ) ^ 4 * (Real.log 2 + 2 * Tb.E + |Cm Tb| + 12) +
    4 * Co * (Real.log (2 + 2 * Tb.coupling) + 1), ?_⟩
  intro a ha
  obtain ⟨L₁, rt₁, C₁, hrt₁, HS⟩ := hS a ha
  refine ⟨L₁, rt₁, C₁, hrt₁, ?_⟩
  intro L hodd hL Tb hTa hTL hD hCold hHalf hrt hCder
  obtain ⟨M₁, HS₂⟩ := HS L hodd hL Tb hTa hTL hD hCold hHalf hrt hCder
  have HM₂ := HM Tb hD
  set y₂ := yM Tb with hy₂
  refine ⟨M₁, ?_⟩
  intro Kr hM₁ h1K h2K hKr hResp
  obtain ⟨y₁, HS₃⟩ := HS₂ Kr hM₁ h1K h2K hKr hResp
  set M₀ : ℕ := ⌈512 * Tb.N 0 / Tb.δ₁⌉₊ with hM₀
  set R₀ : ℕ := 4 * Tb.n₀ + 2 ^ 16 + 2 ^ 11 * (M₀ + 16) with hR₀
  refine ⟨max (max y₁ y₂) (max Tb.floorMin (max ((R₀ : ℝ) ^ 100) (max ((2 * Tb.B + 1) ^ 100) (4 * Tb.B + 3)))), ?_⟩
  intro y hy hret hwil
  have hy1 : y₁ ≤ y := ((le_max_left _ _).trans (le_max_left _ _)).trans hy
  have hy2 : y₂ ≤ y := ((le_max_right _ _).trans (le_max_left _ _)).trans hy
  have hy3 : Tb.floorMin ≤ y := ((le_max_left _ _).trans (le_max_right _ _)).trans hy
  have hy4 : (R₀ : ℝ) ^ 100 ≤ y :=
    ((le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))).trans hy
  have hy5 : (2 * Tb.B + 1) ^ 100 ≤ y :=
    ((le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _)))).trans hy
  have hy6 : 4 * Tb.B + 3 ≤ y :=
    ((le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _)))).trans hy
  have hfit : (Tb.stepParameters y).Admissible := hD.fits y hy3
  have hB0 : 0 < Tb.B := hfit.B_pos
  have hσ0 : 0 < Tb.threshold := hD.σ_pos
  have hκ0 : 0 < Tb.κ := hD.κ_pos
  have hcE0 : 0 < Tb.cE := hD.cE_pos
  have ha1 : 1 ≤ Tb.coupling := hD.a_ge
  have hE1 : 1 ≤ Tb.E := hfit.E_ge
  have hyone : 1 ≤ y := by linarith
  have hR : ExpansionHolds (Tb.stepParameters y) := ⟨hret, hwil⟩
  have hRange : ∀ x : ℝ, y ≤ x → R₀ ≤ clusterRange x := fun x hx => le_clusterRange (hy4.trans hx)
  have hStep : ∀ x x' : ℝ, 0 ≤ x → x ≤ x' + 2 * Tb.B → y ≤ x' → clusterRange x ≤ clusterRange x' + 1 :=
    fun x x' h0 h1 h2 => clusterRange_le_succ hB0.le h0 h1 (hy5.trans h2)
  clear hy4 hy5 hy
  have A₁ := HS₃ y hy1 hret hwil
  have A₂ := HM₂ y hy2 hR
  intro g β K m T u n _ hAt A hne hap
  have hrun := hAt.chain
  have hreach := flow_above_floor hfit hR hA hrun.toCrossingVolume.toFlowCrossing
  have hR₀1 : 4 * Tb.n₀ + 2 ^ 16 ≤ R₀ := by
    rw [hR₀]
    exact Nat.le_add_right _ _
  have hfl : 4 * Tb.n₀ + 2 ^ 16 ≤ clusterRange y := hR₀1.trans (hRange y le_rfl)
  have hLam : 11 * 2 ^ 12 * (Tb.stepParameters y).baseDepth < (Tb.stepParameters y).side := hD.L_gt
  have hcut0 : IsCutoff ((Tb.stepParameters y).threshold / 64) T.base.barrierFn := hrun.cutoff_bottom
  have hcoin := hrun.marks
  have hProb : ∀ (s n' : ℕ) [NeZero n'], IsProbabilityMeasure (markedSampleLaw T β s n') := fun s n' _ =>
    (hWB.2.2 (Tb.stepParameters y) hfit hLam T hcut0 hcoin β s n').1
  have hFacts : ∀ (j n' : ℕ) [NeZero n'], HullChainAtLevel Tb y g β K m T j n' →
      StageFacts T β (∫ W, wilsonWeight β (fineSide (Tb.stepParameters y).side j n') W
          ∂(fieldHaar (fineSide (Tb.stepParameters y).side j n')))
        (Cm Tb + 6 * Real.log (T.stage j).coupling) j n' := fun j n' _ h =>
    stageFacts_of hfit hM h (by rw [h.side_eq]; exact isBlockTorusSide_torusSideAtLevel hfit hrun.toCrossingVolume)
      hreach hyone hfl (fun t hr n'' _ hs => A₂ β t hr n'' hs) (A₁ g β K m T j n' h)
  have hu := hAt.le
  have hxu : (T.stage u).coupling = (couplingFlow (Tb.stepParameters y) β u).1 := hrun.follows u (by omega)
  have hyu : y ≤ (T.stage u).coupling := by
    rw [hxu]
    exact hreach u hu
  have hsideN : IsBlockTorusSide (Tb.stepParameters y) n := by
    rw [hAt.side_eq]
    exact isBlockTorusSide_torusSideAtLevel hfit hrun.toCrossingVolume
  have hLn : (Tb.stepParameters y).side ∣ n := hsideN.1
  set X : ℝ := Real.log (stageCoupling T u) with hX
  have hX1 : 1 ≤ X := by
    rw [hX, Real.le_log_iff_exp_le (by show 0 < (T.stage u).coupling; linarith)]
    have h1 := Real.exp_one_lt_d9
    show Real.exp 1 ≤ (T.stage u).coupling
    linarith
  set k : ℕ := (A.card + 1) / 2 with hk
  have hAk : (A.card : ℝ) ≤ 2 * (k : ℝ) := by
    have : A.card ≤ 2 * k := by omega
    exact_mod_cast this
  have hn4 : (0 : ℝ) ≤ (n : ℝ) ^ 4 := by positivity
  set bb : ℝ := Real.log 2 + 2 * Tb.E with hbb
  have hbb0 : 0 ≤ bb := by
    have := Real.log_nonneg (show (1 : ℝ) ≤ 2 by norm_num)
    rw [hbb]
    linarith
  have hL4 : (1 : ℝ) ≤ (Tb.side : ℝ) ^ 4 := by
    have : (1 : ℝ) ≤ (Tb.side : ℝ) := by
      have h2 : 1 ≤ Tb.side := by
        have := hfit.L_ge
        have h3 : 2 ^ 16 ≤ Tb.side := this
        omega
      exact_mod_cast h2
    exact one_le_pow₀ this
  have hlg : 0 ≤ Real.log (2 + 2 * Tb.coupling) := Real.log_nonneg (by linarith)
  set Cd : ℝ := 4 * Co * (Real.log (2 + 2 * Tb.coupling) + 1) with hCd
  have hCd0 : 0 ≤ Cd := by positivity
  set ee : ℝ := Real.exp (((Tb.side : ℝ) ^ 4 * (Real.log 2 + 2 * Tb.E + |Cm Tb| + 12) + Cd) * X * (n : ℝ) ^ 4 -
    unitDecayRate Tb * stageCoupling T u * (A.card : ℝ)) with hee
  have hee0 : 0 < ee := Real.exp_pos _
  have hxu0 : 0 < (T.stage u).coupling := by linarith
  have hc1 : unitDecayRate Tb ≤ Tb.κ * Tb.threshold ^ 2 / 4 := by
    unfold unitDecayRate
    have := min_le_left (Tb.κ * Tb.threshold ^ 2) Tb.cE
    linarith
  have hc2 : unitDecayRate Tb ≤ Tb.cE / 4 := by
    unfold unitDecayRate
    have := min_le_right (Tb.κ * Tb.threshold ^ 2) Tb.cE
    linarith
  have hc0 : 0 ≤ unitDecayRate Tb := by
    unfold unitDecayRate
    have : 0 ≤ min (Tb.κ * Tb.threshold ^ 2) Tb.cE := le_min (by positivity) hcE0.le
    linarith
  have hHot : (markedSampleLaw T β u n).real
      {w | k ≤ (torusHotLumps (Tb.stepParameters y) (topField (Tb.stepParameters y) u n w)).card} ≤ ee := by
    have hP := hProb u n
    refine (hotLumps_probability_le hPay (hFacts u n hAt) hP k).trans ?_
    rw [← Real.exp_add, hee]
    apply Real.exp_le_exp.mpr
    have h1 := hot_exponent_le (N := (n : ℝ) ^ 4) (X := X) (C := Cm Tb) (b := bb) (L4 := (Tb.side : ℝ) ^ 4)
      (Cd := Cd) hn4 hX1 hbb0 hL4 hCd0
    have h2 : unitDecayRate Tb * (T.stage u).coupling * (A.card : ℝ) ≤
        (T.stage u).coupling * Tb.κ * Tb.threshold ^ 2 * (k : ℝ) := by
      have hA0 : (0 : ℝ) ≤ (A.card : ℝ) := by positivity
      have h3 : unitDecayRate Tb * (A.card : ℝ) ≤ Tb.κ * Tb.threshold ^ 2 / 4 * (2 * (k : ℝ)) :=
        mul_le_mul hc1 hAk hA0 (by positivity)
      have h4 := mul_le_mul_of_nonneg_left h3 hxu0.le
      have hk0 : (0 : ℝ) ≤ (k : ℝ) := by positivity
      have h5 : 0 ≤ (T.stage u).coupling * Tb.κ * Tb.threshold ^ 2 * (k : ℝ) := by positivity
      have e1 : unitDecayRate Tb * (T.stage u).coupling * (A.card : ℝ) =
          (T.stage u).coupling * (unitDecayRate Tb * (A.card : ℝ)) := by ring
      have e2 : (T.stage u).coupling * (Tb.κ * Tb.threshold ^ 2 / 4 * (2 * (k : ℝ))) =
          (T.stage u).coupling * Tb.κ * Tb.threshold ^ 2 * (k : ℝ) / 2 := by ring
      linarith
    have e1 : (bb + (Cm Tb + 6 * X)) * (n : ℝ) ^ 4 =
        (Real.log 2 + 2 * (Tb.stepParameters y).E + (Cm Tb + 6 * Real.log (T.stage u).coupling)) * (n : ℝ) ^ 4 := rfl
    have e2 : -((T.stage u).coupling * (Tb.stepParameters y).κ * (Tb.stepParameters y).threshold ^ 2 * (k : ℝ)) =
        -((T.stage u).coupling * Tb.κ * Tb.threshold ^ 2 * (k : ℝ)) := rfl
    rw [← e1, e2]
    have e3 : unitDecayRate Tb * stageCoupling T u * (A.card : ℝ) =
        unitDecayRate Tb * (T.stage u).coupling * (A.card : ℝ) := rfl
    rw [e3]
    linarith
  have hfinal : ∀ P : ℝ, P ≤ ee + ee → P ≤ 2 ^ (1 + A.card) * ee := by
    intro P hP
    have h2 : (2 : ℝ) ≤ 2 ^ (1 + A.card) := by
      calc (2 : ℝ) = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ (1 + A.card) := pow_le_pow_right₀ (by norm_num) (by omega)
    have h3 := mul_le_mul_of_nonneg_right h2 hee0.le
    linarith
  have hmono : ∀ (B : Set (MarkedSample (Tb.stepParameters y) u n)), {w | ∀ z ∈ A, IsUnit T u n w z} ⊆ B →
      (markedSampleLaw T β u n).real {w | ∀ z ∈ A, IsUnit T u n w z} ≤ (markedSampleLaw T β u n).real B :=
    fun B hB => by
      have hP := hProb u n
      exact measureReal_mono hB
  cases u with
  | zero =>
    apply hfinal
    refine (hmono _ ?_).trans ((hHot).trans (by linarith))
    intro w hw
    have h1 : A.card ≤ (torusHotLumps (Tb.stepParameters y) (topField (Tb.stepParameters y) 0 n w)).card :=
      card_le_card_torusHotLumps hfit hLn hap fun z hz => by
        rcases hw z hz with h | h
        · exact h
        · exact h.elim
    have h2 : 1 ≤ A.card := Finset.card_pos.mpr hne
    show k ≤ _
    omega
  | succ s =>
    apply hfinal
    have hAtS : HullChainAtLevel Tb y g β K m T s (n * (Tb.stepParameters y).side) := by
      refine ⟨hrun, by omega, ?_⟩
      have e0 : K - s = (K - (s + 1)) + 1 := by omega
      show n * Tb.side = torusSideAtLevel Tb.side K m s
      rw [hAt.side_eq]
      unfold torusSideAtLevel
      rw [fineSide_eq, fineSide_eq, e0, pow_succ]
      ring
    have hLs := hFacts s (n * (Tb.stepParameters y).side) hAtS
    have hxs : (T.stage s).coupling = (couplingFlow (Tb.stepParameters y) β s).1 := hrun.follows s (by omega)
    have hys : y ≤ (T.stage s).coupling := by
      rw [hxs]
      exact hreach s (by omega)
    have hreachs : CouplingsAboveFloor (Tb.stepParameters y) β s := fun i hi => hreach i (by omega)
    have hrow := (hA _ hR β s hreachs).1
    have hstep := abs_expansionCoupling_sub_le hret (hreach s (by omega)) hrow
    have hd : |(T.stage (s + 1)).coupling - (T.stage s).coupling| ≤ 2 * Tb.B := by
      rw [hxu, hxs]
      exact hstep
    obtain ⟨hd1, hd2⟩ := abs_le.mp hd
    have hxx : (T.stage s).nextCoupling = (T.stage (s + 1)).coupling := rfl
    have hxs0 : 0 < (T.stage s).coupling := by linarith
    have hrf : RangesAdmissible (clusterRange (T.stage s).coupling) (clusterRange (T.stage s).nextCoupling) := by
      rw [hxx]
      refine ⟨hStep _ _ hxs0.le (by linarith) hyu, ?_, ?_⟩
      · have h1 := hRange _ hyu
        have h2 : 2 ^ 16 ≤ R₀ := (range_floor_facts Tb.n₀ M₀).1
        exact h2.trans h1
      · have h1 := hRange _ hys
        have h2 : 16 * 2 ^ 11 ≤ R₀ := (range_floor_facts Tb.n₀ M₀).2.1
        exact (Nat.le_div_iff_mul_le (by norm_num)).mpr (h2.trans h1)
    have hN0 : 0 < Tb.N 0 := hD.chain.2.2.2.2.2.2.2.1 0
    have hδ0 : 0 < Tb.δ₁ := hD.δ₁_pos
    have hgap : Tb.N 0 * Tb.threshold *
        Real.exp (-(Tb.δ₁ * ((clusterRange (T.stage s).coupling / 2 ^ 11 : ℕ) : ℝ))) ≤ Tb.threshold / 512 := by
      refine decay_gap_le (M := (M₀ : ℝ)) hN0.le hσ0.le hδ0.le ?_ ?_
      · have h1 : 512 * Tb.N 0 / Tb.δ₁ ≤ (M₀ : ℝ) := Nat.le_ceil _
        have h2 := mul_le_mul_of_nonneg_left h1 hδ0.le
        rw [mul_div_cancel₀ _ hδ0.ne'] at h2
        exact h2
      · have h1 := hRange _ hys
        have h2 : M₀ * 2 ^ 11 ≤ R₀ := (range_floor_facts Tb.n₀ M₀).2.2
        have h3 : M₀ ≤ clusterRange (T.stage s).coupling / 2 ^ 11 :=
          (Nat.le_div_iff_mul_le (by norm_num)).mpr (h2.trans h1)
        exact_mod_cast h3
    have hρ : (T.stage s).anchorRadius = Tb.ρA := (stage_anchorRadius T s).trans hrun.anchor_bottom
    have hcs : IsCutoff ((Tb.stepParameters y).threshold / 64) (T.stage s).barrierFn := by
      rw [stage_barrierFn]
      exact hcut0
    have hpaid := hBad Tb y hD hfit (T.stage s) hρ hcs hrf hgap n hsideN
    set Cl : ℝ := Co * Real.log (2 + Tb.coupling * (T.stage s).coupling) with hCl
    have hax : 0 ≤ Tb.coupling * (T.stage s).coupling := by positivity
    have hom' : ∀ (W : TorusField (n * (Tb.stepParameters y).side)) (b : BaseChoice (Tb.stepParameters y).side n)
        (e : TorusBond n),
        logPartitionGap ((Tb.stepParameters y).coupling * (T.stage s).coupling *
          meanNorm (Tb.stepParameters y) W b e) ≤ Cl := by
      intro W b e
      have hr0 : 0 ≤ meanNorm (Tb.stepParameters y) W b e := norm_nonneg _
      have hr1 : meanNorm (Tb.stepParameters y) W b e ≤ 1 := norm_contourMean_le _ _ _ _ _
      have hs0 : 0 ≤ Tb.coupling * (T.stage s).coupling * meanNorm (Tb.stepParameters y) W b e := mul_nonneg hax hr0
      have h1 := hom _ hs0
      have h2 : Tb.coupling * (T.stage s).coupling * meanNorm (Tb.stepParameters y) W b e ≤
          Tb.coupling * (T.stage s).coupling := by
        have := mul_le_mul_of_nonneg_left hr1 hax
        linarith
      have h3 : Real.log (2 + Tb.coupling * (T.stage s).coupling * meanNorm (Tb.stepParameters y) W b e) ≤
          Real.log (2 + Tb.coupling * (T.stage s).coupling) :=
        Real.log_le_log (by linarith) (by linarith)
      exact h1.trans (mul_le_mul_of_nonneg_left h3 hCo.le)
    set Kk : ℝ := Real.exp (4 * (n : ℝ) ^ 4 * Cl - (T.stage s).coupling * Tb.cE * (k : ℝ)) with hKk
    have hpt : ∀ (W : TorusField (n * (Tb.stepParameters y).side)) (b : BaseChoice (Tb.stepParameters y).side n)
        (V : TorusField n) (bad : Finset (TorusBond (n * (Tb.stepParameters y).side))),
        b ∈ baseChoices (Tb.stepParameters y) (readAtLevel (stepBlockFrame (Tb.stepParameters y).side n) 0 W) →
        markLaw (T.stage s).toStepSetup W V bad ≠ 0 →
        (k ≤ (bad.image fun e => parentBlock (Tb.stepParameters y).side e.1).card) →
        (∏ c : (stepBlockFrame (Tb.stepParameters y).side n).Cell × Fin 4,
          bondKernel (Tb.stepParameters y) (T.stage s).coupling
            (readAtLevel (stepBlockFrame (Tb.stepParameters y).side n) 0 W)
            (readAtLevel (stepBlockFrame (Tb.stepParameters y).side n) 1 V) b c) *
          Real.exp (-((T.stage s).coupling * actionAtLevel (Tb.stepParameters y).coupling (Tb.stepParameters y).side
            (T.stage s).depth (Finset.univ \ thickening lumpRange (torusHotSites (Tb.stepParameters y) W)) W) -
            (T.stage s).coupling * (Tb.stepParameters y).κ * (Tb.stepParameters y).threshold ^ 2 *
              ((torusHotLumps (Tb.stepParameters y) W).card : ℝ)) ≤ Kk := by
      intro W b V bad hb hc hkb
      have hp := hpaid V W b bad hb hc
      have hk1 := prod_bondKernel_le hK (T.stage s).coupling Cl W V b (hom' W b)
      refine (mul_le_mul_of_nonneg_right hk1 (Real.exp_pos _).le).trans ?_
      rw [← Real.exp_add, hKk]
      apply Real.exp_le_exp.mpr
      have hkb' : (k : ℝ) ≤ ((bad.image fun e => parentBlock (Tb.stepParameters y).side e.1).card : ℝ) := by
        exact_mod_cast hkb
      have h2 : Tb.cE * (k : ℝ) ≤ Tb.cE * ((bad.image fun e => parentBlock (Tb.stepParameters y).side e.1).card : ℝ) :=
        mul_le_mul_of_nonneg_left hkb' hcE0.le
      have h3 := mul_le_mul_of_nonneg_left (h2.trans hp) hxs0.le
      have e1 : (T.stage s).coupling * (actionAtLevel Tb.coupling Tb.side (T.stage s).depth
            (Finset.univ \ thickening lumpRange (torusHotSites (Tb.stepParameters y) W)) W +
            Tb.κ * Tb.threshold ^ 2 * ((torusHotLumps (Tb.stepParameters y) W).card : ℝ) +
            Tb.coupling * ∑ e : TorusBond n, bondFit (Tb.stepParameters y) W V b e) =
          (T.stage s).coupling * actionAtLevel Tb.coupling Tb.side (T.stage s).depth
            (Finset.univ \ thickening lumpRange (torusHotSites (Tb.stepParameters y) W)) W +
            (T.stage s).coupling * Tb.κ * Tb.threshold ^ 2 * ((torusHotLumps (Tb.stepParameters y) W).card : ℝ) +
            Tb.coupling * (T.stage s).coupling * ∑ e : TorusBond n, bondFit (Tb.stepParameters y) W V b e := by ring
      have e2 : (T.stage s).coupling * (Tb.cE * (k : ℝ)) = (T.stage s).coupling * Tb.cE * (k : ℝ) := by ring
      rw [e1, e2] at h3
      show -(Tb.coupling * (T.stage s).coupling) * ∑ e : TorusBond n, bondFit (Tb.stepParameters y) W V b e +
          4 * (n : ℝ) ^ 4 * Cl +
          (-((T.stage s).coupling * actionAtLevel Tb.coupling Tb.side (T.stage s).depth
            (Finset.univ \ thickening lumpRange (torusHotSites (Tb.stepParameters y) W)) W) -
            (T.stage s).coupling * Tb.κ * Tb.threshold ^ 2 * ((torusHotLumps (Tb.stepParameters y) W).card : ℝ)) ≤ _
      linarith
    have hcs' : IsCutoff (T.stage s).toStepSetup.ballRadius (T.stage s).toStepSetup.barrierFn := hcs
    have hbadc := badBlocks_measure_le hPay hSD hLs (hProb s _) hcs' hcoin k Kk (Real.exp_pos _).le hpt
    have hxu2 : (T.stage (s + 1)).coupling ≤ 2 * (T.stage s).coupling := by linarith
    have hxs2 : (T.stage s).coupling ≤ 2 * (T.stage (s + 1)).coupling := by linarith
    have hxu1 : 2 ≤ (T.stage (s + 1)).coupling := by linarith
    have hYle : Real.log (T.stage s).coupling ≤ 2 * X := by
      have h1 : (T.stage s).coupling ≤ (T.stage (s + 1)).coupling ^ 2 := le_sq_of_le_two_mul hxu1 hxs2
      have h2 := Real.log_le_log hxs0 h1
      rw [Real.log_pow] at h2
      exact_mod_cast h2
    have hCle : 4 * Cl ≤ Cd * X := by
      have h1 : 2 + Tb.coupling * (T.stage s).coupling ≤ (2 + 2 * Tb.coupling) * (T.stage (s + 1)).coupling :=
        two_add_mul_le (by linarith) (by linarith) hxs2
      have h2 := Real.log_le_log (by linarith) h1
      rw [Real.log_mul (by linarith) (by linarith)] at h2
      have h3 : Real.log (2 + Tb.coupling * (T.stage s).coupling) ≤ (Real.log (2 + 2 * Tb.coupling) + 1) * X := by
        have h4 : Real.log (T.stage (s + 1)).coupling = X := rfl
        rw [h4] at h2
        exact le_add_one_mul hX1 hlg h2
      have h5 := mul_le_mul_of_nonneg_left h3 hCo.le
      rw [hCl, hCd]
      linarith
    have hBadReal : (markedSampleLaw T β (s + 1) n).real
        (Prod.snd ⁻¹' badOutcomes (T.stage s).toStepSetup (n := n) k) ≤ ee := by
      refine (ENNReal.toReal_le_of_le_ofReal (by positivity) hbadc).trans ?_
      rw [hKk, ← Real.exp_add, hee]
      apply Real.exp_le_exp.mpr
      have h1 := bad_exponent_le (N := (n : ℝ) ^ 4) (X := X) (Y := Real.log (T.stage s).coupling) (C := Cm Tb)
        (b := bb) (L4 := (Tb.side : ℝ) ^ 4) (Cl := Cl) (Cd := Cd) hn4 hX1 hbb0 hL4 hYle hCle
      have e1 : ((n * (Tb.stepParameters y).side : ℕ) : ℝ) ^ 4 = (n : ℝ) ^ 4 * (Tb.side : ℝ) ^ 4 := by
        show ((n * Tb.side : ℕ) : ℝ) ^ 4 = _
        push_cast
        ring
      have e2 : Real.log 2 + 2 * (Tb.stepParameters y).E + (Cm Tb + 6 * Real.log (T.stage s).coupling) =
          bb + (Cm Tb + 6 * Real.log (T.stage s).coupling) := rfl
      rw [e1, e2]
      have h2 : unitDecayRate Tb * (T.stage (s + 1)).coupling * (A.card : ℝ) ≤
          (T.stage s).coupling * Tb.cE * (k : ℝ) := by
        have hA0 : (0 : ℝ) ≤ (A.card : ℝ) := by positivity
        have h3 : unitDecayRate Tb * (T.stage (s + 1)).coupling ≤ Tb.cE / 4 * (2 * (T.stage s).coupling) :=
          mul_le_mul hc2 hxu2 (by linarith) (by positivity)
        have h4 : unitDecayRate Tb * (T.stage (s + 1)).coupling * (A.card : ℝ) ≤
            Tb.cE / 4 * (2 * (T.stage s).coupling) * (2 * (k : ℝ)) :=
          mul_le_mul h3 hAk hA0 (by positivity)
        have e3 : Tb.cE / 4 * (2 * (T.stage s).coupling) * (2 * (k : ℝ)) = (T.stage s).coupling * Tb.cE * (k : ℝ) := by
          ring
        linarith
      have e3 : unitDecayRate Tb * stageCoupling T (s + 1) * (A.card : ℝ) =
          unitDecayRate Tb * (T.stage (s + 1)).coupling * (A.card : ℝ) := rfl
      rw [e3]
      linarith
    refine (hmono ({w | k ≤ (torusHotLumps (Tb.stepParameters y) (topField (Tb.stepParameters y) (s + 1) n w)).card} ∪
      (Prod.snd ⁻¹' badOutcomes (T.stage s).toStepSetup (n := n) k)) ?_).trans
      ((measureReal_union_le _ _).trans (add_le_add hHot hBadReal))
    intro w hw
    have hw' : ∀ z ∈ A, IsUnit T (s + 1) n w z := hw
    set P : TorusSite n → Prop := fun z => ContainsHotPlaquette (Tb.stepParameters y)
      (topField (Tb.stepParameters y) (s + 1) n w) (box z (4 * stageRange T (s + 1))) with hPdef
    have hcard : (A.filter P).card + (A.filter fun z => ¬ P z).card = A.card :=
      Finset.card_filter_add_card_filter_not _
    have hap1 : Separated (2 ^ 17 + 8 * stageRange T (s + 1)) (A.filter P) := fun a ha b hb hne =>
      hap a (Finset.mem_of_mem_filter _ ha) b (Finset.mem_of_mem_filter _ hb) hne
    have hap2 : Separated (2 ^ 17 + 8 * stageRange T (s + 1)) (A.filter fun z => ¬ P z) := fun a ha b hb hne =>
      hap a (Finset.mem_of_mem_filter _ ha) b (Finset.mem_of_mem_filter _ hb) hne
    have h1 : (A.filter P).card ≤
        (torusHotLumps (Tb.stepParameters y) (topField (Tb.stepParameters y) (s + 1) n w)).card :=
      card_le_card_torusHotLumps hfit hLn hap1 fun z hz => (Finset.mem_filter.mp hz).2
    have h2 : (A.filter fun z => ¬ P z).card ≤
        ((show Finset (TorusBond (n * (Tb.stepParameters y).side)) from w.2.2.2).image
          fun e => parentBlock (Tb.stepParameters y).side e.1).card := by
      refine card_le_card_blocks (Tb.stepParameters y).side (parentBlock (Tb.stepParameters y).side) hap2
        fun z hz => ?_
      obtain ⟨hzA, hzP⟩ := Finset.mem_filter.mp hz
      rcases hw' z hzA with h | h
      · exact absurd h hzP
      · obtain ⟨b, hb, hin⟩ := h
        exact ⟨b, hb, hin⟩
    by_cases hc : k ≤ (torusHotLumps (Tb.stepParameters y) (topField (Tb.stepParameters y) (s + 1) n w)).card
    · exact Or.inl hc
    · refine Or.inr ?_
      show k ≤ ((show Finset (TorusBond (n * (Tb.stepParameters y).side)) from w.2.2.2).image
        fun e => parentBlock (Tb.stepParameters y).side e.1).card
      omega
end Proof
end YangMills.Construction.HullsInEveryVolume
end
