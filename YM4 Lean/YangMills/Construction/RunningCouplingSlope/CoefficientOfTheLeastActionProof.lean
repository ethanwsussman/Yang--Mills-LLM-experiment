import YangMills.Construction.ClusterExpansionOfAStep.ColdExpansionOfFourDensitiesProofForm
import YangMills.Construction.ClusterExpansionOfAStep.FormOfTheShares
import YangMills.Construction.LawInAState.WilsonSharesAreACurvatureFamily
import YangMills.Construction.QuaternionicWilsonModel.TheSeamsOfTheModelProof
import YangMills.Construction.RunningCouplingSlope.DensityOfTheStepIsLocalProof
import YangMills.Construction.RunningCouplingSlope.NumberOfALocalDensity
import YangMills.Construction.RunningCouplingSlope.StepTotalsHaveCoefficientsProof
import YangMills.Construction.RunningCouplingSlope.TotalAtTheLeastFieldProof
import YangMills.Construction.SummableBoundsOfTheFlow.TiltOfTheImageProof
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Topology Quaternion
namespace YangMills.Construction.RunningCouplingSlope.MinimalActionCoefficient
open YangMills.Construction.BlockAverages YangMills.Construction.TorusFields YangMills.Construction.TorusLumps YangMills.Construction.SlopeCoefficient YangMills.Construction.ShareFamilies YangMills.Construction.StepCosts YangMills.Construction.FreeBonds YangMills.Construction.RenormalizationStepParameters Filter
section Near
variable {n : ℕ}
private def BondsNearOne (ε : ℝ) (V : TorusField n) : Prop :=
  ∀ x i, ‖((V x i : UnitQuaternion) : ℍ[ℝ]) - 1‖ < ε
private theorem norm_inv_sub_one (g : UnitQuaternion) :
    ‖((g⁻¹ : UnitQuaternion) : ℍ[ℝ]) - 1‖ = ‖(g : ℍ[ℝ]) - 1‖ := by apply _root_.YangMills.Construction.BlockAverages.norm_coe_inv_sub_one <;> assumption
private theorem norm_mul_sub_one_le (g h : UnitQuaternion) :
    ‖((g * h : UnitQuaternion) : ℍ[ℝ]) - 1‖ ≤ ‖(g : ℍ[ℝ]) - 1‖ + ‖(h : ℍ[ℝ]) - 1‖ := by apply _root_.YangMills.Construction.BlockAverages.norm_coe_mul_sub_one_le <;> assumption
private theorem isCold_of_bondsNearOne {s : ℝ} {W : TorusField n} (h : BondsNearOne (s / 4) W) : IsCold s W := by
  intro x μ ν _
  unfold curvature holonomy
  have a1 := norm_mul_sub_one_le (W x μ * W (x + TorusFields.unitStep n μ) ν *
    (W (x + TorusFields.unitStep n ν) μ)⁻¹) (W x ν)⁻¹
  have a2 := norm_mul_sub_one_le (W x μ * W (x + TorusFields.unitStep n μ) ν)
    (W (x + TorusFields.unitStep n ν) μ)⁻¹
  have a3 := norm_mul_sub_one_le (W x μ) (W (x + TorusFields.unitStep n μ) ν)
  rw [norm_inv_sub_one] at a1 a2
  have b1 := h x μ
  have b2 := h (x + TorusFields.unitStep n μ) ν
  have b3 := h (x + TorusFields.unitStep n ν) μ
  have b4 := h x ν
  linarith
private theorem eventually_bondsNearOne [NeZero n] {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ V in 𝓝 (trivialField n), BondsNearOne ε V := by
  unfold BondsNearOne
  rw [eventually_all]
  intro x
  rw [eventually_all]
  intro i
  have hc : Continuous fun V : TorusField n => ‖((V x i : UnitQuaternion) : ℍ[ℝ]) - 1‖ :=
    (((continuous_subtype_val.comp ((continuous_apply i).comp (continuous_apply x))).sub
      continuous_const)).norm
  have h0 : ‖((trivialField n x i : UnitQuaternion) : ℍ[ℝ]) - 1‖ < ε := by
    simpa [trivialField] using hε
  exact hc.continuousAt.eventually (gt_mem_nhds h0)
private theorem exists_bond_of_transports [NeZero n] (g : TorusIsometry) {W W' : TorusField n}
    (h : g.Transports W W') (y : TorusSite n) (j : Fin 4) :
    ∃ (x : TorusSite n) (k : Fin 4), W' y j = W x k ∨ (W' y j)⁻¹ = W x k := by apply _root_.YangMills.SharedProofs.p7027 <;> assumption
private theorem bondsNearOne_of_transports [NeZero n] (g : TorusIsometry) {W W' : TorusField n} {ε : ℝ}
    (h : g.Transports W W') (hW : BondsNearOne ε W) : BondsNearOne ε W' := by
  intro y j
  obtain ⟨x, k, e | e⟩ := exists_bond_of_transports g h y j
  · rw [e]
    exact hW x k
  · have := hW x k
    rw [← e, norm_inv_sub_one] at this
    exact this
private theorem tendsto_perturb_trivial {k : ℕ} (c : Fin k → TorusBond n) (X : Fin k → imaginaryQuaternions) :
    Tendsto (fun σ : Fin k → ℝ => perturb c X σ (trivialField n)) (𝓝 0) (𝓝 (trivialField n)) := by apply _root_.YangMills.Construction.RunningCouplingSlope.StepGaugeTotals.tendsto_perturb_trivialField <;> assumption
private theorem tendsto_gaugeTransform :
    Tendsto (fun p : (TorusSite n → UnitQuaternion) × TorusField n => _root_.YangMills.Construction.TorusFields.gaugeTransform p.1 p.2)
      (𝓝 (1, trivialField n)) (𝓝 (trivialField n)) := by apply _root_.YangMills.SharedProofs.p29867 <;> assumption
private theorem tendsto_constant_gaugeTransform (g : UnitQuaternion) :
    Tendsto (fun V : TorusField n => _root_.YangMills.Construction.TorusFields.gaugeTransform (fun _ => g) V) (𝓝 (trivialField n)) (𝓝 (trivialField n)) := by apply _root_.YangMills.SharedProofs.p78957 <;> assumption
end Near
section Congruence
variable {n : ℕ}
private def AgreeNearTrivial (ε : ℝ) (H H' : GaugeTotal) (n : ℕ) : Prop :=
  ∀ V : TorusField n, BondsNearOne ε V → H n V = H' n V
private theorem isGaugeTotalAt_congr [NeZero n] {ε : ℝ} (hε : 0 < ε) {H H' : GaugeTotal}
    (e : AgreeNearTrivial ε H H' n) (h : IsGaugeTotalAt H n) : IsGaugeTotalAt H' n where
  contDiffAt_perturb := fun k c X => by
    refine (h.contDiffAt_perturb k c X).congr_of_eventuallyEq ?_
    filter_upwards [(tendsto_perturb_trivial c X).eventually (eventually_bondsNearOne hε)] with σ hσ
    exact (e _ hσ).symm
  gauge_invariant_near := by
    have hs : Tendsto (Prod.snd : (TorusSite n → UnitQuaternion) × TorusField n → TorusField n)
        (𝓝 (1, trivialField n)) (𝓝 (trivialField n)) :=
      continuous_snd.tendsto _
    filter_upwards [h.gauge_invariant_near, tendsto_gaugeTransform.eventually (eventually_bondsNearOne hε),
      hs.eventually (eventually_bondsNearOne hε)] with p a b c
    rw [← e _ b, ← e _ c, a]
  constant_gauge_invariant := fun g => by
    filter_upwards [h.constant_gauge_invariant g,
      (tendsto_constant_gaugeTransform g).eventually (eventually_bondsNearOne hε),
      eventually_bondsNearOne hε] with V a b c
    rw [← e _ b, ← e _ c, a]
  isometry_invariant := fun g => by
    filter_upwards [h.isometry_invariant g, eventually_bondsNearOne hε] with V a b V' hc
    rw [← e _ b, ← e _ (bondsNearOne_of_transports g hc b), a V' hc]
private theorem hessianAtTrivial_congr [NeZero n] {ε : ℝ} (hε : 0 < ε) {H H' : GaugeTotal}
    (e : AgreeNearTrivial ε H H' n) (c c' : TorusBond n) (X X' : imaginaryQuaternions) :
    hessianAtTrivial H n c c' X X' = hessianAtTrivial H' n c c' X X' := by
  unfold hessianAtTrivial mixedDeriv
  have hev : (fun σ : Fin 2 → ℝ => H n (perturb ![c, c'] ![X, X'] σ (trivialField n))) =ᶠ[𝓝 0]
      fun σ => H' n (perturb ![c, c'] ![X, X'] σ (trivialField n)) := by
    filter_upwards [(tendsto_perturb_trivial ![c, c'] ![X, X']).eventually (eventually_bondsNearOne hε)]
      with σ hσ
    exact e _ hσ
  rw [(Filter.EventuallyEq.iteratedFDeriv ℝ hev 2).eq_of_nhds]
private theorem hasSlopeCoefficient_congr {l : Filter ℕ} {ε : ℝ} (hε : 0 < ε) {H H' : GaugeTotal} {b : ℝ}
    (hpos : ∀ᶠ n in l, n ≠ 0) (e : ∀ᶠ n in l, AgreeNearTrivial ε H H' n) (h : HasSlopeCoefficient l H b) :
    HasSlopeCoefficient l H' b := by
  obtain ⟨K, hK, hS⟩ := h
  refine ⟨K, ⟨?_, ?_, fun c c' X X' => ?_⟩, hS⟩
  · filter_upwards [hpos, e, hK.eventually_isGaugeTotalAt] with n p a t
    have : NeZero n := ⟨p⟩
    exact isGaugeTotalAt_congr hε a t
  · obtain ⟨M, θ, hθ, hd⟩ := hK.exp_decay
    refine ⟨M, θ, hθ, ?_⟩
    filter_upwards [hpos, e, hd] with n p a d c c' X X' hX hX'
    have : NeZero n := ⟨p⟩
    rw [← hessianAtTrivial_congr hε a]
    exact d c c' X X' hX hX'
  · refine (hK.tendsto_kernel c c' X X').congr' ?_
    filter_upwards [hpos, e] with n p a
    have : NeZero n := ⟨p⟩
    exact hessianAtTrivial_congr hε a _ _ _ _
end Congruence
section Family
variable {ℓ : _root_.YangMills.Construction.TorusLumps.StepParameters} {C : ℝ} {f : LocalDensity}
private theorem weight_pos (ℓ : _root_.YangMills.Construction.TorusLumps.StepParameters) (m : ℕ) : 0 < ℓ.weight m := by apply _root_.YangMills.Construction.WilsonExpansion.weight_pos <;> assumption
private theorem weightRate_pos (hrt : 0 < ℓ.rt) : 0 < ℓ.weightRate := by
  unfold StepParameters.weightRate
  positivity
private theorem div_weight_le (hC : 0 ≤ C) (m : ℕ) :
    C / ℓ.weight m ≤ C * Real.exp (-(ℓ.weightRate * m)) := by
  unfold StepParameters.weight
  have h1 : Real.exp (ℓ.weightRate * m) ≤ max 1 (((m : ℝ) / ℓ.n₁) ^ 16000) * Real.exp (ℓ.weightRate * m) :=
    le_mul_of_one_le_left (Real.exp_pos _).le (le_max_left _ _)
  rw [Real.exp_neg, ← div_eq_mul_inv]
  exact div_le_div_of_nonneg_left hC (Real.exp_pos _) h1
private theorem trivialField_isCold (hσ : 0 < ℓ.threshold) (n : ℕ) : IsCold ℓ.threshold (trivialField n) := by apply _root_.YangMills.Construction.TorusLumps.DensityExpansion.trivialField_isCold <;> assumption
private theorem eventually_isCold {n : ℕ} [NeZero n] (hσ : 0 < ℓ.threshold) :
    ∀ᶠ V in 𝓝 (trivialField n), IsCold ℓ.threshold V :=
  (eventually_bondsNearOne (show 0 < ℓ.threshold / 4 by positivity)).mono fun _ hV => isCold_of_bondsNearOne hV
private theorem areUnitVectors_pair {X X' : imaginaryQuaternions} (hX : ‖X‖ = 1) (hX' : ‖X'‖ = 1) :
    AreUnitVectors ![X, X'] := by apply _root_.YangMills.SharedProofs.p1051 <;> assumption
private theorem centeredDensityTotal_eq {n : ℕ} [NeZero n] (V : TorusField n) :
    centeredDensityTotal f n V = ∑ y, centered f n y V := by
  simp [centeredDensityTotal, NeZero.ne n]
private theorem minimalActionTotal_eq {n : ℕ} [NeZero n] (a : ℝ) (L t : ℕ) (V : TorusField n) :
    minimalActionTotal a L t n V = actionAtLevel a L t Finset.univ V := by
  simp [minimalActionTotal, NeZero.ne n]
private theorem unitPlaneCurvature_antisymm (μ ν : Fin 4) :
    unitPlaneCurvature μ ν = -unitPlaneCurvature ν μ := by apply _root_.YangMills.SharedProofs.p4715 <;> assumption
private theorem isLocalGaugeDensity_of_curvatureFamily (hσ : 0 < ℓ.threshold) (hrt : 0 < ℓ.rt) (hC : 0 ≤ C)
    (hn₀ : 0 < ℓ.n₀) (hc : IsCurvatureFamily ℓ C f) (hlim : HasLimitSecondDeriv f) : IsLocalGaugeDensity f where
  contDiffAt := by
    filter_upwards [eventually_ge_atTop ℓ.n₀] with n hn y k c X
    have i1 : NeZero n := ⟨by omega⟩
    exact (hc.smooth n hn y (trivialField n) (trivialField_isCold hσ n) k c X).of_le (by norm_num)
  gauge_invariant := by
    filter_upwards [eventually_ge_atTop ℓ.n₀] with n hn y
    have i1 : NeZero n := ⟨by omega⟩
    have hs : Tendsto (Prod.snd : (TorusSite n → UnitQuaternion) × TorusField n → TorusField n)
        (𝓝 (1, trivialField n)) (𝓝 (trivialField n)) :=
      continuous_snd.tendsto _
    filter_upwards [hs.eventually (eventually_isCold hσ)] with p hp
    exact hc.gauge n hn y p.1 p.2 hp
  translation_invariant := by
    filter_upwards [eventually_ge_atTop ℓ.n₀] with n hn y u
    have i1 : NeZero n := ⟨by omega⟩
    filter_upwards [eventually_isCold hσ] with V hV
    exact hc.translation n hn y u V hV
  kernel_decay := by
    refine ⟨C, ℓ.weightRate, weightRate_pos hrt, ?_⟩
    filter_upwards [eventually_ge_atTop ℓ.n₀] with n hn c c' X X' hX hX'
    have i1 : NeZero n := ⟨by omega⟩
    have h := hc.decay n hn 0 (trivialField n) (trivialField_isCold hσ n) 2 ![c, c'] ![X, X'] (by norm_num)
      (by norm_num) (areUnitVectors_pair hX hX')
    exact h.trans (div_weight_le hC _)
  tendsto := hlim
private theorem isGaugeTotalAt_of_curvatureFamily (hσ : 0 < ℓ.threshold) (hc : IsCurvatureFamily ℓ C f)
    (hcar : SumInvariantUnderIsometries ℓ f) {n : ℕ} [NeZero n] (hn : ℓ.n₀ ≤ n) :
    IsGaugeTotalAt (centeredDensityTotal f) n where
  contDiffAt_perturb := fun k c X => by
    have e : (fun σ : Fin k → ℝ => centeredDensityTotal f n (perturb c X σ (trivialField n))) =
        fun σ => ∑ y, (f n y (perturb c X σ (trivialField n)) - f n y (trivialField n)) := by
      funext σ
      rw [centeredDensityTotal_eq]
      rfl
    rw [e]
    refine ContDiffAt.sum fun y _ => ?_
    exact ((hc.smooth n hn y (trivialField n) (trivialField_isCold hσ n) k c X).of_le (by norm_num)).sub
      contDiffAt_const
  gauge_invariant_near := by
    have hs : Tendsto (Prod.snd : (TorusSite n → UnitQuaternion) × TorusField n → TorusField n)
        (𝓝 (1, trivialField n)) (𝓝 (trivialField n)) :=
      continuous_snd.tendsto _
    filter_upwards [hs.eventually (eventually_isCold hσ)] with p hp
    rw [centeredDensityTotal_eq, centeredDensityTotal_eq]
    refine Finset.sum_congr rfl fun y _ => ?_
    simp only [centered]
    rw [hc.gauge n hn y p.1 p.2 hp]
  constant_gauge_invariant := fun g => by
    filter_upwards [eventually_isCold hσ] with V hV
    rw [centeredDensityTotal_eq, centeredDensityTotal_eq]
    refine Finset.sum_congr rfl fun y _ => ?_
    simp only [centered]
    rw [hc.gauge n hn y _ V hV]
  isometry_invariant := fun g => by
    filter_upwards [eventually_bondsNearOne (n := n) (show 0 < ℓ.threshold / 4 by positivity)] with V hV V' hg
    rw [centeredDensityTotal_eq, centeredDensityTotal_eq]
    exact hcar n hn g V V' (isCold_of_bondsNearOne hV)
      (isCold_of_bondsNearOne (bondsNearOne_of_transports g hg hV)) hg
private theorem norm_quaternionI : ‖quaternionI‖ = 1 := by apply _root_.YangMills.SharedProofs.p9532 <;> assumption
private theorem curvaturePairing_unitPlane : curvaturePairing unitPlaneCurvature unitPlaneCurvature = 1 := by apply _root_.YangMills.SharedProofs.p11741 <;> assumption
private theorem bound_nonneg (hσ : 0 < ℓ.threshold) (hn₀ : 0 < ℓ.n₀) (hc : IsCurvatureFamily ℓ C f) : 0 ≤ C := by
  have : NeZero ℓ.n₀ := ⟨by omega⟩
  have h := hc.decay ℓ.n₀ le_rfl 0 (trivialField ℓ.n₀) (trivialField_isCold hσ ℓ.n₀) 1 (fun _ => (0, 0))
    (fun _ => quaternionI) le_rfl (by norm_num) (fun _ => norm_quaternionI)
  have hw := weight_pos ℓ (supportDiam (0 : TorusSite ℓ.n₀) (fun _ : Fin 1 => ((0, 0) : TorusBond ℓ.n₀)))
  have h0 := mul_nonneg ((abs_nonneg _).trans h) hw.le
  rwa [div_mul_cancel₀ _ hw.ne'] at h0
private theorem hasSlopeCoefficient_one (hCoef : LocalDensityCoefficient.Claim)
    (hNum : CoefficientFromDensity.Claim) (hfit : ℓ.Admissible) {a : ℝ} {L t : ℕ}
    (hc : IsCurvatureFamily ℓ C f) (hcar : SumInvariantUnderIsometries ℓ f) (hform : HasCurvatureForm f 1)
    (hsum : ∀ (n : ℕ) [NeZero n], ℓ.n₀ ≤ n → ∀ V : TorusField n, IsCold ℓ.threshold V →
      ∑ z, centered f n z V = actionAtLevel a L t Finset.univ V) :
    HasSlopeCoefficient atTop (minimalActionTotal a L t) 1 := by
  have hσ := hfit.σ_pos
  have hn₀ : 0 < ℓ.n₀ := by
    have := hfit.n₀_ge
    omega
  have hC := bound_nonneg hσ hn₀ hc
  have hloc : IsLocalGaugeDensity f :=
    isLocalGaugeDensity_of_curvatureFamily hσ hfit.rt_pos hC hn₀ hc hform.1
  have htot : ∀ᶠ n in atTop, IsGaugeTotalAt (centeredDensityTotal f) n := by
    filter_upwards [eventually_ge_atTop ℓ.n₀] with n hn
    have i1 : NeZero n := ⟨by omega⟩
    exact isGaugeTotalAt_of_curvatureFamily hσ hc hcar hn
  have hnear : ∀ᶠ n in atTop, ∀ᶠ V in 𝓝 (trivialField n),
      centeredDensityTotal f n V = centeredDensityTotal f n V :=
    Eventually.of_forall fun _ => Eventually.of_forall fun _ => rfl
  obtain ⟨b, hb⟩ := hCoef f (centeredDensityTotal f) hloc htot hnear
  have hs := hNum f _ b hloc hb hnear
  have h1 := hform.2 unitPlaneCurvature unitPlaneCurvature unitPlaneCurvature_antisymm
    unitPlaneCurvature_antisymm
  rw [curvaturePairing_unitPlane, mul_one] at h1
  have e : b = 1 := hs.unique h1
  subst e
  refine hasSlopeCoefficient_congr (show 0 < ℓ.threshold / 4 by positivity) ?_ ?_ hb
  · filter_upwards [eventually_ge_atTop ℓ.n₀] with n hn
    omega
  · filter_upwards [eventually_ge_atTop ℓ.n₀] with n hn V hV
    have i1 : NeZero n := ⟨by omega⟩
    rw [centeredDensityTotal_eq, minimalActionTotal_eq]
    exact hsum n hn V (isCold_of_bondsNearOne hV)
end Family
section Bottom
variable {n : ℕ}
private theorem wilsonAction_trivialField [NeZero n] :
    TorusFields.wilsonAction (Finset.univ : Finset (TorusSite n)) (trivialField n) = 0 := by apply _root_.YangMills.Construction.ModelSeamsProof.wilsonAction_trivialField <;> assumption
private theorem levelShareFamily_zero [NeZero n] (a : ℝ) (L : ℕ) (y : TorusSite n) (V : TorusField n) :
    levelShareFamily a L 0 n y V = levelShare a L 0 Finset.univ y V := by
  simp [levelShareFamily, NeZero.ne n]
private theorem sum_centered_levelShareFamily_zero [NeZero n] (a : ℝ) (L : ℕ) (V : TorusField n) :
    ∑ z, centered (levelShareFamily a L 0) n z V = actionAtLevel a L 0 Finset.univ V := by
  simp only [centered, Finset.sum_sub_distrib, levelShareFamily_zero]
  rw [sum_levelShare_zero, sum_levelShare_zero]
  show TorusFields.wilsonAction Finset.univ V - TorusFields.wilsonAction Finset.univ (trivialField n) =
    TorusFields.wilsonAction Finset.univ V
  rw [wilsonAction_trivialField, sub_zero]
end Bottom
theorem minimalActionHasUnitCoefficient (hCoef : LocalDensityCoefficient.Claim)
    (hNum : CoefficientFromDensity.Claim) (hShares : LevelSharesFormCurvatureFamily)
    (hForm : LevelSharesHaveUnitCurvatureForm) (hWilson : WilsonSharesFormCurvatureFamily) :
    MinimalActionHasUnitCoefficient := by
  intro T hD t
  have hF := hD.fits T.floorMin le_rfl
  cases t with
  | zero =>
    obtain ⟨C, -, hfam, hform⟩ := hWilson _ hF
    refine hasSlopeCoefficient_one hCoef hNum hF hfam ?_ hform fun n _ _ V _ =>
      sum_centered_levelShareFamily_zero _ _ V
    intro n _ _ g W W' _ _ hg
    rw [sum_centered_levelShareFamily_zero, sum_centered_levelShareFamily_zero]
    exact wilsonAction_of_transports hg
  | succ t =>
    obtain ⟨hfam, hcar, hsum⟩ := hShares T hD T.floorMin le_rfl t
    exact hasSlopeCoefficient_one hCoef hNum hF hfam hcar (hForm T hD t) hsum
end YangMills.Construction.RunningCouplingSlope.MinimalActionCoefficient
end
