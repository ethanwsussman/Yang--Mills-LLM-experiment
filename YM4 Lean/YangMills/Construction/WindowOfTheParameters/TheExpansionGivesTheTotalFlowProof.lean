import YangMills.Construction.RunningCouplingSlope.CoefficientOfTheLeastAction
import YangMills.Construction.RunningCouplingSlope.CoefficientsAdd
import YangMills.Construction.RunningCouplingSlope.DensitiesOfAnExpansionHaveNoCoefficient
import YangMills.Construction.RunningCouplingSlope.StepTotalsHaveCoefficientsProof
import YangMills.Construction.RunningCouplingSlope.TotalAtTheLeastFieldProof
import YangMills.Construction.WindowOfTheParameters.TheExpansionGivesTheTotalFlow
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Topology Quaternion
open Filter
namespace YangMills.Construction
open TorusFields TorusLumps RenormalizationStepParameters SlopeCoefficient RunningCouplingSlope
open BlockAverages hiding unitStep gaugeTransform
namespace TotalDensityFlow
section NearTrivial
variable {n : ℕ}
private def BondsNearOne (ε : ℝ) (V : TorusField n) : Prop :=
  ∀ x i, ‖((V x i : UnitQuaternion) : ℍ[ℝ]) - 1‖ < ε
private theorem norm_inv_sub_one (g : UnitQuaternion) :
    ‖((g⁻¹ : UnitQuaternion) : ℍ[ℝ]) - 1‖ = ‖(g : ℍ[ℝ]) - 1‖ := by apply _root_.YangMills.Construction.BlockAverages.norm_coe_inv_sub_one <;> assumption
private theorem norm_mul_sub_one_le (g h : UnitQuaternion) :
    ‖((g * h : UnitQuaternion) : ℍ[ℝ]) - 1‖ ≤ ‖(g : ℍ[ℝ]) - 1‖ + ‖(h : ℍ[ℝ]) - 1‖ := by apply _root_.YangMills.Construction.BlockAverages.norm_coe_mul_sub_one_le <;> assumption
private theorem isCold_of_bondsNearOne {s : ℝ} {W : TorusField n} (h : BondsNearOne (s / 4) W) :
    IsCold s W := by
  intro x μ ν _
  unfold curvature holonomy
  have a1 := norm_mul_sub_one_le (W x μ * W (x + unitStep n μ) ν * (W (x + unitStep n ν) μ)⁻¹) (W x ν)⁻¹
  have a2 := norm_mul_sub_one_le (W x μ * W (x + unitStep n μ) ν) (W (x + unitStep n ν) μ)⁻¹
  have a3 := norm_mul_sub_one_le (W x μ) (W (x + unitStep n μ) ν)
  rw [norm_inv_sub_one] at a1 a2
  have b1 := h x μ
  have b2 := h (x + unitStep n μ) ν
  have b3 := h (x + unitStep n ν) μ
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
private theorem tendsto_perturb {k : ℕ} (c : Fin k → TorusBond n) (X : Fin k → imaginaryQuaternions) :
    Tendsto (fun σ : Fin k → ℝ => perturb c X σ (trivialField n)) (𝓝 0) (𝓝 (trivialField n)) := by apply _root_.YangMills.Construction.RunningCouplingSlope.StepGaugeTotals.tendsto_perturb_trivialField <;> assumption
private theorem tendsto_gaugeTransform :
    Tendsto (fun p : (TorusSite n → UnitQuaternion) × TorusField n => gaugeTransform p.1 p.2)
      (𝓝 (1, trivialField n)) (𝓝 (trivialField n)) := by apply _root_.YangMills.SharedProofs.p29867 <;> assumption
private theorem tendsto_constGaugeTransform (g : UnitQuaternion) :
    Tendsto (fun V : TorusField n => gaugeTransform (fun _ => g) V) (𝓝 (trivialField n))
      (𝓝 (trivialField n)) := by apply _root_.YangMills.SharedProofs.p78957 <;> assumption
end NearTrivial
section Congruence
variable {n : ℕ}
private def EqOnNearOne (ε : ℝ) (H H' : GaugeTotal) (n : ℕ) : Prop :=
  ∀ V : TorusField n, BondsNearOne ε V → H n V = H' n V
private theorem isGaugeTotalAt_congr [NeZero n] {ε : ℝ} (hε : 0 < ε) {H H' : GaugeTotal}
    (e : EqOnNearOne ε H H' n) (h : IsGaugeTotalAt H n) : IsGaugeTotalAt H' n where
  contDiffAt_perturb := fun k c X => by
    refine (h.contDiffAt_perturb k c X).congr_of_eventuallyEq ?_
    filter_upwards [(tendsto_perturb c X).eventually (eventually_bondsNearOne hε)] with σ hσ
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
      (tendsto_constGaugeTransform g).eventually (eventually_bondsNearOne hε),
      eventually_bondsNearOne hε] with V a b c
    rw [← e _ b, ← e _ c, a]
  isometry_invariant := fun g => by
    filter_upwards [h.isometry_invariant g, eventually_bondsNearOne hε] with V a b V' hc
    rw [← e _ b, ← e _ (bondsNearOne_of_transports g hc b), a V' hc]
private theorem hessianAtTrivial_congr [NeZero n] {ε : ℝ} (hε : 0 < ε) {H H' : GaugeTotal}
    (e : EqOnNearOne ε H H' n) (c c' : TorusBond n) (X X' : imaginaryQuaternions) :
    hessianAtTrivial H n c c' X X' = hessianAtTrivial H' n c c' X X' := by
  unfold hessianAtTrivial mixedDeriv
  have hev : (fun σ : Fin 2 → ℝ => H n (perturb ![c, c'] ![X, X'] σ (trivialField n))) =ᶠ[𝓝 0]
      fun σ => H' n (perturb ![c, c'] ![X, X'] σ (trivialField n)) := by
    filter_upwards [(tendsto_perturb ![c, c'] ![X, X']).eventually (eventually_bondsNearOne hε)] with σ hσ
    exact e _ hσ
  rw [(Filter.EventuallyEq.iteratedFDeriv ℝ hev 2).eq_of_nhds]
private theorem hasSlopeCoefficient_congr {l : Filter ℕ} {ε : ℝ} (hε : 0 < ε) {H H' : GaugeTotal} {b : ℝ}
    (hpos : ∀ᶠ n in l, n ≠ 0) (e : ∀ᶠ n in l, EqOnNearOne ε H H' n) (h : HasSlopeCoefficient l H b) :
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
section Scaling
variable {n : ℕ}
private def smulTotal (r : ℝ) (H : GaugeTotal) : GaugeTotal := fun n V => r * H n V
private theorem isGaugeTotalAt_smulTotal (r : ℝ) {H : GaugeTotal} (h : IsGaugeTotalAt H n) :
    IsGaugeTotalAt (smulTotal r H) n where
  contDiffAt_perturb := fun k c X => contDiffAt_const.mul (h.contDiffAt_perturb k c X)
  gauge_invariant_near := by
    filter_upwards [h.gauge_invariant_near] with p a
    simp only [smulTotal, a]
  constant_gauge_invariant := fun g => by
    filter_upwards [h.constant_gauge_invariant g] with V a
    simp only [smulTotal, a]
  isometry_invariant := fun g => by
    filter_upwards [h.isometry_invariant g] with V a V' hc
    simp only [smulTotal, a V' hc]
private theorem hessianAtTrivial_smulTotal (r : ℝ) {H : GaugeTotal} (h : IsGaugeTotalAt H n)
    (c c' : TorusBond n) (X X' : imaginaryQuaternions) :
    hessianAtTrivial (smulTotal r H) n c c' X X' = r * hessianAtTrivial H n c c' X X' := by
  unfold hessianAtTrivial mixedDeriv
  have e := iteratedFDeriv_const_smul_apply (𝕜 := ℝ) (i := 2) (a := r)
    (h.contDiffAt_perturb 2 ![c, c'] ![X, X'])
  have e2 : (fun σ : Fin 2 → ℝ => smulTotal r H n (perturb ![c, c'] ![X, X'] σ (trivialField n))) =
      r • fun σ => H n (perturb ![c, c'] ![X, X'] σ (trivialField n)) := rfl
  rw [e2, e]
  rfl
private theorem hasSlopeCoefficient_smulTotal (r : ℝ) {H : GaugeTotal} {b : ℝ}
    (h : HasSlopeCoefficient atTop H b) : HasSlopeCoefficient atTop (smulTotal r H) (r * b) := by
  obtain ⟨K, hK, hS⟩ := h
  obtain ⟨M, θ, hθ, hd⟩ := hK.exp_decay
  refine ⟨fun c c' => r * K c c', ⟨?_, ⟨|r| * M, θ, hθ, ?_⟩, fun c c' X X' => ?_⟩, ?_⟩
  · filter_upwards [hK.eventually_isGaugeTotalAt] with n t
    exact isGaugeTotalAt_smulTotal r t
  · filter_upwards [hK.eventually_isGaugeTotalAt, hd] with n t d c c' X X' hX hX'
    rw [hessianAtTrivial_smulTotal r t, abs_mul, mul_assoc]
    exact mul_le_mul_of_nonneg_left (d c c' X X' hX hX') (abs_nonneg r)
  · have h := (hK.tendsto_kernel c c' X X').const_mul r
    have e : r * (inner ℝ (X : ℍ[ℝ]) (X' : ℍ[ℝ]) * K c c') =
        inner ℝ (X : ℍ[ℝ]) (X' : ℍ[ℝ]) * (r * K c c') := by
      ring
    rw [e] at h
    refine h.congr' ?_
    filter_upwards [hK.eventually_isGaugeTotalAt] with n t
    exact (hessianAtTrivial_smulTotal r t _ _ _ _).symm
  · have e : secondMomentTerm (fun c c' => r * K c c') = fun z => r * secondMomentTerm K z := by
      funext z
      simp only [secondMomentTerm]
      ring
    rw [e]
    exact hS.mul_left r
end Scaling
section Sides
private theorem sideFilter_le_atTop {L : ℕ} (hL : 1 < L) : sideFilter L ≤ atTop := by
  exact show Tendsto (fun q : ℕ => 2 * L ^ q) atTop atTop from
    tendsto_atTop_mono (fun q => Nat.le_mul_of_pos_left _ (by norm_num))
      (tendsto_pow_atTop_atTop_of_one_lt hL)
private theorem hasSlopeCoefficient_mono {l l' : Filter ℕ} (hl : l ≤ l') {H : GaugeTotal} {b : ℝ}
    (h : HasSlopeCoefficient l' H b) : HasSlopeCoefficient l H b := by
  obtain ⟨K, hK, hS⟩ := h
  obtain ⟨M, θ, hθ, hd⟩ := hK.exp_decay
  exact ⟨K, ⟨hK.eventually_isGaugeTotalAt.filter_mono hl, ⟨M, θ, hθ, hd.filter_mono hl⟩,
    fun c c' X X' => (hK.tendsto_kernel c c' X X').mono_left hl⟩, hS⟩
end Sides
section Expansion
variable {ℓ : StepParameters} {t : ℕ} {x : ℝ} {D : TorusFunctional} {f : LocalDensity}
private theorem eqOnNearOne_of_expansion (hrow : ColdExpansion ℓ t x D f) {n : ℕ} (hn : ℓ.n₀ ≤ n)
    (h0 : n ≠ 0) :
    EqOnNearOne (ℓ.threshold / 4)
      (addGaugeTotal (smulTotal (-x) (minimalActionTotal ℓ.coupling ℓ.side t)) (centeredDensityTotal f))
      (logRatio D) n := by
  intro V hV
  have : NeZero n := ⟨h0⟩
  have h := hrow.form n hn V (isCold_of_bondsNearOne hV)
  simp only [addGaugeTotal, smulTotal, minimalActionTotal, centeredDensityTotal, logRatio, dif_neg h0]
  exact h.symm
private theorem hasNextCoupling_of_expansion {T : ParameterAssignment} {z : ℝ}
    (hleast : MinimalActionHasUnitCoefficient) (hdens : ColdDensitiesHaveZeroCoefficient)
    (hadd : SlopeCoefficientAdditive) (hDr : T.Admissible) (hfit : (T.stepParameters z).Admissible)
    (hL : Conventions.IsAdmissibleBlockingFactor (T.stepParameters z).side)
    (h : HasExpansion (T.stepParameters z) t x D) :
    HasNextCoupling (T.stepParameters z).side D x := by
  set ℓ := T.stepParameters z with hℓ
  obtain ⟨harr, f, hrow, -⟩ := h
  have hσ : 0 < ℓ.threshold := hfit.σ_pos
  have hL1 : 1 < ℓ.side := by
    have := hL.2
    omega
  have hsides := sideFilter_le_atTop hL1
  have hbig : ∀ᶠ n in sideFilter ℓ.side, ℓ.n₀ ≤ n ∧ n ≠ 0 := by
    have h1 : ∀ᶠ n : ℕ in atTop, ℓ.n₀ + 1 ≤ n := eventually_ge_atTop _
    refine (h1.filter_mono hsides).mono fun n hn => ⟨by omega, by omega⟩
  have hA := hleast T hDr t
  have hD := (hdens T z t x 1 D f hDr hfit one_pos le_rfl harr hrow).1
  have hS := hadd.1 _ _ _ _ (hasSlopeCoefficient_smulTotal (-x) hA) hD
  refine ⟨?_, ?_⟩
  · filter_upwards [hbig] with n hn
    have : NeZero n := ⟨hn.2⟩
    filter_upwards [eventually_bondsNearOne (n := n) (show 0 < ℓ.threshold / 4 by positivity)] with V hV
    exact hrow.positive n hn.1 V (isCold_of_bondsNearOne hV)
  · have e : -x * 1 + 0 = -x := by ring
    rw [e] at hS
    refine hasSlopeCoefficient_congr (show 0 < ℓ.threshold / 4 by positivity)
      (hbig.mono fun n hn => hn.2) ?_ (hasSlopeCoefficient_mono hsides hS)
    exact hbig.mono fun n hn => eqOnNearOne_of_expansion hrow hn.1 hn.2
end Expansion
theorem expansionGivesFlow_of_slopeCoefficients (hleast : MinimalActionHasUnitCoefficient)
    (hdens : ColdDensitiesHaveZeroCoefficient) (hadd : SlopeCoefficientAdditive) :
    ExpansionGivesFlow := by
  intro T z hDr hfit hL β t y h0 hfloor hrow
  refine ⟨h0, fun j hj => lt_of_lt_of_le (lt_of_lt_of_le one_pos hfit.y₁_ge) (hfloor j hj), fun j hj => ?_⟩
  exact hasNextCoupling_of_expansion hleast hdens hadd hDr hfit hL (hrow (j + 1) hj)
end TotalDensityFlow
end YangMills.Construction
end
