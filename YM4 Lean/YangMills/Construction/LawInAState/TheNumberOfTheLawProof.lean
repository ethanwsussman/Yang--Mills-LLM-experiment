import YangMills.Construction.FreeEnergiesOfTheFlow.ScoredTowerOfTheFlow
import YangMills.Construction.LawInAState.ASiteNearThePair
import YangMills.Construction.LawInAState.ConcentrationInOneBoxProof
import YangMills.Construction.LawInAState.MomentsOfTheCentredResponsesProof
import YangMills.Construction.LawInAState.PairOfTheLawIsNearAPointProof
import YangMills.Construction.LawInAState.TheNumberOfAMovedPair
import YangMills.Construction.LawInAState.TheNumberOfTheBox
import YangMills.Construction.LawInAState.TheNumberOfTheLawForm
import YangMills.Construction.PassageToTheLimit.SpaceAsAMetricSpaceTestFunctionsTranslationsReflectionsProof
import YangMills.Construction.ResponseInTheExpansion.NumbersOfAScoredTowerAreTheChain
import YangMills.Construction.ResponseInTheExpansion.NumbersOfTheChainAreOne
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Filter
namespace YangMills.Construction.StateLaws
open InfiniteLattice (AmbientSpace)
namespace CovarianceAtSeparation
private theorem holdsOnParameters_of_holdsAtAdmissible {P : RenormalizationStepParameters.ParameterAssignment → ℝ → Prop}
    (hP : WeightedResponses.HoldsAtAdmissibleParameters P) : ResponseInTheExpansion.HoldsOnParameterFamilies P := by apply _root_.YangMills.SharedProofs.p23606 <;> assumption
private theorem flow_coupling_le_of_steps {ℓ : TorusLumps.StepParameters} (hR : StepReturn.ExpansionReturnsAt ℓ)
    (hW : ∀ β : ℝ, ℓ.y₁ ≤ β → TorusLumps.HasExpansion ℓ 0 β (TorusLumps.wilsonWeight β)) {β : ℝ} {K : ℕ}
    (h : ∀ j ≤ K, ℓ.y₁ ≤ (TorusLumps.couplingFlow ℓ β j).1) (e : ℕ) (he : e ≤ K) :
    (TorusLumps.couplingFlow ℓ β (K - e)).1 ≤ (TorusLumps.couplingFlow ℓ β K).1 + 2 * ℓ.B * e := by apply _root_.YangMills.SharedProofs.p54754 <;> assumption
private theorem eventually_mul_rpow_le_rpow (a b c : ℝ) (hab : a < b) :
    ∀ᶠ x : ℝ in atTop, c * x ^ a ≤ x ^ b := by
  have h : Tendsto (fun x : ℝ => x ^ (b - a)) atTop atTop := tendsto_rpow_atTop (by linarith)
  filter_upwards [h.eventually_ge_atTop c, eventually_gt_atTop 0] with x h1 h2
  have e : x ^ b = x ^ (b - a) * x ^ a := by
    rw [← Real.rpow_add h2]
    congr 1
    ring
  rw [e]
  exact mul_le_mul_of_nonneg_right h1 (Real.rpow_nonneg h2.le _)
private theorem eventually_error_le (C rt : ℝ) (hrt : 0 < rt) :
    ∀ᶠ x : ℝ in atTop, x ^ C * Real.exp (-(4 * rt * (TorusLumps.clusterRange x : ℝ))) ≤ x ^ (-3 : ℝ) := by
  have h1 : Tendsto (fun u : ℝ => u ^ (100 * (C + 3)) * Real.exp (-(4 * rt) * u)) atTop (nhds 0) :=
    tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero _ _ (by positivity)
  have h2 : Tendsto (fun x : ℝ => x ^ ((1 : ℝ) / 100)) atTop atTop := tendsto_rpow_atTop (by norm_num)
  have h3 := (h2.eventually (h1.eventually (ge_mem_nhds (zero_lt_one))))
  filter_upwards [h3, eventually_gt_atTop 0] with x hx hx0
  have e1 : (x ^ ((1 : ℝ) / 100)) ^ (100 * (C + 3)) = x ^ (C + 3) := by
    rw [← Real.rpow_mul hx0.le]
    congr 1
    ring
  rw [e1] at hx
  have hr : x ^ ((1 : ℝ) / 100) ≤ (TorusLumps.clusterRange x : ℝ) := Nat.le_ceil _
  have h4 : Real.exp (-(4 * rt * (TorusLumps.clusterRange x : ℝ))) ≤
      Real.exp (-(4 * rt) * x ^ ((1 : ℝ) / 100)) := by
    apply Real.exp_le_exp.mpr
    have := mul_le_mul_of_nonneg_left hr (by positivity : 0 ≤ 4 * rt)
    linarith
  have e2 : x ^ C = x ^ (-3 : ℝ) * x ^ (C + 3) := by
    rw [← Real.rpow_add hx0]
    congr 1
    ring
  have hp3 : 0 ≤ x ^ (-3 : ℝ) := Real.rpow_nonneg hx0.le _
  calc x ^ C * Real.exp (-(4 * rt * (TorusLumps.clusterRange x : ℝ)))
      ≤ x ^ C * Real.exp (-(4 * rt) * x ^ ((1 : ℝ) / 100)) :=
        mul_le_mul_of_nonneg_left h4 (Real.rpow_nonneg hx0.le _)
    _ = x ^ (-3 : ℝ) * (x ^ (C + 3) * Real.exp (-(4 * rt) * x ^ ((1 : ℝ) / 100))) := by
        rw [e2]
        ring
    _ ≤ x ^ (-3 : ℝ) * 1 := mul_le_mul_of_nonneg_left hx hp3
    _ = x ^ (-3 : ℝ) := mul_one _
private theorem eventually_room (Lr B Xi : ℝ) (hB : 0 < B) : ∀ᶠ x : ℝ in atTop,
    1 ≤ x ∧ 3 ≤ x ∧ 5 * (2 ^ 13 * Lr * (x ^ ((1 : ℝ) / 100) + 1)) + 4 ≤ x ^ ((1 : ℝ) / 27) / 32 ∧
      2 * B * (x ^ ((1 : ℝ) / 27) + 1) + Xi ≤ x ∧ 2 * B * x ^ ((1 : ℝ) / 10) + Xi ≤ x := by
  have h1 := eventually_mul_rpow_le_rpow (1 / 100) (1 / 27) (32 * (5 * 2 ^ 14 * |Lr| + 4)) (by norm_num)
  have h2 := eventually_mul_rpow_le_rpow (1 / 27) 1 (8 * B) (by norm_num)
  have h3 := eventually_mul_rpow_le_rpow (1 / 10) 1 (4 * B) (by norm_num)
  filter_upwards [h1, h2, h3, eventually_ge_atTop (1 : ℝ), eventually_ge_atTop (3 : ℝ),
    eventually_ge_atTop (2 * |Xi| + 8 * B)] with x g1 g2 g3 g4 g5 g6
  have p1 : 1 ≤ x ^ ((1 : ℝ) / 100) := Real.one_le_rpow g4 (by norm_num)
  have p2 : 1 ≤ x ^ ((1 : ℝ) / 27) := Real.one_le_rpow g4 (by norm_num)
  rw [Real.rpow_one] at g2 g3
  have hl : Lr ≤ |Lr| := le_abs_self _
  have hx : Xi ≤ |Xi| := le_abs_self _
  have hx0 : 0 ≤ |Xi| := abs_nonneg _
  refine ⟨g4, g5, ?_, ?_, ?_⟩
  · have e1 : 2 ^ 13 * Lr * (x ^ ((1 : ℝ) / 100) + 1) ≤ 2 ^ 13 * |Lr| * (2 * x ^ ((1 : ℝ) / 100)) := by
      have : x ^ ((1 : ℝ) / 100) + 1 ≤ 2 * x ^ ((1 : ℝ) / 100) := by linarith
      calc 2 ^ 13 * Lr * (x ^ ((1 : ℝ) / 100) + 1) ≤ 2 ^ 13 * |Lr| * (x ^ ((1 : ℝ) / 100) + 1) := by
            apply mul_le_mul_of_nonneg_right _ (by linarith)
            linarith
        _ ≤ 2 ^ 13 * |Lr| * (2 * x ^ ((1 : ℝ) / 100)) :=
            mul_le_mul_of_nonneg_left this (by positivity)
    nlinarith [g1, e1, p1]
  · nlinarith [g2, p2]
  · nlinarith [g3]
private theorem abs_le_euclidNormVec (w : Fin 4 → ℝ) (i : Fin 4) : |w i| ≤ TorusMetric.euclidNormVec w := by apply _root_.YangMills.Construction.Parametrix.UnitKernelSupport.abs_apply_le_euclidNormVec <;> assumption
private theorem euclidNormVec_neg (w : Fin 4 → ℝ) : TorusMetric.euclidNormVec (-w) = TorusMetric.euclidNormVec w := by apply _root_.YangMills.Construction.LimitSpaces.AmbientMetric.euclidNormVec_neg <;> assumption
private theorem norm_le_of_uniformNorm_eq_one {f : AmbientSpace → ℝ} (h : TestFunctions.uniformNorm f = 1)
    (x : AmbientSpace) : ‖f x‖ ≤ 1 := by
  have hb : BddAbove (Set.range fun x => ‖f x‖) := by
    by_contra hn
    have h0 : TestFunctions.uniformNorm f = 0 := Real.iSup_of_not_bddAbove hn
    rw [h] at h0
    exact one_ne_zero h0
  rw [← h]
  exact le_ciSup hb x
private theorem norm_sub_le_lipschitz {f : AmbientSpace → ℝ}
    (hl : TestFunctions.IsLipschitzFor TestFunctions.euclidDistR4 f) (x y : AmbientSpace) :
    ‖f x - f y‖ ≤ TestFunctions.bestLipschitzConstant TestFunctions.euclidDistR4 f * TestFunctions.euclidDistR4 x y := by apply _root_.YangMills.SharedProofs.p56457 <;> assumption
private theorem mem_tsupport_of_translate {g : AmbientSpace → ℝ} {τ x : AmbientSpace}
    (hx : x ∈ tsupport fun y => g (y - τ)) : x - τ ∈ tsupport g := by
  have hcl : IsClosed ((fun y : AmbientSpace => y - τ) ⁻¹' tsupport g) :=
    (isClosed_tsupport g).preimage (continuous_id.sub continuous_const)
  have hsub : Function.support (fun y => g (y - τ)) ⊆ (fun y : AmbientSpace => y - τ) ⁻¹' tsupport g :=
    fun y hy => subset_tsupport g hy
  exact closure_minimal hsub hcl hx
private structure PairGeometry (d vt : ℝ) (f h : AmbientSpace → ℝ) (c : AmbientSpace) : Prop where
  left_cube : ∀ x ∈ tsupport f, ∀ i, |x i - c i| ≤ 5 * d
  right_cube : ∀ x ∈ tsupport h, ∀ i, |x i - c i| ≤ 5 * d
  separated : ∀ u ∈ tsupport f, ∀ u' ∈ tsupport h,
    d ≤ TorusMetric.euclidNormVec (u - u') ∧ TorusMetric.euclidNormVec (u - u') ≤ 10 * d
  kernel_ge : TestPairs.kernelLowerConst * vt ^ 2 ≤ TestFunctions.inverseEighthKernel f h
private theorem exists_pairGeometry (hG : TestPairs.GeometryAndKernelBounds) {d vt : ℝ} {f h : AmbientSpace → ℝ}
    (hd : 0 < d) (h0 : 0 < vt) (h1 : vt ≤ 1) (hp : IsNormalizedTestPair d vt f h) :
    ∃ c, PairGeometry d vt f h c := by
  obtain ⟨x₁, x₂, ⟨a₁, a₂, a₃, a₄, a₅, a₆⟩, ⟨b₁, b₂, b₃, b₄, b₅, b₆⟩, c₁, c₂⟩ := hp.mem_class
  have hcent : TestFunctions.IsCentrePairR4 d vt x₁ x₂ (f, h) := ⟨⟨a₄, a₅, a₆⟩, ⟨b₄, b₅, b₆⟩, c₁, c₂⟩
  obtain ⟨⟨hB1, hB2, hB3, hB4, hB5⟩, -⟩ := hG.1 d vt ⟨hd, h0, h1⟩ x₁ x₂ f h hp.mem_class hcent
  refine ⟨TestPairs.midpointR4 x₁ x₂, fun x hx i => ?_, fun x hx i => ?_, fun u hu u' hu' => hB3 u hu u' hu', ?_⟩
  · exact (abs_le_euclidNormVec (x - TestPairs.midpointR4 x₁ x₂) i).trans (hB2.2 (Or.inl hx))
  · exact (abs_le_euclidNormVec (x - TestPairs.midpointR4 x₁ x₂) i).trans (hB2.2 (Or.inr hx))
  · have e := hB5.1.trans hB5.2.1
    rw [hp.norm_left, hp.norm_right] at e
    simpa using e
private theorem le_euclidNormVec_periodic {d vt : ℝ} {f h : AmbientSpace → ℝ} {c : AmbientSpace} (hd : d ≤ 1 / 8)
    (hc : PairGeometry d vt f h c) {u u' : AmbientSpace} (hu : u ∈ tsupport f) (hu' : u' ∈ tsupport h)
    (z : Fin 4 → ℤ) :
    d ≤ TorusMetric.euclidNormVec fun a => u a - u' a + 2 * (z a : ℝ) := by
  by_cases hz : z = 0
  · subst hz
    have e : (fun a => u a - u' a + 2 * (((0 : Fin 4 → ℤ) a : ℤ) : ℝ)) = u - u' := by
      funext a
      simp
    rw [e]
    exact (hc.separated u hu u' hu').1
  · obtain ⟨a, ha⟩ : ∃ a, z a ≠ 0 := by
      by_contra hn
      push Not at hn
      exact hz (funext hn)
    have h1 := abs_le_euclidNormVec (fun a => u a - u' a + 2 * (z a : ℝ)) a
    have h2 := abs_le_euclidNormVec (u - u') a
    have h3 := (hc.separated u hu u' hu').2
    have h4 : (1 : ℝ) ≤ |(z a : ℝ)| := by
      have : (1 : ℤ) ≤ |z a| := Int.one_le_abs ha
      exact_mod_cast this
    simp only [Pi.sub_apply] at h2
    have h5 : 2 * |(z a : ℝ)| - |u a - u' a| ≤ |u a - u' a + 2 * (z a : ℝ)| := by
      have := abs_sub_abs_le_abs_sub (2 * (z a : ℝ)) (-(u a - u' a))
      rw [abs_neg, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)] at this
      have e : 2 * (z a : ℝ) - -(u a - u' a) = u a - u' a + 2 * (z a : ℝ) := by ring
      rw [e] at this
      exact this
    linarith
private theorem separatedBumpFamily_translate {d vt : ℝ} {f h : AmbientSpace → ℝ} {c : AmbientSpace} (hd : 0 < d)
    (hd' : d ≤ 1 / 8) (h0 : 0 < vt) (hp : IsNormalizedTestPair d vt f h) (hc : PairGeometry d vt f h c)
    (τ : AmbientSpace) :
    IsSeparatedBumpFamily d vt ![fun x => f (x - τ), fun x => h (x - τ)] := by
  obtain ⟨x₁, x₂, ⟨a₁, a₂, a₃, a₄, a₅, a₆⟩, ⟨b₁, b₂, b₃, b₄, b₅, b₆⟩, c₁, c₂⟩ := hp.mem_class
  have slope : ∀ g : AmbientSpace → ℝ, TestFunctions.IsLipschitzFor TestFunctions.euclidDistR4 g →
      TestFunctions.uniformNorm g = 1 →
      TestFunctions.bestLipschitzConstant TestFunctions.euclidDistR4 g ≤ TestFunctions.uniformNorm g / (vt * d) →
      ∀ x x', |g (x - τ) - g (x' - τ)| ≤ TorusMetric.euclidNormVec (x - x') / (vt * d) := by
    intro g hl hs hc' x x'
    have e1 := norm_sub_le_lipschitz hl (x - τ) (x' - τ)
    have e2 : TestFunctions.euclidDistR4 (x - τ) (x' - τ) = TorusMetric.euclidNormVec (x - x') := by
      show TorusMetric.euclidNormVec (x - τ - (x' - τ)) = _
      rw [sub_sub_sub_cancel_right]
    rw [e2, Real.norm_eq_abs] at e1
    have e3 : 0 ≤ TorusMetric.euclidNormVec (x - x') := Real.sqrt_nonneg _
    rw [hs] at hc'
    calc |g (x - τ) - g (x' - τ)| ≤ _ := e1
      _ ≤ 1 / (vt * d) * TorusMetric.euclidNormVec (x - x') := mul_le_mul_of_nonneg_right hc' e3
      _ = _ := by ring
  have ball : ∀ (g : AmbientSpace → ℝ) (b : AmbientSpace), tsupport g ⊆ TestFunctions.closedBallR4 b d →
      tsupport (fun x => g (x - τ)) ⊆ TestFunctions.closedBallR4 (b + τ) d := by
    intro g b hs x hx
    have e1 := hs (mem_tsupport_of_translate hx)
    have e2 : x - τ - b = x - (b + τ) := by abel
    show TorusMetric.euclidNormVec (x - (b + τ)) ≤ d
    rw [← e2]
    exact e1
  have lead : ∀ x x' : AmbientSpace, x ∈ (tsupport fun y => f (y - τ)) → x' ∈ (tsupport fun y => h (y - τ)) →
      ∀ z : Fin 4 → ℤ, d ≤ TorusMetric.euclidNormVec fun a => x a - x' a + 2 * (z a : ℝ) := by
    intro x x' hx hx' z
    have e := le_euclidNormVec_periodic hd' hc (mem_tsupport_of_translate hx) (mem_tsupport_of_translate hx') z
    have e2 : (fun a => (x - τ) a - (x' - τ) a + 2 * (z a : ℝ)) = fun a => x a - x' a + 2 * (z a : ℝ) := by
      funext a
      simp
    rwa [e2] at e
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact Fin.forall_fin_two.mpr ⟨fun x => a₂ _, fun x => b₂ _⟩
  · refine Fin.forall_fin_two.mpr ⟨fun x => ?_, fun x => ?_⟩
    · exact (le_abs_self _).trans (norm_le_of_uniformNorm_eq_one hp.norm_left _)
    · exact (le_abs_self _).trans (norm_le_of_uniformNorm_eq_one hp.norm_right _)
  · exact Fin.forall_fin_two.mpr ⟨slope f a₁ hp.norm_left a₆, slope h b₁ hp.norm_right b₆⟩
  · exact Fin.forall_fin_two.mpr ⟨⟨_, ball f x₁ a₄⟩, ⟨_, ball h x₂ b₄⟩⟩
  · refine Fin.forall_fin_two.mpr ⟨Fin.forall_fin_two.mpr ⟨fun hne => absurd rfl hne, fun _ x hx x' hx' z => ?_⟩,
      Fin.forall_fin_two.mpr ⟨fun _ x hx x' hx' z => ?_, fun hne => absurd rfl hne⟩⟩
    · exact lead x x' hx hx' z
    · have e := lead x' x hx' hx (-z)
      have e2 : (fun a => x' a - x a + 2 * (((-z) a : ℤ) : ℝ)) = -fun a => x a - x' a + 2 * (z a : ℝ) := by
        funext a
        simp
        ring
      rwa [e2, euclidNormVec_neg] at e
private theorem isWeightKernel_mono {L k : ℕ} [NeZero L] {N : ℕ} [NeZero N] {al C C' c err err' : ℝ}
    {h : WeightedResponses.PlaquetteWeight (WeightedResponses.fineSide L k N)}
    {κ : TorusFields.TorusSite N → TorusFields.TorusPlaquette N → TorusFields.TorusPlaquette N → ℝ}
    (hC : C ≤ C') (he : err ≤ err')
    (H : BoxMarks.IsWeightKernel L k al C c err h κ) : BoxMarks.IsWeightKernel L k al C' c err' h κ :=
  ⟨H.symm, fun y p p' => (H.decay y p p').trans (mul_le_mul_of_nonneg_right hC (Real.exp_pos _).le), H.vanish_far,
    fun y μ ν ρ τ h1 h2 => (H.plane_sums y μ ν ρ τ h1 h2).trans he⟩
private theorem isBoxKernelFamily_mono {ℓ : TorusLumps.StepParameters} {T : WeightedResponses.StageTower ℓ} {β : ℝ}
    {al : ℕ → ℝ} {K k m : ℕ}
    {o : TorusFields.TorusSite (BoxResponses.boxSide ℓ.side K k)} {R : ℕ} {c : BoxGaussian.BoxChart T k o R}
    {C C' cc errK errK' err err' : ℝ}
    {w : (Fin 4 → ℤ) → AmbientSpace → ℝ}
    {κ : (Fin 4 → ℤ) → TorusFields.TorusSite (BoxResponses.boxSide ℓ.side K k) →
      TorusFields.TorusPlaquette (BoxResponses.boxSide ℓ.side K k) →
      TorusFields.TorusPlaquette (BoxResponses.boxSide ℓ.side K k) → ℝ}
    {κ₀ : (Fin 4 → ℤ) → ℝ} (hC : C ≤ C') (hK : errK ≤ errK') (he : err ≤ err')
    (H : BoxMarks.IsBoxKernelFamily T β al K k m c C cc errK err w κ κ₀) :
    BoxMarks.IsBoxKernelFamily T β al K k m c C' cc errK' err' w κ κ₀ :=
  ⟨fun v hv => isWeightKernel_mono hC hK (H.isWeightKernel v hv),
    H.response_approx.mono fun _ hu h1 v hv => (hu h1 v hv).trans he⟩
private theorem isInGauge_mono {ℓ : TorusLumps.StepParameters} {T : WeightedResponses.StageTower ℓ} {k n : ℕ}
    [NeZero n] {o : TorusFields.TorusSite n} {R : ℕ}
    {c : BoxGaussian.BoxChart T k o R} {C C' δ c₀ : ℝ} (hδ : 0 ≤ δ) (hC : C ≤ C') (H : c.IsInGauge C δ c₀) :
    c.IsInGauge C' δ c₀ := by
  refine ⟨H.mem_chart, H.coord_unique, fun p hp => ?_⟩
  obtain ⟨γ, v, β', hγ, h1, h2, h3, h4⟩ := H.bounds p hp
  have hR : (0 : ℝ) ≤ (R : ℝ) := Nat.cast_nonneg _
  refine ⟨γ, v, β', hγ, fun b hb => ?_, h2.trans ?_, fun q hq => (h3 q hq).trans ?_, h4.trans ?_⟩
  · obtain ⟨e1, e2, e3, e4, e5, e6⟩ := h1 b hb
    have hm : C * (R : ℝ) ^ 3 * δ ≤ C' * (R : ℝ) ^ 3 * δ :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hC (by positivity)) hδ
    exact ⟨e1, e2, e3, e4.trans hm, e5.trans hm, e6.trans hm⟩
  · exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hC (by positivity)) (by positivity)
  · exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hC (by positivity)) hδ
  · exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hC (by positivity)) (by positivity)
private theorem hasLaw_mono {ℓ : TorusLumps.StepParameters} {T : WeightedResponses.StageTower ℓ} {k n : ℕ}
    [NeZero n] {o : TorusFields.TorusSite n} {R : ℕ}
    {c : BoxGaussian.BoxChart T k o R} {P : Measure (WeightedResponses.MarkedSample ℓ k n)} {x c₀ ε ε' : ℝ}
    (he : ε ≤ ε') (H : c.HasLaw P x c₀ ε) : c.HasLaw P x c₀ ε' :=
  ⟨H.integral_eq, fun q hq ζ hζ => ⟨(H.weight_bounds q hq ζ hζ).1, (H.weight_bounds q hq ζ hζ).2.trans he⟩,
    H.ellipsoid_mass⟩
private theorem hasCurl_mono {ℓ : TorusLumps.StepParameters} {T : WeightedResponses.StageTower ℓ} {k n : ℕ}
    [NeZero n] {o : TorusFields.TorusSite n} {R : ℕ}
    {c : BoxGaussian.BoxChart T k o R} {x C C' δ φ φ' : ℝ} {Cj : ℕ → ℝ} (hδ : 0 ≤ δ) (hC : C ≤ C') (hφ : φ ≤ φ')
    (H : c.HasCurl x C δ φ Cj) : c.HasCurl x C' δ φ' Cj := by
  exact ⟨H.map_eq_gaussian, fun q hq p hp => (H.meanCurl_le q hq p hp).trans
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hC (by positivity)) hδ), H.iteratedDiff_le,
    fun q hq p hp => (H.meanCurl_le_inner q hq p hp).trans hφ⟩
private theorem abs_sub_le_of_eLpNorm_mean {Ω ι : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {Q : Finset ι}
    (hQ : Q.Nonempty) {F : ι → Ω → ℝ} (hF : ∀ v ∈ Q, Integrable (F v) P) {kap κ E b : ℝ} (hb : 0 ≤ b)
    (hE : ∀ v ∈ Q, |kap - ∫ u, F v u ∂P| ≤ E)
    (hL : eLpNorm (fun u => ((Q.card : ℝ)⁻¹ * ∑ v ∈ Q, F v u) - κ) 16 P ≤ ENNReal.ofReal b) :
    |kap - κ| ≤ E + b := by
  have hc : (0 : ℝ) < Q.card := by exact_mod_cast hQ.card_pos
  have hGi : Integrable (fun u => (Q.card : ℝ)⁻¹ * ∑ v ∈ Q, F v u) P :=
    (integrable_finsetSum Q hF).const_mul _
  have h1 : ∫ u, (Q.card : ℝ)⁻¹ * ∑ v ∈ Q, F v u ∂P = (Q.card : ℝ)⁻¹ * ∑ v ∈ Q, ∫ u, F v u ∂P := by
    rw [integral_const_mul, integral_finsetSum _ hF]
  have h2 : |kap - ∫ u, (Q.card : ℝ)⁻¹ * ∑ v ∈ Q, F v u ∂P| ≤ E := by
    rw [h1]
    have e : kap - (Q.card : ℝ)⁻¹ * ∑ v ∈ Q, ∫ u, F v u ∂P =
        (Q.card : ℝ)⁻¹ * ∑ v ∈ Q, (kap - ∫ u, F v u ∂P) := by
      rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
      field_simp
    rw [e, abs_mul, abs_of_pos (inv_pos.mpr hc)]
    have h3 : |∑ v ∈ Q, (kap - ∫ u, F v u ∂P)| ≤ Q.card * E := by
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      have := Finset.sum_le_card_nsmul Q _ E hE
      simpa [nsmul_eq_mul] using this
    calc (Q.card : ℝ)⁻¹ * |∑ v ∈ Q, (kap - ∫ u, F v u ∂P)| ≤ (Q.card : ℝ)⁻¹ * (Q.card * E) :=
          mul_le_mul_of_nonneg_left h3 (inv_pos.mpr hc).le
      _ = E := by field_simp
  have hSub : Integrable (fun u => ((Q.card : ℝ)⁻¹ * ∑ v ∈ Q, F v u) - κ) P := hGi.sub (integrable_const κ)
  have h3 : |∫ u, (((Q.card : ℝ)⁻¹ * ∑ v ∈ Q, F v u) - κ) ∂P| ≤ b := by
    have e1 := enorm_integral_le_lintegral_enorm (μ := P) (fun u => ((Q.card : ℝ)⁻¹ * ∑ v ∈ Q, F v u) - κ)
    rw [← eLpNorm_one_eq_lintegral_enorm] at e1
    have e2 := eLpNorm_le_eLpNorm_of_exponent_le (p := 1) (q := 16) (by norm_num) hSub.aestronglyMeasurable
    have e3 := (e1.trans e2).trans hL
    rw [Real.enorm_eq_ofReal_abs] at e3
    exact (ENNReal.ofReal_le_ofReal_iff hb).mp e3
  have h4 : ∫ u, (((Q.card : ℝ)⁻¹ * ∑ v ∈ Q, F v u) - κ) ∂P =
      (∫ u, (Q.card : ℝ)⁻¹ * ∑ v ∈ Q, F v u ∂P) - κ := by
    rw [integral_sub hGi (integrable_const κ)]
    simp
  rw [h4] at h3
  have h5 := abs_add_le (kap - ∫ u, (Q.card : ℝ)⁻¹ * ∑ v ∈ Q, F v u ∂P)
    ((∫ u, (Q.card : ℝ)⁻¹ * ∑ v ∈ Q, F v u ∂P) - κ)
  have h6 : kap - ∫ u, (Q.card : ℝ)⁻¹ * ∑ v ∈ Q, F v u ∂P + ((∫ u, (Q.card : ℝ)⁻¹ * ∑ v ∈ Q, F v u ∂P) - κ) =
      kap - κ := by
    ring
  rw [h6] at h5
  linarith
private theorem exists_relative_error {kap A B q s ε Ca c₀ : ℝ} (hq : 0 < q) (hc₀ : 0 < c₀) (hs : 0 ≤ s)
    (hCa : 0 ≤ Ca) (hB : c₀ * q ≤ B) (hA : 9 / 16 ≤ A) (ha : |kap - A * B * (1 + ε)| ≤ Ca * (q * s)) :
    ∃ ε' : ℝ, |ε'| ≤ |ε| + 4 * Ca / c₀ * s ∧ kap = A * B * (1 + ε') := by
  have hB0 : 0 < B := lt_of_lt_of_le (by positivity) hB
  have hAB : 0 < A * B := by nlinarith
  have hAB4 : c₀ * q / 4 ≤ A * B := by nlinarith
  refine ⟨ε + (kap - A * B * (1 + ε)) / (A * B), ?_, ?_⟩
  · refine (abs_add_le _ _).trans (add_le_add le_rfl ?_)
    rw [abs_div, abs_of_pos hAB, div_le_iff₀ hAB]
    calc |kap - A * B * (1 + ε)| ≤ Ca * (q * s) := ha
      _ = 4 * Ca / c₀ * s * (c₀ * q / 4) := by field_simp
      _ ≤ 4 * Ca / c₀ * s * (A * B) := mul_le_mul_of_nonneg_left hAB4 (by positivity)
  · field_simp
    ring
private theorem supBall_mono {n : ℕ} [NeZero n] (o : TorusFields.TorusSite n) {r r' : ℝ} (h : r ≤ r') :
    ResponseInTheExpansion.supBall o r ⊆ ResponseInTheExpansion.supBall o r' :=
  fun _ hz => Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hz).2.trans h⟩
private theorem integrable_centered_product {ℓ : TorusLumps.StepParameters}
    (hResp : WeightedResponses.ResponsesBounded) (hf : ℓ.Admissible)
    (hJ : 11 * 2 ^ 12 * ℓ.baseDepth < ℓ.side) {T : WeightedResponses.StageTower ℓ}
    (hc : ColdStepAtMirrorFrames.IsCutoff (ℓ.threshold / 64) T.base.barrierFn) (hb : T.MarksMeasurable)
    (β : ℝ) (al : ℕ → ℝ) (K k : ℕ) [IsProbabilityMeasure (BoxResponses.stageLaw T β K k)] (f h : AmbientSpace → ℝ) :
    Integrable (fun u => BoxResponses.centeredBoxResponse T β al K k f u *
      BoxResponses.centeredBoxResponse T β al K k h u) (BoxResponses.stageLaw T β K k) := by
  obtain ⟨m₁, C₁, b₁⟩ := hResp ℓ hf hJ T hc hb β al k (BoxResponses.boxSide ℓ.side K k)
    (BoxResponses.unitTorusWeight ℓ.side K k f)
  obtain ⟨m₂, C₂, b₂⟩ := hResp ℓ hf hJ T hc hb β al k (BoxResponses.boxSide ℓ.side K k)
    (BoxResponses.unitTorusWeight ℓ.side K k h)
  set a₁ : ℝ := ∫ u', BoxResponses.boxResponse T β al K k f u' ∂BoxResponses.stageLaw T β K k
  set a₂ : ℝ := ∫ u', BoxResponses.boxResponse T β al K k h u' ∂BoxResponses.stageLaw T β K k
  have hm : Measurable fun u => BoxResponses.centeredBoxResponse T β al K k f u *
      BoxResponses.centeredBoxResponse T β al K k h u :=
    (m₁.sub_const a₁).mul (m₂.sub_const a₂)
  refine Integrable.of_bound hm.aestronglyMeasurable ((|C₁| + |a₁|) * (|C₂| + |a₂|)) ?_
  filter_upwards [b₁, b₂] with u u₁ u₂
  have e₁ : |BoxResponses.centeredBoxResponse T β al K k f u| ≤ |C₁| + |a₁| :=
    (abs_sub _ _).trans (add_le_add (u₁.trans (le_abs_self _)) le_rfl)
  have e₂ : |BoxResponses.centeredBoxResponse T β al K k h u| ≤ |C₂| + |a₂| :=
    (abs_sub _ _).trans (add_le_add (u₂.trans (le_abs_self _)) le_rfl)
  rw [Real.norm_eq_abs, abs_mul]
  exact mul_le_mul e₁ e₂ (abs_nonneg _) (by positivity)
set_option maxHeartbeats 4000000 in
private theorem covariance_near_boxCoefficient (hLev : separationLevelStatement)
    (hGrow : couplingAtSeparation_tendsto_statement) (hLaw : BoxGaussian.boxGaussianLawStatement)
    (hMk : boxResponsesQuadraticStatement)
    (hPr : boxProductsStatement) (hBox : BoxMarks.boxCoefficientStatement) (hPM : centeredProductsAtLevelStatement)
    (hMove : covarianceTranslationInvariantStatement) (hResp : WeightedResponses.ResponsesBounded)
    (hTP : ResponseInTheExpansion.TwoPointByTotalCovarianceStatement) (hSite : siteNearPairStatement)
    (hG : TestPairs.GeometryAndKernelBounds) :
    HoldsForShapes fun Tb y Kr Xi vt => ∃ C d₀ : ℝ, 0 ≤ C ∧ 0 < d₀ ∧ ∀ d : ℝ, 0 < d → d ≤ d₀ →
      ∀ (K : ℕ) (β : ℝ) (al : ℕ → ℝ)
      (T : WeightedResponses.StageTower (Tb.stepParameters y)), BoxResponses.IsStateChain Tb y Kr Xi d K β al T →
      ∀ f h : AmbientSpace → ℝ, IsNormalizedTestPair d vt f h →
        ∃ ε : ℝ, |ε| ≤ C * lengthInSites (Tb.stepParameters y).side K
              (separationLevel (Tb.stepParameters y) β K d) d ^ (-(1 / 2) : ℝ) +
              C * couplingAtSeparation (Tb.stepParameters y) β K d ^ (-(1 / 130) : ℝ) ∧
          |unitTorusCovariance (Tb.stepParameters y).side K β f h -
            al (separationLevel (Tb.stepParameters y) β K d) ^ 2 * (9 / Real.pi ^ 4) *
              (couplingAtSeparation (Tb.stepParameters y) β K d ^ 2)⁻¹ *
                TestFunctions.inverseEighthKernel f h * (1 + ε)| ≤
            C * couplingAtSeparation (Tb.stepParameters y) β K d ^ (-(2 + 1 / 130) : ℝ) := by
  refine HoldsForShapes.mono (HoldsForShapes.params.and ((HoldsForShapes.of_holdsOnParameters hLev).and
    ((HoldsForShapes.of_holdsOnParameters hGrow).and
    ((HoldsForShapes.of_holdsOnParameters (holdsOnParameters_of_holdsAtAdmissible hLaw)).and
      (hMk.and (hPr.and (hBox.and hPM))))))) ?_
  rintro Tb y Kr Xi vt ⟨⟨hDr, hy0, hRs, hKr, hXi, h0, h1⟩, hLv, hGr, hLw, hMk', hPr', hBx, hPM'⟩
  have hfit : (Tb.stepParameters y).Admissible := hDr.fits y hy0
  have hJ : 11 * 2 ^ 12 * (Tb.stepParameters y).baseDepth < (Tb.stepParameters y).side := hfit.depth_lt
  have hR := hRs.returns_at
  have hW := hRs.wilson_expansion
  obtain ⟨CL, C0, xs, Cj, xp, hL⟩ := hLw (1 / 27) le_rfl (by norm_num)
  obtain ⟨C₁, hC₁⟩ : ∃ C₁ : ℝ, C₁ = max (max CL (2 * Tb.coercivity)⁻¹) 1 := ⟨_, rfl⟩
  have hC₁a : CL ≤ C₁ := hC₁ ▸ (le_max_left _ _).trans (le_max_left _ _)
  have hC₁b : (2 * Tb.coercivity)⁻¹ ≤ C₁ := hC₁ ▸ (le_max_right _ _).trans (le_max_left _ _)
  have hC₁c : 1 ≤ C₁ := hC₁ ▸ le_max_right _ _
  obtain ⟨CM, cc, dM, hcc, hdM, hM⟩ := hMk' C₁ Cj xp
  obtain ⟨C₂, hC₂⟩ : ∃ C₂ : ℝ, C₂ = max C₁ CM := ⟨_, rfl⟩
  have hC₂a : C₁ ≤ C₂ := hC₂ ▸ le_max_left _ _
  have hC₂b : CM ≤ C₂ := hC₂ ▸ le_max_right _ _
  obtain ⟨CP, dP, hdP, hP⟩ := hPr' C₂ cc Cj xp hcc
  obtain ⟨CB, dB, hdB, hB⟩ := hBx C₂ cc hcc
  obtain ⟨CE, dE, hdE, hE⟩ := hPM'
  obtain ⟨X, hX⟩ := eventually_atTop.mp ((eventually_room ((Tb.stepParameters y).side : ℝ)
    (Tb.stepParameters y).B Xi hfit.B_pos).and
    (eventually_error_le CE (Tb.stepParameters y).rt hfit.rt_pos))
  obtain ⟨d₁, hd₁, hG₁⟩ := hGr Xi hXi (max X xs)
  refine ⟨|CB| + |CP| + 1, min (min dM dP) (min (min dB dE) (min d₁ (1 / 8))), by positivity,
    lt_min (lt_min hdM hdP) (lt_min (lt_min hdB hdE) (lt_min hd₁ (by norm_num))), ?_⟩
  intro d hd hdd K β al T hchain f h hp
  have hdat := hchain.isFlowDatum
  have hcut := hchain.minimalCutoff_le
  have hdM' : d ≤ dM := hdd.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hdP' : d ≤ dP := hdd.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hdB' : d ≤ dB := hdd.trans ((min_le_right _ _).trans ((min_le_left _ _).trans (min_le_left _ _)))
  have hdE' : d ≤ dE := hdd.trans ((min_le_right _ _).trans ((min_le_left _ _).trans (min_le_right _ _)))
  have hd₁' : d ≤ d₁ := hdd.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hd8 : d ≤ 1 / 8 := hdd.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  obtain ⟨hfar, hkK, hnle⟩ := hLv Xi hXi d hd (by linarith) K β hdat hcut
  have hxX := hG₁ d hd hd₁' K β hdat hcut
  obtain ⟨k, hk⟩ : ∃ k, k = separationLevel (Tb.stepParameters y) β K d := ⟨_, rfl⟩
  obtain ⟨x, hx⟩ : ∃ x, x = couplingAtSeparation (Tb.stepParameters y) β K d := ⟨_, rfl⟩
  obtain ⟨R, hRd⟩ : ∃ R, R = boxRadius x := ⟨_, rfl⟩
  obtain ⟨m, hm⟩ : ∃ m, m = averagingRadius x := ⟨_, rfl⟩
  rw [← hx] at hxX hnle
  rw [← hk] at hfar hkK hnle ⊢
  rw [← hx]
  obtain ⟨⟨hx1, hx3, hroom, hside1, hside2⟩, herr⟩ := hX x ((le_max_left _ _).trans hxX)
  have hxs : xs ≤ x := (le_max_right _ _).trans hxX
  have hx0 : 0 < x := by linarith
  have hxk : x = (TorusLumps.couplingFlow (Tb.stepParameters y) β k).1 := by rw [hx, hk]; rfl
  have hK2 := hdat.two_le
  have hst := hchain.onFamily
  have hcutT := hchain.isCutoff_bottom
  have hcoin := hchain.marksMeasurable
  have hal : 3 / 4 ≤ al k := by
    obtain ⟨S, -, hSr, hSn⟩ := hchain.scored
    have e := abs_le.mp (hSr.coeff_near_one k (by omega))
    rw [← hSn]
    show 3 / 4 ≤ (S.setup k).coeff
    linarith only [e.1]
  have hbelow : x ≤ Xi + 2 * (Tb.stepParameters y).B * ((K - k : ℕ) : ℝ) := by
    have e := flow_coupling_le_of_steps hR hW (fun j hj => hdat.le_coupling j hj) (K - k) (Nat.sub_le _ _)
    rw [Nat.sub_sub_self hkK.le, ← hxk] at e
    have e2 : (TorusLumps.couplingFlow (Tb.stepParameters y) β K).1 ≤ Xi := hdat.coupling_le_top
    linarith
  have hBpos := hfit.B_pos
  have hL2 : 2 ≤ (Tb.stepParameters y).side := by
    have := hfit.L_ge
    omega
  have hLr1 : (1 : ℝ) ≤ ((Tb.stepParameters y).side : ℝ) := by
    exact_mod_cast (by omega : 1 ≤ (Tb.stepParameters y).side)
  have hgap1 : x ^ ((1 : ℝ) / 27) + 1 ≤ ((K - k : ℕ) : ℝ) := by
    have e : 2 * (Tb.stepParameters y).B * (x ^ ((1 : ℝ) / 27) + 1) ≤
        2 * (Tb.stepParameters y).B * ((K - k : ℕ) : ℝ) := by linarith
    exact le_of_mul_le_mul_left e (by positivity)
  have hgap2 : x ^ ((1 : ℝ) / 10) ≤ ((K - k : ℕ) : ℝ) := by
    have e : 2 * (Tb.stepParameters y).B * x ^ ((1 : ℝ) / 10) ≤
        2 * (Tb.stepParameters y).B * ((K - k : ℕ) : ℝ) := by linarith
    exact le_of_mul_le_mul_left e (by positivity)
  have hRle : (R : ℝ) ≤ x ^ ((1 : ℝ) / 27) + 1 := by
    rw [hRd]
    exact (Nat.ceil_lt_add_one (Real.rpow_nonneg hx0.le _)).le
  have hRge : x ^ ((1 : ℝ) / 27) ≤ (R : ℝ) := by
    rw [hRd]
    exact Nat.le_ceil _
  have hR1 : (1 : ℝ) ≤ (R : ℝ) := (Real.one_le_rpow hx1 (by norm_num)).trans hRge
  have hsteps : BoxGaussian.coarseningSteps (Tb.stepParameters y).side R ≤ K - k - 1 := by
    refine Nat.sInf_le ?_
    have e1 : (R : ℝ) ^ ((2 : ℝ) / 3) ≤ (R : ℝ) := by
      have := Real.rpow_le_rpow_of_exponent_le hR1 (by norm_num : (2 : ℝ) / 3 ≤ 1)
      rwa [Real.rpow_one] at this
    have e2 : K - k - 1 < (Tb.stepParameters y).side ^ (K - k - 1) := Nat.lt_pow_self (by omega)
    have e3 : ((K - k : ℕ) : ℝ) ≤ ((Tb.stepParameters y).side : ℝ) ^ (K - k - 1) := by
      have : K - k ≤ (Tb.stepParameters y).side ^ (K - k - 1) := by omega
      exact_mod_cast this
    show (R : ℝ) ^ ((2 : ℝ) / 3) ≤ ((Tb.stepParameters y).side : ℝ) ^ (K - k - 1)
    linarith
  have hwide : x ^ ((1 : ℝ) / 10) ≤ ((BoxResponses.boxSide (Tb.stepParameters y).side K k : ℕ) : ℝ) := by
    have e2 : K - k < (Tb.stepParameters y).side ^ (K - k) := Nat.lt_pow_self (by omega)
    have e3 : ((K - k : ℕ) : ℝ) ≤ ((BoxResponses.boxSide (Tb.stepParameters y).side K k : ℕ) : ℝ) := by
      have : K - k ≤ BoxResponses.boxSide (Tb.stepParameters y).side K k := by
        unfold BoxResponses.boxSide
        omega
      exact_mod_cast this
    linarith
  have hdb : BoxEvents.IsBoxDatum Tb y T β (1 / 27) xs k (BoxResponses.boxSide (Tb.stepParameters y).side K k) := by
    refine ⟨?_, ?_, hcoin, ⟨K - k, rfl⟩, ?_⟩
    · rw [show BoxEvents.flowCoupling (Tb.stepParameters y) β k = x from hxk.symm]
      exact hxs
    · rw [show BoxEvents.flowCoupling (Tb.stepParameters y) β k = x from hxk.symm,
        show BoxGaussian.boxRadius (1 / 27) x = R from hRd.symm]
      refine ⟨hst.startsAtWilson, fun j hj => hst.coupling_eq j (by omega), fun j hj => hst.onFamily j (by omega)⟩
    · rw [show BoxEvents.flowCoupling (Tb.stepParameters y) β k = x from hxk.symm]
      exact hwide
  obtain ⟨cpt, hPF⟩ := exists_pairGeometry hG hd h0 h1 hp
  obtain ⟨o, ho⟩ := hSite (Tb.stepParameters y).side K k m cpt (5 * d) hfit.L_odd hkK.le (by positivity)
  have hrad : ((Tb.stepParameters y).side : ℝ) ^ (K - k) * (5 * d) + m + 4 ≤ 3 * (R : ℝ) / 32 := by
    have e1 : (m : ℝ) ≤ (R : ℝ) / 16 := by
      rw [hm]
      show ((boxRadius x / 16 : ℕ) : ℝ) ≤ _
      rw [← hRd]
      exact Nat.cast_div_le
    have e2 : ((TorusLumps.clusterRange x : ℕ) : ℝ) ≤ x ^ ((1 : ℝ) / 100) + 1 :=
      (Nat.ceil_lt_add_one (Real.rpow_nonneg hx0.le _)).le
    have e3 : lengthInSites (Tb.stepParameters y).side K k d ≤
        2 ^ 13 * ((Tb.stepParameters y).side : ℝ) * (x ^ ((1 : ℝ) / 100) + 1) :=
      hnle.trans (mul_le_mul_of_nonneg_left e2 (by positivity))
    have e4 : ((Tb.stepParameters y).side : ℝ) ^ (K - k) * (5 * d) =
        5 * lengthInSites (Tb.stepParameters y).side K k d := by
      unfold lengthInSites
      ring
    rw [e4]
    linarith
  have hnR : lengthInSites (Tb.stepParameters y).side K k d ≤ (R : ℝ) / 32 := by
    have e2 : ((TorusLumps.clusterRange x : ℕ) : ℝ) ≤ x ^ ((1 : ℝ) / 100) + 1 :=
      (Nat.ceil_lt_add_one (Real.rpow_nonneg hx0.le _)).le
    have e3 : lengthInSites (Tb.stepParameters y).side K k d ≤
        2 ^ 13 * ((Tb.stepParameters y).side : ℝ) * (x ^ ((1 : ℝ) / 100) + 1) :=
      hnle.trans (mul_le_mul_of_nonneg_left e2 (by positivity))
    have e4 : 0 ≤ lengthInSites (Tb.stepParameters y).side K k d := by
      unfold lengthInSites
      positivity
    linarith
  have hrad' : ((Tb.stepParameters y).side : ℝ) ^ (K - k) * (5 * d) + m + 4 ≤
      (R : ℝ) / 8 - lengthInSites (Tb.stepParameters y).side K k d := by
    linarith
  have hif : BoxMarks.IsDeepInBox (Tb.stepParameters y).side K k m R
      (lengthInSites (Tb.stepParameters y).side K k d) o f := fun v hv =>
    (ho f hPF.left_cube v hv).trans (supBall_mono o hrad')
  have hih : BoxMarks.IsDeepInBox (Tb.stepParameters y).side K k m R
      (lengthInSites (Tb.stepParameters y).side K k d) o h := fun v hv =>
    (ho h hPF.right_cube v hv).trans (supBall_mono o hrad')
  have hwf : IsWellLocalizedNear (Tb.stepParameters y).side K k m R o f := fun v hv =>
    (ho f hPF.left_cube v hv).trans (supBall_mono o hrad)
  have hwh : IsWellLocalizedNear (Tb.stepParameters y).side K k m R o h := fun v hv =>
    (ho h hPF.right_cube v hv).trans (supBall_mono o hrad)
  have h38 : 3 * (R : ℝ) / 32 ≤ (R : ℝ) / 8 := by linarith
  have hnf : BoxMarks.IsLocalizedNear (Tb.stepParameters y).side K k m R o f := fun v hv =>
    (hwf v hv).trans (supBall_mono o h38)
  have hnh : BoxMarks.IsLocalizedNear (Tb.stepParameters y).side K k m R o h := fun v hv =>
    (hwh v hv).trans (supBall_mono o h38)
  have hsix : 16 * R < BoxResponses.boxSide (Tb.stepParameters y).side K k := by
    have e1 : R ≤ K - k := by exact_mod_cast hRle.trans hgap1
    have e2 : K - k - 1 < (Tb.stepParameters y).side ^ (K - k - 1) := Nat.lt_pow_self (by omega)
    have e3 : (Tb.stepParameters y).side ^ (K - k) =
        (Tb.stepParameters y).side ^ (K - k - 1) * (Tb.stepParameters y).side := by
      rw [← pow_succ]
      congr 1
      omega
    have e4 : 2 ^ 16 ≤ (Tb.stepParameters y).side := hfit.L_ge
    have e5 : (K - k) * 2 ^ 16 ≤ (Tb.stepParameters y).side ^ (K - k - 1) * (Tb.stepParameters y).side :=
      Nat.mul_le_mul (by omega) e4
    unfold BoxResponses.boxSide
    rw [e3]
    generalize (Tb.stepParameters y).side ^ (K - k - 1) * (Tb.stepParameters y).side = P at e5
    omega
  obtain ⟨c, cb, cl, co, cg, cw, cu, ck⟩ :=
    hL T β k (BoxResponses.boxSide (Tb.stepParameters y).side K k) o x R hdb hxk hRd
  have hδ : 0 ≤ BoxGaussian.boxScale x := by
    unfold BoxGaussian.boxScale
    have := Real.log_nonneg hx1
    positivity
  have hlog1 : 1 ≤ Real.log x := by
    rw [Real.le_log_iff_exp_le hx0]
    have := Real.exp_one_lt_d9
    linarith
  have hch : ∀ C' : ℝ, C₁ ≤ C' → BoxMarks.IsGoodChart T β K k c x C'
      (C0 * (R : ℝ) ^ 4 * BoxGaussian.boxScale x ^ 2)
      (C' * (R : ℝ) ^ 9 * x ^ (-(1 / 2) : ℝ) * Real.log x ^ 3)
      (C' * (R : ℝ) ^ (-(2 / 3) : ℝ) * BoxGaussian.boxScale x * Real.log x) Cj xp := by
    intro C' hC'
    have hCL : CL ≤ C' := hC₁a.trans hC'
    have hC0 : 0 ≤ C' := by linarith
    have hr : (0 : ℝ) ≤ (R : ℝ) ^ (-(2 / 3) : ℝ) := Real.rpow_nonneg (by positivity) _
    have hxh : (0 : ℝ) ≤ x ^ (-(1 / 2) : ℝ) := Real.rpow_nonneg hx0.le _
    refine ⟨cb, cl, ?_, isInGauge_mono hδ hCL cg, hasLaw_mono ?_ cw, hasCurl_mono hδ hCL ?_ cu,
      fun w => ⟨(ck w).1, (ck w).2.trans ?_⟩⟩
    · intro u hu
      exact co _ hu
    · have e : CL * (R : ℝ) ^ 9 ≤ C' * (R : ℝ) ^ 9 := mul_le_mul_of_nonneg_right hCL (by positivity)
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right e hxh) (by positivity)
    · have e : CL * (R : ℝ) ^ (-(2 / 3) : ℝ) * BoxGaussian.boxScale x ≤
          C' * (R : ℝ) ^ (-(2 / 3) : ℝ) * BoxGaussian.boxScale x :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCL hr) hδ
      have e2 : C' * (R : ℝ) ^ (-(2 / 3) : ℝ) * BoxGaussian.boxScale x ≤
          C' * (R : ℝ) ^ (-(2 / 3) : ℝ) * BoxGaussian.boxScale x * Real.log x :=
        le_mul_of_one_le_right (by positivity) hlog1
      exact e.trans e2
    · exact mul_le_mul_of_nonneg_right (hC₁b.trans hC')
        (Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _)
  obtain ⟨κ, κ', κ₀, κ₀', hm₁, hm₂⟩ := hM d hd hdM' K β al T hchain k m R x hk hx hRd hm f h hp o hnf hnh c _ _ _
    (hch C₁ le_rfl)
  have hnpos : 0 ≤ ((vt * lengthInSites (Tb.stepParameters y).side K k d)⁻¹ + Real.exp (-(cc * R))) := by
    have : 0 ≤ lengthInSites (Tb.stepParameters y).side K k d := by
      unfold lengthInSites
      positivity
    positivity
  have hn4 : 0 ≤ lengthInSites (Tb.stepParameters y).side K k d ^ 4 * (R : ℝ) ^ 8 * BoxGaussian.boxScale x ^ 3 := by
    have : 0 ≤ lengthInSites (Tb.stepParameters y).side K k d := by
      unfold lengthInSites
      positivity
    positivity
  have hM₁ := isBoxKernelFamily_mono (C' := C₂)
    (errK' := C₂ * ((vt * lengthInSites (Tb.stepParameters y).side K k d)⁻¹ + Real.exp (-(cc * R))))
    (err' := C₂ * lengthInSites (Tb.stepParameters y).side K k d ^ 4 * (R : ℝ) ^ 8 * BoxGaussian.boxScale x ^ 3 +
      Real.exp (-(cc * R)))
    hC₂b (mul_le_mul_of_nonneg_right hC₂b hnpos)
    (by nlinarith [mul_le_mul_of_nonneg_right hC₂b hn4]) hm₁
  have hM₂ := isBoxKernelFamily_mono (C' := C₂)
    (errK' := C₂ * ((vt * lengthInSites (Tb.stepParameters y).side K k d)⁻¹ + Real.exp (-(cc * R))))
    (err' := C₂ * lengthInSites (Tb.stepParameters y).side K k d ^ 4 * (R : ℝ) ^ 8 * BoxGaussian.boxScale x ^ 3 +
      Real.exp (-(cc * R)))
    hC₂b (mul_le_mul_of_nonneg_right hC₂b hnpos)
    (by nlinarith [mul_le_mul_of_nonneg_right hC₂b hn4]) hm₂
  obtain ⟨p₁, -, -⟩ := hP d hd hdP' K β al T hchain k m R x hk hx hRd hm hsix f h hp o hwf hwh c _ (hch C₂ hC₂a)
    κ κ' κ₀ κ₀' hM₁ hM₂
  obtain ⟨ε, hε, hεe⟩ := hB d hd hdB' K β al T hchain k m R x hk hx hRd hm f h hp hal o hif hih κ κ'
    (fun v hv => hM₁.isWeightKernel v hv) (fun v hv => hM₂.isWeightKernel v hv)
  have hprob : IsProbabilityMeasure (BoxResponses.stageLaw T β K k) :=
    (hTP (Tb.stepParameters y) hfit hJ T hcutT hcoin β al k (BoxResponses.boxSide (Tb.stepParameters y).side K k)).1
  have hβ : 0 < β := by
    have e : y ≤ β := hdat.le_coupling 0 (by omega)
    have e2 : (1 : ℝ) ≤ y := hfit.y₁_ge
    linarith
  have hE₂ : ∀ v ∈ shiftSet m, |unitTorusCovariance (Tb.stepParameters y).side K β f h -
      ∫ u, BoxResponses.centeredBoxResponse T β al K k (translateBy (Tb.stepParameters y).side K k v f) u *
        BoxResponses.centeredBoxResponse T β al K k (translateBy (Tb.stepParameters y).side K k v h) u
          ∂BoxResponses.stageLaw T β K k| ≤ x ^ (-3 : ℝ) := by
    intro v _
    have e := hE d hd hdE' K β al T hchain 2
      ![translateBy (Tb.stepParameters y).side K k v f, translateBy (Tb.stepParameters y).side K k v h]
      (by norm_num) (separatedBumpFamily_translate hd hd8 h0 hp hPF _) Finset.univ
    simp only [Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, ← hx] at e
    rw [← hMove (Tb.stepParameters y).side K k β d vt v f h hfit.L_odd (by have := hfit.L_ge; omega) (by omega)
      hkK.le hβ hd h0 h1 hp]
    subst hk
    exact e.trans herr
  have hQ : (shiftSet m).Nonempty := ⟨0, Fintype.mem_piFinset.mpr fun i => Finset.mem_Icc.mpr (by simp)⟩
  have hb₀ : 0 ≤ CP * x ^ (-(2 + 1 / 130) : ℝ) ∨ CP * x ^ (-(2 + 1 / 130) : ℝ) < 0 := le_or_gt _ _
  have hxp : 0 < x ^ (-(2 + 1 / 130) : ℝ) := Real.rpow_pos_of_pos hx0 _
  have hclose := abs_sub_le_of_eLpNorm_mean (P := BoxResponses.stageLaw T β K k) hQ
    (F := fun v u => BoxResponses.centeredBoxResponse T β al K k (translateBy (Tb.stepParameters y).side K k v f) u *
      BoxResponses.centeredBoxResponse T β al K k (translateBy (Tb.stepParameters y).side K k v h) u)
    (fun v _ => integrable_centered_product hResp hfit hJ hcutT hcoin β al K k _ _)
    (kap := unitTorusCovariance (Tb.stepParameters y).side K β f h)
    (κ := BoxMarks.boxCoefficient (Tb.stepParameters y).coupling (Tb.stepParameters y).side k m o R x κ κ')
    (E := x ^ (-3 : ℝ))
    (b := |CP| * x ^ (-(2 + 1 / 130) : ℝ)) (by positivity) hE₂
    (p₁.trans (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (le_abs_self _) hxp.le)))
  have hx3 : x ^ (-3 : ℝ) ≤ x ^ (-(2 + 1 / 130) : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hx1 (by norm_num)
  have hnn : 0 ≤ lengthInSites (Tb.stepParameters y).side K k d ^ (-(1 / 2) : ℝ) := by
    have : 0 ≤ lengthInSites (Tb.stepParameters y).side K k d := by
      unfold lengthInSites
      positivity
    exact Real.rpow_nonneg this _
  have hxx : 0 ≤ x ^ (-(1 / 130) : ℝ) := Real.rpow_nonneg hx0.le _
  refine ⟨ε, hε.trans ?_, ?_⟩
  · have e1 : CB ≤ |CB| + |CP| + 1 := by linarith [le_abs_self CB, abs_nonneg CP]
    exact add_le_add (mul_le_mul_of_nonneg_right e1 hnn) (mul_le_mul_of_nonneg_right e1 hxx)
  · rw [hεe] at hclose
    refine hclose.trans ?_
    nlinarith [abs_nonneg CB, abs_nonneg CP]
set_option maxHeartbeats 4000000 in
private theorem covariance_form_of_chain (hLev : separationLevelStatement)
    (hGrow : couplingAtSeparation_tendsto_statement) (hLaw : BoxGaussian.boxGaussianLawStatement)
    (hMk : boxResponsesQuadraticStatement)
    (hPr : boxProductsStatement) (hBox : BoxMarks.boxCoefficientStatement) (hPM : centeredProductsAtLevelStatement)
    (hMove : covarianceTranslationInvariantStatement) (hResp : WeightedResponses.ResponsesBounded)
    (hTP : ResponseInTheExpansion.TwoPointByTotalCovarianceStatement) (hSite : siteNearPairStatement)
    (hG : TestPairs.GeometryAndKernelBounds) :
    HoldsForShapes fun Tb y Kr Xi vt => ∃ C d₀ : ℝ, 0 < d₀ ∧ ∀ d : ℝ, 0 < d → d ≤ d₀ →
      ∀ (K : ℕ) (β : ℝ) (al : ℕ → ℝ)
      (T : WeightedResponses.StageTower (Tb.stepParameters y)), BoxResponses.IsStateChain Tb y Kr Xi d K β al T →
      ∀ f h : AmbientSpace → ℝ, IsNormalizedTestPair d vt f h →
        ∃ ε : ℝ, |ε| ≤ C * lengthInSites (Tb.stepParameters y).side K
              (separationLevel (Tb.stepParameters y) β K d) d ^ (-(1 / 2) : ℝ) +
              C * couplingAtSeparation (Tb.stepParameters y) β K d ^ (-(1 / 130) : ℝ) ∧
          unitTorusCovariance (Tb.stepParameters y).side K β f h =
            al (separationLevel (Tb.stepParameters y) β K d) ^ 2 * (9 / Real.pi ^ 4) *
              (couplingAtSeparation (Tb.stepParameters y) β K d ^ 2)⁻¹ *
                TestFunctions.inverseEighthKernel f h * (1 + ε) := by
  have hc := covariance_near_boxCoefficient hLev hGrow hLaw hMk hPr hBox hPM hMove hResp hTP hSite hG
  refine HoldsForShapes.mono (HoldsForShapes.params.and (hc.and ((HoldsForShapes.of_holdsOnParameters hLev).and
    (HoldsForShapes.of_holdsOnParameters hGrow)))) ?_
  rintro Tb y Kr Xi vt ⟨⟨-, -, -, hKr, hXi, h0, h1⟩, hc', hLv, hGr⟩
  obtain ⟨Ca, da, hCa, hda, ha⟩ := hc'
  have hfl : 0 < TestPairs.kernelLowerConst := by
    unfold TestPairs.kernelLowerConst
    positivity
  obtain ⟨c₀, hc₀⟩ : ∃ c₀ : ℝ, c₀ = 9 / Real.pi ^ 4 * (TestPairs.kernelLowerConst * vt ^ 2) := ⟨_, rfl⟩
  have hc₀p : 0 < c₀ := by
    rw [hc₀]
    positivity
  obtain ⟨d₁, hd₁, hG₁⟩ := hGr Xi hXi 1
  refine ⟨Ca + 4 * Ca / c₀, min da (min d₁ (1 / 2)), lt_min hda (lt_min hd₁ (by norm_num)), ?_⟩
  intro d hd hdd K β al T hchain f h hp
  have hdat := hchain.isFlowDatum
  have hcut := hchain.minimalCutoff_le
  have hda' : d ≤ da := hdd.trans (min_le_left _ _)
  have hd₁' : d ≤ d₁ := hdd.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hd2 : d ≤ 1 / 2 := hdd.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hx1' := hG₁ d hd hd₁' K β hdat hcut
  obtain ⟨ε, hε, hεa⟩ := ha d hd hda' K β al T hchain f h hp
  obtain ⟨-, hlk, -⟩ := hLv Xi hXi d hd (by linarith) K β hdat hcut
  have hal : |al (separationLevel (Tb.stepParameters y) β K d) - 1| ≤ 1 / 4 := by
    obtain ⟨S, -, hSr, hSn⟩ := hchain.scored
    rw [← hSn]
    exact hSr.coeff_near_one _ (by omega)
  obtain ⟨k, hk⟩ : ∃ k, k = separationLevel (Tb.stepParameters y) β K d := ⟨_, rfl⟩
  obtain ⟨x, hx⟩ : ∃ x, x = couplingAtSeparation (Tb.stepParameters y) β K d := ⟨_, rfl⟩
  rw [← hx] at hx1' hε hεa
  rw [← hk] at hε hεa hal
  rw [← hx, ← hk]
  have hx0 : 0 < x := by linarith only [hx1']
  obtain ⟨c, hPF⟩ := exists_pairGeometry hG hd h0 h1 hp
  have hn0' : 0 ≤ lengthInSites (Tb.stepParameters y).side K k d ^ (-(1 / 2) : ℝ) := by
    have : 0 ≤ lengthInSites (Tb.stepParameters y).side K k d := by
      unfold lengthInSites
      positivity
    exact Real.rpow_nonneg this _
  have hs0 : 0 ≤ x ^ (-(1 / 130) : ℝ) := Real.rpow_nonneg hx0.le _
  have hxq : x ^ (-(2 + 1 / 130) : ℝ) = (x ^ 2)⁻¹ * x ^ (-(1 / 130) : ℝ) := by
    have e : (-(2 + 1 / 130) : ℝ) = -2 + -(1 / 130) := by ring
    rw [e, Real.rpow_add hx0, Real.rpow_neg hx0.le, Real.rpow_two]
  have hA : 9 / 16 ≤ al k ^ 2 := by
    have e := abs_le.mp hal
    nlinarith only [e.1, e.2]
  have hq : 0 < (x ^ 2)⁻¹ := by positivity
  have hK : TestPairs.kernelLowerConst * vt ^ 2 ≤ TestFunctions.inverseEighthKernel f h := hPF.kernel_ge
  have hBq : c₀ * (x ^ 2)⁻¹ ≤ 9 / Real.pi ^ 4 * (x ^ 2)⁻¹ * TestFunctions.inverseEighthKernel f h := by
    rw [hc₀]
    have e := mul_le_mul_of_nonneg_left hK (by positivity : 0 ≤ 9 / Real.pi ^ 4 * (x ^ 2)⁻¹)
    calc 9 / Real.pi ^ 4 * (TestPairs.kernelLowerConst * vt ^ 2) * (x ^ 2)⁻¹ =
        9 / Real.pi ^ 4 * (x ^ 2)⁻¹ * (TestPairs.kernelLowerConst * vt ^ 2) := by ring
      _ ≤ _ := e
  have hea : |unitTorusCovariance (Tb.stepParameters y).side K β f h -
      al k ^ 2 * (9 / Real.pi ^ 4 * (x ^ 2)⁻¹ * TestFunctions.inverseEighthKernel f h) * (1 + ε)| ≤
      Ca * ((x ^ 2)⁻¹ * x ^ (-(1 / 130) : ℝ)) := by
    rw [← hxq]
    have e : al k ^ 2 * (9 / Real.pi ^ 4 * (x ^ 2)⁻¹ * TestFunctions.inverseEighthKernel f h) * (1 + ε) =
        al k ^ 2 * (9 / Real.pi ^ 4) * (x ^ 2)⁻¹ * TestFunctions.inverseEighthKernel f h * (1 + ε) := by ring
    rw [e]
    exact hεa
  obtain ⟨ε', hε', hkap⟩ := exists_relative_error hq hc₀p hs0 hCa hBq hA hea
  refine ⟨ε', ?_, ?_⟩
  · have e1 : 0 ≤ 4 * Ca / c₀ := by positivity
    refine hε'.trans ?_
    have e2 := mul_nonneg e1 hn0'
    linarith only [hε, e2]
  · rw [hkap]
    ring
set_option maxHeartbeats 4000000 in
theorem holds (hScored : FreeEnergies.scoredTowerExistsStatement)
    (hOn : ResponseInTheExpansion.scoredTowerCoeffsAreChainStatement)
    (hOne : ResponseInTheExpansion.chainResponseCoeffsUnique)
    (hLev : separationLevelStatement)
    (hGrow : couplingAtSeparation_tendsto_statement) (hLaw : BoxGaussian.boxGaussianLawStatement)
    (hMk : boxResponsesQuadraticStatement)
    (hPr : boxProductsStatement) (hBox : BoxMarks.boxCoefficientStatement) (hPM : centeredProductsAtLevelStatement)
    (hMove : covarianceTranslationInvariantStatement) (hResp : WeightedResponses.ResponsesBounded)
    (hTP : ResponseInTheExpansion.TwoPointByTotalCovarianceStatement) (hSite : siteNearPairStatement)
    (hG : TestPairs.GeometryAndKernelBounds) :
    covarianceAtSeparationStatement := by
  have hQ := (covariance_form_of_chain hLev hGrow hLaw hMk hPr hBox hPM hMove hResp hTP hSite hG).and
    ((HoldsForShapes.of_holdsOnParameters hOn).and ((HoldsForShapes.of_holdsOnParameters hOne).and (HoldsForShapes.of_holdsOnParameters hLev)))
  intro a ha
  obtain ⟨L₁, r₁, C₁, hr₁, H₁⟩ := hQ a ha
  obtain ⟨L₂, r₂, C₂, hr₂, H₂⟩ := hScored a ha
  refine ⟨max L₁ L₂, fun c => min (r₁ c) (r₂ c), max C₁ C₂, fun c => lt_min (hr₁ c) (hr₂ c), ?_⟩
  intro L hodd hL Tb hTa hTL hD hCs hO hrt hCd Kr
  obtain ⟨Kr₀, y₂, G₂⟩ := H₂ L hodd (le_of_max_le_right hL) Tb hTa hTL hD hCs hO (hrt.trans (min_le_right _ _))
    ((le_max_right _ _).trans hCd)
  obtain ⟨y₁, G₁⟩ := H₁ L hodd (le_of_max_le_left hL) Tb hTa hTL hD hCs hO (hrt.trans (min_le_left _ _))
    ((le_max_left _ _).trans hCd) Kr₀
  refine ⟨max y₁ y₂, fun y hy hRS hKr Xi hXi vt h0 h1 => ?_⟩
  have hSc := G₂ y (le_of_max_le_right hy) hRS
  have hK₀ : Kr₀.Admissible (Tb.stepParameters y) := by
    obtain ⟨T₀, S₀, hS₀, hr₀⟩ := hSc y 0 (fun j hj => by
      obtain rfl : j = 0 := by omega
      exact le_refl _)
    have e := (hr₀.isAdmissible 0 le_rfl).params_admissible
    rw [hr₀.params_eq 0, hS₀] at e
    exact e
  obtain ⟨⟨C, d₀, hd₀, H⟩, hOn', hOne', hLv⟩ := G₁ y (le_of_max_le_left hy) hRS hK₀ Xi hXi vt h0 h1
  refine ⟨C, min d₀ (1 / 2), lt_min hd₀ (by norm_num), fun d hd hdd K β hdat hcut al hnum f h hp => ?_⟩
  have hd₀' : d ≤ d₀ := hdd.trans (min_le_left _ _)
  have hd2 : d ≤ 1 / 2 := hdd.trans (min_le_right _ _)
  have hK2 := hdat.two_le
  obtain ⟨-, hkK, -⟩ := hLv Xi hXi d hd (by linarith) K β hdat hcut
  obtain ⟨T, S, hSK, hSr⟩ := hSc β (K - 1) fun j hj => hdat.le_coupling j (by omega)
  have hst : ResponseInTheExpansion.IsTowerAtParameters Tb y T β (K - 1) := by
    refine ⟨hSr.startsAtWilson, fun j hj => ?_, fun j hj => (hSr.isFlowStep j hj).onFamily⟩
    cases j with
    | zero => exact (hSr.isFlowStep 0 (Nat.zero_le _)).coupling_eq
    | succ i => exact (hSr.isFlowStep i (by omega)).nextCoupling_eq
  have e₁ := hOn' β (K - 1) T S hSr
  rw [hSK] at e₁
  have hnum₀ : ResponseInTheExpansion.IsChainResponseCoeff (Tb.stepParameters y) Kr₀ β
      (separationLevel (Tb.stepParameters y) β K d) S.coeffs :=
    ⟨e₁.zero_eq, fun j hj => e₁.bounds j (by omega)⟩
  have hchain : BoxResponses.IsStateChain Tb y Kr₀ Xi d K β S.coeffs T :=
    ⟨hdat, hcut, hnum₀, hst, hSr.isCutoff_bottom, hSr.marksMeasurable, ⟨S, hSK, hSr, rfl⟩⟩
  obtain ⟨ε, hε, he⟩ := H d hd hd₀' K β _ T hchain f h hp
  have e₂ := hOne' Kr Kr₀ hKr hK₀ β _ al S.coeffs (fun j hj => hdat.le_coupling j (by omega)) hnum hnum₀ _ le_rfl
  exact ⟨ε, hε, by rw [e₂]; exact he⟩
end CovarianceAtSeparation
end YangMills.Construction.StateLaws
end
