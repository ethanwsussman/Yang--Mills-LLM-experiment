import YangMills.Construction.ClusterExpansionOfAStep.ChartCoordinateIsBorel
import YangMills.Construction.ClusterExpansionOfAStep.ChartsOverTheTopOfAStep
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
open MeasureTheory
namespace YangMills.Construction
open BlockAverages LumpContours GaugeFixing TorusFields TorusLumps
namespace StepCosts
theorem norm_unitQuaternion (g : UnitQuaternion) : ‖((g : UnitQuaternion) : ℍ[ℝ])‖ = 1 := by apply _root_.YangMills.Construction.BlockAverages.norm_coe_unitQuaternion <;> assumption
theorem sq_norm_eq_re_sq_add_sq_norm_im (q : ℍ[ℝ]) : ‖q‖ ^ 2 = q.re ^ 2 + ‖q.im‖ ^ 2 := by apply _root_.YangMills.Construction.TopLevelSites.norm_sq_eq_re_sq_add_norm_im_sq <;> assumption
theorem minimalLog_eq_arccos_smul_im (g : UnitQuaternion)
    (hne : ((g : UnitQuaternion) : ℍ[ℝ]).re ≠ -1) :
    ((minimalLog g : imaginaryQuaternions) : ℍ[ℝ]) =
      (Real.arccos ((g : UnitQuaternion) : ℍ[ℝ]).re / ‖((g : UnitQuaternion) : ℍ[ℝ]).im‖) •
        ((g : UnitQuaternion) : ℍ[ℝ]).im := by
  set q : ℍ[ℝ] := ((g : UnitQuaternion) : ℍ[ℝ]) with hq
  have hsum : q.re ^ 2 + ‖q.im‖ ^ 2 = 1 := by
    rw [← sq_norm_eq_re_sq_add_sq_norm_im, hq, norm_unitQuaternion]
    norm_num
  have hle : q.re ≤ 1 := by nlinarith [sq_nonneg ‖q.im‖]
  have hge : -1 ≤ q.re := by nlinarith [sq_nonneg ‖q.im‖]
  by_cases hv : q.im = 0
  · have hr : q.re = 1 := by
      rw [hv, norm_zero] at hsum
      have hprod : (q.re - 1) * (q.re + 1) = 0 := by nlinarith
      rcases mul_eq_zero.mp hprod with h | h
      · linarith
      · exact absurd (by linarith) hne
    have hg : g = expUnit 0 := by
      apply Subtype.ext
      show q = NormedSpace.exp ((0 : imaginaryQuaternions) : ℍ[ℝ])
      have : q = 1 := by
        rw [← Quaternion.re_add_im q, hv, hr]
        simp
      rw [this]
      simp [NormedSpace.exp_zero]
    have hzero : minimalLog g = 0 := by
      rw [hg]
      exact minimalLog_expUnit 0 (by simpa using Real.pi_pos)
    rw [hzero, hv]
    simp
  · have hvpos : 0 < ‖q.im‖ := norm_pos_iff.2 hv
    set θ := Real.arccos q.re with hθ
    have hθnonneg : 0 ≤ θ := Real.arccos_nonneg _
    have hcos : Real.cos θ = q.re := Real.cos_arccos hge hle
    have hsin : Real.sin θ = ‖q.im‖ := by
      rw [hθ, Real.sin_arccos]
      have : 1 - q.re ^ 2 = ‖q.im‖ ^ 2 := by linarith
      rw [this, Real.sqrt_sq (norm_nonneg _)]
    have hθne : θ ≠ 0 := by
      intro h
      rw [h] at hsin
      simp at hsin
      exact hv (norm_eq_zero.1 hsin.symm)
    have hθlt : θ < Real.pi := by
      refine lt_of_le_of_ne (Real.arccos_le_pi _) fun h => ?_
      have := Real.arccos_eq_pi.mp h
      exact hne (le_antisymm this hge)
    have hmem : ((θ / ‖q.im‖) • q.im).re = 0 := by simp
    have hnorm : ‖(θ / ‖q.im‖) • q.im‖ = θ := by
      rw [norm_smul, Real.norm_of_nonneg (by positivity)]
      field_simp
    have hexp : expUnit ⟨_, hmem⟩ = g := by
      apply Subtype.ext
      show NormedSpace.exp ((θ / ‖q.im‖) • q.im) = q
      rw [Quaternion.exp_of_re_eq_zero _ hmem, hnorm, hcos, hsin, smul_smul]
      have : ‖q.im‖ / θ * (θ / ‖q.im‖) = 1 := by field_simp
      rw [this, one_smul]
      exact Quaternion.re_add_im q
    have hlog : minimalLog g = ⟨_, hmem⟩ := by
      rw [← hexp]
      refine minimalLog_expUnit _ ?_
      show ‖(θ / ‖q.im‖) • q.im‖ < Real.pi
      rw [hnorm]
      exact hθlt
    rw [hlog]
theorem continuous_re_unit : Continuous fun g : UnitQuaternion => ((g : UnitQuaternion) : ℍ[ℝ]).re :=
  Quaternion.continuous_re.comp continuous_subtype_val
theorem continuous_im_unit : Continuous fun g : UnitQuaternion => ((g : UnitQuaternion) : ℍ[ℝ]).im :=
  Quaternion.continuous_im.comp continuous_subtype_val
theorem eq_of_re_eq_neg_one : ∀ g g' : UnitQuaternion, ((g : UnitQuaternion) : ℍ[ℝ]).re = -1 →
    ((g' : UnitQuaternion) : ℍ[ℝ]).re = -1 → g = g' := by
  have key : ∀ g : UnitQuaternion, ((g : UnitQuaternion) : ℍ[ℝ]).re = -1 →
      ((g : UnitQuaternion) : ℍ[ℝ]) = -1 := by
    intro g h
    have hs := sq_norm_eq_re_sq_add_sq_norm_im (g : ℍ[ℝ])
    rw [norm_unitQuaternion, h] at hs
    have hsq : ‖((g : UnitQuaternion) : ℍ[ℝ]).im‖ ^ 2 = 0 := by linarith
    have him : ((g : UnitQuaternion) : ℍ[ℝ]).im = 0 := by
      have := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hsq
      exact norm_eq_zero.mp this
    rw [← Quaternion.re_add_im (g : ℍ[ℝ]), him, h]
    simp
  intro g g' h h'
  exact Subtype.ext ((key g h).trans (key g' h').symm)
theorem measurable_of_eqOn_re_ne_neg_one {f : UnitQuaternion → ℝ}
    (hoff : ∃ f' : UnitQuaternion → ℝ, Measurable f' ∧
      ∀ g, ((g : UnitQuaternion) : ℍ[ℝ]).re ≠ -1 → f g = f' g) : Measurable f := by
  classical
  obtain ⟨f', hm, he⟩ := hoff
  have hset : MeasurableSet {g : UnitQuaternion | ((g : UnitQuaternion) : ℍ[ℝ]).re = -1} :=
    (isClosed_eq continuous_re_unit continuous_const).measurableSet
  rcases Set.eq_empty_or_nonempty {g : UnitQuaternion | ((g : UnitQuaternion) : ℍ[ℝ]).re = -1}
    with hempty | ⟨g₀, hg₀⟩
  · have : f = f' := by
      funext g
      refine he g fun h => ?_
      have : g ∈ ({g : UnitQuaternion | ((g : UnitQuaternion) : ℍ[ℝ]).re = -1}) := h
      rw [hempty] at this
      exact this
    rw [this]
    exact hm
  · have : f = fun g => if ((g : UnitQuaternion) : ℍ[ℝ]).re = -1 then f g₀ else f' g := by
      funext g
      split_ifs with h
      · rw [eq_of_re_eq_neg_one g g₀ h hg₀]
      · exact he g h
    rw [this]
    exact Measurable.ite hset measurable_const hm
theorem measurableQuaternion_minimalLog :
    MeasurableQuaternion fun g : UnitQuaternion => ((minimalLog g : imaginaryQuaternions) : ℍ[ℝ]) := by
  have hA : Measurable fun g : UnitQuaternion =>
      Real.arccos ((g : UnitQuaternion) : ℍ[ℝ]).re / ‖((g : UnitQuaternion) : ℍ[ℝ]).im‖ :=
    (Real.continuous_arccos.comp continuous_re_unit).measurable.div continuous_im_unit.norm.measurable
  have hI : Continuous fun g : UnitQuaternion => ((g : UnitQuaternion) : ℍ[ℝ]).imI :=
    Quaternion.continuous_imI.comp continuous_subtype_val
  have hJ : Continuous fun g : UnitQuaternion => ((g : UnitQuaternion) : ℍ[ℝ]).imJ :=
    Quaternion.continuous_imJ.comp continuous_subtype_val
  have hK : Continuous fun g : UnitQuaternion => ((g : UnitQuaternion) : ℍ[ℝ]).imK :=
    Quaternion.continuous_imK.comp continuous_subtype_val
  refine ⟨?_, ?_, ?_, ?_⟩
  · have : (fun g : UnitQuaternion => ((minimalLog g : imaginaryQuaternions) : ℍ[ℝ]).re) =
        fun _ => 0 := by
      funext g
      exact (minimalLog g).2
    rw [this]
    exact measurable_const
  · refine measurable_of_eqOn_re_ne_neg_one ⟨_, hA.mul hI.measurable, fun g h => ?_⟩
    show ((minimalLog g : imaginaryQuaternions) : ℍ[ℝ]).imI =
      Real.arccos ((g : UnitQuaternion) : ℍ[ℝ]).re / ‖((g : UnitQuaternion) : ℍ[ℝ]).im‖ *
        ((g : UnitQuaternion) : ℍ[ℝ]).imI
    rw [minimalLog_eq_arccos_smul_im g h]
    simp
  · refine measurable_of_eqOn_re_ne_neg_one ⟨_, hA.mul hJ.measurable, fun g h => ?_⟩
    show ((minimalLog g : imaginaryQuaternions) : ℍ[ℝ]).imJ =
      Real.arccos ((g : UnitQuaternion) : ℍ[ℝ]).re / ‖((g : UnitQuaternion) : ℍ[ℝ]).im‖ *
        ((g : UnitQuaternion) : ℍ[ℝ]).imJ
    rw [minimalLog_eq_arccos_smul_im g h]
    simp
  · refine measurable_of_eqOn_re_ne_neg_one ⟨_, hA.mul hK.measurable, fun g h => ?_⟩
    show ((minimalLog g : imaginaryQuaternions) : ℍ[ℝ]).imK =
      Real.arccos ((g : UnitQuaternion) : ℍ[ℝ]).re / ‖((g : UnitQuaternion) : ℍ[ℝ]).im‖ *
        ((g : UnitQuaternion) : ℍ[ℝ]).imK
    rw [minimalLog_eq_arccos_smul_im g h]
    simp
section Continuity
variable {F : BlockFrame} {j : ℕ}
theorem continuous_pathHolonomy (l : List PathStep) (x : F.Site j) :
    Continuous fun X : F.GaugeField j => pathHolonomy X x l := by apply _root_.YangMills.Construction.BlockAverages.MinimalChain.continuous_pathHolonomy <;> assumption
theorem continuous_readAtLevel {m : ℕ} (j : ℕ) : Continuous (readAtLevel (n := m) F j) := by
  unfold readAtLevel
  fun_prop
end Continuity
instance instSecondCountableTorusField (m : ℕ) [NeZero m] :
    SecondCountableTopology (TorusField m) := by
  unfold TorusField
  infer_instance
instance instBorelTorusField (m : ℕ) [NeZero m] : BorelSpace (TorusField m) := by
  unfold TorusField
  infer_instance
theorem chartCoordMeasurable_holds : ChartCoordMeasurable := by
  intro ℓ n _ b
  classical
  have : NeZero (n * ℓ.side) := ⟨mul_ne_zero (NeZero.ne n) (NeZero.ne ℓ.side)⟩
  set F := stepBlockFrame ℓ.side n with hF
  set x : F.Site F.depth := torusSiteInFrame F 0 b.1 with hx
  have hcomp : ∀ A : TorusField n × TorusField (n * ℓ.side) → UnitQuaternion, Continuous A →
      MeasurableQuaternion fun p => ((minimalLog (A p) : imaginaryQuaternions) : ℍ[ℝ]) := by
    intro A hA
    obtain ⟨h0, h1, h2, h3⟩ := measurableQuaternion_minimalLog
    exact ⟨h0.comp hA.measurable, h1.comp hA.measurable, h2.comp hA.measurable,
      h3.comp hA.measurable⟩
  have hfine : Continuous fun p : TorusField n × TorusField (n * ℓ.side) => readAtLevel F 0 p.2 :=
    (continuous_readAtLevel 0).comp continuous_snd
  have hcoarse : Continuous fun p : TorusField n × TorusField (n * ℓ.side) => readAtLevel F 1 p.1 :=
    (continuous_readAtLevel 1).comp continuous_fst
  have hgauge : ∀ z : F.Site F.depth, Continuous fun p : TorusField n × TorusField (n * ℓ.side) =>
      axialGauge 1 (readAtLevel F 0 p.2) z := by
    intro z
    unfold axialGauge
    exact (continuous_pathHolonomy _ _).comp hfine
  have htransform : Continuous fun p : TorusField n × TorusField (n * ℓ.side) =>
      BlockAverages.gaugeTransform (axialGauge 1 (readAtLevel F 0 p.2)) (readAtLevel F 0 p.2) x b.2 := by
    unfold BlockAverages.gaugeTransform
    have hlink : Continuous fun p : TorusField n × TorusField (n * ℓ.side) =>
        readAtLevel F 0 p.2 x b.2 :=
      (continuous_apply b.2).comp ((continuous_apply x).comp hfine)
    exact ((hgauge x).mul hlink).mul (hgauge _).inv
  by_cases hc : IsCrossingBond (x, b.2)
  · have e : (fun p : TorusField n × TorusField (n * ℓ.side) =>
        ((chartCoord ℓ p.1 p.2 b : imaginaryQuaternions) : ℍ[ℝ])) =
        fun p => ((minimalLog (BlockAverages.gaugeTransform (axialGauge 1 (readAtLevel F 0 p.2))
          (readAtLevel F 0 p.2) x b.2 *
          (readAtLevel F 1 p.1 (enclosingCell x) b.2)⁻¹) : imaginaryQuaternions) : ℍ[ℝ]) := by
      funext p
      simp only [chartCoord, bondCoordinate]
      rw [if_pos hc]
    rw [e]
    refine hcomp _ (htransform.mul ?_)
    exact ((continuous_apply b.2).comp ((continuous_apply (enclosingCell x)).comp hcoarse)).inv
  · have e : (fun p : TorusField n × TorusField (n * ℓ.side) =>
        ((chartCoord ℓ p.1 p.2 b : imaginaryQuaternions) : ℍ[ℝ])) =
        fun p => ((minimalLog (BlockAverages.gaugeTransform (axialGauge 1 (readAtLevel F 0 p.2))
          (readAtLevel F 0 p.2) x b.2) : imaginaryQuaternions) : ℍ[ℝ]) := by
      funext p
      simp only [chartCoord, bondCoordinate]
      rw [if_neg hc]
    rw [e]
    exact hcomp _ htransform
end StepCosts
end YangMills.Construction
end
