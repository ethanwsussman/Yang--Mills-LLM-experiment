import YangMills.Construction.ReflectionPositivity.FromFivePointInequalitiesAtSmallTimesToTheConeProof
import YangMills.Construction.SpectralTheory.GeneratorsOfUnitaryGroupsAndSemigroups
import Mathlib
set_option autoImplicit false
open MeasureTheory Set Filter Topology
open scoped NNReal InnerProductSpace ENNReal
noncomputable section
namespace YangMills.Construction.ReflectionPositivity.ShiftSpectralMeasure
open YangMills.Construction.SeparatedTuples YangMills.Construction.ReflectionPositivity.TupleForm YangMills.Construction.ReflectionPositivity.Reconstruction YangMills.Construction.ReflectionPositivity.ContractionFunctionals YangMills.Construction.SpectralTheory
open YangMills.Construction.HilbertSpaceBasics (IsPosSemidef ofBounded)
section Forms
variable {ℋ : Type} [NormedAddCommGroup ℋ] [InnerProductSpace ℂ ℋ] [CompleteSpace ℋ]
abbrev HalfPlaneSpectralMeasure (ℋ : Type) [NormedAddCommGroup ℋ] [InnerProductSpace ℂ ℋ]
    [CompleteSpace ℋ] : Type :=
  YangMills.Construction.BorelSpectral.SpectralMeasure nonnegHalfPlane ℋ
theorem inner_apply_apply (J : HalfPlaneSpectralMeasure ℋ)
    (B C : YangMills.Construction.BorelSpectral.BorelSubsets nonnegHalfPlane) (ψ : ℋ) :
    ⟪J B ψ, J C ψ⟫_ℂ = ⟪ψ, J ⟨B.1 ∩ C.1, B.2.inter C.2⟩ ψ⟫_ℂ := by
  rw [J.map_inter]
  exact ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp
    (J.isStarProjection B).isSelfAdjoint ψ (J C ψ)
theorem tendsto_sum_apply_iUnion (J : HalfPlaneSpectralMeasure ℋ) (A : ℕ → Set nonnegHalfPlane)
    (hA : ∀ r, MeasurableSet (A r)) (hd : Pairwise fun r s => Disjoint (A r) (A s)) (ψ : ℋ) :
    Tendsto (fun N => ∑ r ∈ Finset.range N, J ⟨A r, hA r⟩ ψ) atTop
      (𝓝 (J ⟨⋃ r, A r, MeasurableSet.iUnion hA⟩ ψ)) := by
  obtain ⟨w, hw⟩ : ∃ w, w = J ⟨⋃ r, A r, MeasurableSet.iUnion hA⟩ ψ := ⟨_, rfl⟩
  obtain ⟨v, hv⟩ : ∃ v : ℕ → ℋ, v = fun r => J ⟨A r, hA r⟩ ψ := ⟨_, rfl⟩
  have hsum : HasSum (fun r => ‖v r‖ ^ 2) (‖w‖ ^ 2) := by
    have hc := J.countablyAdditive ψ (fun r => ⟨A r, hA r⟩) hd
    simp only [YangMills.Construction.BorelSpectral.SpectralMeasure.inner_apply_self_eq_norm_sq]
      at hc
    rw [hv, hw]
    exact Complex.hasSum_ofReal.mp hc
  have horth : ∀ r s, r ≠ s → ⟪v r, v s⟫_ℂ = 0 := fun r s hrs => by
    have he : (⟨A r ∩ A s, (hA r).inter (hA s)⟩ :
        YangMills.Construction.BorelSpectral.BorelSubsets nonnegHalfPlane) =
        ⟨∅, MeasurableSet.empty⟩ :=
      Subtype.ext (Set.disjoint_iff_inter_eq_empty.mp (hd hrs))
    rw [hv]
    simp only
    rw [inner_apply_apply J ⟨A r, hA r⟩ ⟨A s, hA s⟩ ψ]
    simp only
    rw [he, J.apply_empty]
    simp
  have hcross : ∀ r, ⟪w, v r⟫_ℂ = ((‖v r‖ ^ 2 : ℝ) : ℂ) := fun r => by
    have he : (⟨(⋃ r, A r) ∩ A r, (MeasurableSet.iUnion hA).inter (hA r)⟩ :
        YangMills.Construction.BorelSpectral.BorelSubsets nonnegHalfPlane) = ⟨A r, hA r⟩ :=
      Subtype.ext (inter_eq_right.mpr (subset_iUnion A r))
    rw [hv, hw]
    simp only
    rw [inner_apply_apply J ⟨⋃ r, A r, MeasurableSet.iUnion hA⟩ ⟨A r, hA r⟩ ψ]
    simp only
    rw [he, J.inner_apply_self_eq_norm_sq]
  have hkey : ∀ k, ‖w - ∑ r ∈ Finset.range k, v r‖ ^ 2 =
      ‖w‖ ^ 2 - ∑ r ∈ Finset.range k, ‖v r‖ ^ 2 := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have hin : ⟪w - ∑ r ∈ Finset.range k, v r, v k⟫_ℂ = ((‖v k‖ ^ 2 : ℝ) : ℂ) := by
        rw [inner_sub_left, sum_inner, Finset.sum_eq_zero, sub_zero, hcross]
        intro r hr
        exact horth r k (Finset.mem_range.mp hr).ne
      rw [Finset.sum_range_succ, Finset.sum_range_succ, ← sub_sub, norm_sub_sq (𝕜 := ℂ), ih, hin]
      have hre : RCLike.re ((‖v k‖ ^ 2 : ℝ) : ℂ) = ‖v k‖ ^ 2 := Complex.ofReal_re _
      rw [hre]
      ring
  have hsq : Tendsto (fun k => ‖w - ∑ r ∈ Finset.range k, v r‖ ^ 2) atTop (𝓝 0) := by
    have hl := (tendsto_const_nhds (x := ‖w‖ ^ 2)).sub hsum.tendsto_sum_nat
    rw [sub_self] at hl
    exact hl.congr fun k => (hkey k).symm
  have hnorm : Tendsto (fun k => ‖(∑ r ∈ Finset.range k, v r) - w‖) atTop (𝓝 0) := by
    have hl := hsq.sqrt
    rw [Real.sqrt_zero] at hl
    refine hl.congr fun k => ?_
    rw [Real.sqrt_sq (norm_nonneg _), norm_sub_rev]
  rw [← hw]
  have hl := tendsto_iff_norm_sub_tendsto_zero.mpr hnorm
  rw [hv] at hl
  exact hl
def ofHalfPlane (J : HalfPlaneSpectralMeasure ℋ) : SpectralMeasureOn energyMomentumRegion ℋ where
  toFun A := J ⟨Subtype.val ⁻¹' A.1, measurable_subtype_coe A.2.1⟩
  isStarProjection A := J.isStarProjection _
  map_empty := J.apply_empty
  map_whole := by
    have hw : (⟨Subtype.val ⁻¹' nonnegHalfPlane,
        measurable_subtype_coe measurableSet_nonnegHalfPlane⟩ :
        YangMills.Construction.BorelSpectral.BorelSubsets nonnegHalfPlane) =
        ⟨univ, MeasurableSet.univ⟩ :=
      Subtype.ext (eq_univ_of_forall fun y => y.2)
    exact (congrArg J.toFun hw).trans J.map_univ
  map_inter A B := J.map_inter ⟨_, measurable_subtype_coe A.2.1⟩ ⟨_, measurable_subtype_coe B.2.1⟩
  tendsto_sum A hA ψ := by
    have hl := tendsto_sum_apply_iUnion J (fun r => Subtype.val ⁻¹' (A r).1)
      (fun r => measurable_subtype_coe (A r).2.1) (fun r s hrs => (hA hrs).preimage _) ψ
    have hu : (⟨Subtype.val ⁻¹' ⋃ r, (A r).1,
        measurable_subtype_coe (MeasurableSet.iUnion fun r => (A r).2.1)⟩ :
        YangMills.Construction.BorelSpectral.BorelSubsets nonnegHalfPlane) =
        ⟨⋃ r, Subtype.val ⁻¹' (A r).1,
          MeasurableSet.iUnion fun r => measurable_subtype_coe (A r).2.1⟩ :=
      Subtype.ext preimage_iUnion
    refine hl.congr' ?_ |>.trans ?_
    · exact Eventually.of_forall fun _ => rfl
    · exact le_of_eq (congrArg (fun x => 𝓝 (J x ψ)) hu.symm)
theorem extend_ofHalfPlane (J : HalfPlaneSpectralMeasure ℋ) (A : BorelSets 2) :
    (ofHalfPlane J).extend A = J ⟨Subtype.val ⁻¹' A.1, measurable_subtype_coe A.2⟩ := by
  have hs : (⟨Subtype.val ⁻¹' (A.1 ∩ nonnegHalfPlane),
      measurable_subtype_coe (A.2.inter measurableSet_nonnegHalfPlane)⟩ :
      YangMills.Construction.BorelSpectral.BorelSubsets nonnegHalfPlane) =
      ⟨Subtype.val ⁻¹' A.1, measurable_subtype_coe A.2⟩ :=
    Subtype.ext (by ext y; simp)
  exact congrArg J.toFun hs
theorem diagonalMeasure_extend_ofHalfPlane (J : HalfPlaneSpectralMeasure ℋ) (ψ : ℋ) :
    (ofHalfPlane J).extend.spectralValueMeasure ψ = (J.diagMeasure ψ).map Subtype.val := by
  refine Measure.ext fun A hA => ?_
  rw [Measure.map_apply measurable_subtype_coe hA,
    (ofHalfPlane J).extend.spectralValueMeasure_apply ψ ⟨A, hA⟩,
    J.diagMeasure_apply ψ ⟨Subtype.val ⁻¹' A, measurable_subtype_coe hA⟩,
    extend_ofHalfPlane]
theorem integral_extendByZero_diagonalMeasure (J : HalfPlaneSpectralMeasure ℋ) (ψ : ℋ)
    (g : nonnegHalfPlane → ℂ) :
    ∫ x, extendByZero energyMomentumRegion g x ∂((ofHalfPlane J).extend.spectralValueMeasure ψ) =
      ∫ y, g y ∂(J.diagMeasure ψ) := by
  rw [diagonalMeasure_extend_ofHalfPlane,
    (MeasurableEmbedding.subtype_coe measurableSet_nonnegHalfPlane).integral_map]
  exact integral_congr_ae
    (Eventually.of_forall fun y => extendByZero_apply_of_mem energyMomentumRegion g y)
end Forms
section Rules
variable {ℋ : Type} [NormedAddCommGroup ℋ] [InnerProductSpace ℂ ℋ] [CompleteSpace ℋ]
def heatWave (t : ℝ≥0) (u : ℝ) (y : nonnegHalfPlane) : ℂ :=
  Complex.exp (((-(t : ℝ) * y.1 0 : ℝ) : ℂ) + Complex.I * ((u * y.1 1 : ℝ) : ℂ))
theorem measurable_heatWave (t : ℝ≥0) (u : ℝ) : Measurable (heatWave t u) := by
  have h₀ : Measurable fun y : nonnegHalfPlane => y.1 0 :=
    (measurable_pi_apply 0).comp measurable_subtype_coe
  have h₁ : Measurable fun y : nonnegHalfPlane => y.1 1 :=
    (measurable_pi_apply 1).comp measurable_subtype_coe
  exact Complex.measurable_exp.comp ((Complex.measurable_ofReal.comp (h₀.const_mul _)).add
    (measurable_const.mul (Complex.measurable_ofReal.comp (h₁.const_mul _))))
theorem norm_heatWave_le_one (t : ℝ≥0) (u : ℝ) (y : nonnegHalfPlane) : ‖heatWave t u y‖ ≤ 1 := by
  have hy : (0 : ℝ) ≤ y.1 0 := y.2
  have ht : (0 : ℝ) ≤ (t : ℝ) := t.2
  rw [heatWave, Complex.norm_exp, Real.exp_le_one_iff]
  have hr : (((-(t : ℝ) * y.1 0 : ℝ) : ℂ) + Complex.I * ((u * y.1 1 : ℝ) : ℂ)).re =
      -(t : ℝ) * y.1 0 := by
    simp
  rw [hr]
  nlinarith [mul_nonneg ht hy]
theorem measurable_extendByZero_heatWave (t : ℝ≥0) (u : ℝ) :
    Measurable (extendByZero energyMomentumRegion (heatWave t u)) :=
  measurable_extendByZero energyMomentumRegion (measurable_heatWave t u)
theorem isBoundedComplexFn_extendByZero_heatWave (t : ℝ≥0) (u : ℝ) :
    IsBoundedComplexFn (extendByZero energyMomentumRegion (heatWave t u)) := by
  refine ⟨1, fun x => ?_⟩
  by_cases hx : x ∈ energyMomentumRegion.1
  · have hm := extendByZero_apply_of_mem energyMomentumRegion (heatWave t u) ⟨x, hx⟩
    simp only at hm
    rw [hm]
    exact norm_heatWave_le_one t u ⟨x, hx⟩
  · rw [extendByZero_apply_of_not_mem energyMomentumRegion (heatWave t u) hx]
    simp
theorem inner_boundedIntegralOp {n : ℕ} [NeZero n] (E : ProjectionMeasure n ℋ)
    (R : E.CalculusLaws) {f : (Fin n → ℝ) → ℂ} (hf : Measurable f)
    (hb : IsBoundedComplexFn f) (ψ : ℋ) :
    ⟪ψ, E.boundedCalculus f ψ⟫_ℂ = ∫ x, f x ∂(E.spectralValueMeasure ψ) :=
  ((R.eq_functionalCalculus_iff f hf (toUnboundedOperator (E.boundedCalculus f))).mpr
    (R.isBoundedCalculusOf f hf hb).symm).2 ⟨ψ, Submodule.mem_top⟩
theorem ofBounded_eq_spectralIntegral {n : ℕ} [NeZero n] (E : ProjectionMeasure n ℋ)
    (R : E.CalculusLaws) {f : (Fin n → ℝ) → ℂ} (hf : Measurable f)
    (hb : IsBoundedComplexFn f) (T : ℋ →L[ℂ] ℋ)
    (h : ∀ ψ, ⟪ψ, T ψ⟫_ℂ = ∫ x, f x ∂(E.spectralValueMeasure ψ)) :
    ofBounded T = E.functionalCalculus f :=
  (R.eq_functionalCalculus_iff f hf (ofBounded T)).mp
    ⟨by rw [R.functionalDomain_eq_univ f hf hb]; rfl, fun ψ => h ψ⟩
theorem ofBounded_integralOp_eq (J : HalfPlaneSpectralMeasure ℋ)
    (R : (ofHalfPlane J).extend.CalculusLaws) (t : ℝ≥0) (u : ℝ) :
    ofBounded (J.integralOp (heatWave t u)) =
      (ofHalfPlane J).extend.functionalCalculusOn energyMomentumRegion (heatWave t u) := by
  have hf := measurable_extendByZero_heatWave t u
  have hb := isBoundedComplexFn_extendByZero_heatWave t u
  have hd : J.IsDiagonalIntegral (heatWave t u)
      ((ofHalfPlane J).extend.boundedCalculus
        (extendByZero energyMomentumRegion (heatWave t u))) := fun ψ => by
    rw [inner_boundedIntegralOp _ R hf hb, integral_extendByZero_diagonalMeasure]
  have hs : J.IsDiagonalIntegral (heatWave t u) (J.integralOp (heatWave t u)) :=
    Classical.epsilon_spec ⟨_, hd⟩
  exact ofBounded_eq_spectralIntegral _ R hf hb _ fun ψ => by
    rw [hs ψ, integral_extendByZero_diagonalMeasure]
def RepresentsShifts (T : ℝ≥0 → ℋ →L[ℂ] ℋ) (U : ℝ → ℋ →L[ℂ] ℋ)
    (E : SpectralMeasureOn energyMomentumRegion ℋ) : Prop :=
  ∀ t u, ofBounded (T t * U u) = E.extend.functionalCalculusOn energyMomentumRegion (heatWave t u)
theorem extend_eq_zero_of_disjoint (E : SpectralMeasureOn energyMomentumRegion ℋ) (S : BorelSets 2)
    (h : ∀ y ∈ S.1, y ∉ nonnegHalfPlane) : E.extend S = 0 := by
  have ht : SpectralMeasureOn.restrictSet energyMomentumRegion S =
      ⟨∅, MeasurableSet.empty, empty_subset _⟩ :=
    Subtype.ext (eq_empty_of_forall_notMem fun y hy => h y hy.1 hy.2)
  rw [E.extend_apply, ht, E.map_empty]
theorem spectralIntegral_congr_halfPlane (E : SpectralMeasureOn energyMomentumRegion ℋ)
    (R : E.extend.CalculusLaws) {f g : (Fin 2 → ℝ) → ℂ} (hf : Measurable f)
    (hg : Measurable g) (h : ∀ y ∈ nonnegHalfPlane, f y = g y) :
    E.extend.functionalCalculus f = E.extend.functionalCalculus g :=
  R.calculus_congr f g hf hg (extend_eq_zero_of_disjoint E _ fun y hy hY => hy (h y hY))
abbrev energySpectral (E : SpectralMeasureOn energyMomentumRegion ℋ) : ProjectionMeasure 1 ℋ :=
  E.extend.imageMeasure energyProj measurable_energyProj
abbrev momentumSpectral (E : SpectralMeasureOn energyMomentumRegion ℋ) : ProjectionMeasure 1 ℋ :=
  E.extend.imageMeasure momentumProj measurable_momentumProj
theorem energySpectral_concentrated (E : SpectralMeasureOn energyMomentumRegion ℋ) :
    (energySpectral E).IsConcentratedOn nonnegReals :=
  extend_eq_zero_of_disjoint E ⟨energyProj ⁻¹' nonnegReals.1ᶜ,
    measurable_energyProj nonnegReals.2.compl⟩ fun _ hy hY => hy hY
theorem heatSemigroup_energySpectral {T : ℝ≥0 → ℋ →L[ℂ] ℋ} {U : ℝ → ℋ →L[ℂ] ℋ}
    (E : SpectralMeasureOn energyMomentumRegion ℋ) (R : E.extend.CalculusLaws)
    (hU : U 0 = 1) (hE : RepresentsShifts T U E) (t : ℝ≥0) :
    (energySpectral E).expNegMulOp t = ofBounded (T t) := by
  have hp := hE t 0
  rw [hU, mul_one] at hp
  rw [hp]
  have hφ : Measurable fun x : nonnegReals.1 =>
      Complex.exp (-(t : ℂ) * ((x.1 0 : ℝ) : ℂ)) := by
    have h₀ : Measurable fun x : nonnegReals.1 => x.1 0 :=
      (measurable_pi_apply 0).comp measurable_subtype_coe
    exact Complex.measurable_exp.comp (measurable_const.mul (Complex.measurable_ofReal.comp h₀))
  have hm := measurable_extendByZero nonnegReals hφ
  unfold ProjectionMeasure.expNegMulOp ProjectionMeasure.functionalCalculusOn
  rw [R.calculus_imageMeasure 1 energyProj measurable_energyProj _ hm]
  refine spectralIntegral_congr_halfPlane E R (hm.comp measurable_energyProj)
    (measurable_extendByZero_heatWave t 0) fun y hy => ?_
  have h₁ := extendByZero_apply_of_mem nonnegReals
    (fun x : nonnegReals.1 => Complex.exp (-(t : ℂ) * ((x.1 0 : ℝ) : ℂ)))
    ⟨energyProj y, hy⟩
  have h₂ := extendByZero_apply_of_mem energyMomentumRegion (heatWave t 0) ⟨y, hy⟩
  simp only at h₁ h₂
  rw [Function.comp_apply, h₁, h₂]
  simp [heatWave, energyProj]
theorem unitaryGroup_momentumSpectral {T : ℝ≥0 → ℋ →L[ℂ] ℋ} {U : ℝ → ℋ →L[ℂ] ℋ}
    (E : SpectralMeasureOn energyMomentumRegion ℋ) (R : E.extend.CalculusLaws)
    (hT : T 0 = 1) (hE : RepresentsShifts T U E) (u : ℝ) :
    (momentumSpectral E).expIMulOp u = ofBounded (U u) := by
  have hp := hE 0 u
  rw [hT, one_mul] at hp
  rw [hp]
  have hφ : Measurable fun x : Fin 1 → ℝ => Complex.exp (Complex.I * u * ((x 0 : ℝ) : ℂ)) :=
    Complex.measurable_exp.comp
      (measurable_const.mul (Complex.measurable_ofReal.comp (measurable_pi_apply 0)))
  unfold ProjectionMeasure.expIMulOp ProjectionMeasure.functionalCalculusOn
  rw [R.calculus_imageMeasure 1 momentumProj measurable_momentumProj _ hφ]
  refine spectralIntegral_congr_halfPlane E R (hφ.comp measurable_momentumProj)
    (measurable_extendByZero_heatWave 0 u) fun y hy => ?_
  have h₂ := extendByZero_apply_of_mem energyMomentumRegion (heatWave 0 u) ⟨y, hy⟩
  simp only at h₂
  rw [Function.comp_apply, h₂]
  simp [heatWave, momentumProj]
  rw [mul_assoc]
theorem ext_apply {E E' : SpectralMeasureOn energyMomentumRegion ℋ} (h : ∀ A, E A = E' A) :
    E = E' := by
  cases E
  cases E'
  congr
  exact funext h
theorem apply_eq_extend (E : SpectralMeasureOn energyMomentumRegion ℋ)
    (A : BorelSubsets energyMomentumRegion) : E A = E.extend ⟨A.1, A.2.1⟩ := by
  rw [E.extend_apply]
  exact congrArg E.toFun (Subtype.ext (inter_eq_left.mpr A.2.2).symm)
theorem extend_pi (E : SpectralMeasureOn energyMomentumRegion ℋ) (Δ : Fin 2 → Set ℝ)
    (hΔ : ∀ r, MeasurableSet (Δ r)) :
    E.extend ⟨Set.pi univ Δ, MeasurableSet.univ_pi hΔ⟩ =
      energySpectral E (toLineBorel ⟨Δ 0, hΔ 0⟩) *
        momentumSpectral E (toLineBorel ⟨Δ 1, hΔ 1⟩) := by
  have hs : (⟨Set.pi univ Δ, MeasurableSet.univ_pi hΔ⟩ : BorelSets 2) =
      ⟨energyProj ⁻¹' (toLineBorel ⟨Δ 0, hΔ 0⟩).1 ∩ momentumProj ⁻¹' (toLineBorel ⟨Δ 1, hΔ 1⟩).1,
        (measurable_energyProj (toLineBorel ⟨Δ 0, hΔ 0⟩).2).inter
          (measurable_momentumProj (toLineBorel ⟨Δ 1, hΔ 1⟩).2)⟩ :=
    Subtype.ext (by
      ext y
      simp [Set.mem_pi, Fin.forall_fin_two, energyProj, momentumProj, toLineBorel])
  rw [hs]
  exact E.extend.map_inter ⟨_, measurable_energyProj (toLineBorel ⟨Δ 0, hΔ 0⟩).2⟩
    ⟨_, measurable_momentumProj (toLineBorel ⟨Δ 1, hΔ 1⟩).2⟩
theorem representsShifts_unique (hR : SpectralIntegralLawsHold)
    (hG : YangMills.Construction.GeneratorsAndFlows.GeneratorFlowTheorem)
    {T : ℝ≥0 → ℋ →L[ℂ] ℋ} {U : ℝ → ℋ →L[ℂ] ℋ} (hT : T 0 = 1) (hU : U 0 = 1)
    {E E' : SpectralMeasureOn energyMomentumRegion ℋ} (hE : RepresentsShifts T U E)
    (hE' : RepresentsShifts T U E') : E = E' := by
  have R : E.extend.CalculusLaws := hR 2 ℋ E.extend
  have R' : E'.extend.CalculusLaws := hR 2 ℋ E'.extend
  have hH : energySpectral E' = energySpectral E :=
    ((hG ℋ).1 (energySpectral E)).2.2.1.eq_of_expNegMulOp _ (energySpectral_concentrated E)
      (energySpectral_concentrated E') fun t _ _ => by
        rw [heatSemigroup_energySpectral E' R' hU hE' t, heatSemigroup_energySpectral E R hU hE t]
  have hP : momentumSpectral E' = momentumSpectral E :=
    ((hG ℋ).1 (momentumSpectral E)).2.2.1.eq_of_expIMulOp _ fun u => by
      rw [unitaryGroup_momentumSpectral E' R' hT hE' u, unitaryGroup_momentumSpectral E R hT hE u]
  have hr : E'.extend = E.extend :=
    R.ext_of_fourier_or_boxes E'.extend (Or.inr fun Δ hΔ => by
      rw [extend_pi E' Δ hΔ, extend_pi E Δ hΔ, hH, hP])
  refine ext_apply fun A => ?_
  rw [apply_eq_extend, apply_eq_extend E', hr]
theorem energyCoord_hasSpectralResolution (E : SpectralMeasureOn energyMomentumRegion ℋ)
    (R : E.extend.CalculusLaws) :
    HasSpectralResolution (E.extend.coordinateOp 0) (energySpectral E) := by
  unfold HasSpectralResolution
  rw [R.calculus_imageMeasure 1 energyProj measurable_energyProj _ (measurable_coordFun 0)]
  rfl
theorem momentumCoord_hasSpectralResolution (E : SpectralMeasureOn energyMomentumRegion ℋ)
    (R : E.extend.CalculusLaws) :
    HasSpectralResolution (E.extend.coordinateOp 1) (momentumSpectral E) := by
  unfold HasSpectralResolution
  rw [R.calculus_imageMeasure 1 momentumProj measurable_momentumProj _ (measurable_coordFun 0)]
  rfl
theorem apply_eq_of_eq_ofBounded {S : UnboundedOperator ℋ} {B : ℋ →L[ℂ] ℋ} (h : S = ofBounded B)
    (x : S.domain) : S x = B x := by apply _root_.YangMills.Construction.ReflectionPositivity.SmallTimeCone.apply_eq_of_eq_ofBounded <;> assumption
theorem ofBounded_injective {A B : ℋ →L[ℂ] ℋ} (h : ofBounded A = ofBounded B) : A = B := by
  ext ψ
  exact apply_eq_of_eq_ofBounded h ⟨ψ, Submodule.mem_top⟩
end Rules
section Reconstruction
variable (σ : TupleFunctional) (h : IsPosSemidef (reflectionForm σ))
abbrev axisShift (i : Fin 3) (u : ℝ) : PhysicalSpace σ h →L[ℂ] PhysicalSpace σ h :=
  spaceShift σ h (u • spatialBasisVec i)
theorem timeShift_vacuum (hT : IsTimeShiftFamily σ h (timeShift σ h)) (t : ℝ≥0) :
    timeShift σ h t (vacuum σ h) = vacuum σ h := by
  have ht := hT t (posTupleVec ⟨SepTuple.nil, nil_mem_supportedIn _⟩)
  have hact : pushSpan (translate ((t : ℝ) • timeBasisVec))
      (posTupleVec ⟨SepTuple.nil, nil_mem_supportedIn _⟩).1 =
      (posTupleVec ⟨SepTuple.nil, nil_mem_supportedIn _⟩).1 := by
    change pushSpan _ (basisVec SepTuple.nil) = basisVec SepTuple.nil
    rw [pushSpan, linearExtend_basisVec, push_nil]
  rw [hact] at ht
  unfold spanClass at ht
  rw [dif_pos (posTupleVec ⟨SepTuple.nil, nil_mem_supportedIn _⟩).2] at ht
  exact ht
theorem properties_of_axis (hR : SpectralIntegralLawsHold)
    (hG : YangMills.Construction.GeneratorsAndFlows.GeneratorFlowTheorem)
    (hS : SemigroupProperties σ h) (hP : SpatialProperties σ h)
    (hJ : JointSpectralProperties σ h) (i : Fin 3) :
    ExistsUniqueShiftMeasure σ h i ∧ EnergyOpProperties σ h i ∧ MomentumOpProperties σ h i ∧
      VacuumAnnihilated σ h i ∧ AgreesWithReconstruction σ h i := by
  obtain ⟨-, hTT, -, hSemi, -, -, hHam, -⟩ := hS
  obtain ⟨-, -, -, hRep, -, hFix, -, hMom, -⟩ := hP
  have hT0 : timeShift σ h 0 = 1 := hSemi.1
  have hU0 : axisShift σ h i 0 = 1 := by
    simp only [axisShift, zero_smul]
    exact hRep.2.1
  have R₀ : (ofHalfPlane (jointSpectralMeasure σ h i)).extend.CalculusLaws := hR 2 _ _
  have hE₀ : RepresentsShifts (timeShift σ h) (axisShift σ h i)
      (ofHalfPlane (jointSpectralMeasure σ h i)) := fun t u => by
    have hprod : timeShift σ h t * axisShift σ h i u =
        (jointSpectralMeasure σ h i).integralOp (heatWave t u) := by
      have hj := (hJ i).2.1 t u
      rw [hHam.2 t, show axisShift σ h i u = _ from (hMom i).2 u]
      exact hj
    rw [hprod]
    exact ofBounded_integralOp_eq _ R₀ t u
  have hpm : RepresentsShifts (timeShift σ h) (axisShift σ h i) (shiftSpectralMeasure σ h i) :=
    Classical.epsilon_spec (p := IsShiftSpectralMeasure σ h i) ⟨_, hE₀⟩
  have huniq : ∀ E, RepresentsShifts (timeShift σ h) (axisShift σ h i) E →
      E = shiftSpectralMeasure σ h i := fun E hE => representsShifts_unique hR hG hT0 hU0 hE hpm
  have hJm : shiftSpectralMeasure σ h i = ofHalfPlane (jointSpectralMeasure σ h i) :=
    (huniq _ hE₀).symm
  have R : (shiftSpectralMeasure σ h i).extend.CalculusLaws := hR 2 _ _
  have hCar := energySpectral_concentrated (shiftSpectralMeasure σ h i)
  have hExpH := heatSemigroup_energySpectral (shiftSpectralMeasure σ h i) R hU0 hpm
  have hExpP := unitaryGroup_momentumSpectral (shiftSpectralMeasure σ h i) R hT0 hpm
  have hSpH := energyCoord_hasSpectralResolution (shiftSpectralMeasure σ h i) R
  have hSpP := momentumCoord_hasSpectralResolution (shiftSpectralMeasure σ h i) R
  have hFacts := fun F => (hG (PhysicalSpace σ h)).1 F
  have hMeasure : ExistsUniqueShiftMeasure σ h i := ⟨⟨_, hpm, fun E hE => huniq E hE⟩, hpm⟩
  have hEnergy : EnergyOpProperties σ h i := by
    refine ⟨⟨_, fun _ => rfl, hSpH, hCar, hExpH⟩, ⟨_, hSpH, hCar⟩, ?_⟩
    intro A F hA hF hexp
    have hFH : F = energySpectral (shiftSpectralMeasure σ h i) :=
      (hFacts _).2.2.1.eq_of_expNegMulOp F hCar hF fun t _ _ => by rw [hexp t, hExpH t]
    have hA' : A = F.functionalCalculus (coordFun 0) := hA
    rw [hA', hFH]
    exact hSpH.symm
  have hMomentum : MomentumOpProperties σ h i := by
    refine ⟨⟨_, fun _ => rfl, hSpP, hExpP⟩, ?_⟩
    intro A F hA hexp
    have hFP : F = momentumSpectral (shiftSpectralMeasure σ h i) :=
      (hFacts _).2.2.1.eq_of_expIMulOp F fun u => by rw [hexp u, hExpP u]
    have hA' : A = F.functionalCalculus (coordFun 0) := hA
    rw [hA', hFP]
    exact hSpP.symm
  have hVacuum : VacuumAnnihilated σ h i := by
    constructor
    · have hSF := (hFacts (energySpectral (shiftSpectralMeasure σ h i))).2.1 hCar
      have hk : vacuum σ h ∈
          opKernel ((energySpectral (shiftSpectralMeasure σ h i)).coordinateOp 0) := by
        rw [hSF.kernel_eq_fixedPoints]
        intro t
        have he : (energySpectral (shiftSpectralMeasure σ h i)).contractionFlow t =
            timeShift σ h t :=
          ofBounded_injective ((hSF.expNegMulOp_eq t).symm.trans (hExpH t))
        rw [he]
        exact timeShift_vacuum σ h hTT t
      exact show vacuum σ h ∈ opKernel (energyOp σ h i) from by
        have hA : energyOp σ h i =
            (energySpectral (shiftSpectralMeasure σ h i)).coordinateOp 0 := hSpH
        rw [hA]
        exact hk
    · have hUF := (hFacts (momentumSpectral (shiftSpectralMeasure σ h i))).1
      have hfix : ∀ u, (momentumSpectral (shiftSpectralMeasure σ h i)).unitaryFlow u
          (vacuum σ h) = vacuum σ h := fun u => by
        have he : (momentumSpectral (shiftSpectralMeasure σ h i)).unitaryFlow u =
            axisShift σ h i u :=
          ofBounded_injective ((hUF.expIMulOp_eq u).symm.trans (hExpP u))
        rw [he]
        exact hFix _
      have hmem : vacuum σ h ∈
          ((momentumSpectral (shiftSpectralMeasure σ h i)).coordinateOp 0).domain := by
        refine (hUF.mem_domain_iff_bdd _).mpr ⟨0, ?_⟩
        rintro _ ⟨u, -, rfl⟩
        simp [hfix u]
      have hval : (momentumSpectral (shiftSpectralMeasure σ h i)).coordinateOp 0
          ⟨vacuum σ h, hmem⟩ = 0 := by
        have ht := hUF.tendsto_derivQuot ⟨vacuum σ h, hmem⟩
        have h0 : (fun u : ℝ => (Complex.I * (u : ℂ))⁻¹ •
            ((momentumSpectral (shiftSpectralMeasure σ h i)).unitaryFlow u (vacuum σ h) -
              vacuum σ h)) = fun _ => 0 := by
          funext u
          simp [hfix u]
        simp only [h0] at ht
        exact tendsto_nhds_unique ht tendsto_const_nhds
      have hk : vacuum σ h ∈
          opKernel ((momentumSpectral (shiftSpectralMeasure σ h i)).coordinateOp 0) :=
        ⟨hmem, hval⟩
      exact show vacuum σ h ∈ opKernel (momentumOp σ h i) from by
        have hA : momentumOp σ h i =
            (momentumSpectral (shiftSpectralMeasure σ h i)).coordinateOp 0 := hSpP
        rw [hA]
        exact hk
  have hRecon : AgreesWithReconstruction σ h i := by
    have hen : ∀ Δ, energyMarginal σ h i (toLineBorel Δ) =
        jointSpectralMeasure σ h i (energyBand Δ) := by
      intro Δ
      unfold energyMarginal
      rw [hJm]
      exact extend_ofHalfPlane _ _
    have hmo : ∀ Δ, momentumMarginal σ h i (toLineBorel Δ) =
        jointSpectralMeasure σ h i (momentumBand Δ) := by
      intro Δ
      unfold momentumMarginal
      rw [hJm]
      exact extend_ofHalfPlane _ _
    refine ⟨fun A => ?_, fun Δ => ⟨hen Δ, (hen Δ).trans ((hJ i).2.2.1 Δ)⟩,
      fun Δ => ⟨hmo Δ, (hmo Δ).trans ((hJ i).2.2.2.1 Δ)⟩⟩
    rw [hJm]
    rfl
  exact ⟨hMeasure, hEnergy, hMomentum, hVacuum, hRecon⟩
end Reconstruction
theorem shiftSpectralMeasureTheorem_holds (hRec : ReconstructionTheorem)
    (hR : SpectralIntegralLawsHold)
    (hG : YangMills.Construction.GeneratorsAndFlows.GeneratorFlowTheorem) :
    ShiftSpectralMeasureTheorem := by
  intro σ hσ
  obtain ⟨D₀, hD⟩ := hσ.contraction
  obtain ⟨h, -, hS, hP, -, hJ, -⟩ := hRec σ D₀ hD
  have hc := properties_of_axis σ h hR hG hS hP hJ
  refine ⟨h, hc, fun i j => ?_⟩
  obtain ⟨⟨F, -, hA, hF, hexp⟩, -, -⟩ := (hc i).2.1
  exact (hc j).2.1.2.2 _ F hA hF hexp
end YangMills.Construction.ReflectionPositivity.ShiftSpectralMeasure
