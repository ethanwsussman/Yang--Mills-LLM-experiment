import YangMills.Construction.ReflectionPositivity.PropertiesOfTheFormOfAFunctionalProof
import YangMills.Construction.Continuum.CubicGroupAndHypercubicMapsKeepingTheTimeAxisProof
import YangMills.Construction.HilbertSpace.BasicFacts
import YangMills.Construction.ReflectionPositivity.ComplementsToTheReconstruction
import YangMills.Construction.ReflectionPositivity.HamiltonianBoundsTheMomentaInTheLimit
import YangMills.Construction.ReflectionPositivity.MeasureOfTheSemigroupAndOneGroupOfTranslationsProof
import YangMills.Construction.ReflectionPositivity.SymmetriesAndMirrorsOfTheLimitProof
import YangMills.Construction.SpectralTheory.JointMeasureOfASemigroupAndARepresentation
import Mathlib
set_option autoImplicit false
open MeasureTheory Set Filter Topology
open scoped NNReal InnerProductSpace ENNReal
noncomputable section
namespace YangMills.Construction.ReflectionPositivity.ReconstructionComplements
open YangMills.Construction.SeparatedTuples YangMills.Construction.ReflectionPositivity.TupleForm YangMills.Construction.SpectralTheory YangMills.Construction.LimitConventions
open YangMills.Construction.InfiniteLattice (AmbientSpace hyperoctahedralLinearGroup)
open YangMills.Construction.ReflectionPositivity.Reconstruction (PhysicalSpace spanClass posClass
  spaceShift spatialBasisVec embedSpatial timeShift timeBasisVec vacuum)
open YangMills.Construction.Continuum.AxisPreservingSymmetries (timeBasisVector)
open YangMills.Construction.ReflectionPositivity.PairMeasureOperators (pairHamiltonian pairMomentum)
open YangMills.Construction.ReflectionPositivity.ShiftSpectralMeasure (energyMomentumRegion
  shiftSpectralMeasure IsShiftSpectralMeasure)
open YangMills.Construction.HilbertSpaceBasics (IsPosSemidef ofBounded)
section Forms
variable {ℋ : Type} [NormedAddCommGroup ℋ] [InnerProductSpace ℂ ℋ] [CompleteSpace ℋ]
abbrev posEnergyRegion : Set (Fin 4 → ℝ) := SemigroupRepresentation.nonnegHalfSpace 3
theorem measurableSet_posEnergyRegion : MeasurableSet posEnergyRegion :=
  SemigroupRepresentation.measurableSet_nonnegHalfSpace 3
def posEnergyBorel : BorelSets 4 := ⟨posEnergyRegion, measurableSet_posEnergyRegion⟩
abbrev SubtypeSpectralMeasure (ℋ : Type) [NormedAddCommGroup ℋ] [InnerProductSpace ℂ ℋ]
    [CompleteSpace ℋ] : Type :=
  BorelSpectral.SpectralMeasure posEnergyRegion ℋ
theorem inner_apply_apply_eq (J : SubtypeSpectralMeasure ℋ)
    (B C : BorelSpectral.BorelSubsets posEnergyRegion) (ψ : ℋ) :
    ⟪J B ψ, J C ψ⟫_ℂ = ⟪ψ, J ⟨B.1 ∩ C.1, B.2.inter C.2⟩ ψ⟫_ℂ := by
  rw [J.map_inter]
  exact ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp
    (J.isStarProjection B).isSelfAdjoint ψ (J C ψ)
theorem tendsto_sum_range_apply (J : SubtypeSpectralMeasure ℋ) (A : ℕ → Set posEnergyRegion)
    (hA : ∀ r, MeasurableSet (A r)) (hd : Pairwise fun r s => Disjoint (A r) (A s)) (ψ : ℋ) :
    Tendsto (fun N => ∑ r ∈ Finset.range N, J ⟨A r, hA r⟩ ψ) atTop
      (𝓝 (J ⟨⋃ r, A r, MeasurableSet.iUnion hA⟩ ψ)) := by
  obtain ⟨w, hw⟩ : ∃ w, w = J ⟨⋃ r, A r, MeasurableSet.iUnion hA⟩ ψ := ⟨_, rfl⟩
  obtain ⟨v, hv⟩ : ∃ v : ℕ → ℋ, v = fun r => J ⟨A r, hA r⟩ ψ := ⟨_, rfl⟩
  have hsum : HasSum (fun r => ‖v r‖ ^ 2) (‖w‖ ^ 2) := by
    have h := J.countablyAdditive ψ (fun r => ⟨A r, hA r⟩) hd
    simp only [BorelSpectral.SpectralMeasure.inner_apply_self_eq_norm_sq] at h
    rw [hv, hw]
    exact Complex.hasSum_ofReal.mp h
  have horth : ∀ r s, r ≠ s → ⟪v r, v s⟫_ℂ = 0 := fun r s hrs => by
    have he : (⟨A r ∩ A s, (hA r).inter (hA s)⟩ :
        BorelSpectral.BorelSubsets posEnergyRegion) =
        ⟨∅, MeasurableSet.empty⟩ :=
      Subtype.ext (Set.disjoint_iff_inter_eq_empty.mp (hd hrs))
    rw [hv]
    simp only
    rw [inner_apply_apply_eq J ⟨A r, hA r⟩ ⟨A s, hA s⟩ ψ]
    simp only
    rw [he, J.apply_empty]
    simp
  have hcross : ∀ r, ⟪w, v r⟫_ℂ = ((‖v r‖ ^ 2 : ℝ) : ℂ) := fun r => by
    have he : (⟨(⋃ r, A r) ∩ A r, (MeasurableSet.iUnion hA).inter (hA r)⟩ :
        BorelSpectral.BorelSubsets posEnergyRegion) = ⟨A r, hA r⟩ :=
      Subtype.ext (inter_eq_right.mpr (subset_iUnion A r))
    rw [hv, hw]
    simp only
    rw [inner_apply_apply_eq J ⟨⋃ r, A r, MeasurableSet.iUnion hA⟩ ⟨A r, hA r⟩ ψ]
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
    have h := (tendsto_const_nhds (x := ‖w‖ ^ 2)).sub hsum.tendsto_sum_nat
    rw [sub_self] at h
    exact h.congr fun k => (hkey k).symm
  have hnorm : Tendsto (fun k => ‖(∑ r ∈ Finset.range k, v r) - w‖) atTop (𝓝 0) := by
    have h := hsq.sqrt
    rw [Real.sqrt_zero] at h
    refine h.congr fun k => ?_
    rw [Real.sqrt_sq (norm_nonneg _), norm_sub_rev]
  rw [← hw]
  have h := tendsto_iff_norm_sub_tendsto_zero.mpr hnorm
  rw [hv] at h
  exact h
def toSpectralMeasureOn (J : SubtypeSpectralMeasure ℋ) : SpectralMeasureOn posEnergyBorel ℋ where
  toFun A := J ⟨Subtype.val ⁻¹' A.1, measurable_subtype_coe A.2.1⟩
  isStarProjection A := J.isStarProjection _
  map_empty := J.apply_empty
  map_whole := by
    have h : (⟨Subtype.val ⁻¹' posEnergyRegion,
        measurable_subtype_coe measurableSet_posEnergyRegion⟩ :
        BorelSpectral.BorelSubsets posEnergyRegion) =
        ⟨univ, MeasurableSet.univ⟩ :=
      Subtype.ext (eq_univ_of_forall fun y => y.2)
    exact (congrArg J.toFun h).trans J.map_univ
  map_inter A B := J.map_inter ⟨_, measurable_subtype_coe A.2.1⟩ ⟨_, measurable_subtype_coe B.2.1⟩
  tendsto_sum A hA ψ := by
    have h := tendsto_sum_range_apply J (fun r => Subtype.val ⁻¹' (A r).1)
      (fun r => measurable_subtype_coe (A r).2.1) (fun r s hrs => (hA hrs).preimage _) ψ
    have hu : (⟨Subtype.val ⁻¹' ⋃ r, (A r).1,
        measurable_subtype_coe (MeasurableSet.iUnion fun r => (A r).2.1)⟩ :
        BorelSpectral.BorelSubsets posEnergyRegion) =
        ⟨⋃ r, Subtype.val ⁻¹' (A r).1,
          MeasurableSet.iUnion fun r => measurable_subtype_coe (A r).2.1⟩ :=
      Subtype.ext preimage_iUnion
    refine h.congr' ?_ |>.trans ?_
    · exact Eventually.of_forall fun _ => rfl
    · exact le_of_eq (congrArg (fun x => 𝓝 (J x ψ)) hu.symm)
theorem extend_toSpectralMeasureOn (J : SubtypeSpectralMeasure ℋ) (A : BorelSets 4) :
    (toSpectralMeasureOn J).extend A = J ⟨Subtype.val ⁻¹' A.1, measurable_subtype_coe A.2⟩ := by
  have h : (⟨Subtype.val ⁻¹' (A.1 ∩ posEnergyRegion),
      measurable_subtype_coe (A.2.inter measurableSet_posEnergyRegion)⟩ :
      BorelSpectral.BorelSubsets posEnergyRegion) =
      ⟨Subtype.val ⁻¹' A.1, measurable_subtype_coe A.2⟩ :=
    Subtype.ext (by ext y; simp)
  exact congrArg J.toFun h
theorem diagonalMeasure_extend (J : SubtypeSpectralMeasure ℋ) (ψ : ℋ) :
    (toSpectralMeasureOn J).extend.spectralValueMeasure ψ = (J.diagMeasure ψ).map Subtype.val := by
  refine Measure.ext fun A hA => ?_
  rw [Measure.map_apply measurable_subtype_coe hA,
    (toSpectralMeasureOn J).extend.spectralValueMeasure_apply ψ ⟨A, hA⟩,
    J.diagMeasure_apply ψ ⟨Subtype.val ⁻¹' A, measurable_subtype_coe hA⟩,
    extend_toSpectralMeasureOn]
theorem integral_diagonalMeasure_extend (J : SubtypeSpectralMeasure ℋ) (ψ : ℋ)
    (g : posEnergyRegion → ℂ) :
    ∫ x, extendByZero posEnergyBorel g x ∂((toSpectralMeasureOn J).extend.spectralValueMeasure ψ) =
      ∫ y, g y ∂(J.diagMeasure ψ) := by
  rw [diagonalMeasure_extend,
    (MeasurableEmbedding.subtype_coe measurableSet_posEnergyRegion).integral_map]
  exact integral_congr_ae
    (Eventually.of_forall fun y => extendByZero_apply_of_mem posEnergyBorel g y)
end Forms
section Phases
theorem continuous_heatPhase (t : ℝ≥0) (a : SpaceVec) : Continuous (heatPhase t a) := by
  unfold heatPhase spaceDot SeparatedTupleFunctionals.dotProd spatialPart
  fun_prop
theorem measurable_heatPhase (t : ℝ≥0) (a : SpaceVec) : Measurable (heatPhase t a) :=
  (continuous_heatPhase t a).measurable
theorem norm_heatPhase_le_one (t : ℝ≥0) (a : SpaceVec) {y : Fin 4 → ℝ} (hy : 0 ≤ y 0) :
    ‖heatPhase t a y‖ ≤ 1 := by
  have ht : (0 : ℝ) ≤ (t : ℝ) := t.2
  rw [heatPhase, Complex.norm_exp, Real.exp_le_one_iff]
  have h : (((-(t : ℝ) * y 0 : ℝ) : ℂ) + Complex.I *
      ((spaceDot a (spatialPart y) : ℝ) : ℂ)).re = -(t : ℝ) * y 0 := by
    simp
  rw [h]
  nlinarith [mul_nonneg ht hy]
def heatPhaseOn (t : ℝ≥0) (a : SpaceVec) (y : posEnergyRegion) : ℂ :=
  heatPhase t a y.1
theorem measurable_heatPhaseOn (t : ℝ≥0) (a : SpaceVec) : Measurable (heatPhaseOn t a) :=
  (measurable_heatPhase t a).comp measurable_subtype_coe
theorem measurable_extendByZero_heatPhaseOn (t : ℝ≥0) (a : SpaceVec) :
    Measurable (extendByZero posEnergyBorel (heatPhaseOn t a)) :=
  measurable_extendByZero posEnergyBorel (measurable_heatPhaseOn t a)
theorem isBoundedComplexFn_extendByZero_heatPhaseOn (t : ℝ≥0) (a : SpaceVec) :
    IsBoundedComplexFn (extendByZero posEnergyBorel (heatPhaseOn t a)) := by
  refine ⟨1, fun x => ?_⟩
  by_cases hx : x ∈ posEnergyBorel.1
  · have h := extendByZero_apply_of_mem posEnergyBorel (heatPhaseOn t a) ⟨x, hx⟩
    simp only at h
    rw [h]
    exact norm_heatPhase_le_one t a hx
  · rw [extendByZero_apply_of_not_mem posEnergyBorel (heatPhaseOn t a) hx]
    simp
theorem isBoundedComplexFn_heatPhase_zero (a : SpaceVec) :
    IsBoundedComplexFn (heatPhase 0 a) := by
  refine ⟨1, fun y => ?_⟩
  rw [heatPhase, Complex.norm_exp]
  simp
def energyPhase (τ : ℝ) (y : Fin 4 → ℝ) : ℂ :=
  Complex.exp (Complex.I * τ * (y 0 : ℝ))
theorem measurable_energyPhase (τ : ℝ) : Measurable (energyPhase τ) := by
  have h : Continuous (energyPhase τ) := by
    unfold energyPhase
    fun_prop
  exact h.measurable
theorem isBoundedComplexFn_energyPhase (τ : ℝ) : IsBoundedComplexFn (energyPhase τ) := by
  refine ⟨1, fun y => ?_⟩
  have h : Complex.I * τ * (y 0 : ℝ) = ((τ * y 0 : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  rw [energyPhase, h, Complex.norm_exp_ofReal_mul_I]
theorem energyPhase_mul_heatPhase_zero (τ : ℝ) (a : SpaceVec) (y : Fin 4 → ℝ) :
    energyPhase τ y * heatPhase 0 a y = unitaryPhase τ a y := by
  rw [energyPhase, heatPhase, unitaryPhase, ← Complex.exp_add]
  congr 1
  push_cast
  simp
  ring
end Phases
section Products
variable {ℋ : Type} [NormedAddCommGroup ℋ] [InnerProductSpace ℂ ℋ] [CompleteSpace ℋ]
theorem compBounded_ofBounded (B C : ℋ →L[ℂ] ℋ) :
    compBounded (ofBounded B) C = ofBounded (B * C) := by
  refine (unboundedOperator_eq_iff _ _).2 ⟨Submodule.comap_top _, ?_⟩
  rintro ⟨x, hx⟩ ⟨y, hy⟩ hxy
  obtain rfl : x = y := hxy
  rfl
theorem boundedComp_ofBounded (B C : ℋ →L[ℂ] ℋ) :
    boundedComp B (ofBounded C) = ofBounded (B * C) :=
  rfl
theorem eq_of_ofBounded_eq {A B : ℋ →L[ℂ] ℋ} (h : ofBounded A = ofBounded B) : A = B := by apply _root_.YangMills.Construction.ReflectionPositivity.ShiftSpectralMeasure.ofBounded_injective <;> assumption
end Products
section Rules
variable {ℋ : Type} [NormedAddCommGroup ℋ] [InnerProductSpace ℂ ℋ] [CompleteSpace ℋ]
theorem inner_boundedIntegralOp {n : ℕ} [NeZero n] (E : ProjectionMeasure n ℋ)
    (R : E.CalculusLaws) {f : (Fin n → ℝ) → ℂ} (hf : Measurable f)
    (hb : IsBoundedComplexFn f) (ψ : ℋ) :
    ⟪ψ, E.boundedCalculus f ψ⟫_ℂ = ∫ x, f x ∂(E.spectralValueMeasure ψ) := by apply _root_.YangMills.Construction.ReflectionPositivity.ShiftSpectralMeasure.inner_boundedIntegralOp <;> assumption
theorem ofBounded_eq_spectralIntegral {n : ℕ} [NeZero n] (E : ProjectionMeasure n ℋ)
    (R : E.CalculusLaws) {f : (Fin n → ℝ) → ℂ} (hf : Measurable f)
    (hb : IsBoundedComplexFn f) (T : ℋ →L[ℂ] ℋ)
    (h : ∀ ψ, ⟪ψ, T ψ⟫_ℂ = ∫ x, f x ∂(E.spectralValueMeasure ψ)) :
    ofBounded T = E.functionalCalculus f := by apply _root_.YangMills.Construction.ReflectionPositivity.ShiftSpectralMeasure.ofBounded_eq_spectralIntegral <;> assumption
theorem ofBounded_integralOp_eq (J : SubtypeSpectralMeasure ℋ)
    (R : (toSpectralMeasureOn J).extend.CalculusLaws) (t : ℝ≥0) (a : SpaceVec) :
    ofBounded (J.integralOp (heatPhaseOn t a)) =
      (toSpectralMeasureOn J).extend.functionalCalculusOn posEnergyBorel (heatPhaseOn t a) := by
  have hf := measurable_extendByZero_heatPhaseOn t a
  have hb := isBoundedComplexFn_extendByZero_heatPhaseOn t a
  have hd : J.IsDiagonalIntegral (heatPhaseOn t a)
      ((toSpectralMeasureOn J).extend.boundedCalculus
        (extendByZero posEnergyBorel (heatPhaseOn t a))) := fun ψ => by
    rw [inner_boundedIntegralOp _ R hf hb, integral_diagonalMeasure_extend]
  have hs : J.IsDiagonalIntegral (heatPhaseOn t a) (J.integralOp (heatPhaseOn t a)) :=
    Classical.epsilon_spec ⟨_, hd⟩
  exact ofBounded_eq_spectralIntegral _ R hf hb _ fun ψ => by
    rw [hs ψ, integral_diagonalMeasure_extend]
theorem extend_eq_zero_of_disjoint (E : SpectralMeasureOn posEnergyBorel ℋ) (S : BorelSets 4)
    (h : ∀ y ∈ S.1, y ∉ posEnergyRegion) : E.extend S = 0 := by
  have ht : SpectralMeasureOn.restrictSet posEnergyBorel S =
      ⟨∅, MeasurableSet.empty, empty_subset _⟩ :=
    Subtype.ext (eq_empty_of_forall_notMem fun y hy => h y hy.1 hy.2)
  rw [E.extend_apply, ht, E.map_empty]
theorem spectralIntegral_congr_on (E : SpectralMeasureOn posEnergyBorel ℋ)
    (R : E.extend.CalculusLaws) {f g : (Fin 4 → ℝ) → ℂ} (hf : Measurable f)
    (hg : Measurable g) (h : ∀ y ∈ posEnergyRegion, f y = g y) :
    E.extend.functionalCalculus f = E.extend.functionalCalculus g :=
  R.calculus_congr f g hf hg (extend_eq_zero_of_disjoint E _ fun y hy hY => hy (h y hY))
def IsHeatShiftMeasure (T : ℝ≥0 → ℋ →L[ℂ] ℋ) (U : SpaceVec → ℋ →L[ℂ] ℋ)
    (E : SpectralMeasureOn posEnergyBorel ℋ) : Prop :=
  ∀ t a, ofBounded (T t * U a) = E.extend.functionalCalculus (heatPhase t a)
theorem isHeatShiftMeasure_toSpectralMeasureOn (J : SubtypeSpectralMeasure ℋ)
    (R : (toSpectralMeasureOn J).extend.CalculusLaws)
    {T : ℝ≥0 → ℋ →L[ℂ] ℋ} {U : SpaceVec → ℋ →L[ℂ] ℋ}
    (hJ : SemigroupRepresentation.IsJointSpectralMeasure J T U) :
    IsHeatShiftMeasure T U (toSpectralMeasureOn J) := fun t a => by
  have h : T t * U a = J.integralOp (heatPhaseOn t a) := hJ t a
  rw [h, ofBounded_integralOp_eq J R t a]
  refine spectralIntegral_congr_on _ R (measurable_extendByZero_heatPhaseOn t a)
    (measurable_heatPhase t a) fun y hy => ?_
  exact extendByZero_apply_of_mem posEnergyBorel (heatPhaseOn t a) ⟨y, hy⟩
abbrev marginal (K : ProjectionMeasure 4 ℋ) (r : Fin 4) : ProjectionMeasure 1 ℋ :=
  K.imageMeasure (coordProj r) (measurable_coordProj r)
theorem hasSpectralResolution_marginal (K : ProjectionMeasure 4 ℋ)
    (R : K.CalculusLaws) (r : Fin 4) :
    HasSpectralResolution (K.coordinateOp r) (marginal K r) := by
  unfold HasSpectralResolution
  rw [R.calculus_imageMeasure 1 _ _ _ (measurable_coordFun 0)]
  rfl
theorem unitaryGroup_marginal (K : ProjectionMeasure 4 ℋ) (R : K.CalculusLaws)
    (r : Fin 4) (u : ℝ) :
    (marginal K r).expIMulOp u =
      K.functionalCalculus fun y => Complex.exp (Complex.I * u * (y r : ℝ)) := by
  have hφ : Measurable fun x : Fin 1 → ℝ => Complex.exp (Complex.I * u * ((x 0 : ℝ) : ℂ)) :=
    Complex.measurable_exp.comp
      (measurable_const.mul (Complex.measurable_ofReal.comp (measurable_pi_apply 0)))
  unfold ProjectionMeasure.expIMulOp
  rw [R.calculus_imageMeasure 1 _ _ _ hφ]
  rfl
variable {T : ℝ≥0 → ℋ →L[ℂ] ℋ} {U : SpaceVec → ℋ →L[ℂ] ℋ}
  (E : SpectralMeasureOn posEnergyBorel ℋ) (R : E.extend.CalculusLaws)
theorem marginal_zero_isConcentratedOn :
    (marginal E.extend 0).IsConcentratedOn nonnegReals :=
  extend_eq_zero_of_disjoint E ⟨coordProj 0 ⁻¹' nonnegReals.1ᶜ,
    measurable_coordProj 0 nonnegReals.2.compl⟩ fun _ hy hY => hy hY
include R in
theorem heatSemigroup_marginal_zero (hU : U 0 = 1) (hE : IsHeatShiftMeasure T U E) (t : ℝ≥0) :
    (marginal E.extend 0).expNegMulOp t = ofBounded (T t) := by
  have h := hE t 0
  rw [hU, mul_one] at h
  rw [h]
  have hφ : Measurable fun x : nonnegReals.1 =>
      Complex.exp (-(t : ℂ) * ((x.1 0 : ℝ) : ℂ)) := by
    have h₀ : Measurable fun x : nonnegReals.1 => x.1 0 :=
      (measurable_pi_apply 0).comp measurable_subtype_coe
    exact Complex.measurable_exp.comp (measurable_const.mul (Complex.measurable_ofReal.comp h₀))
  have hm := measurable_extendByZero nonnegReals hφ
  unfold ProjectionMeasure.expNegMulOp ProjectionMeasure.functionalCalculusOn
  rw [R.calculus_imageMeasure 1 _ _ _ hm]
  refine spectralIntegral_congr_on E R (hm.comp (measurable_coordProj 0))
    (measurable_heatPhase t 0) fun y hy => ?_
  have h₁ := extendByZero_apply_of_mem nonnegReals
    (fun x : nonnegReals.1 => Complex.exp (-(t : ℂ) * ((x.1 0 : ℝ) : ℂ)))
    ⟨coordProj 0 y, hy⟩
  simp only at h₁
  rw [Function.comp_apply, h₁]
  simp [heatPhase, coordProj, spaceDot, SeparatedTupleFunctionals.dotProd]
include R in
theorem shift_eq_boundedIntegralOp (hT : T 0 = 1) (hE : IsHeatShiftMeasure T U E) (a : SpaceVec) :
    U a = E.extend.boundedCalculus (heatPhase 0 a) := by
  have h := hE 0 a
  rw [hT, one_mul, show E.extend.functionalCalculus (heatPhase 0 a) = _ from
    R.isBoundedCalculusOf _ (measurable_heatPhase 0 a) (isBoundedComplexFn_heatPhase_zero a)] at h
  exact eq_of_ofBounded_eq h
include R in
theorem compBounded_unitaryGroup_marginal_zero (hT : T 0 = 1) (hE : IsHeatShiftMeasure T U E)
    (τ : ℝ) (a : SpaceVec) :
    compBounded ((marginal E.extend 0).expIMulOp τ) (U a) =
      E.extend.functionalCalculus (unitaryPhase τ a) := by
  have h₁ : (marginal E.extend 0).expIMulOp τ =
      ofBounded (E.extend.boundedCalculus (energyPhase τ)) :=
    (unitaryGroup_marginal E.extend R 0 τ).trans
      (R.isBoundedCalculusOf _ (measurable_energyPhase τ) (isBoundedComplexFn_energyPhase τ))
  have hm : Measurable fun y => energyPhase τ y * heatPhase 0 a y :=
    (measurable_energyPhase τ).mul (measurable_heatPhase 0 a)
  have hb : IsBoundedComplexFn fun y => energyPhase τ y * heatPhase 0 a y := by
    simp only [energyPhase_mul_heatPhase_zero]
    refine ⟨1, fun y => ?_⟩
    show ‖unitaryPhase τ a y‖ ≤ 1
    rw [unitaryPhase, mul_comm]
    exact (Complex.norm_exp_ofReal_mul_I _).le
  rw [h₁, compBounded_ofBounded, shift_eq_boundedIntegralOp E R hT hE a,
    R.boundedCalculus_mul _ _ (measurable_energyPhase τ) (measurable_heatPhase 0 a)
      (isBoundedComplexFn_energyPhase τ) (isBoundedComplexFn_heatPhase_zero a)]
  have h₂ := (R.isBoundedCalculusOf _ hm hb)
  have h₃ : (fun y => energyPhase τ y * heatPhase 0 a y) = unitaryPhase τ a :=
    funext (energyPhase_mul_heatPhase_zero τ a)
  rw [h₃] at h₂ ⊢
  exact h₂.symm
include R in
theorem compBounded_heatSemigroup_marginal_zero (hU : U 0 = 1) (hE : IsHeatShiftMeasure T U E)
    (t : ℝ≥0) (a : SpaceVec) :
    compBounded ((marginal E.extend 0).expNegMulOp t) (U a) =
      E.extend.functionalCalculus (heatPhase t a) := by
  rw [heatSemigroup_marginal_zero E R hU hE t, compBounded_ofBounded]
  exact hE t a
theorem spaceDot_smul_basisVec (u : ℝ) (i : Fin 3) (y : Fin 4 → ℝ) :
    spaceDot (u • spatialBasisVec i) (spatialPart y) = u * y i.succ := by
  simp [spaceDot, SeparatedTupleFunctionals.dotProd, spatialBasisVec, spatialPart,
    Pi.single_apply]
include R in
theorem unitaryGroup_marginal_succ (hT : T 0 = 1) (hE : IsHeatShiftMeasure T U E) (i : Fin 3)
    (u : ℝ) :
    (marginal E.extend i.succ).expIMulOp u = ofBounded (U (u • spatialBasisVec i)) := by
  have h := hE 0 (u • spatialBasisVec i)
  rw [hT, one_mul] at h
  rw [h, unitaryGroup_marginal E.extend R]
  congr 1
  funext y
  simp only [heatPhase, spaceDot_smul_basisVec]
  simp
  ring_nf
include R in
theorem eq_extend_of_unitaryPhase (hG : GeneratorsAndFlows.GeneratorFlowTheorem)
    (hT : T 0 = 1) (hE : IsHeatShiftMeasure T U E)
    (E' : ProjectionMeasure 4 ℋ) (F' : ProjectionMeasure 1 ℋ)
    (hF' : HasSpectralResolution (E.extend.coordinateOp 0) F')
    (h' : ∀ τ a, compBounded (F'.expIMulOp τ) (U a) = E'.functionalCalculus (unitaryPhase τ a)) :
    E' = E.extend := by
  have hFF : F' = marginal E.extend 0 :=
    ((hG ℋ).1 (marginal E.extend 0)).2.2.1.eq_of_generator F' (by
      have h₁ : E.extend.coordinateOp 0 = F'.coordinateOp 0 := hF'
      have h₂ : E.extend.coordinateOp 0 = (marginal E.extend 0).coordinateOp 0 :=
        hasSpectralResolution_marginal E.extend R 0
      rw [← h₁, h₂])
  refine R.ext_of_fourier_or_boxes E' (Or.inl fun x => ?_)
  have hfun : (fun ξ : Fin 4 → ℝ => Complex.exp (Complex.I * ((∑ i, x i * ξ i : ℝ) : ℂ))) =
      unitaryPhase (x 0) (fun i => x i.succ) := by
    funext ξ
    rw [unitaryPhase, Fin.sum_univ_succ]
    rfl
  rw [hfun, ← h', hFF]
  exact compBounded_unitaryGroup_marginal_zero E R hT hE _ _
end Rules
section Marginals
variable {ℋ : Type} [NormedAddCommGroup ℋ] [InnerProductSpace ℂ ℋ] [CompleteSpace ℋ]
theorem stronglyCommute_of_eq_coordOp (hG : GeneratorsAndFlows.GeneratorFlowTheorem)
    (K : ProjectionMeasure 4 ℋ) (R : K.CalculusLaws) (A : Fin 4 → UnboundedOperator ℋ)
    (hA : ∀ r, A r = K.coordinateOp r) : StronglyCommute A := by
  have hsp : ∀ r (F : ProjectionMeasure 1 ℋ), HasSpectralResolution (A r) F →
      F = marginal K r := fun r F hF =>
    ((hG ℋ).1 (marginal K r)).2.2.1.eq_of_generator F (by
      have h₁ : A r = F.coordinateOp 0 := hF
      have h₂ : K.coordinateOp r = (marginal K r).coordinateOp 0 :=
        hasSpectralResolution_marginal K R r
      rw [← h₁, hA, h₂])
  refine ⟨fun r => ⟨marginal K r, ?_⟩, ?_⟩
  · rw [hA]
    exact hasSpectralResolution_marginal K R r
  · rintro i j - P Q ⟨F, hF, Δ, rfl⟩ ⟨F', hF', Δ', rfl⟩
    rw [hsp i F hF, hsp j F' hF']
    exact ((hG ℋ).2 4 K).marginals_commute i j Δ Δ'
theorem spectralMeasure_ext {n : ℕ} [NeZero n] {K K' : ProjectionMeasure n ℋ}
    (h : ∀ A, K A = K' A) : K = K' := by
  cases K
  cases K'
  congr
  exact funext h
def toHalfPlaneMeasure (M : ProjectionMeasure 2 ℋ) (hY : M energyMomentumRegion = 1) :
    SpectralMeasureOn energyMomentumRegion ℋ where
  toFun A := M ⟨A.1, A.2.1⟩
  isStarProjection _ := M.isStarProjection _
  map_empty := M.map_empty
  map_whole := hY
  map_inter A B := M.map_inter ⟨A.1, A.2.1⟩ ⟨B.1, B.2.1⟩
  tendsto_sum A hA ψ := M.tendsto_sum (fun r => ⟨(A r).1, (A r).2.1⟩) hA ψ
theorem extend_toHalfPlaneMeasure (M : ProjectionMeasure 2 ℋ) (hY : M energyMomentumRegion = 1) :
    (toHalfPlaneMeasure M hY).extend = M :=
  spectralMeasure_ext fun A => (M.map_inter A energyMomentumRegion).trans (by rw [hY, mul_one])
theorem extend_posEnergyBorel (E : SpectralMeasureOn posEnergyBorel ℋ) :
    E.extend posEnergyBorel = 1 := by
  rw [E.extend_apply]
  have h : SpectralMeasureOn.restrictSet posEnergyBorel posEnergyBorel =
      ⟨posEnergyBorel.1, posEnergyBorel.2, Subset.rfl⟩ :=
    Subtype.ext (inter_self _)
  rw [h, E.map_whole]
abbrev pairMarginal (K : ProjectionMeasure 4 ℋ) (i : Fin 3) : ProjectionMeasure 2 ℋ :=
  K.imageMeasure (energyMomentumProj i) (measurable_energyMomentumProj i)
theorem pairMarginal_energyMomentumRegion (E : SpectralMeasureOn posEnergyBorel ℋ) (i : Fin 3) :
    pairMarginal E.extend i energyMomentumRegion = 1 := by
  have h : (⟨energyMomentumProj i ⁻¹' energyMomentumRegion.1,
      measurable_energyMomentumProj i energyMomentumRegion.2⟩ : BorelSets 4) = posEnergyBorel :=
    Subtype.ext (by
      ext y
      show 0 ≤ energyMomentumProj i y 0 ↔ 0 ≤ y 0
      simp [energyMomentumProj])
  exact (congrArg E.extend.toFun h).trans (extend_posEnergyBorel E)
variable {T : ℝ≥0 → ℋ →L[ℂ] ℋ} {U : SpaceVec → ℋ →L[ℂ] ℋ}
def pairPhase (t : ℝ≥0) (u : ℝ) (y : energyMomentumRegion.1) : ℂ :=
  Complex.exp (((-(t : ℝ) * y.1 0 : ℝ) : ℂ) + Complex.I * ((u * y.1 1 : ℝ) : ℂ))
theorem measurable_pairPhase (t : ℝ≥0) (u : ℝ) : Measurable (pairPhase t u) := by
  have h₀ : Measurable fun y : energyMomentumRegion.1 => y.1 0 :=
    (measurable_pi_apply 0).comp measurable_subtype_coe
  have h₁ : Measurable fun y : energyMomentumRegion.1 => y.1 1 :=
    (measurable_pi_apply 1).comp measurable_subtype_coe
  exact Complex.measurable_exp.comp ((Complex.measurable_ofReal.comp (h₀.const_mul _)).add
    (measurable_const.mul (Complex.measurable_ofReal.comp (h₁.const_mul _))))
theorem spectralIntegralOn_pairMarginal (E : SpectralMeasureOn posEnergyBorel ℋ)
    (R : E.extend.CalculusLaws) (hE : IsHeatShiftMeasure T U E) (i : Fin 3) (t : ℝ≥0) (u : ℝ) :
    ofBounded (T t * U (u • spatialBasisVec i)) =
      (pairMarginal E.extend i).functionalCalculusOn energyMomentumRegion (pairPhase t u) := by
  have hm := measurable_extendByZero energyMomentumRegion (measurable_pairPhase t u)
  unfold ProjectionMeasure.functionalCalculusOn
  rw [R.calculus_imageMeasure 2 _ _ _ hm, hE t]
  refine spectralIntegral_congr_on E R (measurable_heatPhase t _)
    (hm.comp (measurable_energyMomentumProj i)) fun y hy => ?_
  have hy' : energyMomentumProj i y ∈ energyMomentumRegion.1 := by
    show 0 ≤ energyMomentumProj i y 0
    have hy₀ : 0 ≤ y 0 := hy
    simpa [energyMomentumProj] using hy₀
  have h₁ := extendByZero_apply_of_mem energyMomentumRegion (pairPhase t u)
    ⟨energyMomentumProj i y, hy'⟩
  simp only at h₁
  rw [Function.comp_apply, h₁, heatPhase, pairPhase, spaceDot_smul_basisVec]
  simp [energyMomentumProj]
theorem isConcentratedOn_forwardCone (hS : SpectralSupport.ConcentratedOnSupportTheorem)
    (K : ProjectionMeasure 4 ℋ) (hc : ∀ i : Fin 3, ∀ hm,
      K ⟨energyMomentumProj i ⁻¹' QuantumSystem.forwardConeᶜ, hm⟩ = 0) :
    K.IsConcentratedOn forwardCone := by
  have hclosed : IsClosed QuantumSystem.forwardCone := by
    have h₀ : Continuous fun y : Fin 2 → ℝ => y 0 := continuous_apply 0
    have h₁ : Continuous fun y : Fin 2 → ℝ => |y 1| := (continuous_apply 1).abs
    exact isClosed_le h₁ h₀
  have hmeas : ∀ i : Fin 3, MeasurableSet (energyMomentumProj i ⁻¹' QuantumSystem.forwardConeᶜ) :=
    fun i => measurable_energyMomentumProj i hclosed.isOpen_compl.measurableSet
  have hU := (hS 4 ℋ K).vanishesOn_iUnion (Fin 3)
    (fun i => ⟨energyMomentumProj i ⁻¹' QuantumSystem.forwardConeᶜ, hmeas i⟩)
    (fun i => hc i (hmeas i))
  have hset : (⟨forwardCone.1ᶜ, forwardCone.2.compl⟩ : BorelSets 4) =
      ⟨⋃ i : Fin 3, energyMomentumProj i ⁻¹' QuantumSystem.forwardConeᶜ,
        MeasurableSet.iUnion hmeas⟩ :=
    Subtype.ext (by
      ext y
      simp [forwardCone, energyMomentumProj, QuantumSystem.forwardCone])
  unfold ProjectionMeasure.IsConcentratedOn ProjectionMeasure.VanishesOn
  rw [hset]
  exact hU
end Marginals
section Measure
variable (σ : TupleFunctional) (h : IsPosSemidef (reflectionForm σ))
theorem exists_isHeatShiftMeasure (hR : SpectralIntegralLawsHold)
    (hJ : SemigroupRepresentation.JointSpectralTheoremForPair)
    (hS : Reconstruction.SemigroupProperties σ h)
    (hP : Reconstruction.SpatialProperties σ h) :
    ∃ E, IsHeatShiftMeasure (timeShift σ h) (spaceShift σ h) E := by
  obtain ⟨-, -, hcT, hSemi, hsa, -⟩ := hS
  obtain ⟨-, -, hcU, hRep, hcomm, -⟩ := hP
  have hpair : SemigroupRepresentation.IsCommutingSemigroupRep
      (timeShift σ h) (spaceShift σ h) :=
    { isContractionSemigroup :=
        { semigroup := hSemi
          selfAdjoint := fun t => (hsa t).1
          contraction := fun t => (hsa t).2.1
          tendsto_zero := fun ψ => by
            have ht := (hcT ψ).tendsto 0
            rw [hSemi.1] at ht
            exact ht.mono_left nhdsWithin_le_nhds }
      isUnitaryRep := hRep
      tendstoStrongly_zero := fun ψ => by
        have ht := (hcU ψ).tendsto 0
        rw [hRep.2.1] at ht
        exact ht
      commute := fun a t => hcomm a t }
  have hj := ((hJ (PhysicalSpace σ h) 3 (by norm_num)).1 _ _ hpair).2.2.1
  exact ⟨toSpectralMeasureOn (SemigroupRepresentation.jointSpectralMeasure
    (timeShift σ h) (spaceShift σ h)), isHeatShiftMeasure_toSpectralMeasureOn _ (hR 4 _ _) hj⟩
open YangMills.Construction.ReflectionPositivity.LimitReconstruction (IsShiftGenerator
  IsHeatGenerator TimeSemigroupProperties SpaceShiftProperties)
theorem measure_claims (hR : SpectralIntegralLawsHold)
    (hG : GeneratorsAndFlows.GeneratorFlowTheorem)
    (hSup : SpectralSupport.ConcentratedOnSupportTheorem)
    (E : SpectralMeasureOn posEnergyBorel (PhysicalSpace σ h))
    (hE : IsHeatShiftMeasure (timeShift σ h) (spaceShift σ h) E)
    (hSH : TimeSemigroupProperties σ h) (hTM : SpaceShiftProperties σ h)
    (hPair : ∀ i, ShiftSpectralMeasure.ExistsUniqueShiftMeasure σ h i)
    (hCone : ∀ i, PairMeasureOperators.HamiltonianDominatesMomentum σ h i) :
    MeasureClaim σ h ∧ OperatorClaim σ h ∧ SupportClaim σ h ∧ MarginalClaim σ h ∧
      ∃ F : ProjectionMeasure 1 (PhysicalSpace σ h),
        HasSpectralResolution (pairHamiltonian σ h) F ∧ F.IsConcentratedOn nonnegReals ∧
          ∀ t : ℝ≥0, F.expNegMulOp t = ofBounded (timeShift σ h t) := by
  have R : E.extend.CalculusLaws := hR 4 _ _
  obtain ⟨-, -, -, hSemi, -, -, hHuniq, -⟩ := hSH
  obtain ⟨-, -, -, hRep, -, -, hMom⟩ := hTM
  have hT0 : timeShift σ h 0 = 1 := hSemi.map_zero
  have hU0 : spaceShift σ h 0 = 1 := hRep.map_zero
  have hCar := marginal_zero_isConcentratedOn E
  have hExpH := heatSemigroup_marginal_zero E R hU0 hE
  have hSpH₀ := hasSpectralResolution_marginal E.extend R 0
  have hH : E.extend.coordinateOp 0 = pairHamiltonian σ h :=
    hHuniq _ ⟨_, hSpH₀, hCar, fun t => (hExpH t).symm⟩
  have hSpH : HasSpectralResolution (pairHamiltonian σ h) (marginal E.extend 0) := by
    rw [← hH]
    exact hSpH₀
  have hP : ∀ i : Fin 3, E.extend.coordinateOp i.succ = pairMomentum σ h i := fun i =>
    (hMom i).2.1 _ ⟨_, hasSpectralResolution_marginal E.extend R i.succ, fun u =>
      (unitaryGroup_marginal_succ E R hT0 hE i u).symm⟩
  have hK : IsJointGroupMeasure σ h E.extend :=
    ⟨_, hSpH, compBounded_unitaryGroup_marginal_zero E R hT0 hE⟩
  have huniq : ∀ E', IsJointGroupMeasure σ h E' → E' = E.extend := by
    rintro E' ⟨F', hF', h'⟩
    exact eq_extend_of_unitaryPhase E R hG hT0 hE E' F' (by rw [hH]; exact hF') h'
  have hEm : jointMeasure σ h = E.extend :=
    huniq _ (Classical.epsilon_spec (p := IsJointGroupMeasure σ h) ⟨_, hK⟩)
  have hfour : ∀ r, energyMomentumOps σ h r = E.extend.coordinateOp r := fun r => by
    refine Fin.cases ?_ (fun i => ?_) r
    · exact hH.symm
    · exact (hP i).symm
  have hpairEq : ∀ i, toHalfPlaneMeasure (pairMarginal E.extend i)
      (pairMarginal_energyMomentumRegion E i) = shiftSpectralMeasure σ h i := fun i =>
    (hPair i).1.unique (fun t u => spectralIntegralOn_pairMarginal E R hE i t u
      |>.trans (by
        rw [extend_toHalfPlaneMeasure]
        rfl)) (hPair i).2
  have hmarg : ∀ (i : Fin 3) (B : BorelSets 2),
      E.extend.pushforward (energyMomentumProj i) (measurable_energyMomentumProj i) B =
        (shiftSpectralMeasure σ h i).extend B := fun i B => by
    rw [← hpairEq i, extend_toHalfPlaneMeasure]
    rfl
  refine ⟨⟨⟨_, hK, huniq⟩, by rw [hEm]; exact hK⟩, ?_, ?_, ?_, ⟨_, hSpH, hCar, hExpH⟩⟩
  · rw [OperatorClaim, hEm]
    refine ⟨hH.symm, fun i => (hP i).symm,
      stronglyCommute_of_eq_coordOp hG E.extend R _ hfour, hfour⟩
  · rw [SupportClaim, hEm]
    exact ⟨E.extend_isConcentratedOn, _, hSpH, hCar,
      compBounded_heatSemigroup_marginal_zero E R hU0 hE⟩
  · rw [MarginalClaim, hEm]
    refine ⟨hmarg, isConcentratedOn_forwardCone hSup E.extend fun i hm => ?_⟩
    have hclosed : IsClosed QuantumSystem.forwardCone :=
      isClosed_le (continuous_apply 1).abs (continuous_apply 0)
    have hz := ((hSup 2 _ (shiftSpectralMeasure σ h i).extend).support_subset_iff _
      hclosed).1 (hCone i)
    rw [← hmarg i] at hz
    exact hz
end Measure
section Action
def lowerHalfSpace : Set AmbientSpace := {x | TimeAxis.timeComponent x < 0}
theorem isOpen_upperHalfSpace : IsOpen TimeAxis.upperHalfSpace :=
  isOpen_lt continuous_const (continuous_apply TimeAxis.timeIdx)
theorem isOpen_lowerHalfSpace : IsOpen lowerHalfSpace := by apply _root_.YangMills.Construction.ReflectionPositivity.FormProperties.isOpen_lowerHalfSpace <;> assumption
theorem disjoint_lowerHalfSpace_upperHalfSpace :
    Disjoint lowerHalfSpace TimeAxis.upperHalfSpace := by apply _root_.YangMills.Construction.ReflectionPositivity.FormProperties.disjoint_lowerHalfSpace_upperHalfSpace <;> assumption
theorem isEuclidIsometry_timeReflection : IsEuclidIsometry TimeAxis.timeReflection := by apply _root_.YangMills.Construction.ReflectionPositivity.FormProperties.isEuclidIsometry_timeReflection <;> assumption
theorem isEuclidIsometry_of_mem_hyperoctahedral {g : AmbientSpace ≃ₗ[ℝ] AmbientSpace}
    (hg : g ∈ hyperoctahedralLinearGroup) : IsEuclidIsometry g := by apply _root_.YangMills.Construction.ReflectionPositivity.LimitSymmetryArgument.isEuclidIsometry_of_mem <;> assumption
theorem timeReflection_mkPoint (a : SpaceVec) (t : ℝ) :
    TimeAxis.timeReflection (mkPoint a t) = mkPoint a (-t) := by apply _root_.YangMills.Construction.Continuum.AxisPreservingSymmetries.timeReflection_mkPoint <;> assumption
theorem timeReflection_comp_timeExtension (w : SpaceVec ≃ₗ[ℝ] SpaceVec) :
    TimeAxis.timeReflection ∘ ⇑(timeExtension w) = ⇑(timeExtension w) ∘ TimeAxis.timeReflection := by
  funext x
  rw [← mkPoint_spacePart_timeComponent x]
  simp only [Function.comp_apply, timeExtension_mkPoint, timeReflection_mkPoint]
theorem timeExtension_comp_translate (w : SpaceVec ≃ₗ[ℝ] SpaceVec) (v : AmbientSpace) :
    ⇑(timeExtension w) ∘ SeparatedTuples.translate v =
      SeparatedTuples.translate (timeExtension w v) ∘ ⇑(timeExtension w) := by
  funext x
  simp [SeparatedTuples.translate]
theorem timeComponent_timeExtension (w : SpaceVec ≃ₗ[ℝ] SpaceVec) (x : AmbientSpace) :
    TimeAxis.timeComponent (timeExtension w x) = TimeAxis.timeComponent x := by
  conv_lhs => rw [← mkPoint_spacePart_timeComponent x]
  rw [timeExtension_mkPoint, timeComponent_mkPoint]
theorem embedSpatial_eq_mkPoint (a : SpaceVec) : embedSpatial a = mkPoint a 0 := by
  refine funext fun μ => Fin.lastCases ?_ (fun i => ?_) μ
  · rw [mkPoint_last]
    rfl
  · rw [mkPoint_castSucc]
    fin_cases i <;> rfl
theorem spanExtension_basisVec (σ : TupleFunctional) (X : SepTuple) :
    σ.spanExtension (basisVec X) = (σ X : ℂ) :=
  linearExtend_basisVec _ X
theorem pushSpan_basisVec (r : AmbientSpace → AmbientSpace) (X : SepTuple) :
    pushSpan r (basisVec X) = basisVec (push r X) :=
  linearExtend_basisVec _ X
theorem conjugation_mem_spanIn {O : Set AmbientSpace} {G : FormalSpan} (hG : G ∈ spanIn O) :
    SeparatedTuples.conjugation G ∈ spanIn O := by apply _root_.YangMills.Construction.ReflectionPositivity.FormProperties.conjugation_mem_spanIn <;> assumption
theorem spanExtension_pushSpan {σ : TupleFunctional} {r : AmbientSpace → AmbientSpace}
    (hI : σ.IsInvariant r) (G : FormalSpan) :
    σ.spanExtension (pushSpan r G) = σ.spanExtension G := by
  induction G using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => simp only [map_add, hf, hg]
  | single X c =>
    have h : Finsupp.single X c = c • basisVec X := by simp [basisVec]
    rw [h, map_smul, map_smul, map_smul, pushSpan_basisVec, spanExtension_basisVec,
      spanExtension_basisVec, hI X]
variable (hAct : BasicFacts.PushSpanProperties)
include hAct
theorem pushSpan_mem_spanIn (r : AmbientSpace → AmbientSpace) (hr : IsEuclidIsometry r)
    {O O' : Set AmbientSpace} (hO : IsOpen O) (hOO : r '' O ⊆ O') {G : FormalSpan}
    (hG : G ∈ spanIn O) : pushSpan r G ∈ spanIn O' := by apply _root_.YangMills.Construction.ReflectionPositivity.FormProperties.pushSpan_mem_of_image_subset <;> assumption
theorem reflectConj_mem_lowerHalfSpace (F : PositiveSpan) :
    reflectConj F ∈ spanIn lowerHalfSpace := by apply _root_.YangMills.Construction.ReflectionPositivity.FormProperties.reflectConj_mem_lowerHalfSpace <;> assumption
theorem pushSpan_translate_mem {v : AmbientSpace} (hv : 0 ≤ TimeAxis.timeComponent v)
    {G : FormalSpan} (hG : G ∈ spanIn TimeAxis.upperHalfSpace) :
    pushSpan (translate v) G ∈ spanIn TimeAxis.upperHalfSpace := by apply _root_.YangMills.Construction.ReflectionPositivity.FormProperties.pushSpan_translate_mem <;> assumption
theorem pushSpan_timeExtension_mem (w : SpaceVec ≃ₗ[ℝ] SpaceVec)
    (hw : IsEuclidIsometry (timeExtension w)) {G : FormalSpan}
    (hG : G ∈ spanIn TimeAxis.upperHalfSpace) :
    pushSpan (timeExtension w) G ∈ spanIn TimeAxis.upperHalfSpace := by
  refine pushSpan_mem_spanIn hAct _ hw isOpen_upperHalfSpace ?_ hG
  rintro _ ⟨x, hx, rfl⟩
  show 0 < TimeAxis.timeComponent (timeExtension w x)
  rw [timeComponent_timeExtension]
  exact hx
theorem timeReflection_conjugation_pushSpan {r : AmbientSpace → AmbientSpace}
    (hr : IsEuclidIsometry r)
    (hθ : TimeAxis.timeReflection ∘ r = r ∘ TimeAxis.timeReflection) (G : FormalSpan) :
    pushSpan TimeAxis.timeReflection (SeparatedTuples.conjugation (pushSpan r G)) =
      pushSpan r (pushSpan TimeAxis.timeReflection (SeparatedTuples.conjugation G)) := by
  have h₁ := isEuclidIsometry_timeReflection
  rw [(hAct _ _ hr hr 0 0 G).2.2.2.1, ← (hAct _ _ h₁ hr 0 0 _).1, hθ, (hAct _ _ hr h₁ 0 0 _).1]
theorem pushSpan_timeExtension_translate (w : SpaceVec ≃ₗ[ℝ] SpaceVec)
    (hw : IsEuclidIsometry (timeExtension w)) (v : AmbientSpace) (G : FormalSpan) :
    pushSpan (timeExtension w) (pushSpan (translate v) G) =
      pushSpan (translate (timeExtension w v)) (pushSpan (timeExtension w) G) := by
  have hτ := isEuclidIsometry_translate v
  have hτ' := isEuclidIsometry_translate (timeExtension w v)
  rw [← (hAct _ _ hw hτ 0 0 G).1, timeExtension_comp_translate, (hAct _ _ hτ' hw 0 0 G).1]
theorem pushSpan_timeExtension_symm (w : SpaceVec ≃ₗ[ℝ] SpaceVec)
    (hw : IsEuclidIsometry (timeExtension w)) (hw' : IsEuclidIsometry (timeExtension w.symm))
    (G : FormalSpan) :
    pushSpan (timeExtension w) (pushSpan (timeExtension w.symm) G) = G := by
  have hτ := isEuclidIsometry_translate 0
  have hid : ⇑(timeExtension w) ∘ ⇑(timeExtension w.symm) = SeparatedTuples.translate 0 := by
    funext x
    have hs : timeExtension w.symm x = (timeExtension w).symm x := rfl
    simp [SeparatedTuples.translate, hs]
  rw [← (hAct _ _ hw hw' 0 0 G).1, hid]
  exact (hAct _ _ hτ hτ 0 0 G).2.2.1
end Action
section Unitary
variable (σ : TupleFunctional) (h : IsPosSemidef (reflectionForm σ))
def restrictPos (A : FormalSpan →ₗ[ℂ] FormalSpan)
    (hm : ∀ G ∈ spanIn TimeAxis.upperHalfSpace, A G ∈ spanIn TimeAxis.upperHalfSpace) :
    PositiveSpan →ₗ[ℂ] PositiveSpan :=
  A.restrict hm
theorem spanClass_val (F : PositiveSpan) :
    spanClass σ h F.1 = posClass σ h F := by
  unfold spanClass
  rw [dif_pos F.2]
variable {σ h}
theorem spanClass_of_mem {G : FormalSpan} (hG : G ∈ spanIn TimeAxis.upperHalfSpace) :
    spanClass σ h G = posClass σ h ⟨G, hG⟩ :=
  spanClass_val σ h ⟨G, hG⟩
variable (hC : HilbertSpaceFacts.CompletionProperties)
  (hId : HilbertSpaceFacts.DenseSubsetIdentities)
include hC in
theorem inner_posClass (F F' : PositiveSpan) :
    ⟪posClass σ h F, posClass σ h F'⟫_ℂ = reflectionForm σ F F' :=
  (hC _ (reflectionForm σ) h).2.1 F F'
include hC in
theorem dense_range_posClass : Dense (Set.range (posClass σ h)) := by
  have hd := (hC _ (reflectionForm σ) h).2.2.2.1
  rwa [LinearMap.coe_range] at hd
include hC hId in
theorem ext_on_posClass {A B : PhysicalSpace σ h →L[ℂ] PhysicalSpace σ h}
    (hAB : ∀ F, A (posClass σ h F) = B (posClass σ h F)) : A = B := by
  refine (hId _ _ (dense_range_posClass hC)).2.1 A B ?_
  rintro _ ⟨F, rfl⟩
  exact hAB F
include hC hId in
theorem exists_isometric_extension (hO : HilbertSpaceFacts.CompletionOperatorExtension)
    (A : FormalSpan →ₗ[ℂ] FormalSpan)
    (hm : ∀ G ∈ spanIn TimeAxis.upperHalfSpace, A G ∈ spanIn TimeAxis.upperHalfSpace)
    (hform : ∀ F F', reflectionForm σ (restrictPos A hm F) (restrictPos A hm F') =
      reflectionForm σ F F') :
    ∃ B : PhysicalSpace σ h →L[ℂ] PhysicalSpace σ h,
      (∀ F : PositiveSpan, B (posClass σ h F) = spanClass σ h (A F.1)) ∧
        ∀ φ ψ, ⟪B φ, B ψ⟫_ℂ = ⟪φ, ψ⟫_ℂ := by
  obtain ⟨-, B, hB, -, -⟩ := hO _ (reflectionForm σ) h 1 (restrictPos A hm) zero_le_one fun F => by
    rw [one_mul]
    exact le_of_eq (congrArg (fun z : ℂ => Real.sqrt z.re) (hform F F))
  have hB' : ∀ F : PositiveSpan, B (posClass σ h F) = spanClass σ h (A F.1) := fun F => by
    rw [spanClass_of_mem (hm F.1 F.2)]
    exact hB F
  refine ⟨B, hB', fun φ ψ => ?_⟩
  have hall := (hId _ _ (dense_range_posClass hC)).1 B B 1 1 (by
    rintro _ ⟨F, rfl⟩ _ ⟨F', rfl⟩
    rw [hB, hB, inner_posClass hC, hform]
    exact (inner_posClass hC F F').symm) φ ψ
  exact hall
include hC hId in
theorem exists_unitary_extension {A A' : FormalSpan →ₗ[ℂ] FormalSpan}
    (hm : ∀ G ∈ spanIn TimeAxis.upperHalfSpace, A G ∈ spanIn TimeAxis.upperHalfSpace)
    (hm' : ∀ G ∈ spanIn TimeAxis.upperHalfSpace, A' G ∈ spanIn TimeAxis.upperHalfSpace)
    (hAA' : ∀ G, A (A' G) = G) (hA'A : ∀ G, A' (A G) = G)
    {B B' : PhysicalSpace σ h →L[ℂ] PhysicalSpace σ h}
    (hB : ∀ F : PositiveSpan, B (posClass σ h F) = spanClass σ h (A F.1))
    (hB' : ∀ F : PositiveSpan, B' (posClass σ h F) = spanClass σ h (A' F.1))
    (hi : ∀ φ ψ, ⟪B φ, B ψ⟫_ℂ = ⟪φ, ψ⟫_ℂ) :
    ∃ V : PhysicalSpace σ h ≃ₗᵢ[ℂ] PhysicalSpace σ h, ∀ ψ, V ψ = B ψ := by
  have h₁ : B * B' = 1 := ext_on_posClass hC hId fun F => by
    show B (B' (posClass σ h F)) = posClass σ h F
    rw [hB', spanClass_of_mem (hm' F.1 F.2), hB]
    simp only
    rw [hAA']
    exact spanClass_val σ h F
  have h₂ : B' * B = 1 := ext_on_posClass hC hId fun F => by
    show B' (B (posClass σ h F)) = posClass σ h F
    rw [hB, spanClass_of_mem (hm F.1 F.2), hB']
    simp only
    rw [hA'A]
    exact spanClass_val σ h F
  refine ⟨⟨LinearEquiv.ofLinearMap (B : PhysicalSpace σ h →ₗ[ℂ] PhysicalSpace σ h)
    (B' : PhysicalSpace σ h →ₗ[ℂ] PhysicalSpace σ h)
    (LinearMap.ext fun ψ => congrArg (fun C : PhysicalSpace σ h →L[ℂ] PhysicalSpace σ h => C ψ) h₁)
    (LinearMap.ext fun ψ => congrArg (fun C : PhysicalSpace σ h →L[ℂ] PhysicalSpace σ h => C ψ) h₂),
    fun ψ => ?_⟩, fun ψ => rfl⟩
  have hn : ‖B ψ‖ ^ 2 = ‖ψ‖ ^ 2 := by
    rw [@norm_sq_eq_re_inner ℂ, @norm_sq_eq_re_inner ℂ _ _ _ _ ψ, hi]
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 hn
include hC hId in
theorem intertwine_of_relation {A S S' : FormalSpan →ₗ[ℂ] FormalSpan}
    (hmA : ∀ G ∈ spanIn TimeAxis.upperHalfSpace, A G ∈ spanIn TimeAxis.upperHalfSpace)
    (hmS : ∀ G ∈ spanIn TimeAxis.upperHalfSpace, S G ∈ spanIn TimeAxis.upperHalfSpace)
    {V B C : PhysicalSpace σ h →L[ℂ] PhysicalSpace σ h}
    (hV : ∀ F : PositiveSpan, V (posClass σ h F) = spanClass σ h (A F.1))
    (hB : ∀ F : PositiveSpan, B (posClass σ h F) = spanClass σ h (S F.1))
    (hCl : ∀ F : PositiveSpan, C (posClass σ h F) = spanClass σ h (S' F.1))
    (hrel : ∀ G, A (S G) = S' (A G)) : V * B = C * V :=
  ext_on_posClass hC hId fun F => by
    show V (B (posClass σ h F)) = C (V (posClass σ h F))
    rw [hB, spanClass_of_mem (hmS F.1 F.2), hV, hV, spanClass_of_mem (hmA F.1 F.2), hCl]
    simp only
    rw [hrel]
end Unitary
section Octahedral
variable (σ : TupleFunctional) (h : IsPosSemidef (reflectionForm σ))
open YangMills.Construction.ReflectionPositivity.Reconstruction (IsSpaceShiftFamily IsTimeShiftFamily
  posTupleVec)
theorem unitary_claims (hG : GeneratorsAndFlows.GeneratorFlowTheorem)
    (hAct : BasicFacts.PushSpanProperties)
    (hC : HilbertSpaceFacts.CompletionProperties)
    (hO : HilbertSpaceFacts.CompletionOperatorExtension)
    (hId : HilbertSpaceFacts.DenseSubsetIdentities)
    (hI : ∀ w ∈ octahedralGroup3, σ.IsInvariant (timeExtension w))
    (hCub : ∀ w ∈ octahedralGroup3, timeExtension w ∈ hyperoctahedralLinearGroup ∧
      timeExtension w timeBasisVector = timeBasisVector)
    (hT : IsTimeShiftFamily σ h (timeShift σ h))
    (hS : IsSpaceShiftFamily σ h (spaceShift σ h))
    (F : ProjectionMeasure 1 (PhysicalSpace σ h))
    (hF : HasSpectralResolution (pairHamiltonian σ h) F) (hFc : F.IsConcentratedOn nonnegReals)
    (hFe : ∀ t : ℝ≥0, F.expNegMulOp t = ofBounded (timeShift σ h t))
    {w : SpaceVec ≃ₗ[ℝ] SpaceVec} (hw : w ∈ octahedralGroup3) :
    UnitaryClaim σ h w ∧ IntertwiningClaim σ h w := by
  have hiso : ∀ v ∈ octahedralGroup3, IsEuclidIsometry (timeExtension v) := fun v hv =>
    isEuclidIsometry_of_mem_hyperoctahedral (hCub v hv).1
  have hmem : ∀ v (hv : v ∈ octahedralGroup3), ∀ G ∈ spanIn TimeAxis.upperHalfSpace,
      pushSpan (timeExtension v) G ∈ spanIn TimeAxis.upperHalfSpace :=
    fun v hv G hG => pushSpan_timeExtension_mem hAct v (hiso v hv) hG
  have hform : ∀ v (hv : v ∈ octahedralGroup3) (Fa Fb : PositiveSpan),
      reflectionForm σ (restrictPos (pushSpan (timeExtension v)) (hmem v hv) Fa)
        (restrictPos (pushSpan (timeExtension v)) (hmem v hv) Fb) = reflectionForm σ Fa Fb := by
    intro v hv Fa Fb
    have hr : reflectConj (restrictPos (pushSpan (timeExtension v)) (hmem v hv) Fa) =
        pushSpan (timeExtension v) (reflectConj Fa) :=
      timeReflection_conjugation_pushSpan hAct (hiso v hv)
        (timeReflection_comp_timeExtension v) Fa.1
    unfold reflectionForm
    rw [hr]
    show σ.spanExtension (formalMul (pushSpan (timeExtension v) (reflectConj Fa))
      (pushSpan (timeExtension v) Fb.1)) = _
    rw [(hAct _ _ (hiso v hv) (hiso v hv) 0 0 0).2.2.2.2.2 lowerHalfSpace TimeAxis.upperHalfSpace
      isOpen_lowerHalfSpace isOpen_upperHalfSpace disjoint_lowerHalfSpace_upperHalfSpace _
      (reflectConj_mem_lowerHalfSpace hAct Fa) _ Fb.2, spanExtension_pushSpan (hI v hv)]
  have hw' : w.symm ∈ octahedralGroup3 := inv_mem hw
  obtain ⟨B, hB, hi⟩ := exists_isometric_extension hC hId hO _ (hmem w hw) (hform w hw)
  obtain ⟨B', hB', -⟩ := exists_isometric_extension hC hId hO _ (hmem _ hw') (hform _ hw')
  obtain ⟨V, hV⟩ := exists_unitary_extension hC hId (hmem w hw) (hmem _ hw')
    (pushSpan_timeExtension_symm hAct w (hiso w hw) (hiso _ hw'))
    (pushSpan_timeExtension_symm hAct w.symm (hiso _ hw') (hiso w hw)) hB hB' hi
  have hVu : IsOctahedralUnitary σ h w V := fun Z => by
    rw [hV]
    exact hB Z
  have hunique : ∀ V', IsOctahedralUnitary σ h w V' → V' = V := fun V' hV' => by
    have hb : (V'.toContinuousLinearEquiv : PhysicalSpace σ h →L[ℂ] PhysicalSpace σ h) =
        V.toContinuousLinearEquiv := ext_on_posClass hC hId fun Z =>
      (hV' Z).trans (hVu Z).symm
    exact LinearIsometryEquiv.ext fun ψ =>
      congrArg (fun C : PhysicalSpace σ h →L[ℂ] PhysicalSpace σ h => C ψ) hb
  have hcu : octahedralUnitary σ h w = V :=
    hunique _ (Classical.epsilon_spec (p := IsOctahedralUnitary σ h w) ⟨V, hVu⟩)
  have hVb : ∀ Z : PositiveSpan, octahedralUnitaryCLM σ h w (posClass σ h Z) =
      spanClass σ h (pushSpan (timeExtension w) Z.1) := fun Z => by
    show octahedralUnitary σ h w (posClass σ h Z) = _
    rw [hcu]
    exact hVu Z
  have htime : ∀ t : ℝ≥0, 0 ≤ TimeAxis.timeComponent ((t : ℝ) • timeBasisVec) := fun t => by
    simp [TimeAxis.timeComponent, timeBasisVec, PeriodicLattice.coordVec]
  have hspace : ∀ a : SpaceVec, 0 ≤ TimeAxis.timeComponent (embedSpatial a) := fun a => by
    rw [embedSpatial_eq_mkPoint, timeComponent_mkPoint]
  have hVT : ∀ t, octahedralUnitaryCLM σ h w * timeShift σ h t =
      timeShift σ h t * octahedralUnitaryCLM σ h w := fun t =>
    intertwine_of_relation hC hId (hmem w hw)
      (fun G hG => pushSpan_translate_mem hAct (htime t) hG) hVb (hT t) (hT t)
      fun G => by
        have hfix : timeExtension w ((t : ℝ) • timeBasisVec) = (t : ℝ) • timeBasisVec := by
          rw [map_smul]
          exact congrArg (fun x : AmbientSpace => (t : ℝ) • x) (hCub w hw).2
        have hrel := pushSpan_timeExtension_translate hAct w (hiso w hw) ((t : ℝ) • timeBasisVec) G
        rwa [hfix] at hrel
  have hVU : ∀ a, octahedralUnitaryCLM σ h w * spaceShift σ h a =
      spaceShift σ h (w a) * octahedralUnitaryCLM σ h w := fun a =>
    intertwine_of_relation hC hId (hmem w hw)
      (fun G hG => pushSpan_translate_mem hAct (hspace a) hG) hVb (hS a)
      (hS (w a)) fun G => by
        have hfix : timeExtension w (embedSpatial a) = embedSpatial (w a) := by
          rw [embedSpatial_eq_mkPoint, timeExtension_mkPoint, embedSpatial_eq_mkPoint]
        have hrel := pushSpan_timeExtension_translate hAct w (hiso w hw) (embedSpatial a) G
        rwa [hfix] at hrel
  have hGen := (hG (PhysicalSpace σ h)).1 F
  have hSF := hGen.2.1 hFc
  have hsg : ∀ t, F.contractionFlow t = timeShift σ h t := fun t =>
    eq_of_ofBounded_eq ((hSF.expNegMulOp_eq t).symm.trans (hFe t))
  have hcomm : F.CommutesWithFlows (octahedralUnitaryCLM σ h w) :=
    Or.inr ⟨hFc, fun t _ _ => by
      rw [hsg]
      exact hVT t⟩
  have hconj := (hGen.2.2.2 _ hcomm).2 (octahedralUnitary σ h w) fun ψ => rfl
  have hvac : octahedralUnitary σ h w (vacuum σ h) = vacuum σ h := by
    have h₁ := hVb (posTupleVec ⟨SepTuple.nil, nil_mem_supportedIn _⟩)
    have h₂ : pushSpan (timeExtension w)
        (posTupleVec ⟨SepTuple.nil, nil_mem_supportedIn _⟩).1 =
        (posTupleVec ⟨SepTuple.nil, nil_mem_supportedIn _⟩).1 := by
      show pushSpan _ (basisVec SepTuple.nil) = basisVec SepTuple.nil
      rw [pushSpan_basisVec, push_nil]
    rw [h₂, spanClass_val] at h₁
    exact h₁
  have hinv : octahedralUnitaryCLM σ h w * octahedralUnitaryInvCLM σ h w = 1 := by
    ext ψ
    show octahedralUnitary σ h w ((octahedralUnitary σ h w).symm ψ) = ψ
    simp
  refine ⟨⟨⟨V, hVu, hunique⟩, by rw [hcu]; exact hVu⟩, hvac, ⟨F, hF, hFc, fun t => ?_⟩, ?_,
    fun a => ?_⟩
  · rw [hFe t, boundedComp_ofBounded, compBounded_ofBounded, hVT t]
  · rw [show pairHamiltonian σ h = F.coordinateOp 0 from hF]
    exact hconj
  · rw [hVU a, mul_assoc, hinv, mul_one]
end Octahedral
theorem complementsTheorem_holds (hHF : HilbertSpaceFacts.Facts) (hFacts : BasicFacts.MainFacts)
    (hR : SpectralIntegralLawsHold)
    (hG : GeneratorsAndFlows.GeneratorFlowTheorem)
    (hSup : SpectralSupport.ConcentratedOnSupportTheorem)
    (hJ : SemigroupRepresentation.JointSpectralTheoremForPair)
    (hRec : Reconstruction.ReconstructionTheorem)
    (hLim : LimitReconstruction.LimitReconstructionTheorem)
    (hPair : ShiftSpectralMeasure.ShiftSpectralMeasureTheorem)
    (hCone : LimitMomentumBound.MomentumBoundTheorem)
    (hFirst : LimitSymmetries.LimitHasSymmetries)
    (hCub : Continuum.AxisPreservingSymmetries.Classification) :
    ComplementsTheorem := by
  obtain ⟨-, -, -, -, -, hC, -, hO, -, -, -, -, -, -, -, -, -, -, -, hId, -⟩ := hHF
  have hAct : BasicFacts.PushSpanProperties := hFacts.2.2.2.2.1
  refine ⟨hCub.2.2.2.2.2.2.2.1, ?_⟩
  intro D T σ hb hrp hlim
  obtain ⟨hH, -, h, -, hSH, hTM, -⟩ := hLim D T σ hb hrp hlim
  obtain ⟨D₀, hD⟩ := hH.contraction
  obtain ⟨h₁, -, hS, hP, -, -, -⟩ := hRec σ D₀ hD
  obtain ⟨h₂, hPairs, -⟩ := hPair σ hH
  obtain ⟨-, -, h₃, -, -, -, -, hAss⟩ := hCone.1 D T σ hb hrp hlim
  obtain ⟨hσ, -, ⟨hInv, -⟩, -⟩ := hFirst D T σ hb hrp hlim
  obtain ⟨E, hE⟩ := exists_isHeatShiftMeasure σ h hR hJ hS hP
  obtain ⟨hM, hOp, hCar, hMar, F, hF, hFc, hFe⟩ := measure_claims σ h hR hG hSup E hE hSH hTM
    (fun i => (hPairs i).1) (fun i => (hAss i).2.1)
  refine ⟨h, hM, hOp, hCar, hMar, fun w hw => ?_⟩
  refine unitary_claims σ h hG hAct hC hO hId (fun v hv => ?_) hCub.1 hS.2.1 hP.2.1 F hF hFc hFe hw
  exact hInv (timeExtension v).toEquiv ⟨timeExtension v, (hCub.1 v hv).1, 0, fun x => by simp⟩
end YangMills.Construction.ReflectionPositivity.ReconstructionComplements
