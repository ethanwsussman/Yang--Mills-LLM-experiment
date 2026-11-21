import YangMills.Construction.ReflectionPositivity.ComplementsToTheReconstructionProof
import YangMills.Construction.TotalDensitiesGiveASystem.ComplementsOfAFunctionalWithAContraction
import Mathlib
set_option autoImplicit false
open MeasureTheory Set Filter Topology
open scoped NNReal InnerProductSpace ENNReal
noncomputable section
namespace YangMills.Construction.TotalDensitiesGiveASystem.ContractionFunctionalComplementsProof
open ReflectionPositivity.ReconstructionComplements
open SeparatedTuples ReflectionPositivity.TupleForm SpectralTheory
  LimitConventions
open InfiniteLattice (AmbientSpace hyperoctahedralLinearGroup)
open ReflectionPositivity.Reconstruction (PhysicalSpace spanClass posClass spaceShift
  spatialBasisVec embedSpatial timeShift timeBasisVec vacuum)
open Continuum.AxisPreservingSymmetries (timeBasisVector)
open ReflectionPositivity.PairMeasureOperators (pairHamiltonian pairMomentum)
open ReflectionPositivity.ShiftSpectralMeasure (energyMomentumRegion shiftSpectralMeasure
  IsShiftSpectralMeasure)
open HilbertSpaceBasics (IsPosSemidef ofBounded)
section Forms
variable {ℋ : Type} [NormedAddCommGroup ℋ] [InnerProductSpace ℂ ℋ] [CompleteSpace ℋ]
private abbrev posEnergyRegion : Set (Fin 4 → ℝ) := SemigroupRepresentation.nonnegHalfSpace 3
private theorem measurableSet_posEnergyRegion : MeasurableSet posEnergyRegion := by apply _root_.YangMills.Construction.ReflectionPositivity.ReconstructionComplements.measurableSet_posEnergyRegion <;> assumption
private def posEnergyBorel : BorelSets 4 := ⟨posEnergyRegion, measurableSet_posEnergyRegion⟩
private abbrev SubtypeSpectralMeasure (ℋ : Type) [NormedAddCommGroup ℋ] [InnerProductSpace ℂ ℋ]
    [CompleteSpace ℋ] : Type :=
  BorelSpectral.SpectralMeasure posEnergyRegion ℋ
private theorem inner_apply_apply (J : SubtypeSpectralMeasure ℋ)
    (B C : BorelSpectral.BorelSubsets posEnergyRegion) (ψ : ℋ) :
    ⟪J B ψ, J C ψ⟫_ℂ = ⟪ψ, J ⟨B.1 ∩ C.1, B.2.inter C.2⟩ ψ⟫_ℂ := by apply _root_.YangMills.Construction.ReflectionPositivity.ReconstructionComplements.inner_apply_apply_eq <;> assumption
private theorem tendsto_partialSums (J : SubtypeSpectralMeasure ℋ) (A : ℕ → Set posEnergyRegion)
    (hA : ∀ r, MeasurableSet (A r)) (hd : Pairwise fun r s => Disjoint (A r) (A s)) (ψ : ℋ) :
    Tendsto (fun N => ∑ r ∈ Finset.range N, J ⟨A r, hA r⟩ ψ) atTop
      (𝓝 (J ⟨⋃ r, A r, MeasurableSet.iUnion hA⟩ ψ)) := by apply _root_.YangMills.Construction.ReflectionPositivity.ReconstructionComplements.tendsto_sum_range_apply <;> assumption
private def toSpectralMeasureOn (J : SubtypeSpectralMeasure ℋ) : SpectralMeasureOn posEnergyBorel ℋ where
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
    have h := tendsto_partialSums J (fun r => Subtype.val ⁻¹' (A r).1)
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
private theorem extend_toSpectralMeasureOn (J : SubtypeSpectralMeasure ℋ) (A : BorelSets 4) :
    (toSpectralMeasureOn J).extend A = J ⟨Subtype.val ⁻¹' A.1, measurable_subtype_coe A.2⟩ := by
  have h : (⟨Subtype.val ⁻¹' (A.1 ∩ posEnergyRegion),
      measurable_subtype_coe (A.2.inter measurableSet_posEnergyRegion)⟩ :
      BorelSpectral.BorelSubsets posEnergyRegion) =
      ⟨Subtype.val ⁻¹' A.1, measurable_subtype_coe A.2⟩ :=
    Subtype.ext (by ext y; simp)
  exact congrArg J.toFun h
private theorem spectralValueMeasure_extend (J : SubtypeSpectralMeasure ℋ) (ψ : ℋ) :
    (toSpectralMeasureOn J).extend.spectralValueMeasure ψ = (J.diagMeasure ψ).map Subtype.val := by
  refine Measure.ext fun A hA => ?_
  rw [Measure.map_apply measurable_subtype_coe hA,
    (toSpectralMeasureOn J).extend.spectralValueMeasure_apply ψ ⟨A, hA⟩,
    J.diagMeasure_apply ψ ⟨Subtype.val ⁻¹' A, measurable_subtype_coe hA⟩,
    extend_toSpectralMeasureOn]
private theorem integral_spectralValueMeasure_extend (J : SubtypeSpectralMeasure ℋ) (ψ : ℋ)
    (g : posEnergyRegion → ℂ) :
    ∫ x, _root_.YangMills.Construction.SpectralTheory.extendByZero posEnergyBorel g x ∂((toSpectralMeasureOn J).extend.spectralValueMeasure ψ) =
      ∫ y, g y ∂(J.diagMeasure ψ) := by
  rw [spectralValueMeasure_extend,
    (MeasurableEmbedding.subtype_coe measurableSet_posEnergyRegion).integral_map]
  exact integral_congr_ae (Eventually.of_forall fun y =>
    extendByZero_apply_of_mem posEnergyBorel g y)
end Forms
private theorem measurable_heatPhase (t : ℝ≥0) (a : SpaceVec) : Measurable (heatPhase t a) := by apply _root_.YangMills.Construction.ReflectionPositivity.ReconstructionComplements.measurable_heatPhase <;> assumption
private def heatPhaseOn (t : ℝ≥0) (a : SpaceVec) (y : posEnergyRegion) : ℂ :=
  heatPhase t a y.1
private theorem measurable_heatPhaseOn (t : ℝ≥0) (a : SpaceVec) : Measurable (heatPhaseOn t a) := by apply _root_.YangMills.Construction.ReflectionPositivity.ReconstructionComplements.measurable_heatPhaseOn <;> assumption
private theorem measurable_heatPhaseExt (t : ℝ≥0) (a : SpaceVec) :
    Measurable (_root_.YangMills.Construction.SpectralTheory.extendByZero posEnergyBorel (heatPhaseOn t a)) := by apply _root_.YangMills.Construction.ReflectionPositivity.ReconstructionComplements.measurable_extendByZero_heatPhaseOn <;> assumption
private theorem isBoundedComplexFn_heatPhaseExt (t : ℝ≥0) (a : SpaceVec) :
    IsBoundedComplexFn (_root_.YangMills.Construction.SpectralTheory.extendByZero posEnergyBorel (heatPhaseOn t a)) := by apply _root_.YangMills.Construction.ReflectionPositivity.ReconstructionComplements.isBoundedComplexFn_extendByZero_heatPhaseOn <;> assumption
private theorem isBoundedComplexFn_heatPhase_zero (a : SpaceVec) :
    IsBoundedComplexFn (heatPhase 0 a) := by apply _root_.YangMills.Construction.ReflectionPositivity.ReconstructionComplements.isBoundedComplexFn_heatPhase_zero <;> assumption
private def energyPhase (τ : ℝ) (y : Fin 4 → ℝ) : ℂ :=
  Complex.exp (Complex.I * τ * (y 0 : ℝ))
private theorem measurable_energyPhase (τ : ℝ) : Measurable (energyPhase τ) := by
  have h : Continuous (energyPhase τ) := by
    unfold energyPhase
    fun_prop
  exact h.measurable
private theorem isBoundedComplexFn_energyPhase (τ : ℝ) : IsBoundedComplexFn (energyPhase τ) := by
  refine ⟨1, fun y => ?_⟩
  have h : Complex.I * τ * (y 0 : ℝ) = ((τ * y 0 : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  rw [energyPhase, h, Complex.norm_exp_ofReal_mul_I]
private theorem energyPhase_mul_heatPhase (τ : ℝ) (a : SpaceVec) (y : Fin 4 → ℝ) :
    energyPhase τ y * heatPhase 0 a y = unitaryPhase τ a y := by
  rw [energyPhase, heatPhase, unitaryPhase, ← Complex.exp_add]
  congr 1
  push_cast
  simp
  ring
section Products
variable {ℋ : Type} [NormedAddCommGroup ℋ] [InnerProductSpace ℂ ℋ] [CompleteSpace ℋ]
private theorem compBounded_ofBounded (B C : ℋ →L[ℂ] ℋ) :
    compBounded (ofBounded B) C = ofBounded (B * C) := by apply _root_.YangMills.Construction.ReflectionPositivity.ReconstructionComplements.compBounded_ofBounded <;> assumption
private theorem ofBounded_injective {A B : ℋ →L[ℂ] ℋ} (h : ofBounded A = ofBounded B) : A = B := by apply _root_.YangMills.Construction.ReflectionPositivity.ShiftSpectralMeasure.ofBounded_injective <;> assumption
end Products
section Rules
variable {ℋ : Type} [NormedAddCommGroup ℋ] [InnerProductSpace ℂ ℋ] [CompleteSpace ℋ]
private theorem inner_boundedCalculus {n : ℕ} [NeZero n] (E : ProjectionMeasure n ℋ)
    (R : E.CalculusLaws) {f : (Fin n → ℝ) → ℂ} (hf : Measurable f)
    (hb : IsBoundedComplexFn f) (ψ : ℋ) :
    ⟪ψ, E.boundedCalculus f ψ⟫_ℂ = ∫ x, f x ∂(E.spectralValueMeasure ψ) := by apply _root_.YangMills.Construction.ReflectionPositivity.ShiftSpectralMeasure.inner_boundedIntegralOp <;> assumption
private theorem ofBounded_eq_functionalCalculus {n : ℕ} [NeZero n] (E : ProjectionMeasure n ℋ)
    (R : E.CalculusLaws) {f : (Fin n → ℝ) → ℂ} (hf : Measurable f)
    (hb : IsBoundedComplexFn f) (T : ℋ →L[ℂ] ℋ)
    (h : ∀ ψ, ⟪ψ, T ψ⟫_ℂ = ∫ x, f x ∂(E.spectralValueMeasure ψ)) :
    ofBounded T = E.functionalCalculus f := by apply _root_.YangMills.Construction.ReflectionPositivity.ShiftSpectralMeasure.ofBounded_eq_spectralIntegral <;> assumption
private theorem ofBounded_integralOp (J : SubtypeSpectralMeasure ℋ)
    (R : (toSpectralMeasureOn J).extend.CalculusLaws) (t : ℝ≥0) (a : SpaceVec) :
    ofBounded (J.integralOp (heatPhaseOn t a)) =
      (toSpectralMeasureOn J).extend.functionalCalculusOn posEnergyBorel (heatPhaseOn t a) := by
  have hf := measurable_heatPhaseExt t a
  have hb := isBoundedComplexFn_heatPhaseExt t a
  have hd : J.IsDiagonalIntegral (heatPhaseOn t a)
      ((toSpectralMeasureOn J).extend.boundedCalculus
        (_root_.YangMills.Construction.SpectralTheory.extendByZero posEnergyBorel (heatPhaseOn t a))) := fun ψ => by
    rw [inner_boundedCalculus _ R hf hb, integral_spectralValueMeasure_extend]
  have hs : J.IsDiagonalIntegral (heatPhaseOn t a) (J.integralOp (heatPhaseOn t a)) :=
    Classical.epsilon_spec ⟨_, hd⟩
  exact ofBounded_eq_functionalCalculus _ R hf hb _ fun ψ => by
    rw [hs ψ, integral_spectralValueMeasure_extend]
private theorem extend_eq_zero (E : SpectralMeasureOn posEnergyBorel ℋ) (S : BorelSets 4)
    (h : ∀ y ∈ S.1, y ∉ posEnergyRegion) : E.extend S = 0 := by
  have ht : SpectralMeasureOn.restrictSet posEnergyBorel S =
      ⟨∅, MeasurableSet.empty, empty_subset _⟩ :=
    Subtype.ext (eq_empty_of_forall_notMem fun y hy => h y hy.1 hy.2)
  rw [E.extend_apply, ht, E.map_empty]
private theorem calculus_congr_on (E : SpectralMeasureOn posEnergyBorel ℋ)
    (R : E.extend.CalculusLaws) {f g : (Fin 4 → ℝ) → ℂ} (hf : Measurable f)
    (hg : Measurable g) (h : ∀ y ∈ posEnergyRegion, f y = g y) :
    E.extend.functionalCalculus f = E.extend.functionalCalculus g :=
  R.calculus_congr f g hf hg (extend_eq_zero E _ fun y hy hY => hy (h y hY))
private def IsHeatShiftCalculus (T : ℝ≥0 → ℋ →L[ℂ] ℋ) (U : SpaceVec → ℋ →L[ℂ] ℋ)
    (E : SpectralMeasureOn posEnergyBorel ℋ) : Prop :=
  ∀ t a, ofBounded (T t * U a) = E.extend.functionalCalculus (heatPhase t a)
private theorem isHeatShiftCalculus_toSpectralMeasureOn (J : SubtypeSpectralMeasure ℋ)
    (R : (toSpectralMeasureOn J).extend.CalculusLaws)
    {T : ℝ≥0 → ℋ →L[ℂ] ℋ} {U : SpaceVec → ℋ →L[ℂ] ℋ}
    (hJ : SemigroupRepresentation.IsJointSpectralMeasure J T U) :
    IsHeatShiftCalculus T U (toSpectralMeasureOn J) := fun t a => by
  have h : T t * U a = J.integralOp (heatPhaseOn t a) := hJ t a
  rw [h, ofBounded_integralOp J R t a]
  refine calculus_congr_on _ R (measurable_heatPhaseExt t a) (measurable_heatPhase t a)
    fun y hy => ?_
  exact extendByZero_apply_of_mem posEnergyBorel (heatPhaseOn t a) ⟨y, hy⟩
private abbrev marginal (K : ProjectionMeasure 4 ℋ) (r : Fin 4) : ProjectionMeasure 1 ℋ :=
  K.imageMeasure (coordProj r) (measurable_coordProj r)
private theorem hasSpectralResolution_marginal (K : ProjectionMeasure 4 ℋ)
    (R : K.CalculusLaws) (r : Fin 4) :
    HasSpectralResolution (K.coordinateOp r) (marginal K r) := by
  unfold HasSpectralResolution
  rw [R.calculus_imageMeasure 1 _ _ _ (measurable_coordFun 0)]
  rfl
private theorem expIMulOp_marginal (K : ProjectionMeasure 4 ℋ) (R : K.CalculusLaws)
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
private theorem marginal_isConcentratedOn :
    (marginal E.extend 0).IsConcentratedOn nonnegReals :=
  extend_eq_zero E ⟨coordProj 0 ⁻¹' nonnegReals.1ᶜ,
    measurable_coordProj 0 nonnegReals.2.compl⟩ fun _ hy hY => hy hY
include R in
private theorem expNegMulOp_marginal (hU : U 0 = 1) (hE : IsHeatShiftCalculus T U E) (t : ℝ≥0) :
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
  refine calculus_congr_on E R (hm.comp (measurable_coordProj 0))
    (measurable_heatPhase t 0) fun y hy => ?_
  have h₁ := extendByZero_apply_of_mem nonnegReals
    (fun x : nonnegReals.1 => Complex.exp (-(t : ℂ) * ((x.1 0 : ℝ) : ℂ)))
    ⟨coordProj 0 y, hy⟩
  simp only at h₁
  rw [Function.comp_apply, h₁]
  simp [heatPhase, coordProj, spaceDot, SeparatedTupleFunctionals.dotProd]
include R in
private theorem spaceShift_eq_boundedCalculus (hT : T 0 = 1) (hE : IsHeatShiftCalculus T U E)
    (a : SpaceVec) :
    U a = E.extend.boundedCalculus (heatPhase 0 a) := by
  have h := hE 0 a
  rw [hT, one_mul, show E.extend.functionalCalculus (heatPhase 0 a) = _ from
    R.isBoundedCalculusOf _ (measurable_heatPhase 0 a) (isBoundedComplexFn_heatPhase_zero a)] at h
  exact ofBounded_injective h
include R in
private theorem unitaryPhase_marginal (hT : T 0 = 1) (hE : IsHeatShiftCalculus T U E) (τ : ℝ)
    (a : SpaceVec) :
    compBounded ((marginal E.extend 0).expIMulOp τ) (U a) =
      E.extend.functionalCalculus (unitaryPhase τ a) := by
  have h₁ : (marginal E.extend 0).expIMulOp τ =
      ofBounded (E.extend.boundedCalculus (energyPhase τ)) :=
    (expIMulOp_marginal E.extend R 0 τ).trans
      (R.isBoundedCalculusOf _ (measurable_energyPhase τ) (isBoundedComplexFn_energyPhase τ))
  have hm : Measurable fun y => energyPhase τ y * heatPhase 0 a y :=
    (measurable_energyPhase τ).mul (measurable_heatPhase 0 a)
  have hb : IsBoundedComplexFn fun y => energyPhase τ y * heatPhase 0 a y := by
    simp only [energyPhase_mul_heatPhase]
    refine ⟨1, fun y => ?_⟩
    show ‖unitaryPhase τ a y‖ ≤ 1
    rw [unitaryPhase, mul_comm]
    exact (Complex.norm_exp_ofReal_mul_I _).le
  rw [h₁, compBounded_ofBounded, spaceShift_eq_boundedCalculus E R hT hE a,
    R.boundedCalculus_mul _ _ (measurable_energyPhase τ) (measurable_heatPhase 0 a)
      (isBoundedComplexFn_energyPhase τ) (isBoundedComplexFn_heatPhase_zero a)]
  have h₂ := (R.isBoundedCalculusOf _ hm hb)
  have h₃ : (fun y => energyPhase τ y * heatPhase 0 a y) = unitaryPhase τ a :=
    funext (energyPhase_mul_heatPhase τ a)
  rw [h₃] at h₂ ⊢
  exact h₂.symm
include R in
private theorem heatPhase_marginal (hU : U 0 = 1) (hE : IsHeatShiftCalculus T U E) (t : ℝ≥0)
    (a : SpaceVec) :
    compBounded ((marginal E.extend 0).expNegMulOp t) (U a) =
      E.extend.functionalCalculus (heatPhase t a) := by
  rw [expNegMulOp_marginal E R hU hE t, compBounded_ofBounded]
  exact hE t a
private theorem spaceDot_smul_basis (u : ℝ) (i : Fin 3) (y : Fin 4 → ℝ) :
    spaceDot (u • spatialBasisVec i) (spatialPart y) = u * y i.succ := by
  simp [spaceDot, SeparatedTupleFunctionals.dotProd, spatialBasisVec, spatialPart, Pi.single_apply]
include R in
private theorem expIMulOp_momentumMarginal (hT : T 0 = 1) (hE : IsHeatShiftCalculus T U E)
    (i : Fin 3) (u : ℝ) :
    (marginal E.extend i.succ).expIMulOp u = ofBounded (U (u • spatialBasisVec i)) := by
  have h := hE 0 (u • spatialBasisVec i)
  rw [hT, one_mul] at h
  rw [h, expIMulOp_marginal E.extend R]
  congr 1
  funext y
  simp only [heatPhase, spaceDot_smul_basis]
  simp
  ring_nf
include R in
private theorem eq_extend_of_unitaryPhase (hG : GeneratorsAndFlows.GeneratorFlowTheorem)
    (hT : T 0 = 1) (hE : IsHeatShiftCalculus T U E)
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
  exact unitaryPhase_marginal E R hT hE _ _
end Rules
section Marginals
variable {ℋ : Type} [NormedAddCommGroup ℋ] [InnerProductSpace ℂ ℋ] [CompleteSpace ℋ]
private theorem stronglyCommute_of_eq (hG : GeneratorsAndFlows.GeneratorFlowTheorem)
    (K : ProjectionMeasure 4 ℋ) (R : K.CalculusLaws) (A : Fin 4 → UnboundedOperator ℋ)
    (hA : ∀ r, A r = K.coordinateOp r) : StronglyCommute A := by apply _root_.YangMills.Construction.ReflectionPositivity.ReconstructionComplements.stronglyCommute_of_eq_coordOp <;> assumption
end Marginals
section Measure
variable (σ : TupleFunctional) (h : IsPosSemidef (reflectionForm σ))
private theorem exists_heatShiftCalculus (hR : SpectralTheory.SpectralIntegralLawsHold)
    (hJ : SemigroupRepresentation.JointSpectralTheoremForPair)
    (hS : ReflectionPositivity.Reconstruction.SemigroupProperties σ h)
    (hP : ReflectionPositivity.Reconstruction.SpatialProperties σ h) :
    ∃ E, IsHeatShiftCalculus (timeShift σ h) (spaceShift σ h) E := by
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
    (timeShift σ h) (spaceShift σ h)), isHeatShiftCalculus_toSpectralMeasureOn _ (hR 4 _ _) hj⟩
open ReflectionPositivity.LimitReconstruction (IsShiftGenerator IsHeatGenerator
  TimeSemigroupProperties SpaceShiftProperties)
end Measure
section Cubic
variable (σ : TupleFunctional) (h : IsPosSemidef (reflectionForm σ))
open ReflectionPositivity.Reconstruction (IsSpaceShiftFamily IsTimeShiftFamily posTupleVec)
private theorem unitaryClaims (hG : GeneratorsAndFlows.GeneratorFlowTheorem)
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
    UnitaryClaim σ h w ∧ IntertwiningClaim σ h w := by apply _root_.YangMills.Construction.ReflectionPositivity.ReconstructionComplements.unitary_claims <;> assumption
end Cubic
section MeasureParts
open scoped NNReal
open LimitConventions
open ReflectionPositivity.Reconstruction (PhysicalSpace spanClass posClass spaceShift
  spatialBasisVec embedSpatial timeShift timeBasisVec vacuum)
open ReflectionPositivity.PairMeasureOperators (pairHamiltonian pairMomentum)
open HilbertSpaceBasics (IsPosSemidef ofBounded)
open ReflectionPositivity.LimitReconstruction (IsShiftGenerator IsHeatGenerator
  TimeSemigroupProperties SpaceShiftProperties)
variable (σ : TupleFunctional) (h : IsPosSemidef (reflectionForm σ))
private theorem measureClaims (hR : SpectralTheory.SpectralIntegralLawsHold)
    (hG : GeneratorsAndFlows.GeneratorFlowTheorem)
    (E : SpectralMeasureOn posEnergyBorel (PhysicalSpace σ h))
    (hE : IsHeatShiftCalculus (timeShift σ h) (spaceShift σ h) E)
    (hSH : TimeSemigroupProperties σ h) (hTM : SpaceShiftProperties σ h) :
    MeasureClaim σ h ∧ OperatorClaim σ h ∧ SupportClaim σ h ∧
      ∃ F : ProjectionMeasure 1 (PhysicalSpace σ h),
        HasSpectralResolution (pairHamiltonian σ h) F ∧ F.IsConcentratedOn nonnegReals ∧
          ∀ t : ℝ≥0, F.expNegMulOp t = ofBounded (timeShift σ h t) := by
  have R : E.extend.CalculusLaws := hR 4 _ _
  obtain ⟨-, -, -, hSemi, -, -, hHuniq, -⟩ := hSH
  obtain ⟨-, -, -, hRep, -, -, hMom⟩ := hTM
  have hT0 : timeShift σ h 0 = 1 := hSemi.map_zero
  have hU0 : spaceShift σ h 0 = 1 := hRep.map_zero
  have hCar := marginal_isConcentratedOn E
  have hExpH := expNegMulOp_marginal E R hU0 hE
  have hSpH₀ := hasSpectralResolution_marginal E.extend R 0
  have hH : E.extend.coordinateOp 0 = pairHamiltonian σ h :=
    hHuniq _ ⟨_, hSpH₀, hCar, fun t => (hExpH t).symm⟩
  have hSpH : HasSpectralResolution (pairHamiltonian σ h) (marginal E.extend 0) := by
    rw [← hH]
    exact hSpH₀
  have hP : ∀ i : Fin 3, E.extend.coordinateOp i.succ = pairMomentum σ h i := fun i =>
    (hMom i).2.1 _ ⟨_, hasSpectralResolution_marginal E.extend R i.succ, fun u =>
      (expIMulOp_momentumMarginal E R hT0 hE i u).symm⟩
  have hK : IsJointGroupMeasure σ h E.extend :=
    ⟨_, hSpH, unitaryPhase_marginal E R hT0 hE⟩
  have huniq : ∀ E', IsJointGroupMeasure σ h E' → E' = E.extend := by
    rintro E' ⟨F', hF', h'⟩
    exact eq_extend_of_unitaryPhase E R hG hT0 hE E' F' (by rw [hH]; exact hF') h'
  have hEm : jointMeasure σ h = E.extend :=
    huniq _ (Classical.epsilon_spec (p := IsJointGroupMeasure σ h) ⟨_, hK⟩)
  have hfour : ∀ r, energyMomentumOps σ h r = E.extend.coordinateOp r := fun r => by
    refine Fin.cases ?_ (fun i => ?_) r
    · exact hH.symm
    · exact (hP i).symm
  refine ⟨⟨⟨_, hK, huniq⟩, by rw [hEm]; exact hK⟩, ?_, ?_, ⟨_, hSpH, hCar, hExpH⟩⟩
  · rw [OperatorClaim, hEm]
    refine ⟨hH.symm, fun i => (hP i).symm,
      stronglyCommute_of_eq hG E.extend R _ hfour, hfour⟩
  · rw [SupportClaim, hEm]
    exact ⟨E.extend_isConcentratedOn, _, hSpH, hCar, heatPhase_marginal E R hU0 hE⟩
end MeasureParts
section TheProof
open ReflectionPositivity.LimitReconstruction (TimeSemigroupProperties SpaceShiftProperties)
open ReflectionPositivity.ContractionFunctionals (IsAdmissible)
open ReflectionPositivity.ShiftSpectralMeasure (EnergyOpProperties MomentumOpProperties
  VacuumAnnihilated AgreesWithReconstruction)
private theorem exists_isometryEquiv_of_unitary {ℋ : Type*} [NormedAddCommGroup ℋ]
    [InnerProductSpace ℂ ℋ] [CompleteSpace ℋ] {A : ℋ →L[ℂ] ℋ}
    (hA : HilbertSpaceBasics.IsUnitaryOp A) :
    ∃ V : ℋ ≃ₗᵢ[ℂ] ℋ, ∀ ψ, A ψ = V ψ :=
  ⟨Unitary.linearIsometryEquiv ⟨A, hA.1, hA.2⟩, fun _ => rfl⟩
theorem contractionFunctionalComplements_holds (hHF : HilbertSpaceFacts.Facts)
    (hFacts : SeparatedTuples.BasicFacts.MainFacts)
    (hR : SpectralTheory.SpectralIntegralLawsHold)
    (hG : GeneratorsAndFlows.GeneratorFlowTheorem)
    (hJ : SemigroupRepresentation.JointSpectralTheoremForPair)
    (hRec : ReflectionPositivity.Reconstruction.ReconstructionTheorem)
    (hPair : ReflectionPositivity.ShiftSpectralMeasure.ShiftSpectralMeasureTheorem)
    (hCub : Continuum.AxisPreservingSymmetries.Classification) :
    ContractionFunctionalComplements := by
  intro σ hH hI
  obtain ⟨-, -, -, -, -, hC, -, hO, -, -, -, -, -, -, -, -, -, -, -, hId, -⟩ := hHF
  have hAct : BasicFacts.PushSpanProperties := hFacts.2.2.2.2.1
  obtain ⟨D₀, hcn⟩ := hH.contraction
  obtain ⟨h, hV, hSg, hSp, hM, -, -⟩ := hRec _ D₀ hcn
  obtain ⟨h', hP', -⟩ := hPair _ hH
  have hPr : ∀ i : Fin 3, ReflectionPositivity.ShiftSpectralMeasure.ExistsUniqueShiftMeasure σ h i ∧
      EnergyOpProperties σ h i ∧ MomentumOpProperties σ h i ∧ VacuumAnnihilated σ h i ∧
        AgreesWithReconstruction σ h i := hP'
  have hSH : TimeSemigroupProperties σ h := by
    obtain ⟨hu, hT', hsc, hsg, hself, -⟩ := hSg
    obtain ⟨-, ⟨⟨F, -, hs, hcar, hexp⟩, -, huniq⟩, -, ⟨hΩ, -⟩, -⟩ := hPr 0
    refine ⟨hu, hT', hsc, ⟨hsg.1, fun a b => (hsg.2 a b).symm⟩, fun t => ⟨(hself t).1, (hself t).2.1,
      LinearMap.ker_eq_bot'.mpr (hself t).2.2⟩, ⟨F, hs, hcar, fun t => (hexp t).symm⟩, ?_, hΩ⟩
    rintro A ⟨G, hG', hGc, hGe⟩
    exact huniq A G hG' hGc fun t => (hGe t).symm
  have hTM : SpaceShiftProperties σ h := by
    obtain ⟨hu, hU, hsc, hur, hcomm, hfix, -⟩ := hSp
    refine ⟨hu, hU, hsc, ⟨hur.2.1, fun a b => (hur.2.2 a b).symm,
      fun a => exists_isometryEquiv_of_unitary (hur.1 a)⟩, hcomm, hfix, fun i => ?_⟩
    obtain ⟨-, -, ⟨⟨F, -, hs, hexp⟩, huniq⟩, ⟨-, hΩ⟩, -⟩ := hPr i
    refine ⟨⟨F, hs, fun u => (hexp u).symm⟩, ?_, hΩ⟩
    rintro A ⟨G, hG', hGe⟩
    exact huniq A G hG' fun u => (hGe u).symm
  obtain ⟨E, hE⟩ := exists_heatShiftCalculus _ h hR hJ hSg hSp
  obtain ⟨hMP, hOps, hCar, F, hF, hFc, hFe⟩ := measureClaims _ h hR hG E hE hSH hTM
  exact ⟨h, hV, hSH, hTM, hM, hMP, hOps, hCar, fun w hw =>
    unitaryClaims _ h hG hAct hC hO hId hI hCub.1 hSg.2.1 hSp.2.1 F hF hFc hFe hw⟩
end TheProof
end YangMills.Construction.TotalDensitiesGiveASystem.ContractionFunctionalComplementsProof
end
