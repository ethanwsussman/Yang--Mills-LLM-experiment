import YangMills.Construction.ClusterExpansionOfAStep.UnitQuaternionsAreTheMatrixGroup
import YangMills.Construction.QuaternionicWilsonModel.TheQuaternionModelIsSUTwoWithWilsonsWeight
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped ENNReal Quaternion
namespace YangMills.Construction.QuaternionModel
open YangMills.Construction.PeriodicLattice
open YangMills.Construction.TorusFields
open YangMills.Construction.ClusterExpansionOfAStep
open YangMills.Construction.BlockAverages (UnitQuaternion)
open YangMills.Construction.SoftAverages (quaternionToMatrix quaternionToMatrix_mul quaternionToMatrix_one)
section LatticeCoordinates
variable {L m K n : ℕ}
private theorem blockFactor_pos (hn : n = 2 * L ^ (m + K)) (h2 : 2 < n) : 0 < L := by
  rcases Nat.eq_zero_or_pos L with h | h
  · subst h
    rcases Nat.eq_zero_or_pos (m + K) with h' | h'
    · rw [h'] at hn; simp at hn; omega
    · rw [zero_pow h'.ne'] at hn; omega
  · exact h
abbrev _root_.YangMills.SharedProofs.p82021 := @blockFactor_pos
private theorem meshSize_pos' (hL : 0 < L) : 0 < meshSize L (K : ℤ) := by
  unfold meshSize
  exact zpow_pos (by exact_mod_cast hL) _
private theorem torusSide_eq_mul_meshSize (hn : n = 2 * L ^ (m + K)) (hL : 0 < L) :
    torusSide L m = (n : ℝ) * meshSize L (K : ℤ) := by
  subst hn
  simp only [PeriodicLattice.torusSide, meshSize, zpow_neg, zpow_natCast]
  push_cast
  rw [pow_add]
  field_simp
private theorem coe_mul_meshSize_eq_iff (hn : n = 2 * L ^ (m + K)) (hL : 0 < L) (a b : ℤ) :
    (((a : ℝ) * meshSize L (K : ℤ) : ℝ) : AddCircle (torusSide L m)) =
        (((b : ℝ) * meshSize L (K : ℤ) : ℝ) : AddCircle (torusSide L m)) ↔ (a : ZMod n) = (b : ZMod n) := by
  have hsp := meshSize_pos' (K := K) hL
  have hs := torusSide_eq_mul_meshSize hn hL
  rw [← sub_eq_zero, ← AddCircle.coe_sub, AddCircle.coe_eq_zero_iff, ← sub_eq_zero (a := (a : ZMod n)),
    ← Int.cast_sub, CharP.intCast_eq_zero_iff (ZMod n) n]
  constructor
  · rintro ⟨k, hk⟩
    refine ⟨k, ?_⟩
    rw [zsmul_eq_mul, hs] at hk
    have : ((a - b : ℤ) : ℝ) = ((n * k : ℤ) : ℝ) := by
      push_cast
      have h3 : ((a : ℝ) - b) * meshSize L (K : ℤ) = ((n : ℝ) * k) * meshSize L (K : ℤ) := by
        rw [sub_mul, ← hk]; ring
      exact mul_right_cancel₀ hsp.ne' h3
    exact_mod_cast this
  · rintro ⟨k, hk⟩
    refine ⟨k, ?_⟩
    rw [zsmul_eq_mul, hs]
    have : ((a : ℝ) - b) = (n : ℝ) * k := by exact_mod_cast hk
    rw [← sub_mul, this]
    ring
abbrev _root_.YangMills.SharedProofs.p25868 := @coe_mul_meshSize_eq_iff
private theorem coe_offsetSite_apply (p : Fin 4 → ℤ) (μ : Fin 4) :
    ((offsetSite (0 : Site L m (K : ℤ)) p : Site L m (K : ℤ)) : FourTorus L m) μ =
      (((p μ : ℝ) * meshSize L (K : ℤ) : ℝ) : AddCircle (torusSide L m)) := by
  simp only [offsetSite, zero_add, AddSubgroup.val_finsetSum, Finset.sum_apply,
    AddSubgroup.coe_zsmul, Pi.smul_apply, PeriodicLattice.unitStep, pointOnAxis]
  rw [Finset.sum_eq_single μ]
  · rw [Pi.single_eq_same, ← AddCircle.coe_zsmul, zsmul_eq_mul]
  · intro ν _ hν
    rw [Pi.single_eq_of_ne hν.symm, smul_zero]
  · simp
abbrev _root_.YangMills.SharedProofs.p59635 := @coe_offsetSite_apply
private theorem offsetSite_zero_add (p q : Fin 4 → ℤ) :
    offsetSite (0 : Site L m (K : ℤ)) (p + q) =
      offsetSite (0 : Site L m (K : ℤ)) p + offsetSite (0 : Site L m (K : ℤ)) q := by
  simp [offsetSite, add_smul, Finset.sum_add_distrib]
private theorem offsetSite_zero_neg (p : Fin 4 → ℤ) :
    offsetSite (0 : Site L m (K : ℤ)) (-p) = -offsetSite (0 : Site L m (K : ℤ)) p := by
  simp [offsetSite, neg_smul, Finset.sum_neg_distrib]
private theorem unitStep_eq_offsetSite (μ : Fin 4) :
    PeriodicLattice.unitStep L m (K : ℤ) μ = offsetSite (0 : Site L m (K : ℤ)) (Pi.single μ 1) := by
  simp [offsetSite, Pi.single_apply, ite_smul]
private theorem offsetSite_zero_eq_iff (hn : n = 2 * L ^ (m + K)) (hL : 0 < L) (p q : Fin 4 → ℤ) :
    offsetSite (0 : Site L m (K : ℤ)) p = offsetSite (0 : Site L m (K : ℤ)) q ↔
      ∀ μ, (p μ : ZMod n) = (q μ : ZMod n) := by
  rw [Subtype.ext_iff, funext_iff]
  simp only [coe_offsetSite_apply, coe_mul_meshSize_eq_iff hn hL]
private theorem unitStep_ne_neg_unitStep (hn : n = 2 * L ^ (m + K)) (hL : 0 < L) (h2 : 2 < n) (μ ν : Fin 4) :
    PeriodicLattice.unitStep L m (K : ℤ) μ ≠ -PeriodicLattice.unitStep L m (K : ℤ) ν := by
  have : Fact (1 < n) := ⟨by omega⟩
  intro h
  rw [unitStep_eq_offsetSite, unitStep_eq_offsetSite, ← offsetSite_zero_neg, offsetSite_zero_eq_iff hn hL] at h
  have h3 := h μ
  by_cases e : μ = ν
  · subst e
    simp only [Pi.single_eq_same, Pi.neg_apply, Int.cast_one, Int.cast_neg] at h3
    have h4 : ((2 : ℤ) : ZMod n) = 0 := by
      push_cast
      linear_combination h3
    rw [CharP.intCast_eq_zero_iff (ZMod n) n] at h4
    have := Int.le_of_dvd (by norm_num) h4
    omega
  · simp [Pi.single_eq_of_ne e] at h3
private theorem unitStep_injective' (hn : n = 2 * L ^ (m + K)) (hL : 0 < L) (h2 : 2 < n) {μ ν : Fin 4}
    (h : PeriodicLattice.unitStep L m (K : ℤ) μ = PeriodicLattice.unitStep L m (K : ℤ) ν) : μ = ν := by
  have : Fact (1 < n) := ⟨by omega⟩
  by_contra e
  rw [unitStep_eq_offsetSite, unitStep_eq_offsetSite, offsetSite_zero_eq_iff hn hL] at h
  have h3 := h μ
  simp [Pi.single_eq_of_ne e] at h3
variable [NeZero n]
omit [NeZero n] in
private theorem periodicLatticeSite_add_unitStep (hn : n = 2 * L ^ (m + K)) (hL : 0 < L) (x : TorusSite n)
    (μ : Fin 4) :
    periodicLatticeSite L m (K : ℤ) (x + TorusFields.unitStep n μ) =
      periodicLatticeSite L m (K : ℤ) x + PeriodicLattice.unitStep L m (K : ℤ) μ := by
  rw [unitStep_eq_offsetSite, periodicLatticeSite, periodicLatticeSite, ← offsetSite_zero_add,
    offsetSite_zero_eq_iff hn hL]
  intro ν
  simp only [ZMod.intCast_zmod_cast, Pi.add_apply, Int.cast_add, TorusFields.unitStep, Pi.single_apply]
  split_ifs <;> simp
private theorem coe_periodicLatticeSite_apply (x : TorusSite n) (μ : Fin 4) :
    ((periodicLatticeSite L m (K : ℤ) x : Site L m (K : ℤ)) : FourTorus L m) μ =
      ((((x μ).val : ℝ) * meshSize L (K : ℤ) : ℝ) : AddCircle (torusSide L m)) := by
  have hc : ((x μ).cast : ℤ) = ((x μ).val : ℤ) := (ZMod.natCast_val _).symm
  rw [periodicLatticeSite, coe_offsetSite_apply, hc]
  simp
abbrev _root_.YangMills.SharedProofs.p20856 := @coe_periodicLatticeSite_apply
private theorem pointOnAxis_half (L m : ℕ) (μ i : Fin 4) (s : ℝ) :
    pointOnAxis L m μ (s / 2) i =
      (((if i = μ then (1 / 2 : ℝ) else 0) * s : ℝ) : AddCircle (torusSide L m)) := by
  unfold pointOnAxis
  by_cases h : i = μ
  · subst h
    rw [Pi.single_eq_same, if_pos rfl]
    congr 1
    ring
  · rw [Pi.single_eq_of_ne h, if_neg h]
    simp
abbrev _root_.YangMills.SharedProofs.p60603 := @pointOnAxis_half
private theorem barycenter_plaquetteOfOriented_apply (q : WeightedResponses.OrientedPlaquette n) (i : Fin 4) :
    (plaquetteOfOriented L m K q).barycenter i =
      (((((q.1.1 i).val : ℝ) + (if i = q.1.2.1 then 1 / 2 else 0) + (if i = q.1.2.2 then 1 / 2 else 0)) *
        meshSize L (K : ℤ) : ℝ) : AddCircle (torusSide L m)) := by
  simp only [PeriodicLattice.Plaquette.barycenter, plaquetteOfOriented, Pi.add_apply]
  rw [coe_periodicLatticeSite_apply, pointOnAxis_half, pointOnAxis_half, ← AddCircle.coe_add, ← AddCircle.coe_add]
  congr 1
  ring
end LatticeCoordinates
section BondOrientation
variable {L m K n : ℕ} [NeZero n]
private theorem isPositivelyOriented_or_opposite (b : PeriodicLattice.Bond L m (K : ℤ)) :
    b.IsPositivelyOriented ∨ b.opposite.IsPositivelyOriented := by
  obtain ⟨μ, h | h⟩ := b.isNeighbour
  · exact Or.inl ⟨μ, h⟩
  · refine Or.inr ⟨μ, ?_⟩
    show b.source - b.target = _
    rw [← neg_sub, h, neg_neg]
abbrev _root_.YangMills.SharedProofs.p39011 := @isPositivelyOriented_or_opposite
omit [NeZero n] in
private theorem not_isPositivelyOriented_opposite (hn : n = 2 * L ^ (m + K)) (hL : 0 < L) (h2 : 2 < n)
    {b : PeriodicLattice.Bond L m (K : ℤ)} (hb : b.IsPositivelyOriented) :
    ¬ b.opposite.IsPositivelyOriented := by
  obtain ⟨μ, h⟩ := hb
  rintro ⟨ν, h'⟩
  have h3 : b.source - b.target = PeriodicLattice.unitStep L m (K : ℤ) ν := h'
  rw [← neg_sub, h] at h3
  exact unitStep_ne_neg_unitStep hn hL h2 ν μ h3.symm
omit [NeZero n] in
private theorem xor_isPositivelyOriented_opposite (hn : n = 2 * L ^ (m + K)) (hL : 0 < L) (h2 : 2 < n)
    (b : PeriodicLattice.Bond L m (K : ℤ)) : Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented := by
  rcases isPositivelyOriented_or_opposite b with h | h
  · exact Or.inl ⟨h, not_isPositivelyOriented_opposite hn hL h2 h⟩
  · refine Or.inr ⟨h, fun h' => ?_⟩
    exact not_isPositivelyOriented_opposite hn hL h2 h h'
private theorem isPositivelyOriented_iff_exists (A : TorusFieldsAreGaugeFields L m K n)
    (b : PeriodicLattice.Bond L m (K : ℤ)) :
    b.IsPositivelyOriented ↔
      ∃ (x : TorusSite n) (μ : Fin 4), b = PeriodicLattice.Bond.forwardFrom (periodicLatticeSite L m (K : ℤ) x) μ := by
  constructor
  · rintro ⟨μ, h⟩
    obtain ⟨x, hx⟩ := A.siteBijective.2 b.source
    refine ⟨x, μ, PeriodicLattice.Bond.ext hx.symm ?_⟩
    simp only [PeriodicLattice.Bond.forwardFrom]
    rw [hx, ← h]
    abel
  · rintro ⟨x, μ, rfl⟩
    exact ⟨μ, by simp [PeriodicLattice.Bond.forwardFrom]⟩
private theorem forwardFrom_periodicLatticeSite_injective (hn : n = 2 * L ^ (m + K)) (hL : 0 < L) (h2 : 2 < n)
    (A : TorusFieldsAreGaugeFields L m K n) :
    Function.Injective fun p : TorusSite n × Fin 4 =>
      PeriodicLattice.Bond.forwardFrom (periodicLatticeSite L m (K : ℤ) p.1) p.2 := by
  rintro ⟨x, μ⟩ ⟨y, ν⟩ h
  have h1 : periodicLatticeSite L m (K : ℤ) x = periodicLatticeSite L m (K : ℤ) y :=
    congrArg PeriodicLattice.Bond.source h
  have h3 : periodicLatticeSite L m (K : ℤ) x + PeriodicLattice.unitStep L m (K : ℤ) μ =
      periodicLatticeSite L m (K : ℤ) y + PeriodicLattice.unitStep L m (K : ℤ) ν :=
    congrArg PeriodicLattice.Bond.target h
  rw [h1] at h3
  exact Prod.ext (A.siteBijective.1 h1) (unitStep_injective' hn hL h2 (add_left_cancel h3))
private theorem quaternionToMatrix_inv (u : UnitQuaternion) :
    quaternionToMatrix ((u⁻¹ : UnitQuaternion) : ℍ[ℝ]) = (quaternionToMatrix (u : ℍ[ℝ]))⁻¹ := by
  have h : quaternionToMatrix ((u⁻¹ : UnitQuaternion) : ℍ[ℝ]) * quaternionToMatrix (u : ℍ[ℝ]) = 1 := by
    rw [← quaternionToMatrix_mul, ← Submonoid.coe_mul, inv_mul_cancel]
    exact quaternionToMatrix_one
  exact (Matrix.inv_eq_left_inv h).symm
abbrev _root_.YangMills.SharedProofs.p81137 := @quaternionToMatrix_inv
private theorem gaugeFieldOfTorusField_opposite (A : TorusFieldsAreGaugeFields L m K n) (W : TorusField n)
    (x : TorusSite n) (μ : Fin 4) :
    gaugeFieldOfTorusField L m (K : ℤ) W
        (PeriodicLattice.Bond.forwardFrom (periodicLatticeSite L m (K : ℤ) x) μ).opposite =
      quaternionToMatrix (((W x μ)⁻¹ : UnitQuaternion) : ℍ[ℝ]) := by
  have hr : gaugeFieldOfTorusField L m (K : ℤ) W ∈ compactGaugeFields L m (K : ℤ) := by
    rw [← A.range_gaugeField]
    exact ⟨W, rfl⟩
  rw [hr.2 _ (Set.mem_univ _), A.gaugeField_forwardFrom, quaternionToMatrix_inv]
private theorem specialUnitary_coe_inv' (g : Matrices.ComplexMatrix2.specialUnitary) :
    ((g⁻¹ : Matrices.ComplexMatrix2.specialUnitary) : Matrices.ComplexMatrix2) =
      (g : Matrices.ComplexMatrix2)⁻¹ := by apply _root_.YangMills.Construction.InfiniteLattice.specialUnitary_coe_inv <;> assumption
omit [NeZero n] in
private theorem continuous_gaugeFieldOfTorusField :
    Continuous (gaugeFieldOfTorusField (n := n) L m (K : ℤ)) := by
  have hf : ∀ b : PositivelyOrientedBond L m (K : ℤ),
      Continuous fun W : TorusField n => fieldOnPositiveBond W b := by
    intro b
    exact (map_continuous unitQuaternionEquivSpecialUnitary).comp
      ((continuous_apply _).comp (continuous_apply _))
  refine continuous_pi fun b => ?_
  unfold gaugeFieldOfTorusField gaugeFieldOfPositive
  by_cases h : b.IsPositivelyOriented
  · simp only [dif_pos h]
    exact continuous_subtype_val.comp (hf ⟨b, h⟩)
  · by_cases h' : b.opposite.IsPositivelyOriented
    · simp only [dif_neg h, dif_pos h']
      have e : (fun W : TorusField n =>
            ((fieldOnPositiveBond W ⟨b.opposite, h'⟩ : Matrices.ComplexMatrix2.specialUnitary) :
              Matrices.ComplexMatrix2)⁻¹) =
          fun W => (((fieldOnPositiveBond W ⟨b.opposite, h'⟩)⁻¹ : Matrices.ComplexMatrix2.specialUnitary) :
              Matrices.ComplexMatrix2) :=
        funext fun W => (specialUnitary_coe_inv' _).symm
      rw [e]
      exact continuous_subtype_val.comp (continuous_inv.comp (hf _))
    · simp only [dif_neg h, dif_neg h']
      exact continuous_const
end BondOrientation
section GibbsMeasures
variable {L m K n : ℕ} [NeZero n]
private theorem plaquetteOfOriented_bijective (A : TorusFieldsAreGaugeFields L m K n) :
    Function.Bijective (plaquetteOfOriented L m K (n := n)) := by
  constructor
  · intro q q' h
    have h1 : periodicLatticeSite L m (K : ℤ) q.1.1 = periodicLatticeSite L m (K : ℤ) q'.1.1 :=
      congrArg PeriodicLattice.Plaquette.origin h
    have h2 : q.1.2.1 = q'.1.2.1 := congrArg PeriodicLattice.Plaquette.firstAxis h
    have h3 : q.1.2.2 = q'.1.2.2 := congrArg PeriodicLattice.Plaquette.secondAxis h
    exact Subtype.ext (Prod.ext (A.siteBijective.1 h1) (Prod.ext h2 h3))
  · intro p
    obtain ⟨x, hx⟩ := A.siteBijective.2 p.origin
    exact ⟨⟨(x, p.firstAxis, p.secondAxis), p.firstAxis_lt_secondAxis⟩, PeriodicLattice.Plaquette.ext hx rfl rfl⟩
private theorem plaquetteCost_eq_plaquetteEnergy (h1 : UnitQuaternionHaarTraceNorm)
    (A : TorusFieldsAreGaugeFields L m K n) (W : TorusField n) (q : WeightedResponses.OrientedPlaquette n) :
    plaquetteCost (gaugeFieldOfTorusField L m (K : ℤ) W) (plaquetteOfOriented L m K q) =
      plaquetteEnergy W q.1.1 q.1.2.1 q.1.2.2 := by
  have h := (h1.2.1 (holonomy W q.1.1 q.1.2.1 q.1.2.2)).1
  rw [coe_unitQuaternionEquivSpecialUnitary] at h
  unfold plaquetteCost TorusFields.plaquetteEnergy plaquetteOfOriented
  rw [A.plaquetteHolonomy_eq W q.1.1 q.1.2.1 q.1.2.2 q.2, h]
private theorem smearedObservable_eq_sum (h1 : UnitQuaternionHaarTraceNorm)
    (A : TorusFieldsAreGaugeFields L m K n) (f : FourTorus L m → ℝ) (W : TorusField n) :
    smearedObservable f (gaugeFieldOfTorusField L m (K : ℤ) W) =
      ∑ q : WeightedResponses.OrientedPlaquette n,
        plaquetteEnergy W q.1.1 q.1.2.1 q.1.2.2 * f (plaquetteOfOriented L m K q).barycenter := by
  unfold smearedObservable
  rw [← finsum_comp_equiv (Equiv.ofBijective _ (plaquetteOfOriented_bijective A)), finsum_eq_sum_of_fintype]
  refine Finset.sum_congr rfl fun q _ => ?_
  simp only [Equiv.ofBijective_apply, smul_eq_mul]
  rw [plaquetteCost_eq_plaquetteEnergy h1 A]
private theorem continuous_wilsonAction_univ :
    Continuous (TorusFields.wilsonAction (n := n) Finset.univ) := by
  unfold TorusFields.wilsonAction TorusFields.plaquetteEnergy TorusFields.holonomy
  refine continuous_finsetSum _ fun p _ => continuous_const.sub ?_
  have hq : Continuous fun q : Quaternion ℝ => q.re := Quaternion.continuous_re
  refine hq.comp (continuous_subtype_val.comp ?_)
  fun_prop
abbrev _root_.YangMills.SharedProofs.p11090 := @continuous_wilsonAction_univ
private theorem wilsonWeight_eq_exp (β : ℝ) :
    TorusLumps.wilsonWeight β n = fun W => Real.exp (-β * wilsonAction Finset.univ W) := by
  funext W
  unfold TorusLumps.wilsonWeight
  rw [dif_neg (NeZero.ne n)]
private theorem continuous_wilsonWeight (β : ℝ) : Continuous (TorusLumps.wilsonWeight β n) := by
  rw [wilsonWeight_eq_exp]
  exact Real.continuous_exp.comp (continuous_const.mul continuous_wilsonAction_univ)
private theorem integrable_wilsonWeight (β : ℝ) : Integrable (TorusLumps.wilsonWeight β n) (fieldHaar n) :=
  (continuous_wilsonWeight β).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
private theorem integral_wilsonWeight_pos (β : ℝ) : 0 < ∫ W, TorusLumps.wilsonWeight β n W ∂(fieldHaar n) := by
  have hc := integrable_wilsonWeight (n := n) β
  rw [wilsonWeight_eq_exp] at hc ⊢
  exact integral_exp_pos hc
private theorem wilsonLaw_eq_withDensity (β : ℝ) : WeightedResponses.wilsonLaw β n = (fieldHaar n).withDensity fun W =>
    ENNReal.ofReal (TorusLumps.wilsonWeight β n W / ∫ W', TorusLumps.wilsonWeight β n W' ∂(fieldHaar n)) := by
  simp only [wilsonWeight_eq_exp]
  rfl
private theorem wilsonLaw_isProbabilityMeasure (β : ℝ) : IsProbabilityMeasure (WeightedResponses.wilsonLaw β n) := by
  have hm := integral_wilsonWeight_pos (n := n) β
  have hi : Integrable (fun W => TorusLumps.wilsonWeight β n W /
      ∫ W', TorusLumps.wilsonWeight β n W' ∂(fieldHaar n)) (fieldHaar n) :=
    (integrable_wilsonWeight β).div_const _
  have hn : 0 ≤ᵐ[fieldHaar n] fun W => TorusLumps.wilsonWeight β n W /
      ∫ W', TorusLumps.wilsonWeight β n W' ∂(fieldHaar n) :=
    Filter.Eventually.of_forall fun W => by
      have : 0 ≤ TorusLumps.wilsonWeight β n W := by
        rw [wilsonWeight_eq_exp]
        exact (Real.exp_pos _).le
      exact div_nonneg this hm.le
  constructor
  rw [wilsonLaw_eq_withDensity, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal hi hn, integral_div, div_self hm.ne', ENNReal.ofReal_one]
abbrev _root_.YangMills.SharedProofs.p2076 := @wilsonLaw_isProbabilityMeasure
private theorem wilsonLaw_eq_smul_withDensity (β : ℝ) : WeightedResponses.wilsonLaw β n =
    (ENNReal.ofReal (∫ W, TorusLumps.wilsonWeight β n W ∂(fieldHaar n)))⁻¹ •
      (fieldHaar n).withDensity fun W => ENNReal.ofReal (TorusLumps.wilsonWeight β n W) := by
  have hm : Measurable fun W : TorusField n => ENNReal.ofReal (TorusLumps.wilsonWeight β n W) :=
    ENNReal.measurable_ofReal.comp (continuous_wilsonWeight β).measurable
  rw [← withDensity_smul _ hm, wilsonLaw_eq_withDensity]
  congr 1
  funext W
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [ENNReal.ofReal_div_of_pos (integral_wilsonWeight_pos β), div_eq_mul_inv, mul_comm]
private theorem wilsonGibbsMeasure_eq_map (A : TorusFieldsAreGaugeFields L m K n) (β : ℝ) :
    wilsonGibbsMeasure L m K β =
      (WeightedResponses.wilsonLaw β n).map (gaugeFieldOfTorusField L m (K : ℤ)) := by
  rw [A.wilsonGibbsMeasure_eq β, wilsonLaw_eq_smul_withDensity, Measure.map_smul]
end GibbsMeasures
private theorem flowData_snd_eq_chainFunctional (ℓ : TorusLumps.StepParameters) (β : ℝ) (t : ℕ) :
    (TotalDensityFlow.flowData ℓ β t).2 =
      WeightedResponses.chainFunctional ℓ β (TotalDensityFlow.coupling ℓ β) t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    show TorusLumps.kernelImage ℓ (TotalDensityFlow.flowData ℓ β t).1 (TotalDensityFlow.flowData ℓ β t).2 =
      TorusLumps.kernelImage ℓ (TotalDensityFlow.coupling ℓ β t)
        (WeightedResponses.chainFunctional ℓ β (TotalDensityFlow.coupling ℓ β) t)
    rw [ih]
    rfl
abbrev _root_.YangMills.SharedProofs.p64958 := @flowData_snd_eq_chainFunctional
theorem quaternionModelIsWilsonSU2 (h1 : UnitQuaternionHaarTraceNorm)
    (h2 : WilsonMeasureOnTorusFields)
    (h3 : FourPointCondition.torusUrsellEqWeightedCurvatureStatement)
    (h4 : bottomChainLawIsWilsonGibbsStatement) :
    quaternionModelIsWilsonSU2Statement := by
  refine ⟨⟨fun _ => rfl, h1.1, fun u => ?_, fun u => (h1.2.1 u).2, h1.2.2⟩, ?_, ?_, ?_, h3, h4⟩
  · rw [(h1.2.1 u).1]
  · intro L m K n _ hn hgt
    have A : TorusFieldsAreGaugeFields L m K n := h2 L m K n hn hgt
    have hL := blockFactor_pos hn hgt
    exact
      { fields := A
        site_coe := coe_periodicLatticeSite_apply
        site_add_unitStep := periodicLatticeSite_add_unitStep hn hL
        isPositivelyOriented_iff := isPositivelyOriented_iff_exists A
        forwardFrom_injective := forwardFrom_periodicLatticeSite_injective hn hL hgt A
        xor_opposite := xor_isPositivelyOriented_opposite hn hL hgt
        opposite_eq := gaugeFieldOfTorusField_opposite A
        isClosedEmbedding := continuous_gaugeFieldOfTorusField.isClosedEmbedding A.gaugeField_injective
        plaquette_bijective := plaquetteOfOriented_bijective A
        barycenter_eq := barycenter_plaquetteOfOriented_apply
        plaquetteCost_eq := plaquetteCost_eq_plaquetteEnergy h1 A
        smearedObservable_eq := smearedObservable_eq_sum h1 A
        partition_pos := integral_wilsonWeight_pos
        wilsonLaw_eq := wilsonLaw_eq_withDensity
        wilsonLaw_isProbability := wilsonLaw_isProbabilityMeasure
        wilsonGibbs_isProbability := fun β => by
          have := wilsonLaw_isProbabilityMeasure (n := n) β
          rw [wilsonGibbsMeasure_eq_map A β]
          exact Measure.isProbabilityMeasure_map A.measurable_gaugeField.aemeasurable
        wilsonGibbs_eq_map := wilsonGibbsMeasure_eq_map A }
  · intro L m K hL hm
    refine ⟨by rw [WeightedResponses.fineSide_eq, pow_add]; ring, ?_⟩
    have h1 : 2 ≤ L ^ (m + K) := le_trans hL (Nat.le_self_pow (by omega) L)
    omega
  · intro ℓ β
    exact ⟨rfl, rfl, flowData_snd_eq_chainFunctional ℓ β⟩
end YangMills.Construction.QuaternionModel
end
