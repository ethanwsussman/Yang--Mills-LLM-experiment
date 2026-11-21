import YangMills.Construction.QuaternionicWilsonModel.TheQuaternionModelIsSUTwoWithWilsonsWeightProof
import YangMills.Construction.Towers.WilsonActionIsRealAnalyticOnTheConfigurationsProof
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped ENNReal Quaternion
namespace YangMills.Construction.ClusterExpansionOfAStep
open BlockAverages (UnitQuaternion)
open SoftAverages (quaternionToMatrix quaternionToMatrix_mul)
open Matrices
open PeriodicLattice
section Sites
variable {L m K n : ℕ}
private theorem side_pos_of_eq (hn : n = 2 * L ^ (m + K)) (h2 : 2 < n) : 0 < L := by apply _root_.YangMills.SharedProofs.p82021 <;> assumption
private theorem coe_intMul_eq_iff (hn : n = 2 * L ^ (m + K)) (hL : 0 < L) (a b : ℤ) :
    (((a : ℝ) * meshSize L (K : ℤ) : ℝ) : AddCircle (torusSide L m)) =
        (((b : ℝ) * meshSize L (K : ℤ) : ℝ) : AddCircle (torusSide L m)) ↔ (a : ZMod n) = (b : ZMod n) := by apply _root_.YangMills.SharedProofs.p25868 <;> assumption
private theorem coe_offsetSite (p : Fin 4 → ℤ) (μ : Fin 4) :
    ((offsetSite (0 : Site L m (K : ℤ)) p : Site L m (K : ℤ)) : FourTorus L m) μ =
      (((p μ : ℝ) * meshSize L (K : ℤ) : ℝ) : AddCircle (torusSide L m)) := by apply _root_.YangMills.SharedProofs.p59635 <;> assumption
private theorem offsetSite_add (p q : Fin 4 → ℤ) :
    offsetSite (0 : Site L m (K : ℤ)) (p + q) =
      offsetSite (0 : Site L m (K : ℤ)) p + offsetSite (0 : Site L m (K : ℤ)) q := by
  simp [offsetSite, add_smul, Finset.sum_add_distrib]
private theorem offsetSite_neg (p : Fin 4 → ℤ) :
    offsetSite (0 : Site L m (K : ℤ)) (-p) = -offsetSite (0 : Site L m (K : ℤ)) p := by
  simp [offsetSite, neg_smul, Finset.sum_neg_distrib]
private theorem unitStep_eq_offsetSite (μ : Fin 4) :
    unitStep L m (K : ℤ) μ = offsetSite (0 : Site L m (K : ℤ)) (Pi.single μ 1) := by
  simp [offsetSite, Pi.single_apply, ite_smul]
private theorem offsetSite_eq_iff (hn : n = 2 * L ^ (m + K)) (hL : 0 < L) (p q : Fin 4 → ℤ) :
    offsetSite (0 : Site L m (K : ℤ)) p = offsetSite (0 : Site L m (K : ℤ)) q ↔
      ∀ μ, (p μ : ZMod n) = (q μ : ZMod n) := by
  rw [Subtype.ext_iff, funext_iff]
  simp only [coe_offsetSite, coe_intMul_eq_iff hn hL]
variable [NeZero n]
private theorem coordinate_spec (s : Site L m (K : ℤ)) (μ : Fin 4) :
    (s : FourTorus L m) μ = ((((s.2.choose μ : ℤ) : ℝ) * meshSize L (K : ℤ) : ℝ) : AddCircle (torusSide L m)) :=
  s.2.choose_spec μ
private theorem torusSite_periodicSite (hn : n = 2 * L ^ (m + K)) (hL : 0 < L) (x : TorusFields.TorusSite n) :
    torusSiteOfLatticeSite n (periodicLatticeSite L m (K : ℤ) x) = x := by
  funext μ
  have h := coordinate_spec (L := L) (m := m) (K := K) (periodicLatticeSite L m (K : ℤ) x) μ
  rw [periodicLatticeSite, coe_offsetSite, coe_intMul_eq_iff hn hL, ZMod.intCast_zmod_cast] at h
  exact h.symm
private theorem periodicSite_torusSite (hn : n = 2 * L ^ (m + K)) (hL : 0 < L) (s : Site L m (K : ℤ)) :
    periodicLatticeSite L m (K : ℤ) (torusSiteOfLatticeSite n s) = s := by
  refine Subtype.ext (funext fun μ => ?_)
  rw [periodicLatticeSite, coe_offsetSite, coordinate_spec s μ, coe_intMul_eq_iff hn hL, ZMod.intCast_zmod_cast]
  rfl
private theorem periodicSite_add_unitStep (hn : n = 2 * L ^ (m + K)) (hL : 0 < L) (x : TorusFields.TorusSite n)
    (μ : Fin 4) :
    periodicLatticeSite L m (K : ℤ) (x + TorusFields.unitStep n μ) =
      periodicLatticeSite L m (K : ℤ) x + unitStep L m (K : ℤ) μ := by
  rw [unitStep_eq_offsetSite, periodicLatticeSite, periodicLatticeSite, ← offsetSite_add, offsetSite_eq_iff hn hL]
  intro ν
  simp only [ZMod.intCast_zmod_cast, Pi.add_apply, Int.cast_add, TorusFields.unitStep, Pi.single_apply]
  split_ifs <;> simp
private theorem unitStep_ne_neg (hn : n = 2 * L ^ (m + K)) (hL : 0 < L) (h2 : 2 < n) (μ ν : Fin 4) :
    unitStep L m (K : ℤ) μ ≠ -unitStep L m (K : ℤ) ν := by
  haveI : Fact (1 < n) := ⟨by omega⟩
  intro h
  rw [unitStep_eq_offsetSite, unitStep_eq_offsetSite, ← offsetSite_neg, offsetSite_eq_iff hn hL] at h
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
private theorem unitStep_injective (hn : n = 2 * L ^ (m + K)) (hL : 0 < L) (h2 : 2 < n) {μ ν : Fin 4}
    (h : unitStep L m (K : ℤ) μ = unitStep L m (K : ℤ) ν) : μ = ν := by
  haveI : Fact (1 < n) := ⟨by omega⟩
  by_contra e
  rw [unitStep_eq_offsetSite, unitStep_eq_offsetSite, offsetSite_eq_iff hn hL] at h
  have h3 := h μ
  simp [Pi.single_eq_of_ne e] at h3
private theorem periodicSite_bijective (hn : n = 2 * L ^ (m + K)) (hL : 0 < L) :
    Function.Bijective (periodicLatticeSite (n := n) L m (K : ℤ)) :=
  Function.bijective_iff_has_inverse.mpr
    ⟨torusSiteOfLatticeSite n, torusSite_periodicSite hn hL, periodicSite_torusSite hn hL⟩
end Sites
section Bonds
variable {L m K n : ℕ} [NeZero n]
private theorem coe_inv_specialUnitary (g : ComplexMatrix2.specialUnitary) :
    ((g⁻¹ : ComplexMatrix2.specialUnitary) : ComplexMatrix2) = (g : ComplexMatrix2)⁻¹ := by apply _root_.YangMills.Construction.InfiniteLattice.specialUnitary_coe_inv <;> assumption
private theorem inv_inv_specialUnitary (g : ComplexMatrix2.specialUnitary) :
    ((g : ComplexMatrix2)⁻¹)⁻¹ = (g : ComplexMatrix2) := by
  rw [← coe_inv_specialUnitary, ← coe_inv_specialUnitary, inv_inv]
private theorem inv_mem_specialUnitary {A : ComplexMatrix2} (h : A ∈ ComplexMatrix2.specialUnitary) :
    A⁻¹ ∈ ComplexMatrix2.specialUnitary := by apply _root_.YangMills.Construction.Tower.WilsonAnalyticity.inv_mem_specialUnitary <;> assumption
private theorem positive_or_opposite_positive (b : PeriodicLattice.Bond L m (K : ℤ)) :
    b.IsPositivelyOriented ∨ b.opposite.IsPositivelyOriented := by apply _root_.YangMills.SharedProofs.p39011 <;> assumption
private theorem not_positive_opposite (hn : n = 2 * L ^ (m + K)) (hL : 0 < L) (h2 : 2 < n)
    {b : PeriodicLattice.Bond L m (K : ℤ)} (hb : b.IsPositivelyOriented) : ¬ b.opposite.IsPositivelyOriented := by
  obtain ⟨μ, h⟩ := hb
  rintro ⟨ν, h'⟩
  have h3 : b.source - b.target = unitStep L m (K : ℤ) ν := h'
  rw [← neg_sub, h] at h3
  exact unitStep_ne_neg hn hL h2 ν μ h3.symm
private theorem gaugeFieldOfPositive_of_positive
    (v : PositivelyOrientedBond L m (K : ℤ) → ComplexMatrix2.specialUnitary)
    {b : PeriodicLattice.Bond L m (K : ℤ)} (hb : b.IsPositivelyOriented) :
    gaugeFieldOfPositive v b = (v ⟨b, hb⟩ : ComplexMatrix2) := by
  rw [gaugeFieldOfPositive, dif_pos hb]
private theorem gaugeFieldOfPositive_opposite_of_positive (hn : n = 2 * L ^ (m + K)) (hL : 0 < L) (h2 : 2 < n)
    (v : PositivelyOrientedBond L m (K : ℤ) → ComplexMatrix2.specialUnitary)
    {b : PeriodicLattice.Bond L m (K : ℤ)} (hb : b.IsPositivelyOriented) :
    gaugeFieldOfPositive v b.opposite = (v ⟨b, hb⟩ : ComplexMatrix2)⁻¹ := by
  rw [gaugeFieldOfPositive, dif_neg (not_positive_opposite hn hL h2 hb), dif_pos (by exact hb)]
  rfl
private theorem gaugeFieldOfPositive_mem (hn : n = 2 * L ^ (m + K)) (hL : 0 < L) (h2 : 2 < n)
    (v : PositivelyOrientedBond L m (K : ℤ) → ComplexMatrix2.specialUnitary) (b : PeriodicLattice.Bond L m (K : ℤ)) :
    gaugeFieldOfPositive v b ∈ ComplexMatrix2.specialUnitary := by
  rcases positive_or_opposite_positive b with h | h
  · rw [gaugeFieldOfPositive_of_positive v h]
    exact (v ⟨b, h⟩).2
  · have e : gaugeFieldOfPositive v b = (v ⟨b.opposite, h⟩ : ComplexMatrix2)⁻¹ :=
      gaugeFieldOfPositive_opposite_of_positive hn hL h2 v h
    rw [e]
    exact inv_mem_specialUnitary (v ⟨b.opposite, h⟩).2
private theorem gaugeFieldOfPositive_opposite (hn : n = 2 * L ^ (m + K)) (hL : 0 < L) (h2 : 2 < n)
    (v : PositivelyOrientedBond L m (K : ℤ) → ComplexMatrix2.specialUnitary) (b : PeriodicLattice.Bond L m (K : ℤ)) :
    gaugeFieldOfPositive v b.opposite = (gaugeFieldOfPositive v b)⁻¹ := by
  rcases positive_or_opposite_positive b with h | h
  · rw [gaugeFieldOfPositive_opposite_of_positive hn hL h2 v h, gaugeFieldOfPositive_of_positive v h]
  · have e : gaugeFieldOfPositive v b = (v ⟨b.opposite, h⟩ : ComplexMatrix2)⁻¹ :=
      gaugeFieldOfPositive_opposite_of_positive hn hL h2 v h
    rw [e, gaugeFieldOfPositive_of_positive v h, inv_inv_specialUnitary]
private theorem gaugeFieldOfPositive_injective :
    Function.Injective (gaugeFieldOfPositive (L := L) (m := m) (j := (K : ℤ))) := by
  intro v w h
  funext b
  have := congrFun h b.1
  rw [gaugeFieldOfPositive_of_positive v b.2, gaugeFieldOfPositive_of_positive w b.2] at this
  exact Subtype.ext this
private theorem range_gaugeFieldOfPositive (hn : n = 2 * L ^ (m + K)) (hL : 0 < L) (h2 : 2 < n) :
    Set.range (gaugeFieldOfPositive (L := L) (m := m) (j := (K : ℤ))) = compactGaugeFields L m (K : ℤ) := by
  ext U
  constructor
  · rintro ⟨v, rfl⟩
    exact ⟨fun b _ => gaugeFieldOfPositive_mem hn hL h2 v b, fun b _ => gaugeFieldOfPositive_opposite hn hL h2 v b⟩
  · rintro ⟨h1, h3⟩
    refine ⟨fun b => ⟨U b.1, h1 b.1 trivial⟩, funext fun b => ?_⟩
    rcases positive_or_opposite_positive b with h | h
    · exact gaugeFieldOfPositive_of_positive _ h
    · have e : gaugeFieldOfPositive
          (fun b : PositivelyOrientedBond L m (K : ℤ) => (⟨U b.1, h1 b.1 trivial⟩ : ComplexMatrix2.specialUnitary)) b =
          (U b.opposite)⁻¹ := gaugeFieldOfPositive_opposite_of_positive hn hL h2 _ h
      rw [e, h3 b trivial]
      exact inv_inv_specialUnitary ⟨U b, h1 b trivial⟩
private theorem forwardFrom_positive (s : Site L m (K : ℤ)) (μ : Fin 4) :
    (Bond.forwardFrom s μ).IsPositivelyOriented :=
  ⟨μ, by simp [Bond.forwardFrom]⟩
private theorem axis_of_sub_eq (hn : n = 2 * L ^ (m + K)) (hL : 0 < L) (h2 : 2 < n)
    {b : PeriodicLattice.Bond L m (K : ℤ)} {μ : Fin 4} (hb : b.target - b.source = unitStep L m (K : ℤ) μ) :
    b.axis = μ := by
  rcases b.isNeighbour.choose_spec with h | h
  · exact unitStep_injective hn hL h2 (h.symm.trans hb)
  · exact absurd (hb.symm.trans h) (unitStep_ne_neg hn hL h2 μ _)
private def positiveBondEquiv (hn : n = 2 * L ^ (m + K)) (hL : 0 < L) (h2 : 2 < n) :
    TorusFields.TorusSite n × Fin 4 ≃ PositivelyOrientedBond L m (K : ℤ) where
  toFun p := ⟨Bond.forwardFrom (periodicLatticeSite L m (K : ℤ) p.1) p.2, forwardFrom_positive _ _⟩
  invFun b := (torusSiteOfLatticeSite n b.1.source, b.1.axis)
  left_inv p := by
    refine Prod.ext (torusSite_periodicSite hn hL p.1) ?_
    exact axis_of_sub_eq hn hL h2 (by simp [Bond.forwardFrom])
  right_inv b := by
    obtain ⟨b, μ, h⟩ := b
    refine Subtype.ext (Bond.ext (periodicSite_torusSite hn hL _) ?_)
    show periodicLatticeSite L m (K : ℤ) (torusSiteOfLatticeSite n b.source) + unitStep L m (K : ℤ) b.axis = b.target
    rw [periodicSite_torusSite hn hL, axis_of_sub_eq hn hL h2 h, ← h]
    abel
private theorem fieldOnPositiveBond_eq (hn : n = 2 * L ^ (m + K)) (hL : 0 < L) (h2 : 2 < n)
    (W : TorusFields.TorusField n) (b : PositivelyOrientedBond L m (K : ℤ)) :
    fieldOnPositiveBond W b =
      unitQuaternionEquivSpecialUnitary
        (W ((positiveBondEquiv hn hL h2).symm b).1 ((positiveBondEquiv hn hL h2).symm b).2) := rfl
private theorem fieldOnPositiveBond_equiv (hn : n = 2 * L ^ (m + K)) (hL : 0 < L) (h2 : 2 < n)
    (W : TorusFields.TorusField n) (x : TorusFields.TorusSite n) (μ : Fin 4) :
    fieldOnPositiveBond W (positiveBondEquiv hn hL h2 (x, μ)) = unitQuaternionEquivSpecialUnitary (W x μ) := by
  rw [fieldOnPositiveBond_eq hn hL h2, Equiv.symm_apply_apply]
private theorem torusGauge_forward (hn : n = 2 * L ^ (m + K)) (hL : 0 < L) (h2 : 2 < n)
    (W : TorusFields.TorusField n) (x : TorusFields.TorusSite n) (μ : Fin 4) :
    gaugeFieldOfTorusField L m (K : ℤ) W (Bond.forwardFrom (periodicLatticeSite L m (K : ℤ) x) μ) =
      quaternionToMatrix (W x μ : ℍ[ℝ]) := by
  rw [gaugeFieldOfTorusField, gaugeFieldOfPositive_of_positive _ (forwardFrom_positive _ _)]
  exact congrArg Subtype.val (fieldOnPositiveBond_equiv hn hL h2 W x μ)
private theorem torusGauge_opposite (hn : n = 2 * L ^ (m + K)) (hL : 0 < L) (h2 : 2 < n)
    (W : TorusFields.TorusField n) (b : PeriodicLattice.Bond L m (K : ℤ)) :
    gaugeFieldOfTorusField L m (K : ℤ) W b.opposite = (gaugeFieldOfTorusField L m (K : ℤ) W b)⁻¹ :=
  gaugeFieldOfPositive_opposite hn hL h2 _ b
private theorem torusGauge_opposite_forward (hn : n = 2 * L ^ (m + K)) (hL : 0 < L) (h2 : 2 < n)
    (W : TorusFields.TorusField n) (x : TorusFields.TorusSite n) (μ : Fin 4) :
    gaugeFieldOfTorusField L m (K : ℤ) W (Bond.forwardFrom (periodicLatticeSite L m (K : ℤ) x) μ).opposite =
      (quaternionToMatrix (W x μ : ℍ[ℝ]))⁻¹ := by
  rw [torusGauge_opposite hn hL h2, torusGauge_forward hn hL h2]
private theorem quaternionToMatrix_inv (u : UnitQuaternion) :
    quaternionToMatrix ((u⁻¹ : UnitQuaternion) : ℍ[ℝ]) = (quaternionToMatrix (u : ℍ[ℝ]))⁻¹ := by apply _root_.YangMills.SharedProofs.p81137 <;> assumption
private theorem torusGauge_plaquette (hn : n = 2 * L ^ (m + K)) (hL : 0 < L) (h2 : 2 < n)
    (W : TorusFields.TorusField n) (x : TorusFields.TorusSite n) (μ ν : Fin 4) (h : μ < ν) :
    plaquetteHolonomy (gaugeFieldOfTorusField L m (K : ℤ) W) ⟨periodicLatticeSite L m (K : ℤ) x, μ, ν, h⟩ =
      quaternionToMatrix (TorusFields.holonomy W x μ ν : ℍ[ℝ]) := by
  simp only [plaquetteHolonomy, pathHolonomy, Plaquette.boundaryBonds, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, mul_one]
  rw [← periodicSite_add_unitStep hn hL, ← periodicSite_add_unitStep hn hL, torusGauge_forward hn hL h2,
    torusGauge_forward hn hL h2, torusGauge_opposite_forward hn hL h2, torusGauge_opposite_forward hn hL h2]
  simp only [TorusFields.holonomy, Submonoid.coe_mul, quaternionToMatrix_mul, quaternionToMatrix_inv, mul_assoc]
private theorem eq_forward_or_opposite (hn : n = 2 * L ^ (m + K)) (hL : 0 < L) (h2 : 2 < n)
    (b : PeriodicLattice.Bond L m (K : ℤ)) : ∃ (x : TorusFields.TorusSite n) (μ : Fin 4),
      b = Bond.forwardFrom (periodicLatticeSite L m (K : ℤ) x) μ ∨
        b = (Bond.forwardFrom (periodicLatticeSite L m (K : ℤ) x) μ).opposite := by
  rcases positive_or_opposite_positive b with h | h
  · obtain ⟨p, hp⟩ := (positiveBondEquiv (K := K) hn hL h2).surjective ⟨b, h⟩
    exact ⟨p.1, p.2, Or.inl (congrArg Subtype.val hp).symm⟩
  · obtain ⟨p, hp⟩ := (positiveBondEquiv (K := K) hn hL h2).surjective ⟨b.opposite, h⟩
    refine ⟨p.1, p.2, Or.inr ?_⟩
    have h3 : Bond.forwardFrom (periodicLatticeSite L m (K : ℤ) p.1) p.2 = b.opposite := congrArg Subtype.val hp
    rw [h3]
    rfl
end Bonds
section Measure
variable {L m K n : ℕ} [NeZero n]
private theorem continuous_pathHolonomy (Γ : List (PeriodicLattice.Bond L m (K : ℤ))) :
    Continuous fun U : PeriodicLattice.Bond L m (K : ℤ) → ComplexMatrix2 => pathHolonomy U Γ := by
  induction Γ with
  | nil => exact continuous_const
  | cons b Γ ih =>
    simp only [pathHolonomy, List.map_cons, List.prod_cons] at ih ⊢
    exact (continuous_apply b).matrix_mul ih
private def plaquetteEquiv (hn : n = 2 * L ^ (m + K)) (hL : 0 < L) :
    {p : TorusFields.TorusPlaquette n // p.2.1 < p.2.2} ≃ Plaquette L m (K : ℤ) where
  toFun p := ⟨periodicLatticeSite L m (K : ℤ) p.1.1, p.1.2.1, p.1.2.2, p.2⟩
  invFun p := ⟨(torusSiteOfLatticeSite n p.origin, p.firstAxis, p.secondAxis), p.firstAxis_lt_secondAxis⟩
  left_inv p := Subtype.ext (Prod.ext (torusSite_periodicSite hn hL _) rfl)
  right_inv p := Plaquette.ext (periodicSite_torusSite hn hL _) rfl rfl
private theorem wilsonAction_eq_sum (hn : n = 2 * L ^ (m + K)) (hL : 0 < L)
    (U : PeriodicLattice.Bond L m (K : ℤ) → ComplexMatrix2) :
    PeriodicLattice.wilsonAction U =
      ∑ p : {p : TorusFields.TorusPlaquette n // p.2.1 < p.2.2}, plaquetteCost U (plaquetteEquiv hn hL p) := by
  rw [PeriodicLattice.wilsonAction, ← finsum_comp_equiv (plaquetteEquiv hn hL), finsum_eq_sum_of_fintype]
private theorem measurable_boltzmannWeight (hn : n = 2 * L ^ (m + K)) (hL : 0 < L) (β : ℝ) :
    Measurable (boltzmannWeight (L := L) (m := m) (j := (K : ℤ)) β) := by
  have hw : Continuous (PeriodicLattice.wilsonAction (L := L) (m := m) (j := (K : ℤ))) := by
    have : PeriodicLattice.wilsonAction (L := L) (m := m) (j := (K : ℤ)) = fun U =>
        ∑ p : {p : TorusFields.TorusPlaquette n // p.2.1 < p.2.2}, plaquetteCost U (plaquetteEquiv hn hL p) :=
      funext (wilsonAction_eq_sum hn hL)
    rw [this]
    refine continuous_finset_sum _ fun p _ => ?_
    exact continuous_const.sub (continuous_const.mul
      (Complex.continuous_re.comp (continuous_pathHolonomy _).matrix_trace))
  haveI : SecondCountableTopology ComplexMatrix2 := inferInstanceAs (SecondCountableTopology (Fin 2 → Fin 2 → ℂ))
  exact (Real.continuous_exp.comp (continuous_const.mul hw)).measurable
private theorem measurable_gaugeFieldOfPositive :
    Measurable (gaugeFieldOfPositive (L := L) (m := m) (j := (K : ℤ))) := by
  refine measurable_pi_iff.mpr fun b => ?_
  unfold gaugeFieldOfPositive
  by_cases h : b.IsPositivelyOriented
  · simp only [dif_pos h]
    exact continuous_subtype_val.measurable.comp (measurable_pi_apply _)
  · by_cases h' : b.opposite.IsPositivelyOriented
    · simp only [dif_neg h, dif_pos h']
      have e : (fun v : PositivelyOrientedBond L m (K : ℤ) → ComplexMatrix2.specialUnitary =>
            ((v ⟨b.opposite, h'⟩ : ComplexMatrix2))⁻¹) =
          fun v => (((v ⟨b.opposite, h'⟩)⁻¹ : ComplexMatrix2.specialUnitary) : ComplexMatrix2) :=
        funext fun v => (coe_inv_specialUnitary _).symm
      rw [e]
      exact (continuous_subtype_val.comp continuous_inv).measurable.comp (measurable_pi_apply _)
    · simp only [dif_neg h, dif_neg h']
      exact measurable_const
private theorem measurable_fieldOnPositiveBond :
    Measurable fun W : TorusFields.TorusField n =>
      (fieldOnPositiveBond W : PositivelyOrientedBond L m (K : ℤ) → ComplexMatrix2.specialUnitary) := by
  refine measurable_pi_iff.mpr fun b => ?_
  exact unitQuaternionEquivSpecialUnitary.continuous.measurable.comp
    ((measurable_pi_apply _).comp (measurable_pi_apply _))
private theorem measurable_torusGauge :
    Measurable (gaugeFieldOfTorusField (n := n) L m (K : ℤ)) :=
  measurable_gaugeFieldOfPositive.comp measurable_fieldOnPositiveBond
private theorem map_fieldHaar_positive
    (h1 : TorusFields.haarUnit.map unitQuaternionEquivSpecialUnitary = ComplexMatrix2.haarProb)
    (hn : n = 2 * L ^ (m + K)) (hL : 0 < L) (h2 : 2 < n) :
    (TorusFields.fieldHaar n).map (fun W : TorusFields.TorusField n =>
        (fieldOnPositiveBond W : PositivelyOrientedBond L m (K : ℤ) → ComplexMatrix2.specialUnitary)) =
      gaugeFieldHaar L m (K : ℤ) := by
  haveI : Finite (PositivelyOrientedBond L m (K : ℤ)) := Finite.of_equiv _ (positiveBondEquiv hn hL h2)
  letI : Fintype (PositivelyOrientedBond L m (K : ℤ)) := Fintype.ofFinite _
  have hm : Measurable unitQuaternionEquivSpecialUnitary := unitQuaternionEquivSpecialUnitary.continuous.measurable
  have hh : ∀ A : Set ComplexMatrix2.specialUnitary, MeasurableSet A →
      TorusFields.haarUnit (unitQuaternionEquivSpecialUnitary ⁻¹' A) = ComplexMatrix2.haarProb A :=
    fun A hA => by rw [← h1, Measure.map_apply hm hA]
  rw [gaugeFieldHaar, ComplexMatrix2.haarPi, Measure.infinitePi_eq_pi]
  symm
  refine Measure.pi_eq fun t ht => ?_
  rw [Measure.map_apply measurable_fieldOnPositiveBond (MeasurableSet.univ_pi ht)]
  have hset : (fun W : TorusFields.TorusField n =>
        (fieldOnPositiveBond W : PositivelyOrientedBond L m (K : ℤ) → ComplexMatrix2.specialUnitary)) ⁻¹'
      Set.pi Set.univ t = Set.pi Set.univ fun x => Set.pi Set.univ fun μ =>
        unitQuaternionEquivSpecialUnitary ⁻¹' t (positiveBondEquiv hn hL h2 (x, μ)) := by
    ext W
    simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, forall_true_left]
    constructor
    · intro h x μ
      have := h (positiveBondEquiv hn hL h2 (x, μ))
      rwa [fieldOnPositiveBond_equiv hn hL h2] at this
    · intro h b
      obtain ⟨p, rfl⟩ := (positiveBondEquiv hn hL h2).surjective b
      rw [fieldOnPositiveBond_equiv hn hL h2]
      exact h p.1 p.2
  rw [hset, TorusFields.fieldHaar, Measure.pi_pi]
  simp_rw [Measure.pi_pi, hh _ (ht _)]
  rw [← Fintype.prod_prod_type
    (f := fun p : TorusFields.TorusSite n × Fin 4 => ComplexMatrix2.haarProb (t (positiveBondEquiv hn hL h2 p)))]
  exact Fintype.prod_equiv (positiveBondEquiv hn hL h2) _ _ fun _ => rfl
end Measure
theorem wilsonMeasureOnTorusFields (h1 : UnitQuaternionHaarTraceNorm) :
    WilsonMeasureOnTorusFields := by
  intro L m K n _ hn h2
  have hL := side_pos_of_eq hn h2
  have hmc : Measurable (gaugeFieldOfTorusField (n := n) L m (K : ℤ)) := measurable_torusGauge
  have hfield : Function.Bijective
      fun W : TorusFields.TorusField n =>
        (fieldOnPositiveBond W : PositivelyOrientedBond L m (K : ℤ) → ComplexMatrix2.specialUnitary) := by
    refine Function.bijective_iff_has_inverse.mpr
      ⟨fun v x μ => unitQuaternionEquivSpecialUnitary.symm (v (positiveBondEquiv hn hL h2 (x, μ))), ?_, ?_⟩
    · intro W
      funext x μ
      simp only [fieldOnPositiveBond_equiv hn hL h2, ContinuousMulEquiv.symm_apply_apply]
    · intro v
      funext b
      obtain ⟨p, rfl⟩ := (positiveBondEquiv hn hL h2).surjective b
      simp only [fieldOnPositiveBond_equiv hn hL h2, Prod.mk.eta,
        ContinuousMulEquiv.apply_symm_apply]
  have haction : ∀ W : TorusFields.TorusField n,
      PeriodicLattice.wilsonAction (gaugeFieldOfTorusField L m (K : ℤ) W) = TorusFields.wilsonAction Finset.univ W := by
    intro W
    rw [wilsonAction_eq_sum hn hL, TorusFields.wilsonAction]
    classical
    rw [Finset.sum_subtype (TorusFields.plaquettesIn (Finset.univ : Finset (TorusFields.TorusSite n)))
      (p := fun p : TorusFields.TorusPlaquette n => p.2.1 < p.2.2)
      (by intro p; simp [TorusFields.plaquettesIn])]
    refine Finset.sum_congr rfl fun p _ => ?_
    obtain ⟨⟨x, μ, ν⟩, h⟩ := p
    show plaquetteCost _ ⟨periodicLatticeSite L m (K : ℤ) x, μ, ν, h⟩ = _
    have := (h1.2.1 (TorusFields.holonomy W x μ ν)).1
    rw [coe_unitQuaternionEquivSpecialUnitary] at this
    rw [plaquetteCost, torusGauge_plaquette hn hL h2, TorusFields.plaquetteEnergy, this]
  have hdensity : ∀ (β : ℝ) (W : TorusFields.TorusField n),
      boltzmannWeight β (gaugeFieldOfTorusField L m (K : ℤ) W) = TorusLumps.wilsonWeight β n W := by
    intro β W
    rw [boltzmannWeight, haction, TorusLumps.wilsonWeight, dif_neg (NeZero.ne n)]
  have hhaar : (TorusFields.fieldHaar n).map (gaugeFieldOfTorusField L m (K : ℤ)) =
      productHaarMeasure L m (K : ℤ) := by
    rw [productHaarMeasure, ← map_fieldHaar_positive h1.1 hn hL h2,
      Measure.map_map measurable_gaugeFieldOfPositive measurable_fieldOnPositiveBond]
    rfl
  have hmass : ∀ β : ℝ,
      partitionFunction L m K β = ∫ W, TorusLumps.wilsonWeight β n W ∂(TorusFields.fieldHaar n) := by
    intro β
    rw [partitionFunction, ← hhaar,
      integral_map hmc.aemeasurable (measurable_boltzmannWeight hn hL β).aestronglyMeasurable]
    exact integral_congr_ae (Filter.Eventually.of_forall fun W => hdensity β W)
  refine
    { siteBijective := periodicSite_bijective hn hL
      torusSite_periodicLatticeSite := torusSite_periodicSite hn hL
      gaugeField_injective := gaugeFieldOfPositive_injective.comp hfield.1
      range_gaugeField := ?_
      gaugeField_forwardFrom := torusGauge_forward hn hL h2
      plaquetteHolonomy_eq := torusGauge_plaquette hn hL h2
      gaugeTransform_eq := ?_
      wilsonAction_eq := haction
      measurable_gaugeField := hmc
      map_fieldHaar := hhaar
      boltzmannWeight_eq := hdensity
      partitionFunction_eq := hmass
      wilsonGibbsMeasure_eq := ?_ }
  · have : gaugeFieldOfTorusField (n := n) L m (K : ℤ) =
        gaugeFieldOfPositive ∘ fun W : TorusFields.TorusField n =>
          (fieldOnPositiveBond W : PositivelyOrientedBond L m (K : ℤ) → ComplexMatrix2.specialUnitary) := rfl
    rw [this, Set.range_comp, hfield.2.range_eq, Set.image_univ, range_gaugeFieldOfPositive hn hL h2]
  · intro g W
    funext b
    have hg : ∀ x : TorusFields.TorusSite n, ∀ s : Site L m (K : ℤ), s = periodicLatticeSite L m (K : ℤ) x →
        quaternionToMatrix (g (torusSiteOfLatticeSite n s) : ℍ[ℝ]) = quaternionToMatrix (g x : ℍ[ℝ]) := by
      rintro x s rfl
      rw [torusSite_periodicSite hn hL]
    have hfw : ∀ (x : TorusFields.TorusSite n) (μ : Fin 4),
        gaugeFieldOfTorusField L m (K : ℤ) (TorusFields.gaugeTransform g W)
            (Bond.forwardFrom (periodicLatticeSite L m (K : ℤ) x) μ) =
          quaternionToMatrix (g x : ℍ[ℝ]) * quaternionToMatrix (W x μ : ℍ[ℝ]) *
            (quaternionToMatrix (g (x + TorusFields.unitStep n μ) : ℍ[ℝ]))⁻¹ := by
      intro x μ
      rw [torusGauge_forward hn hL h2]
      simp only [TorusFields.gaugeTransform, Submonoid.coe_mul, quaternionToMatrix_mul, quaternionToMatrix_inv]
    obtain ⟨x, μ, rfl | rfl⟩ := eq_forward_or_opposite (K := K) hn hL h2 b
    · rw [hfw, PeriodicLattice.gaugeTransform, torusGauge_forward hn hL h2]
      simp only [Bond.forwardFrom]
      rw [hg x _ rfl, hg (x + TorusFields.unitStep n μ) _ (periodicSite_add_unitStep hn hL x μ).symm]
    · rw [torusGauge_opposite hn hL h2, hfw, PeriodicLattice.gaugeTransform, torusGauge_opposite_forward hn hL h2]
      simp only [Bond.opposite, Bond.forwardFrom]
      rw [hg x _ rfl, hg (x + TorusFields.unitStep n μ) _ (periodicSite_add_unitStep hn hL x μ).symm]
      rw [Matrix.mul_inv_rev, Matrix.mul_inv_rev, mul_assoc]
      have hii := inv_inv_specialUnitary (unitQuaternionEquivSpecialUnitary (g (x + TorusFields.unitStep n μ)))
      rw [coe_unitQuaternionEquivSpecialUnitary] at hii
      rw [hii]
  · intro β
    rw [wilsonGibbsMeasure, hmass, ← hhaar]
    congr 1
    ext A hA
    have hf : Measurable fun U =>
        ENNReal.ofReal (boltzmannWeight (L := L) (m := m) (j := (K : ℤ)) β U) :=
      (measurable_boltzmannWeight hn hL β).ennreal_ofReal
    rw [withDensity_apply _ hA, Measure.map_apply hmc hA, withDensity_apply _ (hmc hA),
      setLIntegral_map hA hf hmc]
    simp_rw [hdensity]
end YangMills.Construction.ClusterExpansionOfAStep
end
