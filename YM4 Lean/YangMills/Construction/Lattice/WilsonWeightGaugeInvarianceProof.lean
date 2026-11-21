import YangMills.Construction.SourcesAndGluing.ConfigurationsUnderLatticeSimilaritiesOfToriProof
import YangMills.Construction.Lattice.CommutationOfTheDifferenceWithTheLaplaciansProof
import YangMills.Construction.Lattice.SignAndGaugeInvarianceOfTheActionProof
import YangMills.Construction.Lattice.WilsonWeightGaugeInvariance
import YangMills.Construction.Torus.NeighborCountProof
import Mathlib
open MeasureTheory Set
open scoped ENNReal
noncomputable section
namespace YangMills.Construction.PeriodicLattice.WilsonWeightGaugeInvariance
open Matrices
variable {L m : ℕ} {j : ℤ}
instance : SecondCountableTopology ComplexMatrix2 :=
  inferInstanceAs (SecondCountableTopology (Fin 2 → Fin 2 → ℂ))
theorem compactGaugeGroup_inv_eq_star {A : ComplexMatrix2} (hA : A ∈ compactGaugeGroup) :
    A⁻¹ = star A := by apply _root_.YangMills.Construction.PeriodicLattice.IsometryInvariance.inv_eq_star_of_mem <;> assumption
theorem compactGaugeGroup_inv_mul {A : ComplexMatrix2} (hA : A ∈ compactGaugeGroup) :
    A⁻¹ * A = 1 := by apply _root_.YangMills.SharedProofs.p14555 <;> assumption
theorem compactGaugeGroup_inv_mem {A : ComplexMatrix2} (hA : A ∈ compactGaugeGroup) :
    A⁻¹ ∈ compactGaugeGroup := by apply _root_.YangMills.Construction.PeriodicLattice.BlockAverageContinuity.inv_mem_compactGaugeGroup <;> assumption
theorem coe_specialUnitary_inv (g : ComplexMatrix2.specialUnitary) :
    ((g⁻¹ : ComplexMatrix2.specialUnitary) : ComplexMatrix2) = (g : ComplexMatrix2)⁻¹ := by apply _root_.YangMills.Construction.InfiniteLattice.specialUnitary_coe_inv <;> assumption
theorem compactGaugeGroup_inv_inv {A : ComplexMatrix2} (hA : A ∈ compactGaugeGroup) :
    (A⁻¹)⁻¹ = A := by apply _root_.YangMills.Construction.PeriodicLattice.BlockAverageContinuity.inv_inv_of_mem_compactGaugeGroup <;> assumption
theorem abs_re_fullTrace_le_two {A : ComplexMatrix2} (hA : A ∈ compactGaugeGroup) :
    |(ComplexMatrix2.fullTrace A).re| ≤ 2 := by apply _root_.YangMills.Construction.PeriodicLattice.ActionSign.abs_fullTrace_re_le_two <;> assumption
theorem re_fullTrace_inv {A : ComplexMatrix2} (hA : A ∈ compactGaugeGroup) :
    (ComplexMatrix2.fullTrace A⁻¹).re = (ComplexMatrix2.fullTrace A).re := by apply _root_.YangMills.Construction.SourcesAndGluing.FieldsUnderScaledMotionsOfTori.re_fullTrace_inv <;> assumption
instance : ComplexMatrix2.haarProb.IsMulLeftInvariant := by
  unfold ComplexMatrix2.haarProb
  infer_instance
theorem haarProb_map_mul_left (g : ComplexMatrix2.specialUnitary) :
    ComplexMatrix2.haarProb.map (g * ·) = ComplexMatrix2.haarProb :=
  map_mul_left_eq_self _ g
theorem haarProb_map_mul_right (g : ComplexMatrix2.specialUnitary) :
    ComplexMatrix2.haarProb.map (· * g) = ComplexMatrix2.haarProb := by apply _root_.YangMills.Construction.PeriodicLattice.IsometryInvariance.haarProb_map_mul_right <;> assumption
theorem haarProb_map_left_right (g h : ComplexMatrix2.specialUnitary) :
    ComplexMatrix2.haarProb.map (fun w => g * w * h⁻¹) = ComplexMatrix2.haarProb := by
  have hl : Measurable fun w : ComplexMatrix2.specialUnitary => g * w := measurable_const_mul g
  have hr : Measurable fun w : ComplexMatrix2.specialUnitary => w * h⁻¹ := measurable_mul_const h⁻¹
  have e : (fun w : ComplexMatrix2.specialUnitary => g * w * h⁻¹) =
      (fun w => w * h⁻¹) ∘ fun w => g * w := rfl
  rw [e, ← Measure.map_map hr hl, haarProb_map_mul_left, haarProb_map_mul_right]
theorem addCircle_coe_ne_zero {p x : ℝ} (hx : 0 < x) (hp : x < p) : (x : AddCircle p) ≠ 0 := by apply _root_.YangMills.Construction.Torus.NeighborCount.addCircle_coe_ne_zero_of_lt <;> assumption
theorem siteCount_mul_meshSize (hL : 0 < L) (K : ℕ) :
    ((2 * L ^ (m + K) : ℕ) : ℝ) * meshSize L (K : ℤ) = torusSide L m := by
  simp only [meshSize, torusSide, zpow_neg, zpow_natCast]
  push_cast
  rw [pow_add]
  field_simp
theorem site_finite (hL : 0 < L) (K : ℕ) : Finite (Site L m (K : ℤ)) := by
  set N := 2 * L ^ (m + K) with hN
  have hNpos : 0 < N := by positivity
  let g : (Fin 4 → Fin N) → Site L m (K : ℤ) := fun f =>
    ⟨fun μ => (((((f μ : ℕ) : ℤ) : ℝ) * meshSize L (K : ℤ) : ℝ) : AddCircle (torusSide L m)),
      ⟨fun μ => ((f μ : ℕ) : ℤ), fun _ => rfl⟩⟩
  refine Finite.of_surjective g ?_
  rintro ⟨x, n, hn⟩
  have hNz : (0 : ℤ) < (N : ℤ) := by exact_mod_cast hNpos
  refine ⟨fun μ => ⟨(n μ % (N : ℤ)).toNat, ?_⟩, Subtype.ext (funext fun μ => ?_)⟩
  · have h₁ := Int.emod_nonneg (n μ) hNz.ne'
    have h₂ := Int.emod_lt_of_pos (n μ) hNz
    omega
  · have h₁ := Int.emod_nonneg (n μ) hNz.ne'
    have h₂ : (((n μ % (N : ℤ)).toNat : ℕ) : ℤ) = n μ % (N : ℤ) := Int.toNat_of_nonneg h₁
    change ((((((n μ % (N : ℤ)).toNat : ℕ) : ℤ) : ℝ) * meshSize L (K : ℤ) : ℝ) :
      AddCircle (torusSide L m)) = x μ
    rw [h₂, hn μ, ← sub_eq_zero, ← AddCircle.coe_sub, AddCircle.coe_eq_zero_iff]
    refine ⟨-(n μ / (N : ℤ)), ?_⟩
    have h₃ : (n μ : ℝ) = ((n μ % (N : ℤ) : ℤ) : ℝ) + (N : ℝ) * ((n μ / (N : ℤ) : ℤ) : ℝ) := by
      exact_mod_cast (Int.emod_add_mul_ediv (n μ) (N : ℤ)).symm
    rw [← siteCount_mul_meshSize hL K, ← hN, zsmul_eq_mul, h₃]
    push_cast
    ring
theorem plaquette_finite [Finite (Site L m j)] : Finite (Plaquette L m j) := by apply _root_.YangMills.Construction.GradLaplacianCommutation.plaquette_finite <;> assumption
theorem opposite_not_positivelyOriented (hL : 1 < L) {K : ℕ} (hK : 0 < K) (b : Bond L m (K : ℤ))
    (hb : b.IsPositivelyOriented) : ¬ b.opposite.IsPositivelyOriented := by
  rintro ⟨ν, hν⟩
  obtain ⟨μ, hμ⟩ := hb
  have hL' : (2 : ℝ) ≤ L := by exact_mod_cast hL
  have ha0 : 0 < meshSize L (K : ℤ) := by
    unfold meshSize
    exact zpow_pos (by linarith) _
  have ha1 : 2 * meshSize L (K : ℤ) ≤ 1 := by
    have : (L : ℝ) ^ K ≥ 2 := by
      calc (L : ℝ) ^ K ≥ (L : ℝ) ^ 1 := pow_le_pow_right₀ (by linarith) hK
        _ ≥ 2 := by simpa using hL'
    simp only [meshSize, zpow_neg, zpow_natCast]
    rw [← div_eq_mul_inv]
    rw [div_le_one (by linarith)]
    linarith
  have hside : 2 ≤ torusSide L m := by
    have : (1 : ℝ) ≤ (L : ℝ) ^ m := one_le_pow₀ (by linarith)
    unfold torusSide
    linarith
  have hsum : unitStep L m (K : ℤ) μ + unitStep L m (K : ℤ) ν = 0 := by
    rw [← hμ, ← hν]
    simp [Bond.opposite]
  have hc := congrFun (congrArg Subtype.val hsum) μ
  by_cases h : ν = μ
  · subst h
    have : (((2 * meshSize L (K : ℤ) : ℝ)) : AddCircle (torusSide L m)) = 0 := by
      rw [two_mul, AddCircle.coe_add]
      simpa [unitStep, pointOnAxis] using hc
    exact addCircle_coe_ne_zero (by linarith) (by linarith) this
  · have : ((meshSize L (K : ℤ) : ℝ) : AddCircle (torusSide L m)) = 0 := by
      simpa [unitStep, pointOnAxis, Pi.single_eq_of_ne (Ne.symm h), Pi.single_eq_of_ne h] using hc
    exact addCircle_coe_ne_zero ha0 (by linarith) this
theorem positivelyOriented_or_opposite (b : Bond L m j) :
    b.IsPositivelyOriented ∨ b.opposite.IsPositivelyOriented := by apply _root_.YangMills.SharedProofs.p7155 <;> assumption
theorem gaugeFieldOfPositive_apply_of_pos
    (v : PositivelyOrientedBond L m j → ComplexMatrix2.specialUnitary) {b : Bond L m j}
    (h : b.IsPositivelyOriented) : gaugeFieldOfPositive v b = (v ⟨b, h⟩ : ComplexMatrix2) := by
  simp [gaugeFieldOfPositive, h]
theorem gaugeFieldOfPositive_apply_of_not_pos
    (v : PositivelyOrientedBond L m j → ComplexMatrix2.specialUnitary)
    {b : Bond L m j} (h : ¬ b.IsPositivelyOriented) (h' : b.opposite.IsPositivelyOriented) :
    gaugeFieldOfPositive v b = ((v ⟨b.opposite, h'⟩ : ComplexMatrix2))⁻¹ := by
  simp [gaugeFieldOfPositive, h, h']
theorem gaugeFieldOfPositive_mem
    (hnp : ∀ b : Bond L m j, b.IsPositivelyOriented → ¬ b.opposite.IsPositivelyOriented)
    (v : PositivelyOrientedBond L m j → ComplexMatrix2.specialUnitary) :
    gaugeFieldOfPositive v ∈ compactGaugeFields L m j := by
  refine ⟨fun b _ => ?_, fun b _ => ?_⟩
  · by_cases h : b.IsPositivelyOriented
    · rw [gaugeFieldOfPositive_apply_of_pos v h]
      exact (v _).2
    · have h' := (positivelyOriented_or_opposite b).resolve_left h
      rw [gaugeFieldOfPositive_apply_of_not_pos v h h']
      exact compactGaugeGroup_inv_mem (v _).2
  · by_cases h : b.IsPositivelyOriented
    · have h' := hnp b h
      rw [gaugeFieldOfPositive_apply_of_pos v h,
        gaugeFieldOfPositive_apply_of_not_pos v h' h]
      rfl
    · have h' := (positivelyOriented_or_opposite b).resolve_left h
      rw [gaugeFieldOfPositive_apply_of_pos v h', gaugeFieldOfPositive_apply_of_not_pos v h h',
        compactGaugeGroup_inv_inv (v _).2]
theorem measurable_gaugeFieldOfPositive :
    Measurable (gaugeFieldOfPositive :
      (PositivelyOrientedBond L m j → ComplexMatrix2.specialUnitary) → Bond L m j → ComplexMatrix2) := by apply _root_.YangMills.Construction.PeriodicLattice.IsometryInvariance.measurable_gaugeFieldOfPositive <;> assumption
theorem isClosed_compactGaugeFields : IsClosed (compactGaugeFields L m j) := by apply _root_.YangMills.Construction.PeriodicLattice.isClosed_compactGaugeFields <;> assumption
theorem measurableSet_compactGaugeFields : MeasurableSet (compactGaugeFields L m j) :=
  isClosed_compactGaugeFields.measurableSet
theorem isProbabilityMeasure_productHaarMeasure :
    IsProbabilityMeasure (productHaarMeasure L m j) := by
  have : IsProbabilityMeasure (gaugeFieldHaar L m j) := by
    unfold gaugeFieldHaar ComplexMatrix2.haarPi
    infer_instance
  exact Measure.isProbabilityMeasure_map measurable_gaugeFieldOfPositive.aemeasurable
theorem productHaarMeasure_compl_eq_zero
    (hnp : ∀ b : Bond L m j, b.IsPositivelyOriented → ¬ b.opposite.IsPositivelyOriented) :
    productHaarMeasure L m j (compactGaugeFields L m j)ᶜ = 0 := by
  unfold productHaarMeasure
  rw [Measure.map_apply measurable_gaugeFieldOfPositive
    measurableSet_compactGaugeFields.compl]
  have : gaugeFieldOfPositive ⁻¹' (compactGaugeFields L m j)ᶜ = ∅ := by
    ext v
    simpa using gaugeFieldOfPositive_mem hnp v
  rw [this, measure_empty]
theorem ae_mem_compactGaugeFields
    (hnp : ∀ b : Bond L m j, b.IsPositivelyOriented → ¬ b.opposite.IsPositivelyOriented) :
    ∀ᵐ U ∂productHaarMeasure L m j, U ∈ compactGaugeFields L m j :=
  mem_ae_iff.mpr (productHaarMeasure_compl_eq_zero hnp)
theorem pathHolonomy_mem {U : Bond L m j → ComplexMatrix2} (hU : U ∈ compactGaugeFields L m j)
    (γ : List (Bond L m j)) : pathHolonomy U γ ∈ compactGaugeGroup := by apply _root_.YangMills.Construction.PeriodicLattice.BlockAverageContinuity.pathHolonomy_mem_compactGaugeGroup <;> assumption
theorem pathHolonomy_reversePath {U : Bond L m j → ComplexMatrix2}
    (hU : U ∈ compactGaugeFields L m j) (γ : List (Bond L m j)) :
    pathHolonomy U (reversePath γ) = (pathHolonomy U γ)⁻¹ := by
  induction γ with
  | nil => simp [pathHolonomy, reversePath]
  | cons b γ ih =>
    have e : reversePath (b :: γ) = reversePath γ ++ [b.opposite] := by simp [reversePath]
    have e₁ : pathHolonomy U (reversePath γ ++ [b.opposite]) =
        pathHolonomy U (reversePath γ) * U b.opposite := by
      simp [pathHolonomy]
    have e₂ : pathHolonomy U (b :: γ) = U b * pathHolonomy U γ := by simp [pathHolonomy]
    rw [e, e₁, e₂, ih, hU.2 b (mem_univ _), Matrix.mul_inv_rev]
theorem fullTrace_pathHolonomy_rotate (U : Bond L m j → ComplexMatrix2) (γ : List (Bond L m j))
    (k : ℕ) :
    ComplexMatrix2.fullTrace (pathHolonomy U (γ.rotate k)) =
      ComplexMatrix2.fullTrace (pathHolonomy U γ) := by
  rw [List.rotate_eq_drop_append_take_mod]
  simp only [pathHolonomy, List.map_append, List.prod_append]
  rw [ComplexMatrix2.fullTrace, Matrix.trace_mul_comm, ← List.prod_append, ← List.map_append,
    List.take_append_drop]
theorem plaquetteEnergy_mem_Icc {U : Bond L m j → ComplexMatrix2}
    (hU : U ∈ compactGaugeFields L m j) (p : Plaquette L m j) :
    plaquetteCost U p ∈ Icc (0 : ℝ) 2 := by
  have h := abs_le.mp (abs_re_fullTrace_le_two (pathHolonomy_mem hU p.boundaryBonds))
  have e : plaquetteCost U p =
      1 - (1 / 2) * (ComplexMatrix2.fullTrace (pathHolonomy U p.boundaryBonds)).re := rfl
  rw [e]
  constructor <;> linarith [h.1, h.2]
theorem continuous_plaquetteEnergy (p : Plaquette L m j) :
    Continuous fun U : Bond L m j → ComplexMatrix2 => plaquetteCost U p := by apply _root_.YangMills.Construction.EqualSideGridsAtEveryExponent.continuous_plaquetteCost <;> assumption
theorem continuous_wilsonAction [Finite (Plaquette L m j)] :
    Continuous (wilsonAction : (Bond L m j → ComplexMatrix2) → ℝ) := by
  have := Fintype.ofFinite (Plaquette L m j)
  have e : (wilsonAction : (Bond L m j → ComplexMatrix2) → ℝ) =
      fun U => ∑ p, plaquetteCost U p := by
    funext U
    exact finsum_eq_sum_of_fintype _
  rw [e]
  exact continuous_finsetSum _ fun p _ => continuous_plaquetteEnergy p
theorem continuous_boltzmannWeight [Finite (Plaquette L m j)] (β : ℝ) :
    Continuous (boltzmannWeight β : (Bond L m j → ComplexMatrix2) → ℝ) := by
  unfold boltzmannWeight
  exact Real.continuous_exp.comp (continuous_const.mul continuous_wilsonAction)
theorem abs_wilsonAction_le [Finite (Plaquette L m j)] {U : Bond L m j → ComplexMatrix2}
    (hU : U ∈ compactGaugeFields L m j) :
    |wilsonAction U| ≤ 2 * Nat.card (Plaquette L m j) := by
  have := Fintype.ofFinite (Plaquette L m j)
  have e : wilsonAction U = ∑ p, plaquetteCost U p := finsum_eq_sum_of_fintype _
  have h₀ : 0 ≤ wilsonAction U := by
    rw [e]
    exact Finset.sum_nonneg fun p _ => (plaquetteEnergy_mem_Icc hU p).1
  have h₂ : wilsonAction U ≤ 2 * Nat.card (Plaquette L m j) := by
    rw [e, Nat.card_eq_fintype_card, mul_comm, ← nsmul_eq_mul, Fintype.card]
    exact Finset.sum_le_card_nsmul _ _ _ fun p _ => (plaquetteEnergy_mem_Icc hU p).2
  rwa [abs_of_nonneg h₀]
theorem integrable_boltzmannWeight [Finite (Plaquette L m j)]
    (hnp : ∀ b : Bond L m j, b.IsPositivelyOriented → ¬ b.opposite.IsPositivelyOriented) (β : ℝ) :
    Integrable (boltzmannWeight β : (Bond L m j → ComplexMatrix2) → ℝ)
      (productHaarMeasure L m j) := by
  have := isProbabilityMeasure_productHaarMeasure (L := L) (m := m) (j := j)
  refine Integrable.of_bound (continuous_boltzmannWeight β).measurable.aestronglyMeasurable
    (Real.exp (|β| * (2 * Nat.card (Plaquette L m j)))) ?_
  filter_upwards [ae_mem_compactGaugeFields hnp] with U hU
  unfold boltzmannWeight
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  refine Real.exp_le_exp.mpr ?_
  have h₁ := abs_wilsonAction_le hU
  calc -β * wilsonAction U ≤ |-β * wilsonAction U| := le_abs_self _
    _ = |β| * |wilsonAction U| := by rw [abs_mul, abs_neg]
    _ ≤ _ := by gcongr
theorem gaugeTransform_mem {u : Site L m j → ComplexMatrix2} (hu : IsGaugeMap compactGaugeGroup u)
    {U : Bond L m j → ComplexMatrix2} (hU : U ∈ compactGaugeFields L m j) :
    gaugeTransform u U ∈ compactGaugeFields L m j := by
  refine ⟨fun b _ => ?_, fun b _ => ?_⟩
  · exact Submonoid.mul_mem _ (Submonoid.mul_mem _ (hu _) (hU.1 b (mem_univ _)))
      (compactGaugeGroup_inv_mem (hu _))
  · change u b.target * U b.opposite * (u b.source)⁻¹ =
      (u b.source * U b * (u b.target)⁻¹)⁻¹
    rw [hU.2 b (mem_univ _), Matrix.mul_inv_rev, Matrix.mul_inv_rev,
      compactGaugeGroup_inv_inv (hu _), mul_assoc]
theorem plaquetteHolonomy_gaugeTransform {u : Site L m j → ComplexMatrix2}
    (hu : IsGaugeMap compactGaugeGroup u) (U : Bond L m j → ComplexMatrix2)
    (p : Plaquette L m j) :
    plaquetteHolonomy (gaugeTransform u U) p =
      u p.origin * plaquetteHolonomy U p * (u p.origin)⁻¹ := by
  have cancel : ∀ (x : Site L m j) (X : ComplexMatrix2), (u x)⁻¹ * (u x * X) = X := fun x X => by
    rw [← mul_assoc, compactGaugeGroup_inv_mul (hu x), one_mul]
  have e : p.origin + unitStep L m j p.secondAxis + unitStep L m j p.firstAxis =
      p.origin + unitStep L m j p.firstAxis + unitStep L m j p.secondAxis := add_right_comm _ _ _
  simp only [plaquetteHolonomy, pathHolonomy, Plaquette.boundaryBonds, List.map_cons,
    List.map_nil, List.prod_cons, List.prod_nil, gaugeTransform, Bond.forwardFrom, Bond.opposite,
    mul_one, e, mul_assoc, cancel]
theorem plaquetteEnergy_gaugeTransform {u : Site L m j → ComplexMatrix2}
    (hu : IsGaugeMap compactGaugeGroup u) (U : Bond L m j → ComplexMatrix2)
    (p : Plaquette L m j) :
    plaquetteCost (gaugeTransform u U) p = plaquetteCost U p := by
  unfold plaquetteCost
  rw [plaquetteHolonomy_gaugeTransform hu, ComplexMatrix2.fullTrace, Matrix.trace_mul_comm,
    ← mul_assoc, compactGaugeGroup_inv_mul (hu _), one_mul]
theorem wilsonAction_gaugeTransform {u : Site L m j → ComplexMatrix2}
    (hu : IsGaugeMap compactGaugeGroup u) (U : Bond L m j → ComplexMatrix2) :
    wilsonAction (gaugeTransform u U) = wilsonAction U := by
  unfold wilsonAction
  exact finsum_congr fun p => plaquetteEnergy_gaugeTransform hu U p
theorem boltzmannWeight_gaugeTransform {u : Site L m j → ComplexMatrix2}
    (hu : IsGaugeMap compactGaugeGroup u) (β : ℝ) (U : Bond L m j → ComplexMatrix2) :
    boltzmannWeight β (gaugeTransform u U) = boltzmannWeight β U := by
  unfold boltzmannWeight
  rw [wilsonAction_gaugeTransform hu]
theorem continuous_gaugeTransform (u : Site L m j → ComplexMatrix2) :
    Continuous (gaugeTransform u) := by
  refine continuous_pi fun b => ?_
  unfold gaugeTransform
  exact (continuous_const.matrix_mul (continuous_apply b)).matrix_mul continuous_const
theorem productHaarMeasure_map_gaugeTransform {u : Site L m j → ComplexMatrix2}
    (hu : IsGaugeMap compactGaugeGroup u) :
    (productHaarMeasure L m j).map (gaugeTransform u) = productHaarMeasure L m j := by
  let g : Site L m j → ComplexMatrix2.specialUnitary := fun x => ⟨u x, hu x⟩
  let f : PositivelyOrientedBond L m j → ComplexMatrix2.specialUnitary →
      ComplexMatrix2.specialUnitary :=
    fun b w => g b.1.source * w * (g b.1.target)⁻¹
  let F : (PositivelyOrientedBond L m j → ComplexMatrix2.specialUnitary) →
      PositivelyOrientedBond L m j → ComplexMatrix2.specialUnitary := fun v b => f b (v b)
  have hf : ∀ b, Measurable (f b) := fun b =>
    (measurable_mul_const _).comp (measurable_const_mul _)
  have hF : Measurable F := measurable_pi_lambda _ fun b =>
    (hf b).comp (measurable_pi_apply b)
  have hg : Measurable (gaugeTransform u) := (continuous_gaugeTransform u).measurable
  have key : gaugeTransform u ∘ (gaugeFieldOfPositive (L := L) (m := m) (j := j)) =
      gaugeFieldOfPositive ∘ F := by
    funext v
    funext b
    by_cases h : b.IsPositivelyOriented
    · simp only [Function.comp, gaugeTransform]
      rw [gaugeFieldOfPositive_apply_of_pos v h, gaugeFieldOfPositive_apply_of_pos (F v) h]
      change _ = ((g b.source * v ⟨b, h⟩ * (g b.target)⁻¹ : ComplexMatrix2.specialUnitary) :
        ComplexMatrix2)
      simp only [Submonoid.coe_mul, coe_specialUnitary_inv]
      rfl
    · have h' := (positivelyOriented_or_opposite b).resolve_left h
      simp only [Function.comp, gaugeTransform]
      rw [gaugeFieldOfPositive_apply_of_not_pos v h h',
        gaugeFieldOfPositive_apply_of_not_pos (F v) h h']
      change _ = (((g b.target * v ⟨b.opposite, h'⟩ * (g b.source)⁻¹ :
        ComplexMatrix2.specialUnitary) : ComplexMatrix2))⁻¹
      simp only [Submonoid.coe_mul, coe_specialUnitary_inv]
      change _ = (u b.target * (v ⟨b.opposite, h'⟩ : ComplexMatrix2) * (u b.source)⁻¹)⁻¹
      rw [Matrix.mul_inv_rev, Matrix.mul_inv_rev, compactGaugeGroup_inv_inv (hu _), mul_assoc]
  have hmap : (gaugeFieldHaar L m j).map F = gaugeFieldHaar L m j := by
    unfold gaugeFieldHaar ComplexMatrix2.haarPi
    have e : (fun b => ComplexMatrix2.haarProb.map (f b)) =
        fun _ : PositivelyOrientedBond L m j => ComplexMatrix2.haarProb :=
      funext fun b => haarProb_map_left_right _ _
    have h₁ := Measure.infinitePi_map_pi
      (fun _ : PositivelyOrientedBond L m j => ComplexMatrix2.haarProb) hf
    simp only [e] at h₁
    exact h₁
  unfold productHaarMeasure
  rw [Measure.map_map hg measurable_gaugeFieldOfPositive, key,
    ← Measure.map_map measurable_gaugeFieldOfPositive hF, hmap]
theorem map_withDensity_eq_of_invariant {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {T : α → α} (hT : Measurable T) (hμ : μ.map T = μ) {f : α → ℝ≥0∞} (hf : Measurable f)
    (hfT : ∀ᵐ x ∂μ, f (T x) = f x) : (μ.withDensity f).map T = μ.withDensity f := by
  ext s hs
  rw [Measure.map_apply hT hs, withDensity_apply _ (hT hs), withDensity_apply _ hs]
  calc ∫⁻ x in T ⁻¹' s, f x ∂μ = ∫⁻ x in T ⁻¹' s, f (T x) ∂μ :=
        lintegral_congr_ae (ae_restrict_of_ae (hfT.mono fun x hx => hx.symm))
    _ = ∫⁻ x in s, f x ∂(μ.map T) := (setLIntegral_map hs hf hT).symm
    _ = ∫⁻ x in s, f x ∂μ := by rw [hμ]
theorem statement_holds : statement := by
  intro L m K β hL hm hK
  have hL0 : 0 < L := by omega
  have : Finite (Site L m (K : ℤ)) := site_finite hL0 K
  have : Finite (Plaquette L m (K : ℤ)) := plaquette_finite
  have hnp : ∀ b : Bond L m (K : ℤ), b.IsPositivelyOriented → ¬ b.opposite.IsPositivelyOriented :=
    opposite_not_positivelyOriented hL hK
  have hprob := isProbabilityMeasure_productHaarMeasure (L := L) (m := m) (j := (K : ℤ))
  have hint := integrable_boltzmannWeight hnp β
  have hZ : 0 < partitionFunction L m K β := integral_exp_pos hint
  have hdens : Measurable fun U : Bond L m (K : ℤ) → ComplexMatrix2 =>
      ENNReal.ofReal (boltzmannWeight β U) :=
    ENNReal.measurable_ofReal.comp (continuous_boltzmannWeight β).measurable
  refine ⟨fun U hU p => ⟨plaquetteEnergy_mem_Icc hU p, fun k => ?_,
      pathHolonomy_reversePath hU _, ?_, ?_⟩,
    (continuous_boltzmannWeight β).continuousOn, fun U _ => Real.exp_pos _, hint, hZ, hprob,
    productHaarMeasure_compl_eq_zero hnp, ?_, ?_, fun u hu => ⟨fun U hU =>
      ⟨gaugeTransform_mem hu hU, fun p => ⟨plaquetteHolonomy_gaugeTransform hu U p,
        plaquetteEnergy_gaugeTransform hu U p⟩, wilsonAction_gaugeTransform hu U,
        boltzmannWeight_gaugeTransform hu β U⟩, ?_⟩⟩
  · rw [fullTrace_pathHolonomy_rotate]
    rfl
  · exact compactGaugeGroup_inv_eq_star (pathHolonomy_mem hU _)
  · rw [pathHolonomy_reversePath hU]
    exact re_fullTrace_inv (pathHolonomy_mem hU _)
  · refine ⟨?_⟩
    have hmass : (productHaarMeasure L m (K : ℤ)).withDensity
        (fun U => ENNReal.ofReal (boltzmannWeight β U)) univ =
        ENNReal.ofReal (partitionFunction L m K β) := by
      rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
      exact (ofReal_integral_eq_lintegral_ofReal hint
        (Filter.Eventually.of_forall fun U => (Real.exp_pos _).le)).symm
    unfold wilsonGibbsMeasure
    rw [Measure.smul_apply, hmass, smul_eq_mul]
    exact ENNReal.inv_mul_cancel (by simpa using hZ) ENNReal.ofReal_ne_top
  · unfold wilsonGibbsMeasure
    rw [Measure.smul_apply,
      withDensity_absolutelyContinuous _ _ (productHaarMeasure_compl_eq_zero hnp), smul_zero]
  · have hT : Measurable (gaugeTransform u) := (continuous_gaugeTransform u).measurable
    unfold wilsonGibbsMeasure
    rw [Measure.map_smul, map_withDensity_eq_of_invariant hT
      (productHaarMeasure_map_gaugeTransform hu) hdens
      (Filter.Eventually.of_forall fun U => by rw [boltzmannWeight_gaugeTransform hu])]
end YangMills.Construction.PeriodicLattice.WilsonWeightGaugeInvariance
