import YangMills.Construction.InfiniteLattice.PlaquetteFunctionAndActionOfTheIsometriesProof
import YangMills.Construction.Lattice.ConfigurationsAreAProduct
import YangMills.Construction.Lattice.CountingSitesBondsPlaquettes
import YangMills.Construction.Matrices.FiniteProductOfSpecialUnitary
import Mathlib
set_option autoImplicit false
open MeasureTheory Set
noncomputable section
namespace YangMills.Construction.GaugeFieldProduct
open YangMills.Construction.PeriodicLattice YangMills.Construction.Matrices
variable {L m : ℕ} {j : ℤ}
theorem torusSide_div_meshSize (hL : 0 < L) :
    torusSide L m / meshSize L j = 2 * (L : ℝ) ^ ((m : ℤ) + j) := by
  have hL' : (L : ℝ) ≠ 0 := by exact_mod_cast hL.ne'
  rw [torusSide, meshSize, zpow_neg, div_inv_eq_mul, zpow_add₀ hL', zpow_natCast]
  ring
theorem meshSize_pos (hL : 0 < L) : 0 < meshSize L j := by apply _root_.YangMills.SharedProofs.p16883 <;> assumption
theorem one_lt_zpow_exponent (h1 : 1 < L) (hk : 0 < (m : ℤ) + j) :
    (1 : ℝ) < (L : ℝ) ^ ((m : ℤ) + j) :=
  one_lt_zpow₀ (by exact_mod_cast h1) hk
theorem two_mul_meshSize_lt_torusSide (h1 : 1 < L) (hk : 0 < (m : ℤ) + j) :
    2 * meshSize L j < torusSide L m := by
  have hL : 0 < L := by omega
  have hs := meshSize_pos (j := j) hL
  have hgt := one_lt_zpow_exponent (m := m) (j := j) h1 hk
  have h := torusSide_div_meshSize (m := m) (j := j) hL
  rw [div_eq_iff hs.ne'] at h
  rw [h]
  nlinarith
theorem not_isPositivelyOriented_opposite (h1 : 1 < L) (hk : 0 < (m : ℤ) + j) {b : Bond L m j}
    (hb : b.IsPositivelyOriented) : ¬ b.opposite.IsPositivelyOriented := by apply _root_.YangMills.Construction.PeriodicLattice.Counting.not_isPositivelyOriented_opposite <;> assumption
theorem isPositivelyOriented_or_opposite (b : Bond L m j) :
    b.IsPositivelyOriented ∨ b.opposite.IsPositivelyOriented := by apply _root_.YangMills.SharedProofs.p7155 <;> assumption
theorem meshAndOrientation (h1 : 1 < L) (hk : 0 < (m : ℤ) + j) :
    MeshAndOrientation L m j := by
  have hL : 0 < L := by omega
  have hs := meshSize_pos (j := j) hL
  refine ⟨torusSide_div_meshSize hL, ?_, hs, by linarith, two_mul_meshSize_lt_torusSide h1 hk,
    fun b => ?_⟩
  · have := one_lt_zpow_exponent (m := m) (j := j) h1 hk
    linarith
  · rcases em b.IsPositivelyOriented with h | h
    · exact Or.inl ⟨h, not_isPositivelyOriented_opposite h1 hk h⟩
    · exact Or.inr ⟨(isPositivelyOriented_or_opposite b).resolve_left h, h⟩
theorem finiteAndNonempty (hcounts : SiteAndPlaquetteCounts) (h1 : 1 < L)
    (hk : 0 < (m : ℤ) + j) : FiniteAndNonempty L m j := by
  have hL : 0 < L := by omega
  obtain ⟨-, -, hsite, hplaq, -, hrest⟩ := hcounts L m j hL (by omega)
  have hN : 0 < 2 * L ^ ((m : ℤ) + j).toNat := Nat.mul_pos two_pos (pow_pos hL _)
  refine ⟨⟨Nat.finite_of_card_ne_zero ?_, ⟨0⟩⟩,
    ⟨(hrest h1 hk).1, ⟨⟨Bond.forwardFrom 0 0, 0, ?_⟩⟩⟩,
    ⟨Nat.finite_of_card_ne_zero ?_, ⟨⟨0, 0, 1, by decide⟩⟩⟩⟩
  · rw [hsite]
    exact (pow_pos hN 4).ne'
  · simp [Bond.forwardFrom]
  · rw [hplaq]
    exact (Nat.mul_pos (by norm_num) (pow_pos hN 4)).ne'
theorem gaugeFieldOfPositive_apply
    (v : PositivelyOrientedBond L m j → ComplexMatrix2.specialUnitary) {b : Bond L m j}
    (h : b.IsPositivelyOriented) : gaugeFieldOfPositive v b = (v ⟨b, h⟩ : ComplexMatrix2) := by
  simp only [gaugeFieldOfPositive, dif_pos h]
def gaugeFieldWithValues
    (hr : range (gaugeFieldOfPositive :
      (PositivelyOrientedBond L m j → ComplexMatrix2.specialUnitary) → _) =
      compactGaugeFields L m j)
    (v : PositivelyOrientedBond L m j → ComplexMatrix2.specialUnitary) :
    CompactGaugeField L m j :=
  (⟨gaugeFieldOfPositive v, hr ▸ mem_range_self v⟩ : ↥(compactGaugeFields L m j))
theorem restrictToPositiveBonds_eq
    (v : PositivelyOrientedBond L m j → ComplexMatrix2.specialUnitary)
    (U : CompactGaugeField L m j) (hU : U.1 = gaugeFieldOfPositive v) :
    restrictToPositiveBonds U = v := by
  funext b
  apply Subtype.ext
  change U.1 b.1 = _
  rw [hU, gaugeFieldOfPositive_apply v b.2]
theorem continuous_linkValue (b : Bond L m j) :
    Continuous (fun U : CompactGaugeField L m j => CompactGaugeField.linkValue U b) := by apply _root_.YangMills.Construction.InfiniteLattice.FaceEnergyAndMotions.continuous_linkValue <;> assumption
theorem continuous_restrictToPositiveBonds :
    Continuous (restrictToPositiveBonds : CompactGaugeField L m j → _) :=
  continuous_pi fun b => continuous_linkValue b.1
def restrictHomeomorph
    (hr : range (gaugeFieldOfPositive :
      (PositivelyOrientedBond L m j → ComplexMatrix2.specialUnitary) → _) =
      compactGaugeFields L m j)
    (hc : Continuous (gaugeFieldOfPositive :
      (PositivelyOrientedBond L m j → ComplexMatrix2.specialUnitary) → Bond L m j → ComplexMatrix2)) :
    CompactGaugeField L m j ≃ₜ (PositivelyOrientedBond L m j → ComplexMatrix2.specialUnitary) where
  toFun := restrictToPositiveBonds
  invFun := gaugeFieldWithValues hr
  left_inv U := by
    have hU : U.1 ∈ range (gaugeFieldOfPositive :
        (PositivelyOrientedBond L m j → ComplexMatrix2.specialUnitary) → _) := by
      rw [hr]
      exact U.2
    obtain ⟨w, hw⟩ := hU
    have hv := restrictToPositiveBonds_eq w U hw.symm
    apply Subtype.ext
    change gaugeFieldOfPositive (restrictToPositiveBonds U) = U.1
    rw [hv, hw]
  right_inv v := restrictToPositiveBonds_eq v _ rfl
  continuous_toFun := continuous_restrictToPositiveBonds
  continuous_invFun := by
    refine continuous_iInf_rng.2 fun b => continuous_induced_rng.2 ?_
    exact ((continuous_apply b).comp hc).subtype_mk _
theorem borelSpace_pi (hgroup : ComplexMatrix2.FiniteProductGroupStatement) (S : Type)
    [Finite S] : BorelSpace (S → ComplexMatrix2.specialUnitary) :=
  ⟨(hgroup.2.1 S).1.symm⟩
theorem productStructure (hgroup : ComplexMatrix2.FiniteProductGroupStatement)
    (hcounts : SiteAndPlaquetteCounts) (h1 : 1 < L) (hk : 0 < (m : ℤ) + j) :
    ProductStructure L m j := by
  have hL : 0 < L := by omega
  obtain ⟨-, -, -, -, -, hrest⟩ := hcounts L m j hL (by omega)
  obtain ⟨hfin, hemb, hr, -, -⟩ := hrest h1 hk
  have hc := hemb.continuous
  let e := restrictHomeomorph hr hc
  have hcoe : ⇑e = restrictToPositiveBonds := rfl
  have hborel := borelSpace_pi hgroup (PositivelyOrientedBond L m j)
  obtain ⟨-, -, hmetr⟩ := hgroup.1 (PositivelyOrientedBond L m j)
  have hprob : IsProbabilityMeasure (ComplexMatrix2.haarPi (PositivelyOrientedBond L m j)) :=
    (hgroup.2.1 (PositivelyOrientedBond L m j)).2.2.1
  have hme : Measurable (e : CompactGaugeField L m j → _) := e.continuous.measurable
  have hms : Measurable (e.symm : _ → CompactGaugeField L m j) := e.symm.continuous.measurable
  have hex : IsProductHaarImage L m j
      ((ComplexMatrix2.haarPi (PositivelyOrientedBond L m j)).map e.symm) := by
    unfold IsProductHaarImage
    rw [← hcoe, Measure.map_map hme hms]
    have : (e ∘ e.symm) = id := funext e.apply_symm_apply
    rw [this, Measure.map_id]
  have huniq : ∀ μ μ' : Measure (CompactGaugeField L m j), IsProductHaarImage L m j μ →
      IsProductHaarImage L m j μ' → μ = μ' := by
    intro μ μ' h h'
    have hmap : μ.map e = μ'.map e := by
      rw [hcoe]
      exact h.trans h'.symm
    have hback : ∀ ν : Measure (CompactGaugeField L m j), (ν.map e).map e.symm = ν := by
      intro ν
      rw [Measure.map_map hms hme]
      have : (e.symm ∘ e) = id := funext e.symm_apply_apply
      rw [this, Measure.map_id]
    rw [← hback μ, hmap, hback μ']
  have hspec : IsProductHaarImage L m j (gaugeFieldMeasure L m j) :=
    Classical.epsilon_spec (p := IsProductHaarImage L m j) ⟨_, hex⟩
  refine ⟨e.bijective, ⟨e, hcoe⟩, e.symm.compactSpace, e.isEmbedding.metrizableSpace,
    ⟨_, hex, fun μ hμ => huniq _ _ hμ hex⟩, hspec, ⟨?_⟩⟩
  have hmap := Measure.map_apply (μ := gaugeFieldMeasure L m j) hme MeasurableSet.univ
  rw [preimage_univ] at hmap
  rw [← hmap]
  change ((gaugeFieldMeasure L m j).map restrictToPositiveBonds) univ = 1
  rw [hspec]
  exact measure_univ
theorem coe_inv_specialUnitary (U : ComplexMatrix2.specialUnitary) :
    (U : ComplexMatrix2)⁻¹ = ((U⁻¹ : ComplexMatrix2.specialUnitary) : ComplexMatrix2) := by apply _root_.YangMills.Construction.PeriodicLattice.WilsonPlaquetteSum.coe_inv_specialUnitary <;> assumption
theorem fullTrace_real_mem_Icc (g : ComplexMatrix2.specialUnitary) :
    ∃ t : ℝ, t ∈ Icc (-2 : ℝ) 2 ∧ ComplexMatrix2.fullTrace (g : ComplexMatrix2) = (t : ℂ) := by
  obtain ⟨hu, hd⟩ := Matrix.mem_specialUnitaryGroup_iff.1 g.2
  have hadj : star (g : ComplexMatrix2) = Matrix.adjugate (g : ComplexMatrix2) := by
    have h₁ : star (g : ComplexMatrix2) * (g : ComplexMatrix2) = 1 :=
      (Matrix.mem_unitaryGroup_iff').1 hu
    have h₂ : (g : ComplexMatrix2) * Matrix.adjugate (g : ComplexMatrix2) = 1 := by
      rw [Matrix.mul_adjugate, hd, one_smul]
    calc star (g : ComplexMatrix2)
          = star (g : ComplexMatrix2) * ((g : ComplexMatrix2) * Matrix.adjugate (g : ComplexMatrix2)) := by
          rw [h₂, mul_one]
      _ = Matrix.adjugate (g : ComplexMatrix2) := by rw [← mul_assoc, h₁, one_mul]
  have h00 : (starRingEnd ℂ) ((g : ComplexMatrix2) 0 0) = (g : ComplexMatrix2) 1 1 := by
    have := congrFun (congrFun hadj 0) 0
    simpa [Matrix.star_apply, Matrix.adjugate_fin_two] using this
  have hbound : ‖(g : ComplexMatrix2) 0 0‖ ≤ 1 := entry_norm_bound_of_unitary hu 0 0
  have hre : |((g : ComplexMatrix2) 0 0).re| ≤ 1 := (Complex.abs_re_le_norm _).trans hbound
  refine ⟨2 * ((g : ComplexMatrix2) 0 0).re, ?_, ?_⟩
  · obtain ⟨h₁, h₂⟩ := abs_le.1 hre
    constructor <;> linarith
  · rw [ComplexMatrix2.fullTrace, Matrix.trace_fin_two, ← h00, Complex.add_conj]
def plaquetteGroupElement (U : CompactGaugeField L m j) (p : Plaquette L m j) :
    ComplexMatrix2.specialUnitary :=
  U.linkValue (Bond.forwardFrom p.origin p.firstAxis) *
    U.linkValue (Bond.forwardFrom (p.origin + unitStep L m j p.firstAxis) p.secondAxis) *
    (U.linkValue (Bond.forwardFrom (p.origin + unitStep L m j p.secondAxis) p.firstAxis))⁻¹ *
      (U.linkValue (Bond.forwardFrom p.origin p.secondAxis))⁻¹
theorem coe_plaquetteGroupElement (U : CompactGaugeField L m j) (p : Plaquette L m j) :
    (plaquetteGroupElement U p : ComplexMatrix2) = plaquetteHolonomy U.1 p := by
  have hv : ∀ b : Bond L m j, (U.linkValue b : ComplexMatrix2) = U.1 b := fun _ => rfl
  have hr : ∀ b : Bond L m j, U.1 b.opposite = (U.1 b)⁻¹ := fun b => U.2.2 b (mem_univ b)
  simp only [plaquetteGroupElement, plaquetteHolonomy, pathHolonomy, Plaquette.boundaryBonds,
    List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, Submonoid.coe_mul,
    ← coe_inv_specialUnitary, hv, hr, mul_assoc]
theorem continuous_plaquetteGroupElement (p : Plaquette L m j) :
    Continuous (fun U : CompactGaugeField L m j => plaquetteGroupElement U p) :=
  (((continuous_linkValue _).mul (continuous_linkValue _)).mul (continuous_linkValue _).inv).mul
    (continuous_linkValue _).inv
theorem plaquetteEnergy_continuous_bounded : PlaquetteEnergyContinuousBounded L m j := by
  intro p
  refine ⟨?_, fun U => ?_⟩
  · have e : (fun U : CompactGaugeField L m j => plaquetteEnergy U.1 p) =
        fun U => 1 - (1 / 2) * ComplexMatrix2.fullTrace (plaquetteGroupElement U p : ComplexMatrix2) := by
      funext U
      rw [coe_plaquetteGroupElement]
      rfl
    rw [e]
    have hc : Continuous
        (fun U : CompactGaugeField L m j => (plaquetteGroupElement U p : ComplexMatrix2)) :=
      continuous_subtype_val.comp (continuous_plaquetteGroupElement p)
    exact continuous_const.sub (continuous_const.mul hc.matrix_trace)
  · obtain ⟨t, ⟨ht₁, ht₂⟩, ht⟩ := fullTrace_real_mem_Icc (plaquetteGroupElement U p)
    refine ⟨1 - t / 2, ⟨by linarith, by linarith⟩, ?_⟩
    simp only [plaquetteEnergy]
    rw [← coe_plaquetteGroupElement, ht]
    push_cast
    ring
theorem reindexFactors_symm_reindexFactors {S S' : Type} (u : S ≃ S')
    (g : S → ComplexMatrix2.specialUnitary) :
    reindexFactors u.symm (reindexFactors u g) = g := by
  funext σ
  simp [reindexFactors]
theorem reindexFactors_reindexFactors_symm {S S' : Type} (u : S ≃ S')
    (g : S' → ComplexMatrix2.specialUnitary) :
    reindexFactors u (reindexFactors u.symm g) = g := by
  funext σ
  simp [reindexFactors]
theorem continuous_reindexFactors {S S' : Type} (u : S ≃ S') :
    Continuous (reindexFactors u :
      (S → ComplexMatrix2.specialUnitary) → S' → ComplexMatrix2.specialUnitary) :=
  continuous_pi fun _ => continuous_apply _
def reindexHomeomorph {S S' : Type} (u : S ≃ S') :
    (S → ComplexMatrix2.specialUnitary) ≃ₜ (S' → ComplexMatrix2.specialUnitary) where
  toFun := reindexFactors u
  invFun := reindexFactors u.symm
  left_inv := reindexFactors_symm_reindexFactors u
  right_inv := reindexFactors_reindexFactors_symm u
  continuous_toFun := continuous_reindexFactors u
  continuous_invFun := continuous_reindexFactors u.symm
theorem reindexingFactors (hgroup : ComplexMatrix2.FiniteProductGroupStatement) :
    ReindexingFactors := by
  intro S S' _ _ u
  refine ⟨⟨reindexHomeomorph u, rfl⟩, ?_⟩
  have hb := borelSpace_pi hgroup S
  have hb' := borelSpace_pi hgroup S'
  obtain ⟨hG, -, -⟩ := hgroup.1 S
  obtain ⟨hG', -, -⟩ := hgroup.1 S'
  obtain ⟨-, -, hprob, hleft, -⟩ := hgroup.2.1 S
  obtain ⟨-, ⟨μ₀, -, huniq⟩, hprob', hleft', -⟩ := hgroup.2.1 S'
  have hr : Measurable (reindexFactors u :
      (S → ComplexMatrix2.specialUnitary) → S' → ComplexMatrix2.specialUnitary) :=
    (continuous_reindexFactors u).measurable
  have hmul : ∀ g' g : S' → ComplexMatrix2.specialUnitary, reindexFactors u.symm (g' * g) =
      reindexFactors u.symm g' * reindexFactors u.symm g := fun _ _ => rfl
  have hnew : IsProbabilityMeasure ((ComplexMatrix2.haarPi S).map (reindexFactors u)) :=
    Measure.isProbabilityMeasure_map hr.aemeasurable
  have hinv : ((ComplexMatrix2.haarPi S).map (reindexFactors u)).IsMulLeftInvariant := by
    refine ⟨fun g' => ?_⟩
    have hm' : Measurable (fun x : S' → ComplexMatrix2.specialUnitary => g' * x) :=
      (continuous_const.mul continuous_id).measurable
    have hm : Measurable
        (fun x : S → ComplexMatrix2.specialUnitary => reindexFactors u.symm g' * x) :=
      (continuous_const.mul continuous_id).measurable
    rw [Measure.map_map hm' hr]
    have hcomp : (fun x : S' → ComplexMatrix2.specialUnitary => g' * x) ∘ reindexFactors u =
        reindexFactors u ∘ fun x : S → ComplexMatrix2.specialUnitary =>
          reindexFactors u.symm g' * x := by
      funext x σ
      simp [reindexFactors]
    rw [hcomp, ← Measure.map_map hr hm, hleft.map_mul_left_eq_self]
  have e₁ := huniq _ ⟨hnew, hinv⟩
  have e₂ := huniq _ ⟨hprob', hleft'⟩
  exact e₁.trans e₂.symm
theorem statement_holds (hgroup : ComplexMatrix2.FiniteProductGroupStatement)
    (hcounts : SiteAndPlaquetteCounts) : Statement := by
  refine ⟨fun L m j hL hm hj => ?_, reindexingFactors hgroup⟩
  have h1 : 1 < L := by
    have := hL.2
    omega
  have hk : 0 < (m : ℤ) + j := by omega
  exact ⟨meshAndOrientation h1 hk, finiteAndNonempty hcounts h1 hk,
    productStructure hgroup hcounts h1 hk, plaquetteEnergy_continuous_bounded⟩
end YangMills.Construction.GaugeFieldProduct
