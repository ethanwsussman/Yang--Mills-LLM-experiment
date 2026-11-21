import YangMills.Construction.Lattice.CombSchemeGaugeLawAndConjugationProof
import YangMills.Construction.Lattice.MeanSchemeIsTheAveragingMapOnSmallConfigurationsProof
import YangMills.Construction.Lattice.OneStepObjectsAtRealBondFunctions
import YangMills.Construction.Lattice.OneStepObjectsNearSmallPlaquettes
import YangMills.Construction.Lattice.ValuesOfTheTwoSchemes
import YangMills.Construction.Lattice.WeightedDistanceOfASeparatedSequence
import Mathlib
open Set
open scoped Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction.PeriodicLattice
open YangMills.Construction.Matrices
variable {L m K n : ℕ}
namespace RealBondFieldStep
theorem norm_eq_one_of_mem_gaugeGroup {X : ComplexMatrix2} (hX : X ∈ compactGaugeGroup) :
    ‖X‖ = 1 := by apply _root_.YangMills.Construction.PeriodicLattice.CentredAverageSmallFields.norm_eq_one_of_mem_compactGaugeGroup <;> assumption
theorem inv_mem_gaugeGroup {A : ComplexMatrix2} (h : A ∈ compactGaugeGroup) :
    A⁻¹ ∈ compactGaugeGroup := by apply _root_.YangMills.Construction.PeriodicLattice.BlockAverageContinuity.inv_mem_compactGaugeGroup <;> assumption
theorem inv_mul_cancel_of_mem_gaugeGroup {A : ComplexMatrix2} (h : A ∈ compactGaugeGroup) :
    A⁻¹ * A = 1 := by apply _root_.YangMills.SharedProofs.p14555 <;> assumption
theorem mul_inv_cancel_of_mem_gaugeGroup {A : ComplexMatrix2} (h : A ∈ compactGaugeGroup) :
    A * A⁻¹ = 1 := by apply _root_.YangMills.SharedProofs.p16098 <;> assumption
theorem inv_inv_of_mem_gaugeGroup {A : ComplexMatrix2} (h : A ∈ compactGaugeGroup) :
    A⁻¹⁻¹ = A := by apply _root_.YangMills.Construction.PeriodicLattice.BlockAverageContinuity.inv_inv_of_mem_compactGaugeGroup <;> assumption
theorem norm_inv_sub_inv_le_of_mem {X Y : ComplexMatrix2} (hX : X ∈ compactGaugeGroup)
    (hY : Y ∈ compactGaugeGroup) : ‖X⁻¹ - Y⁻¹‖ ≤ ‖X - Y‖ := by
  have hid : X⁻¹ - Y⁻¹ = X⁻¹ * (Y - X) * Y⁻¹ := by
    rw [mul_sub, sub_mul, mul_assoc X⁻¹ Y, mul_inv_cancel_of_mem_gaugeGroup hY, mul_one,
      inv_mul_cancel_of_mem_gaugeGroup hX, one_mul]
  calc ‖X⁻¹ - Y⁻¹‖ = ‖X⁻¹ * (Y - X) * Y⁻¹‖ := by rw [hid]
    _ ≤ ‖X⁻¹‖ * ‖Y - X‖ * ‖Y⁻¹‖ := by
      refine (norm_mul_le _ _).trans ?_
      gcongr
      exact norm_mul_le _ _
    _ = ‖X - Y‖ := by
      rw [norm_eq_one_of_mem_gaugeGroup (inv_mem_gaugeGroup hX),
        norm_eq_one_of_mem_gaugeGroup (inv_mem_gaugeGroup hY), one_mul, mul_one, norm_sub_rev]
theorem smul_logSeries_mem_compactLieAlgebra (hE : ComplexMatrix2.ExpLogEstimates)
    {A : ComplexMatrix2} (hA : A ∈ compactGaugeGroup)
    (h1 : ComplexMatrix2.operatorNorm (A - 1) < 1) :
    Complex.I⁻¹ • ComplexMatrix2.logSeries A ∈ compactLieAlgebra := by
  obtain ⟨hAu, hdet⟩ := Matrix.mem_specialUnitaryGroup_iff.mp hA
  obtain ⟨-, -, -, -, -, -, -, hU, -, -⟩ := hE
  obtain ⟨H, -, -, -, -, -, hd⟩ := hU A hAu h1
  obtain ⟨-, -, ⟨Y, hY, hlog⟩, -⟩ := hd hdet
  rw [hlog, smul_smul, inv_mul_cancel₀ Complex.I_ne_zero, one_smul]
  exact hY
theorem norm_matExp_sub_one_le (hE : ComplexMatrix2.ExpLogEstimates)
    (hI : ComplexMatrix2.UnitaryLogarithmProperties) {Y : ComplexMatrix2}
    (hY : Y ∈ ComplexMatrix2.hermitianTraceless)
    (hs : ComplexMatrix2.operatorNorm Y < Real.log 2) :
    ComplexMatrix2.operatorNorm (ComplexMatrix2.matExp (Complex.I • Y) - 1) ≤
      ComplexMatrix2.operatorNorm Y := by
  have hmem : ComplexMatrix2.matExp (Complex.I • Y) ∈ ComplexMatrix2.specialUnitary :=
    (hI.1 Y hY).2.2.2
  obtain ⟨-, -, -, -, hsmall, -, -, hU, -, -⟩ := hE
  have hZ : ComplexMatrix2.operatorNorm (Complex.I • Y) = ComplexMatrix2.operatorNorm Y := by
    simp [ComplexMatrix2.operatorNorm, norm_smul]
  obtain ⟨h1, hlog⟩ := hsmall (Complex.I • Y) (hZ.symm ▸ hs)
  obtain ⟨H, -, hH, -, -, hnorm, -⟩ :=
    hU _ (Matrix.mem_specialUnitaryGroup_iff.mp hmem).1 h1
  have hHY : H = Y := by
    have h := hH.symm.trans hlog
    exact smul_right_injective ComplexMatrix2 Complex.I_ne_zero h
  rw [hnorm, hHY]
  have := Real.sin_le (show 0 ≤ ComplexMatrix2.operatorNorm Y / 2 by positivity)
  linarith
theorem pathHolonomy_sub_le {j : ℤ} {U V : Bond L m j → ComplexMatrix2} {δ : ℝ}
    (Γ : List (Bond L m j))
    (h : ∀ b ∈ Γ, U b ∈ compactGaugeGroup ∧ V b ∈ compactGaugeGroup ∧ ‖U b - V b‖ ≤ δ) :
    pathHolonomy U Γ ∈ compactGaugeGroup ∧ pathHolonomy V Γ ∈ compactGaugeGroup ∧
      ‖pathHolonomy U Γ - pathHolonomy V Γ‖ ≤ Γ.length * δ := by
  induction Γ with
  | nil =>
    refine ⟨(ComplexMatrix2.specialUnitary).one_mem, (ComplexMatrix2.specialUnitary).one_mem, ?_⟩
    simp [pathHolonomy]
  | cons b Γ ih =>
    obtain ⟨hU, hV, hd⟩ := ih fun b' hb' => h b' (List.mem_cons_of_mem _ hb')
    obtain ⟨hUb, hVb, hb⟩ := h b List.mem_cons_self
    have eU : pathHolonomy U (b :: Γ) = U b * pathHolonomy U Γ := by simp [pathHolonomy]
    have eV : pathHolonomy V (b :: Γ) = V b * pathHolonomy V Γ := by simp [pathHolonomy]
    refine ⟨eU ▸ (ComplexMatrix2.specialUnitary).mul_mem hUb hU,
      eV ▸ (ComplexMatrix2.specialUnitary).mul_mem hVb hV, ?_⟩
    have hid : U b * pathHolonomy U Γ - V b * pathHolonomy V Γ =
        (U b - V b) * pathHolonomy U Γ + V b * (pathHolonomy U Γ - pathHolonomy V Γ) := by
      noncomm_ring
    rw [eU, eV, hid, List.length_cons]
    calc ‖(U b - V b) * pathHolonomy U Γ + V b * (pathHolonomy U Γ - pathHolonomy V Γ)‖
        ≤ ‖U b - V b‖ * ‖pathHolonomy U Γ‖ + ‖V b‖ * ‖pathHolonomy U Γ - pathHolonomy V Γ‖ :=
          (norm_add_le _ _).trans (add_le_add (norm_mul_le _ _) (norm_mul_le _ _))
      _ ≤ δ + Γ.length * δ := by
          rw [norm_eq_one_of_mem_gaugeGroup hU, norm_eq_one_of_mem_gaugeGroup hVb, mul_one,
            one_mul]
          exact add_le_add hb hd
      _ = ((Γ.length + 1 : ℕ) : ℝ) * δ := by push_cast; ring
theorem boundaryBonds_mem (c : BondAtLevel L m K (n + 1)) {p : PlaquetteAtLevel L m K n}
    (hp : p ∈ (doubleBlockPlaquettes c : Set (PlaquetteAtLevel L m K n))) :
    ∀ b ∈ p.boundaryBonds, b ∈ (bondsInDoubleBlock c : Set (BondAtLevel L m K n)) := by apply _root_.YangMills.Construction.PeriodicLattice.CentredAverageSmallFields.boundaryBonds_mem_bondsInDoubleBlock <;> assumption
theorem plaquetteHolonomy_le_curvature {c : BondAtLevel L m K (n + 1)}
    {W : BondAtLevel L m K n → ComplexMatrix2}
    (hW : IsGaugeField compactGaugeGroup (bondsInDoubleBlock c) W) {p : PlaquetteAtLevel L m K n}
    (hp : p ∈ (doubleBlockPlaquettes c : Set (PlaquetteAtLevel L m K n))) :
    ComplexMatrix2.operatorNorm (plaquetteHolonomy W p - 1) ≤ doubleBlockCurvature W c := by apply _root_.YangMills.Construction.PeriodicLattice.CentredAverageSmallFields.plaquetteHolonomy_sub_one_le_curvature <;> assumption
theorem bondsWithin_sitesInBondBlockPair (c : BondAtLevel L m K (n + 1)) :
    (bondsWithin (sitesInBondBlockPair n c)).bonds =
      (bondsInDoubleBlock c : Set (BondAtLevel L m K n)) := by
  have h : bondBlockPair n c = bondDoubleBlock c := by
    change refinedBlock (n + 1 - n) c.source ∪ refinedBlock (n + 1 - n) c.target =
      refinedBlock 1 c.source ∪ refinedBlock 1 c.target
    rw [Nat.add_sub_cancel_left]
  ext b
  change ((b.source : FourTorus L m) ∈ bondBlockPair n c ∧
      (b.target : FourTorus L m) ∈ bondBlockPair n c) ↔
    ((b.source : FourTorus L m) ∈ bondDoubleBlock c ∧ (b.target : FourTorus L m) ∈ bondDoubleBlock c)
  rw [h]
theorem exists_gaugeField_extension {c : BondAtLevel L m K (n + 1)}
    {W : BondAtLevel L m K n → ComplexMatrix2}
    (hW : IsGaugeField compactGaugeGroup (bondsInDoubleBlock c) W) :
    ∃ V ∈ gaugeFieldsAtLevel L m K n,
      ∀ b ∈ (bondsInDoubleBlock c : Set (BondAtLevel L m K n)), V b = W b := by apply _root_.YangMills.Construction.PeriodicLattice.CentredAverageSmallFields.exists_gaugeField_extension <;> assumption
theorem twistedConfig_of_positive (c : BondAtLevel L m K (n + 1))
    (a : LieBondField (doubleBlockSymmetricSet c)) (W₀ : BondAtLevel L m K n → ComplexMatrix2)
    {b : BondAtLevel L m K n} (hb : b.IsPositivelyOriented) :
    twistedConfig c a W₀ b =
      ComplexMatrix2.matExp (Complex.I • (a.eval b : ComplexMatrix2)) * W₀ b := by
  simp only [twistedConfig, expTwist, if_pos hb]
theorem twistedConfig_of_not_positive (c : BondAtLevel L m K (n + 1))
    (a : LieBondField (doubleBlockSymmetricSet c)) (W₀ : BondAtLevel L m K n → ComplexMatrix2)
    {b : BondAtLevel L m K n} (hb : ¬ b.IsPositivelyOriented) :
    twistedConfig c a W₀ b =
      (ComplexMatrix2.matExp (Complex.I • (a.eval b.opposite : ComplexMatrix2)) *
        W₀ b.opposite)⁻¹ := by
  simp only [twistedConfig, expTwist, if_neg hb]
end RealBondFieldStep
open RealBondFieldStep in
theorem realBondFieldStep_holds
    (hN : StepObjectsNearSmallCurvature)
    (hV : SchemeValuesInGaugeGroup)
    (hM : CentredAverageAgreesOnSmallFields)
    (hE : ComplexMatrix2.ExpLogEstimates)
    (hI : ComplexMatrix2.UnitaryLogarithmProperties) :
    RealBondFieldStepStatement := by
  intro L hL r hr m K n hm hn s c hc W₀ hW₀ hϖ a ha haR
  have hL13 : 13 ≤ L := hL.2
  have hL0 : 0 < L := by omega
  have hL2 : 2 ≤ L := by omega
  have hj : -(m : ℤ) < levelDepth K n := by
    simp only [levelDepth]
    omega
  have hsite : Finite (Site L m (levelDepth K n)) :=
    (SeparatedSequence.sublattice_finite hL0 hj.le).to_subtype
  have hbondFin : Finite (BondAtLevel L m K n) :=
    Finite.of_injective (fun b : BondAtLevel L m K n => (b.source, b.target))
      (fun b b' h => Bond.ext (congrArg Prod.fst h) (congrArg Prod.snd h))
  have hbdd : BddAbove (range fun i : PositiveBondsOf (doubleBlockSymmetricSet c) =>
      ComplexMatrix2.operatorNorm (a i : ComplexMatrix2)) := (Set.finite_range _).bddAbove
  have hxor : ∀ b : BondAtLevel L m K n, b.IsPositivelyOriented →
      ¬ b.opposite.IsPositivelyOriented := by
    intro b hpos
    rcases MatrixValued.xor_isPositivelyOriented_opposite hL2 hj b with h | h
    · exact h.2
    · exact absurd hpos h.2
  have hrad := Averaging.isSmoothingRadius_smoothingRadius hL.1 hL13
  have hω₁ : Averaging.smoothingRadius L ≤ 1 := by
    refine hrad.2.trans ?_
    have h13 : (13 : ℝ) ≤ L := by exact_mod_cast hL13
    rw [div_le_one (by positivity)]
    nlinarith
  set σ := supOperatorNorm a with hσ
  have hσ₀ : 0 ≤ σ := Real.iSup_nonneg fun _ => norm_nonneg _
  have hσr : σ < r := ha.trans_le (min_le_left _ _)
  have hσω : σ < Averaging.smoothingRadius L / 8 :=
    ha.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hσlog : σ < Real.log 2 := by
    have := Real.log_two_gt_d9
    linarith
  have hϖω : doubleBlockCurvature W₀ c ≤ Averaging.smoothingRadius L / 2 :=
    hϖ.trans (min_le_left _ _)
  set W := twistedConfig c a W₀ with hWdef
  have hfactor : ∀ b : BondAtLevel L m K n, b ∈ (bondsInDoubleBlock c : Set (BondAtLevel L m K n)) →
      b.IsPositivelyOriented →
        ComplexMatrix2.matExp (Complex.I • (a.eval b : ComplexMatrix2)) ∈ compactGaugeGroup ∧
        ‖ComplexMatrix2.matExp (Complex.I • (a.eval b : ComplexMatrix2)) - 1‖ ≤ σ := by
    intro b hb hpos
    let i : PositiveBondsOf (doubleBlockSymmetricSet c) := ⟨b, hb, hpos⟩
    have hv : (a.eval b : ComplexMatrix2) = (a i : ComplexMatrix2) := by
      rw [show a.eval b = a i from a.eval_of_positive i]
    have hle : ComplexMatrix2.operatorNorm (a i : ComplexMatrix2) ≤ σ := le_ciSup hbdd i
    rw [hv]
    exact ⟨(hI.1 _ (haR i)).2.2.2,
      (norm_matExp_sub_one_le hE hI (haR i) (hle.trans_lt hσlog)).trans hle⟩
  have hpositive : ∀ b : BondAtLevel L m K n,
      b ∈ (bondsInDoubleBlock c : Set (BondAtLevel L m K n)) →
      b.IsPositivelyOriented → W b ∈ compactGaugeGroup ∧ ‖W b - W₀ b‖ ≤ σ := by
    intro b hb hpos
    obtain ⟨hEm, hEn⟩ := hfactor b hb hpos
    have hW₀b : W₀ b ∈ compactGaugeGroup := hW₀.1 b hb
    have hval : W b = ComplexMatrix2.matExp (Complex.I • (a.eval b : ComplexMatrix2)) * W₀ b :=
      twistedConfig_of_positive c a W₀ hpos
    refine ⟨hval ▸ (ComplexMatrix2.specialUnitary).mul_mem hEm hW₀b, ?_⟩
    rw [hval, ← sub_one_mul]
    calc _ ≤ ‖ComplexMatrix2.matExp (Complex.I • (a.eval b : ComplexMatrix2)) - 1‖ * ‖W₀ b‖ :=
          norm_mul_le _ _
      _ ≤ σ := by rw [norm_eq_one_of_mem_gaugeGroup hW₀b, mul_one]; exact hEn
  have hbonds : ∀ b : BondAtLevel L m K n,
      b ∈ (bondsInDoubleBlock c : Set (BondAtLevel L m K n)) →
      W b ∈ compactGaugeGroup ∧ W₀ b ∈ compactGaugeGroup ∧ ‖W b - W₀ b‖ ≤ σ := by
    intro b hb
    by_cases hpos : b.IsPositivelyOriented
    · exact ⟨(hpositive b hb hpos).1, hW₀.1 b hb, (hpositive b hb hpos).2⟩
    · have hb' : b.opposite ∈ (bondsInDoubleBlock c : Set (BondAtLevel L m K n)) := ⟨hb.2, hb.1⟩
      have hpos' : b.opposite.IsPositivelyOriented := Bond.opposite_isPositivelyOriented hpos
      obtain ⟨hWr, hdr⟩ := hpositive b.opposite hb' hpos'
      have hval : W b = (W b.opposite)⁻¹ := by
        rw [hWdef, twistedConfig_of_not_positive c a W₀ hpos, twistedConfig_of_positive c a W₀ hpos']
      have hW₀r : W₀ b.opposite ∈ compactGaugeGroup := hW₀.1 _ hb'
      have hW₀b : W₀ b = (W₀ b.opposite)⁻¹ := hW₀.2 _ hb'
      refine ⟨hval ▸ inv_mem_gaugeGroup hWr, hW₀.1 b hb, ?_⟩
      rw [hval, hW₀b]
      exact (norm_inv_sub_inv_le_of_mem hWr hW₀r).trans hdr
  have hWcfg : IsGaugeField compactGaugeGroup (bondsInDoubleBlock c) W := by
    refine ⟨fun b hb => (hbonds b hb).1, fun b hb => ?_⟩
    by_cases hpos : b.IsPositivelyOriented
    · have hnot := hxor b hpos
      rw [hWdef, twistedConfig_of_not_positive c a W₀ hnot, twistedConfig_of_positive c a W₀ hpos]
      rfl
    · have hb' : b.opposite ∈ (bondsInDoubleBlock c : Set (BondAtLevel L m K n)) := ⟨hb.2, hb.1⟩
      have hval : W b = (W b.opposite)⁻¹ := by
        rw [hWdef, twistedConfig_of_not_positive c a W₀ hpos,
          twistedConfig_of_positive c a W₀ (Bond.opposite_isPositivelyOriented hpos)]
      rw [hval, inv_inv_of_mem_gaugeGroup (hbonds _ hb').1]
  have hsize : doubleBlockCurvature W c ≤ doubleBlockCurvature W₀ c + 4 * σ := by
    have hnn : 0 ≤ doubleBlockCurvature W₀ c := Real.iSup_nonneg fun _ => norm_nonneg _
    refine Real.iSup_le (fun p => ?_) (by positivity)
    have h4 := (pathHolonomy_sub_le p.1.boundaryBonds fun b hb =>
      hbonds b (boundaryBonds_mem c p.2 b hb)).2.2
    have hlen : (p.1.boundaryBonds.length : ℝ) = 4 := by simp [Plaquette.boundaryBonds]
    rw [hlen] at h4
    have h0 := plaquetteHolonomy_le_curvature hW₀ p.2
    calc ComplexMatrix2.operatorNorm (plaquetteHolonomy W p.1 - 1)
        = ‖(plaquetteHolonomy W p.1 - plaquetteHolonomy W₀ p.1) +
            (plaquetteHolonomy W₀ p.1 - 1)‖ := by rw [sub_add_sub_cancel]
      _ ≤ ‖plaquetteHolonomy W p.1 - plaquetteHolonomy W₀ p.1‖ +
            ‖plaquetteHolonomy W₀ p.1 - 1‖ := norm_add_le _ _
      _ ≤ doubleBlockCurvature W₀ c + 4 * σ := by
        have h4' : ‖plaquetteHolonomy W p.1 - plaquetteHolonomy W₀ p.1‖ ≤ 4 * σ := h4
        linarith
  have hsmall : doubleBlockCurvature W c < Averaging.smoothingRadius L := by linarith
  have hB : StepQuantitiesBounded s c a W₀ :=
    (hN L hL r hr m K n hm hn s c hc W₀ hW₀ hϖ).1 a hσr
  obtain ⟨-, hDefW, hDef₀, hprod⟩ : StepLogsDefined s c a W₀ ∧
      IsSchemeAverageDefined s W c ∧ IsSchemeAverageDefined s W₀ c ∧
      ComplexMatrix2.operatorNorm (stepProduct s c a W₀ - 1) < 1 := hB.variable_bound.1
  obtain ⟨hcW, -, -, havgW⟩ := hV L hL m K n hm hn s c hc W hDefW hWcfg
  obtain ⟨hc₀, -, -, havg₀⟩ := hV L hL m K n hm hn s c hc W₀ hDef₀ hW₀
  have hlogs : ∀ y ∈ ({c.source, c.target} : Set (SiteAtLevel L m K (n + 1))),
      ∀ x ∈ sitesInBlock (levelDepth K n) y, stepLog s c a W₀ y x ∈ compactLieAlgebra := by
    intro y hy x hx
    refine smul_logSeries_mem_compactLieAlgebra hE ?_ (hB.log_bound y hy x hx).1.2.2
    exact (ComplexMatrix2.specialUnitary).mul_mem (hcW y hy x hx)
      (inv_mem_gaugeGroup (hc₀ y hy x hx))
  have hgauge : ∀ y ∈ ({c.source, c.target} : Set (SiteAtLevel L m K (n + 1))),
      stepGauge s c a W₀ y ∈ compactGaugeGroup := by
    intro y hy
    have hsum : (∑ᶠ x ∈ sitesInBlock (levelDepth K n) y, stepLog s c a W₀ y x) ∈
        ComplexMatrix2.hermitianTraceless :=
      finsum_mem_induction (· ∈ ComplexMatrix2.hermitianTraceless) (Submodule.zero_mem _)
        (fun _ _ => Submodule.add_mem _) (hlogs y hy)
    have hw : inverseFourthPowerWeight L • (∑ᶠ x ∈ sitesInBlock (levelDepth K n) y,
        stepLog s c a W₀ y x) ∈ ComplexMatrix2.hermitianTraceless := by
      have h := Submodule.smul_mem ComplexMatrix2.hermitianTraceless ((L : ℝ) ^ (-4 : ℤ)) hsum
      convert h using 1
      ext i k
      simp [inverseFourthPowerWeight]
    exact (hI.1 _ hw).2.2.2
  refine ⟨hlogs, fun y hy => ?_, ?_, hgauge, hsmall.trans_le le_rfl, ?_⟩
  · exact smul_logSeries_mem_compactLieAlgebra hE (hgauge y hy) (hB.gauge_bound y hy).2.1
  · refine smul_logSeries_mem_compactLieAlgebra hE ?_ hprod
    have ht := hgauge c.source (Or.inl rfl)
    have hh := hgauge c.target (Or.inr rfl)
    exact (ComplexMatrix2.specialUnitary).mul_mem
      ((ComplexMatrix2.specialUnitary).mul_mem
        ((ComplexMatrix2.specialUnitary).mul_mem (inv_mem_gaugeGroup ht) havgW) hh)
      (inv_mem_gaugeGroup havg₀)
  · have hData : Averaging.OneStep.Parameters 4 2 L K m ComplexMatrix2.specialUnitary :=
      ⟨rfl, rfl, rfl, hL.1, hL13, by omega, hm⟩
    have hMean := hM L m K n hData hn c hc W hWcfg hsmall
    obtain ⟨V, hVc, hVW⟩ := exists_gaugeField_extension hWcfg
    have hε : ExtendsAround c W (Classical.epsilon (ExtendsAround c W)) :=
      Classical.epsilon_spec (p := ExtendsAround c W)
        ⟨V, hVc, fun b hb => hVW b (bondsWithin_sitesInBondBlockPair c ▸ hb)⟩
    have hU : ∀ b ∈ (bondsInDoubleBlock c : Set (BondAtLevel L m K n)),
        Classical.epsilon (ExtendsAround c W) b = W b :=
      fun b hb => hε.2 b ((bondsWithin_sitesInBondBlockPair c).symm ▸ hb)
    exact (hMean.of_extension _ hε.1 hU).2.2.symm
end YangMills.Construction.PeriodicLattice
