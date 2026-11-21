import YangMills.Construction.Lattice.BareBaseSitesOfTheSchemes
import YangMills.Construction.Lattice.ElementaryBoundsOfOneStepProof
import YangMills.Construction.Lattice.GaugeCovarianceOfTheIteratesOfTheSchemes
import YangMills.Construction.Lattice.IteratesOfTheTwoSchemes
import YangMills.Construction.Lattice.SchemeIterateReadsTheBareDoubleBlock
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.PeriodicLattice
variable {L m K : ℕ}
private theorem isUnit_det_of_mem {X : Matrices.ComplexMatrix2} (h : X ∈ compactGaugeGroup) :
    IsUnit X.det := by apply _root_.YangMills.Construction.PeriodicLattice.SingleStepEstimate.det_isUnit_of_mem <;> assumption
private theorem inv_mem_compact {X : Matrices.ComplexMatrix2} (h : X ∈ compactGaugeGroup) :
    X⁻¹ ∈ compactGaugeGroup := by apply _root_.YangMills.Construction.PeriodicLattice.BlockAverageContinuity.inv_mem_compactGaugeGroup <;> assumption
private theorem gaugeTransform_mem {U : BondAtLevel L m K 0 → Matrices.ComplexMatrix2}
    {u : SiteAtLevel L m K 0 → Matrices.ComplexMatrix2}
    (hU : U ∈ gaugeFieldsAtLevel L m K 0) (hu : IsGaugeMap compactGaugeGroup u) :
    gaugeTransform u U ∈ gaugeFieldsAtLevel L m K 0 := by
  refine ⟨fun b _ => ?_, fun b _ => ?_⟩
  · exact mul_mem (mul_mem (hu _) (hU.1 b (mem_univ b))) (inv_mem_compact (hu _))
  · have hr := hU.2 b (mem_univ b)
    change u b.target * U b.opposite * (u b.source)⁻¹ = (u b.source * U b * (u b.target)⁻¹)⁻¹
    rw [hr, Matrix.mul_inv_rev, Matrix.mul_inv_rev,
      Matrix.nonsing_inv_nonsing_inv _ (isUnit_det_of_mem (hu _)), mul_assoc]
private theorem isGaugeMap_inv {u : SiteAtLevel L m K 0 → Matrices.ComplexMatrix2}
    (hu : IsGaugeMap compactGaugeGroup u) :
    IsGaugeMap compactGaugeGroup (fun x => (u x)⁻¹) :=
  fun x => inv_mem_compact (hu x)
private theorem gaugeTransform_inv_gaugeTransform
    {u : SiteAtLevel L m K 0 → Matrices.ComplexMatrix2}
    (hu : IsGaugeMap compactGaugeGroup u) (U : BondAtLevel L m K 0 → Matrices.ComplexMatrix2) :
    gaugeTransform (fun x => (u x)⁻¹) (gaugeTransform u U) = U := by
  funext b
  change (u b.source)⁻¹ * (u b.source * U b * (u b.target)⁻¹) * ((u b.target)⁻¹)⁻¹ = U b
  rw [Matrix.nonsing_inv_nonsing_inv _ (isUnit_det_of_mem (hu _)), mul_assoc, mul_assoc, mul_assoc,
    Matrix.nonsing_inv_mul _ (isUnit_det_of_mem (hu _)), mul_one, ← mul_assoc,
    Matrix.nonsing_inv_mul _ (isUnit_det_of_mem (hu _)), one_mul]
private theorem opposite_isPositivelyOriented {j : ℤ} {c : Bond L m j}
    (hc : ¬c.IsPositivelyOriented) : c.opposite.IsPositivelyOriented := by apply _root_.YangMills.Construction.PeriodicLattice.Bond.opposite_isPositivelyOriented <;> assumption
private theorem positivelyOriented_isPositivelyOriented {j : ℤ} (c : Bond L m j) :
    c.positivelyOriented.IsPositivelyOriented := by
  by_cases hc : c.IsPositivelyOriented
  · rw [Bond.positivelyOriented, if_pos hc]
    exact hc
  · rw [Bond.positivelyOriented, if_neg hc]
    exact opposite_isPositivelyOriented hc
abbrev _root_.YangMills.DeltaSharedProofs.p500474 := @positivelyOriented_isPositivelyOriented
private theorem isBareIterateDefined_of_mem (s : AveragingScheme)
    {U : BondAtLevel L m K 0 → Matrices.ComplexMatrix2} :
    ∀ (j : ℕ), U ∈ iteratedAverageDomain s j → ∀ c : BondAtLevel L m K j,
      IsBareIterateDefined s U j c
  | 0, _, _ => trivial
  | j + 1, h, c =>
    ⟨fun b _ => isBareIterateDefined_of_mem s j h.1 b,
      h.2 _ (positivelyOriented_isPositivelyOriented c)⟩
private theorem gaugeTransform_mem_domain (hG : IteratedAverageGaugeCovariance)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hK : 0 < K) (hm : 0 < m)
    (s : AveragingScheme)
    {U : BondAtLevel L m K 0 → Matrices.ComplexMatrix2} (hU : U ∈ gaugeFieldsAtLevel L m K 0)
    {u : SiteAtLevel L m K 0 → Matrices.ComplexMatrix2} (hu : IsGaugeMap compactGaugeGroup u) :
    ∀ j : ℕ, j ≤ K → U ∈ iteratedAverageDomain s j →
      gaugeTransform u U ∈ iteratedAverageDomain s j
  | 0, _, _ => mem_univ _
  | j + 1, hj, h => by
    refine ⟨gaugeTransform_mem_domain hG hL hK hm s hU hu j (by omega) h.1, fun c hc => ?_⟩
    have hd := (hG L hL K m hK hm s (j + 1) hj U hU u hu c
      (isBareIterateDefined_of_mem s (j + 1) h c)).1
    have h₂ : IsOneStepAverageFormed s (iteratedAverage s j (gaugeTransform u U))
        c.positivelyOriented := hd.2
    have e : c.positivelyOriented = c := if_pos hc
    rw [e] at h₂
    exact h₂
private theorem bondsInDoubleBlock_positivelyOriented {n : ℕ} (c : BondAtLevel L m K (n + 1)) :
    (bondsInDoubleBlock c.positivelyOriented : Set (BondAtLevel L m K n)) =
      (bondsWithin (sitesInBondBlockPair n c)).bonds := by
  have h : n + 1 - n = 1 := by omega
  have e₁ : (bondsWithin (sitesInBondBlockPair n c)).bonds =
      (bondsInDoubleBlock c : Set (BondAtLevel L m K n)) := by
    ext b
    simp only [bondsWithin, Bond.LiesIn, sitesInBondBlockPair, bondBlockPair, blockAtLevel,
      bondsInDoubleBlock, bondsInside, bondDoubleBlock, unitBlock, Set.mem_ofPred_eq, h]
  rw [e₁]
  by_cases hc : c.IsPositivelyOriented
  · have e : c.positivelyOriented = c := if_pos hc
    rw [e]
  · have e : c.positivelyOriented = c.opposite := if_neg hc
    rw [e]
    ext b
    simp only [bondsInDoubleBlock, bondsInside, bondDoubleBlock, Bond.opposite, Set.mem_ofPred_eq,
      Set.union_comm]
private theorem isSchemeAverageDefinedAt_iff {j' j : ℤ} (s : AveragingScheme)
    (W : Bond L m j' → Matrices.ComplexMatrix2) (c : Bond L m j) :
    IsSchemeAverageDefinedAt s W c ↔ IsOneStepAverageFormed s W c.positivelyOriented := by
  by_cases hc : c.IsPositivelyOriented
  · have e : c.positivelyOriented = c := if_pos hc
    rw [e]
    simp only [IsSchemeAverageDefinedAt, if_pos hc, IsOneStepAverageFormed]
  · have e : c.positivelyOriented = c.opposite := if_neg hc
    rw [e]
    simp only [IsSchemeAverageDefinedAt, if_neg hc, IsOneStepAverageFormed]
private theorem isBareIterateDefined_iff (s : AveragingScheme)
    (U : BondAtLevel L m K 0 → Matrices.ComplexMatrix2) :
    ∀ (n : ℕ) (c : BondAtLevel L m K n),
      IsBareIterateDefined s U n c ↔ IsIteratedAverageDefinedAt s U n c
  | 0, _ => by simp only [IsBareIterateDefined, IsIteratedAverageDefinedAt]
  | n + 1, c => by
    rw [IsBareIterateDefined, IsIteratedAverageDefinedAt, bondsInDoubleBlock_positivelyOriented,
      isSchemeAverageDefinedAt_iff]
    exact and_congr_left fun _ => forall₂_congr fun b _ => isBareIterateDefined_iff s U n b
private theorem lowestBlockSite_spec (hodd : Odd L) {j : ℤ} (n : ℕ) (y : Site L m j) :
    IsLowestBlockSite n y (lowestBlockSite n y) := by
  obtain ⟨b, hb⟩ : Odd ((L : ℤ) ^ n) := Odd.pow (by exact_mod_cast hodd)
  have hpos : 0 < (L : ℤ) ^ n := pow_pos (by exact_mod_cast hodd.pos) n
  have hb0 : 0 ≤ b := by omega
  have hp : (fun _ => -b : Fin 4 → ℤ) ∈ blockOffsets L n := by
    intro μ
    simp only [abs_neg, abs_of_nonneg hb0, hb]
    omega
  have hmin : ∀ q ∈ blockOffsets L n, ∀ μ, (fun _ => -b : Fin 4 → ℤ) μ ≤ q μ := by
    intro q hq μ
    have h := hq μ
    rw [hb] at h
    have h' := neg_abs_le (q μ)
    show -b ≤ q μ
    linarith
  exact Classical.epsilon_spec (p := IsLowestBlockSite n y) ⟨_, _, hp, rfl, hmin⟩
private theorem refinedOffsetSite_sub {j : ℤ} (n : ℕ) (y : Site L m j) (p q : Fin 4 → ℤ) :
    refinedOffsetSite n y p - refinedOffsetSite n y q =
      ∑ μ, (p μ - q μ) • unitStep L m (j + n) μ := by
  simp only [refinedOffsetSite, offsetSite, add_sub_add_left_eq_sub, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun μ _ => (sub_smul _ _ _).symm
private theorem coe_sum_unitStep_eq {j₁ j₂ : ℤ} (e : j₁ = j₂) (d : Fin 4 → ℤ) :
    ((∑ μ, d μ • unitStep L m j₁ μ : Site L m j₁) : FourTorus L m) =
      ((∑ μ, d μ • unitStep L m j₂ μ : Site L m j₂) : FourTorus L m) := by
  subst e
  rfl
private theorem offset_mul_meshSize_lt (hL : Conventions.IsAdmissibleBlockingFactor L) {d : ℤ}
    (hd : |d| < (L : ℤ) ^ K) :
    ((|d| : ℤ) : ℝ) * meshSize L (levelDepth K 0) < torusSide L m / 2 := by
  have hL1 : (1 : ℝ) ≤ L := by
    have := hL.2
    exact_mod_cast (by omega : 1 ≤ L)
  have hL0 : (0 : ℝ) < L := by linarith
  have hsp : 0 < meshSize L (levelDepth K 0) := zpow_pos hL0 _
  have hone : (L : ℝ) ^ K * meshSize L (levelDepth K 0) = 1 := by
    simp only [meshSize, levelDepth, Nat.cast_zero, sub_zero, zpow_neg, zpow_natCast]
    exact mul_inv_cancel₀ (pow_pos hL0 K).ne'
  have hd' : ((|d| : ℤ) : ℝ) < (L : ℝ) ^ K := by exact_mod_cast hd
  have hside : torusSide L m / 2 = (L : ℝ) ^ m := by
    simp only [torusSide]
    ring
  calc ((|d| : ℤ) : ℝ) * meshSize L (levelDepth K 0)
        < (L : ℝ) ^ K * meshSize L (levelDepth K 0) := mul_lt_mul_of_pos_right hd' hsp
    _ = 1 := hone
    _ ≤ torusSide L m / 2 := by
        rw [hside]
        exact one_le_pow₀ hL1
private theorem finestBaseSite_lowest (hB : SchemeFinestBaseSites)
    (hC : CoordinateDescription) (hL : Conventions.IsAdmissibleBlockingFactor L)
    (hm : 0 < m) (hK : 0 < K) {j : ℕ} (hj : j ≤ K) (y : SiteAtLevel L m K j) :
    finestBaseSite .cornered K j y ∈ sitesIn (refinedBlock j y) ∧
      ∀ z ∈ (sitesIn (refinedBlock j y) : Set (SiteAtLevel L m K 0)),
        ∃ d, IsChartOffset (finestBaseSite .cornered K j y) z d ∧ ∀ μ, 0 ≤ d μ := by
  have hblock := (hC L m hL.1 hL.2 hm).2.2.1 (levelDepth K j) j (by simp only [levelDepth]; omega)
  have himg := (hblock y).2.1
  have hdata : Averaging.OneStep.Parameters 4 2 L K m Matrices.ComplexMatrix2.specialUnitary :=
    ⟨rfl, rfl, rfl, hL.1, hL.2, hK, hm⟩
  have hbase := (hB 4 2 L K m Matrices.ComplexMatrix2.specialUnitary hdata j hj y).2
  obtain ⟨p₀, hp₀, hx₀, hmin⟩ := lowestBlockSite_spec (m := m) hL.1 j y
  have hbase' : ((finestBaseSite .cornered K j y : SiteAtLevel L m K 0) : FourTorus L m) =
      (refinedOffsetSite j y p₀ : FourTorus L m) := by
    rw [hbase, hx₀]
  refine ⟨?_, fun z hz => ?_⟩
  · show ((finestBaseSite .cornered K j y : SiteAtLevel L m K 0) : FourTorus L m) ∈
      refinedBlock j y
    rw [himg, hbase']
    exact ⟨p₀, hp₀, rfl⟩
  · have hz' : (z : FourTorus L m) ∈ refinedBlock j y := hz
    rw [himg] at hz'
    obtain ⟨p, hp, hpz⟩ := hz'
    have hpz' : (refinedOffsetSite j y p : FourTorus L m) = z := hpz
    have hdepth : levelDepth K j + (j : ℤ) = levelDepth K 0 := by
      simp only [levelDepth]
      push_cast
      omega
    have e₁ : (z : FourTorus L m) -
        ((finestBaseSite .cornered K j y : SiteAtLevel L m K 0) : FourTorus L m) =
        ((∑ μ, (p μ - p₀ μ) • unitStep L m (levelDepth K j + (j : ℤ)) μ :
          Site L m (levelDepth K j + (j : ℤ))) : FourTorus L m) := by
      rw [← hpz', hbase', ← refinedOffsetSite_sub]
      rfl
    refine ⟨fun μ => p μ - p₀ μ,
      ⟨Subtype.ext (e₁.trans (coe_sum_unitStep_eq hdepth _)), fun μ => ?_⟩,
      fun μ => by
        have := hmin p hp μ
        show 0 ≤ p μ - p₀ μ
        omega⟩
    refine offset_mul_meshSize_lt hL ?_
    have h₁ := hp μ
    have h₂ := hp₀ μ
    have hle : (L : ℤ) ^ j ≤ (L : ℤ) ^ K :=
      pow_le_pow_right₀ (by have := hL.2; omega) hj
    generalize (L : ℤ) ^ j = T at h₁ h₂ hle
    generalize (L : ℤ) ^ K = T' at hle ⊢
    show |p μ - p₀ μ| < T'
    rcases abs_cases (p μ) with ⟨e, _⟩ | ⟨e, _⟩ <;> rcases abs_cases (p₀ μ) with ⟨e', _⟩ | ⟨e', _⟩ <;>
      rcases abs_cases (p μ - p₀ μ) with ⟨e'', _⟩ | ⟨e'', _⟩ <;> omega
theorem iteratedAverageGaugeLocality_proof (hB : SchemeFinestBaseSites)
    (hC : CoordinateDescription)
    (hG : IteratedAverageGaugeCovariance)
    (hR : IteratedAverageLocality) :
    IteratedAverageGaugeLocality := by
  intro L hL m K hm hK s j hj
  refine ⟨fun y => finestBaseSite_lowest hB hC hL hm hK hj y, ?_, ?_, ?_, ?_, ?_⟩
  · intro U hU u hu
    refine ⟨fun h => ?_, gaugeTransform_mem_domain hG hL hK hm s hU hu j hj⟩
    have h' := gaugeTransform_mem_domain hG hL hK hm s (gaugeTransform_mem hU hu)
      (isGaugeMap_inv hu) j hj h
    rwa [gaugeTransform_inv_gaugeTransform hu] at h'
  · intro U hU u hu hd
    funext c
    exact (hG L hL K m hK hm s j hj U hU u hu c (isBareIterateDefined_of_mem s j hd c)).2
  · intro U hU u hu c
    refine ⟨fun h => ?_, fun h => (hG L hL K m hK hm s j hj U hU u hu c h).1⟩
    have h' := (hG L hL K m hK hm s j hj _ (gaugeTransform_mem hU hu) _ (isGaugeMap_inv hu) c h).1
    rwa [gaugeTransform_inv_gaugeTransform hu] at h'
  · intro U hU u hu c hd
    exact (hG L hL K m hK hm s j hj U hU u hu c hd).2
  · intro U hU U' hU' c hagree
    have hcfg : ∀ {V : BondAtLevel L m K 0 → Matrices.ComplexMatrix2},
        V ∈ gaugeFieldsAtLevel L m K 0 →
        IsGaugeField complexGaugeGroup (bondsWithin (sitesInBondBlockPair 0 c)).bonds V :=
      fun hV => ⟨fun b _ => (Matrix.mem_specialUnitaryGroup_iff.1 (hV.1 b (mem_univ b))).2,
        fun b _ => hV.2 b (mem_univ b)⟩
    have hsame : ∀ b ∈ (bondsWithin (sitesInBondBlockPair 0 c)).bonds, U b = U' b :=
      fun b hb => hagree b ⟨hb.1, hb.2⟩
    have h := hR L hL m K hm hK s j hj c U U' (hcfg hU) (hcfg hU') hsame
    rw [isBareIterateDefined_iff, isBareIterateDefined_iff]
    exact ⟨h.1, fun hd => h.2 hd⟩
end YangMills.Construction.PeriodicLattice
