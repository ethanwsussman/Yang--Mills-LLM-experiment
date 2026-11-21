import YangMills.Construction.Lattice.AveragingMapContinuousOnEachCaseSetProof
import YangMills.Construction.Lattice.AveragingMapIsABorelMapProof
import YangMills.Construction.Lattice.BlocksAndLinearSizesUnderIsometriesProof
import YangMills.Construction.Lattice.BondOrientationDichotomy
import YangMills.Construction.Lattice.BondsWithTheirReverses
import YangMills.Construction.Lattice.ComplexAverageReadsTheDoubleBlock
import YangMills.Construction.Lattice.GaugeOnBlocksUnderIsometriesProof
import YangMills.Construction.Lattice.IsometryCovarianceOfHolonomiesAndActions
import YangMills.Construction.Lattice.LinearisedConstraintAtAFormedBond
import YangMills.Construction.Lattice.OneStepIdentitiesAtAnImageBond
import YangMills.Construction.Lattice.RealConstraintAtAnImageBond
import YangMills.Construction.Lattice.TwistedMapsAndHessiansUnderIsometries
import YangMills.Construction.Matrices.SpecialUnitaryAngleBoundsProof
import YangMills.Construction.Matrices.SpecialUnitaryExpSurjective
import Mathlib
set_option autoImplicit false
open Set Filter
open scoped Matrix.Norms.L2Operator Topology
noncomputable section
namespace YangMills.Construction
open Matrices
namespace PeriodicLattice.RealConstraintImageProof
variable {L m : ℕ}
theorem inv_inv_of_mem_specialUnitary {A : ComplexMatrix2} (h : A ∈ ComplexMatrix2.specialUnitary) :
    A⁻¹⁻¹ = A := by apply _root_.YangMills.SharedProofs.p318 <;> assumption
theorem inv_mul_self_of_mem_specialUnitary {A : ComplexMatrix2}
    (h : A ∈ ComplexMatrix2.specialUnitary) : A⁻¹ * A = 1 := by apply _root_.YangMills.SharedProofs.p1227 <;> assumption
theorem mem_unitaryGroup_of_mem_specialUnitary {A : ComplexMatrix2}
    (h : A ∈ ComplexMatrix2.specialUnitary) : A ∈ Matrix.unitaryGroup (Fin 2) ℂ :=
  (Matrix.mem_specialUnitaryGroup_iff.mp h).1
theorem inv_mem_specialUnitary {A : ComplexMatrix2} (h : A ∈ ComplexMatrix2.specialUnitary) :
    A⁻¹ ∈ ComplexMatrix2.specialUnitary := by apply _root_.YangMills.Construction.Tower.WilsonAnalyticity.inv_mem_specialUnitary <;> assumption
theorem mem_complexGaugeGroup_of_mem_specialUnitary {A : ComplexMatrix2}
    (h : A ∈ ComplexMatrix2.specialUnitary) : A ∈ complexGaugeGroup :=
  (Matrix.mem_specialUnitaryGroup_iff.mp h).2
theorem matExp_I_smul_mem_specialUnitary {X : ComplexMatrix2}
    (hX : X ∈ ComplexMatrix2.hermitianTraceless) :
    ComplexMatrix2.matExp (Complex.I • X) ∈ ComplexMatrix2.specialUnitary := by apply _root_.YangMills.Construction.Matrices.ComplexMatrix2.ExpSurjective.matExp_I_smul_mem_specialUnitary <;> assumption
theorem ofReal_smul_mem_hermitianTraceless {X : ComplexMatrix2}
    (hX : X ∈ ComplexMatrix2.hermitianTraceless) (t : ℝ) :
    (t : ℂ) • X ∈ ComplexMatrix2.hermitianTraceless := by apply _root_.YangMills.SharedProofs.p60538 <;> assumption
theorem inv_mul_inv_inv_mem_logBall_iff (hN : ComplexMatrix2.OperatorNormUnderConjugation)
    {X Y : ComplexMatrix2} (hX : X ∈ ComplexMatrix2.specialUnitary)
    (hY : Y ∈ ComplexMatrix2.specialUnitary) :
    Y⁻¹ * X⁻¹⁻¹ ∈ ComplexMatrix2.logBall ↔ Y * X⁻¹ ∈ ComplexMatrix2.logBall := by
  have hZ : Y * X⁻¹ ∈ ComplexMatrix2.specialUnitary := mul_mem hY (inv_mem_specialUnitary hX)
  have e : Y⁻¹ * X⁻¹⁻¹ - 1 = X⁻¹ * ((Y * X⁻¹)⁻¹ - 1) * X⁻¹⁻¹ := by
    simp only [Matrix.mul_inv_rev, inv_inv_of_mem_specialUnitary hX]
    rw [mul_sub, sub_mul, mul_one, ← mul_assoc, inv_mul_self_of_mem_specialUnitary hX, one_mul]
  show ComplexMatrix2.operatorNorm (Y⁻¹ * X⁻¹⁻¹ - 1) < 1 ↔
    ComplexMatrix2.operatorNorm (Y * X⁻¹ - 1) < 1
  rw [e, hN.2.1 _ _ (mem_unitaryGroup_of_mem_specialUnitary (inv_mem_specialUnitary hX)),
    hN.2.2.1 _ (mem_unitaryGroup_of_mem_specialUnitary hZ)]
section Bonds
variable {j j' : ℤ}
theorem opposite_opposite (c : Bond L m j) : c.opposite.opposite = c := Bond.ext rfl rfl
theorem not_isPositivelyOriented_opposite
    (hX : ∀ b : Bond L m j, Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented)
    {b : Bond L m j} (hb : b.IsPositivelyOriented) : ¬b.opposite.IsPositivelyOriented := by apply _root_.YangMills.Construction.PeriodicLattice.not_isPositivelyOriented_opposite <;> assumption
theorem isPositivelyOriented_opposite
    (hX : ∀ b : Bond L m j, Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented)
    {b : Bond L m j} (hb : ¬b.IsPositivelyOriented) : b.opposite.IsPositivelyOriented := by apply _root_.YangMills.Construction.PeriodicLattice.isPositivelyOriented_opposite <;> assumption
theorem expTwist_congr {P : Set (Bond L m j)} (hP : IsReversalClosed P)
    {A A' W : Bond L m j → ComplexMatrix2} (h : ∀ b ∈ P, A b = A' b) {b : Bond L m j}
    (hb : b ∈ P) : expTwist A W b = expTwist A' W b := by
  unfold expTwist
  by_cases p : b.IsPositivelyOriented
  · simp only [if_pos p, h b hb]
  · simp only [if_neg p, h _ (hP b hb)]
theorem isGaugeField_expTwist {P : Set (Bond L m j)} (hP : IsReversalClosed P)
    (hX : ∀ b : Bond L m j, Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented)
    {A W : Bond L m j → ComplexMatrix2}
    (hW : IsGaugeField compactGaugeGroup P W)
    (hA : ∀ b ∈ P, b.IsPositivelyOriented → A b ∈ ComplexMatrix2.hermitianTraceless) :
    IsGaugeField compactGaugeGroup P (expTwist A W) := by
  have pos : ∀ b ∈ P, b.IsPositivelyOriented →
      ComplexMatrix2.matExp (Complex.I • A b) * W b ∈ ComplexMatrix2.specialUnitary :=
    fun b hb p => mul_mem (matExp_I_smul_mem_specialUnitary (hA b hb p)) (hW.1 b hb)
  refine ⟨fun b hb => ?_, fun b hb => ?_⟩
  · unfold expTwist
    by_cases p : b.IsPositivelyOriented
    · rw [if_pos p]
      exact pos b hb p
    · rw [if_neg p]
      exact inv_mem_specialUnitary (pos _ (hP b hb) (isPositivelyOriented_opposite hX p))
  · unfold expTwist
    by_cases p : b.IsPositivelyOriented
    · rw [if_neg (not_isPositivelyOriented_opposite hX p), if_pos p, opposite_opposite]
    · have q := isPositivelyOriented_opposite hX p
      rw [if_pos q, if_neg p, inv_inv_of_mem_specialUnitary (pos _ (hP b hb) q)]
theorem continuous_matExp : Continuous (ComplexMatrix2.matExp) := by apply _root_.YangMills.Construction.PeriodicLattice.BlockAverageContinuity.continuous_matExp <;> assumption
theorem continuous_matExp_I_smul_ofReal_smul (X : ComplexMatrix2) :
    Continuous fun t : ℝ => ComplexMatrix2.matExp (Complex.I • ((t : ℂ) • X)) :=
  continuous_matExp.comp (by fun_prop)
theorem continuous_matExp_neg_I_smul_ofReal_smul (X : ComplexMatrix2) :
    Continuous fun t : ℝ => ComplexMatrix2.matExp (-(Complex.I • ((t : ℂ) • X))) :=
  continuous_matExp.comp (by fun_prop)
theorem tendsto_expTwist_ofReal_smul {P : Set (Bond L m j)} (hP : IsReversalClosed P)
    {W : Bond L m j → ComplexMatrix2}
    (hW : IsGaugeField compactGaugeGroup P W) (A : Bond L m j → ComplexMatrix2) {b : Bond L m j}
    (hb : b ∈ P) :
    Tendsto (fun t : ℝ => expTwist ((t : ℂ) • A) W b) (𝓝 0) (𝓝 (W b)) := by
  by_cases p : b.IsPositivelyOriented
  · have e : (fun t : ℝ => expTwist ((t : ℂ) • A) W b) =
        fun t : ℝ => ComplexMatrix2.matExp (Complex.I • ((t : ℂ) • A b)) * W b := by
      funext t
      simp only [expTwist, if_pos p, Pi.smul_apply]
    rw [e]
    have hc : Continuous fun t : ℝ => ComplexMatrix2.matExp (Complex.I • ((t : ℂ) • A b)) * W b :=
      (continuous_matExp_I_smul_ofReal_smul (A b)).mul continuous_const
    have h := hc.tendsto 0
    simpa using h
  · have e : (fun t : ℝ => expTwist ((t : ℂ) • A) W b) =
        fun t : ℝ => (W b.opposite)⁻¹ *
          ComplexMatrix2.matExp (-(Complex.I • ((t : ℂ) • A b.opposite))) := by
      funext t
      simp only [expTwist, if_neg p, Pi.smul_apply]
      rw [Matrix.mul_inv_rev]
      exact congrArg _ (Matrix.exp_neg _).symm
    rw [e]
    have hc : Continuous fun t : ℝ =>
        (W b.opposite)⁻¹ * ComplexMatrix2.matExp (-(Complex.I • ((t : ℂ) • A b.opposite))) :=
      continuous_const.mul (continuous_matExp_neg_I_smul_ofReal_smul (A b.opposite))
    have h := hc.tendsto 0
    have hv : W b = (W b.opposite)⁻¹ := by
      have := hW.2 _ (hP b hb)
      rwa [opposite_opposite] at this
    rw [hv]
    simpa using h
theorem tendsto_pathHolonomy {ι : Type*} {l : Filter ι} {U : ι → Bond L m j → ComplexMatrix2}
    {W : Bond L m j → ComplexMatrix2} (Γ : List (Bond L m j))
    (h : ∀ b ∈ Γ, Tendsto (fun s => U s b) l (𝓝 (W b))) :
    Tendsto (fun s => pathHolonomy (U s) Γ) l (𝓝 (pathHolonomy W Γ)) := by
  induction Γ with
  | nil => simpa [pathHolonomy] using tendsto_const_nhds
  | cons b Γ ih =>
    simp only [pathHolonomy, List.map_cons, List.prod_cons]
    exact (h b (by simp)).mul (ih fun b' hb' => h b' (by simp [hb']))
theorem plaquette_finite (hL : 0 < L) : Finite (Plaquette L m j) := by
  have := SeparatedSequences.BaseParameters.site_finite hL m j
  refine Finite.of_injective
    (fun p : Plaquette L m j => (p.origin, p.firstAxis, p.secondAxis)) ?_
  intro p q h
  simp only [Prod.mk.injEq] at h
  exact Plaquette.ext h.1 h.2.1 h.2.2
theorem eventually_doubleBlockPlaquettesNear (hL : 0 < L) {ω : ℝ} {c : Bond L m j}
    {P : Set (Bond L m j')}
    (hB : ∀ p ∈ (doubleBlockPlaquettes c : Set (Plaquette L m j')), ∀ b ∈ p.boundaryBonds, b ∈ P)
    {W : Bond L m j' → ComplexMatrix2} (hW : DoubleBlockPlaquettesNear ω c W) {ι : Type*}
    {l : Filter ι} {U : ι → Bond L m j' → ComplexMatrix2}
    (hU : ∀ b ∈ P, Tendsto (fun s => U s b) l (𝓝 (W b))) :
    ∀ᶠ s in l, DoubleBlockPlaquettesNear ω c (U s) := by
  have := plaquette_finite (L := L) (m := m) (j := j') hL
  have h : ∀ p : Plaquette L m j', ∀ᶠ s in l, p ∈ (doubleBlockPlaquettes c : Set _) →
      ComplexMatrix2.operatorNorm (plaquetteHolonomy (U s) p - 1) < ω := by
    intro p
    by_cases hp : p ∈ (doubleBlockPlaquettes c : Set (Plaquette L m j'))
    · have h1 := tendsto_pathHolonomy p.boundaryBonds fun b hb => hU b (hB p hp b hb)
      have h2 : Tendsto (fun s => ComplexMatrix2.operatorNorm (plaquetteHolonomy (U s) p - 1)) l
          (𝓝 (ComplexMatrix2.operatorNorm (plaquetteHolonomy W p - 1))) := (h1.sub_const 1).norm
      filter_upwards [h2.eventually (gt_mem_nhds (hW p hp))] with s hs _ using hs
    · exact Eventually.of_forall fun _ h => absurd h hp
  filter_upwards [eventually_all.2 h] with s hs p hp using hs p hp
theorem doubleBlockCurvature_lt (hL : 0 < L) {ω : ℝ} (hω : 0 < ω) {c : Bond L m j}
    {U : Bond L m j' → ComplexMatrix2}
    (h : DoubleBlockPlaquettesNear ω c U) : doubleBlockCurvature U c < ω := by
  have := plaquette_finite (L := L) (m := m) (j := j') hL
  unfold doubleBlockCurvature
  rcases isEmpty_or_nonempty ↥(doubleBlockPlaquettes c : Set (Plaquette L m j')) with he | hne
  · rw [Real.iSup_of_isEmpty]
    exact hω
  · obtain ⟨p, hp⟩ := exists_eq_ciSup_of_finite
      (f := fun p : ↥(doubleBlockPlaquettes c : Set (Plaquette L m j')) =>
        ComplexMatrix2.operatorNorm (plaquetteHolonomy U p.1 - 1))
    rw [← hp]
    exact h p.1 p.2
end Bonds
section Step
variable {K k : ℕ}
theorem blockAverage_formed_of_near (hS : AveragingSchemeProperties)
    (hs : Conventions.IsAdmissibleBlockingFactor L) (hm : 0 < m) (hk : k < K)
    {c : BondAtLevel L m K (k + 1)} (hc : c.IsPositivelyOriented)
    {W : BondAtLevel L m K k → ComplexMatrix2}
    (hW : IsGaugeField compactGaugeGroup (bondsInDoubleBlock c) W)
    (hsm : DoubleBlockPlaquettesNear (Averaging.smoothingRadius L) c W) :
    W ∈ (complexAveragingDomainNearOne c : Set (BondAtLevel L m K k → ComplexMatrix2)) ∧
      IsRegularAveragingCase (Averaging.smoothingRadius L) W c ∧
      blockAverage (Averaging.smoothingRadius L) W c = complexBlockAverage W c := by
  have hL : 0 < L := by have := hs.2; omega
  obtain ⟨-, hB, -⟩ := hS L hs m K k hm hk .centred
  obtain ⟨-, -, hD, -, hM, -⟩ := hB c hc
  have hω : 0 < Averaging.smoothingRadius L :=
    (Averaging.isSmoothingRadius_smoothingRadius hs.1 hs.2).1
  have hMean := hM W hW (doubleBlockCurvature_lt hL hω hsm)
  refine ⟨?_, hMean.regular_case, hMean.average_eq.symm.trans (hD.average_eq W hMean.mem_domain)⟩
  rw [← hD.domain_eq]
  exact hMean.mem_domain
theorem complexBlockAverage_mem_specialUnitary (hS : AveragingSchemeProperties)
    (hs : Conventions.IsAdmissibleBlockingFactor L) (hm : 0 < m) (hk : k < K)
    {c : BondAtLevel L m K (k + 1)} (hc : c.IsPositivelyOriented)
    {W : BondAtLevel L m K k → ComplexMatrix2}
    (hW : IsGaugeField compactGaugeGroup (bondsInDoubleBlock c) W)
    (hD : W ∈ (complexAveragingDomainNearOne c : Set (BondAtLevel L m K k → ComplexMatrix2))) :
    complexBlockAverage W c ∈ ComplexMatrix2.specialUnitary := by
  obtain ⟨-, hB, -⟩ := hS L hs m K k hm hk .centred
  obtain ⟨-, -, hDom, hVal, -, -⟩ := hB c hc
  have hd : W ∈ (schemeHolomorphyDomain .centred c : Set (BondAtLevel L m K k → ComplexMatrix2)) := by
    rw [hDom.domain_eq]
    exact hD
  rw [← hDom.average_eq W hd]
  exact (hVal W hd hW).average_mem
structure StepData (c : BondAtLevel L m K (k + 1)) : Prop where
  reversal : IsReversalClosed (bondsInDoubleBlock c : Set (BondAtLevel L m K k))
  orientation : ∀ b : BondAtLevel L m K k, Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented
  edges_mem : ∀ p ∈ (doubleBlockPlaquettes c : Set (Plaquette L m (levelDepth K k))),
    ∀ b ∈ p.boundaryBonds, b ∈ (bondsInDoubleBlock c : Set (BondAtLevel L m K k))
theorem logRatioCurve_blockAverage_eventuallyEq (hS : AveragingSchemeProperties)
    (hs : Conventions.IsAdmissibleBlockingFactor L) (hm : 0 < m) (hk : k < K)
    {c : BondAtLevel L m K (k + 1)} (hc : c.IsPositivelyOriented) (ht : StepData c)
    {W A : BondAtLevel L m K k → ComplexMatrix2}
    (hW : IsGaugeField compactGaugeGroup (bondsInDoubleBlock c) W)
    (hsm : DoubleBlockPlaquettesNear (Averaging.smoothingRadius L) c W)
    (hA : ∀ b ∈ (bondsInDoubleBlock c : Set (BondAtLevel L m K k)), b.IsPositivelyOriented →
      A b ∈ ComplexMatrix2.hermitianTraceless) :
    logRatioCurve (blockAverage (Averaging.smoothingRadius L)) W A c =ᶠ[𝓝 0]
      logRatioCurve complexBlockAverage W A c := by
  have hL : 0 < L := by have := hs.2; omega
  have h := eventually_doubleBlockPlaquettesNear hL ht.edges_mem hsm
    (U := fun t : ℝ => expTwist ((t : ℂ) • A) W)
    (fun b hb => tendsto_expTwist_ofReal_smul ht.reversal hW A hb)
  filter_upwards [h] with t hst
  have hcfg : IsGaugeField compactGaugeGroup (bondsInDoubleBlock c) (expTwist ((t : ℂ) • A) W) :=
    isGaugeField_expTwist ht.reversal ht.orientation hW
      fun b hb p => ofReal_smul_mem_hermitianTraceless (hA b hb p) t
  unfold logRatioCurve
  rw [(blockAverage_formed_of_near hS hs hm hk hc hcfg hst).2.2,
    (blockAverage_formed_of_near hS hs hm hk hc hW hsm).2.2]
theorem linearizedConstraintReal_eq (hS : AveragingSchemeProperties)
    (hs : Conventions.IsAdmissibleBlockingFactor L) (hm : 0 < m) (hk : k < K)
    {c : BondAtLevel L m K (k + 1)} (hc : c.IsPositivelyOriented) (ht : StepData c)
    {W A : BondAtLevel L m K k → ComplexMatrix2}
    (hW : IsGaugeField compactGaugeGroup (bondsInDoubleBlock c) W)
    (hsm : DoubleBlockPlaquettesNear (Averaging.smoothingRadius L) c W)
    (hA : ∀ b ∈ (bondsInDoubleBlock c : Set (BondAtLevel L m K k)), b.IsPositivelyOriented →
      A b ∈ ComplexMatrix2.hermitianTraceless) :
    linearizedConstraintReal (Averaging.smoothingRadius L) W A c = linearizedConstraint W A c := by
  unfold linearizedConstraintReal linearizedConstraint constraintDerivativeForm
  simp only [if_pos hc]
  rw [(logRatioCurve_blockAverage_eventuallyEq hS hs hm hk hc ht hW hsm hA).deriv_eq]
end Step
section Image
variable {σ : FourTorus L m ≃ FourTorus L m} {j j' : ℤ}
structure BondEnds (σ : FourTorus L m ≃ FourTorus L m) (j : ℤ) : Prop where
  forward : ∀ b : Bond L m j, ((bondImage σ b).source : FourTorus L m) = σ b.source ∧
    ((bondImage σ b).target : FourTorus L m) = σ b.target
  backward : ∀ b : Bond L m j, ((bondPreimage σ b).source : FourTorus L m) = σ.symm b.source ∧
    ((bondPreimage σ b).target : FourTorus L m) = σ.symm b.target
theorem symm_mem_latticeIsometries (hG : LatticeIsometryGroupActionStatement)
    (hs : Conventions.IsAdmissibleBlockingFactor L) (hm : 0 < m) {i : ℤ} (hi : -(m : ℤ) ≤ i)
    (hσ : σ ∈ latticeIsometries L m i) : σ.symm ∈ latticeIsometries L m i := by
  obtain ⟨H, hH⟩ := (hG L m i hs hm hi).1.1
  have h1 : σ ∈ H := by
    have : σ ∈ (H : Set (Equiv.Perm (FourTorus L m))) := by rw [hH]; exact hσ
    exact this
  have h3 : σ⁻¹ ∈ (H : Set (Equiv.Perm (FourTorus L m))) := H.inv_mem h1
  rw [hH] at h3
  exact h3
theorem bondEnds_of_mem (hG : LatticeIsometryGroupActionStatement)
    (hs : Conventions.IsAdmissibleBlockingFactor L) (hm : 0 < m) {i : ℤ} (hi : -(m : ℤ) ≤ i)
    (hσ : σ ∈ latticeIsometries L m i) (hj : i ≤ j) : BondEnds σ j :=
  ⟨((hG L m i hs hm hi).2.2.2.2 σ hσ j hj).1.2.2.2.1,
    ((hG L m i hs hm hi).2.2.2.2 σ.symm (symm_mem_latticeIsometries hG hs hm hi hσ) j hj).1.2.2.2.1⟩
theorem bondPreimage_bondImage (h : BondEnds σ j) (c : Bond L m j) :
    bondPreimage σ (bondImage σ c) = c := by
  have e := h.forward c
  have p := h.backward (bondImage σ c)
  apply Bond.ext <;> apply Subtype.ext
  · rw [p.1, e.1]; simp
  · rw [p.2, e.2]; simp
theorem bondImage_bondPreimage (h : BondEnds σ j) (b : Bond L m j) :
    bondImage σ (bondPreimage σ b) = b := by
  have e := h.backward b
  have p := h.forward (bondPreimage σ b)
  apply Bond.ext <;> apply Subtype.ext
  · rw [p.1, e.1]; simp
  · rw [p.2, e.2]; simp
theorem bondPreimage_opposite (h : BondEnds σ j) (b : Bond L m j) :
    bondPreimage σ b.opposite = (bondPreimage σ b).opposite := by
  have p := h.backward b
  have q := h.backward b.opposite
  apply Bond.ext <;> apply Subtype.ext
  · exact q.1.trans p.2.symm
  · exact q.2.trans p.1.symm
theorem mem_image_equiv_iff (X : Set (FourTorus L m)) (t : FourTorus L m) :
    t ∈ σ '' X ↔ σ.symm t ∈ X := by apply _root_.YangMills.Construction.PeriodicLattice.IsometryInvariance.mem_image_equiv_iff <;> assumption
theorem coe_sitePreimage_symm
    (hC : σ '' (sublattice L m j : Set (FourTorus L m)) = sublattice L m j) (y : Site L m j) :
    ((sitePreimage σ.symm y : Site L m j) : FourTorus L m) = σ y := by apply _root_.YangMills.Construction.PeriodicLattice.BlockwiseGauge.coe_sitePreimage_symm <;> assumption
theorem bondDoubleBlock_opposite (c : Bond L m j) : bondDoubleBlock c.opposite = bondDoubleBlock c :=
  union_comm _ _
theorem bondDoubleBlock_bondImage
    (hC : σ '' (sublattice L m j : Set (FourTorus L m)) = sublattice L m j)
    (hE : BondEnds σ j) (hB : IsometryInvariance.MapsBlocks σ j) (c : Bond L m j) :
    bondDoubleBlock (bondImage σ c) = σ '' bondDoubleBlock c := by
  have ht : (bondImage σ c).source = sitePreimage σ.symm c.source :=
    Subtype.ext ((hE.forward c).1.trans (coe_sitePreimage_symm hC _).symm)
  have hh : (bondImage σ c).target = sitePreimage σ.symm c.target :=
    Subtype.ext ((hE.forward c).2.trans (coe_sitePreimage_symm hC _).symm)
  unfold bondDoubleBlock
  rw [image_union, ht, hh]
  exact congrArg₂ (· ∪ ·) (hB 1 c.source).symm (hB 1 c.target).symm
theorem mem_bondsInDoubleBlock_iff (hE : BondEnds σ j') {c : Bond L m j} {c₀ : Bond L m j}
    (hD : bondDoubleBlock c₀ = σ '' bondDoubleBlock c) (b : Bond L m j') :
    b ∈ (bondsInDoubleBlock c₀ : Set (Bond L m j')) ↔
      bondPreimage σ b ∈ (bondsInDoubleBlock c : Set (Bond L m j')) := by
  have p := hE.backward b
  show ((b.source : FourTorus L m) ∈ bondDoubleBlock c₀ ∧
      (b.target : FourTorus L m) ∈ bondDoubleBlock c₀) ↔
    (((bondPreimage σ b).source : FourTorus L m) ∈ bondDoubleBlock c ∧
      ((bondPreimage σ b).target : FourTorus L m) ∈ bondDoubleBlock c)
  rw [p.1, p.2, hD, mem_image_equiv_iff, mem_image_equiv_iff]
theorem twistedFormValue_congr_of_preimage {c c' : Bond L m j}
    (hp : bondPreimage σ c' = c ∨ bondPreimage σ c' = c.opposite) (hc : c.IsPositivelyOriented)
    (hr : ¬c.opposite.IsPositivelyOriented)
    (W F G : Bond L m j → ComplexMatrix2) (h : F c = G c) :
    twistedFormValue σ W F c' = twistedFormValue σ W G c' := by
  unfold twistedFormValue
  rcases hp with e | e
  · rw [e, if_pos hc, if_pos hc, h]
  · rw [e, if_neg hr, if_neg hr, opposite_opposite, h]
theorem twistedFormValue_congr {P : Set (Bond L m j)} (hP : IsReversalClosed P)
    {V A B : Bond L m j → ComplexMatrix2} (h : ∀ b ∈ P, A b = B b) {b : Bond L m j}
    (hb : bondPreimage σ b ∈ P) : twistedFormValue σ V A b = twistedFormValue σ V B b := by
  unfold twistedFormValue
  by_cases p : (bondPreimage σ b).IsPositivelyOriented
  · rw [if_pos p, if_pos p, h _ hb]
  · rw [if_neg p, if_neg p, h _ (hP _ hb)]
end Image
section Twist
variable {σ : FourTorus L m ≃ FourTorus L m} {j : ℤ}
theorem twistedTransportForm_mem_hermitianTraceless {P P' : Set (Bond L m j)}
    (hP : IsReversalClosed P)
    (hX : ∀ b : Bond L m j, Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented)
    (hmem : ∀ b, b ∈ P' ↔ bondPreimage σ b ∈ P) {V A : Bond L m j → ComplexMatrix2}
    (hV : IsGaugeField compactGaugeGroup P V) (hA : IsBondForm compactLieAlgebra A) :
    ∀ b ∈ P', b.IsPositivelyOriented →
      twistedTransportForm σ V A b ∈ ComplexMatrix2.hermitianTraceless := by
  intro b hb p
  simp only [twistedTransportForm, if_pos p, twistedFormValue]
  by_cases h : (bondPreimage σ b).IsPositivelyOriented
  · rw [if_pos h]
    exact hA.1 _ h
  · rw [if_neg h]
    have h2 := isPositivelyOriented_opposite hX h
    have hin := hP _ ((hmem b).1 hb)
    exact ComplexMatrix2.hermitianTraceless.neg_mem
      (ComplexMatrix2.conjugateBy_mem_hermitianTraceless
        (inv_mem_specialUnitary (hV.1 _ hin)) _ (hA.1 _ h2))
theorem expTwist_twistedTransportForm {P P' : Set (Bond L m j)} (hP : IsReversalClosed P)
    (hP' : IsReversalClosed P') (hmem : ∀ b, b ∈ P' ↔ bondPreimage σ b ∈ P)
    (hI : ∀ b ∈ P', b ∈ bondSetTransport σ P) {V B : Bond L m j → ComplexMatrix2}
    (hB : IsBondForm compactLieAlgebra B) (hTw : IsTwistedTransportOn σ P V) :
    ∀ b' ∈ P', expTwist (twistedTransportForm σ V B) (transportGaugeField σ V) b' =
      transportGaugeField σ (expTwist B V) b' := by
  intro b' hb'
  have hAB : ∀ b ∈ P, P.indicator B b = B b := fun b hb => indicator_of_mem hb _
  have hA₀ : P.indicator B ∈ complexFormsOn P := by
    refine ⟨⟨fun b p => ?_, fun b => ?_⟩, ?_⟩
    · by_cases hb : b ∈ P
      · rw [hAB b hb]
        exact (hB.1 b p).2
      · rw [indicator_of_notMem hb]
        exact ComplexMatrix2.traceless.zero_mem
    · by_cases hb : b ∈ P
      · rw [hAB b hb, hAB _ (hP b hb), hB.2 b]
      · have hr : b.opposite ∉ P := fun h => hb (by simpa [opposite_opposite] using hP _ h)
        rw [indicator_of_notMem hb, indicator_of_notMem hr, neg_zero]
    · funext b
      by_cases hb : b ∈ P
      · simp only [indicator_of_mem hb]
      · simp only [indicator_of_notMem hb]
  have hx := hTw.transport_expTwist _ hA₀ b' (hI b' hb')
  have h1 : transportGaugeField σ (expTwist B V) b' =
      transportGaugeField σ (expTwist (P.indicator B) V) b' :=
    expTwist_congr hP (fun b hb => (hAB b hb).symm) ((hmem b').1 hb')
  rw [h1, hx]
  refine expTwist_congr hP' (fun b hb => ?_) hb'
  have hc : ∀ x ∈ P, B x = P.indicator B x := fun x hx => (hAB x hx).symm
  unfold twistedTransportForm
  by_cases p : b.IsPositivelyOriented
  · simp only [if_pos p]
    exact twistedFormValue_congr hP hc ((hmem b).1 hb)
  · simp only [if_neg p]
    rw [twistedFormValue_congr hP hc ((hmem _).1 (hP' b hb))]
end Twist
section Formed
variable {K k : ℕ} {σ : FourTorus L m ≃ FourTorus L m}
theorem complexConstraint_formed_iff (hH : ComplexAverageEquivariance)
    (hR : ComplexAverageIsLocal)
    (hN : ComplexMatrix2.OperatorNormUnderConjugation) (hS : AveragingSchemeProperties)
    (hs : Conventions.IsAdmissibleBlockingFactor L) (hm : 0 < m) {i : ℤ} (hi : -(m : ℤ) ≤ i)
    (hσ : σ ∈ latticeIsometries L m i) (hk : k < K) (hd : i ≤ levelDepth K (k + 1))
    {V E E' : BondAtLevel L m K k → ComplexMatrix2} {c c' : BondAtLevel L m K (k + 1)}
    (hc : c.IsPositivelyOriented) (hc' : c'.IsPositivelyOriented)
    (hcc' : c' = bondImage σ c ∨ c' = (bondImage σ c).opposite)
    (hVr : IsGaugeField compactGaugeGroup (bondsInDoubleBlock c) V)
    (hV : V ∈ (complexAveragingDomainNearOne c : Set (BondAtLevel L m K k → ComplexMatrix2)))
    (hσV : transportGaugeField σ V ∈
      (complexAveragingDomainNearOne c' : Set (BondAtLevel L m K k → ComplexMatrix2)))
    (hEr : IsGaugeField compactGaugeGroup (bondsInDoubleBlock c) E)
    (hEE : ∀ b' ∈ (bondsInDoubleBlock c' : Set (BondAtLevel L m K k)),
      E' b' = transportGaugeField σ E b') :
    (E ∈ (complexAveragingDomainNearOne c : Set (BondAtLevel L m K k → ComplexMatrix2)) ∧
        complexBlockAverage E c * (complexBlockAverage V c)⁻¹ ∈ ComplexMatrix2.logBall) ↔
      (E' ∈ (complexAveragingDomainNearOne c' : Set (BondAtLevel L m K k → ComplexMatrix2)) ∧
        complexBlockAverage E' c' *
          (complexBlockAverage (transportGaugeField σ V) c')⁻¹ ∈ ComplexMatrix2.logBall) := by
  have hRd := hR L m K k hs.1 hs.2 hm hk c' hc'
  have hdom := hRd.mem_domain_iff E' (transportGaugeField σ E) hEE
  have hav : (complexBlockAverage E' c' : ComplexMatrix2) =
      complexBlockAverage (transportGaugeField σ E) c' := by
    simp only [complexBlockAverage, if_pos hc']
    exact hRd.average_eq _ _ hEE
  have H := hH L m K k i σ hs hm hi hσ hk hd E c c' hc hc' hcc'
    ⟨fun b hb => mem_complexGaugeGroup_of_mem_specialUnitary (hEr.1 b hb), hEr.2⟩
  have H0 := hH L m K k i σ hs hm hi hσ hk hd V c c' hc hc' hcc' hV.1.1
  have hiff := H.mem_domain_iff_of_compact hEr
  rw [hdom, hiff, hav]
  refine and_congr_right fun hE => ?_
  rcases hcc' with h | h
  · rw [H.average_image h hE, H0.average_image h hV]
  · rw [H.average_opposite h hE (hiff.2 hE), H0.average_opposite h hV hσV]
    exact (inv_mul_inv_inv_mem_logBall_iff hN
      (complexBlockAverage_mem_specialUnitary hS hs hm hk hc hVr hV)
      (complexBlockAverage_mem_specialUnitary hS hs hm hk hc hEr hE)).symm
end Formed
theorem realConstraintAtImageStatement (hBl : IsometryInvariance.InvariantUnderIsometries)
    (hBP : DoubleBlockStructure.Statement)
    (hH : ComplexAverageEquivariance)
    (hR : ComplexAverageIsLocal)
    (hX : BondOrientationDichotomy)
    (hOb : IsometryImages.Statement)
    (hCov : IsometryCovariance.Statement)
    (hG : LatticeIsometryGroupActionStatement)
    (hF : LinearizedConstraintAtBond.Statement)
    (hId : TransportIdentitiesAtImageBond)
    (hN : ComplexMatrix2.OperatorNormUnderConjugation)
    (hS : AveragingSchemeProperties)
    (hT : TwistedTransportIsometryInvariance) :
    RealConstraintAtImageStatement := by
  intro L m K k i σ hs hm hi hσ hk hd V c c' hc hc' hcc' hcase _ hV
  have hL : 0 < L := by have := hs.2; omega
  have hf0 : 0 ≤ levelDepth K (k + 1) ∧ levelDepth K k = levelDepth K (k + 1) + 1 := by
    constructor <;> simp only [levelDepth] <;> push_cast <;> omega
  have hif : i ≤ levelDepth K k := by omega
  have hmf : -(m : ℤ) < levelDepth K k := by omega
  have hmc : -(m : ℤ) < levelDepth K (k + 1) := by omega
  have hXf := hX L m hs hm (levelDepth K k) hmf
  have hXc := hX L m hs hm (levelDepth K (k + 1)) hmc
  have hEf : BondEnds σ (levelDepth K k) := bondEnds_of_mem hG hs hm hi hσ hif
  have hEc : BondEnds σ (levelDepth K (k + 1)) := bondEnds_of_mem hG hs hm hi hσ hd
  have hCc := ((hG L m i hs hm hi).2.2.2.2 σ hσ (levelDepth K (k + 1)) hd).1.1
  have hBc := ((hBl L m hs hm i hi σ hσ).1 (levelDepth K (k + 1)) hd).1
  have hDimg := bondDoubleBlock_bondImage hCc hEc hBc c
  have hD : bondDoubleBlock c' = σ '' bondDoubleBlock c := by
    rcases hcc' with h | h
    · rw [h]; exact hDimg
    · rw [h, bondDoubleBlock_opposite]; exact hDimg
  have hmem := mem_bondsInDoubleBlock_iff hEf hD
  have hcl : IsReversalClosed (bondsInDoubleBlock c : Set (BondAtLevel L m K k)) :=
    fun _ hb => ⟨hb.2, hb.1⟩
  have hcl' : IsReversalClosed (bondsInDoubleBlock c' : Set (BondAtLevel L m K k)) :=
    fun _ hb => ⟨hb.2, hb.1⟩
  have ht : StepData c := ⟨hcl, hXf, (hBP L m K k hs hm hk c).2.2.2.1⟩
  have ht' : StepData c' := ⟨hcl', hXf, (hBP L m K k hs hm hk c').2.2.2.1⟩
  have hVr := hcase.1
  have hsm : DoubleBlockPlaquettesNear (Averaging.smoothingRadius L) c V :=
    (hcase.2.self_of_nhdsWithin hcase.1).1
  have hT' := (hT L m i σ hs hm hi hσ).2.2.1 (levelDepth K k) hmf hif _ hcl
  have hI : ∀ b ∈ (bondsInDoubleBlock c' : Set (BondAtLevel L m K k)),
      b ∈ bondSetTransport σ (bondsInDoubleBlock c : Set (BondAtLevel L m K k)) :=
    fun b hb => ⟨_, (hmem b).1 hb, bondImage_bondPreimage hEf b⟩
  have hVr' : IsGaugeField compactGaugeGroup (bondsInDoubleBlock c') (transportGaugeField σ V) := by
    have h := ((hT L m i σ hs hm hi hσ).2.1 (levelDepth K k) hif _ hcl V).1 hVr
    exact ⟨fun b hb => h.1 b (hI b hb), fun b hb => h.2 b (hI b hb)⟩
  have hsm' : DoubleBlockPlaquettesNear (Averaging.smoothingRadius L) c'
      (transportGaugeField σ V) := by
    obtain ⟨ε, hε⟩ := hCov
    have hCarry := ((hε L m hs hm i hi σ hσ).1 (levelDepth K k) hif).1 _ V hcl hVr
    have hPl : plaquetteImage σ '' (doubleBlockPlaquettes c : Set (Plaquette L m (levelDepth K k))) =
        doubleBlockPlaquettes c' := by
      have h := ((hOb L m hs hm i hi σ hσ (levelDepth K (k + 1)) (levelDepth K k) hd hf0.1
        hf0.2).2 c).2.2
      have e : bondDoubleBlock c' = bondDoubleBlock (bondImage σ c) := hD.trans hDimg.symm
      unfold doubleBlockPlaquettes at h ⊢
      rw [e]
      exact h
    intro p' hp'
    rw [← hPl] at hp'
    obtain ⟨p, hp, rfl⟩ := hp'
    rw [(hCarry.2 p (ht.edges_mem p hp)).2.2.2]
    exact hsm p hp
  have hf := blockAverage_formed_of_near hS hs hm hk hc hVr hsm
  have hf' := blockAverage_formed_of_near hS hs hm hk hc' hVr' hsm'
  have hp : bondPreimage σ c' = c ∨ bondPreimage σ c' = c.opposite := by
    rcases hcc' with h | h
    · left
      rw [h]
      exact bondPreimage_bondImage hEc c
    · right
      rw [h, bondPreimage_opposite hEc, bondPreimage_bondImage hEc]
  have hAc : ∀ {A : BondAtLevel L m K k → ComplexMatrix2}, IsBondForm compactLieAlgebra A →
      IsBondForm complexLieAlgebra A := fun hA => ⟨fun b hb => (hA.1 b hb).2, hA.2⟩
  refine ⟨hf.2.2, ⟨hVr', ?_⟩, ?_, hf'.1, ?_, ?_⟩
  · have h := eventually_doubleBlockPlaquettesNear hL ht'.edges_mem hsm'
      (l := 𝓝[{U | IsGaugeField compactGaugeGroup (bondsInDoubleBlock c') U}]
        (transportGaugeField σ V)) (U := id)
      (fun b _ => ((continuous_apply b).tendsto _).mono_left nhdsWithin_le_nhds)
    filter_upwards [h, self_mem_nhdsWithin] with U h1 h2
    exact (blockAverage_formed_of_near hS hs hm hk hc' h2 h1).2.1
  · intro A hA
    have hd1 := (hF L m K k hs hm hk _ c' hc' hf'.1).differentiableAt_logRatioCurve A (hAc hA)
    exact hd1.congr_of_eventuallyEq
      (logRatioCurve_blockAverage_eventuallyEq hS hs hm hk hc' ht' hVr' hsm' fun b _ p => hA.1 b p)
  · intro A hA
    have e1 := linearizedConstraintReal_eq hS hs hm hk hc' ht' hVr' hsm'
      (twistedTransportForm_mem_hermitianTraceless hcl hXf hmem hVr hA)
    have e2 := linearizedConstraintReal_eq hS hs hm hk hc ht hVr hsm fun b _ p => hA.1 b p
    have e3 := (hId L m K k i σ hs hm hi hσ hk hd V (blockAverage (Averaging.smoothingRadius L) V)
      c c' hc hc' hcc' hV hf'.1 hf.2.2).linearized A (hAc hA)
    rw [e1, e3]
    exact twistedFormValue_congr_of_preimage hp hc (not_isPositivelyOriented_opposite hXc hc)
      _ _ _ e2.symm
  · intro B hB
    have hEr := isGaugeField_expTwist hcl hXf hVr fun b _ p => hB.1 b p
    have hEE := expTwist_twistedTransportForm hcl hcl' hmem hI hB (hT'.2.2.1 V hV.1.1)
    exact complexConstraint_formed_iff hH hR hN hS hs hm hi hσ hk hd hc hc' hcc' hVr hV hf'.1
      hEr hEE
end PeriodicLattice.RealConstraintImageProof
end YangMills.Construction
