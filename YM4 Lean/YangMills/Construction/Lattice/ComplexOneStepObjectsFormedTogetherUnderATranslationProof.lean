import YangMills.Construction.Lattice.BondOrientationDichotomy
import YangMills.Construction.Lattice.ComplexOneStepObjectsFormedTogetherUnderATranslation
import YangMills.Construction.Lattice.IsometryCovarianceOfHolonomiesAndActionsProof
import YangMills.Construction.Lattice.OneStepIdentitiesAtAnImageBond
import YangMills.Construction.Lattice.TwistedMapsAndHessiansUnderIsometries
import Mathlib
set_option autoImplicit false
open Set
namespace YangMills.Construction.PeriodicLattice
namespace TranslationComplexStep
variable {L m : ℕ} {j : ℤ} {σ : FourTorus L m ≃ FourTorus L m}
theorem bondPreimage_bondImage (h : MapsCellsAndCubes σ j)
    (h' : MapsCellsAndCubes σ.symm j) (b : Bond L m j) :
    bondPreimage σ (bondImage σ b) = b := by apply _root_.YangMills.Construction.PeriodicLattice.ContourCovariance.bondPreimage_bondImage <;> assumption
theorem bondImage_opposite (h : MapsCellsAndCubes σ j) (b : Bond L m j) :
    bondImage σ b.opposite = (bondImage σ b).opposite := by apply _root_.YangMills.Construction.PeriodicLattice.IsometryCovariance.bondImage_opposite <;> assumption
theorem isGaugeField_of_transport {G : Set Matrices.ComplexMatrix2} {S S' : Set (Bond L m j)}
    (hp : ∀ b : Bond L m j, bondPreimage σ (bondImage σ b) = b)
    (hr : ∀ b : Bond L m j, bondImage σ b.opposite = (bondImage σ b).opposite)
    (himg : ∀ b ∈ S, bondImage σ b ∈ S') {U : Bond L m j → Matrices.ComplexMatrix2}
    (hU : IsGaugeField G S' (transportGaugeField σ U)) : IsGaugeField G S U := by
  refine ⟨fun b hb => ?_, fun b hb => ?_⟩
  · have h := hU.1 _ (himg b hb)
    simpa only [transportGaugeField, hp] using h
  · have h := hU.2 _ (himg b hb)
    rw [← hr] at h
    simpa only [transportGaugeField, hp] using h
theorem transportGaugeField_expTwist
    (hopp : ∀ b : Bond L m j, ¬b.IsPositivelyOriented → b.opposite.IsPositivelyOriented)
    (hpos : ∀ b : Bond L m j, b.IsPositivelyOriented → (bondPreimage σ b).IsPositivelyOriented)
    (hneg : ∀ b : Bond L m j, ¬b.IsPositivelyOriented →
      ¬(bondPreimage σ b).IsPositivelyOriented)
    (hr : ∀ b : Bond L m j, bondPreimage σ b.opposite = (bondPreimage σ b).opposite)
    (A V : Bond L m j → Matrices.ComplexMatrix2) :
    transportGaugeField σ (expTwist A V) =
      expTwist (twistedTransportForm σ V A) (transportGaugeField σ V) := by
  have htw : ∀ b : Bond L m j, b.IsPositivelyOriented →
      twistedTransportForm σ V A b = A (bondPreimage σ b) := by
    intro b hb
    simp only [twistedTransportForm, twistedFormValue, if_pos hb, if_pos (hpos b hb)]
  funext b
  by_cases hb : b.IsPositivelyOriented
  · simp only [transportGaugeField, expTwist, if_pos hb, if_pos (hpos b hb), htw b hb]
  · simp only [transportGaugeField, expTwist, if_neg hb, if_neg (hneg b hb),
      htw _ (hopp b hb), hr]
end TranslationComplexStep
open ComplexTransport TranslationComplexStep in
theorem translationPreservesComplexStepData_holds
    (hO : BondOrientationDichotomy)
    (hG : LatticeIsometryGroupActionStatement)
    (hB : IsometryInvariance.InvariantUnderIsometries)
    (hT : TwistedTransportIsometryInvariance)
    (hA : ComplexAverageEquivariance)
    (hI : TransportIdentitiesAtImageBond) :
    TranslationPreservesComplexStepData := by
  intro L m i σ hL hm hi hσ ht K k hk hik Γ hΓ V
  have hfine : i ≤ levelDepth K k := by
    simp only [levelDepth] at hik ⊢
    omega
  have hfine' : -(m : ℤ) < levelDepth K k := by
    simp only [levelDepth]
    omega
  have hcoarse' : -(m : ℤ) < levelDepth K (k + 1) := by
    simp only [levelDepth]
    omega
  have hgroups := hG L m i hL hm hi
  have hsymm : σ.symm ∈ latticeIsometries L m i := by
    obtain ⟨H, hH⟩ := hgroups.1.1
    have hmem : σ ∈ H := by
      rw [← SetLike.mem_coe, hH]
      exact hσ
    have hinvmem := H.inv_mem hmem
    rw [← SetLike.mem_coe, hH] at hinvmem
    exact hinvmem
  have hC := (hgroups.2.2.2.2 σ hσ _ hfine).1
  have hC' := (hgroups.2.2.2.2 σ.symm hsymm _ hfine).1
  have hpi : ∀ b : BondAtLevel L m K k, bondPreimage σ (bondImage σ b) = b :=
    bondPreimage_bondImage hC hC'
  have hip : ∀ b : BondAtLevel L m K k, bondImage σ (bondPreimage σ b) = b :=
    bondPreimage_bondImage hC' hC
  have hio : ∀ b : BondAtLevel L m K k, bondImage σ b.opposite = (bondImage σ b).opposite :=
    bondImage_opposite hC
  have hpo' : ∀ b : BondAtLevel L m K k,
      bondPreimage σ b.opposite = (bondPreimage σ b).opposite :=
    bondImage_opposite hC'
  have hkeep := (hT L m i σ hL hm hi hσ).1 (Or.inl ht)
  have hkeepF : ∀ b : BondAtLevel L m K k, b.IsPositivelyOriented →
      (bondImage σ b).IsPositivelyOriented :=
    hkeep _ hfine' hfine
  have hkeepC : ∀ c : BondAtLevel L m K (k + 1), c.IsPositivelyOriented →
      (bondImage σ c).IsPositivelyOriented :=
    hkeep _ hcoarse' hik
  have hxorF := hO L m hL hm _ hfine'
  have hxorC := hO L m hL hm _ hcoarse'
  have hopp : ∀ b : BondAtLevel L m K k, ¬b.IsPositivelyOriented →
      b.opposite.IsPositivelyOriented := by
    intro b hb
    rcases hxorF b with h | h
    · exact absurd h.1 hb
    · exact h.1
  have hneg : ∀ b : BondAtLevel L m K k, ¬b.IsPositivelyOriented →
      ¬(bondPreimage σ b).IsPositivelyOriented := by
    intro b hb hp
    exact hb (hip b ▸ hkeepF _ hp)
  have hpos : ∀ b : BondAtLevel L m K k, b.IsPositivelyOriented →
      (bondPreimage σ b).IsPositivelyOriented := by
    intro b hb
    by_contra hp
    have h := hkeepF _ (hopp _ hp)
    rw [hio, hip] at h
    rcases hxorF b with h' | h'
    · exact h'.2 h
    · exact h'.2 hb
  have hE : ∀ A U : BondAtLevel L m K k → Matrices.ComplexMatrix2,
      transportGaugeField σ (expTwist A U) =
        expTwist (twistedTransportForm σ U A) (transportGaugeField σ U) :=
    transportGaugeField_expTwist hopp hpos hneg hpo'
  have hcarry := (hB L m hL hm i hi σ hσ).2.1 K k hk hik
  have hdouble : ∀ c : BondAtLevel L m K (k + 1), c.IsPositivelyOriented →
      ∀ b ∈ (bondsInDoubleBlock c : Set (BondAtLevel L m K k)),
        bondImage σ b ∈ (bondsInDoubleBlock (bondImage σ c) : Set (BondAtLevel L m K k)) := by
    intro c hc b hb
    have hpor : ∀ c : BondAtLevel L m K (k + 1), c.IsPositivelyOriented →
        c.positivelyOriented = c :=
      fun c hc => if_pos hc
    have h := (hcarry c).2.2.2
    rw [hpor c hc, hpor _ (hkeepC c hc)] at h
    rw [← h]
    exact mem_image_of_mem _ hb
  have hdom : ∀ c : BondAtLevel L m K (k + 1), c.IsPositivelyOriented →
      ∀ U : BondAtLevel L m K k → Matrices.ComplexMatrix2,
      (transportGaugeField σ U ∈
          (complexAveragingDomainNearOne (bondImage σ c) :
            Set (BondAtLevel L m K k → Matrices.ComplexMatrix2)) ↔
        U ∈ (complexAveragingDomainNearOne c :
            Set (BondAtLevel L m K k → Matrices.ComplexMatrix2))) := by
    intro c hc U
    constructor
    · intro h
      have hU : IsGaugeField complexGaugeGroup (bondsInDoubleBlock c) U :=
        isGaugeField_of_transport hpi hio (hdouble c hc) h.1.1
      exact ((hA L m K k i σ hL hm hi hσ hk hik U c _ hc (hkeepC c hc) (Or.inl rfl)
        hU).mem_domain_iff rfl).1 h
    · intro h
      exact ((hA L m K k i σ hL hm hi hσ hk hik U c _ hc (hkeepC c hc) (Or.inl rfl)
        h.1.1).mem_domain_iff rfl).2 h
  have havg : ∀ c : BondAtLevel L m K (k + 1), c.IsPositivelyOriented →
      ∀ U : BondAtLevel L m K k → Matrices.ComplexMatrix2,
      U ∈ (complexAveragingDomainNearOne c :
          Set (BondAtLevel L m K k → Matrices.ComplexMatrix2)) →
      complexBlockAverage (transportGaugeField σ U) (bondImage σ c) =
        complexBlockAverage U c := by
    intro c hc U h
    exact (hA L m K k i σ hL hm hi hσ hk hik U c _ hc (hkeepC c hc) (Or.inl rfl)
      h.1.1).average_image rfl h
  have hsame : ∀ c c' : BondAtLevel L m K (k + 1), c.IsPositivelyOriented →
      IsOrientedImage σ c c' → c' = bondImage σ c := by
    intro c c' hc hp
    rcases hp.2 with h | h
    · exact h
    · exfalso
      have h₁ := hkeepC c hc
      have h₂ := hp.1
      rw [h] at h₂
      rcases hxorC (bondImage σ c) with h' | h'
      · exact h'.2 h₂
      · exact h'.2 h₁
  have hinv : ∀ c : BondAtLevel L m K (k + 1), c.IsPositivelyOriented →
      V ∈ (complexAveragingDomainNearOne c :
        Set (BondAtLevel L m K k → Matrices.ComplexMatrix2)) →
      (PivotCoeffInvertible V c ↔
        PivotCoeffInvertible (transportGaugeField σ V) (bondImage σ c)) := by
    intro c hc h
    exact (hI L m K k i σ hL hm hi hσ hk hik V (complexBlockAverage V) c _ hc (hkeepC c hc)
      (Or.inl rfl) h ((hdom c hc V).2 h) rfl).invertible_iff
  refine ⟨⟨fun hf => ⟨?_, ?_⟩, fun hf => ⟨?_, ?_⟩⟩, ?_⟩
  · rintro c' ⟨c, hc, hp⟩
    obtain rfl := hsame c c' (hΓ c hc) hp
    exact (hdom c (hΓ c hc) V).2 (hf.defined c hc)
  · rintro c' ⟨c, hc, hp⟩
    obtain rfl := hsame c c' (hΓ c hc) hp
    exact (hinv c (hΓ c hc) (hf.defined c hc)).1 (hf.pivot_invertible c hc)
  · intro c hc
    exact (hdom c (hΓ c hc) V).1
      (hf.defined _ ⟨c, hc, hkeepC c (hΓ c hc), Or.inl rfl⟩)
  · intro c hc
    have hV := (hdom c (hΓ c hc) V).1
      (hf.defined _ ⟨c, hc, hkeepC c (hΓ c hc), Or.inl rfl⟩)
    exact (hinv c (hΓ c hc) hV).2 (hf.pivot_invertible _ ⟨c, hc, hkeepC c (hΓ c hc), Or.inl rfl⟩)
  · intro hf A _ c hc c' hp
    obtain rfl := hsame c c' (hΓ c hc) hp
    have hcp := hΓ c hc
    have hV := hf.defined c hc
    simp only [ConstraintMapDefined, ← hE]
    constructor
    · rintro ⟨h₁, h₂⟩
      refine ⟨(hdom c hcp _).2 h₁, ?_⟩
      rw [havg c hcp _ h₁, havg c hcp _ hV]
      exact h₂
    · rintro ⟨h₁, h₂⟩
      have h₃ := (hdom c hcp _).1 h₁
      refine ⟨h₃, ?_⟩
      rw [havg c hcp _ h₃, havg c hcp _ hV] at h₂
      exact h₂
end YangMills.Construction.PeriodicLattice
