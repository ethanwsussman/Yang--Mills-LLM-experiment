import YangMills.Construction.Averaging.RadiiBelowTheExplicitBound
import YangMills.Construction.Lattice.BondsWithinSiteSets
import YangMills.Construction.Lattice.ComplexAverageReadsTheDoubleBlockProof
import YangMills.Construction.Lattice.MeanSchemeAverageIsComplexAverage
import YangMills.Construction.Averaging.OneStepToolboxData
import YangMills.Construction.Lattice.SchemesOfTheOneStepToolbox
import Mathlib
set_option autoImplicit false

noncomputable section
namespace YangMills.Construction.PeriodicLattice
variable {L m K n : ℕ}
structure CentredAverageAgreesAt (W : BondAtLevel L m K n → Matrices.ComplexMatrix2)
    (c : BondAtLevel L m K (n + 1)) : Prop where
  formed : IsOneStepAverageFormed .centred W c
  regular : IsRegularAveragingCase (Averaging.smoothingRadius L) W c
  average_eq : oneStepAverage .centred W c = regularAverageValue W c
  of_extension : ∀ U ∈ gaugeFieldsAtLevel L m K n,
    (∀ b ∈ (bondsInDoubleBlock c : Set (BondAtLevel L m K n)), U b = W b) →
      U ∈ (smallPlaquetteFields (Averaging.smoothingRadius L) c :
          Set (BondAtLevel L m K n → Matrices.ComplexMatrix2)) ∧
        IsRegularAveragingCase (Averaging.smoothingRadius L) U c ∧
        Averaging.OneStep.averagingAtRadius U c = oneStepAverage .centred W c
def CentredAverageAgreesOnSmallFields : Prop :=
  ∀ L m K n : ℕ,
    Averaging.OneStep.Parameters 4 2 L K m Matrices.ComplexMatrix2.specialUnitary → n < K →
    ∀ c : BondAtLevel L m K (n + 1), c.IsPositivelyOriented →
      ∀ W : BondAtLevel L m K n → Matrices.ComplexMatrix2,
        IsGaugeField compactGaugeGroup (bondsInDoubleBlock c) W →
        doubleBlockCurvature W c < Averaging.smoothingRadius L → CentredAverageAgreesAt W c
end YangMills.Construction.PeriodicLattice
end

open Set
open scoped Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction
namespace PeriodicLattice
variable {L m K n : ℕ}
namespace CentredAverageSmallFields
theorem pathHolonomy_congr {j : ℤ} {A A' : Bond L m j → Matrices.ComplexMatrix2}
    {γ : List (Bond L m j)} (hA : ∀ b ∈ γ, A b = A' b) : pathHolonomy A γ = pathHolonomy A' γ := by apply _root_.YangMills.Construction.PeriodicLattice.ComplexAverageLocality.pathHolonomy_congr <;> assumption
theorem plaquetteHolonomy_congr {j : ℤ} {A B : Bond L m j → Matrices.ComplexMatrix2}
    {p : Plaquette L m j} (hAB : ∀ b ∈ p.boundaryBonds, A b = B b) :
    plaquetteHolonomy A p = plaquetteHolonomy B p := by
  simp only [plaquetteHolonomy, pathHolonomy, List.map_congr_left hAB]
theorem boundaryBonds_mem_bondsInDoubleBlock (c : BondAtLevel L m K (n + 1))
    {p : PlaquetteAtLevel L m K n}
    (hp : p ∈ (doubleBlockPlaquettes c : Set (PlaquetteAtLevel L m K n))) :
    ∀ b ∈ p.boundaryBonds, b ∈ (bondsInDoubleBlock c : Set (BondAtLevel L m K n)) := by
  intro b hb
  exact Plaquette.LiesIn.boundaryBonds_liesIn
    (Z := {x : SiteAtLevel L m K n | (x : FourTorus L m) ∈ bondDoubleBlock c})
    (fun x hx => hp x hx) b hb
theorem norm_eq_one_of_mem_compactGaugeGroup {g : Matrices.ComplexMatrix2}
    (hg : g ∈ compactGaugeGroup) : ‖g‖ = 1 :=
  CStarRing.norm_of_mem_unitary (Matrix.mem_specialUnitaryGroup_iff.mp hg).1
theorem plaquetteHolonomy_sub_one_le_two {c : BondAtLevel L m K (n + 1)}
    {A : BondAtLevel L m K n → Matrices.ComplexMatrix2}
    (hA : IsGaugeField compactGaugeGroup (bondsInDoubleBlock c) A) {p : PlaquetteAtLevel L m K n}
    (hp : p ∈ (doubleBlockPlaquettes c : Set (PlaquetteAtLevel L m K n))) :
    Matrices.ComplexMatrix2.operatorNorm (plaquetteHolonomy A p - 1) ≤ 2 := by
  have hmem : plaquetteHolonomy A p ∈ compactGaugeGroup := by
    refine Submonoid.list_prod_mem _ fun g hg => ?_
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hg
    exact hA.1 b (boundaryBonds_mem_bondsInDoubleBlock c hp b hb)
  have hone : ‖(1 : Matrices.ComplexMatrix2)‖ = 1 :=
    norm_eq_one_of_mem_compactGaugeGroup (one_mem _)
  calc Matrices.ComplexMatrix2.operatorNorm (plaquetteHolonomy A p - 1)
        ≤ ‖plaquetteHolonomy A p‖ + ‖(1 : Matrices.ComplexMatrix2)‖ := norm_sub_le _ _
    _ = 2 := by rw [norm_eq_one_of_mem_compactGaugeGroup hmem, hone]; norm_num
theorem plaquetteHolonomy_sub_one_le_curvature {c : BondAtLevel L m K (n + 1)}
    {A : BondAtLevel L m K n → Matrices.ComplexMatrix2}
    (hA : IsGaugeField compactGaugeGroup (bondsInDoubleBlock c) A) {p : PlaquetteAtLevel L m K n}
    (hp : p ∈ (doubleBlockPlaquettes c : Set (PlaquetteAtLevel L m K n))) :
    Matrices.ComplexMatrix2.operatorNorm (plaquetteHolonomy A p - 1) ≤ doubleBlockCurvature A c := by
  have hbdd : BddAbove (range fun q : ↥(doubleBlockPlaquettes c : Set (PlaquetteAtLevel L m K n)) =>
      Matrices.ComplexMatrix2.operatorNorm (plaquetteHolonomy A q.1 - 1)) :=
    ⟨2, by rintro _ ⟨q, rfl⟩; exact plaquetteHolonomy_sub_one_le_two hA q.2⟩
  exact le_ciSup hbdd (⟨p, hp⟩ : ↥(doubleBlockPlaquettes c : Set (PlaquetteAtLevel L m K n)))
theorem exists_gaugeField_extension {c : BondAtLevel L m K (n + 1)}
    {A : BondAtLevel L m K n → Matrices.ComplexMatrix2}
    (hA : IsGaugeField compactGaugeGroup (bondsInDoubleBlock c) A) :
    ∃ B ∈ gaugeFieldsAtLevel L m K n,
      ∀ b ∈ (bondsInDoubleBlock c : Set (BondAtLevel L m K n)), B b = A b := by
  classical
  have hopp : ∀ b : BondAtLevel L m K n, b ∈ (bondsInDoubleBlock c : Set (BondAtLevel L m K n)) →
      b.opposite ∈ (bondsInDoubleBlock c : Set (BondAtLevel L m K n)) := fun b hb => ⟨hb.2, hb.1⟩
  refine ⟨fun b => if b ∈ (bondsInDoubleBlock c : Set (BondAtLevel L m K n)) then A b else 1,
    ⟨fun b _ => ?_, fun b _ => ?_⟩, fun b hb => if_pos hb⟩
  · by_cases hb : b ∈ (bondsInDoubleBlock c : Set (BondAtLevel L m K n))
    · simpa only [if_pos hb] using hA.1 b hb
    · dsimp only
      rw [if_neg hb]
      exact SetLike.mem_coe.mpr (one_mem _)
  · by_cases hb : b ∈ (bondsInDoubleBlock c : Set (BondAtLevel L m K n))
    · dsimp only
      rw [if_pos hb, if_pos (hopp b hb)]
      exact hA.2 b hb
    · have hb' : b.opposite ∉ (bondsInDoubleBlock c : Set (BondAtLevel L m K n)) :=
        fun h => hb ⟨h.2, h.1⟩
      dsimp only
      rw [if_neg hb, if_neg hb', inv_one]
theorem regularCase_congr (hP : BlockPaths.Statement) (hodd : Odd L)
    (hL : 13 ≤ L) (hm : 0 < m) (hn : n < K) {c : BondAtLevel L m K (n + 1)}
    (hc : c.IsPositivelyOriented) (ω : ℝ) {A B : BondAtLevel L m K n → Matrices.ComplexMatrix2}
    (hAB : ∀ b ∈ (bondsInDoubleBlock c : Set (BondAtLevel L m K n)), A b = B b) :
    (IsRegularAveragingCase ω A c → IsRegularAveragingCase ω B c) ∧
      regularAverageValue A c = regularAverageValue B c := by
  obtain ⟨μ, hμ⟩ := hc
  obtain ⟨hy, hcμ⟩ := hP L m K hodd hL hm n hn
  obtain ⟨hD, -, -, hS, hPaths⟩ := hcμ c μ hμ
  obtain ⟨-, -, -, hI, hsh, -⟩ := hD
  have hzero : (0 : Fin 4 → ℤ) ∈ blockIndexBox L := by
    intro ν
    have h2 : 0 ≤ centreToFaceSteps L := by
      unfold centreToFaceSteps
      have : (13 : ℤ) ≤ (L : ℤ) := by exact_mod_cast hL
      omega
    simpa using h2
  have hsource : c.source.toSublattice (levelDepth K n) ∈
      sitesInBlock (levelDepth K n) c.source := by
    have himg := (hy c.source).1.1.2
    have : ((offsetSite (c.source.toSublattice (levelDepth K n)) 0 : Site L m (levelDepth K n)) :
        FourTorus L m) ∈ unitBlock c.source := by
      rw [← himg]
      exact ⟨0, hzero, rfl⟩
    simpa [sitesInBlock, offsetSite] using this
  have htarget : ∀ x ∈ sitesInBlock (levelDepth K n) c.source,
      shiftAcross c x ∈ sitesInBlock (levelDepth K n) c.target := by
    intro x hx
    rw [hsh x hx, ← hI]
    exact ⟨x, hx, rfl⟩
  have hcont : ∀ y : SiteAtLevel L m K (n + 1), (y = c.source ∨ y = c.target) →
      ∀ x ∈ sitesInBlock (levelDepth K n) y, contourHolonomies A y x = contourHolonomies B y x := by
    intro y hy' x hx
    funext σ
    exact pathHolonomy_congr fun b hb => hAB b ((hPaths.1 y hy' x hx).1 _ ⟨σ, rfl⟩ b hb)
  have hcross : ∀ x ∈ sitesInBlock (levelDepth K n) c.source,
      pathHolonomy A (crossingPath c x) = pathHolonomy B (crossingPath c x) :=
    fun x hx => pathHolonomy_congr fun b hb => hAB b (hPaths.2 x hx b hb)
  have htransport : parallelTransport A c = parallelTransport B c := by
    unfold parallelTransport
    rw [hS.2.1]
    exact hcross _ hsource
  have hdefect : ∀ x ∈ sitesInBlock (levelDepth K n) c.source,
      crossingDefect A c x = crossingDefect B c x := by
    intro x hx
    unfold crossingDefect meanContourHolonomy
    rw [hcont c.source (Or.inl rfl) x hx, hcont c.target (Or.inr rfl) (shiftAcross c x) (htarget x hx),
      hcross x hx, htransport]
  refine ⟨?_, ?_⟩
  · rintro ⟨hpl, hs, ht, hd⟩
    refine ⟨fun p hp => ?_, fun x hx => ?_, fun x hx => ?_, fun x hx => ?_⟩
    · rw [← plaquetteHolonomy_congr fun b hb =>
        hAB b (boundaryBonds_mem_bondsInDoubleBlock c hp b hb)]
      exact hpl p hp
    · have := hs x hx
      unfold HasContourMean at this ⊢
      rwa [← hcont c.source (Or.inl rfl) x hx]
    · have := ht x hx
      unfold HasContourMean at this ⊢
      rwa [← hcont c.target (Or.inr rfl) x hx]
    · rw [← hdefect x hx]
      exact hd x hx
  · unfold regularAverageValue
    rw [htransport, finsum_mem_congr rfl fun x hx => by rw [hdefect x hx]]
end CentredAverageSmallFields
open CentredAverageSmallFields in
theorem centredAverageAgreesOnSmallFields
    (hR : Averaging.ExplicitRadii.Holds)
    (hC : ComplexAverageIsLocal)
    (hM : CentredAverageEqComplexBlockAverage)
    (hP : BlockPaths.Statement) :
    CentredAverageAgreesOnSmallFields := by
  intro L m K n hpar hn c hc A hA hsmall
  have hodd := hpar.odd_L
  have h13 := hpar.thirteen_le_L
  have hKpos := hpar.K_pos
  have hmpos := hpar.m_pos
  have hS := hR.2.2.1 (⟨L, ⟨hodd, h13⟩, ⟨K, hKpos⟩, ⟨m, hmpos⟩⟩ : Conventions.StandingParameters)
  have hω : Averaging.smoothingRadius L ∈ Ioc (0 : ℝ) (averagingRadiusCap L) :=
    ⟨hpar.smoothingRadius_pos, hpar.smoothingRadius_le⟩
  have hdom : ∀ U ∈ gaugeFieldsAtLevel L m K n,
      (∀ b ∈ (bondsInDoubleBlock c : Set (BondAtLevel L m K n)), U b = A b) →
        U ∈ (smallPlaquetteFields (Averaging.smoothingRadius L) c :
          Set (BondAtLevel L m K n → Matrices.ComplexMatrix2)) := by
    intro U hU hUA
    refine ⟨hU, fun p hp => ?_⟩
    rw [plaquetteHolonomy_congr fun b hb => hUA b (boundaryBonds_mem_bondsInDoubleBlock c hp b hb)]
    exact lt_of_le_of_lt (plaquetteHolonomy_sub_one_le_curvature hA hp) hsmall
  have hregular : ∀ U ∈ gaugeFieldsAtLevel L m K n,
      (∀ b ∈ (bondsInDoubleBlock c : Set (BondAtLevel L m K n)), U b = A b) →
        IsRegularAveragingCase (Averaging.smoothingRadius L) U c :=
    fun U hU hUA => hS.regular _ hω n hn c hc U (hdom U hU hUA)
  obtain ⟨B, hB, hBA⟩ := exists_gaugeField_extension hA
  have hloc := hC L m K n hodd h13 hmpos hn c hc
  have hMC := hM L m K n hodd h13 hmpos hn c hc
  have hAnear : A ∈ (complexAveragingDomainNearOne c :
      Set (BondAtLevel L m K n → Matrices.ComplexMatrix2)) :=
    (hloc.mem_domain_iff B A hBA).mp (hS.complexDomain _ hω n hn c hc B (hdom B hB hBA)).1
  have hcentred : oneStepAverage .centred A c = complexBlockAverageOnPositive A c := by
    rw [hMC.oneStepAverage_eq A hAnear]
    simp only [complexBlockAverage, if_pos hc]
  have hvalue : ∀ U ∈ gaugeFieldsAtLevel L m K n,
      (∀ b ∈ (bondsInDoubleBlock c : Set (BondAtLevel L m K n)), U b = A b) →
        regularAverageValue U c = oneStepAverage .centred A c := by
    intro U hU hUA
    rw [hcentred, ← hloc.average_eq U A hUA]
    exact (hS.complexDomain _ hω n hn c hc U (hdom U hU hUA)).2.symm
  have hcongr := regularCase_congr hP hodd h13 hmpos hn hc (Averaging.smoothingRadius L) hBA
  refine ⟨(hMC.isOneStepAverageFormed_iff A).mpr hAnear, hcongr.1 (hregular B hB hBA), ?_,
    fun U hU hUA => ?_⟩
  · rw [← hcongr.2, hvalue B hB hBA]
  · refine ⟨hdom U hU hUA, hregular U hU hUA, ?_⟩
    have hcase := hregular U hU hUA
    rw [← hvalue U hU hUA]
    simp only [Averaging.OneStep.averagingAtRadius, blockAverage, blockAverageOnPositive, if_pos hc,
      if_pos hcase]
end PeriodicLattice
end YangMills.Construction
