import YangMills.Construction.Lattice.GaugeCovarianceOfTheTwoSchemesProof
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.PeriodicLattice
open YangMills.Construction.Matrices YangMills.Construction.Averaging
namespace GaugeGroupValues
variable {L m : ℕ} {j j' : ℤ}
theorem inv_mem_compactGaugeGroup {V : ComplexMatrix2} (hV : V ∈ compactGaugeGroup) :
    V⁻¹ ∈ compactGaugeGroup := by apply _root_.YangMills.Construction.PeriodicLattice.BlockAverageContinuity.inv_mem_compactGaugeGroup <;> assumption
theorem mul_mem_compactGaugeGroup {U V : ComplexMatrix2} (hU : U ∈ compactGaugeGroup)
    (hV : V ∈ compactGaugeGroup) : U * V ∈ compactGaugeGroup := by apply _root_.YangMills.Construction.PeriodicLattice.SingleStepEstimate.mul_mem_of_mem <;> assumption
theorem pathHolonomy_mem_compactGaugeGroup {B : Set (Bond L m j')}
    {A : Bond L m j' → ComplexMatrix2} (hA : IsGaugeField compactGaugeGroup B A)
    {γ : List (Bond L m j')} (hγ : ∀ b ∈ γ, b ∈ B) :
    pathHolonomy A γ ∈ compactGaugeGroup := by apply _root_.YangMills.Construction.PeriodicLattice.SingleStepEstimate.pathHolonomy_mem <;> assumption
section Reindexing
variable {α β : Type*}
theorem familyDiameter_comp_equiv (e : α ≃ β) (V : β → ComplexMatrix2) :
    ComplexMatrix2.familyDiameter (V ∘ e) = ComplexMatrix2.familyDiameter V := by apply _root_.YangMills.Construction.PeriodicLattice.SchemeCovariance.familyDiameter_comp_equiv <;> assumption
theorem complexLogMean_comp_equiv [Fintype α] [Fintype β] (e : α ≃ β)
    (V : β → ComplexMatrix2) : complexLogMean (V ∘ e) = complexLogMean V := by apply _root_.YangMills.Construction.Averaging.ExplicitRadiiProof.complexLogMean_comp_equiv <;> assumption
end Reindexing
theorem complexMeanContourHolonomy_mem_compactGaugeGroup
    (hmean : ∀ n : ℕ, 1 ≤ n → ComplexLogMeanProperties n)
    {A : Bond L m j' → ComplexMatrix2} {y : Site L m j} {x : Site L m j'}
    (hvals : ∀ σ, contourHolonomies A y x σ ∈ compactGaugeGroup)
    (hsmall : ComplexMatrix2.familyDiameter (contourHolonomies A y x) < centreOfMassDiameter) :
    complexMeanContourHolonomy A y x ∈ compactGaugeGroup := by
  have : Nonempty (AxisOrdering y x) := ⟨(Finset.equivFin _).symm⟩
  classical
  have hcard : 1 ≤ Fintype.card (AxisOrdering y x) := Fintype.card_pos
  have hprops := hmean _ hcard
  let e : Fin (Fintype.card (AxisOrdering y x)) ≃ AxisOrdering y x := (Fintype.equivFin _).symm
  have hvals' : ∀ a, (contourHolonomies A y x ∘ e) a ∈ compactGaugeGroup := fun a => hvals (e a)
  have hsmall' : ComplexMatrix2.familyDiameter (contourHolonomies A y x ∘ e) <
      centreOfMassDiameter := by
    rw [familyDiameter_comp_equiv]
    exact hsmall
  have hmem := hprops.memRealGroup _ hvals' hsmall'
  rwa [complexLogMean_comp_equiv] at hmem
theorem real_smul_I_smul_hermitianTraceless (r : ℝ) {Y : ComplexMatrix2}
    (hY : Y ∈ ComplexMatrix2.hermitianTraceless) :
    ∃ Y' ∈ ComplexMatrix2.hermitianTraceless,
      ((r : ℂ)) • (Complex.I • Y) = Complex.I • Y' := by
  refine ⟨r • Y, ComplexMatrix2.hermitianTraceless.smul_mem r hY, ?_⟩
  ext a b
  simp only [Matrix.smul_apply, smul_eq_mul, Complex.real_smul]
  ring
end GaugeGroupValues
open GaugeGroupValues in
theorem SchemeValuesInGaugeGroup.holds (hP : BlockPaths.Statement)
    (hM : ComplexLogMeanOfSmallFamilies) (hE : ComplexMatrix2.ExpLogEstimates)
    (hI : ComplexMatrix2.UnitaryLogarithmProperties) : SchemeValuesInGaugeGroup := by
  intro L hL m K n hm hn s c hc A hdef hA
  obtain ⟨-, -, -, hmean, -⟩ := hM
  obtain ⟨-, -, -, -, -, -, -, hlogU, -, -⟩ := hE
  obtain ⟨μ, hμ⟩ := id hc
  obtain ⟨hy, hb⟩ := hP L m K hL.1 hL.2 hm n hn
  obtain ⟨hcoord, -, -, haxial, hin⟩ := hb c μ hμ
  have hzero : (0 : Fin 4 → ℤ) ∈ blockIndexBox L := by
    intro ν
    have hnonneg : 0 ≤ centreToFaceSteps L := by
      have : 13 ≤ L := hL.2
      unfold centreToFaceSteps
      omega
    simpa using hnonneg
  have hcentre : ∀ y : SiteAtLevel L m K (n + 1),
      (y.toSublattice (levelDepth K n) : SiteAtLevel L m K n) ∈
        sitesInBlock (levelDepth K n) y := by
    intro y
    change ((y.toSublattice (levelDepth K n) : SiteAtLevel L m K n) : FourTorus L m) ∈
      unitBlock y
    rw [← (hy y).1.1.2]
    exact ⟨0, hzero, by simp [offsetSite]⟩
  have hbase : (schemeBaseSite s (levelDepth K n) c.source : SiteAtLevel L m K n) ∈
      sitesInBlock (levelDepth K n) c.source := by
    cases s with
    | centred => exact hcentre c.source
    | cornered => exact (hy c.source).1.2.2
  have haxial_eq : axialPath (schemeBaseSite s (levelDepth K n) c.source)
      (schemeBaseSite s (levelDepth K n) c.target) =
        crossingPath c (schemeBaseSite s (levelDepth K n) c.source) := by
    cases s with
    | centred => exact haxial.2.1
    | cornered => exact haxial.2.2
  have hshift : ∀ x ∈ sitesInBlock (levelDepth K n) c.source,
      shiftAcross c x ∈ sitesInBlock (levelDepth K n) c.target := by
    intro x hx
    rw [hcoord.2.2.2.2.1 x hx, ← hcoord.2.2.2.1]
    exact ⟨x, hx, rfl⟩
  have hdefined : ∀ y ∈ ({c.source, c.target} : Set (SiteAtLevel L m K (n + 1))),
      ∀ x ∈ sitesInBlock (levelDepth K n) y, IsContourHolonomyDefined s A y x := by
    intro y hy' x hx
    rcases hy' with rfl | hy'
    · exact hdef.2.1.1 x hx
    · rw [Set.mem_singleton_iff.mp hy']
      rw [Set.mem_singleton_iff.mp hy'] at hx
      exact hdef.2.1.2 x hx
  have hcontour : ∀ y ∈ ({c.source, c.target} : Set (SiteAtLevel L m K (n + 1))),
      ∀ x ∈ sitesInBlock (levelDepth K n) y, contourHolonomy s A y x ∈ compactGaugeGroup := by
    intro y hy' x hx
    have hpaths := hin.1 y (by simpa using hy') x hx
    cases s with
    | cornered => exact pathHolonomy_mem_compactGaugeGroup hA hpaths.2
    | centred =>
      exact complexMeanContourHolonomy_mem_compactGaugeGroup hmean
        (fun σ => pathHolonomy_mem_compactGaugeGroup hA (hpaths.1 _ ⟨σ, rfl⟩))
        (hdefined y hy' x hx).2.2
  have htransport : baseTransport s A c ∈ compactGaugeGroup := by
    unfold baseTransport
    rw [haxial_eq]
    exact pathHolonomy_mem_compactGaugeGroup hA (hin.2 _ hbase)
  have hdefect : ∀ x ∈ sitesInBlock (levelDepth K n) c.source,
      localDefect s A c x ∈ compactGaugeGroup := by
    intro x hx
    exact mul_mem_compactGaugeGroup (mul_mem_compactGaugeGroup (mul_mem_compactGaugeGroup
      (hcontour c.source (Or.inl rfl) x hx) (pathHolonomy_mem_compactGaugeGroup hA (hin.2 x hx)))
      (inv_mem_compactGaugeGroup (hcontour c.target (Or.inr rfl) _ (hshift x hx))))
      (inv_mem_compactGaugeGroup htransport)
  have hlog : ∀ x ∈ sitesInBlock (levelDepth K n) c.source,
      ∃ Y ∈ ComplexMatrix2.hermitianTraceless,
        ComplexMatrix2.logSeries (localDefect s A c x) = Complex.I • Y := by
    intro x hx
    obtain ⟨hunit, hdet⟩ := Matrix.mem_specialUnitaryGroup_iff.1 (hdefect x hx)
    obtain ⟨H, -, -, -, -, -, hH⟩ := hlogU _ hunit (hdef.2.2 x hx)
    exact (hH hdet).2.2.1
  have hsum : ∃ Y ∈ ComplexMatrix2.hermitianTraceless,
      (∑ᶠ x ∈ sitesInBlock (levelDepth K n) c.source,
        ComplexMatrix2.logSeries (localDefect s A c x)) = Complex.I • Y := by
    refine finsum_mem_induction
      (fun Z : ComplexMatrix2 => ∃ Y ∈ ComplexMatrix2.hermitianTraceless, Z = Complex.I • Y)
      ⟨0, ComplexMatrix2.hermitianTraceless.zero_mem, by simp⟩ ?_ hlog
    rintro _ _ ⟨Y, hY, rfl⟩ ⟨Y', hY', rfl⟩
    exact ⟨Y + Y', ComplexMatrix2.hermitianTraceless.add_mem hY hY', by rw [smul_add]⟩
  have hexponent : ∃ Y ∈ ComplexMatrix2.hermitianTraceless,
      (inverseFourthPowerWeight L • ∑ᶠ x ∈ sitesInBlock (levelDepth K n) c.source,
        ComplexMatrix2.logSeries (localDefect s A c x)) = Complex.I • Y := by
    obtain ⟨Y, hY, e⟩ := hsum
    rw [e]
    exact real_smul_I_smul_hermitianTraceless _ hY
  refine ⟨hcontour, hdefect, hexponent, ?_⟩
  have hpos : schemeBlockAverage s A c = positiveBondAverage s A c := by
    unfold schemeBlockAverage
    exact if_pos hc
  rw [hpos]
  unfold positiveBondAverage
  obtain ⟨Y, hY, e⟩ := hexponent
  rw [e]
  exact mul_mem_compactGaugeGroup (hI.1 Y hY).2.2.2 htransport
end YangMills.Construction.PeriodicLattice
