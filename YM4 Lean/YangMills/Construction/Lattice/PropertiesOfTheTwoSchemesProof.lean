import YangMills.Construction.Lattice.DomainsOfTheTwoSchemesProof
import YangMills.Construction.Lattice.ElementaryBoundsOfOneStepProof
import YangMills.Construction.Lattice.IteratesOfTheTwoSchemes
import YangMills.Construction.Lattice.MeanSchemeAverageIsComplexAverage
import YangMills.Construction.Lattice.PropertiesOfTheTwoSchemes
import YangMills.Construction.Lattice.TwoSidedCovarianceOfTheTwoSchemes
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.PeriodicLattice
variable {L m K n : ℕ} {j j' : ℤ}
private theorem exists_offset_of_isParametrizedBy {w : Site L m j'} {Q : Set (Fin 4 → ℤ)}
    {R : Set (FourTorus L m)} (h : IsParametrizedBy w Q R) {x : Site L m j'}
    (hx : (x : FourTorus L m) ∈ R) :
    ∃ p ∈ Q, x = offsetSite w p := by apply _root_.YangMills.Construction.PeriodicLattice.SingleStepEstimate.exists_offset <;> assumption
private theorem zero_mem_blockIndexBox (hL : 1 ≤ L) : (0 : Fin 4 → ℤ) ∈ blockIndexBox L := by apply _root_.YangMills.SharedProofs.p113877 <;> assumption
private theorem single_mem_blockIndexBox (hL : 3 ≤ L) (ν : Fin 4) :
    (Pi.single ν 1 : Fin 4 → ℤ) ∈ blockIndexBox L ∧
      (-Pi.single ν 1 : Fin 4 → ℤ) ∈ blockIndexBox L := by apply _root_.YangMills.SharedProofs.p64624 <;> assumption
private theorem offsetSite_single (w : Site L m j') (ν : Fin 4) :
    offsetSite w (Pi.single ν 1) = w + unitStep L m j' ν := by apply _root_.YangMills.SharedProofs.p21430 <;> assumption
private theorem offsetSite_neg_single (w : Site L m j') (ν : Fin 4) :
    offsetSite w (-Pi.single ν 1) = w - unitStep L m j' ν := by apply _root_.YangMills.SharedProofs.p79766 <;> assumption
private theorem axis_eq_of_sub_eq_unitStep {w : Site L m j'} {R : Set (FourTorus L m)}
    (hL : 3 ≤ L) (h : IsParametrizedBy w (blockIndexBox L) R) {b : Bond L m j'} {ν : Fin 4}
    (hb : b.target - b.source = unitStep L m j' ν) : b.axis = ν := by
  have hs := b.isNeighbour.choose_spec
  have hd : b.target - b.source = unitStep L m j' b.axis ∨
      b.target - b.source = -unitStep L m j' b.axis := hs
  by_contra hne
  rcases hd with hd | hd
  · have e : offsetSite w (Pi.single ν 1) =
        offsetSite w (Pi.single b.axis 1) := by
      rw [offsetSite_single, offsetSite_single, ← hb, hd]
    have := h.1 (single_mem_blockIndexBox hL ν).1
      (single_mem_blockIndexBox hL b.axis).1 e
    have h1 := congrFun this ν
    simp [Pi.single_eq_of_ne (Ne.symm hne)] at h1
  · have e : offsetSite w (Pi.single ν 1) =
        offsetSite w (-Pi.single b.axis 1) := by
      rw [offsetSite_single, offsetSite_neg_single, ← hb, hd, sub_eq_add_neg]
    have := h.1 (single_mem_blockIndexBox hL ν).1
      (single_mem_blockIndexBox hL b.axis).2 e
    have h1 := congrFun this ν
    simp [Pi.single_eq_of_ne (Ne.symm hne)] at h1
private theorem pathHolonomy_congr {U U' : Bond L m j' → Matrices.ComplexMatrix2}
    {Γ : List (Bond L m j')}
    (h : ∀ b ∈ Γ, U b = U' b) : pathHolonomy U Γ = pathHolonomy U' Γ := by apply _root_.YangMills.Construction.PeriodicLattice.ComplexAverageLocality.pathHolonomy_congr <;> assumption
private theorem isGaugeField_congr_inside {X : Set (FourTorus L m)}
    {U U' : Bond L m j' → Matrices.ComplexMatrix2}
    (h : ∀ b ∈ (bondsInside X : Set (Bond L m j')), U b = U' b)
    {G : Set Matrices.ComplexMatrix2}
    (hU : IsGaugeField G (bondsInside X) U) : IsGaugeField G (bondsInside X) U' := by
  refine ⟨fun b hb => h b hb ▸ hU.1 b hb, fun b hb => ?_⟩
  have hr : b.opposite ∈ (bondsInside X : Set (Bond L m j')) := ⟨hb.2, hb.1⟩
  rw [← h b hb, ← h _ hr]
  exact hU.2 b hb
private theorem blockPathProperties_of (hP : BlockPaths.Statement)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hm : 0 < m) (hn : n < K)
    (y : SiteAtLevel L m K (n + 1)) {x : SiteAtLevel L m K n}
    (hx : x ∈ sitesInBlock (levelDepth K n) y) :
    BlockPathProperties y x := by
  obtain ⟨hy, hc⟩ := hP L m K hL.1 hL.2 hm n hn
  obtain ⟨hblock, -, hpaths⟩ := hy y
  obtain ⟨p, hp, rfl⟩ := exists_offset_of_isParametrizedBy hblock.1 hx
  obtain ⟨hcontour, hcomb⟩ := hpaths p hp
  have h3 : 3 ≤ L := by have := hL.2; omega
  refine
    { lowest := ⟨hblock.2.2, fun z hz => ?_⟩
      comb_in_box := hcomb.1
      comb_count_le := fun ν => ?_
      comb_translate := fun ν => ?_
      comb_within := ⟨hcomb.2.2.2.2.2.1 _ (by simp [sitesOfPath]), fun b hb =>
        hcomb.2.2.2.2.2.2 b hb⟩
      contour_within := fun σ => ?_ }
  · obtain ⟨q, hq, rfl⟩ := exists_offset_of_isParametrizedBy hblock.1 hz
    refine ⟨_, (hpaths q hq).2.2.1, fun μ => ?_⟩
    have := (hq μ).1
    omega
  · have e : (coordinateComb (schemeBaseSite .cornered (levelDepth K n) y) (offsetSite
        (y.toSublattice (levelDepth K n)) p)).countP (fun b => decide (b.axis = ν)) =
        countSteps (coordinateComb (blockAnchor (levelDepth K n) y) (offsetSite
          (y.toSublattice (levelDepth K n)) p)) (unitStep L m (levelDepth K n) ν) := by
      unfold countSteps
      apply List.countP_congr
      intro b hb
      simp only [decide_eq_true_eq]
      constructor
      · intro hd
        obtain ⟨μ, hμ⟩ := hcomb.2.2.2.2.1 b hb
        have := axis_eq_of_sub_eq_unitStep h3 hblock.1 hμ
        rw [hd] at this
        rw [this]
        exact hμ
      · exact axis_eq_of_sub_eq_unitStep h3 hblock.1
    rw [e, (hcomb.2.2.2.1 ν).1]
    have := (hcomb.2.2.2.1 ν).2
    omega
  · obtain ⟨-, -, ht, -, -⟩ := hc (Bond.forwardFrom y ν) ν (by simp [Bond.forwardFrom])
    exact (ht _ hx).2
  · have hΓ := hcontour (orderedContour y _ σ) ⟨σ, rfl⟩
    exact ⟨hΓ.2.2.2.1 _ (by simp [sitesOfPath]), fun b hb => hΓ.2.2.2.2 b hb⟩
private theorem contourHolonomyIsLocal_of (hP : BlockPaths.Statement)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hm : 0 < m) (hn : n < K)
    (s : AveragingScheme)
    (y : SiteAtLevel L m K (n + 1)) {x : SiteAtLevel L m K n}
    (hx : x ∈ sitesInBlock (levelDepth K n) y) :
    ContourHolonomyIsLocal s y x := by
  obtain ⟨hy, -⟩ := hP L m K hL.1 hL.2 hm n hn
  obtain ⟨hblock, -, hpaths⟩ := hy y
  obtain ⟨p, hp, rfl⟩ := exists_offset_of_isParametrizedBy hblock.1 hx
  obtain ⟨hcontour, hcomb⟩ := hpaths p hp
  intro W W' hW
  have hW' : ∀ b ∈ (bondsInside (unitBlock y) : Set (BondAtLevel L m K n)), W' b = W b :=
    fun b hb => (hW b hb).symm
  have hconf : IsGaugeField complexGaugeGroup (bondsInside (unitBlock y)) W ↔
      IsGaugeField complexGaugeGroup (bondsInside (unitBlock y)) W' :=
    ⟨isGaugeField_congr_inside hW, isGaugeField_congr_inside hW'⟩
  cases s with
  | centred =>
    have hv : contourHolonomies W y (offsetSite (y.toSublattice (levelDepth K n)) p) =
        contourHolonomies W' y (offsetSite (y.toSublattice (levelDepth K n)) p) := by
      funext σ
      exact pathHolonomy_congr fun b hb => hW b ((hcontour _ ⟨σ, rfl⟩).2.2.2.2 b hb)
    constructor
    · simp only [IsContourHolonomyDefined, hv, hconf]
    · intro _
      simp only [contourHolonomy, complexMeanContourHolonomy, hv]
  | cornered =>
    constructor
    · simp only [IsContourHolonomyDefined, hconf]
    · intro _
      exact pathHolonomy_congr fun b hb => hW b (hcomb.2.2.2.2.2.2 b hb)
private theorem doubleBlockStraightPaths_of (hP : BlockPaths.Statement)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hm : 0 < m) (hn : n < K)
    (s : AveragingScheme) (c : BondAtLevel L m K (n + 1)) (hc : c.IsPositivelyOriented) :
    DoubleBlockStraightPaths s c := by
  obtain ⟨μ, hμ⟩ := hc
  obtain ⟨hy, hcs⟩ := hP L m K hL.1 hL.2 hm n hn
  obtain ⟨-, -, -, hS, hI⟩ := hcs c μ hμ
  have hbase : schemeBaseSite s (levelDepth K n) c.source ∈
      sitesInBlock (levelDepth K n) c.source := by
    cases s with
    | centred =>
      have h := (hy c.source).1.1.2
      show ((c.source.toSublattice (levelDepth K n) : Site L m (levelDepth K n)) : FourTorus L m) ∈
        unitBlock c.source
      rw [← h]
      exact ⟨0, zero_mem_blockIndexBox (by have := hL.2; omega), by simp [offsetSite]⟩
    | cornered => exact (hy c.source).1.2.2
  have hstraight : axialPath (schemeBaseSite s (levelDepth K n) c.source)
      (schemeBaseSite s (levelDepth K n) c.target) =
      crossingPath c (schemeBaseSite s (levelDepth K n) c.source) := by
    cases s with
    | centred => exact hS.2.1
    | cornered => exact hS.2.2
  refine ⟨fun x hx => ⟨Or.inl hx, fun b hb => hI.2 x hx b hb⟩, ?_⟩
  rw [hstraight]
  exact ⟨Or.inl hbase, fun b hb => hI.2 _ hbase b hb⟩
theorem averagingSchemeProperties_holds
    (hP : BlockPaths.Statement)
    (hM : CentredAverageEqComplexBlockAverage)
    (hD : AveragingDomainsOpenAndHolomorphic)
    (hV : SchemeValuesInGaugeGroup)
    (hS : CentredSchemeAtSmallCurvature.Statement)
    (hC : SchemesGaugeCovariant)
    (hI : IteratedAverageGaugeLocality) :
    AveragingSchemeProperties := by
  intro L hL m K n hm hn s
  refine ⟨fun y x hx => ⟨blockPathProperties_of hP hL hm hn y hx,
      contourHolonomyIsLocal_of hP hL hm hn s y hx⟩,
    fun c hc => ⟨doubleBlockStraightPaths_of hP hL hm hn s c hc, ?_, ?_, ?_, ?_, ?_⟩,
    fun j hj => ?_⟩
  · obtain ⟨h₁, h₂, h₃⟩ := hD L hL m K n hm hn s c hc
    exact ⟨h₁, h₂, h₃⟩
  · have h := hM L m K n hL.1 hL.2 hm hn c hc
    exact ⟨Set.ext fun W => h.isOneStepAverageFormed_iff W,
      fun W hW x hx => h.localDefect_eq W ((h.isOneStepAverageFormed_iff W).1 hW) x hx,
      fun W hW => h.oneStepAverage_eq W ((h.isOneStepAverageFormed_iff W).1 hW)⟩
  · intro W hW hG
    obtain ⟨h₁, h₂, h₃, h₄⟩ := hV L hL m K n hm hn s c hc W hW hG
    exact ⟨h₁, h₂, h₃, h₄⟩
  · intro W hG hω
    obtain ⟨h₁, h₂, h₃, h₄, h₅⟩ := hS L hL m K n hm hn c hc W hG hω
    exact ⟨h₁, h₂, h₃, h₄, h₅⟩
  · intro h W hh hW
    obtain ⟨h₁, h₂, h₃, h₄, h₅⟩ := hC L hL m K n hm hn s c hc h W hh hW
    exact ⟨h₁, h₂, h₃, h₄, h₅⟩
  · obtain ⟨h₁, h₂, h₃, h₄, h₅, h₆⟩ := hI L hL m K hm (by omega) s j hj
    exact ⟨h₁, h₂, h₃, h₄, h₅, h₆⟩
end YangMills.Construction.PeriodicLattice
