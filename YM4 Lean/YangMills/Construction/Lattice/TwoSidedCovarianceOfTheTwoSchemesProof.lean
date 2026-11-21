import YangMills.Construction.Lattice.GaugeCovarianceOfTheTwoSchemesProof
import YangMills.Construction.Lattice.TwoSidedCovarianceOfTheTwoSchemes
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open YangMills.Construction.Matrices
namespace PeriodicLattice
namespace TwoSidedCovariance
variable {L m K n : ℕ}
theorem mem_unitaryGroup_of_mem_compact {V : ComplexMatrix2} (hV : V ∈ compactGaugeGroup) :
    V ∈ Matrix.unitaryGroup (Fin 2) ℂ :=
  (Matrix.mem_specialUnitaryGroup_iff.1 hV).1
theorem inv_mul_of_mem_compact {V : ComplexMatrix2} (hV : V ∈ compactGaugeGroup) :
    V⁻¹ * V = 1 := by apply _root_.YangMills.SharedProofs.p14555 <;> assumption
theorem inv_inv_of_mem_compact {V : ComplexMatrix2} (hV : V ∈ compactGaugeGroup) :
    V⁻¹⁻¹ = V := by apply _root_.YangMills.Construction.PeriodicLattice.BlockAverageContinuity.inv_inv_of_mem_compactGaugeGroup <;> assumption
theorem fourfold_product_eq {g g' u v A B C D : ComplexMatrix2} (hu : u⁻¹ * u = 1)
    (hv : v⁻¹ * v = 1) (hv' : v⁻¹⁻¹ = v) (hg : g'⁻¹ * g' = 1) (hg' : g'⁻¹⁻¹ = g') :
    (g * A * u⁻¹) * (u * B * v⁻¹) * (g' * C * v⁻¹)⁻¹ * (g * D * g'⁻¹)⁻¹ =
      g * (A * B * C⁻¹ * D⁻¹) * g⁻¹ := by apply _root_.YangMills.SharedProofs.p47100 <;> assumption
theorem familyDiameter_twoSided {ι : Type*}
    (hnorm : ∀ (X g : ComplexMatrix2), g ∈ Matrix.unitaryGroup (Fin 2) ℂ →
      ComplexMatrix2.operatorNorm (g * X * g⁻¹ - 1) = ComplexMatrix2.operatorNorm (X - 1))
    {g k : ComplexMatrix2} (hg : g ∈ compactGaugeGroup) (hk : k ∈ compactGaugeGroup)
    (V : ι → ComplexMatrix2) :
    ComplexMatrix2.familyDiameter (fun i => g * V i * k⁻¹) = ComplexMatrix2.familyDiameter V := by apply _root_.YangMills.Construction.PeriodicLattice.SchemeCovariance.familyDiameter_transform <;> assumption
theorem isGaugeField_gaugeTransform {j : ℤ} {ℬ : Set (Bond L m j)} {h : Site L m j → ComplexMatrix2}
    {W : Bond L m j → ComplexMatrix2}
    (hh : ∀ b ∈ ℬ, h b.source ∈ compactGaugeGroup ∧ h b.target ∈ compactGaugeGroup)
    (hW : IsGaugeField complexGaugeGroup ℬ W) :
    IsGaugeField complexGaugeGroup ℬ (gaugeTransform h W) := by apply _root_.YangMills.Construction.PeriodicLattice.SchemeCovariance.isGaugeField_gaugeTransform <;> assumption
theorem isBondPathFromTo_forwardFlow {j : ℤ} (μ : Fin 4) (k : ℕ) (x : Site L m j) :
    IsBondPathFromTo (forwardAxisPath x μ k) x (x + (k : ℤ) • unitStep L m j μ) := by apply _root_.YangMills.SharedProofs.p4940 <;> assumption
end TwoSidedCovariance
open TwoSidedCovariance in
theorem schemesGaugeCovariant_twoSided
    (hcovariance : GaugeCovarianceStatement)
    (hconj : ComplexMatrix2.NormExpLogConjugation)
    (hlaws : CorneredSchemeGaugeLawAndConjugation)
    (hpaths : BlockPaths.Statement) :
    SchemesGaugeCovariant := by
  intro L hL m K n hm hn s c hc h W hh hW
  obtain ⟨-, -, -, hnorm, -, -, -, -⟩ := hconj
  obtain ⟨hcorner, -, -⟩ := hlaws
  obtain ⟨μ, hμ⟩ := id hc
  obtain ⟨hy, hb⟩ := hpaths L m K hL.1 hL.2 hm n hn
  obtain ⟨hcoord, -, -, hstraight, hin⟩ := hb c μ hμ
  have hlaw := hcorner L hL m K n hm hn c hc h W hh hW
  have hcov := hcovariance L hL m K n hm hn s c hc h W hh hW
  have hsub : ∀ y ∈ ({c.source, c.target} : Set (SiteAtLevel L m K (n + 1))),
      unitBlock y ⊆ bondDoubleBlock c := by
    intro y hy' z hz
    rcases hy' with rfl | rfl
    · exact Or.inl hz
    · exact Or.inr hz
  have hsource : c.source ∈ ({c.source, c.target} : Set (SiteAtLevel L m K (n + 1))) := Or.inl rfl
  have htarget : c.target ∈ ({c.source, c.target} : Set (SiteAtLevel L m K (n + 1))) := Or.inr rfl
  have hzero : (0 : Fin 4 → ℤ) ∈ blockIndexBox L := by
    intro ν
    have hh₀ : 0 ≤ centreToFaceSteps L := by
      have : 13 ≤ L := hL.2
      unfold centreToFaceSteps
      omega
    simpa using hh₀
  have hcentre : ∀ y : SiteAtLevel L m K (n + 1),
      (y.toSublattice (levelDepth K n) : SiteAtLevel L m K n) ∈ sitesInBlock (levelDepth K n) y := by
    intro y
    change ((y.toSublattice (levelDepth K n) : SiteAtLevel L m K n) : FourTorus L m) ∈ unitBlock y
    rw [← (hy y).1.1.2]
    exact ⟨0, hzero, by simp [offsetSite]⟩
  have hbase : ∀ y : SiteAtLevel L m K (n + 1),
      (schemeBaseSite s (levelDepth K n) y : SiteAtLevel L m K n) ∈
        sitesInBlock (levelDepth K n) y := by
    intro y
    cases s with
    | centred => exact hcentre y
    | cornered => exact (hy y).1.2.2
  have hcontours : ∀ y ∈ ({c.source, c.target} : Set (SiteAtLevel L m K (n + 1))),
      ∀ x ∈ sitesInBlock (levelDepth K n) y, ∀ σ : AxisOrdering y x,
        IsBondPathFromTo (orderedContour y x σ) (y.toSublattice (levelDepth K n)) x ∧
          ∀ b ∈ orderedContour y x σ, b ∈ (bondsInDoubleBlock c : Set (BondAtLevel L m K n)) := by
    intro y hy' x hx σ
    refine ⟨?_, ?_⟩
    · have hxb : (x : FourTorus L m) ∈ unitBlock y := hx
      rw [← (hy y).1.1.2] at hxb
      obtain ⟨p, hp, hpx⟩ := hxb
      have hsite : offsetSite (y.toSublattice (levelDepth K n)) p = x := Subtype.ext hpx
      have hin' := ((hy y).2.2 p hp).1
      rw [hsite] at hin'
      exact (hin' _ ⟨σ, rfl⟩).1
    · exact (hin.1 y (by simpa using hy') x hx).1 _ ⟨σ, rfl⟩
  have hvalues : ∀ y ∈ ({c.source, c.target} : Set (SiteAtLevel L m K (n + 1))),
      ∀ x ∈ sitesInBlock (levelDepth K n) y,
        contourHolonomies (gaugeTransform h W) y x =
          fun σ => h (y.toSublattice (levelDepth K n)) * contourHolonomies W y x σ * (h x)⁻¹ := by
    intro y hy' x hx
    funext σ
    obtain ⟨hp, hbonds⟩ := hcontours y hy' x hx σ
    exact hlaw.holonomy_law _ _ _ hp (hsub y hy' (hcentre y)) hbonds
  have hW' : IsGaugeField complexGaugeGroup (bondsInDoubleBlock c) (gaugeTransform h W) :=
    isGaugeField_gaugeTransform (fun b hb => ⟨hh _ hb.1, hh _ hb.2⟩) hW
  have hrestrict : ∀ (V : BondAtLevel L m K n → ComplexMatrix2),
      IsGaugeField complexGaugeGroup (bondsInDoubleBlock c) V →
      ∀ y ∈ ({c.source, c.target} : Set (SiteAtLevel L m K (n + 1))),
        IsGaugeField complexGaugeGroup (bondsInside (unitBlock y)) V := by
    intro V hV y hy'
    have hbond : ∀ b ∈ (bondsInside (unitBlock y) : Set (BondAtLevel L m K n)),
        b ∈ (bondsInDoubleBlock c : Set (BondAtLevel L m K n)) :=
      fun b hb => And.intro (hsub y hy' hb.1) (hsub y hy' hb.2)
    exact ⟨fun b hb => hV.1 b (hbond b hb), fun b hb => hV.2 b (hbond b hb)⟩
  have hdefined : ∀ y ∈ ({c.source, c.target} : Set (SiteAtLevel L m K (n + 1))),
      ∀ x ∈ sitesInBlock (levelDepth K n) y,
        (IsContourHolonomyDefined s (gaugeTransform h W) y x ↔
          IsContourHolonomyDefined s W y x) := by
    intro y hy' x hx
    have hconf := hrestrict W hW y hy'
    have hconf' := hrestrict _ hW' y hy'
    cases s with
    | cornered => exact ⟨fun _ => ⟨hx, hconf, trivial⟩, fun _ => ⟨hx, hconf', trivial⟩⟩
    | centred =>
      have hg : h (y.toSublattice (levelDepth K n)) ∈ compactGaugeGroup :=
        hh _ (hsub y hy' (hcentre y))
      have hk : h x ∈ compactGaugeGroup := hh _ (hsub y hy' hx)
      have hdiam : ComplexMatrix2.familyDiameter (contourHolonomies (gaugeTransform h W) y x) =
          ComplexMatrix2.familyDiameter (contourHolonomies W y x) := by
        rw [hvalues y hy' x hx]
        exact familyDiameter_twoSided hnorm hg hk _
      constructor
      · rintro ⟨-, -, hsize⟩
        have hsize' : ComplexMatrix2.familyDiameter (contourHolonomies (gaugeTransform h W) y x) <
            Averaging.centreOfMassDiameter := hsize
        exact ⟨hx, hconf, hdiam.ge.trans_lt hsize'⟩
      · rintro ⟨-, -, hsize⟩
        have hsize' : ComplexMatrix2.familyDiameter (contourHolonomies W y x) <
            Averaging.centreOfMassDiameter := hsize
        exact ⟨hx, hconf', hdiam.le.trans_lt hsize'⟩
  have hshift : ∀ x ∈ sitesInBlock (levelDepth K n) c.source,
      shiftAcross c x ∈ sitesInBlock (levelDepth K n) c.target := by
    intro x hx
    rw [hcoord.2.2.2.2.1 x hx, ← hcoord.2.2.2.1]
    exact ⟨x, hx, rfl⟩
  have hbase_shift : shiftAcross c (schemeBaseSite s (levelDepth K n) c.source) =
      schemeBaseSite s (levelDepth K n) c.target := by
    rw [hcoord.2.2.2.2.1 _ (hbase c.source)]
    cases s with
    | centred => exact hcoord.1.symm
    | cornered => exact hcoord.2.1.symm
  have haxial_eq : axialPath (schemeBaseSite s (levelDepth K n) c.source)
      (schemeBaseSite s (levelDepth K n) c.target) =
        crossingPath c (schemeBaseSite s (levelDepth K n) c.source) := by
    cases s with
    | centred => exact hstraight.2.1
    | cornered => exact hstraight.2.2
  have hcross : ∀ x ∈ sitesInBlock (levelDepth K n) c.source,
      IsBondPathFromTo (crossingPath c x) x (shiftAcross c x) ∧
        ∀ b ∈ crossingPath c x, b ∈ (bondsInDoubleBlock c : Set (BondAtLevel L m K n)) := by
    intro x hx
    refine ⟨?_, hin.2 x hx⟩
    rw [(hstraight.1 x hx).2.1, hcoord.2.2.2.2.1 x hx]
    exact isBondPathFromTo_forwardFlow μ L x
  set g := h (schemeBaseSite s (levelDepth K n) c.source) with hgdef
  set g' := h (schemeBaseSite s (levelDepth K n) c.target) with hg'def
  have hgG : g ∈ compactGaugeGroup := hh _ (hsub _ hsource (hbase c.source))
  have hg'G : g' ∈ compactGaugeGroup := hh _ (hsub _ htarget (hbase c.target))
  have htransport : baseTransport s (gaugeTransform h W) c =
      g * baseTransport s W c * g'⁻¹ := by
    have hcross₂ := hcross _ (hbase c.source)
    rw [hbase_shift] at hcross₂
    unfold baseTransport
    rw [haxial_eq]
    exact hlaw.holonomy_law _ _ _ hcross₂.1 (hsub _ hsource (hbase c.source)) hcross₂.2
  have hdefect : AreContourHolonomiesDefined s W c → ∀ x ∈ sitesInBlock (levelDepth K n) c.source,
      localDefect s (gaugeTransform h W) c x = g * localDefect s W c x * g⁻¹ := by
    intro hd x hx
    have hx' := hshift x hx
    have hxG : h x ∈ compactGaugeGroup := hh _ (hsub _ hsource hx)
    have hx'G : h (shiftAcross c x) ∈ compactGaugeGroup := hh _ (hsub _ htarget hx')
    have hcross₁ := hcross x hx
    have hb₁ : pathHolonomy (gaugeTransform h W) (crossingPath c x) =
        h x * pathHolonomy W (crossingPath c x) * (h (shiftAcross c x))⁻¹ :=
      hlaw.holonomy_law _ _ _ hcross₁.1 (hsub _ hsource hx) hcross₁.2
    have hc₁ := (hcov.contour c.source hsource x hx (hd.1 x hx)).2
    have hc₂ := (hcov.contour c.target htarget _ hx' (hd.2 _ hx')).2
    unfold localDefect
    rw [hc₁, hc₂, hb₁, htransport]
    exact fourfold_product_eq (inv_mul_of_mem_compact hxG) (inv_mul_of_mem_compact hx'G)
      (inv_inv_of_mem_compact hx'G) (inv_mul_of_mem_compact hg'G) (inv_inv_of_mem_compact hg'G)
  have hvariables : AreContourHolonomiesDefined s (gaugeTransform h W) c →
      AreContourHolonomiesDefined s W c := fun hd =>
    ⟨fun x hx => (hdefined c.source hsource x hx).1 (hd.1 x hx),
      fun x hx => (hdefined c.target htarget x hx).1 (hd.2 x hx)⟩
  refine ⟨hdefined, fun y hy' x hx hd => (hcov.contour y hy' x hx hd).2, ⟨?_, ?_⟩,
    fun hd => (hcov.average hd).2, hdefect⟩
  · rintro ⟨-, hd, hsmall⟩
    have hd' := hvariables hd
    refine ⟨hW, hd', fun x hx => ?_⟩
    have hs := hsmall x hx
    rw [hdefect hd' x hx, hnorm _ g (mem_unitaryGroup_of_mem_compact hgG)] at hs
    exact hs
  · exact fun hd => (hcov.average hd).1
end PeriodicLattice
end YangMills.Construction
