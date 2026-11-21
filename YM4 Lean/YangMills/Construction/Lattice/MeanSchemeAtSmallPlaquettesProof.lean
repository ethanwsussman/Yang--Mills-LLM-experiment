import YangMills.Construction.Lattice.LocalityAndGaugeCovarianceOfTheAveragingMapProof
import YangMills.Construction.Lattice.MeanSchemeIsTheAveragingMapOnSmallConfigurationsProof
import YangMills.Construction.Lattice.SchemeObjectsNearTheIdentityProof
import Mathlib
set_option autoImplicit false
open Set
open scoped Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction
open Matrices
namespace PeriodicLattice
namespace CentredSchemeAtSmallCurvature
section Families
variable {ι κ : Type} [Fintype ι] [Fintype κ]
theorem isLogMean_comp_equiv (e : κ ≃ ι) (𝒢 : Set ComplexMatrix2) (V : ι → ComplexMatrix2)
    (W : ComplexMatrix2) :
    ComplexMatrix2.IsLogMean 𝒢 (V ∘ e) W ↔ ComplexMatrix2.IsLogMean 𝒢 V W := by apply _root_.YangMills.Construction.PeriodicLattice.NearOneBounds.isLogMean_comp_equiv <;> assumption
theorem complexLogMean_comp_equiv (e : κ ≃ ι) (V : ι → ComplexMatrix2) :
    complexLogMean (V ∘ e) = complexLogMean V := by apply _root_.YangMills.SharedProofs.p1929 <;> assumption
theorem logMean_comp_equiv (e : κ ≃ ι) (𝒢 : Set ComplexMatrix2) (V : ι → ComplexMatrix2) :
    ComplexMatrix2.logMean 𝒢 (V ∘ e) = ComplexMatrix2.logMean 𝒢 V :=
  congrArg Classical.epsilon (funext fun W => propext (isLogMean_comp_equiv e 𝒢 V W))
omit [Fintype ι] [Fintype κ] in
theorem familyDiameter_comp_equiv (e : κ ≃ ι) (V : ι → ComplexMatrix2) :
    ComplexMatrix2.familyDiameter (V ∘ e) = ComplexMatrix2.familyDiameter V := by apply _root_.YangMills.Construction.PeriodicLattice.NearOneBounds.familyDiameter_comp_equiv <;> assumption
theorem complexLogMean_eq_logMean [Nonempty ι]
    (hM : ∀ n : ℕ, 1 ≤ n → Averaging.ComplexLogMeanProperties n) {V : ι → ComplexMatrix2}
    (hV : ∀ i, V i ∈ compactGaugeGroup)
    (hd : ComplexMatrix2.familyDiameter V < Averaging.centreOfMassDiameter) :
    complexLogMean V = ComplexMatrix2.logMean compactGaugeGroup V := by
  have e := (Fintype.equivFin ι).symm
  have h := (hM _ Fintype.card_pos).meanEqualsAverage (V ∘ e) (fun i => hV (e i))
    (by rwa [familyDiameter_comp_equiv])
  rwa [logMean_comp_equiv, complexLogMean_comp_equiv, eq_comm] at h
end Families
variable {L m K i : ℕ}
theorem pathHolonomy_congr {j : ℤ} {U W : Bond L m j → ComplexMatrix2} {Γ : List (Bond L m j)}
    (h : ∀ b ∈ Γ, U b = W b) : pathHolonomy U Γ = pathHolonomy W Γ := by apply _root_.YangMills.Construction.PeriodicLattice.ComplexAverageLocality.pathHolonomy_congr <;> assumption
theorem pathHolonomy_mem {j : ℤ} {U : Bond L m j → ComplexMatrix2} {Γ : List (Bond L m j)}
    (h : ∀ b ∈ Γ, U b ∈ compactGaugeGroup) : pathHolonomy U Γ ∈ compactGaugeGroup := by apply _root_.YangMills.SharedProofs.p53533 <;> assumption
theorem boundaryBonds_mem_bondsInDoubleBlock (c : BondAtLevel L m K (i + 1))
    {p : PlaquetteAtLevel L m K i}
    (hp : p ∈ (doubleBlockPlaquettes c : Set (PlaquetteAtLevel L m K i))) :
    ∀ b ∈ p.boundaryBonds, b ∈ (bondsInDoubleBlock c : Set (BondAtLevel L m K i)) := by apply _root_.YangMills.Construction.PeriodicLattice.CentredAverageSmallFields.boundaryBonds_mem_bondsInDoubleBlock <;> assumption
theorem plaquetteHolonomy_le_doubleBlockCurvature {c : BondAtLevel L m K (i + 1)}
    {W : BondAtLevel L m K i → ComplexMatrix2}
    (hW : IsGaugeField compactGaugeGroup (bondsInDoubleBlock c) W)
    {p : PlaquetteAtLevel L m K i}
    (hp : p ∈ (doubleBlockPlaquettes c : Set (PlaquetteAtLevel L m K i))) :
    ComplexMatrix2.operatorNorm (plaquetteHolonomy W p - 1) ≤ doubleBlockCurvature W c := by apply _root_.YangMills.Construction.PeriodicLattice.CentredAverageSmallFields.plaquetteHolonomy_sub_one_le_curvature <;> assumption
theorem exists_gaugeField_extension {c : BondAtLevel L m K (i + 1)}
    {W : BondAtLevel L m K i → ComplexMatrix2}
    (hW : IsGaugeField compactGaugeGroup (bondsInDoubleBlock c) W) :
    ∃ V ∈ gaugeFieldsAtLevel L m K i,
      ∀ b ∈ (bondsInDoubleBlock c : Set (BondAtLevel L m K i)), V b = W b := by apply _root_.YangMills.Construction.PeriodicLattice.CentredAverageSmallFields.exists_gaugeField_extension <;> assumption
theorem isGaugeField_complex {j : ℤ} {ℬ : Set (Bond L m j)} {W : Bond L m j → ComplexMatrix2}
    (hW : IsGaugeField compactGaugeGroup ℬ W) : IsGaugeField complexGaugeGroup ℬ W :=
  ⟨fun b hb => (Matrix.mem_specialUnitaryGroup_iff.mp (hW.1 b hb)).2, hW.2⟩
end CentredSchemeAtSmallCurvature
open CentredSchemeAtSmallCurvature in
theorem CentredSchemeAtSmallCurvature.statement_holds
    (hP : BlockPaths.Statement)
    (hE : Averaging.SmallRadius.EverySmallRadiusSuffices)
    (hM : Averaging.ComplexLogMeanOfSmallFamilies) :
    CentredSchemeAtSmallCurvature.Statement := by
  intro L hL m K n hm hn c hc W hW hsmall
  obtain ⟨μ, hμ⟩ := id hc
  have hKpos : 0 < K := by omega
  have hω : Averaging.smoothingRadius L ∈ Ioc (0 : ℝ) (averagingRadiusCap L) :=
    Averaging.isSmoothingRadius_smoothingRadius hL.1 hL.2
  have hconcl : Averaging.SmallRadius.PropertiesAtBond (Averaging.smoothingRadius L) n c :=
    hE ⟨L, hL, ⟨K, hKpos⟩, ⟨m, hm⟩⟩ _ hω n hn c
  have hsmallFamilies : ∀ U ∈ (smallPlaquetteFields (Averaging.smoothingRadius L) c :
      Set (BondAtLevel L m K n → ComplexMatrix2)),
      ∀ y ∈ ({c.source, c.target} : Set (SiteAtLevel L m K (n + 1))),
      ∀ x ∈ sitesInBlock (levelDepth K n) y,
        ComplexMatrix2.familyDiameter (contourHolonomies U y x) < Averaging.centreOfMassDiameter :=
    (hM.2.2.2.2 (⟨L, hL, ⟨K, hKpos⟩, ⟨m, hm⟩⟩ : Conventions.StandingParameters)).2 _ hω n hn c
  have hfamilies := hM.2.2.2.1
  obtain ⟨hsite, hbond⟩ := hP L m K hL.1 hL.2 hm n hn
  obtain ⟨hDB, -, -, hStraight, hIn⟩ := hbond c μ hμ
  obtain ⟨V, hV, hVW⟩ := exists_gaugeField_extension hW
  have hPW : DoubleBlockPlaquettesNear (Averaging.smoothingRadius L) c W := fun p hp =>
    lt_of_le_of_lt (plaquetteHolonomy_le_doubleBlockCurvature hW hp) hsmall
  have hVdom : V ∈ (smallPlaquetteFields (Averaging.smoothingRadius L) c :
      Set (BondAtLevel L m K n → ComplexMatrix2)) := by
    refine ⟨hV, fun p hp => ?_⟩
    have : plaquetteHolonomy V p = plaquetteHolonomy W p :=
      pathHolonomy_congr fun b hb => hVW b (boundaryBonds_mem_bondsInDoubleBlock c hp b hb)
    rw [this]
    exact hPW p hp
  have hcontour : ∀ y ∈ ({c.source, c.target} : Set (SiteAtLevel L m K (n + 1))),
      ∀ x ∈ sitesInBlock (levelDepth K n) y, contourHolonomies W y x = contourHolonomies V y x := by
    intro y hy x hx
    funext σ
    exact pathHolonomy_congr fun b hb =>
      (hVW b ((hIn.1 y (by simpa using hy) x hx).1 _ ⟨σ, rfl⟩ b hb)).symm
  have hcrossing : ∀ x ∈ sitesInBlock (levelDepth K n) c.source,
      pathHolonomy W (crossingPath c x) = pathHolonomy V (crossingPath c x) := fun x hx =>
    pathHolonomy_congr fun b hb => (hVW b (hIn.2 x hx b hb)).symm
  have hcentre : c.source.toSublattice (levelDepth K n) ∈ sitesInBlock (levelDepth K n) c.source := by
    have hzero : (0 : Fin 4 → ℤ) ∈ blockIndexBox L := by
      intro ν
      have : 0 ≤ centreToFaceSteps L := by
        have := hL.2
        unfold centreToFaceSteps
        omega
      simp only [Pi.zero_apply]
      omega
    have h := (hsite c.source).1.1.2 ▸ mem_image_of_mem
      (fun p => (offsetSite (c.source.toSublattice (levelDepth K n)) p : FourTorus L m)) hzero
    simpa [sitesInBlock, offsetSite] using h
  have htransport : parallelTransport W c = parallelTransport V c := by
    unfold parallelTransport
    rw [hStraight.2.1]
    exact hcrossing _ hcentre
  have htranslated : ∀ x ∈ sitesInBlock (levelDepth K n) c.source,
      shiftAcross c x ∈ sitesInBlock (levelDepth K n) c.target := by
    intro x hx
    rw [hDB.2.2.2.2.1 x hx, ← hDB.2.2.2.1]
    exact mem_image_of_mem _ hx
  have htail : c.source ∈ ({c.source, c.target} : Set (SiteAtLevel L m K (n + 1))) := by simp
  have hhead : c.target ∈ ({c.source, c.target} : Set (SiteAtLevel L m K (n + 1))) := by simp
  have hexists : ∀ y ∈ ({c.source, c.target} : Set (SiteAtLevel L m K (n + 1))),
      ∀ x ∈ sitesInBlock (levelDepth K n) y, HasContourMean W y x := by
    intro y hy x hx
    unfold HasContourMean
    rw [hcontour y hy x hx]
    exact (hconcl.contourMean_spec V hVdom y hy x hx).1
  have hdiameter : ∀ y ∈ ({c.source, c.target} : Set (SiteAtLevel L m K (n + 1))),
      ∀ x ∈ sitesInBlock (levelDepth K n) y,
        ComplexMatrix2.familyDiameter (contourHolonomies W y x) < Averaging.centreOfMassDiameter := by
    intro y hy x hx
    rw [hcontour y hy x hx]
    exact hsmallFamilies V hVdom y hy x hx
  have hmean : ∀ y ∈ ({c.source, c.target} : Set (SiteAtLevel L m K (n + 1))),
      ∀ x ∈ sitesInBlock (levelDepth K n) y,
        contourHolonomy .centred W y x = meanContourHolonomy W y x := by
    intro y hy x hx
    have : Nonempty (AxisOrdering y x) := ⟨(offsetAxes y x).equivFin.symm⟩
    refine complexLogMean_eq_logMean hfamilies (fun σ => ?_) (hdiameter y hy x hx)
    rw [hcontour y hy x hx]
    exact pathHolonomy_mem fun b _ => hV.1 b (mem_univ b)
  have helement : ∀ x ∈ sitesInBlock (levelDepth K n) c.source,
      localDefect .centred W c x = crossingDefect W c x := by
    intro x hx
    unfold localDefect crossingDefect
    rw [hmean _ htail x hx, hmean _ hhead _ (htranslated x hx)]
    rfl
  have hextended : ∀ x ∈ sitesInBlock (levelDepth K n) c.source,
      crossingDefect W c x = crossingDefect V c x := by
    intro x hx
    unfold crossingDefect meanContourHolonomy
    rw [hcontour _ htail x hx, hcontour _ hhead _ (htranslated x hx), hcrossing x hx, htransport]
  have hnear : ∀ x ∈ sitesInBlock (levelDepth K n) c.source,
      ComplexMatrix2.operatorNorm (crossingDefect W c x - 1) < 1 := by
    intro x hx
    rw [hextended x hx]
    exact lt_trans (hconcl.crossingDefect_near hc V hVdom x hx).2 (by norm_num)
  have hcase : IsRegularAveragingCase (Averaging.smoothingRadius L) W c :=
    ⟨hPW, fun x hx => hexists _ htail x hx, fun x hx => hexists _ hhead x hx, hnear⟩
  have hblock : ∀ y ∈ ({c.source, c.target} : Set (SiteAtLevel L m K (n + 1))),
      IsGaugeField complexGaugeGroup (bondsInside (unitBlock y)) W := by
    intro y hy
    have hsub : unitBlock y ⊆ bondDoubleBlock c := by
      rcases hy with rfl | hy
      · exact subset_union_left
      · rw [mem_singleton_iff.mp hy]
        exact subset_union_right
    have hW' := isGaugeField_complex hW
    exact ⟨fun b hb => hW'.1 b ⟨hsub hb.1, hsub hb.2⟩, fun b hb => hW'.2 b ⟨hsub hb.1, hsub hb.2⟩⟩
  have hdefined : ∀ y ∈ ({c.source, c.target} : Set (SiteAtLevel L m K (n + 1))),
      ∀ x ∈ sitesInBlock (levelDepth K n) y, IsContourHolonomyDefined .centred W y x :=
    fun y hy x hx => ⟨hx, hblock y hy, hdiameter y hy x hx⟩
  refine ⟨⟨isGaugeField_complex hW, ⟨fun x hx => hdefined _ htail x hx,
      fun x hx => hdefined _ hhead x hx⟩, fun x hx => ?_⟩, hexists, hmean, hcase, ?_⟩
  · rw [helement x hx]
    exact hnear x hx
  · have hsum : ∑ᶠ x ∈ sitesInBlock (levelDepth K n) c.source,
          ComplexMatrix2.logSeries (localDefect .centred W c x) =
        ∑ᶠ x ∈ sitesInBlock (levelDepth K n) c.source,
          ComplexMatrix2.logSeries (crossingDefect W c x) :=
      finsum_mem_congr rfl fun x hx => by rw [helement x hx]
    simp only [schemeBlockAverage, blockAverage, blockAverageOnPositive, if_pos hc, if_pos hcase,
      positiveBondAverage, regularAverageValue, hsum]
    rfl
end PeriodicLattice
end YangMills.Construction
end
