import YangMills.Construction.Averaging.RadiiBelowTheExplicitBoundProof
import YangMills.Construction.Lattice.CovarianceOfComplexContourVariablesProof
import YangMills.Construction.Lattice.ElementaryBoundsOfOneStepProof
import YangMills.Construction.Lattice.GaugeCovarianceOfTheTwoSchemes
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.PeriodicLattice
open Matrices Averaging Conventions
namespace SchemeCovariance
variable {L m K n : ℕ}
theorem isUnit_det_of_mem {U : ComplexMatrix2} (hU : U ∈ compactGaugeGroup) : IsUnit U.det := by apply _root_.YangMills.Construction.PeriodicLattice.SingleStepEstimate.det_isUnit_of_mem <;> assumption
theorem mem_unitaryGroup_of_mem {U : ComplexMatrix2} (hU : U ∈ compactGaugeGroup) :
    U ∈ Matrix.unitaryGroup (Fin 2) ℂ :=
  (Matrix.mem_specialUnitaryGroup_iff.1 hU).1
theorem inv_mul_eq_one_of_mem {U : ComplexMatrix2} (hU : U ∈ compactGaugeGroup) : U⁻¹ * U = 1 := by apply _root_.YangMills.SharedProofs.p14555 <;> assumption
theorem mul_inv_eq_one_of_mem {U : ComplexMatrix2} (hU : U ∈ compactGaugeGroup) : U * U⁻¹ = 1 := by apply _root_.YangMills.SharedProofs.p16098 <;> assumption
theorem inv_inv_of_mem {U : ComplexMatrix2} (hU : U ∈ compactGaugeGroup) : U⁻¹⁻¹ = U := by apply _root_.YangMills.Construction.PeriodicLattice.BlockAverageContinuity.inv_inv_of_mem_compactGaugeGroup <;> assumption
theorem inv_mem_compact {U : ComplexMatrix2} (hU : U ∈ compactGaugeGroup) :
    U⁻¹ ∈ compactGaugeGroup := by apply _root_.YangMills.Construction.PeriodicLattice.BlockAverageContinuity.inv_mem_compactGaugeGroup <;> assumption
theorem transform_mul_transform_inv {g k : ComplexMatrix2} (hk : k ∈ compactGaugeGroup)
    (A B : ComplexMatrix2) :
    (g * A * k⁻¹) * (g * B * k⁻¹)⁻¹ = g * (A * B⁻¹) * g⁻¹ := by
  rw [Matrix.mul_inv_rev, Matrix.mul_inv_rev, inv_inv_of_mem hk]
  calc g * A * k⁻¹ * (k * (B⁻¹ * g⁻¹)) = g * A * (k⁻¹ * k) * (B⁻¹ * g⁻¹) := by
        simp only [mul_assoc]
    _ = g * (A * B⁻¹) * g⁻¹ := by
        rw [inv_mul_eq_one_of_mem hk, mul_one]
        simp only [mul_assoc]
theorem fourFactor_product {g g' u v A B C D : ComplexMatrix2} (hu : u⁻¹ * u = 1)
    (hv : v⁻¹ * v = 1) (hv' : v⁻¹⁻¹ = v) (hg : g'⁻¹ * g' = 1) (hg' : g'⁻¹⁻¹ = g') :
    (g * A * u⁻¹) * (u * B * v⁻¹) * (g' * C * v⁻¹)⁻¹ * (g * D * g'⁻¹)⁻¹ =
      g * (A * B * C⁻¹ * D⁻¹) * g⁻¹ := by apply _root_.YangMills.SharedProofs.p47100 <;> assumption
theorem conj_finsum_mem {g : ComplexMatrix2} (hg : g ∈ compactGaugeGroup) {ι : Type*} (S : Set ι)
    (f : ι → ComplexMatrix2) :
    g * (∑ᶠ x ∈ S, f x) * g⁻¹ = ∑ᶠ x ∈ S, g * f x * g⁻¹ := by
  let e : ComplexMatrix2 ≃+ ComplexMatrix2 :=
    { toFun := fun X => g * X * g⁻¹
      invFun := fun X => g⁻¹ * X * g
      left_inv := fun X => by
        change g⁻¹ * (g * X * g⁻¹) * g = X
        calc g⁻¹ * (g * X * g⁻¹) * g = (g⁻¹ * g) * X * (g⁻¹ * g) := by simp only [mul_assoc]
          _ = X := by rw [inv_mul_eq_one_of_mem hg, one_mul, mul_one]
      right_inv := fun X => by
        change g * (g⁻¹ * X * g) * g⁻¹ = X
        calc g * (g⁻¹ * X * g) * g⁻¹ = (g * g⁻¹) * X * (g * g⁻¹) := by simp only [mul_assoc]
          _ = X := by rw [mul_inv_eq_one_of_mem hg, one_mul, mul_one]
      map_add' := fun X Y => by
        change g * (X + Y) * g⁻¹ = g * X * g⁻¹ + g * Y * g⁻¹
        rw [mul_add, add_mul] }
  classical
  rw [finsum_mem_def, finsum_mem_def]
  change e (∑ᶠ x, S.indicator f x) = _
  rw [AddEquiv.map_finsum]
  refine finsum_congr fun x => ?_
  by_cases hx : x ∈ S
  · simp only [Set.indicator_of_mem hx]
    rfl
  · simp only [Set.indicator_of_notMem hx, map_zero]
section Families
variable {ι κ : Type*}
theorem familyDiameter_comp_equiv (e : ι ≃ κ) (V : κ → ComplexMatrix2) :
    ComplexMatrix2.familyDiameter (V ∘ e) = ComplexMatrix2.familyDiameter V := by
  unfold ComplexMatrix2.familyDiameter
  exact (e.prodCongr e).iSup_congr fun _ => rfl
theorem complexLogMean_comp_equiv [Fintype ι] [Fintype κ] (e : ι ≃ κ) (V : κ → ComplexMatrix2) :
    complexLogMean (V ∘ e) = complexLogMean V := by apply _root_.YangMills.Construction.Averaging.ExplicitRadiiProof.complexLogMean_comp_equiv <;> assumption
theorem complexLogMean_conj (hmean : ∀ n : ℕ, 1 ≤ n → ComplexLogMeanProperties n)
    [Fintype ι] [Nonempty ι] (V : ι → ComplexMatrix2) (hV : ∀ i, V i ∈ complexGaugeGroup)
    (hd : ComplexMatrix2.familyDiameter V < centreOfMassDiameter) {A B : ComplexMatrix2}
    (hA : A ∈ compactGaugeGroup) (hB : B ∈ compactGaugeGroup) :
    complexLogMean (fun i => A * V i * B) = A * complexLogMean V * B := by
  let e := Fintype.equivFin ι
  have hn : 1 ≤ Fintype.card ι := Fintype.card_pos
  have hsmall : V ∘ e.symm ∈ smallComplexFamilies (Fintype.card ι) :=
    ⟨fun i => hV _, by rw [familyDiameter_comp_equiv]; exact hd⟩
  have h := (hmean _ hn).covariant _ hsmall A hA B hB
  rw [complexLogMean_comp_equiv] at h
  exact (complexLogMean_comp_equiv e.symm fun i => A * V i * B).symm.trans h
theorem familyDiameter_transform
    (hnorm : ∀ (X g : ComplexMatrix2), g ∈ Matrix.unitaryGroup (Fin 2) ℂ →
      ComplexMatrix2.operatorNorm (g * X * g⁻¹ - 1) = ComplexMatrix2.operatorNorm (X - 1))
    {g k : ComplexMatrix2} (hg : g ∈ compactGaugeGroup) (hk : k ∈ compactGaugeGroup)
    (V : ι → ComplexMatrix2) :
    ComplexMatrix2.familyDiameter (fun i => g * V i * k⁻¹) = ComplexMatrix2.familyDiameter V := by
  unfold ComplexMatrix2.familyDiameter
  refine iSup_congr fun p => ?_
  rw [transform_mul_transform_inv hk]
  exact hnorm _ g (mem_unitaryGroup_of_mem hg)
end Families
theorem isGaugeField_gaugeTransform {j : ℤ} {ℬ : Set (Bond L m j)} {h : Site L m j → ComplexMatrix2}
    {W : Bond L m j → ComplexMatrix2}
    (hh : ∀ b ∈ ℬ, h b.source ∈ compactGaugeGroup ∧ h b.target ∈ compactGaugeGroup)
    (hW : IsGaugeField complexGaugeGroup ℬ W) :
    IsGaugeField complexGaugeGroup ℬ (gaugeTransform h W) := by
  constructor
  · intro b hb
    obtain ⟨h₁, h₂⟩ := hh b hb
    have hdet : (W b).det = 1 := hW.1 b hb
    change (h b.source * W b * (h b.target)⁻¹).det = 1
    rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_nonsing_inv,
      (Matrix.mem_specialUnitaryGroup_iff.1 h₁).2, (Matrix.mem_specialUnitaryGroup_iff.1 h₂).2, hdet]
    simp
  · intro b hb
    obtain ⟨h₁, h₂⟩ := hh b hb
    change h b.opposite.source * W b.opposite * (h b.opposite.target)⁻¹ =
      (h b.source * W b * (h b.target)⁻¹)⁻¹
    rw [hW.2 b hb, Matrix.mul_inv_rev, Matrix.mul_inv_rev, inv_inv_of_mem h₂]
    simp only [Bond.opposite, mul_assoc]
theorem pathHolonomy_mem_complex {j : ℤ} {W : Bond L m j → ComplexMatrix2} {Γ : List (Bond L m j)}
    (hΓ : ∀ b ∈ Γ, W b ∈ complexGaugeGroup) : pathHolonomy W Γ ∈ complexGaugeGroup := by apply _root_.YangMills.Construction.PeriodicLattice.ContourCovariance.pathHolonomy_mem_complexGaugeGroup <;> assumption
theorem isBondPathFromTo_forwardFlow {j : ℤ} (μ : Fin 4) (k : ℕ) (x : Site L m j) :
    IsBondPathFromTo (forwardAxisPath x μ k) x (x + (k : ℤ) • unitStep L m j μ) := by apply _root_.YangMills.SharedProofs.p4940 <;> assumption
theorem schemeBlockAverage_of_positive {j j' : ℤ} (s : AveragingScheme)
    (W : Bond L m j' → ComplexMatrix2) {c : Bond L m j} (hc : c.IsPositivelyOriented) :
    schemeBlockAverage s W c = positiveBondAverage s W c := by
  unfold schemeBlockAverage
  exact if_pos hc
theorem isGaugeCovariantAt_of_positive (hconj : ComplexMatrix2.NormExpLogConjugation)
    (hlaws : CorneredSchemeGaugeLawAndConjugation)
    (hmeans : ComplexLogMeanOfSmallFamilies)
    (hpaths : BlockPaths.Statement)
    (hL : IsAdmissibleBlockingFactor L) (hm : 0 < m) (hn : n < K) (s : AveragingScheme)
    (c : BondAtLevel L m K (n + 1)) (hc : c.IsPositivelyOriented)
    (h : SiteAtLevel L m K n → ComplexMatrix2)
    (W : BondAtLevel L m K n → ComplexMatrix2)
    (hh : ∀ x : SiteAtLevel L m K n, (x : FourTorus L m) ∈ bondDoubleBlock c →
      h x ∈ compactGaugeGroup)
    (hW : IsGaugeField complexGaugeGroup (bondsInDoubleBlock c) W) :
    IsGaugeCovariantAt s h W c := by
  obtain ⟨-, -, -, hnorm, -, -, -, -⟩ := hconj
  obtain ⟨-, -, -, hmean, -⟩ := hmeans
  obtain ⟨hcorner, hconjugate, hdomain⟩ := hlaws
  obtain ⟨μ, hμ⟩ := id hc
  obtain ⟨hy, hb⟩ := hpaths L m K hL.1 hL.2 hm n hn
  obtain ⟨hcoord, -, -, haxial, hin⟩ := hb c μ hμ
  have hlaw := hcorner L hL m K n hm hn c hc h W hh hW
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
  have hrelation : ∀ y ∈ ({c.source, c.target} : Set (SiteAtLevel L m K (n + 1))),
      ∀ x ∈ sitesInBlock (levelDepth K n) y, IsContourHolonomyDefined s W y x →
        IsContourHolonomyDefined s (gaugeTransform h W) y x ∧
          contourHolonomy s (gaugeTransform h W) y x =
            h (schemeBaseSite s (levelDepth K n) y) * contourHolonomy s W y x * (h x)⁻¹ := by
    intro y hy' x hx hd
    obtain ⟨-, hfield, hsize⟩ := hd
    have hfield' : IsGaugeField complexGaugeGroup (bondsInside (unitBlock y))
        (gaugeTransform h W) :=
      isGaugeField_gaugeTransform
        (fun b hb => ⟨hh _ (hsub y hy' hb.1), hh _ (hsub y hy' hb.2)⟩) hfield
    cases s with
    | cornered => exact ⟨⟨hx, hfield', trivial⟩, hlaw.contourHolonomy_eq y hy' x hx⟩
    | centred =>
      have hg : h (y.toSublattice (levelDepth K n)) ∈ compactGaugeGroup :=
        hh _ (hsub y hy' (hcentre y))
      have hk : h x ∈ compactGaugeGroup := hh _ (hsub y hy' hx)
      have hsize' : ComplexMatrix2.familyDiameter (contourHolonomies W y x) <
          centreOfMassDiameter := hsize
      have hdiam : ComplexMatrix2.familyDiameter (contourHolonomies (gaugeTransform h W) y x) =
          ComplexMatrix2.familyDiameter (contourHolonomies W y x) := by
        rw [hvalues y hy' x hx]
        exact familyDiameter_transform hnorm hg hk _
      refine ⟨⟨hx, hfield', hdiam.le.trans_lt hsize'⟩, ?_⟩
      change complexLogMean (contourHolonomies (gaugeTransform h W) y x) =
        h (y.toSublattice (levelDepth K n)) * complexLogMean (contourHolonomies W y x) * (h x)⁻¹
      rw [hvalues y hy' x hx]
      have : Nonempty (AxisOrdering y x) := ⟨(Finset.equivFin _).symm⟩
      exact complexLogMean_conj hmean _
        (fun σ => pathHolonomy_mem_complex fun b hb =>
          hW.1 b ((hcontours y hy' x hx σ).2 b hb))
        hsize' hg (inv_mem_compact hk)
  have hshifted : ∀ x ∈ sitesInBlock (levelDepth K n) c.source,
      shiftAcross c x ∈ sitesInBlock (levelDepth K n) c.target := by
    intro x hx
    rw [hcoord.2.2.2.2.1 x hx, ← hcoord.2.2.2.1]
    exact ⟨x, hx, rfl⟩
  have hbase_shifted : shiftAcross c (schemeBaseSite s (levelDepth K n) c.source) =
      schemeBaseSite s (levelDepth K n) c.target := by
    rw [hcoord.2.2.2.2.1 _ (hbase c.source)]
    cases s with
    | centred => exact hcoord.1.symm
    | cornered => exact hcoord.2.1.symm
  have haxial_eq : axialPath (schemeBaseSite s (levelDepth K n) c.source)
      (schemeBaseSite s (levelDepth K n) c.target) =
        crossingPath c (schemeBaseSite s (levelDepth K n) c.source) := by
    cases s with
    | centred => exact haxial.2.1
    | cornered => exact haxial.2.2
  have hcross : ∀ x ∈ sitesInBlock (levelDepth K n) c.source,
      IsBondPathFromTo (crossingPath c x) x (shiftAcross c x) ∧
        ∀ b ∈ crossingPath c x, b ∈ (bondsInDoubleBlock c : Set (BondAtLevel L m K n)) := by
    intro x hx
    refine ⟨?_, hin.2 x hx⟩
    rw [(haxial.1 x hx).2.1, hcoord.2.2.2.2.1 x hx]
    exact isBondPathFromTo_forwardFlow μ L x
  set g := h (schemeBaseSite s (levelDepth K n) c.source) with hgdef
  set g' := h (schemeBaseSite s (levelDepth K n) c.target) with hg'def
  have hgG : g ∈ compactGaugeGroup := hh _ (hsub _ hsource (hbase c.source))
  have hg'G : g' ∈ compactGaugeGroup := hh _ (hsub _ htarget (hbase c.target))
  have htransport : baseTransport s (gaugeTransform h W) c =
      g * baseTransport s W c * g'⁻¹ := by
    have hcross₂ := hcross _ (hbase c.source)
    rw [hbase_shifted] at hcross₂
    unfold baseTransport
    rw [haxial_eq]
    exact hlaw.holonomy_law _ _ _ hcross₂.1 (hsub _ hsource (hbase c.source)) hcross₂.2
  have hdefect : AreContourHolonomiesDefined s W c →
      ∀ x ∈ sitesInBlock (levelDepth K n) c.source,
        localDefect s (gaugeTransform h W) c x = g * localDefect s W c x * g⁻¹ := by
    intro hd x hx
    have hx' := hshifted x hx
    have hxG : h x ∈ compactGaugeGroup := hh _ (hsub _ hsource hx)
    have hx'G : h (shiftAcross c x) ∈ compactGaugeGroup := hh _ (hsub _ htarget hx')
    have hcross₁ := hcross x hx
    have hb₁ : pathHolonomy (gaugeTransform h W) (crossingPath c x) =
        h x * pathHolonomy W (crossingPath c x) * (h (shiftAcross c x))⁻¹ :=
      hlaw.holonomy_law _ _ _ hcross₁.1 (hsub _ hsource hx) hcross₁.2
    have hc₁ := (hrelation c.source hsource x hx (hd.1 x hx)).2
    have hc₂ := (hrelation c.target htarget _ hx' (hd.2 _ hx')).2
    unfold localDefect
    rw [hc₁, hc₂, hb₁, htransport]
    exact fourFactor_product (inv_mul_eq_one_of_mem hxG) (inv_mul_eq_one_of_mem hx'G)
      (inv_inv_of_mem hx'G) (inv_mul_eq_one_of_mem hg'G) (inv_inv_of_mem hg'G)
  refine ⟨fun y hy' x hx hd => hrelation y hy' x hx hd, ?_⟩
  intro hd
  obtain ⟨-, hcv, hsmall⟩ := hd
  have hdef := hdefect hcv
  have hformed : IsOneStepAverageFormed s (gaugeTransform h W) c := by
    refine ⟨isGaugeField_gaugeTransform
        (fun b hb => ⟨hh _ hb.1, hh _ hb.2⟩) hW, ⟨?_, ?_⟩, ?_⟩
    · exact fun x hx => (hrelation c.source hsource x hx (hcv.1 x hx)).1
    · exact fun x hx => (hrelation c.target htarget x hx (hcv.2 x hx)).1
    · intro x hx
      rw [hdef x hx, hnorm _ g (mem_unitaryGroup_of_mem hgG)]
      exact hsmall x hx
  refine ⟨hformed, ?_⟩
  have hcov := hconjugate g (isUnit_det_of_mem hgG)
  have hlogs : (∑ᶠ x ∈ sitesInBlock (levelDepth K n) c.source,
        ComplexMatrix2.logSeries (localDefect s (gaugeTransform h W) c x)) =
      g * (∑ᶠ x ∈ sitesInBlock (levelDepth K n) c.source,
        ComplexMatrix2.logSeries (localDefect s W c x)) * g⁻¹ := by
    rw [conj_finsum_mem hgG]
    refine finsum_mem_congr rfl fun x hx => ?_
    rw [hdef x hx]
    exact hcov.2 _ (hsmall x hx) (hdomain g (mem_unitaryGroup_of_mem hgG) _ (hsmall x hx))
  change schemeBlockAverage s (gaugeTransform h W) c = g * schemeBlockAverage s W c * g'⁻¹
  rw [schemeBlockAverage_of_positive _ _ hc, schemeBlockAverage_of_positive _ _ hc]
  unfold positiveBondAverage
  have hsmul : ∀ (a : ℂ) (X : ComplexMatrix2), a • (g * X * g⁻¹) = g * (a • X) * g⁻¹ :=
    fun a X => by
      rw [mul_smul_comm, smul_mul_assoc]
  rw [hlogs, htransport, hsmul, hcov.1]
  have hcancel : ∀ X : ComplexMatrix2, g⁻¹ * (g * X) = X := fun X => by
    rw [← mul_assoc, inv_mul_eq_one_of_mem hgG, one_mul]
  simp only [mul_assoc, hcancel]
end SchemeCovariance
theorem schemesGaugeCovariant_of_statements
    (hconj : ComplexMatrix2.NormExpLogConjugation)
    (hlaws : CorneredSchemeGaugeLawAndConjugation)
    (hmeans : ComplexLogMeanOfSmallFamilies)
    (hpaths : BlockPaths.Statement) :
    GaugeCovarianceStatement := by
  intro L hL m K n hm hn s c hc h W hh hW
  exact SchemeCovariance.isGaugeCovariantAt_of_positive hconj hlaws hmeans hpaths hL hm hn s c hc h
    W hh hW
end YangMills.Construction.PeriodicLattice
