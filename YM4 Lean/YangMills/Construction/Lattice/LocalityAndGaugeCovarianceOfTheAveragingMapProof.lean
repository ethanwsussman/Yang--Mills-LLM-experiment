import YangMills.Construction.Averaging.RadiiBelowTheExplicitBoundProof
import YangMills.Construction.Lattice.BlockPartition
import YangMills.Construction.Lattice.ComplexAverageReadsTheDoubleBlockProof
import YangMills.Construction.Lattice.CovarianceOfComplexContourVariablesProof
import YangMills.Construction.Lattice.ElementaryBoundsOfOneStepProof
import YangMills.Construction.Lattice.LocalityAndGaugeCovarianceOfTheAveragingMap
import YangMills.Construction.Matrices.LogMeanCovariance
import YangMills.Construction.Matrices.UnitaryLogConjugation
import Mathlib
set_option autoImplicit false
open Set
open YangMills.Construction.Matrices
noncomputable section
namespace YangMills.Construction.PeriodicLattice
variable {L m K : ℕ}
private structure Ingredients (L m : ℕ) : Prop where
  hL : Conventions.IsAdmissibleBlockingFactor L
  hm : 0 < m
  blocks : BlockPartition.Properties
  paths : BlockPaths.Statement
  gauge : GaugeCovarianceOfHolonomy
  mean : ComplexMatrix2.LogMeanCovariance
  norm : ComplexMatrix2.OperatorNormUnderConjugation
  ilog : ComplexMatrix2.UnitaryLogConjugationProperties
  explog : ComplexMatrix2.ExpLogEstimates
  cmean : Averaging.ComplexLogMeanOfSmallFamilies
private theorem isUnit_det_of_mem {V : ComplexMatrix2} (hV : V ∈ compactGaugeGroup) :
    IsUnit V.det := by apply _root_.YangMills.Construction.PeriodicLattice.SingleStepEstimate.det_isUnit_of_mem <;> assumption
private theorem mem_unitaryGroup_of_mem {V : ComplexMatrix2} (hV : V ∈ compactGaugeGroup) :
    V ∈ Matrix.unitaryGroup (Fin 2) ℂ :=
  (Matrix.mem_specialUnitaryGroup_iff.1 hV).1
private theorem mem_complex_of_mem {V : ComplexMatrix2} (hV : V ∈ compactGaugeGroup) :
    V ∈ complexGaugeGroup :=
  (Matrix.mem_specialUnitaryGroup_iff.1 hV).2
private theorem inv_mem_compact {V : ComplexMatrix2} (hV : V ∈ compactGaugeGroup) :
    V⁻¹ ∈ compactGaugeGroup := by apply _root_.YangMills.Construction.PeriodicLattice.BlockAverageContinuity.inv_mem_compactGaugeGroup <;> assumption
private theorem mul_mem_compact {V W : ComplexMatrix2} (hV : V ∈ compactGaugeGroup)
    (hW : W ∈ compactGaugeGroup) : V * W ∈ compactGaugeGroup := by apply _root_.YangMills.Construction.PeriodicLattice.SingleStepEstimate.mul_mem_of_mem <;> assumption
private theorem conj_four_factors {p q r s : ComplexMatrix2} (hq : IsUnit q.det)
    (hr : IsUnit r.det) (hs : IsUnit s.det) (A H B C : ComplexMatrix2) :
    (p * A * q⁻¹) * (q * H * r⁻¹) * (s * B * r⁻¹)⁻¹ * (p * C * s⁻¹)⁻¹ =
      p * (A * H * B⁻¹ * C⁻¹) * p⁻¹ := by
  have e1 : r⁻¹⁻¹ = r := Matrix.nonsing_inv_nonsing_inv r hr
  have e2 : s⁻¹⁻¹ = s := Matrix.nonsing_inv_nonsing_inv s hs
  simp only [Matrix.mul_inv_rev, e1, e2, mul_assoc]
  rw [Matrix.nonsing_inv_mul_cancel_left _ _ hq, Matrix.nonsing_inv_mul_cancel_left _ _ hr,
    Matrix.nonsing_inv_mul_cancel_left _ _ hs]
private theorem operatorNorm_conj_sub_one (T : Ingredients L m) {V : ComplexMatrix2}
    (hV : V ∈ compactGaugeGroup) (X : ComplexMatrix2) :
    ComplexMatrix2.operatorNorm (V * X * V⁻¹ - 1) = ComplexMatrix2.operatorNorm (X - 1) := by
  have e : V * X * V⁻¹ - 1 = V * (X - 1) * V⁻¹ := by
    rw [mul_sub, sub_mul, mul_one, Matrix.mul_nonsing_inv V (isUnit_det_of_mem hV)]
  rw [e]
  exact T.norm.2.1 _ _ (mem_unitaryGroup_of_mem hV)
private def conjLinearEquiv (t : ComplexMatrix2) (ht : IsUnit t.det) :
    ComplexMatrix2 ≃ₗ[ℂ] ComplexMatrix2 where
  toFun X := t * X * t⁻¹
  invFun X := t⁻¹ * X * t
  map_add' X Y := by simp only [mul_add, add_mul]
  map_smul' a X := by simp
  left_inv X := by
    simp only [mul_assoc]
    rw [Matrix.nonsing_inv_mul t ht, mul_one, ← mul_assoc, Matrix.nonsing_inv_mul t ht, one_mul]
  right_inv X := by
    simp only [mul_assoc]
    rw [Matrix.mul_nonsing_inv t ht, mul_one, ← mul_assoc, Matrix.mul_nonsing_inv t ht, one_mul]
private theorem matExp_smul_conj_mul (T : Ingredients L m) {t h : ComplexMatrix2}
    (ht : IsUnit t.det) (w : ℂ) (Z C : ComplexMatrix2) :
    ComplexMatrix2.matExp (w • (t * Z * t⁻¹)) * (t * C * h⁻¹) =
      t * (ComplexMatrix2.matExp (w • Z) * C) * h⁻¹ := by
  have e := T.norm.2.2.2.2.1 t (w • Z) ((Matrix.isUnit_iff_isUnit_det t).2 ht)
  have e2 : w • (t * Z * t⁻¹) = t * (w • Z) * t⁻¹ := by simp
  rw [e2, ← e]
  simp only [mul_assoc]
  rw [Matrix.nonsing_inv_mul_cancel_left _ _ ht]
private theorem conj_eq_neg_one_iff {t Y : ComplexMatrix2} (ht : IsUnit t.det) :
    t * Y * t⁻¹ = -1 ↔ Y = -1 := by
  constructor
  · intro h
    have := congrArg (conjLinearEquiv t ht).symm h
    have e : (conjLinearEquiv t ht).symm (t * Y * t⁻¹) = Y := (conjLinearEquiv t ht).left_inv Y
    rw [e] at this
    rw [this]
    change t⁻¹ * (-1) * t = -1
    rw [mul_neg, neg_mul, mul_one, Matrix.nonsing_inv_mul t ht]
  · rintro rfl
    rw [mul_neg, neg_mul, mul_one, Matrix.mul_nonsing_inv t ht]
private def iLie : Submodule ℝ ComplexMatrix2 where
  carrier := {Z | ∃ Y ∈ ComplexMatrix2.hermitianTraceless, Z = Complex.I • Y}
  add_mem' := by
    rintro _ _ ⟨Y, hY, rfl⟩ ⟨Y', hY', rfl⟩
    exact ⟨Y + Y', add_mem hY hY', (smul_add _ _ _).symm⟩
  zero_mem' := ⟨0, zero_mem _, (smul_zero _).symm⟩
  smul_mem' := by
    rintro r _ ⟨Y, hY, rfl⟩
    refine ⟨r • Y, Submodule.smul_mem _ r hY, ?_⟩
    ext a b
    simp [Matrix.smul_apply]
    ring
private theorem ofReal_smul_mem_iLie (r : ℝ) {Z : ComplexMatrix2} (hZ : Z ∈ iLie) :
    ((r : ℂ)) • Z ∈ iLie := by
  have e : ((r : ℂ)) • Z = r • Z := by
    ext a b
    simp [Matrix.smul_apply]
  rw [e]
  exact Submodule.smul_mem _ r hZ
private theorem matExp_mem_of_mem_iLie (T : Ingredients L m) {Z : ComplexMatrix2} (hZ : Z ∈ iLie) :
    ComplexMatrix2.matExp Z ∈ compactGaugeGroup := by
  obtain ⟨Y, hY, rfl⟩ := hZ
  exact (T.ilog.1 Y hY).2.2
private theorem logSeries_mem_iLie (T : Ingredients L m) {W : ComplexMatrix2}
    (hW : W ∈ compactGaugeGroup) (h : ComplexMatrix2.operatorNorm (W - 1) < 1) :
    ComplexMatrix2.logSeries W ∈ iLie := by
  obtain ⟨H, -, -, -, -, -, hH⟩ := T.explog.2.2.2.2.2.2.2.1 W (mem_unitaryGroup_of_mem hW) h
  obtain ⟨Y, hY, e⟩ := (hH (mem_complex_of_mem hW)).2.2.1
  exact ⟨Y, hY, e⟩
private theorem unitaryLog_mem_iLie (T : Ingredients L m) {W : ComplexMatrix2}
    (hW : W ∈ ComplexMatrix2.unitaryLogDomain) : ComplexMatrix2.unitaryLog W ∈ iLie := by
  obtain ⟨Y, hY, -⟩ := T.ilog.2.1 W hW
  exact ⟨ComplexMatrix2.unitaryLieLog W, (Classical.epsilon_spec (p := fun Y : ComplexMatrix2 =>
    Y ∈ ComplexMatrix2.hermitianTraceless ∧ ComplexMatrix2.operatorNorm Y < Real.pi ∧
      ComplexMatrix2.matExp (Complex.I • Y) = W) ⟨Y, hY⟩).1, rfl⟩
private theorem isBondPathFromTo_cons {j : ℤ} (b : Bond L m j) {Γ : List (Bond L m j)}
    {x' : Site L m j} (h : IsBondPathFromTo Γ b.target x') :
    IsBondPathFromTo (b :: Γ) b.source x' := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨?_, by simp, by simp, ?_⟩
  · cases Γ with
    | nil => exact List.isChain_singleton _
    | cons a Γ' => exact List.isChain_cons_cons.2 ⟨(h3 a (by simp)).symm, h1⟩
  · cases Γ with
    | nil =>
      intro d hd
      have : b = d := by simpa using hd
      subst this
      exact h2 rfl
    | cons a Γ' =>
      intro d hd
      exact h4 d (by simpa [List.getLast?_cons_cons] using hd)
private theorem isBondPathFromTo_forwardFlow {j : ℤ} (μ : Fin 4) :
    ∀ (n : ℕ) (x : Site L m j),
      IsBondPathFromTo (forwardAxisPath x μ n) x (x + (n : ℤ) • unitStep L m j μ)
  | 0, x => by simp [IsBondPathFromTo, forwardAxisPath, IsBondPath]
  | n + 1, x => by
    have h := isBondPathFromTo_forwardFlow μ n (x + unitStep L m j μ)
    have e : x + unitStep L m j μ + (n : ℤ) • unitStep L m j μ =
        x + ((n + 1 : ℕ) : ℤ) • unitStep L m j μ := by
      push_cast
      rw [add_smul, one_smul]
      abel
    rw [e] at h
    exact isBondPathFromTo_cons (Bond.forwardFrom x μ) h
private theorem pathHolonomy_congr {j : ℤ} {U U' : Bond L m j → ComplexMatrix2}
    {Γ : List (Bond L m j)} (h : ∀ b ∈ Γ, U b = U' b) : pathHolonomy U Γ = pathHolonomy U' Γ := by apply _root_.YangMills.Construction.PeriodicLattice.ComplexAverageLocality.pathHolonomy_congr <;> assumption
private theorem pathHolonomy_mem {j : ℤ} {U : Bond L m j → ComplexMatrix2} {Γ : List (Bond L m j)}
    (h : ∀ b ∈ Γ, U b ∈ compactGaugeGroup) : pathHolonomy U Γ ∈ compactGaugeGroup := by
  unfold pathHolonomy
  refine Submonoid.list_prod_mem _ ?_
  intro a ha
  obtain ⟨b, hb, rfl⟩ := List.mem_map.1 ha
  exact h b hb
abbrev _root_.YangMills.SharedProofs.p53533 := @pathHolonomy_mem
private theorem pathHolonomy_mem_complex {j : ℤ} {U : Bond L m j → ComplexMatrix2}
    {Γ : List (Bond L m j)} (h : ∀ b ∈ Γ, U b ∈ complexGaugeGroup) :
    pathHolonomy U Γ ∈ complexGaugeGroup := by apply _root_.YangMills.Construction.PeriodicLattice.ContourCovariance.pathHolonomy_mem_complexGaugeGroup <;> assumption
private theorem conj_finsum_mem {α : Type*} {t : ComplexMatrix2} (ht : IsUnit t.det) (s : Set α)
    (f : α → ComplexMatrix2) : t * (∑ᶠ x ∈ s, f x) * t⁻¹ = ∑ᶠ x ∈ s, t * f x * t⁻¹ := by
  rw [finsum_mem_def, finsum_mem_def]
  have h := (conjLinearEquiv t ht).toAddEquiv.map_finsum (s.indicator f)
  refine h.trans (finsum_congr fun a => ?_)
  by_cases ha : a ∈ s
  · simp only [Set.indicator_of_mem ha]
    rfl
  · simp only [Set.indicator_of_notMem ha, map_zero]
private theorem logMean_mem {ι : Type*} [Fintype ι] {V : ι → ComplexMatrix2}
    (h : ComplexMatrix2.HasUniqueLogMean compactGaugeGroup V) :
    ComplexMatrix2.logMean compactGaugeGroup V ∈ compactGaugeGroup :=
  (Classical.epsilon_spec h.exists).1
private theorem gaugeField_complex {j : ℤ} {ℬ : Set (Bond L m j)} {U : Bond L m j → ComplexMatrix2}
    (h : IsGaugeField compactGaugeGroup ℬ U) : IsGaugeField complexGaugeGroup ℬ U :=
  ⟨fun b hb => mem_complex_of_mem (h.1 b hb), h.2⟩
private theorem gaugeMap_complex {j : ℤ} {u : Site L m j → ComplexMatrix2}
    (h : IsGaugeMap compactGaugeGroup u) : IsGaugeMap complexGaugeGroup u :=
  fun x => mem_complex_of_mem (h x)
private theorem pathHolonomy_gaugeTransform (T : Ingredients L m) {j : ℤ} (hj : -(m : ℤ) ≤ j)
    {ℬ : Set (Bond L m j)} (hℬ : IsReversalClosed ℬ) {U : Bond L m j → ComplexMatrix2}
    (hU : IsGaugeField complexGaugeGroup ℬ U) {u : Site L m j → ComplexMatrix2}
    (hu : IsGaugeMap compactGaugeGroup u) {Γ : List (Bond L m j)} {x x' : Site L m j}
    (hΓ : IsBondPathFromTo Γ x x') (hb : ∀ b ∈ Γ, b ∈ ℬ) :
    pathHolonomy (gaugeTransform u U) Γ = u x * pathHolonomy U Γ * (u x')⁻¹ :=
  (T.gauge L m T.hL.1 T.hL.2 T.hm j hj ℬ U u u hℬ hU (gaugeMap_complex hu)
    (gaugeMap_complex hu)).2.1 Γ x x' hΓ hb
private theorem isReversalClosed_bondsInDoubleBlock {j j' : ℤ} (c : Bond L m j) :
    IsReversalClosed (bondsInDoubleBlock c : Set (Bond L m j')) :=
  fun _ hb => ⟨hb.2, hb.1⟩
private theorem isReversalClosed_bondsInside {j : ℤ} (X : Set (FourTorus L m)) :
    IsReversalClosed (bondsInside X : Set (Bond L m j)) :=
  fun _ hb => ⟨hb.2, hb.1⟩
private theorem opposite_isPositivelyOriented_of_not {j : ℤ} {c : Bond L m j}
    (hc : ¬c.IsPositivelyOriented) : c.opposite.IsPositivelyOriented := by apply _root_.YangMills.Construction.PeriodicLattice.Bond.opposite_isPositivelyOriented <;> assumption
section Cases
variable {j j' : ℤ} {ω : ℝ} {U U' : Bond L m j' → ComplexMatrix2} {c : Bond L m j}
private theorem blockAverageCase_congr
    (hA : IsRegularAveragingCase ω U c ↔ IsRegularAveragingCase ω U' c)
    (hN : NoCrossingDefectIsNegOne U c ↔ NoCrossingDefectIsNegOne U' c) :
    blockAverageCase ω U c = blockAverageCase ω U' c := by
  unfold blockAverageCase
  by_cases h : IsRegularAveragingCase ω U c
  · rw [if_pos h, if_pos (hA.1 h)]
  · rw [if_neg h, if_neg fun h' => h (hA.2 h')]
    by_cases h2 : NoCrossingDefectIsNegOne U c
    · rw [if_pos h2, if_pos (hN.1 h2)]
    · rw [if_neg h2, if_neg fun h' => h2 (hN.2 h')]
private theorem blockAverageOnPositive_of_iff {f : ComplexMatrix2 → ComplexMatrix2}
    (hA : IsRegularAveragingCase ω U c ↔ IsRegularAveragingCase ω U' c)
    (hN : NoCrossingDefectIsNegOne U c ↔ NoCrossingDefectIsNegOne U' c)
    (hVA : IsRegularAveragingCase ω U c →
      regularAverageValue U' c = f (regularAverageValue U c))
    (hVB : NoCrossingDefectIsNegOne U c → logAverageValue U' c = f (logAverageValue U c))
    (hT : parallelTransport U' c = f (parallelTransport U c)) :
    blockAverageOnPositive ω U' c = f (blockAverageOnPositive ω U c) := by
  unfold NoCrossingDefectIsNegOne at hN hVB
  unfold blockAverageOnPositive
  by_cases h : IsRegularAveragingCase ω U c
  · rw [if_pos h, if_pos (hA.1 h)]
    exact hVA h
  · rw [if_neg h, if_neg fun h' => h (hA.2 h')]
    by_cases h2 : ∀ x ∈ sitesInBlock j' c.source, ∀ σ σ', contourCrossingDefect U c x σ σ' ≠ -1
    · rw [if_pos h2, if_pos (hN.1 h2)]
      exact hVB h2
    · rw [if_neg h2, if_neg fun h' => h2 (hN.2 h')]
      exact hT
private theorem blockAverage_of_pos (ω : ℝ) (U : Bond L m j' → ComplexMatrix2)
    (hc : c.IsPositivelyOriented) : blockAverage ω U c = blockAverageOnPositive ω U c := by
  simp only [blockAverage, if_pos hc]
private theorem blockAverage_of_not_pos (ω : ℝ) (U : Bond L m j' → ComplexMatrix2)
    (hc : ¬c.IsPositivelyOriented) :
    blockAverage ω U c = (blockAverageOnPositive ω U c.opposite)⁻¹ := by
  simp only [blockAverage, if_neg hc]
end Cases
section OneStep
variable {k : ℕ}
private theorem neg_le_levelDepth (hk : k ≤ K) : -(m : ℤ) ≤ levelDepth K k := by
  simp only [levelDepth]
  omega
private theorem orderedContour_facts (T : Ingredients L m) (hk : k < K)
    (y : SiteAtLevel L m K (k + 1)) {x : SiteAtLevel L m K k}
    (hx : x ∈ sitesInBlock (levelDepth K k) y) (σ : AxisOrdering y x) :
    IsBondPathFromTo (orderedContour y x σ) (y.toSublattice (levelDepth K k)) x ∧
      ∀ b ∈ orderedContour y x σ, b ∈ (bondsInside (unitBlock y) : Set (BondAtLevel L m K k)) := by
  obtain ⟨⟨⟨-, himg⟩, -, -⟩, -, hp⟩ := (T.paths L m K T.hL.1 T.hL.2 T.hm k hk).1 y
  have hxb : (x : FourTorus L m) ∈ (fun p =>
      (offsetSite (y.toSublattice (levelDepth K k)) p : FourTorus L m)) '' blockIndexBox L := by
    rw [himg]
    exact hx
  obtain ⟨p, hpQ, hpx⟩ := hxb
  obtain rfl : offsetSite (y.toSublattice (levelDepth K k)) p = x := Subtype.ext hpx
  have h := (hp p hpQ).1 _ ⟨σ, rfl⟩
  exact ⟨h.1, h.2.2.2.2⟩
private theorem toSublattice_mem_sitesInBlock (T : Ingredients L m) (hk : k < K)
    (y : SiteAtLevel L m K (k + 1)) :
    y.toSublattice (levelDepth K k) ∈ sitesInBlock (levelDepth K k) y := by
  obtain ⟨⟨⟨-, himg⟩, -, -⟩, -, -⟩ := (T.paths L m K T.hL.1 T.hL.2 T.hm k hk).1 y
  have h0 : (0 : Fin 4 → ℤ) ∈ blockIndexBox L := by
    intro ν
    have h13 := T.hL.2
    have : 0 ≤ centreToFaceSteps L := by
      unfold centreToFaceSteps
      omega
    simpa using this
  exact show ((y.toSublattice (levelDepth K k) : SiteAtLevel L m K k) : FourTorus L m) ∈
      unitBlock y from by
    rw [← himg]
    exact ⟨0, h0, by simp [offsetSite]⟩
private structure DoubleBlockPaths (K k : ℕ) (c : BondAtLevel L m K (k + 1)) : Prop where
  target_mem : ∀ x ∈ sitesInBlock (levelDepth K k) c.source,
    shiftAcross c x ∈ sitesInBlock (levelDepth K k) c.target
  crossing_path : ∀ x ∈ sitesInBlock (levelDepth K k) c.source,
    IsBondPathFromTo (crossingPath c x) x (shiftAcross c x)
  crossing_bonds : ∀ x ∈ sitesInBlock (levelDepth K k) c.source, ∀ b ∈ crossingPath c x,
    b ∈ (bondsInDoubleBlock c : Set (BondAtLevel L m K k))
  source_contours : ∀ x ∈ sitesInBlock (levelDepth K k) c.source, ∀ σ,
    ∀ b ∈ orderedContour c.source x σ, b ∈ (bondsInDoubleBlock c : Set (BondAtLevel L m K k))
  target_contours : ∀ x ∈ sitesInBlock (levelDepth K k) c.target, ∀ σ,
    ∀ b ∈ orderedContour c.target x σ, b ∈ (bondsInDoubleBlock c : Set (BondAtLevel L m K k))
  axial_path : IsBondPathFromTo
    (axialPath (c.source.toSublattice (levelDepth K k)) (c.target.toSublattice (levelDepth K k)))
    (c.source.toSublattice (levelDepth K k)) (c.target.toSublattice (levelDepth K k))
  axial_bonds : ∀ b ∈ axialPath (c.source.toSublattice (levelDepth K k))
      (c.target.toSublattice (levelDepth K k)),
    b ∈ (bondsInDoubleBlock c : Set (BondAtLevel L m K k))
  plaquettes : ∀ p ∈ (doubleBlockPlaquettes c : Set (PlaquetteAtLevel L m K k)),
    ∀ b ∈ p.boundaryBonds, b ∈ (bondsInDoubleBlock c : Set (BondAtLevel L m K k))
private theorem doubleBlockPaths (T : Ingredients L m) (hk : k < K) (c : BondAtLevel L m K (k + 1))
    (hc : c.IsPositivelyOriented) : DoubleBlockPaths K k c := by
  obtain ⟨μ, hμ⟩ := hc
  obtain ⟨⟨hd1, -, -, hd4, hd5, -⟩, -, -, hS, hPth⟩ :=
    (T.paths L m K T.hL.1 T.hL.2 T.hm k hk).2 c μ hμ
  have hpath : ∀ x ∈ sitesInBlock (levelDepth K k) c.source,
      IsBondPathFromTo (crossingPath c x) x (shiftAcross c x) := by
    intro x hx
    rw [(hS.1 x hx).2.1, hd5 x hx]
    exact isBondPathFromTo_forwardFlow μ L x
  have ht := toSublattice_mem_sitesInBlock T hk c.source
  have hbonds : ∀ x ∈ sitesInBlock (levelDepth K k) c.source, ∀ b ∈ crossingPath c x,
      b ∈ (bondsInDoubleBlock c : Set (BondAtLevel L m K k)) := hPth.2
  refine ⟨?_, hpath, hbonds, ?_, ?_, ?_, ?_, ?_⟩
  · intro x hx
    rw [hd5 x hx, ← hd4]
    exact ⟨x, hx, rfl⟩
  · intro x hx σ b hb
    exact (hPth.1 c.source (Or.inl rfl) x hx).1 _ ⟨σ, rfl⟩ b hb
  · intro x hx σ b hb
    exact (hPth.1 c.target (Or.inr rfl) x hx).1 _ ⟨σ, rfl⟩ b hb
  · rw [hS.2.1]
    have h := hpath _ ht
    rwa [hd5 _ ht, ← hd1] at h
  · rw [hS.2.1]
    exact hbonds _ ht
  · intro p hp b hb
    have hp' : ∀ z ∈ p.vertices, (z : FourTorus L m) ∈ bondDoubleBlock c := hp
    have c1 : p.origin ∈ p.vertices := by simp [Plaquette.vertices]
    have c2 : p.origin + unitStep L m (levelDepth K k) p.firstAxis ∈ p.vertices := by
      simp [Plaquette.vertices]
    have c3 : p.origin + unitStep L m (levelDepth K k) p.firstAxis +
        unitStep L m (levelDepth K k) p.secondAxis ∈ p.vertices := by
      simp [Plaquette.vertices]
    have c3' : p.origin + unitStep L m (levelDepth K k) p.secondAxis +
        unitStep L m (levelDepth K k) p.firstAxis ∈ p.vertices := by
      rw [add_right_comm]
      exact c3
    have c4 : p.origin + unitStep L m (levelDepth K k) p.secondAxis ∈ p.vertices := by
      simp [Plaquette.vertices]
    simp only [Plaquette.boundaryBonds, List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact ⟨hp' _ c1, hp' _ c2⟩
    · exact ⟨hp' _ c2, hp' _ c3⟩
    · exact ⟨hp' _ c3', hp' _ c4⟩
    · exact ⟨hp' _ c4, hp' _ c1⟩
private theorem onPositive_local (T : Ingredients L m) (hk : k < K) (ω : ℝ)
    {c : BondAtLevel L m K (k + 1)} (hc : c.IsPositivelyOriented)
    {U U' : BondAtLevel L m K k → ComplexMatrix2}
    (h : ∀ b ∈ (bondsInDoubleBlock c : Set (BondAtLevel L m K k)), U b = U' b) :
    blockAverageCase ω U c = blockAverageCase ω U' c ∧
      blockAverageOnPositive ω U c = blockAverageOnPositive ω U' c := by
  have hB := doubleBlockPaths T hk c hc
  have hTail : ∀ x ∈ sitesInBlock (levelDepth K k) c.source,
      contourHolonomies U c.source x = contourHolonomies U' c.source x :=
    fun x hx => funext fun σ =>
      pathHolonomy_congr fun b hb => h b (hB.source_contours x hx σ b hb)
  have hHead : ∀ x ∈ sitesInBlock (levelDepth K k) c.target,
      contourHolonomies U c.target x = contourHolonomies U' c.target x :=
    fun x hx => funext fun σ =>
      pathHolonomy_congr fun b hb => h b (hB.target_contours x hx σ b hb)
  have hCr : ∀ x ∈ sitesInBlock (levelDepth K k) c.source,
      pathHolonomy U (crossingPath c x) = pathHolonomy U' (crossingPath c x) :=
    fun x hx => pathHolonomy_congr fun b hb => h b (hB.crossing_bonds x hx b hb)
  have hTr : parallelTransport U c = parallelTransport U' c :=
    pathHolonomy_congr fun b hb => h b (hB.axial_bonds b hb)
  have hAE : ∀ x ∈ sitesInBlock (levelDepth K k) c.source,
      crossingDefect U c x = crossingDefect U' c x := by
    intro x hx
    unfold crossingDefect meanContourHolonomy
    rw [hTail x hx, hHead _ (hB.target_mem x hx), hCr x hx, hTr]
  have hCE : ∀ x ∈ sitesInBlock (levelDepth K k) c.source, ∀ σ σ',
      contourCrossingDefect U c x σ σ' = contourCrossingDefect U' c x σ σ' := by
    intro x hx σ σ'
    have e1 : pathHolonomy U (orderedContour c.source x σ) =
        pathHolonomy U' (orderedContour c.source x σ) :=
      congrFun (hTail x hx) σ
    have e2 : pathHolonomy U (orderedContour c.target (shiftAcross c x) σ') =
        pathHolonomy U' (orderedContour c.target (shiftAcross c x) σ') :=
      congrFun (hHead _ (hB.target_mem x hx)) σ'
    unfold contourCrossingDefect
    rw [e1, e2, hCr x hx, hTr]
  have hA : IsRegularAveragingCase ω U c ↔ IsRegularAveragingCase ω U' c := by
    unfold IsRegularAveragingCase HasContourMean DoubleBlockPlaquettesNear
    refine and_congr ?_ (and_congr ?_ (and_congr ?_ ?_))
    · refine forall₂_congr fun p hp => ?_
      unfold plaquetteHolonomy
      rw [pathHolonomy_congr fun b hb => h b (hB.plaquettes p hp b hb)]
    · exact forall₂_congr fun x hx => by rw [hTail x hx]
    · exact forall₂_congr fun x hx => by rw [hHead x hx]
    · exact forall₂_congr fun x hx => by rw [hAE x hx]
  have hN : NoCrossingDefectIsNegOne U c ↔ NoCrossingDefectIsNegOne U' c := by
    unfold NoCrossingDefectIsNegOne
    exact forall₂_congr fun x hx => forall_congr' fun σ => forall_congr' fun σ' => by
      rw [hCE x hx σ σ']
  refine ⟨blockAverageCase_congr hA hN,
    Eq.symm (blockAverageOnPositive_of_iff (f := id) hA hN ?_ ?_ hTr.symm)⟩
  · intro _
    unfold regularAverageValue
    rw [hTr]
    simp only [id]
    refine congrArg (fun Z => ComplexMatrix2.matExp (inverseFourthPowerWeight L • Z) *
      parallelTransport U' c) (finsum_mem_congr rfl fun x hx => ?_)
    rw [hAE x hx]
  · intro _
    unfold logAverageValue
    rw [hTr]
    simp only [id]
    refine congrArg (fun Z => ComplexMatrix2.matExp (inverseFourthPowerWeight L • Z) *
      parallelTransport U' c) (finsum_mem_congr rfl fun x hx => ?_)
    simp only [hCE x hx]
private theorem contourHolonomies_gaugeTransform (T : Ingredients L m) (hk : k < K)
    {ℬ : Set (BondAtLevel L m K k)} (hℬ : IsReversalClosed ℬ)
    {U : BondAtLevel L m K k → ComplexMatrix2} (hU : IsGaugeField complexGaugeGroup ℬ U)
    {u : SiteAtLevel L m K k → ComplexMatrix2} (hu : IsGaugeMap compactGaugeGroup u)
    (y : SiteAtLevel L m K (k + 1)) {x : SiteAtLevel L m K k}
    (hx : x ∈ sitesInBlock (levelDepth K k) y) (hb : ∀ σ, ∀ b ∈ orderedContour y x σ, b ∈ ℬ) :
    contourHolonomies (gaugeTransform u U) y x =
      fun σ => u (y.toSublattice (levelDepth K k)) * contourHolonomies U y x σ * (u x)⁻¹ :=
  funext fun σ => pathHolonomy_gaugeTransform T (neg_le_levelDepth hk.le) hℬ hU hu
    (orderedContour_facts T hk y hx σ).1 (hb σ)
private theorem meanContourHolonomy_gaugeTransform (T : Ingredients L m) (hk : k < K)
    {ℬ : Set (BondAtLevel L m K k)} (hℬ : IsReversalClosed ℬ)
    {U : BondAtLevel L m K k → ComplexMatrix2} (hU : IsGaugeField compactGaugeGroup ℬ U)
    {u : SiteAtLevel L m K k → ComplexMatrix2} (hu : IsGaugeMap compactGaugeGroup u)
    (y : SiteAtLevel L m K (k + 1)) {x : SiteAtLevel L m K k}
    (hx : x ∈ sitesInBlock (levelDepth K k) y) (hb : ∀ σ, ∀ b ∈ orderedContour y x σ, b ∈ ℬ) :
    (HasContourMean (gaugeTransform u U) y x ↔ HasContourMean U y x) ∧
      (HasContourMean U y x → meanContourHolonomy (gaugeTransform u U) y x =
        u (y.toSublattice (levelDepth K k)) * meanContourHolonomy U y x * (u x)⁻¹) := by
  have hV : ∀ σ, contourHolonomies U y x σ ∈ (ComplexMatrix2.specialUnitary : Set ComplexMatrix2) :=
    fun σ => pathHolonomy_mem fun b hb' => hU.1 b (hb σ b hb')
  have hc := T.mean (AxisOrdering y x) (contourHolonomies U y x)
    (u (y.toSublattice (levelDepth K k))) (u x)⁻¹ hV (hu _) (inv_mem_compact (hu x))
  have e := contourHolonomies_gaugeTransform T hk hℬ (gaugeField_complex hU) hu y hx hb
  unfold HasContourMean meanContourHolonomy
  rw [e]
  exact ⟨hc.2.1.symm, hc.2.2⟩
private theorem contourCrossingDefect_mem {c : BondAtLevel L m K (k + 1)}
    (hB : DoubleBlockPaths K k c) {U : BondAtLevel L m K k → ComplexMatrix2}
    (hU : IsGaugeField compactGaugeGroup (bondsInDoubleBlock c) U) {x : SiteAtLevel L m K k}
    (hx : x ∈ sitesInBlock (levelDepth K k) c.source) (σ : AxisOrdering c.source x)
    (σ' : AxisOrdering c.target (shiftAcross c x)) :
    contourCrossingDefect U c x σ σ' ∈ compactGaugeGroup :=
  mul_mem_compact (mul_mem_compact (mul_mem_compact
    (pathHolonomy_mem fun b hb => hU.1 b (hB.source_contours x hx σ b hb))
    (pathHolonomy_mem fun b hb => hU.1 b (hB.crossing_bonds x hx b hb)))
    (inv_mem_compact (pathHolonomy_mem fun b hb =>
      hU.1 b (hB.target_contours _ (hB.target_mem x hx) σ' b hb))))
    (inv_mem_compact (pathHolonomy_mem fun b hb => hU.1 b (hB.axial_bonds b hb)))
private theorem crossingDefect_mem {c : BondAtLevel L m K (k + 1)} (hB : DoubleBlockPaths K k c)
    {U : BondAtLevel L m K k → ComplexMatrix2}
    (hU : IsGaugeField compactGaugeGroup (bondsInDoubleBlock c) U)
    {x : SiteAtLevel L m K k} (hx : x ∈ sitesInBlock (levelDepth K k) c.source)
    (h1 : HasContourMean U c.source x) (h2 : HasContourMean U c.target (shiftAcross c x)) :
    crossingDefect U c x ∈ compactGaugeGroup :=
  mul_mem_compact (mul_mem_compact (mul_mem_compact (logMean_mem h1)
    (pathHolonomy_mem fun b hb => hU.1 b (hB.crossing_bonds x hx b hb)))
    (inv_mem_compact (logMean_mem h2)))
    (inv_mem_compact (pathHolonomy_mem fun b hb => hU.1 b (hB.axial_bonds b hb)))
private def crossingLogSum {j j' : ℤ} (U : Bond L m j' → ComplexMatrix2) (c : Bond L m j) :
    ComplexMatrix2 :=
  ∑ᶠ x ∈ sitesInBlock j' c.source,
    (((Fintype.card (AxisOrdering c.source x) : ℝ)⁻¹ : ℝ) : ℂ) • ∑ σ : AxisOrdering c.source x,
      (((Fintype.card (AxisOrdering c.target (shiftAcross c x)) : ℝ)⁻¹ : ℝ) : ℂ) •
        ∑ σ' : AxisOrdering c.target (shiftAcross c x),
          ComplexMatrix2.unitaryLog (contourCrossingDefect U c x σ σ')
private theorem onPositive_gaugeTransform (T : Ingredients L m) (hk : k < K) (ω : ℝ)
    {c : BondAtLevel L m K (k + 1)} (hc : c.IsPositivelyOriented)
    {U : BondAtLevel L m K k → ComplexMatrix2}
    (hU : IsGaugeField compactGaugeGroup (bondsInDoubleBlock c) U)
    {u : SiteAtLevel L m K k → ComplexMatrix2} (hu : IsGaugeMap compactGaugeGroup u) :
    blockAverageCase ω U c = blockAverageCase ω (gaugeTransform u U) c ∧
      blockAverageOnPositive ω (gaugeTransform u U) c =
        u (c.source.toSublattice (levelDepth K k)) * blockAverageOnPositive ω U c *
          (u (c.target.toSublattice (levelDepth K k)))⁻¹ := by
  have hB := doubleBlockPaths T hk c hc
  have hcl := isReversalClosed_bondsInDoubleBlock (j' := levelDepth K k) c
  have hUc := gaugeField_complex hU
  have hj := neg_le_levelDepth (m := m) hk.le
  set t := u (c.source.toSublattice (levelDepth K k)) with htd
  set s := u (c.target.toSublattice (levelDepth K k)) with hsd
  have ht : t ∈ compactGaugeGroup := hu _
  have hs : s ∈ compactGaugeGroup := hu _
  have hcT : ∀ x ∈ sitesInBlock (levelDepth K k) c.source,
      (HasContourMean (gaugeTransform u U) c.source x ↔ HasContourMean U c.source x) ∧
      (HasContourMean U c.source x → meanContourHolonomy (gaugeTransform u U) c.source x =
        t * meanContourHolonomy U c.source x * (u x)⁻¹) :=
    fun x hx => meanContourHolonomy_gaugeTransform T hk hcl hU hu c.source hx
      (hB.source_contours x hx)
  have hcH : ∀ x ∈ sitesInBlock (levelDepth K k) c.target,
      (HasContourMean (gaugeTransform u U) c.target x ↔ HasContourMean U c.target x) ∧
      (HasContourMean U c.target x → meanContourHolonomy (gaugeTransform u U) c.target x =
        s * meanContourHolonomy U c.target x * (u x)⁻¹) :=
    fun x hx => meanContourHolonomy_gaugeTransform T hk hcl hU hu c.target hx
      (hB.target_contours x hx)
  have hH : ∀ x ∈ sitesInBlock (levelDepth K k) c.source,
      pathHolonomy (gaugeTransform u U) (crossingPath c x) =
        u x * pathHolonomy U (crossingPath c x) * (u (shiftAcross c x))⁻¹ :=
    fun x hx => pathHolonomy_gaugeTransform T hj hcl hUc hu (hB.crossing_path x hx)
      (hB.crossing_bonds x hx)
  have hTr : parallelTransport (gaugeTransform u U) c = t * parallelTransport U c * s⁻¹ :=
    pathHolonomy_gaugeTransform T hj hcl hUc hu hB.axial_path hB.axial_bonds
  have hE : ∀ x ∈ sitesInBlock (levelDepth K k) c.source, HasContourMean U c.source x →
      HasContourMean U c.target (shiftAcross c x) →
      crossingDefect (gaugeTransform u U) c x = t * crossingDefect U c x * t⁻¹ := by
    intro x hx h1 h2
    unfold crossingDefect
    rw [(hcT x hx).2 h1, (hcH _ (hB.target_mem x hx)).2 h2, hH x hx, hTr]
    exact conj_four_factors (isUnit_det_of_mem (hu x)) (isUnit_det_of_mem (hu _))
      (isUnit_det_of_mem hs) _ _ _ _
  have hCross : ∀ x ∈ sitesInBlock (levelDepth K k) c.source, ∀ σ σ',
      contourCrossingDefect (gaugeTransform u U) c x σ σ' =
        t * contourCrossingDefect U c x σ σ' * t⁻¹ := by
    intro x hx σ σ'
    have hx' := hB.target_mem x hx
    unfold contourCrossingDefect
    rw [pathHolonomy_gaugeTransform T hj hcl hUc hu (orderedContour_facts T hk c.source hx σ).1
        (hB.source_contours x hx σ),
      pathHolonomy_gaugeTransform T hj hcl hUc hu (orderedContour_facts T hk c.target hx' σ').1
        (hB.target_contours _ hx' σ'), hH x hx, hTr]
    exact conj_four_factors (isUnit_det_of_mem (hu x)) (isUnit_det_of_mem (hu _))
      (isUnit_det_of_mem hs) _ _ _ _
  have hPl : DoubleBlockPlaquettesNear ω c U ↔ DoubleBlockPlaquettesNear ω c (gaugeTransform u U) := by
    unfold DoubleBlockPlaquettesNear
    refine forall₂_congr fun p hp => ?_
    have e := (T.gauge L m T.hL.1 T.hL.2 T.hm (levelDepth K k) hj _ U u u hcl hUc
      (gaugeMap_complex hu) (gaugeMap_complex hu)).2.2 p (hB.plaquettes p hp)
    rw [e, operatorNorm_conj_sub_one T (hu _)]
  have hA : IsRegularAveragingCase ω U c ↔ IsRegularAveragingCase ω (gaugeTransform u U) c := by
    unfold IsRegularAveragingCase
    constructor
    · rintro ⟨p0, p1, p2, p3⟩
      refine ⟨hPl.1 p0, fun x hx => (hcT x hx).1.2 (p1 x hx),
        fun x hx => (hcH x hx).1.2 (p2 x hx), fun x hx => ?_⟩
      rw [hE x hx (p1 x hx) (p2 _ (hB.target_mem x hx)), operatorNorm_conj_sub_one T ht]
      exact p3 x hx
    · rintro ⟨q0, q1, q2, q3⟩
      have p1 : ∀ x ∈ sitesInBlock (levelDepth K k) c.source, HasContourMean U c.source x :=
        fun x hx => (hcT x hx).1.1 (q1 x hx)
      have p2 : ∀ x ∈ sitesInBlock (levelDepth K k) c.target, HasContourMean U c.target x :=
        fun x hx => (hcH x hx).1.1 (q2 x hx)
      refine ⟨hPl.2 q0, p1, p2, fun x hx => ?_⟩
      have h := q3 x hx
      rwa [hE x hx (p1 x hx) (p2 _ (hB.target_mem x hx)), operatorNorm_conj_sub_one T ht] at h
  have hN : NoCrossingDefectIsNegOne U c ↔ NoCrossingDefectIsNegOne (gaugeTransform u U) c := by
    unfold NoCrossingDefectIsNegOne
    refine forall₂_congr fun x hx => forall_congr' fun σ => forall_congr' fun σ' => ?_
    rw [hCross x hx σ σ']
    exact not_congr (conj_eq_neg_one_iff (isUnit_det_of_mem ht)).symm
  refine ⟨blockAverageCase_congr hA hN,
    blockAverageOnPositive_of_iff (f := fun M => t * M * s⁻¹) hA hN ?_ ?_ hTr⟩
  · rintro ⟨-, h1, h2, h3⟩
    have hsum : (∑ᶠ x ∈ sitesInBlock (levelDepth K k) c.source,
        ComplexMatrix2.logSeries (crossingDefect (gaugeTransform u U) c x)) =
        t * (∑ᶠ x ∈ sitesInBlock (levelDepth K k) c.source,
          ComplexMatrix2.logSeries (crossingDefect U c x)) * t⁻¹ := by
      rw [conj_finsum_mem (isUnit_det_of_mem ht)]
      refine finsum_mem_congr rfl fun x hx => ?_
      rw [hE x hx (h1 x hx) (h2 _ (hB.target_mem x hx))]
      exact T.norm.2.2.2.2.2.1 t _ ((Matrix.isUnit_iff_isUnit_det t).2 (isUnit_det_of_mem ht))
        (h3 x hx) (by rw [operatorNorm_conj_sub_one T ht]; exact h3 x hx)
    show regularAverageValue (gaugeTransform u U) c = t * regularAverageValue U c * s⁻¹
    unfold regularAverageValue
    rw [hsum, hTr]
    exact matExp_smul_conj_mul T (isUnit_det_of_mem ht) _ _ _
  · intro hN0
    have hsum : crossingLogSum (gaugeTransform u U) c = t * crossingLogSum U c * t⁻¹ := by
      unfold crossingLogSum
      rw [conj_finsum_mem (isUnit_det_of_mem ht)]
      refine finsum_mem_congr rfl fun x hx => ?_
      have e : ∀ σ σ', ComplexMatrix2.unitaryLog (contourCrossingDefect (gaugeTransform u U) c x σ σ') =
          conjLinearEquiv t (isUnit_det_of_mem ht)
            (ComplexMatrix2.unitaryLog (contourCrossingDefect U c x σ σ')) := by
        intro σ σ'
        rw [hCross x hx σ σ']
        exact (T.ilog.2.2 _ ⟨contourCrossingDefect_mem hB hU hx σ σ', fun h => hN0 x hx σ σ' h⟩
          t ht).2
      have e3 : ∀ σ, (∑ σ', ComplexMatrix2.unitaryLog
            (contourCrossingDefect (gaugeTransform u U) c x σ σ')) =
          conjLinearEquiv t (isUnit_det_of_mem ht)
            (∑ σ', ComplexMatrix2.unitaryLog (contourCrossingDefect U c x σ σ')) := by
        intro σ
        rw [map_sum]
        exact Finset.sum_congr rfl fun σ' _ => e σ σ'
      simp only [e3, ← map_smul, ← map_sum]
      rfl
    show ComplexMatrix2.matExp (inverseFourthPowerWeight L • crossingLogSum (gaugeTransform u U) c) *
        parallelTransport (gaugeTransform u U) c =
      t * (ComplexMatrix2.matExp (inverseFourthPowerWeight L • crossingLogSum U c) *
        parallelTransport U c) * s⁻¹
    rw [hsum, hTr]
    exact matExp_smul_conj_mul T (isUnit_det_of_mem ht) _ _ _
private theorem onPositive_mem (T : Ingredients L m) (hk : k < K) (ω : ℝ)
    {c : BondAtLevel L m K (k + 1)} (hc : c.IsPositivelyOriented)
    {U : BondAtLevel L m K k → ComplexMatrix2}
    (hU : IsGaugeField compactGaugeGroup (bondsInDoubleBlock c) U) :
    blockAverageOnPositive ω U c ∈ compactGaugeGroup := by
  have hB := doubleBlockPaths T hk c hc
  have hTr : parallelTransport U c ∈ compactGaugeGroup :=
    pathHolonomy_mem fun b hb => hU.1 b (hB.axial_bonds b hb)
  unfold blockAverageOnPositive
  split_ifs with h1 h2
  · obtain ⟨-, p1, p2, p3⟩ := h1
    refine mul_mem_compact (matExp_mem_of_mem_iLie T ?_) hTr
    refine ofReal_smul_mem_iLie _ ?_
    refine finsum_mem_induction (· ∈ iLie) (zero_mem _) (fun _ _ => add_mem) fun x hx => ?_
    exact logSeries_mem_iLie T
      (crossingDefect_mem hB hU hx (p1 x hx) (p2 _ (hB.target_mem x hx))) (p3 x hx)
  · refine mul_mem_compact (matExp_mem_of_mem_iLie T ?_) hTr
    refine ofReal_smul_mem_iLie _ ?_
    refine finsum_mem_induction (· ∈ iLie) (zero_mem _) (fun _ _ => add_mem) fun x hx => ?_
    refine ofReal_smul_mem_iLie _ (sum_mem fun σ _ => ofReal_smul_mem_iLie _
      (sum_mem fun σ' _ => unitaryLog_mem_iLie T ?_))
    exact ⟨contourCrossingDefect_mem hB hU hx σ σ', fun h => h2 x hx σ σ' h⟩
  · exact hTr
private theorem blockAverage_local (T : Ingredients L m) (hk : k < K) (ω : ℝ)
    (c : BondAtLevel L m K (k + 1)) {U U' : BondAtLevel L m K k → ComplexMatrix2}
    (h : ∀ b ∈ (bondsInDoubleBlock c : Set (BondAtLevel L m K k)), U b = U' b) :
    blockAverage ω U c = blockAverage ω U' c := by
  by_cases hc : c.IsPositivelyOriented
  · rw [blockAverage_of_pos ω U hc, blockAverage_of_pos ω U' hc]
    exact (onPositive_local T hk ω hc h).2
  · have hr := opposite_isPositivelyOriented_of_not hc
    rw [blockAverage_of_not_pos ω U hc, blockAverage_of_not_pos ω U' hc,
      (onPositive_local T hk ω hr fun b hb =>
        h b (by rwa [bondsInDoubleBlock_opposite] at hb)).2]
private theorem blockAverage_gaugeTransform (T : Ingredients L m) (hk : k < K) (ω : ℝ)
    (c : BondAtLevel L m K (k + 1)) {U : BondAtLevel L m K k → ComplexMatrix2}
    (hU : IsGaugeField compactGaugeGroup (bondsInDoubleBlock c) U)
    {u : SiteAtLevel L m K k → ComplexMatrix2} (hu : IsGaugeMap compactGaugeGroup u) :
    blockAverage ω (gaugeTransform u U) c =
      gaugeTransform (restrictGaugeMap (k + 1) u) (blockAverage ω U) c := by
  show _ = u (c.source.toSublattice (levelDepth K k)) * blockAverage ω U c *
    (u (c.target.toSublattice (levelDepth K k)))⁻¹
  by_cases hc : c.IsPositivelyOriented
  · rw [blockAverage_of_pos ω _ hc, blockAverage_of_pos ω U hc]
    exact (onPositive_gaugeTransform T hk ω hc hU hu).2
  · have hr := opposite_isPositivelyOriented_of_not hc
    have hU' : IsGaugeField compactGaugeGroup (bondsInDoubleBlock c.opposite) U := by
      rw [bondsInDoubleBlock_opposite]
      exact hU
    rw [blockAverage_of_not_pos ω _ hc, blockAverage_of_not_pos ω U hc,
      (onPositive_gaugeTransform T hk ω hr hU' hu).2]
    change (u (c.target.toSublattice (levelDepth K k)) * _ *
      (u (c.source.toSublattice (levelDepth K k)))⁻¹)⁻¹ = _
    rw [Matrix.mul_inv_rev, Matrix.mul_inv_rev,
      Matrix.nonsing_inv_nonsing_inv _ (isUnit_det_of_mem (hu _)), mul_assoc]
private theorem blockAverage_mem (T : Ingredients L m) (hk : k < K) (ω : ℝ)
    {U : BondAtLevel L m K k → ComplexMatrix2} (hU : U ∈ gaugeFieldsAtLevel L m K k) :
    (blockAverage ω U : BondAtLevel L m K (k + 1) → ComplexMatrix2) ∈
      gaugeFieldsAtLevel L m K (k + 1) := by
  have hP : ∀ c : BondAtLevel L m K (k + 1), c.IsPositivelyOriented →
      blockAverageOnPositive ω U c ∈ compactGaugeGroup := fun c hc => onPositive_mem T hk ω hc
    ⟨fun b _ => hU.1 b (mem_univ b), fun b _ => hU.2 b (mem_univ b)⟩
  have hj : -(m : ℤ) < levelDepth K (k + 1) := by
    have := T.hm
    simp only [levelDepth]
    omega
  have hL2 : 2 ≤ L := by
    have := T.hL.2
    omega
  refine ⟨fun b _ => ?_, fun b _ => ?_⟩
  · by_cases hb : b.IsPositivelyOriented
    · rw [blockAverage_of_pos ω U hb]
      exact hP b hb
    · rw [blockAverage_of_not_pos ω U hb]
      exact inv_mem_compact (hP _ (opposite_isPositivelyOriented_of_not hb))
  · rcases MatrixValued.xor_isPositivelyOriented_opposite hL2 hj b with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · have e : b.opposite.opposite = b := Bond.ext rfl rfl
      rw [blockAverage_of_not_pos ω U h2, blockAverage_of_pos ω U h1, e]
    · rw [blockAverage_of_pos ω U h1, blockAverage_of_not_pos ω U h2,
        Matrix.nonsing_inv_nonsing_inv _ (isUnit_det_of_mem (hP _ h1))]
private theorem blockAverage_covariant (T : Ingredients L m) (hk : k < K) :
    BlockAverageGaugeCovariant L m K k := by
  intro U hU u hu
  have hc : ∀ c : BondAtLevel L m K (k + 1),
      IsGaugeField compactGaugeGroup (bondsInDoubleBlock c) U := fun c =>
    ⟨fun b _ => hU.1 b (mem_univ b), fun b _ => hU.2 b (mem_univ b)⟩
  refine ⟨fun c hp => (onPositive_gaugeTransform T hk _ hp (hc c) hu).1.symm,
    fun y x hx hA => ?_, funext fun c => blockAverage_gaugeTransform T hk _ c (hc c) hu⟩
  have h := meanContourHolonomy_gaugeTransform T hk (ℬ := univ) (fun _ _ => mem_univ _) hU hu
    y hx fun _ _ _ => mem_univ _
  exact ⟨h.1.2 hA, h.2 hA⟩
private theorem blockAverage_localToDoubleBlock (T : Ingredients L m) (hk : k < K) :
    BlockAverageLocalToDoubleBlock L m K k := by
  intro c hc U _ U' _ h
  exact ⟨blockAverage_local T hk _ c h, (onPositive_local T hk _ hc h).1⟩
end OneStep
private theorem self_mem_refinedBlock (T : Ingredients L m) {j : ℤ} (hj : -(m : ℤ) ≤ j) (n : ℕ)
    (y : Site L m j) : (y : FourTorus L m) ∈ refinedBlock n y :=
  (T.blocks L m T.hL T.hm j n 0 hj).2.1.1 y
private theorem refinedBlock_subset (T : Ingredients L m) {j j' : ℤ} (hj : -(m : ℤ) ≤ j)
    (n₁ n₂ : ℕ) (e : j' = j + n₁) (y : Site L m j) (x : Site L m j')
    (hx : (x : FourTorus L m) ∈ refinedBlock n₁ y) :
    refinedBlock n₂ x ⊆ refinedBlock (n₁ + n₂) y := by
  subst e
  have h := (T.blocks L m T.hL T.hm j n₁ n₂ hj).2.2.1 y
  unfold RefinedBlockOfSumOrder at h
  intro z hz
  rw [h]
  exact Set.mem_iUnion₂.2 ⟨x, hx, hz⟩
private theorem refinedBlock_subset_of_mem_bondDoubleBlock (T : Ingredients L m) {k : ℕ}
    (hk : k < K) (c : BondAtLevel L m K (k + 1)) (n : ℕ) {x : SiteAtLevel L m K k}
    (hx : (x : FourTorus L m) ∈ bondDoubleBlock c) :
    refinedBlock n x ⊆ refinedBlock (n + 1) c.source ∪ refinedBlock (n + 1) c.target := by
  have e : levelDepth K k = levelDepth K (k + 1) + ((1 : ℕ) : ℤ) := by
    simp only [levelDepth]
    push_cast
    ring
  have hj : -(m : ℤ) ≤ levelDepth K (k + 1) := by
    simp only [levelDepth]
    omega
  rw [Nat.add_comm n 1]
  rcases hx with hx | hx
  · exact (refinedBlock_subset T hj 1 n e c.source x hx).trans Set.subset_union_left
  · exact (refinedBlock_subset T hj 1 n e c.target x hx).trans Set.subset_union_right
private theorem bondsInside_subset (T : Ingredients L m) {k : ℕ} (hk : k < K)
    (c : BondAtLevel L m K (k + 1)) (n : ℕ) {b : BondAtLevel L m K k}
    (hb : b ∈ (bondsInDoubleBlock c : Set (BondAtLevel L m K k))) {i : ℤ} :
    (bondsInside (refinedBlock n b.source ∪ refinedBlock n b.target) : Set (Bond L m i)) ⊆
      bondsInside (refinedBlock (n + 1) c.source ∪ refinedBlock (n + 1) c.target) := by
  have h := Set.union_subset (refinedBlock_subset_of_mem_bondDoubleBlock T hk c n hb.1)
    (refinedBlock_subset_of_mem_bondDoubleBlock T hk c n hb.2)
  exact fun a ha => ⟨h ha.1, h ha.2⟩
private theorem blockAverageIter_local (T : Ingredients L m) (ω : ℝ) (j n : ℕ) : j + n ≤ K →
    ∀ (c : BondAtLevel L m K (j + n)) (W W' : BondAtLevel L m K j → ComplexMatrix2),
      (∀ b ∈ (bondsInside (refinedBlock n c.source ∪ refinedBlock n c.target) :
        Set (BondAtLevel L m K j)), W b = W' b) →
      blockAverageIter ω j n W c = blockAverageIter ω j n W' c := by
  induction n with
  | zero =>
    intro hn c W W' h
    have hj : -(m : ℤ) ≤ levelDepth K (j + 0) := neg_le_levelDepth hn
    exact h c ⟨Or.inl (self_mem_refinedBlock T hj 0 _), Or.inr (self_mem_refinedBlock T hj 0 _)⟩
  | succ n ih =>
    intro hn c W W' h
    have hk : j + n < K := hn
    show blockAverage ω (blockAverageIter ω j n W) c = blockAverage ω (blockAverageIter ω j n W') c
    exact blockAverage_local T hk ω c fun b hb =>
      ih hk.le b W W' fun a ha => h a (bondsInside_subset T hk c n hb ha)
private theorem blockFieldAtLevel_local (T : Ingredients L m) (ω : ℝ) (n : ℕ) : n ≤ K →
    ∀ (c : BondAtLevel L m K n) (W W' : BondAtLevel L m K 0 → ComplexMatrix2),
      (∀ b ∈ (bondsInside (refinedBlock n c.source ∪ refinedBlock n c.target) :
        Set (BondAtLevel L m K 0)), W b = W' b) →
      blockFieldAtLevel ω n W c = blockFieldAtLevel ω n W' c := by
  induction n with
  | zero =>
    intro hn c W W' h
    have hj : -(m : ℤ) ≤ levelDepth K 0 := neg_le_levelDepth hn
    exact h c ⟨Or.inl (self_mem_refinedBlock T hj 0 _), Or.inr (self_mem_refinedBlock T hj 0 _)⟩
  | succ n ih =>
    intro hn c W W' h
    have hk : n < K := hn
    show blockAverage ω (blockFieldAtLevel ω n W) c = blockAverage ω (blockFieldAtLevel ω n W') c
    exact blockAverage_local T hk ω c fun b hb =>
      ih hk.le b W W' fun a ha => h a (bondsInside_subset T hk c n hb ha)
private theorem refinedBlock_subset_region (T : Ingredients L m) {a j : ℤ} (ha : -(m : ℤ) ≤ a)
    (haj : a ≤ j) {X : Set (FourTorus L m)} (hX : IsPartitionRegion a X) (y : Site L m j)
    (hy : (y : FourTorus L m) ∈ X) (n : ℕ) : refinedBlock n y ⊆ X := by
  obtain ⟨C, hC, rfl⟩ := hX
  obtain ⟨Q, hQ, hyQ⟩ := hy
  obtain ⟨z, rfl⟩ := hC hQ
  obtain ⟨d, hd⟩ : ∃ d : ℕ, j = a + d := ⟨(j - a).toNat, by omega⟩
  have hzy : (y : FourTorus L m) ∈ refinedBlock d z := ⟨hyQ, by rw [← hd]; exact y.2⟩
  intro p hp
  exact ⟨cubeAround z, hQ, (refinedBlock_subset T ha d n hd z y hzy hp).1⟩
private theorem extendByOne_gaugeTransform {i : ℤ} {ℬ : Set (Bond L m i)}
    (U : Bond L m i → ComplexMatrix2) (u : Site L m i → ComplexMatrix2) {b : Bond L m i}
    (hb : b ∈ ℬ) :
    extendByOne ℬ (gaugeTransform u U) b = gaugeTransform u (extendByOne ℬ U) b := by
  simp [extendByOne, gaugeTransform, hb]
private theorem partialBlockAverage_covariant (T : Ingredients L m) {k : ℕ} (hk : k < K) :
    PartialBlockAverageGaugeCovariant L m K k := by
  intro a ha haj X hX U hU u hu
  have hclosed := isReversalClosed_bondsInside (j := levelDepth K k) X
  have hExt := extendByOne_mem_compactGaugeFields hclosed hU
  have hXc : ∀ c ∈ (bondsInside X : Set (BondAtLevel L m K (k + 1))),
      (bondsInDoubleBlock c : Set (BondAtLevel L m K k)) ⊆ bondsInside X := by
    intro c hc b hb
    have hsub : bondDoubleBlock c ⊆ X := Set.union_subset
      (refinedBlock_subset_region T ha haj hX c.source hc.1 1)
      (refinedBlock_subset_region T ha haj hX c.target hc.2 1)
    exact ⟨hsub hb.1, hsub hb.2⟩
  have hEq : ∀ c ∈ (bondsInside X : Set (BondAtLevel L m K (k + 1))),
      ∀ b ∈ (bondsInDoubleBlock c : Set (BondAtLevel L m K k)),
        extendByOne (bondsInside X) (gaugeTransform u U) b =
          gaugeTransform u (extendByOne (bondsInside X) U) b :=
    fun c hc b hb => extendByOne_gaugeTransform U u (hXc c hc hb)
  have hconf : ∀ c : BondAtLevel L m K (k + 1), IsGaugeField compactGaugeGroup
      (bondsInDoubleBlock c) (extendByOne (bondsInside X) U) := fun c =>
    ⟨fun b _ => hExt.1 b (mem_univ b), fun b _ => hExt.2 b (mem_univ b)⟩
  refine ⟨fun c hc hp => ?_, fun y hy x hx hA => ?_, fun c hc => ?_⟩
  · rw [(onPositive_local T hk _ hp (hEq c hc)).1]
    exact (onPositive_gaugeTransform T hk _ hp (hconf c) hu).1.symm
  · have h := meanContourHolonomy_gaugeTransform T hk hclosed hU hu y hx
      fun σ b hb => hy ((orderedContour_facts T hk y hx σ).2 b hb)
    exact ⟨h.1.2 hA, h.2 hA⟩
  · show blockAverage (Averaging.smoothingRadius L)
        (extendByOne (bondsInside X) (gaugeTransform u U)) c =
      gaugeTransform (restrictGaugeMap (k + 1) u)
        (blockAverage (Averaging.smoothingRadius L) (extendByOne (bondsInside X) U)) c
    rw [blockAverage_local T hk _ c (hEq c hc)]
    exact blockAverage_gaugeTransform T hk _ c (hconf c) hu
private theorem coe_toSublattice (T : Ingredients L m) {j j' : ℤ} (h : j ≤ j') (y : Site L m j) :
    ((y.toSublattice j' : Site L m j') : FourTorus L m) = y :=
  Classical.epsilon_spec (p := fun x : Site L m j' => (x : FourTorus L m) = y)
    ⟨⟨y, sublattice_mono (by have := T.hL.2; omega) m h y.2⟩, rfl⟩
private theorem blockFieldAtLevel_facts (T : Ingredients L m) (ω : ℝ) (n : ℕ) : n ≤ K →
    ∀ U ∈ gaugeFieldsAtLevel L m K 0,
      (blockFieldAtLevel ω n U : BondAtLevel L m K n → ComplexMatrix2) ∈
        gaugeFieldsAtLevel L m K n ∧
      ∀ u : SiteAtLevel L m K 0 → ComplexMatrix2, IsGaugeMap compactGaugeGroup u →
        (blockFieldAtLevel ω n (gaugeTransform u U) : BondAtLevel L m K n → ComplexMatrix2) =
          gaugeTransform (restrictGaugeMap n u) (blockFieldAtLevel ω n U) := by
  induction n with
  | zero =>
    intro _ U hU
    refine ⟨hU, fun u _ => ?_⟩
    have e : restrictGaugeMap 0 u = u :=
      funext fun x => congrArg u (Subtype.ext (coe_toSublattice T le_rfl x))
    rw [e]
    rfl
  | succ n ih =>
    intro hn U hU
    have hk : n < K := hn
    obtain ⟨h1, h2⟩ := ih hk.le U hU
    refine ⟨blockAverage_mem T hk ω h1, fun u hu => ?_⟩
    have l1 : levelDepth K (n + 1) ≤ levelDepth K n := by
      simp only [levelDepth]
      omega
    have l2 : levelDepth K n ≤ levelDepth K 0 := by
      simp only [levelDepth]
      omega
    have e : restrictGaugeMap (n + 1) (restrictGaugeMap n u) = restrictGaugeMap (n + 1) u := by
      funext x
      refine congrArg u (Subtype.ext ?_)
      rw [coe_toSublattice T l2, coe_toSublattice T l1, coe_toSublattice T (l1.trans l2)]
    show blockAverage ω (blockFieldAtLevel ω n (gaugeTransform u U)) =
      gaugeTransform (restrictGaugeMap (n + 1) u) (blockAverage ω (blockFieldAtLevel ω n U))
    rw [h2 u hu, ← e]
    exact funext fun c => blockAverage_gaugeTransform T hk ω c
      ⟨fun b _ => h1.1 b (mem_univ b), fun b _ => h1.2 b (mem_univ b)⟩ fun x => hu _
private theorem regionBlockField_covariant (T : Ingredients L m) (n : ℕ) (hn : n ≤ K) :
    RegionBlockFieldGaugeCovariant L m K n := by
  intro a ha haj Ω₀ hΩ U hU u hu c hc
  have hclosed := isReversalClosed_bondsInside (j := levelDepth K 0) Ω₀
  have hExt := extendByOne_mem_compactGaugeFields hclosed hU
  have hsub : refinedBlock n c.source ∪ refinedBlock n c.target ⊆ Ω₀ := Set.union_subset
    (refinedBlock_subset_region T ha haj hΩ c.source hc.1 n)
    (refinedBlock_subset_region T ha haj hΩ c.target hc.2 n)
  show blockFieldAtLevel (Averaging.smoothingRadius L) n
      (extendByOne (bondsInside Ω₀) (gaugeTransform u U)) c =
    gaugeTransform (restrictGaugeMap n u)
      (blockFieldAtLevel (Averaging.smoothingRadius L) n (extendByOne (bondsInside Ω₀) U)) c
  rw [blockFieldAtLevel_local T _ n hn c _ (gaugeTransform u (extendByOne (bondsInside Ω₀) U))
      fun b hb => extendByOne_gaugeTransform U u ⟨hsub hb.1, hsub hb.2⟩,
    (blockFieldAtLevel_facts T _ n hn _ hExt).2 u hu]
private theorem blockField_mapsOrbits (T : Ingredients L m) (n : ℕ) (hn : n ≤ K) :
    BlockFieldMapsOrbitsToOrbits L m K n := by
  intro U hU
  have h := blockFieldAtLevel_facts T (Averaging.smoothingRadius L) n hn U hU
  refine ⟨blockFieldAtLevel (Averaging.smoothingRadius L) n U, h.1, ?_⟩
  rintro _ ⟨_, ⟨v, hv, rfl⟩, rfl⟩
  exact ⟨restrictGaugeMap n v, fun x => hv _, h.2 v hv⟩
private theorem complexLogMean_reindex {ι ι' : Type*} [Fintype ι] [Fintype ι'] (e : ι ≃ ι')
    (V : ι' → ComplexMatrix2) : complexLogMean (V ∘ e) = complexLogMean V := by apply _root_.YangMills.Construction.Averaging.ExplicitRadiiProof.complexLogMean_comp_equiv <;> assumption
private theorem familyDiameter_reindex {ι ι' : Type*} [Fintype ι] [Fintype ι'] (e : ι ≃ ι')
    (V : ι' → ComplexMatrix2) :
    ComplexMatrix2.familyDiameter (V ∘ e) = ComplexMatrix2.familyDiameter V :=
  (Equiv.prodCongr e e).iSup_comp
    (g := fun p : ι' × ι' => ComplexMatrix2.operatorNorm (V p.1 * (V p.2)⁻¹ - 1))
abbrev _root_.YangMills.SharedProofs.p70753 := @familyDiameter_reindex
private theorem familyDiameter_mul_mul (T : Ingredients L m) {ι : Type*} [Fintype ι]
    (V : ι → ComplexMatrix2) {W W' : ComplexMatrix2} (hW : W ∈ compactGaugeGroup)
    (hW' : W' ∈ compactGaugeGroup) :
    ComplexMatrix2.familyDiameter (fun i => W * V i * W') = ComplexMatrix2.familyDiameter V := by
  unfold ComplexMatrix2.familyDiameter
  refine iSup_congr fun p => ?_
  have e : (W * V p.1 * W') * (W * V p.2 * W')⁻¹ = W * (V p.1 * (V p.2)⁻¹) * W⁻¹ := by
    simp only [Matrix.mul_inv_rev, mul_assoc]
    rw [Matrix.mul_nonsing_inv_cancel_left _ _ (isUnit_det_of_mem hW')]
  rw [e]
  exact operatorNorm_conj_sub_one T hW _
private theorem complexLogMean_facts (T : Ingredients L m) {ι : Type} [Fintype ι] [Nonempty ι]
    {V : ι → ComplexMatrix2} (hV : ∀ i, V i ∈ complexGaugeGroup)
    (hd : ComplexMatrix2.familyDiameter V < Averaging.centreOfMassDiameter) :
    complexLogMean V ∈ complexGaugeGroup ∧ ∀ W ∈ compactGaugeGroup, ∀ W' ∈ compactGaugeGroup,
      complexLogMean (fun i => W * V i * W') = W * complexLogMean V * W' := by
  obtain ⟨n, ⟨e⟩⟩ : ∃ n, Nonempty (ι ≃ Fin n) := ⟨_, ⟨Fintype.equivFin ι⟩⟩
  have hn : 1 ≤ n := Fin.pos_iff_nonempty.2 (Nonempty.map e ‹_›)
  have hM := T.cmean.2.2.2.1 n hn
  have eM : complexLogMean (V ∘ e.symm) = complexLogMean V := complexLogMean_reindex e.symm V
  have hS : V ∘ e.symm ∈ Averaging.smallComplexFamilies n :=
    ⟨fun i => hV _, by rw [familyDiameter_reindex]; exact hd⟩
  constructor
  · rw [← eM]
    obtain ⟨W, hW, -⟩ := hM.existsUnique _ hS
    exact (Classical.epsilon_spec (p := fun W =>
      ComplexMatrix2.IsLogMean complexGaugeGroup (V ∘ e.symm) W ∧
        ∃ i, ComplexMatrix2.operatorNorm ((V ∘ e.symm) i * W⁻¹ - 1) ≤ complexMeanTolerance)
      ⟨W, hW⟩).1.1
  · intro W hW W' hW'
    have e1 := hM.covariant _ hS W hW W' hW'
    have e2 := complexLogMean_reindex e.symm (fun i => W * V i * W')
    rw [← e2, ← eM]
    exact e1
private theorem complexBlockAverage_covariant (T : Ingredients L m) {k : ℕ} (hk : k < K) :
    ComplexBlockAverageGaugeCovariant L m K k := by
  intro c hc U hUd u hu
  have hB := doubleBlockPaths T hk c hc
  have hcl := isReversalClosed_bondsInDoubleBlock (j' := levelDepth K k) c
  obtain ⟨⟨hUc, hdT, hdH⟩, hsmall⟩ := hUd
  have hj := neg_le_levelDepth (m := m) hk.le
  set t := u (c.source.toSublattice (levelDepth K k)) with htd
  set s := u (c.target.toSublattice (levelDepth K k)) with hsd
  have ht : t ∈ compactGaugeGroup := hu _
  have hs : s ∈ compactGaugeGroup := hu _
  have hne : ∀ (y : SiteAtLevel L m K (k + 1)) (x : SiteAtLevel L m K k),
      Nonempty (AxisOrdering y x) :=
    fun y x => ⟨(offsetAxes y x).equivFin.symm⟩
  have hvT : ∀ x ∈ sitesInBlock (levelDepth K k) c.source,
      contourHolonomies (gaugeTransform u U) c.source x =
        fun σ => t * contourHolonomies U c.source x σ * (u x)⁻¹ :=
    fun x hx => contourHolonomies_gaugeTransform T hk hcl hUc hu c.source hx
      (hB.source_contours x hx)
  have hvH : ∀ x ∈ sitesInBlock (levelDepth K k) c.target,
      contourHolonomies (gaugeTransform u U) c.target x =
        fun σ => s * contourHolonomies U c.target x σ * (u x)⁻¹ :=
    fun x hx => contourHolonomies_gaugeTransform T hk hcl hUc hu c.target hx
      (hB.target_contours x hx)
  have hAT : ∀ x ∈ sitesInBlock (levelDepth K k) c.source,
      complexMeanContourHolonomy (gaugeTransform u U) c.source x =
        t * complexMeanContourHolonomy U c.source x * (u x)⁻¹ := by
    intro x hx
    have := hne c.source x
    unfold complexMeanContourHolonomy
    rw [hvT x hx]
    exact (complexLogMean_facts T (fun σ => pathHolonomy_mem_complex fun b hb =>
      hUc.1 b (hB.source_contours x hx σ b hb)) (hdT x hx)).2 _ ht _ (inv_mem_compact (hu x))
  have hAH : ∀ x ∈ sitesInBlock (levelDepth K k) c.target,
      complexMeanContourHolonomy (gaugeTransform u U) c.target x =
        s * complexMeanContourHolonomy U c.target x * (u x)⁻¹ := by
    intro x hx
    have := hne c.target x
    unfold complexMeanContourHolonomy
    rw [hvH x hx]
    exact (complexLogMean_facts T (fun σ => pathHolonomy_mem_complex fun b hb =>
      hUc.1 b (hB.target_contours x hx σ b hb)) (hdH x hx)).2 _ hs _ (inv_mem_compact (hu x))
  have hH : ∀ x ∈ sitesInBlock (levelDepth K k) c.source,
      pathHolonomy (gaugeTransform u U) (crossingPath c x) =
        u x * pathHolonomy U (crossingPath c x) * (u (shiftAcross c x))⁻¹ :=
    fun x hx => pathHolonomy_gaugeTransform T hj hcl hUc hu (hB.crossing_path x hx)
      (hB.crossing_bonds x hx)
  have hTr : parallelTransport (gaugeTransform u U) c = t * parallelTransport U c * s⁻¹ :=
    pathHolonomy_gaugeTransform T hj hcl hUc hu hB.axial_path hB.axial_bonds
  have hE : ∀ x ∈ sitesInBlock (levelDepth K k) c.source,
      complexCrossingDefect (gaugeTransform u U) c x = t * complexCrossingDefect U c x * t⁻¹ := by
    intro x hx
    unfold complexCrossingDefect
    rw [hAT x hx, hAH _ (hB.target_mem x hx), hH x hx, hTr]
    exact conj_four_factors (isUnit_det_of_mem (hu x)) (isUnit_det_of_mem (hu _))
      (isUnit_det_of_mem hs) _ _ _ _
  have hconf : IsGaugeField complexGaugeGroup (bondsInDoubleBlock c) (gaugeTransform u U) :=
    (T.gauge L m T.hL.1 T.hL.2 T.hm (levelDepth K k) hj _ U u u hcl hUc (gaugeMap_complex hu)
      (gaugeMap_complex hu)).1.1
  refine ⟨⟨⟨hconf, fun x hx => ?_, fun x hx => ?_⟩, fun x hx => ?_⟩, ?_, ?_⟩
  · rw [hvT x hx, familyDiameter_mul_mul T _ ht (inv_mem_compact (hu x))]
    exact hdT x hx
  · rw [hvH x hx, familyDiameter_mul_mul T _ hs (inv_mem_compact (hu x))]
    exact hdH x hx
  · rw [hE x hx, operatorNorm_conj_sub_one T ht]
    exact hsmall x hx
  · rintro y (rfl | rfl) x hx
    · exact hAT x hx
    · exact hAH x hx
  · have hsum : (∑ᶠ x ∈ sitesInBlock (levelDepth K k) c.source,
        ComplexMatrix2.logSeries (complexCrossingDefect (gaugeTransform u U) c x)) =
        t * (∑ᶠ x ∈ sitesInBlock (levelDepth K k) c.source,
          ComplexMatrix2.logSeries (complexCrossingDefect U c x)) * t⁻¹ := by
      rw [conj_finsum_mem (isUnit_det_of_mem ht)]
      refine finsum_mem_congr rfl fun x hx => ?_
      rw [hE x hx]
      exact T.norm.2.2.2.2.2.1 t _ ((Matrix.isUnit_iff_isUnit_det t).2 (isUnit_det_of_mem ht))
        (hsmall x hx) (by rw [operatorNorm_conj_sub_one T ht]; exact hsmall x hx)
    simp only [complexBlockAverage, if_pos hc]
    unfold complexBlockAverageOnPositive
    rw [hsum, hTr]
    exact matExp_smul_conj_mul T (isUnit_det_of_mem ht) _ _ _
theorem blockAverageLocalityAndCovariance_holds
    (h₁ : BlockPartition.Properties) (h₂ : BlockPaths.Statement)
    (h₃ : GaugeCovarianceOfHolonomy)
    (h₄ : ComplexMatrix2.LogMeanCovariance) (h₅ : ComplexMatrix2.OperatorNormUnderConjugation)
    (h₆ : ComplexMatrix2.UnitaryLogConjugationProperties)
    (h₇ : ComplexMatrix2.ExpLogEstimates) (h₈ : Averaging.ComplexLogMeanOfSmallFamilies) :
    BlockAverageLocalityAndCovariance := by
  intro L m K hL hm
  have T : Ingredients L m := ⟨hL, hm, h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈⟩
  exact ⟨fun k hk => ⟨blockAverage_covariant T hk, partialBlockAverage_covariant T hk,
      blockAverage_localToDoubleBlock T hk, complexBlockAverage_covariant T hk⟩,
    fun j n hjn c W _ W' _ h => blockAverageIter_local T _ j n hjn c W W' h,
    fun n hn => ⟨fun U hU u hu => (blockFieldAtLevel_facts T _ n hn U hU).2 u hu,
      regionBlockField_covariant T n hn, blockField_mapsOrbits T n hn⟩⟩
end YangMills.Construction.PeriodicLattice
