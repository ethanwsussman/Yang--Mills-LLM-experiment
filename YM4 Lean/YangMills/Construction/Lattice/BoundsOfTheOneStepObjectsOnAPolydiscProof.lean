import YangMills.Construction.Lattice.BoundsOfTheOneStepObjectsOnAPolydisc
import YangMills.Construction.Lattice.LayerBondsCoarseSpacesAndAverages
import YangMills.Construction.Lattice.LevelBondOrientationDichotomy
import YangMills.Construction.Lattice.MatricesBlocksAndGaugeTransformations
import YangMills.Construction.Lattice.SchemeObjectsNearTheIdentity
import YangMills.Construction.Matrices.ExpLogEstimates
import Mathlib
set_option autoImplicit false
open scoped Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction
open Matrices
namespace PeriodicLattice
namespace OneStepBounds
theorem norm_le_one_add_norm_sub_one (M : ComplexMatrix2) : ‖M‖ ≤ 1 + ‖M - 1‖ := by
  have hM : M = 1 + (M - 1) := by abel
  calc ‖M‖ = ‖1 + (M - 1)‖ := by rw [← hM]
    _ ≤ ‖(1 : ComplexMatrix2)‖ + ‖M - 1‖ := norm_add_le _ _
    _ = 1 + ‖M - 1‖ := by rw [norm_one]
theorem norm_mul_sub_one_le_of_le {M N : ComplexMatrix2} {α β γ : ℝ} (hM : ‖M - 1‖ ≤ α)
    (hN : ‖N - 1‖ ≤ β) (hγ : α + β + α * β ≤ γ) : ‖M * N - 1‖ ≤ γ := by
  have e : M * N - 1 = (M - 1) + (N - 1) + (M - 1) * (N - 1) := by noncomm_ring
  have hα : 0 ≤ α := (norm_nonneg _).trans hM
  rw [e]
  calc _ ≤ ‖M - 1‖ + ‖N - 1‖ + ‖M - 1‖ * ‖N - 1‖ :=
        (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) (norm_mul_le _ _))
    _ ≤ α + β + α * β := by
        have := mul_le_mul hM hN (norm_nonneg _) hα
        linarith
    _ ≤ γ := hγ
section Series
variable (hExp : ComplexMatrix2.ExpLogEstimates)
include hExp
theorem norm_matExp_sub_one_le {Z : ComplexMatrix2} {t : ℝ} (ht : t ≤ 1) (hZ : ‖Z‖ ≤ t) :
    ‖ComplexMatrix2.matExp Z - 1‖ ≤ 2 * t := by
  have h := (hExp.1 Z).2
  have h₂ := Real.abs_exp_sub_one_le (x := ‖Z‖) (by rw [abs_of_nonneg (norm_nonneg _)]; linarith)
  rw [abs_of_nonneg (norm_nonneg _)] at h₂
  exact h.trans (((le_abs_self _).trans h₂).trans (by linarith))
theorem norm_inv_sub_one_le {M : ComplexMatrix2} {t : ℝ} (ht : t ≤ 1 / 2) (hM : ‖M - 1‖ ≤ t) :
    ‖M⁻¹ - 1‖ ≤ 2 * t := by
  have hlt : ‖M - 1‖ < 1 := by linarith
  have h := (hExp.2.2.2.1 (M - 1) hlt).2.2.2.1
  have e : 1 + (M - 1) = M := by abel
  rw [e] at h
  refine h.trans ?_
  rw [div_le_iff₀ (by linarith)]
  nlinarith [norm_nonneg (M - 1)]
theorem norm_logSeries_le {M : ComplexMatrix2} {t : ℝ} (ht : t ≤ 1 / 2) (hM : ‖M - 1‖ ≤ t) :
    ‖ComplexMatrix2.logSeries M‖ ≤ 2 * t := by
  have hlt : ‖M - 1‖ < 1 := by linarith
  have h := hExp.2.2.2.1 (M - 1) hlt
  have e : 1 + (M - 1) = M := by abel
  rw [e] at h
  refine h.1.trans (h.2.1.trans ?_)
  rw [div_le_iff₀ (by linarith)]
  nlinarith [norm_nonneg (M - 1)]
theorem norm_inv_I_smul_logSeries_le {M : ComplexMatrix2} {t : ℝ} (ht : t ≤ 1 / 2)
    (hM : ‖M - 1‖ ≤ t) : ‖Complex.I⁻¹ • ComplexMatrix2.logSeries M‖ ≤ 2 * t := by
  rw [norm_smul, norm_inv, Complex.norm_I, inv_one, one_mul]
  exact norm_logSeries_le hExp ht hM
end Series
theorem operatorNorm_le_supOperatorNorm {ι : Type*} [Finite ι] (f : ι → ↥ComplexMatrix2.traceless)
    (i : ι) : ComplexMatrix2.operatorNorm (f i : ComplexMatrix2) ≤ supOperatorNorm f :=
  le_ciSup (f := fun i => ComplexMatrix2.operatorNorm (f i : ComplexMatrix2))
    (Set.finite_range _).bddAbove i
variable {L m K n : ℕ}
theorem trivialGaugeField_isNearOne (c : BondAtLevel L m K (n + 1)) :
    IsNearOneOnDoubleBlock 0 c (trivialGaugeField : BondAtLevel L m K n → ComplexMatrix2) := by
  refine ⟨⟨fun b _ => ?_, fun b _ => ?_⟩, fun b _ => ?_⟩
  · show (1 : ComplexMatrix2).det = 1
    simp
  · simp [trivialGaugeField]
  · simp [trivialGaugeField]
theorem twistedConfig_isNearOne (hExp : ComplexMatrix2.ExpLogEstimates)
    [Finite (BondAtLevel L m K n)]
    (hXor : ∀ b : BondAtLevel L m K n, Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented)
    {c : BondAtLevel L m K (n + 1)} (a : LieBondField (doubleBlockSymmetricSet c))
    {W₀ : BondAtLevel L m K n → ComplexMatrix2} {ε₀ r : ℝ} (hr : supOperatorNorm a ≤ r)
    (hr1 : r ≤ 1 / 2) (hu : 2 * r + ε₀ + 2 * r * ε₀ ≤ 1 / 2)
    (hW : IsNearOneOnDoubleBlock ε₀ c W₀) :
    IsNearOneOnDoubleBlock (2 * (2 * r + ε₀ + 2 * r * ε₀)) c (twistedConfig c a W₀) := by
  obtain ⟨⟨hdet₀, -⟩, hnear⟩ := hW
  have hposval : ∀ b : BondAtLevel L m K n, b.IsPositivelyOriented →
      twistedConfig c a W₀ b =
        ComplexMatrix2.matExp (Complex.I • (a.eval b : ComplexMatrix2)) * W₀ b := by
    intro b h
    simp only [twistedConfig, expTwist, if_pos h]
  have hnegval : ∀ b : BondAtLevel L m K n, ¬ b.IsPositivelyOriented →
      twistedConfig c a W₀ b =
        (ComplexMatrix2.matExp (Complex.I • (a.eval b.opposite : ComplexMatrix2)) *
          W₀ b.opposite)⁻¹ := by
    intro b h
    simp only [twistedConfig, expTwist, if_neg h]
  have hdet : ∀ b ∈ bondsInDoubleBlock c,
      (ComplexMatrix2.matExp (Complex.I • (a.eval b : ComplexMatrix2)) * W₀ b).det = 1 := by
    intro b hb
    have htr : ComplexMatrix2.fullTrace (a.eval b : ComplexMatrix2) = 0 := (a.eval b).2
    have h₁ : (W₀ b).det = 1 := hdet₀ b hb
    rw [Matrix.det_mul, h₁, mul_one, hExp.2.2.2.2.2.1]
    have : ComplexMatrix2.fullTrace (Complex.I • (a.eval b : ComplexMatrix2)) = 0 := by
      simp only [ComplexMatrix2.fullTrace] at htr ⊢
      rw [Matrix.trace_smul, htr, smul_zero]
    rw [this, Complex.exp_zero]
  have hclose : ∀ b ∈ bondsInDoubleBlock c, b.IsPositivelyOriented →
      ‖ComplexMatrix2.matExp (Complex.I • (a.eval b : ComplexMatrix2)) * W₀ b - 1‖ ≤
        2 * r + ε₀ + 2 * r * ε₀ := by
    intro b hb h
    have hv : ‖(a.eval b : ComplexMatrix2)‖ ≤ r := by
      have e := a.eval_of_positive ⟨b, hb, h⟩
      have e' : a.eval b = a ⟨b, hb, h⟩ := e
      rw [e']
      exact (operatorNorm_le_supOperatorNorm a _).trans hr
    have hE : ‖ComplexMatrix2.matExp (Complex.I • (a.eval b : ComplexMatrix2)) - 1‖ ≤ 2 * r := by
      refine norm_matExp_sub_one_le hExp (t := r) (by linarith) ?_
      rw [norm_smul, Complex.norm_I, one_mul]
      exact hv
    exact norm_mul_sub_one_le_of_le hE (hnear b hb) le_rfl
  have hrev : ∀ b ∈ bondsInDoubleBlock c, b.opposite ∈ bondsInDoubleBlock c :=
    (doubleBlockSymmetricSet c).opposite_mem
  refine ⟨⟨fun b hb => ?_, fun b hb => ?_⟩, fun b hb => ?_⟩
  · show (twistedConfig c a W₀ b).det = 1
    by_cases h : b.IsPositivelyOriented
    · rw [hposval b h]
      exact hdet b hb
    · rw [hnegval b h, Matrix.det_nonsing_inv, hdet _ (hrev b hb)]
      simp
  · rcases hXor b with ⟨h, h'⟩ | ⟨h', h⟩
    · rw [hposval b h, hnegval _ h']
      rfl
    · have hd := hdet _ (hrev b hb)
      rw [hposval _ h', hnegval b h,
        Matrix.nonsing_inv_nonsing_inv _ (by rw [hd]; exact isUnit_one)]
  · show ‖twistedConfig c a W₀ b - 1‖ ≤ _
    by_cases h : b.IsPositivelyOriented
    · rw [hposval b h]
      have h₁ := hclose b hb h
      have h₂ := (norm_nonneg _).trans h₁
      linarith
    · rw [hnegval b h]
      exact norm_inv_sub_one_le hExp hu
        (hclose _ (hrev b hb) (Bond.opposite_isPositivelyOriented h))
theorem isNearOneOnDoubleBlock_mono {c : BondAtLevel L m K (n + 1)}
    {W : BondAtLevel L m K n → ComplexMatrix2} {ε ε' : ℝ} (h : ε ≤ ε')
    (hW : IsNearOneOnDoubleBlock ε c W) : IsNearOneOnDoubleBlock ε' c W :=
  ⟨hW.1, fun b hb => (hW.2 b hb).trans h⟩
theorem contourHolonomy_isDefined_of_average {s : AveragingScheme} {c : BondAtLevel L m K (n + 1)}
    {W : BondAtLevel L m K n → ComplexMatrix2} (h : IsSchemeAverageDefined s W c)
    {y : SiteAtLevel L m K (n + 1)}
    (hy : y ∈ ({c.source, c.target} : Set (SiteAtLevel L m K (n + 1))))
    {x : SiteAtLevel L m K n} (hx : x ∈ sitesInBlock (levelDepth K n) y) :
    IsContourHolonomyDefined s W y x := by
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
  rcases hy with rfl | rfl
  · exact h.2.1.1 x hx
  · exact h.2.1.2 x hx
theorem norm_I_smul_blockMean_le {y : SiteAtLevel L m K (n + 1)} (hL : 0 < L)
    (hB : (sitesInBlock (levelDepth K n) y : Set (SiteAtLevel L m K n)).Finite)
    (hcard : (sitesInBlock (levelDepth K n) y : Set (SiteAtLevel L m K n)).ncard ≤ L ^ 4)
    {f : SiteAtLevel L m K n → ComplexMatrix2} {t : ℝ} (ht : 0 ≤ t)
    (hf : ∀ x ∈ sitesInBlock (levelDepth K n) y, ‖f x‖ ≤ t) :
    ‖Complex.I • (inverseFourthPowerWeight L • ∑ᶠ x ∈ sitesInBlock (levelDepth K n) y, f x)‖ ≤
      t := by
  have hsum : ‖∑ᶠ x ∈ sitesInBlock (levelDepth K n) y, f x‖ ≤ (L : ℝ) ^ 4 * t := by
    rw [finsum_mem_eq_finite_toFinset_sum _ hB]
    refine (norm_sum_le _ _).trans ?_
    refine (Finset.sum_le_card_nsmul _ _ _ fun x hx => hf x (hB.mem_toFinset.1 hx)).trans ?_
    rw [nsmul_eq_mul, ← Set.ncard_eq_toFinset_card _ hB]
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) ht
  have hw : ‖inverseFourthPowerWeight L‖ = ((L : ℝ) ^ 4)⁻¹ := by
    unfold inverseFourthPowerWeight
    rw [Complex.norm_real, Real.norm_of_nonneg (by positivity), zpow_neg]
    norm_cast
  rw [norm_smul, Complex.norm_I, one_mul, norm_smul, hw]
  calc ((L : ℝ) ^ 4)⁻¹ * ‖∑ᶠ x ∈ sitesInBlock (levelDepth K n) y, f x‖
      ≤ ((L : ℝ) ^ 4)⁻¹ * ((L : ℝ) ^ 4 * t) := mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = t := by field_simp
theorem stepQuantitiesBounded_of_near (hExp : ComplexMatrix2.ExpLogEstimates) (hL : 0 < L)
    {s : AveragingScheme} {c : BondAtLevel L m K (n + 1)}
    {a : LieBondField (doubleBlockSymmetricSet c)} {W₀ : BondAtLevel L m K n → ComplexMatrix2}
    (hblock : ∀ y : SiteAtLevel L m K (n + 1),
      (sitesInBlock (levelDepth K n) y : Set (SiteAtLevel L m K n)).Finite ∧
        (sitesInBlock (levelDepth K n) y : Set (SiteAtLevel L m K n)).ncard ≤ L ^ 4)
    (h₀ : SchemeObjectsNearOne (1 / 1000) s c W₀)
    (h : SchemeObjectsNearOne (1 / 1000) s c (twistedConfig c a W₀)) :
    StepQuantitiesBounded s c a W₀ := by
  have hratio : ∀ y ∈ ({c.source, c.target} : Set (SiteAtLevel L m K (n + 1))),
      ∀ x ∈ sitesInBlock (levelDepth K n) y, ‖stepRatio s c a W₀ y x - 1‖ ≤ 1 / 250 := by
    intro y hy x hx
    have hinv := norm_inv_sub_one_le hExp (t := 1 / 1000) (by norm_num) (h₀.contourNear y hy x hx)
    exact norm_mul_sub_one_le_of_le (h.contourNear y hy x hx) hinv (by norm_num)
  have hformed : ∀ y ∈ ({c.source, c.target} : Set (SiteAtLevel L m K (n + 1))),
      ∀ x ∈ sitesInBlock (levelDepth K n) y, IsContourRatioLogDefined s c a W₀ y x := by
    intro y hy x hx
    refine ⟨contourHolonomy_isDefined_of_average h.isDefined hy hx,
      contourHolonomy_isDefined_of_average h₀.isDefined hy hx, ?_⟩
    exact lt_of_le_of_lt (hratio y hy x hx) (by norm_num)
  have hlog : ∀ y ∈ ({c.source, c.target} : Set (SiteAtLevel L m K (n + 1))),
      ∀ x ∈ sitesInBlock (levelDepth K n) y, ‖stepLog s c a W₀ y x‖ ≤ 1 / 125 := by
    intro y hy x hx
    have := norm_inv_I_smul_logSeries_le hExp (t := 1 / 250) (by norm_num) (hratio y hy x hx)
    exact this.trans (by norm_num)
  have hgauge : ∀ y ∈ ({c.source, c.target} : Set (SiteAtLevel L m K (n + 1))),
      ‖stepGauge s c a W₀ y - 1‖ ≤ 2 / 125 := by
    intro y hy
    have := norm_I_smul_blockMean_le hL (hblock y).1 (hblock y).2 (t := 1 / 125) (by norm_num)
      (hlog y hy)
    exact (norm_matExp_sub_one_le hExp (t := 1 / 125) (by norm_num) this).trans (by norm_num)
  have hsource : c.source ∈ ({c.source, c.target} : Set (SiteAtLevel L m K (n + 1))) := Or.inl rfl
  have htarget : c.target ∈ ({c.source, c.target} : Set (SiteAtLevel L m K (n + 1))) := Or.inr rfl
  have hproduct : ‖stepProduct s c a W₀ - 1‖ ≤ 7 / 100 := by
    have h₁ := norm_inv_sub_one_le hExp (t := 2 / 125) (by norm_num) (hgauge _ hsource)
    have h₂ := norm_inv_sub_one_le hExp (t := 1 / 1000) (by norm_num) h₀.averageNear
    have h₃ := norm_mul_sub_one_le_of_le (γ := 1 / 25) h₁ h.averageNear (by norm_num)
    have h₄ := norm_mul_sub_one_le_of_le (γ := 3 / 50) h₃ (hgauge _ htarget) (by norm_num)
    exact norm_mul_sub_one_le_of_le h₄ h₂ (by norm_num)
  refine ⟨fun y hy x hx => ⟨hformed y hy x hx, (hlog y hy x hx).trans (by norm_num)⟩,
    fun y hy => ⟨fun x hx => hformed y hy x hx,
      lt_of_le_of_lt (hgauge y hy) (by norm_num), ?_⟩, ⟨⟨h.isDefined.2.1, h₀.isDefined.2.1,
        fun x hx => (hformed _ hsource x hx).2.2, fun x hx => (hformed _ htarget x hx).2.2⟩,
      h.isDefined, h₀.isDefined, lt_of_le_of_lt hproduct (by norm_num)⟩, ?_⟩
  · exact (norm_inv_I_smul_logSeries_le hExp (t := 2 / 125) (by norm_num) (hgauge y hy)).trans
      (by norm_num)
  · exact (norm_inv_I_smul_logSeries_le hExp (t := 7 / 100) (by norm_num) hproduct).trans
      (by norm_num)
theorem norm_conjugateBy_le (hExp : ComplexMatrix2.ExpLogEstimates) {V : ComplexMatrix2}
    (hV : ‖V - 1‖ ≤ 1 / 400) (X : ComplexMatrix2) :
    ‖ComplexMatrix2.conjugateBy V X‖ ≤ 2 * ‖X‖ := by
  have h₁ : ‖V‖ ≤ 1 + 1 / 400 := (norm_le_one_add_norm_sub_one V).trans (by linarith)
  have h₂ : ‖V⁻¹‖ ≤ 1 + 1 / 200 :=
    (norm_le_one_add_norm_sub_one _).trans
      (by have := norm_inv_sub_one_le hExp (t := 1 / 400) (by norm_num) hV; linarith)
  have hX := norm_nonneg X
  calc ‖V * X * V⁻¹‖ ≤ ‖V‖ * ‖X‖ * ‖V⁻¹‖ := (norm_mul_le _ _).trans
        (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
    _ ≤ (1 + 1 / 400) * ‖X‖ * (1 + 1 / 200) := by
        gcongr
    _ ≤ 2 * ‖X‖ := by nlinarith
end OneStepBounds
open OneStepBounds in
theorem oneStepPolydiscRadiusExists_holds (hNear : SchemeObjectsNearOneUniformly)
    (hExp : ComplexMatrix2.ExpLogEstimates)
    (hPos : LevelBondOrientationDichotomy)
    (hBlk : ElementaryStepFacts) :
    OneStepPolydiscRadiusExists := by
  intro L hL
  have hL0 : 0 < L := by
    have := hL.2
    omega
  obtain ⟨ε, hε, hnear⟩ := hNear L hL (1 / 1000) (by norm_num)
  refine ⟨min (1 / 100) (ε / 14), lt_min (by norm_num) (by linarith),
    (min_le_left _ _).trans (by norm_num), ?_⟩
  set r := min (1 / 100 : ℝ) (ε / 14) with hrdef
  have hr0 : 0 < r := lt_min (by norm_num) (by linarith)
  have hr1 : r ≤ 1 / 100 := min_le_left _ _
  have hr2 : r ≤ ε / 14 := min_le_right _ _
  intro m K n hm hn s c hc a₀ a ha₀ ha
  have : Finite (SiteAtLevel L m K n) :=
    SeparatedSequences.BaseParameters.site_finite hL0 m (levelDepth K n)
  have : Finite (BondAtLevel L m K n) :=
    Finite.of_injective (fun b : BondAtLevel L m K n => (b.source, b.target)) fun b b' hb =>
      Bond.ext (congrArg Prod.fst hb) (congrArg Prod.snd hb)
  have hXor : ∀ b : BondAtLevel L m K n,
      Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented :=
    hPos L m K hL hm (by omega) n hn.le
  have hB := (hBlk L m K n hL hm hn).2.2.2.2.2.1.2 n hn
  have hblock : ∀ y : SiteAtLevel L m K (n + 1),
      (sitesInBlock (levelDepth K n) y : Set (SiteAtLevel L m K n)).Finite ∧
        (sitesInBlock (levelDepth K n) y : Set (SiteAtLevel L m K n)).ncard ≤ L ^ 4 := by
    intro y
    have hcardB := hB.2.2.1 y
    have hfinB : (unitBlock y).Finite := by
      refine Set.finite_of_ncard_ne_zero ?_
      rw [hcardB]
      exact pow_ne_zero _ hL0.ne'
    refine ⟨hfinB.preimage Subtype.val_injective.injOn, ?_⟩
    rw [← Set.ncard_image_of_injective _ Subtype.val_injective, ← hcardB]
    refine Set.ncard_le_ncard ?_ hfinB
    rintro _ ⟨x, hx, rfl⟩
    exact hx
  have hnear₀ : IsNearOneOnDoubleBlock (4 * r) c (expOfBondField c a₀) := by
    have := twistedConfig_isNearOne hExp hXor a₀ (r := r) ha₀.le (by linarith)
      (by linarith) (trivialGaugeField_isNearOne c)
    exact isNearOneOnDoubleBlock_mono (by linarith) this
  have hnear₁ : IsNearOneOnDoubleBlock (14 * r) c (twistedConfig c a (expOfBondField c a₀)) := by
    have := twistedConfig_isNearOne hExp hXor a (r := r) ha.le (by linarith)
      (by nlinarith) hnear₀
    exact isNearOneOnDoubleBlock_mono (by nlinarith) this
  have h₀ := hnear m K n hm hn s c hc _ (isNearOneOnDoubleBlock_mono (by linarith) hnear₀)
  have h₁ := hnear m K n hm hn s c hc _ (isNearOneOnDoubleBlock_mono (by linarith) hnear₁)
  refine ⟨stepQuantitiesBounded_of_near hExp hL0 hblock h₀ h₁, ⟨h₀.isDefined,
    lt_of_le_of_lt h₀.averageNear (by norm_num), ?_⟩, fun x hx b hb X => ?_⟩
  · exact (norm_inv_I_smul_logSeries_le hExp (t := 1 / 1000) (by norm_num) h₀.averageNear).trans
      (by norm_num)
  · refine norm_conjugateBy_le hExp ?_ X
    exact norm_mul_sub_one_le_of_le (h₀.contourNear _ (Or.inl rfl) x hx) (h₀.axialNear x hx b hb)
      (by norm_num)
end PeriodicLattice
end YangMills.Construction
