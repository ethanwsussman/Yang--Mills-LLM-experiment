import YangMills.Construction.Lattice.ChessboardEstimateAtEveryGridDatum
import YangMills.Construction.Lattice.ChessboardValuesAsSeminormsOfAGridDatum
import YangMills.Construction.Lattice.CopyRuleOfAGridDatum
import Mathlib
set_option autoImplicit false
open MeasureTheory
open scoped ComplexOrder
noncomputable section
namespace YangMills.Construction.CheckerboardSeminorms
variable {L : ℕ} {κ : ℤ} {d : CellGrid L κ}
theorem isProbabilityMeasure_gibbsMeasure (hw : GridLattice.BoltzmannWeightIntegrable d)
    {β : ℝ} (hβ : 0 < β) : IsProbabilityMeasure (d.gibbsMeasure β) := by
  obtain ⟨-, hpos, hint, hZ⟩ := hw.2 β hβ
  have hZpos : 0 < d.normalizingIntegral β := hZ
  have hlint : ∫⁻ U, ENNReal.ofReal (d.boltzmannFactor β U)
      ∂(BoxTorus.haarConfigMeasure L κ d.sideLengths) =
        ENNReal.ofReal (d.normalizingIntegral β) :=
    (ofReal_integral_eq_lintegral_ofReal hint
      (Filter.Eventually.of_forall fun U => (hpos U).le)).symm
  constructor
  rw [CellGrid.gibbsMeasure, Measure.smul_apply, smul_eq_mul,
    withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ, hlint]
  exact ENNReal.inv_mul_cancel (by simpa using hZpos) ENNReal.ofReal_ne_top
theorem measurable_of_mem_cellObservables {c : d.spaceCells} {F : d.GaugeConfig → ℂ}
    (hF : F ∈ d.cellObservables c) : Measurable F := by
  obtain ⟨f, hf, -, hFf⟩ := hF
  have e : F = fun U => f fun b => U b.1 := funext hFf
  rw [e]
  exact hf.comp (measurable_pi_lambda _ fun b => measurable_pi_apply _)
theorem exists_norm_le_of_mem_cellObservables {c : d.spaceCells} {F : d.GaugeConfig → ℂ}
    (hF : F ∈ d.cellObservables c) : ∃ C : ℝ, ∀ U, ‖F U‖ ≤ C := by
  obtain ⟨f, -, ⟨C, hC⟩, hFf⟩ := hF
  exact ⟨C, fun U => by rw [hFf U]; exact hC _⟩
theorem integrable_prod_cellObservables [Fintype d.spaceCells] (μ : Measure d.GaugeConfig)
    [IsFiniteMeasure μ] (G : (c : d.spaceCells) → d.cellObservables c) :
    Integrable (fun U => ∏ c : d.spaceCells, (G c).1 U) μ := by
  have hbound : ∀ c : d.spaceCells, ∃ C : ℝ, ∀ U, ‖(G c).1 U‖ ≤ C :=
    fun c => exists_norm_le_of_mem_cellObservables (G c).2
  choose C hC using hbound
  refine Integrable.of_bound
    (Finset.measurable_prod _ fun c _ =>
      measurable_of_mem_cellObservables (G c).2).aestronglyMeasurable
    (∏ c, C c) (Filter.Eventually.of_forall fun U => ?_)
  rw [norm_prod]
  exact Finset.prod_le_prod (fun c _ => norm_nonneg _) fun c _ => hC c U
theorem checkerboardCopy_apply_of_sign_eq_one {c c' : d.spaceCells} (F : d.cellObservables c)
    (h : d.inducedSign (d.cellTransporter c.1 c'.1) = 1) (U : d.GaugeConfig) :
    d.checkerboardCopy c c' F U =
      F.1 ((d.symmetryOfMap (d.cellTransporter c.1 c'.1)).pullback U) := by
  unfold CellGrid.checkerboardCopy
  rw [if_pos h]
  rfl
theorem checkerboardCopy_apply_of_sign_ne_one {c c' : d.spaceCells} (F : d.cellObservables c)
    (h : ¬ d.inducedSign (d.cellTransporter c.1 c'.1) = 1) (U : d.GaugeConfig) :
    d.checkerboardCopy c c' F U = starRingEnd ℂ
      (F.1 ((d.symmetryOfMap (d.cellTransporter c.1 c'.1)).pullback U)) := by
  unfold CellGrid.checkerboardCopy
  rw [if_neg h]
  rfl
theorem checkerboardCopy_cellConj {c : d.spaceCells} (c' : d.spaceCells)
    (F : d.cellObservables c) (U : d.GaugeConfig) :
    d.checkerboardCopy c c' (d.cellConj c F) U =
      starRingEnd ℂ (d.checkerboardCopy c c' F U) := by
  by_cases h : d.inducedSign (d.cellTransporter c.1 c'.1) = 1
  · rw [checkerboardCopy_apply_of_sign_eq_one _ h, checkerboardCopy_apply_of_sign_eq_one _ h]
    rfl
  · rw [checkerboardCopy_apply_of_sign_ne_one _ h, checkerboardCopy_apply_of_sign_ne_one _ h]
    rfl
theorem checkerboardCopy_cellSmul {c : d.spaceCells} (c' : d.spaceCells) (z : ℂ)
    (F : d.cellObservables c) (U : d.GaugeConfig) :
    d.checkerboardCopy c c' (d.cellSmul c z F) U =
      (open Classical in if d.inducedSign (d.cellTransporter c.1 c'.1) = 1 then z
        else starRingEnd ℂ z) * d.checkerboardCopy c c' F U := by
  by_cases h : d.inducedSign (d.cellTransporter c.1 c'.1) = 1
  · rw [checkerboardCopy_apply_of_sign_eq_one _ h, checkerboardCopy_apply_of_sign_eq_one _ h,
      if_pos h]
    rfl
  · rw [checkerboardCopy_apply_of_sign_ne_one _ h, checkerboardCopy_apply_of_sign_ne_one _ h,
      if_neg h]
    exact map_mul _ _ _
theorem checkerboardCopy_cellAdd {c : d.spaceCells} (c' : d.spaceCells)
    (F F' : d.cellObservables c) (U : d.GaugeConfig) :
    d.checkerboardCopy c c' (d.cellAdd c F F') U =
      d.checkerboardCopy c c' F U + d.checkerboardCopy c c' F' U := by
  by_cases h : d.inducedSign (d.cellTransporter c.1 c'.1) = 1
  · rw [checkerboardCopy_apply_of_sign_eq_one _ h, checkerboardCopy_apply_of_sign_eq_one _ h,
      checkerboardCopy_apply_of_sign_eq_one _ h]
    rfl
  · rw [checkerboardCopy_apply_of_sign_ne_one _ h, checkerboardCopy_apply_of_sign_ne_one _ h,
      checkerboardCopy_apply_of_sign_ne_one _ h]
    exact map_add _ _ _
theorem checkerboardCopy_cellOne {c : d.spaceCells} (c' : d.spaceCells) (U : d.GaugeConfig) :
    d.checkerboardCopy c c' (d.cellOne c) U = 1 := by
  by_cases h : d.inducedSign (d.cellTransporter c.1 c'.1) = 1
  · rw [checkerboardCopy_apply_of_sign_eq_one _ h]
    rfl
  · rw [checkerboardCopy_apply_of_sign_ne_one _ h]
    exact map_one _
theorem norm_checkerboardCopy_le {c : d.spaceCells} (c' : d.spaceCells)
    (F : d.cellObservables c) {M : ℝ} (hM : ∀ U, ‖F.1 U‖ ≤ M) (U : d.GaugeConfig) :
    ‖d.checkerboardCopy c c' F U‖ ≤ M := by
  by_cases h : d.inducedSign (d.cellTransporter c.1 c'.1) = 1
  · rw [checkerboardCopy_apply_of_sign_eq_one _ h]
    exact hM _
  · rw [checkerboardCopy_apply_of_sign_ne_one _ h, RCLike.norm_conj]
    exact hM _
theorem exists_inducedSign_eq_neg_one (hg : GroupAndCells.ReflectionGroupActsOnCubes d)
    (hi : GroupAndCells.InducedMapsFormGroup d)
    (hs : GroupAndCells.SignDescends d) :
    ∃ h ∈ d.inducedGroupMaps, d.inducedSign h = -1 := by
  have hk := (hg.2.1 0 (Pi.single 0 1))
  obtain ⟨gbar, hind, -, -⟩ := hi.1 (d.cubeTransporter 0 (Pi.single 0 1)).1
    (d.cubeTransporter 0 (Pi.single 0 1)).2
  refine ⟨gbar, ⟨_, (d.cubeTransporter 0 (Pi.single 0 1)).2, hind⟩, ?_⟩
  rw [hs.2.1 (d.cubeTransporter 0 (Pi.single 0 1)) gbar hind, hk.2.2 _ hk.2.1]
  simp
theorem cellTransporter_eq_comp (hi : GroupAndCells.InducedMapsFormGroup d)
    (hst : GroupAndCells.SimplyTransitiveOnCells d) {h : d.Space → d.Space}
    (hh : h ∈ d.inducedGroupMaps) (c c' c'' : d.spaceCells) (e : c''.1 = h '' c'.1) :
    d.cellTransporter c.1 c''.1 = h ∘ d.cellTransporter c.1 c'.1 := by
  obtain ⟨hu, hc⟩ := hst.2 c.1 c.2 c''.1 c''.2
  obtain ⟨-, hc'⟩ := hst.2 c.1 c.2 c'.1 c'.2
  refine hu.unique hc ⟨hi.2.2.2.1 h hh _ hc'.1, ?_⟩
  rw [Set.image_comp, hc'.2, e]
open Classical in
theorem card_sign_one_eq_card_sign_ne_one [Fintype d.spaceCells]
    (hg : GroupAndCells.ReflectionGroupActsOnCubes d)
    (hi : GroupAndCells.InducedMapsFormGroup d)
    (hst : GroupAndCells.SimplyTransitiveOnCells d)
    (hs : GroupAndCells.SignDescends d) (c : d.spaceCells) :
    (Finset.univ.filter fun c' : d.spaceCells =>
        d.inducedSign (d.cellTransporter c.1 c'.1) = 1).card =
      (Finset.univ.filter fun c' : d.spaceCells =>
        ¬ d.inducedSign (d.cellTransporter c.1 c'.1) = 1).card := by
  obtain ⟨h, hh, hneg⟩ := exists_inducedSign_eq_neg_one hg hi hs
  obtain ⟨k, -, -, hk⟩ := hi.2.2.2.2 h hh
  have hinj : Function.Injective h :=
    Function.LeftInverse.injective (g := k) fun x => congrFun hk x
  let φ : d.spaceCells → d.spaceCells := fun c' => ⟨h '' c'.1, hst.1 h hh c'.1 c'.2⟩
  have hφ : Function.Injective φ := fun a b e =>
    Subtype.ext (hinj.image_injective (congrArg Subtype.val e))
  have hb : Function.Bijective φ := Finite.injective_iff_bijective.1 hφ
  refine Finset.card_bijective φ hb fun c' => ?_
  have e : d.inducedSign (d.cellTransporter c.1 (φ c').1) =
      -d.inducedSign (d.cellTransporter c.1 c'.1) := by
    rw [cellTransporter_eq_comp hi hst hh c c' (φ c') rfl,
      hs.2.2.2 h hh _ (hst.2 c.1 c.2 c'.1 c'.2).2.1, hneg]
    ring
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, e]
  rcases hs.2.2.1 _ (hst.2 c.1 c.2 c'.1 c'.2).2.1 with e1 | e1 <;> rw [e1] <;> norm_num
open Classical in
theorem prod_sign_twisted_eq_norm_pow [Fintype d.spaceCells]
    (hcard : Fintype.card d.spaceCells = d.numCells)
    (hg : GroupAndCells.ReflectionGroupActsOnCubes d)
    (hi : GroupAndCells.InducedMapsFormGroup d)
    (hst : GroupAndCells.SimplyTransitiveOnCells d)
    (hs : GroupAndCells.SignDescends d) (c : d.spaceCells) (z : ℂ) :
    ∏ c' : d.spaceCells, (if d.inducedSign (d.cellTransporter c.1 c'.1) = 1 then z
        else starRingEnd ℂ z) = ((‖z‖ ^ d.numCells : ℝ) : ℂ) := by
  have e := card_sign_one_eq_card_sign_ne_one hg hi hst hs c
  have hsum := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset d.spaceCells))
    (fun c' : d.spaceCells => d.inducedSign (d.cellTransporter c.1 c'.1) = 1)
  rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const, ← e, ← mul_pow, Complex.mul_conj,
    Complex.normSq_eq_norm_sq]
  rw [← e, Finset.card_univ, hcard] at hsum
  rw [← hsum]
  push_cast
  ring
theorem checkerboardNorm_le_of_re_le {β : ℝ} {c : d.spaceCells} {F : d.cellObservables c}
    {M : ℝ} (hM : 0 ≤ M) (hn : d.numCells ≠ 0) (h0 : 0 ≤ (d.copiesProductMean β c F).re)
    (h : (d.copiesProductMean β c F).re ≤ M ^ d.numCells) : d.checkerboardNorm β c F ≤ M := by
  have := Real.rpow_le_rpow h0 h (by positivity : (0 : ℝ) ≤ 1 / (d.numCells : ℝ))
  rwa [one_div, Real.pow_rpow_inv_natCast hM hn, ← one_div] at this
theorem checkerboardNorm_checkerboardCopy {β : ℝ} {c c' : d.spaceCells}
    {F : d.cellObservables c} (h : d.checkerboardCopy c c' F ∈ d.cellObservables c')
    (hcc : ∀ c'' : d.spaceCells,
      d.checkerboardCopy c' c'' ⟨d.checkerboardCopy c c' F, h⟩ = d.checkerboardCopy c c'' F) :
    d.checkerboardNorm β c' ⟨d.checkerboardCopy c c' F, h⟩ = d.checkerboardNorm β c F := by
  simp only [CellGrid.checkerboardNorm, CellGrid.copiesProductMean, hcc]
theorem checkerboardNorm_cellConj [Fintype d.spaceCells] (β : ℝ) (c : d.spaceCells)
    (F : d.cellObservables c) :
    d.checkerboardNorm β c (d.cellConj c F) = d.checkerboardNorm β c F := by
  have hp : ∀ U, ∏ᶠ c' : d.spaceCells, d.checkerboardCopy c c' (d.cellConj c F) U =
      starRingEnd ℂ (∏ᶠ c' : d.spaceCells, d.checkerboardCopy c c' F U) := fun U => by
    rw [finprod_eq_prod_of_fintype, finprod_eq_prod_of_fintype, map_prod]
    exact Finset.prod_congr rfl fun c' _ => checkerboardCopy_cellConj c' F U
  have hE : d.copiesProductMean β c (d.cellConj c F) =
      starRingEnd ℂ (d.copiesProductMean β c F) := by
    simp only [CellGrid.copiesProductMean, CellGrid.gibbsMean, hp]
    exact integral_conj
  simp only [CellGrid.checkerboardNorm, hE, Complex.conj_re]
theorem checkerboardNorm_cellOne (β : ℝ) [IsProbabilityMeasure (d.gibbsMeasure β)]
    (c : d.spaceCells) : d.checkerboardNorm β c (d.cellOne c) = 1 := by
  have hE : d.copiesProductMean β c (d.cellOne c) = 1 := by
    simp only [CellGrid.copiesProductMean, CellGrid.gibbsMean, checkerboardCopy_cellOne,
      finprod_one]
    simp
  simp [CellGrid.checkerboardNorm, hE]
theorem checkerboardNorm_le_iSup_norm [Fintype d.spaceCells] (β : ℝ)
    [IsProbabilityMeasure (d.gibbsMeasure β)]
    (hcard : Fintype.card d.spaceCells = d.numCells) (hn : d.numCells ≠ 0)
    (c : d.spaceCells) (F : d.cellObservables c) (h0 : 0 ≤ (d.copiesProductMean β c F).re) :
    d.checkerboardNorm β c F ≤ ⨆ U, ‖F.1 U‖ := by
  obtain ⟨C, hC⟩ := exists_norm_le_of_mem_cellObservables F.2
  have hbdd : BddAbove (Set.range fun U => ‖F.1 U‖) := ⟨C, by rintro _ ⟨U, rfl⟩; exact hC U⟩
  have hle : ∀ U, ‖F.1 U‖ ≤ ⨆ U, ‖F.1 U‖ := fun U => le_ciSup hbdd U
  have hM : 0 ≤ ⨆ U, ‖F.1 U‖ := Real.iSup_nonneg fun _ => norm_nonneg _
  refine checkerboardNorm_le_of_re_le hM hn h0 ((Complex.re_le_norm _).trans ?_)
  have hb : ∀ U, ‖∏ᶠ c' : d.spaceCells, d.checkerboardCopy c c' F U‖ ≤
      (⨆ U, ‖F.1 U‖) ^ d.numCells := fun U => by
    rw [finprod_eq_prod_of_fintype, norm_prod, ← hcard, ← Finset.card_univ, ← Finset.prod_const]
    exact Finset.prod_le_prod (fun _ _ => norm_nonneg _) fun c' _ =>
      norm_checkerboardCopy_le c' F hle U
  have := norm_integral_le_of_norm_le_const (μ := d.gibbsMeasure β)
    (Filter.Eventually.of_forall hb)
  simpa [CellGrid.copiesProductMean, CellGrid.gibbsMean] using this
theorem checkerboardNorm_cellSmul [Fintype d.spaceCells] (β : ℝ) (hn : d.numCells ≠ 0)
    (c : d.spaceCells) (z : ℂ) (F : d.cellObservables c)
    (h0 : 0 ≤ (d.copiesProductMean β c F).re)
    (hsigns : ∏ c' : d.spaceCells,
      (open Classical in if d.inducedSign (d.cellTransporter c.1 c'.1) = 1 then z
        else starRingEnd ℂ z) = ((‖z‖ ^ d.numCells : ℝ) : ℂ)) :
    d.checkerboardNorm β c (d.cellSmul c z F) = ‖z‖ * d.checkerboardNorm β c F := by
  have hp : ∀ U, ∏ᶠ c' : d.spaceCells, d.checkerboardCopy c c' (d.cellSmul c z F) U =
      ((‖z‖ ^ d.numCells : ℝ) : ℂ) * ∏ᶠ c' : d.spaceCells, d.checkerboardCopy c c' F U :=
    fun U => by
      rw [finprod_eq_prod_of_fintype, finprod_eq_prod_of_fintype, ← hsigns,
        ← Finset.prod_mul_distrib]
      exact Finset.prod_congr rfl fun c' _ => checkerboardCopy_cellSmul c' z F U
  have hE : d.copiesProductMean β c (d.cellSmul c z F) =
      ((‖z‖ ^ d.numCells : ℝ) : ℂ) * d.copiesProductMean β c F := by
    simp only [CellGrid.copiesProductMean, CellGrid.gibbsMean, hp]
    exact integral_const_mul _ _
  have hre : (d.copiesProductMean β c (d.cellSmul c z F)).re =
      ‖z‖ ^ d.numCells * (d.copiesProductMean β c F).re := by
    rw [hE, Complex.re_ofReal_mul]
  show (d.copiesProductMean β c (d.cellSmul c z F)).re ^ (1 / (d.numCells : ℝ)) =
    ‖z‖ * (d.copiesProductMean β c F).re ^ (1 / (d.numCells : ℝ))
  rw [hre, Real.mul_rpow (by positivity) h0, one_div,
    Real.pow_rpow_inv_natCast (norm_nonneg z) hn]
theorem checkerboardNorm_cellAdd_le [Fintype d.spaceCells] (β : ℝ)
    [IsProbabilityMeasure (d.gibbsMeasure β)]
    (hcard : Fintype.card d.spaceCells = d.numCells) (hn : d.numCells ≠ 0)
    (hest : d.CheckerboardBound β)
    (hmem : ∀ (c c' : d.spaceCells) (F : d.cellObservables c),
      d.checkerboardCopy c c' F ∈ d.cellObservables c')
    (hval : ∀ (c c' : d.spaceCells) (F : d.cellObservables c),
      d.checkerboardNorm β c' ⟨d.checkerboardCopy c c' F, hmem c c' F⟩ =
        d.checkerboardNorm β c F)
    (c : d.spaceCells) (F F' : d.cellObservables c) :
    d.checkerboardNorm β c (d.cellAdd c F F') ≤
      d.checkerboardNorm β c F + d.checkerboardNorm β c F' := by
  classical
  have hre : ∀ F₁ : d.cellObservables c, 0 ≤ (d.copiesProductMean β c F₁).re := fun F₁ =>
    (Complex.le_def.1 (hest.1 c F₁)).1
  have ha : 0 ≤ d.checkerboardNorm β c F := Real.rpow_nonneg (hre F) _
  have hb : 0 ≤ d.checkerboardNorm β c F' := Real.rpow_nonneg (hre F') _
  obtain ⟨G, hG⟩ : ∃ G : Finset d.spaceCells → (c' : d.spaceCells) → d.cellObservables c',
      ∀ S c', (c' ∈ S → (G S c').1 = d.checkerboardCopy c c' F ∧
          d.checkerboardNorm β c' (G S c') = d.checkerboardNorm β c F) ∧
        (c' ∉ S → (G S c').1 = d.checkerboardCopy c c' F' ∧
          d.checkerboardNorm β c' (G S c') = d.checkerboardNorm β c F') := by
    refine ⟨fun S c' => if c' ∈ S then ⟨_, hmem c c' F⟩ else ⟨_, hmem c c' F'⟩,
      fun S c' => ⟨fun h => ?_, fun h => ?_⟩⟩
    · simp only [if_pos h]
      exact ⟨trivial, hval c c' F⟩
    · simp only [if_neg h]
      exact ⟨trivial, hval c c' F'⟩
  have hexpand : ∀ U, ∏ᶠ c' : d.spaceCells, d.checkerboardCopy c c' (d.cellAdd c F F') U =
      ∑ S ∈ (Finset.univ : Finset d.spaceCells).powerset, ∏ c' : d.spaceCells, (G S c').1 U := by
    intro U
    rw [finprod_eq_prod_of_fintype]
    simp only [checkerboardCopy_cellAdd]
    rw [Finset.prod_add]
    refine Finset.sum_congr rfl fun S _ => ?_
    rw [← Finset.prod_sdiff (Finset.subset_univ S), mul_comm]
    congr 1
    · exact Finset.prod_congr rfl fun c' hc' => by
        rw [(hG S c').2 (Finset.mem_sdiff.1 hc').2 |>.1]
    · exact Finset.prod_congr rfl fun c' hc' => by rw [((hG S c').1 hc').1]
  have hE : d.copiesProductMean β c (d.cellAdd c F F') =
      ∑ S ∈ (Finset.univ : Finset d.spaceCells).powerset,
        d.gibbsMean β fun U => ∏ c' : d.spaceCells, (G S c').1 U := by
    simp only [CellGrid.copiesProductMean, CellGrid.gibbsMean, hexpand]
    exact integral_finsetSum _ fun S _ => integrable_prod_cellObservables _ (G S)
  have hterm : ∀ S : Finset d.spaceCells,
      ‖d.gibbsMean β fun U => ∏ c' : d.spaceCells, (G S c').1 U‖ ≤
        d.checkerboardNorm β c F ^ S.card *
          d.checkerboardNorm β c F' ^ ((Finset.univ : Finset d.spaceCells).card - S.card) := by
    intro S
    have h := hest.2 (G S)
    simp only [finprod_eq_prod_of_fintype] at h
    refine h.trans (le_of_eq ?_)
    rw [← Finset.prod_sdiff (Finset.subset_univ S), mul_comm]
    congr 1
    · rw [Finset.prod_congr rfl fun c' hc' => ((hG S c').1 hc').2, Finset.prod_const]
    · rw [Finset.prod_congr rfl fun c' hc' => ((hG S c').2 (Finset.mem_sdiff.1 hc').2).2,
        Finset.prod_const, Finset.card_sdiff_of_subset (Finset.subset_univ S)]
  refine checkerboardNorm_le_of_re_le (add_nonneg ha hb) hn (hre _)
    ((Complex.re_le_norm _).trans ?_)
  rw [hE, ← hcard, ← Finset.card_univ, ← Finset.sum_pow_mul_eq_add_pow]
  exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun S _ => hterm S)
theorem finprod_subtype_eq_finprod_of_eq_one {α M : Type*} [CommMonoid M] (S : Set α)
    (A : α → M) (hA : ∀ a, a ∉ S → A a = 1) : ∏ᶠ s : S, A s.1 = ∏ᶠ a, A a := by
  rw [finprod_set_coe_eq_finprod_mem, finprod_mem_def,
    Set.mulIndicator_eq_self.2 fun a ha => by_contra fun h => ha (hA a h)]
theorem checkerboardBound_on_set (β : ℝ) [IsProbabilityMeasure (d.gibbsMeasure β)]
    (hest : d.CheckerboardBound β) (S : Set d.spaceCells)
    (G : (c' : S) → d.cellObservables c'.1) :
    ‖d.gibbsMean β fun U => ∏ᶠ c' : S, (G c').1 U‖ ≤
      ∏ᶠ c' : S, d.checkerboardNorm β c'.1 (G c') := by
  classical
  obtain ⟨G', hG'⟩ : ∃ G' : (c : d.spaceCells) → d.cellObservables c,
      (∀ s : S, G' s.1 = G s) ∧ ∀ c, c ∉ S → G' c = d.cellOne c := by
    refine ⟨fun c => if h : c ∈ S then G ⟨c, h⟩ else d.cellOne c,
      fun s => dif_pos s.2, fun c h => dif_neg h⟩
  have e₁ : ∀ U, ∏ᶠ c' : S, (G c').1 U = ∏ᶠ c : d.spaceCells, (G' c).1 U := fun U => by
    rw [← finprod_subtype_eq_finprod_of_eq_one S (fun c => (G' c).1 U)
      fun c h => by rw [hG'.2 c h]; rfl]
    exact finprod_congr fun s => by rw [hG'.1 s]
  have e₂ : ∏ᶠ c' : S, d.checkerboardNorm β c'.1 (G c') =
      ∏ᶠ c : d.spaceCells, d.checkerboardNorm β c (G' c) := by
    rw [← finprod_subtype_eq_finprod_of_eq_one S (fun c => d.checkerboardNorm β c (G' c))
      fun c h => by rw [hG'.2 c h]; exact checkerboardNorm_cellOne β c]
    exact finprod_congr fun s => by rw [hG'.1 s]
  simp only [e₁, e₂]
  exact hest.2 G'
theorem statement_holds (hLat : GridLattice.Properties) (hGeom : GroupAndCells.AllHold)
    (hCopy : GridCopyRule.CopyRuleHolds) (hChess : CellGrid.CheckerboardBoundAtAllGrids) :
    Statement := by
  intro L κ d β hβ c F F' z
  obtain ⟨hcube, hind, hcells, hst, hsgn, -, -⟩ := hGeom L κ d
  obtain ⟨-, -, -, -, hdens⟩ := hLat L κ d
  have hest := hChess L κ d β hβ
  have := isProbabilityMeasure_gibbsMeasure hdens hβ
  have hn : d.numCells ≠ 0 := (Finset.prod_pos fun μ _ => d.counts_pos μ).ne'
  have : Finite d.spaceCells :=
    (Set.finite_of_ncard_ne_zero (by rw [hcells.2.2.2]; exact hn)).to_subtype
  let _ : Fintype d.spaceCells := Fintype.ofFinite _
  have hcard : Fintype.card d.spaceCells = d.numCells := by
    rw [← Nat.card_eq_fintype_card, Nat.card_coe_set_eq, hcells.2.2.2]
  have hmem : ∀ (c c' : d.spaceCells) (F : d.cellObservables c),
      d.checkerboardCopy c c' F ∈ d.cellObservables c' := fun c c' F => by
    obtain ⟨h, -⟩ := hCopy L κ d c c' F
    exact h
  have hval : ∀ (c c' : d.spaceCells) (F : d.cellObservables c),
      d.checkerboardNorm β c' ⟨d.checkerboardCopy c c' F, hmem c c' F⟩ =
        d.checkerboardNorm β c F := fun c c' F => by
    obtain ⟨h, -, -, hcc, -⟩ := hCopy L κ d c c' F
    exact checkerboardNorm_checkerboardCopy _ hcc
  have hre : ∀ (c : d.spaceCells) (F₁ : d.cellObservables c),
      0 ≤ (d.copiesProductMean β c F₁).re := fun c F₁ =>
    (Complex.le_def.1 (hest.1 c F₁)).1
  refine ⟨⟨fun c' => ⟨hmem c c' F, hval c c' F⟩, checkerboardNorm_cellConj β c F⟩,
    ⟨checkerboardNorm_le_iSup_norm β hcard hn c F (hre c F), checkerboardNorm_cellOne β c⟩,
    ⟨checkerboardNorm_cellSmul β hn c z F (hre c F)
        (prod_sign_twisted_eq_norm_pow hcard hcube hind hst hsgn c z),
      checkerboardNorm_cellAdd_le β hcard hn hest hmem hval c F F'⟩,
    fun S G => checkerboardBound_on_set β hest S G⟩
end YangMills.Construction.CheckerboardSeminorms
end
