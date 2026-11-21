import YangMills.Construction.PeriodicOperators.ImaginaryShiftOfASymbol
import YangMills.Construction.PeriodicOperators.IndexSetsOfATower
import YangMills.Construction.PeriodicOperators.NormOfTheSymbol
import YangMills.Construction.Towers.AveragesAreContractions
import YangMills.Construction.Towers.BoundsOfTheSymbolsOfTheAverages
import YangMills.Construction.Towers.TheFreeOperatorsArePeriodicOperators
import Mathlib
set_option autoImplicit false
open Set
open scoped ENNReal
noncomputable section
namespace YangMills.Construction.Tower.SymbolBounds
open PeriodicOperators
open PeriodicOperators.StripSymbols (openStripInterior)
open Tower.FreeResolvents
open Tower.FreeOperators (HasFiniteRangeEveryRate)
theorem quotHomNorm_symbolHom (I I' : PeriodicData) [Finite I.UnitQuot]
    (T : I'.Carrier → I.Carrier → ℂ) (κ : Fin 4 → ℂ) :
    quotHomNorm (symbolHom I I' T κ) = quotOpNorm I I' (quotSymbol I I' T κ) := by
  unfold quotHomNorm quotOpNorm
  congr 1
  funext f
  exact linearMapOfEntries_eq_applyKernel (quotSymbol I I' T κ) f
theorem addIVec_re_imVec (κ : Fin 4 → ℂ) :
    addIVec (toComplexVec fun μ => (κ μ).re) (PeriodicOperators.imVec κ) = κ := by
  funext μ
  apply Complex.ext <;> simp [addIVec, toComplexVec, PeriodicOperators.imVec]
theorem euclidNormVec_imVec_toComplexVec (y : InfiniteLattice.AmbientSpace) :
    TorusMetric.euclidNormVec (PeriodicOperators.imVec (toComplexVec y)) = 0 := by
  simp [TorusMetric.euclidNormVec, PeriodicOperators.imVec, toComplexVec]
theorem quotHomNorm_symbolHom_le_expConj (hshift : PeriodicOperators.SymbolImShift.Claim)
    (hnorm : PeriodicOperators.SymbolNormBound) {I I' : PeriodicData} (hI : IsPeriodic I)
    (hI' : IsPeriodic I') {T : I'.Carrier → I.Carrier → ℂ}
    (hT : HasFiniteRangeEveryRate I I' T) (κ : Fin 4 → ℂ) :
    quotHomNorm (symbolHom I I' T κ) ≤
      kernelOpNorm I I' (expConj I I' (PeriodicOperators.imVec κ) T) := by
  have : Finite I.UnitQuot := hI.finite_quot
  set θ := PeriodicOperators.imVec κ with hθ
  set y : InfiniteLattice.AmbientSpace := fun μ => (κ μ).re with hy
  have hθnn : 0 ≤ TorusMetric.euclidNormVec θ := Real.sqrt_nonneg _
  have hwidth : 0 < TorusMetric.euclidNormVec θ + 1 := by linarith
  have hy_mem : toComplexVec y ∈ strictImStrip (TorusMetric.euclidNormVec θ + 1 -
      TorusMetric.euclidNormVec θ) := by
    change TorusMetric.euclidNormVec (PeriodicOperators.imVec (toComplexVec y)) < _
    rw [euclidNormVec_imVec_toComplexVec]
    linarith
  obtain ⟨hper, -, hsym⟩ := hshift I I' hI hI' T _ hT.1 (hT.2.2 _ hwidth) θ (by linarith) _ hy_mem
  have hpoint : addIVec (toComplexVec y) θ = κ := addIVec_re_imVec κ
  rw [hpoint] at hsym
  have hmat : quotSymbol I I' T κ =
      quotSymbol I I' (expConj I I' θ T) (toComplexVec y) := by
    unfold quotSymbol
    rw [hsym]
  rw [quotHomNorm_symbolHom, hmat]
  exact hnorm I I' hI hI' _ hper y
theorem quotHomNorm_symbolHom_kernelTranspose (hstrip : PeriodicOperators.StripSymbols.Claim)
    (hquot : PeriodicOperators.Quotients.QuotientTransposeNorm) {I I' : PeriodicData}
    (hI : IsPeriodic I) (hI' : IsPeriodic I') {T : I'.Carrier → I.Carrier → ℂ}
    (hT : HasFiniteRangeEveryRate I I' T) (κ : Fin 4 → ℂ) :
    quotHomNorm (symbolHom I' I (kernelTranspose I I' T) κ) =
      quotHomNorm (symbolHom I I' T (-κ)) := by
  have : Finite I.UnitQuot := hI.finite_quot
  have : Finite I'.UnitQuot := hI'.finite_quot
  have hsumm : SymbolSummableAt I I' T (-κ) :=
    (hstrip.2.1 I I' hI hI').1.finiteRange T hT.1 hT.2.1 (-κ) (mem_univ _)
  have hcalc := ((hstrip.2.1 I I' hI hI').2.1 T (-κ) hT.1 hsumm).transpose.2.2
  rw [neg_neg] at hcalc
  rw [quotHomNorm_symbolHom, quotHomNorm_symbolHom, hcalc]
  have hsame := (hquot I I' hI hI' 1 one_pos).2.2.1 1 1 (Or.inl rfl) (Or.inl rfl)
  exact hsame.2.2.2 (quotSymbol I I' T (-κ))
theorem l1NormVec_imVec_le {κ : Fin 4 → ℂ} (hκ : κ ∈ openImStrip (1 / 8)) :
    TorusMetric.l1NormVec (PeriodicOperators.imVec κ) ≤ 1 / 2 := by
  have h : ∀ μ, |PeriodicOperators.imVec κ μ| ≤ 1 / 8 := fun μ => (hκ μ).le
  simp only [TorusMetric.l1NormVec, Fin.sum_univ_four]
  linarith [h 0, h 1, h 2, h 3]
theorem neg_mem_openImStrip {κ : Fin 4 → ℂ} (hκ : κ ∈ openImStrip (1 / 8)) :
    -κ ∈ openImStrip (1 / 8) := by
  intro μ
  simpa using hκ μ
theorem freeSymbolNormBounds_holds (hfree : Tower.FreeOperators.FreeOperatorsArePeriodic)
    (hcontr : Tower.SmoothingContraction.Claim)
    (hshift : PeriodicOperators.SymbolImShift.Claim) (hnorm : PeriodicOperators.SymbolNormBound)
    (hstrip : PeriodicOperators.StripSymbols.Claim)
    (hquot : PeriodicOperators.Quotients.QuotientTransposeNorm)
    (hindex : PeriodicOperators.TowerIndexSets.Claim) : FreeSymbolNormBounds := by
  intro L hL k hk κ hκ
  have hinterior : openStripInterior (1 / 8) = openImStrip (1 / 8) :=
    (hstrip.1 (1 / 8) (by norm_num)).1
  rw [hinterior] at hκ
  have hE₀ := (hindex L hL k 0 (Nat.zero_le k)).2.1
  have hEk := (hindex L hL k k le_rfl).2.1
  have hV₀ := (hindex L hL k 0 (Nat.zero_le k)).1
  have hVk := (hindex L hL k k le_rfl).1
  have hmaps := (hfree.2 L hL k hk).1
  have hQ := hmaps.edgeAverage.finite_range
  have hR := hmaps.vertexAverage.finite_range
  have hcontract := (hcontr L hL k hk).1.2
  have boundQ : ∀ z ∈ openImStrip (1 / 8),
      quotHomNorm (symbolHom (colourEdges L k 0) (colourEdges L k k)
        (trivialRescaledOperators L k).Q z) ≤ ENNReal.ofReal (Real.exp 1) := by
    intro z hz
    refine (quotHomNorm_symbolHom_le_expConj hshift hnorm hE₀ hEk hQ z).trans ?_
    refine ((hcontract (PeriodicOperators.imVec z)).2.1.2.2).trans ?_
    apply ENNReal.ofReal_le_ofReal
    apply Real.exp_le_exp.mpr
    linarith [l1NormVec_imVec_le hz]
  have boundR : ∀ z ∈ openImStrip (1 / 8),
      quotHomNorm (symbolHom (colourVertices L k 0) (colourVertices L k k)
        (trivialRescaledOperators L k).R z) ≤ ENNReal.ofReal (Real.exp 1) := by
    intro z hz
    refine (quotHomNorm_symbolHom_le_expConj hshift hnorm hV₀ hVk hR z).trans ?_
    refine ((hcontract (PeriodicOperators.imVec z)).2.2.2.2).trans ?_
    apply ENNReal.ofReal_le_ofReal
    apply Real.exp_le_exp.mpr
    linarith [l1NormVec_imVec_le hz]
  refine ⟨boundQ κ hκ, boundR κ hκ, ?_, ?_⟩
  · have e := quotHomNorm_symbolHom_kernelTranspose hstrip hquot hE₀ hEk hQ κ
    exact (le_of_eq e).trans (boundQ _ (neg_mem_openImStrip hκ))
  · have e := quotHomNorm_symbolHom_kernelTranspose hstrip hquot hV₀ hVk hR κ
    exact (le_of_eq e).trans (boundR _ (neg_mem_openImStrip hκ))
end YangMills.Construction.Tower.SymbolBounds
end
