import YangMills.Construction.Lattice.OneStepObjectsReadInTheChartProof
import YangMills.Construction.Lattice.BareBaseSitesOfTheSchemesProof
import YangMills.Construction.Lattice.CovarianceOfComplexContourVariablesProof
import YangMills.Construction.Lattice.PivotOfBond
import YangMills.Construction.Towers.DilationCarriesObjectsAtAStepOfASide
import YangMills.Construction.Towers.DilationCarriesObjectsAtAnIndexOfATower
import Mathlib
set_option autoImplicit false
open Set YangMills.Construction.Matrices
noncomputable section
namespace YangMills.Construction.Tower.ScalingPreservesStepsAtSide
section Reindexing
variable {ι ι' : Type*} [Fintype ι] [Fintype ι']
theorem isLogMean_congr_equiv (𝒢 : Set ComplexMatrix2) (e : ι ≃ ι') {V : ι → ComplexMatrix2}
    {V' : ι' → ComplexMatrix2} (h : ∀ a, V' (e a) = V a) (W : ComplexMatrix2) :
    ComplexMatrix2.IsLogMean 𝒢 V' W ↔ ComplexMatrix2.IsLogMean 𝒢 V W := by
  have h1 : (∀ a', ComplexMatrix2.operatorNorm (V' a' * W⁻¹ - 1) < 1) ↔
      ∀ a, ComplexMatrix2.operatorNorm (V a * W⁻¹ - 1) < 1 := by
    constructor
    · intro H a
      simpa [h] using H (e a)
    · intro H a'
      obtain ⟨a, rfl⟩ := e.surjective a'
      simpa [h] using H a
  have h2 : ∑ a', ComplexMatrix2.logSeries (V' a' * W⁻¹) =
      ∑ a, ComplexMatrix2.logSeries (V a * W⁻¹) := by
    rw [← e.sum_comp]
    simp only [h]
  unfold ComplexMatrix2.IsLogMean
  rw [h1, h2]
theorem hasUniqueLogMean_congr_equiv (𝒢 : Set ComplexMatrix2) (e : ι ≃ ι')
    {V : ι → ComplexMatrix2} {V' : ι' → ComplexMatrix2} (h : ∀ a, V' (e a) = V a) :
    ComplexMatrix2.HasUniqueLogMean 𝒢 V' ↔ ComplexMatrix2.HasUniqueLogMean 𝒢 V := by
  unfold ComplexMatrix2.HasUniqueLogMean
  simp only [isLogMean_congr_equiv 𝒢 e h]
theorem logMean_congr_equiv (𝒢 : Set ComplexMatrix2) (e : ι ≃ ι') {V : ι → ComplexMatrix2}
    {V' : ι' → ComplexMatrix2} (h : ∀ a, V' (e a) = V a) :
    ComplexMatrix2.logMean 𝒢 V' = ComplexMatrix2.logMean 𝒢 V := by
  have hp : ComplexMatrix2.IsLogMean 𝒢 V' = ComplexMatrix2.IsLogMean 𝒢 V :=
    funext fun W => propext (isLogMean_congr_equiv 𝒢 e h W)
  simp only [ComplexMatrix2.logMean, hp]
omit [Fintype ι] [Fintype ι'] in
theorem familyDiameter_congr_equiv (e : ι ≃ ι') {V : ι → ComplexMatrix2}
    {V' : ι' → ComplexMatrix2} (h : ∀ a, V' (e a) = V a) :
    ComplexMatrix2.familyDiameter V' = ComplexMatrix2.familyDiameter V := by
  unfold ComplexMatrix2.familyDiameter
  refine ((Equiv.prodCongr e e).iSup_congr fun p => ?_).symm
  simp [h]
theorem complexLogMean_congr_equiv (e : ι ≃ ι') {V : ι → ComplexMatrix2}
    {V' : ι' → ComplexMatrix2} (h : ∀ a, V' (e a) = V a) :
    PeriodicLattice.complexLogMean V' = PeriodicLattice.complexLogMean V := by apply _root_.YangMills.Construction.PeriodicLattice.ContourCovariance.complexLogMean_comp_equiv <;> assumption
end Reindexing
variable {L n k j i : ℕ}
theorem levelDepth_succ_le (K a : ℕ) :
    PeriodicLattice.levelDepth K (a + 1) ≤ PeriodicLattice.levelDepth K a := by
  simp only [PeriodicLattice.levelDepth]
  omega
theorem coe_toSublattice {m : ℕ} (hL : 0 < L) {d d' : ℤ} (h : d ≤ d')
    (y : PeriodicLattice.Site L m d) :
    ((PeriodicLattice.Site.toSublattice y d' : PeriodicLattice.Site L m d') :
      PeriodicLattice.FourTorus L m) = y := by apply _root_.YangMills.SharedProofs.p9023 <;> assumption
theorem scaleVertex_toSublattice (hL : 0 < L) (hj : j ≤ k) (y : Vertex L n k (i + 1)) :
    scaleVertex hL hj i (PeriodicLattice.Site.toSublattice y (PeriodicLattice.levelDepth k i)) =
      PeriodicLattice.Site.toSublattice (scaleVertex hL hj (i + 1) y)
        (PeriodicLattice.levelDepth j i) := by
  apply Subtype.ext
  rw [coe_scaleVertex, coe_toSublattice hL (levelDepth_succ_le k i),
    coe_toSublattice hL (levelDepth_succ_le j i), coe_scaleVertex]
theorem scaleEdge_source (hL : 0 < L) (hj : j ≤ k) (b : Edge L n k i) :
    (scaleEdge hL hj i b).source = scaleVertex hL hj i b.source := rfl
theorem scaleEdge_target (hL : 0 < L) (hj : j ≤ k) (b : Edge L n k i) :
    (scaleEdge hL hj i b).target = scaleVertex hL hj i b.target := rfl
theorem scaleEdge_opposite (hL : 0 < L) (hj : j ≤ k) (b : Edge L n k i) :
    scaleEdge hL hj i b.opposite = (scaleEdge hL hj i b).opposite :=
  PeriodicLattice.Bond.ext rfl rfl
theorem scaleEdge_forwardFrom (hL : 0 < L) (hj : j ≤ k) (x : Vertex L n k i) (μ : Fin 4) :
    scaleEdge hL hj i (PeriodicLattice.Bond.forwardFrom x μ) =
      PeriodicLattice.Bond.forwardFrom (scaleVertex hL hj i x) μ :=
  PeriodicLattice.Bond.ext rfl (by
    change scaleVertex hL hj i (x + PeriodicLattice.unitStep L n (PeriodicLattice.levelDepth k i) μ) = _
    rw [map_add, scaleVertex_unitStep]
    rfl)
theorem scaleEdge_backwardFrom (hL : 0 < L) (hj : j ≤ k) (x : Vertex L n k i) (μ : Fin 4) :
    scaleEdge hL hj i (PeriodicLattice.Bond.backwardFrom x μ) =
      PeriodicLattice.Bond.backwardFrom (scaleVertex hL hj i x) μ :=
  PeriodicLattice.Bond.ext rfl (by
    change scaleVertex hL hj i (x - PeriodicLattice.unitStep L n (PeriodicLattice.levelDepth k i) μ) = _
    rw [map_sub, scaleVertex_unitStep]
    rfl)
theorem isPositivelyOriented_scaleEdge (hL : 0 < L) (hj : j ≤ k) (b : Edge L n k i) :
    (scaleEdge hL hj i b).IsPositivelyOriented ↔ b.IsPositivelyOriented := by
  unfold PeriodicLattice.Bond.IsPositivelyOriented
  refine exists_congr fun μ => ?_
  rw [scaleEdge_source, scaleEdge_target, ← map_sub, ← scaleVertex_unitStep hL hj i μ]
  exact (scaleVertex hL hj i).injective.eq_iff
theorem map_forwardFlow (hL : 0 < L) (hj : j ≤ k) (x : Vertex L n k i) (μ : Fin 4) (a : ℕ) :
    (PeriodicLattice.forwardAxisPath x μ a).map (scaleEdge hL hj i) =
      PeriodicLattice.forwardAxisPath (scaleVertex hL hj i x) μ a := by
  induction a generalizing x with
  | zero => rfl
  | succ a ih =>
    simp only [PeriodicLattice.forwardAxisPath, List.map_cons, scaleEdge_forwardFrom, ih, map_add,
      scaleVertex_unitStep]
theorem map_backwardFlow (hL : 0 < L) (hj : j ≤ k) (x : Vertex L n k i) (μ : Fin 4) (a : ℕ) :
    (PeriodicLattice.backwardAxisPath x μ a).map (scaleEdge hL hj i) =
      PeriodicLattice.backwardAxisPath (scaleVertex hL hj i x) μ a := by
  induction a generalizing x with
  | zero => rfl
  | succ a ih =>
    simp only [PeriodicLattice.backwardAxisPath, List.map_cons, scaleEdge_backwardFrom, ih, map_sub,
      scaleVertex_unitStep]
theorem map_flowAlong (hL : 0 < L) (hj : j ≤ k) (x : Vertex L n k i) (μ : Fin 4) (a : ℤ) :
    (PeriodicLattice.flowAlong x μ a).map (scaleEdge hL hj i) =
      PeriodicLattice.flowAlong (scaleVertex hL hj i x) μ a := by
  unfold PeriodicLattice.flowAlong
  split_ifs
  · exact map_forwardFlow hL hj x μ _
  · exact map_backwardFlow hL hj x μ _
theorem map_stepsThroughAxes (hL : 0 < L) (hj : j ≤ k) (a : Fin 4 → ℤ) (x : Vertex L n k i)
    (l : List (Fin 4)) :
    (PeriodicLattice.stepsThroughAxes a x l).map (scaleEdge hL hj i) =
      PeriodicLattice.stepsThroughAxes a (scaleVertex hL hj i x) l := by
  induction l generalizing x with
  | nil => rfl
  | cons μ l ih =>
    simp only [PeriodicLattice.stepsThroughAxes, List.map_append, map_flowAlong, ih, map_add,
      map_zsmul, scaleVertex_unitStep]
theorem pathHolonomy_transportTotal (hL : 0 < L) (hj : j ≤ k) (U : Edge L n k i → ComplexMatrix2)
    (Γ : List (Edge L n k i)) :
    PeriodicLattice.pathHolonomy (transportTotal (scaleEdge hL hj i) U) (scalePath hL hj i Γ) =
      PeriodicLattice.pathHolonomy U Γ := by
  simp [PeriodicLattice.pathHolonomy, scalePath, transportList, Function.comp_def, transportTotal]
theorem bondFormSumAlong_transportTotal (hL : 0 < L) (hj : j ≤ k)
    (U : Edge L n k i → ComplexMatrix2) (Γ : List (Edge L n k i)) :
    PeriodicLattice.bondFormSumAlong (transportTotal (scaleEdge hL hj i) U)
        (scalePath hL hj i Γ) = PeriodicLattice.bondFormSumAlong U Γ := by
  simp [PeriodicLattice.bondFormSumAlong, scalePath, transportList, Function.comp_def,
    transportTotal]
theorem isBlockOffset_scaleVertex_iff (hL : 0 < L) (hj : j ≤ k) {i₁ i₂ : ℕ} (y : Vertex L n k i₁)
    (x : Vertex L n k i₂) (a : Fin 4 → ℤ) :
    PeriodicLattice.IsBlockOffset (scaleVertex hL hj i₁ y) (scaleVertex hL hj i₂ x) a ↔
      PeriodicLattice.IsBlockOffset y x a := by
  have key : scaling hL n k j (∑ μ, PeriodicLattice.pointOnAxis L n μ
        ((a μ : ℝ) * PeriodicLattice.meshSize L (PeriodicLattice.levelDepth k i₂))) =
      ∑ μ, PeriodicLattice.pointOnAxis L (scaledExponent n k j) μ
        ((a μ : ℝ) * PeriodicLattice.meshSize L (PeriodicLattice.levelDepth j i₂)) := by
    rw [map_sum]
    refine Finset.sum_congr rfl fun μ _ => ?_
    rw [scaling_pointOnAxis, ← pow_mul_meshSize_levelDepth hL hj i₂]
    congr 1
    ring
  have keyx : ((scaleVertex hL hj i₂ x : PeriodicLattice.FourTorus L (scaledExponent n k j)) -
        (scaleVertex hL hj i₁ y : PeriodicLattice.FourTorus L (scaledExponent n k j))) =
      scaling hL n k j ((x : PeriodicLattice.FourTorus L n) - (y : PeriodicLattice.FourTorus L n)) := by
    rw [coe_scaleVertex, coe_scaleVertex, map_sub]
  unfold PeriodicLattice.IsBlockOffset
  constructor
  · rintro ⟨h, hb⟩
    refine ⟨(scaling hL n k j).injective ?_, hb⟩
    rw [key, ← h, keyx]
  · rintro ⟨h, hb⟩
    refine ⟨?_, hb⟩
    rw [keyx, h, key]
theorem blockOffset_scaleVertex (hL : 0 < L) (hj : j ≤ k) {i₁ i₂ : ℕ} (y : Vertex L n k i₁)
    (x : Vertex L n k i₂) :
    PeriodicLattice.blockOffset (scaleVertex hL hj i₁ y) (scaleVertex hL hj i₂ x) =
      PeriodicLattice.blockOffset y x := by
  have hp : PeriodicLattice.IsBlockOffset (scaleVertex hL hj i₁ y)
      (scaleVertex hL hj i₂ x) = PeriodicLattice.IsBlockOffset y x :=
    funext fun a => propext (isBlockOffset_scaleVertex_iff hL hj y x a)
  simp only [PeriodicLattice.blockOffset, hp]
theorem offsetAxes_scaleVertex (hL : 0 < L) (hj : j ≤ k) {i₁ i₂ : ℕ} (y : Vertex L n k i₁)
    (x : Vertex L n k i₂) :
    PeriodicLattice.offsetAxes (scaleVertex hL hj i₁ y) (scaleVertex hL hj i₂ x) =
      PeriodicLattice.offsetAxes y x := by
  simp only [PeriodicLattice.offsetAxes, blockOffset_scaleVertex]
def axisList (S : Finset (Fin 4)) (σ : Fin S.card ≃ S) : List (Fin 4) :=
  (List.finRange _).map fun a => ((σ a : S) : Fin 4)
theorem exists_axisList_equiv {S S' : Finset (Fin 4)} (h : S = S') :
    ∃ e : (Fin S.card ≃ S) ≃ (Fin S'.card ≃ S'),
      ∀ σ, axisList S' (e σ) = axisList S σ := by apply _root_.YangMills.Construction.PeriodicLattice.ChartInvariance.exists_ordering_equiv <;> assumption
theorem exists_axisOrdering_equiv (hL : 0 < L) (hj : j ≤ k) (y : Vertex L n k (i + 1))
    (x : Vertex L n k i) (y' : Vertex L (scaledExponent n k j) j (i + 1))
    (x' : Vertex L (scaledExponent n k j) j i) (hy : y' = scaleVertex hL hj (i + 1) y)
    (hx : x' = scaleVertex hL hj i x) :
    ∃ e : PeriodicLattice.AxisOrdering y x ≃ PeriodicLattice.AxisOrdering y' x',
      ∀ σ, PeriodicLattice.orderedContour y' x' (e σ) =
        scalePath hL hj i (PeriodicLattice.orderedContour y x σ) := by
  subst hy hx
  obtain ⟨e, he⟩ := exists_axisList_equiv (offsetAxes_scaleVertex hL hj y x).symm
  refine ⟨e, fun σ => ?_⟩
  change PeriodicLattice.stepsThroughAxes _ _ (axisList _ (e σ)) =
    (PeriodicLattice.stepsThroughAxes _ _ (axisList _ σ)).map _
  rw [he, blockOffset_scaleVertex, map_stepsThroughAxes, scaleVertex_toSublattice]
theorem exists_contourHolonomies_equiv (hL : 0 < L) (hj : j ≤ k)
    (U : Edge L n k i → ComplexMatrix2) (y : Vertex L n k (i + 1)) (x : Vertex L n k i) :
    ∃ e : PeriodicLattice.AxisOrdering y x ≃ PeriodicLattice.AxisOrdering
        (scaleVertex hL hj (i + 1) y) (scaleVertex hL hj i x),
      ∀ σ, PeriodicLattice.contourHolonomies (transportTotal (scaleEdge hL hj i) U)
          (scaleVertex hL hj (i + 1) y) (scaleVertex hL hj i x) (e σ) =
        PeriodicLattice.contourHolonomies U y x σ := by
  obtain ⟨e, he⟩ := exists_axisOrdering_equiv hL hj y x _ _ rfl rfl
  refine ⟨e, fun σ => ?_⟩
  simp only [PeriodicLattice.contourHolonomies, he, pathHolonomy_transportTotal]
theorem hasContourMean_scale_iff (hL : 0 < L) (hj : j ≤ k) (U : Edge L n k i → ComplexMatrix2)
    (y : Vertex L n k (i + 1)) (x : Vertex L n k i) :
    PeriodicLattice.HasContourMean (transportTotal (scaleEdge hL hj i) U)
        (scaleVertex hL hj (i + 1) y) (scaleVertex hL hj i x) ↔
      PeriodicLattice.HasContourMean U y x := by
  obtain ⟨e, he⟩ := exists_contourHolonomies_equiv hL hj U y x
  exact hasUniqueLogMean_congr_equiv _ e he
theorem meanContourHolonomy_scale (hL : 0 < L) (hj : j ≤ k) (U : Edge L n k i → ComplexMatrix2)
    (y : Vertex L n k (i + 1)) (x : Vertex L n k i) :
    PeriodicLattice.meanContourHolonomy (transportTotal (scaleEdge hL hj i) U)
        (scaleVertex hL hj (i + 1) y) (scaleVertex hL hj i x) =
      PeriodicLattice.meanContourHolonomy U y x := by
  obtain ⟨e, he⟩ := exists_contourHolonomies_equiv hL hj U y x
  exact logMean_congr_equiv _ e he
theorem complexMeanContourHolonomy_scale (hL : 0 < L) (hj : j ≤ k)
    (U : Edge L n k i → ComplexMatrix2) (y : Vertex L n k (i + 1)) (x : Vertex L n k i) :
    PeriodicLattice.complexMeanContourHolonomy (transportTotal (scaleEdge hL hj i) U)
        (scaleVertex hL hj (i + 1) y) (scaleVertex hL hj i x) =
      PeriodicLattice.complexMeanContourHolonomy U y x := by
  obtain ⟨e, he⟩ := exists_contourHolonomies_equiv hL hj U y x
  exact complexLogMean_congr_equiv e he
theorem familyDiameter_contourHolonomies_scale (hL : 0 < L) (hj : j ≤ k)
    (U : Edge L n k i → ComplexMatrix2) (y : Vertex L n k (i + 1)) (x : Vertex L n k i) :
    ComplexMatrix2.familyDiameter (PeriodicLattice.contourHolonomies
        (transportTotal (scaleEdge hL hj i) U)
        (scaleVertex hL hj (i + 1) y) (scaleVertex hL hj i x)) =
      ComplexMatrix2.familyDiameter (PeriodicLattice.contourHolonomies U y x) := by
  obtain ⟨e, he⟩ := exists_contourHolonomies_equiv hL hj U y x
  exact familyDiameter_congr_equiv e he
theorem contourFormAverage_scale (hL : 0 < L) (hj : j ≤ k) (B : Edge L n k i → ComplexMatrix2)
    (y : Vertex L n k (i + 1)) (x : Vertex L n k i) :
    PeriodicLattice.contourFormAverage (transportTotal (scaleEdge hL hj i) B)
        (scaleVertex hL hj (i + 1) y) (scaleVertex hL hj i x) =
      PeriodicLattice.contourFormAverage B y x := by
  obtain ⟨e, he⟩ := exists_axisOrdering_equiv hL hj y x _ _ rfl rfl
  unfold PeriodicLattice.contourFormAverage
  rw [Fintype.card_congr e.symm, ← e.sum_comp]
  simp only [he, bondFormSumAlong_transportTotal]
theorem scaling_mem_unitBlock_iff (hL : 0 < L) (hj : j ≤ k)
    (hb : ScalingPreservesAtLevel hL hj n (i + 1)) (y : Vertex L n k (i + 1))
    (p : PeriodicLattice.FourTorus L n) :
    scaling hL n k j p ∈ PeriodicLattice.unitBlock (scaleVertex hL hj (i + 1) y) ↔
      p ∈ PeriodicLattice.unitBlock y := by
  change scaling hL n k j p ∈ PeriodicLattice.refinedBlock 1 (scaleVertex hL hj (i + 1) y) ↔
    p ∈ PeriodicLattice.refinedBlock 1 y
  rw [← hb.refinedBlock_image 1 (by omega) y]
  exact (scaling hL n k j).injective.mem_set_image
theorem scaleVertex_mem_sitesInBlock_iff (hL : 0 < L) (hj : j ≤ k)
    (hb : ScalingPreservesAtLevel hL hj n (i + 1)) (y : Vertex L n k (i + 1))
    (x : Vertex L n k i) :
    scaleVertex hL hj i x ∈
        PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth j i) (scaleVertex hL hj (i + 1) y) ↔
      x ∈ PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k i) y :=
  scaling_mem_unitBlock_iff hL hj hb y x
theorem sitesInBlock_scaleVertex (hL : 0 < L) (hj : j ≤ k)
    (hb : ScalingPreservesAtLevel hL hj n (i + 1)) (y : Vertex L n k (i + 1)) :
    PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth j i) (scaleVertex hL hj (i + 1) y) =
      scaleVertex hL hj i '' PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k i) y := by
  ext x'
  obtain ⟨x, rfl⟩ := (scaleVertex hL hj i).surjective x'
  rw [(scaleVertex hL hj i).injective.mem_set_image]
  exact scaleVertex_mem_sitesInBlock_iff hL hj hb y x
theorem image_bondDoubleBlock (hL : 0 < L) (hj : j ≤ k)
    (hb : ScalingPreservesAtLevel hL hj n (i + 1)) (c : Edge L n k (i + 1)) :
    scaling hL n k j '' PeriodicLattice.bondDoubleBlock c =
      PeriodicLattice.bondDoubleBlock (scaleEdge hL hj (i + 1) c) := by
  unfold PeriodicLattice.bondDoubleBlock
  rw [image_union, hb.refinedBlock_image 1 (by omega), hb.refinedBlock_image 1 (by omega)]
  rfl
theorem scaling_mem_bondDoubleBlock_iff (hL : 0 < L) (hj : j ≤ k)
    (hb : ScalingPreservesAtLevel hL hj n (i + 1)) (c : Edge L n k (i + 1))
    (p : PeriodicLattice.FourTorus L n) :
    scaling hL n k j p ∈ PeriodicLattice.bondDoubleBlock (scaleEdge hL hj (i + 1) c) ↔
      p ∈ PeriodicLattice.bondDoubleBlock c := by
  rw [← image_bondDoubleBlock hL hj hb c]
  exact (scaling hL n k j).injective.mem_set_image
theorem vertices_scaleFace (hL : 0 < L) (hj : j ≤ k) (p : Face L n k i) :
    (scaleFace hL hj i p).vertices = scaleVertex hL hj i '' p.vertices := by
  have hb : (scaleFace hL hj i p).origin = scaleVertex hL hj i p.origin := rfl
  have h1 : (scaleFace hL hj i p).firstAxis = p.firstAxis := rfl
  have h2 : (scaleFace hL hj i p).secondAxis = p.secondAxis := rfl
  simp only [PeriodicLattice.Plaquette.vertices, image_insert_eq, image_singleton, map_add,
    scaleVertex_unitStep, hb, h1, h2]
theorem image_doubleBlockPlaquettes (hL : 0 < L) (hj : j ≤ k)
    (hb : ScalingPreservesAtLevel hL hj n (i + 1)) (c : Edge L n k (i + 1)) :
    scaleFace hL hj i ''
        (PeriodicLattice.doubleBlockPlaquettes c : Set (Face L n k i)) =
      PeriodicLattice.doubleBlockPlaquettes (scaleEdge hL hj (i + 1) c) := by
  ext p'
  obtain ⟨p, rfl⟩ := (scaleFace hL hj i).surjective p'
  rw [(scaleFace hL hj i).injective.mem_set_image]
  simp only [PeriodicLattice.doubleBlockPlaquettes, PeriodicLattice.plaquettesInside, mem_ofPred_eq,
    vertices_scaleFace, forall_mem_image]
  exact forall₂_congr fun x _ => (scaling_mem_bondDoubleBlock_iff hL hj hb c x).symm
theorem image_bondCorridor (hL : 0 < L) (hj : j ≤ k)
    (hb : ScalingPreservesAtLevel hL hj n (i + 1)) (c : Edge L n k (i + 1)) :
    scaleEdge hL hj i '' (PeriodicLattice.bondCorridor c : Set (Edge L n k i)) =
      PeriodicLattice.bondCorridor (scaleEdge hL hj (i + 1) c) := by
  ext b'
  obtain ⟨b, rfl⟩ := (scaleEdge hL hj i).surjective b'
  rw [(scaleEdge hL hj i).injective.mem_set_image]
  exact and_congr (scaling_mem_unitBlock_iff hL hj hb c.source b.source).symm
    (scaling_mem_unitBlock_iff hL hj hb c.target b.target).symm
theorem image_bondsInDoubleBlock (hL : 0 < L) (hj : j ≤ k)
    (hb : ScalingPreservesAtLevel hL hj n (i + 1)) (c : Edge L n k (i + 1)) :
    scaleEdge hL hj i '' (PeriodicLattice.bondsInDoubleBlock c : Set (Edge L n k i)) =
      PeriodicLattice.bondsInDoubleBlock (scaleEdge hL hj (i + 1) c) := by
  ext b'
  obtain ⟨b, rfl⟩ := (scaleEdge hL hj i).surjective b'
  rw [(scaleEdge hL hj i).injective.mem_set_image]
  exact and_congr (scaling_mem_bondDoubleBlock_iff hL hj hb c b.source).symm
    (scaling_mem_bondDoubleBlock_iff hL hj hb c b.target).symm
theorem scalePath_axialPath (hL : 0 < L) (hj : j ≤ k) (hs : ScalingPreservesAtLevel hL hj n i)
    (x x' : Vertex L n k i) :
    scalePath hL hj i (PeriodicLattice.axialPath x x') =
      PeriodicLattice.axialPath (scaleVertex hL hj i x) (scaleVertex hL hj i x') := by
  by_cases h : ∃ q : Fin 4 × ℤ, PeriodicLattice.IsAxialDisplacement x x' q.1 q.2
  · obtain ⟨q, hq⟩ := h
    exact hs.axialPath_image x x' q.1 q.2 hq
  · have h' : ¬∃ q : Fin 4 × ℤ, PeriodicLattice.IsAxialDisplacement (scaleVertex hL hj i x)
        (scaleVertex hL hj i x') q.1 q.2 := fun ⟨q, hq⟩ =>
      h ⟨q, (hs.isAxialDisplacement_iff x x' q.1 q.2).2 hq⟩
    simp only [PeriodicLattice.axialPath, dif_neg h, dif_neg h']
    rfl
theorem scaleVertex_shiftAcross (hL : 0 < L) (hj : j ≤ k) (c : Edge L n k (i + 1))
    (x : Vertex L n k i) :
    scaleVertex hL hj i (PeriodicLattice.shiftAcross c x) =
      PeriodicLattice.shiftAcross (scaleEdge hL hj (i + 1) c) (scaleVertex hL hj i x) := by
  unfold PeriodicLattice.shiftAcross
  rw [map_add, scaleVertex_toSublattice, map_sub]
  rfl
theorem scalePath_crossingPath (hL : 0 < L) (hj : j ≤ k) (hs : ScalingPreservesAtLevel hL hj n i)
    (c : Edge L n k (i + 1)) (x : Vertex L n k i) :
    scalePath hL hj i (PeriodicLattice.crossingPath c x) =
      PeriodicLattice.crossingPath (scaleEdge hL hj (i + 1) c) (scaleVertex hL hj i x) := by
  unfold PeriodicLattice.crossingPath
  rw [scalePath_axialPath hL hj hs, scaleVertex_shiftAcross]
theorem scalePath_axialPath_ends (hL : 0 < L) (hj : j ≤ k)
    (hs : ScalingPreservesAtLevel hL hj n i) (c : Edge L n k (i + 1)) :
    scalePath hL hj i (PeriodicLattice.axialPath
        (PeriodicLattice.Site.toSublattice c.source (PeriodicLattice.levelDepth k i))
        (PeriodicLattice.Site.toSublattice c.target (PeriodicLattice.levelDepth k i))) =
      PeriodicLattice.axialPath
        (PeriodicLattice.Site.toSublattice (scaleEdge hL hj (i + 1) c).source
          (PeriodicLattice.levelDepth j i))
        (PeriodicLattice.Site.toSublattice (scaleEdge hL hj (i + 1) c).target
          (PeriodicLattice.levelDepth j i)) := by
  rw [scalePath_axialPath hL hj hs, scaleVertex_toSublattice, scaleVertex_toSublattice]
  rfl
theorem parallelTransport_scale (hL : 0 < L) (hj : j ≤ k) (hs : ScalingPreservesAtLevel hL hj n i)
    (U : Edge L n k i → ComplexMatrix2) (c : Edge L n k (i + 1)) :
    PeriodicLattice.parallelTransport (transportTotal (scaleEdge hL hj i) U)
        (scaleEdge hL hj (i + 1) c) = PeriodicLattice.parallelTransport U c := by
  unfold PeriodicLattice.parallelTransport
  rw [← scalePath_axialPath_ends hL hj hs, pathHolonomy_transportTotal]
theorem pathHolonomy_crossingPath_scale (hL : 0 < L) (hj : j ≤ k)
    (hs : ScalingPreservesAtLevel hL hj n i) (U : Edge L n k i → ComplexMatrix2)
    (c : Edge L n k (i + 1)) (x : Vertex L n k i) :
    PeriodicLattice.pathHolonomy (transportTotal (scaleEdge hL hj i) U)
        (PeriodicLattice.crossingPath (scaleEdge hL hj (i + 1) c) (scaleVertex hL hj i x)) =
      PeriodicLattice.pathHolonomy U (PeriodicLattice.crossingPath c x) := by
  rw [← scalePath_crossingPath hL hj hs, pathHolonomy_transportTotal]
theorem bondFormSumAlong_crossingPath_scale (hL : 0 < L) (hj : j ≤ k)
    (hs : ScalingPreservesAtLevel hL hj n i) (U : Edge L n k i → ComplexMatrix2)
    (c : Edge L n k (i + 1)) (x : Vertex L n k i) :
    PeriodicLattice.bondFormSumAlong (transportTotal (scaleEdge hL hj i) U)
        (PeriodicLattice.crossingPath (scaleEdge hL hj (i + 1) c) (scaleVertex hL hj i x)) =
      PeriodicLattice.bondFormSumAlong U (PeriodicLattice.crossingPath c x) := by
  rw [← scalePath_crossingPath hL hj hs, bondFormSumAlong_transportTotal]
theorem scaleEdge_pivot (hL : 0 < L) (hj : j ≤ k)
    (hb : ScalingPreservesAtLevel hL hj n (i + 1)) (hs : ScalingPreservesAtLevel hL hj n i)
    (h₁ : ∀ c : Edge L n k (i + 1), PeriodicLattice.PivotProperties c)
    (h₂ : ∀ c : Edge L (scaledExponent n k j) j (i + 1), PeriodicLattice.PivotProperties c)
    (c : Edge L n k (i + 1)) :
    scaleEdge hL hj i (PeriodicLattice.pivot c) =
      PeriodicLattice.pivot (scaleEdge hL hj (i + 1) c) := by
  obtain ⟨hc, hp⟩ := (h₁ c).isPivot
  obtain ⟨hc', hp'⟩ := (h₂ (scaleEdge hL hj (i + 1) c)).isPivot
  refine (h₂ (scaleEdge hL hj (i + 1) c)).existsUnique_onAxialPath.unique ⟨?_, ?_⟩ ⟨hp', hc'⟩
  · rw [← scalePath_axialPath_ends hL hj hs]
    exact List.mem_map.2 ⟨_, hp, rfl⟩
  · rw [← image_bondCorridor hL hj hb]
    exact mem_image_of_mem _ hc
theorem isGaugeField_image_iff (hL : 0 < L) (hj : j ≤ k) (𝒢 : Set ComplexMatrix2)
    (S : Set (Edge L n k i)) (U : Edge L n k i → ComplexMatrix2) :
    PeriodicLattice.IsGaugeField 𝒢 (scaleEdge hL hj i '' S)
        (transportTotal (scaleEdge hL hj i) U) ↔ PeriodicLattice.IsGaugeField 𝒢 S U := by
  unfold PeriodicLattice.IsGaugeField
  simp only [forall_mem_image, ← scaleEdge_opposite, transportTotal_apply]
theorem scalePath_boundaryBonds (hL : 0 < L) (hj : j ≤ k) (p : Face L n k i) :
    scalePath hL hj i p.boundaryBonds = (scaleFace hL hj i p).boundaryBonds := by
  have hb : (scaleFace hL hj i p).origin = scaleVertex hL hj i p.origin := rfl
  have h1 : (scaleFace hL hj i p).firstAxis = p.firstAxis := rfl
  have h2 : (scaleFace hL hj i p).secondAxis = p.secondAxis := rfl
  simp only [scalePath, transportList, PeriodicLattice.Plaquette.boundaryBonds, List.map_cons,
    List.map_nil, scaleEdge_opposite, scaleEdge_forwardFrom, map_add, scaleVertex_unitStep, hb,
    h1, h2]
theorem plaquetteHolonomy_scale (hL : 0 < L) (hj : j ≤ k) (U : Edge L n k i → ComplexMatrix2)
    (p : Face L n k i) :
    PeriodicLattice.plaquetteHolonomy (transportTotal (scaleEdge hL hj i) U)
        (scaleFace hL hj i p) = PeriodicLattice.plaquetteHolonomy U p := by
  unfold PeriodicLattice.plaquetteHolonomy
  rw [← scalePath_boundaryBonds, pathHolonomy_transportTotal]
theorem complexCrossingDefect_scale (hL : 0 < L) (hj : j ≤ k)
    (hs : ScalingPreservesAtLevel hL hj n i) (U : Edge L n k i → ComplexMatrix2)
    (c : Edge L n k (i + 1)) (x : Vertex L n k i) :
    PeriodicLattice.complexCrossingDefect (transportTotal (scaleEdge hL hj i) U)
        (scaleEdge hL hj (i + 1) c) (scaleVertex hL hj i x) =
      PeriodicLattice.complexCrossingDefect U c x := by
  unfold PeriodicLattice.complexCrossingDefect
  have a₁ : PeriodicLattice.complexMeanContourHolonomy (transportTotal (scaleEdge hL hj i) U)
      (scaleEdge hL hj (i + 1) c).source (scaleVertex hL hj i x) =
      PeriodicLattice.complexMeanContourHolonomy U c.source x :=
    complexMeanContourHolonomy_scale hL hj U c.source x
  have a₂ : PeriodicLattice.complexMeanContourHolonomy (transportTotal (scaleEdge hL hj i) U)
      (scaleEdge hL hj (i + 1) c).target
        (scaleVertex hL hj i (PeriodicLattice.shiftAcross c x)) =
      PeriodicLattice.complexMeanContourHolonomy U c.target (PeriodicLattice.shiftAcross c x) :=
    complexMeanContourHolonomy_scale hL hj U c.target _
  rw [pathHolonomy_crossingPath_scale hL hj hs, parallelTransport_scale hL hj hs,
    ← scaleVertex_shiftAcross, a₁, a₂]
theorem crossingDefect_scale (hL : 0 < L) (hj : j ≤ k)
    (hs : ScalingPreservesAtLevel hL hj n i) (U : Edge L n k i → ComplexMatrix2)
    (c : Edge L n k (i + 1)) (x : Vertex L n k i) :
    PeriodicLattice.crossingDefect (transportTotal (scaleEdge hL hj i) U)
        (scaleEdge hL hj (i + 1) c) (scaleVertex hL hj i x) =
      PeriodicLattice.crossingDefect U c x := by
  unfold PeriodicLattice.crossingDefect
  have a₁ : PeriodicLattice.meanContourHolonomy (transportTotal (scaleEdge hL hj i) U)
      (scaleEdge hL hj (i + 1) c).source (scaleVertex hL hj i x) =
      PeriodicLattice.meanContourHolonomy U c.source x := meanContourHolonomy_scale hL hj U c.source x
  have a₂ : PeriodicLattice.meanContourHolonomy (transportTotal (scaleEdge hL hj i) U)
      (scaleEdge hL hj (i + 1) c).target
        (scaleVertex hL hj i (PeriodicLattice.shiftAcross c x)) =
      PeriodicLattice.meanContourHolonomy U c.target (PeriodicLattice.shiftAcross c x) :=
    meanContourHolonomy_scale hL hj U c.target _
  rw [pathHolonomy_crossingPath_scale hL hj hs, parallelTransport_scale hL hj hs,
    ← scaleVertex_shiftAcross, a₁, a₂]
theorem mem_complexAveragingDomainNearOne_iff (hL : 0 < L) (hj : j ≤ k)
    (hb : ScalingPreservesAtLevel hL hj n (i + 1)) (hs : ScalingPreservesAtLevel hL hj n i)
    (c : Edge L n k (i + 1)) (U : Edge L n k i → ComplexMatrix2) :
    U ∈ PeriodicLattice.complexAveragingDomainNearOne c ↔
      transportTotal (scaleEdge hL hj i) U ∈
        PeriodicLattice.complexAveragingDomainNearOne (scaleEdge hL hj (i + 1) c) := by
  have ht : PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth j i)
      (scaleEdge hL hj (i + 1) c).source =
      scaleVertex hL hj i '' PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k i) c.source :=
    sitesInBlock_scaleVertex hL hj hb c.source
  have hh : PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth j i)
      (scaleEdge hL hj (i + 1) c).target =
      scaleVertex hL hj i '' PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k i) c.target :=
    sitesInBlock_scaleVertex hL hj hb c.target
  have hd : ∀ (y : Vertex L n k (i + 1)) (x : Vertex L n k i),
      ComplexMatrix2.familyDiameter (PeriodicLattice.contourHolonomies
        (transportTotal (scaleEdge hL hj i) U)
        (scaleVertex hL hj (i + 1) y) (scaleVertex hL hj i x)) =
      ComplexMatrix2.familyDiameter (PeriodicLattice.contourHolonomies U y x) :=
    familyDiameter_contourHolonomies_scale hL hj U
  simp only [PeriodicLattice.complexAveragingDomainNearOne, PeriodicLattice.complexAveragingDomain,
    mem_ofPred_eq]
  rw [← image_bondsInDoubleBlock hL hj hb, isGaugeField_image_iff, ht, hh]
  simp only [forall_mem_image, complexCrossingDefect_scale hL hj hs]
  have d₁ : ∀ x : Vertex L n k i,
      ComplexMatrix2.familyDiameter (PeriodicLattice.contourHolonomies
        (transportTotal (scaleEdge hL hj i) U)
        (scaleEdge hL hj (i + 1) c).source (scaleVertex hL hj i x)) =
      ComplexMatrix2.familyDiameter (PeriodicLattice.contourHolonomies U c.source x) :=
    fun x => hd c.source x
  have d₂ : ∀ x : Vertex L n k i,
      ComplexMatrix2.familyDiameter (PeriodicLattice.contourHolonomies
        (transportTotal (scaleEdge hL hj i) U)
        (scaleEdge hL hj (i + 1) c).target (scaleVertex hL hj i x)) =
      ComplexMatrix2.familyDiameter (PeriodicLattice.contourHolonomies U c.target x) :=
    fun x => hd c.target x
  simp only [d₁, d₂]
theorem linearSmoothing_scale (hL : 0 < L) (hj : j ≤ k)
    (hb : ScalingPreservesAtLevel hL hj n (i + 1)) (hs : ScalingPreservesAtLevel hL hj n i)
    (B : Edge L n k i → ComplexMatrix2) :
    transportTotal (scaleEdge hL hj (i + 1)) (PeriodicLattice.scaledLinearBlockStep i B) =
      linearSmoothing L (scaledExponent n k j) j i (transportTotal (scaleEdge hL hj i) B) := by
  funext c'
  obtain ⟨c, rfl⟩ := (scaleEdge hL hj (i + 1)).surjective c'
  rw [transportTotal_apply]
  change PeriodicLattice.inverseFourthPowerWeight L • PeriodicLattice.linearBlockSum B c =
    PeriodicLattice.inverseFourthPowerWeight L • PeriodicLattice.linearBlockSum
      (transportTotal (scaleEdge hL hj i) B) (scaleEdge hL hj (i + 1) c)
  congr 1
  have ht : PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth j i)
      (scaleEdge hL hj (i + 1) c).source =
      scaleVertex hL hj i '' PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k i) c.source :=
    sitesInBlock_scaleVertex hL hj hb c.source
  unfold PeriodicLattice.linearBlockSum
  rw [ht, finsum_mem_image (scaleVertex hL hj i).injective.injOn]
  refine finsum_congr fun x => finsum_congr fun _ => ?_
  have a₁ : PeriodicLattice.contourFormAverage (transportTotal (scaleEdge hL hj i) B)
      (scaleEdge hL hj (i + 1) c).source (scaleVertex hL hj i x) =
      PeriodicLattice.contourFormAverage B c.source x := contourFormAverage_scale hL hj B c.source x
  have a₂ : PeriodicLattice.contourFormAverage (transportTotal (scaleEdge hL hj i) B)
      (scaleEdge hL hj (i + 1) c).target
        (scaleVertex hL hj i (PeriodicLattice.shiftAcross c x)) =
      PeriodicLattice.contourFormAverage B c.target (PeriodicLattice.shiftAcross c x) :=
    contourFormAverage_scale hL hj B c.target _
  rw [bondFormSumAlong_crossingPath_scale hL hj hs, ← scaleVertex_shiftAcross, a₁, a₂]
theorem image_contourSet (hL : 0 < L) (hj : j ≤ k) (y : Vertex L n k (i + 1))
    (x : Vertex L n k i) :
    scalePath hL hj i '' PeriodicLattice.contourSet y x =
      PeriodicLattice.contourSet (scaleVertex hL hj (i + 1) y) (scaleVertex hL hj i x) := by
  obtain ⟨e, he⟩ := exists_axisOrdering_equiv hL hj y x _ _ rfl rfl
  ext Γ
  constructor
  · rintro ⟨_, ⟨σ, rfl⟩, rfl⟩
    exact ⟨e σ, he σ⟩
  · rintro ⟨σ', rfl⟩
    obtain ⟨σ, rfl⟩ := e.surjective σ'
    exact ⟨_, ⟨σ, rfl⟩, (he σ).symm⟩
theorem sitesInBlock_source (hL : 0 < L) (hj : j ≤ k)
    (hb : ScalingPreservesAtLevel hL hj n (i + 1)) (c : Edge L n k (i + 1)) :
    PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth j i) (scaleEdge hL hj (i + 1) c).source =
      scaleVertex hL hj i '' PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k i) c.source :=
  sitesInBlock_scaleVertex hL hj hb c.source
theorem sitesInBlock_target (hL : 0 < L) (hj : j ≤ k)
    (hb : ScalingPreservesAtLevel hL hj n (i + 1)) (c : Edge L n k (i + 1)) :
    PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth j i) (scaleEdge hL hj (i + 1) c).target =
      scaleVertex hL hj i '' PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k i) c.target :=
  sitesInBlock_scaleVertex hL hj hb c.target
theorem doubleBlockPlaquettesNear_scale_iff (hL : 0 < L) (hj : j ≤ k)
    (hb : ScalingPreservesAtLevel hL hj n (i + 1)) (ω : ℝ) (c : Edge L n k (i + 1))
    (U : Edge L n k i → ComplexMatrix2) :
    PeriodicLattice.DoubleBlockPlaquettesNear ω (scaleEdge hL hj (i + 1) c)
        (transportTotal (scaleEdge hL hj i) U) ↔
      PeriodicLattice.DoubleBlockPlaquettesNear ω c U := by
  unfold PeriodicLattice.DoubleBlockPlaquettesNear
  rw [← image_doubleBlockPlaquettes hL hj hb c]
  simp only [forall_mem_image, plaquetteHolonomy_scale]
theorem isRegularAveragingCase_scale_iff (hL : 0 < L) (hj : j ≤ k)
    (hb : ScalingPreservesAtLevel hL hj n (i + 1)) (hs : ScalingPreservesAtLevel hL hj n i)
    (ω : ℝ) (c : Edge L n k (i + 1)) (U : Edge L n k i → ComplexMatrix2) :
    PeriodicLattice.IsRegularAveragingCase ω (transportTotal (scaleEdge hL hj i) U)
        (scaleEdge hL hj (i + 1) c) ↔ PeriodicLattice.IsRegularAveragingCase ω U c := by
  have h₁ : ∀ x : Vertex L n k i,
      PeriodicLattice.HasContourMean (transportTotal (scaleEdge hL hj i) U)
        (scaleEdge hL hj (i + 1) c).source (scaleVertex hL hj i x) ↔
      PeriodicLattice.HasContourMean U c.source x :=
    fun x => hasContourMean_scale_iff hL hj U c.source x
  have h₂ : ∀ x : Vertex L n k i,
      PeriodicLattice.HasContourMean (transportTotal (scaleEdge hL hj i) U)
        (scaleEdge hL hj (i + 1) c).target (scaleVertex hL hj i x) ↔
      PeriodicLattice.HasContourMean U c.target x :=
    fun x => hasContourMean_scale_iff hL hj U c.target x
  unfold PeriodicLattice.IsRegularAveragingCase
  rw [doubleBlockPlaquettesNear_scale_iff hL hj hb, sitesInBlock_source hL hj hb,
    sitesInBlock_target hL hj hb]
  simp only [forall_mem_image, crossingDefect_scale hL hj hs, h₁, h₂]
theorem regularAverageValue_scale (hL : 0 < L) (hj : j ≤ k)
    (hb : ScalingPreservesAtLevel hL hj n (i + 1)) (hs : ScalingPreservesAtLevel hL hj n i)
    (c : Edge L n k (i + 1)) (U : Edge L n k i → ComplexMatrix2) :
    PeriodicLattice.regularAverageValue (transportTotal (scaleEdge hL hj i) U)
        (scaleEdge hL hj (i + 1) c) = PeriodicLattice.regularAverageValue U c := by
  unfold PeriodicLattice.regularAverageValue
  rw [sitesInBlock_source hL hj hb, finsum_mem_image (scaleVertex hL hj i).injective.injOn,
    parallelTransport_scale hL hj hs]
  simp only [crossingDefect_scale hL hj hs]
theorem exists_contourCrossingDefect_equiv (hL : 0 < L) (hj : j ≤ k)
    (hs : ScalingPreservesAtLevel hL hj n i) (c : Edge L n k (i + 1))
    (U : Edge L n k i → ComplexMatrix2) (x : Vertex L n k i) :
    ∃ (e : PeriodicLattice.AxisOrdering c.source x ≃ PeriodicLattice.AxisOrdering
        (scaleEdge hL hj (i + 1) c).source (scaleVertex hL hj i x))
      (e' : PeriodicLattice.AxisOrdering c.target (PeriodicLattice.shiftAcross c x) ≃
        PeriodicLattice.AxisOrdering (scaleEdge hL hj (i + 1) c).target
          (PeriodicLattice.shiftAcross (scaleEdge hL hj (i + 1) c) (scaleVertex hL hj i x))),
      ∀ σ σ', PeriodicLattice.contourCrossingDefect (transportTotal (scaleEdge hL hj i) U)
          (scaleEdge hL hj (i + 1) c) (scaleVertex hL hj i x) (e σ) (e' σ') =
        PeriodicLattice.contourCrossingDefect U c x σ σ' := by
  obtain ⟨e, he⟩ := exists_axisOrdering_equiv hL hj c.source x
    (scaleEdge hL hj (i + 1) c).source (scaleVertex hL hj i x) rfl rfl
  obtain ⟨e', he'⟩ := exists_axisOrdering_equiv hL hj c.target (PeriodicLattice.shiftAcross c x)
    (scaleEdge hL hj (i + 1) c).target
    (PeriodicLattice.shiftAcross (scaleEdge hL hj (i + 1) c) (scaleVertex hL hj i x)) rfl
    (scaleVertex_shiftAcross hL hj c x).symm
  refine ⟨e, e', fun σ σ' => ?_⟩
  simp only [PeriodicLattice.contourCrossingDefect, he, he', pathHolonomy_transportTotal,
    pathHolonomy_crossingPath_scale hL hj hs, parallelTransport_scale hL hj hs]
theorem logAverageValue_scale (hL : 0 < L) (hj : j ≤ k)
    (hb : ScalingPreservesAtLevel hL hj n (i + 1)) (hs : ScalingPreservesAtLevel hL hj n i)
    (c : Edge L n k (i + 1)) (U : Edge L n k i → ComplexMatrix2) :
    PeriodicLattice.logAverageValue (transportTotal (scaleEdge hL hj i) U)
        (scaleEdge hL hj (i + 1) c) = PeriodicLattice.logAverageValue U c := by
  unfold PeriodicLattice.logAverageValue
  rw [sitesInBlock_source hL hj hb, finsum_mem_image (scaleVertex hL hj i).injective.injOn,
    parallelTransport_scale hL hj hs]
  refine congrArg (fun z => ComplexMatrix2.matExp (PeriodicLattice.inverseFourthPowerWeight L • z) *
      PeriodicLattice.parallelTransport U c)
    (finsum_congr fun x => finsum_congr fun _ => ?_)
  obtain ⟨e, e', he⟩ := exists_contourCrossingDefect_equiv hL hj hs c U x
  rw [Fintype.card_congr e.symm, Fintype.card_congr e'.symm, ← e.sum_comp]
  refine congrArg _ (Finset.sum_congr rfl fun σ _ => ?_)
  rw [← e'.sum_comp]
  simp only [he]
theorem crossingCondition_scale_iff (hL : 0 < L) (hj : j ≤ k)
    (hb : ScalingPreservesAtLevel hL hj n (i + 1)) (hs : ScalingPreservesAtLevel hL hj n i)
    (c : Edge L n k (i + 1)) (U : Edge L n k i → ComplexMatrix2) :
    (∀ x ∈ PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth j i)
          (scaleEdge hL hj (i + 1) c).source, ∀ σ σ',
        PeriodicLattice.contourCrossingDefect (transportTotal (scaleEdge hL hj i) U)
          (scaleEdge hL hj (i + 1) c) x σ σ' ≠ -1) ↔
      ∀ x ∈ PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k i) c.source, ∀ σ σ',
        PeriodicLattice.contourCrossingDefect U c x σ σ' ≠ -1 := by
  rw [sitesInBlock_source hL hj hb, forall_mem_image]
  refine forall₂_congr fun x _ => ?_
  obtain ⟨e, e', he⟩ := exists_contourCrossingDefect_equiv hL hj hs c U x
  constructor
  · intro H σ σ'
    rw [← he σ σ']
    exact H _ _
  · intro H σ σ'
    obtain ⟨a, rfl⟩ := e.surjective σ
    obtain ⟨b, rfl⟩ := e'.surjective σ'
    rw [he]
    exact H _ _
theorem blockAverageOnPositive_scale (hL : 0 < L) (hj : j ≤ k)
    (hb : ScalingPreservesAtLevel hL hj n (i + 1)) (hs : ScalingPreservesAtLevel hL hj n i)
    (ω : ℝ) (c : Edge L n k (i + 1)) (U : Edge L n k i → ComplexMatrix2) :
    PeriodicLattice.blockAverageOnPositive ω (transportTotal (scaleEdge hL hj i) U)
        (scaleEdge hL hj (i + 1) c) = PeriodicLattice.blockAverageOnPositive ω U c := by
  have hA := isRegularAveragingCase_scale_iff hL hj hb hs ω c U
  have hB := crossingCondition_scale_iff hL hj hb hs c U
  unfold PeriodicLattice.blockAverageOnPositive
  by_cases h₁ : PeriodicLattice.IsRegularAveragingCase ω U c
  · rw [if_pos h₁, if_pos (hA.2 h₁), regularAverageValue_scale hL hj hb hs]
  · rw [if_neg h₁, if_neg (mt hA.1 h₁)]
    by_cases h₂ : ∀ x ∈ PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k i) c.source,
        ∀ σ σ', PeriodicLattice.contourCrossingDefect U c x σ σ' ≠ -1
    · rw [if_pos h₂, if_pos (hB.2 h₂), logAverageValue_scale hL hj hb hs]
    · rw [if_neg h₂, if_neg (mt hB.1 h₂), parallelTransport_scale hL hj hs]
theorem smoothingStep_scale (hL : 0 < L) (hj : j ≤ k)
    (hb : ScalingPreservesAtLevel hL hj n (i + 1)) (hs : ScalingPreservesAtLevel hL hj n i)
    (V : Edge L n k i → ComplexMatrix2) :
    transportTotal (scaleEdge hL hj (i + 1))
        (PeriodicLattice.blockAverageStep (Averaging.smoothingRadius L) i V) =
      smoothingStep L (scaledExponent n k j) j i (transportTotal (scaleEdge hL hj i) V) := by
  funext c'
  obtain ⟨c, rfl⟩ := (scaleEdge hL hj (i + 1)).surjective c'
  rw [transportTotal_apply]
  change PeriodicLattice.blockAverage (Averaging.smoothingRadius L) V c =
    PeriodicLattice.blockAverage (Averaging.smoothingRadius L)
      (transportTotal (scaleEdge hL hj i) V) (scaleEdge hL hj (i + 1) c)
  have hp := isPositivelyOriented_scaleEdge hL hj (n := n) (i := i + 1) c
  simp only [PeriodicLattice.blockAverage]
  by_cases hc : c.IsPositivelyOriented
  · rw [if_pos hc, if_pos (hp.2 hc), blockAverageOnPositive_scale hL hj hb hs]
  · rw [if_neg hc, if_neg (mt hp.1 hc), ← scaleEdge_opposite,
      blockAverageOnPositive_scale hL hj hb hs]
theorem coe_scaleVertex_ne_iff (hL : 0 < L) (hj : j ≤ k) (x : Vertex L n k i)
    (y : Vertex L n k (i + 1)) :
    ((scaleVertex hL hj i x : Vertex L (scaledExponent n k j) j i) :
        PeriodicLattice.FourTorus L (scaledExponent n k j)) ≠
      (scaleVertex hL hj (i + 1) y : Vertex L (scaledExponent n k j) j (i + 1)) ↔
      (x : PeriodicLattice.FourTorus L n) ≠ y :=
  (scaling hL n k j).injective.ne_iff
theorem blockSitesExceptCenter_scaleVertex (hL : 0 < L) (hj : j ≤ k)
    (hb : ScalingPreservesAtLevel hL hj n (i + 1)) (y : Vertex L n k (i + 1)) :
    PeriodicLattice.blockSitesExceptCenter j i (scaleVertex hL hj (i + 1) y) =
      scaleVertex hL hj i '' PeriodicLattice.blockSitesExceptCenter k i y := by
  ext z'
  obtain ⟨z, rfl⟩ := (scaleVertex hL hj i).surjective z'
  rw [(scaleVertex hL hj i).injective.mem_set_image]
  exact and_congr (scaleVertex_mem_sitesInBlock_iff hL hj hb y z) (coe_scaleVertex_ne_iff hL hj z y)
theorem image_blockBonds (hL : 0 < L) (hj : j ≤ k)
    (hb : ScalingPreservesAtLevel hL hj n (i + 1)) :
    scaleEdge hL hj i '' (PeriodicLattice.blockBonds (PeriodicLattice.levelDepth k i)
        (univ : Set (Vertex L n k (i + 1))) : Set (Edge L n k i)) =
      PeriodicLattice.blockBonds (PeriodicLattice.levelDepth j i)
        (univ : Set (Vertex L (scaledExponent n k j) j (i + 1))) := by
  ext b'
  obtain ⟨b, rfl⟩ := (scaleEdge hL hj i).surjective b'
  rw [(scaleEdge hL hj i).injective.mem_set_image]
  constructor
  · rintro ⟨y, -, h₁, h₂⟩
    exact ⟨scaleVertex hL hj (i + 1) y, mem_univ _,
      And.intro ((scaleVertex_mem_sitesInBlock_iff hL hj hb y _).2 h₁)
        ((scaleVertex_mem_sitesInBlock_iff hL hj hb y _).2 h₂)⟩
  · rintro ⟨y', -, h₁, h₂⟩
    obtain ⟨y, rfl⟩ := (scaleVertex hL hj (i + 1)).surjective y'
    exact ⟨y, mem_univ _,
      And.intro ((scaleVertex_mem_sitesInBlock_iff hL hj hb y _).1 h₁)
        ((scaleVertex_mem_sitesInBlock_iff hL hj hb y _).1 h₂)⟩
theorem isAxialGaugeAt_scale_iff (hL : 0 < L) (hj : j ≤ k)
    (hb : ScalingPreservesAtLevel hL hj n (i + 1)) (hik : i < k) (hij : i < j)
    (V : Edge L n k i → ComplexMatrix2) :
    PeriodicLattice.IsBlockAxialGauge k i univ V ↔
      IsAxialGaugeAt L (scaledExponent n k j) j i (transportTotal (scaleEdge hL hj i) V) := by
  unfold IsAxialGaugeAt PeriodicLattice.IsBlockAxialGauge PeriodicLattice.BlockAxialData
  rw [← image_blockBonds hL hj hb, isGaugeField_image_iff,
    ← image_univ_of_surjective (scaleVertex hL hj (i + 1)).surjective]
  simp only [forall_mem_image, sitesInBlock_scaleVertex hL hj hb, hasContourMean_scale_iff,
    meanContourHolonomy_scale, coe_scaleVertex_ne_iff, hik, hij, true_and]
theorem axialFunction_scale (hL : 0 < L) (hj : j ≤ k)
    (hb : ScalingPreservesAtLevel hL hj n (i + 1)) (V : Edge L n k i → ComplexMatrix2) :
    PeriodicLattice.axialGaugeFunction k i univ V =
      axialFunction L (scaledExponent n k j) j i (transportTotal (scaleEdge hL hj i) V) := by
  unfold axialFunction PeriodicLattice.axialGaugeFunction
  rw [← image_univ_of_surjective (scaleVertex hL hj (i + 1)).surjective,
    finsum_mem_image (scaleVertex hL hj (i + 1)).injective.injOn]
  refine finsum_congr fun y => finsum_congr fun _ => ?_
  rw [blockSitesExceptCenter_scaleVertex hL hj hb,
    finsum_mem_image (scaleVertex hL hj i).injective.injOn]
  simp only [meanContourHolonomy_scale]
theorem statement_holds (hI : ScalingPreservesObjectsAtLevel.Statement)
    (hP : PeriodicLattice.PivotOfEveryBond) : Statement := by
  intro L hL hS k j hj hj₁ i hi n hn
  have hb := (hI L hL hS k j hj hj₁ (i + 1) hi).1 n hn
  have hs := (hI L hL hS k j hj hj₁ i hi.le).1 n hn
  have hik : i < k := lt_of_lt_of_le hi hj
  have h₁ : ∀ c : Edge L n k (i + 1), PeriodicLattice.PivotProperties c :=
    hP ⟨L, hS, ⟨k, by omega⟩, ⟨n, hn⟩⟩ i hik
  have h₂ : ∀ c : Edge L (scaledExponent n k j) j (i + 1), PeriodicLattice.PivotProperties c :=
    hP ⟨L, hS, ⟨j, by omega⟩, ⟨scaledExponent n k j, Nat.add_pos_left hn _⟩⟩ i hi
  exact
    { bondDoubleBlock_image := image_bondDoubleBlock hL hj hb
      doubleBlockPlaquettes_image := image_doubleBlockPlaquettes hL hj hb
      bondCorridor_image := image_bondCorridor hL hj hb
      pivot_image := scaleEdge_pivot hL hj hb hs h₁ h₂
      contourSet_image := fun y x _ => image_contourSet hL hj y x
      bondsInDoubleBlock_image := image_bondsInDoubleBlock hL hj hb
      mem_complexDomain_iff := mem_complexAveragingDomainNearOne_iff hL hj hb hs
      hasContourMean_iff := fun y x U _ => (hasContourMean_scale_iff hL hj U y x).symm
      meanContourHolonomy_eq := fun y x U _ _ => meanContourHolonomy_scale hL hj U y x
      complexMeanContourHolonomy_eq := fun y x U _ _ _ =>
        complexMeanContourHolonomy_scale hL hj U y x
      contourFormAverage_eq := fun y x B _ => contourFormAverage_scale hL hj B y x
      linearSmoothing_eq := linearSmoothing_scale hL hj hb hs
      smoothingStep_eq := fun V _ => smoothingStep_scale hL hj hb hs V
      isAxialGauge_iff := isAxialGaugeAt_scale_iff hL hj hb hik hi
      axialFunction_eq := fun V _ => axialFunction_scale hL hj hb V }
end YangMills.Construction.Tower.ScalingPreservesStepsAtSide
end
