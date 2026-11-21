import YangMills.Construction.Lattice.AveragingAtAnOrientedBondUnderAnIsometry
import YangMills.Construction.Lattice.ComplexAverageAtAnImageBondProof
import YangMills.Construction.Lattice.IsometryCovarianceOfHolonomiesAndActions
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.PeriodicLattice.BlockAverageIsometry
open IsometryImages
variable {L m : ℕ} {j j' : ℤ}
theorem isLogMean_congr_equiv {ι κ : Type*} [Fintype ι] [Fintype κ] (e : ι ≃ κ)
    {F : κ → Matrices.ComplexMatrix2} {F₀ : ι → Matrices.ComplexMatrix2}
    (hF : ∀ s, F (e s) = F₀ s) (W : Matrices.ComplexMatrix2) :
    Matrices.ComplexMatrix2.IsLogMean compactGaugeGroup F W ↔
      Matrices.ComplexMatrix2.IsLogMean compactGaugeGroup F₀ W := by
  unfold Matrices.ComplexMatrix2.IsLogMean
  refine and_congr_right fun _ => and_congr ?_ ?_
  · constructor
    · intro h s
      rw [← hF]
      exact h _
    · intro h k
      obtain ⟨s, rfl⟩ := e.surjective k
      rw [hF]
      exact h s
  · rw [← e.sum_comp]
    simp only [hF]
structure PreservesAveragingData (σ : FourTorus L m ≃ FourTorus L m) (j j' : ℤ) : Prop where
  source_site : ∀ b : Bond L m j, (bondImage σ b).source = sitePreimage σ.symm b.source
  target_site : ∀ b : Bond L m j, (bondImage σ b).target = sitePreimage σ.symm b.target
  apply_bondImage : ∀ (V : Bond L m j' → Matrices.ComplexMatrix2) (b : Bond L m j'),
    transportGaugeField σ V (bondImage σ b) = V b
  blocks : ∀ y : Site L m j, MapsBlockSites σ j' y
  contours : ∀ (y : Site L m j) (x : Site L m j'), x ∈ sitesInBlock j' y →
    MapsContourIndices σ y x
  crossings : ∀ (c : Bond L m j) (x : Site L m j'), MapsCrossing σ c x
  paths : ∀ c : Bond L m j, MapsTransportPath σ j' c
  plaquettes : ∀ c : Bond L m j, MapsDoubleBlockPlaquettes σ j' c
section Formulas
variable {σ : FourTorus L m ≃ FourTorus L m}
theorem pathHolonomy_pathImage (h : PreservesAveragingData σ j j')
    (V : Bond L m j' → Matrices.ComplexMatrix2) (Γ : List (Bond L m j')) :
    pathHolonomy (transportGaugeField σ V) (pathImage σ Γ) = pathHolonomy V Γ := by
  simp only [pathHolonomy, pathImage, List.map_map]
  congr 1
  exact List.map_congr_left fun b _ => h.apply_bondImage V b
theorem parallelTransport_bondImage (h : PreservesAveragingData σ j j')
    (V : Bond L m j' → Matrices.ComplexMatrix2) (c : Bond L m j) :
    parallelTransport (transportGaugeField σ V) (bondImage σ c) = parallelTransport V c :=
  (congrArg (pathHolonomy (transportGaugeField σ V)) (h.paths c)).symm.trans
    (pathHolonomy_pathImage h V _)
theorem pathHolonomy_crossingPath_image (h : PreservesAveragingData σ j j')
    (V : Bond L m j' → Matrices.ComplexMatrix2) (c : Bond L m j) (x : Site L m j') :
    pathHolonomy (transportGaugeField σ V)
        (crossingPath (bondImage σ c) (sitePreimage σ.symm x)) =
      pathHolonomy V (crossingPath c x) :=
  (congrArg (pathHolonomy (transportGaugeField σ V)) (h.crossings c x).2).symm.trans
    (pathHolonomy_pathImage h V _)
theorem exists_contourEquiv (h : PreservesAveragingData σ j j')
    (V : Bond L m j' → Matrices.ComplexMatrix2) {y y' : Site L m j}
    {x x' : Site L m j'} (hy : y' = sitePreimage σ.symm y) (hx : x' = sitePreimage σ.symm x)
    (hxy : x ∈ sitesInBlock j' y) :
    ∃ e : AxisOrdering y x ≃ AxisOrdering y' x',
      ∀ s, contourHolonomies (transportGaugeField σ V) y' x' (e s) =
        contourHolonomies V y x s := by
  subst hy hx
  obtain ⟨e, he⟩ := h.contours y x hxy
  refine ⟨e, fun s => ?_⟩
  simp only [contourHolonomies]
  rw [he]
  exact pathHolonomy_pathImage h V _
theorem hasContourMean_image_iff (h : PreservesAveragingData σ j j')
    (V : Bond L m j' → Matrices.ComplexMatrix2) {y y' : Site L m j}
    {x x' : Site L m j'} (hy : y' = sitePreimage σ.symm y) (hx : x' = sitePreimage σ.symm x)
    (hxy : x ∈ sitesInBlock j' y) :
    HasContourMean (transportGaugeField σ V) y' x' ↔ HasContourMean V y x := by
  obtain ⟨e, he⟩ := exists_contourEquiv h V hy hx hxy
  exact existsUnique_congr (isLogMean_congr_equiv e he)
theorem meanContourHolonomy_image (h : PreservesAveragingData σ j j')
    (V : Bond L m j' → Matrices.ComplexMatrix2) {y y' : Site L m j}
    {x x' : Site L m j'} (hy : y' = sitePreimage σ.symm y) (hx : x' = sitePreimage σ.symm x)
    (hxy : x ∈ sitesInBlock j' y) :
    meanContourHolonomy (transportGaugeField σ V) y' x' = meanContourHolonomy V y x := by
  obtain ⟨e, he⟩ := exists_contourEquiv h V hy hx hxy
  have hf : Matrices.ComplexMatrix2.IsLogMean compactGaugeGroup
        (contourHolonomies (transportGaugeField σ V) y' x') =
      Matrices.ComplexMatrix2.IsLogMean compactGaugeGroup (contourHolonomies V y x) :=
    funext fun W => propext (isLogMean_congr_equiv e he W)
  simp only [meanContourHolonomy, Matrices.ComplexMatrix2.logMean, hf]
theorem shiftAcross_mem_sitesInBlock (hL : 0 < L) (hjj : j' = j + 1) (c : Bond L m j)
    {x : Site L m j'} (hx : x ∈ sitesInBlock j' c.source) :
    shiftAcross c x ∈ sitesInBlock j' c.target := by apply _root_.YangMills.Construction.PeriodicLattice.ImageBondEquivariance.shiftAcross_mem_sitesInBlock <;> assumption
theorem forall_sitesInBlock_image_iff (h : PreservesAveragingData σ j j') {y y' : Site L m j}
    (hy : y' = sitePreimage σ.symm y) {P' P : Site L m j' → Prop}
    (hP : ∀ x ∈ sitesInBlock j' y, (P' (sitePreimage σ.symm x) ↔ P x)) :
    (∀ x ∈ sitesInBlock j' y', P' x) ↔ ∀ x ∈ sitesInBlock j' y, P x := by
  subst hy
  have hb := h.blocks y
  constructor
  · intro H x hx
    exact (hP x hx).1 (H _ (hb.mapsTo hx))
  · intro H x' hx'
    obtain ⟨x, hx, rfl⟩ := hb.surjOn hx'
    exact (hP x hx).2 (H x hx)
theorem bijOn_sitesInBlock_source (h : PreservesAveragingData σ j j') (c : Bond L m j) :
    BijOn (sitePreimage σ.symm) (sitesInBlock j' c.source)
      (sitesInBlock j' (bondImage σ c).source) := by
  rw [h.source_site c]
  exact h.blocks c.source
theorem crossingDefect_image (h : PreservesAveragingData σ j j') (hL : 0 < L) (hjj : j' = j + 1)
    (V : Bond L m j' → Matrices.ComplexMatrix2) (c : Bond L m j) {x : Site L m j'}
    (hx : x ∈ sitesInBlock j' c.source) :
    crossingDefect (transportGaugeField σ V) (bondImage σ c) (sitePreimage σ.symm x) =
      crossingDefect V c x := by
  unfold crossingDefect
  rw [meanContourHolonomy_image h V (h.source_site c) rfl hx,
    meanContourHolonomy_image h V (h.target_site c) (h.crossings c x).1.symm
      (shiftAcross_mem_sitesInBlock hL hjj c hx),
    pathHolonomy_crossingPath_image h, parallelTransport_bondImage h]
theorem exists_crossingDefect_equiv (h : PreservesAveragingData σ j j') (hL : 0 < L)
    (hjj : j' = j + 1) (V : Bond L m j' → Matrices.ComplexMatrix2) (c : Bond L m j)
    {x : Site L m j'} (hx : x ∈ sitesInBlock j' c.source) :
    ∃ (e : AxisOrdering c.source x ≃
          AxisOrdering (bondImage σ c).source (sitePreimage σ.symm x))
      (e' : AxisOrdering c.target (shiftAcross c x) ≃
          AxisOrdering (bondImage σ c).target
            (shiftAcross (bondImage σ c) (sitePreimage σ.symm x))),
      ∀ s s', contourCrossingDefect (transportGaugeField σ V) (bondImage σ c)
        (sitePreimage σ.symm x) (e s) (e' s') = contourCrossingDefect V c x s s' := by
  obtain ⟨e, he⟩ := exists_contourEquiv h V (h.source_site c) rfl hx
  obtain ⟨e', he'⟩ := exists_contourEquiv h V (h.target_site c) (h.crossings c x).1.symm
    (shiftAcross_mem_sitesInBlock hL hjj c hx)
  refine ⟨e, e', fun s s' => ?_⟩
  have a := he s
  have b := he' s'
  simp only [contourHolonomies] at a b
  unfold contourCrossingDefect
  rw [a, b, pathHolonomy_crossingPath_image h, parallelTransport_bondImage h]
theorem doubleBlockPlaquettesNear_image_iff (h : PreservesAveragingData σ j j') (ω : ℝ)
    (V : Bond L m j' → Matrices.ComplexMatrix2) (c : Bond L m j)
    (hn : ∀ p : Plaquette L m j',
      Matrices.ComplexMatrix2.operatorNorm
          (plaquetteHolonomy (transportGaugeField σ V) (plaquetteImage σ p) - 1) =
        Matrices.ComplexMatrix2.operatorNorm (plaquetteHolonomy V p - 1)) :
    DoubleBlockPlaquettesNear ω (bondImage σ c) (transportGaugeField σ V) ↔
      DoubleBlockPlaquettesNear ω c V := by
  have hp : plaquetteImage σ '' (doubleBlockPlaquettes c : Set (Plaquette L m j')) =
      doubleBlockPlaquettes (bondImage σ c) := h.plaquettes c
  constructor
  · intro H p hpc
    rw [← hn]
    exact H _ (hp ▸ mem_image_of_mem _ hpc)
  · intro H p' hp'
    rw [← hp] at hp'
    obtain ⟨p, hpc, rfl⟩ := hp'
    rw [hn]
    exact H p hpc
theorem isRegularAveragingCase_image_iff (h : PreservesAveragingData σ j j') (hL : 0 < L)
    (hjj : j' = j + 1) (ω : ℝ) (V : Bond L m j' → Matrices.ComplexMatrix2) (c : Bond L m j)
    (hn : ∀ p : Plaquette L m j',
      Matrices.ComplexMatrix2.operatorNorm
          (plaquetteHolonomy (transportGaugeField σ V) (plaquetteImage σ p) - 1) =
        Matrices.ComplexMatrix2.operatorNorm (plaquetteHolonomy V p - 1)) :
    IsRegularAveragingCase ω (transportGaugeField σ V) (bondImage σ c) ↔
      IsRegularAveragingCase ω V c := by
  unfold IsRegularAveragingCase
  refine and_congr (doubleBlockPlaquettesNear_image_iff h ω V c hn)
    (and_congr ?_ (and_congr ?_ ?_))
  · exact forall_sitesInBlock_image_iff h (h.source_site c) fun x hx =>
      hasContourMean_image_iff h V (h.source_site c) rfl hx
  · exact forall_sitesInBlock_image_iff h (h.target_site c) fun x hx =>
      hasContourMean_image_iff h V (h.target_site c) rfl hx
  · refine forall_sitesInBlock_image_iff h (h.source_site c) fun x hx => ?_
    rw [crossingDefect_image h hL hjj V c hx]
theorem noCrossingDefectIsNegOne_image_iff (h : PreservesAveragingData σ j j') (hL : 0 < L)
    (hjj : j' = j + 1) (V : Bond L m j' → Matrices.ComplexMatrix2) (c : Bond L m j) :
    NoCrossingDefectIsNegOne (transportGaugeField σ V) (bondImage σ c) ↔
      NoCrossingDefectIsNegOne V c := by
  unfold NoCrossingDefectIsNegOne
  refine forall_sitesInBlock_image_iff h (h.source_site c) fun x hx => ?_
  obtain ⟨e, e', he⟩ := exists_crossingDefect_equiv h hL hjj V c hx
  constructor
  · intro H s s'
    rw [← he]
    exact H _ _
  · intro H s s'
    have := H (e.symm s) (e'.symm s')
    rw [← he] at this
    simpa using this
theorem regularAverageValue_image (h : PreservesAveragingData σ j j') (hL : 0 < L)
    (hjj : j' = j + 1) (V : Bond L m j' → Matrices.ComplexMatrix2) (c : Bond L m j) :
    regularAverageValue (transportGaugeField σ V) (bondImage σ c) = regularAverageValue V c := by
  unfold regularAverageValue
  rw [parallelTransport_bondImage h]
  congr 3
  exact (finsum_mem_eq_of_bijOn _ (bijOn_sitesInBlock_source h c) fun x hx => by
    rw [crossingDefect_image h hL hjj V c hx]).symm
theorem logAverageValue_image (h : PreservesAveragingData σ j j') (hL : 0 < L)
    (hjj : j' = j + 1) (V : Bond L m j' → Matrices.ComplexMatrix2) (c : Bond L m j) :
    logAverageValue (transportGaugeField σ V) (bondImage σ c) = logAverageValue V c := by
  unfold logAverageValue
  rw [parallelTransport_bondImage h]
  congr 3
  refine (finsum_mem_eq_of_bijOn _ (bijOn_sitesInBlock_source h c) fun x hx => ?_).symm
  obtain ⟨e, e', he⟩ := exists_crossingDefect_equiv h hL hjj V c hx
  rw [Fintype.card_congr e, Fintype.card_congr e']
  congr 1
  refine Fintype.sum_equiv e _ _ fun s => ?_
  congr 1
  exact Fintype.sum_equiv e' _ _ fun s' => by rw [he]
theorem blockAverageCase_image (h : PreservesAveragingData σ j j') (hL : 0 < L)
    (hjj : j' = j + 1) (ω : ℝ) (V : Bond L m j' → Matrices.ComplexMatrix2) (c : Bond L m j)
    (hn : ∀ p : Plaquette L m j',
      Matrices.ComplexMatrix2.operatorNorm
          (plaquetteHolonomy (transportGaugeField σ V) (plaquetteImage σ p) - 1) =
        Matrices.ComplexMatrix2.operatorNorm (plaquetteHolonomy V p - 1)) :
    blockAverageCase ω (transportGaugeField σ V) (bondImage σ c) = blockAverageCase ω V c := by
  have hA := isRegularAveragingCase_image_iff h hL hjj ω V c hn
  have hB := noCrossingDefectIsNegOne_image_iff h hL hjj V c
  unfold blockAverageCase
  by_cases a : IsRegularAveragingCase ω V c
  · rw [if_pos a, if_pos (hA.2 a)]
  · rw [if_neg a, if_neg (mt hA.1 a)]
    by_cases b : NoCrossingDefectIsNegOne V c
    · rw [if_pos b, if_pos (hB.2 b)]
    · rw [if_neg b, if_neg (mt hB.1 b)]
theorem blockAverageOnPositive_image (h : PreservesAveragingData σ j j') (hL : 0 < L)
    (hjj : j' = j + 1) (ω : ℝ) (V : Bond L m j' → Matrices.ComplexMatrix2) (c : Bond L m j)
    (hn : ∀ p : Plaquette L m j',
      Matrices.ComplexMatrix2.operatorNorm
          (plaquetteHolonomy (transportGaugeField σ V) (plaquetteImage σ p) - 1) =
        Matrices.ComplexMatrix2.operatorNorm (plaquetteHolonomy V p - 1)) :
    blockAverageOnPositive ω (transportGaugeField σ V) (bondImage σ c) =
      blockAverageOnPositive ω V c := by
  rw [blockAverageOnPositive_eq_byCase, blockAverageOnPositive_eq_byCase,
    blockAverageCase_image h hL hjj ω V c hn]
  cases blockAverageCase ω V c
  · exact regularAverageValue_image h hL hjj V c
  · exact logAverageValue_image h hL hjj V c
  · exact parallelTransport_bondImage h V c
end Formulas
theorem preservesAveragingData_of_mem (hO : IsometryImages.Statement)
    (hG : LatticeIsometryGroupActionStatement) (hs : Conventions.IsAdmissibleBlockingFactor L)
    (hm : 0 < m) {i : ℤ} (hi : -(m : ℤ) ≤ i) {σ : FourTorus L m ≃ FourTorus L m}
    (hσ : σ ∈ latticeIsometries L m i) (hij : i ≤ j) (hj : 0 ≤ j) (hjj : j' = j + 1) :
    PreservesAveragingData σ j j' := by
  have hσ' : σ.symm ∈ latticeIsometries L m i := by
    obtain ⟨H, hH⟩ := (hG L m i hs hm hi).1.1
    have h1 : σ ∈ H := by
      have : σ ∈ (H : Set (Equiv.Perm (FourTorus L m))) := by rw [hH]; exact hσ
      exact this
    have h3 : σ⁻¹ ∈ (H : Set (Equiv.Perm (FourTorus L m))) := H.inv_mem h1
    rw [hH] at h3
    exact h3
  have hij' : i ≤ j' := by omega
  have hC := ((hG L m i hs hm hi).2.2.2.2 σ hσ j hij).1
  have hC' := ((hG L m i hs hm hi).2.2.2.2 σ hσ j' hij').1
  have hD' := ((hG L m i hs hm hi).2.2.2.2 σ.symm hσ' j' hij').1
  have hsite : ∀ y : Site L m j,
      ((sitePreimage σ.symm y : Site L m j) : FourTorus L m) = σ y := by
    intro y
    have hex : ∃ x : Site L m j, (x : FourTorus L m) = σ.symm.symm y := by
      have hmem : σ y ∈ σ '' (sublattice L m j : Set (FourTorus L m)) := ⟨y, y.2, rfl⟩
      rw [hC.1] at hmem
      exact ⟨⟨σ y, hmem⟩, rfl⟩
    exact Classical.epsilon_spec hex
  have hO' := hO L m hs hm i hi σ hσ j j' hij hj hjj
  refine ⟨fun b => Subtype.ext ?_, fun b => Subtype.ext ?_, fun V b => ?_,
    fun y => (hO'.1 y).1, fun y x hx => (hO'.1 y).2 x hx, fun c x => (hO'.2 c).1 x,
    fun c => (hO'.2 c).2.1, fun c => (hO'.2 c).2.2⟩
  · rw [hsite]
    exact (hC.2.2.2.1 b).1
  · rw [hsite]
    exact (hC.2.2.2.1 b).2
  · have e := hC'.2.2.2.1 b
    have p := hD'.2.2.2.1 (bondImage σ b)
    have : bondPreimage σ (bondImage σ b) = b := by
      apply Bond.ext <;> apply Subtype.ext
      · refine Eq.trans p.1 ?_
        rw [e.1]
        simp
      · refine Eq.trans p.2 ?_
        rw [e.2]
        simp
    exact congrArg V this
theorem blockAverageCommutesWithIsometries (hO : IsometryImages.Statement)
    (hH : IsometryCovariance.Statement)
    (hG : LatticeIsometryGroupActionStatement) : BlockAverageCommutesWithIsometries := by
  intro L m hs hm i hi σ hσ j j' hij hj hjj ω c U hU
  have hL : 0 < L := by have := hs.2; omega
  have h := preservesAveragingData_of_mem hO hG hs hm hi hσ hij hj hjj
  have hij' : i ≤ j' := by omega
  obtain ⟨ε, hε⟩ := hH
  have hn : ∀ p : Plaquette L m j',
      Matrices.ComplexMatrix2.operatorNorm
          (plaquetteHolonomy (transportGaugeField σ U) (plaquetteImage σ p) - 1) =
        Matrices.ComplexMatrix2.operatorNorm (plaquetteHolonomy U p - 1) := fun p =>
    (((hε L m hs hm i hi σ hσ).1 j' hij').1 univ U (fun _ _ => mem_univ _) hU).2 p
      (fun _ _ => mem_univ _) |>.2.2.2
  exact ⟨doubleBlockPlaquettesNear_image_iff h ω U c hn, blockAverageCase_image h hL hjj ω U c hn,
    blockAverageOnPositive_image h hL hjj ω U c hn⟩
end YangMills.Construction.PeriodicLattice.BlockAverageIsometry
