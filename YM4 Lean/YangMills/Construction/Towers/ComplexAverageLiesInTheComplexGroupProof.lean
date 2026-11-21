import YangMills.Construction.Matrices.ExpChartHolomorphyProof
import YangMills.Construction.Averaging.MeanInTheComplexGroup
import YangMills.Construction.Lattice.BondsPathsAndAveragesOfADoubleBlock
import YangMills.Construction.Lattice.GaugeCovarianceOfHolonomyProof
import YangMills.Construction.Matrices.LogSeriesTracelessOnUnitDet
import YangMills.Construction.Towers.BlocksCorridorsPivotBondsAndPathsProof
import YangMills.Construction.Towers.ComplexAverageLiesInTheComplexGroup
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction
open Matrices
namespace Tower.ComplexMeanMembership
open PeriodicLattice (complexGaugeGroup)
theorem one_mem_gaugeGroup : (1 : ComplexMatrix2) ∈ complexGaugeGroup := Matrix.det_one
theorem mul_mem_gaugeGroup {A B : ComplexMatrix2} (hA : A ∈ complexGaugeGroup)
    (hB : B ∈ complexGaugeGroup) : A * B ∈ complexGaugeGroup := by apply _root_.YangMills.SharedProofs.p592 <;> assumption
theorem inv_mem_gaugeGroup {A : ComplexMatrix2} (hA : A ∈ complexGaugeGroup) :
    A⁻¹ ∈ complexGaugeGroup := by apply _root_.YangMills.Construction.Averaging.SmallFieldAnalyticity.inv_mem_complexGaugeGroup <;> assumption
theorem list_prod_mem_gaugeGroup (l : List ComplexMatrix2) (h : ∀ A ∈ l, A ∈ complexGaugeGroup) :
    l.prod ∈ complexGaugeGroup := by
  induction l with
  | nil => exact one_mem_gaugeGroup
  | cons A l ih =>
    rw [List.prod_cons]
    exact mul_mem_gaugeGroup (h A (by simp)) (ih fun B hB => h B (by simp [hB]))
theorem map_prod_mem_gaugeGroup {β : Type} (U : β → ComplexMatrix2) (Γ : List β)
    (h : ∀ b ∈ Γ, U b ∈ complexGaugeGroup) : (Γ.map U).prod ∈ complexGaugeGroup :=
  list_prod_mem_gaugeGroup _ fun A hA => by
    obtain ⟨b, hb, rfl⟩ := List.mem_map.1 hA
    exact h b hb
theorem complexLogMean_mem (hM : Averaging.ComplexLogMeanOfSmallFamilies) {ι : Type} [Fintype ι]
    [Nonempty ι] (V : ι → ComplexMatrix2) (hV : ∀ i, V i ∈ complexGaugeGroup)
    (hd : ComplexMatrix2.familyDiameter V < Averaging.centreOfMassDiameter) :
    PeriodicLattice.complexLogMean V ∈ complexGaugeGroup := by
  let e := Fintype.equivFin ι
  have hn : 1 ≤ Fintype.card ι := Fintype.card_pos
  have hF := hM.2.2.2.1 (Fintype.card ι) hn
  let V' : Fin (Fintype.card ι) → ComplexMatrix2 := fun i => V (e.symm i)
  have hdiam : ComplexMatrix2.familyDiameter V' = ComplexMatrix2.familyDiameter V :=
    (Equiv.prodCongr e.symm e.symm).iSup_comp
      (g := fun p : ι × ι => ComplexMatrix2.operatorNorm (V p.1 * (V p.2)⁻¹ - 1))
  have hs : V' ∈ Averaging.smallComplexFamilies (Fintype.card ι) :=
    ⟨fun i => hV _, by rw [hdiam]; exact hd⟩
  obtain ⟨W, hW, -⟩ := hF.existsUnique V' hs
  have key : ∃ W, ComplexMatrix2.IsLogMean complexGaugeGroup V W ∧
      ∃ i, ComplexMatrix2.operatorNorm (V i * W⁻¹ - 1) ≤ PeriodicLattice.complexMeanTolerance := by
    refine ⟨W, ⟨hW.1.1, fun i => ?_, ?_⟩, ?_⟩
    · have := hW.1.2.1 (e i)
      simpa [V'] using this
    · rw [← hW.1.2.2]
      exact (Equiv.sum_comp e.symm fun i => ComplexMatrix2.logSeries (V i * W⁻¹)).symm
    · obtain ⟨i, hi⟩ := hW.2
      exact ⟨e.symm i, hi⟩
  exact (Classical.epsilon_spec key).1.1
theorem matExp_mem (hE : ComplexMatrix2.ExpLogEstimates) {Z : ComplexMatrix2}
    (hZ : Z ∈ ComplexMatrix2.traceless) : ComplexMatrix2.matExp Z ∈ complexGaugeGroup := by apply _root_.YangMills.DeltaSharedProofs.p501082 <;> assumption
theorem smoothed_mem (hE : ComplexMatrix2.ExpLogEstimates)
    (hT : ComplexMatrix2.LogSeriesTracelessOfUnitDet) {X : Type} (s : Set X)
    (W : X → ComplexMatrix2) (T : ComplexMatrix2) (w : ℂ) (hW : ∀ x ∈ s, W x ∈ complexGaugeGroup)
    (hW₁ : ∀ x ∈ s, ComplexMatrix2.operatorNorm (W x - 1) < 1) (hTr : T ∈ complexGaugeGroup) :
    ComplexMatrix2.matExp (w • ∑ᶠ x ∈ s, ComplexMatrix2.logSeries (W x)) * T ∈
      complexGaugeGroup := by
  have hS : (∑ᶠ x ∈ s, ComplexMatrix2.logSeries (W x)) ∈ ComplexMatrix2.traceless :=
    finsum_mem_induction (· ∈ ComplexMatrix2.traceless) (zero_mem _) (fun _ _ => add_mem)
      fun x hx => hT _ (hW x hx) (hW₁ x hx)
  exact mul_mem_gaugeGroup (matExp_mem hE (ComplexMatrix2.traceless.smul_mem w hS)) hTr
section FiniteSide
open PeriodicLattice
variable {L m K n : ℕ}
private theorem nonempty_axisOrdering {j j' : ℤ} (y : PeriodicLattice.Site L m j)
    (x : PeriodicLattice.Site L m j') : Nonempty (AxisOrdering y x) :=
  ⟨(offsetAxes y x).equivFin.symm⟩
private theorem toSublattice_coe_and_mem (hL : 0 < L) (y : SiteAtLevel L m K (n + 1)) :
    ((y.toSublattice (levelDepth K n) : SiteAtLevel L m K n) : FourTorus L m) = y ∧
      y.toSublattice (levelDepth K n) ∈ sitesInBlock (levelDepth K n) y := by
  have hle : levelDepth K (n + 1) ≤ levelDepth K n := by
    simp only [levelDepth]; push_cast; omega
  have hstep : levelDepth K (n + 1) + ((1 : ℕ) : ℤ) = levelDepth K n := by
    simp only [levelDepth]; push_cast; ring
  have hy : (y : FourTorus L m) ∈ sublattice L m (levelDepth K n) := sublattice_mono hL m hle y.2
  have hcoe : ((y.toSublattice (levelDepth K n) : SiteAtLevel L m K n) : FourTorus L m) = y :=
    Classical.epsilon_spec
      (p := fun z : PeriodicLattice.Site L m (levelDepth K n) => (z : FourTorus L m) = y)
      ⟨⟨y, hy⟩, rfl⟩
  refine ⟨hcoe, ?_, ?_⟩
  · rw [hcoe]
    show TorusMetric.torusSupNorm ((y : FourTorus L m) - (y : FourTorus L m)) ≤ meshSize L _ / 2
    rw [sub_self]
    have hs : 0 < meshSize L (levelDepth K (n + 1)) := by
      unfold meshSize
      have : (0 : ℝ) < L := by exact_mod_cast hL
      positivity
    have h0 : TorusMetric.torusSupNorm (0 : FourTorus L m) ≤ 0 := by
      refine csInf_le_of_le ⟨0, ?_⟩ ⟨0, ?_, ?_⟩ le_rfl
      · rintro _ ⟨u, -, rfl⟩
        exact (abs_nonneg (u 0)).trans (Finset.le_sup' (fun ν => |u ν|) (Finset.mem_univ 0))
      · funext μ
        simp [TorusMetric.torusProj]
      · simp [TorusMetric.supNormVec]
    linarith
  · rw [hcoe, hstep]
    exact hy
abbrev _root_.YangMills.SharedProofs.p56939 := @toSublattice_coe_and_mem
private theorem axialPath_eq_crossingPath (hL : 0 < L) (c : BondAtLevel L m K (n + 1)) :
    axialPath (c.source.toSublattice (levelDepth K n)) (c.target.toSublattice (levelDepth K n)) =
      crossingPath c (c.source.toSublattice (levelDepth K n)) := by
  have hle : levelDepth K (n + 1) ≤ levelDepth K n := by
    simp only [levelDepth]; push_cast; omega
  have hin : ((((c.target - c.source).toSublattice (levelDepth K n)) : SiteAtLevel L m K n) :
        FourTorus L m) =
      ((c.target - c.source : SiteAtLevel L m K (n + 1)) : FourTorus L m) :=
    Classical.epsilon_spec (p := fun z : SiteAtLevel L m K n =>
      (z : FourTorus L m) = ((c.target - c.source : SiteAtLevel L m K (n + 1)) : FourTorus L m))
      ⟨⟨_, sublattice_mono hL m hle (c.target - c.source).2⟩, rfl⟩
  have ht : c.target.toSublattice (levelDepth K n) =
      shiftAcross c (c.source.toSublattice (levelDepth K n)) := by
    apply Subtype.ext
    unfold shiftAcross
    rw [AddSubgroup.coe_add, hin, (toSublattice_coe_and_mem hL c.target).1,
      (toSublattice_coe_and_mem hL c.source).1, AddSubgroup.coe_sub, add_sub_cancel]
  rw [ht]
  rfl
abbrev _root_.YangMills.SharedProofs.p11419 := @axialPath_eq_crossingPath
theorem mem_of_finiteSide (hM : Averaging.ComplexLogMeanOfSmallFamilies)
    (hD : DoubleBlockStructure.Statement)
    (hE : ComplexMatrix2.ExpLogEstimates)
    (hT : ComplexMatrix2.LogSeriesTracelessOfUnitDet)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hm : 0 < m) (hn : n < K)
    (c : BondAtLevel L m K (n + 1)) (V : BondAtLevel L m K n → ComplexMatrix2)
    (hc : c.IsPositivelyOriented)
    (hV : V ∈ (complexAveragingDomainNearOne c : Set (BondAtLevel L m K n → ComplexMatrix2))) :
    (∀ y : SiteAtLevel L m K (n + 1), (y = c.source ∨ y = c.target) →
      ∀ x ∈ sitesInBlock (levelDepth K n) y,
        complexMeanContourHolonomy V y x ∈ complexGaugeGroup) ∧
    complexBlockAverage V c ∈ complexGaugeGroup := by
  have hL0 : 0 < L := by have := hL.2; omega
  obtain ⟨-, hContours, hStraight, -, -⟩ := hD L m K n hL hm hn c
  obtain ⟨⟨hconf, hdt, hdh⟩, hW₁⟩ := hV
  have hvalues : ∀ y : SiteAtLevel L m K (n + 1), (y = c.source ∨ y = c.target) →
      ∀ x ∈ sitesInBlock (levelDepth K n) y, ∀ σ,
        contourHolonomies V y x σ ∈ complexGaugeGroup :=
    fun y hy x hx σ => map_prod_mem_gaugeGroup V _ fun b hb =>
      hconf.1 b ((hContours y hy x hx _ ⟨σ, rfl⟩).2 b hb)
  have hcontour : ∀ y : SiteAtLevel L m K (n + 1), (y = c.source ∨ y = c.target) →
      ∀ x ∈ sitesInBlock (levelDepth K n) y,
        complexMeanContourHolonomy V y x ∈ complexGaugeGroup := by
    intro y hy x hx
    have := nonempty_axisOrdering y x
    refine complexLogMean_mem hM _ (hvalues y hy x hx) ?_
    rcases hy with rfl | rfl
    · exact hdt x hx
    · exact hdh x hx
  have hcross : ∀ x ∈ sitesInBlock (levelDepth K n) c.source,
      pathHolonomy V (crossingPath c x) ∈ complexGaugeGroup :=
    fun x hx => map_prod_mem_gaugeGroup V _ fun b hb =>
      hconf.1 b ((hStraight.1 x hx).2.2.2.2 b hb)
  have htr : parallelTransport V c ∈ complexGaugeGroup := by
    unfold parallelTransport
    rw [axialPath_eq_crossingPath hL0 c]
    exact hcross _ (toSublattice_coe_and_mem hL0 c.source).2
  refine ⟨hcontour, ?_⟩
  have hval : complexBlockAverage V c = complexBlockAverageOnPositive V c := if_pos hc
  rw [hval]
  refine smoothed_mem hE hT _ _ _ _ (fun x hx => ?_) hW₁ htr
  exact mul_mem_gaugeGroup (mul_mem_gaugeGroup
    (mul_mem_gaugeGroup (hcontour _ (Or.inl rfl) x hx) (hcross x hx))
    (inv_mem_gaugeGroup (hcontour _ (Or.inr rfl) _ (hStraight.1 x hx).1)))
    (inv_mem_gaugeGroup htr)
end FiniteSide
section SideAtInfinity
open FullSpace
open InfiniteLattice (AmbientSpace)
variable {L k j : ℕ}
private theorem nonempty_contourOrder {a a' : ℝ} (y : InfiniteLattice.LatticePoint a)
    (x : InfiniteLattice.LatticePoint a') : Nonempty (ContourOrder L y x) :=
  ⟨(offsetSupport L y x).equivFin.symm⟩
private theorem mem_coarser_latticeSubgroup (hL : Conventions.IsAdmissibleBlockingFactor L)
    (hP : CubesOfOrderPartition L k j 1) (w : FullSpace.Vertex L k j) :
    (w : AmbientSpace) ∈ InfiniteLattice.latticeSubgroup (meshAt L k (j - 1)) := by
  have h13 : (13 : ℝ) ≤ L := by exact_mod_cast hL.2
  have h0 : (0 : Fin 4 → ℤ) ∈ offsetBox L 1 := by
    intro μ
    show |(((0 : Fin 4 → ℤ) μ : ℤ) : ℝ)| ≤ ((L : ℝ) ^ 1 - 1) / 2
    rw [Pi.zero_apply, Int.cast_zero, abs_zero, pow_one]
    linarith
  have h := hP.offsetPoint_mem w 0 h0
  have e : cubeOffsetPoint (meshAt L k (j - 1)) w 0 = (w : AmbientSpace) := by
    simp [cubeOffsetPoint]
  rwa [e] at h
abbrev _root_.YangMills.SharedProofs.p3071 := @mem_coarser_latticeSubgroup
private theorem coe_toFiner {a a' : ℝ} {y : InfiniteLattice.LatticePoint a}
    (hy : (y : AmbientSpace) ∈ InfiniteLattice.latticeSubgroup a') :
    (toFiner a' y : AmbientSpace) = y := by apply _root_.YangMills.Construction.Tower.FullSpace.CubeCorridorProof.coe_toFiner <;> assumption
theorem mem_of_sideAtInfinity (hM : Averaging.ComplexLogMeanOfSmallFamilies)
    (hY : CubesCorridorsPivotEdgesAndPaths)
    (hE : ComplexMatrix2.ExpLogEstimates)
    (hT : ComplexMatrix2.LogSeriesTracelessOfUnitDet)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hj : 1 ≤ j) (hjk : j ≤ k)
    (c : FullSpace.Edge L k j) (V : FullSpace.Edge L k (j - 1) → ComplexMatrix2)
    (hc : c.IsPositivelyOriented) (hV : V ∈ complexDomainNearOne L c) :
    (∀ y : FullSpace.Vertex L k j, (y = c.initial ∨ y = c.terminal) →
      ∀ x ∈ cubeVertices L (meshAt L k (j - 1)) y,
        complexContourMean L V y x ∈ complexGaugeGroup) ∧
    complexSmoothing L V c ∈ complexGaugeGroup := by
  obtain ⟨hP, -, -, hPaths⟩ := hY L hL k j 1 (hj.trans hjk) hj hjk le_rfl hj
  obtain ⟨⟨hconf, hdt, hdh⟩, hW₁⟩ := hV
  have hsub : ∀ y : FullSpace.Vertex L k j, (y = c.initial ∨ y = c.terminal) →
      cube L (meshAt L k (j - 1)) y ⊆ doubleCube L (meshAt L k (j - 1)) c := by
    rintro y (rfl | rfl) z hz
    · exact Or.inl hz
    · exact Or.inr hz
  have hvalues : ∀ y : FullSpace.Vertex L k j, (y = c.initial ∨ y = c.terminal) →
      ∀ x ∈ cubeVertices L (meshAt L k (j - 1)) y, ∀ σ,
        contourHolonomies L V y x σ ∈ complexGaugeGroup := by
    intro y hy x hx σ
    refine map_prod_mem_gaugeGroup V _ fun b hb => hconf.1 b ?_
    have hz := hPaths.contour_vertex_mem y x hx _ ⟨σ, rfl⟩
    exact ⟨hsub y hy (hz b.initial (Or.inr (Or.inr ⟨b, hb, Or.inl rfl⟩))),
      hsub y hy (hz b.terminal (Or.inr (Or.inr ⟨b, hb, Or.inr rfl⟩)))⟩
  have hcontour : ∀ y : FullSpace.Vertex L k j, (y = c.initial ∨ y = c.terminal) →
      ∀ x ∈ cubeVertices L (meshAt L k (j - 1)) y,
        complexContourMean L V y x ∈ complexGaugeGroup := by
    intro y hy x hx
    have := nonempty_contourOrder (L := L) y x
    refine complexLogMean_mem hM _ (hvalues y hy x hx) ?_
    rcases hy with rfl | rfl
    · exact hdt x hx
    · exact hdh x hx
  have hcross : ∀ x ∈ cubeVertices L (meshAt L k (j - 1)) c.initial,
      linkHolonomy V (crossingPath c x) ∈ complexGaugeGroup := by
    intro x hx
    refine map_prod_mem_gaugeGroup V _ fun b hb => hconf.1 b ?_
    have hz := hPaths.crossing_vertex_mem c x hx
    exact ⟨hz b.initial (Or.inr (Or.inr ⟨b, hb, Or.inl rfl⟩)),
      hz b.terminal (Or.inr (Or.inr ⟨b, hb, Or.inr rfl⟩))⟩
  have hdiff : (toFiner (meshAt L k (j - 1)) (c.terminal - c.initial) : AmbientSpace) =
      (c.terminal : AmbientSpace) - (c.initial : AmbientSpace) := by
    rw [coe_toFiner (mem_coarser_latticeSubgroup hL hP (c.terminal - c.initial)),
      AddSubgroup.coe_sub]
  have hhead : ∀ x ∈ cubeVertices L (meshAt L k (j - 1)) c.initial,
      shifted c x ∈ cubeVertices L (meshAt L k (j - 1)) c.terminal := by
    intro x hx
    have ht := hP.cube_add c.initial (c.terminal - c.initial)
    rw [add_sub_cancel] at ht
    show ((shifted c x : FullSpace.Vertex L k (j - 1)) : AmbientSpace) ∈
      cubeOfOrder L (meshAt L k (j - 1)) 1 c.terminal
    rw [ht]
    refine ⟨(x : AmbientSpace), hx, ?_⟩
    unfold shifted
    rw [AddSubgroup.coe_add, hdiff, AddSubgroup.coe_sub]
  have htr : transportAlong V c ∈ complexGaugeGroup := by
    have hcoeT := coe_toFiner (mem_coarser_latticeSubgroup hL hP c.initial)
    have hcoeH := coe_toFiner (mem_coarser_latticeSubgroup hL hP c.terminal)
    have ht : toFiner (meshAt L k (j - 1)) c.terminal =
        shifted c (toFiner (meshAt L k (j - 1)) c.initial) := by
      apply Subtype.ext
      unfold shifted
      rw [AddSubgroup.coe_add, hdiff, hcoeH, hcoeT, add_sub_cancel]
    have hx₀ : toFiner (meshAt L k (j - 1)) c.initial ∈
        cubeVertices L (meshAt L k (j - 1)) c.initial := by
      show ((toFiner (meshAt L k (j - 1)) c.initial : FullSpace.Vertex L k (j - 1)) :
          AmbientSpace) ∈ cubeOfOrder L (meshAt L k (j - 1)) 1 c.initial
      rw [hcoeT]
      exact (hP.center_mem c.initial)
    unfold transportAlong
    rw [ht]
    exact hcross _ hx₀
  refine ⟨hcontour, ?_⟩
  have hval : complexSmoothing L V c = complexSmoothingPositive L V c := if_pos hc
  rw [hval]
  refine smoothed_mem hE hT _ _ _ _ (fun x hx => ?_) hW₁ htr
  exact mul_mem_gaugeGroup (mul_mem_gaugeGroup
    (mul_mem_gaugeGroup (hcontour _ (Or.inl rfl) x hx) (hcross x hx))
    (inv_mem_gaugeGroup (hcontour _ (Or.inr rfl) _ (hhead x hx))))
    (inv_mem_gaugeGroup htr)
end SideAtInfinity
theorem complexMeanLiesInComplexGaugeGroup_holds (hM : Averaging.ComplexLogMeanOfSmallFamilies)
    (hD : PeriodicLattice.DoubleBlockStructure.Statement)
    (hY : FullSpace.CubesCorridorsPivotEdgesAndPaths)
    (hE : ComplexMatrix2.ExpLogEstimates)
    (hT : ComplexMatrix2.LogSeriesTracelessOfUnitDet) : ComplexMeanLiesInComplexGaugeGroup := by
  refine ⟨fun X hX hX₁ => ?_, fun L k j hL hj hjk => ?_⟩
  · have h := hT X hX hX₁
    exact ⟨h, h⟩
  · obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
    refine ⟨fun n hn c V hc hV => ?_, fun c V hc hV => ?_⟩
    · exact mem_of_finiteSide hM hD hE hT hL hn (by omega) c V hc hV
    · exact mem_of_sideAtInfinity hM hY hE hT hL hj hjk c V hc hV
end Tower.ComplexMeanMembership
end YangMills.Construction
end
