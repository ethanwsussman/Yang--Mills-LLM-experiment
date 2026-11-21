import YangMills.Construction.Lattice.AveragingMapContinuousOnEachCaseSetProof
import YangMills.Construction.Lattice.ComplexObjectsReadTheBondsOfADoubleBlock
import YangMills.Construction.Towers.AveragedContourOfAPairDoesNotDependOnTheBondProof
import YangMills.Construction.Towers.BlocksCorridorsPivotBondsAndPaths
import YangMills.Construction.Towers.WhatTheMapsOfOneStepOfATowerRead
import Mathlib
set_option autoImplicit false
open Set
open YangMills.Construction.InfiniteLattice (AmbientSpace)
noncomputable section
namespace YangMills.Construction.Tower.StepMapsLocalityProof
namespace OnTorus
variable {L n k j : ℕ}
theorem pathHolonomy_congr {U U' : Edge L n k j → Matrices.ComplexMatrix2}
    {Γ : List (Edge L n k j)} (h : ∀ e ∈ Γ, U e = U' e) :
    PeriodicLattice.pathHolonomy U Γ = PeriodicLattice.pathHolonomy U' Γ := by apply _root_.YangMills.Construction.Tower.PairContourIndependence.pathHolonomy_congr <;> assumption
theorem bondFormSumAlong_congr {A A' : Edge L n k j → Matrices.ComplexMatrix2}
    {Γ : List (Edge L n k j)} (h : ∀ e ∈ Γ, A e = A' e) :
    PeriodicLattice.bondFormSumAlong A Γ = PeriodicLattice.bondFormSumAlong A' Γ := by
  unfold PeriodicLattice.bondFormSumAlong
  rw [List.map_congr_left h]
theorem shiftAcross_mem (hL : 0 < L) {c : Edge L n k (j + 1)} {x : Vertex L n k j}
    (hx : x ∈ PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k j) c.source) :
    PeriodicLattice.shiftAcross c x ∈
      PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k j) c.target := by apply _root_.YangMills.Construction.PeriodicLattice.BlockAverageContinuity.shiftAcross_mem_sitesInBlock <;> assumption
theorem source_edges_subset (c : Edge L n k (j + 1)) :
    OneStep.blockInnerEdges c.source ⊆
      (PeriodicLattice.bondsInDoubleBlock c : Set (Edge L n k j)) :=
  fun _ he => ⟨Or.inl he.1, Or.inl he.2⟩
theorem target_edges_subset (c : Edge L n k (j + 1)) :
    OneStep.blockInnerEdges c.target ⊆
      (PeriodicLattice.bondsInDoubleBlock c : Set (Edge L n k j)) :=
  fun _ he => ⟨Or.inr he.1, Or.inr he.2⟩
section Paths
variable (hP : PeriodicLattice.AveragingSchemeProperties)
  (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) (hj : j < k)
include hP hL hn hj
theorem contour_edge_mem {y : Vertex L n k (j + 1)} {x : Vertex L n k j}
    (hx : x ∈ PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k j) y)
    (σ : PeriodicLattice.AxisOrdering y x) {e : Edge L n k j}
    (he : e ∈ PeriodicLattice.orderedContour y x σ) : e ∈ OneStep.blockInnerEdges y :=
  (((hP L hL n k j hn hj .centred).1 y x hx).1.contour_within σ).2 e he
theorem crossing_edge_mem {c : Edge L n k (j + 1)} (hc : c.IsPositivelyOriented)
    {x : Vertex L n k j}
    (hx : x ∈ PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k j) c.source)
    {e : Edge L n k j} (he : e ∈ PeriodicLattice.crossingPath c x) :
    e ∈ (PeriodicLattice.bondsInDoubleBlock c : Set (Edge L n k j)) :=
  (((hP L hL n k j hn hj .centred).2.1 c hc).1.crossing_within x hx).2 e he
variable {U U' : Edge L n k j → Matrices.ComplexMatrix2}
theorem contourFormAverage_congr {y : Vertex L n k (j + 1)} {x : Vertex L n k j}
    (h : EqOn U U' (OneStep.blockInnerEdges y))
    (hx : x ∈ PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k j) y) :
    PeriodicLattice.contourFormAverage U y x = PeriodicLattice.contourFormAverage U' y x := by
  unfold PeriodicLattice.contourFormAverage
  congr 1
  refine Finset.sum_congr rfl fun σ _ => bondFormSumAlong_congr fun e he => ?_
  exact h (contour_edge_mem hP hL hn hj hx σ he)
theorem complexMeanContour_congr {y : Vertex L n k (j + 1)} {x : Vertex L n k j}
    (h : EqOn U U' (OneStep.blockInnerEdges y))
    (hx : x ∈ PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k j) y) :
    PeriodicLattice.complexMeanContourHolonomy U y x =
      PeriodicLattice.complexMeanContourHolonomy U' y x := by
  have hv : PeriodicLattice.contourHolonomies U y x =
      PeriodicLattice.contourHolonomies U' y x := by
    funext σ
    exact pathHolonomy_congr fun e he => h (contour_edge_mem hP hL hn hj hx σ he)
  unfold PeriodicLattice.complexMeanContourHolonomy
  rw [hv]
theorem gaugeFactor_congr {y : Vertex L n k (j + 1)}
    (h : EqOn U U' (OneStep.blockInnerEdges y)) :
    OneStep.gaugeFactor U y = OneStep.gaugeFactor U' y := by
  have hs : (∑ᶠ x ∈ PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k j) y,
        Matrices.ComplexMatrix2.logSeries (PeriodicLattice.complexMeanContourHolonomy U y x)) =
      ∑ᶠ x ∈ PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k j) y,
        Matrices.ComplexMatrix2.logSeries (PeriodicLattice.complexMeanContourHolonomy U' y x) :=
    finsum_mem_congr rfl fun x hx =>
      congrArg Matrices.ComplexMatrix2.logSeries (complexMeanContour_congr hP hL hn hj h hx)
  unfold OneStep.gaugeFactor
  rw [hs]
theorem gaugeFactorDefinedAt_congr {y : Vertex L n k (j + 1)}
    (h : EqOn U U' (OneStep.blockInnerEdges y)) :
    OneStep.GaugeFactorDefinedAt U y ↔ OneStep.GaugeFactorDefinedAt U' y := by
  unfold OneStep.GaugeFactorDefinedAt
  refine forall₂_congr fun x hx => ?_
  rw [complexMeanContour_congr hP hL hn hj h hx]
omit hP hL hn hj in
theorem cubeCentre_eq_of_mem (hZ : BlockStructure) (hL : Conventions.IsAdmissibleBlockingFactor L)
    (hn : 0 < n) (hj : j < k) (x : FineOnlyVertex L n k j) {y : Vertex L n k (j + 1)}
    (hx : x.1 ∈ PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k j) y) :
    cubeCentre x = y := by
  have hne : (x.1 : PeriodicLattice.FourTorus L n) ≠ y := fun e => x.2 (e ▸ y.2)
  have hs := Classical.epsilon_spec
    (p := fun y' : Vertex L n k (j + 1) =>
      x.1 ∈ PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k j) y' ∧
        (x.1 : PeriodicLattice.FourTorus L n) ≠ y') ⟨y, hx, hne⟩
  have hsort : BlocksPartitionFiner L n k (j + 1) :=
    ((hZ L k (j + 1) hL (by omega) (by omega) hj).1 n hn).2.1
  obtain ⟨-, hu, -⟩ := hsort
  exact (hu x.1).unique hs.1 hx
end Paths
section Averages
variable (hP : PeriodicLattice.AveragingSchemeProperties)
  (hC : PeriodicLattice.ComplexDataDeterminedOnDoubleBlock)
  (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) (hj : j < k)
  {c : Edge L n k (j + 1)} (hc : c.IsPositivelyOriented)
  {U U' : Edge L n k j → Matrices.ComplexMatrix2}
  (h : EqOn U U' (PeriodicLattice.bondsInDoubleBlock c : Set (Edge L n k j)))
include hC hL hn hj hc h
theorem complexBlockAverageStep_congr :
    PeriodicLattice.complexBlockAverageStep j U c =
      PeriodicLattice.complexBlockAverageStep j U' c :=
  (hC L hL n k j hn hj c hc U U' fun _ he => h he).average_eq
theorem mem_nearOneDomain_congr :
    U ∈ PeriodicLattice.complexAveragingDomainNearOne c ↔
      U' ∈ PeriodicLattice.complexAveragingDomainNearOne c :=
  (hC L hL n k j hn hj c hc U U' fun _ he => h he).nearOne_iff
include hP
theorem straightenedMean_congr :
    OneStep.straightenedMean U c = OneStep.straightenedMean U' c := by
  unfold OneStep.straightenedMean
  rw [complexBlockAverageStep_congr hC hL hn hj hc h,
    gaugeFactor_congr hP hL hn hj (h.mono (source_edges_subset c)),
    gaugeFactor_congr hP hL hn hj (h.mono (target_edges_subset c))]
theorem straightenedMeanDefinedAt_congr :
    OneStep.StraightenedMeanDefinedAt U c ↔ OneStep.StraightenedMeanDefinedAt U' c := by
  unfold OneStep.StraightenedMeanDefinedAt
  rw [mem_nearOneDomain_congr hC hL hn hj hc h,
    gaugeFactorDefinedAt_congr hP hL hn hj (h.mono (source_edges_subset c)),
    gaugeFactorDefinedAt_congr hP hL hn hj (h.mono (target_edges_subset c))]
end Averages
theorem expTwist_eqOn (hC : PeriodicLattice.ComplexDataDeterminedOnDoubleBlock)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) (hj : j < k)
    {c : Edge L n k (j + 1)} (hc : c.IsPositivelyOriented)
    {B B' : Edge L n k j → Matrices.ComplexMatrix2}
    (h : EqOn B B' (PeriodicLattice.bondsInDoubleBlock c : Set (Edge L n k j))) :
    EqOn (PeriodicLattice.expTwist B 1) (PeriodicLattice.expTwist B' 1)
      (PeriodicLattice.bondsInDoubleBlock c : Set (Edge L n k j)) :=
  fun e he => (hC L hL n k j hn hj c hc 1 1 fun _ _ => rfl).twist_eq B B'
    (fun _ he' => h he') e he
theorem vertexLocality (hP : PeriodicLattice.AveragingSchemeProperties)
    (hZ : BlockStructure) (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n)
    (hj : j < k) (y : Vertex L n k (j + 1)) : OneStep.VertexLocality L n k j y := by
  refine ⟨fun B _ B' _ h => ?_, fun l _ l' _ h => ?_,
    ⟨fun V _ V' _ h => propext (gaugeFactorDefinedAt_congr hP hL hn hj h),
      fun V _ V' _ h => gaugeFactor_congr hP hL hn hj h⟩,
    fun x hx V _ V' _ h => complexMeanContour_congr hP hL hn hj h hx,
    fun x hx B _ B' _ h => ?_⟩
  · show PeriodicLattice.inverseFourthPowerWeight L • _ =
      PeriodicLattice.inverseFourthPowerWeight L • _
    congr 1
    exact finsum_mem_congr rfl fun x hx => contourFormAverage_congr hP hL hn hj h hx
  · show PeriodicLattice.inverseFourthPowerWeight L • _ =
      PeriodicLattice.inverseFourthPowerWeight L • _
    congr 1
    exact finsum_mem_congr rfl fun x hx => h hx
  · show PeriodicLattice.contourFormAverage B (cubeCentre x) x.1 =
      PeriodicLattice.contourFormAverage B' (cubeCentre x) x.1
    rw [cubeCentre_eq_of_mem hZ hL hn hj x hx]
    exact contourFormAverage_congr hP hL hn hj h hx
theorem edgeLocality (hP : PeriodicLattice.AveragingSchemeProperties)
    (hC : PeriodicLattice.ComplexDataDeterminedOnDoubleBlock)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) (hj : j < k)
    (c : Edge L n k (j + 1)) (hc : c.IsPositivelyOriented) : OneStep.EdgeLocality L n k j c := by
  have hE := fun {B B' : Edge L n k j → Matrices.ComplexMatrix2} (h : EqOn B B'
      (PeriodicLattice.bondsInDoubleBlock c : Set (Edge L n k j))) =>
    expTwist_eqOn hC hL hn hj hc h
  refine ⟨fun B _ B' _ h => ?_, fun B _ B' _ h => ?_,
    ⟨fun V _ V' _ h => propext (mem_nearOneDomain_congr hC hL hn hj hc h),
      fun V _ V' _ h => complexBlockAverageStep_congr hC hL hn hj hc h⟩,
    ⟨fun V _ V' _ h => propext (straightenedMeanDefinedAt_congr hP hC hL hn hj hc h),
      fun V _ V' _ h => straightenedMean_congr hP hC hL hn hj hc h⟩,
    ⟨fun B _ B' _ h => propext ?_, fun B _ B' _ h => ?_⟩,
    ⟨fun B _ B' _ h => propext ?_, fun B _ B' _ h => ?_⟩⟩
  · show PeriodicLattice.inverseFourthPowerWeight L • _ =
      PeriodicLattice.inverseFourthPowerWeight L • _
    congr 1
    exact finsum_mem_congr rfl fun x hx =>
      bondFormSumAlong_congr fun e he => h (crossing_edge_mem hP hL hn hj hc hx he)
  · show PeriodicLattice.inverseFourthPowerWeight L • PeriodicLattice.linearBlockSum B c =
      PeriodicLattice.inverseFourthPowerWeight L • PeriodicLattice.linearBlockSum B' c
    congr 1
    unfold PeriodicLattice.linearBlockSum
    refine finsum_mem_congr rfl fun x hx => ?_
    rw [contourFormAverage_congr hP hL hn hj (h.mono (source_edges_subset c)) hx,
      bondFormSumAlong_congr (fun e he => h (crossing_edge_mem hP hL hn hj hc hx he)),
      contourFormAverage_congr hP hL hn hj (h.mono (target_edges_subset c))
        (shiftAcross_mem (by have := hL.2; omega) hx)]
  · have hB := hE h
    show (PeriodicLattice.expTwist B 1 ∈ PeriodicLattice.complexAveragingDomainNearOne c ∧
        PeriodicLattice.complexBlockAverageStep j (PeriodicLattice.expTwist B 1) c ∈
          Matrices.ComplexMatrix2.logBall) ↔
      (PeriodicLattice.expTwist B' 1 ∈ PeriodicLattice.complexAveragingDomainNearOne c ∧
        PeriodicLattice.complexBlockAverageStep j (PeriodicLattice.expTwist B' 1) c ∈
          Matrices.ComplexMatrix2.logBall)
    rw [mem_nearOneDomain_congr hC hL hn hj hc hB, complexBlockAverageStep_congr hC hL hn hj hc hB]
  · have hB := hE h
    show Complex.I⁻¹ • Matrices.ComplexMatrix2.logSeries (PeriodicLattice.complexBlockAverageStep j
        (PeriodicLattice.expTwist B 1) c) = Complex.I⁻¹ • Matrices.ComplexMatrix2.logSeries
          (PeriodicLattice.complexBlockAverageStep j (PeriodicLattice.expTwist B' 1) c)
    rw [complexBlockAverageStep_congr hC hL hn hj hc hB]
  · have hB := hE h
    show (OneStep.StraightenedMeanDefinedAt (PeriodicLattice.expTwist B 1) c ∧
        OneStep.straightenedMean (PeriodicLattice.expTwist B 1) c ∈
          Matrices.ComplexMatrix2.logBall) ↔
      (OneStep.StraightenedMeanDefinedAt (PeriodicLattice.expTwist B' 1) c ∧
        OneStep.straightenedMean (PeriodicLattice.expTwist B' 1) c ∈
          Matrices.ComplexMatrix2.logBall)
    rw [straightenedMeanDefinedAt_congr hP hC hL hn hj hc hB,
      straightenedMean_congr hP hC hL hn hj hc hB]
  · have hB := hE h
    show Complex.I⁻¹ • Matrices.ComplexMatrix2.logSeries (OneStep.straightenedMean
        (PeriodicLattice.expTwist B 1) c) = Complex.I⁻¹ • Matrices.ComplexMatrix2.logSeries
          (OneStep.straightenedMean (PeriodicLattice.expTwist B' 1) c)
    rw [straightenedMean_congr hP hC hL hn hj hc hB]
theorem faceLocality (p : Face L n k (j + 1)) :
    UnitScale.OneStep.DependsOnlyOn univ (OneStep.facesOfFaceMean p)
      fun F => OneStep.faceMean F p := by
  intro F _ F' _ h
  show PeriodicLattice.inverseFourthPowerWeight L • _ =
    PeriodicLattice.inverseFourthPowerWeight L • _
  congr 1
  exact finsum_mem_congr rfl fun x hx => Finset.sum_congr rfl fun s _ =>
    Finset.sum_congr rfl fun s' _ => h ⟨x, hx, s, s', rfl⟩
end OnTorus
namespace OnSpace
section Congruence
variable {a : ℝ}
theorem linkHolonomy_congr {U U' : InfiniteLattice.Link a → Matrices.ComplexMatrix2}
    {Γ : List (InfiniteLattice.Link a)} (h : ∀ e ∈ Γ, U e = U' e) :
    FullSpace.linkHolonomy U Γ = FullSpace.linkHolonomy U' Γ := by apply _root_.YangMills.Construction.Tower.PairContourIndependence.Infinite.linkHolonomy_congr <;> assumption
theorem sumAlong_congr {A A' : InfiniteLattice.Link a → Matrices.ComplexMatrix2}
    {Γ : List (InfiniteLattice.Link a)} (h : ∀ e ∈ Γ, A e = A' e) :
    FullSpace.sumAlong A Γ = FullSpace.sumAlong A' Γ := by
  unfold FullSpace.sumAlong
  rw [List.map_congr_left h]
theorem expTwist_congr {S : Set (InfiniteLattice.Link a)} (hS : ∀ e ∈ S, e.opposite ∈ S)
    {B B' : InfiniteLattice.Link a → Matrices.ComplexMatrix2} (h : EqOn B B' S)
    {e : InfiniteLattice.Link a} (he : e ∈ S) :
    FullSpace.expTwist B 1 e = FullSpace.expTwist B' 1 e := by
  unfold FullSpace.expTwist
  split_ifs
  · rw [h he]
  · rw [h (hS e he)]
end Congruence
variable {L k j : ℕ}
theorem initial_links_subset (c : FullSpace.Edge L k (j + 1)) :
    FullSpace.cubeLinks L (meshAt L k j) c.initial ⊆
      FullSpace.doubleCubeLinks L (meshAt L k j) c :=
  fun _ he => ⟨Or.inl he.1, Or.inl he.2⟩
theorem terminal_links_subset (c : FullSpace.Edge L k (j + 1)) :
    FullSpace.cubeLinks L (meshAt L k j) c.terminal ⊆
      FullSpace.doubleCubeLinks L (meshAt L k j) c :=
  fun _ he => ⟨Or.inr he.1, Or.inr he.2⟩
theorem opposite_mem_doubleCubeLinks (c : FullSpace.Edge L k (j + 1)) :
    ∀ e ∈ FullSpace.doubleCubeLinks L (meshAt L k j) c,
      e.opposite ∈ FullSpace.doubleCubeLinks L (meshAt L k j) c :=
  fun _ he => ⟨he.2, he.1⟩
section Paths
variable (hY : FullSpace.CubesCorridorsPivotEdgesAndPaths)
  (hL : Conventions.IsAdmissibleBlockingFactor L) (hj : j < k)
include hY hL hj
theorem cubesPartition : FullSpace.CubesOfOrderPartition L k (j + 1) 1 :=
  (hY L hL k (j + 1) 1 (by omega) (by omega) hj le_rfl (by omega)).1
theorem pathsStay : FullSpace.PathsStayInCubes L k (j + 1) :=
  (hY L hL k (j + 1) 1 (by omega) (by omega) hj le_rfl (by omega)).2.2.2
theorem coe_toFiner (y : FullSpace.Vertex L k (j + 1)) :
    ((FullSpace.toFiner (meshAt L k j) y : FullSpace.Vertex L k j) : AmbientSpace) = y := by
  have hself : (y : AmbientSpace) ∈ FullSpace.cubeOfOrder L (meshAt L k j) 1 y :=
    (cubesPartition hY hL hj).center_mem y
  have hmem : (y : AmbientSpace) ∈
      (InfiniteLattice.latticeSubgroup (meshAt L k j) : Set AmbientSpace) := by
    have h' : (⋃ y' : FullSpace.Vertex L k (j + 1), FullSpace.cubeOfOrder L (meshAt L k j) 1 y') =
        (InfiniteLattice.latticeSubgroup (meshAt L k j) : Set AmbientSpace) :=
      (cubesPartition hY hL hj).iUnion_cube
    rw [← h']
    exact mem_iUnion.2 ⟨y, hself⟩
  have hex : ∃ x : InfiniteLattice.LatticePoint (meshAt L k j), (x : AmbientSpace) = y :=
    ⟨⟨y, hmem⟩, rfl⟩
  exact Classical.epsilon_spec hex
theorem toFiner_mem_cube (y : FullSpace.Vertex L k (j + 1)) :
    FullSpace.toFiner (meshAt L k j) y ∈ FullSpace.cubeVertices L (meshAt L k j) y := by
  show ((FullSpace.toFiner (meshAt L k j) y : FullSpace.Vertex L k j) : AmbientSpace) ∈
    FullSpace.cube L (meshAt L k j) y
  rw [coe_toFiner hY hL hj]
  exact (cubesPartition hY hL hj).center_mem y
theorem coe_shifted (c : FullSpace.Edge L k (j + 1)) (x : FullSpace.Vertex L k j) :
    ((FullSpace.shifted c x : FullSpace.Vertex L k j) : AmbientSpace) =
      (x : AmbientSpace) +
        ((c.terminal - c.initial : FullSpace.Vertex L k (j + 1)) : AmbientSpace) := by
  unfold FullSpace.shifted
  rw [AddSubgroup.coe_add, coe_toFiner hY hL hj]
theorem shifted_mem_cube (c : FullSpace.Edge L k (j + 1)) {x : FullSpace.Vertex L k j}
    (hx : x ∈ FullSpace.cubeVertices L (meshAt L k j) c.initial) :
    FullSpace.shifted c x ∈ FullSpace.cubeVertices L (meshAt L k j) c.terminal := by
  have h' : FullSpace.cube L (meshAt L k j) (c.initial + (c.terminal - c.initial)) =
      (fun z : AmbientSpace =>
          z + ((c.terminal - c.initial : FullSpace.Vertex L k (j + 1)) : AmbientSpace)) ''
        FullSpace.cube L (meshAt L k j) c.initial :=
    (cubesPartition hY hL hj).cube_add c.initial (c.terminal - c.initial)
  rw [add_sub_cancel] at h'
  show ((FullSpace.shifted c x : FullSpace.Vertex L k j) : AmbientSpace) ∈
    FullSpace.cube L (meshAt L k j) c.terminal
  rw [coe_shifted hY hL hj, h']
  exact ⟨x, hx, rfl⟩
theorem axisPath_eq_crossingPath (c : FullSpace.Edge L k (j + 1)) :
    FullSpace.axisPath (FullSpace.toFiner (meshAt L k j) c.initial)
        (FullSpace.toFiner (meshAt L k j) c.terminal) =
      FullSpace.crossingPath c (FullSpace.toFiner (meshAt L k j) c.initial) := by
  unfold FullSpace.crossingPath
  congr 1
  apply Subtype.ext
  rw [coe_shifted hY hL hj, coe_toFiner hY hL hj, coe_toFiner hY hL hj, AddSubgroup.coe_sub]
  abel
theorem contour_link_mem {y : FullSpace.Vertex L k (j + 1)} {x : FullSpace.Vertex L k j}
    (hx : x ∈ FullSpace.cubeVertices L (meshAt L k j) y) (σ : FullSpace.ContourOrder L y x)
    {e : FullSpace.Edge L k j} (he : e ∈ FullSpace.contour L y x σ) :
    e ∈ FullSpace.cubeLinks L (meshAt L k j) y := by
  have hΓ : FullSpace.contour L y x σ ∈ FullSpace.contourSet L y x := mem_range_self σ
  exact ⟨(pathsStay hY hL hj).contour_vertex_mem y x hx _ hΓ e.initial
      (Or.inr (Or.inr ⟨e, he, Or.inl rfl⟩)),
    (pathsStay hY hL hj).contour_vertex_mem y x hx _ hΓ e.terminal
      (Or.inr (Or.inr ⟨e, he, Or.inr rfl⟩))⟩
theorem crossing_link_mem (c : FullSpace.Edge L k (j + 1)) {x : FullSpace.Vertex L k j}
    (hx : x ∈ FullSpace.cubeVertices L (meshAt L k j) c.initial) {e : FullSpace.Edge L k j}
    (he : e ∈ FullSpace.crossingPath c x) : e ∈ FullSpace.doubleCubeLinks L (meshAt L k j) c :=
  ⟨(pathsStay hY hL hj).crossing_vertex_mem c x hx e.initial
      (Or.inr (Or.inr ⟨e, he, Or.inl rfl⟩)),
    (pathsStay hY hL hj).crossing_vertex_mem c x hx e.terminal
      (Or.inr (Or.inr ⟨e, he, Or.inr rfl⟩))⟩
variable {U U' : FullSpace.Edge L k j → Matrices.ComplexMatrix2}
theorem contourAverage_congr {y : FullSpace.Vertex L k (j + 1)} {x : FullSpace.Vertex L k j}
    (h : EqOn U U' (FullSpace.cubeLinks L (meshAt L k j) y))
    (hx : x ∈ FullSpace.cubeVertices L (meshAt L k j) y) :
    FullSpace.contourAverage L U y x = FullSpace.contourAverage L U' y x := by
  unfold FullSpace.contourAverage
  congr 1
  refine Finset.sum_congr rfl fun σ _ => sumAlong_congr fun e he => ?_
  exact h (contour_link_mem hY hL hj hx σ he)
theorem contourHolonomies_congr {y : FullSpace.Vertex L k (j + 1)} {x : FullSpace.Vertex L k j}
    (h : EqOn U U' (FullSpace.cubeLinks L (meshAt L k j) y))
    (hx : x ∈ FullSpace.cubeVertices L (meshAt L k j) y) :
    FullSpace.contourHolonomies L U y x = FullSpace.contourHolonomies L U' y x := by
  funext σ
  exact linkHolonomy_congr fun e he => h (contour_link_mem hY hL hj hx σ he)
theorem complexContourMean_congr {y : FullSpace.Vertex L k (j + 1)}
    {x : FullSpace.Vertex L k j} (h : EqOn U U' (FullSpace.cubeLinks L (meshAt L k j) y))
    (hx : x ∈ FullSpace.cubeVertices L (meshAt L k j) y) :
    FullSpace.complexContourMean L U y x = FullSpace.complexContourMean L U' y x := by
  unfold FullSpace.complexContourMean
  rw [contourHolonomies_congr hY hL hj h hx]
theorem gaugeFactor_congr {y : FullSpace.Vertex L k (j + 1)}
    (h : EqOn U U' (FullSpace.cubeLinks L (meshAt L k j) y)) :
    FullSpace.OneStep.gaugeFactor U y = FullSpace.OneStep.gaugeFactor U' y := by
  have hs : (∑ᶠ x ∈ FullSpace.cubeVertices L (meshAt L k j) y,
        Matrices.ComplexMatrix2.logSeries (FullSpace.complexContourMean L U y x)) =
      ∑ᶠ x ∈ FullSpace.cubeVertices L (meshAt L k j) y,
        Matrices.ComplexMatrix2.logSeries (FullSpace.complexContourMean L U' y x) :=
    finsum_mem_congr rfl fun x hx =>
      congrArg Matrices.ComplexMatrix2.logSeries (complexContourMean_congr hY hL hj h hx)
  unfold FullSpace.OneStep.gaugeFactor
  rw [hs]
theorem gaugeFactorDefinedAt_congr {y : FullSpace.Vertex L k (j + 1)}
    (h : EqOn U U' (FullSpace.cubeLinks L (meshAt L k j) y)) :
    FullSpace.OneStep.GaugeFactorDefinedAt U y ↔ FullSpace.OneStep.GaugeFactorDefinedAt U' y := by
  unfold FullSpace.OneStep.GaugeFactorDefinedAt
  refine forall₂_congr fun x hx => ?_
  rw [complexContourMean_congr hY hL hj h hx]
theorem crossingDefect_congr {c : FullSpace.Edge L k (j + 1)}
    (h : EqOn U U' (FullSpace.doubleCubeLinks L (meshAt L k j) c))
    {x : FullSpace.Vertex L k j} (hx : x ∈ FullSpace.cubeVertices L (meshAt L k j) c.initial) :
    FullSpace.crossingDefect L U c x = FullSpace.crossingDefect L U' c x := by
  have hcross : ∀ x ∈ FullSpace.cubeVertices L (meshAt L k j) c.initial,
      FullSpace.linkHolonomy U (FullSpace.crossingPath c x) =
        FullSpace.linkHolonomy U' (FullSpace.crossingPath c x) :=
    fun x hx => linkHolonomy_congr fun e he => h (crossing_link_mem hY hL hj c hx he)
  have htransport : FullSpace.transportAlong U c = FullSpace.transportAlong U' c := by
    unfold FullSpace.transportAlong
    rw [axisPath_eq_crossingPath hY hL hj c]
    exact hcross _ (toFiner_mem_cube hY hL hj c.initial)
  unfold FullSpace.crossingDefect
  rw [complexContourMean_congr hY hL hj (h.mono (initial_links_subset c)) hx, hcross x hx,
    complexContourMean_congr hY hL hj (h.mono (terminal_links_subset c))
      (shifted_mem_cube hY hL hj c hx), htransport]
theorem complexMean_congr {c : FullSpace.Edge L k (j + 1)}
    (h : EqOn U U' (FullSpace.doubleCubeLinks L (meshAt L k j) c))
    (hc : c.IsPositivelyOriented) :
    FullSpace.OneStep.complexMean L k j U c = FullSpace.OneStep.complexMean L k j U' c := by
  have htransport : FullSpace.transportAlong U c = FullSpace.transportAlong U' c := by
    unfold FullSpace.transportAlong
    rw [axisPath_eq_crossingPath hY hL hj c]
    exact linkHolonomy_congr fun e he =>
      h (crossing_link_mem hY hL hj c (toFiner_mem_cube hY hL hj c.initial) he)
  have hsum : (∑ᶠ x ∈ FullSpace.cubeVertices L (meshAt L k j) c.initial,
        Matrices.ComplexMatrix2.logSeries (FullSpace.crossingDefect L U c x)) =
      ∑ᶠ x ∈ FullSpace.cubeVertices L (meshAt L k j) c.initial,
        Matrices.ComplexMatrix2.logSeries (FullSpace.crossingDefect L U' c x) :=
    finsum_mem_congr rfl fun x hx => by rw [crossingDefect_congr hY hL hj h hx]
  show FullSpace.complexSmoothing L U c = FullSpace.complexSmoothing L U' c
  unfold FullSpace.complexSmoothing
  rw [if_pos hc, if_pos hc]
  unfold FullSpace.complexSmoothingPositive
  rw [hsum, htransport]
theorem mem_complexDomain_of_eqOn {c : FullSpace.Edge L k (j + 1)}
    (h : EqOn U U' (FullSpace.doubleCubeLinks L (meshAt L k j) c))
    (hU : U ∈ FullSpace.complexDomainNearOne L c) : U' ∈ FullSpace.complexDomainNearOne L c := by
  obtain ⟨⟨⟨hv, hr⟩, ht, hh⟩, hw⟩ := hU
  refine ⟨⟨⟨fun e he => ?_, fun e he => ?_⟩, fun x hx => ?_, fun x hx => ?_⟩, fun x hx => ?_⟩
  · rw [← h he]
    exact hv e he
  · rw [← h he, ← h (opposite_mem_doubleCubeLinks c e he)]
    exact hr e he
  · rw [← contourHolonomies_congr hY hL hj (h.mono (initial_links_subset c)) hx]
    exact ht x hx
  · rw [← contourHolonomies_congr hY hL hj (h.mono (terminal_links_subset c)) hx]
    exact hh x hx
  · rw [← crossingDefect_congr hY hL hj h hx]
    exact hw x hx
theorem mem_complexDomain_congr {c : FullSpace.Edge L k (j + 1)}
    (h : EqOn U U' (FullSpace.doubleCubeLinks L (meshAt L k j) c)) :
    U ∈ FullSpace.complexDomainNearOne L c ↔ U' ∈ FullSpace.complexDomainNearOne L c :=
  ⟨mem_complexDomain_of_eqOn hY hL hj h, mem_complexDomain_of_eqOn hY hL hj h.symm⟩
theorem straightenedMean_congr {c : FullSpace.Edge L k (j + 1)}
    (h : EqOn U U' (FullSpace.doubleCubeLinks L (meshAt L k j) c))
    (hc : c.IsPositivelyOriented) :
    FullSpace.OneStep.straightenedMean U c = FullSpace.OneStep.straightenedMean U' c := by
  unfold FullSpace.OneStep.straightenedMean
  rw [complexMean_congr hY hL hj h hc,
    gaugeFactor_congr hY hL hj (h.mono (initial_links_subset c)),
    gaugeFactor_congr hY hL hj (h.mono (terminal_links_subset c))]
theorem straightenedMeanDefinedAt_congr {c : FullSpace.Edge L k (j + 1)}
    (h : EqOn U U' (FullSpace.doubleCubeLinks L (meshAt L k j) c)) :
    FullSpace.OneStep.StraightenedMeanDefinedAt U c ↔
      FullSpace.OneStep.StraightenedMeanDefinedAt U' c := by
  unfold FullSpace.OneStep.StraightenedMeanDefinedAt
  rw [mem_complexDomain_congr hY hL hj h,
    gaugeFactorDefinedAt_congr hY hL hj (h.mono (initial_links_subset c)),
    gaugeFactorDefinedAt_congr hY hL hj (h.mono (terminal_links_subset c))]
end Paths
theorem cubeCentre_eq_of_mem (hZ : BlockStructure) (hL : Conventions.IsAdmissibleBlockingFactor L)
    (hj : j < k) (x : FullSpace.FineOnlyVertex (meshAt L k (j + 1)) (meshAt L k j))
    {y : FullSpace.Vertex L k (j + 1)} (hx : x.1 ∈ FullSpace.cubeVertices L (meshAt L k j) y) :
    FullSpace.cubeCentre L x = y := by
  have hne : (x.1 : AmbientSpace) ≠ y := fun e => x.2 (e ▸ y.2)
  have hs := Classical.epsilon_spec
    (p := fun y' : FullSpace.Vertex L k (j + 1) =>
      x.1 ∈ FullSpace.cubeVertices L (meshAt L k j) y' ∧ (x.1 : AmbientSpace) ≠ y')
    ⟨y, hx, hne⟩
  have hsort : FullSpace.BlocksPartitionFiner L k (j + 1) :=
    (hZ L k (j + 1) hL (by omega) (by omega) hj).2.2.1
  obtain ⟨-, hu, -⟩ := hsort
  exact (hu x.1).unique hs.1 hx
theorem vertexLocality (hY : FullSpace.CubesCorridorsPivotEdgesAndPaths)
    (hZ : BlockStructure) (hL : Conventions.IsAdmissibleBlockingFactor L) (hj : j < k)
    (y : FullSpace.Vertex L k (j + 1)) : FullSpace.OneStep.VertexLocality L k j y := by
  refine ⟨fun B _ B' _ h => ?_, fun l _ l' _ h => ?_,
    ⟨fun V _ V' _ h => propext (gaugeFactorDefinedAt_congr hY hL hj h),
      fun V _ V' _ h => gaugeFactor_congr hY hL hj h⟩,
    fun x hx V _ V' _ h => complexContourMean_congr hY hL hj h hx,
    fun x hx B _ B' _ h => ?_⟩
  · show PeriodicLattice.inverseFourthPowerWeight L • _ =
      PeriodicLattice.inverseFourthPowerWeight L • _
    congr 1
    exact finsum_mem_congr rfl fun x hx => contourAverage_congr hY hL hj h hx
  · show PeriodicLattice.inverseFourthPowerWeight L • _ =
      PeriodicLattice.inverseFourthPowerWeight L • _
    congr 1
    exact finsum_mem_congr rfl fun x hx => h hx
  · show FullSpace.contourAverage L B (FullSpace.cubeCentre L x) x.1 =
      FullSpace.contourAverage L B' (FullSpace.cubeCentre L x) x.1
    rw [cubeCentre_eq_of_mem hZ hL hj x hx]
    exact contourAverage_congr hY hL hj h hx
theorem edgeLocality (hY : FullSpace.CubesCorridorsPivotEdgesAndPaths)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hj : j < k) (c : FullSpace.Edge L k (j + 1))
    (hc : c.IsPositivelyOriented) : FullSpace.OneStep.EdgeLocality L k j c := by
  have hE : ∀ {B B' : FullSpace.Edge L k j → Matrices.ComplexMatrix2},
      EqOn B B' (FullSpace.doubleCubeLinks L (meshAt L k j) c) →
      EqOn (FullSpace.expTwist B 1) (FullSpace.expTwist B' 1)
        (FullSpace.doubleCubeLinks L (meshAt L k j) c) :=
    fun h _ he => expTwist_congr (opposite_mem_doubleCubeLinks c) h he
  refine ⟨fun B _ B' _ h => ?_, fun B _ B' _ h => ?_,
    ⟨fun V _ V' _ h => propext (mem_complexDomain_congr hY hL hj h),
      fun V _ V' _ h => complexMean_congr hY hL hj h hc⟩,
    ⟨fun V _ V' _ h => propext (straightenedMeanDefinedAt_congr hY hL hj h),
      fun V _ V' _ h => straightenedMean_congr hY hL hj h hc⟩,
    ⟨fun B _ B' _ h => propext ?_, fun B _ B' _ h => ?_⟩,
    ⟨fun B _ B' _ h => propext ?_, fun B _ B' _ h => ?_⟩⟩
  · show PeriodicLattice.inverseFourthPowerWeight L • _ =
      PeriodicLattice.inverseFourthPowerWeight L • _
    congr 1
    exact finsum_mem_congr rfl fun x hx =>
      sumAlong_congr fun e he => h (crossing_link_mem hY hL hj c hx he)
  · show PeriodicLattice.inverseFourthPowerWeight L • _ =
      PeriodicLattice.inverseFourthPowerWeight L • _
    congr 1
    refine finsum_mem_congr rfl fun x hx => ?_
    rw [contourAverage_congr hY hL hj (h.mono (initial_links_subset c)) hx,
      sumAlong_congr (fun e he => h (crossing_link_mem hY hL hj c hx he)),
      contourAverage_congr hY hL hj (h.mono (terminal_links_subset c))
        (shifted_mem_cube hY hL hj c hx)]
  · have hB := hE h
    show (FullSpace.expTwist B 1 ∈ FullSpace.complexDomainNearOne L c ∧
        FullSpace.OneStep.complexMean L k j (FullSpace.expTwist B 1) c ∈
          Matrices.ComplexMatrix2.logBall) ↔
      (FullSpace.expTwist B' 1 ∈ FullSpace.complexDomainNearOne L c ∧
        FullSpace.OneStep.complexMean L k j (FullSpace.expTwist B' 1) c ∈
          Matrices.ComplexMatrix2.logBall)
    rw [mem_complexDomain_congr hY hL hj hB, complexMean_congr hY hL hj hB hc]
  · have hB := hE h
    show Complex.I⁻¹ • Matrices.ComplexMatrix2.logSeries (FullSpace.OneStep.complexMean L k j
        (FullSpace.expTwist B 1) c) = Complex.I⁻¹ • Matrices.ComplexMatrix2.logSeries
          (FullSpace.OneStep.complexMean L k j (FullSpace.expTwist B' 1) c)
    rw [complexMean_congr hY hL hj hB hc]
  · have hB := hE h
    show (FullSpace.OneStep.StraightenedMeanDefinedAt (FullSpace.expTwist B 1) c ∧
        FullSpace.OneStep.straightenedMean (FullSpace.expTwist B 1) c ∈
          Matrices.ComplexMatrix2.logBall) ↔
      (FullSpace.OneStep.StraightenedMeanDefinedAt (FullSpace.expTwist B' 1) c ∧
        FullSpace.OneStep.straightenedMean (FullSpace.expTwist B' 1) c ∈
          Matrices.ComplexMatrix2.logBall)
    rw [straightenedMeanDefinedAt_congr hY hL hj hB, straightenedMean_congr hY hL hj hB hc]
  · have hB := hE h
    show Complex.I⁻¹ • Matrices.ComplexMatrix2.logSeries (FullSpace.OneStep.straightenedMean
        (FullSpace.expTwist B 1) c) = Complex.I⁻¹ • Matrices.ComplexMatrix2.logSeries
          (FullSpace.OneStep.straightenedMean (FullSpace.expTwist B' 1) c)
    rw [straightenedMean_congr hY hL hj hB hc]
theorem faceLocality (p : FullSpace.Face L k (j + 1)) :
    UnitScale.OneStep.DependsOnlyOn univ (FullSpace.OneStep.facesOfFaceMean p)
      fun F => FullSpace.OneStep.faceMean F p := by
  intro F _ F' _ h
  show PeriodicLattice.inverseFourthPowerWeight L • _ =
    PeriodicLattice.inverseFourthPowerWeight L • _
  congr 1
  exact finsum_mem_congr rfl fun x hx => Finset.sum_congr rfl fun s _ =>
    Finset.sum_congr rfl fun s' _ => h ⟨x, hx, s, s', rfl⟩
end OnSpace
theorem holds (hY : FullSpace.CubesCorridorsPivotEdgesAndPaths)
    (hZ : BlockStructure) (hP : PeriodicLattice.AveragingSchemeProperties)
    (hC : PeriodicLattice.ComplexDataDeterminedOnDoubleBlock) : StepMapsLocalityStatement := by
  intro L k j hL hj
  exact ⟨fun n hn => ⟨OnTorus.vertexLocality hP hZ hL hn hj,
      OnTorus.edgeLocality hP hC hL hn hj, OnTorus.faceLocality⟩,
    ⟨OnSpace.vertexLocality hY hZ hL hj, OnSpace.edgeLocality hY hL hj,
      OnSpace.faceLocality⟩⟩
end YangMills.Construction.Tower.StepMapsLocalityProof
end
