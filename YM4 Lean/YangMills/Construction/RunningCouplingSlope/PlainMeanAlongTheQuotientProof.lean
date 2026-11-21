import YangMills.Construction.RunningCouplingSlope.DerivativeOfThePlainAverageAtOneProof
import YangMills.Construction.RunningCouplingSlope.PlainMapsAtOneOnTheWholeProof
import YangMills.Construction.RunningCouplingSlope.PlainMeanAlongTheQuotient
import YangMills.Construction.Towers.QuotientOfATowerCarriesSetsProof
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.RunningCouplingSlope.AlongProjection
open Tower
variable {L n k i : ℕ}
section Flows
variable (ends : ∀ b : FullSpace.Edge L k i,
  (FullSpace.projEdge L n k i b).source = FullSpace.projVertex L n k i b.initial ∧
    (FullSpace.projEdge L n k i b).target = FullSpace.projVertex L n k i b.terminal)
include ends
private theorem map_projEdge_stepsInOrder (ν : Fin 4 → ℤ) (x : FullSpace.Vertex L k i)
    (l : List (Fin 4)) :
    (FullSpace.stepsInOrder ν x l).map (FullSpace.projEdge L n k i) =
      PeriodicLattice.stepsThroughAxes ν (FullSpace.projVertex L n k i x) l := by apply _root_.YangMills.Construction.Tower.FullSpace.ProjectionSets.map_stepsInOrder <;> assumption
end Flows
private theorem coe_toFiner (hL : 0 < L) (w : FullSpace.Vertex L k (i + 1)) :
    ((FullSpace.toFiner (Tower.meshAt L k i) w : FullSpace.Vertex L k i) :
      InfiniteLattice.AmbientSpace) = w := by apply _root_.YangMills.Construction.Tower.FullSpace.ScalingOfValues.coe_toFiner <;> assumption
private theorem toSublattice_projVertex (hL : 0 < L) (y : FullSpace.Vertex L k (i + 1)) :
    (FullSpace.projVertex L n k (i + 1) y).toSublattice (PeriodicLattice.levelDepth k i) =
      FullSpace.projVertex L n k i (FullSpace.toFiner (Tower.meshAt L k i) y) := by apply _root_.YangMills.Construction.Tower.FullSpace.ProjectionSets.toSublattice_projVertex <;> assumption
private theorem isCubeOffset_of_mem {y : FullSpace.Vertex L k (i + 1)}
    {x : FullSpace.Vertex L k i}
    (hx : x ∈ FullSpace.cubeVertices L (Tower.meshAt L k i) y) :
    FullSpace.IsCubeOffset L y x (FullSpace.cubeOffset L y x) := by apply _root_.YangMills.Construction.Tower.FullSpace.ProjectionSets.isCubeOffset_of_mem <;> assumption
private theorem isBlockOffset_of_isCubeOffset {y : FullSpace.Vertex L k (i + 1)}
    {x : FullSpace.Vertex L k i} {ν : Fin 4 → ℤ} (h : FullSpace.IsCubeOffset L y x ν) :
    PeriodicLattice.IsBlockOffset (FullSpace.projVertex L n k (i + 1) y)
      (FullSpace.projVertex L n k i x) ν := by apply _root_.YangMills.Construction.Tower.FieldProjection.isBlockOffset_projVertex <;> assumption
private abbrev permList (π : Equiv.Perm (Fin 4)) : List (Fin 4) := (List.finRange 4).map π
private abbrev enumList {S : Finset (Fin 4)} (σ : Fin S.card ≃ S) : List (Fin 4) :=
  (List.finRange S.card).map fun i => ((σ i : S) : Fin 4)
private theorem exists_enum_eq_filter (S : Finset (Fin 4)) (π : Equiv.Perm (Fin 4)) :
    ∃ σ : Fin S.card ≃ S, enumList σ = (permList π).filter (· ∈ S) := by apply _root_.YangMills.Construction.RunningCouplingSlope.NormalizedMeanAtOneProof.exists_enumList_eq_filter <;> assumption
private theorem stepsInOrder_filter {a : ℝ} (d : Fin 4 → ℤ) (S : Finset (Fin 4))
    (hS : ∀ μ, μ ∉ S → d μ = 0) (x : InfiniteLattice.LatticePoint a) (l : List (Fin 4)) :
    FullSpace.stepsInOrder d x l = FullSpace.stepsInOrder d x (l.filter (· ∈ S)) := by apply _root_.YangMills.SharedProofs.p61879 <;> assumption
private theorem stepsInOrder_perm_mem_contourSet {a a' : ℝ} (y : InfiniteLattice.LatticePoint a)
    (x : InfiniteLattice.LatticePoint a') (π : Equiv.Perm (Fin 4)) :
    FullSpace.stepsInOrder (FullSpace.cubeOffset L y x) (FullSpace.toFiner a' y)
        ((List.finRange 4).map π) ∈
      FullSpace.contourSet L y x := by
  obtain ⟨σ, hσ⟩ := exists_enum_eq_filter (FullSpace.offsetSupport L y x) π
  refine ⟨σ, ?_⟩
  show FullSpace.stepsInOrder (FullSpace.cubeOffset L y x) (FullSpace.toFiner a' y)
    (enumList σ) = _
  rw [hσ, ← stepsInOrder_filter]
  intro μ hμ
  by_contra h
  exact hμ (Finset.mem_filter.2 ⟨Finset.mem_univ _, h⟩)
private theorem linkHolonomy_eq_of_map {W : FullSpace.Edge L k i → Matrices.ComplexMatrix2}
    {V : Tower.Edge L n k i → Matrices.ComplexMatrix2} {Γ : List (FullSpace.Edge L k i)}
    (h : ∀ b ∈ Γ, W b = V (FullSpace.projEdge L n k i b)) :
    FullSpace.linkHolonomy W Γ =
      PeriodicLattice.pathHolonomy V (Γ.map (FullSpace.projEdge L n k i)) := by
  unfold FullSpace.linkHolonomy PeriodicLattice.pathHolonomy
  rw [List.map_map, List.map_congr_left h]
  rfl
theorem contourMeanAlongProjection_holds (hC : PeriodicLattice.BlockContoursAndCombs)
    (hB : Tower.FullSpace.CubesCorridorsPivotEdgesAndPaths)
    (hQ : Tower.EdgeProjectionProperties)
    (hS : Tower.ProjectionCarriesSetsStatement) :
    RunningCouplingSlope.ContourMeanAlongProjection := by
  intro L hL n k j hn hj c hc W V hWV
  have hL0 : 0 < L := by have := hL.2; omega
  have hk : 1 ≤ k := by omega
  have Q : FullSpace.ProjPreservesSets L n k j c := (hS L hL0 hL k hk n hn).2 j hj c hc
  have hq := (hQ L n k j hL hn hj.le).1
  have ends : ∀ b : FullSpace.Edge L k j,
      (FullSpace.projEdge L n k j b).source = FullSpace.projVertex L n k j b.initial ∧
        (FullSpace.projEdge L n k j b).target = FullSpace.projVertex L n k j b.terminal :=
    fun b => ⟨(hq b).1, (hq b).2.1⟩
  have hc1 := (hQ L n k (j + 1) hL hn hj).1 c
  obtain ⟨hpart, -, -, hpaths⟩ := hB L hL k (j + 1) 1 hk (by omega) hj le_rfl (by omega)
  have hblock : ∀ y : FullSpace.Vertex L k (j + 1), (y = c.initial ∨ y = c.terminal) →
      ∀ x ∈ FullSpace.cubeVertices L (Tower.meshAt L k j) y,
        ((FullSpace.projVertex L n k j x : Tower.Vertex L n k j) :
            PeriodicLattice.FourTorus L n) ∈
          PeriodicLattice.unitBlock (FullSpace.projVertex L n k (j + 1) y) := by
    rintro y (rfl | rfl) x hx
    · rw [← hc1.1, ← Q.cube_initial]
      exact ⟨_, hx, rfl⟩
    · rw [← hc1.2.1, ← Q.cube_terminal]
      exact ⟨_, hx, rfl⟩
  have hleg : ∀ y : FullSpace.Vertex L k (j + 1), (y = c.initial ∨ y = c.terminal) →
      ∀ x ∈ FullSpace.cubeVertices L (Tower.meshAt L k j) y, ∀ π : Equiv.Perm (Fin 4),
        (RunningCouplingSlope.FullLattice.contourLeg y x π).map (FullSpace.projEdge L n k j) =
          RunningCouplingSlope.contourLeg (FullSpace.projVertex L n k (j + 1) y)
            (FullSpace.projVertex L n k j x) π := by
    intro y hy x hx π
    have hw := isBlockOffset_of_isCubeOffset (n := n) (isCubeOffset_of_mem hx)
    have hd : PeriodicLattice.blockOffset (FullSpace.projVertex L n k (j + 1) y)
        (FullSpace.projVertex L n k j x) = FullSpace.cubeOffset L y x :=
      (hC L n k hL hn j hj _ _ (hblock y hy x hx)).1.unique
        (Classical.epsilon_spec (p := PeriodicLattice.IsBlockOffset _ _) ⟨_, hw⟩) hw
    unfold RunningCouplingSlope.FullLattice.contourLeg RunningCouplingSlope.contourLeg
    rw [map_projEdge_stepsInOrder ends, hd, toSublattice_projVertex hL0]
  have hlegin : ∀ y : FullSpace.Vertex L k (j + 1), (y = c.initial ∨ y = c.terminal) →
      ∀ x ∈ FullSpace.cubeVertices L (Tower.meshAt L k j) y, ∀ π : Equiv.Perm (Fin 4),
        ∀ b ∈ RunningCouplingSlope.FullLattice.contourLeg y x π,
          W b = V (FullSpace.projEdge L n k j b) := by
    intro y hy x hx π b hb
    refine hWV b ?_
    have hfam := stepsInOrder_perm_mem_contourSet (L := L) y x π
    have hs := hpaths.contour_vertex_mem y x hx _ hfam
    have h₁ := hs b.initial (Or.inr (Or.inr ⟨b, hb, Or.inl rfl⟩))
    have h₂ := hs b.terminal (Or.inr (Or.inr ⟨b, hb, Or.inr rfl⟩))
    rcases hy with rfl | rfl
    · exact ⟨Or.inl h₁, Or.inl h₂⟩
    · exact ⟨Or.inr h₁, Or.inr h₂⟩
  have htrans : ∀ x ∈ FullSpace.cubeVertices L (Tower.meshAt L k j) c.initial,
      FullSpace.shifted c x ∈ FullSpace.cubeVertices L (Tower.meshAt L k j) c.terminal := by
    intro x hx
    obtain ⟨ν, hb, he⟩ := hx
    refine ⟨ν, hb, ?_⟩
    show ((x + FullSpace.toFiner (Tower.meshAt L k j) (c.terminal - c.initial) :
      FullSpace.Vertex L k j) : InfiniteLattice.AmbientSpace) = _
    rw [AddSubgroup.coe_add, coe_toFiner hL0, he]
    simp only [AddSubgroup.coe_sub]
    abel
  have hcv : ∀ x ∈ FullSpace.cubeVertices L (Tower.meshAt L k j) c.initial,
      ∀ π : Equiv.Perm (Fin 4),
      RunningCouplingSlope.FullLattice.contourHolonomy W c x π =
        RunningCouplingSlope.contourHolonomy V (FullSpace.projEdge L n k (j + 1) c)
          (FullSpace.projVertex L n k j x) π := by
    intro x hx π
    unfold RunningCouplingSlope.FullLattice.contourHolonomy RunningCouplingSlope.contourHolonomy
    have hcr : ∀ b ∈ FullSpace.crossingPath c x, W b = V (FullSpace.projEdge L n k j b) := by
      intro b hb
      refine hWV b ⟨?_, ?_⟩
      · exact hpaths.crossing_vertex_mem c x hx b.initial
          (Or.inr (Or.inr ⟨b, hb, Or.inl rfl⟩))
      · exact hpaths.crossing_vertex_mem c x hx b.terminal
          (Or.inr (Or.inr ⟨b, hb, Or.inr rfl⟩))
    rw [linkHolonomy_eq_of_map (hlegin c.initial (Or.inl rfl) x hx π),
      hleg c.initial (Or.inl rfl) x hx π,
      linkHolonomy_eq_of_map hcr,
      show (FullSpace.crossingPath c x).map (FullSpace.projEdge L n k j) = _ from
        Q.crossingPath_eq x hx,
      linkHolonomy_eq_of_map (hlegin c.terminal (Or.inr rfl) _ (htrans x hx) π),
      hleg c.terminal (Or.inr rfl) _ (htrans x hx) π, Q.shifted_eq x hx, hc1.1, hc1.2.1]
  have hbij : BijOn (FullSpace.projVertex L n k j)
      (FullSpace.cubeVertices L (Tower.meshAt L k j) c.initial)
      (PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k j)
        (FullSpace.projEdge L n k (j + 1) c).source) := by
    refine ⟨fun x hx => ?_, fun x hx x' hx' h => ?_, fun x' hx' => ?_⟩
    · show ((FullSpace.projVertex L n k j x : Tower.Vertex L n k j) :
          PeriodicLattice.FourTorus L n) ∈
        PeriodicLattice.unitBlock (FullSpace.projEdge L n k (j + 1) c).source
      rw [← Q.cube_initial]
      exact ⟨_, hx, rfl⟩
    · exact Subtype.ext (Q.injOn_doubleCube (Or.inl hx) (Or.inl hx') (congrArg Subtype.val h))
    · have hx'' : (x' : PeriodicLattice.FourTorus L n) ∈
          PeriodicLattice.unitBlock (FullSpace.projEdge L n k (j + 1) c).source := hx'
      rw [← Q.cube_initial] at hx''
      obtain ⟨p, hp, he⟩ := hx''
      have hps : p ∈ (InfiniteLattice.latticeSubgroup (Tower.meshAt L k j) :
          Set InfiniteLattice.AmbientSpace) := by
        have hu := hpart.iUnion_cube
        have : p ∈ ⋃ y : FullSpace.Vertex L k (j + 1),
            FullSpace.cubeOfOrder L (Tower.meshAt L k j) 1 y :=
          mem_iUnion.2 ⟨c.initial, hp⟩
        exact hu ▸ this
      exact ⟨⟨p, hps⟩, hp, Subtype.ext he⟩
  unfold RunningCouplingSlope.FullLattice.contourMean RunningCouplingSlope.contourMean
  congr 1
  exact finsum_mem_eq_of_bijOn _ hbij fun x hx => Finset.sum_congr rfl fun π _ => hcv x hx π
end YangMills.Construction.RunningCouplingSlope.AlongProjection
end
