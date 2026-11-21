import YangMills.Construction.Lattice.ActionOfABareGaugeTransformation
import YangMills.Construction.Lattice.GeometryOfASeparatedSequenceProof
import YangMills.Construction.Lattice.LatticesOfATorusAndTheProductTopologyOfConfigurations
import YangMills.Construction.RunningCouplingSlope.CellsOfABlockAreNear
import YangMills.Construction.RunningCouplingSlope.CellsOfNeighbouringFineSitesProof
import YangMills.Construction.RunningCouplingSlope.TopBondsAndTheirBlocks
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.RunningCouplingSlope
open Tower TorusMetric
namespace CellsOfBlocks
private theorem torusEuclidNorm_le_two_mul {S : ℝ} (x : Torus4 S) (a : ℝ) (ha : 0 ≤ a) (h : ∀ μ, ‖x μ‖ ≤ a) :
    torusEuclidNorm x ≤ 2 * a := by apply _root_.YangMills.SharedProofs.p16188 <;> assumption
variable {L n k : ℕ}
private theorem meshSize_top (L k : ℕ) : PeriodicLattice.meshSize L (PeriodicLattice.levelDepth k k) = 1 := by
  simp [PeriodicLattice.meshSize, PeriodicLattice.levelDepth]
private theorem meshSize_le_one (hL : Conventions.IsAdmissibleBlockingFactor L) {m : ℕ} (hm : m ≤ k) :
    PeriodicLattice.meshSize L (PeriodicLattice.levelDepth k m) ≤ 1 := by
  have hL1 : (1 : ℝ) ≤ L := by
    have := hL.2
    exact_mod_cast (by omega : 1 ≤ L)
  simp only [PeriodicLattice.meshSize, PeriodicLattice.levelDepth]
  exact zpow_le_one_of_nonpos₀ hL1 (by omega)
private theorem meshSize_nonneg (m : ℤ) : 0 ≤ PeriodicLattice.meshSize L m := by apply _root_.YangMills.Construction.SequenceGeometryProof.meshSize_nonneg' <;> assumption
private theorem norm_sub_cell_le_half (hc : NeighbouringFineVertexCells)
    (hL : Conventions.IsAdmissibleBlockingFactor L) {m : ℕ} (x : Vertex L n k m) (μ : Fin 4) :
    ‖((x : PeriodicLattice.FourTorus L n) - (levelVertexCell x : PeriodicLattice.FourTorus L n)) μ‖ ≤ 1 / 2 := by
  have hpos : 0 < L := by
    have := hL.2
    omega
  have h := ((hc L hL n k).2.2.1 (x.toSublattice (PeriodicLattice.levelDepth k 0))).1
  change torusSupNorm _ ≤ _ at h
  rw [SeparatedSequence.torusSupNorm_le_iff, meshSize_top] at h
  have e := PeriodicLattice.coe_toSublattice_finest hpos x
  have := h μ
  rw [e] at this
  exact this
private theorem cellDist_le_of_coord_le (hc : NeighbouringFineVertexCells)
    (hL : Conventions.IsAdmissibleBlockingFactor L) {i m : ℕ} (a : Vertex L n k i) (b : Vertex L n k m) {w : ℝ}
    (hw : 0 ≤ w) (h : ∀ μ, ‖((a : PeriodicLattice.FourTorus L n) - b) μ‖ ≤ w) :
    cellDist (levelVertexCell a) (levelVertexCell b) ≤ 2 * (w + 1) := by
  refine torusEuclidNorm_le_two_mul _ _ (by positivity) fun μ => ?_
  have h1 := norm_sub_cell_le_half (k := k) hc hL a μ
  have h2 := norm_sub_cell_le_half (k := k) hc hL b μ
  have e : ((levelVertexCell a : PeriodicLattice.FourTorus L n) - levelVertexCell b) μ =
      ((a : PeriodicLattice.FourTorus L n) - b) μ -
        ((a : PeriodicLattice.FourTorus L n) - levelVertexCell a) μ +
        ((b : PeriodicLattice.FourTorus L n) - levelVertexCell b) μ := by
    simp only [Pi.sub_apply]
    abel
  rw [e]
  have h3 := norm_add_le (((a : PeriodicLattice.FourTorus L n) - b) μ -
    ((a : PeriodicLattice.FourTorus L n) - levelVertexCell a) μ)
    (((b : PeriodicLattice.FourTorus L n) - levelVertexCell b) μ)
  have h4 := norm_sub_le (((a : PeriodicLattice.FourTorus L n) - b) μ)
    (((a : PeriodicLattice.FourTorus L n) - levelVertexCell a) μ)
  have := h μ
  linarith
abbrev _root_.YangMills.SharedProofs.p26872 := @cellDist_le_of_coord_le
private theorem norm_unitStep_le_one (hL : Conventions.IsAdmissibleBlockingFactor L) {m : ℕ} (hm : m ≤ k) (μ ν : Fin 4) :
    ‖((PeriodicLattice.unitStep L n (PeriodicLattice.levelDepth k m) μ : Vertex L n k m) :
      PeriodicLattice.FourTorus L n) ν‖ ≤ 1 := by
  by_cases h : ν = μ
  · subst h
    simp only [PeriodicLattice.unitStep, PeriodicLattice.pointOnAxis, Pi.single_eq_same]
    refine (addCircle_norm_coe_le_abs _).trans ?_
    rw [abs_of_nonneg (meshSize_nonneg _)]
    exact meshSize_le_one hL hm
  · simp [PeriodicLattice.unitStep, PeriodicLattice.pointOnAxis, Pi.single_eq_of_ne h]
end CellsOfBlocks
open CellsOfBlocks in
theorem cellDistBlockBounds_of_neighbouringFineVertexCells (hc : NeighbouringFineVertexCells)
    (ht : TopEdgesAndCubes) : CellDistBlockBounds := by
  intro L hL n k hn hk
  refine ⟨fun y y' => ?_, (ht L hL n k hn hk).1, (hc L hL n k).1, (hc L hL n k).2.1,
    fun m hm y x hx => ?_, fun m hm b => ?_⟩
  · unfold cellDist
    rw [AmbientPoints.torusEuclidNorm_eq_sqrt]
    exact Real.sqrt_nonneg _
  · have h := cellDist_le_of_coord_le (k := k) hc hL x y (w := 1 / 2) (by norm_num) fun μ => ?_
    · linarith
    · have h1 := hx.1
      change torusSupNorm _ ≤ _ at h1
      rw [SeparatedSequence.torusSupNorm_le_iff] at h1
      have h2 := h1 μ
      have h3 := meshSize_le_one (k := k) hL (m := m + 1) hm
      linarith
  · have h := cellDist_le_of_coord_le (k := k) hc hL b.source b.target (w := 1) (by norm_num) fun μ => ?_
    · linarith
    · rcases PeriodicLattice.Bond.positive_or_opposite_positive b with hb | hb
      · obtain ⟨ν, hν⟩ := hb
        have e : (b.source : PeriodicLattice.FourTorus L n) - b.target =
            -((PeriodicLattice.unitStep L n (PeriodicLattice.levelDepth k m) ν : Vertex L n k m) :
              PeriodicLattice.FourTorus L n) := by
          rw [← hν]
          push_cast
          abel
        rw [e, Pi.neg_apply, norm_neg]
        exact norm_unitStep_le_one hL hm ν μ
      · obtain ⟨ν, hν⟩ := hb
        have e : (b.source : PeriodicLattice.FourTorus L n) - b.target =
            ((PeriodicLattice.unitStep L n (PeriodicLattice.levelDepth k m) ν : Vertex L n k m) :
              PeriodicLattice.FourTorus L n) := by
          rw [← hν]
          rfl
        rw [e]
        exact norm_unitStep_le_one hL hm ν μ
end YangMills.Construction.RunningCouplingSlope
end
