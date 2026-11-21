import YangMills.Construction.Lattice.WeightedDistanceOfASeparatedSequence
import YangMills.Construction.RunningCouplingSlope.CellsOfNeighbouringFineSites
import YangMills.Construction.Torus.GeometryAndFreeKernelOfATestPairProof
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
namespace RunningCouplingSlope
open Tower TorusMetric
section EuclidNorm
variable {S : ℝ}
private theorem torusEuclidNorm_add_le' (x y : Torus4 S) :
    torusEuclidNorm (x + y) ≤ torusEuclidNorm x + torusEuclidNorm y := by apply _root_.YangMills.Construction.TestPairs.torusEuclidNorm_add_le <;> assumption
private theorem torusEuclidNorm_neg' (x : Torus4 S) : torusEuclidNorm (-x) = torusEuclidNorm x := by apply _root_.YangMills.Construction.PeriodicLattice.IsometryInvariance.torusEuclidNorm_neg <;> assumption
private theorem torusEuclidNorm_le_two_mul (x : Torus4 S) (a : ℝ) (ha : 0 ≤ a) (h : ∀ μ, ‖x μ‖ ≤ a) :
    torusEuclidNorm x ≤ 2 * a := by
  rw [AmbientPoints.torusEuclidNorm_eq_sqrt]
  refine Real.sqrt_le_iff.2 ⟨by positivity, ?_⟩
  have hsq : ∀ μ, ‖x μ‖ ^ 2 ≤ a ^ 2 := fun μ => pow_le_pow_left₀ (norm_nonneg _) (h μ) 2
  rw [Fin.sum_univ_four]
  nlinarith [hsq 0, hsq 1, hsq 2, hsq 3]
abbrev _root_.YangMills.SharedProofs.p16188 := @torusEuclidNorm_le_two_mul
end EuclidNorm
variable {L n k : ℕ}
private theorem meshSize_coarsest (L k : ℕ) : PeriodicLattice.meshSize L (PeriodicLattice.levelDepth k k) = 1 := by
  simp [PeriodicLattice.meshSize, PeriodicLattice.levelDepth]
private theorem exists_coarse_cell (x : PeriodicLattice.Site L n (PeriodicLattice.levelDepth k 0)) :
    ∃ y : Tower.Vertex L n k k, (x : PeriodicLattice.FourTorus L n) ∈ PeriodicLattice.refinedBlock k y := by
  obtain ⟨m, hm⟩ := x.2
  set r : Fin 4 → ℝ := fun μ => (m μ : ℝ) * PeriodicLattice.meshSize L (PeriodicLattice.levelDepth k 0) with hr
  refine ⟨⟨fun μ => (((round (r μ) : ℤ) : ℝ) * PeriodicLattice.meshSize L (PeriodicLattice.levelDepth k k) : ℝ),
    ⟨fun μ => round (r μ), fun μ => rfl⟩⟩, ?_, ?_⟩
  · change torusSupNorm _ ≤ _
    rw [SeparatedSequence.torusSupNorm_le_iff]
    intro μ
    have hhalf : (1 / 2 : ℝ) ≤ PeriodicLattice.meshSize L (PeriodicLattice.levelDepth k k) / 2 := by
      rw [meshSize_coarsest]
    refine le_trans ?_ hhalf
    have e : ((x : PeriodicLattice.FourTorus L n) - fun μ => ((((round (r μ) : ℤ) : ℝ) *
        PeriodicLattice.meshSize L (PeriodicLattice.levelDepth k k) : ℝ) : AddCircle (PeriodicLattice.torusSide L n))) μ =
        ((r μ - round (r μ) : ℝ) : AddCircle (PeriodicLattice.torusSide L n)) := by
      simp only [Pi.sub_apply, hm μ, meshSize_coarsest, mul_one, hr, AddCircle.coe_sub]
    change ‖((x : PeriodicLattice.FourTorus L n) - _) μ‖ ≤ _
    refine (congrArg norm e).le.trans ?_
    exact (addCircle_norm_coe_le_abs _).trans (by simpa using abs_sub_round (r μ))
  · have e : PeriodicLattice.levelDepth k k + (k : ℤ) = PeriodicLattice.levelDepth k 0 := by
      simp [PeriodicLattice.levelDepth]
    rw [e]
    exact x.2
private theorem mem_fineVertexCell (x : PeriodicLattice.Site L n (PeriodicLattice.levelDepth k 0)) :
    (x : PeriodicLattice.FourTorus L n) ∈ PeriodicLattice.refinedBlock k (fineVertexCell (L := L) (n := n) (k := k) x) :=
  Classical.epsilon_spec (exists_coarse_cell x)
private theorem norm_sub_fineVertexCell_le (x : PeriodicLattice.Site L n (PeriodicLattice.levelDepth k 0)) (μ : Fin 4) :
    ‖((x : PeriodicLattice.FourTorus L n) - (fineVertexCell (L := L) (n := n) (k := k) x : PeriodicLattice.FourTorus L n)) μ‖ ≤ 1 / 2 := by
  have h := (mem_fineVertexCell x).1
  change torusSupNorm _ ≤ _ at h
  rw [SeparatedSequence.torusSupNorm_le_iff, meshSize_coarsest] at h
  exact h μ
theorem neighbouringFineVertexCells_holds : NeighbouringFineVertexCells := by
  intro L hL n k
  refine ⟨fun y y' => ?_, fun y y' y'' => ?_, mem_fineVertexCell, fun x μ => ?_⟩
  · unfold cellDist
    rw [← neg_sub, torusEuclidNorm_neg']
  · unfold cellDist
    have e : (y : PeriodicLattice.FourTorus L n) - y'' = (y - y' : PeriodicLattice.FourTorus L n) + (y' - y'') := by abel
    rw [e]
    exact torusEuclidNorm_add_le' _ _
  · unfold cellDist
    set y := fineVertexCell (L := L) (n := n) (k := k) x with hy
    set y' := fineVertexCell (L := L) (n := n) (k := k) (x + PeriodicLattice.unitStep L n _ μ) with hy'
    have hL1 : (1 : ℝ) ≤ L := by
      have := hL.2
      exact_mod_cast (by omega : 1 ≤ L)
    have hη : PeriodicLattice.meshSize L (PeriodicLattice.levelDepth k 0) ≤ 1 := by
      simp only [PeriodicLattice.meshSize, PeriodicLattice.levelDepth]
      have : (0 : ℤ) ≤ (k : ℤ) - ((0 : ℕ) : ℤ) := by simp
      exact zpow_le_one_of_nonpos₀ hL1 (by omega)
    have hη0 : 0 ≤ PeriodicLattice.meshSize L (PeriodicLattice.levelDepth k 0) := by
      unfold PeriodicLattice.meshSize
      positivity
    have hstep : ∀ ν, ‖((PeriodicLattice.unitStep L n _ μ : PeriodicLattice.Site L n (PeriodicLattice.levelDepth k 0)) : PeriodicLattice.FourTorus L n) ν‖ ≤ 1 := by
      intro ν
      by_cases h : ν = μ
      · subst h
        simp only [PeriodicLattice.unitStep, PeriodicLattice.pointOnAxis, Pi.single_eq_same]
        exact (addCircle_norm_coe_le_abs _).trans (by rwa [abs_of_nonneg hη0])
      · simp [PeriodicLattice.unitStep, PeriodicLattice.pointOnAxis, Pi.single_eq_of_ne h]
    have := torusEuclidNorm_le_two_mul (S := PeriodicLattice.torusSide L n)
      ((y : PeriodicLattice.FourTorus L n) - y') 2 (by norm_num) fun ν => ?_
    · linarith
    · have h1 := norm_sub_fineVertexCell_le (k := k) x ν
      have h2 := norm_sub_fineVertexCell_le (k := k) (x + PeriodicLattice.unitStep L n _ μ) ν
      have e : ((y : PeriodicLattice.FourTorus L n) - y') ν =
          (((x + PeriodicLattice.unitStep L n _ μ : PeriodicLattice.Site L n (PeriodicLattice.levelDepth k 0)) : PeriodicLattice.FourTorus L n) - y') ν -
            ((x : PeriodicLattice.FourTorus L n) - y) ν -
            ((PeriodicLattice.unitStep L n _ μ : PeriodicLattice.Site L n (PeriodicLattice.levelDepth k 0)) : PeriodicLattice.FourTorus L n) ν := by
        simp only [AddSubgroup.coe_add, Pi.sub_apply, Pi.add_apply]
        abel
      rw [e]
      refine (norm_sub_le _ _).trans ?_
      have h3 := norm_sub_le
        ((((x + PeriodicLattice.unitStep L n _ μ : PeriodicLattice.Site L n (PeriodicLattice.levelDepth k 0)) : PeriodicLattice.FourTorus L n) - y' : PeriodicLattice.FourTorus L n) ν)
        (((x : PeriodicLattice.FourTorus L n) - y) ν)
      linarith [hstep ν]
end RunningCouplingSlope
end YangMills.Construction
end
