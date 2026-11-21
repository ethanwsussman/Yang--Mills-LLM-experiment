import YangMills.Construction.Towers.BlockGaugesUnderTheDilation
import YangMills.Construction.Towers.BlocksOfATower
import YangMills.Construction.Towers.DilationCarriesObjectsAtAnIndexOfATower
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Tower.BlockGaugeScaling
theorem blockGaugeLift_eq_of_unique {L n k i : ℕ} (v : Vertex L n k (i + 1) → Matrices.ComplexMatrix2)
    (x : Vertex L n k i) (y : Vertex L n k (i + 1))
    (hy : (x : PeriodicLattice.FourTorus L n) ∈ PeriodicLattice.unitBlock y)
    (huniq : ∀ z : Vertex L n k (i + 1),
      (x : PeriodicLattice.FourTorus L n) ∈ PeriodicLattice.unitBlock z → z = y) :
    blockGaugeLift v x = v y := by
  have hsites : x ∈ PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k i) y := hy
  have hspec := Classical.epsilon_spec
    (p := fun z : Vertex L n k (i + 1) => x ∈ PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k i) z)
    ⟨y, hsites⟩
  have heq := huniq _ hspec
  unfold blockGaugeLift
  exact congrArg v heq
theorem blockGaugeLift_commutes_with_scaling (hBlocks : BlockStructure)
    (hObjects : ScalingPreservesObjectsAtLevel.Statement) :
    BlockGaugeLiftCommutesWithScaling := by
  intro L n k j hL hj hLs hn hj1 i hi v
  have hk : 1 ≤ k := hj1.trans hj
  have hFirst := (((hBlocks L k (i + 1) hLs hk (by omega) (by omega)).1 n hn).2.1).2.1
  have hSecond := (((hBlocks L j (i + 1) hLs hj1 (by omega) (by omega)).1
    (scaledExponent n k j) (Nat.add_pos_left hn _)).2.1).2.1
  funext x'
  obtain ⟨x, rfl⟩ := (scaleVertex (n := n) hL hj i).toEquiv.surjective x'
  obtain ⟨y, hy, huniq⟩ := hFirst x
  have hImage := ((hObjects L hL hLs k j hj hj1 (i + 1) (by omega)).1 n hn).refinedBlock_image 1
    (by omega) y
  have hMem : ((scaleVertex (n := n) hL hj i).toEquiv x :
      PeriodicLattice.FourTorus L (scaledExponent n k j)) ∈
      PeriodicLattice.unitBlock (scaleVertex (n := n) hL hj (i + 1) y) := by
    have h : scaling hL n k j (x : PeriodicLattice.FourTorus L n) ∈
        scaling hL n k j '' PeriodicLattice.refinedBlock 1 y := ⟨_, hy, rfl⟩
    rw [hImage] at h
    exact h
  obtain ⟨y', -, huniq'⟩ := hSecond ((scaleVertex (n := n) hL hj i).toEquiv x)
  rw [transportTotal_apply, blockGaugeLift_eq_of_unique v x y hy huniq,
    blockGaugeLift_eq_of_unique _ _ (scaleVertex (n := n) hL hj (i + 1) y) hMem
      (fun z hz => (huniq' z hz).trans (huniq' _ hMem).symm)]
  exact (transportTotal_apply (scaleVertex (n := n) hL hj (i + 1)).toEquiv v y).symm
end YangMills.Construction.Tower.BlockGaugeScaling
end
