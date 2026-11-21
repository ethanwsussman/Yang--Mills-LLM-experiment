import YangMills.Construction.Lattice.BondsPathsAndAveragesOfADoubleBlock
import YangMills.Construction.Lattice.CoarseBlockCentres
import YangMills.Construction.Lattice.PositiveOneOfABondAndItsReverse
import YangMills.Construction.Lattice.RealAverageIsDefinedAtInnerBonds
import YangMills.Construction.Torus.CompressionOfTheCutOperatorToACubeProof
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.PeriodicLattice
open Set TorusMetric
variable {L m K : ℕ}
theorem torusSupNorm_zero_le {S r : ℝ} (hr : 0 ≤ r) : _root_.YangMills.Construction.TorusMetric.torusSupNorm (0 : Torus4 S) ≤ r := by apply _root_.YangMills.Construction.GeneralTorus.CubeGreenCompressionProof.torusSupNorm_zero_le <;> assumption
theorem site_mem_cubeAtLevel (hL : 0 < L) {q : ℕ} (y : SiteAtLevel L m K q) :
    (y : FourTorus L m) ∈ cubeAtLevel y := by
  have hs : 0 ≤ meshSize L (levelDepth K q) / 2 := by
    have : 0 < meshSize L (levelDepth K q) := zpow_pos (by exact_mod_cast hL) _
    positivity
  change _root_.YangMills.Construction.TorusMetric.torusSupNorm ((y : FourTorus L m) - (y : FourTorus L m)) ≤ meshSize L (levelDepth K q) / 2
  rw [sub_self]
  exact torusSupNorm_zero_le hs
theorem realAverageDefinedAtInnerBonds_holds
    (hCentres : CoarseCentreProperties)
    (hDouble : DoubleBlockStructure.Statement)
    (hOrient : PositiveOrientationOfBondAndOpposite) :
    RealAverageDefinedAtInnerBonds := by
  intro L m K hL hm j hj X hX U hU c hc
  have hK : 0 < K := by omega
  have hL0 : 0 < L := by
    have := hL.2
    omega
  have hUnit : ∀ y : SiteAtLevel L m K (j + 1), (y : FourTorus L m) ∈ X → unitBlock y ⊆ X := by
    intro y hy
    obtain ⟨h1, -, -, -, -, h6⟩ := hCentres L m K hL hm hK (j + 1) (j + 1) le_rfl hj
    have hcentre := ((h1 y).2 y).1 (site_mem_cubeAtLevel hL0 y)
    have hsub := (h6 X hX y hy).1
    rw [← hcentre] at hsub
    exact fun z hz => hsub hz.1
  have hD : bondDoubleBlock c ⊆ X := union_subset (hUnit _ hc.1) (hUnit _ hc.2)
  have hP : (bondsInDoubleBlock c : Set (BondAtLevel L m K j)) ⊆ bondsInside X :=
    fun b hb => ⟨hD hb.1, hD hb.2⟩
  have hkinds := (hDouble L m K j hL hm hj c).1
  have hW : onSetElseOne (bondsInDoubleBlock c) U ∈ gaugeFieldsAtLevel L m K j :=
    extendByOne_mem_compactGaugeFields hkinds.2.2.1
      ⟨fun b hb => hU.1 b (hP hb), fun b hb => hU.2 b (hP hb)⟩
  have hWU : ∀ b ∈ (bondsInDoubleBlock c : Set (BondAtLevel L m K j)),
      onSetElseOne (bondsInDoubleBlock c) U b = U b := fun b hb => if_pos hb
  intro average
  refine ⟨hP, ⟨_, hW, hWU⟩, fun V hV hVU => ?_⟩
  have hread : ∀ d : BondAtLevel L m K (j + 1), d.IsPositivelyOriented →
      (bondsInDoubleBlock d : Set (BondAtLevel L m K j)) = bondsInDoubleBlock c →
      blockAverage (Averaging.smoothingRadius L) (onSetElseOne (bondsInDoubleBlock c) U) d =
        blockAverage (Averaging.smoothingRadius L) V d := by
    intro d hd hdc
    refine ((hDouble L m K j hL hm hj d).2.2.2.2 hd _ hW _ hV fun b hb => ?_).2.2
    rw [hdc] at hb
    rw [hWU b hb, hVU b hb]
  change blockAverage (Averaging.smoothingRadius L) (onSetElseOne (bondsInDoubleBlock c) U) c =
    blockAverage (Averaging.smoothingRadius L) V c
  rcases (hOrient L m K hL hm hK j hj c).2.1 with ⟨hpos, -⟩ | ⟨hneg, hnot⟩
  · exact hread c hpos rfl
  · have hrev := hread c.opposite hneg hkinds.2.2.2.1
    simp only [blockAverage, if_pos hneg] at hrev
    simp only [blockAverage, if_neg hnot, hrev]
end YangMills.Construction.PeriodicLattice
