import YangMills.Construction.Lattice.GeometryOfASeparatedSequenceProof
import YangMills.Construction.Torus.CubeSetsBumpsCutOffsAndProductRule
import YangMills.Construction.Torus.DifferencesAndAveragesOnAGeneralTorusProof
import YangMills.Construction.Torus.GeometryOfCubesAndCutSequences
import YangMills.Construction.Torus.GreenIdentitiesAndBlockForm
import YangMills.Construction.Torus.TermsOfTheChangeOfTheSequence
import YangMills.Construction.Torus.ScalarProductsTransposesAndProjectionsOfASetting
import Mathlib
set_option autoImplicit false
open Set YangMills.Construction.TorusMetric
noncomputable section
namespace YangMills.Construction.GeneralTorus
namespace LocalChainChange
theorem levelSpacing_pos (D : ScaleData) (n : ℕ) : 0 < D.levelSpacing n := by apply _root_.YangMills.Construction.GeneralTorus.ChainStructureProof.levelSpacing_pos <;> assumption
variable {S : ℝ}
theorem torusSupNorm_le_of_forall {x : Torus4 S} {r : ℝ} (h : ∀ μ, ‖x μ‖ ≤ r) :
    torusSupNorm x ≤ r := by apply _root_.YangMills.Construction.SequenceGeometryProof.torusSupNorm_le_of_forall <;> assumption
theorem torusSupNorm_add_le (x y : Torus4 S) :
    torusSupNorm (x + y) ≤ torusSupNorm x + torusSupNorm y := by apply _root_.YangMills.Construction.SequenceGeometryProof.torusSupNorm_add_le <;> assumption
theorem self_mem_supCube {s : ℝ} (hs : 0 ≤ s) (y : Torus4 S) : y ∈ supCube s y := by apply _root_.YangMills.Construction.GeneralTorus.CubePartitions.self_mem_supCube <;> assumption
section Plaquettes
variable (D : ScaleData)
end Plaquettes
abbrev BondAtLevel (D : ScaleData) : Type := Σ n : Fin (D.lastLevel + 1), D.PosBond n
def meanAt (D : ScaleData) (s : BondAtLevel D) (F : D.BondField) : ℝ :=
  D.blockBondMean s.1 F s.2
def withChain (C : CubeGaugeSetting) (B : SeparatedChain C.data) : CubeGaugeSetting where
  data := C.data
  chain := B
  L_le_gapCount := C.L_le_gapCount
  choice := C.choice
  mass := C.mass
  mass_pos := C.mass_pos
  twelve_mul_L_le_blockCount := C.twelve_mul_L_le_blockCount
structure NearCube (C : CubeGaugeSetting) (Q : C.data.CubeIndex) (B : SeparatedChain C.data) :
    Prop where
  cutoff_eq_one : ∀ x ∈ ScaleData.scaledCube Q (4 / 3), ScaleData.cutoffFn Q x = 1
  cutoff_eq_zero : ∀ x, 5 / 3 * ScaleData.cubeScale Q ≤ torusSupNorm (x - Q.2) →
    ScaleData.cutoffFn Q x = 0
  bondSet_iff : ∀ b : C.data.BaseBond, (b.1.src : C.data.Space) ∈ ScaleData.scaledCube Q 2 →
    (b.1.tgt : C.data.Space) ∈ ScaleData.scaledCube Q 2 →
      (b ∈ C.bondSet ↔ b ∈ (withChain C B).bondSet)
  coarseBonds_iff : ∀ (m : Fin (C.data.lastLevel + 1)) (c : C.data.PosBond m),
    (c.1.src : C.data.Space) ∈ ScaleData.scaledCube Q 2 →
    (c.1.tgt : C.data.Space) ∈ ScaleData.scaledCube Q 2 →
      (c ∈ C.coarseBondsAt m ↔ c ∈ (withChain C B).coarseBondsAt m)
  support_subset : ∀ (m : Fin (C.data.lastLevel + 1)) (c : C.data.PosBond m),
    (c ∈ C.coarseBondsAt m ∨ c ∈ (withChain C B).coarseBondsAt m) →
    (ScaleData.bondSupport c ∩ ScaleData.scaledCube Q (5 / 3 + 1 / 12)).Nonempty →
      ScaleData.bondSupport c ⊆ ScaleData.scaledCube Q 2
  mean_local : BlockBondMeanIsLocal
section NearTheCube
variable {C : CubeGaugeSetting} {Q : C.data.CubeIndex} {B : SeparatedChain C.data}
end NearTheCube
end LocalChainChange
end YangMills.Construction.GeneralTorus
