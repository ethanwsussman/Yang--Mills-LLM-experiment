import YangMills.Construction.Lattice.PositionsNumbersNormsAndTheDistanceOfAFrameProof
import YangMills.Construction.Lattice.CubesOfASeparatedSequence
import YangMills.Construction.SeparatedSequences.BasePointIsThatOfTheOperatorsAndTheFootProof
import YangMills.Construction.SeparatedSequences.PartitionsCubesExpansionsAndTheTriangleInequalityProof
import YangMills.Construction.SeparatedSequences.TopsOfTheBareSitesNearATop
import Mathlib
set_option autoImplicit false
namespace YangMills.Construction
open Set PeriodicLattice PeriodicLattice.DirichletOperators TorusMetric CubeCovering
noncomputable section
namespace SeparatedClasses
namespace NearApex
theorem thirteen_le_L (C : ClassData) : (13 : ℝ) ≤ C.L := by
  exact_mod_cast C.isAdmissible.2
theorem L_pos (C : ClassData) : (0 : ℝ) < C.L := by apply _root_.YangMills.Construction.SeparatedClasses.AnchorAgreementProof.cast_L_pos <;> assumption
theorem memberAt_eq {C : ClassData} {Ω : ℕ → Set C.Point} (hΩ : Ω ∈ C.separatedClass) (n : ℕ) :
    C.memberAt Ω n = Ω n := by apply _root_.YangMills.Construction.SeparatedClasses.BlockStructureProof.memberAt_eq <;> assumption
theorem supDist_comm (C : ClassData) (a b : C.Point) : C.supDist a b = C.supDist b a := by
  have h : ∀ a b : C.Point, torusSupNorm (a - b) ≤ torusSupNorm (b - a) := fun a b =>
    (SeparatedSequence.torusSupNorm_le_iff _ _).2 fun μ => by
      have := (SeparatedSequence.torusSupNorm_le_iff (b - a) _).1 le_rfl μ
      rwa [Pi.sub_apply, norm_sub_rev, ← Pi.sub_apply] at this
  simp only [ClassData.supDist]
  rw [le_antisymm (h a b) (h b a)]
variable {L m : ℕ}
end NearApex
end SeparatedClasses
end
end YangMills.Construction
