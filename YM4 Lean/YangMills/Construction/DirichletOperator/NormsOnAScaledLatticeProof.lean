import YangMills.Construction.DirichletOperator.BondsCarriedToTheTorusOfACubeProof
import YangMills.Construction.DirichletOperator.DifferencesOnAScaledLatticeProof
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.BareDilation.DilatedNorms
section TorusLengths
variable {S : ℝ}
theorem lOneNorm_eq_sum_norm (p : Torus.PeriodicTorus 4 S) : Torus.lOneNorm p = ∑ μ, ‖p μ‖ := by apply _root_.YangMills.Construction.PartitionCubes.TorusTransfer.lOneNorm_eq_sum_norm <;> assumption
theorem supNorm_eq_norm (p : Torus.PeriodicTorus 4 S) : Torus.supNorm p = ‖p‖ := by apply _root_.YangMills.Construction.PartitionCubes.CubeTorusAveraging.supNorm_eq_norm <;> assumption
end TorusLengths
section FiniteSuprema
end FiniteSuprema
section DilatedHolder
variable {N : ℕ} {s : PeriodicLattice.Mesh N} {r : ℝ}
end DilatedHolder
section NearbySites
variable {L j N : ℕ}
end NearbySites
section Pullback
variable {L j N : ℕ} {𝒯 : RegionSequence.NestedRegions} {S : PeriodicLattice.Scales 4 L j N} {r : ℝ}
variable (R : DilationData 𝒯 S r)
def bondEquiv : Fin 4 × PeriodicLattice.DilatedSite 4 S.fineMesh r ≃ 𝒯.FineBond where
  toFun q := ⟨R.fineSiteEquiv q.2, q.1⟩
  invFun b := (b.dir, R.fineSiteEquiv.symm b.source)
  left_inv q := by simp
  right_inv b := by
    cases b
    simp
instance dilatedSite_nonempty : Nonempty (PeriodicLattice.DilatedSite 4 S.fineMesh r) := ⟨⟨0⟩⟩
include R in
theorem finite_fineBond : Finite 𝒯.FineBond := Finite.of_equiv _ (bondEquiv R)
end Pullback
end YangMills.Construction.BareDilation.DilatedNorms
