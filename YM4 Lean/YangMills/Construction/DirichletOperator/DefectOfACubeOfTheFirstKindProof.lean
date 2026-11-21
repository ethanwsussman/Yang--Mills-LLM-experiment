import YangMills.Construction.DirichletOperator.ChangedLongitudinalSourceAtTheCellsOfACubeProof
import YangMills.Construction.DirichletOperator.CommutatorOfTheLongitudinalOperatorOfACubeProof
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.FirstTypeDefect
open YangMills.Construction.Dirichlet YangMills.Construction.Torus YangMills.Construction.RegionSequence YangMills.Construction.RegionSequence.NestedRegions YangMills.Construction.PartitionCubes
theorem supNorm_torusProj_le {S : ℝ} (w : Fin 4 → ℝ) : supNorm (torusProj 4 S w) ≤ ‖w‖ := by apply _root_.YangMills.Construction.PartitionCubes.LocalTorusOperators.supNorm_proj_le <;> assumption
theorem supNorm_zero_le {S : ℝ} : supNorm (0 : PeriodicTorus 4 S) ≤ 0 := by apply _root_.YangMills.Construction.PartitionCubes.LocalTorusOperators.supNorm_zero_le <;> assumption
theorem torusProj_sub {S : ℝ} (u w : Fin 4 → ℝ) :
    torusProj 4 S (u - w) = torusProj 4 S u - torusProj 4 S w := by apply _root_.YangMills.Construction.PartitionCubes.CubeTorusBonds.torusProj_sub <;> assumption
theorem torusProj_neg {S : ℝ} (u : Fin 4 → ℝ) : torusProj 4 S (-u) = -torusProj 4 S u := by apply _root_.YangMills.Construction.PartitionCubes.TorusTransfer.torusProj_neg <;> assumption
theorem torusProj_zero {S : ℝ} : torusProj 4 S 0 = 0 := by apply _root_.YangMills.Construction.CubeCommutator.torusProj_zero <;> assumption
theorem norm_piSingle_le {ξ : ℝ} (hξ : 0 ≤ ξ) (ν : Fin 4) : ‖(Pi.single ν ξ : Fin 4 → ℝ)‖ ≤ ξ := by apply _root_.YangMills.Construction.PartitionCubes.LocalTorusOperators.norm_pi_single_le <;> assumption
section Adjoint
variable (𝒯 : NestedRegions)
theorem finite_fineSite : Finite 𝒯.FineSite := by apply _root_.YangMills.Construction.RegionSequence.AvgOpWeightSum.finite_fineSite <;> assumption
variable {𝒯}
theorem innerSum_comm (f g : 𝒯.FineSite → ℝ) : innerSum f g = innerSum g f := by apply _root_.YangMills.Construction.RegionSequence.GradientAdjointsOnTorus.innerSum_comm <;> assumption
theorem bondInner_eq_sum_comp (A B : 𝒯.FineBond → ℝ) :
    bondInner A B = ∑ ν, innerSum (comp A ν) (comp B ν) := by
  have := finite_fineSite 𝒯
  let e : 𝒯.FineBond ≃ 𝒯.FineSite × Fin 4 :=
    ⟨fun b => (b.source, b.dir), fun p => ⟨p.1, p.2⟩, fun _ => rfl, fun _ => rfl⟩
  let _ := Fintype.ofFinite 𝒯.FineSite
  let _ : Fintype 𝒯.FineBond := Fintype.ofEquiv _ e.symm
  simp only [bondInner, innerSum, finsum_eq_sum_of_fintype, comp]
  rw [← Finset.mul_sum]
  congr 1
  rw [Fintype.sum_equiv e (fun b => A b * B b) (fun p => A ⟨p.1, p.2⟩ * B ⟨p.1, p.2⟩) (fun b => rfl),
    Fintype.sum_prod_type_right]
theorem innerSum_sum_left (f : Fin 4 → 𝒯.FineSite → ℝ) (u : 𝒯.FineSite → ℝ) :
    innerSum (fun x => ∑ ν, f ν x) u = ∑ ν, innerSum (f ν) u := by
  have := finite_fineSite 𝒯
  let _ := Fintype.ofFinite 𝒯.FineSite
  simp only [innerSum, finsum_eq_sum_of_fintype, Finset.sum_mul, ← Finset.mul_sum]
  rw [Finset.sum_comm]
end Adjoint
section Operators
variable {𝒯 : NestedRegions}
end Operators
section Cube
variable {𝒮 : NestedRegions} {M : ℕ}
theorem scale_zero : 𝒮.scale 0 = 𝒮.ξ := by apply _root_.YangMills.Construction.PartitionCubes.CubeTorusAveraging.scale_zero <;> assumption
theorem thicken_mono (Q : LevelCube 𝒮 M) {a b : ℝ} (hab : a ≤ b) : Q.thicken a ⊆ Q.thicken b := by apply _root_.YangMills.Construction.CubeAdjointDefect.LongChangeAtCells.thicken_mono' <;> assumption
variable {Q : LevelCube 𝒮 M} {A : 𝒮.FineBond → ℝ}
end Cube
end YangMills.Construction.FirstTypeDefect
