import YangMills.Construction.Lattice.ClosedCubesOfTheCoarseSitesOfACubeProof
import YangMills.Construction.Lattice.GreenOperatorsOfCubesInLevelUnits
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.CubeCovering.RescaledGreen
open PeriodicLattice
section Scaling
variable {d N : ℕ} {s : Mesh N} {r : ℝ} {ι : Type}
theorem normAt_nonneg [Fintype ι] (f : MultiField d s ι) (x : GridPoint d s) :
    0 ≤ MultiField.normAt f x := Real.iSup_nonneg fun _ => abs_nonneg _
theorem multiField_maxNorm_nonneg [Fintype ι] (f : MultiField d s ι) : 0 ≤ MultiField.maxNorm f :=
  Real.iSup_nonneg fun _ => normAt_nonneg f _
theorem siteFun_maxNorm_nonneg (f : SiteFun d s) : 0 ≤ SiteFun.maxNorm f :=
  Real.iSup_nonneg fun _ => abs_nonneg _
theorem holderQuotientSup_nonneg (α : ℝ) (v : GridPoint d s → GridPoint d s → ℝ)
    (hv : ∀ x x', 0 ≤ v x x') : 0 ≤ holderQuotientSup s α v := by
  refine Real.sSup_nonneg ?_
  rintro t ⟨x, x', h0, -, rfl⟩
  exact mul_nonneg (Real.rpow_nonneg h0.le _) (hv x x')
theorem multiField_holderSemi_nonneg [Fintype ι] (α : ℝ) (f : MultiField d s ι) :
    0 ≤ MultiField.holderSemi α f :=
  holderQuotientSup_nonneg α _ fun _ _ => Real.iSup_nonneg fun _ => abs_nonneg _
theorem siteFun_holderSemi_nonneg (α : ℝ) (f : SiteFun d s) :
    0 ≤ SiteFun.holderSemi α f :=
  holderQuotientSup_nonneg α _ fun _ _ => abs_nonneg _
theorem normAt_smul [Fintype ι] {a : ℝ} (ha : 0 ≤ a) (f : MultiField d s ι) (x : GridPoint d s) :
    MultiField.normAt (a • f) x = a * MultiField.normAt f x := by
  unfold MultiField.normAt
  rw [Real.mul_iSup_of_nonneg ha]
  refine iSup_congr fun i => ?_
  rw [ScaledFun.smul_apply, abs_mul, abs_of_nonneg ha]
theorem maxNorm_smul [Fintype ι] {a : ℝ} (ha : 0 ≤ a) (f : MultiField d s ι) :
    MultiField.maxNorm (a • f) = a * MultiField.maxNorm f := by
  unfold MultiField.maxNorm
  rw [Real.mul_iSup_of_nonneg ha]
  exact iSup_congr fun x => normAt_smul ha f x
end Scaling
section FirstCase
variable {d N L j : ℕ} (S : Scales d L j N) (Λ' : Set (GridPoint d S.coarseMesh)) {r r' : ℝ}
end FirstCase
section SecondCase
open DirichletLaplacian
variable {d N : ℕ} {hN : 0 < N} {r : ℝ}
end SecondCase
section Geometry
open Set
variable {L m : ℕ}
theorem levelScale_pos (C : CubeData L m) (n : ℕ) : 0 < C.levelScale n := by apply _root_.YangMills.Construction.CubeCovering.CoarseSiteCubes.levelScale_pos <;> assumption
theorem convex_closedCube (c : Space) (a : ℝ) : Convex ℝ (CubeCovering.closedCube c a) := by
  intro x hx y hy α β hα hβ hαβ μ
  have h1 := abs_le.mp (hx μ)
  have h2 := abs_le.mp (hy μ)
  have e : (α • x + β • y) μ - c μ = α * (x μ - c μ) + β * (y μ - c μ) := by
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    linear_combination (c μ) * hαβ
  have hs : (α + β) * (a / 2) = a / 2 := by rw [hαβ, one_mul]
  rw [e, abs_le]
  constructor
  · nlinarith [mul_le_mul_of_nonneg_left h1.1 hα, mul_le_mul_of_nonneg_left h2.1 hβ]
  · nlinarith [mul_le_mul_of_nonneg_left h1.2 hα, mul_le_mul_of_nonneg_left h2.2 hβ]
variable {C : CubeData L m} {Q : Cube C}
theorem exists_cubeAround_mem (hL : 0 < L) (i : ℤ) (t : Fin 4 → ℝ) :
    ∃ y : PeriodicLattice.Site L m i,
      TorusMetric.torusProj (PeriodicLattice.torusSide L m) t ∈ PeriodicLattice.cubeAround y := by
  have hW : 0 < PeriodicLattice.meshSize L i := zpow_pos (by exact_mod_cast hL) _
  let n : Fin 4 → ℤ := fun μ => round (t μ / PeriodicLattice.meshSize L i)
  refine ⟨⟨fun μ => (((n μ : ℝ) * PeriodicLattice.meshSize L i : ℝ) :
    AddCircle (PeriodicLattice.torusSide L m)), n, fun μ => rfl⟩, ?_⟩
  let v : Fin 4 → ℝ := fun μ => t μ - n μ * PeriodicLattice.meshSize L i
  have hle : TorusMetric.torusSupNorm (TorusMetric.torusProj (PeriodicLattice.torusSide L m) v) ≤
      TorusMetric.supNormVec v := by
    refine csInf_le ⟨0, ?_⟩ ⟨v, rfl, rfl⟩
    rintro _ ⟨u, -, rfl⟩
    exact (abs_nonneg (u 0)).trans
      (Finset.le_sup' (fun μ => |u μ|) (Finset.mem_univ (0 : Fin 4)))
  change TorusMetric.torusSupNorm
    (TorusMetric.torusProj (PeriodicLattice.torusSide L m) v) ≤ _ at hle
  change TorusMetric.torusSupNorm (_ - _) ≤ PeriodicLattice.meshSize L i / 2
  have hv : TorusMetric.torusProj (PeriodicLattice.torusSide L m) t -
      (fun μ => (((n μ : ℝ) * PeriodicLattice.meshSize L i : ℝ) :
        AddCircle (PeriodicLattice.torusSide L m))) =
      TorusMetric.torusProj (PeriodicLattice.torusSide L m) v := funext fun μ => by
    simp only [Pi.sub_apply, TorusMetric.torusProj, v, AddCircle.coe_sub]
  erw [hv]
  refine hle.trans (Finset.sup'_le _ _ fun μ _ => ?_)
  have h := abs_sub_round (t μ / PeriodicLattice.meshSize L i)
  have e : v μ = PeriodicLattice.meshSize L i *
      (t μ / PeriodicLattice.meshSize L i - round (t μ / PeriodicLattice.meshSize L i)) := by
    simp only [v, n]
    field_simp
  rw [e, abs_mul, abs_of_pos hW]
  nlinarith
theorem unitScale_pos (Q : Cube C) : 0 < Q.unitScale := levelScale_pos C _
end Geometry
end YangMills.Construction.CubeCovering.RescaledGreen
