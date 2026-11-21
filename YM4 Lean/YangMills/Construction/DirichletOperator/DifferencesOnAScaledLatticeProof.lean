import YangMills.Construction.DirichletOperator.CornerBoundsOnTheToriOfTheCubesProof
import YangMills.Construction.DirichletOperator.CurlFormOnAScaledLatticeProof
import Mathlib
set_option autoImplicit false
open Set
open YangMills.Construction.RegionSequence YangMills.Construction.RegionSequence.NestedRegions
noncomputable section
namespace YangMills.Construction
namespace PeriodicLattice
section Adjoint
variable {d N : ℕ} (s : Mesh N) (ι : Type) [Fintype ι]
end Adjoint
section Dilated
variable {d N : ℕ} {s : Mesh N} {r : ℝ} {ι : Type}
end Dilated
end PeriodicLattice
namespace BareDilation
namespace DilationData
variable {L j N : ℕ} {𝒯 : NestedRegions} {S : PeriodicLattice.Scales 4 L j N} {r : ℝ}
variable (R : DilationData 𝒯 S r)
def bondSlice (F : 𝒯.FineBond → ℝ) (μ : Fin 4) : PeriodicLattice.SiteFun 4 S.fineMesh :=
  PeriodicLattice.ScaledFun.ofMap fun y => F ⟨R.fineSiteEquiv ⟨y⟩, μ⟩
def bondEquiv : Fin 4 × PeriodicLattice.DilatedSite 4 S.fineMesh r ≃ 𝒯.FineBond where
  toFun q := ⟨R.fineSiteEquiv q.2, q.1⟩
  invFun b := (b.dir, R.fineSiteEquiv.symm b.source)
  left_inv q := by simp
  right_inv b := by simp
def indexPairEquiv : (Fin 2 → Fin 4) × (Fin 4 × PeriodicLattice.DilatedSite 4 S.fineMesh r) ≃
    (Fin 4 × Fin 4 × Fin 4) × PeriodicLattice.DilatedSite 4 S.fineMesh r where
  toFun q := ((q.1 0, q.1 1, q.2.1), q.2.2)
  invFun q := (![q.1.1, q.1.2.1], (q.1.2.2, q.2))
  left_inv q := by
    obtain ⟨ν, μ, x⟩ := q
    have hν : ![ν 0, ν 1] = ν := by
      funext i
      fin_cases i <;> rfl
    simp [hν]
  right_inv q := rfl
end DilationData
end BareDilation
end YangMills.Construction
