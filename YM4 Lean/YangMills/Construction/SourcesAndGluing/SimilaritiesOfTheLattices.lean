import YangMills.Construction.SourcesAndGluing.LatticeSimilarities
import Mathlib
set_option autoImplicit false
open MeasureTheory
noncomputable section
namespace YangMills.Construction
open TorusLifts
namespace SourcesAndGluing
open InfiniteLattice (AmbientSpace)
structure LatticeRescaling (D : GluingSetup) where
  exp : ℤ
  exp_nonneg : 0 ≤ exp
  exp_lt_K : exp < ((D.K : ℕ) : ℤ)
  base : AmbientSpace
  base_mem : base ∈ D.gridPoints
namespace LatticeRescaling
variable {D : GluingSetup} (Ψ : LatticeRescaling D)
def scaleExponent : ScaleExponent D where
  shift := Ψ.exp
  one_le_cutoff_sub := by have := Ψ.exp_lt_K; omega
  one_le_side_add := by have := Ψ.exp_nonneg; have := D.m.pos; omega
def toSpace (x : AmbientSpace) : AmbientSpace := (D.L : ℝ) ^ Ψ.exp • (x + Ψ.base)
def scaledBase : AmbientSpace := (D.L : ℝ) ^ Ψ.exp • Ψ.base
theorem scaledBase_mem : Ψ.scaledBase ∈ Ψ.scaleExponent.target.gridPoints := by
  obtain ⟨n, hn⟩ := Ψ.base_mem
  refine ⟨n, fun μ => ?_⟩
  have hmesh : Ψ.scaleExponent.target.mesh = (D.L : ℝ) ^ Ψ.exp * D.mesh :=
    (ScaledLatticeMotion.target_mesh (e := Ψ.scaleExponent)).trans
      (meshSize_shift_eq_zpow_mul ScaleExponent.L_pos rfl)
  rw [hmesh, scaledBase, Pi.smul_apply, hn μ, smul_eq_mul]
  ring
def toMotion : ScaledLatticeMotion Ψ.scaleExponent :=
  ⟨1, one_mem _, Ψ.scaledBase, Ψ.scaledBase_mem⟩
theorem toMotion_onSpace : Ψ.toMotion.onSpace = Ψ.toSpace := by
  funext x
  simp [ScaledLatticeMotion.onSpace, toMotion, scaledMotion, toSpace, scaledBase, scaleExponent,
    smul_add]
def toTorus : D.Torus → Ψ.scaleExponent.target.Torus := Ψ.toMotion.onTorus
def pull (U : Ψ.scaleExponent.target.GridField) : D.GridField :=
  Ψ.toMotion.pullField U
def pullTorus (U : Ψ.scaleExponent.target.PeriodicLink → Matrices.ComplexMatrix2) :
    D.PeriodicLink → Matrices.ComplexMatrix2 :=
  Ψ.toMotion.pullTorusField U
theorem onLink_initial (c : InfiniteLattice.Link D.mesh) :
    ((Ψ.toMotion.onLink c).initial : AmbientSpace) = Ψ.toSpace c.initial :=
  congrFun Ψ.toMotion_onSpace _
theorem onLink_terminal (c : InfiniteLattice.Link D.mesh) :
    ((Ψ.toMotion.onLink c).terminal : AmbientSpace) = Ψ.toSpace c.terminal :=
  congrFun Ψ.toMotion_onSpace _
def precompose {α : Type*} (A : D.GridField → α) :
    Ψ.scaleExponent.target.GridField → α :=
  A ∘ Ψ.pull
def precomposeTorus {α : Type*} (A : (D.PeriodicLink → Matrices.ComplexMatrix2) → α) :
    (Ψ.scaleExponent.target.PeriodicLink → Matrices.ComplexMatrix2) → α :=
  A ∘ Ψ.pullTorus
def pullInv :
    D.GridField → Ψ.scaleExponent.target.GridField :=
  haveI : Nonempty Ψ.scaleExponent.target.GridField := ⟨⟨fun _ => 1, fun _ => by simp⟩⟩
  Function.invFun Ψ.pull
def pushMeasure (ν : Measure D.GridField) :
    Measure Ψ.scaleExponent.target.GridField :=
  ν.map Ψ.pullInv
end LatticeRescaling
end SourcesAndGluing
end YangMills.Construction
end
