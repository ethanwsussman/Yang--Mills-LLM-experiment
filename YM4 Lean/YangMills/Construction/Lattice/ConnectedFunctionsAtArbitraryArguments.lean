import YangMills.Construction.Lattice.ObservablesAndTestNorms
import YangMills.Construction.ReflectionPositivity.ReflectionsMirrorsAndSlabsAtOneCutoff
import Mathlib
set_option autoImplicit false
open MeasureTheory
noncomputable section
namespace YangMills.Construction
namespace ConnectedFunctions
def markPart {X : Type*} (h : X → ℂ) (b : Fin 2) : X → ℝ :=
  fun x => if b = 0 then (h x).re else (h x).im
def markWeight {J : Type*} [Fintype J] (b : J → Fin 2) : ℕ := ∑ l, (b l : ℕ)
def IsRealValued {X : Type*} (h : X → ℂ) : Prop := ∀ x, (h x).im = 0
structure CouplingData extends Conventions.StandingParameters where
  coupling : ℝ
  coupling_pos : 0 < coupling
namespace CouplingData
variable (D : CouplingData)
def withDir (μ : Fin 4) : ReflectionPositivity.CutoffMirrors.MirrorData :=
  { D.toStandingParameters with coupling := D.coupling, coupling_pos := D.coupling_pos, dir := μ }
def proj (y : Fin 4 → ℝ) : D.Torus :=
  TorusMetric.torusProj (PeriodicLattice.torusSide D.L D.m) y
def IsC1 (h : D.Torus → ℝ) : Prop := ContDiff ℝ 1 (h ∘ D.proj)
abbrev Config : Type :=
  PeriodicLattice.Bond D.L D.m ((D.K : ℕ) : ℤ) → Matrices.ComplexMatrix2
def obs (h : D.Torus → ℂ) : D.Config → ℂ := PeriodicLattice.smearedObservable h
def expect (F : D.Config → ℂ) : ℂ :=
  PeriodicLattice.gibbsExpectation D.L D.m D.K D.coupling F
def centred (h : D.Torus → ℂ) : D.Config → ℂ :=
  fun U => D.obs h U - D.expect (D.obs h)
variable {n : ℕ}
def cumulantReal (f : Fin n → D.Torus → ℝ) : ℂ :=
  PeriodicLattice.gibbsCumulant D.L D.m D.K D.coupling
    fun i U => PeriodicLattice.smearedObservable (f i) U
def markSum (f : Fin n → D.Torus → ℂ) : ℂ :=
  ∑ b : Fin n → Fin 2, Complex.I ^ markWeight b *
    D.cumulantReal fun i => markPart (f i) (b i)
open Classical in
def connected (f : Fin n → D.Torus → ℂ) : ℂ :=
  if ∀ i, IsRealValued (f i) then D.cumulantReal fun i x => (f i x).re
  else D.markSum f
theorem connected_ofReal (f : Fin n → D.Torus → ℝ) :
    D.connected (fun i x => (f i x : ℂ)) = D.cumulantReal f := by
  have h : ∀ i, IsRealValued fun x => ((f i x : ℝ) : ℂ) := fun i x => Complex.ofReal_im _
  simp [connected, h]
theorem connected_of_not_real (f : Fin n → D.Torus → ℂ)
    (h : ¬ ∀ i, IsRealValued (f i)) : D.connected f = D.markSum f := by
  simp [connected, h]
end CouplingData
end ConnectedFunctions
end YangMills.Construction
