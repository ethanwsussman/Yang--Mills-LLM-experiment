import YangMills.Construction.Lattice.DecayingKernels
import YangMills.Construction.Lattice.LocalizedDecayBounds
import YangMills.Construction.Lattice.TwoScaleOperatorDefs
import YangMills.Construction.LatticeFields.CompressedGreenBounds
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.PeriodicLattice
open ScaledFun
def singleScaleCoerciveConst (d : ℕ) : ℝ := LatticeFields.coerciveConst d 1
def singleScaleDecayConst (d : ℕ) : ℝ := LatticeFields.greenDecayConst d 1
def gaugeProjDecayPrefactor (d : ℕ) : ℝ :=
  46 * (d : ℝ) ^ 2 * (LatticeFields.blockMomentLowerBound d)⁻¹
def gaugeProjDecayConst (d : ℕ) : ℝ :=
  LatticeFields.blockMomentLowerBound d / (260 * ((d : ℝ) + 1) * (d : ℝ) ^ 3)
def localBoundsRate (d : ℕ) : ℝ :=
  1 / 2 * min (singleScaleDecayConst d) (gaugeProjDecayConst d)
variable {d N : ℕ}
section SiteSets
variable {s : Mesh N} {ι : Type}
def siteSetDist (U U' : Set (GridPoint d s)) : ℝ :=
  sInf {t | ∃ x ∈ U, ∃ x' ∈ U', t = taxicabDist (x : Torus d N) x'}
open Classical in
def siteIndicator (U : Set (GridPoint d s)) : SiteFun d s :=
  ofMap fun x => if x ∈ U then 1 else 0
def SiteFun.restrictTo (U : Set (GridPoint d s)) (f : SiteFun d s) : SiteFun d s :=
  ofMap fun x => siteIndicator U x * f x
def MultiField.restrictTo (U : Set (GridPoint d s)) (f : MultiField d s ι) : MultiField d s ι :=
  MultiField.mulLeft (siteIndicator U) f
def maxBall (s : Mesh N) (r : ℝ) (u : Torus d N) : Set (GridPoint d s) :=
  {x | maxDist (x : Torus d N) u ≤ r}
end SiteSets
section Pullback
variable {M : ℕ} {κ : LatticeFields.LatticeShape d} {s : Mesh N}
def pullField {ι I : Type} (e : I → ι) (φ : LatticeFields.LatticeSite M κ ≃ GridPoint d s)
    (f : MultiField d s ι) : LatticeFields.LatticeField M κ I :=
  fun x i => f (e i, φ x)
def idxOne (i : Fin 1 → Fin d) : Fin d := i 0
def idxTwo (i : Fin 2 → Fin d) : Fin d × Fin d := (i 0, i 1)
def pullTensorTwo (φ : LatticeFields.LatticeSite M κ ≃ GridPoint d s)
    (F : MultiField d s (Fin d × Fin d)) : LatticeFields.LatticeTensor M κ 2 :=
  pullField idxTwo φ F
end Pullback
namespace Scales
variable {L j : ℕ} (S : Scales d L j N)
end Scales
end YangMills.Construction.PeriodicLattice
