import YangMills.Construction.Lattice.PointwiseBoundsOfTheGradientOfTheComplementProof
import Mathlib
set_option autoImplicit false
open Finset
noncomputable section
namespace YangMills.Construction.PeriodicLattice.GreenPointwise
open ScaledFun
variable {d N : ℕ}
section Norms
variable {s : Mesh N} {ι : Type}
theorem abs_apply_le_normAt [Fintype ι] (f : MultiField d s ι) (i : ι) (x : GridPoint d s) :
    |f (i, x)| ≤ MultiField.normAt f x :=
  le_ciSup (f := fun i => |f (i, x)|) (Set.finite_range _).bddAbove i
theorem normAt_nonneg [Fintype ι] (f : MultiField d s ι) (x : GridPoint d s) :
    0 ≤ MultiField.normAt f x :=
  Real.iSup_nonneg fun _ => abs_nonneg _
theorem normAt_le_maxNorm [Fintype ι] (f : MultiField d s ι) (x : GridPoint d s) :
    MultiField.normAt f x ≤ MultiField.maxNorm f :=
  le_ciSup (f := fun x => MultiField.normAt f x) (Set.finite_range _).bddAbove x
theorem abs_apply_le_maxNorm [Fintype ι] (f : MultiField d s ι) (i : ι) (x : GridPoint d s) :
    |f (i, x)| ≤ MultiField.maxNorm f :=
  (abs_apply_le_normAt f i x).trans (normAt_le_maxNorm f x)
theorem maxNorm_nonneg [Fintype ι] (f : MultiField d s ι) : 0 ≤ MultiField.maxNorm f :=
  Real.iSup_nonneg fun x => normAt_nonneg f x
theorem siteFun_maxNorm_nonneg (f : SiteFun d s) : 0 ≤ SiteFun.maxNorm f :=
  Real.iSup_nonneg fun _ => abs_nonneg _
theorem siteFun_restrictTo_apply (Y : Set (GridPoint d s)) (f : SiteFun d s) (z : GridPoint d s) :
    SiteFun.restrictTo Y f z = siteIndicator Y z * f z := rfl
theorem siteIndicator_of_mem {Y : Set (GridPoint d s)} {z : GridPoint d s} (h : z ∈ Y) :
    siteIndicator Y z = 1 := by
  simp [siteIndicator, h]
theorem siteIndicator_of_not_mem {Y : Set (GridPoint d s)} {z : GridPoint d s} (h : z ∉ Y) :
    siteIndicator Y z = 0 := by
  simp [siteIndicator, h]
end Norms
section Distances
theorem taxicabDist_comm (u v : Torus d N) : taxicabDist u v = taxicabDist v u := by apply _root_.YangMills.SharedProofs.p1021 <;> assumption
theorem taxicabDist_triangle (u v w : Torus d N) :
    taxicabDist u w ≤ taxicabDist u v + taxicabDist v w := by apply _root_.YangMills.Construction.PeriodicLattice.CenteredCubeDecay.taxicabDist_triangle <;> assumption
theorem taxicabDist_nonneg (u v : Torus d N) : 0 ≤ taxicabDist u v :=
  sum_nonneg fun _ _ => norm_nonneg _
theorem taxicabDist_sub_basisStep_le {s : Mesh N} (z : GridPoint d s) (μ : Fin d) :
    taxicabDist ((z - s.basisStep μ : GridPoint d s) : Torus d N) z ≤ s.h := by apply _root_.YangMills.Construction.PeriodicLattice.GradComplPointwise.taxicabDist_sub_basisStep_le <;> assumption
end Distances
section Adjoints
variable {s : Mesh N}
theorem finset_sum_apply {κ : Type} (t : Finset κ) (g : κ → SiteFun d s) (z : GridPoint d s) :
    (∑ p ∈ t, g p) z = ∑ p ∈ t, g p z := by
  classical
  induction t using Finset.induction_on with
  | empty => rfl
  | insert a t ha ih =>
    rw [sum_insert ha, sum_insert ha, add_apply, ih]
def single (ν : Fin d) (w : SiteFun d s) : OneForm d s :=
  ofMap fun q => if q.1 = ν then w q.2 else 0
end Adjoints
section Operators
open Scales
variable {L j : ℕ} (S : Scales d L j N)
end Operators
section Holder
variable {s : Mesh N}
theorem holderQuotientSup_nonneg (α : ℝ) {v : GridPoint d s → GridPoint d s → ℝ}
    (hv : ∀ x x', 0 ≤ v x x') : 0 ≤ holderQuotientSup s α v := by apply _root_.YangMills.Construction.CubeCovering.RescaledGreen.holderQuotientSup_nonneg <;> assumption
theorem holderSemi_nonneg {ι : Type} [Fintype ι] (α : ℝ) (f : MultiField d s ι) :
    0 ≤ MultiField.holderSemi α f := by apply _root_.YangMills.Construction.CubeCovering.RescaledGreen.multiField_holderSemi_nonneg <;> assumption
end Holder
section Data
variable {L j : ℕ}
def expWeightFactor (d : ℕ) : ℝ := Real.exp (localBoundsRate d * (17 * (d : ℝ) + 1))
structure GreenInputs (S : Scales d L j N) (c : ℝ) (cα : ℝ → ℝ) (cβε : ℝ → ℝ → ℝ) (a₀ c₁ : ℝ) :
    Prop where
  poisson : ∀ x x' : GridPoint d S.fineMesh, taxicabDist (x : Torus d N) x' ≤ 1 →
    ∀ (u g : SiteFun d S.fineMesh) (F : OneForm d S.fineMesh),
      IsPoissonSolutionOn (maxBall S.fineMesh 16 (x : Torus d N)) u g F →
      PoissonTwoSiteBounds c cα cβε (maxBall S.fineMesh 16 (x : Torus d N)) x x' u g F
  a_pos : 0 < a₀
  c_pos : 0 < c₁
  rate_pos : 0 < localBoundsRate d
  rate_le : localBoundsRate d ≤ singleScaleDecayConst d
  ops : DifferenceOperatorIdentities d S.fineMesh
  cube_eq : ∀ u : Torus d N, closedMaxBall S.fineMesh u = maxBall S.fineMesh 1 u
  lifts : LiftsOfTorusAllDimensions
  balls : MaxBallSiteEstimates
variable {S : Scales d L j N} {c : ℝ} {cα : ℝ → ℝ} {cβε : ℝ → ℝ → ℝ} {a₀ c₁ : ℝ}
theorem GreenInputs.one_le_weight (D : GreenInputs S c cα cβε a₀ c₁) {a u : Torus d N}
    (h : taxicabDist a u ≤ 17 * (d : ℝ) + 1) :
    1 ≤ expWeightFactor d * Real.exp (-localBoundsRate d * taxicabDist a u) := by
  unfold expWeightFactor
  rw [← Real.exp_add]
  refine Real.one_le_exp ?_
  nlinarith [mul_le_mul_of_nonneg_left h D.rate_pos.le]
end Data
section Arithmetic
end Arithmetic
end YangMills.Construction.PeriodicLattice.GreenPointwise
