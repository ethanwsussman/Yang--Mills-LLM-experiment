import YangMills.Construction.Lattice.OneScaleGreenOperatorOnCornerCubesProof
import YangMills.Construction.Lattice.SingleScaleOperatorBounds
import YangMills.Construction.Lattice.SingleScaleOperatorsProof
import YangMills.Construction.Lattice.UnitMeshOperatorBounds
import YangMills.Construction.PeriodicLattice.CoverPullback
import Mathlib
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset
open scoped ContDiff Topology
noncomputable section
namespace YangMills.Construction.PeriodicLattice.CenteredDecay
open ScaledFun
section
variable {d N : ℕ}
def hat (t : AddCircle (N : ℝ)) : ℝ := max 0 (1 - ‖t‖)
def latticePoint (n : Fin d → ℤ) : Torus d N := fun μ => (((n μ : ℝ)) : AddCircle (N : ℝ))
theorem abs_prod_sub_prod_le_sum {ι : Type} (s : Finset ι) (a b : ι → ℝ)
    (ha : ∀ i, 0 ≤ a i ∧ a i ≤ 1) (hb : ∀ i, 0 ≤ b i ∧ b i ≤ 1) :
    |∏ i ∈ s, a i - ∏ i ∈ s, b i| ≤ ∑ i ∈ s, |a i - b i| := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    rw [prod_insert hi, prod_insert hi, sum_insert hi]
    have hB : ∏ i ∈ s, b i ≤ 1 := prod_le_one (fun j _ => (hb j).1) fun j _ => (hb j).2
    have hB0 : 0 ≤ ∏ i ∈ s, b i := prod_nonneg fun j _ => (hb j).1
    have e : a i * ∏ i ∈ s, a i - b i * ∏ i ∈ s, b i =
        a i * (∏ i ∈ s, a i - ∏ i ∈ s, b i) + (a i - b i) * ∏ i ∈ s, b i := by ring
    rw [e]
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_mul, abs_of_nonneg (ha i).1, abs_of_nonneg hB0]
    have h₁ : a i * |∏ i ∈ s, a i - ∏ i ∈ s, b i| ≤ |∏ i ∈ s, a i - ∏ i ∈ s, b i| :=
      mul_le_of_le_one_left (abs_nonneg _) (ha i).2
    have h₂ : |a i - b i| * ∏ i ∈ s, b i ≤ |a i - b i| :=
      mul_le_of_le_one_right (abs_nonneg _) hB
    linarith
end
section
variable {d N : ℕ}
def circleRep (u : AddCircle (N : ℝ)) : ℝ := Classical.choose (QuotientAddGroup.mk_surjective u)
theorem coe_circleRep (u : AddCircle (N : ℝ)) : ((circleRep u : ℝ) : AddCircle (N : ℝ)) = u :=
  Classical.choose_spec (QuotientAddGroup.mk_surjective u)
end
section
variable {d N : ℕ} {s : Mesh N} {ι κ τ τ' : Type}
theorem finsetSum_apply {X : Type} (T : Finset τ) (f : τ → ScaledFun d s X) (q : X) :
    (∑ t ∈ T, f t) q = ∑ t ∈ T, f t q := by
  classical
  induction T using Finset.induction_on with
  | empty => rfl
  | insert t T ht ih => rw [sum_insert ht, sum_insert ht, add_apply, ih]
theorem siteFun_holderSemi_nonneg (α : ℝ) (f : SiteFun d s) :
    0 ≤ SiteFun.holderSemi α f := by apply _root_.YangMills.Construction.CubeCovering.RescaledGreen.siteFun_holderSemi_nonneg <;> assumption
section MultiFields
variable [Fintype ι] [Fintype κ]
def osc (f : MultiField d s ι) (x x' : GridPoint d s) : ℝ := ⨆ i, |f (i, x) - f (i, x')|
theorem multiField_holderSemi_nonneg (α : ℝ) (f : MultiField d s ι) :
    0 ≤ MultiField.holderSemi α f := by apply _root_.YangMills.Construction.CubeCovering.RescaledGreen.multiField_holderSemi_nonneg <;> assumption
theorem normAt_nonneg (f : MultiField d s ι) (x : GridPoint d s) : 0 ≤ MultiField.normAt f x :=
  Real.iSup_nonneg fun _ => abs_nonneg _
theorem le_normAt (f : MultiField d s ι) (x : GridPoint d s) (i : ι) :
    |f (i, x)| ≤ MultiField.normAt f x :=
  le_ciSup (f := fun i => |f (i, x)|) (Set.finite_range _).bddAbove i
theorem maxNorm_nonneg (f : MultiField d s ι) : 0 ≤ MultiField.maxNorm f :=
  Real.iSup_nonneg fun x => normAt_nonneg f x
theorem normAt_le_maxNorm (f : MultiField d s ι) (x : GridPoint d s) :
    MultiField.normAt f x ≤ MultiField.maxNorm f :=
  le_ciSup (f := fun x => MultiField.normAt f x) (Set.finite_range _).bddAbove x
theorem abs_le_maxNorm (f : MultiField d s ι) (i : ι) (x : GridPoint d s) :
    |f (i, x)| ≤ MultiField.maxNorm f :=
  (le_normAt f x i).trans (normAt_le_maxNorm f x)
theorem mulLeft_apply (ζ : SiteFun d s) (f : MultiField d s ι) (q : ι × GridPoint d s) :
    MultiField.mulLeft ζ f q = ζ q.2 * f q := rfl
end MultiFields
theorem siteFun_maxNorm_nonneg (f : SiteFun d s) : 0 ≤ SiteFun.maxNorm f :=
  Real.iSup_nonneg fun _ => abs_nonneg _
theorem siteFun_abs_le_maxNorm (f : SiteFun d s) (x : GridPoint d s) :
    |f x| ≤ SiteFun.maxNorm f :=
  le_ciSup (f := fun x => |f x|) (Set.finite_range _).bddAbove x
def scaleBy (w ζ : SiteFun d s) : SiteFun d s := ofMap fun x => w x * ζ x
end
section
variable {d N L j : ℕ} {s : Mesh N} {ι : Type}
theorem taxicab_triangle (u v w : Torus d N) : taxicabDist u w ≤ taxicabDist u v + taxicabDist v w := by apply _root_.YangMills.Construction.PeriodicLattice.CenteredCubeDecay.taxicabDist_triangle <;> assumption
end
section
open DirichletLaplacian
variable {d N L j : ℕ}
theorem mesh_ext {s t : Mesh N} (h : s.h = t.h) (p : s.count = t.count) : s = t := by apply _root_.YangMills.Construction.PeriodicLattice.SingleScaleOps.mesh_ext <;> assumption
theorem indicatorMul_empty {s : Mesh N} {X : Type} (f : ScaledFun d s X) : indicatorMul ∅ f = 0 :=
  ScaledFun.ext fun _ => indicatorMul_apply_of_notMem f (Set.notMem_empty _)
structure ConstLe (k k' : DecayConstants) : Prop where
  base : k.base ≤ k'.base
  holder : ∀ α, k.holder α ≤ k'.holder α
  grad : ∀ ε, k.grad ε ≤ k'.grad ε
  gradHolder : ∀ α ε, k.gradHolder α ε ≤ k'.gradHolder α ε
theorem ConstLe.trans {a b c : DecayConstants} (h₁ : ConstLe a b) (h₂ : ConstLe b c) :
    ConstLe a c :=
  ⟨h₁.base.trans h₂.base, fun α => (h₁.holder α).trans (h₂.holder α),
    fun ε => (h₁.grad ε).trans (h₂.grad ε),
    fun α ε => (h₁.gradHolder α ε).trans (h₂.gradHolder α ε)⟩
end
end YangMills.Construction.PeriodicLattice.CenteredDecay
