import YangMills.Construction.Dirichlet.NearCentresOfCubeProof
import YangMills.Construction.DirichletOperator.NormsOnAScaledLattice
import YangMills.Construction.RegionSequence.ShellDecomposition
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction
open RegionSequence RegionSequence.NestedRegions
namespace BareDilation.GaugeForm
section Circle
variable {p : ℝ}
theorem exists_lift_abs_eq_norm (t : AddCircle p) : ∃ a : ℝ, (a : AddCircle p) = t ∧ |a| = ‖t‖ := by apply _root_.YangMills.Construction.TorusMetric.exists_coe_eq_abs_eq_norm <;> assumption
theorem norm_coe_le_abs (hp : 0 < p) (a : ℝ) : ‖(a : AddCircle p)‖ ≤ |a| := by apply _root_.YangMills.Construction.Dirichlet.NearCentres.norm_coe_le_abs_of_pos <;> assumption
variable {h : ℝ} {P : ℕ}
end Circle
section Blocks
open PeriodicLattice
variable {N : ℕ}
theorem torusPeriod_pos (s : Mesh N) : (0 : ℝ) < N := by
  rw [s.period_eq]
  exact mul_pos (by exact_mod_cast s.count_pos) s.h_pos
variable {L j : ℕ} (S : Scales 4 L j N)
include S in
theorem factor_ne_zero : (L : ℝ) ≠ 0 := by exact_mod_cast S.factor_pos.ne'
end Blocks
section EvaluationMaps
open PeriodicLattice (GridPoint Mesh DilatedSite)
variable {L j N : ℕ} {𝒯 : RegionSequence.NestedRegions} {S : PeriodicLattice.Scales 4 L j N} {r : ℝ}
  (R : DilationData 𝒯 S r)
include R in
theorem odd_factor : Odd L := R.blockFactor_eq ▸ 𝒯.odd_L
include R in
theorem thirteen_le_factor : 13 ≤ L := R.blockFactor_eq ▸ 𝒯.thirteen_le_L
def pullFun : (𝒯.FineSite → ℝ) ≃ₗ[ℝ] PeriodicLattice.SiteFun 4 S.fineMesh where
  toFun f := PeriodicLattice.ScaledFun.ofMap fun x => f (R.fineSiteEquiv ⟨x⟩)
  invFun g := fun b => g (R.fineSiteEquiv.symm b).base
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv f := funext fun b => by
    change f (R.fineSiteEquiv (R.fineSiteEquiv.symm b)) = f b
    rw [Equiv.apply_symm_apply]
  right_inv g := PeriodicLattice.ScaledFun.ext fun x => by
    change g (R.fineSiteEquiv.symm (R.fineSiteEquiv ⟨x⟩)).base = g x
    rw [Equiv.symm_apply_apply]
def latticeEquiv : GridPoint 4 S.fineMesh ≃ 𝒯.FineSite :=
  (PeriodicLattice.DilatedSite.equivSite S.fineMesh r).symm.trans R.fineSiteEquiv
theorem innerSum_eq (u v : 𝒯.FineSite → ℝ) :
    Dirichlet.innerSum u v = r ^ 4 * inner ℝ (pullFun R u) (pullFun R v) := by
  have hs : ∑ᶠ x, u x * v x = ∑ x : GridPoint 4 S.fineMesh, pullFun R u x * pullFun R v x := by
    rw [← finsum_comp_equiv (latticeEquiv R), finsum_eq_sum_of_fintype]
    rfl
  rw [Dirichlet.innerSum, hs, PeriodicLattice.ScaledFun.inner_eq, R.mesh_eq, Finset.mul_sum,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [show S.fineMesh.h = PeriodicLattice.fineScale L j from rfl]
  ring
theorem finsum_mem_eq_sum (X : Set 𝒯.FineSite) (F : Finset (GridPoint 4 S.fineMesh))
    (hF : ∀ x, x ∈ F ↔ R.fineSiteEquiv ⟨x⟩ ∈ X) (f : 𝒯.FineSite → ℝ) :
    ∑ᶠ b ∈ X, f b = ∑ x ∈ F, f (R.fineSiteEquiv ⟨x⟩) := by
  classical
  rw [finsum_mem_def, ← finsum_comp_equiv (latticeEquiv R), finsum_eq_sum_of_fintype]
  calc ∑ x, X.indicator f (latticeEquiv R x) =
        ∑ x, if x ∈ F then f (R.fineSiteEquiv ⟨x⟩) else 0 := by
        refine Finset.sum_congr rfl fun x _ => ?_
        by_cases h : x ∈ F
        · rw [if_pos h, Set.indicator_of_mem (show latticeEquiv R x ∈ X from (hF x).1 h)]
          rfl
        · rw [if_neg h, Set.indicator_of_notMem
            (show latticeEquiv R x ∉ X from fun h' => h ((hF x).2 h'))]
    _ = ∑ x ∈ F, f (R.fineSiteEquiv ⟨x⟩) := by simp
end EvaluationMaps
section Layers
open PeriodicLattice (GridPoint Mesh DilatedSite)
variable {L j N : ℕ} {𝒯 : RegionSequence.NestedRegions} {S : PeriodicLattice.Scales 4 L j N} {r : ℝ}
  (R : DilationData 𝒯 S r)
include R in
theorem scale_level : 𝒯.scale j = r * S.unitMesh.h := by
  have hL := factor_ne_zero S
  change Torus.scaleSpacing 𝒯.L 𝒯.ξ (j : ℤ) = r * 1
  rw [Torus.scaleSpacing, R.blockFactor_eq, R.mesh_eq, zpow_natCast, PeriodicLattice.fineScale]
  field_simp
include R in
theorem scale_succ : 𝒯.scale (j + 1) = r * S.coarseMesh.h := by
  have hL := factor_ne_zero S
  change Torus.scaleSpacing 𝒯.L 𝒯.ξ ((j + 1 : ℕ) : ℤ) = r * (L : ℝ)
  rw [Torus.scaleSpacing, R.blockFactor_eq, R.mesh_eq, zpow_natCast, PeriodicLattice.fineScale,
    pow_succ]
  field_simp
variable {R} (hN : PulledNorms R) (hT : TwoLayered 𝒯 j)
include hN
include hT
omit hN hT in
theorem le_lastNonemptyIndex {n : ℕ} (hn : (𝒯.Ω n).Nonempty) :
    n ≤ Torus.lastNonemptyIndex 𝒯.Ω := by apply _root_.YangMills.Construction.RegionSequence.ShellDecomposition.le_lastNonemptyIndex <;> assumption
omit hN
theorem projSites_eq (f : 𝒯.FineSite → ℝ) : projSites f = f := by
  have h : {x : 𝒯.FineSite | (x : 𝒯.Point) ∈ 𝒯.Ω 0} = univ :=
    Set.eq_univ_of_forall fun x => by
      change (x : 𝒯.Point) ∈ 𝒯.Ω 0
      rw [hT.lower_eq_univ 0 (Nat.zero_le j)]
      trivial
  simp only [projSites, Dirichlet.restrictTo, h, Set.indicator_univ]
theorem dirichletLap_eq (f : 𝒯.FineSite → ℝ) :
    dirichletLap f = Dirichlet.latticeLaplacian f := by
  rw [dirichletLap, projSites_eq hT, projSites_eq hT]
include hN
end Layers
end BareDilation.GaugeForm
end YangMills.Construction
