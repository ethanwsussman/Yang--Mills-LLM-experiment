import YangMills.Construction.Dirichlet.CrossingChainSumEstimate
import YangMills.Construction.Lattice.DecayingKernels
import YangMills.Construction.Lattice.LocalizedDecayBounds
import YangMills.Construction.Lattice.TwoScaleOperatorDefs
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.PeriodicLattice
open ScaledFun
variable {d N m : ℕ}
def circleMod (m N : ℕ) : AddCircle (((m * N : ℕ) : ℝ)) →+ AddCircle (N : ℝ) :=
  QuotientAddGroup.map _ _ (AddMonoidHom.id ℝ) (by
    intro y hy
    obtain ⟨n, rfl⟩ := AddSubgroup.mem_zmultiples_iff.mp hy
    refine AddSubgroup.mem_zmultiples_iff.mpr ⟨n * m, ?_⟩
    simp only [zsmul_eq_mul]
    push_cast
    ring)
@[simp] theorem circleMod_coe (y : ℝ) :
    circleMod m N (y : AddCircle (((m * N : ℕ) : ℝ))) = (y : AddCircle (N : ℝ)) := rfl
def torusMod (d m N : ℕ) : Torus d (m * N) →+ Torus d N :=
  (circleMod m N).compLeft (Fin d)
def siteMod {s : Mesh N} {t : Mesh (m * N)} (hst : t.h = s.h) :
    GridPoint d t →+ GridPoint d s :=
  AddMonoidHom.mk' (fun p => ⟨torusMod d m N p.1, fun μ _ => by
    obtain ⟨n, hn⟩ := AddSubgroup.mem_zmultiples_iff.mp (p.2 μ (Set.mem_univ μ))
    refine AddSubgroup.mem_zmultiples_iff.mpr ⟨n, ?_⟩
    have hp : torusMod d m N p.1 μ = circleMod m N (p.1 μ) := rfl
    rw [hp, ← hn, map_zsmul, hst, circleMod_coe]⟩)
    fun p q => Subtype.ext (map_add (torusMod d m N) p.1 q.1)
def pullFun {s : Mesh N} {t : Mesh (m * N)} (hst : t.h = s.h) :
    SiteFun d s →ₗ[ℝ] SiteFun d t where
  toFun f := ofMap fun p => f (siteMod hst p)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
def DecayConstants.rescale (k : DecayConstants) (t : ℝ) (ht : 0 < t) :
    DecayConstants where
  base := t * k.base
  holder α := t * k.holder α
  grad ε := t * k.grad ε
  gradHolder α ε := t * k.gradHolder α ε
  base_pos := mul_pos ht k.base_pos
  holder_pos α h₀ h₁ := mul_pos ht (k.holder_pos α h₀ h₁)
  grad_pos ε h₀ h₁ := mul_pos ht (k.grad_pos ε h₀ h₁)
  gradHolder_pos α ε h₀ h₁ h₂ := mul_pos ht (k.gradHolder_pos α ε h₀ h₁ h₂)
theorem summable_exp_neg_mul_abs_int {δ : ℝ} (hδ : 0 < δ) :
    Summable fun k : ℤ => Real.exp (-δ * |(k : ℝ)|) := by apply _root_.YangMills.Construction.Dirichlet.ChainSumEstimate.summable_exp_neg_mul_abs <;> assumption
namespace Scales
variable {L j : ℕ} (S : Scales d L j N)
end Scales
end YangMills.Construction.PeriodicLattice
