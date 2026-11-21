import YangMills.Construction.TorusOrFourSpace.StandingSignsOfTheSupportAdaptedFamily
import Mathlib
set_option autoImplicit false
open scoped ENNReal
noncomputable section
namespace YangMills.Construction.PeriodicSpace.GrowingDomains
def IsLatticePowerScale (P : Params) : Prop := ∃ k : ℕ, P.M = (P.L : ℝ) ^ k
abbrev cOneNorm (P : Params) (X : Kind) (f : X.Pt P → ℝ) : ℝ≥0∞ :=
  SupportAdapted.c1EuclidNorm P X f
section Multilinear
variable {n : ℕ} {V : Fin n → Type*} [∀ i, AddCommGroup (V i)] [∀ i, Module ℝ (V i)]
  {W : Type*} [AddCommGroup W] [Module ℝ W]
def IsMultilinearFun (F : (∀ i, V i) → W) : Prop :=
  ∀ (x : ∀ i, V i) (i : Fin n), IsLinearMap ℝ fun v : V i => F (Function.update x i v)
theorem isMultilinearFun_iff_exists_multilinearMap (F : (∀ i, V i) → W) :
    IsMultilinearFun F ↔ ∃ G : MultilinearMap ℝ V W, ⇑G = F := by
  constructor
  · intro h
    refine ⟨{ toFun := F, map_update_add' := ?_, map_update_smul' := ?_ }, rfl⟩
    · intro _ x i a b
      have hd : ‹DecidableEq (Fin n)› = instDecidableEqFin n := Subsingleton.elim _ _
      subst hd
      exact (h x i).map_add a b
    · intro _ x i c a
      have hd : ‹DecidableEq (Fin n)› = instDecidableEqFin n := Subsingleton.elim _ _
      subst hd
      exact (h x i).map_smul c a
  · rintro ⟨G, rfl⟩ x i
    exact ⟨fun a b => G.map_update_add x i a b, fun c a => G.map_update_smul x i c a⟩
end Multilinear
end YangMills.Construction.PeriodicSpace.GrowingDomains
