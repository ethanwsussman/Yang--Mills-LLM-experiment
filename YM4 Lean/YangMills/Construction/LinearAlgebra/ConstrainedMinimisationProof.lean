import YangMills.Construction.LinearAlgebra.ConstrainedMinimisation
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ConstrainedForms
open LinearMap (adjoint ker range)
variable {H K : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [FiniteDimensional ℝ H]
  [NormedAddCommGroup K] [InnerProductSpace ℝ K] [FiniteDimensional ℝ K]
theorem IsPosDefOp.isUnit {A : Module.End ℝ H} (hA : IsPosDefOp A) : IsUnit A := by
  rw [Module.End.isUnit_iff]
  have inj : Function.Injective A := by
    rw [injective_iff_map_eq_zero]
    intro f hf
    by_contra hne
    have hpos := hA.2 f hne
    rw [hf, inner_zero_right] at hpos
    exact lt_irrefl _ hpos
  exact ⟨inj, LinearMap.injective_iff_surjective.mp inj⟩
theorem posDef_apply_inverse {A : Module.End ℝ H} (hA : IsPosDefOp A) (f : H) :
    A (Ring.inverse A f) = f :=
  LinearMap.congr_fun (Ring.mul_inverse_cancel A hA.isUnit) f
theorem IsPosDefOp.inverse {A : Module.End ℝ H} (hA : IsPosDefOp A) :
    IsPosDefOp (Ring.inverse A) := by
  refine ⟨fun f g => ?_, fun f hf => ?_⟩
  · calc inner ℝ (Ring.inverse A f) g
        = inner ℝ (Ring.inverse A f) (A (Ring.inverse A g)) := by rw [posDef_apply_inverse hA]
      _ = inner ℝ (A (Ring.inverse A f)) (Ring.inverse A g) := (hA.1 _ _).symm
      _ = inner ℝ f (Ring.inverse A g) := by rw [posDef_apply_inverse hA]
  · have hne : Ring.inverse A f ≠ 0 := fun h0 => hf (by rw [← posDef_apply_inverse hA f, h0, map_zero])
    have hpos := hA.2 _ hne
    rw [posDef_apply_inverse hA] at hpos
    rwa [real_inner_comm]
section Lemma
variable {X : Module.End ℝ H} {q : H →ₗ[ℝ] K} {m : Module.End ℝ K}
end Lemma
section Compressions
omit [FiniteDimensional ℝ H] in
theorem IsOrthProj.apply_of_mem {χ : Module.End ℝ H} (hχ : IsOrthProj χ) {u : H}
    (hu : u ∈ range χ) : χ u = u := by
  obtain ⟨v, rfl⟩ := hu
  exact LinearMap.congr_fun hχ.1 v
omit [FiniteDimensional ℝ H] in
theorem compress_coe (χ ψ A : Module.End ℝ H) (u : range ψ) :
    ((compress χ ψ A u : range χ) : H) = χ (A (ψ u)) := rfl
omit [FiniteDimensional ℝ H] in
theorem inner_compress {χ ψ : Module.End ℝ H} (hχ : IsOrthProj χ)
    (hψ : IsOrthProj ψ) (A : Module.End ℝ H) (u : range χ) (v : range ψ) :
    inner ℝ u (compress χ ψ A v) = inner ℝ (u : H) (A v) := by
  rw [Submodule.coe_inner, compress_coe, ← hχ.2, IsOrthProj.apply_of_mem hχ u.2,
    IsOrthProj.apply_of_mem hψ v.2]
end Compressions
section Passage
variable {X : Module.End ℝ H} {q : H →ₗ[ℝ] K} {m : Module.End ℝ K}
end Passage
end YangMills.Construction.ConstrainedForms
end
