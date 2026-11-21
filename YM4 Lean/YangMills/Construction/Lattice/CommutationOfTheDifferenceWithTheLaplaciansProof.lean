import YangMills.Construction.Lattice.MassiveDirichletOperatorIdentityFacts
import YangMills.Construction.Lattice.CovariantAdjointsBySummationByParts
import YangMills.Construction.Lattice.DecompositionOfTheFormGreenOperatorProof
import YangMills.Construction.Lattice.DifferenceOperatorsOfTheBareLattice
import YangMills.Construction.SeparatedSequences.ClassExpansionsInASettingOfRegionsProof
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open Set PeriodicLattice PeriodicLattice.DirichletOperators SeparatedSequences
namespace GradLaplacianCommutation
section InnerProducts
variable {ι κ : Type} {L t : ℕ}
theorem latticeInner_comm (f g : ι → ℝ) : latticeInner L t f g = latticeInner L t g f := by apply _root_.YangMills.Construction.SeparatedSequences.GreenDecomposition.latticeInner_comm <;> assumption
theorem latticeInner_add_right [Finite ι] (f g h : ι → ℝ) :
    latticeInner L t f (g + h) = latticeInner L t f g + latticeInner L t f h := by
  simp only [latticeInner, Pi.add_apply, mul_add, SeparatedSequences.BaseParameters.finsum_add_finite]
theorem formalAdjoint_spec [Finite ι] [Finite κ] (T : (ι → ℝ) →ₗ[ℝ] (κ → ℝ)) (f : ι → ℝ)
    (g : κ → ℝ) :
    latticeInner L t g (T f) = latticeInner L t (formalAdjoint L t T g) f := by apply _root_.YangMills.Construction.SeparatedClasses.NestedOneForms.formalAdjoint_spec <;> assumption
theorem latticeInner_indicatorMul (X : Set ι) (f g : ι → ℝ) :
    latticeInner L t f (indicatorMul X g) = latticeInner L t (indicatorMul X f) g := by
  simp only [latticeInner]
  congr 1
  refine finsum_congr fun i => ?_
  change f i * X.indicator g i = X.indicator f i * g i
  by_cases hi : i ∈ X <;> simp [hi]
theorem indicatorMul_idem (X : Set ι) (f : ι → ℝ) :
    indicatorMul X (indicatorMul X f) = indicatorMul X f := by
  funext i
  change X.indicator (X.indicator f) i = X.indicator f i
  by_cases hi : i ∈ X <;> simp [hi]
end InnerProducts
section Finiteness
variable {L m : ℕ} {j : ℤ}
theorem bond_finite [Finite (Site L m j)] : Finite (Bond L m j) := by apply _root_.YangMills.SharedProofs.p19159 <;> assumption
theorem plaquette_finite [Finite (Site L m j)] : Finite (Plaquette L m j) :=
  Finite.of_injective (fun p : Plaquette L m j => (p.origin, p.firstAxis, p.secondAxis)) (by
    rintro ⟨a, b, c, _⟩ ⟨a', b', c', _⟩ h
    simp only [Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    rfl)
end Finiteness
section Operators
variable {L m K t : ℕ} [Finite (BareSite L m K)] [Finite (BareBond L m K)]
  [Finite (BarePlaquette L m K)]
omit [Finite (BarePlaquette L m K)] in
theorem grad_adjoint_spec (A : OneForms L m K) (f : ZeroForms L m K) :
    latticeInner L t A (grad t f) = latticeInner L t (gradAdjoint L m K t A) f :=
  formalAdjoint_spec (grad t) f A
omit [Finite (BareSite L m K)] in
theorem curl_adjoint_spec (B : TwoForms L m K) (A : OneForms L m K) :
    latticeInner L t B (curl t A) = latticeInner L t (curlAdjoint L m K t B) A :=
  formalAdjoint_spec (curl t) A B
theorem latticeInner_hodgeLaplacian (C E : OneForms L m K) :
    latticeInner L t C (hodgeLaplacian L m K t E) =
      latticeInner L t (curl t E) (curl t C) +
        latticeInner L t (gradAdjoint L m K t C) (gradAdjoint L m K t E) := by
  have h : hodgeLaplacian L m K t E =
      curlAdjoint L m K t (curl t E) + grad t (gradAdjoint L m K t E) := rfl
  rw [h, latticeInner_add_right, latticeInner_comm C (curlAdjoint L m K t _), ← curl_adjoint_spec,
    grad_adjoint_spec]
variable (U : Set (FourTorus L m)) (φ : BondFrame)
end Operators
section Sequence
variable (D : BaseParameters) (Ω : ℕ → Set D.Torus) (φ : BondFrame)
theorem bareSite_finite : Finite (BareSite D.L D.m D.K) :=
  BaseParameters.site_finite (by have := D.three_le_L; omega) _ _
theorem finestMesh_ne_zero : finestMeshInLevelUnits D.L D.t ≠ 0 := by
  rw [← D.levelMeshRatio_zero]
  have hL : (0 : ℝ) < D.L := by
    have := D.three_le_L
    exact_mod_cast (by omega : 0 < D.L)
  simp only [BaseParameters.levelMeshRatio, ScaleData.levelMesh]
  exact (zpow_pos hL _).ne'
theorem siteProjection_val (f : D.RegionZeroForms Ω) : siteProjection D.K (Ω 0) f.1 = f.1 := by
  obtain ⟨g, hg⟩ := f.2
  rw [← hg]
  exact indicatorMul_idem _ g
end Sequence
end GradLaplacianCommutation
end YangMills.Construction
end
