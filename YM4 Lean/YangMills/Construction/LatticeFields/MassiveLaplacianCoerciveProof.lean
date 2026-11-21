import YangMills.Construction.LatticeFields.CompressedGreenDecayProof
import YangMills.Construction.LatticeFields.ProjGradDecayProof
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.LatticeFields.CoerciveBound
instance finite_latticeSite_torus {d : ℕ} (N : ℕ) [NeZero N] (ℓ : Fin d → ℕ) (hℓ : ∀ μ, 1 ≤ ℓ μ) :
    Finite (LatticeSite N (LatticeShape.torus ℓ hℓ)) := by
  have hN : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  have hpos : ∀ μ, (0 : ℤ) < (N : ℤ) * (ℓ μ : ℤ) := fun μ =>
    mul_pos (by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)) (by exact_mod_cast hℓ μ)
  let g : (∀ μ, Fin (N * ℓ μ)) → LatticeSite N (LatticeShape.torus ℓ hℓ) := fun n =>
    toSite N _ ⟨fun μ => latticeSpacing N * (((n μ : ℕ) : ℤ) : ℝ), fun μ => ⟨((n μ : ℕ) : ℤ), rfl⟩⟩
  refine Finite.of_surjective g ?_
  intro z
  obtain ⟨v, rfl⟩ := toSite_surjective N _ z
  have hv : ∀ μ, ∃ n : ℤ, (v : Fin d → ℝ) μ = latticeSpacing N * n := v.2
  choose m hm using hv
  have hlt : ∀ μ, (m μ % ((N : ℤ) * (ℓ μ : ℤ))).toNat < N * ℓ μ := fun μ => by
    have h1 := Int.emod_lt_of_pos (m μ) (hpos μ)
    have h2 := Int.emod_nonneg (m μ) (hpos μ).ne'
    zify
    rw [Int.toNat_of_nonneg h2]
    exact h1
  refine ⟨fun μ => ⟨_, hlt μ⟩, ?_⟩
  rw [← sub_eq_zero, ← map_sub, toSite_eq_zero_iff]
  change ∀ μ, ∃ n : ℤ, _ = (ℓ μ : ℝ) * n
  intro μ
  refine ⟨-(m μ / ((N : ℤ) * (ℓ μ : ℤ))), ?_⟩
  have h2 := Int.emod_nonneg (m μ) (hpos μ).ne'
  have h3 : m μ = m μ % ((N : ℤ) * (ℓ μ : ℤ)) + (N : ℤ) * (ℓ μ : ℤ) * (m μ / ((N : ℤ) * (ℓ μ : ℤ))) :=
    (Int.emod_add_mul_ediv _ _).symm
  have h4 : (m μ : ℝ) = ((m μ % ((N : ℤ) * (ℓ μ : ℤ)) : ℤ) : ℝ) +
      (N : ℝ) * (ℓ μ : ℝ) * ((m μ / ((N : ℤ) * (ℓ μ : ℤ)) : ℤ) : ℝ) := by
    exact_mod_cast h3
  have h5 : (((m μ % ((N : ℤ) * (ℓ μ : ℤ))).toNat : ℤ) : ℝ) =
      ((m μ % ((N : ℤ) * (ℓ μ : ℤ)) : ℤ) : ℝ) := by
    rw [Int.toNat_of_nonneg h2]
  change latticeSpacing N * (((m μ % ((N : ℤ) * (ℓ μ : ℤ))).toNat : ℤ) : ℝ) - (v : Fin d → ℝ) μ = _
  rw [h5, hm μ, h4]
  simp only [latticeSpacing]
  push_cast
  field_simp
  ring
section Inner
variable {d N : ℕ} {κ : LatticeShape d} {I : Type}
theorem fieldInner_comm (F G : LatticeField N κ I) : fieldInner F G = fieldInner G F :=
  tsum_congr fun p => by ring
theorem fieldNorm_sq (F : LatticeField N κ I) : fieldNorm F ^ 2 = fieldInner F F := by apply _root_.YangMills.Construction.LatticeFields.CompressedGreenDecayProof.fieldNorm_sq_eq <;> assumption
theorem fieldNorm_nonneg (F : LatticeField N κ I) : 0 ≤ fieldNorm F := Real.sqrt_nonneg _
variable [Finite (LatticeSite N κ)] [Finite I]
theorem fieldSquareSummable_of_finite (F : LatticeField N κ I) : FieldSquareSummable F :=
  Summable.of_finite
theorem fieldInner_add_right (F G H : LatticeField N κ I) :
    fieldInner F (G + H) = fieldInner F G + fieldInner F H := by apply _root_.YangMills.Construction.LatticeFields.CompressedGreenDecayProof.fieldInner_add <;> assumption
theorem fieldInner_sub_right (F G H : LatticeField N κ I) :
    fieldInner F (G - H) = fieldInner F G - fieldInner F H := by apply _root_.YangMills.Construction.LatticeFields.CompressedGreenDecayProof.fieldInner_sub <;> assumption
theorem abs_fieldInner_le (F G : LatticeField N κ I) :
    |fieldInner F G| ≤ fieldNorm F * fieldNorm G := by apply _root_.YangMills.Construction.LatticeFields.CompressedGreenDecayProof.abs_fieldInner_le <;> assumption
end Inner
section Numbers
theorem blockLapConst_nonneg (d : ℕ) : 0 ≤ blockLapConst d := by apply _root_.YangMills.SharedProofs.p12226 <;> assumption
end Numbers
section Operators
variable {d N : ℕ} {κ : LatticeShape d}
theorem tensorGrad_eq_latticeGrad (f : ScalarField N κ) : tensorGrad f = latticeGrad f := by apply _root_.YangMills.Construction.LatticeFields.ProjGradDecayProof.tensorGrad_eq_latticeGrad <;> assumption
theorem tensorLaplacian_eq_latticeDiv_latticeGrad (f : ScalarField N κ) :
    tensorLaplacian f = latticeDiv (latticeGrad f) := by apply _root_.YangMills.Construction.LatticeFields.ProjGradDecayProof.tensorLaplacian_eq_div_grad <;> assumption
structure TorusOperatorFacts (N : ℕ) (κ : LatticeShape d) : Prop where
  grad_adjoint : ∀ (f : ScalarField N κ) (B : LatticeOneForm N κ),
    fieldInner (latticeGrad f) B = fieldInner f (latticeDiv B)
  unit_grad_adjoint : ∀ (f : ScalarField 1 κ) (B : LatticeOneForm 1 κ),
    fieldInner (latticeGrad f) B = fieldInner f (latticeDiv B)
  blockAvg_adjoint : ∀ (f : ScalarField N κ) (ω : ScalarField 1 κ),
    fieldInner (siteBlockAvg f) ω = fieldInner f (siteBlockAvgAdj ω)
  blockAvg_adj_right_inv : ∀ ω : ScalarField 1 κ,
    siteBlockAvg (siteBlockAvgAdj (N := N) ω) = ω
  blockAvg_norm_le : ∀ f : ScalarField N κ, fieldNorm (siteBlockAvg f) ≤ fieldNorm f
  bondAvg_norm_le : ∀ A : LatticeOneForm N κ, fieldNorm (bondBlockAvg A) ≤ fieldNorm A
  bondAvg_grad : ∀ f : ScalarField N κ,
    bondBlockAvg (latticeGrad f) = latticeGrad (siteBlockAvg f)
  blockAvg_div : ∀ A : LatticeOneForm N κ,
    siteBlockAvg (latticeDiv A) = latticeDiv (exitFaceAvg A)
  bondAvg_sub_exitAvg_sq : ∀ A : LatticeOneForm N κ,
    fieldNorm (bondBlockAvg A - exitFaceAvg A) ^ 2 ≤ 4 * (d : ℝ) * fieldNorm (tensorGrad A) ^ 2
  norm_tensorGrad_grad : ∀ f : ScalarField N κ,
    fieldNorm (tensorGrad (latticeGrad f)) = fieldNorm (tensorLaplacian f)
variable [Finite (LatticeSite N κ)] [Finite (LatticeSite 1 κ)]
theorem fieldInner_tensorLaplacian (H : TorusOperatorFacts N κ) (g f : ScalarField N κ) :
    fieldInner g (tensorLaplacian f) = fieldInner (latticeGrad g) (latticeGrad f) := by
  rw [tensorLaplacian_eq_latticeDiv_latticeGrad, H.grad_adjoint]
theorem massiveBlockLaplacian_symm (H : TorusOperatorFacts N κ) (f g : ScalarField N κ) :
    fieldInner (massiveBlockLaplacian f) g = fieldInner f (massiveBlockLaplacian g) := by
  unfold massiveBlockLaplacian
  rw [fieldInner_comm _ g, fieldInner_add_right, fieldInner_add_right, fieldInner_tensorLaplacian H,
    fieldInner_tensorLaplacian H, ← H.blockAvg_adjoint, ← H.blockAvg_adjoint,
    fieldInner_comm (latticeGrad g), fieldInner_comm (siteBlockAvg g)]
end Operators
end YangMills.Construction.LatticeFields.CoerciveBound
