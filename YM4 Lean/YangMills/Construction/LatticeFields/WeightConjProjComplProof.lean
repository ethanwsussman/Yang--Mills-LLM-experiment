import YangMills.Construction.LatticeFields.BlockAveragingBounds
import YangMills.Construction.LatticeFields.ConjugatedBlockAveragingBound
import YangMills.Construction.LatticeFields.TorusLatticeLaws
import YangMills.Construction.LatticeFields.WeightConjProjComplBound
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.LatticeFields.WeightConjProjComplProof
variable {d N : ℕ} {κ : LatticeShape d}
theorem finite_torusSites [NeZero N] (ℓ : Fin d → ℕ) (hℓ : ∀ μ, 1 ≤ ℓ μ) :
    Finite (LatticeSite N (LatticeShape.torus ℓ hℓ)) := by
  have hN : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  have hM : ∀ μ, 0 < N * ℓ μ := fun μ =>
    Nat.mul_pos (Nat.pos_of_ne_zero (NeZero.ne N)) (hℓ μ)
  let lift : (∀ μ : Fin d, Fin (N * ℓ μ)) → scaledIntLattice d N := fun a =>
    ⟨fun μ => latticeSpacing N * (((a μ : ℕ) : ℤ) : ℝ), fun μ => ⟨_, rfl⟩⟩
  refine Finite.of_surjective (fun a => toSite N (LatticeShape.torus ℓ hℓ) (lift a)) ?_
  intro z
  obtain ⟨w, rfl⟩ := toSite_surjective N (LatticeShape.torus ℓ hℓ) z
  have hw : ∀ μ, ∃ n : ℤ, (w : Fin d → ℝ) μ = latticeSpacing N * n := w.2
  choose n hn using hw
  have hMz : ∀ μ, (0 : ℤ) < ((N * ℓ μ : ℕ) : ℤ) := fun μ => by exact_mod_cast hM μ
  have hnonneg : ∀ μ, 0 ≤ n μ % ((N * ℓ μ : ℕ) : ℤ) := fun μ => Int.emod_nonneg _ (hMz μ).ne'
  have hlt : ∀ μ, n μ % ((N * ℓ μ : ℕ) : ℤ) < ((N * ℓ μ : ℕ) : ℤ) := fun μ =>
    Int.emod_lt_of_pos _ (hMz μ)
  let a : ∀ μ : Fin d, Fin (N * ℓ μ) := fun μ =>
    ⟨(n μ % ((N * ℓ μ : ℕ) : ℤ)).toNat, by
      have h := hlt μ
      have h' := hnonneg μ
      omega⟩
  refine ⟨a, ?_⟩
  show toSite N (LatticeShape.torus ℓ hℓ) (lift a) = toSite N (LatticeShape.torus ℓ hℓ) w
  rw [← sub_eq_zero, ← map_sub, toSite_eq_zero_iff]
  intro μ
  refine ⟨-(n μ / ((N * ℓ μ : ℕ) : ℤ)), ?_⟩
  have ha : (((a μ : ℕ) : ℤ)) = n μ % ((N * ℓ μ : ℕ) : ℤ) := Int.toNat_of_nonneg (hnonneg μ)
  have hdiv : n μ % ((N * ℓ μ : ℕ) : ℤ) + ((N * ℓ μ : ℕ) : ℤ) * (n μ / ((N * ℓ μ : ℕ) : ℤ)) = n μ :=
    Int.emod_add_mul_ediv _ _
  have hdivR : (((a μ : ℕ) : ℤ) : ℝ) + (N : ℝ) * (ℓ μ : ℝ) * ((n μ / ((N * ℓ μ : ℕ) : ℤ) : ℤ) : ℝ) =
      (n μ : ℝ) := by
    rw [ha]
    exact_mod_cast hdiv
  have hv : ((lift a - w : scaledIntLattice d N) : Fin d → ℝ) μ =
      latticeSpacing N * (((a μ : ℕ) : ℤ) : ℝ) - (w : Fin d → ℝ) μ := rfl
  show ((lift a - w : scaledIntLattice d N) : Fin d → ℝ) μ = _
  rw [hv, hn μ, ← hdivR, latticeSpacing]
  push_cast
  field_simp
  ring
section Norms
variable {M : ℕ} {I : Type}
theorem latticeSpacing_nonneg (M : ℕ) : 0 ≤ latticeSpacing M := inv_nonneg.mpr (Nat.cast_nonneg M)
theorem fieldInner_eq_sum [Fintype (LatticeSite M κ)] [Fintype I] (F G : LatticeField M κ I) :
    fieldInner F G = latticeSpacing M ^ d * ∑ p : LatticeSite M κ × I, F p.1 p.2 * G p.1 p.2 := by
  unfold fieldInner
  rw [tsum_fintype, Finset.mul_sum]
  exact Finset.sum_congr rfl fun p _ => by ring
theorem fieldInner_self_nonneg [Fintype (LatticeSite M κ)] [Fintype I] (F : LatticeField M κ I) :
    0 ≤ fieldInner F F := by
  rw [fieldInner_eq_sum]
  exact mul_nonneg (pow_nonneg (latticeSpacing_nonneg M) d)
    (Finset.sum_nonneg fun p _ => mul_self_nonneg _)
theorem fieldNorm_sq [Fintype (LatticeSite M κ)] [Fintype I] (F : LatticeField M κ I) :
    fieldNorm F ^ 2 = fieldInner F F :=
  Real.sq_sqrt (fieldInner_self_nonneg F)
theorem fieldNorm_nonneg (F : LatticeField M κ I) : 0 ≤ fieldNorm F := Real.sqrt_nonneg _
theorem fieldInner_le_mul_norm [Fintype (LatticeSite M κ)] [Fintype I] (F G : LatticeField M κ I) :
    fieldInner F G ≤ fieldNorm F * fieldNorm G := by
  have hcs : (∑ p : LatticeSite M κ × I, F p.1 p.2 * G p.1 p.2) ^ 2 ≤
      (∑ p : LatticeSite M κ × I, F p.1 p.2 ^ 2) * ∑ p : LatticeSite M κ × I, G p.1 p.2 ^ 2 :=
    Finset.sum_mul_sq_le_sq_mul_sq _ _ _
  have hsq : fieldInner F G ^ 2 ≤ fieldInner F F * fieldInner G G := by
    simp only [fieldInner_eq_sum, ← sq]
    calc _ = (latticeSpacing M ^ d) ^ 2 * (∑ p : LatticeSite M κ × I, F p.1 p.2 * G p.1 p.2) ^ 2 := by
          ring
      _ ≤ (latticeSpacing M ^ d) ^ 2 * ((∑ p : LatticeSite M κ × I, F p.1 p.2 ^ 2) *
            ∑ p : LatticeSite M κ × I, G p.1 p.2 ^ 2) :=
          mul_le_mul_of_nonneg_left hcs (sq_nonneg _)
      _ = _ := by ring
  refine (le_abs_self _).trans ((Real.abs_le_sqrt hsq).trans_eq ?_)
  exact Real.sqrt_mul (fieldInner_self_nonneg F) _
theorem fieldInner_add_left [Fintype (LatticeSite M κ)] [Fintype I] (F F' G : LatticeField M κ I) :
    fieldInner (F + F') G = fieldInner F G + fieldInner F' G := by
  simp only [fieldInner_eq_sum, Pi.add_apply, add_mul, Finset.sum_add_distrib, mul_add]
theorem fieldInner_comm [Fintype (LatticeSite M κ)] [Fintype I] (F G : LatticeField M κ I) :
    fieldInner F G = fieldInner G F := by
  rw [fieldInner_eq_sum, fieldInner_eq_sum]
  exact congrArg _ (Finset.sum_congr rfl fun p _ => by ring)
theorem fieldInner_sub_right [Fintype (LatticeSite M κ)] [Fintype I] (F G G' : LatticeField M κ I) :
    fieldInner F (G - G') = fieldInner F G - fieldInner F G' := by
  simp only [fieldInner_eq_sum, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]
theorem fieldNorm_add_le [Fintype (LatticeSite M κ)] [Fintype I] (F G : LatticeField M κ I) :
    fieldNorm (F + G) ≤ fieldNorm F + fieldNorm G := by
  have h0 := fieldNorm_nonneg F
  have h1 := fieldNorm_nonneg G
  refine Real.sqrt_le_iff.mpr ⟨add_nonneg h0 h1, ?_⟩
  have hc := fieldInner_le_mul_norm F G
  have e : fieldInner (F + G) (F + G) =
      fieldInner F F + 2 * fieldInner F G + fieldInner G G := by
    rw [fieldInner_add_left, fieldInner_comm F (F + G), fieldInner_comm G (F + G),
      fieldInner_add_left, fieldInner_add_left, fieldInner_comm G F]
    ring
  rw [e]
  nlinarith [fieldNorm_sq F, fieldNorm_sq G]
end Norms
section Operators
end Operators
end YangMills.Construction.LatticeFields.WeightConjProjComplProof
