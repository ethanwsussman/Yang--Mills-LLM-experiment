import YangMills.Construction.LatticeFields.BlockBumpFunctions
import YangMills.Construction.LatticeFields.BlockMomentInverseProof
import YangMills.Construction.LatticeFields.CompressedSiteOperator
import YangMills.Construction.LatticeFields.KernelProjectionUnique
import YangMills.Construction.LatticeFields.WeightConjDirichletGreenBoundsProof
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.LatticeFields.DirichletBlockOpsProof
variable {d : ℕ}
section InnerProduct
variable {N : ℕ} {κ : LatticeShape d} {I : Type}
theorem fieldInner_eq_sum [Fintype (LatticeSite N κ)] [Fintype I] (F G : LatticeField N κ I) :
    fieldInner F G = ∑ p : LatticeSite N κ × I, latticeSpacing N ^ d * F p.1 p.2 * G p.1 p.2 :=
  tsum_fintype _
theorem fieldInner_comm [Fintype (LatticeSite N κ)] [Fintype I] (F G : LatticeField N κ I) :
    fieldInner F G = fieldInner G F := by apply _root_.YangMills.Construction.LatticeFields.WeightConjGreen.fieldInner_comm_aux <;> assumption
theorem fieldInner_add_left [Fintype (LatticeSite N κ)] [Fintype I] (F F' G : LatticeField N κ I) :
    fieldInner (F + F') G = fieldInner F G + fieldInner F' G := by
  simp only [fieldInner_eq_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun p _ => by simp only [Pi.add_apply]; ring
theorem fieldInner_add_right [Fintype (LatticeSite N κ)] [Fintype I] (F G G' : LatticeField N κ I) :
    fieldInner F (G + G') = fieldInner F G + fieldInner F G' := by
  rw [fieldInner_comm, fieldInner_add_left, fieldInner_comm G, fieldInner_comm G']
theorem fieldInner_smul_left [Fintype (LatticeSite N κ)] [Fintype I] (c : ℝ)
    (F G : LatticeField N κ I) :
    fieldInner (c • F) G = c * fieldInner F G := by
  simp only [fieldInner_eq_sum, Finset.mul_sum]
  exact Finset.sum_congr rfl fun p _ => by simp only [Pi.smul_apply, smul_eq_mul]; ring
theorem fieldInner_sub_left [Fintype (LatticeSite N κ)] [Fintype I] (F F' G : LatticeField N κ I) :
    fieldInner (F - F') G = fieldInner F G - fieldInner F' G := by apply _root_.YangMills.Construction.LatticeFields.WeightConjGreen.fieldInner_sub_left_aux <;> assumption
theorem fieldInner_sub_right [Fintype (LatticeSite N κ)] [Fintype I] (F G G' : LatticeField N κ I) :
    fieldInner F (G - G') = fieldInner F G - fieldInner F G' := by
  rw [fieldInner_comm, fieldInner_sub_left, fieldInner_comm G, fieldInner_comm G']
theorem latticeSpacing_pow_pos [NeZero N] : 0 < latticeSpacing N ^ d := by
  have : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  exact pow_pos (inv_pos.mpr this) d
theorem fieldInner_self_nonneg [NeZero N] [Fintype (LatticeSite N κ)] [Fintype I]
    (F : LatticeField N κ I) :
    0 ≤ fieldInner F F := by
  rw [fieldInner_eq_sum]
  refine Finset.sum_nonneg fun p _ => ?_
  have := mul_self_nonneg (F p.1 p.2)
  have h := (latticeSpacing_pow_pos (d := d) (N := N))
  nlinarith
theorem eq_zero_of_fieldInner_self_eq_zero [NeZero N] [Fintype (LatticeSite N κ)] [Fintype I]
    (F : LatticeField N κ I) (h : fieldInner F F = 0) : F = 0 := by
  have hs := latticeSpacing_pow_pos (d := d) (N := N)
  rw [fieldInner_eq_sum, Finset.sum_eq_zero_iff_of_nonneg fun p _ => by
    have := mul_self_nonneg (F p.1 p.2)
    nlinarith] at h
  funext x i
  have hp := h (x, i) (Finset.mem_univ _)
  have hq : F x i * F x i = 0 := by
    have : latticeSpacing N ^ d * (F x i * F x i) = 0 := by
      simpa [mul_assoc] using hp
    exact (mul_eq_zero.mp this).resolve_left hs.ne'
  simpa using hq
theorem fieldNorm_sq [NeZero N] [Fintype (LatticeSite N κ)] [Fintype I] (F : LatticeField N κ I) :
    fieldNorm F ^ 2 = fieldInner F F :=
  Real.sq_sqrt (fieldInner_self_nonneg F)
theorem fieldNorm_nonneg (F : LatticeField N κ I) : 0 ≤ fieldNorm F := Real.sqrt_nonneg _
end InnerProduct
section Operators
variable {N : ℕ} {κ : LatticeShape d}
theorem siteBlockAvg_add [Finite (LatticeSite N κ)] (f g : ScalarField N κ) :
    siteBlockAvg (f + g) = siteBlockAvg f + siteBlockAvg g := by apply _root_.YangMills.Construction.LatticeFields.BlockMomentInverse.siteBlockAvg_add <;> assumption
theorem siteBlockAvg_smul [Finite (LatticeSite N κ)] (c : ℝ) (f : ScalarField N κ) :
    siteBlockAvg (c • f) = c • siteBlockAvg f := by apply _root_.YangMills.Construction.LatticeFields.BlockMomentInverse.siteBlockAvg_smul <;> assumption
theorem siteBlockAvgAdj_add [Fintype (LatticeSite 1 κ)] (ω ω' : ScalarField 1 κ) :
    (siteBlockAvgAdj (ω + ω') : ScalarField N κ) =
      siteBlockAvgAdj ω + siteBlockAvgAdj ω' := by apply _root_.YangMills.Construction.LatticeFields.BlockMomentInverse.siteBlockAvgAdj_add <;> assumption
theorem siteBlockAvgAdj_smul [Fintype (LatticeSite 1 κ)] (c : ℝ) (ω : ScalarField 1 κ) :
    (siteBlockAvgAdj (c • ω) : ScalarField N κ) = c • siteBlockAvgAdj ω := by apply _root_.YangMills.Construction.LatticeFields.BlockMomentInverse.siteBlockAvgAdj_smul <;> assumption
theorem restrictSites_add (X : Set (LatticeSite N κ)) (f g : ScalarField N κ) :
    restrictSites X (f + g) = restrictSites X f + restrictSites X g := by apply _root_.YangMills.Construction.LatticeFields.BlockMomentInverse.restrictSites_add <;> assumption
theorem restrictSites_smul (X : Set (LatticeSite N κ)) (c : ℝ) (f : ScalarField N κ) :
    restrictSites X (c • f) = c • restrictSites X f := by apply _root_.YangMills.Construction.LatticeFields.BlockMomentInverse.restrictSites_smul <;> assumption
theorem fieldInner_restrictSites [Fintype (LatticeSite N κ)] {X : Set (LatticeSite N κ)}
    {u : ScalarField N κ} (hu : u ∈ fieldsSupportedIn X) (h : ScalarField N κ) :
    fieldInner u (restrictSites X h) = fieldInner u h := by
  simp only [fieldInner_eq_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  obtain ⟨x, i⟩ := p
  rw [Subsingleton.elim i scalarIndex]
  by_cases hx : x ∈ X
  · simp [restrictSites, mulBase, hx]
  · have h1 : u x scalarIndex = 0 := hu x hx
    simp [h1]
theorem blockLapConst_nonneg : 0 ≤ blockLapConst d := by apply _root_.YangMills.SharedProofs.p12226 <;> assumption
end Operators
end YangMills.Construction.LatticeFields.DirichletBlockOpsProof
