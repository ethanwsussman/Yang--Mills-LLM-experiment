import YangMills.Construction.Lattice.GaugeTermOnACubeProof
import YangMills.Construction.LatticeFields.WeightConjProjComplProof
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.LatticeFields.BlockMomentInverse
variable {d N : ℕ} {κ : LatticeShape d}
theorem finite_torusSites [NeZero N] (ℓ : Fin d → ℕ) (hℓ : ∀ μ, 1 ≤ ℓ μ) :
    Finite (LatticeSite N (LatticeShape.torus ℓ hℓ)) := by apply _root_.YangMills.Construction.LatticeFields.WeightConjProjComplProof.finite_torusSites <;> assumption
section Norms
variable {M : ℕ} {I : Type}
theorem fieldInner_eq_sum [Fintype (LatticeSite M κ)] [Fintype I] (F G : LatticeField M κ I) :
    fieldInner F G = latticeSpacing M ^ d * ∑ p : LatticeSite M κ × I, F p.1 p.2 * G p.1 p.2 := by apply _root_.YangMills.Construction.LatticeFields.WeightConjProjComplProof.fieldInner_eq_sum <;> assumption
theorem fieldNorm_nonneg (F : LatticeField M κ I) : 0 ≤ fieldNorm F := Real.sqrt_nonneg _
theorem fieldNorm_add_le [Fintype (LatticeSite M κ)] [Fintype I] (F G : LatticeField M κ I) :
    fieldNorm (F + G) ≤ fieldNorm F + fieldNorm G := by apply _root_.YangMills.Construction.LatticeFields.WeightConjProjComplProof.fieldNorm_add_le <;> assumption
end Norms
section Operators
theorem tensorLaplacian_add (F G : ScalarField N κ) :
    tensorLaplacian (F + G) = tensorLaplacian F + tensorLaplacian G := by
  funext x i
  simp only [tensorLaplacian, tensorGradAdjoint, tensorGrad, backwardDiff, forwardDiff, shiftForward,
    shiftBackward, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
    ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun μ _ => by ring
theorem tensorLaplacian_smul (c : ℝ) (F : ScalarField N κ) :
    tensorLaplacian (c • F) = c • tensorLaplacian F := by
  funext x i
  simp only [tensorLaplacian, tensorGradAdjoint, tensorGrad, backwardDiff, forwardDiff, shiftForward,
    shiftBackward, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun μ _ => by ring
theorem siteBlockAvg_add [Finite (LatticeSite N κ)] (f g : ScalarField N κ) :
    siteBlockAvg (f + g) = siteBlockAvg f + siteBlockAvg g := by
  funext y i
  simp only [siteBlockAvg, Pi.add_apply]
  rw [← finsum_mem_add_distrib (Set.toFinite _)]
  refine finsum_mem_congr rfl fun x _ => ?_
  simp only [ScalarField.eval, Pi.add_apply]
  ring
theorem siteBlockAvg_smul [Finite (LatticeSite N κ)] (c : ℝ) (f : ScalarField N κ) :
    siteBlockAvg (c • f) = c • siteBlockAvg f := by
  funext y i
  simp only [siteBlockAvg, Pi.smul_apply, smul_eq_mul]
  rw [mul_finsum_mem' _ _ (Set.toFinite _)]
  refine finsum_mem_congr rfl fun x _ => ?_
  simp only [ScalarField.eval, Pi.smul_apply, smul_eq_mul]
  ring
theorem fieldInner_add_right [Fintype (LatticeSite 1 κ)] (F G G' : ScalarField 1 κ) :
    fieldInner F (G + G') = fieldInner F G + fieldInner F G' := by
  simp only [fieldInner_eq_sum, ← mul_add, ← Finset.sum_add_distrib]
  congr 1
theorem fieldInner_smul_right [Fintype (LatticeSite 1 κ)] (c : ℝ) (F G : ScalarField 1 κ) :
    fieldInner F (c • G) = c * fieldInner F G := by
  simp only [fieldInner_eq_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  simp only [Pi.smul_apply, smul_eq_mul]
  ring
theorem siteBlockAvgAdj_add [Fintype (LatticeSite 1 κ)] (ω ω' : ScalarField 1 κ) :
    (siteBlockAvgAdj (ω + ω') : ScalarField N κ) =
      siteBlockAvgAdj ω + siteBlockAvgAdj ω' := by
  funext x i
  simp only [siteBlockAvgAdj, fieldAdjointAt, Pi.add_apply, fieldInner_add_right, mul_add]
theorem siteBlockAvgAdj_smul [Fintype (LatticeSite 1 κ)] (c : ℝ) (ω : ScalarField 1 κ) :
    (siteBlockAvgAdj (c • ω) : ScalarField N κ) = c • siteBlockAvgAdj ω := by
  funext x i
  simp only [siteBlockAvgAdj, fieldAdjointAt, Pi.smul_apply, fieldInner_smul_right, smul_eq_mul]
  ring
theorem restrictSites_add (X : Set (LatticeSite N κ)) (f g : ScalarField N κ) :
    restrictSites X (f + g) = restrictSites X f + restrictSites X g := by
  funext x i
  simp only [restrictSites, mulBase, Pi.add_apply]
  ring
theorem restrictSites_smul (X : Set (LatticeSite N κ)) (c : ℝ) (f : ScalarField N κ) :
    restrictSites X (c • f) = c • restrictSites X f := by
  funext x i
  simp only [restrictSites, mulBase, Pi.smul_apply, smul_eq_mul]
  ring
end Operators
section Weights
variable [NeZero N]
theorem weightMul_exp_exp_neg (θ : LatticeSite N κ → ℝ) (s : LatticeScale) {I : Type}
    (F : LatticeField (s.invSpacing N) κ I) :
    weightMul (fun x => Real.exp (θ x)) s (weightMul (fun x => Real.exp (-θ x)) s F) = F := by
  cases s <;>
    · funext x i
      simp only [weightMul, mulBase, restrictUnitSites, ← mul_assoc, ← Real.exp_add]
      simp
end Weights
section Inverse
variable [Fintype (LatticeSite N κ)] [Fintype (LatticeSite 1 κ)]
theorem blockMomentLowerBound_pos : 0 < blockMomentLowerBound d := by apply _root_.YangMills.SharedProofs.p223 <;> assumption
end Inverse
section Main
variable [NeZero N] [Fintype (LatticeSite N κ)] [Fintype (LatticeSite 1 κ)]
end Main
end YangMills.Construction.LatticeFields.BlockMomentInverse
