import YangMills.Construction.ColdStepAtMirrorFrames.GapOfANormNearOneProof
import YangMills.Construction.ColdStepAtMirrorFrames.SumsOfHolonomies
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction.ColdStepAtMirrorFrames
open BlockAverages
namespace HolonomySums
abbrev topSmoothness : WithTop ℕ∞ := ((⊤ : ℕ∞) : WithTop ℕ∞)
theorem natCast_le_topSmoothness (j : ℕ) : (j : WithTop ℕ∞) ≤ topSmoothness := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.NormNearOne.natCast_le_smoothTop <;> assumption
def zeroCoord {k : ℕ} (i : Fin k) : (Fin k → ℝ) →L[ℝ] (Fin k → ℝ) :=
  ContinuousLinearMap.pi fun m => if m = i then 0 else ContinuousLinearMap.proj m
theorem zeroCoord_apply {k : ℕ} (i : Fin k) (t : Fin k → ℝ) :
    zeroCoord i t = Function.update t i 0 := by
  funext m
  by_cases h : m = i
  · subst h
    simp [zeroCoord]
  · simp [zeroCoord, h, Function.update_of_ne h]
theorem iteratedFDeriv_basis_eq_zero_of_update_invariant {E : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {k : ℕ}
    {u : (Fin k → ℝ) → E} (hu : ContDiff ℝ topSmoothness u) (i : Fin k)
    (hinv : ∀ (t : Fin k → ℝ) (s : ℝ), u (Function.update t i s) = u t) :
    iteratedFDeriv ℝ k u 0 (fun m => Pi.single m 1) = 0 := by
  have h1 : u ∘ zeroCoord i = u := by
    funext t
    simp only [Function.comp, zeroCoord_apply]
    exact hinv t 0
  have h2 := (zeroCoord i).iteratedFDeriv_comp_right hu (0 : Fin k → ℝ) (i := k)
    (natCast_le_topSmoothness k)
  rw [h1] at h2
  rw [h2]
  simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply, map_zero]
  apply ContinuousMultilinearMap.map_coord_zero _ i
  rw [zeroCoord_apply]
  funext m
  by_cases h : m = i
  · subst h
    simp
  · simp [Function.update_of_ne h, Pi.single_eq_of_ne h]
theorem norm_apply_basis_le {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {k : ℕ}
    (D : (Fin k → ℝ) [×k]→L[ℝ] E) : ‖D (fun m => Pi.single m 1)‖ ≤ ‖D‖ := by
  have h := D.le_opNorm (fun m => Pi.single m (1 : ℝ))
  have h2 : ∏ m : Fin k, ‖(Pi.single m (1 : ℝ) : Fin k → ℝ)‖ ≤ 1 := by
    refine Finset.prod_le_one (fun _ _ => norm_nonneg _) fun m _ => ?_
    refine (pi_norm_le_iff_of_nonneg zero_le_one).2 fun r => ?_
    by_cases hr : r = m
    · subst hr
      simp
    · simp [Pi.single_eq_of_ne hr]
  calc _ ≤ ‖D‖ * ∏ m : Fin k, ‖(Pi.single m (1 : ℝ) : Fin k → ℝ)‖ := h
    _ ≤ ‖D‖ * 1 := mul_le_mul_of_nonneg_left h2 (norm_nonneg _)
    _ = ‖D‖ := mul_one _
theorem holonomySumDerivBounds_of_holonomyDerivativeBounds (H : HolonomyDerivativeBounds) :
    HolonomySumDerivBounds := by
  classical
  obtain ⟨C, hC0, hC⟩ := H
  refine ⟨fun k n => C k n k, fun k n => hC0 k n k, ?_⟩
  intro F lev ι Q x l E _ _ A e₀ G hG W
  have hrep : ∀ (k : ℕ) (c : Fin k → F.Site lev × Fin 4) (X : Fin k → imaginaryQuaternions),
      (fun t : Fin k → ℝ => G (leftTranslate (bondSpread c X t) W)) =
        fun t => e₀ + ∑ q ∈ Q, A q (perturbedHolonomy W (x q) (l q) c X t) := by
    intro k c X
    funext t
    rw [hG]
    rfl
  have hu : ∀ (k : ℕ) (c : Fin k → F.Site lev × Fin 4) (X : Fin k → imaginaryQuaternions) (q : ι),
      ContDiff ℝ topSmoothness (perturbedHolonomy W (x q) (l q) c X) := fun k c X q =>
    (hC F lev W (x q) (l q) k c X).1
  have hv : ∀ (k : ℕ) (c : Fin k → F.Site lev × Fin 4) (X : Fin k → imaginaryQuaternions),
      ContDiff ℝ topSmoothness
        (fun t => ∑ q ∈ Q, A q (perturbedHolonomy W (x q) (l q) c X t)) := fun k c X =>
    ContDiff.sum fun q _ => (A q).contDiff.comp (hu k c X q)
  refine ⟨fun k c X => ?_, fun k c X hk hX => ?_⟩
  · rw [hrep]
    exact (contDiff_const.add (hv k c X)).contDiffAt.of_le
      (le_trans (by norm_cast) (natCast_le_topSmoothness 3))
  · unfold bondDeriv
    rw [hrep]
    have hk0 : k ≠ 0 := by omega
    have hkle : (k : WithTop ℕ∞) ≤ topSmoothness := natCast_le_topSmoothness k
    have hsplit : iteratedFDeriv ℝ k
        (fun t => e₀ + ∑ q ∈ Q, A q (perturbedHolonomy W (x q) (l q) c X t)) 0 =
        ∑ q ∈ Q, iteratedFDeriv ℝ k ((A q) ∘ perturbedHolonomy W (x q) (l q) c X) 0 := by
      have hvf : (∑ q ∈ Q, (A q) ∘ perturbedHolonomy W (x q) (l q) c X) =
          fun t => ∑ q ∈ Q, A q (perturbedHolonomy W (x q) (l q) c X t) := by
        funext t
        simp [Finset.sum_apply]
      have h1 : (fun t => e₀ + ∑ q ∈ Q, A q (perturbedHolonomy W (x q) (l q) c X t)) =
          (fun _ => e₀) + ∑ q ∈ Q, (A q) ∘ perturbedHolonomy W (x q) (l q) c X := by
        rw [hvf]
        rfl
      have hc : ContDiffAt ℝ k (∑ q ∈ Q, (A q) ∘ perturbedHolonomy W (x q) (l q) c X) 0 := by
        rw [hvf]
        exact (hv k c X).contDiffAt.of_le hkle
      rw [h1, iteratedFDeriv_add_apply (contDiff_const.contDiffAt.of_le hkle) hc,
        iteratedFDeriv_const_of_ne hk0]
      simp only [Pi.zero_apply, zero_add]
      rw [iteratedFDeriv_sum_apply]
      intro q _
      exact ((A q).contDiff.comp (hu k c X q)).contDiffAt.of_le hkle
    rw [hsplit]
    have hterm : ∀ q ∈ Q, iteratedFDeriv ℝ k ((A q) ∘ perturbedHolonomy W (x q) (l q) c X) 0
        (fun j => Pi.single j 1) =
        A q (iteratedFDeriv ℝ k (perturbedHolonomy W (x q) (l q) c X) 0
          (fun j => Pi.single j 1)) := by
      intro q _
      have := (A q).iteratedFDeriv_comp_left ((hu k c X q).contDiffAt (x := 0)) (i := k) hkle
      rw [this]
      rfl
    rw [ContinuousMultilinearMap.sum_apply, Finset.sum_congr rfl hterm]
    rw [← Finset.sum_filter_add_sum_filter_not Q
      (fun q => ∀ i, c i ∈ pathPositiveBonds (x q) (l q))]
    have hzero : ∑ q ∈ Q.filter (fun q => ¬ ∀ i, c i ∈ pathPositiveBonds (x q) (l q)),
        A q (iteratedFDeriv ℝ k (perturbedHolonomy W (x q) (l q) c X) 0
          (fun j => Pi.single j 1)) = 0 := by
      refine Finset.sum_eq_zero fun q hq => ?_
      obtain ⟨i, hi⟩ := not_forall.1 (Finset.mem_filter.1 hq).2
      rw [iteratedFDeriv_basis_eq_zero_of_update_invariant (hu k c X q) i
        ((hC F lev W (x q) (l q) k c X).2.2 i hi), map_zero]
    rw [hzero, add_zero]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun q _ => ?_)
    refine ((A q).le_opNorm _).trans (mul_le_mul_of_nonneg_left ?_ (norm_nonneg _))
    refine (norm_apply_basis_le _).trans ?_
    exact (hC F lev W (x q) (l q) k c X).2.1 (fun i => (hX i).le) k
end HolonomySums
end YangMills.Construction.ColdStepAtMirrorFrames
end
