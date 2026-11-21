import YangMills.Construction.Towers.BoundOfTheChainsOfLocalKernels
import YangMills.Construction.Towers.SumsInsideTheChainsOfLocalKernels
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Tower.LocalFamilies
namespace LoopSums
variable {J : Type}
theorem tsum_comm_of_dominated {N P : Type} (F : N → P → ℂ) (G : P → ℝ) (B : ℝ)
    (hF : ∀ p, Summable fun n => ‖F n p‖) (hG : ∀ p, ∑' n, ‖F n p‖ = G p)
    (hGs : Summable G) (hB : ∑' p, G p ≤ B) :
    Summable (fun n => ‖∑' p, F n p‖) ∧ ∑' n, ‖∑' p, F n p‖ ≤ B ∧
      ∑' p, ∑' n, F n p = ∑' n, ∑' p, F n p := by
  have hprodSum : Summable (fun q : P × N => ‖F q.2 q.1‖) := by
    rw [summable_prod_of_nonneg (fun _ => norm_nonneg _)]
    refine ⟨hF, ?_⟩
    simpa only [hG] using hGs
  have hprodSum' : Summable (fun q : N × P => ‖F q.1 q.2‖) :=
    (Equiv.prodComm N P).summable_iff.2 hprodSum
  have hrows : ∀ n, Summable fun p => ‖F n p‖ := fun n => hprodSum'.prod_factor n
  have hnorm : ∀ n, ‖∑' p, F n p‖ ≤ ∑' p, ‖F n p‖ := fun n => norm_tsum_le_tsum_norm (hrows n)
  have hinner : Summable (fun n => ∑' p, ‖F n p‖) := hprodSum'.prod
  refine ⟨Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hnorm hinner, ?_, ?_⟩
  · calc ∑' n, ‖∑' p, F n p‖ ≤ ∑' n, ∑' p, ‖F n p‖ :=
          (Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hnorm hinner).tsum_le_tsum hnorm hinner
      _ = ∑' p, ∑' n, ‖F n p‖ :=
          (Summable.tsum_comm (f := fun n p => ‖F n p‖) hprodSum').symm
      _ = ∑' p, G p := by simp only [hG]
      _ ≤ B := hB
  · exact Summable.tsum_comm (f := F) hprodSum'.of_norm
theorem isExpDecayKernel_norm {pos : J → InfiniteLattice.AmbientSpace} {c s : ℝ} {S : J → J → ℂ}
    (h : IsExpDecayKernel pos c s S) :
    IsExpDecayKernel pos c s (fun a b => ((‖S a b‖ : ℝ) : ℂ)) := by
  intro a b
  rw [Complex.norm_real, norm_norm]
  exact h a b
theorem isCubicGrowthLocalKernel_tsum_norm {N : Type} {pos : J → InfiniteLattice.AmbientSpace}
    {A : ℝ} {X : N → J → J → ℂ} (h : IsCubicGrowthLocalFamily pos A X) :
    IsCubicGrowthLocalKernel pos A (fun a b => ((∑' n, ‖X n a b‖ : ℝ) : ℂ)) := by
  refine ⟨fun a b hab => ?_, fun a b => ?_⟩
  · have hzero : ∀ n, X n a b = 0 := fun n => h.1 n a b hab
    simp [hzero]
  · rw [Complex.norm_real, Real.norm_of_nonneg (tsum_nonneg fun _ => norm_nonneg _)]
    exact (h.2 a b).2
theorem tsum_mul_three {N : Type} (a b : ℂ) (u : N → ℂ) (hu : Summable fun n => ‖u n‖) :
    Summable (fun n => ‖a * u n * b‖) ∧
      ∑' n, ‖a * u n * b‖ = ‖a‖ * (∑' n, ‖u n‖) * ‖b‖ ∧
      ∑' n, a * u n * b = a * (∑' n, u n) * b := by
  have hshape : ∀ n, ‖a * u n * b‖ = ‖a‖ * ‖b‖ * ‖u n‖ := fun n => by
    rw [norm_mul, norm_mul]; ring
  refine ⟨?_, ?_, ?_⟩
  · simp only [hshape]
    exact hu.mul_left _
  · simp only [hshape]
    rw [tsum_mul_left]; ring
  · have hshape' : ∀ n, a * u n * b = a * b * u n := fun n => by ring
    simp only [hshape']
    rw [tsum_mul_left]; ring
theorem tsum_mul_five {N N' : Type} (a b d : ℂ) (u : N → ℂ) (v : N' → ℂ)
    (hu : Summable fun n => ‖u n‖) (hv : Summable fun n => ‖v n‖) :
    Summable (fun q : N × N' => ‖a * u q.1 * b * v q.2 * d‖) ∧
      ∑' q : N × N', ‖a * u q.1 * b * v q.2 * d‖ =
        ‖a‖ * (∑' n, ‖u n‖) * ‖b‖ * (∑' n, ‖v n‖) * ‖d‖ ∧
      ∑' q : N × N', a * u q.1 * b * v q.2 * d = a * (∑' n, u n) * b * (∑' n, v n) * d := by
  have hshape : ∀ q : N × N', ‖a * u q.1 * b * v q.2 * d‖ = ‖a‖ * ‖b‖ * ‖d‖ * (‖u q.1‖ * ‖v q.2‖) :=
    fun q => by
      simp only [norm_mul]; ring
  have hpair : Summable (fun q : N × N' => ‖u q.1‖ * ‖v q.2‖) :=
    hu.mul_of_nonneg hv (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)
  refine ⟨?_, ?_, ?_⟩
  · simp only [hshape]
    exact hpair.mul_left _
  · simp only [hshape]
    rw [tsum_mul_left, ← tsum_mul_tsum_of_summable_norm (f := fun n => ‖u n‖)
      (g := fun n => ‖v n‖) (by simpa using hu) (by simpa using hv)]
    ring
  · have hshape' : ∀ q : N × N', a * u q.1 * b * v q.2 * d = a * b * d * (u q.1 * v q.2) :=
      fun q => by ring
    simp only [hshape']
    rw [tsum_mul_left, ← tsum_mul_tsum_of_summable_norm hu hv]
    ring
end LoopSums
open LoopSums in
theorem loopSums_linear_and_tsum_of_loopTermsBound (hbound : LoopTermsBound) :
    loopSums_linear_and_tsum := by
  intro c m hc
  obtain ⟨M, hM0, hM⟩ := hbound c m hc
  refine ⟨M, hM0, fun J pos hpos s hs => ?_⟩
  obtain ⟨h1, h2, -⟩ := hM J pos hpos s hs
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro S₀ S₁ X Y A A' a hA hA' hS₀ hS₁ hX hY
    have sX : Summable (loopTermsOne pos S₀ X S₁) :=
      (h1 S₀ S₁ X A hA hS₀ hS₁ hX).1.of_norm
    have sY : Summable (loopTermsOne pos S₀ Y S₁) :=
      (h1 S₀ S₁ Y A' hA' hS₀ hS₁ hY).1.of_norm
    unfold loopSumOne
    rw [← tsum_mul_left, ← sX.tsum_add (sY.mul_left a)]
    refine tsum_congr fun p => ?_
    simp only [loopTermsOne]
    ring
  · intro S₀ S₁ S₂ X X' Y A A' A'' a hA hA' hA'' hS₀ hS₁ hS₂ hX hX' hY
    constructor
    · have sX : Summable (loopTermsTwo pos S₀ X S₁ Y S₂) :=
        (h2 S₀ S₁ S₂ X Y A A'' hA hA'' hS₀ hS₁ hS₂ hX hY).1.of_norm
      have sY : Summable (loopTermsTwo pos S₀ X' S₁ Y S₂) :=
        (h2 S₀ S₁ S₂ X' Y A' A'' hA' hA'' hS₀ hS₁ hS₂ hX' hY).1.of_norm
      unfold loopSumTwo
      rw [← tsum_mul_left, ← sX.tsum_add (sY.mul_left a)]
      refine tsum_congr fun p => ?_
      simp only [loopTermsTwo]
      ring
    · have sX : Summable (loopTermsTwo pos S₀ Y S₁ X S₂) :=
        (h2 S₀ S₁ S₂ Y X A'' A hA'' hA hS₀ hS₁ hS₂ hY hX).1.of_norm
      have sY : Summable (loopTermsTwo pos S₀ Y S₁ X' S₂) :=
        (h2 S₀ S₁ S₂ Y X' A'' A' hA'' hA' hS₀ hS₁ hS₂ hY hX').1.of_norm
      unfold loopSumTwo
      rw [← tsum_mul_left, ← sX.tsum_add (sY.mul_left a)]
      refine tsum_congr fun p => ?_
      simp only [loopTermsTwo]
      ring
  · intro N S₀ S₁ X A hA hS₀ hS₁ hX
    have hb := h1 _ _ _ A hA (isExpDecayKernel_norm hS₀) (isExpDecayKernel_norm hS₁)
      (isCubicGrowthLocalKernel_tsum_norm hX)
    have key := fun p : OriginIndex pos × J × J =>
      tsum_mul_three (S₀ p.1 p.2.1) (S₁ p.2.2 p.1) (fun n => X n p.2.1 p.2.2) (hX.2 _ _).1
    obtain ⟨e1, e2, e3⟩ := tsum_comm_of_dominated (fun n p => loopTermsOne pos S₀ (X n) S₁ p)
      (fun p => ‖loopTermsOne pos (fun a b => ((‖S₀ a b‖ : ℝ) : ℂ))
        (fun a b => ((∑' n, ‖X n a b‖ : ℝ) : ℂ)) (fun a b => ((‖S₁ a b‖ : ℝ) : ℂ)) p‖)
      (M * A * s ^ 2) (fun p => (key p).1)
      (fun p => by
        refine (key p).2.1.trans ?_
        simp only [loopTermsOne, norm_mul, Complex.norm_real, norm_norm]
        rw [Real.norm_of_nonneg (tsum_nonneg fun _ => norm_nonneg _)])
      hb.1 hb.2
    refine ⟨e1, e2, ?_⟩
    unfold loopSumOne
    rw [← e3]
    refine tsum_congr fun p => ?_
    exact (key p).2.2.symm
  · intro N N' S₀ S₁ S₂ X Y A A' hA hA' hS₀ hS₁ hS₂ hX hY
    have hb := h2 _ _ _ _ _ A A' hA hA' (isExpDecayKernel_norm hS₀) (isExpDecayKernel_norm hS₁)
      (isExpDecayKernel_norm hS₂) (isCubicGrowthLocalKernel_tsum_norm hX)
      (isCubicGrowthLocalKernel_tsum_norm hY)
    have key := fun p : OriginIndex pos × J × J × J × J =>
      tsum_mul_five (S₀ p.1 p.2.1) (S₁ p.2.2.1 p.2.2.2.1) (S₂ p.2.2.2.2 p.1)
        (fun n => X n p.2.1 p.2.2.1) (fun n => Y n p.2.2.2.1 p.2.2.2.2) (hX.2 _ _).1 (hY.2 _ _).1
    obtain ⟨e1, e2, e3⟩ := tsum_comm_of_dominated
      (fun (q : N × N') p => loopTermsTwo pos S₀ (X q.1) S₁ (Y q.2) S₂ p)
      (fun p => ‖loopTermsTwo pos (fun a b => ((‖S₀ a b‖ : ℝ) : ℂ))
        (fun a b => ((∑' n, ‖X n a b‖ : ℝ) : ℂ)) (fun a b => ((‖S₁ a b‖ : ℝ) : ℂ))
        (fun a b => ((∑' n, ‖Y n a b‖ : ℝ) : ℂ)) (fun a b => ((‖S₂ a b‖ : ℝ) : ℂ)) p‖)
      (M * A * A' * s ^ 3) (fun p => (key p).1)
      (fun p => by
        refine (key p).2.1.trans ?_
        simp only [loopTermsTwo, norm_mul, Complex.norm_real, norm_norm]
        rw [Real.norm_of_nonneg (tsum_nonneg fun _ => norm_nonneg _),
          Real.norm_of_nonneg (tsum_nonneg fun _ => norm_nonneg _)])
      hb.1 hb.2
    refine ⟨e1, e2, ?_⟩
    unfold loopSumTwo
    rw [← e3]
    refine tsum_congr fun p => ?_
    exact (key p).2.2.symm
end YangMills.Construction.Tower.LocalFamilies
end
