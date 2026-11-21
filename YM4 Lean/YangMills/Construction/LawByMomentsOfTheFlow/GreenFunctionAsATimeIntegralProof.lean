import YangMills.Construction.FreeKernel.LatticeGreenFunctionExistence
import YangMills.Construction.LawByMomentsOfTheFlow.GreenFunctionAsATimeIntegral
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.MomentLaw
open FreeKernel.UnitLattice MeasureTheory Filter Topology
variable {d : ℕ}
private lemma l1Length_nonneg (x : Fin d → ℤ) : 0 ≤ l1Length x :=
  Finset.sum_nonneg fun _ _ => abs_nonneg _
private lemma integrableOn_Ioi_latticeHeatKernel (hEv : FreeKernel.IntegerHeatKernelEvolution)
    (hDec : FreeKernel.LatticeHeatKernelDecayBound) (hTime : FreeKernel.TimeIntegralOfHeatBound) (hd : 3 ≤ d)
    (x : Fin d → ℤ) : IntegrableOn (fun t => latticeHeatKernel t x) (Set.Ioi 0) := by apply _root_.YangMills.Construction.FreeKernel.LatticeGreen.integrableOn_latticeHeatKernel <;> assumption
private lemma wordDiff_integral_comm (hInt : ∀ x : Fin d → ℤ, IntegrableOn (fun t => latticeHeatKernel t x) (Set.Ioi 0))
    (w : List (Fin d ⊕ Fin d)) : ∀ x : Fin d → ℤ,
    IntegrableOn (fun t => wordDiff w (latticeHeatKernel t) x) (Set.Ioi 0) ∧
      wordDiff w (fun y => ∫ t in Set.Ioi (0 : ℝ), latticeHeatKernel t y) x =
        ∫ t in Set.Ioi (0 : ℝ), wordDiff w (latticeHeatKernel t) x := by apply _root_.YangMills.Construction.FreeKernel.LatticeGreen.wordDiff_timeIntegral <;> assumption
private lemma latticeLaplacian_green (hEv : FreeKernel.IntegerHeatKernelEvolution)
    (hDec : FreeKernel.LatticeHeatKernelDecayBound) (hd : 3 ≤ d)
    (hInt : ∀ x : Fin d → ℤ, IntegrableOn (fun t => latticeHeatKernel t x) (Set.Ioi 0))
    (x : Fin d → ℤ) :
    latticeLaplacian (fun y => ∫ t in Set.Ioi (0 : ℝ), latticeHeatKernel t y) x =
      if x = 0 then 1 else 0 := by apply _root_.YangMills.Construction.FreeKernel.LatticeGreen.latticeLaplacian_timeIntegral <;> assumption
private lemma green_wordDiff_decay (hTime : FreeKernel.TimeIntegralOfHeatBound)
    (hEv : FreeKernel.IntegerHeatKernelEvolution) (hDec : FreeKernel.LatticeHeatKernelDecayBound) (hd : 3 ≤ d) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ w : List (Fin d ⊕ Fin d), w.length ≤ 3 → ∀ x : Fin d → ℤ,
      |wordDiff w (fun y => ∫ t in Set.Ioi (0 : ℝ), latticeHeatKernel t y) x| ≤
        c * (l1Length x + 1) ^ (-((d : ℝ) - 2 + (w.length : ℝ))) := by
  have hInt := fun x : Fin d → ℤ => integrableOn_Ioi_latticeHeatKernel hEv hDec hTime hd x
  obtain ⟨c₁, hc₁, hb⟩ := hDec d
  choose! C hC0 hC using hTime
  have hCsum : 0 ≤ ∑ k ∈ Finset.range 4, C (d + k) :=
    Finset.sum_nonneg fun k _ => hC0 _ (by omega)
  have hCle : ∀ k, k ≤ 3 → C (d + k) ≤ ∑ k ∈ Finset.range 4, C (d + k) := fun k hk =>
    Finset.single_le_sum (f := fun k => C (d + k)) (fun k _ => hC0 _ (by omega))
      (Finset.mem_range.2 (by omega))
  refine ⟨c₁ * ∑ k ∈ Finset.range 4, C (d + k), mul_nonneg hc₁ hCsum, ?_⟩
  intro w hw x
  have hR := l1Length_nonneg x
  obtain ⟨hint, hbound⟩ := hC (d + w.length) (by omega) (l1Length x) hR
  have hκ : -(((d + w.length : ℕ) : ℝ)) / 2 = -((d : ℝ) + (w.length : ℝ)) / 2 := by
    push_cast
    ring
  have hexp : 2 - ((d + w.length : ℕ) : ℝ) = -((d : ℝ) - 2 + (w.length : ℝ)) := by
    push_cast
    ring
  rw [hκ, hexp] at hbound
  rw [hκ] at hint
  rw [(wordDiff_integral_comm hInt w x).2, ← Real.norm_eq_abs]
  have hnorm : ‖∫ t in Set.Ioi (0 : ℝ), wordDiff w (latticeHeatKernel t) x‖ ≤
      ∫ t in Set.Ioi (0 : ℝ), c₁ * ((max t 1) ^ (-((d : ℝ) + (w.length : ℝ)) / 2) *
        Real.exp (-l1Length x / Real.sqrt (max t 1))) := by
    refine norm_integral_le_of_norm_le (hint.const_mul c₁) ?_
    refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun t ht => ?_)
    have hbt := hb t (le_of_lt ht) w hw x
    rw [mul_assoc] at hbt
    exact hbt
  rw [integral_const_mul] at hnorm
  have hpow : 0 ≤ (l1Length x + 1) ^ (-((d : ℝ) - 2 + (w.length : ℝ))) :=
    Real.rpow_nonneg (by linarith) _
  calc _ ≤ _ := hnorm
    _ ≤ c₁ * (C (d + w.length) * (l1Length x + 1) ^ (-((d : ℝ) - 2 + (w.length : ℝ)))) :=
        mul_le_mul_of_nonneg_left hbound hc₁
    _ ≤ c₁ * ((∑ k ∈ Finset.range 4, C (d + k)) *
          (l1Length x + 1) ^ (-((d : ℝ) - 2 + (w.length : ℝ)))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (hCle _ hw) hpow) hc₁
    _ = _ := by ring
theorem greenAsHeatTimeIntegral (hTime : FreeKernel.TimeIntegralOfHeatBound)
    (hEv : FreeKernel.IntegerHeatKernelEvolution) (hDec : FreeKernel.LatticeHeatKernelDecayBound) :
    greenAsHeatTimeIntegralStatement := by
  have h4 : 3 ≤ 4 := by norm_num
  have hInt := fun z : Fin 4 → ℤ => integrableOn_Ioi_latticeHeatKernel hEv hDec hTime h4 z
  refine ⟨hInt, fun z => latticeLaplacian_green hEv hDec h4 hInt z, ?_⟩
  obtain ⟨c, hc, hb⟩ := green_wordDiff_decay hTime hEv hDec h4
  refine ⟨c, hc, fun μ z => ?_⟩
  have hz := hb [Sum.inl μ] (by simp) z
  have e : -(((4 : ℕ) : ℝ) - 2 + (([Sum.inl μ] : List (Fin 4 ⊕ Fin 4)).length : ℝ)) = (-3 : ℝ) := by
    norm_num
  rw [e] at hz
  exact hz
end YangMills.Construction.MomentLaw
end
