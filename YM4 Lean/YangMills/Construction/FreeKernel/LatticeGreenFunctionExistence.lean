import YangMills.Construction.FreeKernel.HeatBoundTimeIntegral
import YangMills.Construction.FreeKernel.IntegerHeatEquation
import YangMills.Construction.FreeKernel.LatticeHeatKernelDecay
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.FreeKernel.LatticeGreen
open YangMills.Construction.FreeKernel.UnitLattice MeasureTheory Filter Topology
variable {d : ℕ}
lemma latticeHeatKernel_eq_of_eq_off (T : ℝ) (x y : Fin d → ℤ) (μ : Fin d)
    (h : ∀ j, j ≠ μ → y j = x j) :
    latticeHeatKernel T y = integerHeatKernel T (y μ) * ∏ j ∈ Finset.univ.erase μ, integerHeatKernel T (x j) := by
  unfold latticeHeatKernel
  rw [← Finset.mul_prod_erase Finset.univ (fun j => integerHeatKernel T (y j)) (Finset.mem_univ μ)]
  congr 1
  exact Finset.prod_congr rfl fun j hj => by rw [h j (Finset.ne_of_mem_erase hj)]
lemma hasDerivAt_latticeHeatKernel (hE : FreeKernel.IntegerHeatKernelEvolution) (T : ℝ)
    (x : Fin d → ℤ) :
    HasDerivAt (fun t => latticeHeatKernel t x) (-latticeLaplacian (latticeHeatKernel T) x) T := by
  have h := HasDerivAt.fun_finsetProd (u := Finset.univ) (x := T)
    (f := fun μ t => integerHeatKernel t (x μ))
    (f' := fun μ => integerHeatKernel T (x μ + 1) + integerHeatKernel T (x μ - 1) - 2 * integerHeatKernel T (x μ))
    (fun μ _ => hE.2 T (x μ))
  have e : (∑ μ, (∏ j ∈ Finset.univ.erase μ, integerHeatKernel T (x j)) •
      (integerHeatKernel T (x μ + 1) + integerHeatKernel T (x μ - 1) - 2 * integerHeatKernel T (x μ))) =
      -latticeLaplacian (latticeHeatKernel T) x := by
    unfold latticeLaplacian
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun μ _ => ?_
    have h0 := latticeHeatKernel_eq_of_eq_off T x x μ (fun _ _ => rfl)
    have h1 := latticeHeatKernel_eq_of_eq_off T x (x + Pi.single μ 1) μ
      (fun j hj => by simp [Pi.single_eq_of_ne hj])
    have h2 := latticeHeatKernel_eq_of_eq_off T x (x - Pi.single μ 1) μ
      (fun j hj => by simp [Pi.single_eq_of_ne hj])
    simp only [Pi.add_apply, Pi.sub_apply, Pi.single_eq_same] at h1 h2
    rw [h0, h1, h2, smul_eq_mul]
    ring
  rw [e] at h
  exact h
lemma continuous_latticeHeatKernel (hE : FreeKernel.IntegerHeatKernelEvolution) (x : Fin d → ℤ) :
    Continuous (fun t => latticeHeatKernel t x) :=
  continuous_iff_continuousAt.2 fun T => (hasDerivAt_latticeHeatKernel hE T x).continuousAt
lemma l1Length_nonneg (x : Fin d → ℤ) : 0 ≤ l1Length x :=
  Finset.sum_nonneg fun _ _ => abs_nonneg _
lemma integrableOn_latticeHeatKernel (hE : FreeKernel.IntegerHeatKernelEvolution)
    (hD : FreeKernel.LatticeHeatKernelDecayBound) (hB : FreeKernel.TimeIntegralOfHeatBound) (hd : 3 ≤ d)
    (x : Fin d → ℤ) : IntegrableOn (fun T => latticeHeatKernel T x) (Set.Ioi 0) := by
  obtain ⟨c, -, hdec⟩ := hD d
  obtain ⟨c', -, hint⟩ := hB d hd
  refine Integrable.mono' (((hint _ (l1Length_nonneg x)).1).const_mul c)
    (continuous_latticeHeatKernel hE x).aestronglyMeasurable ?_
  refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun T hT => ?_)
  have h := hdec T (le_of_lt hT) [] (by simp) x
  have e : -((d : ℝ) + (([] : List (Fin d ⊕ Fin d)).length : ℝ)) / 2 = -(d : ℝ) / 2 := by simp
  rw [e, mul_assoc] at h
  exact h
lemma tendsto_latticeHeatKernel_atTop (hD : FreeKernel.LatticeHeatKernelDecayBound) (hd : 3 ≤ d)
    (x : Fin d → ℤ) : Tendsto (fun T => latticeHeatKernel T x) atTop (𝓝 0) := by
  obtain ⟨c, hc, hdec⟩ := hD d
  have hlim : Tendsto (fun T : ℝ => c * T ^ (-((d : ℝ) / 2))) atTop (𝓝 0) := by
    simpa using (tendsto_rpow_neg_atTop (y := (d : ℝ) / 2) (by positivity)).const_mul c
  refine squeeze_zero_norm' ?_ hlim
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with T hT
  have h := hdec T (by linarith) [] (by simp) x
  have e : -((d : ℝ) + (([] : List (Fin d ⊕ Fin d)).length : ℝ)) / 2 = -((d : ℝ) / 2) := by
    simp [neg_div]
  rw [max_eq_left hT, e] at h
  have hexp : Real.exp (-l1Length x / Real.sqrt T) ≤ 1 :=
    Real.exp_le_one_iff.2
      (div_nonpos_of_nonpos_of_nonneg (neg_nonpos.2 (l1Length_nonneg x)) (Real.sqrt_nonneg _))
  have hpow : 0 ≤ c * T ^ (-((d : ℝ) / 2)) :=
    mul_nonneg hc (Real.rpow_nonneg (by linarith) _)
  calc ‖latticeHeatKernel T x‖ = |wordDiff [] (latticeHeatKernel T) x| := rfl
    _ ≤ c * T ^ (-((d : ℝ) / 2)) * Real.exp (-l1Length x / Real.sqrt T) := h
    _ ≤ c * T ^ (-((d : ℝ) / 2)) * 1 := mul_le_mul_of_nonneg_left hexp hpow
    _ = c * T ^ (-((d : ℝ) / 2)) := mul_one _
lemma latticeHeatKernel_zero (hE : FreeKernel.IntegerHeatKernelEvolution) (x : Fin d → ℤ) :
    latticeHeatKernel 0 x = if x = 0 then 1 else 0 := by
  unfold latticeHeatKernel
  split_ifs with h
  · subst h
    exact Finset.prod_eq_one fun μ _ => by rw [hE.1]; simp
  · obtain ⟨μ, hμ⟩ := Function.ne_iff.1 h
    refine Finset.prod_eq_zero (Finset.mem_univ μ) ?_
    rw [hE.1]
    exact if_neg hμ
lemma wordDiff_timeIntegral (hI : ∀ x : Fin d → ℤ, IntegrableOn (fun T => latticeHeatKernel T x) (Set.Ioi 0))
    (β : List (Fin d ⊕ Fin d)) : ∀ x : Fin d → ℤ,
    IntegrableOn (fun T => wordDiff β (latticeHeatKernel T) x) (Set.Ioi 0) ∧
      wordDiff β (fun y => ∫ T in Set.Ioi (0 : ℝ), latticeHeatKernel T y) x =
        ∫ T in Set.Ioi (0 : ℝ), wordDiff β (latticeHeatKernel T) x := by
  induction β with
  | nil => exact fun x => ⟨hI x, rfl⟩
  | cons o β ih =>
    intro x
    cases o with
    | inl μ =>
      obtain ⟨i1, e1⟩ := ih (x + Pi.single μ 1)
      obtain ⟨i2, e2⟩ := ih x
      refine ⟨i1.sub i2, ?_⟩
      change wordDiff β _ (x + Pi.single μ 1) - wordDiff β _ x =
        ∫ T in Set.Ioi (0 : ℝ), (wordDiff β (latticeHeatKernel T) (x + Pi.single μ 1) -
          wordDiff β (latticeHeatKernel T) x)
      rw [e1, e2, integral_sub i1 i2]
    | inr μ =>
      obtain ⟨i1, e1⟩ := ih (x - Pi.single μ 1)
      obtain ⟨i2, e2⟩ := ih x
      refine ⟨i1.sub i2, ?_⟩
      change wordDiff β _ (x - Pi.single μ 1) - wordDiff β _ x =
        ∫ T in Set.Ioi (0 : ℝ), (wordDiff β (latticeHeatKernel T) (x - Pi.single μ 1) -
          wordDiff β (latticeHeatKernel T) x)
      rw [e1, e2, integral_sub i1 i2]
lemma latticeLaplacian_timeIntegral (hE : FreeKernel.IntegerHeatKernelEvolution)
    (hD : FreeKernel.LatticeHeatKernelDecayBound) (hd : 3 ≤ d)
    (hI : ∀ x : Fin d → ℤ, IntegrableOn (fun T => latticeHeatKernel T x) (Set.Ioi 0))
    (x : Fin d → ℤ) :
    latticeLaplacian (fun y => ∫ T in Set.Ioi (0 : ℝ), latticeHeatKernel T y) x =
      if x = 0 then 1 else 0 := by
  have hterm : ∀ μ : Fin d, IntegrableOn (fun T => 2 * latticeHeatKernel T x -
      latticeHeatKernel T (x + Pi.single μ 1) - latticeHeatKernel T (x - Pi.single μ 1)) (Set.Ioi 0) :=
    fun μ => (((hI x).const_mul 2).sub (hI _)).sub (hI _)
  have hsum : IntegrableOn (fun T => latticeLaplacian (latticeHeatKernel T) x) (Set.Ioi 0) :=
    integrable_finsetSum _ fun μ _ => hterm μ
  have hG : latticeLaplacian (fun y => ∫ T in Set.Ioi (0 : ℝ), latticeHeatKernel T y) x =
      ∫ T in Set.Ioi (0 : ℝ), latticeLaplacian (latticeHeatKernel T) x := by
    unfold latticeLaplacian
    rw [integral_finsetSum _ fun μ _ => hterm μ]
    refine Finset.sum_congr rfl fun μ _ => ?_
    have i0 := (hI x).const_mul 2
    have e1 : ∫ T in Set.Ioi (0 : ℝ), (2 * latticeHeatKernel T x - latticeHeatKernel T (x + Pi.single μ 1) -
        latticeHeatKernel T (x - Pi.single μ 1)) =
        (∫ T in Set.Ioi (0 : ℝ), (2 * latticeHeatKernel T x - latticeHeatKernel T (x + Pi.single μ 1))) -
          ∫ T in Set.Ioi (0 : ℝ), latticeHeatKernel T (x - Pi.single μ 1) :=
      integral_sub (i0.sub (hI _)) (hI _)
    have e2 : ∫ T in Set.Ioi (0 : ℝ), (2 * latticeHeatKernel T x - latticeHeatKernel T (x + Pi.single μ 1)) =
        (∫ T in Set.Ioi (0 : ℝ), 2 * latticeHeatKernel T x) -
          ∫ T in Set.Ioi (0 : ℝ), latticeHeatKernel T (x + Pi.single μ 1) :=
      integral_sub i0 (hI _)
    rw [e1, e2, integral_const_mul]
  have hF := integral_Ioi_of_hasDerivAt_of_tendsto (a := 0) (m := 0)
    (f := fun T => latticeHeatKernel T x)
    (f' := fun T => -latticeLaplacian (latticeHeatKernel T) x)
    (continuous_latticeHeatKernel hE x).continuousWithinAt
    (fun T _ => hasDerivAt_latticeHeatKernel hE T x) hsum.neg (tendsto_latticeHeatKernel_atTop hD hd x)
  rw [integral_neg, latticeHeatKernel_zero hE, zero_sub, neg_inj] at hF
  rw [hG, hF]
end YangMills.Construction.FreeKernel.LatticeGreen
