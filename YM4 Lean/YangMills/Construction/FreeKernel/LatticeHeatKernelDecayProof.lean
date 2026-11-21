import YangMills.Construction.FreeKernel.IntegerHeatKernelDecay
import YangMills.Construction.FreeKernel.LatticeHeatKernelDecay
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.FreeKernel.LatticeDecay
open YangMills.Construction.FreeKernel.UnitLattice
theorem backwardDiff_commute_forwardDiff : Function.Commute backwardDiff forwardDiff := by
  intro f
  funext n
  simp only [forwardDiff, backwardDiff, sub_add_cancel, add_sub_cancel_right]
  ring
theorem prod_sub_prod_eq_prod_of_coord {d : ℕ} (F F' : Fin d → ℤ → ℝ) (μ : Fin d)
    (n m : Fin d → ℤ) (hm : ∀ ν, ν ≠ μ → m ν = n ν) (hF : ∀ ν, ν ≠ μ → F' ν = F ν)
    (hμ : F' μ (n μ) = F μ (m μ) - F μ (n μ)) :
    ∏ ν, F ν (m ν) - ∏ ν, F ν (n ν) = ∏ ν, F' ν (n ν) := by
  have hrest : ∀ G : Fin d → ℝ, ∏ ν, G ν = G μ * ∏ ν ∈ Finset.univ.erase μ, G ν :=
    fun G => (Finset.mul_prod_erase Finset.univ G (Finset.mem_univ μ)).symm
  rw [hrest (fun ν => F ν (m ν)), hrest (fun ν => F ν (n ν)), hrest (fun ν => F' ν (n ν))]
  have h1 : ∏ ν ∈ Finset.univ.erase μ, F ν (m ν) = ∏ ν ∈ Finset.univ.erase μ, F ν (n ν) :=
    Finset.prod_congr rfl fun ν hν => by rw [hm ν (Finset.ne_of_mem_erase hν)]
  have h2 : ∏ ν ∈ Finset.univ.erase μ, F' ν (n ν) = ∏ ν ∈ Finset.univ.erase μ, F ν (n ν) :=
    Finset.prod_congr rfl fun ν hν => by rw [hF ν (Finset.ne_of_mem_erase hν)]
  simp only [h1, h2, hμ]
  ring
theorem wordDiff_latticeHeatKernel_eq_prod (T : ℝ) {d : ℕ} (β : List (Fin d ⊕ Fin d)) :
    ∃ a a' : Fin d → ℕ, ∑ μ, (a μ + a' μ) = β.length ∧
      ∀ n, wordDiff β (latticeHeatKernel T) n =
        ∏ μ, forwardDiff^[a μ] (backwardDiff^[a' μ] (integerHeatKernel T)) (n μ) := by
  induction β with
  | nil => exact ⟨0, 0, by simp, fun n => by simp [wordDiff, latticeHeatKernel]⟩
  | cons o β ih =>
    obtain ⟨a, a', hs, hw⟩ := ih
    have hcons : ∀ f : (Fin d → ℤ) → ℝ, wordDiff (o :: β) f =
        Sum.elim (fun μ => latticeForwardDiff μ (wordDiff β f))
          (fun μ => latticeBackwardDiff μ (wordDiff β f)) o :=
      fun f => rfl
    rcases o with μ | μ
    · refine ⟨a + Pi.single μ 1, a', ?_, fun n => ?_⟩
      · simp only [Pi.add_apply, Finset.sum_add_distrib, List.length_cons] at hs ⊢
        simp only [Finset.sum_pi_single', Finset.mem_univ, if_true]
        omega
      · rw [hcons]
        simp only [Sum.elim_inl, latticeForwardDiff, hw]
        refine prod_sub_prod_eq_prod_of_coord _ _ μ n _ (fun ν h => ?_) (fun ν h => ?_) ?_
        · simp [h]
        · simp [h]
        · simp only [Pi.add_apply, Pi.single_eq_same, Function.iterate_succ_apply']
          rfl
    · refine ⟨a, a' + Pi.single μ 1, ?_, fun n => ?_⟩
      · simp only [Pi.add_apply, Finset.sum_add_distrib, List.length_cons] at hs ⊢
        simp only [Finset.sum_pi_single', Finset.mem_univ, if_true]
        omega
      · rw [hcons]
        simp only [Sum.elim_inr, latticeBackwardDiff, hw]
        refine prod_sub_prod_eq_prod_of_coord _ _ μ n _ (fun ν h => ?_) (fun ν h => ?_) ?_
        · simp [h]
        · simp [h]
        · simp only [Pi.add_apply, Pi.single_eq_same, Function.iterate_succ_apply', Pi.sub_apply]
          rw [← backwardDiff_commute_forwardDiff.iterate_right (a μ) _]
          rfl
theorem latticeHeatKernelDecayBound_of_integer (hline : IntegerHeatKernelDecayBound) :
    LatticeHeatKernelDecayBound := by
  obtain ⟨c, hc, hb⟩ := hline
  intro d
  refine ⟨c ^ d, by positivity, fun T hT β hβ n => ?_⟩
  obtain ⟨a, a', hs, hw⟩ := wordDiff_latticeHeatKernel_eq_prod T β
  have hθ : 0 < max T 1 := lt_max_of_lt_right one_pos
  have hle : ∀ μ, a μ + a' μ ≤ 3 := fun μ =>
    (Finset.single_le_sum (f := fun ν => a ν + a' ν) (fun _ _ => Nat.zero_le _)
      (Finset.mem_univ μ)).trans (hs.le.trans hβ)
  have he : ∑ μ, (-((1 : ℝ) + a μ + a' μ) / 2) = -((d : ℝ) + (β.length : ℝ)) / 2 := by
    rw [← hs, ← Finset.sum_div, Finset.sum_neg_distrib]
    push_cast
    simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, mul_one]
    ring
  have hx : ∑ μ, (-|(n μ : ℝ)| / Real.sqrt (max T 1)) =
      -l1Length n / Real.sqrt (max T 1) := by
    rw [← Finset.sum_div, Finset.sum_neg_distrib]
    rfl
  rw [hw, Finset.abs_prod]
  calc ∏ μ, |forwardDiff^[a μ] (backwardDiff^[a' μ] (integerHeatKernel T)) (n μ)|
      ≤ ∏ μ, (c * (max T 1) ^ (-((1 : ℝ) + a μ + a' μ) / 2) *
          Real.exp (-|(n μ : ℝ)| / Real.sqrt (max T 1))) :=
        Finset.prod_le_prod (fun _ _ => abs_nonneg _) (fun μ _ => hb T hT _ _ (hle μ) (n μ))
    _ = c ^ d * (max T 1) ^ (-((d : ℝ) + (β.length : ℝ)) / 2) *
          Real.exp (-l1Length n / Real.sqrt (max T 1)) := by
        rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, ← Real.rpow_sum_of_pos hθ,
          ← Real.exp_sum, he, hx]
        simp
end YangMills.Construction.FreeKernel.LatticeDecay
