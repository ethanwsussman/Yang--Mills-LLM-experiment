import YangMills.Construction.Continuum.FunctionsVanishingOnAnOpenSet
import Mathlib
set_option autoImplicit false
open scoped ContDiff Topology
noncomputable section
namespace YangMills.Construction.ConfigSpace
namespace VanishingOnOpen
variable {n : ℕ}
theorem iteratedPartial_induction (P : (Config n → ℂ) → Prop)
    (hP : ∀ i μ g, P g → P (coordPartial i μ g)) (α : MultiIndex n) {f : Config n → ℂ}
    (hf : P f) : P (iteratedPartial α f) := by
  have hiter : ∀ (i : Fin n) (μ : Fin 4) (m : ℕ) (g : Config n → ℂ), P g →
      P ((coordPartial i μ)^[m] g) := by
    intro i μ m
    induction m with
    | zero => intro g hg; exact hg
    | succ m ih =>
      intro g hg
      rw [Function.iterate_succ_apply]
      exact ih _ (hP i μ g hg)
  have hinner : ∀ (i : Fin n) (l : List (Fin 4)) (g : Config n → ℂ), P g →
      P (l.foldr (fun μ h' => (coordPartial i μ)^[α i μ] h') g) := by
    intro i l g hg
    induction l with
    | nil => exact hg
    | cons μ l ih => exact hiter i μ _ _ ih
  have houter : ∀ l : List (Fin n), P (l.foldr (fun i h => (List.finRange 4).foldr
      (fun μ h' => (coordPartial i μ)^[α i μ] h') h) f) := by
    intro l
    induction l with
    | nil => exact hf
    | cons i l ih => exact hinner i _ _ ih
  exact houter _
theorem contDiff_and_eqOn_zero_coordPartial {W : Set (Config n)} (hW : IsOpen W) (i : Fin n)
    (μ : Fin 4) {g : Config n → ℂ} (hg : ContDiff ℝ ∞ g ∧ ∀ x ∈ W, g x = 0) :
    ContDiff ℝ ∞ (coordPartial i μ g) ∧ ∀ x ∈ W, coordPartial i μ g x = 0 := by
  obtain ⟨hs, hz⟩ := hg
  have hd : Differentiable ℝ g := hs.differentiable (by simp)
  have heq : coordPartial i μ g =
      fun x => fderiv ℝ g x (Pi.single i (Pi.single μ 1)) := by
    funext x
    exact (hd x).lineDeriv_eq_fderiv
  constructor
  · rw [heq]
    exact (hs.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const
  · intro x hx
    have hloc : g =ᶠ[𝓝 x] fun _ => 0 := by
      filter_upwards [hW.mem_nhds hx] with y hy using hz y hy
    rw [heq]
    show fderiv ℝ g x _ = 0
    rw [hloc.fderiv_eq]
    simp
theorem flatOn_closure_of_eqOn_zero {W : Set (Config n)} {f : Config n → ℂ} (hW : IsOpen W)
    (hs : ContDiff ℝ ∞ f) (hz : ∀ x ∈ W, f x = 0) : FlatOn f (closure W) := by
  refine ⟨hs, fun x hx => ⟨hs, fun α => ?_⟩⟩
  have h := iteratedPartial_induction (fun g => ContDiff ℝ ∞ g ∧ ∀ x ∈ W, g x = 0)
    (fun i μ g hg => contDiff_and_eqOn_zero_coordPartial hW i μ hg) α (f := f) ⟨hs, hz⟩
  have hcl : IsClosed {y | iteratedPartial α f y = 0} :=
    isClosed_eq h.1.continuous continuous_const
  exact closure_minimal (fun y hy => h.2 y hy) hcl hx
def timeBasisVec (i : Fin n) : Config n := Pi.single i (Pi.single 3 1)
theorem argTime_add_smul_timeBasisVec (x : Config n) (t : ℝ) (i j : Fin n) :
    argTime (x + t • timeBasisVec i) j = argTime x j + if j = i then t else 0 := by
  by_cases h : j = i
  · subst h
    simp [argTime, lastCoord, timeBasisVec]
  · simp [argTime, lastCoord, timeBasisVec, h]
theorem mem_closure_of_forall_pos_add_smul {W : Set (Config n)} {x v : Config n} {c : ℝ}
    (h : ∀ t : ℝ, 0 < t → x + (c * t) • v ∈ W) : x ∈ closure W := by
  have hc : Filter.Tendsto (fun t : ℝ => x + (c * t) • v) (𝓝[>] 0) (𝓝 x) := by
    have hcont : Continuous (fun t : ℝ => x + (c * t) • v) := by fun_prop
    have h0 := hcont.tendsto 0
    simp only [mul_zero, zero_smul, add_zero] at h0
    exact h0.mono_left nhdsWithin_le_nhds
  exact mem_closure_of_tendsto hc (Filter.eventually_of_mem self_mem_nhdsWithin h)
theorem continuous_argTime (i : Fin n) : Continuous fun x : Config n => argTime x i :=
  (continuous_apply (3 : Fin 4)).comp (continuous_apply i)
theorem isOpen_exists_argTime_neg : IsOpen {x : Config n | ∃ i, argTime x i < 0} := by
  have h : {x : Config n | ∃ i, argTime x i < 0} = ⋃ i, {x : Config n | argTime x i < 0} := by
    ext x
    simp
  rw [h]
  exact isOpen_iUnion fun i => isOpen_lt (continuous_argTime i) continuous_const
theorem mem_closure_exists_argTime_neg {x : Config n} {i : Fin n} (hi : argTime x i ≤ 0) :
    x ∈ closure {y : Config n | ∃ j, argTime y j < 0} := by
  refine mem_closure_of_forall_pos_add_smul (c := -1) (v := timeBasisVec i) fun t ht => ⟨i, ?_⟩
  rw [argTime_add_smul_timeBasisVec]
  simp only [if_true]
  linarith
theorem mem_schwartzFlatOffPosTime_of_vanish_neg {f : Config n → ℂ}
    (hf : f ∈ schwartzFlatOffDiagonal n)
    (hz : ∀ (x : Config n) (i : Fin n), argTime x i < 0 → f x = 0) :
    f ∈ schwartzFlatOffPosTime n := by
  obtain ⟨hS, -, -, hdiag⟩ := hf
  have hflat := flatOn_closure_of_eqOn_zero isOpen_exists_argTime_neg hS.1
    (fun x (hx : ∃ i, argTime x i < 0) => hx.elim fun i hi => hz x i hi)
  refine ⟨hS, hS.1, isOpen_posTimeSet, fun x hx => ?_⟩
  by_cases hd : x ∈ distinctArgs n
  · have hex : ∃ i, argTime x i ≤ 0 := by
      by_contra hne
      push Not at hne
      exact hx ⟨hd, hne⟩
    obtain ⟨i, hi⟩ := hex
    exact hflat.2 x (mem_closure_exists_argTime_neg hi)
  · exact hdiag x hd
theorem orderedPosTimeSet_subset : orderedPosTimeSet n ⊆ posTimeSet n := by
  rintro x ⟨hpos, hmono⟩
  refine ⟨?_, hpos⟩
  show Function.Injective x
  intro i j e
  exact hmono.injective (by simp only [argTime, e])
def disorderedSet (n : ℕ) : Set (Config n) :=
  {x | ∃ i, argTime x i < 0} ∪ ⋃ (i : Fin n) (j : Fin n) (_ : i < j), {x | argTime x j < argTime x i}
theorem isOpen_disorderedSet : IsOpen (disorderedSet n) :=
  isOpen_exists_argTime_neg.union <| isOpen_iUnion fun i => isOpen_iUnion fun j =>
    isOpen_iUnion fun _ => isOpen_lt (continuous_argTime j) (continuous_argTime i)
theorem not_mem_orderedPosTimeSet_of_mem_disorderedSet {x : Config n}
    (hx : x ∈ disorderedSet n) : x ∉ orderedPosTimeSet n := by
  rintro ⟨hpos, hmono⟩
  rcases hx with ⟨i, hi⟩ | hx
  · exact absurd (hpos i) (not_lt.2 hi.le)
  · simp only [Set.mem_iUnion, exists_prop] at hx
    obtain ⟨i, j, hij, h⟩ := hx
    exact absurd (hmono hij) (not_lt.2 (le_of_lt h))
theorem mem_closure_disorderedSet {x : Config n} (hx : x ∉ orderedPosTimeSet n) :
    x ∈ closure (disorderedSet n) := by
  by_cases hpos : ∀ i, 0 < argTime x i
  · have hnot : ¬ StrictMono (argTime x) := fun hm => hx ⟨hpos, hm⟩
    simp only [StrictMono, not_forall, not_lt] at hnot
    obtain ⟨a, b, hab, h⟩ := hnot
    refine mem_closure_of_forall_pos_add_smul (c := 1) (v := timeBasisVec a) fun t ht => Or.inr ?_
    simp only [Set.mem_iUnion, exists_prop]
    refine ⟨a, b, hab, ?_⟩
    show argTime _ b < argTime _ a
    rw [argTime_add_smul_timeBasisVec, argTime_add_smul_timeBasisVec]
    simp only [if_true, if_neg hab.ne']
    linarith
  · push Not at hpos
    obtain ⟨i, hi⟩ := hpos
    exact closure_mono Set.subset_union_left (mem_closure_exists_argTime_neg hi)
theorem mem_schwartzFlatOffPosTime_of_vanish_unordered {f : Config n → ℂ} (hS : IsSchwartz f)
    (hz : ∀ x, x ∉ orderedPosTimeSet n → f x = 0) :
    f ∈ schwartzFlatOffPosTime n := by
  have hflat := flatOn_closure_of_eqOn_zero isOpen_disorderedSet hS.1
    (fun x hx => hz x (not_mem_orderedPosTimeSet_of_mem_disorderedSet hx))
  exact ⟨hS, hS.1, isOpen_posTimeSet, fun x hx =>
    hflat.2 x (mem_closure_disorderedSet fun h => hx (orderedPosTimeSet_subset h))⟩
end VanishingOnOpen
theorem vanishingOnOpenProperties_holds : VanishingOnOpenProperties :=
  fun _ _ => ⟨fun _ _ hW hs hz => VanishingOnOpen.flatOn_closure_of_eqOn_zero hW hs hz,
    fun _ hf hz => VanishingOnOpen.mem_schwartzFlatOffPosTime_of_vanish_neg hf hz,
    VanishingOnOpen.orderedPosTimeSet_subset,
    fun _ hS hz => VanishingOnOpen.mem_schwartzFlatOffPosTime_of_vanish_unordered hS hz⟩
end YangMills.Construction.ConfigSpace
end
