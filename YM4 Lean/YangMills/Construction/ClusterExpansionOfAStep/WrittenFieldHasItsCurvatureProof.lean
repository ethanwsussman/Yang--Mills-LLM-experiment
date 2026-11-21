import YangMills.Construction.ClusterExpansionOfAStep.AnglesAlongOneDirection
import YangMills.Construction.ClusterExpansionOfAStep.WrittenFieldHasItsCurvature
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.TorusLumps
open YangMills.Construction.TorusFields
variable {n : ℕ}
private theorem val_add_one_eq [NeZero n] (a : ZMod n) :
    (a + 1).val = if a.val + 1 = n then 0 else a.val + 1 := by
  have hlt := ZMod.val_lt a
  rw [ZMod.val_add, ZMod.val_one_eq_one_mod, Nat.add_mod_mod]
  split_ifs with h
  · rw [h, Nat.mod_self]
  · exact Nat.mod_eq_of_lt (by omega)
private theorem coord_add_unitStep_self (x : TorusSite n) (i : Fin 4) : (x + unitStep n i) i = x i + 1 := by
  simp [unitStep]
private theorem coord_add_unitStep_of_ne (x : TorusSite n) {i k : Fin 4} (h : k ≠ i) :
    (x + unitStep n i) k = x k := by
  simp [unitStep, h]
private theorem planeAngle_of_ne (g : ℝ) {p q k : Fin 4} (y : TorusSite n) (h1 : k ≠ p) (h2 : k ≠ q) :
    planeAngle g p q y k = 0 := by
  simp [planeAngle, h1, h2]
private theorem planeAngle_congr (g : ℝ) (p q k : Fin 4) (y y' : TorusSite n) (h1 : y p = y' p)
    (h2 : y q = y' q) : planeAngle g p q y k = planeAngle g p q y' k := by
  simp [planeAngle, h1, h2]
private theorem angleCurl_planeAngle_same [NeZero n] (g : ℝ) {i j : Fin 4} (hij : i < j) (x : TorusSite n) :
    angleCurl (planeAngle g i j) x i j =
      g - (if (x i).val + 1 = n ∧ (x j).val + 1 = n then g * (n : ℝ) ^ 2 else 0) := by
  have hne : i ≠ j := ne_of_lt hij
  simp only [angleCurl, planeAngle, if_true, if_neg hne, coord_add_unitStep_self,
    coord_add_unitStep_of_ne x hne, coord_add_unitStep_of_ne x hne.symm, true_and, val_add_one_eq]
  by_cases h1 : (x i).val + 1 = n
  · have e1 : (((x i).val : ℕ) : ℝ) = (n : ℝ) - 1 := by
      have : (((x i).val : ℕ) : ℝ) + 1 = n := by exact_mod_cast h1
      linarith
    by_cases h2 : (x j).val + 1 = n
    · have e2 : (((x j).val : ℕ) : ℝ) = (n : ℝ) - 1 := by
        have : (((x j).val : ℕ) : ℝ) + 1 = n := by exact_mod_cast h2
        linarith
      simp only [if_pos h1, if_pos h2, if_pos (And.intro h1 h2), e1, e2]
      push_cast
      ring
    · simp only [if_pos h1, if_neg h2, if_neg (fun e : _ ∧ _ => h2 e.2), e1]
      push_cast
      ring
  · simp only [if_neg h1, if_neg (fun e : _ ∧ _ => h1 e.1)]
    push_cast
    ring
private theorem angleCurl_planeAngle_other (g : ℝ) {p q i j : Fin 4} (hpq : p < q) (hij : i < j)
    (hne : ¬(p = i ∧ q = j)) (x : TorusSite n) : angleCurl (planeAngle g p q) x i j = 0 := by
  have t1 : planeAngle g p q x i = planeAngle g p q (x + unitStep n j) i := by
    by_cases hj : j = p ∨ j = q
    · have hip : i ≠ p := by
        rcases hj with rfl | rfl
        · exact ne_of_lt hij
        · rintro rfl
          exact hne ⟨rfl, rfl⟩
      have hiq : i ≠ q := by
        rcases hj with rfl | rfl
        · exact ne_of_lt (hij.trans hpq)
        · exact ne_of_lt hij
      rw [planeAngle_of_ne g x hip hiq, planeAngle_of_ne g _ hip hiq]
    · push Not at hj
      exact planeAngle_congr g p q i _ _ (coord_add_unitStep_of_ne x (Ne.symm hj.1)).symm
        (coord_add_unitStep_of_ne x (Ne.symm hj.2)).symm
  have t2 : planeAngle g p q (x + unitStep n i) j = planeAngle g p q x j := by
    by_cases hi : i = p ∨ i = q
    · have hjq : j ≠ q := by
        rcases hi with rfl | rfl
        · rintro rfl
          exact hne ⟨rfl, rfl⟩
        · exact ne_of_gt hij
      have hjp : j ≠ p := by
        rcases hi with rfl | rfl
        · exact ne_of_gt hij
        · exact ne_of_gt (hpq.trans hij)
      rw [planeAngle_of_ne g x hjp hjq, planeAngle_of_ne g _ hjp hjq]
    · push Not at hi
      exact planeAngle_congr g p q j _ _ (coord_add_unitStep_of_ne x (Ne.symm hi.1))
        (coord_add_unitStep_of_ne x (Ne.symm hi.2))
  simp only [angleCurl]
  rw [t1, t2]
  ring
private theorem angleCurl_totalAngle [NeZero n] (γ : ℝ) (ω : Fin 4 → Fin 4 → ℝ) {i j : Fin 4} (hij : i < j)
    (x : TorusSite n) :
    angleCurl (totalAngle γ ω) x i j = γ * ω i j -
      (if (x i).val + 1 = n ∧ (x j).val + 1 = n then γ * ω i j * (n : ℝ) ^ 2 else 0) := by
  have hsum : angleCurl (totalAngle γ ω) x i j =
      ∑ p, ∑ q, if p < q then angleCurl (planeAngle (γ * ω p q) p q) x i j else 0 := by
    simp only [angleCurl, totalAngle, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
    split_ifs <;> simp
  rw [hsum, Finset.sum_eq_single i, Finset.sum_eq_single j, if_pos hij, angleCurl_planeAngle_same _ hij]
  · intro q _ hq
    split_ifs with h
    · exact angleCurl_planeAngle_other _ h hij (fun e => hq e.2) x
    · rfl
  · simp
  · intro p _ hp
    refine Finset.sum_eq_zero fun q _ => ?_
    split_ifs with h
    · exact angleCurl_planeAngle_other _ h hij (fun e => hp e.1) x
    · rfl
  · simp
theorem abelianFieldOfAngles_hasCurvature : AbelianFieldOfAnglesHasCurvature := by
  intro n _ X ω l hX _ hint
  refine ⟨⟨totalAngle _ ω, fun x i => rfl⟩, fun x i j hij => ?_⟩
  rw [holonomy_eq_expUnit_angleCurl X (totalAngle (2 * Real.pi * l / (n : ℝ) ^ 2) ω)
    (abelianFieldOfAngles n X (2 * Real.pi * l / (n : ℝ) ^ 2) ω) (fun _ _ => rfl), angleCurl_totalAngle _ _ hij]
  split_ifs with hc
  · obtain ⟨z, hz⟩ := hint i j
    have hn : (n : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne n
    have e : 2 * Real.pi * l / (n : ℝ) ^ 2 * ω i j * (n : ℝ) ^ 2 = 2 * Real.pi * z := by
      rw [← hz]
      field_simp
    rw [e, expUnit_sub_smul, expUnit_two_pi_int_smul X hX]
    simp
  · simp
end YangMills.Construction.TorusLumps
end
