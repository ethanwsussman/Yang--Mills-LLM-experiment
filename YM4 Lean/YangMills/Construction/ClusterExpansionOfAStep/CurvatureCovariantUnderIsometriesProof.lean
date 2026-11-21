import YangMills.Construction.ClusterExpansionOfAStep.AnglesAlongOneDirection
import YangMills.Construction.ClusterExpansionOfAStep.CurvatureCovariantUnderIsometries
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.TorusLumps
open YangMills.Construction.TorusFields
open YangMills.Construction.BlockAverages (expUnit)
variable {n : ℕ}
private def signedPreimage (p : Equiv.Perm (Fin 4)) (s : Fin 4 → ℤ) (y : TorusSite n) : TorusSite n :=
  fun k => ((s (p.symm k) : ℤ) : ZMod n) * y (p.symm k)
private theorem signedPreimage_add_of_pos (p : Equiv.Perm (Fin 4)) (s : Fin 4 → ℤ) (y : TorusSite n) (a : Fin 4)
    (ha : s a = 1) :
    signedPreimage p s (y + unitStep n a) = signedPreimage p s y + unitStep n (p a) := by
  funext k
  by_cases hk : k = p a
  · subst hk
    simp [signedPreimage, unitStep, ha, mul_add]
  · have hk' : p.symm k ≠ a := fun e => hk (by rw [← e]; simp)
    simp [signedPreimage, unitStep, Pi.single_apply, hk, hk']
private theorem signedPreimage_add_of_neg (p : Equiv.Perm (Fin 4)) (s : Fin 4 → ℤ) (y : TorusSite n) (a : Fin 4)
    (ha : s a = -1) :
    signedPreimage p s (y + unitStep n a) = signedPreimage p s y - unitStep n (p a) := by
  funext k
  by_cases hk : k = p a
  · subst hk
    simp [signedPreimage, unitStep, ha, mul_add]
    ring
  · have hk' : p.symm k ≠ a := fun e => hk (by rw [← e]; simp)
    simp [signedPreimage, unitStep, Pi.single_apply, hk, hk']
private theorem signedPreimage_mapSite (p : Equiv.Perm (Fin 4)) (s : Fin 4 → ℤ) (hs : ∀ i, s i = 1 ∨ s i = -1)
    (x : TorusSite n) :
    signedPreimage p s ((⟨p, s, 0, hs⟩ : TorusIsometry).mapSite x) = x := by
  funext k
  simp only [signedPreimage, TorusIsometry.mapSite, Pi.zero_apply, Int.cast_zero, add_zero,
    Equiv.apply_symm_apply]
  rcases hs (p.symm k) with h | h <;> simp [h]
private def imageAngles (θ : TorusSite n → Fin 4 → ℝ) (p : Equiv.Perm (Fin 4)) (s : Fin 4 → ℤ) (y : TorusSite n)
    (a : Fin 4) : ℝ :=
  if s a = 1 then θ (signedPreimage p s y) (p a) else - θ (signedPreimage p s (y + unitStep n a)) (p a)
private theorem imageAngles_of_pos (θ : TorusSite n → Fin 4 → ℝ) (p : Equiv.Perm (Fin 4)) (s : Fin 4 → ℤ)
    (y : TorusSite n) (a : Fin 4) (ha : s a = 1) :
    imageAngles θ p s y a = θ (signedPreimage p s y) (p a) := by
  simp [imageAngles, ha]
private theorem imageAngles_of_neg (θ : TorusSite n → Fin 4 → ℝ) (p : Equiv.Perm (Fin 4)) (s : Fin 4 → ℤ)
    (y : TorusSite n) (a : Fin 4) (ha : s a = -1) :
    imageAngles θ p s y a = - θ (signedPreimage p s y - unitStep n (p a)) (p a) := by
  simp [imageAngles, ha, signedPreimage_add_of_neg p s y a ha]
private theorem angleCurl_swap (θ : TorusSite n → Fin 4 → ℝ) (x : TorusSite n) (i j : Fin 4) :
    angleCurl θ x j i = - angleCurl θ x i j := by
  simp only [angleCurl]
  ring
theorem isometryRotatesCurvature_holds : CurvatureUnderAnIsometry := by
  rintro n _ X ω γ V p s hs hω ⟨⟨θ, hθ⟩, hcurv⟩
  refine ⟨fun y a => expUnit (imageAngles θ p s y a • X), ?_, ⟨imageAngles θ p s, fun _ _ => rfl⟩, ?_⟩
  · intro x k
    have hpk : p (p.symm k) = k := by simp
    simp only
    by_cases ha : s (p.symm k) = 1
    · rw [if_pos ha, imageAngles_of_pos θ p s _ _ ha, signedPreimage_mapSite p s hs, hpk, hθ]
    · rw [if_neg ha]
      simp only [imageAngles, if_neg ha, sub_add_cancel, signedPreimage_mapSite, hpk, expUnit_neg_smul,
        inv_inv, hθ]
  · intro y a b hab
    have hne : p a ≠ p b := fun e => (ne_of_lt hab) (p.injective e)
    have hall : ∀ x, expUnit (angleCurl θ x (p a) (p b) • X) = expUnit ((γ * ω (p a) (p b)) • X) := by
      intro x
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · rw [← holonomy_eq_expUnit_angleCurl X θ V hθ, hcurv x _ _ hlt]
      · have hrev := hcurv x _ _ hgt
        rw [holonomy_eq_expUnit_angleCurl X θ V hθ] at hrev
        rw [angleCurl_swap, expUnit_neg_smul, hrev, ← expUnit_neg_smul, hω (p b) (p a)]
        congr 2
        ring
    rw [holonomy_eq_expUnit_angleCurl X _ (fun y a => expUnit (imageAngles θ p s y a • X)) (fun _ _ => rfl)]
    rcases hs a with ha | ha <;> rcases hs b with hb | hb
    · have e : angleCurl (imageAngles θ p s) y a b = angleCurl θ (signedPreimage p s y) (p a) (p b) := by
        simp only [angleCurl]
        rw [imageAngles_of_pos θ p s y a ha, imageAngles_of_pos θ p s _ b hb, imageAngles_of_pos θ p s _ a ha,
          imageAngles_of_pos θ p s y b hb, signedPreimage_add_of_pos p s y a ha,
          signedPreimage_add_of_pos p s y b hb]
      rw [e, hall]
      simp [ha, hb]
    · have e : angleCurl (imageAngles θ p s) y a b =
          - angleCurl θ (signedPreimage p s y - unitStep n (p b)) (p a) (p b) := by
        simp only [angleCurl]
        rw [imageAngles_of_pos θ p s y a ha, imageAngles_of_neg θ p s _ b hb, imageAngles_of_pos θ p s _ a ha,
          imageAngles_of_neg θ p s y b hb, signedPreimage_add_of_pos p s y a ha,
          signedPreimage_add_of_neg p s y b hb, sub_add_cancel,
          show signedPreimage p s y + unitStep n (p a) - unitStep n (p b)
            = signedPreimage p s y - unitStep n (p b) + unitStep n (p a) by abel]
        ring
      rw [e, expUnit_neg_smul, hall, ← expUnit_neg_smul]
      congr 2
      simp [ha, hb]
    · have e : angleCurl (imageAngles θ p s) y a b =
          - angleCurl θ (signedPreimage p s y - unitStep n (p a)) (p a) (p b) := by
        simp only [angleCurl]
        rw [imageAngles_of_neg θ p s y a ha, imageAngles_of_pos θ p s _ b hb, imageAngles_of_neg θ p s _ a ha,
          imageAngles_of_pos θ p s y b hb, signedPreimage_add_of_neg p s y a ha,
          signedPreimage_add_of_pos p s y b hb, sub_add_cancel,
          show signedPreimage p s y + unitStep n (p b) - unitStep n (p a)
            = signedPreimage p s y - unitStep n (p a) + unitStep n (p b) by abel]
        ring
      rw [e, expUnit_neg_smul, hall, ← expUnit_neg_smul]
      congr 2
      simp [ha, hb]
    · have e : angleCurl (imageAngles θ p s) y a b =
          angleCurl θ (signedPreimage p s y - unitStep n (p a) - unitStep n (p b)) (p a) (p b) := by
        simp only [angleCurl]
        rw [imageAngles_of_neg θ p s y a ha, imageAngles_of_neg θ p s _ b hb, imageAngles_of_neg θ p s _ a ha,
          imageAngles_of_neg θ p s y b hb, signedPreimage_add_of_neg p s y a ha,
          signedPreimage_add_of_neg p s y b hb,
          show signedPreimage p s y - unitStep n (p a) - unitStep n (p b) + unitStep n (p a)
            = signedPreimage p s y - unitStep n (p b) by abel,
          show signedPreimage p s y - unitStep n (p a) - unitStep n (p b) + unitStep n (p b)
            = signedPreimage p s y - unitStep n (p a) by abel,
          show signedPreimage p s y - unitStep n (p b) - unitStep n (p a)
            = signedPreimage p s y - unitStep n (p a) - unitStep n (p b) by abel]
        ring
      rw [e, hall]
      simp [ha, hb]
end YangMills.Construction.TorusLumps
end
