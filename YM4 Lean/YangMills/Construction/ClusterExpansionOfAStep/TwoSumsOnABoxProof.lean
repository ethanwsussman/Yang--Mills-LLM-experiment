import YangMills.Construction.ClusterExpansionOfAStep.DistancesAndClasses
import YangMills.Construction.ClusterExpansionOfAStep.SumsOverATorus
import YangMills.Construction.ClusterExpansionOfAStep.TwoSumsOnABox
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.TorusSums
open TorusFields TorusLumps
theorem twoTorusSumsBound (hS : TorusSumBounds) : TwoTorusSumsBound := by
  intro n n' _ _ a a' H Y Y' d c ε hc hε hd hH hinj hinj' hfar hfar' hnear
  classical
  set box : Finset (Fin 4 → ℤ) := Fintype.piFinset fun _ : Fin 4 => Finset.Icc (-((d - 1 : ℕ) : ℤ)) ((d - 1 : ℕ) : ℤ)
    with hbox
  have hb1 : ∀ g ∈ box, OffsetInBox (d - 1) g := by
    intro g hg i
    have := Fintype.mem_piFinset.mp hg i
    rw [Finset.mem_Icc] at this
    exact abs_le.mpr this
  have hb2 : ∀ g, OffsetInBox (d - 1) g → g ∈ box := by
    intro g hg
    refine Fintype.mem_piFinset.mpr fun i => ?_
    rw [Finset.mem_Icc]
    exact abs_le.mp (hg i)
  have hcard : (box.card : ℝ) ≤ (2 * (d : ℝ) + 1) ^ 4 := by
    have h1 : box.card = (2 * (d - 1) + 1) ^ 4 := by
      rw [hbox, Fintype.card_piFinset]
      simp only [Int.card_Icc, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      congr 1
      omega
    rw [h1]
    push_cast
    have : ((d - 1 : ℕ) : ℝ) ≤ d := by exact_mod_cast Nat.sub_le d 1
    have h2 : (0 : ℝ) ≤ ((d - 1 : ℕ) : ℝ) := Nat.cast_nonneg _
    exact pow_le_pow_left₀ (by linarith) (by linarith) 4
  set X : Finset (Fin 4 → ℤ) := Finset.image₂ (· + ·) H box with hX
  have hXm : ∀ x ∈ X, ∃ h ∈ H, ∃ g, OffsetInBox (d - 1) g ∧ x = h + g := by
    intro x hx
    obtain ⟨h, hh, g, hg, rfl⟩ := Finset.mem_image₂.mp hx
    exact ⟨h, hh, g, hb1 g hg, rfl⟩
  have hXc : (X.card : ℝ) ≤ (H.card : ℝ) * (2 * (d : ℝ) + 1) ^ 4 := by
    have h1 : X.card ≤ H.card * box.card := Finset.card_image₂_le _ _ _
    have h2 : (X.card : ℝ) ≤ (H.card : ℝ) * box.card := by exact_mod_cast h1
    exact h2.trans (mul_le_mul_of_nonneg_left hcard (Nat.cast_nonneg _))
  have side : ∀ (m : ℕ) [NeZero m] (b : TorusSite m → ℝ) (Z : TorusSite m),
      (∀ h ∈ H, ∀ h₂ ∈ H, ∀ g g₂, OffsetInBox (d - 1) g → OffsetInBox (d - 1) g₂ →
        (Z + siteOfInt (h + g) = Z + siteOfInt (h₂ + g₂) ↔ h + g = h₂ + g₂)) →
      (∀ (y : TorusSite m) (D : ℕ), d ≤ D → (∀ h ∈ H, D ≤ _root_.YangMills.Construction.TorusFields.supDist y (Z + siteOfInt h)) →
        |b y| ≤ Real.exp (-(c * ((D : ℝ) - 2)))) →
      ∃ rest : ℝ, ∑ y, b y = ∑ x ∈ X, b (Z + siteOfInt x) + rest ∧
        |rest| ≤ (H.card : ℝ) * (Real.exp (2 * c) * Real.exp (-(3 / 4 * c * d)) *
          (2 / (1 - Real.exp (-(c / 16)))) ^ 4) := by
    intro m _ b Z hZ hb
    set Q : Finset (TorusSite m) := X.image fun x => Z + siteOfInt x with hQ
    have hQs : ∑ y ∈ Q, b y = ∑ x ∈ X, b (Z + siteOfInt x) := by
      refine Finset.sum_image fun x hx x₂ hx₂ hxx => ?_
      obtain ⟨h, hh, g, hg, rfl⟩ := hXm x (by simpa using hx)
      obtain ⟨h₂, hh₂, g₂, hg₂, rfl⟩ := hXm x₂ (by simpa using hx₂)
      exact (hZ h hh h₂ hh₂ g g₂ hg hg₂).mp hxx
    refine ⟨∑ y ∈ Qᶜ, b y, ?_, ?_⟩
    · rw [← hQs, Finset.sum_add_sum_compl]
    have hoff : ∀ y ∈ Qᶜ, ∀ h ∈ H, d ≤ _root_.YangMills.Construction.TorusFields.supDist y (Z + siteOfInt h) := by
      intro y hy h hh
      by_contra hlt
      have hlt' : _root_.YangMills.Construction.TorusFields.supDist y (Z + siteOfInt h) ≤ d - 1 := by omega
      have hle := (_root_.YangMills.Construction.TorusFields.supDist_le_iff y (Z + siteOfInt h) (d - 1)).mp hlt'
      let g : Fin 4 → ℤ := fun i => (y i - (Z + siteOfInt h : TorusSite m) i).valMinAbs
      have hg : OffsetInBox (d - 1) g := by
        intro i
        have := hle i
        change |(y i - (Z + siteOfInt h : TorusSite m) i).valMinAbs| ≤ _
        rw [Int.abs_eq_natAbs]
        exact_mod_cast this
      have hy' : y = Z + siteOfInt (h + g) := by
        rw [siteOfInt_add, ← add_assoc]
        funext i
        have hp : ((g i : ℤ) : ZMod m) = y i - (Z + siteOfInt h : TorusSite m) i := ZMod.coe_valMinAbs _
        change y i = (Z + siteOfInt h : TorusSite m) i + ((g i : ℤ) : ZMod m)
        rw [hp]
        ring
      apply Finset.mem_compl.mp hy
      rw [hQ, hy']
      exact Finset.mem_image_of_mem _ (Finset.mem_image₂_of_mem hh (hb2 g hg))
    have hpt : ∀ y ∈ Qᶜ, |b y| ≤ Real.exp (2 * c) * Real.exp (-(3 / 4 * c * d)) *
        ∑ h ∈ H, Real.exp (-(c / 4 * (_root_.YangMills.Construction.TorusFields.supDist y (Z + siteOfInt h) : ℝ))) := by
      intro y hy
      obtain ⟨h₀, hh₀, hmin⟩ := Finset.exists_min_image H (fun h => _root_.YangMills.Construction.TorusFields.supDist y (Z + siteOfInt h)) hH
      have h1 := hb y (_root_.YangMills.Construction.TorusFields.supDist y (Z + siteOfInt h₀)) (hoff y hy h₀ hh₀) hmin
      have h2 : (d : ℝ) ≤ _root_.YangMills.Construction.TorusFields.supDist y (Z + siteOfInt h₀) := by exact_mod_cast hoff y hy h₀ hh₀
      have h3 : Real.exp (-(c * ((_root_.YangMills.Construction.TorusFields.supDist y (Z + siteOfInt h₀) : ℝ) - 2))) ≤
          Real.exp (2 * c) * Real.exp (-(3 / 4 * c * d)) *
            Real.exp (-(c / 4 * (_root_.YangMills.Construction.TorusFields.supDist y (Z + siteOfInt h₀) : ℝ))) := by
        rw [← Real.exp_add, ← Real.exp_add]
        refine Real.exp_le_exp.mpr ?_
        nlinarith
      have h4 : Real.exp (-(c / 4 * (_root_.YangMills.Construction.TorusFields.supDist y (Z + siteOfInt h₀) : ℝ))) ≤
          ∑ h ∈ H, Real.exp (-(c / 4 * (supDist y (Z + siteOfInt h) : ℝ))) :=
        Finset.single_le_sum (f := fun h => Real.exp (-(c / 4 * (_root_.YangMills.Construction.TorusFields.supDist y (Z + siteOfInt h) : ℝ))))
          (fun _ _ => (Real.exp_pos _).le) hh₀
      exact h1.trans (h3.trans (mul_le_mul_of_nonneg_left h4 (by positivity)))
    have hW : ∀ h ∈ H, ∑ y : TorusSite m, Real.exp (-(c / 4 * (_root_.YangMills.Construction.TorusFields.supDist y (Z + siteOfInt h) : ℝ))) ≤
        (2 / (1 - Real.exp (-(c / 16)))) ^ 4 := by
      intro h _
      have := (hS m (Z + siteOfInt h)).1 (c / 4) (by positivity)
      have e : c / 4 / 4 = c / 16 := by ring
      rwa [e] at this
    calc |∑ y ∈ Qᶜ, b y| ≤ ∑ y ∈ Qᶜ, |b y| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ y ∈ Qᶜ, Real.exp (2 * c) * Real.exp (-(3 / 4 * c * d)) *
          ∑ h ∈ H, Real.exp (-(c / 4 * (_root_.YangMills.Construction.TorusFields.supDist y (Z + siteOfInt h) : ℝ))) := Finset.sum_le_sum hpt
      _ ≤ ∑ y : TorusSite m, Real.exp (2 * c) * Real.exp (-(3 / 4 * c * d)) *
          ∑ h ∈ H, Real.exp (-(c / 4 * (supDist y (Z + siteOfInt h) : ℝ))) :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun y _ _ =>
          mul_nonneg (by positivity) (Finset.sum_nonneg fun _ _ => (Real.exp_pos _).le)
      _ = Real.exp (2 * c) * Real.exp (-(3 / 4 * c * d)) *
          ∑ h ∈ H, ∑ y : TorusSite m, Real.exp (-(c / 4 * (_root_.YangMills.Construction.TorusFields.supDist y (Z + siteOfInt h) : ℝ))) := by
        rw [← Finset.mul_sum, Finset.sum_comm]
      _ ≤ Real.exp (2 * c) * Real.exp (-(3 / 4 * c * d)) *
          ∑ _h ∈ H, (2 / (1 - Real.exp (-(c / 16)))) ^ 4 :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum hW) (by positivity)
      _ = _ := by
        simp only [Finset.sum_const, nsmul_eq_mul]
        ring
  obtain ⟨ρ, e1, b1⟩ := side n a Y hinj hfar
  obtain ⟨ρ', e2, b2⟩ := side n' a' Y' hinj' hfar'
  have hmain : |∑ x ∈ X, (a (Y + siteOfInt x) - a' (Y' + siteOfInt x))| ≤ (X.card : ℝ) * ε := by
    calc _ ≤ ∑ x ∈ X, |a (Y + siteOfInt x) - a' (Y' + siteOfInt x)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _x ∈ X, ε := Finset.sum_le_sum fun x hx => by
        obtain ⟨h, hh, g, hg, rfl⟩ := hXm x hx
        exact hnear h hh g hg
      _ = _ := by simp
  have hsplit : ∑ y, a y - ∑ y, a' y = ∑ x ∈ X, (a (Y + siteOfInt x) - a' (Y' + siteOfInt x)) + (ρ - ρ') := by
    rw [e1, e2, Finset.sum_sub_distrib]
    ring
  rw [hsplit]
  have h1 : |ρ - ρ'| ≤ |ρ| + |ρ'| := abs_sub ρ ρ'
  have h2 := abs_add_le (∑ x ∈ X, (a (Y + siteOfInt x) - a' (Y' + siteOfInt x))) (ρ - ρ')
  have h3 : (X.card : ℝ) * ε ≤ (H.card : ℝ) * (2 * (d : ℝ) + 1) ^ 4 * ε :=
    mul_le_mul_of_nonneg_right hXc hε
  linarith
end YangMills.Construction.TorusSums
end
