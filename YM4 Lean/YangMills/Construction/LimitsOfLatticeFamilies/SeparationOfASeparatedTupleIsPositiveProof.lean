import YangMills.Construction.LimitsOfLatticeFamilies.LengthOfAPointGivesAnInvariantDistance
import YangMills.Construction.LimitsOfLatticeFamilies.OneProductAndEntriesZero
import YangMills.Construction.LimitsOfLatticeFamilies.SeparationOfASeparatedTupleIsPositive
import Mathlib
set_option autoImplicit false
open Set
open scoped ENNReal
noncomputable section
namespace YangMills.Construction.LatticeLimits
open ModelSpace
namespace SeparationPositivity
section Cover
variable {X : Type*} {δ : X → X → ℝ}
theorem exists_pos_forall_le_of_finite {t : Set ℝ} (ht : t.Finite) (hpos : ∀ r ∈ t, 0 < r) :
    ∃ r : ℝ, 0 < r ∧ ∀ u ∈ t, r ≤ u := by
  induction t, ht using Set.Finite.induction_on with
  | empty => exact ⟨1, one_pos, by simp⟩
  | @insert a t _ _ ih =>
    obtain ⟨r, hr, hle⟩ := ih fun u hu => hpos u (mem_insert_of_mem a hu)
    refine ⟨min a r, lt_min (hpos a (mem_insert a t)) hr, ?_⟩
    rintro u (rfl | hu)
    · exact min_le_left _ _
    · exact (min_le_right _ _).trans (hle u hu)
theorem exists_subset_of_antitone_cover {Z : Set X} (hZ : MetricNotions.IsCompactWrt δ Z)
    (U : ℝ → Set X) (hopen : ∀ r, 0 < r → MetricNotions.IsOpenWrt δ (U r))
    (hanti : ∀ r r', 0 < r → r ≤ r' → U r' ⊆ U r) (hcov : ∀ z ∈ Z, ∃ r, 0 < r ∧ z ∈ U r) :
    ∃ r, 0 < r ∧ Z ⊆ U r := by
  obtain ⟨𝒱, hsub, hfin, hZ'⟩ := hZ (U '' Ioi 0)
    (by rintro _ ⟨r, hr, rfl⟩; exact hopen r hr)
    (fun z hz => by
      obtain ⟨r, hr, hzr⟩ := hcov z hz
      exact ⟨U r, ⟨r, hr, rfl⟩, hzr⟩)
  obtain ⟨t, ht, htfin, hZt⟩ := Set.exists_subset_image_finite_and
    (p := fun T => Z ⊆ ⋃₀ T) |>.1 ⟨𝒱, hsub, hfin, hZ'⟩
  obtain ⟨r, hr, hle⟩ := exists_pos_forall_le_of_finite htfin fun u hu => ht hu
  refine ⟨r, hr, fun z hz => ?_⟩
  obtain ⟨_, ⟨u, hu, rfl⟩, hzu⟩ := hZt hz
  exact hanti r u hr (hle u hu) hzu
theorem exists_pos_le_of_disjoint_compact (hnn : ∀ x y, 0 ≤ δ x y)
    (hzero : ∀ x y, δ x y = 0 ↔ x = y)
    (hsymm : ∀ x y, δ x y = δ y x) (htri : ∀ x y w, δ x y ≤ δ x w + δ w y)
    {A B : Set X} (hA : MetricNotions.IsCompactWrt δ A)
    (hB : MetricNotions.IsCompactWrt δ B) (hdisj : Disjoint A B) :
    ∃ r, 0 < r ∧ ∀ x ∈ A, ∀ y ∈ B, r ≤ δ x y := by
  have hpoint : ∀ x ∈ A, ∃ r, 0 < r ∧ ∀ y ∈ B, r ≤ δ x y := by
    intro x hx
    obtain ⟨r, hr, hsub⟩ := exists_subset_of_antitone_cover hB (fun r => {z | r < δ x z})
      (fun r _ z hz => by
        refine ⟨δ x z - r, sub_pos.2 hz, fun w hw => ?_⟩
        have := htri x z w
        show r < δ x w
        linarith [htri x w z, hsymm w z])
      (fun r r' _ hrr' z hz => lt_of_le_of_lt hrr' hz)
      (fun y hy => by
        have hne : x ≠ y := fun h => Set.disjoint_left.1 hdisj hx (h ▸ hy)
        have hpos : 0 < δ x y := lt_of_le_of_ne (hnn x y) fun h => hne ((hzero x y).1 h.symm)
        exact ⟨δ x y / 2, half_pos hpos, by show δ x y / 2 < δ x y; linarith⟩)
    exact ⟨r, hr, fun y hy => (show r < δ x y from hsub hy).le⟩
  obtain ⟨r, hr, hsub⟩ := exists_subset_of_antitone_cover hA
    (fun r => {z | ∃ r', r < r' ∧ ∀ y ∈ B, r' ≤ δ z y})
    (fun r _ z hz => by
      obtain ⟨r', hrr', hz'⟩ := hz
      refine ⟨(r' - r) / 2, by linarith, fun w hw => ?_⟩
      refine ⟨(r' + r) / 2, by linarith, fun y hy => ?_⟩
      linarith [hz' y hy, htri z y w, htri z w y])
    (fun r r' _ hrr' z hz => by
      obtain ⟨u, hu, hz'⟩ := hz
      exact ⟨u, lt_of_le_of_lt hrr' hu, hz'⟩)
    (fun x hx => by
      obtain ⟨r, hr, hle⟩ := hpoint x hx
      exact ⟨r / 2, half_pos hr, r, by linarith, hle⟩)
  refine ⟨r, hr, fun x hx y hy => ?_⟩
  obtain ⟨r', hrr', hx'⟩ := hsub hx
  exact hrr'.le.trans (hx' y hy)
end Cover
theorem infDist_pos_of_disjoint (s : Conventions.StandingParameters) (Y : ModelSpace)
    (hnn : ∀ x y : Y.Carrier s, 0 ≤ ModelSpace.dist s Y x y)
    (hzero : ∀ x y : Y.Carrier s, ModelSpace.dist s Y x y = 0 ↔ x = y)
    (hsymm : ∀ x y : Y.Carrier s, ModelSpace.dist s Y x y = ModelSpace.dist s Y y x)
    (htri : ∀ x y w : Y.Carrier s,
      ModelSpace.dist s Y x y ≤ ModelSpace.dist s Y x w + ModelSpace.dist s Y w y)
    {A B : Set (Y.Carrier s)} (hA : IsCompactIn s Y A) (hB : IsCompactIn s Y B)
    (hdisj : Disjoint A B) : 0 < ModelSpace.infDist s Y A B := by
  obtain ⟨r, hr, hle⟩ := exists_pos_le_of_disjoint_compact hnn hzero hsymm htri hA hB hdisj
  exact lt_of_lt_of_le (ENNReal.ofReal_pos.2 hr)
    (le_iInf₂ fun x hx => le_iInf₂ fun y hy => ENNReal.ofReal_le_ofReal (hle x hx y hy))
theorem supportIn_nonempty_of_ne_zero (s : Conventions.StandingParameters) (Y : ModelSpace)
    (hzero : ∀ x y : Y.Carrier s, ModelSpace.dist s Y x y = 0 ↔ x = y)
    {g : Y.Carrier s → ℝ} (hg : g ≠ 0) :
    (supportIn s Y g).Nonempty := by
  obtain ⟨y, hy⟩ := Function.ne_iff.1 hg
  exact ⟨y, fun r hr => ⟨y, hy, by rw [(hzero y y).2 rfl]; exact hr⟩⟩
theorem minSeparationPos_holds (hlength : InvariantDistFromNorm.Claim)
    (hentry : CommonProductAndZeroComponent) :
    MinSeparationPos := by
  intro s Y n hn f hf
  obtain ⟨-, -, hnn, hzero, hsymm, htri, -⟩ := hlength s Y
  obtain ⟨-, hcomp, hdisj⟩ := hf
  have hiff : minSeparation s Y f = ⊤ ↔
      ∀ i k, (supportIn s Y (f i)).Nonempty → (supportIn s Y (f k)).Nonempty → i = k := by
    constructor
    · intro h i k hi hk
      by_contra hik
      obtain ⟨x, hx⟩ := hi
      obtain ⟨y, hy⟩ := hk
      have h1 : minSeparation s Y f ≤
          ModelSpace.infDist s Y (supportIn s Y (f i)) (supportIn s Y (f k)) :=
        iInf_le_of_le i (iInf_le_of_le k (iInf_le _ hik))
      have h2 : ModelSpace.infDist s Y (supportIn s Y (f i)) (supportIn s Y (f k)) ≤
          ENNReal.ofReal (ModelSpace.dist s Y x y) :=
        iInf₂_le_of_le x hx (iInf₂_le y hy)
      rw [h] at h1
      exact ENNReal.ofReal_ne_top (top_le_iff.1 (h1.trans h2))
    · intro h
      simp only [minSeparation, iInf_eq_top]
      intro i k hik
      by_cases hi : (supportIn s Y (f i)).Nonempty
      · by_cases hk : (supportIn s Y (f k)).Nonempty
        · exact absurd (h i k hi hk) hik
        · simp [ModelSpace.infDist, not_nonempty_iff_eq_empty.1 hk]
      · simp [ModelSpace.infDist, not_nonempty_iff_eq_empty.1 hi]
  refine ⟨?_, hiff, fun htop => ?_⟩
  · obtain ⟨i, k, hik, he⟩ := ModelSpace.exists_minSeparation_eq s Y hn f
    rw [he]
    exact infDist_pos_of_disjoint s Y hnn hzero hsymm htri (hcomp i) (hcomp k) (hdisj i k hik)
  · have hent : ∃ i, f i = 0 := by
      by_contra hno
      have h01 := hiff.1 htop ⟨0, by omega⟩ ⟨1, by omega⟩
        (supportIn_nonempty_of_ne_zero s Y hzero (not_exists.1 hno _))
        (supportIn_nonempty_of_ne_zero s Y hzero (not_exists.1 hno _))
      simp [Fin.ext_iff] at h01
    refine ⟨hent, fun a ρ hρ Ψ hΨ hmem => ?_⟩
    obtain ⟨i, hi⟩ := hent
    refine (hentry s Y n (by omega) ρ hρ).2.1 Ψ hΨ _ hmem i ?_
    funext y
    simp [ModelSpace.shiftTuple, ModelSpace.shift, hi]
end SeparationPositivity
end YangMills.Construction.LatticeLimits
end
