import YangMills.Construction.ColdChainAtEveryLevel.HomotopyFormulaProof
import YangMills.Construction.ColdChainAtEveryLevel.LeastQuarticGaugeProof
import YangMills.Construction.ColdChainAtEveryLevel.UnitPartsOfQuaternions
import YangMills.Construction.HoleBesideASecondHole.AGaugeOnAShell
import YangMills.Construction.HoleBesideASecondHole.APlaquetteAlongFourSegments
import YangMills.Construction.HoleBesideASecondHole.ASegmentInTheGroup
import YangMills.Construction.HoleBesideASecondHole.TreeGaugeOfAField
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction
open BlockAverages LatticeFractionalIntegration ShellOrthant GroupPaths ShellFilling
namespace ShellFilling
namespace Interpolation
abbrev Site : Type := Lattice4
def distOne (g : UnitQuaternion) : ℝ := ‖(g : ℍ[ℝ]) - 1‖
theorem distOne_nonneg (g : UnitQuaternion) : 0 ≤ distOne g := norm_nonneg _
theorem distOne_one : distOne 1 = 0 := by simp [distOne]
theorem coe_mul_coe_inv (a : UnitQuaternion) : (a : ℍ[ℝ]) * ((a⁻¹ : UnitQuaternion) : ℍ[ℝ]) = 1 := by apply _root_.YangMills.Construction.GaugeFixing.coe_mul_coe_inv <;> assumption
theorem distOne_conj (a g : UnitQuaternion) : distOne (a * g * a⁻¹) = distOne g := by apply _root_.YangMills.Construction.BlockAverages.norm_coe_conj_sub_one <;> assumption
theorem latticePlaquette_gaugeTransform (γ : Site → UnitQuaternion) (X : Site → Fin 4 → UnitQuaternion)
    (y : Site) (μ ν : Fin 4) :
    latticePlaquette (latticeGaugeTransform γ X) y μ ν = γ y * latticePlaquette X y μ ν * (γ y)⁻¹ := by apply _root_.YangMills.Construction.LeastQuarticGauge.latticePlaquette_gaugeTransform <;> assumption
theorem mem_bondsOf {P : Finset Site} {b : Site × Fin 4} :
    b ∈ bondsOf P ↔ b.1 ∈ P ∧ b.1 + basisVector b.2 ∈ P := by apply _root_.YangMills.Construction.LeastQuarticGauge.mem_bondsOf <;> assumption
theorem mem_orientedPlaquettesOf {P : Finset Site} {p : Site × Fin 4 × Fin 4} :
    p ∈ orientedPlaquettesOf P ↔ p.1 ∈ P ∧ p.2.1 ≠ p.2.2 ∧ p.1 + basisVector p.2.1 ∈ P ∧
      p.1 + basisVector p.2.2 ∈ P ∧ p.1 + basisVector p.2.1 + basisVector p.2.2 ∈ P := by
  simp [orientedPlaquettesOf]
theorem basisVector_apply (j k : Fin 4) : basisVector j k = if k = j then 1 else 0 := by apply _root_.YangMills.Construction.LatticeFractionalIntegration.StaircaseHomotopy.basisVector_apply <;> assumption
def supDist (o : Fin 4 → ℝ) (x : Site) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty fun i => |(x i : ℝ) - o i|
theorem le_supDist (o : Fin 4 → ℝ) (x : Site) (i : Fin 4) : |(x i : ℝ) - o i| ≤ _root_.YangMills.Construction.ShellFilling.Interpolation.supDist o x :=
  Finset.le_sup' (fun i => |(x i : ℝ) - o i|) (Finset.mem_univ i)
theorem supDist_le (o : Fin 4 → ℝ) (x : Site) (r : ℝ) (h : ∀ i, |(x i : ℝ) - o i| ≤ r) : _root_.YangMills.Construction.ShellFilling.Interpolation.supDist o x ≤ r :=
  Finset.sup'_le _ _ fun i _ => h i
theorem exists_eq_supDist (o : Fin 4 → ℝ) (x : Site) : ∃ i, _root_.YangMills.Construction.ShellFilling.Interpolation.supDist o x = |(x i : ℝ) - o i| := by
  obtain ⟨i, -, h⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty fun i => |(x i : ℝ) - o i|
  exact ⟨i, h⟩
theorem supDist_add_basis_le (o : Fin 4 → ℝ) (x : Site) (j : Fin 4) :
    _root_.YangMills.Construction.ShellFilling.Interpolation.supDist o (x + basisVector j) ≤ _root_.YangMills.Construction.ShellFilling.Interpolation.supDist o x + 1 := by
  refine supDist_le o _ _ fun i => ?_
  have h := le_supDist o x i
  have e : (((x + basisVector j) i : ℤ) : ℝ) - o i = ((x i : ℝ) - o i) + ((basisVector j i : ℤ) : ℝ) := by
    simp only [Pi.add_apply]
    push_cast
    ring
  rw [e]
  refine (abs_add_le _ _).trans ?_
  have h2 : |((basisVector j i : ℤ) : ℝ)| ≤ 1 := by
    rw [basisVector_apply]
    split_ifs <;> simp
  linarith
theorem supDist_le_add_basis (o : Fin 4 → ℝ) (x : Site) (j : Fin 4) :
    _root_.YangMills.Construction.ShellFilling.Interpolation.supDist o x ≤ _root_.YangMills.Construction.ShellFilling.Interpolation.supDist o (x + basisVector j) + 1 := by
  refine supDist_le o _ _ fun i => ?_
  have h := le_supDist o (x + basisVector j) i
  have e : (x i : ℝ) - o i = ((((x + basisVector j) i : ℤ) : ℝ) - o i) - ((basisVector j i : ℤ) : ℝ) := by
    simp only [Pi.add_apply]
    push_cast
    ring
  rw [e]
  refine (abs_sub _ _).trans ?_
  have h2 : |((basisVector j i : ℤ) : ℝ)| ≤ 1 := by
    rw [basisVector_apply]
    split_ifs <;> simp
  linarith
theorem isBeyondSupDist_iff (o : Fin 4 → ℝ) (r : ℝ) (x : Site) : IsBeyondSupDist o r x ↔ r ≤ _root_.YangMills.Construction.ShellFilling.Interpolation.supDist o x := by
  constructor
  · rintro ⟨i, h⟩
    exact h.trans (le_supDist o x i)
  · intro h
    obtain ⟨i, hi⟩ := exists_eq_supDist o x
    exact ⟨i, hi ▸ h⟩
theorem isWithinSupDist_iff (o : Fin 4 → ℝ) (r : ℝ) (x : Site) : IsWithinSupDist o r x ↔ _root_.YangMills.Construction.ShellFilling.Interpolation.supDist o x ≤ r :=
  ⟨fun h => _root_.YangMills.Construction.ShellFilling.Interpolation.supDist_le o x r h, fun h i => (le_supDist o x i).trans h⟩
theorem isInShellOrthant_zero_iff (o : Fin 4 → ℝ) (l : ℝ) (x : Site) :
    IsInShellOrthant o l (fun _ => 0) x ↔ 1.1 * l ≤ _root_.YangMills.Construction.ShellFilling.Interpolation.supDist o x ∧ _root_.YangMills.Construction.ShellFilling.Interpolation.supDist o x ≤ 1.9 * l := by
  have e1 : orthantLower l 0 = -(1.9 * l) := by simp [orthantLower]
  have e2 : orthantUpper l 0 = 1.9 * l := by simp [orthantUpper]
  unfold IsInShellOrthant
  rw [isBeyondSupDist_iff]
  simp only [e1, e2]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h2, _root_.YangMills.Construction.ShellFilling.Interpolation.supDist_le o x _ fun i => abs_le.2 (h1 i)⟩
  · rintro ⟨h1, h2⟩
    exact ⟨fun i => abs_le.1 ((le_supDist o x i).trans h2), h1⟩
def rampWeight (l : ℝ) (n : ℝ) : ℝ := min 1 (max 0 ((n - 1.2 * l) / (0.6 * l)))
theorem rampWeight_nonneg (l n : ℝ) : 0 ≤ rampWeight l n := le_min zero_le_one (le_max_left _ _)
theorem rampWeight_le_one (l n : ℝ) : rampWeight l n ≤ 1 := min_le_left _ _
theorem rampWeight_eq_zero (l n : ℝ) (hl : 0 < l) (h : n ≤ 1.2 * l) : rampWeight l n = 0 := by
  unfold rampWeight
  have : (n - 1.2 * l) / (0.6 * l) ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) (by positivity)
  rw [max_eq_left this]
  simp
theorem rampWeight_eq_one (l n : ℝ) (hl : 0 < l) (h : 1.8 * l ≤ n) : rampWeight l n = 1 := by
  unfold rampWeight
  have : 1 ≤ (n - 1.2 * l) / (0.6 * l) := by
    rw [le_div_iff₀ (by positivity)]
    linarith
  rw [max_eq_right (by linarith), min_eq_left this]
theorem rampWeight_lipschitz (l n n' : ℝ) (hl : 0 < l) :
    |rampWeight l n - rampWeight l n'| ≤ 2 * |n - n'| / l := by
  unfold rampWeight
  have h1 := abs_min_sub_min_le_max (1 : ℝ) (max 0 ((n - 1.2 * l) / (0.6 * l))) 1
    (max 0 ((n' - 1.2 * l) / (0.6 * l)))
  have h2 := abs_max_sub_max_le_abs ((n - 1.2 * l) / (0.6 * l)) ((n' - 1.2 * l) / (0.6 * l)) 0
  rw [max_comm _ (0 : ℝ), max_comm _ (0 : ℝ)] at h2
  have e : (n - 1.2 * l) / (0.6 * l) - (n' - 1.2 * l) / (0.6 * l) = (n - n') / (0.6 * l) := by
    field_simp
    ring
  rw [e, abs_div, abs_of_pos (by positivity : 0 < 0.6 * l)] at h2
  simp only [sub_self, abs_zero] at h1
  have h3 : |n - n'| / (0.6 * l) ≤ 2 * |n - n'| / l := by
    rw [div_le_div_iff₀ (by positivity) hl]
    have := abs_nonneg (n - n')
    nlinarith
  have h4 : 0 ≤ |n - n'| / (0.6 * l) := by positivity
  refine h1.trans (max_le ?_ ?_)
  · exact h4.trans h3
  · exact h2.trans h3
theorem sum_comp_le_sixteen_mul {α : Type} [DecidableEq α] (R : Finset (Site × Fin 4 × Fin 4)) (B : Finset α)
    (β : Site × Fin 4 × Fin 4 → α) (f : α → ℝ) (hf : ∀ b, 0 ≤ f b) (hmap : ∀ p ∈ R, β p ∈ B)
    (hinj : ∀ p ∈ R, ∀ q ∈ R, p.2 = q.2 → β p = β q → p = q) :
    ∑ p ∈ R, f (β p) ≤ 16 * ∑ b ∈ B, f b := by
  classical
  have hmaps : ∀ p ∈ R, p.2 ∈ (Finset.univ : Finset (Fin 4 × Fin 4)) := fun _ _ => Finset.mem_univ _
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  have hin : ∀ t ∈ (Finset.univ : Finset (Fin 4 × Fin 4)),
      ∑ p ∈ R with p.2 = t, f (β p) ≤ ∑ b ∈ B, f b := by
    intro t _
    have hi : Set.InjOn β (R.filter fun p => p.2 = t : Finset _) := by
      intro a ha b hb hab
      have h1 := Finset.mem_filter.1 ha
      have h2 := Finset.mem_filter.1 hb
      exact hinj a h1.1 b h2.1 (h1.2.trans h2.2.symm) hab
    rw [← Finset.sum_image (f := f) hi]
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun b _ _ => hf b
    intro b hb
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 hb
    exact hmap p (Finset.mem_filter.1 hp).1
  refine (Finset.sum_le_sum hin).trans ?_
  simp
theorem sum_indicator_le {α : Type} [DecidableEq α] (R B : Finset α) (f : α → ℝ) (hf : ∀ b, 0 ≤ f b) :
    ∑ b ∈ R, (if b ∈ B then f b else 0) ≤ ∑ b ∈ B, f b := by
  rw [← Finset.sum_filter]
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun b _ _ => hf b
  intro b hb
  exact (Finset.mem_filter.1 hb).2
theorem card_le_of_supDist_le (l : ℝ) (hl : 100 ≤ l) (o : Fin 4 → ℝ) (P : Finset Site)
    (hP : ∀ x ∈ P, _root_.YangMills.Construction.ShellFilling.Interpolation.supDist o x ≤ 1.9 * l) : (P.card : ℝ) ≤ (4 * l) ^ 4 := by
  classical
  set S : Finset Site := Fintype.piFinset fun k => Finset.Icc ⌈o k - 1.9 * l⌉ ⌊o k + 1.9 * l⌋ with hS
  have hsub : P ⊆ S := by
    intro x hx
    simp only [hS, Fintype.mem_piFinset, Finset.mem_Icc]
    intro k
    have h2 := abs_le.1 ((le_supDist o x k).trans (hP x hx))
    exact ⟨Int.ceil_le.2 (by linarith [h2.1]), Int.le_floor.2 (by linarith [h2.2])⟩
  have h1 : (P.card : ℝ) ≤ (S.card : ℝ) := by
    exact_mod_cast Finset.card_le_card hsub
  refine h1.trans ?_
  have h2 : (S.card : ℝ) = ∏ k, (((Finset.Icc ⌈o k - 1.9 * l⌉ ⌊o k + 1.9 * l⌋).card : ℕ) : ℝ) := by
    simp [hS, Fintype.card_piFinset]
  rw [h2]
  have h3 : ∀ k ∈ (Finset.univ : Finset (Fin 4)),
      (((Finset.Icc ⌈o k - 1.9 * l⌉ ⌊o k + 1.9 * l⌋).card : ℕ) : ℝ) ≤ 4 * l := by
    intro k _
    rw [Int.card_Icc]
    by_cases hz : 0 ≤ ⌊o k + 1.9 * l⌋ + 1 - ⌈o k - 1.9 * l⌉
    · have e : (((⌊o k + 1.9 * l⌋ + 1 - ⌈o k - 1.9 * l⌉).toNat : ℕ) : ℝ) =
          ((⌊o k + 1.9 * l⌋ + 1 - ⌈o k - 1.9 * l⌉ : ℤ) : ℝ) := by
        have := Int.toNat_of_nonneg hz
        exact_mod_cast this
      rw [e]
      push_cast
      have a1 : (⌊o k + 1.9 * l⌋ : ℝ) ≤ o k + 1.9 * l := Int.floor_le _
      have a2 : o k - 1.9 * l ≤ (⌈o k - 1.9 * l⌉ : ℝ) := Int.le_ceil _
      linarith
    · have : (⌊o k + 1.9 * l⌋ + 1 - ⌈o k - 1.9 * l⌉).toNat = 0 := by omega
      rw [this]
      push_cast
      linarith
  calc ∏ k, (((Finset.Icc ⌈o k - 1.9 * l⌉ ⌊o k + 1.9 * l⌋).card : ℕ) : ℝ) ≤ ∏ _k : Fin 4, 4 * l :=
        Finset.prod_le_prod (fun _ _ => by positivity) h3
    _ = (4 * l) ^ 4 := by simp
theorem sq_le_three_mul (g G u v : ℝ) (hg : 0 ≤ g) (h : g ≤ G + u + v) :
    g ^ 2 ≤ 3 * G ^ 2 + 3 * u ^ 2 + 3 * v ^ 2 := by
  have h1 : g ^ 2 ≤ (G + u + v) ^ 2 := pow_le_pow_left₀ hg h 2
  nlinarith [sq_nonneg (G - u), sq_nonneg (G - v), sq_nonneg (u - v)]
theorem plaquette_sq_bound (l g G a₁ a₂ a₃ a₄ d₂ d₃ d₄ : ℝ) (hl : 0 < l) (hg : 0 ≤ g)
    (h1 : 0 ≤ a₁) (h2 : 0 ≤ a₂) (h3 : 0 ≤ a₃) (h4 : 0 ≤ a₄)
    (hd₂ : d₂ ≤ 4 / l) (hd₃ : d₃ ≤ 4 / l) (hd₄ : d₄ ≤ 4 / l)
    (h : g ≤ G + (d₂ * a₂ + d₃ * a₃ + d₄ * a₄) + 11 * (a₁ ^ 2 + a₂ ^ 2 + a₃ ^ 2 + a₄ ^ 2)) :
    g ^ 2 ≤ 3 * G ^ 2 + (144 / l ^ 2 * (a₁ ^ 2 + a₂ ^ 2 + a₃ ^ 2 + a₄ ^ 2) +
      1452 * (a₁ ^ 4 + a₂ ^ 4 + a₃ ^ 4 + a₄ ^ 4)) := by
  set u : ℝ := 4 / l * (a₂ + a₃ + a₄) with hu
  set S : ℝ := a₁ ^ 2 + a₂ ^ 2 + a₃ ^ 2 + a₄ ^ 2 with hS
  have hle : d₂ * a₂ + d₃ * a₃ + d₄ * a₄ ≤ u := by
    have b2 := mul_le_mul_of_nonneg_right hd₂ h2
    have b3 := mul_le_mul_of_nonneg_right hd₃ h3
    have b4 := mul_le_mul_of_nonneg_right hd₄ h4
    rw [hu]
    linarith
  have h5 := sq_le_three_mul g G u (11 * S) hg (by linarith)
  have h6 : (a₂ + a₃ + a₄) ^ 2 ≤ 3 * S := by
    rw [hS]
    nlinarith [sq_nonneg (a₂ - a₃), sq_nonneg (a₂ - a₄), sq_nonneg (a₃ - a₄), sq_nonneg a₁]
  have h7 : 3 * u ^ 2 ≤ 144 / l ^ 2 * S := by
    have e : 3 * u ^ 2 = 48 / l ^ 2 * (a₂ + a₃ + a₄) ^ 2 := by
      rw [hu]
      field_simp
      ring
    rw [e]
    have : 48 / l ^ 2 * (a₂ + a₃ + a₄) ^ 2 ≤ 48 / l ^ 2 * (3 * S) :=
      mul_le_mul_of_nonneg_left h6 (by positivity)
    calc _ ≤ _ := this
      _ = _ := by ring
  have h8 : S ^ 2 ≤ 4 * (a₁ ^ 4 + a₂ ^ 4 + a₃ ^ 4 + a₄ ^ 4) := by
    rw [hS]
    nlinarith [sq_nonneg (a₁ ^ 2 - a₂ ^ 2), sq_nonneg (a₁ ^ 2 - a₃ ^ 2), sq_nonneg (a₁ ^ 2 - a₄ ^ 2),
      sq_nonneg (a₂ ^ 2 - a₃ ^ 2), sq_nonneg (a₂ ^ 2 - a₄ ^ 2), sq_nonneg (a₃ ^ 2 - a₄ ^ 2)]
  have h9 : 3 * (11 * S) ^ 2 = 363 * S ^ 2 := by ring
  rw [h9] at h5
  linarith
theorem min_pairs_close (w0 w1 w2 w3 δ : ℝ) (h01 : |w0 - w1| ≤ δ) (h02 : |w0 - w2| ≤ δ)
    (h13 : |w1 - w3| ≤ δ) (h12 : |w1 - w2| ≤ δ) (hδ : 0 ≤ δ) :
    |min w1 w3 - min w0 w1| ≤ δ ∧ |min w2 w3 - min w0 w1| ≤ δ ∧ |min w0 w2 - min w0 w1| ≤ δ := by
  refine ⟨?_, ?_, ?_⟩
  · refine (abs_min_sub_min_le_max _ _ _ _).trans (max_le ?_ ?_)
    · rwa [abs_sub_comm]
    · rwa [abs_sub_comm]
  · refine (abs_min_sub_min_le_max _ _ _ _).trans (max_le ?_ ?_)
    · rwa [abs_sub_comm]
    · rwa [abs_sub_comm]
  · refine (abs_min_sub_min_le_max _ _ _ _).trans (max_le ?_ ?_)
    · simpa using hδ
    · rwa [abs_sub_comm]
theorem exists_filled_config (Φ : ℝ → UnitQuaternion → UnitQuaternion) (hΦ0 : ∀ q, Φ 0 q = 1)
    (hΦ1 : ∀ q, Φ 1 q = q)
    (hplaq : ∀ (t₁ t₂ t₃ t₄ : ℝ) (q₁ q₂ q₃ q₄ : UnitQuaternion), 0 ≤ t₁ → t₁ ≤ 1 → 0 ≤ t₂ → t₂ ≤ 1 →
      0 ≤ t₃ → t₃ ≤ 1 → 0 ≤ t₄ → t₄ ≤ 1 → distOne q₁ ≤ 1 / 2 → distOne q₂ ≤ 1 / 2 →
      distOne q₃ ≤ 1 / 2 → distOne q₄ ≤ 1 / 2 →
      distOne (Φ t₁ q₁ * Φ t₂ q₂ * (Φ t₃ q₃)⁻¹ * (Φ t₄ q₄)⁻¹) ≤
        distOne (q₁ * q₂ * q₃⁻¹ * q₄⁻¹) +
          (|t₂ - t₁| * distOne q₂ + |t₃ - t₁| * distOne q₃ + |t₄ - t₁| * distOne q₄) +
          11 * (distOne q₁ ^ 2 + distOne q₂ ^ 2 + distOne q₃ ^ 2 + distOne q₄ ^ 2))
    (l : ℝ) (o : Fin 4 → ℝ) (D Sh P₀ : Finset Site) (X : Site → Fin 4 → UnitQuaternion)
    (γ : Site → UnitQuaternion) (A ε : ℝ)
    (hl : 100 ≤ l) (hD : ∀ x, x ∈ D ↔ IsWithinSupDist o (1.95 * l) x)
    (hSh : ∀ x, x ∈ Sh ↔ x ∈ D ∧ IsBeyondSupDist o l x)
    (hP₀ : ∀ x, x ∈ P₀ ↔ 1.1 * l ≤ _root_.YangMills.Construction.ShellFilling.Interpolation.supDist o x ∧ _root_.YangMills.Construction.ShellFilling.Interpolation.supDist o x ≤ 1.9 * l)
    (hsum : plaquetteDefect Sh X ≤ ε ^ 2)
    (hZ : ∑ b ∈ bondsOf P₀, distOne (latticeGaugeTransform γ X b.1 b.2) ^ 4 ≤ A ^ 4) (hA0 : 0 ≤ A)
    (hA : A ≤ 1 / 2) :
    ∃ X' : Site → Fin 4 → UnitQuaternion,
      (∀ b ∈ bondsOf D, IsBeyondSupDist o (1.9 * l) b.1 → IsBeyondSupDist o (1.9 * l) (b.1 + basisVector b.2) →
        X' b.1 b.2 = X b.1 b.2) ∧
      plaquetteDefect D X' ≤ 3 * ε ^ 2 + 387840 * A ^ 2 := by
  classical
  have hl0 : 0 < l := by linarith
  set Z : Site → Fin 4 → UnitQuaternion := latticeGaugeTransform γ X with hZdef
  set w : Site → ℝ := fun x => rampWeight l (_root_.YangMills.Construction.ShellFilling.Interpolation.supDist o x) with hw
  have hw0 : ∀ x, 0 ≤ w x := fun x => rampWeight_nonneg _ _
  have hw1 : ∀ x, w x ≤ 1 := fun x => rampWeight_le_one _ _
  set tb : Site → Fin 4 → ℝ := fun x j => min (w x) (w (x + basisVector j)) with htb
  have htb0 : ∀ x j, 0 ≤ tb x j := fun x j => le_min (hw0 _) (hw0 _)
  have htb1 : ∀ x j, tb x j ≤ 1 := fun x j => (min_le_left _ _).trans (hw1 _)
  set Z' : Site → Fin 4 → UnitQuaternion := fun x j => Φ (tb x j) (Z x j) with hZ'
  set gt : Site → UnitQuaternion := fun x => if 1.8 * l ≤ _root_.YangMills.Construction.ShellFilling.Interpolation.supDist o x then γ x else 1 with hgt
  refine ⟨latticeGaugeTransform (fun x => (gt x)⁻¹) Z', ?_, ?_⟩
  · rintro ⟨x, j⟩ _ h1 h2
    rw [isBeyondSupDist_iff] at h1 h2
    simp only at h1 h2 ⊢
    have e1 : w x = 1 := rampWeight_eq_one l _ hl0 (by linarith)
    have e2 : w (x + basisVector j) = 1 := rampWeight_eq_one l _ hl0 (by linarith)
    have e3 : tb x j = 1 := by simp [htb, e1, e2]
    have e4 : gt x = γ x := by
      have : 1.8 * l ≤ _root_.YangMills.Construction.ShellFilling.Interpolation.supDist o x := by linarith
      simp [hgt, this]
    have e5 : gt (x + basisVector j) = γ (x + basisVector j) := by
      have : 1.8 * l ≤ _root_.YangMills.Construction.ShellFilling.Interpolation.supDist o (x + basisVector j) := by linarith
      simp [hgt, this]
    unfold latticeGaugeTransform
    simp only [hZ', e3, hΦ1, e4, e5, hZdef]
    unfold latticeGaugeTransform
    group
  · set a : Site × Fin 4 → ℝ := fun b => distOne (Z b.1 b.2) with ha
    have ha0 : ∀ b, 0 ≤ a b := fun b => distOne_nonneg _
    have hZ4 : ∑ b ∈ bondsOf P₀, a b ^ 4 ≤ A ^ 4 := hZ
    have hab : ∀ b ∈ bondsOf P₀, a b ≤ 1 / 2 := by
      intro b hb
      have h1 : a b ^ 4 ≤ ∑ b ∈ bondsOf P₀, a b ^ 4 :=
        Finset.single_le_sum (f := fun b => a b ^ 4) (fun b _ => by have := ha0 b; positivity) hb
      exact (le_of_pow_le_pow_left₀ (n := 4) (by norm_num) hA0 (h1.trans hZ4)).trans hA
    set β₁ : Site × Fin 4 × Fin 4 → Site × Fin 4 := fun p => (p.1, p.2.1) with hβ₁
    set β₂ : Site × Fin 4 × Fin 4 → Site × Fin 4 := fun p => (p.1 + basisVector p.2.1, p.2.2) with hβ₂
    set β₃ : Site × Fin 4 × Fin 4 → Site × Fin 4 := fun p => (p.1 + basisVector p.2.2, p.2.1) with hβ₃
    set β₄ : Site × Fin 4 × Fin 4 → Site × Fin 4 := fun p => (p.1, p.2.2) with hβ₄
    set F : Site × Fin 4 × Fin 4 → ℝ := fun p =>
      144 / l ^ 2 * (a (β₁ p) ^ 2 + a (β₂ p) ^ 2 + a (β₃ p) ^ 2 + a (β₄ p) ^ 2) +
        1452 * (a (β₁ p) ^ 4 + a (β₂ p) ^ 4 + a (β₃ p) ^ 4 + a (β₄ p) ^ 4) with hF
    have hF0 : ∀ p, 0 ≤ F p := fun p => by
      simp only [hF]
      positivity
    set Dp : Site × Fin 4 × Fin 4 → ℝ := fun p => distOne (latticePlaquette X p.1 p.2.1 p.2.2) ^ 2 with hDp
    have hDp0 : ∀ p, 0 ≤ Dp p := fun p => by
      simp only [hDp]
      positivity
    have point : ∀ p ∈ orientedPlaquettesOf D,
        distOne (latticePlaquette (latticeGaugeTransform (fun x => (gt x)⁻¹) Z') p.1 p.2.1 p.2.2) ^ 2 ≤
          3 * (if p ∈ orientedPlaquettesOf Sh then Dp p else 0) +
            (if p ∈ orientedPlaquettesOf P₀ then F p else 0) := by
      rintro ⟨y, μ, ν⟩ hp
      obtain ⟨c0, cne, c1, c2, c3⟩ := mem_orientedPlaquettesOf.1 hp
      simp only at c0 cne c1 c2 c3 ⊢
      rw [latticePlaquette_gaugeTransform, distOne_conj]
      set n0 := _root_.YangMills.Construction.ShellFilling.Interpolation.supDist o y with hn0
      set n1 := _root_.YangMills.Construction.ShellFilling.Interpolation.supDist o (y + basisVector μ) with hn1
      set n2 := _root_.YangMills.Construction.ShellFilling.Interpolation.supDist o (y + basisVector ν) with hn2
      set n3 := _root_.YangMills.Construction.ShellFilling.Interpolation.supDist o (y + basisVector μ + basisVector ν) with hn3
      have b01 := _root_.YangMills.Construction.ShellFilling.Interpolation.supDist_add_basis_le o y μ
      have b10 := _root_.YangMills.Construction.ShellFilling.Interpolation.supDist_le_add_basis o y μ
      have b02 := _root_.YangMills.Construction.ShellFilling.Interpolation.supDist_add_basis_le o y ν
      have b20 := _root_.YangMills.Construction.ShellFilling.Interpolation.supDist_le_add_basis o y ν
      have b13 := _root_.YangMills.Construction.ShellFilling.Interpolation.supDist_add_basis_le o (y + basisVector μ) ν
      have b31 := _root_.YangMills.Construction.ShellFilling.Interpolation.supDist_le_add_basis o (y + basisVector μ) ν
      have ecomm : y + basisVector ν + basisVector μ = y + basisVector μ + basisVector ν := add_right_comm _ _ _
      have hzero : ∀ q : ℝ, 0 ≤ (if (y, μ, ν) ∈ orientedPlaquettesOf P₀ then F (y, μ, ν) else 0) := by
        intro _
        split_ifs
        · exact hF0 _
        · exact le_rfl
      have hone : 0 ≤ (if (y, μ, ν) ∈ orientedPlaquettesOf Sh then Dp (y, μ, ν) else 0) := by
        split_ifs
        · exact hDp0 _
        · exact le_rfl
      by_cases cA : n0 < 1.15 * l
      · have z0 : w y = 0 := rampWeight_eq_zero l _ hl0 (by linarith)
        have z1 : w (y + basisVector μ) = 0 := rampWeight_eq_zero l _ hl0 (by linarith)
        have z2 : w (y + basisVector ν) = 0 := rampWeight_eq_zero l _ hl0 (by linarith)
        have z3 : w (y + basisVector μ + basisVector ν) = 0 := rampWeight_eq_zero l _ hl0 (by linarith)
        have t1 : tb y μ = 0 := by simp [htb, z0, z1]
        have t2 : tb (y + basisVector μ) ν = 0 := by simp [htb, z1, z3]
        have t3 : tb (y + basisVector ν) μ = 0 := by simp [htb, ecomm, z2, z3]
        have t4 : tb y ν = 0 := by simp [htb, z0, z2]
        have e : latticePlaquette Z' y μ ν = 1 := by
          unfold latticePlaquette
          simp only [hZ', t1, t2, t3, t4, hΦ0]
          simp
        rw [e, distOne_one]
        have h8 := hzero 0
        have e0 : (0 : ℝ) ^ 2 = 0 := by norm_num
        rw [e0]
        linarith
      · by_cases cB : 1.85 * l < n0
        · have z0 : w y = 1 := rampWeight_eq_one l _ hl0 (by linarith)
          have z1 : w (y + basisVector μ) = 1 := rampWeight_eq_one l _ hl0 (by linarith)
          have z2 : w (y + basisVector ν) = 1 := rampWeight_eq_one l _ hl0 (by linarith)
          have z3 : w (y + basisVector μ + basisVector ν) = 1 := rampWeight_eq_one l _ hl0 (by linarith)
          have t1 : tb y μ = 1 := by simp [htb, z0, z1]
          have t2 : tb (y + basisVector μ) ν = 1 := by simp [htb, z1, z3]
          have t3 : tb (y + basisVector ν) μ = 1 := by simp [htb, ecomm, z2, z3]
          have t4 : tb y ν = 1 := by simp [htb, z0, z2]
          have e : latticePlaquette Z' y μ ν = latticePlaquette Z y μ ν := by
            unfold latticePlaquette
            simp only [hZ', t1, t2, t3, t4, hΦ1]
          have hSmem : (y, μ, ν) ∈ orientedPlaquettesOf Sh := by
            refine mem_orientedPlaquettesOf.2 ⟨?_, cne, ?_, ?_, ?_⟩
            · exact (hSh _).2 ⟨c0, (isBeyondSupDist_iff _ _ _).2 (by linarith)⟩
            · exact (hSh _).2 ⟨c1, (isBeyondSupDist_iff _ _ _).2 (by linarith)⟩
            · exact (hSh _).2 ⟨c2, (isBeyondSupDist_iff _ _ _).2 (by linarith)⟩
            · exact (hSh _).2 ⟨c3, (isBeyondSupDist_iff _ _ _).2 (by linarith)⟩
          rw [e, hZdef, latticePlaquette_gaugeTransform, distOne_conj, if_pos hSmem]
          have := hzero 0
          have h2 := hDp0 (y, μ, ν)
          have e2 : distOne (latticePlaquette X y μ ν) ^ 2 = Dp (y, μ, ν) := rfl
          rw [e2]
          linarith
        · have m0 : y ∈ P₀ := (hP₀ _).2 ⟨by linarith, by linarith⟩
          have m1 : y + basisVector μ ∈ P₀ := (hP₀ _).2 ⟨by linarith, by linarith⟩
          have m2 : y + basisVector ν ∈ P₀ := (hP₀ _).2 ⟨by linarith, by linarith⟩
          have m3 : y + basisVector μ + basisVector ν ∈ P₀ := (hP₀ _).2 ⟨by linarith, by linarith⟩
          have hPmem : (y, μ, ν) ∈ orientedPlaquettesOf P₀ := mem_orientedPlaquettesOf.2 ⟨m0, cne, m1, m2, m3⟩
          have hSmem : (y, μ, ν) ∈ orientedPlaquettesOf Sh := by
            refine mem_orientedPlaquettesOf.2 ⟨?_, cne, ?_, ?_, ?_⟩
            · exact (hSh _).2 ⟨c0, (isBeyondSupDist_iff _ _ _).2 (by linarith)⟩
            · exact (hSh _).2 ⟨c1, (isBeyondSupDist_iff _ _ _).2 (by linarith)⟩
            · exact (hSh _).2 ⟨c2, (isBeyondSupDist_iff _ _ _).2 (by linarith)⟩
            · exact (hSh _).2 ⟨c3, (isBeyondSupDist_iff _ _ _).2 (by linarith)⟩
          rw [if_pos hPmem, if_pos hSmem]
          have q1 : a (y, μ) ≤ 1 / 2 := hab _ (mem_bondsOf.2 ⟨m0, m1⟩)
          have q2 : a (y + basisVector μ, ν) ≤ 1 / 2 := hab _ (mem_bondsOf.2 ⟨m1, m3⟩)
          have q3 : a (y + basisVector ν, μ) ≤ 1 / 2 := hab _ (mem_bondsOf.2 ⟨m2, by simpa [ecomm] using m3⟩)
          have q4 : a (y, ν) ≤ 1 / 2 := hab _ (mem_bondsOf.2 ⟨m0, m2⟩)
          have hmain := hplaq (tb y μ) (tb (y + basisVector μ) ν) (tb (y + basisVector ν) μ) (tb y ν)
            (Z y μ) (Z (y + basisVector μ) ν) (Z (y + basisVector ν) μ) (Z y ν)
            (htb0 _ _) (htb1 _ _) (htb0 _ _) (htb1 _ _) (htb0 _ _) (htb1 _ _) (htb0 _ _) (htb1 _ _) q1 q2 q3 q4
          have hδ : (0 : ℝ) ≤ 4 / l := by positivity
          have wl : ∀ u v : ℝ, |u - v| ≤ 2 → |rampWeight l u - rampWeight l v| ≤ 4 / l := by
            intro u v huv
            refine (rampWeight_lipschitz l u v hl0).trans ?_
            rw [div_le_div_iff_of_pos_right hl0]
            linarith
          have ab : ∀ u v : ℝ, u ≤ v + 2 → v ≤ u + 2 → |u - v| ≤ 2 := fun u v h1 h2 =>
            abs_le.2 ⟨by linarith, by linarith⟩
          obtain ⟨d2, d3, d4⟩ := min_pairs_close (w y) (w (y + basisVector μ)) (w (y + basisVector ν))
            (w (y + basisVector μ + basisVector ν)) (4 / l) (wl _ _ (ab _ _ (by linarith) (by linarith)))
            (wl _ _ (ab _ _ (by linarith) (by linarith))) (wl _ _ (ab _ _ (by linarith) (by linarith)))
            (wl _ _ (ab _ _ (by linarith) (by linarith))) hδ
          have et1 : tb y μ = min (w y) (w (y + basisVector μ)) := rfl
          have et2 : tb (y + basisVector μ) ν = min (w (y + basisVector μ)) (w (y + basisVector μ + basisVector ν)) := rfl
          have et3 : tb (y + basisVector ν) μ = min (w (y + basisVector ν)) (w (y + basisVector μ + basisVector ν)) := by
            simp only [htb, ecomm]
          have et4 : tb y ν = min (w y) (w (y + basisVector ν)) := rfl
          rw [← et2, ← et1] at d2
          rw [← et3, ← et1] at d3
          rw [← et4, ← et1] at d4
          have eZ : distOne (Z y μ * Z (y + basisVector μ) ν * (Z (y + basisVector ν) μ)⁻¹ * (Z y ν)⁻¹) =
              distOne (latticePlaquette X y μ ν) := by
            have : Z y μ * Z (y + basisVector μ) ν * (Z (y + basisVector ν) μ)⁻¹ * (Z y ν)⁻¹ =
                latticePlaquette Z y μ ν := rfl
            rw [this, hZdef, latticePlaquette_gaugeTransform, distOne_conj]
          rw [eZ] at hmain
          exact plaquette_sq_bound l _ _ (a (y, μ)) (a (y + basisVector μ, ν)) (a (y + basisVector ν, μ)) (a (y, ν))
            _ _ _ hl0 (distOne_nonneg _) (ha0 _) (ha0 _) (ha0 _) (ha0 _) d2 d3 d4 hmain
    have hS1 : ∑ p ∈ orientedPlaquettesOf D, (if p ∈ orientedPlaquettesOf Sh then Dp p else 0) ≤ ε ^ 2 :=
      (sum_indicator_le _ (orientedPlaquettesOf Sh) Dp hDp0).trans hsum
    have hS2 : ∑ p ∈ orientedPlaquettesOf D, (if p ∈ orientedPlaquettesOf P₀ then F p else 0) ≤
        ∑ p ∈ orientedPlaquettesOf P₀, F p :=
      sum_indicator_le _ _ F hF0
    set B := bondsOf P₀ with hB
    set T2 := ∑ b ∈ B, a b ^ 2 with hT2
    set T4 := ∑ b ∈ B, a b ^ 4 with hT4
    have fib : ∀ (f : Site × Fin 4 → ℝ), (∀ b, 0 ≤ f b) →
        ∑ p ∈ orientedPlaquettesOf P₀, (f (β₁ p) + f (β₂ p) + f (β₃ p) + f (β₄ p)) ≤ 64 * ∑ b ∈ B, f b := by
      intro f hf
      have mm : ∀ p ∈ orientedPlaquettesOf P₀, β₁ p ∈ B ∧ β₂ p ∈ B ∧ β₃ p ∈ B ∧ β₄ p ∈ B := by
        rintro ⟨y, μ, ν⟩ hp
        obtain ⟨c0, -, c1, c2, c3⟩ := mem_orientedPlaquettesOf.1 hp
        simp only at c0 c1 c2 c3
        refine ⟨mem_bondsOf.2 ⟨c0, c1⟩, mem_bondsOf.2 ⟨c1, c3⟩, mem_bondsOf.2 ⟨c2, ?_⟩, mem_bondsOf.2 ⟨c0, c2⟩⟩
        simp only [hβ₃]
        rw [add_right_comm]
        exact c3
      have i1 := sum_comp_le_sixteen_mul (orientedPlaquettesOf P₀) B β₁ f hf (fun p hp => (mm p hp).1) (by
        rintro ⟨y, μ, ν⟩ _ ⟨y', μ', ν'⟩ _ h1 h2
        simp only [hβ₁, Prod.mk.injEq] at h1 h2 ⊢
        exact ⟨h2.1, h1.1, h1.2⟩)
      have i2 := sum_comp_le_sixteen_mul (orientedPlaquettesOf P₀) B β₂ f hf (fun p hp => (mm p hp).2.1) (by
        rintro ⟨y, μ, ν⟩ _ ⟨y', μ', ν'⟩ _ h1 h2
        simp only [hβ₂, Prod.mk.injEq] at h1 h2 ⊢
        obtain ⟨rfl, rfl⟩ := h1
        exact ⟨add_right_cancel h2.1, rfl, rfl⟩)
      have i3 := sum_comp_le_sixteen_mul (orientedPlaquettesOf P₀) B β₃ f hf (fun p hp => (mm p hp).2.2.1) (by
        rintro ⟨y, μ, ν⟩ _ ⟨y', μ', ν'⟩ _ h1 h2
        simp only [hβ₃, Prod.mk.injEq] at h1 h2 ⊢
        obtain ⟨rfl, rfl⟩ := h1
        exact ⟨add_right_cancel h2.1, rfl, rfl⟩)
      have i4 := sum_comp_le_sixteen_mul (orientedPlaquettesOf P₀) B β₄ f hf (fun p hp => (mm p hp).2.2.2) (by
        rintro ⟨y, μ, ν⟩ _ ⟨y', μ', ν'⟩ _ h1 h2
        simp only [hβ₄, Prod.mk.injEq] at h1 h2 ⊢
        exact ⟨h2.1, h1.1, h1.2⟩)
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib]
      linarith
    have f2 := fib (fun b => a b ^ 2) (fun b => by positivity)
    have f4 := fib (fun b => a b ^ 4) (fun b => by have := ha0 b; positivity)
    have hcardP : (P₀.card : ℝ) ≤ (4 * l) ^ 4 := card_le_of_supDist_le l hl o P₀ fun x hx => ((hP₀ x).1 hx).2
    have hcardB : (B.card : ℝ) ≤ 4 * (4 * l) ^ 4 := by
      have hsub : B ⊆ P₀ ×ˢ (Finset.univ : Finset (Fin 4)) := by
        intro b hb
        simp [(mem_bondsOf.1 hb).1]
      have h1 : B.card ≤ P₀.card * 4 := by
        have := Finset.card_le_card hsub
        simpa using this
      have h2 : (B.card : ℝ) ≤ (P₀.card : ℝ) * 4 := by exact_mod_cast h1
      linarith
    have hT2b : T2 ≤ 32 * l ^ 2 * A ^ 2 := by
      have h1 := sq_sum_le_card_mul_sum_sq (s := B) (f := fun b => a b ^ 2)
      have e : ∑ b ∈ B, (a b ^ 2) ^ 2 = T4 := by
        refine Finset.sum_congr rfl fun b _ => ?_
        ring
      rw [e] at h1
      have hT40 : 0 ≤ T4 := Finset.sum_nonneg fun b _ => by have := ha0 b; positivity
      have h2 : T2 ^ 2 ≤ (32 * l ^ 2 * A ^ 2) ^ 2 := by
        calc T2 ^ 2 ≤ (B.card : ℝ) * T4 := h1
          _ ≤ 4 * (4 * l) ^ 4 * A ^ 4 := mul_le_mul hcardB hZ4 hT40 (by positivity)
          _ = (32 * l ^ 2 * A ^ 2) ^ 2 := by ring
      exact le_of_pow_le_pow_left₀ (n := 2) (by norm_num) (by positivity) h2
    have hFsum : ∑ p ∈ orientedPlaquettesOf P₀, F p ≤ 294912 * A ^ 2 + 92928 * A ^ 4 := by
      have e : ∑ p ∈ orientedPlaquettesOf P₀, F p =
          144 / l ^ 2 * ∑ p ∈ orientedPlaquettesOf P₀, (a (β₁ p) ^ 2 + a (β₂ p) ^ 2 + a (β₃ p) ^ 2 + a (β₄ p) ^ 2) +
          1452 * ∑ p ∈ orientedPlaquettesOf P₀, (a (β₁ p) ^ 4 + a (β₂ p) ^ 4 + a (β₃ p) ^ 4 + a (β₄ p) ^ 4) := by
        simp only [hF]
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
      rw [e]
      have g1 : 144 / l ^ 2 * ∑ p ∈ orientedPlaquettesOf P₀,
          (a (β₁ p) ^ 2 + a (β₂ p) ^ 2 + a (β₃ p) ^ 2 + a (β₄ p) ^ 2) ≤
          144 / l ^ 2 * (64 * (32 * l ^ 2 * A ^ 2)) := by
        refine mul_le_mul_of_nonneg_left (f2.trans ?_) (by positivity)
        linarith
      have g2 : 144 / l ^ 2 * (64 * (32 * l ^ 2 * A ^ 2)) = 294912 * A ^ 2 := by
        field_simp
        ring
      linarith
    have hA2 : A ^ 4 ≤ A ^ 2 := by
      have : A ^ 2 ≤ 1 := by nlinarith
      nlinarith [sq_nonneg A]
    calc plaquetteDefect D (latticeGaugeTransform (fun x => (gt x)⁻¹) Z')
        = ∑ p ∈ orientedPlaquettesOf D,
            distOne (latticePlaquette (latticeGaugeTransform (fun x => (gt x)⁻¹) Z') p.1 p.2.1 p.2.2) ^ 2 := rfl
      _ ≤ ∑ p ∈ orientedPlaquettesOf D, (3 * (if p ∈ orientedPlaquettesOf Sh then Dp p else 0) +
            (if p ∈ orientedPlaquettesOf P₀ then F p else 0)) := Finset.sum_le_sum point
      _ = 3 * ∑ p ∈ orientedPlaquettesOf D, (if p ∈ orientedPlaquettesOf Sh then Dp p else 0) +
            ∑ p ∈ orientedPlaquettesOf D, (if p ∈ orientedPlaquettesOf P₀ then F p else 0) := by
          rw [Finset.sum_add_distrib, Finset.mul_sum]
      _ ≤ _ := by linarith
end Interpolation
open Interpolation in
theorem shellFillingStatement_holds (hG : ShellQuarticGauge) (hS : ExistsPathFromOne)
    (hP : PlaquetteAlongPathsBound) : shellFillingStatement := by
  classical
  obtain ⟨c₀, K, hc₀, hK, hgauge⟩ := hG
  obtain ⟨Φ, hΦ0, hΦ1, hnear, -⟩ := hS
  have hplaq := hP Φ hnear
  refine ⟨min (c₀ ^ 2) (1 / (4 * K ^ 2)), 3 + 387840 * K ^ 2, lt_min (by positivity) (by positivity),
    by positivity, ?_⟩
  intro l o D Sh X ε hl hD hSh h0 hc hsum
  have hεc : ε ≤ c₀ := by
    have h1 : ε ^ 2 ≤ c₀ ^ 2 := hc.trans (min_le_left _ _)
    exact le_of_pow_le_pow_left₀ (n := 2) (by norm_num) hc₀.le h1
  have hKε : K * ε ≤ 1 / 2 := by
    have h1 : ε ^ 2 ≤ 1 / (4 * K ^ 2) := hc.trans (min_le_right _ _)
    rw [le_div_iff₀ (by positivity)] at h1
    have h2 : (K * ε) ^ 2 ≤ (1 / 2) ^ 2 := by nlinarith
    exact le_of_pow_le_pow_left₀ (n := 2) (by norm_num) (by norm_num) h2
  set P₀ : Finset Site := D.filter fun x => 1.1 * l ≤ _root_.YangMills.Construction.ShellFilling.Interpolation.supDist o x ∧ _root_.YangMills.Construction.ShellFilling.Interpolation.supDist o x ≤ 1.9 * l with hP₀
  have hP₀mem : ∀ x, x ∈ P₀ ↔ 1.1 * l ≤ _root_.YangMills.Construction.ShellFilling.Interpolation.supDist o x ∧ _root_.YangMills.Construction.ShellFilling.Interpolation.supDist o x ≤ 1.9 * l := by
    intro x
    rw [hP₀, Finset.mem_filter, hD, isWithinSupDist_iff]
    constructor
    · exact fun h => h.2
    · exact fun h => ⟨by linarith [h.2], h⟩
  have hsub : plaquetteDefect P₀ X ≤ plaquetteDefect Sh X := by
    unfold plaquetteDefect
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun _ _ _ => by positivity
    have hm : ∀ x ∈ P₀, x ∈ Sh := by
      intro x hx
      refine (hSh x).2 ⟨(Finset.mem_filter.1 hx).1, (isBeyondSupDist_iff _ _ _).2 ?_⟩
      have := ((hP₀mem x).1 hx).1
      linarith
    intro p hp
    obtain ⟨a1, a2, a3, a4, a5⟩ := mem_orientedPlaquettesOf.1 hp
    exact mem_orientedPlaquettesOf.2 ⟨hm _ a1, a2, hm _ a3, hm _ a4, hm _ a5⟩
  obtain ⟨γ, hγ⟩ := hgauge l o P₀ hl (fun x => by rw [hP₀mem, isInShellOrthant_zero_iff]) X ε h0 hεc
    (hsub.trans hsum)
  obtain ⟨X', hX1, hX2⟩ := exists_filled_config Φ hΦ0 hΦ1
    (fun t₁ t₂ t₃ t₄ q₁ q₂ q₃ q₄ a₁ b₁ a₂ b₂ a₃ b₃ a₄ b₄ h₁ h₂ h₃ h₄ =>
      hplaq t₁ t₂ t₃ t₄ q₁ q₂ q₃ q₄ a₁ b₁ a₂ b₂ a₃ b₃ a₄ b₄ h₁ h₂ h₃ h₄)
    l o D Sh P₀ X γ (K * ε) ε hl hD hSh hP₀mem hsum hγ (by positivity) hKε
  refine ⟨X', hX1, hX2.trans (le_of_eq ?_)⟩
  ring
end ShellFilling
end YangMills.Construction
end
