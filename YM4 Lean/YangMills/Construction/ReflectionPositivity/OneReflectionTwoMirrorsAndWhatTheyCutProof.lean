import YangMills.Construction.InfiniteLattice.BondsAndCutPlaquettesAtAMirrorProof
import YangMills.Construction.InfiniteLattice.TorusInequalitiesPassToTheMeasuresOfAnInvariantClassProof
import YangMills.Construction.InfiniteLattice.BondsAndPlaquettesOfATorusAreFaithful
import YangMills.Construction.ReflectionPositivity.ActionOfASplitTorusSplitsProof
import YangMills.Construction.ReflectionPositivity.DescentToASplitTorusProof
import YangMills.Construction.ReflectionPositivity.IntegralOverTheTwoHalvesFactorsProof
import YangMills.Construction.TransferOperators.PeriodicGibbsStatesAreInvariantUnderLinkMirrors
import Mathlib
set_option autoImplicit false
open Set
open scoped Matrix
noncomputable section
namespace YangMills.Construction.InfiniteLattice
namespace TwoLevels
open NormalFamilies
open PeriodicLattice (coordVec)
section Residues
variable (z : ℤ)
def UpperHalfRes (W : ℤ) : Prop := ∃ k : ℤ, 0 ≤ W + 4 * (z * k) ∧ W + 4 * (z * k) ≤ 2 * z
def LowerHalfRes (W : ℤ) : Prop := ∃ k : ℤ, 2 * z ≤ W + 4 * (z * k) ∧ W + 4 * (z * k) ≤ 4 * z
def ModCong (W V : ℤ) : Prop := ∃ k : ℤ, V = W + 4 * (z * k)
variable {z}
theorem ModCong.symm {W V : ℤ} (h : ModCong z W V) : ModCong z V W := by
  obtain ⟨k, rfl⟩ := h
  exact ⟨-k, by rw [mul_neg]; ring⟩
theorem ModCong.trans {W V X : ℤ} (h : ModCong z W V) (h' : ModCong z V X) : ModCong z W X := by
  obtain ⟨k, rfl⟩ := h
  obtain ⟨k', rfl⟩ := h'
  exact ⟨k + k', by rw [mul_add]; ring⟩
private theorem mul_cases (hz : 2 ≤ z) (k : ℤ) :
    k = 0 ∨ k = 1 ∨ k = -1 ∨ (2 * z ≤ z * k) ∨ (z * k ≤ -(2 * z)) := by
  rcases lt_trichotomy k 0 with h | h | h
  · rcases eq_or_lt_of_le (show k ≤ -1 by omega) with h' | h'
    · exact Or.inr (Or.inr (Or.inl h'))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (by nlinarith))))
  · exact Or.inl h
  · rcases eq_or_lt_of_le (show 1 ≤ k by omega) with h' | h'
    · exact Or.inr (Or.inl h'.symm)
    · exact Or.inr (Or.inr (Or.inr (Or.inl (by nlinarith))))
theorem exists_residue (hz : 2 ≤ z) (W : ℤ) : ∃ q r : ℤ, W = r + 4 * (z * q) ∧ 0 ≤ r ∧ r < 4 * z := by
  have h4 : (4 * z) ≠ 0 := by omega
  refine ⟨W / (4 * z), W % (4 * z), ?_, Int.emod_nonneg _ h4, Int.emod_lt_of_pos _ (by omega)⟩
  have := Int.emod_add_mul_ediv W (4 * z)
  linarith [this, mul_assoc 4 z (W / (4 * z))]
theorem upperHalfRes_iff (hz : 2 ≤ z) {W r q : ℤ} (h : W = r + 4 * (z * q)) (h₁ : -2 ≤ r)
    (h₂ : r < 4 * z + 2) : UpperHalfRes z W ↔ (0 ≤ r ∧ r ≤ 2 * z) ∨ 4 * z ≤ r := by
  subst h
  constructor
  · rintro ⟨k, hk₁, hk₂⟩
    have e : r + 4 * (z * q) + 4 * (z * k) = r + 4 * (z * (q + k)) := by rw [mul_add]; ring
    rw [e] at hk₁ hk₂
    rcases mul_cases hz (q + k) with h | h | h | h | h
    · rw [h] at hk₁ hk₂; simp at hk₁ hk₂; omega
    · rw [h] at hk₁ hk₂; simp at hk₁ hk₂; omega
    · rw [h] at hk₁ hk₂; simp at hk₁ hk₂; omega
    · omega
    · omega
  · rintro (⟨a, b⟩ | a)
    · refine ⟨-q, ?_, ?_⟩ <;> rw [mul_neg] <;> omega
    · refine ⟨-q - 1, ?_, ?_⟩ <;> rw [mul_sub, mul_neg, mul_one] <;> omega
theorem lowerHalfRes_iff (hz : 2 ≤ z) {W r q : ℤ} (h : W = r + 4 * (z * q)) (h₁ : -2 ≤ r)
    (h₂ : r < 4 * z + 2) : LowerHalfRes z W ↔ (2 * z ≤ r ∧ r ≤ 4 * z) ∨ r ≤ 0 := by
  subst h
  constructor
  · rintro ⟨k, hk₁, hk₂⟩
    have e : r + 4 * (z * q) + 4 * (z * k) = r + 4 * (z * (q + k)) := by rw [mul_add]; ring
    rw [e] at hk₁ hk₂
    rcases mul_cases hz (q + k) with h | h | h | h | h
    · rw [h] at hk₁ hk₂; simp at hk₁ hk₂; omega
    · rw [h] at hk₁ hk₂; simp at hk₁ hk₂; omega
    · rw [h] at hk₁ hk₂; simp at hk₁ hk₂; omega
    · omega
    · omega
  · rintro (⟨a, b⟩ | a)
    · refine ⟨-q, ?_, ?_⟩ <;> rw [mul_neg] <;> omega
    · refine ⟨-q + 1, ?_, ?_⟩ <;> rw [mul_add, mul_neg, mul_one] <;> omega
theorem modCong_iff (hz : 2 ≤ z) {W r q V : ℤ} (h : W = r + 4 * (z * q)) (h₁ : -2 ≤ r)
    (h₂ : r < 4 * z + 2) (h₃ : -1 ≤ V) (h₄ : V ≤ 2 * z + 1) :
    ModCong z W V ↔ r = V ∨ r = V + 4 * z := by
  subst h
  constructor
  · rintro ⟨k, hk⟩
    have e : r + 4 * (z * q) + 4 * (z * k) = r + 4 * (z * (q + k)) := by rw [mul_add]; ring
    rw [e] at hk
    rcases mul_cases hz (q + k) with h | h | h | h | h
    · rw [h] at hk; simp at hk; omega
    · rw [h] at hk; simp at hk; omega
    · rw [h] at hk; simp at hk; omega
    · omega
    · omega
  · rintro (a | a)
    · exact ⟨-q, by rw [mul_neg]; omega⟩
    · exact ⟨-q - 1, by rw [mul_sub, mul_neg, mul_one]; omega⟩
theorem ModCong.eq_of_close (hz : 2 ≤ z) {W V : ℤ} (h : ModCong z W V) (h₁ : V - W < 4 * z)
    (h₂ : W - V < 4 * z) : W = V := by
  obtain ⟨k, rfl⟩ := h
  rcases mul_cases hz k with h | h | h | h | h
  · rw [h]; simp
  · rw [h] at h₁ h₂; simp at h₁ h₂
  · rw [h] at h₁ h₂; simp at h₁ h₂
  · omega
  · omega
theorem ModCong.emod_two_eq {W V : ℤ} (h : ModCong z W V) : W % 2 = V % 2 := by
  obtain ⟨k, rfl⟩ := h
  omega
theorem upper_or_lower (hz : 2 ≤ z) (W : ℤ) : UpperHalfRes z W ∨ LowerHalfRes z W := by
  obtain ⟨q, r, h, h₁, h₂⟩ := exists_residue hz W
  rw [upperHalfRes_iff hz h (by omega) (by omega), lowerHalfRes_iff hz h (by omega) (by omega)]
  omega
theorem triple_even (hz : 2 ≤ z) {W : ℤ} (hW : W % 2 = 0) (h0 : ¬ ModCong z W 0)
    (hz' : ¬ ModCong z W (2 * z)) :
    (UpperHalfRes z W ∧ UpperHalfRes z (W + 2) ∧ UpperHalfRes z (W - 2)) ∨
      (LowerHalfRes z W ∧ LowerHalfRes z (W + 2) ∧ LowerHalfRes z (W - 2)) := by
  obtain ⟨q, r, h, h₁, h₂⟩ := exists_residue hz W
  have h' : W + 2 = (r + 2) + 4 * (z * q) := by omega
  have h'' : W - 2 = (r - 2) + 4 * (z * q) := by omega
  rw [modCong_iff hz h (by omega) (by omega) (by omega) (by omega)] at h0 hz'
  rw [upperHalfRes_iff hz h (by omega) (by omega), lowerHalfRes_iff hz h (by omega) (by omega),
    upperHalfRes_iff hz h' (by omega) (by omega), lowerHalfRes_iff hz h' (by omega) (by omega),
    upperHalfRes_iff hz h'' (by omega) (by omega), lowerHalfRes_iff hz h'' (by omega) (by omega)]
  omega
theorem adjacent_at_level (hz : 2 ≤ z) {W : ℤ} (h0 : ModCong z W 0 ∨ ModCong z W (2 * z)) :
    ¬ (UpperHalfRes z (W + 2) ∧ UpperHalfRes z (W - 2)) ∧
      ¬ (LowerHalfRes z (W + 2) ∧ LowerHalfRes z (W - 2)) := by
  obtain ⟨q, r, h, h₁, h₂⟩ := exists_residue hz W
  have h' : W + 2 = (r + 2) + 4 * (z * q) := by omega
  have h'' : W - 2 = (r - 2) + 4 * (z * q) := by omega
  rw [modCong_iff hz h (by omega) (by omega) (by omega) (by omega),
    modCong_iff hz h (by omega) (by omega) (by omega) (by omega)] at h0
  rw [upperHalfRes_iff hz h' (by omega) (by omega), lowerHalfRes_iff hz h' (by omega) (by omega),
    upperHalfRes_iff hz h'' (by omega) (by omega), lowerHalfRes_iff hz h'' (by omega) (by omega)]
  omega
theorem adjacent_odd_iff (hz : 2 ≤ z) {W : ℤ} (hW : W % 2 = 1) :
    ((UpperHalfRes z W ∧ UpperHalfRes z (W + 2)) ∨ (LowerHalfRes z W ∧ LowerHalfRes z (W + 2))) ↔
      ¬ (ModCong z W (-1) ∨ ModCong z W (2 * z - 1)) := by
  obtain ⟨q, r, h, h₁, h₂⟩ := exists_residue hz W
  have h' : W + 2 = (r + 2) + 4 * (z * q) := by omega
  rw [modCong_iff hz h (by omega) (by omega) (by omega) (by omega),
    modCong_iff hz h (by omega) (by omega) (by omega) (by omega),
    upperHalfRes_iff hz h (by omega) (by omega), lowerHalfRes_iff hz h (by omega) (by omega),
    upperHalfRes_iff hz h' (by omega) (by omega), lowerHalfRes_iff hz h' (by omega) (by omega)]
  omega
theorem UpperHalfRes.neg {W : ℤ} (h : UpperHalfRes z W) : LowerHalfRes z (-W) := by
  obtain ⟨k, h₁, h₂⟩ := h
  refine ⟨1 - k, ?_, ?_⟩ <;> rw [mul_sub, mul_one] <;> omega
theorem LowerHalfRes.neg {W : ℤ} (h : LowerHalfRes z W) : UpperHalfRes z (-W) := by
  obtain ⟨k, h₁, h₂⟩ := h
  refine ⟨1 - k, ?_, ?_⟩ <;> rw [mul_sub, mul_one] <;> omega
end Residues
section IntegerLevels
variable {n : AmbientSpace}
theorem normal_coord (hn : n ∈ normalSet) (ρ : Fin 4) :
    ∃ e : ℤ, n ρ = e ∧ (e = 0 ∨ e = 1 ∨ e = -1) := by
  have single : ∀ μ : Fin 4, coordVec μ ρ = if ρ = μ then 1 else 0 := fun μ => by
    simp [coordVec, Pi.single_apply]
  rcases hn with ⟨μ, rfl⟩ | ⟨μ, lam, hlt, rfl | rfl⟩
  · by_cases h : ρ = μ
    · exact ⟨1, by rw [single]; simp [h], by simp⟩
    · exact ⟨0, by rw [single]; simp [h], by simp⟩
  · by_cases h : ρ = μ
    · subst h
      exact ⟨1, by simp [single, hlt.ne], by simp⟩
    · by_cases h' : ρ = lam
      · subst h'
        exact ⟨1, by simp [single, hlt.ne'], by simp⟩
      · exact ⟨0, by simp [single, h, h'], by simp⟩
  · by_cases h : ρ = μ
    · subst h
      exact ⟨1, by simp [single, hlt.ne], by simp⟩
    · by_cases h' : ρ = lam
      · subst h'
        exact ⟨-1, by simp [single, hlt.ne'], by simp⟩
      · exact ⟨0, by simp [single, h, h'], by simp⟩
def entry (n : AmbientSpace) (ρ : Fin 4) : ℤ := ⌊n ρ⌋
theorem entry_cast (hn : n ∈ normalSet) (ρ : Fin 4) : (entry n ρ : ℝ) = n ρ := by
  obtain ⟨e, he, -⟩ := normal_coord hn ρ
  simp [entry, he]
theorem entry_cases (hn : n ∈ normalSet) (ρ : Fin 4) :
    entry n ρ = 0 ∨ entry n ρ = 1 ∨ entry n ρ = -1 := by
  obtain ⟨e, he, h⟩ := normal_coord hn ρ
  have : entry n ρ = e := by simp [entry, he]
  rwa [this]
def levelInt (n : AmbientSpace) (x : LatticePoint 1) : ℤ := ⌊n ⬝ᵥ (x : AmbientSpace)⌋
theorem levelInt_cast (hn : n ∈ normalSet) (x : LatticePoint 1) :
    (levelInt n x : ℝ) = n ⬝ᵥ (x : AmbientSpace) := by
  obtain ⟨m, hm⟩ := x.2
  have h : n ⬝ᵥ (x : AmbientSpace) = ((∑ μ, entry n μ * m μ : ℤ) : ℝ) := by
    push_cast
    refine Finset.sum_congr rfl fun μ _ => ?_
    rw [entry_cast hn, hm μ, mul_one]
  rw [levelInt, h, Int.floor_intCast]
theorem dotProduct_axisStep (n : AmbientSpace) (x : LatticePoint 1) (ρ : Fin 4) :
    n ⬝ᵥ ((x + axisStep 1 ρ : LatticePoint 1) : AmbientSpace) = n ⬝ᵥ (x : AmbientSpace) + n ρ := by apply _root_.YangMills.Construction.NormalFamilies.LevelCuts.linearHeight_add_axisStep <;> assumption
theorem levelInt_add_axisStep (hn : n ∈ normalSet) (x : LatticePoint 1) (ρ : Fin 4) :
    levelInt n (x + axisStep 1 ρ) = levelInt n x + entry n ρ := by
  have : (levelInt n (x + axisStep 1 ρ) : ℝ) = (levelInt n x + entry n ρ : ℤ) := by
    push_cast
    rw [levelInt_cast hn, levelInt_cast hn, entry_cast hn, dotProduct_axisStep]
  exact_mod_cast this
def halfLevel (n : AmbientSpace) (cc : ℤ) (x : LatticePoint 1) : ℤ := 2 * levelInt n x - cc
theorem dotProduct_eq_halfLevel (hn : n ∈ normalSet) {c : ℝ} {cc : ℤ} (hc : c = (cc : ℝ) / 2)
    (x : LatticePoint 1) :
    n ⬝ᵥ (x : AmbientSpace) = c + (halfLevel n cc x : ℝ) / 2 := by
  rw [halfLevel, hc]
  push_cast
  rw [levelInt_cast hn]
  ring
theorem halfLevel_add_axisStep (hn : n ∈ normalSet) (cc : ℤ) (x : LatticePoint 1) (ρ : Fin 4) :
    halfLevel n cc (x + axisStep 1 ρ) = halfLevel n cc x + 2 * entry n ρ := by
  rw [halfLevel, halfLevel, levelInt_add_axisStep hn]
  ring
theorem exists_half_int (hn : n ∈ normalSet) {c : ℝ} (hc : _root_.YangMills.Construction.NormalFamilies.IsAllowedLevel 1 n c) :
    ∃ cc : ℤ, c = (cc : ℝ) / 2 := by
  obtain ⟨F, rfl⟩ := exists_reflectionClass hn
  rw [isAllowedLevel_one_iff] at hc
  cases F with
  | axial μ =>
    obtain ⟨k, hk⟩ := hc.1 (by
      rw [normSq_eq_dotProduct, ReflectionClass.realNormal_dot_axial])
    exact ⟨k, hk⟩
  | diagonal μ lam hlt s =>
    obtain ⟨k, hk⟩ := hc.2 (by
      rw [normSq_eq_dotProduct, ReflectionClass.realNormal_dot_diagonal])
    exact ⟨2 * k, by rw [hk]; push_cast; ring⟩
end IntegerLevels
structure Setup (Γ : PeriodSublattice 1) (n : AmbientSpace) (z : ℤ) (c : ℝ) (cc : ℤ)
    (w : LatticePoint 1) : Prop where
  normal_mem : n ∈ normalSet
  two_le : 2 ≤ z
  half_eq : c = (cc : ℝ) / 2
  period_mem : w ∈ Γ.periods
  period_eq : (w : AmbientSpace) = (2 * (z : ℝ)) • dualVector n
  height_sub : ∀ x y : LatticePoint 1, Γ.quotientMap x = Γ.quotientMap y →
    ∃ k : ℤ, n ⬝ᵥ (x : AmbientSpace) - n ⬝ᵥ (y : AmbientSpace) = 2 * (z : ℝ) * (k : ℝ)
section QuotientLevels
variable {Γ : PeriodSublattice 1} {n : AmbientSpace} {z : ℤ} {c : ℝ} {cc : ℤ} {w : LatticePoint 1}
theorem mem_siteHeights_iff (D : Setup Γ n z c cc w) (x : LatticePoint 1) (u : ℝ) :
    u ∈ Γ.siteHeights n z (Γ.quotientMap x) ↔
      ∃ k : ℤ, u = n ⬝ᵥ (x : AmbientSpace) + 2 * (z : ℝ) * (k : ℝ) := by
  constructor
  · rintro ⟨y, hy, k, rfl⟩
    obtain ⟨k', hk'⟩ := D.height_sub y x hy
    refine ⟨k + k', ?_⟩
    push_cast
    linarith [hk']
  · rintro ⟨k, rfl⟩
    exact ⟨x, rfl, k, rfl⟩
theorem hasHeight_iff (D : Setup Γ n z c cc w) (x : LatticePoint 1) {u : ℝ} {V : ℤ}
    (hu : u = c + (V : ℝ) / 2) :
    Γ.HasHeight n z (Γ.quotientMap x) u ↔ ModCong z (halfLevel n cc x) V := by
  rw [PeriodSublattice.HasHeight, mem_siteHeights_iff D, hu]
  have h := dotProduct_eq_halfLevel D.normal_mem D.half_eq x
  constructor
  · rintro ⟨k, hk⟩
    refine ⟨k, ?_⟩
    rw [h] at hk
    have : (V : ℝ) = (halfLevel n cc x : ℝ) + 4 * ((z : ℝ) * (k : ℝ)) := by linarith
    exact_mod_cast this
  · rintro ⟨k, hk⟩
    refine ⟨k, ?_⟩
    rw [h]
    have : (V : ℝ) = (halfLevel n cc x : ℝ) + 4 * ((z : ℝ) * (k : ℝ)) := by exact_mod_cast hk
    linarith
theorem mem_plusHalf_iff (D : Setup Γ n z c cc w) (x : LatticePoint 1) :
    Γ.quotientMap x ∈ Γ.plusHalf n z c ↔ UpperHalfRes z (halfLevel n cc x) := by
  have h := dotProduct_eq_halfLevel D.normal_mem D.half_eq x
  constructor
  · rintro ⟨u, hu, h₁, h₂⟩
    obtain ⟨k, rfl⟩ := (mem_siteHeights_iff D x u).1 hu
    rw [h] at h₁ h₂
    refine ⟨k, ?_, ?_⟩
    · have : (0 : ℝ) ≤ (halfLevel n cc x : ℝ) + 4 * ((z : ℝ) * (k : ℝ)) := by linarith
      exact_mod_cast this
    · have : (halfLevel n cc x : ℝ) + 4 * ((z : ℝ) * (k : ℝ)) ≤ 2 * (z : ℝ) := by linarith
      exact_mod_cast this
  · rintro ⟨k, h₁, h₂⟩
    have h₁' : (0 : ℝ) ≤ (halfLevel n cc x : ℝ) + 4 * ((z : ℝ) * (k : ℝ)) := by exact_mod_cast h₁
    have h₂' : (halfLevel n cc x : ℝ) + 4 * ((z : ℝ) * (k : ℝ)) ≤ 2 * (z : ℝ) := by
      exact_mod_cast h₂
    refine ⟨_, (mem_siteHeights_iff D x _).2 ⟨k, rfl⟩, ?_, ?_⟩ <;> rw [h] <;> linarith
theorem mem_minusHalf_iff (D : Setup Γ n z c cc w) (x : LatticePoint 1) :
    Γ.quotientMap x ∈ Γ.minusHalf n z c ↔ LowerHalfRes z (halfLevel n cc x) := by
  have h := dotProduct_eq_halfLevel D.normal_mem D.half_eq x
  constructor
  · rintro ⟨u, hu, h₁, h₂⟩
    obtain ⟨k, rfl⟩ := (mem_siteHeights_iff D x u).1 hu
    rw [h] at h₁ h₂
    refine ⟨k, ?_, ?_⟩
    · have : 2 * (z : ℝ) ≤ (halfLevel n cc x : ℝ) + 4 * ((z : ℝ) * (k : ℝ)) := by linarith
      exact_mod_cast this
    · have : (halfLevel n cc x : ℝ) + 4 * ((z : ℝ) * (k : ℝ)) ≤ 4 * (z : ℝ) := by linarith
      exact_mod_cast this
  · rintro ⟨k, h₁, h₂⟩
    have h₁' : 2 * (z : ℝ) ≤ (halfLevel n cc x : ℝ) + 4 * ((z : ℝ) * (k : ℝ)) := by
      exact_mod_cast h₁
    have h₂' : (halfLevel n cc x : ℝ) + 4 * ((z : ℝ) * (k : ℝ)) ≤ 4 * (z : ℝ) := by
      exact_mod_cast h₂
    refine ⟨_, (mem_siteHeights_iff D x _).2 ⟨k, rfl⟩, ?_, ?_⟩ <;> rw [h] <;> linarith
theorem halfLevel_add_zsmul (D : Setup Γ n z c cc w) (x : LatticePoint 1) (j : ℤ) :
    halfLevel n cc (x + j • w) = halfLevel n cc x + 4 * (z * j) := by
  have hc : ((j • w : LatticePoint 1) : AmbientSpace) = (j : ℝ) • (w : AmbientSpace) := by
    rw [AddSubgroup.coe_zsmul, Int.cast_smul_eq_zsmul]
  have hd : n ⬝ᵥ ((x + j • w : LatticePoint 1) : AmbientSpace) =
      n ⬝ᵥ (x : AmbientSpace) + 2 * (z : ℝ) * (j : ℝ) := by
    have : ((x + j • w : LatticePoint 1) : AmbientSpace) =
        (x : AmbientSpace) + (j : ℝ) • (w : AmbientSpace) := by
      rw [AddSubgroup.coe_add, hc]
    rw [this, dotProduct_add, dotProduct_smul, D.period_eq, dotProduct_smul,
      dotProduct_dualVector D.normal_mem]
    simp only [smul_eq_mul]
    ring
  have h₁ := dotProduct_eq_halfLevel D.normal_mem D.half_eq x
  have h₂ := dotProduct_eq_halfLevel D.normal_mem D.half_eq (x + j • w)
  have : (halfLevel n cc (x + j • w) : ℝ) = (halfLevel n cc x : ℝ) + 4 * ((z : ℝ) * (j : ℝ)) := by
    linarith
  exact_mod_cast this
end QuotientLevels
section LiftsOfCells
variable {Γ : PeriodSublattice 1}
def fwdLink (x : LatticePoint 1) (ρ : Fin 4) : PositiveLink 1 :=
  ⟨Link.forwardFrom x ρ, ρ, by simp [Link.forwardFrom]⟩
theorem exists_eq_fwdLink (b : PositiveLink 1) : ∃ x ρ, b = fwdLink x ρ := by
  obtain ⟨b, ρ, h⟩ := b
  refine ⟨b.initial, ρ, Subtype.ext (InfiniteLattice.Link.ext rfl ?_)⟩
  change b.terminal = b.initial + axisStep 1 ρ
  rw [← h]
  abel
theorem linkClass_surjective (Γ : PeriodSublattice 1) : Function.Surjective Γ.linkClass :=
  fun d => ⟨_, Γ.linkClass_linkRep d⟩
theorem faceClass_surjective (Γ : PeriodSublattice 1) : Function.Surjective Γ.faceClass := by apply _root_.YangMills.Construction.InfiniteLattice.PeriodDescent.faceClass_surjective <;> assumption
theorem endpoints_linkClass (b : PositiveLink 1) :
    Γ.linkEndpoints (Γ.linkClass b) = {Γ.quotientMap b.1.initial, Γ.quotientMap b.1.terminal} := by
  rw [Γ.linkEndpoints_eq, Γ.orientedOfLink_linkClass, Γ.sourcePoint_orientedClass,
    Γ.targetPoint_orientedClass]
theorem linkClass_mem_linksInside_iff {T : Set Γ.QuotientTorus} (b : PositiveLink 1) :
    Γ.linkClass b ∈ Γ.linksInside T ↔
      Γ.quotientMap b.1.initial ∈ T ∧ Γ.quotientMap b.1.terminal ∈ T := by apply _root_.YangMills.Construction.InfiniteLattice.SplitTorusActionProof.linkClass_mem_linksInside_iff <;> assumption
theorem forall_endpoints_fwdLink {Q : Γ.QuotientTorus → Prop} (x : LatticePoint 1) (ρ : Fin 4) :
    (∀ s ∈ Γ.linkEndpoints (Γ.linkClass (fwdLink x ρ)), Q s) ↔
      Q (Γ.quotientMap x) ∧ Q (Γ.quotientMap (x + axisStep 1 ρ)) := by
  rw [endpoints_linkClass]
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, forall_eq_or_imp, forall_eq]
  rfl
def plaquetteShift (p : ElementaryPlaquette 1) (γ : LatticePoint 1) : ElementaryPlaquette 1 :=
  ⟨p.corner + γ, p.lowAxis, p.highAxis, p.lowAxis_lt_highAxis⟩
theorem pointMap_shift (γ x : LatticePoint 1) : (shift γ).pointMap x = x + γ :=
  Subtype.ext rfl
theorem cornerSet_plaquetteShift (p : ElementaryPlaquette 1) (γ : LatticePoint 1) :
    (plaquetteShift p γ).cornerSet = (fun x => x + γ) '' p.cornerSet := by
  simp only [ElementaryPlaquette.cornerSet, plaquetteShift, Set.image_insert_eq, Set.image_singleton,
    add_right_comm]
theorem plaquetteMap_shift (hr : SymmetryActionRules.Statement)
    (γ : LatticePoint 1) (p : ElementaryPlaquette 1) :
    (shift γ).plaquetteMap p = plaquetteShift p γ := by
  refine ((((hr (shift γ) (shift γ)).2.2.2.1 p).1 (plaquetteShift p γ)).2 ?_).symm
  rw [cornerSet_plaquetteShift]
  exact Set.image_congr fun x _ => (pointMap_shift γ x).symm
theorem exists_rep_eq_shift (hr : SymmetryActionRules.Statement)
    (Γ : PeriodSublattice 1) (p : ElementaryPlaquette 1) :
    ∃ γ ∈ Γ.periods, Γ.plaquetteRep (Γ.faceClass p) = plaquetteShift p γ := by
  obtain ⟨γ, hγ, h⟩ := (Γ.quotientPlaquette_nonempty (Γ.faceClass p)).some_mem
  exact ⟨γ, hγ, h.trans (plaquetteMap_shift hr γ p)⟩
theorem plaquetteVertices_faceClass (hr : SymmetryActionRules.Statement)
    (p : ElementaryPlaquette 1) :
    Γ.plaquetteVertices (Γ.faceClass p) = Γ.quotientMap '' p.cornerSet := by apply _root_.YangMills.Construction.InfiniteLattice.PeriodDescent.plaquetteVertices_faceClass <;> assumption
theorem mem_linkSet_iff (p : ElementaryPlaquette 1) (b : PositiveLink 1) :
    b.1 ∈ p.linkSet ↔ b = fwdLink p.corner p.lowAxis ∨
      b = fwdLink (p.corner + axisStep 1 p.lowAxis) p.highAxis ∨
      b = fwdLink (p.corner + axisStep 1 p.highAxis) p.lowAxis ∨ b = fwdLink p.corner p.highAxis := by
  simp only [ElementaryPlaquette.linkSet, ElementaryPlaquette.edges, Set.mem_ofPred_eq, List.mem_cons,
    List.not_mem_nil, or_false, Subtype.ext_iff, fwdLink]
theorem linkClass_fwdLink_add (x : LatticePoint 1) (ρ : Fin 4) {γ : LatticePoint 1}
    (hγ : γ ∈ Γ.periods) : Γ.linkClass (fwdLink (x + γ) ρ) = Γ.linkClass (fwdLink x ρ) := by
  rw [← Γ.linkClass_translate (fwdLink x ρ) hγ]
  congr 1
  refine Subtype.ext (InfiniteLattice.Link.ext rfl ?_)
  change x + γ + axisStep 1 ρ = x + axisStep 1 ρ + γ
  abel
theorem plaquetteLinks_faceClass (hr : SymmetryActionRules.Statement)
    (p : ElementaryPlaquette 1) : Γ.plaquetteLinks (Γ.faceClass p) =
      {d | ∃ b : PositiveLink 1, b.1 ∈ p.linkSet ∧ d = Γ.linkClass b} := by
  obtain ⟨γ, hγ, h⟩ := exists_rep_eq_shift hr Γ p
  have key : ∀ (q : ElementaryPlaquette 1) (δ : LatticePoint 1), δ ∈ Γ.periods →
      ∀ b : PositiveLink 1, b.1 ∈ q.linkSet →
      ∃ b' : PositiveLink 1, b'.1 ∈ (plaquetteShift q δ).linkSet ∧
        Γ.linkClass b = Γ.linkClass b' := by
    intro q δ hδ b hb
    rw [mem_linkSet_iff] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact ⟨fwdLink (q.corner + δ) q.lowAxis, (mem_linkSet_iff _ _).2 (Or.inl rfl),
        (linkClass_fwdLink_add _ _ hδ).symm⟩
    · refine ⟨fwdLink (q.corner + δ + axisStep 1 q.lowAxis) q.highAxis,
        (mem_linkSet_iff _ _).2 (Or.inr (Or.inl rfl)), ?_⟩
      rw [add_right_comm, linkClass_fwdLink_add _ _ hδ]
    · refine ⟨fwdLink (q.corner + δ + axisStep 1 q.highAxis) q.lowAxis,
        (mem_linkSet_iff _ _).2 (Or.inr (Or.inr (Or.inl rfl))), ?_⟩
      rw [add_right_comm, linkClass_fwdLink_add _ _ hδ]
    · exact ⟨fwdLink (q.corner + δ) q.highAxis,
        (mem_linkSet_iff _ _).2 (Or.inr (Or.inr (Or.inr rfl))),
        (linkClass_fwdLink_add _ _ hδ).symm⟩
  have back : plaquetteShift (plaquetteShift p γ) (-γ) = p := by
    simp [plaquetteShift]
  ext d
  simp only [PeriodSublattice.plaquetteLinks, h, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨b, hb, rfl⟩
    obtain ⟨b', hb', e⟩ := key (plaquetteShift p γ) (-γ) (neg_mem hγ) b hb
    rw [back] at hb'
    exact ⟨b', hb', e⟩
  · rintro ⟨b, hb, rfl⟩
    obtain ⟨b', hb', e⟩ := key p γ hγ b hb
    exact ⟨b', hb', e⟩
theorem plaquetteLinks_subset_iff (hr : SymmetryActionRules.Statement)
    (p : ElementaryPlaquette 1) (T : Set Γ.QuotientTorus) :
    Γ.plaquetteLinks (Γ.faceClass p) ⊆ Γ.linksInside T ↔
      ∀ s ∈ p.cornerSet, Γ.quotientMap s ∈ T := by
  rw [plaquetteLinks_faceClass hr]
  have h₁ : ∀ x ρ, Γ.linkClass (fwdLink x ρ) ∈ Γ.linksInside T ↔
      Γ.quotientMap x ∈ T ∧ Γ.quotientMap (x + axisStep 1 ρ) ∈ T := fun x ρ =>
    linkClass_mem_linksInside_iff (fwdLink x ρ)
  constructor
  · intro h s hs
    have b₁ := (h₁ _ _).1 (h ⟨fwdLink p.corner p.lowAxis, (mem_linkSet_iff _ _).2 (Or.inl rfl), rfl⟩)
    have b₂ := (h₁ _ _).1 (h ⟨fwdLink (p.corner + axisStep 1 p.lowAxis) p.highAxis,
      (mem_linkSet_iff _ _).2 (Or.inr (Or.inl rfl)), rfl⟩)
    have b₄ := (h₁ _ _).1 (h ⟨fwdLink p.corner p.highAxis,
      (mem_linkSet_iff _ _).2 (Or.inr (Or.inr (Or.inr rfl))), rfl⟩)
    rcases hs with rfl | rfl | rfl | rfl
    · exact b₁.1
    · exact b₁.2
    · exact b₂.2
    · exact b₄.2
  · rintro h d ⟨b, hb, rfl⟩
    have m₁ : p.corner ∈ p.cornerSet := by simp [ElementaryPlaquette.cornerSet]
    have m₂ : p.corner + axisStep 1 p.lowAxis ∈ p.cornerSet := by
      simp [ElementaryPlaquette.cornerSet]
    have m₃ : p.corner + axisStep 1 p.lowAxis + axisStep 1 p.highAxis ∈ p.cornerSet := by
      simp [ElementaryPlaquette.cornerSet]
    have m₄ : p.corner + axisStep 1 p.highAxis ∈ p.cornerSet := by
      simp [ElementaryPlaquette.cornerSet]
    rcases (mem_linkSet_iff _ _).1 hb with rfl | rfl | rfl | rfl
    · exact (h₁ _ _).2 ⟨h _ m₁, h _ m₂⟩
    · exact (h₁ _ _).2 ⟨h _ m₂, h _ m₃⟩
    · refine (h₁ _ _).2 ⟨h _ m₄, ?_⟩
      rw [add_right_comm]
      exact h _ m₃
    · exact (h₁ _ _).2 ⟨h _ m₁, h _ m₄⟩
end LiftsOfCells
section SplitCells
variable {Γ : PeriodSublattice 1} {n : AmbientSpace} {z : ℤ} {c : ℝ} {cc : ℤ} {w : LatticePoint 1}
theorem linkClass_mem_plusLinks_iff (D : Setup Γ n z c cc w) (b : PositiveLink 1) :
    Γ.linkClass b ∈ Γ.plusLinks n z c ↔
      UpperHalfRes z (halfLevel n cc b.1.initial) ∧ UpperHalfRes z (halfLevel n cc b.1.terminal) := by
  rw [PeriodSublattice.plusLinks, linkClass_mem_linksInside_iff, mem_plusHalf_iff D,
    mem_plusHalf_iff D]
theorem linkClass_mem_minusLinks_iff (D : Setup Γ n z c cc w) (b : PositiveLink 1) :
    Γ.linkClass b ∈ Γ.minusLinks n z c ↔
      LowerHalfRes z (halfLevel n cc b.1.initial) ∧ LowerHalfRes z (halfLevel n cc b.1.terminal) := by
  rw [PeriodSublattice.minusLinks, linkClass_mem_linksInside_iff, mem_minusHalf_iff D,
    mem_minusHalf_iff D]
theorem isSplit_iff (hr : SymmetryActionRules.Statement)
    (D : Setup Γ n z c cc w) (p : ElementaryPlaquette 1) :
    Γ.IsSplitPlaquette n z c (Γ.faceClass p) ↔
      ¬ (∀ s ∈ p.cornerSet, UpperHalfRes z (halfLevel n cc s)) ∧
        ¬ (∀ s ∈ p.cornerSet, LowerHalfRes z (halfLevel n cc s)) := by
  rw [PeriodSublattice.IsSplitPlaquette, PeriodSublattice.plusLinks, PeriodSublattice.minusLinks,
    plaquetteLinks_subset_iff hr, plaquetteLinks_subset_iff hr]
  simp only [mem_plusHalf_iff D, mem_minusHalf_iff D]
end SplitCells
section MoreResidues
variable {z : ℤ}
theorem pair_upper_lower_iff (hz : 2 ≤ z) (W e : ℤ) (he : e = 0 ∨ e = 1 ∨ e = -1) :
    ((UpperHalfRes z W ∧ UpperHalfRes z (W + 2 * e)) ∧
        (LowerHalfRes z W ∧ LowerHalfRes z (W + 2 * e))) ↔
      (ModCong z W 0 ∧ ModCong z (W + 2 * e) 0) ∨
        (ModCong z W (2 * z) ∧ ModCong z (W + 2 * e) (2 * z)) := by
  obtain ⟨q, r, h, h₁, h₂⟩ := exists_residue hz W
  have h' : W + 2 * e = (r + 2 * e) + 4 * (z * q) := by omega
  rw [modCong_iff hz h (by omega) (by omega) (by omega) (by omega),
    modCong_iff hz h (by omega) (by omega) (by omega) (by omega),
    modCong_iff hz h' (by omega) (by omega) (by omega) (by omega),
    modCong_iff hz h' (by omega) (by omega) (by omega) (by omega),
    upperHalfRes_iff hz h (by omega) (by omega), lowerHalfRes_iff hz h (by omega) (by omega),
    upperHalfRes_iff hz h' (by omega) (by omega), lowerHalfRes_iff hz h' (by omega) (by omega)]
  omega
theorem pair_one_side_even (hz : 2 ≤ z) {W : ℤ} (hW : W % 2 = 0) (e : ℤ)
    (he : e = 0 ∨ e = 1 ∨ e = -1) :
    (UpperHalfRes z W ∧ UpperHalfRes z (W + 2 * e)) ∨
      (LowerHalfRes z W ∧ LowerHalfRes z (W + 2 * e)) := by
  obtain ⟨q, r, h, h₁, h₂⟩ := exists_residue hz W
  have h' : W + 2 * e = (r + 2 * e) + 4 * (z * q) := by omega
  rw [upperHalfRes_iff hz h (by omega) (by omega), lowerHalfRes_iff hz h (by omega) (by omega),
    upperHalfRes_iff hz h' (by omega) (by omega), lowerHalfRes_iff hz h' (by omega) (by omega)]
  omega
theorem ModCong.exists_mul {W V m : ℤ} (h : ModCong z W V) (hV : V = 2 * z * m) :
    ∃ j : ℤ, W = 2 * z * j := by
  obtain ⟨k, hk⟩ := h
  exact ⟨m - 2 * k, by linear_combination hV - hk⟩
end MoreResidues
section Entries
theorem entry_of_eq {n : AmbientSpace} {ρ : Fin 4} {e : ℤ} (h : n ρ = e) : entry n ρ = e := by
  simp [entry, h]
theorem entry_coordVec (μ ρ : Fin 4) :
    entry (coordVec μ) ρ = if ρ = μ then 1 else 0 := by
  by_cases h : ρ = μ
  · subst h
    exact (entry_of_eq (e := 1) (by simp [coordVec])).trans (by simp)
  · exact (entry_of_eq (e := 0) (by simp [coordVec, h])).trans (by simp [h])
theorem entry_coordVec_add {μ lam : Fin 4} (hne : μ < lam) (ρ : Fin 4) :
    entry (coordVec μ + coordVec lam) ρ =
      if ρ = μ then 1 else if ρ = lam then 1 else 0 := by
  by_cases h : ρ = μ
  · subst h
    exact (entry_of_eq (e := 1) (by simp [coordVec, hne.ne])).trans (by simp)
  · by_cases h' : ρ = lam
    · subst h'
      exact (entry_of_eq (e := 1) (by simp [coordVec, hne.ne'])).trans (by simp [h])
    · exact (entry_of_eq (e := 0) (by simp [coordVec, h, h'])).trans (by simp [h, h'])
theorem entry_coordVec_sub {μ lam : Fin 4} (hne : μ < lam) (ρ : Fin 4) :
    entry (coordVec μ - coordVec lam) ρ =
      if ρ = μ then 1 else if ρ = lam then -1 else 0 := by
  by_cases h : ρ = μ
  · subst h
    exact (entry_of_eq (e := 1) (by simp [coordVec, hne.ne])).trans (by simp)
  · by_cases h' : ρ = lam
    · subst h'
      exact (entry_of_eq (e := -1) (by simp [coordVec, hne.ne'])).trans (by simp [h])
    · exact (entry_of_eq (e := 0) (by simp [coordVec, h, h'])).trans (by simp [h, h'])
theorem normSq_diag {n : AmbientSpace} {μ lam : Fin 4} (hlt : μ < lam)
    (h : n = coordVec μ - coordVec lam ∨ n = coordVec μ + coordVec lam) : normSq n = 2 := by
  rw [normSq_eq_dotProduct]
  rcases h with rfl | rfl
  · simp [coordVec, dotProduct_sub, hlt.ne, hlt.ne']
    norm_num
  · simp [coordVec, dotProduct_add, hlt.ne, hlt.ne']
    norm_num
theorem normSq_coordVec (μ : Fin 4) : normSq (coordVec μ) = 1 := by apply _root_.YangMills.Construction.TransferOperators.normSq_coordVec <;> assumption
end Entries
section SharedAndCrossing
variable {Γ : PeriodSublattice 1} {n : AmbientSpace} {z : ℤ} {c : ℝ} {cc : ℤ} {w : LatticePoint 1}
theorem level_base : c = c + ((0 : ℤ) : ℝ) / 2 := by simp
theorem level_half_period : c + (z : ℝ) = c + ((2 * z : ℤ) : ℝ) / 2 := by
  push_cast
  ring
theorem sharedLinks_eq (D : Setup Γ n z c cc w) :
    Γ.sharedLinks n z c =
      {b | (∀ s ∈ Γ.linkEndpoints b, Γ.HasHeight n z s c) ∨
        ∀ s ∈ Γ.linkEndpoints b, Γ.HasHeight n z s (c + (z : ℝ))} := by
  ext d
  obtain ⟨b, rfl⟩ := linkClass_surjective Γ d
  obtain ⟨x, ρ, rfl⟩ := exists_eq_fwdLink b
  have hy : (fwdLink x ρ).1.terminal = x + axisStep 1 ρ := rfl
  have hx : (fwdLink x ρ).1.initial = x := rfl
  have e := halfLevel_add_axisStep D.normal_mem cc x ρ
  rw [PeriodSublattice.sharedLinks, Set.mem_inter_iff, linkClass_mem_plusLinks_iff D,
    linkClass_mem_minusLinks_iff D]
  change _ ↔ ((∀ s ∈ Γ.linkEndpoints (Γ.linkClass (fwdLink x ρ)), Γ.HasHeight n z s c) ∨
    ∀ s ∈ Γ.linkEndpoints (Γ.linkClass (fwdLink x ρ)), Γ.HasHeight n z s (c + (z : ℝ)))
  rw [forall_endpoints_fwdLink, forall_endpoints_fwdLink, hx, hy,
    hasHeight_iff D x level_base, hasHeight_iff D (x + axisStep 1 ρ) level_base,
    hasHeight_iff D x level_half_period,
    hasHeight_iff D (x + axisStep 1 ρ) level_half_period, e]
  exact pair_upper_lower_iff D.two_le _ _ (entry_cases D.normal_mem ρ)
theorem halfLevel_even (h : cc % 2 = 0) (x : LatticePoint 1) : halfLevel n cc x % 2 = 0 := by
  rw [halfLevel]
  omega
theorem halfLevel_odd (h : cc % 2 = 1) (x : LatticePoint 1) : halfLevel n cc x % 2 = 1 := by
  rw [halfLevel]
  omega
theorem crossingLinks_empty (D : Setup Γ n z c cc w) (hcc : cc % 2 = 0) :
    Γ.crossingLinks n z c = ∅ := by
  refine Set.eq_empty_of_forall_notMem fun d hd => hd ?_
  obtain ⟨b, rfl⟩ := linkClass_surjective Γ d
  obtain ⟨x, ρ, rfl⟩ := exists_eq_fwdLink b
  have e := halfLevel_add_axisStep D.normal_mem cc x ρ
  rcases pair_one_side_even D.two_le (halfLevel_even (n := n) hcc x) _
      (entry_cases D.normal_mem ρ) with h | h
  · refine Or.inl ((linkClass_mem_plusLinks_iff D _).2 ?_)
    change UpperHalfRes z _ ∧ UpperHalfRes z (halfLevel n cc (x + axisStep 1 ρ))
    rwa [e]
  · refine Or.inr ((linkClass_mem_minusLinks_iff D _).2 ?_)
    change LowerHalfRes z _ ∧ LowerHalfRes z (halfLevel n cc (x + axisStep 1 ρ))
    rwa [e]
theorem reflect_pointMap_coe (D : Setup Γ n z c cc w) (hc : _root_.YangMills.Construction.NormalFamilies.IsAllowedLevel 1 n c)
    (x : LatticePoint 1) :
    ((_root_.YangMills.Construction.NormalFamilies.NormalLevelPair.reflectSymmetry ⟨n, D.normal_mem, c, hc⟩).pointMap x : AmbientSpace) =
      (x : AmbientSpace) - ((halfLevel n cc x : ℤ) : ℝ) • dualVector n := by
  change reflectAcross n c (x : AmbientSpace) = _
  rw [reflectAcross, dotProduct_eq_halfLevel D.normal_mem D.half_eq x]
  congr 2
  ring
theorem reflect_pointMap_of_eq (D : Setup Γ n z c cc w) (hc : _root_.YangMills.Construction.NormalFamilies.IsAllowedLevel 1 n c)
    (x : LatticePoint 1) {j : ℤ} (h : halfLevel n cc x = 2 * z * j) :
    (_root_.YangMills.Construction.NormalFamilies.NormalLevelPair.reflectSymmetry ⟨n, D.normal_mem, c, hc⟩).pointMap x = x + (-j) • w := by
  refine Subtype.ext ?_
  rw [reflect_pointMap_coe D hc, h, AddSubgroup.coe_add, AddSubgroup.coe_zsmul,
    ← Int.cast_smul_eq_zsmul ℝ, D.period_eq, smul_smul]
  push_cast
  rw [sub_eq_add_neg, ← neg_smul]
  congr 2
  ring
theorem shared_fixed (D : Setup Γ n z c cc w) (hc : _root_.YangMills.Construction.NormalFamilies.IsAllowedLevel 1 n c)
    (hI : Γ.DescendsToQuotient (_root_.YangMills.Construction.NormalFamilies.NormalLevelPair.reflectSymmetry ⟨n, D.normal_mem, c, hc⟩)) :
    ∀ b ∈ Γ.sharedLinks n z c,
      Γ.descendOrientedLink (_root_.YangMills.Construction.NormalFamilies.NormalLevelPair.reflectSymmetry ⟨n, D.normal_mem, c, hc⟩)
        (Γ.orientedOfLink b) = Γ.orientedOfLink b := by
  intro d hd
  rw [sharedLinks_eq D] at hd
  obtain ⟨b, rfl⟩ := linkClass_surjective Γ d
  obtain ⟨x, ρ, rfl⟩ := exists_eq_fwdLink b
  have hz := D.two_le
  have e := halfLevel_add_axisStep D.normal_mem cc x ρ
  have near := entry_cases D.normal_mem ρ
  have key : ∃ j : ℤ, halfLevel n cc x = 2 * z * j ∧
      halfLevel n cc (x + axisStep 1 ρ) = 2 * z * j := by
    change (∀ s ∈ Γ.linkEndpoints (Γ.linkClass (fwdLink x ρ)), Γ.HasHeight n z s c) ∨
      ∀ s ∈ Γ.linkEndpoints (Γ.linkClass (fwdLink x ρ)), Γ.HasHeight n z s (c + (z : ℝ)) at hd
    rw [forall_endpoints_fwdLink, forall_endpoints_fwdLink,
      hasHeight_iff D x level_base, hasHeight_iff D (x + axisStep 1 ρ) level_base,
      hasHeight_iff D x level_half_period,
      hasHeight_iff D (x + axisStep 1 ρ) level_half_period] at hd
    rcases hd with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
    · have h₃ := (h₁.trans h₂.symm).eq_of_close hz (by omega) (by omega)
      obtain ⟨j, hj⟩ := h₁.exists_mul (m := 0) (by simp)
      exact ⟨j, hj, h₃ ▸ hj⟩
    · have h₃ := (h₁.trans h₂.symm).eq_of_close hz (by omega) (by omega)
      obtain ⟨j, hj⟩ := h₁.exists_mul (m := 1) (by simp)
      exact ⟨j, hj, h₃ ▸ hj⟩
  obtain ⟨j, h₁, h₂⟩ := key
  rw [Γ.orientedOfLink_linkClass, hI.descendOrientedLink_orientedClass]
  have : (_root_.YangMills.Construction.NormalFamilies.NormalLevelPair.reflectSymmetry ⟨n, D.normal_mem, c, hc⟩).linkMap (fwdLink x ρ).1 =
      (fwdLink x ρ).1.shiftBy ((-j) • w) :=
    InfiniteLattice.Link.ext (reflect_pointMap_of_eq D hc x h₁) (reflect_pointMap_of_eq D hc _ h₂)
  rw [this, Γ.orientedClass_shiftBy _ (zsmul_mem D.period_mem _)]
end SharedAndCrossing
section SiteLevelCells
variable {Γ : PeriodSublattice 1} {n : AmbientSpace} {z : ℤ} {c : ℝ} {cc : ℤ} {w : LatticePoint 1}
theorem isLift_plaquetteShift (hr : SymmetryActionRules.Statement) (p : ElementaryPlaquette 1)
    {γ : LatticePoint 1} (hγ : γ ∈ Γ.periods) :
    Γ.IsLiftOfPlaquette (plaquetteShift p γ) (Γ.faceClass p) :=
  ⟨γ, hγ, (plaquetteMap_shift hr γ p).symm⟩
theorem liesInPlane_faceClass_iff (hr : SymmetryActionRules.Statement)
    {μ lam : Fin 4} (hlt : μ < lam) (p : ElementaryPlaquette 1) :
    Γ.PlaquetteLiesInPlane (Γ.faceClass p) μ lam ↔ p.lowAxis = μ ∧ p.highAxis = lam := by
  constructor
  · intro h
    have hs : plaquetteShift p 0 = p := by simp [plaquetteShift]
    have := h (plaquetteShift p 0) (isLift_plaquetteShift hr p (zero_mem _))
    rw [hs] at this
    rcases this with h | ⟨h₁, h₂⟩
    · exact h
    · have := p.lowAxis_lt_highAxis
      rw [h₁, h₂] at this
      exact absurd hlt this.asymm
  · rintro ⟨h₁, h₂⟩ p' ⟨γ, _, rfl⟩
    rw [plaquetteMap_shift hr]
    exact Or.inl ⟨h₁, h₂⟩
theorem halfLevel_of_mem_cornerSet (D : Setup Γ n z c cc w) (p : ElementaryPlaquette 1)
    {s : LatticePoint 1} (hs : s ∈ p.cornerSet) :
    halfLevel n cc s = halfLevel n cc p.corner ∨
      halfLevel n cc s = halfLevel n cc p.corner + 2 * entry n p.lowAxis ∨
      halfLevel n cc s =
        halfLevel n cc p.corner + 2 * entry n p.lowAxis + 2 * entry n p.highAxis ∨
      halfLevel n cc s = halfLevel n cc p.corner + 2 * entry n p.highAxis := by
  rcases hs with rfl | rfl | rfl | rfl
  · exact Or.inl rfl
  · exact Or.inr (Or.inl (halfLevel_add_axisStep D.normal_mem _ _ _))
  · refine Or.inr (Or.inr (Or.inl ?_))
    rw [halfLevel_add_axisStep D.normal_mem, halfLevel_add_axisStep D.normal_mem]
  · exact Or.inr (Or.inr (Or.inr (halfLevel_add_axisStep D.normal_mem _ _ _)))
theorem not_split_of_coord_zero (hr : SymmetryActionRules.Statement)
    (D : Setup Γ n z c cc w) (hcc : cc % 2 = 0) (p : ElementaryPlaquette 1)
    (h : entry n p.lowAxis = 0 ∨ entry n p.highAxis = 0) :
    ¬ Γ.IsSplitPlaquette n z c (Γ.faceClass p) := by
  rw [isSplit_iff hr D]
  rintro ⟨h₁, h₂⟩
  have hb := halfLevel_even (n := n) hcc p.corner
  have main : ∀ e : ℤ, (e = 0 ∨ e = 1 ∨ e = -1) →
      (∀ s ∈ p.cornerSet, halfLevel n cc s = halfLevel n cc p.corner ∨
        halfLevel n cc s = halfLevel n cc p.corner + 2 * e) → False := by
    intro e he hs
    rcases pair_one_side_even D.two_le hb e he with ⟨a, b⟩ | ⟨a, b⟩
    · exact h₁ fun s m => by rcases hs s m with h | h <;> rw [h] <;> assumption
    · exact h₂ fun s m => by rcases hs s m with h | h <;> rw [h] <;> assumption
  rcases h with h | h
  · refine main _ (entry_cases D.normal_mem p.highAxis) fun s m => ?_
    have := halfLevel_of_mem_cornerSet D p m
    rw [h] at this
    omega
  · refine main _ (entry_cases D.normal_mem p.lowAxis) fun s m => ?_
    have := halfLevel_of_mem_cornerSet D p m
    rw [h] at this
    omega
theorem diag_plane_corners (D : Setup Γ n z c cc w) {μ lam : Fin 4} (hlt : μ < lam)
    (hvec : n = coordVec μ - coordVec lam ∨ n = coordVec μ + coordVec lam)
    (p : ElementaryPlaquette 1) (h₁ : p.lowAxis = μ) (h₂ : p.highAxis = lam) :
    ∃ y y' zp zm : LatticePoint 1, p.cornerSet = {y, y', zp, zm} ∧ IsDiagonalCornerPair p y y' ∧
      halfLevel n cc y = halfLevel n cc p.corner + entry n p.lowAxis + entry n p.highAxis ∧
      halfLevel n cc y' = halfLevel n cc p.corner + entry n p.lowAxis + entry n p.highAxis ∧
      halfLevel n cc zp = halfLevel n cc p.corner + entry n p.lowAxis + entry n p.highAxis + 2 ∧
      halfLevel n cc zm = halfLevel n cc p.corner + entry n p.lowAxis + entry n p.highAxis - 2 := by
  have s₁ := halfLevel_add_axisStep D.normal_mem cc p.corner p.lowAxis
  have s₂ := halfLevel_add_axisStep D.normal_mem cc p.corner p.highAxis
  have s₃ := halfLevel_add_axisStep D.normal_mem cc (p.corner + axisStep 1 p.lowAxis) p.highAxis
  rcases hvec with hv | hv
  · have e₁ : entry n p.lowAxis = 1 := by rw [hv, entry_coordVec_sub hlt, h₁]; simp
    have e₂ : entry n p.highAxis = -1 := by rw [hv, entry_coordVec_sub hlt, h₂]; simp [hlt.ne']
    refine ⟨p.corner, p.corner + axisStep 1 p.lowAxis + axisStep 1 p.highAxis,
      p.corner + axisStep 1 p.lowAxis, p.corner + axisStep 1 p.highAxis, ?_, Or.inl ⟨rfl, rfl⟩,
      ?_, ?_, ?_, ?_⟩
    · ext s
      simp only [ElementaryPlaquette.cornerSet, Set.mem_insert_iff, Set.mem_singleton_iff]
      tauto
    all_goals omega
  · have e₁ : entry n p.lowAxis = 1 := by rw [hv, entry_coordVec_add hlt, h₁]; simp
    have e₂ : entry n p.highAxis = 1 := by rw [hv, entry_coordVec_add hlt, h₂]; simp [hlt.ne']
    refine ⟨p.corner + axisStep 1 p.lowAxis, p.corner + axisStep 1 p.highAxis,
      p.corner + axisStep 1 p.lowAxis + axisStep 1 p.highAxis, p.corner, ?_,
      Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩)), ?_, ?_, ?_, ?_⟩
    · ext s
      simp only [ElementaryPlaquette.cornerSet, Set.mem_insert_iff, Set.mem_singleton_iff]
      tauto
    all_goals omega
theorem entry_zero_of_not_plane {μ lam : Fin 4} (hlt : μ < lam)
    (hvec : n = coordVec μ - coordVec lam ∨ n = coordVec μ + coordVec lam)
    (p : ElementaryPlaquette 1) (hp : ¬ (p.lowAxis = μ ∧ p.highAxis = lam)) :
    entry n p.lowAxis = 0 ∨ entry n p.highAxis = 0 := by
  have hfs := p.lowAxis_lt_highAxis
  have key : (p.lowAxis ≠ μ ∧ p.lowAxis ≠ lam) ∨ (p.highAxis ≠ μ ∧ p.highAxis ≠ lam) := by
    by_contra hcon
    push Not at hcon
    obtain ⟨a, b⟩ := hcon
    by_cases h₁ : p.lowAxis = μ
    · have h₂ : p.highAxis = lam := by
        by_contra h₂
        have := b (fun h₃ => ?_)
        · exact h₂ this
        · rw [h₁, h₃] at hfs
          exact lt_irrefl _ hfs
      exact hp ⟨h₁, h₂⟩
    · have h₃ := a h₁
      by_cases h₂ : p.highAxis = μ
      · rw [h₃, h₂] at hfs
        exact absurd hlt hfs.asymm
      · have := b h₂
        rw [h₃, this] at hfs
        exact lt_irrefl _ hfs
  rcases hvec with rfl | rfl
  · rcases key with ⟨a, b⟩ | ⟨a, b⟩
    · left; rw [entry_coordVec_sub hlt]; simp [a, b]
    · right; rw [entry_coordVec_sub hlt]; simp [a, b]
  · rcases key with ⟨a, b⟩ | ⟨a, b⟩
    · left; rw [entry_coordVec_add hlt]; simp [a, b]
    · right; rw [entry_coordVec_add hlt]; simp [a, b]
theorem split_iff_middle (hr : SymmetryActionRules.Statement)
    (D : Setup Γ n z c cc w) (hcc : cc % 2 = 0) {p : ElementaryPlaquette 1}
    {y y' zp zm : LatticePoint 1} {m : ℤ}
    (hc : p.cornerSet = {y, y', zp, zm}) (h₁ : halfLevel n cc y = m)
    (h₂ : halfLevel n cc y' = m) (h₃ : halfLevel n cc zp = m + 2)
    (h₄ : halfLevel n cc zm = m - 2) :
    Γ.IsSplitPlaquette n z c (Γ.faceClass p) ↔ ModCong z m 0 ∨ ModCong z m (2 * z) := by
  have hm : m % 2 = 0 := h₁ ▸ halfLevel_even hcc y
  rw [isSplit_iff hr D, hc]
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, forall_eq_or_imp, forall_eq, h₁, h₂, h₃, h₄]
  constructor
  · rintro ⟨a, b⟩
    by_contra hn
    push Not at hn
    rcases triple_even D.two_le hm hn.1 hn.2 with ⟨u, v, t⟩ | ⟨u, v, t⟩
    · exact a ⟨u, u, v, t⟩
    · exact b ⟨u, u, v, t⟩
  · intro h
    obtain ⟨a, b⟩ := adjacent_at_level D.two_le h
    exact ⟨fun ⟨_, _, u, v⟩ => a ⟨u, v⟩, fun ⟨_, _, u, v⟩ => b ⟨u, v⟩⟩
theorem quotientMap_ne_of_cornerSet (hr : SymmetryActionRules.Statement)
    (hF : TorusQuotientIsFaithful.Statement) {p : ElementaryPlaquette 1}
    {y y' zp zm : LatticePoint 1}
    (hc : p.cornerSet = {y, y', zp, zm}) : Γ.quotientMap y ≠ Γ.quotientMap y' := by
  intro h
  have h₄ := ((hF Γ).2.2 (Γ.faceClass p)).1
  rw [plaquetteVertices_faceClass hr, hc, Set.image_insert_eq, Set.image_insert_eq, h,
    Set.insert_idem] at h₄
  have h₅ := Set.ncard_insert_le (Γ.quotientMap y') (Γ.quotientMap '' {zp, zm})
  have h₆ : (Γ.quotientMap '' {zp, zm}).ncard ≤ 2 := by
    rw [Set.image_pair]
    exact (Set.ncard_insert_le _ _).trans (by simp)
  omega
theorem hasTwoVertices_iff (hr : SymmetryActionRules.Statement)
    (hF : TorusQuotientIsFaithful.Statement)
    (D : Setup Γ n z c cc w) {p : ElementaryPlaquette 1} {y y' zp zm : LatticePoint 1} {m V : ℤ}
    {u : ℝ}
    (hc : p.cornerSet = {y, y', zp, zm}) (h₁ : halfLevel n cc y = m)
    (h₂ : halfLevel n cc y' = m) (h₃ : halfLevel n cc zp = m + 2)
    (h₄ : halfLevel n cc zm = m - 2) (hu : u = c + (V : ℝ) / 2) :
    Γ.HasTwoVerticesAtHeight n z (Γ.faceClass p) u ↔ ModCong z m V := by
  have hz := D.two_le
  rw [PeriodSublattice.HasTwoVerticesAtHeight, plaquetteVertices_faceClass hr, hc]
  constructor
  · rintro ⟨_, ⟨a, ha, rfl⟩, _, ⟨b, hb, rfl⟩, hne, ha', hb'⟩
    rw [hasHeight_iff D _ hu] at ha' hb'
    have far : ¬ ModCong z (m + 2) (m - 2) := fun h => by
      have := h.eq_of_close hz (by omega) (by omega)
      omega
    rcases ha with rfl | rfl | rfl | ha
    · rwa [h₁] at ha'
    · rwa [h₂] at ha'
    · rw [h₃] at ha'
      rcases hb with rfl | rfl | rfl | hb
      · rwa [h₁] at hb'
      · rwa [h₂] at hb'
      · exact absurd rfl hne
      · rw [Set.mem_singleton_iff.1 hb, h₄] at hb'
        exact absurd (ha'.trans hb'.symm) far
    · rw [Set.mem_singleton_iff.1 ha, h₄] at ha'
      rcases hb with rfl | rfl | rfl | hb
      · rwa [h₁] at hb'
      · rwa [h₂] at hb'
      · rw [h₃] at hb'
        exact absurd (hb'.trans ha'.symm) far
      · exact absurd (by rw [Set.mem_singleton_iff.1 ha, Set.mem_singleton_iff.1 hb]) hne
  · intro h
    exact ⟨_, ⟨y, by simp, rfl⟩, _, ⟨y', by simp, rfl⟩, quotientMap_ne_of_cornerSet hr hF hc,
      (hasHeight_iff D _ hu).2 (h₁ ▸ h), (hasHeight_iff D _ hu).2 (h₂ ▸ h)⟩
theorem split_iff_at_site_level (hr : SymmetryActionRules.Statement)
    (hF : TorusQuotientIsFaithful.Statement)
    (D : Setup Γ n z c cc w) (hcc : cc % 2 = 0) {μ lam : Fin 4} (hlt : μ < lam)
    (hvec : n = coordVec μ - coordVec lam ∨ n = coordVec μ + coordVec lam)
    (q : Γ.QuotientPlaquette) :
    Γ.IsSplitPlaquette n z c q ↔ Γ.PlaquetteLiesInPlane q μ lam ∧
      (Γ.HasTwoVerticesAtHeight n z q c ∨ Γ.HasTwoVerticesAtHeight n z q (c + (z : ℝ))) := by
  obtain ⟨p, rfl⟩ := faceClass_surjective Γ q
  rw [liesInPlane_faceClass_iff hr hlt]
  by_cases hp : p.lowAxis = μ ∧ p.highAxis = lam
  · obtain ⟨y, y', zp, zm, hc, -, h₁, h₂, h₃, h₄⟩ := diag_plane_corners D hlt hvec p hp.1 hp.2
    rw [split_iff_middle hr D hcc hc h₁ h₂ h₃ h₄,
      hasTwoVertices_iff hr hF D hc h₁ h₂ h₃ h₄ level_base,
      hasTwoVertices_iff hr hF D hc h₁ h₂ h₃ h₄ level_half_period]
    simp [hp]
  · have := not_split_of_coord_zero hr D hcc p (entry_zero_of_not_plane hlt hvec p hp)
    simp [this, hp]
theorem linearHeight_of_halfLevel (D : Setup Γ n z c cc w) {Q : NormalLevelPair 1}
    (hv : Q.normal = n) {V : ℤ} (hQ : Q.level = c + (V : ℝ) / 2) {x : LatticePoint 1}
    (h : halfLevel n cc x = V) :
    linearHeight Q.normal (x : LatticePoint 1) = Q.level := by
  rw [hv, linearHeight, dotProduct_eq_halfLevel D.normal_mem D.half_eq x, h, hQ]
theorem exists_diag_lift (hr : SymmetryActionRules.Statement)
    (hF : TorusQuotientIsFaithful.Statement)
    (hm : _root_.YangMills.Construction.NormalFamilies.CutPlaquettesOfMirror)
    (D : Setup Γ n z c cc w) {μ lam : Fin 4} (hlt : μ < lam)
    (hvec : n = coordVec μ - coordVec lam ∨ n = coordVec μ + coordVec lam)
    {Q : NormalLevelPair 1} (hv : Q.normal = n) {V : ℤ} (hQ : Q.level = c + (V : ℝ) / 2)
    (hint : ∃ k : ℤ, Q.level = (k : ℝ)) (q : Γ.QuotientPlaquette)
    (hq : Γ.PlaquetteLiesInPlane q μ lam) (h2 : Γ.HasTwoVerticesAtHeight n z q Q.level) :
    ∃ (p : ElementaryPlaquette 1) (y y' : LatticePoint 1), Γ.IsLiftOfPlaquette p q ∧
      IsCutThroughDiagonalBy Q μ lam p y y' := by
  obtain ⟨p, rfl⟩ := faceClass_surjective Γ q
  obtain ⟨hp₁, hp₂⟩ := (liesInPlane_faceClass_iff hr hlt p).1 hq
  obtain ⟨y, y', zp, zm, hc, -, h₁, h₂, h₃, h₄⟩ := diag_plane_corners D hlt hvec p hp₁ hp₂
  obtain ⟨k, hk⟩ := (hasTwoVertices_iff hr hF D hc h₁ h₂ h₃ h₄ hQ).1 h2
  obtain ⟨a, a', bp, bm, -, ho, g₁, g₂, -, -⟩ :=
    diag_plane_corners D hlt hvec (plaquetteShift p (k • w)) hp₁ hp₂
  have hV : halfLevel n cc (plaquetteShift p (k • w)).corner +
      entry n (plaquetteShift p (k • w)).lowAxis + entry n (plaquetteShift p (k • w)).highAxis = V := by
    change halfLevel n cc (p.corner + k • w) + entry n p.lowAxis + entry n p.highAxis = V
    rw [halfLevel_add_zsmul D]
    omega
  rw [hV] at g₁ g₂
  have e₁ := linearHeight_of_halfLevel D hv hQ g₁
  have e₂ := linearHeight_of_halfLevel D hv hQ g₂
  have hpl : (plaquetteShift p (k • w)).LiesInPlane μ lam := Or.inl ⟨hp₁, hp₂⟩
  have hcut := (hm Q).2.1 μ lam hlt (hv ▸ hvec) hint (plaquetteShift p (k • w))
  exact ⟨plaquetteShift p (k • w), a, a', isLift_plaquetteShift hr p (zsmul_mem D.period_mem k),
    hpl, ho, e₁, e₂, hcut.1.2 ⟨hpl, a, a', ho, e₁, e₂⟩, hcut.2 a a' hpl ho e₁ e₂⟩
end SiteLevelCells
section LinkLevel
variable {Γ : PeriodSublattice 1} {n : AmbientSpace} {z : ℤ} {c : ℝ} {cc : ℤ} {w : LatticePoint 1}
theorem ModCong.add_right {W V : ℤ} (h : ModCong z W V) (t : ℤ) : ModCong z (W + t) (V + t) := by
  obtain ⟨k, rfl⟩ := h
  exact ⟨k, by ring⟩
theorem dualVector_coordVec (μ : Fin 4) :
    dualVector (coordVec μ) = ((axisStep 1 μ : LatticePoint 1) : AmbientSpace) := by apply _root_.YangMills.Construction.InfiniteLattice.InvariantGibbsPeriodicBounds.dual_standardFrame <;> assumption
theorem reflect_pointMap_axial (D : Setup Γ n z c cc w) (hc : _root_.YangMills.Construction.NormalFamilies.IsAllowedLevel 1 n c) {μ : Fin 4}
    (hμ : n = coordVec μ) (s : LatticePoint 1) {ε m : ℤ}
    (h : halfLevel n cc s = ε + 2 * z * m) :
    (_root_.YangMills.Construction.NormalFamilies.NormalLevelPair.reflectSymmetry ⟨n, D.normal_mem, c, hc⟩).pointMap s =
      s + (-ε) • axisStep 1 μ + (-m) • w := by
  refine Subtype.ext ?_
  rw [reflect_pointMap_coe D hc, h, AddSubgroup.coe_add, AddSubgroup.coe_add,
    AddSubgroup.coe_zsmul, AddSubgroup.coe_zsmul, ← Int.cast_smul_eq_zsmul ℝ,
    ← Int.cast_smul_eq_zsmul ℝ, D.period_eq, smul_smul, ← dualVector_coordVec, ← hμ]
  push_cast
  rw [add_smul, add_assoc, sub_eq_add_neg, neg_add, ← neg_smul, ← neg_smul]
  congr 3
  ring
theorem sharedLinks_empty (D : Setup Γ n z c cc w) (hcc : cc % 2 = 1) :
    Γ.sharedLinks n z c = ∅ := by
  refine Set.eq_empty_of_forall_notMem fun d hd => ?_
  rw [sharedLinks_eq D] at hd
  obtain ⟨b, rfl⟩ := linkClass_surjective Γ d
  obtain ⟨x, ρ, rfl⟩ := exists_eq_fwdLink b
  change (∀ s ∈ Γ.linkEndpoints (Γ.linkClass (fwdLink x ρ)), Γ.HasHeight n z s c) ∨
    ∀ s ∈ Γ.linkEndpoints (Γ.linkClass (fwdLink x ρ)), Γ.HasHeight n z s (c + (z : ℝ)) at hd
  rw [forall_endpoints_fwdLink, forall_endpoints_fwdLink, hasHeight_iff D x level_base,
    hasHeight_iff D x level_half_period] at hd
  have hodd := halfLevel_odd (n := n) hcc x
  rcases hd with ⟨h, -⟩ | ⟨h, -⟩
  · have := h.emod_two_eq
    omega
  · have := h.emod_two_eq
    omega
theorem level_link_low : c - 1 / 2 = c + ((-1 : ℤ) : ℝ) / 2 := by
  push_cast
  ring
theorem level_link_high : c + (z : ℝ) - 1 / 2 = c + ((2 * z - 1 : ℤ) : ℝ) / 2 := by
  push_cast
  ring
theorem axisStep_injective {μ ρ : Fin 4} (h : axisStep 1 μ = axisStep 1 ρ) : μ = ρ := by
  by_contra hne
  have := congrFun (congrArg Subtype.val h) μ
  simp [axisStep, hne] at this
theorem crossingLinks_eq (D : Setup Γ n z c cc w) (hcc : cc % 2 = 1) {μ : Fin 4}
    (hμ : n = coordVec μ) :
    Γ.crossingLinks n z c =
      {b | ∃ x : LatticePoint 1,
        (Γ.HasHeight n z (Γ.quotientMap x) (c - 1 / 2) ∨
          Γ.HasHeight n z (Γ.quotientMap x) (c + (z : ℝ) - 1 / 2)) ∧
        Γ.orientedOfLink b = Γ.orientedClass (Link.forwardFrom x μ)} := by
  have hz := D.two_le
  ext d
  obtain ⟨b, rfl⟩ := linkClass_surjective Γ d
  obtain ⟨x, ρ, rfl⟩ := exists_eq_fwdLink b
  have e := halfLevel_add_axisStep D.normal_mem cc x ρ
  have hodd := halfLevel_odd (n := n) hcc x
  have hup := linkClass_mem_plusLinks_iff D (fwdLink x ρ)
  have hlo := linkClass_mem_minusLinks_iff D (fwdLink x ρ)
  have hor : Γ.orientedOfLink (Γ.linkClass (fwdLink x ρ)) =
      Γ.orientedClass (Link.forwardFrom x ρ) :=
    Γ.orientedOfLink_linkClass _
  change halfLevel n cc (x + axisStep 1 ρ) = _ at e
  change _ ↔ UpperHalfRes z (halfLevel n cc x) ∧
    UpperHalfRes z (halfLevel n cc (x + axisStep 1 ρ)) at hup
  change _ ↔ LowerHalfRes z (halfLevel n cc x) ∧
    LowerHalfRes z (halfLevel n cc (x + axisStep 1 ρ)) at hlo
  change (¬ (_ ∨ _)) ↔ ∃ x' : LatticePoint 1, _ ∧ Γ.orientedOfLink (Γ.linkClass (fwdLink x ρ)) = _
  rw [hor]
  by_cases hρ : ρ = μ
  · subst hρ
    have e₁ : entry n ρ = 1 := by rw [hμ, entry_coordVec]; simp
    rw [e₁, mul_one] at e
    rw [e] at hup hlo
    have nb := adjacent_odd_iff hz hodd
    rw [hup, hlo, nb, not_not]
    constructor
    · intro h
      refine ⟨x, ?_, rfl⟩
      rwa [hasHeight_iff D x level_link_low, hasHeight_iff D x level_link_high]
    · rintro ⟨x', h, hb⟩
      obtain ⟨γ, hγ, hb'⟩ := Γ.mem_orientedOrbit_of_orientedClass_eq hb
      have : x' = x + γ := congrArg Link.initial hb'
      rw [this, Γ.quotientMap_add_period x hγ, hasHeight_iff D x level_link_low,
        hasHeight_iff D x level_link_high] at h
      exact h
  · have e₀ : entry n ρ = 0 := by rw [hμ, entry_coordVec]; simp [hρ]
    rw [e₀, mul_zero, add_zero] at e
    rw [e] at hup hlo
    constructor
    · intro h
      exfalso
      refine h ?_
      rcases upper_or_lower hz (halfLevel n cc x) with u | u
      · exact Or.inl (hup.2 ⟨u, u⟩)
      · exact Or.inr (hlo.2 ⟨u, u⟩)
    · rintro ⟨x', -, hb⟩
      exfalso
      obtain ⟨γ, hγ, hb'⟩ := Γ.mem_orientedOrbit_of_orientedClass_eq hb
      have h₁ : x' = x + γ := congrArg Link.initial hb'
      have h₂ : x' + axisStep 1 μ = x + axisStep 1 ρ + γ := congrArg Link.terminal hb'
      rw [h₁, add_right_comm] at h₂
      exact hρ (axisStep_injective (add_left_cancel (add_right_cancel h₂))).symm
theorem crossing_opposite (D : Setup Γ n z c cc w) (hc : _root_.YangMills.Construction.NormalFamilies.IsAllowedLevel 1 n c) (hcc : cc % 2 = 1)
    {μ : Fin 4} (hμ : n = coordVec μ)
    (hI : Γ.DescendsToQuotient (_root_.YangMills.Construction.NormalFamilies.NormalLevelPair.reflectSymmetry ⟨n, D.normal_mem, c, hc⟩)) :
    ∀ b ∈ Γ.crossingLinks n z c,
      Γ.descendOrientedLink (_root_.YangMills.Construction.NormalFamilies.NormalLevelPair.reflectSymmetry ⟨n, D.normal_mem, c, hc⟩)
        (Γ.orientedOfLink b) = Γ.oppositeOriented (Γ.orientedOfLink b) := by
  intro d hd
  rw [crossingLinks_eq D hcc hμ] at hd
  obtain ⟨x, hat, hb⟩ := hd
  rw [hasHeight_iff D x level_link_low, hasHeight_iff D x level_link_high] at hat
  have key : ∃ m : ℤ, halfLevel n cc x = -1 + 2 * z * m := by
    rcases hat with h | h
    · obtain ⟨k, hk⟩ := h
      exact ⟨-(2 * k), by linear_combination -hk⟩
    · obtain ⟨k, hk⟩ := h
      exact ⟨1 - 2 * k, by linear_combination -hk⟩
  obtain ⟨m, hm⟩ := key
  have e : halfLevel n cc (x + axisStep 1 μ) = 1 + 2 * z * m := by
    rw [halfLevel_add_axisStep D.normal_mem, hm, hμ, entry_coordVec]
    simp
    ring
  rw [hb, hI.descendOrientedLink_orientedClass, Γ.oppositeOriented_orientedClass]
  have : (_root_.YangMills.Construction.NormalFamilies.NormalLevelPair.reflectSymmetry ⟨n, D.normal_mem, c, hc⟩).linkMap (Link.forwardFrom x μ) =
      (Link.forwardFrom x μ).opposite.shiftBy ((-m) • w) := by
    refine InfiniteLattice.Link.ext ?_ ?_
    · change (_root_.YangMills.Construction.NormalFamilies.NormalLevelPair.reflectSymmetry ⟨n, D.normal_mem, c, hc⟩).pointMap x =
        x + axisStep 1 μ + (-m) • w
      rw [reflect_pointMap_axial D hc hμ x hm]
      simp
    · change (_root_.YangMills.Construction.NormalFamilies.NormalLevelPair.reflectSymmetry ⟨n, D.normal_mem, c, hc⟩).pointMap (x + axisStep 1 μ) =
        x + (-m) • w
      rw [reflect_pointMap_axial D hc hμ _ e]
      simp
  rw [this, Γ.orientedClass_shiftBy _ (zsmul_mem D.period_mem _)]
theorem hasVertexHeightsAround_iff (hr : SymmetryActionRules.Statement)
    (D : Setup Γ n z c cc w) (p : ElementaryPlaquette 1) {u : ℝ} {V : ℤ}
    (hu : u = c + (V : ℝ) / 2) :
    Γ.HasVertexHeightsAround n z (Γ.faceClass p) u ↔
      (∀ s ∈ p.cornerSet, ModCong z (halfLevel n cc s) (V - 1) ∨
          ModCong z (halfLevel n cc s) (V + 1)) ∧
      (∃ s ∈ p.cornerSet, ModCong z (halfLevel n cc s) (V - 1)) ∧
      ∃ s ∈ p.cornerSet, ModCong z (halfLevel n cc s) (V + 1) := by
  have h₁ : u - 1 / 2 = c + ((V - 1 : ℤ) : ℝ) / 2 := by
    rw [hu]
    push_cast
    ring
  have h₂ : u + 1 / 2 = c + ((V + 1 : ℤ) : ℝ) / 2 := by
    rw [hu]
    push_cast
    ring
  rw [PeriodSublattice.HasVertexHeightsAround, plaquetteVertices_faceClass hr]
  simp only [Set.forall_mem_image, Set.exists_mem_image, hasHeight_iff D _ h₁,
    hasHeight_iff D _ h₂]
theorem axial_plaquette_cases (D : Setup Γ n z c cc w) {μ : Fin 4} (hμ : n = coordVec μ)
    (p : ElementaryPlaquette 1) :
    (∀ s ∈ p.cornerSet, halfLevel n cc s = halfLevel n cc p.corner) ∨
      ∃ lam : Fin 4, lam ≠ μ ∧ HasCornerSquare p p.corner μ lam := by
  by_cases h₁ : p.lowAxis = μ
  · refine Or.inr ⟨p.highAxis, fun h => ?_, ?_⟩
    · have := p.lowAxis_lt_highAxis
      rw [h₁, h] at this
      exact lt_irrefl _ this
    · rw [HasCornerSquare, ← h₁]
      rfl
  · by_cases h₂ : p.highAxis = μ
    · refine Or.inr ⟨p.lowAxis, h₁, ?_⟩
      rw [HasCornerSquare, ← h₂]
      ext s
      simp only [NormalFamilies.plaquetteCorners, Set.mem_insert_iff, Set.mem_singleton_iff,
        add_right_comm p.corner (axisStep 1 p.lowAxis) (axisStep 1 p.highAxis)]
      tauto
    · left
      intro s hs
      have e₁ : entry n p.lowAxis = 0 := by rw [hμ, entry_coordVec]; simp [h₁]
      have e₂ : entry n p.highAxis = 0 := by rw [hμ, entry_coordVec]; simp [h₂]
      have := halfLevel_of_mem_cornerSet D p hs
      rw [e₁, e₂] at this
      omega
theorem cornerSet_of_square (D : Setup Γ n z c cc w) {μ lam : Fin 4} (hμ : n = coordVec μ)
    (hne : lam ≠ μ) {p : ElementaryPlaquette 1} {x : LatticePoint 1}
    (h : HasCornerSquare p x μ lam) :
    p.cornerSet = {x, x + axisStep 1 μ, x + axisStep 1 μ + axisStep 1 lam, x + axisStep 1 lam} ∧
      halfLevel n cc (x + axisStep 1 μ) = halfLevel n cc x + 2 ∧
      halfLevel n cc (x + axisStep 1 μ + axisStep 1 lam) = halfLevel n cc x + 2 ∧
      halfLevel n cc (x + axisStep 1 lam) = halfLevel n cc x := by
  have e₁ : entry n μ = 1 := by rw [hμ, entry_coordVec]; simp
  have e₂ : entry n lam = 0 := by rw [hμ, entry_coordVec]; simp [hne]
  refine ⟨h, ?_, ?_, ?_⟩
  · rw [halfLevel_add_axisStep D.normal_mem, e₁]
    ring
  · rw [halfLevel_add_axisStep D.normal_mem, halfLevel_add_axisStep D.normal_mem, e₁, e₂]
    ring
  · rw [halfLevel_add_axisStep D.normal_mem, e₂]
    ring
theorem split_iff_square (hr : SymmetryActionRules.Statement)
    (D : Setup Γ n z c cc w) (hcc : cc % 2 = 1) {μ lam : Fin 4} (hμ : n = coordVec μ)
    (hne : lam ≠ μ) {p : ElementaryPlaquette 1} {x : LatticePoint 1}
    (h : HasCornerSquare p x μ lam) :
    Γ.IsSplitPlaquette n z c (Γ.faceClass p) ↔
      ModCong z (halfLevel n cc x) (-1) ∨ ModCong z (halfLevel n cc x) (2 * z - 1) := by
  obtain ⟨hc, e₁, e₂, e₃⟩ := cornerSet_of_square D hμ hne h
  have nb := adjacent_odd_iff D.two_le (halfLevel_odd (n := n) hcc x)
  rw [isSplit_iff hr D, hc]
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, forall_eq_or_imp, forall_eq, e₁, e₂, e₃]
  tauto
theorem hasVertexHeightsAround_square_iff (hr : SymmetryActionRules.Statement)
    (D : Setup Γ n z c cc w) {μ lam : Fin 4} (hμ : n = coordVec μ)
    (hne : lam ≠ μ) {p : ElementaryPlaquette 1} {x : LatticePoint 1}
    (h : HasCornerSquare p x μ lam) {u : ℝ} {V : ℤ} (hu : u = c + (V : ℝ) / 2) :
    Γ.HasVertexHeightsAround n z (Γ.faceClass p) u ↔ ModCong z (halfLevel n cc x) (V - 1) := by
  obtain ⟨hc, e₁, e₂, e₃⟩ := cornerSet_of_square D hμ hne h
  have hz := D.two_le
  rw [hasVertexHeightsAround_iff hr D p hu, hc]
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, forall_eq_or_imp, forall_eq, e₁, e₂, e₃,
    exists_eq_or_imp, exists_eq_left]
  constructor
  · rintro ⟨⟨a | a, -⟩, b, -⟩
    · exact a
    · have far : ¬ ModCong z (halfLevel n cc x + 2) (V - 1) := fun b' => by
        have := (b'.symm.trans (a.add_right 2)).eq_of_close hz (by omega) (by omega)
        omega
      rcases b with b | b | b | b
      · exact b
      · exact absurd b far
      · exact absurd b far
      · exact b
  · intro h'
    have h₂ : ModCong z (halfLevel n cc x + 2) (V + 1) := by
      have := h'.add_right 2
      rwa [show V - 1 + 2 = V + 1 by ring] at this
    exact ⟨⟨Or.inl h', Or.inr h₂, Or.inr h₂, Or.inl h'⟩, Or.inl h',
      Or.inr (Or.inl h₂)⟩
theorem not_hasVertexHeightsAround_of_flat (hr : SymmetryActionRules.Statement)
    (D : Setup Γ n z c cc w) {p : ElementaryPlaquette 1}
    (h : ∀ s ∈ p.cornerSet, halfLevel n cc s = halfLevel n cc p.corner)
    {u : ℝ} {V : ℤ} (hu : u = c + (V : ℝ) / 2) :
    ¬ Γ.HasVertexHeightsAround n z (Γ.faceClass p) u := by
  rw [hasVertexHeightsAround_iff hr D p hu]
  rintro ⟨-, ⟨s, hs, a⟩, s', hs', b⟩
  rw [h s hs] at a
  rw [h s' hs'] at b
  have := (a.symm.trans b).eq_of_close D.two_le (by have := D.two_le; omega)
    (by have := D.two_le; omega)
  omega
theorem not_split_of_flat (hr : SymmetryActionRules.Statement)
    (D : Setup Γ n z c cc w) {p : ElementaryPlaquette 1}
    (h : ∀ s ∈ p.cornerSet, halfLevel n cc s = halfLevel n cc p.corner) :
    ¬ Γ.IsSplitPlaquette n z c (Γ.faceClass p) := by
  rw [isSplit_iff hr D]
  rintro ⟨h₁, h₂⟩
  rcases upper_or_lower D.two_le (halfLevel n cc p.corner) with u | u
  · exact h₁ fun s hs => by rw [h s hs]; exact u
  · exact h₂ fun s hs => by rw [h s hs]; exact u
theorem split_iff_at_link_level (hr : SymmetryActionRules.Statement)
    (D : Setup Γ n z c cc w) (hcc : cc % 2 = 1) {μ : Fin 4} (hμ : n = coordVec μ)
    (q : Γ.QuotientPlaquette) :
    Γ.IsSplitPlaquette n z c q ↔
      Γ.HasVertexHeightsAround n z q c ∨ Γ.HasVertexHeightsAround n z q (c + (z : ℝ)) := by
  obtain ⟨p, rfl⟩ := faceClass_surjective Γ q
  rcases axial_plaquette_cases D hμ p with h | ⟨lam, hne, h⟩
  · simp [not_split_of_flat hr D h, not_hasVertexHeightsAround_of_flat hr D h level_base,
      not_hasVertexHeightsAround_of_flat hr D h level_half_period]
  · rw [split_iff_square hr D hcc hμ hne h,
      hasVertexHeightsAround_square_iff hr D hμ hne h level_base,
      hasVertexHeightsAround_square_iff hr D hμ hne h level_half_period]
    simp
theorem hasCornerSquare_plaquetteShift {p : ElementaryPlaquette 1} {x : LatticePoint 1}
    {μ lam : Fin 4} (h : HasCornerSquare p x μ lam) (γ : LatticePoint 1) :
    HasCornerSquare (plaquetteShift p γ) (x + γ) μ lam := by
  change (plaquetteShift p γ).cornerSet = _
  rw [cornerSet_plaquetteShift]
  have h' : p.cornerSet =
      {x, x + axisStep 1 μ, x + axisStep 1 μ + axisStep 1 lam, x + axisStep 1 lam} := h
  rw [h']
  simp only [Set.image_insert_eq, Set.image_singleton, add_right_comm]
theorem exists_axial_lift (hr : SymmetryActionRules.Statement)
    (hm : _root_.YangMills.Construction.NormalFamilies.CutPlaquettesOfMirror)
    (D : Setup Γ n z c cc w) {μ : Fin 4} (hμ : n = coordVec μ)
    {Q : NormalLevelPair 1} (hv : Q.normal = n) {V : ℤ} (hQ : Q.level = c + (V : ℝ) / 2)
    (hint : ∃ k : ℤ, Q.level = (k : ℝ) + 1 / 2) (q : Γ.QuotientPlaquette)
    (h2 : Γ.HasVertexHeightsAround n z q Q.level) :
    ∃ (p : ElementaryPlaquette 1) (x : LatticePoint 1) (lam : Fin 4), Γ.IsLiftOfPlaquette p q ∧
      IsCutAlongLinksBy Q μ lam p x := by
  obtain ⟨p, rfl⟩ := faceClass_surjective Γ q
  rcases axial_plaquette_cases D hμ p with h | ⟨lam, hne, h⟩
  · exact absurd h2 (not_hasVertexHeightsAround_of_flat hr D h hQ)
  · obtain ⟨k, hk⟩ := (hasVertexHeightsAround_square_iff hr D hμ hne h hQ).1 h2
    have hx : halfLevel n cc (p.corner + k • w) = V - 1 := by
      rw [halfLevel_add_zsmul D]
      omega
    have hh : linearHeight Q.normal ((p.corner + k • w : LatticePoint 1) : LatticePoint 1) =
        Q.level - 1 / 2 := by
      rw [hv, linearHeight, dotProduct_eq_halfLevel D.normal_mem D.half_eq, hx, hQ]
      push_cast
      ring
    have h' := hasCornerSquare_plaquetteShift h (k • w)
    have hcut := (hm Q).2.2 μ (hv.trans hμ) hint (plaquetteShift p (k • w))
    exact ⟨plaquetteShift p (k • w), p.corner + k • w, lam,
      isLift_plaquetteShift hr p (zsmul_mem D.period_mem k), hne, h',
      hh, hcut.1.2 ⟨_, lam, hne, h', hh⟩⟩
end LinkLevel
section ReflectionOfHalves
variable {Γ : PeriodSublattice 1} {n : AmbientSpace} {z : ℤ} {c : ℝ} {cc : ℤ} {w : LatticePoint 1}
theorem halfLevel_reflect (D : Setup Γ n z c cc w) (hc : _root_.YangMills.Construction.NormalFamilies.IsAllowedLevel 1 n c)
    (x : LatticePoint 1) :
    halfLevel n cc ((_root_.YangMills.Construction.NormalFamilies.NormalLevelPair.reflectSymmetry ⟨n, D.normal_mem, c, hc⟩).pointMap x) =
      -halfLevel n cc x := by
  have h₁ := dotProduct_eq_halfLevel D.normal_mem D.half_eq
    ((_root_.YangMills.Construction.NormalFamilies.NormalLevelPair.reflectSymmetry ⟨n, D.normal_mem, c, hc⟩).pointMap x)
  rw [reflect_pointMap_coe D hc, dotProduct_sub, dotProduct_smul,
    dotProduct_dualVector D.normal_mem, dotProduct_eq_halfLevel D.normal_mem D.half_eq x] at h₁
  simp only [smul_eq_mul, mul_one] at h₁
  have : (halfLevel n cc ((_root_.YangMills.Construction.NormalFamilies.NormalLevelPair.reflectSymmetry ⟨n, D.normal_mem, c, hc⟩).pointMap x) : ℝ) =
      -(halfLevel n cc x : ℝ) := by linarith
  exact_mod_cast this
theorem reflect_pointMap_involutive (D : Setup Γ n z c cc w) (hc : _root_.YangMills.Construction.NormalFamilies.IsAllowedLevel 1 n c)
    (x : LatticePoint 1) :
    (_root_.YangMills.Construction.NormalFamilies.NormalLevelPair.reflectSymmetry ⟨n, D.normal_mem, c, hc⟩).pointMap
      ((_root_.YangMills.Construction.NormalFamilies.NormalLevelPair.reflectSymmetry ⟨n, D.normal_mem, c, hc⟩).pointMap x) = x := by
  refine Subtype.ext ?_
  rw [reflect_pointMap_coe D hc, halfLevel_reflect D hc, reflect_pointMap_coe D hc]
  push_cast
  rw [neg_smul, sub_neg_eq_add, sub_add_cancel]
theorem quotientMap_surjective (Γ : PeriodSublattice 1) : Function.Surjective Γ.quotientMap :=
  QuotientAddGroup.mk'_surjective Γ.periods
theorem orientedClass_surjective (Γ : PeriodSublattice 1) :
    Function.Surjective Γ.orientedClass :=
  fun d => ⟨_, Γ.orientedClass_orientedRep d⟩
variable (D : Setup Γ n z c cc w) (hc : _root_.YangMills.Construction.NormalFamilies.IsAllowedLevel 1 n c)
  (hI : Γ.DescendsToQuotient (_root_.YangMills.Construction.NormalFamilies.NormalLevelPair.reflectSymmetry ⟨n, D.normal_mem, c, hc⟩))
include hI
theorem image_plusHalf :
    Γ.descendPoint (_root_.YangMills.Construction.NormalFamilies.NormalLevelPair.reflectSymmetry ⟨n, D.normal_mem, c, hc⟩) '' Γ.plusHalf n z c =
      Γ.minusHalf n z c := by
  ext t
  constructor
  · rintro ⟨s, hs, rfl⟩
    obtain ⟨x, rfl⟩ := quotientMap_surjective Γ s
    rw [hI.descendPoint_quotientMap, mem_minusHalf_iff D, halfLevel_reflect D hc]
    exact ((mem_plusHalf_iff D x).1 hs).neg
  · intro ht
    obtain ⟨y, rfl⟩ := quotientMap_surjective Γ t
    refine ⟨Γ.quotientMap ((_root_.YangMills.Construction.NormalFamilies.NormalLevelPair.reflectSymmetry ⟨n, D.normal_mem, c, hc⟩).pointMap y),
      ?_, ?_⟩
    · rw [mem_plusHalf_iff D, halfLevel_reflect D hc]
      exact ((mem_minusHalf_iff D y).1 ht).neg
    · rw [hI.descendPoint_quotientMap, reflect_pointMap_involutive D hc]
theorem image_minusHalf :
    Γ.descendPoint (_root_.YangMills.Construction.NormalFamilies.NormalLevelPair.reflectSymmetry ⟨n, D.normal_mem, c, hc⟩) '' Γ.minusHalf n z c =
      Γ.plusHalf n z c := by
  ext t
  constructor
  · rintro ⟨s, hs, rfl⟩
    obtain ⟨x, rfl⟩ := quotientMap_surjective Γ s
    rw [hI.descendPoint_quotientMap, mem_plusHalf_iff D, halfLevel_reflect D hc]
    exact ((mem_minusHalf_iff D x).1 hs).neg
  · intro ht
    obtain ⟨y, rfl⟩ := quotientMap_surjective Γ t
    refine ⟨Γ.quotientMap ((_root_.YangMills.Construction.NormalFamilies.NormalLevelPair.reflectSymmetry ⟨n, D.normal_mem, c, hc⟩).pointMap y),
      ?_, ?_⟩
    · rw [mem_minusHalf_iff D, halfLevel_reflect D hc]
      exact ((mem_plusHalf_iff D y).1 ht).neg
    · rw [hI.descendPoint_quotientMap, reflect_pointMap_involutive D hc]
omit hI in
theorem orientedOfLink_linkImage (r : LatticeSymmetry 1) (d : Γ.QuotientLink) :
    Γ.orientedOfLink (Γ.linkImage r d) = Γ.descendOrientedLink r (Γ.orientedOfLink d) ∨
      Γ.orientedOfLink (Γ.linkImage r d) =
        Γ.oppositeOriented (Γ.descendOrientedLink r (Γ.orientedOfLink d)) := by
  unfold PeriodSublattice.linkImage
  split_ifs with h
  · left
    rw [Γ.orientedOfLink_linkClass]
    exact Γ.orientedClass_orientedRep _
  · right
    rw [Γ.orientedOfLink_linkClass]
    rfl
omit hI in
theorem endpoints_oppositeOriented (e : Γ.OrientedLink) :
    Γ.sourcePoint (Γ.oppositeOriented e) = Γ.targetPoint e ∧
      Γ.targetPoint (Γ.oppositeOriented e) = Γ.sourcePoint e := by
  obtain ⟨b, rfl⟩ := orientedClass_surjective Γ e
  rw [Γ.oppositeOriented_orientedClass, Γ.sourcePoint_orientedClass,
    Γ.targetPoint_orientedClass, Γ.sourcePoint_orientedClass,
    Γ.targetPoint_orientedClass]
  exact ⟨rfl, rfl⟩
theorem linkEndpoints_linkImage (d : Γ.QuotientLink) :
    Γ.linkEndpoints (Γ.linkImage (_root_.YangMills.Construction.NormalFamilies.NormalLevelPair.reflectSymmetry ⟨n, D.normal_mem, c, hc⟩) d) =
      Γ.descendPoint (_root_.YangMills.Construction.NormalFamilies.NormalLevelPair.reflectSymmetry ⟨n, D.normal_mem, c, hc⟩) ''
        Γ.linkEndpoints d := by
  rw [Γ.linkEndpoints_eq, Γ.linkEndpoints_eq d, Set.image_pair, ← hI.sourcePoint_descend,
    ← hI.targetPoint_descend]
  rcases orientedOfLink_linkImage (_root_.YangMills.Construction.NormalFamilies.NormalLevelPair.reflectSymmetry ⟨n, D.normal_mem, c, hc⟩) d
    with h | h
  · rw [h]
  · rw [h, (endpoints_oppositeOriented _).1, (endpoints_oppositeOriented _).2, Set.pair_comm]
theorem linkImage_mem_linksInside {T T' : Set Γ.QuotientTorus}
    (hT : Γ.descendPoint (_root_.YangMills.Construction.NormalFamilies.NormalLevelPair.reflectSymmetry ⟨n, D.normal_mem, c, hc⟩) '' T = T')
    {d : Γ.QuotientLink} (hd : d ∈ Γ.linksInside T) :
    Γ.linkImage (_root_.YangMills.Construction.NormalFamilies.NormalLevelPair.reflectSymmetry ⟨n, D.normal_mem, c, hc⟩) d ∈
      Γ.linksInside T' := by
  change Γ.linkEndpoints _ ⊆ T'
  rw [linkEndpoints_linkImage D hc hI, ← hT]
  exact Set.image_mono hd
theorem descend_descend (e : Γ.OrientedLink) :
    Γ.descendOrientedLink (_root_.YangMills.Construction.NormalFamilies.NormalLevelPair.reflectSymmetry ⟨n, D.normal_mem, c, hc⟩)
      (Γ.descendOrientedLink (_root_.YangMills.Construction.NormalFamilies.NormalLevelPair.reflectSymmetry ⟨n, D.normal_mem, c, hc⟩) e) = e := by
  obtain ⟨b, rfl⟩ := orientedClass_surjective Γ e
  rw [hI.descendOrientedLink_orientedClass, hI.descendOrientedLink_orientedClass]
  congr 1
  exact InfiniteLattice.Link.ext (reflect_pointMap_involutive D hc _)
    (reflect_pointMap_involutive D hc _)
theorem descend_opposite (e : Γ.OrientedLink) :
    Γ.descendOrientedLink (_root_.YangMills.Construction.NormalFamilies.NormalLevelPair.reflectSymmetry ⟨n, D.normal_mem, c, hc⟩)
      (Γ.oppositeOriented e) =
      Γ.oppositeOriented
        (Γ.descendOrientedLink (_root_.YangMills.Construction.NormalFamilies.NormalLevelPair.reflectSymmetry ⟨n, D.normal_mem, c, hc⟩) e) := by
  obtain ⟨b, rfl⟩ := orientedClass_surjective Γ e
  rw [Γ.oppositeOriented_orientedClass, hI.descendOrientedLink_orientedClass,
    hI.descendOrientedLink_orientedClass, Γ.oppositeOriented_orientedClass]
  rfl
omit hI in
theorem oppositeOriented_oppositeOriented (e : Γ.OrientedLink) :
    Γ.oppositeOriented (Γ.oppositeOriented e) = e := by apply _root_.YangMills.Construction.InfiniteLattice.HalvesFactorizationProof.oppositeOriented_oppositeOriented <;> assumption
omit hI in
theorem not_positive_opposite (d : Γ.QuotientLink) :
    ¬ Γ.OrientedIsPositive (Γ.oppositeOriented (Γ.orientedOfLink d)) := by
  obtain ⟨b, rfl⟩ := linkClass_surjective Γ d
  rw [Γ.orientedOfLink_linkClass, Γ.oppositeOriented_orientedClass,
    Γ.orientedIsPositive_orientedClass_iff]
  exact Γ.not_isPositivelyOriented_opposite b.2
omit hI in
theorem orientedOfLink_positive (d : Γ.QuotientLink) :
    Γ.OrientedIsPositive (Γ.orientedOfLink d) := by
  have h : Γ.orientedOfLink d ∈ Set.range Γ.orientedOfLink := ⟨d, rfl⟩
  rw [Γ.range_orientedOfLink] at h
  exact h
theorem linkImage_involutive :
    Function.Involutive
      (Γ.linkImage (_root_.YangMills.Construction.NormalFamilies.NormalLevelPair.reflectSymmetry ⟨n, D.normal_mem, c, hc⟩)) := by
  intro d
  set r := _root_.YangMills.Construction.NormalFamilies.NormalLevelPair.reflectSymmetry ⟨n, D.normal_mem, c, hc⟩ with hrdef
  have hii := descend_descend D hc hI
  have hir := descend_opposite D hc hI
  rw [← hrdef] at hii hir
  refine Γ.orientedOfLink_injective ?_
  have alt : Γ.orientedOfLink (Γ.linkImage r (Γ.linkImage r d)) = Γ.orientedOfLink d ∨
      Γ.orientedOfLink (Γ.linkImage r (Γ.linkImage r d)) =
        Γ.oppositeOriented (Γ.orientedOfLink d) := by
    rcases orientedOfLink_linkImage r (Γ.linkImage r d) with h | h <;>
      rcases orientedOfLink_linkImage r d with h' | h'
    · left
      rw [h, h', hii]
    · right
      rw [h, h', hir, hii]
    · right
      rw [h, h', hii]
    · left
      rw [h, h', hir, hii, oppositeOriented_oppositeOriented]
  rcases alt with h | h
  · exact h
  · exact absurd (h ▸ orientedOfLink_positive _) (not_positive_opposite d)
theorem linkImage_halves :
    BijOn (Γ.linkImage (_root_.YangMills.Construction.NormalFamilies.NormalLevelPair.reflectSymmetry ⟨n, D.normal_mem, c, hc⟩))
      (Γ.plusLinks n z c \ Γ.sharedLinks n z c)
      (Γ.minusLinks n z c \ Γ.sharedLinks n z c) ∧
    Γ.linkImage (_root_.YangMills.Construction.NormalFamilies.NormalLevelPair.reflectSymmetry ⟨n, D.normal_mem, c, hc⟩) '' Γ.sharedLinks n z c =
      Γ.sharedLinks n z c ∧
    Γ.linkImage (_root_.YangMills.Construction.NormalFamilies.NormalLevelPair.reflectSymmetry ⟨n, D.normal_mem, c, hc⟩) '' Γ.plusLinks n z c =
      Γ.minusLinks n z c ∧
    Γ.linkImage (_root_.YangMills.Construction.NormalFamilies.NormalLevelPair.reflectSymmetry ⟨n, D.normal_mem, c, hc⟩) '' Γ.minusLinks n z c =
      Γ.plusLinks n z c := by
  have inv := linkImage_involutive D hc hI
  set σ := Γ.linkImage (_root_.YangMills.Construction.NormalFamilies.NormalLevelPair.reflectSymmetry ⟨n, D.normal_mem, c, hc⟩) with hσ
  have up : ∀ d ∈ Γ.plusLinks n z c, σ d ∈ Γ.minusLinks n z c := fun d hd =>
    linkImage_mem_linksInside D hc hI (image_plusHalf D hc hI) hd
  have lo : ∀ d ∈ Γ.minusLinks n z c, σ d ∈ Γ.plusLinks n z c := fun d hd =>
    linkImage_mem_linksInside D hc hI (image_minusHalf D hc hI) hd
  have both : ∀ d ∈ Γ.sharedLinks n z c, σ d ∈ Γ.sharedLinks n z c := fun d hd =>
    ⟨lo d hd.2, up d hd.1⟩
  have img : ∀ {A B : Set Γ.QuotientLink}, (∀ d ∈ A, σ d ∈ B) → (∀ d ∈ B, σ d ∈ A) →
      σ '' A = B := by
    intro A B h₁ h₂
    ext d
    constructor
    · rintro ⟨e, he, rfl⟩
      exact h₁ e he
    · intro hd
      exact ⟨σ d, h₂ d hd, inv d⟩
  refine ⟨?_, img both both, img up lo, img lo up⟩
  refine Set.InvOn.bijOn (f' := σ) ⟨fun d _ => inv d, fun d _ => inv d⟩ ?_ ?_
  · intro d hd
    exact ⟨up d hd.1, fun h => hd.2 (inv d ▸ both _ h)⟩
  · intro d hd
    exact ⟨lo d hd.1, fun h => hd.2 (inv d ▸ both _ h)⟩
end ReflectionOfHalves
section BoundedAlgebras
open scoped ComplexConjugate
variable {Γ : PeriodSublattice 1} {n : AmbientSpace} {z : ℤ} {c : ℝ}
theorem conjReflect_mem {P : NormalLevelPair 1} {𝓜 : Set Γ.QuotientLink}
    (hb : ∀ F : Γ.QuotientField → ℂ, Γ.IsBoundedBorelFn F →
      Γ.IsBoundedBorelFn (Γ.compPullback P.reflectSymmetry F) ∧
        ∀ 𝓝 : Set Γ.QuotientLink, PeriodSublattice.DependsOnlyOn F 𝓝 →
          PeriodSublattice.DependsOnlyOn (Γ.compPullback P.reflectSymmetry F)
            (Γ.linkImage P.reflectSymmetry '' 𝓝))
    {F : Γ.QuotientField → ℂ} (hF : F ∈ Γ.boundedAlgebra 𝓜) :
    Γ.conjReflect P F ∈
      Γ.boundedAlgebra (Γ.linkImage P.reflectSymmetry '' 𝓜) := by
  obtain ⟨hm, hC, dep⟩ := hF
  obtain ⟨⟨hm', C, hC'⟩, dep'⟩ := hb F ⟨hm, hC⟩
  refine ⟨Complex.continuous_conj.measurable.comp hm', ⟨C, fun U => ?_⟩, fun U U' h => ?_⟩
  · change ‖conj _‖ ≤ C
    rw [Complex.norm_conj]
    exact hC' U
  · change conj _ = conj _
    rw [dep' 𝓜 dep U U' h]
end BoundedAlgebras
section Gathering
variable {Γ : PeriodSublattice 1}
theorem plaquetteShift_plaquetteShift (p : ElementaryPlaquette 1) (γ γ' : LatticePoint 1) :
    plaquetteShift (plaquetteShift p γ) γ' = plaquetteShift p (γ + γ') := by
  simp only [plaquetteShift, add_assoc]
theorem faceClass_plaquetteShift (hr : SymmetryActionRules.Statement)
    (p : ElementaryPlaquette 1) {γ : LatticePoint 1} (hγ : γ ∈ Γ.periods) :
    Γ.faceClass (plaquetteShift p γ) = Γ.faceClass p := by
  refine Subtype.ext (Set.ext fun q => ⟨?_, ?_⟩)
  · rintro ⟨γ', hγ', rfl⟩
    refine ⟨γ + γ', add_mem hγ hγ', ?_⟩
    rw [plaquetteMap_shift hr, plaquetteMap_shift hr, plaquetteShift_plaquetteShift]
  · rintro ⟨γ', hγ', rfl⟩
    refine ⟨-γ + γ', add_mem (neg_mem hγ) hγ', ?_⟩
    rw [plaquetteMap_shift hr, plaquetteMap_shift hr, plaquetteShift_plaquetteShift,
      add_neg_cancel_left]
theorem eq_faceClass_of_isLift (hr : SymmetryActionRules.Statement)
    {p : ElementaryPlaquette 1} {q : Γ.QuotientPlaquette} (h : Γ.IsLiftOfPlaquette p q) :
    q = Γ.faceClass p := by
  obtain ⟨p₀, rfl⟩ := faceClass_surjective Γ q
  obtain ⟨γ, hγ, rfl⟩ := h
  rw [plaquetteMap_shift hr, faceClass_plaquetteShift hr p₀ hγ]
theorem rep_isLift (q : Γ.QuotientPlaquette) :
    Γ.IsLiftOfPlaquette (Γ.quotientPlaquette_nonempty q).some q :=
  (Γ.quotientPlaquette_nonempty q).some_mem
theorem exists_period_vector {n : AmbientSpace} {z : ℤ} (hs : Γ.SplitsAlongWithHalfPeriod n z) :
    ∃ w ∈ Γ.periods, (w : AmbientSpace) = (2 * (z : ℝ)) • dualVector n := by
  obtain ⟨-, -, H, hH⟩ := hs
  have h₁ : (2 * (z : ℝ)) • ReflectionPositivity.NormalPlanes.normalOverNormSq n ∈
      PeriodSublattice.axialSubgroup n z :=
    AddSubgroup.mem_zmultiples _
  have h₂ : (2 * (z : ℝ)) • ReflectionPositivity.NormalPlanes.normalOverNormSq n ∈ Γ.toAmbient := by
    rw [← hH.sup_eq]
    exact AddSubgroup.mem_sup_right h₁
  obtain ⟨w, hw, e⟩ := h₂
  refine ⟨w, hw, ?_⟩
  have e' : (w : AmbientSpace) = (2 * (z : ℝ)) • ReflectionPositivity.NormalPlanes.normalOverNormSq n := e
  rw [e', dualVector, normSq_eq_dotProduct]
  rfl
end Gathering
end TwoLevels
open NormalFamilies TwoLevels in
open PeriodicLattice (coordVec) in
theorem twoLevelsOfOneReflection_holds
    (hm : _root_.YangMills.Construction.NormalFamilies.CutPlaquettesOfMirror)
    (hd : SplitTorusDescent)
    (hpb : SplitTorusPullbacks)
    (hF : TorusQuotientIsFaithful.Statement)
    (hE : PeriodicQuotient.FinitenessClaim)
    (hr : SymmetryActionRules.Statement) :
    TwoLevelsOfOneReflection := by
  intro Γ n hn z c hc hs
  have hIall : ∀ (c' : ℝ) (hc' : _root_.YangMills.Construction.NormalFamilies.IsAllowedLevel 1 n c'),
      Γ.DescendsToQuotient (_root_.YangMills.Construction.NormalFamilies.NormalLevelPair.reflectSymmetry ⟨n, hn, c', hc'⟩) := fun c' hc' => by
    obtain ⟨-, -, -, -, -, -, -, -, -, h, -⟩ := hd Γ n hn z c' hc' 0 hs
    exact h
  obtain ⟨-, -, -, hsame, -, -, -, -, -, -, -, -, -, -, -, ⟨hz, hmaps⟩, -⟩ := hd Γ n hn z c hc 0 hs
  obtain ⟨w, hw, hwe⟩ := _root_.YangMills.Construction.InfiniteLattice.TwoLevels.exists_period_vector hs
  obtain ⟨cc, hcc⟩ := _root_.YangMills.Construction.InfiniteLattice.TwoLevels.exists_half_int hn hc
  have D : Setup Γ n z c cc w := ⟨hn, hs.2.1, hcc, hw, hwe, hsame⟩
  have hI := hIall c hc
  have hI' := hIall _ hz
  have two := D.two_le
  obtain ⟨hθ, hevery, -⟩ := hpb 1 one_pos Γ n hn z hs
  obtain ⟨-, -, -, -, hΘinv⟩ := hθ c hc
  have hfam : IsClassIsometry n (_root_.YangMills.Construction.NormalFamilies.NormalLevelPair.reflectSymmetry ⟨n, hn, c, hc⟩).toFun :=
    IsGenerator.isClassIsometry (Or.inr ⟨c, hc, rfl⟩)
  obtain ⟨-, -, -, -, hext, -, hbb, -⟩ := hevery _ hfam
  obtain ⟨hbij, hzero, hupimg, hloimg⟩ := linkImage_halves D hc hI
  have hEx := hE.1 Γ
  refine ⟨hz, ?_⟩
  intro P P'
  have vQ : ∀ Q : NormalLevelPair 1, Q = P ∨ Q = P' → Q.normal = n := by
    rintro Q (h | h) <;> rw [h]
  have posQ : ∀ Q : NormalLevelPair 1, Q = P ∨ Q = P' →
      ∃ V : ℤ, (V = 0 ∨ V = 2 * z) ∧ Q.level = c + (V : ℝ) / 2 := by
    rintro Q (h | h)
    · exact ⟨0, Or.inl rfl, by rw [h]; exact level_base⟩
    · exact ⟨2 * z, Or.inr rfl, by rw [h]; exact level_half_period⟩
  have intQ : ∀ Q : NormalLevelPair 1, Q = P ∨ Q = P' → ∀ k : ℤ, c = (k : ℝ) →
      ∃ k' : ℤ, Q.level = (k' : ℝ) := by
    rintro Q (h | h) k hk
    · exact ⟨k, by rw [h]; exact hk⟩
    · exact ⟨k + z, by rw [h]; change c + (z : ℝ) = _; push_cast; rw [hk]⟩
  have halfQ : ∀ Q : NormalLevelPair 1, Q = P ∨ Q = P' → ∀ k : ℤ, c = (k : ℝ) + 1 / 2 →
      ∃ k' : ℤ, Q.level = (k' : ℝ) + 1 / 2 := by
    rintro Q (h | h) k hk
    · exact ⟨k, by rw [h]; exact hk⟩
    · exact ⟨k + z, by rw [h]; change c + (z : ℝ) = _; push_cast; rw [hk]; ring⟩
  have conjImage : ∀ {A B : Set Γ.QuotientLink},
      Γ.linkImage P.reflectSymmetry '' A = B → Γ.linkImage P.reflectSymmetry '' B = A →
      Γ.conjReflect P '' (Γ.boundedAlgebra A : Set (Γ.QuotientField → ℂ)) =
        (Γ.boundedAlgebra B : Set (Γ.QuotientField → ℂ)) := by
    intro A B hAB hBA
    have hb : ∀ F : Γ.QuotientField → ℂ, Γ.IsBoundedBorelFn F →
        Γ.IsBoundedBorelFn (Γ.compPullback P.reflectSymmetry F) ∧
          ∀ 𝓝 : Set Γ.QuotientLink, PeriodSublattice.DependsOnlyOn F 𝓝 →
            PeriodSublattice.DependsOnlyOn (Γ.compPullback P.reflectSymmetry F)
              (Γ.linkImage P.reflectSymmetry '' 𝓝) := fun F hF' =>
      ⟨(hbb F hF').1, (hbb F hF').2.2.2⟩
    ext G
    constructor
    · rintro ⟨F, hF', rfl⟩
      have := conjReflect_mem hb hF'
      rwa [hAB] at this
    · intro hG
      have h₁ := conjReflect_mem hb hG
      rw [hBA] at h₁
      exact ⟨_, h₁, hΘinv G ⟨hG.1, hG.2.1⟩⟩
  refine ⟨sharedLinks_eq D, ?_, ?_, image_plusHalf D hc hI, hbij, hzero,
    conjImage hupimg hloimg, conjImage hloimg hupimg, ?_, ?_, ?_⟩
  · rintro ⟨k, hk⟩
    have hc2 : cc % 2 = 0 := by
      have : (cc : ℝ) = ((2 * k : ℤ) : ℝ) := by
        push_cast
        linarith
      have : cc = 2 * k := by exact_mod_cast this
      omega
    refine ⟨crossingLinks_empty D hc2, shared_fixed D hc hI, ?_, ?_⟩
    · intro hq q
      obtain ⟨p, rfl⟩ := faceClass_surjective Γ q
      rcases hn with ⟨μ, hμ⟩ | ⟨μ, lam, hlt, hμ⟩
      · refine not_split_of_coord_zero hr D hc2 p ?_
        by_cases h : p.lowAxis = μ
        · right
          have h' : p.highAxis ≠ μ := fun e => p.lowAxis_lt_highAxis.ne (h.trans e.symm)
          rw [hμ, entry_coordVec]
          simp [h']
        · left
          rw [hμ, entry_coordVec]
          simp [h]
      · have := normSq_diag hlt hμ.symm
        rw [this] at hq
        norm_num at hq
    · intro μ lam hlt hvec
      refine ⟨split_iff_at_site_level hr hF D hc2 hlt hvec, ?_⟩
      intro Q hQ q hq h2
      obtain ⟨V, -, hpos⟩ := posQ Q hQ
      exact exists_diag_lift hr hF hm D hlt hvec (vQ Q hQ) hpos (intQ Q hQ k hk) q hq h2
  · rintro ⟨k, hk⟩
    have hc2 : cc % 2 = 1 := by
      have : (cc : ℝ) = ((2 * k + 1 : ℤ) : ℝ) := by
        push_cast
        linarith
      have : cc = 2 * k + 1 := by exact_mod_cast this
      omega
    have hμ : ∃ μ : Fin 4, n = coordVec μ := by
      rcases hn with ⟨μ, hμ⟩ | ⟨μ, lam, hlt, hμ⟩
      · exact ⟨μ, hμ⟩
      · exfalso
        obtain ⟨k', hk'⟩ := ((isAllowedLevel_one_iff n c).1 hc).2 (normSq_diag hlt hμ.symm)
        have : ((2 * k + 1 : ℤ) : ℝ) = ((2 * k' : ℤ) : ℝ) := by
          push_cast
          linarith
        have : 2 * k + 1 = 2 * k' := by exact_mod_cast this
        omega
    obtain ⟨μ, hμ⟩ := hμ
    refine ⟨μ, hμ, sharedLinks_empty D hc2, crossingLinks_eq D hc2 hμ,
      crossing_opposite D hc hc2 hμ hI, split_iff_at_link_level hr D hc2 hμ, ?_⟩
    intro Q hQ q h2
    obtain ⟨V, -, hpos⟩ := posQ Q hQ
    exact exists_axial_lift hr hm D hμ (vQ Q hQ) hpos (halfQ Q hQ k hk) q h2
  · intro Q hQ
    refine ⟨?_, ?_⟩
    · intro μ lam hlt hvec hint p y y' hcut
      obtain ⟨-, -, -, -, -, zp, zm, b₁, b₂, b₃, b₄, hcorn, e₁, e₂, -, t₁, t₂, t₃, t₄, t₅, t₆, t₇, t₈,
        hU⟩ := hcut
      exact ⟨zp, zm, b₁, b₂, b₃, b₄, hcorn, e₁, e₂, t₁, t₂, t₃, t₄, t₅, t₆, t₇, t₈, fun U => hU _⟩
    · rintro μ hμ ⟨k, hk⟩ p x lam ⟨hne, hcorners, hh, -⟩ U
      exact (((hm Q).2.2 μ ((vQ Q hQ).trans hμ) (halfQ Q hQ k hk) p).2 x lam hne hcorners hh).2 _
  · intro q p hp
    refine ⟨fun U => ?_, fun U b _ => Γ.lift_apply_positive U b, ?_, ((hF Γ).2.2 q).2⟩
    · have := hEx.faceEnergy_lifts_eq q U _ p (rep_isLift q) hp
      exact this
    · rw [eq_faceClass_of_isLift hr hp]
      exact plaquetteLinks_faceClass hr p
  · intro U
    refine ⟨Subtype.ext (funext fun b => ?_), (hext U).symm⟩
    change Γ.lift U (P'.reflectSymmetry.linkMap b) =
      Γ.lift U (P.reflectSymmetry.linkMap b)
    rw [hEx.lift_apply_link, hEx.lift_apply_link,
      ← hI'.descendOrientedLink_orientedClass, ← hI.descendOrientedLink_orientedClass,
      hmaps.links_eq]
end YangMills.Construction.InfiniteLattice
