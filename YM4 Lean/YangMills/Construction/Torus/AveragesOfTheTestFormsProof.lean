import YangMills.Construction.Lattice.ClosedFormsWithVanishingAveragesAreDifferencesProof
import YangMills.Construction.Torus.ProfilesAndTestForms
import YangMills.Construction.Torus.DifferencesAndAveragesOnAGeneralTorus
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction
open TorusMetric
namespace GeneralTorus
namespace TestFormMeans
@[reducible] private def withGapCountL (D : ScaleData) : ScaleData :=
  { D with gapCount := D.L, gapCount_pow := ⟨1, (pow_one D.L).symm⟩ }
theorem halfSpan_two_mul_add_one (m : ℕ) : halfSpan (2 * m + 1) = m := by
  simp only [halfSpan]
  push_cast
  ring
theorem abs_le_halfSpan_iff {m : ℕ} {a : ℤ} :
    |(a : ℝ)| ≤ halfSpan (2 * m + 1) ↔ -(m : ℤ) ≤ a ∧ a ≤ m := by
  rw [halfSpan_two_mul_add_one, abs_le]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨by exact_mod_cast h1, by exact_mod_cast h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨by exact_mod_cast h1, by exact_mod_cast h2⟩
def cube (m : ℕ) : Finset (Fin 4 → ℤ) := Fintype.piFinset fun _ => Finset.Icc (-(m : ℤ)) m
theorem mem_cube {m : ℕ} {k : Fin 4 → ℤ} : k ∈ cube m ↔ ∀ ν, -(m : ℤ) ≤ k ν ∧ k ν ≤ m := by apply _root_.YangMills.Construction.PeriodicLattice.VanishingAverageGradients.mem_cubeBox <;> assumption
theorem memBondWindow_iff (m : ℕ) (μ : Fin 4) (k : Fin 4 → ℤ) :
    MemBondWindow (2 * m + 1) μ k ↔
      (-(m : ℤ) ≤ k μ ∧ k μ ≤ 3 * m + 1) ∧ ∀ ν, ν ≠ μ → -(m : ℤ) ≤ k ν ∧ k ν ≤ m := by
  unfold MemBondWindow
  constructor
  · rintro ⟨h1, h2, h3⟩
    rw [halfSpan_two_mul_add_one] at h1 h2
    exact ⟨⟨by exact_mod_cast h1, by exact_mod_cast h2⟩, fun ν hν => abs_le_halfSpan_iff.1 (h3 ν hν)⟩
  · rintro ⟨⟨h1, h2⟩, h3⟩
    refine ⟨?_, ?_, fun ν hν => abs_le_halfSpan_iff.2 (h3 ν hν)⟩
    · rw [halfSpan_two_mul_add_one]
      exact_mod_cast h1
    · rw [halfSpan_two_mul_add_one]
      exact_mod_cast h2
section Points
variable (D : ScaleData)
def latticePt (k : Fin 4 → ℤ) : D.Space := torusProj D.torusSide fun ν => D.levelSpacing 0 * (k ν : ℝ)
theorem latticePt_add (k k' : Fin 4 → ℤ) : latticePt D (k + k') = latticePt D k + latticePt D k' := by
  funext ν
  simp only [latticePt, torusProj, Pi.add_apply, Int.cast_add, mul_add, AddCircle.coe_add]
theorem latticePt_sub (k k' : Fin 4 → ℤ) : latticePt D (k - k') = latticePt D k - latticePt D k' := by
  funext ν
  simp only [latticePt, torusProj, Pi.sub_apply, Int.cast_sub, mul_sub, AddCircle.coe_sub]
theorem levelSpacing_zero_pos : 0 < D.levelSpacing 0 := by
  simp only [ScaleData.levelSpacing, pow_zero, one_mul]
  exact D.baseSpacing_pos
theorem dvd_of_latticePt_eq_zero {R : ℕ} (hS : D.torusSide = R * D.levelSpacing 0) {k : Fin 4 → ℤ}
    (h : latticePt D k = 0) (ν : Fin 4) : (R : ℤ) ∣ k ν := by
  have h1 : ((D.levelSpacing 0 * (k ν : ℝ) : ℝ) : AddCircle D.torusSide) = 0 := congrFun h ν
  obtain ⟨i, hi⟩ := (AddCircle.coe_eq_zero_iff D.torusSide).1 h1
  refine ⟨i, ?_⟩
  have hξ := (levelSpacing_zero_pos D).ne'
  have e : (k ν : ℝ) = (R : ℝ) * (i : ℝ) := by
    apply mul_left_cancel₀ hξ
    rw [← hi, zsmul_eq_mul, hS]
    ring
  exact_mod_cast e
theorem unitStep_coe (n : ℕ) (μ : Fin 4) :
    ((unitStep D.torusSide (D.levelSpacing n) μ : LatticeSite D.torusSide (D.levelSpacing n)) : D.Space) =
      latticePt D (Pi.single μ (D.blockSize n : ℤ)) := by
  funext ν
  show (((Pi.single μ (D.levelSpacing n) : Fin 4 → ℝ) ν : ℝ) : AddCircle D.torusSide) =
    ((D.levelSpacing 0 * (((Pi.single μ (D.blockSize n : ℤ) : Fin 4 → ℤ) ν : ℤ) : ℝ) : ℝ) :
      AddCircle D.torusSide)
  by_cases h : ν = μ
  · subst h
    simp only [Pi.single_eq_same, ScaleData.levelSpacing, ScaleData.blockSize]
    congr 1
    push_cast
    ring
  · simp [Pi.single_eq_of_ne h]
variable {D}
theorem tgt_eq {n : ℕ} (c : D.PosBond n) :
    (c.1.tgt : D.Space) =
      (c.1.src : D.Space) + latticePt D (Pi.single (ScaleData.posBondDir c) (D.blockSize n : ℤ)) := by
  rw [← unitStep_coe]
  have h := congrArg Subtype.val c.2.choose_spec
  simp only [AddSubgroupClass.coe_sub] at h
  show _ = _ + ((unitStep D.torusSide (D.levelSpacing n) c.2.choose : LatticeSite D.torusSide (D.levelSpacing n)) : D.Space)
  rw [← h]
  abel
theorem posBondDir_bondFrom {R : ℕ} (hR : 2 ≤ R) (hS : D.torusSide = R * D.levelSpacing 0) (x : D.BaseSite)
    (μ : Fin 4) : ScaleData.posBondDir (ScaleData.bondFrom x μ) = μ := by
  have h := (ScaleData.bondFrom x μ).2.choose_spec
  have h2 : (ScaleData.bondFrom x μ).1.tgt - (ScaleData.bondFrom x μ).1.src =
      unitStep D.torusSide (D.levelSpacing 0) μ := by
    simp [ScaleData.bondFrom, LatticeBond.plus]
  have h4 := congrArg Subtype.val (h.symm.trans h2)
  rw [unitStep_coe, unitStep_coe] at h4
  by_contra hne
  have hne' : (ScaleData.bondFrom x μ).2.choose ≠ μ := hne
  have h0 : latticePt D (Pi.single (ScaleData.bondFrom x μ).2.choose ((D.blockSize 0 : ℕ) : ℤ) -
      Pi.single μ ((D.blockSize 0 : ℕ) : ℤ)) = 0 := by
    rw [latticePt_sub, h4, sub_self]
  have hd := dvd_of_latticePt_eq_zero D hS h0 (ScaleData.bondFrom x μ).2.choose
  simp only [Pi.sub_apply, Pi.single_eq_same, Pi.single_eq_of_ne hne', sub_zero, ScaleData.blockSize,
    pow_zero, Nat.cast_one] at hd
  have := Int.le_of_dvd one_pos hd
  omega
end Points
section Weights
variable {D : ScaleData}
end Weights
section Averages
variable {D : ScaleData} {n : ℕ}
end Averages
end TestFormMeans
end GeneralTorus
end YangMills.Construction
