import YangMills.Construction.TorusForms.BlockSumsBoundedByTheFieldProof
import YangMills.Construction.SeparatedSequences.LowerBoundOnTheContoursAtEveryLevelProof
import YangMills.Construction.TorusForms.BlockAndCorridorParameters
import Mathlib
noncomputable section
namespace YangMills.Construction.BlockSpin.CorridorInequalities
open Finset YangMills.Construction.Lattice
variable {S : LatticeParameters} {ℓ : Fin S.d → ℝ}
theorem gridPoint_add (σ τ : Fin S.d → ℤ) :
    gridPoint ℓ 1 (σ + τ) = gridPoint ℓ 1 σ + gridPoint ℓ 1 τ := by
  apply Subtype.ext
  show torusMk ℓ _ = torusMk ℓ _ + torusMk ℓ _
  rw [← map_add]
  congr 1
  funext μ
  simp
def periodNat (S : LatticeParameters) (ℓ : Fin S.d → ℝ) [h : PeriodsMultipleOfBlock S ℓ]
    (μ : Fin S.d) : ℕ :=
  (h.multiple μ).choose * S.L
variable [hB : PeriodsMultipleOfBlock S ℓ]
theorem periodNat_spec (μ : Fin S.d) : ℓ μ = (periodNat S ℓ μ : ℝ) := by
  have := (hB.multiple μ).choose_spec.2
  simp only [periodNat, Nat.cast_mul]
  exact this
theorem gridPoint_eq_gridPoint_iff (m n : Fin S.d → ℤ) :
    gridPoint ℓ 1 m = gridPoint ℓ 1 n ↔ ∀ μ, (m μ : ZMod (periodNat S ℓ μ)) = n μ := by
  constructor
  · intro h μ
    have h1 : torusMk ℓ (fun μ => (m μ : ℝ) * 1) = torusMk ℓ (fun μ => (n μ : ℝ) * 1) :=
      congrArg Subtype.val h
    rw [torusMk_eq_torusMk_iff] at h1
    obtain ⟨k, hk⟩ := AddSubgroup.mem_zmultiples_iff.mp
      ((AddSubgroup.mem_pi _).mp h1 μ (Set.mem_univ μ))
    rw [ZMod.intCast_eq_intCast_iff_dvd_sub]
    refine ⟨-k, ?_⟩
    have h2 : (k : ℝ) * (periodNat S ℓ μ : ℝ) = (m μ : ℝ) - (n μ : ℝ) := by
      have := hk
      rw [periodNat_spec (ℓ := ℓ) μ, zsmul_eq_mul] at this
      simpa using this
    have h3 : ((n μ - m μ : ℤ) : ℝ) = (((periodNat S ℓ μ : ℤ) * -k : ℤ) : ℝ) := by
      push_cast
      linarith
    exact_mod_cast h3
  · intro h
    apply Subtype.ext
    show torusMk ℓ _ = torusMk ℓ _
    rw [torusMk_eq_torusMk_iff]
    refine (AddSubgroup.mem_pi _).mpr fun μ _ => AddSubgroup.mem_zmultiples_iff.mpr ?_
    obtain ⟨k, hk⟩ := (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).mp (h μ)
    refine ⟨-k, ?_⟩
    have h3 : ((n μ - m μ : ℤ) : ℝ) = (((periodNat S ℓ μ : ℤ) * k : ℤ) : ℝ) := by
      exact_mod_cast hk
    push_cast at h3
    rw [periodNat_spec (ℓ := ℓ) μ, zsmul_eq_mul]
    simp only [Pi.sub_apply, mul_one]
    push_cast
    linarith
def blockSite (S : LatticeParameters) {ℓ : Fin S.d → ℝ} [PeriodsMultipleOfBlock S ℓ]
    (y : LatticeSite ℓ (S.L : ℝ)) (σ : Fin S.d → ℤ) : LatticeSite ℓ 1 :=
  (PeriodsMultipleOfBlock.isBlockSpacing_one (S := S) (ℓ := ℓ)).toFineSite y + gridPoint ℓ 1 σ
theorem blockSite_add (y : LatticeSite ℓ (S.L : ℝ)) (σ τ : Fin S.d → ℤ) :
    blockSite S y (σ + τ) = blockSite S y σ + gridPoint ℓ 1 τ := by
  simp only [blockSite, gridPoint_add, add_assoc]
theorem blockOffset_one (S : LatticeParameters) : blockOffset S 1 = S.offset := by apply _root_.YangMills.Construction.SeparatedClasses.TreeLowerBound.blockOffset_one <;> assumption
def blockIndexRange (S : LatticeParameters) : Finset (Fin S.d → ℤ) :=
  Fintype.piFinset fun _ => Finset.Icc (-(S.offset : ℤ)) ((S.L : ℤ) - 1 - S.offset)
theorem card_blockIndexRange : (blockIndexRange S).card = S.L ^ S.d := by
  simp only [blockIndexRange, Fintype.card_piFinset, Int.card_Icc, Finset.prod_const,
    Finset.card_univ, Fintype.card_fin]
  have : (S.L : ℤ) - 1 - S.offset + 1 - -(S.offset : ℤ) = S.L := by ring
  rw [this]
  simp
theorem sum_range_shift (h : ℕ → ℝ) (L k : ℕ) :
    ∑ a ∈ range L, h (a + k) + ∑ a ∈ range k, h a =
      ∑ a ∈ range L, h a + ∑ a ∈ range k, h (a + L) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [sum_range_succ (fun a => h a) k, sum_range_succ (fun a => h (a + L)) k]
    have h1 : ∑ a ∈ range (L + 1), h (a + k) = ∑ a ∈ range L, h (a + k) + h (L + k) :=
      sum_range_succ _ _
    have h2 : ∑ a ∈ range (L + 1), h (a + k) = ∑ a ∈ range L, h (a + 1 + k) + h (0 + k) :=
      sum_range_succ' _ _
    have h3 : ∑ a ∈ range L, h (a + (k + 1)) = ∑ a ∈ range L, h (a + 1 + k) :=
      sum_congr rfl fun a _ => by congr 1; ring
    have h4 : h (k + L) = h (L + k) := by rw [add_comm]
    simp only [zero_add] at h2
    rw [h3, h4]
    linarith
omit hB in
theorem sq_add_add_le_three_mul (a b c : ℝ) : (a + b + c) ^ 2 ≤ 3 * (a ^ 2 + b ^ 2 + c ^ 2) := by
  nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (a - c)]
section FaceBox
variable (μ : Fin S.d)
end FaceBox
end YangMills.Construction.BlockSpin.CorridorInequalities
