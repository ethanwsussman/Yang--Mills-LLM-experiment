import YangMills.Construction.Geometry.TorusArcs
import YangMills.Construction.Lattice.BlocksInTheCoordinatesOfAFinerLatticeProof
import YangMills.Construction.Lattice.ConstantSequenceAsADatumOfTheSetting
import Mathlib
set_option autoImplicit false
open Set YangMills.Construction.TorusMetric
noncomputable section
namespace YangMills.Construction.PeriodicLattice.UnitSpacingCubes
variable {L m : ℕ}
theorem meshSize_nonneg (i : ℤ) : 0 ≤ meshSize L i := zpow_nonneg (Nat.cast_nonneg L) _
theorem meshSize_pos (hL : 0 < L) (i : ℤ) : 0 < meshSize L i := by apply _root_.YangMills.SharedProofs.p6250 <;> assumption
theorem mem_cubeAround_iff {i : ℤ} (y : Site L m i) (w : FourTorus L m) :
    w ∈ cubeAround y ↔ ∀ μ, ‖(w - (y : FourTorus L m)) μ‖ ≤ meshSize L i / 2 := by
  have h : 0 ≤ meshSize L i / 2 := div_nonneg (meshSize_nonneg i) zero_le_two
  simp only [cubeAround, mem_ofPred_eq]
  rw [TorusArcs.torusSupNorm_eq_norm, pi_norm_le_iff_of_nonneg h]
theorem exists_int_mul_near {a : ℝ} (ha : 0 < a) (v : ℝ) : ∃ n : ℤ, |v - n * a| ≤ a / 2 := by
  refine ⟨round (v / a), ?_⟩
  have h := abs_sub_round (v / a)
  have e : v - (round (v / a) : ℝ) * a = (v / a - round (v / a)) * a := by
    field_simp
  rw [e, abs_mul, abs_of_pos ha]
  nlinarith
theorem exists_bounded_int_mul_near {a : ℝ} (ha : 0 < a) {h : ℤ} (hh : 0 ≤ h) {v : ℝ}
    (hv : |v| ≤ (2 * h + 1) * a / 2) : ∃ t : ℤ, |t| ≤ h ∧ |v - t * a| ≤ a / 2 := by
  have hx : |v / a| ≤ (2 * h + 1) / 2 := by
    rw [abs_div, abs_of_pos ha, div_le_iff₀ ha]
    linarith
  obtain ⟨hx₁, hx₂⟩ := abs_le.mp hx
  have hr := abs_le.mp (abs_sub_round (v / a))
  set x := v / a with hxdef
  set r := round x with hrdef
  have key : ∃ t : ℤ, |t| ≤ h ∧ |x - t| ≤ 1 / 2 := by
    by_cases h₁ : h < r
    · refine ⟨h, by rw [abs_of_nonneg hh], ?_⟩
      have : (h : ℝ) + 1 ≤ r := by exact_mod_cast h₁
      rw [abs_le]
      constructor <;> linarith [hr.1, hr.2]
    · by_cases h₂ : r < -h
      · refine ⟨-h, by rw [abs_neg, abs_of_nonneg hh], ?_⟩
        have : (r : ℝ) + 1 ≤ -h := by exact_mod_cast h₂
        push_cast
        rw [abs_le]
        constructor <;> linarith [hr.1, hr.2]
      · exact ⟨r, abs_le.mpr ⟨by omega, by omega⟩, abs_le.mpr hr⟩
  obtain ⟨t, ht, hxt⟩ := key
  refine ⟨t, ht, ?_⟩
  have e : v - (t : ℝ) * a = (x - t) * a := by
    rw [hxdef]
    field_simp
  rw [e, abs_mul, abs_of_pos ha]
  nlinarith
theorem sUnion_standardCubePartition (hL : 0 < L) (i : ℤ) :
    ⋃₀ standardCubePartition L m i = univ := by apply _root_.YangMills.Construction.SeparatedSequence.sUnion_standardCubePartition <;> assumption
theorem meshSize_eq_pow_mul (hL : 0 < L) (i : ℤ) (d : ℕ) :
    meshSize L i = (L : ℝ) ^ d * meshSize L (i + d) := by apply _root_.YangMills.Construction.PeriodicLattice.RefinedBlockCoordinatesProof.meshSize_eq_pow_mul <;> assumption
theorem cube_eq_sUnion_finer (hL : Odd L) {i i' : ℤ} (h : i ≤ i') {Q : Set (FourTorus L m)}
    (hQ : Q ∈ standardCubePartition L m i) :
    Q = ⋃₀ {Q' | Q' ∈ standardCubePartition L m i' ∧ Q' ⊆ Q} := by
  obtain ⟨y, rfl⟩ := hQ
  refine Subset.antisymm (fun w hw => ?_) (sUnion_subset fun Q' hQ' => hQ'.2)
  have hL0 : 0 < L := hL.pos
  obtain ⟨d, hd⟩ := Int.eq_ofNat_of_zero_le (sub_nonneg.mpr h)
  obtain rfl : i' = i + d := by omega
  have ha := meshSize_pos (L := L) hL0 (i + d)
  obtain ⟨k, hk⟩ : Odd (L ^ d) := hL.pow
  have hside : meshSize L i = (2 * ((k : ℤ) : ℝ) + 1) * meshSize L (i + d) := by
    rw [meshSize_eq_pow_mul hL0 i d]
    congr 1
    have : ((L ^ d : ℕ) : ℝ) = 2 * (k : ℝ) + 1 := by exact_mod_cast hk
    push_cast at this ⊢
    exact this
  have hw' := (mem_cubeAround_iff y w).1 hw
  choose v hv hv' using fun μ => exists_coe_eq_abs_eq_norm ((w - (y : FourTorus L m)) μ)
  have hbound : ∀ μ, |v μ| ≤ (2 * ((k : ℤ) : ℝ) + 1) * meshSize L (i + d) / 2 := fun μ => by
    rw [hv', ← hside]
    exact hw' μ
  choose t ht ht' using fun μ =>
    exists_bounded_int_mul_near ha (Int.natCast_nonneg k) (hbound μ)
  let c : FourTorus L m := fun μ => (((t μ : ℝ) * meshSize L (i + d) : ℝ) : AddCircle (torusSide L m))
  have hc : c ∈ sublattice L m (i + d) := ⟨t, fun μ => rfl⟩
  let y' : Site L m (i + d) :=
    ⟨(y : FourTorus L m) + c, add_mem (sublattice_mono hL0 m (by omega) y.2) hc⟩
  refine ⟨cubeAround y', ⟨⟨y', rfl⟩, fun z hz => ?_⟩, (mem_cubeAround_iff y' w).2 fun μ => ?_⟩
  · refine (mem_cubeAround_iff y z).2 fun μ => ?_
    have hz' := (mem_cubeAround_iff y' z).1 hz μ
    have e : (z - (y : FourTorus L m)) μ = (z - (y' : FourTorus L m)) μ + c μ := by
      simp only [y', Pi.sub_apply, Pi.add_apply]
      abel
    have htμ : |(t μ : ℝ)| ≤ (k : ℝ) := by exact_mod_cast ht μ
    have hcμ : ‖c μ‖ ≤ (k : ℝ) * meshSize L (i + d) := by
      refine (addCircle_norm_coe_le_abs _).trans ?_
      rw [abs_mul, abs_of_pos ha]
      exact mul_le_mul_of_nonneg_right htμ ha.le
    rw [e, hside]
    have := norm_add_le ((z - (y' : FourTorus L m)) μ) (c μ)
    push_cast
    nlinarith
  · have e : (w - (y' : FourTorus L m)) μ =
        ((v μ - (t μ : ℝ) * meshSize L (i + d) : ℝ) : AddCircle (torusSide L m)) := by
      rw [AddCircle.coe_sub, hv μ]
      simp only [y', c, Pi.sub_apply, Pi.add_apply]
      abel
    rw [e]
    exact (addCircle_norm_coe_le_abs _).trans (ht' μ)
end YangMills.Construction.PeriodicLattice.UnitSpacingCubes
