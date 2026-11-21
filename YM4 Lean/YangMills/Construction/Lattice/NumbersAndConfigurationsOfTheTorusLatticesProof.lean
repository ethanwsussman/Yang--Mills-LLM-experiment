import YangMills.Construction.Lattice.NumbersAndConfigurationsOfTheTorusLattices
import Mathlib
set_option autoImplicit false
namespace YangMills.Construction
open Filter PeriodicLattice
namespace LatticeCounts
theorem axisPointCount_of_coordinates
    (h : PeriodicLattice.CoordinateDescription) {L m K : ℕ}
    (hodd : Odd L) (hL : 13 ≤ L) (hm : 0 < m) : AxisPointCount L m K := by
  refine ⟨rfl, pointsPerAxis_eq L m K, fun y μ => ?_⟩
  have hj : -(m : ℤ) ≤ (K : ℤ) := by omega
  have hc := ((h L m hodd hL hm).1 (K : ℤ) hj).2.2.2.2.2.1 y μ
  have hexp : ((m : ℤ) + (K : ℤ)).toNat = m + K := by omega
  rw [hc, pointsPerAxis_eq, halfPeriod, hexp]
  push_cast
  rfl
theorem fieldsDeterminedByPositiveBonds_of_lt {L m : ℕ} {j : ℤ} (hL : 2 ≤ L)
    (hj : -(m : ℤ) < j) : FieldsDeterminedByPositiveBonds L m j := by
  have hsub : forwardBonds L m j ⊆ forwardBonds L m j := subset_rfl
  refine ⟨fun U U' hU => ?_, fun V => ?_⟩
  · have hU' : U.restrictTo (forwardBonds L m j) = U'.restrictTo (forwardBonds L m j) := hU
    have e₁ := CompactGaugeField.eq_glue hL hj hsub
      (U.restrictTo (forwardBonds L m j))
      (CompactGaugeField.identity L m j) U (fun _ => rfl)
      (fun _ hb => absurd hb.1 hb.2)
    have e₂ := CompactGaugeField.eq_glue hL hj hsub
      (U.restrictTo (forwardBonds L m j))
      (CompactGaugeField.identity L m j) U' (fun b => (congrFun hU' b).symm)
      (fun _ hb => absurd hb.1 hb.2)
    exact e₁.trans e₂.symm
  · exact ⟨CompactGaugeField.glue hL hj hsub V (CompactGaugeField.identity L m j),
      funext fun b => CompactGaugeField.glue_of_mem hL hj hsub V _ b⟩
theorem evenAxisCountAndHalfSide_of_le {L m K : ℕ} (hL : 13 ≤ L) (hm : 0 < m) :
    EvenAxisCountAndHalfSide L m K := by
  have hLr : (13 : ℝ) ≤ (L : ℝ) := by exact_mod_cast hL
  have hL1 : (1 : ℝ) ≤ (L : ℝ) := by linarith
  have hbig : ∀ n : ℕ, 0 < n → (13 : ℝ) ≤ (L : ℝ) ^ n := fun n hn => by
    have hp : (L : ℝ) ^ 1 ≤ (L : ℝ) ^ n := pow_le_pow_right₀ hL1 hn
    rw [pow_one] at hp
    linarith
  refine ⟨⟨2 * (L : ℤ) ^ (m + K), even_two_mul _, ?_⟩, ?_, ?_⟩
  · rw [pointsPerAxis_eq]
    push_cast
    rfl
  · rw [pointsPerAxis_eq]
    have := hbig (m + K) (by omega)
    linarith
  · have hinv : ((L : ℝ) ^ K)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ hL1)
    have := hbig m hm
    simp only [meshSize, torusSide, zpow_neg, zpow_natCast]
    linarith
theorem torusSidesUnbounded_of_le {L : ℕ} (hL : 13 ≤ L) : TorusSidesUnbounded L := by
  have hLr : (1 : ℝ) < (L : ℝ) := by
    have : (13 : ℝ) ≤ (L : ℝ) := by exact_mod_cast hL
    linarith
  have hstrict : StrictMono fun n : ℕ => torusSide L n := fun a b hab => by
    have hp := pow_lt_pow_right₀ hLr hab
    simp only [torusSide]
    linarith
  have htend : Tendsto (fun n : ℕ => torusSide L n) atTop atTop := by
    simp only [torusSide]
    exact (tendsto_pow_atTop_atTop_of_one_lt hLr).const_mul_atTop (by norm_num)
  refine ⟨?_, fun u hu hmem => ?_⟩
  · rintro ⟨B, hB⟩
    obtain ⟨n, hn₁, hn₂⟩ :=
      ((htend.eventually (eventually_gt_atTop B)).and (eventually_ge_atTop 1)).exists
    exact absurd (hB ⟨n, hn₂, rfl⟩) (not_le.mpr hn₁)
  · choose e he using hmem
    have hmono : StrictMono e := strictMono_nat_of_lt_succ fun i => by
      have hlt := hu (Nat.lt_succ_self i)
      rw [(he _).2, (he _).2] at hlt
      exact hstrict.lt_iff_lt.mp hlt
    refine tendsto_atTop_mono (fun i => ?_) htend
    rw [(he i).2]
    exact hstrict.monotone hmono.le_apply
theorem torusLatticeFacts_holds (h : PeriodicLattice.CoordinateDescription) :
    torusLatticeFacts := by
  intro s
  have hodd : Odd s.L := s.isAdmissible.1
  have hL : 13 ≤ s.L := s.isAdmissible.2
  have hm : 0 < (s.m : ℕ) := s.m.pos
  have hK : 0 < (s.K : ℕ) := s.K.pos
  exact ⟨axisPointCount_of_coordinates h hodd hL hm,
    fieldsDeterminedByPositiveBonds_of_lt (by omega) (by omega),
    evenAxisCountAndHalfSide_of_le hL hm, torusSidesUnbounded_of_le hL⟩
end LatticeCounts
end YangMills.Construction
