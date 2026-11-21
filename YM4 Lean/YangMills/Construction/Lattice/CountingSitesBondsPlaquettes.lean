import YangMills.Construction.Lattice.SiteCoordinatesProof
import YangMills.Construction.Lattice.SiteAndPlaquetteCounts
import YangMills.Construction.Lattice.WilsonActionAsAPlaquetteSumAndSymmetriesOfProductHaarProof
import YangMills.Construction.SystemOfAdmissibleConstants.CumulantConditionsFromTheInequalityProof
import Mathlib
open Set
noncomputable section
namespace YangMills.Construction
open Matrices
namespace PeriodicLattice.Counting
variable {L m : ℕ} {j : ℤ}
abbrev sitesPerAxis (L m : ℕ) (j : ℤ) : ℕ := 2 * L ^ ((m : ℤ) + j).toNat
theorem sitesPerAxis_pos (hL : 0 < L) : 0 < sitesPerAxis L m j :=
  Nat.mul_pos two_pos (pow_pos hL _)
theorem zero_lt_meshSize (hL : 0 < L) : 0 < meshSize L j := by apply _root_.YangMills.SharedProofs.p16883 <;> assumption
theorem zero_lt_torusSide (hL : 0 < L) : 0 < torusSide L m := by apply _root_.YangMills.SharedProofs.p16249 <;> assumption
theorem torusSide_eq_sitesPerAxis_mul (hL : 0 < L) (hj : -(m : ℤ) ≤ j) :
    torusSide L m = (sitesPerAxis L m j : ℝ) * meshSize L j := by apply _root_.YangMills.DeltaSharedProofs.p501486 <;> assumption
theorem addOrderOf_meshSize (hL : 0 < L) (hj : -(m : ℤ) ≤ j) :
    addOrderOf ((meshSize L j : ℝ) : AddCircle (torusSide L m)) = sitesPerAxis L m j := by
  have : Fact (0 < torusSide L m) := ⟨zero_lt_torusSide hL⟩
  have hN : 0 < sitesPerAxis L m j := sitesPerAxis_pos hL
  have hN' : (sitesPerAxis L m j : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have hmesh : meshSize L j = torusSide L m / (sitesPerAxis L m j : ℝ) := by
    rw [eq_div_iff hN', mul_comm]
    exact (torusSide_eq_sitesPerAxis_mul hL hj).symm
  rw [hmesh]
  exact AddCircle.addOrderOf_period_div hN
abbrev AxisGrid (L m : ℕ) (j : ℤ) : Type :=
  {t : AddCircle (torusSide L m) //
    ∃ n : ℤ, t = (((n : ℝ) * meshSize L j : ℝ) : AddCircle (torusSide L m))}
theorem card_axisGrid (hL : 0 < L) (hj : -(m : ℤ) ≤ j) :
    Nat.card (AxisGrid L m j) = sitesPerAxis L m j := by
  have hcard := Nat.card_zmultiples ((meshSize L j : ℝ) : AddCircle (torusSide L m))
  rw [addOrderOf_meshSize hL hj] at hcard
  rw [← hcard]
  refine Nat.card_congr (Equiv.subtypeEquivRight fun t => ?_)
  rw [AddSubgroup.mem_zmultiples_iff]
  constructor
  · rintro ⟨n, rfl⟩
    exact ⟨n, by rw [← AddCircle.coe_zsmul, zsmul_eq_mul]⟩
  · rintro ⟨n, rfl⟩
    exact ⟨n, by rw [← AddCircle.coe_zsmul, zsmul_eq_mul]⟩
theorem finite_axisGrid (hL : 0 < L) (hj : -(m : ℤ) ≤ j) : Finite (AxisGrid L m j) :=
  Nat.finite_of_card_ne_zero (by
    rw [card_axisGrid hL hj]
    exact (sitesPerAxis_pos hL).ne')
def siteEquivCoords (L m : ℕ) (j : ℤ) : Site L m j ≃ (Fin 4 → AxisGrid L m j) where
  toFun x μ := ⟨x.1 μ, by
    obtain ⟨n, hn⟩ := x.2
    exact ⟨n μ, hn μ⟩⟩
  invFun c := ⟨fun μ => (c μ).1, fun μ => (c μ).2.choose, fun μ => (c μ).2.choose_spec⟩
  left_inv _ := rfl
  right_inv _ := rfl
theorem site_finite (hL : 0 < L) (hj : -(m : ℤ) ≤ j) : Finite (Site L m j) := by
  have := finite_axisGrid hL hj
  exact Finite.of_equiv _ (siteEquivCoords L m j).symm
theorem card_site_eq (hL : 0 < L) (hj : -(m : ℤ) ≤ j) :
    Nat.card (Site L m j) = sitesPerAxis L m j ^ 4 := by
  have := finite_axisGrid hL hj
  rw [Nat.card_congr (siteEquivCoords L m j), Nat.card_fun, card_axisGrid hL hj]
  simp
def plaquetteEquivOriginAxes (L m : ℕ) (j : ℤ) :
    Plaquette L m j ≃ Site L m j × {q : Fin 4 × Fin 4 // q.1 < q.2} where
  toFun p := (p.origin, ⟨(p.firstAxis, p.secondAxis), p.firstAxis_lt_secondAxis⟩)
  invFun x := ⟨x.1, x.2.1.1, x.2.1.2, x.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
theorem card_plaquette_eq (hL : 0 < L) (hj : -(m : ℤ) ≤ j) :
    Nat.card (Plaquette L m j) = 6 * sitesPerAxis L m j ^ 4 := by
  have hpairs : Nat.card {q : Fin 4 × Fin 4 // q.1 < q.2} = 6 := by
    rw [Nat.card_eq_fintype_card]
    decide
  rw [Nat.card_congr (plaquetteEquivOriginAxes L m j), Nat.card_prod, card_site_eq hL hj, hpairs,
    mul_comm]
theorem translate_dualLatticePoints (hL : 0 < L) (hj : -(m : ℤ) ≤ j) (hodd : Odd L) :
    (fun x => x + centerDiagonalPoint L m) '' dualLatticePoints L m j = sublattice L m j := by
  obtain ⟨d, hd⟩ := (hodd.pow : Odd (L ^ ((m : ℤ) + j).toNat))
  have hhalf : (1 / 2 : ℝ) * (L : ℝ) ^ m = ((d : ℝ) + 1 / 2) * meshSize L j := by
    have h₀ := torusSide_eq_sitesPerAxis_mul (m := m) (j := j) hL hj
    simp only [torusSide, sitesPerAxis] at h₀
    rw [hd] at h₀
    push_cast at h₀
    linarith
  ext y
  constructor
  · rintro ⟨x, ⟨n, hn⟩, rfl⟩
    refine ⟨fun μ => n μ + d + 1, fun μ => ?_⟩
    change x μ + (((1 / 2 : ℝ) * (L : ℝ) ^ m : ℝ) : AddCircle (torusSide L m)) = _
    rw [hn μ, ← AddCircle.coe_add, hhalf]
    congr 1
    push_cast
    ring
  · rintro ⟨n, hn⟩
    refine ⟨y - centerDiagonalPoint L m, ⟨fun μ => n μ - d - 1, fun μ => ?_⟩, by simp⟩
    change y μ - (((1 / 2 : ℝ) * (L : ℝ) ^ m : ℝ) : AddCircle (torusSide L m)) = _
    rw [hn μ, ← AddCircle.coe_sub, hhalf]
    congr 1
    push_cast
    ring
theorem four_le_sitesPerAxis (h1 : 1 < L) (hk : 0 < (m : ℤ) + j) : 4 ≤ sitesPerAxis L m j := by
  have hgt : 1 < L ^ ((m : ℤ) + j).toNat := Nat.one_lt_pow (by omega) h1
  simp only [sitesPerAxis]
  omega
theorem unitStep_coord_self (μ : Fin 4) :
    ((unitStep L m j μ : Site L m j) : FourTorus L m) μ =
      ((meshSize L j : ℝ) : AddCircle (torusSide L m)) := by apply _root_.YangMills.SharedProofs.p39116 <;> assumption
theorem unitStep_coord_ne {μ ν : Fin 4} (hne : μ ≠ ν) :
    ((unitStep L m j ν : Site L m j) : FourTorus L m) μ = 0 := by
  simp [unitStep, pointOnAxis, Pi.single_eq_of_ne hne]
theorem not_isPositivelyOriented_opposite (h1 : 1 < L) (hk : 0 < (m : ℤ) + j) {b : Bond L m j}
    (hb : b.IsPositivelyOriented) : ¬ b.opposite.IsPositivelyOriented := by
  have hL : 0 < L := by omega
  have hj : -(m : ℤ) ≤ j := by omega
  rintro ⟨ν, hν⟩
  obtain ⟨μ, hμ⟩ := hb
  have hsum : unitStep L m j μ + unitStep L m j ν = 0 := by
    rw [← hμ, ← hν]
    simp [Bond.opposite]
  have hcoord : ((unitStep L m j μ : Site L m j) : FourTorus L m) μ +
      ((unitStep L m j ν : Site L m j) : FourTorus L m) μ = 0 := by
    have hc := congrArg (fun x : Site L m j => (x : FourTorus L m) μ) hsum
    simpa using hc
  have hord := addOrderOf_meshSize (m := m) (j := j) hL hj
  have h4 := four_le_sitesPerAxis (m := m) (j := j) h1 hk
  by_cases hνμ : μ = ν
  · subst hνμ
    rw [unitStep_coord_self] at hcoord
    have h2 : 2 • ((meshSize L j : ℝ) : AddCircle (torusSide L m)) = 0 := by
      rw [two_nsmul]
      exact hcoord
    have hle := Nat.le_of_dvd two_pos (addOrderOf_dvd_of_nsmul_eq_zero h2)
    omega
  · rw [unitStep_coord_self, unitStep_coord_ne hνμ, add_zero] at hcoord
    have h2 : 1 • ((meshSize L j : ℝ) : AddCircle (torusSide L m)) = 0 := by
      rw [one_nsmul]
      exact hcoord
    have hle := Nat.le_of_dvd one_pos (addOrderOf_dvd_of_nsmul_eq_zero h2)
    omega
theorem inv_coe_specialUnitary (U : ComplexMatrix2.specialUnitary) :
    (U : ComplexMatrix2)⁻¹ = ((U⁻¹ : ComplexMatrix2.specialUnitary) : ComplexMatrix2) := by apply _root_.YangMills.Construction.PeriodicLattice.WilsonPlaquetteSum.coe_inv_specialUnitary <;> assumption
theorem inv_inv_coe_specialUnitary (U : ComplexMatrix2.specialUnitary) :
    ((U : ComplexMatrix2)⁻¹)⁻¹ = U := by
  rw [inv_coe_specialUnitary, inv_coe_specialUnitary, inv_inv]
theorem isPositivelyOriented_or_opposite (b : Bond L m j) :
    b.IsPositivelyOriented ∨ b.opposite.IsPositivelyOriented := by apply _root_.YangMills.SharedProofs.p7155 <;> assumption
theorem gaugeFieldOfPositive_of_pos (v : PositivelyOrientedBond L m j → ComplexMatrix2.specialUnitary)
    {b : Bond L m j} (h : b.IsPositivelyOriented) :
    gaugeFieldOfPositive v b = (v ⟨b, h⟩ : ComplexMatrix2) := by
  simp only [gaugeFieldOfPositive, dif_pos h]
theorem gaugeFieldOfPositive_of_opposite (h1 : 1 < L) (hk : 0 < (m : ℤ) + j)
    (v : PositivelyOrientedBond L m j → ComplexMatrix2.specialUnitary) {b : Bond L m j}
    (h : b.opposite.IsPositivelyOriented) :
    gaugeFieldOfPositive v b = (v ⟨b.opposite, h⟩ : ComplexMatrix2)⁻¹ := by
  have hn : ¬ b.IsPositivelyOriented := fun hb => not_isPositivelyOriented_opposite h1 hk hb h
  simp only [gaugeFieldOfPositive, dif_neg hn, dif_pos h]
theorem continuous_gaugeFieldOfPositive (h1 : 1 < L) (hk : 0 < (m : ℤ) + j) :
    Continuous (gaugeFieldOfPositive :
      (PositivelyOrientedBond L m j → ComplexMatrix2.specialUnitary) → Bond L m j → ComplexMatrix2) := by
  refine continuous_pi fun b => ?_
  rcases em b.IsPositivelyOriented with h | h
  · have e : (fun v : PositivelyOrientedBond L m j → ComplexMatrix2.specialUnitary =>
          gaugeFieldOfPositive v b) = fun v => (v ⟨b, h⟩ : ComplexMatrix2) :=
        funext fun v => gaugeFieldOfPositive_of_pos v h
    rw [e]
    exact continuous_subtype_val.comp (continuous_apply _)
  · have h' := (isPositivelyOriented_or_opposite b).resolve_left h
    have e : (fun v : PositivelyOrientedBond L m j → ComplexMatrix2.specialUnitary =>
          gaugeFieldOfPositive v b) =
        fun v => (((v ⟨b.opposite, h'⟩)⁻¹ : ComplexMatrix2.specialUnitary) : ComplexMatrix2) :=
      funext fun v => by
        rw [gaugeFieldOfPositive_of_opposite h1 hk v h', inv_coe_specialUnitary]
    rw [e]
    exact continuous_subtype_val.comp (continuous_apply _).inv
theorem injective_gaugeFieldOfPositive :
    Function.Injective (gaugeFieldOfPositive :
      (PositivelyOrientedBond L m j → ComplexMatrix2.specialUnitary) → Bond L m j → ComplexMatrix2) := by
  intro v w h
  funext b
  apply Subtype.ext
  have e := congrFun h b.1
  rwa [gaugeFieldOfPositive_of_pos v b.2, gaugeFieldOfPositive_of_pos w b.2] at e
theorem range_gaugeFieldOfPositive (h1 : 1 < L) (hk : 0 < (m : ℤ) + j) :
    range (gaugeFieldOfPositive :
      (PositivelyOrientedBond L m j → ComplexMatrix2.specialUnitary) → Bond L m j → ComplexMatrix2) =
      compactGaugeFields L m j := by
  ext U
  constructor
  · rintro ⟨v, rfl⟩
    refine ⟨fun b _ => ?_, fun b _ => ?_⟩
    · rcases isPositivelyOriented_or_opposite b with h | h
      · rw [gaugeFieldOfPositive_of_pos v h]
        exact (v _).2
      · rw [gaugeFieldOfPositive_of_opposite h1 hk v h, inv_coe_specialUnitary]
        exact ((v ⟨b.opposite, h⟩)⁻¹).2
    · rcases em b.IsPositivelyOriented with h | h
      · have e := gaugeFieldOfPositive_of_opposite h1 hk v (b := b.opposite) h
        rw [gaugeFieldOfPositive_of_pos v h]
        exact e
      · have h' := (isPositivelyOriented_or_opposite b).resolve_left h
        rw [gaugeFieldOfPositive_of_pos v h', gaugeFieldOfPositive_of_opposite h1 hk v h',
          inv_inv_coe_specialUnitary]
  · rintro ⟨hG, hR⟩
    refine ⟨fun b => ⟨U b.1, hG b.1 (mem_univ _)⟩, funext fun b => ?_⟩
    rcases em b.IsPositivelyOriented with h | h
    · rw [gaugeFieldOfPositive_of_pos _ h]
    · have h' := (isPositivelyOriented_or_opposite b).resolve_left h
      rw [gaugeFieldOfPositive_of_opposite h1 hk _ h']
      change (U b.opposite)⁻¹ = U b
      rw [hR b (mem_univ _)]
      exact inv_inv_coe_specialUnitary ⟨U b, hG b (mem_univ _)⟩
theorem bond_finite (hL : 0 < L) (hj : -(m : ℤ) ≤ j) : Finite (Bond L m j) := by
  have := site_finite hL hj
  exact Finite.of_injective (fun b : Bond L m j => (b.source, b.target)) fun b b' h =>
    Bond.ext (congrArg Prod.fst h) (congrArg Prod.snd h)
theorem siteAndPlaquetteCounts_holds : SiteAndPlaquetteCounts := by
  intro L m j hL hj
  refine ⟨?_, card_axisGrid hL hj, card_site_eq hL hj, card_plaquette_eq hL hj,
    translate_dualLatticePoints hL hj, fun h1 hk => ?_⟩
  · rw [torusSide_eq_sitesPerAxis_mul hL hj, mul_div_cancel_right₀ _ (zero_lt_meshSize hL).ne']
  · have := bond_finite hL hj
    have := Fintype.ofFinite (Bond L m j)
    have : TopologicalSpace.MetrizableSpace ComplexMatrix2 :=
      inferInstanceAs (TopologicalSpace.MetrizableSpace (Fin 2 → Fin 2 → ℂ))
    have hc := continuous_gaugeFieldOfPositive (L := L) (m := m) (j := j) h1 hk
    have hr := range_gaugeFieldOfPositive (L := L) (m := m) (j := j) h1 hk
    refine ⟨inferInstance, (hc.isClosedEmbedding injective_gaugeFieldOfPositive).isEmbedding,
      hr, ?_, inferInstance⟩
    rw [← hr]
    exact isCompact_range hc
end PeriodicLattice.Counting
end YangMills.Construction
