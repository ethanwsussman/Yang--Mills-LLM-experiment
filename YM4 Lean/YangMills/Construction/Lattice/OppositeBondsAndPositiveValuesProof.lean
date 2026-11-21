import YangMills.Construction.Lattice.CovariantAdjointsBySummationByParts
import YangMills.Construction.Lattice.OppositeBondsAndPositiveValues
import Mathlib
set_option autoImplicit false
namespace YangMills.Construction.PeriodicLattice.OppositeBonds
variable {L m : ℕ} {j : ℤ}
theorem int_eq_zero_of_abs_le_two_of_coe_eq_zero (hL : 13 ≤ L) (hj : -(m : ℤ) < j) {t : ℤ}
    (ht : |t| ≤ 2)
    (h : (((t : ℝ) * meshSize L j : ℝ) : AddCircle (torusSide L m)) = 0) : t = 0 := by
  obtain ⟨n, hn⟩ := (AddCircle.coe_eq_zero_iff (torusSide L m)).1 h
  obtain ⟨e, he⟩ : ∃ e : ℕ, (m : ℤ) + j = (e : ℤ) + 1 := ⟨((m : ℤ) + j - 1).toNat, by omega⟩
  have hL0 : (L : ℝ) ≠ 0 := by
    have : 0 < L := by omega
    exact_mod_cast this.ne'
  have hpowEq : (L : ℝ) ^ (e + 1) = (L : ℝ) ^ m * (L : ℝ) ^ j := by
    rw [← zpow_natCast, ← zpow_natCast, ← zpow_add₀ hL0]
    congr 1
    push_cast
    omega
  have hmesh : meshSize L j * (L : ℝ) ^ j = 1 := by
    rw [meshSize, zpow_neg]
    exact inv_mul_cancel₀ (zpow_ne_zero _ hL0)
  have hreal : (t : ℝ) = (n : ℝ) * (2 * (L : ℝ) ^ (e + 1)) := by
    rw [zsmul_eq_mul, torusSide] at hn
    calc (t : ℝ) = (t : ℝ) * meshSize L j * (L : ℝ) ^ j := by rw [mul_assoc, hmesh, mul_one]
      _ = (n : ℝ) * (2 * (L : ℝ) ^ m) * (L : ℝ) ^ j := by rw [hn]
      _ = (n : ℝ) * (2 * (L : ℝ) ^ (e + 1)) := by rw [hpowEq]; ring
  have hint : t = n * (2 * (L : ℤ) ^ (e + 1)) := by exact_mod_cast hreal
  by_contra hne
  have hn0 : n ≠ 0 := by
    rintro rfl
    exact hne (by simpa using hint)
  have hLz : (13 : ℤ) ≤ (L : ℤ) := by exact_mod_cast hL
  have hpow : (13 : ℤ) ≤ (L : ℤ) ^ (e + 1) := by
    calc (13 : ℤ) ≤ (L : ℤ) := hLz
      _ = (L : ℤ) ^ 1 := (pow_one _).symm
      _ ≤ (L : ℤ) ^ (e + 1) := pow_le_pow_right₀ (by omega) (by omega)
  have habs : 1 ≤ |n| := Int.one_le_abs hn0
  have hbig : (26 : ℤ) ≤ |t| := by
    rw [hint, abs_mul, abs_of_nonneg (by positivity : (0 : ℤ) ≤ 2 * (L : ℤ) ^ (e + 1))]
    nlinarith
  omega
noncomputable def signedStep (L m : ℕ) (j : ℤ) (μ : Fin 4) (σ : ℤ) : FourTorus L m :=
  fun ν => (((σ : ℝ) * meshSize L j * (Pi.single μ (1 : ℝ) : Fin 4 → ℝ) ν : ℝ) :
    AddCircle (torusSide L m))
theorem axisSignRepresents_iff {b : Bond L m j} {μ : Fin 4} {σ : ℤ} :
    AxisSignRepresents b μ σ ↔
      (b.target : FourTorus L m) - (b.source : FourTorus L m) = signedStep L m j μ σ :=
  Iff.rfl
theorem signedStep_one (μ : Fin 4) :
    signedStep L m j μ 1 = ((unitStep L m j μ : Site L m j) : FourTorus L m) := by
  funext ν
  by_cases h : ν = μ
  · subst h
    simp [signedStep, unitStep, pointOnAxis]
  · simp [signedStep, unitStep, pointOnAxis, Pi.single_eq_of_ne h]
theorem signedStep_neg (μ : Fin 4) (σ : ℤ) :
    signedStep L m j μ (-σ) = -signedStep L m j μ σ := by
  funext ν
  simp only [signedStep, Pi.neg_apply]
  rw [← AddCircle.coe_neg]
  congr 1
  push_cast
  ring
theorem signedStep_injective (hL : 13 ≤ L) (hj : -(m : ℤ) < j) {μ μ' : Fin 4} {σ σ' : ℤ}
    (hσ : σ = 1 ∨ σ = -1) (hσ' : σ' = 1 ∨ σ' = -1)
    (h : signedStep L m j μ σ = signedStep L m j μ' σ') : μ = μ' ∧ σ = σ' := by
  have hμ := congrFun h μ
  by_cases hax : μ = μ'
  · subst hax
    refine ⟨rfl, ?_⟩
    have hz : ((((σ - σ' : ℤ) : ℝ) * meshSize L j : ℝ) : AddCircle (torusSide L m)) = 0 := by
      push_cast
      rw [sub_mul, AddCircle.coe_sub, sub_eq_zero]
      simpa [signedStep] using hμ
    have ht : |σ - σ'| ≤ 2 := by
      rcases hσ with rfl | rfl <;> rcases hσ' with rfl | rfl <;> norm_num
    have := int_eq_zero_of_abs_le_two_of_coe_eq_zero hL hj ht hz
    omega
  · exfalso
    have hz : (((σ : ℝ) * meshSize L j : ℝ) : AddCircle (torusSide L m)) = 0 := by
      have h0 : signedStep L m j μ' σ' μ = 0 := by
        simp [signedStep, Pi.single_eq_of_ne hax]
      rw [h0] at hμ
      simpa [signedStep] using hμ
    have ht : |σ| ≤ 2 := by
      rcases hσ with rfl | rfl <;> norm_num
    have := int_eq_zero_of_abs_le_two_of_coe_eq_zero hL hj ht hz
    omega
theorem exists_axisSignRepresents (b : Bond L m j) :
    ∃ (μ : Fin 4) (σ : ℤ), (σ = 1 ∨ σ = -1) ∧ AxisSignRepresents b μ σ := by
  obtain ⟨μ, h | h⟩ := b.isNeighbour
  · refine ⟨μ, 1, Or.inl rfl, axisSignRepresents_iff.2 ?_⟩
    rw [signedStep_one, ← h]
    rfl
  · refine ⟨μ, -1, Or.inr rfl, axisSignRepresents_iff.2 ?_⟩
    rw [signedStep_neg, signedStep_one, ← neg_eq_iff_eq_neg.mpr h]
    simp
theorem axisSignRepresents_opposite {b : Bond L m j} {μ : Fin 4} {σ : ℤ}
    (h : AxisSignRepresents b μ σ) : AxisSignRepresents b.opposite μ (-σ) := by
  refine axisSignRepresents_iff.2 ?_
  rw [signedStep_neg, ← axisSignRepresents_iff.1 h]
  exact (neg_sub _ _).symm
theorem isPositivelyOriented_iff {b : Bond L m j} :
    b.IsPositivelyOriented ↔ ∃ μ, AxisSignRepresents b μ 1 := by
  constructor
  · rintro ⟨μ, h⟩
    refine ⟨μ, axisSignRepresents_iff.2 ?_⟩
    rw [signedStep_one, ← h]
    rfl
  · rintro ⟨μ, h⟩
    exact ⟨μ, Subtype.ext ((axisSignRepresents_iff.1 h).trans (signedStep_one μ))⟩
theorem opposite_opposite (b : Bond L m j) : b.opposite.opposite = b := by apply _root_.YangMills.SharedProofs.p1012 <;> assumption
theorem positive_xor_opposite_positive (hL : 13 ≤ L) (hj : -(m : ℤ) < j) (b : Bond L m j) :
    (b.IsPositivelyOriented ∧ ¬b.opposite.IsPositivelyOriented) ∨
      (b.opposite.IsPositivelyOriented ∧ ¬b.IsPositivelyOriented) := by
  obtain ⟨μ, σ, hσ, hp⟩ := exists_axisSignRepresents b
  have hr := axisSignRepresents_opposite hp
  rcases hσ with rfl | rfl
  · refine Or.inl ⟨isPositivelyOriented_iff.2 ⟨μ, hp⟩, fun hpos => ?_⟩
    obtain ⟨μ', h'⟩ := isPositivelyOriented_iff.1 hpos
    have := (signedStep_injective hL hj (Or.inl rfl) (Or.inr rfl)
      ((axisSignRepresents_iff.1 h').symm.trans (axisSignRepresents_iff.1 hr))).2
    omega
  · rw [neg_neg] at hr
    refine Or.inr ⟨isPositivelyOriented_iff.2 ⟨μ, hr⟩, fun hpos => ?_⟩
    obtain ⟨μ', h'⟩ := isPositivelyOriented_iff.1 hpos
    have := (signedStep_injective hL hj (Or.inl rfl) (Or.inr rfl)
      ((axisSignRepresents_iff.1 h').symm.trans (axisSignRepresents_iff.1 hp))).2
    omega
theorem det_eq_one_and_inv_mem {H : Set Matrices.ComplexMatrix2}
    (hH : H = compactGaugeGroup ∨ H = complexGaugeGroup) {X : Matrices.ComplexMatrix2}
    (hX : X ∈ H) : X.det = 1 ∧ X⁻¹ ∈ H := by
  rcases hH with rfl | rfl
  · obtain ⟨hu, hd⟩ := Matrix.mem_specialUnitaryGroup_iff.1 hX
    refine ⟨hd, ?_⟩
    rw [Matrix.inv_eq_right_inv (Matrix.mem_unitaryGroup_iff.1 hu)]
    refine Matrix.mem_specialUnitaryGroup_iff.2 ⟨Matrix.mem_unitaryGroup_iff.2 ?_, ?_⟩
    · rw [star_star]
      exact Matrix.mem_unitaryGroup_iff'.1 hu
    · rw [Matrix.star_eq_conjTranspose, Matrix.det_conjTranspose, hd, star_one]
  · have hd : X.det = 1 := hX
    refine ⟨hd, ?_⟩
    show X⁻¹.det = 1
    rw [Matrix.det_nonsing_inv, hd, Ring.inverse_one]
theorem inv_inv_of_mem_gaugeGroup {H : Set Matrices.ComplexMatrix2}
    (hH : H = compactGaugeGroup ∨ H = complexGaugeGroup) {X : Matrices.ComplexMatrix2}
    (hX : X ∈ H) : X⁻¹⁻¹ = X :=
  Matrix.nonsing_inv_nonsing_inv X ((det_eq_one_and_inv_mem hH hX).1 ▸ isUnit_one)
theorem bijOn_restrictToPositive (hL : 13 ≤ L) (hj : -(m : ℤ) < j) (ℬ : Set (Bond L m j))
    (H : Set Matrices.ComplexMatrix2) (hℬ : IsReversalClosed ℬ)
    (hH : H = compactGaugeGroup ∨ H = complexGaugeGroup) :
    Set.BijOn (restrictToPositive ℬ) (gaugeFieldsOn H ℬ) (familiesValuedIn H ℬ) := by
  classical
  have hrev : ∀ b : Bond L m j, ¬b.IsPositivelyOriented → b.opposite.IsPositivelyOriented :=
    fun b hb => by
      rcases positive_xor_opposite_positive hL hj b with h | h
      · exact absurd h.1 hb
      · exact h.1
  have hnot : ∀ b : Bond L m j, b.IsPositivelyOriented → ¬b.opposite.IsPositivelyOriented :=
    fun b hb => by
      rcases positive_xor_opposite_positive hL hj b with h | h
      · exact h.2
      · exact absurd hb h.2
  refine ⟨fun V hV => ?_, fun V hV V' hV' hEq => ?_, fun g hg => ?_⟩
  · obtain ⟨U, hU, hVU⟩ := hV
    show ∀ b, restrictToPositive ℬ V b ∈ H
    intro b
    show V ⟨b.1, b.2.1⟩ ∈ H
    rw [hVU]
    exact hU.1 _ b.2.1
  · obtain ⟨U, hU, hVU⟩ := hV
    obtain ⟨U', hU', hVU'⟩ := hV'
    have key : ∀ (c : Bond L m j) (hc : c ∈ positiveBonds ℬ), U c = U' c := fun c hc => by
      have := congrFun hEq ⟨c, hc⟩
      have e : V ⟨c, hc.1⟩ = V' ⟨c, hc.1⟩ := this
      rw [hVU, hVU'] at e
      exact e
    funext ⟨b, hb⟩
    rw [hVU, hVU']
    show U b = U' b
    by_cases hp : b.IsPositivelyOriented
    · exact key b ⟨hb, hp⟩
    · have e := key b.opposite ⟨hℬ b hb, hrev b hp⟩
      rw [hU.2 b hb, hU'.2 b hb] at e
      calc U b = (U b)⁻¹⁻¹ := (inv_inv_of_mem_gaugeGroup hH (hU.1 b hb)).symm
        _ = (U' b)⁻¹⁻¹ := by rw [e]
        _ = U' b := inv_inv_of_mem_gaugeGroup hH (hU'.1 b hb)
  · have hgH : ∀ b, g b ∈ H := hg
    let g' : Bond L m j → Matrices.ComplexMatrix2 :=
      fun b => if h : b ∈ positiveBonds ℬ then g ⟨b, h⟩ else 1
    have hg' : ∀ (b : Bond L m j) (h : b ∈ positiveBonds ℬ), g' b = g ⟨b, h⟩ :=
      fun b h => dif_pos h
    have hmem : ∀ b : Bond L m j, b ∈ positiveBonds ℬ → g' b ∈ H := fun b h => by
      rw [hg' b h]
      exact hgH _
    let U : Bond L m j → Matrices.ComplexMatrix2 :=
      fun b => if b.IsPositivelyOriented then g' b else (g' b.opposite)⁻¹
    have Upos : ∀ b : Bond L m j, b.IsPositivelyOriented → U b = g' b := fun b h => if_pos h
    have Uneg : ∀ b : Bond L m j, ¬b.IsPositivelyOriented → U b = (g' b.opposite)⁻¹ :=
      fun b h => if_neg h
    have hfield : IsGaugeField H ℬ U := by
      refine ⟨fun b hb => ?_, fun b hb => ?_⟩
      · by_cases hp : b.IsPositivelyOriented
        · rw [Upos b hp]
          exact hmem b ⟨hb, hp⟩
        · rw [Uneg b hp]
          exact (det_eq_one_and_inv_mem hH (hmem _ ⟨hℬ b hb, hrev b hp⟩)).2
      · by_cases hp : b.IsPositivelyOriented
        · rw [Uneg _ (hnot b hp), Upos b hp, opposite_opposite]
        · rw [Upos _ (hrev b hp), Uneg b hp,
            inv_inv_of_mem_gaugeGroup hH (hmem _ ⟨hℬ b hb, hrev b hp⟩)]
    refine ⟨fun b => U b, ⟨U, hfield, fun _ => rfl⟩, ?_⟩
    funext b
    show U b.1 = g b
    rw [Upos _ b.2.2, hg' _ b.2]
theorem oppositeAndPositiveRestriction_holds : OppositeAndPositiveRestriction := by
  intro s j hj
  have hL : 13 ≤ s.L := s.isAdmissible.2
  refine ⟨fun b => ⟨rfl, rfl, opposite_opposite b, ?_,
      fun μ σ _ h => axisSignRepresents_opposite h, ?_⟩,
    fun ℬ H hℬ hH => bijOn_restrictToPositive hL hj ℬ H hℬ hH⟩
  · obtain ⟨μ, σ, hσ, hp⟩ := exists_axisSignRepresents b
    refine ⟨(μ, σ), ⟨hσ, hp⟩, ?_⟩
    rintro ⟨μ', σ'⟩ ⟨hσ', hp'⟩
    obtain ⟨h1, h2⟩ := signedStep_injective hL hj hσ' hσ
      ((axisSignRepresents_iff.1 hp').symm.trans (axisSignRepresents_iff.1 hp))
    exact Prod.ext h1 h2
  · exact positive_xor_opposite_positive hL hj b
end YangMills.Construction.PeriodicLattice.OppositeBonds
