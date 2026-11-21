import YangMills.Construction.Lattice.WilsonActionAsAPlaquetteSumAndSymmetriesOfProductHaar
import YangMills.Construction.Measures.SubstitutionByAGroupElementTimesTheInversePreservesHaarMeasure
import YangMills.Construction.PeriodicLattice.WilsonMeasureIsometryInvarianceProof
import Mathlib
set_option autoImplicit false
open MeasureTheory
noncomputable section
namespace YangMills.Construction
namespace PeriodicLattice
namespace WilsonPlaquetteSum
variable {L m : ℕ}
theorem coe_inv_specialUnitary (g : Matrices.ComplexMatrix2.specialUnitary) :
    (g : Matrices.ComplexMatrix2)⁻¹ =
      ((g⁻¹ : Matrices.ComplexMatrix2.specialUnitary) : Matrices.ComplexMatrix2) := by
  apply Matrix.inv_eq_right_inv
  rw [← Submonoid.coe_mul, mul_inv_cancel, Submonoid.coe_one]
theorem siteCount_mul_meshSize (hL : 1 < L) (d : ℕ) :
    ((2 * L ^ (m + d) : ℕ) : ℝ) * meshSize L (d : ℤ) = torusSide L m := by
  simp only [meshSize, torusSide, zpow_neg, zpow_natCast]
  push_cast
  rw [pow_add]
  field_simp
theorem small_multiple_meshSize_ne_zero (hL : 1 < L) (hm : 0 < m) (d : ℕ) (c : ℤ)
    (hc : c = 1 ∨ c = 2) :
    (((c : ℝ) * meshSize L (d : ℤ) : ℝ) : AddCircle (torusSide L m)) ≠ 0 := by
  intro h
  obtain ⟨n, hn⟩ := (AddCircle.coe_eq_zero_iff _).mp h
  have hs : meshSize L (d : ℤ) ≠ 0 := by
    have : (0 : ℝ) < L := by exact_mod_cast (by omega : 0 < L)
    exact (zpow_pos this _).ne'
  rw [← siteCount_mul_meshSize (m := m) hL d, zsmul_eq_mul, ← mul_assoc] at hn
  have hr := mul_right_cancel₀ hs hn
  have hz : n * (2 * (L : ℤ) ^ (m + d)) = c := by exact_mod_cast hr
  have hK : 2 ≤ (L : ℤ) ^ (m + d) := by
    have h2 : 2 ≤ L ^ (m + d) :=
      le_trans hL (Nat.le_self_pow (by omega) L)
    exact_mod_cast h2
  rcases lt_trichotomy n 0 with hn0 | hn0 | hn0
  · have : n ≤ -1 := by omega
    rcases hc with rfl | rfl <;> nlinarith
  · subst hn0
    rcases hc with rfl | rfl <;> simp at hz
  · have : 1 ≤ n := by omega
    rcases hc with rfl | rfl <;> nlinarith
theorem not_positivelyOriented_and_opposite (hL : 1 < L) (hm : 0 < m) (d : ℕ)
    (b : Bond L m (d : ℤ))
    (h₁ : b.IsPositivelyOriented) (h₂ : b.opposite.IsPositivelyOriented) : False := by
  obtain ⟨μ, hμ⟩ := h₁
  obtain ⟨ν, hν⟩ := h₂
  change b.source - b.target = unitStep L m (d : ℤ) ν at hν
  have hsum : unitStep L m (d : ℤ) μ + unitStep L m (d : ℤ) ν = 0 := by
    rw [← hμ, ← hν]; abel
  have hcoord := congrFun (congrArg (Subtype.val) hsum) μ
  by_cases hνμ : ν = μ
  · subst hνμ
    refine small_multiple_meshSize_ne_zero hL hm d 2 (Or.inr rfl) ?_
    have : (((2 : ℤ) : ℝ) * meshSize L (d : ℤ) : ℝ) =
        meshSize L (d : ℤ) + meshSize L (d : ℤ) := by
      push_cast; ring
    rw [this, AddCircle.coe_add]
    simpa [unitStep, pointOnAxis] using hcoord
  · refine small_multiple_meshSize_ne_zero hL hm d 1 (Or.inl rfl) ?_
    have hne : μ ≠ ν := fun h => hνμ h.symm
    simpa [unitStep, pointOnAxis, Pi.single_eq_of_ne hne] using hcoord
theorem finite_site (hL : 1 < L) (d : ℕ) : Finite (Site L m (d : ℤ)) := by
  obtain ⟨N, hN⟩ : ∃ N : ℕ, N = 2 * L ^ (m + d) := ⟨_, rfl⟩
  have hsp : (N : ℝ) * meshSize L (d : ℤ) = torusSide L m := by
    rw [hN]; exact siteCount_mul_meshSize hL d
  have hN0 : 0 < N := by
    rw [hN]; exact Nat.mul_pos (by omega) (Nat.pow_pos (by omega))
  have hNi : (0 : ℤ) < N := by exact_mod_cast hN0
  let f : (Fin 4 → Fin N) → Site L m (d : ℤ) := fun r =>
    ⟨fun μ => (((((r μ : ℕ) : ℤ) : ℝ) * meshSize L (d : ℤ) : ℝ) : AddCircle (torusSide L m)),
      ⟨fun μ => ((r μ : ℕ) : ℤ), fun _ => rfl⟩⟩
  refine Finite.of_surjective f ?_
  rintro ⟨x, n, hn⟩
  refine ⟨fun μ => ⟨(n μ % (N : ℤ)).toNat, ?_⟩, ?_⟩
  · have h1 := Int.emod_lt_of_pos (n μ) hNi
    have h2 := Int.emod_nonneg (n μ) hNi.ne'
    omega
  · apply Subtype.ext
    funext μ
    change (((((((n μ % (N : ℤ)).toNat : ℕ) : ℤ) : ℝ) * meshSize L (d : ℤ) : ℝ)) :
      AddCircle (torusSide L m)) = x μ
    rw [hn μ, Int.toNat_of_nonneg (Int.emod_nonneg _ hNi.ne')]
    have hdiv : (n μ : ℝ) =
        ((n μ % (N : ℤ) : ℤ) : ℝ) + (N : ℝ) * ((n μ / (N : ℤ) : ℤ) : ℝ) := by
      exact_mod_cast (Int.emod_add_mul_ediv (n μ) (N : ℤ)).symm
    have hq : (n μ : ℝ) * meshSize L (d : ℤ) =
        ((n μ % (N : ℤ) : ℤ) : ℝ) * meshSize L (d : ℤ) + (n μ / (N : ℤ)) • torusSide L m := by
      rw [zsmul_eq_mul, ← hsp]
      conv_lhs => rw [hdiv]
      ring
    have hz : (((n μ / (N : ℤ)) • torusSide L m : ℝ) : AddCircle (torusSide L m)) = 0 :=
      (AddCircle.coe_eq_zero_iff _).mpr ⟨_, rfl⟩
    rw [hq, AddCircle.coe_add, hz, add_zero]
theorem finite_plaquette (hL : 1 < L) (d : ℕ) : Finite (Plaquette L m (d : ℤ)) := by
  have := finite_site (m := m) hL d
  refine Finite.of_injective
    (fun p : Plaquette L m (d : ℤ) => (p.origin, p.firstAxis, p.secondAxis)) ?_
  intro p q h
  simp only [Prod.mk.injEq] at h
  exact Plaquette.ext h.1 h.2.1 h.2.2
theorem wilsonPlaquetteFunction_inv (g : Matrices.ComplexMatrix2)
    (hg : g ∈ Matrices.ComplexMatrix2.specialUnitary) :
    wilsonPlaquetteFunction g⁻¹ = wilsonPlaquetteFunction g := by
  have h : g⁻¹ = star g := Matrix.inv_eq_right_inv
    (Matrix.mem_unitaryGroup_iff.mp (Matrix.specialUnitaryGroup_le_unitaryGroup hg))
  unfold wilsonPlaquetteFunction
  simp only [Matrices.ComplexMatrix2.fullTrace]
  rw [h, Matrix.star_eq_conjTranspose, Matrix.trace_conjTranspose]
  simp
theorem wilsonPlaquetteFunction_conj (g h : Matrices.ComplexMatrix2)
    (hh : h ∈ Matrices.ComplexMatrix2.specialUnitary) :
    wilsonPlaquetteFunction (h * g * h⁻¹) = wilsonPlaquetteFunction g := by
  have hd : IsUnit h.det := by
    rw [(Matrix.mem_specialUnitaryGroup_iff.mp hh).2]
    exact isUnit_one
  have hm : h⁻¹ * h = 1 := Matrix.nonsing_inv_mul _ hd
  unfold wilsonPlaquetteFunction
  simp only [Matrices.ComplexMatrix2.fullTrace]
  rw [Matrix.trace_mul_cycle, hm, one_mul]
variable {j : ℤ}
theorem positivelyOriented_or_opposite (b : Bond L m j) :
    b.IsPositivelyOriented ∨ b.opposite.IsPositivelyOriented := by apply _root_.YangMills.SharedProofs.p7155 <;> assumption
theorem opposite_opposite (b : Bond L m j) : b.opposite.opposite = b := Bond.ext rfl rfl
def orientedRep (b : Bond L m j) : PositivelyOrientedBond L m j :=
  open Classical in
  if h : b.IsPositivelyOriented then ⟨b, h⟩
  else ⟨b.opposite, (positivelyOriented_or_opposite b).resolve_left h⟩
theorem orientedRep_val (b : Bond L m j) :
    (orientedRep b).1 = b ∨ (orientedRep b).1 = b.opposite := by
  unfold orientedRep
  split_ifs <;> simp
theorem orientedRep_of_positivelyOriented (p : PositivelyOrientedBond L m j) :
    orientedRep p.1 = p := by
  unfold orientedRep
  rw [dif_pos p.2]
theorem orientedRep_opposite
    (hExcl : ∀ b : Bond L m j, b.IsPositivelyOriented → ¬ b.opposite.IsPositivelyOriented)
    (p : PositivelyOrientedBond L m j) : orientedRep p.1.opposite = p := by
  unfold orientedRep
  rw [dif_neg (hExcl _ p.2)]
  exact Subtype.ext (opposite_opposite _)
def inducedMap (τ : Bond L m j ≃ Bond L m j) (p : PositivelyOrientedBond L m j) :
    PositivelyOrientedBond L m j :=
  orientedRep (τ p.1)
theorem symm_opposite (τ : Bond L m j ≃ Bond L m j)
    (hτ : ∀ b, τ b.opposite = (τ b).opposite)
    (b : Bond L m j) : τ.symm b.opposite = (τ.symm b).opposite := by
  apply τ.injective
  rw [hτ, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
theorem inducedMap_symm_inducedMap
    (hExcl : ∀ b : Bond L m j, b.IsPositivelyOriented → ¬ b.opposite.IsPositivelyOriented)
    (τ : Bond L m j ≃ Bond L m j) (hτ : ∀ b, τ b.opposite = (τ b).opposite)
    (p : PositivelyOrientedBond L m j) : inducedMap τ.symm (inducedMap τ p) = p := by
  unfold inducedMap
  rcases orientedRep_val (τ p.1) with h | h
  · rw [h, Equiv.symm_apply_apply]
    exact orientedRep_of_positivelyOriented p
  · rw [h, symm_opposite τ hτ, Equiv.symm_apply_apply]
    exact orientedRep_opposite hExcl p
def inducedEquiv
    (hExcl : ∀ b : Bond L m j, b.IsPositivelyOriented → ¬ b.opposite.IsPositivelyOriented)
    (τ : Bond L m j ≃ Bond L m j) (hτ : ∀ b, τ b.opposite = (τ b).opposite) :
    PositivelyOrientedBond L m j ≃ PositivelyOrientedBond L m j where
  toFun := inducedMap τ
  invFun := inducedMap τ.symm
  left_inv := inducedMap_symm_inducedMap hExcl τ hτ
  right_inv := inducedMap_symm_inducedMap hExcl τ.symm (symm_opposite τ hτ)
theorem haarPi_map_reindex {ι : Type} [Countable ι] (e : ι ≃ ι) :
    (Matrices.ComplexMatrix2.haarPi ι).map (fun v p => v (e p)) =
      Matrices.ComplexMatrix2.haarPi ι := by
  have h := Measure.infinitePi_map_piCongrLeft
    (μ := fun _ : ι => Matrices.ComplexMatrix2.haarProb) e.symm
  have hfun : (fun (v : ι → Matrices.ComplexMatrix2.specialUnitary) p => v (e p)) =
      ⇑(MeasurableEquiv.piCongrLeft
        (fun _ : ι => Matrices.ComplexMatrix2.specialUnitary) e.symm) := by
    funext v p
    rw [MeasurableEquiv.coe_piCongrLeft]
    obtain ⟨a, rfl⟩ := e.symm.surjective p
    rw [Equiv.piCongrLeft_apply_apply]
    simp
  rw [hfun]
  exact h
theorem haarPi_map_pointwise {ι : Type} [Countable ι]
    (f : ι → Matrices.ComplexMatrix2.specialUnitary → Matrices.ComplexMatrix2.specialUnitary)
    (hf : ∀ i, Measurable (f i))
    (hm : ∀ i, Matrices.ComplexMatrix2.haarProb.map (f i) = Matrices.ComplexMatrix2.haarProb) :
    (Matrices.ComplexMatrix2.haarPi ι).map (fun v i => f i (v i)) =
      Matrices.ComplexMatrix2.haarPi ι := by
  unfold Matrices.ComplexMatrix2.haarPi
  rw [Measure.infinitePi_map_pi _ hf]
  simp only [hm]
theorem gaugeFieldOfPositive_apply_positivelyOriented
    (v : PositivelyOrientedBond L m j → Matrices.ComplexMatrix2.specialUnitary)
    (p : PositivelyOrientedBond L m j) :
    gaugeFieldOfPositive v p.1 = (v p : Matrices.ComplexMatrix2) := by
  unfold gaugeFieldOfPositive
  rw [dif_pos p.2]
theorem gaugeFieldOfPositive_apply_opposite
    (hExcl : ∀ b : Bond L m j, b.IsPositivelyOriented → ¬ b.opposite.IsPositivelyOriented)
    (v : PositivelyOrientedBond L m j → Matrices.ComplexMatrix2.specialUnitary)
    (p : PositivelyOrientedBond L m j) :
    gaugeFieldOfPositive v p.1.opposite =
      (((v p)⁻¹ : Matrices.ComplexMatrix2.specialUnitary) : Matrices.ComplexMatrix2) := by
  unfold gaugeFieldOfPositive
  rw [dif_neg (hExcl _ p.2),
    dif_pos (show p.1.opposite.opposite.IsPositivelyOriented from p.2)]
  exact coe_inv_specialUnitary (v p)
theorem measurable_gaugeFieldOfPositive :
    Measurable (gaugeFieldOfPositive (L := L) (m := m) (j := j)) := by apply _root_.YangMills.Construction.PeriodicLattice.IsometryInvariance.measurable_gaugeFieldOfPositive <;> assumption
def orientationCorrection (τ : Bond L m j ≃ Bond L m j) (p : PositivelyOrientedBond L m j) :
    Matrices.ComplexMatrix2.specialUnitary → Matrices.ComplexMatrix2.specialUnitary :=
  open Classical in if (τ p.1).IsPositivelyOriented then id else Inv.inv
def inducedValues
    (hExcl : ∀ b : Bond L m j, b.IsPositivelyOriented → ¬ b.opposite.IsPositivelyOriented)
    (τ : Bond L m j ≃ Bond L m j) (hτ : ∀ b, τ b.opposite = (τ b).opposite)
    (v : PositivelyOrientedBond L m j → Matrices.ComplexMatrix2.specialUnitary)
    (p : PositivelyOrientedBond L m j) : Matrices.ComplexMatrix2.specialUnitary :=
  orientationCorrection τ p (v (inducedEquiv hExcl τ hτ p))
theorem gaugeFieldOfPositive_apply_image
    (hExcl : ∀ b : Bond L m j, b.IsPositivelyOriented → ¬ b.opposite.IsPositivelyOriented)
    (τ : Bond L m j ≃ Bond L m j) (hτ : ∀ b, τ b.opposite = (τ b).opposite)
    (v : PositivelyOrientedBond L m j → Matrices.ComplexMatrix2.specialUnitary)
    (p : PositivelyOrientedBond L m j) :
    gaugeFieldOfPositive v (τ p.1) =
      (inducedValues hExcl τ hτ v p : Matrices.ComplexMatrix2) := by
  have hval : inducedValues hExcl τ hτ v p =
      orientationCorrection τ p (v (orientedRep (τ p.1))) := rfl
  rw [hval]
  by_cases h : (τ p.1).IsPositivelyOriented
  · have h1 := gaugeFieldOfPositive_apply_positivelyOriented v ⟨τ p.1, h⟩
    change gaugeFieldOfPositive v (τ p.1) = _ at h1
    rw [h1]
    simp only [orientationCorrection, if_pos h, id, orientedRep, dif_pos h]
  · have hr := (positivelyOriented_or_opposite (τ p.1)).resolve_left h
    have h2 := gaugeFieldOfPositive_apply_opposite hExcl v ⟨(τ p.1).opposite, hr⟩
    change gaugeFieldOfPositive v (τ p.1) = _ at h2
    rw [h2]
    simp only [orientationCorrection, if_neg h, orientedRep, dif_neg h]
theorem gaugeFieldOfPositive_opposite
    (hExcl : ∀ b : Bond L m j, b.IsPositivelyOriented → ¬ b.opposite.IsPositivelyOriented)
    (v : PositivelyOrientedBond L m j → Matrices.ComplexMatrix2.specialUnitary)
    (b : Bond L m j) :
    gaugeFieldOfPositive v b.opposite = (gaugeFieldOfPositive v b)⁻¹ := by
  rcases positivelyOriented_or_opposite b with h | h
  · have h1 := gaugeFieldOfPositive_apply_opposite hExcl v ⟨b, h⟩
    have h2 := gaugeFieldOfPositive_apply_positivelyOriented v ⟨b, h⟩
    change gaugeFieldOfPositive v b.opposite = _ at h1
    change gaugeFieldOfPositive v b = _ at h2
    rw [h1, h2, coe_inv_specialUnitary]
  · have h1 := gaugeFieldOfPositive_apply_positivelyOriented v ⟨b.opposite, h⟩
    have h2 := gaugeFieldOfPositive_apply_opposite hExcl v ⟨b.opposite, h⟩
    change gaugeFieldOfPositive v b.opposite = _ at h1
    change gaugeFieldOfPositive v b = _ at h2
    rw [h1, h2, coe_inv_specialUnitary, inv_inv]
theorem gaugeFieldOfPositive_comp
    (hExcl : ∀ b : Bond L m j, b.IsPositivelyOriented → ¬ b.opposite.IsPositivelyOriented)
    (τ : Bond L m j ≃ Bond L m j) (hτ : ∀ b, τ b.opposite = (τ b).opposite)
    (v : PositivelyOrientedBond L m j → Matrices.ComplexMatrix2.specialUnitary) :
    gaugeFieldOfPositive v ∘ τ = gaugeFieldOfPositive (inducedValues hExcl τ hτ v) := by
  have onPositive : ∀ p : PositivelyOrientedBond L m j,
      gaugeFieldOfPositive v (τ p.1) =
        gaugeFieldOfPositive (inducedValues hExcl τ hτ v) p.1 := fun p => by
    rw [gaugeFieldOfPositive_apply_image hExcl τ hτ v p,
      gaugeFieldOfPositive_apply_positivelyOriented]
  funext b
  change gaugeFieldOfPositive v (τ b) = _
  rcases positivelyOriented_or_opposite b with h | h
  · exact onPositive ⟨b, h⟩
  · have hb : τ b = (τ b.opposite).opposite := by
      have := hτ b.opposite
      rwa [opposite_opposite] at this
    have hp := onPositive ⟨b.opposite, h⟩
    change gaugeFieldOfPositive v (τ b.opposite) =
      gaugeFieldOfPositive (inducedValues hExcl τ hτ v) b.opposite at hp
    rw [hb, gaugeFieldOfPositive_opposite hExcl, hp, ← gaugeFieldOfPositive_opposite hExcl,
      opposite_opposite]
theorem measurable_and_map_inducedValues
    (hInv : Matrices.ComplexMatrix2.haarProb.map
      (fun u : Matrices.ComplexMatrix2.specialUnitary => u⁻¹) = Matrices.ComplexMatrix2.haarProb)
    (hExcl : ∀ b : Bond L m j, b.IsPositivelyOriented → ¬ b.opposite.IsPositivelyOriented)
    (τ : Bond L m j ≃ Bond L m j) (hτ : ∀ b, τ b.opposite = (τ b).opposite) :
    Measurable (inducedValues hExcl τ hτ) ∧
      (gaugeFieldHaar L m j).map (inducedValues hExcl τ hτ) = gaugeFieldHaar L m j := by
  have hf : ∀ p, Measurable (orientationCorrection τ p) := fun p => by
    unfold orientationCorrection
    split_ifs
    · exact measurable_id
    · exact measurable_inv
  have hm : ∀ p, Matrices.ComplexMatrix2.haarProb.map (orientationCorrection τ p) =
      Matrices.ComplexMatrix2.haarProb := fun p => by
    unfold orientationCorrection
    split_ifs
    · exact Measure.map_id
    · exact hInv
  have hr : Measurable (fun (v : PositivelyOrientedBond L m j →
      Matrices.ComplexMatrix2.specialUnitary) p => v (inducedEquiv hExcl τ hτ p)) :=
    measurable_pi_lambda _ fun p => measurable_pi_apply _
  have hs : Measurable (fun (v : PositivelyOrientedBond L m j →
      Matrices.ComplexMatrix2.specialUnitary) p => orientationCorrection τ p (v p)) :=
    measurable_pi_lambda _ fun p => (hf p).comp (measurable_pi_apply _)
  have hcomp : inducedValues hExcl τ hτ =
      (fun (v : PositivelyOrientedBond L m j → Matrices.ComplexMatrix2.specialUnitary) p =>
          orientationCorrection τ p (v p)) ∘
        (fun (v : PositivelyOrientedBond L m j → Matrices.ComplexMatrix2.specialUnitary) p =>
          v (inducedEquiv hExcl τ hτ p)) := rfl
  refine ⟨hcomp ▸ hs.comp hr, ?_⟩
  rw [hcomp]
  unfold gaugeFieldHaar
  rw [← Measure.map_map hs hr, haarPi_map_reindex, haarPi_map_pointwise _ hf hm]
theorem productHaarMeasure_map_comp
    (hInv : Matrices.ComplexMatrix2.haarProb.map
      (fun u : Matrices.ComplexMatrix2.specialUnitary => u⁻¹) = Matrices.ComplexMatrix2.haarProb)
    (hExcl : ∀ b : Bond L m j, b.IsPositivelyOriented → ¬ b.opposite.IsPositivelyOriented)
    (τ : Bond L m j ≃ Bond L m j) (hτ : ∀ b, τ b.opposite = (τ b).opposite) :
    (productHaarMeasure L m j).map (fun U => U ∘ τ) = productHaarMeasure L m j := by
  obtain ⟨hT, hmap⟩ := measurable_and_map_inducedValues hInv hExcl τ hτ
  have hC := measurable_gaugeFieldOfPositive (L := L) (m := m) (j := j)
  have hU : Measurable (fun U : Bond L m j → Matrices.ComplexMatrix2 => U ∘ τ) :=
    measurable_pi_lambda _ fun b => measurable_pi_apply _
  have hcomp : (fun U : Bond L m j → Matrices.ComplexMatrix2 => U ∘ τ) ∘ gaugeFieldOfPositive =
      gaugeFieldOfPositive ∘ inducedValues hExcl τ hτ := by
    funext v
    exact gaugeFieldOfPositive_comp hExcl τ hτ v
  unfold productHaarMeasure
  rw [Measure.map_map hU hC, hcomp, ← Measure.map_map hC hT, hmap]
theorem wilsonPlaquetteSumAndHaarSymmetry_holds
    (hsub : Measures.HaarMapMulInvEq) : WilsonActionPlaquetteSumAndHaarSymmetry := by
  intro L m j hL hm hj
  obtain ⟨d, rfl⟩ := Int.eq_ofNat_of_zero_le hj
  have hInv : Matrices.ComplexMatrix2.haarProb.map
      (fun u : Matrices.ComplexMatrix2.specialUnitary => u⁻¹) =
        Matrices.ComplexMatrix2.haarProb := by
    simpa using hsub 1
  exact ⟨fun g hg => ⟨wilsonPlaquetteFunction_inv g hg,
      fun h hh => wilsonPlaquetteFunction_conj g h hh⟩,
    finite_plaquette hL d, fun U => rfl, fun τ hτ =>
      productHaarMeasure_map_comp hInv
        (fun b h₁ h₂ => not_positivelyOriented_and_opposite hL hm d b h₁ h₂) τ hτ⟩
end WilsonPlaquetteSum
end PeriodicLattice
end YangMills.Construction
