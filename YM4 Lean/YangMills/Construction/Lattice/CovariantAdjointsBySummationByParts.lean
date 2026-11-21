import YangMills.Construction.Lattice.CovariantAdjointFormulas
import YangMills.Construction.Lattice.GaugeCovarianceOfHolonomy
import YangMills.Construction.Matrices.OperatorNormUnderConjugation
import Mathlib
open Set
open scoped Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction
open Matrices
namespace PeriodicLattice
namespace TransposeFormulas
variable {L m : ℕ} {j : ℤ}
private theorem one_lt_base (hL : 13 ≤ L) : (1 : ℝ) < L := by
  have : (13 : ℝ) ≤ L := by exact_mod_cast hL
  linarith
abbrev _root_.YangMills.SharedProofs.p15248 := @one_lt_base
private theorem meshSize_pos (hL : 13 ≤ L) : 0 < meshSize L j :=
  zpow_pos (by linarith [one_lt_base hL]) _
private theorem two_meshSize_lt_torusSide (hL : 13 ≤ L) (hj : -(m : ℤ) < j) :
    2 * meshSize L j < torusSide L m := by
  have h : meshSize L j < (L : ℝ) ^ m := by
    unfold meshSize
    rw [← zpow_natCast]
    exact zpow_lt_zpow_right₀ (one_lt_base hL) (by omega)
  unfold torusSide
  linarith
abbrev _root_.YangMills.SharedProofs.p8012 := @two_meshSize_lt_torusSide
private theorem addCircle_coe_ne_zero {t : ℝ} (h₀ : 0 < t) (h₁ : t < torusSide L m)
    (_hp : 0 < torusSide L m) : (t : AddCircle (torusSide L m)) ≠ 0 := by
  intro h
  obtain ⟨n, hn⟩ := (AddCircle.coe_eq_zero_iff (torusSide L m)).1 h
  rw [zsmul_eq_mul] at hn
  rcases le_or_gt n 0 with h' | h'
  · have : (n : ℝ) ≤ 0 := by exact_mod_cast h'
    nlinarith
  · have : (1 : ℝ) ≤ n := by exact_mod_cast h'
    nlinarith
private theorem unitStep_apply_self (μ : Fin 4) :
    ((unitStep L m j μ : Site L m j) : FourTorus L m) μ =
      (meshSize L j : AddCircle (torusSide L m)) := by
  simp [unitStep, pointOnAxis]
abbrev _root_.YangMills.SharedProofs.p39116 := @unitStep_apply_self
private theorem unitStep_apply_of_ne {μ ν : Fin 4} (h : μ ≠ ν) :
    ((unitStep L m j ν : Site L m j) : FourTorus L m) μ = 0 := by
  simp [unitStep, pointOnAxis, Pi.single_eq_of_ne h]
private theorem torusSide_pos (hL : 13 ≤ L) : 0 < torusSide L m := by
  have : (0 : ℝ) < L := by linarith [one_lt_base hL]
  unfold torusSide
  positivity
abbrev _root_.YangMills.SharedProofs.p14627 := @torusSide_pos
private theorem unitStep_injective (hL : 13 ≤ L) (hj : -(m : ℤ) < j) {μ ν : Fin 4}
    (h : unitStep L m j μ = unitStep L m j ν) : μ = ν := by
  by_contra hne
  have h₁ := congrArg (fun s : Site L m j => (s : FourTorus L m) μ) h
  simp only [unitStep_apply_self, unitStep_apply_of_ne hne] at h₁
  have hp := meshSize_pos (j := j) hL
  exact addCircle_coe_ne_zero hp (by linarith [two_meshSize_lt_torusSide hL hj])
    (torusSide_pos hL) h₁
private theorem unitStep_ne_neg (hL : 13 ≤ L) (hj : -(m : ℤ) < j) (μ ν : Fin 4) :
    unitStep L m j μ ≠ -unitStep L m j ν := by
  intro h
  have hp := meshSize_pos (j := j) hL
  have hlt := two_meshSize_lt_torusSide hL hj
  have h₁ := congrArg (fun s : Site L m j => (s : FourTorus L m) μ) h
  by_cases hne : μ = ν
  · subst hne
    simp only [AddSubgroup.coe_neg, Pi.neg_apply, unitStep_apply_self] at h₁
    have h₂ : (((2 * meshSize L j : ℝ)) : AddCircle (torusSide L m)) = 0 := by
      rw [two_mul, AddCircle.coe_add]
      nth_rewrite 1 [h₁]
      simp
    exact addCircle_coe_ne_zero (by linarith) hlt (torusSide_pos hL) h₂
  · simp only [AddSubgroup.coe_neg, Pi.neg_apply, unitStep_apply_self,
      unitStep_apply_of_ne hne, neg_zero] at h₁
    exact addCircle_coe_ne_zero hp (by linarith) (torusSide_pos hL) h₁
abbrev _root_.YangMills.SharedProofs.p70 := @unitStep_ne_neg
private theorem forwardFrom_isPositivelyOriented (x : Site L m j) (μ : Fin 4) :
    (Bond.forwardFrom x μ).IsPositivelyOriented :=
  ⟨μ, by simp [Bond.forwardFrom]⟩
private theorem opposite_opposite (b : Bond L m j) : b.opposite.opposite = b := rfl
abbrev _root_.YangMills.SharedProofs.p1012 := @opposite_opposite
private theorem axis_eq_of_step (hL : 13 ≤ L) (hj : -(m : ℤ) < j) {b : Bond L m j}
    {μ : Fin 4} (h : b.target - b.source = unitStep L m j μ) : b.axis = μ := by
  rcases b.isNeighbour.choose_spec with h' | h'
  · exact unitStep_injective hL hj (h'.symm.trans h)
  · exact absurd (h.symm.trans h') (unitStep_ne_neg hL hj _ _)
private theorem axis_forwardFrom (hL : 13 ≤ L) (hj : -(m : ℤ) < j) (x : Site L m j)
    (μ : Fin 4) : (Bond.forwardFrom x μ).axis = μ :=
  axis_eq_of_step hL hj (by simp [Bond.forwardFrom])
private theorem eq_forwardFrom (hL : 13 ≤ L) (hj : -(m : ℤ) < j) {b : Bond L m j}
    (hb : b.IsPositivelyOriented) : b = Bond.forwardFrom b.source b.axis := by
  obtain ⟨μ, hμ⟩ := hb
  rw [axis_eq_of_step hL hj hμ]
  refine Bond.ext rfl ?_
  show b.target = b.source + unitStep L m j μ
  rw [← hμ]
  abel
private theorem not_opposite_positive (hL : 13 ≤ L) (hj : -(m : ℤ) < j) {b : Bond L m j}
    (hb : b.IsPositivelyOriented) : ¬ b.opposite.IsPositivelyOriented := by
  obtain ⟨μ, hμ⟩ := hb
  rintro ⟨ν, hν⟩
  refine unitStep_ne_neg hL hj μ ν ?_
  rw [← hμ, ← hν]
  show b.target - b.source = -(b.source - b.target)
  abel
private theorem positive_or_opposite_positive (b : Bond L m j) :
    b.IsPositivelyOriented ∨ b.opposite.IsPositivelyOriented := by
  obtain ⟨μ, h | h⟩ := b.isNeighbour
  · exact Or.inl ⟨μ, h⟩
  · refine Or.inr ⟨μ, ?_⟩
    show b.source - b.target = unitStep L m j μ
    rw [← neg_sub, h, neg_neg]
abbrev _root_.YangMills.SharedProofs.p7155 := @positive_or_opposite_positive
private theorem forwardFrom_injective (hL : 13 ≤ L) (hj : -(m : ℤ) < j) {x y : Site L m j}
    {μ ν : Fin 4} (h : Bond.forwardFrom y ν = Bond.forwardFrom x μ) : y = x ∧ ν = μ := by
  have h₁ : y = x := congrArg Bond.source h
  subst h₁
  have h₂ : y + unitStep L m j ν = y + unitStep L m j μ := congrArg Bond.target h
  exact ⟨rfl, unitStep_injective hL hj (add_left_cancel h₂)⟩
private theorem bondFormOfPositive_apply_pos (a : Bond L m j → ComplexMatrix2) {b : Bond L m j}
    (hb : b.IsPositivelyOriented) : bondFormOfPositive a b = a b := by
  simp [bondFormOfPositive, hb]
private theorem bondFormOfPositive_apply_not_pos (a : Bond L m j → ComplexMatrix2)
    {b : Bond L m j} (hb : ¬ b.IsPositivelyOriented) :
    bondFormOfPositive a b = -a b.opposite := by
  simp [bondFormOfPositive, hb]
private theorem bondFormOfPositive_opposite (hL : 13 ≤ L) (hj : -(m : ℤ) < j)
    (a : Bond L m j → ComplexMatrix2) (b : Bond L m j) :
    bondFormOfPositive a b.opposite = -bondFormOfPositive a b := by
  by_cases hb : b.IsPositivelyOriented
  · rw [bondFormOfPositive_apply_not_pos a (not_opposite_positive hL hj hb), opposite_opposite,
      bondFormOfPositive_apply_pos a hb]
  · have hr : b.opposite.IsPositivelyOriented :=
      (positive_or_opposite_positive b).resolve_left hb
    rw [bondFormOfPositive_apply_pos a hr, bondFormOfPositive_apply_not_pos a hb, neg_neg]
private theorem bondFormOfPositive_forwardFrom (a : Bond L m j → ComplexMatrix2)
    (x : Site L m j) (μ : Fin 4) :
    bondFormOfPositive a (Bond.forwardFrom x μ) = a (Bond.forwardFrom x μ) :=
  bondFormOfPositive_apply_pos a (forwardFrom_isPositivelyOriented x μ)
private theorem isBondForm_bondFormOfPositive (hL : 13 ≤ L) (hj : -(m : ℤ) < j)
    {𝔥 : Set ComplexMatrix2} {a : Bond L m j → ComplexMatrix2}
    (h : ∀ b : Bond L m j, b.IsPositivelyOriented → a b ∈ 𝔥) :
    IsBondForm 𝔥 (bondFormOfPositive a) :=
  ⟨fun b hb => by rw [bondFormOfPositive_apply_pos a hb]; exact h b hb,
    bondFormOfPositive_opposite hL hj a⟩
private theorem site_finite (hL : 13 ≤ L) (hj : -(m : ℤ) < j) : Finite (Site L m j) := by
  obtain ⟨d, hd⟩ := Int.eq_ofNat_of_zero_le (show 0 ≤ (m : ℤ) + j by omega)
  have hLne : (L : ℝ) ≠ 0 := by linarith [one_lt_base hL]
  set N : ℤ := 2 * (L : ℤ) ^ d with hN
  have hNpos : 0 < N := by
    have : 0 < (L : ℤ) := by omega
    positivity
  have hNs : (N : ℝ) * meshSize L j = torusSide L m := by
    have h₁ : (L : ℝ) ^ d * (L : ℝ) ^ (-j) = (L : ℝ) ^ m := by
      rw [← zpow_natCast (L : ℝ) d, ← zpow_add₀ hLne, ← zpow_natCast (L : ℝ) m]
      congr 1
      omega
    simp only [hN, meshSize, torusSide]
    push_cast
    rw [mul_assoc, h₁]
  let f : (Fin 4 → ↥(Set.Ico (0 : ℤ) N)) → Site L m j := fun n =>
    ⟨fun μ => ((((n μ : ℤ) : ℝ) * meshSize L j : ℝ) : AddCircle (torusSide L m)),
      ⟨fun μ => (n μ : ℤ), fun _ => rfl⟩⟩
  refine Finite.of_surjective f ?_
  rintro ⟨x, n, hn⟩
  refine ⟨fun μ => ⟨n μ % N, Int.emod_nonneg _ hNpos.ne', Int.emod_lt_of_pos _ hNpos⟩, ?_⟩
  refine Subtype.ext (funext fun μ => ?_)
  show ((((n μ % N : ℤ) : ℝ) * meshSize L j : ℝ) : AddCircle (torusSide L m)) = x μ
  rw [hn μ]
  have h₂ : ((n μ : ℤ) : ℝ) * meshSize L j =
      ((n μ % N : ℤ) : ℝ) * meshSize L j + ((n μ / N : ℤ)) • torusSide L m := by
    rw [zsmul_eq_mul, ← hNs]
    have h₃ : ((n μ : ℤ) : ℝ) = ((n μ % N : ℤ) : ℝ) + (N : ℝ) * ((n μ / N : ℤ) : ℝ) := by
      exact_mod_cast (Int.emod_add_mul_ediv (n μ) N).symm
    rw [h₃]
    ring
  rw [h₂, AddCircle.coe_add]
  have h₄ : (((n μ / N : ℤ) • torusSide L m : ℝ) : AddCircle (torusSide L m)) = 0 :=
    (AddCircle.coe_eq_zero_iff (torusSide L m)).2 ⟨_, rfl⟩
  rw [h₄, add_zero]
private theorem bond_finite [Finite (Site L m j)] : Finite (Bond L m j) :=
  Finite.of_injective (fun b : Bond L m j => (b.source, b.target)) fun _ _ h =>
    Bond.ext (congrArg Prod.fst h) (congrArg Prod.snd h)
abbrev _root_.YangMills.SharedProofs.p19159 := @bond_finite
private theorem conj_sub (V A B : ComplexMatrix2) :
    ComplexMatrix2.conjugateBy V (A - B) =
      ComplexMatrix2.conjugateBy V A - ComplexMatrix2.conjugateBy V B := by
  simp [ComplexMatrix2.conjugateBy, Matrix.mul_sub, Matrix.sub_mul]
private theorem conj_neg (V A : ComplexMatrix2) :
    ComplexMatrix2.conjugateBy V (-A) = -ComplexMatrix2.conjugateBy V A := by
  simp [ComplexMatrix2.conjugateBy]
private theorem conj_zero (V : ComplexMatrix2) : ComplexMatrix2.conjugateBy V 0 = 0 := by
  simp [ComplexMatrix2.conjugateBy]
private theorem conj_smul (V A : ComplexMatrix2) (c : ℂ) :
    ComplexMatrix2.conjugateBy V (c • A) = c • ComplexMatrix2.conjugateBy V A := by
  simp [ComplexMatrix2.conjugateBy]
private theorem conj_sum {ι : Type*} (V : ComplexMatrix2) (s : Finset ι) (f : ι → ComplexMatrix2) :
    ComplexMatrix2.conjugateBy V (∑ i ∈ s, f i) = ∑ i ∈ s, ComplexMatrix2.conjugateBy V (f i) := by
  simp [ComplexMatrix2.conjugateBy, Finset.mul_sum, Finset.sum_mul]
private theorem trace_conj {V : ComplexMatrix2} (hV : IsUnit V.det) (A : ComplexMatrix2) :
    Matrix.trace (ComplexMatrix2.conjugateBy V A) = Matrix.trace A := by
  unfold ComplexMatrix2.conjugateBy
  rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hV, Matrix.one_mul]
private theorem det_inv_isUnit {V : ComplexMatrix2} (hV : IsUnit V.det) : IsUnit (V⁻¹).det := by
  exact Matrix.isUnit_nonsing_inv_det _ hV
private theorem trace_mul_conj {W : ComplexMatrix2} (hW : IsUnit W.det) (Y Z : ComplexMatrix2) :
    Matrix.trace (Y * ComplexMatrix2.conjugateBy W Z) =
      Matrix.trace (ComplexMatrix2.conjugateBy W⁻¹ Y * Z) := by
  unfold ComplexMatrix2.conjugateBy
  rw [Matrix.nonsing_inv_nonsing_inv _ hW]
  have h₁ : Y * (W * Z * W⁻¹) = (Y * (W * Z)) * W⁻¹ := by simp only [Matrix.mul_assoc]
  have h₂ : W⁻¹ * Y * W * Z = W⁻¹ * (Y * (W * Z)) := by simp only [Matrix.mul_assoc]
  rw [h₁, h₂, Matrix.trace_mul_comm]
private theorem conj_gauge {a W c : ComplexMatrix2} (ha : IsUnit a.det) (hW : IsUnit W.det)
    (hc : IsUnit c.det) (Z : ComplexMatrix2) :
    ComplexMatrix2.conjugateBy (a * W * c⁻¹)⁻¹ (ComplexMatrix2.conjugateBy a Z) =
      ComplexMatrix2.conjugateBy c (ComplexMatrix2.conjugateBy W⁻¹ Z) := by
  have hP : IsUnit (a * W * c⁻¹).det := by
    rw [Matrix.det_mul, Matrix.det_mul]
    exact (ha.mul hW).mul (det_inv_isUnit hc)
  unfold ComplexMatrix2.conjugateBy
  rw [Matrix.nonsing_inv_nonsing_inv _ hP, Matrix.nonsing_inv_nonsing_inv _ hW,
    Matrix.mul_inv_rev, Matrix.mul_inv_rev, Matrix.nonsing_inv_nonsing_inv _ hc]
  have h₁ : a⁻¹ * a = 1 := Matrix.nonsing_inv_mul _ ha
  calc c * (W⁻¹ * a⁻¹) * (a * Z * a⁻¹) * (a * W * c⁻¹)
      = c * W⁻¹ * (a⁻¹ * a) * Z * (a⁻¹ * a) * W * c⁻¹ := by simp only [Matrix.mul_assoc]
    _ = c * (W⁻¹ * Z * W) * c⁻¹ := by
        rw [h₁]; simp only [Matrix.mul_one, Matrix.mul_assoc]
abbrev _root_.YangMills.SharedProofs.p76369 := @conj_gauge
private theorem sum_comp_sub [Fintype (Site L m j)] (s : Site L m j) (g : Site L m j → ℂ) :
    ∑ x, g (x - s) = ∑ x, g x :=
  Equiv.sum_comp (Equiv.subRight s) g
private theorem halfTrace_smul_mul (c : ℂ) (A B : ComplexMatrix2) :
    ComplexMatrix2.halfTrace ((c • A) * B) = c * ComplexMatrix2.halfTrace (A * B) := by
  simp only [ComplexMatrix2.halfTrace, ComplexMatrix2.fullTrace, Matrix.smul_mul,
    Matrix.trace_smul, smul_eq_mul]
  ring
private theorem halfTrace_mul_smul (c : ℂ) (A B : ComplexMatrix2) :
    ComplexMatrix2.halfTrace (A * (c • B)) = c * ComplexMatrix2.halfTrace (A * B) := by
  simp only [ComplexMatrix2.halfTrace, ComplexMatrix2.fullTrace, Matrix.mul_smul,
    Matrix.trace_smul, smul_eq_mul]
  ring
private theorem halfTrace_sub_mul (A B C : ComplexMatrix2) :
    ComplexMatrix2.halfTrace ((A - B) * C) =
      ComplexMatrix2.halfTrace (A * C) - ComplexMatrix2.halfTrace (B * C) := by
  simp only [ComplexMatrix2.halfTrace, ComplexMatrix2.fullTrace, Matrix.sub_mul, Matrix.trace_sub]
  ring
private theorem halfTrace_mul_sub (A B C : ComplexMatrix2) :
    ComplexMatrix2.halfTrace (A * (B - C)) =
      ComplexMatrix2.halfTrace (A * B) - ComplexMatrix2.halfTrace (A * C) := by
  simp only [ComplexMatrix2.halfTrace, ComplexMatrix2.fullTrace, Matrix.mul_sub, Matrix.trace_sub]
  ring
private theorem halfTrace_sum_mul {ι : Type*} (s : Finset ι) (f : ι → ComplexMatrix2)
    (C : ComplexMatrix2) :
    ComplexMatrix2.halfTrace ((∑ i ∈ s, f i) * C) =
      ∑ i ∈ s, ComplexMatrix2.halfTrace (f i * C) := by
  simp only [ComplexMatrix2.halfTrace, ComplexMatrix2.fullTrace, Finset.sum_mul, Matrix.trace_sum,
    Finset.mul_sum]
private theorem summation_by_parts [Fintype (Site L m j)] (ξ : ℝ) (U : Bond L m j → ComplexMatrix2)
    (hU : ∀ b, IsUnit (U b).det) (ν : Fin 4) (Y f : Site L m j → ComplexMatrix2) :
    ∑ x, ComplexMatrix2.halfTrace (Y x * covDeriv ξ U ν f x) =
      ∑ x, ComplexMatrix2.halfTrace (covDerivAdjointComponent ξ U ν Y x * f x) := by
  set s := unitStep L m j ν with hs
  let g : Site L m j → ℂ := fun x =>
    ComplexMatrix2.halfTrace
      (ComplexMatrix2.conjugateBy (U (Bond.forwardFrom x ν))⁻¹ (Y x) * f (x + s))
  have h₁ : ∀ x, ComplexMatrix2.halfTrace (Y x * covDeriv ξ U ν f x) =
      ((ξ⁻¹ : ℝ) : ℂ) * (g x - ComplexMatrix2.halfTrace (Y x * f x)) := by
    intro x
    unfold covDeriv
    rw [halfTrace_mul_smul, halfTrace_mul_sub]
    simp only [g, ComplexMatrix2.halfTrace, ComplexMatrix2.fullTrace]
    rw [trace_mul_conj (hU _)]
  have h₂ : ∀ x, ComplexMatrix2.halfTrace (covDerivAdjointComponent ξ U ν Y x * f x) =
      ((ξ⁻¹ : ℝ) : ℂ) * (g (x - s) - ComplexMatrix2.halfTrace (Y x * f x)) := by
    intro x
    unfold covDerivAdjointComponent
    rw [halfTrace_smul_mul, halfTrace_sub_mul]
    simp only [g, sub_add_cancel, hs]
  simp only [h₁, h₂, ← Finset.mul_sum, Finset.sum_sub_distrib]
  rw [sum_comp_sub s g]
private theorem sum_pairs_four (T : Fin 4 → Fin 4 → ℂ) :
    ∑ μ, ∑ ν ∈ Finset.Ioi μ, (T ν μ + T μ ν) = ∑ μ, ∑ ν ∈ Finset.univ.erase μ, T μ ν := by
  have i0 : Finset.Ioi (0 : Fin 4) = {1, 2, 3} := by decide
  have i1 : Finset.Ioi (1 : Fin 4) = {2, 3} := by decide
  have i2 : Finset.Ioi (2 : Fin 4) = {3} := by decide
  have i3 : Finset.Ioi (3 : Fin 4) = ∅ := by decide
  have e0 : Finset.univ.erase (0 : Fin 4) = {1, 2, 3} := by decide
  have e1 : Finset.univ.erase (1 : Fin 4) = {0, 2, 3} := by decide
  have e2 : Finset.univ.erase (2 : Fin 4) = {0, 1, 3} := by decide
  have e3 : Finset.univ.erase (3 : Fin 4) = {0, 1, 2} := by decide
  simp only [Fin.sum_univ_four, i0, i1, i2, i3, e0, e1, e2, e3]
  simp
  ring
private def adjointBondForm (ξ : ℝ) (U : Bond L m j → ComplexMatrix2)
    (X : Fin 4 → Fin 4 → Site L m j → ComplexMatrix2) : Bond L m j → ComplexMatrix2 :=
  bondFormOfPositive fun b => covDerivAdjointSum ξ U X b.axis b.source
private theorem adjointBondForm_component (hL : 13 ≤ L) (hj : -(m : ℤ) < j) (ξ : ℝ)
    (U : Bond L m j → ComplexMatrix2) (X : Fin 4 → Fin 4 → Site L m j → ComplexMatrix2)
    (μ : Fin 4) (x : Site L m j) :
    bondFormComponent (adjointBondForm ξ U X) μ x = covDerivAdjointSum ξ U X μ x := by
  unfold bondFormComponent adjointBondForm
  rw [bondFormOfPositive_forwardFrom, axis_forwardFrom hL hj]
  rfl
private theorem adjointBondForm_inner (hL : 13 ≤ L) (hj : -(m : ℤ) < j) [Fintype (Site L m j)]
    (ξ : ℝ) (U : Bond L m j → ComplexMatrix2) (hU : ∀ b, IsUnit (U b).det)
    (X : Fin 4 → Fin 4 → Site L m j → ComplexMatrix2) (hX : ∀ μ ν x, X ν μ x = -X μ ν x)
    (A : Bond L m j → ComplexMatrix2) :
    bondFormInner ξ (adjointBondForm ξ U X) A =
      plaquetteFormInner ξ X (covExteriorDeriv ξ U A) := by
  rw [bondFormInner, plaquetteFormInner, finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype]
  congr 1
  let T : Site L m j → Fin 4 → Fin 4 → ℂ := fun x μ ν =>
    ComplexMatrix2.halfTrace (X ν μ x * covDeriv ξ U ν (bondFormComponent A μ) x)
  have hl : ∑ x, ∑ μ, ComplexMatrix2.halfTrace
      (bondFormComponent (adjointBondForm ξ U X) μ x * bondFormComponent A μ x) =
      ∑ x, ∑ μ, ∑ ν ∈ Finset.univ.erase μ, T x μ ν := by
    calc ∑ x, ∑ μ, ComplexMatrix2.halfTrace
          (bondFormComponent (adjointBondForm ξ U X) μ x * bondFormComponent A μ x)
        = ∑ x, ∑ μ, ∑ ν ∈ Finset.univ.erase μ, ComplexMatrix2.halfTrace
            (covDerivAdjointComponent ξ U ν (X ν μ) x * bondFormComponent A μ x) := by
          refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun μ _ => ?_
          rw [adjointBondForm_component hL hj]
          unfold covDerivAdjointSum
          rw [halfTrace_sum_mul]
      _ = ∑ μ, ∑ ν ∈ Finset.univ.erase μ, ∑ x, ComplexMatrix2.halfTrace
            (covDerivAdjointComponent ξ U ν (X ν μ) x * bondFormComponent A μ x) := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun μ _ => ?_
          rw [Finset.sum_comm]
      _ = ∑ μ, ∑ ν ∈ Finset.univ.erase μ, ∑ x, T x μ ν := by
          refine Finset.sum_congr rfl fun μ _ => Finset.sum_congr rfl fun ν _ => ?_
          exact (summation_by_parts ξ U hU ν (X ν μ) (bondFormComponent A μ)).symm
      _ = ∑ μ, ∑ x, ∑ ν ∈ Finset.univ.erase μ, T x μ ν :=
          Finset.sum_congr rfl fun μ _ => Finset.sum_comm
      _ = ∑ x, ∑ μ, ∑ ν ∈ Finset.univ.erase μ, T x μ ν := Finset.sum_comm
  have hr : ∀ x, ∑ μ, ∑ ν ∈ Finset.Ioi μ, ComplexMatrix2.halfTrace
      (X μ ν x * covExteriorDeriv ξ U A μ ν x) =
      ∑ μ, ∑ ν ∈ Finset.Ioi μ, (T x ν μ + T x μ ν) := by
    intro x
    refine Finset.sum_congr rfl fun μ _ => Finset.sum_congr rfl fun ν _ => ?_
    show ComplexMatrix2.halfTrace (X μ ν x * (covDeriv ξ U μ (bondFormComponent A ν) x -
        covDeriv ξ U ν (bondFormComponent A μ) x)) =
      ComplexMatrix2.halfTrace (X μ ν x * covDeriv ξ U μ (bondFormComponent A ν) x) +
        ComplexMatrix2.halfTrace (X ν μ x * covDeriv ξ U ν (bondFormComponent A μ) x)
    rw [halfTrace_mul_sub, hX μ ν x]
    simp only [ComplexMatrix2.halfTrace, ComplexMatrix2.fullTrace, Matrix.neg_mul,
      Matrix.trace_neg]
    ring
  rw [hl]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [hr x, sum_pairs_four]
open Classical in
private def bondIndicator (x : Site L m j) (μ : Fin 4) (Y : ComplexMatrix2) :
    Bond L m j → ComplexMatrix2 :=
  bondFormOfPositive fun b => if b = Bond.forwardFrom x μ then Y else 0
private theorem inner_bondIndicator (hL : 13 ≤ L) (hj : -(m : ℤ) < j) [Fintype (Site L m j)]
    (ξ : ℝ) (C : Bond L m j → ComplexMatrix2) (x : Site L m j) (μ : Fin 4) (Y : ComplexMatrix2) :
    bondFormInner ξ C (bondIndicator x μ Y) =
      ((ξ ^ 4 : ℝ) : ℂ) * ComplexMatrix2.halfTrace (C (Bond.forwardFrom x μ) * Y) := by
  classical
  have hv : ∀ y ν, bondFormComponent (bondIndicator x μ Y) ν y =
      if Bond.forwardFrom y ν = Bond.forwardFrom x μ then Y else 0 := by
    intro y ν
    unfold bondFormComponent bondIndicator
    rw [bondFormOfPositive_forwardFrom]
  rw [bondFormInner, finsum_eq_sum_of_fintype]
  congr 1
  rw [Finset.sum_eq_single x, Finset.sum_eq_single μ]
  · rw [hv, if_pos rfl]
    rfl
  · intro ν _ hν
    rw [hv, if_neg fun h => hν (forwardFrom_injective hL hj h).2]
    simp
  · simp
  · intro y _ hy
    refine Finset.sum_eq_zero fun ν _ => ?_
    rw [hv, if_neg fun h => hy (forwardFrom_injective hL hj h).1]
    simp
  · simp
private theorem trace_eq_of_scaled_halfTrace {ξ : ℝ} (hξ : ξ ≠ 0) {P Q : ComplexMatrix2}
    (h : ((ξ ^ 4 : ℝ) : ℂ) * ComplexMatrix2.halfTrace P =
      ((ξ ^ 4 : ℝ) : ℂ) * ComplexMatrix2.halfTrace Q) :
    Matrix.trace P = Matrix.trace Q := by
  have hc : ((ξ ^ 4 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast pow_ne_zero 4 hξ
  have h₁ := mul_left_cancel₀ hc h
  exact mul_left_cancel₀ (by norm_num : (1 / 2 : ℂ) ≠ 0) h₁
abbrev _root_.YangMills.SharedProofs.p25377 := @trace_eq_of_scaled_halfTrace
private theorem bondForm_eq_of_inner (hL : 13 ≤ L) (hj : -(m : ℤ) < j) [Fintype (Site L m j)]
    {ξ : ℝ} (hξ : ξ ≠ 0) {𝔥 : Set ComplexMatrix2} (h0 : (0 : ComplexMatrix2) ∈ 𝔥)
    (hsub : ∀ a ∈ 𝔥, ∀ b ∈ 𝔥, a - b ∈ 𝔥)
    (hnd : ∀ Z ∈ 𝔥, (∀ Y ∈ 𝔥, Matrix.trace (Z * Y) = 0) → Z = 0)
    {B B' : Bond L m j → ComplexMatrix2} (hB : IsBondForm 𝔥 B) (hB' : IsBondForm 𝔥 B')
    (h : ∀ A, IsBondForm 𝔥 A → bondFormInner ξ B A = bondFormInner ξ B' A) : B = B' := by
  classical
  have hfw : ∀ x μ, B (Bond.forwardFrom x μ) = B' (Bond.forwardFrom x μ) := by
    intro x μ
    have hZ := hsub _ (hB.1 _ (forwardFrom_isPositivelyOriented x μ)) _
      (hB'.1 _ (forwardFrom_isPositivelyOriented x μ))
    refine sub_eq_zero.1 (hnd _ hZ fun Y hY => ?_)
    have hA : IsBondForm 𝔥 (bondIndicator x μ Y) := by
      refine isBondForm_bondFormOfPositive hL hj fun b _ => ?_
      split_ifs
      · exact hY
      · exact h0
    have h₁ := h _ hA
    rw [inner_bondIndicator hL hj, inner_bondIndicator hL hj] at h₁
    rw [Matrix.sub_mul, Matrix.trace_sub, trace_eq_of_scaled_halfTrace hξ h₁, sub_self]
  funext b
  rcases positive_or_opposite_positive b with hb | hb
  · rw [eq_forwardFrom hL hj hb]
    exact hfw _ _
  · have h₁ := hB.2 b.opposite
    have h₂ := hB'.2 b.opposite
    rw [opposite_opposite] at h₁ h₂
    have h₃ : B b.opposite = B' b.opposite := by
      rw [eq_forwardFrom hL hj hb]
      exact hfw _ _
    rw [h₁, h₂, h₃]
private theorem traceForm_nondegenerate_sl (Z : ComplexMatrix2) (hZ : Z ∈ complexLieAlgebra)
    (h : ∀ Y ∈ complexLieAlgebra, Matrix.trace (Z * Y) = 0) : Z = 0 := by
  have hZ' : Z 0 0 + Z 1 1 = 0 := by
    have : Matrix.trace Z = 0 := hZ
    simpa [Matrix.trace_fin_two] using this
  have h₁ := h !![0, 1; 0, 0] (show Matrix.trace _ = 0 by simp [Matrix.trace_fin_two])
  have h₂ := h !![0, 0; 1, 0] (show Matrix.trace _ = 0 by simp [Matrix.trace_fin_two])
  have h₃ := h !![1, 0; 0, -1] (show Matrix.trace _ = 0 by simp [Matrix.trace_fin_two])
  simp [Matrix.trace_fin_two, Matrix.mul_apply, Fin.sum_univ_two] at h₁ h₂ h₃
  have h₄ : Z 0 0 = 0 := by linear_combination (1 / 2 : ℂ) * h₃ + (1 / 2 : ℂ) * hZ'
  have h₅ : Z 1 1 = 0 := by linear_combination hZ' - h₄
  ext i k
  fin_cases i <;> fin_cases k <;> simp [h₁, h₂, h₄, h₅]
private theorem traceForm_nondegenerate_full (Z : ComplexMatrix2)
    (_hZ : Z ∈ (univ : Set ComplexMatrix2))
    (h : ∀ Y ∈ (univ : Set ComplexMatrix2), Matrix.trace (Z * Y) = 0) : Z = 0 := by
  have h₁ := h !![0, 1; 0, 0] (mem_univ _)
  have h₂ := h !![0, 0; 1, 0] (mem_univ _)
  have h₃ := h !![1, 0; 0, 0] (mem_univ _)
  have h₄ := h !![0, 0; 0, 1] (mem_univ _)
  simp [Matrix.trace_fin_two, Matrix.mul_apply, Fin.sum_univ_two] at h₁ h₂ h₃ h₄
  ext i k
  fin_cases i <;> fin_cases k <;> simp [h₁, h₂, h₃, h₄]
private theorem epsilon_adjoint_eq (hL : 13 ≤ L) (hj : -(m : ℤ) < j) [Fintype (Site L m j)]
    {ξ : ℝ} (hξ : ξ ≠ 0) {𝔥 : Set ComplexMatrix2} (h0 : (0 : ComplexMatrix2) ∈ 𝔥)
    (hsub : ∀ a ∈ 𝔥, ∀ b ∈ 𝔥, a - b ∈ 𝔥)
    (hnd : ∀ Z ∈ 𝔥, (∀ Y ∈ 𝔥, Matrix.trace (Z * Y) = 0) → Z = 0)
    (U : Bond L m j → ComplexMatrix2) (hU : ∀ b, IsUnit (U b).det)
    (X : Fin 4 → Fin 4 → Site L m j → ComplexMatrix2) (hX : ∀ μ ν x, X ν μ x = -X μ ν x)
    (hmem : IsBondForm 𝔥 (adjointBondForm ξ U X)) :
    (Classical.epsilon fun B => IsBondForm 𝔥 B ∧ ∀ A, IsBondForm 𝔥 A →
      bondFormInner ξ B A = plaquetteFormInner ξ X (covExteriorDeriv ξ U A)) =
      adjointBondForm ξ U X := by
  have hs := Classical.epsilon_spec (p := fun B => IsBondForm 𝔥 B ∧ ∀ A, IsBondForm 𝔥 A →
      bondFormInner ξ B A = plaquetteFormInner ξ X (covExteriorDeriv ξ U A))
    ⟨adjointBondForm ξ U X, hmem, fun A _ => adjointBondForm_inner hL hj ξ U hU X hX A⟩
  exact bondForm_eq_of_inner hL hj hξ h0 hsub hnd hs.1 hmem fun A hA =>
    (hs.2 A hA).trans (adjointBondForm_inner hL hj ξ U hU X hX A).symm
private theorem conj_mem_lie {V : ComplexMatrix2} (hV : IsUnit V.det) {A : ComplexMatrix2}
    (hA : A ∈ complexLieAlgebra) : ComplexMatrix2.conjugateBy V A ∈ complexLieAlgebra := by
  show Matrix.trace (ComplexMatrix2.conjugateBy V A) = 0
  rw [trace_conj hV]
  exact hA
private theorem covDerivAdjointComponent_mem {ξ : ℝ} {U : Bond L m j → ComplexMatrix2}
    (hU : ∀ b, IsUnit (U b).det) (ν : Fin 4) {f : Site L m j → ComplexMatrix2}
    (hf : ∀ y, f y ∈ complexLieAlgebra) (x : Site L m j) :
    covDerivAdjointComponent ξ U ν f x ∈ complexLieAlgebra :=
  ComplexMatrix2.traceless.smul_mem _ (ComplexMatrix2.traceless.sub_mem
    (conj_mem_lie (Matrix.isUnit_nonsing_inv_det _ (hU _)) (hf _)) (hf x))
private theorem plaquetteForm_mem {F : Fin 4 → Fin 4 → Site L m j → ComplexMatrix2}
    (hF : IsPlaquetteForm complexLieAlgebra F) {ν μ : Fin 4} (h : ν ≠ μ) (y : Site L m j) :
    F ν μ y ∈ complexLieAlgebra := by
  rcases lt_or_gt_of_ne h with h' | h'
  · exact hF.1 _ _ _ h'
  · rw [hF.2 μ ν y]
    exact ComplexMatrix2.traceless.neg_mem (hF.1 _ _ _ h')
private theorem covDerivAdjointSum_mem {ξ : ℝ} {U : Bond L m j → ComplexMatrix2}
    (hU : ∀ b, IsUnit (U b).det) {F : Fin 4 → Fin 4 → Site L m j → ComplexMatrix2}
    (hF : IsPlaquetteForm complexLieAlgebra F) (μ : Fin 4) (x : Site L m j) :
    covDerivAdjointSum ξ U F μ x ∈ complexLieAlgebra :=
  ComplexMatrix2.traceless.sum_mem fun ν hν =>
    covDerivAdjointComponent_mem hU ν (plaquetteForm_mem hF (Finset.ne_of_mem_erase hν)) x
private theorem covExteriorDerivAdjoint_eq (hL : 13 ≤ L) (hj : -(m : ℤ) < j)
    [Fintype (Site L m j)] {ξ : ℝ} (hξ : ξ ≠ 0) {U : Bond L m j → ComplexMatrix2}
    (hU : ∀ b, IsUnit (U b).det) {F : Fin 4 → Fin 4 → Site L m j → ComplexMatrix2}
    (hF : IsPlaquetteForm complexLieAlgebra F) :
    covExteriorDerivAdjoint ξ U F = adjointBondForm ξ U F :=
  epsilon_adjoint_eq hL hj hξ ComplexMatrix2.traceless.zero_mem
    (fun _ ha _ hb => ComplexMatrix2.traceless.sub_mem ha hb)
    traceForm_nondegenerate_sl U hU F hF.2
    (isBondForm_bondFormOfPositive hL hj fun _ _ => covDerivAdjointSum_mem hU hF _ _)
private theorem matrixTranspose_eq_adjointBondForm (hL : 13 ≤ L) (hj : -(m : ℤ) < j)
    [Fintype (Site L m j)] {ξ : ℝ} (hξ : ξ ≠ 0) {U : Bond L m j → ComplexMatrix2}
    (hU : ∀ b, IsUnit (U b).det) {X : Fin 4 → Fin 4 → Site L m j → ComplexMatrix2}
    (hX : IsPlaquetteForm univ X) :
    matrixCovExteriorDerivTranspose ξ U X = adjointBondForm ξ U X :=
  epsilon_adjoint_eq hL hj hξ (mem_univ _) (fun _ _ _ _ => mem_univ _)
    traceForm_nondegenerate_full U hU X hX.2
    (isBondForm_bondFormOfPositive hL hj fun _ _ => mem_univ _)
private theorem covDerivAdjointSum_eq_transported (ξ : ℝ) (U : Bond L m j → ComplexMatrix2)
    {X : Fin 4 → Fin 4 → Site L m j → ComplexMatrix2} (hX : ∀ μ ν x, X ν μ x = -X μ ν x)
    (μ : Fin 4) (x : Site L m j) :
    covDerivAdjointSum ξ U X μ x = transportedDifferenceSum ξ U X μ x := by
  unfold covDerivAdjointSum transportedDifferenceSum covDerivAdjointComponent
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun ν _ => ?_
  congr 1
  rw [hX μ ν, hX μ ν, conj_neg]
  abel
private theorem lieFormsFormula (hL : 13 ≤ L) (hj : -(m : ℤ) < j) [Fintype (Site L m j)]
    {ξ : ℝ} (hξ : ξ ≠ 0) {U : Bond L m j → ComplexMatrix2} (hU : ∀ b, IsUnit (U b).det) :
    AdjointFormulaOnLieForms ξ U := fun F hF μ x =>
  ⟨by rw [covExteriorDerivAdjoint_eq hL hj hξ hU hF, adjointBondForm_component hL hj],
    covDerivAdjointSum_eq_transported ξ U hF.2 μ x⟩
private theorem matrixFormsFormula (hL : 13 ≤ L) (hj : -(m : ℤ) < j) [Fintype (Site L m j)]
    {ξ : ℝ} (hξ : ξ ≠ 0) {U : Bond L m j → ComplexMatrix2} (hU : ∀ b, IsUnit (U b).det) :
    AdjointFormulaOnMatrixForms ξ U := fun X hX => by
  rw [matrixTranspose_eq_adjointBondForm hL hj hξ hU hX]
  refine ⟨isBondForm_bondFormOfPositive hL hj fun _ _ => mem_univ _,
    fun A _ => adjointBondForm_inner hL hj ξ U hU X hX.2 A, fun μ x => ?_⟩
  rw [adjointBondForm_component hL hj]
  exact ⟨rfl, covDerivAdjointSum_eq_transported ξ U hX.2 μ x⟩
private theorem zeroExtendSiteField_univ (f : Site L m j → ComplexMatrix2) :
    zeroExtendSiteField (univ : Set (FourTorus L m)) f = f := by
  have h : sitesIn (univ : Set (FourTorus L m)) = (univ : Set (Site L m j)) := by
    ext x
    simp [sitesIn]
  simp [zeroExtendSiteField, h]
abbrev _root_.YangMills.SharedProofs.p23088 := @zeroExtendSiteField_univ
private theorem zeroExtendBondForm_univ (A : Bond L m j → ComplexMatrix2) :
    zeroExtendBondForm (univ : Set (FourTorus L m)) A = A := by
  have h : bondsMeeting (univ : Set (FourTorus L m)) = (univ : Set (Bond L m j)) := by
    ext x
    simp [bondsMeeting]
  simp [zeroExtendBondForm, h]
abbrev _root_.YangMills.SharedProofs.p57978 := @zeroExtendBondForm_univ
private theorem covGradient_component (hL : 13 ≤ L) (hj : -(m : ℤ) < j) (ξ : ℝ)
    (U : Bond L m j → ComplexMatrix2) (f : Site L m j → ComplexMatrix2) (μ : Fin 4)
    (x : Site L m j) :
    bondFormComponent (covGradient univ ξ U f) μ x = covDeriv ξ U μ f x := by
  unfold covGradient
  rw [zeroExtendBondForm_univ, zeroExtendSiteField_univ]
  unfold bondFormComponent
  rw [bondFormOfPositive_forwardFrom, axis_forwardFrom hL hj]
  rfl
private theorem covGradient_inner (hL : 13 ≤ L) (hj : -(m : ℤ) < j) [Fintype (Site L m j)]
    (ξ : ℝ) (U : Bond L m j → ComplexMatrix2) (hU : ∀ b, IsUnit (U b).det)
    (A : Bond L m j → ComplexMatrix2) (f : Site L m j → ComplexMatrix2) :
    bondFormInner ξ A (covGradient univ ξ U f) =
      siteInner ξ (bondFormDivergenceSum ξ U A) f := by
  rw [bondFormInner, siteInner, finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype]
  congr 1
  simp only [covGradient_component hL hj, bondFormDivergenceSum, halfTrace_sum_mul]
  calc ∑ x, ∑ μ, ComplexMatrix2.halfTrace
        (bondFormComponent A μ x * covDeriv ξ U μ f x)
      = ∑ μ, ∑ x, ComplexMatrix2.halfTrace
          (bondFormComponent A μ x * covDeriv ξ U μ f x) := Finset.sum_comm
    _ = ∑ μ, ∑ x, ComplexMatrix2.halfTrace
          (covDerivAdjointComponent ξ U μ (bondFormComponent A μ) x * f x) :=
        Finset.sum_congr rfl fun μ _ => summation_by_parts ξ U hU μ _ f
    _ = ∑ x, ∑ μ, ComplexMatrix2.halfTrace
          (covDerivAdjointComponent ξ U μ (bondFormComponent A μ) x * f x) := Finset.sum_comm
private theorem siteField_eq_of_inner [Fintype (Site L m j)] {ξ : ℝ} (hξ : ξ ≠ 0)
    {B B' : Site L m j → ComplexMatrix2} (hB : IsSiteField complexLieAlgebra B)
    (hB' : IsSiteField complexLieAlgebra B')
    (h : ∀ f, IsSiteField complexLieAlgebra f → siteInner ξ B f = siteInner ξ B' f) :
    B = B' := by
  classical
  have delta : ∀ (C : Site L m j → ComplexMatrix2) (x : Site L m j) (Y : ComplexMatrix2),
      siteInner ξ C (fun y => if y = x then Y else 0) =
        ((ξ ^ 4 : ℝ) : ℂ) * ComplexMatrix2.halfTrace (C x * Y) := by
    intro C x Y
    rw [siteInner, finsum_eq_sum_of_fintype]
    congr 1
    rw [Finset.sum_eq_single x]
    · simp
    · intro y _ hy
      simp [hy]
    · simp
  funext x
  refine sub_eq_zero.1 (traceForm_nondegenerate_sl _
    (ComplexMatrix2.traceless.sub_mem (hB x) (hB' x)) fun Y hY => ?_)
  have h₁ := h (fun y => if y = x then Y else 0) fun y => by
    show (if y = x then Y else 0) ∈ complexLieAlgebra
    split_ifs
    · exact hY
    · exact ComplexMatrix2.traceless.zero_mem
  rw [delta, delta] at h₁
  rw [Matrix.sub_mul, Matrix.trace_sub, trace_eq_of_scaled_halfTrace hξ h₁, sub_self]
private theorem divergenceSum_eq_covDivergence (hL : 13 ≤ L) (hj : -(m : ℤ) < j)
    [Fintype (Site L m j)] {ξ : ℝ} (hξ : ξ ≠ 0) {U : Bond L m j → ComplexMatrix2}
    (hU : ∀ b, IsUnit (U b).det) {A : Bond L m j → ComplexMatrix2}
    (hA : IsBondForm complexLieAlgebra A) :
    bondFormDivergenceSum ξ U A = covDivergence univ ξ U A := by
  have hmem : IsSiteField complexLieAlgebra (bondFormDivergenceSum ξ U A) := fun x =>
    ComplexMatrix2.traceless.sum_mem fun μ _ =>
      covDerivAdjointComponent_mem hU μ
        (fun y => hA.1 _ (forwardFrom_isPositivelyOriented y μ)) x
  have hs := Classical.epsilon_spec (p := fun B : Site L m j → ComplexMatrix2 =>
      IsSiteField complexLieAlgebra B ∧ zeroExtendSiteField univ B = B ∧
      ∀ f, IsSiteField complexLieAlgebra f →
        siteInner ξ B (zeroExtendSiteField univ f) =
          bondFormInner ξ (zeroExtendBondForm univ A) (covGradient univ ξ U f))
    ⟨bondFormDivergenceSum ξ U A, hmem, zeroExtendSiteField_univ _, fun f _ => by
      rw [zeroExtendSiteField_univ, zeroExtendBondForm_univ]
      exact (covGradient_inner hL hj ξ U hU A f).symm⟩
  refine siteField_eq_of_inner hξ hmem hs.1 fun f hf => ?_
  have h₁ : siteInner ξ (covDivergence univ ξ U A) f =
      bondFormInner ξ A (covGradient univ ξ U f) :=
    calc siteInner ξ (covDivergence univ ξ U A) f
        = siteInner ξ (covDivergence univ ξ U A) (zeroExtendSiteField univ f) := by
          rw [zeroExtendSiteField_univ f]
      _ = bondFormInner ξ (zeroExtendBondForm univ A) (covGradient univ ξ U f) := hs.2.2 f hf
      _ = bondFormInner ξ A (covGradient univ ξ U f) := by rw [zeroExtendBondForm_univ A]
  exact (covGradient_inner hL hj ξ U hU A f).symm.trans h₁.symm
private theorem finestIdentities (hL : 13 ≤ L) (hj : -(m : ℤ) < j) [Fintype (Site L m j)]
    {ξ : ℝ} (hξ : ξ ≠ 0) {U : Bond L m j → ComplexMatrix2} (hU : ∀ b, IsUnit (U b).det) :
    FinestOperatorIdentities ξ U := by
  refine ⟨fun F hF μ x => ?_, fun A hA => divergenceSum_eq_covDivergence hL hj hξ hU hA⟩
  rw [covExteriorDerivAdjoint_eq hL hj hξ hU hF, adjointBondForm_component hL hj]
  have hsplit : Finset.univ.erase μ = Finset.Iio μ ∪ Finset.Ioi μ := by
    ext ν
    simp [lt_or_lt_iff_ne]
  have hdisj : Disjoint (Finset.Iio μ) (Finset.Ioi μ) := by
    rw [Finset.disjoint_left]
    intro ν h₁ h₂
    exact lt_asymm (Finset.mem_Iio.1 h₁) (Finset.mem_Ioi.1 h₂)
  unfold covDerivAdjointSum plaquetteFormDivergenceSum
  rw [hsplit, Finset.sum_union hdisj, sub_eq_add_neg, ← Finset.sum_neg_distrib]
  congr 1
  refine Finset.sum_congr rfl fun ν _ => ?_
  unfold covDerivAdjointComponent
  rw [hF.2 μ ν, hF.2 μ ν, conj_neg]
  rw [← smul_neg]
  congr 1
  abel
private theorem plaquetteFormOf_antisymm (f : Plaquette L m j → ComplexMatrix2) (μ ν : Fin 4)
    (x : Site L m j) : plaquetteFormOf f ν μ x = -plaquetteFormOf f μ ν x := by
  unfold plaquetteFormOf
  rcases lt_trichotomy μ ν with h | h | h
  · simp [h, not_lt_of_gt h]
  · subst h
    simp
  · simp [h, not_lt_of_gt h]
abbrev _root_.YangMills.SharedProofs.p51177 := @plaquetteFormOf_antisymm
private theorem plaquetteFormOf_isPlaquetteForm (f : Plaquette L m j → ComplexMatrix2) :
    IsPlaquetteForm univ (plaquetteFormOf f) :=
  ⟨fun _ _ _ _ => mem_univ _, plaquetteFormOf_antisymm f⟩
private theorem plaquetteFormOf_conjugateAtOrigin (u : Site L m j → ComplexMatrix2)
    (X : Plaquette L m j → ComplexMatrix2) (ν μ : Fin 4) (y : Site L m j) :
    plaquetteFormOf (conjugateAtOrigin u X) ν μ y =
      ComplexMatrix2.conjugateBy (u y) (plaquetteFormOf X ν μ y) := by
  unfold plaquetteFormOf conjugateAtOrigin
  split_ifs <;> simp [conj_neg, conj_zero]
private theorem covDerivAdjointComponent_gaugeTransform {ξ : ℝ}
    {U : Bond L m j → ComplexMatrix2} {u : Site L m j → ComplexMatrix2}
    (hU : ∀ b, IsUnit (U b).det) (hu : ∀ x, IsUnit (u x).det)
    (ν : Fin 4) (f : Site L m j → ComplexMatrix2) (x : Site L m j) :
    covDerivAdjointComponent ξ (gaugeTransform u U) ν
        (fun y => ComplexMatrix2.conjugateBy (u y) (f y)) x =
      ComplexMatrix2.conjugateBy (u x) (covDerivAdjointComponent ξ U ν f x) := by
  unfold covDerivAdjointComponent
  rw [conj_smul, conj_sub]
  congr 2
  show ComplexMatrix2.conjugateBy (u (x - unitStep L m j ν) *
      U (Bond.forwardFrom (x - unitStep L m j ν) ν) *
      (u (x - unitStep L m j ν + unitStep L m j ν))⁻¹)⁻¹
      (ComplexMatrix2.conjugateBy (u (x - unitStep L m j ν)) (f (x - unitStep L m j ν))) = _
  rw [sub_add_cancel]
  exact conj_gauge (hu _) (hU _) (hu _) _
private theorem covDerivAdjointSum_gaugeTransform {ξ : ℝ} {U : Bond L m j → ComplexMatrix2}
    {u : Site L m j → ComplexMatrix2} (hU : ∀ b, IsUnit (U b).det)
    (hu : ∀ x, IsUnit (u x).det) (X : Plaquette L m j → ComplexMatrix2)
    (μ : Fin 4) (x : Site L m j) :
    covDerivAdjointSum ξ (gaugeTransform u U) (plaquetteFormOf (conjugateAtOrigin u X)) μ x =
      ComplexMatrix2.conjugateBy (u x) (covDerivAdjointSum ξ U (plaquetteFormOf X) μ x) := by
  unfold covDerivAdjointSum
  rw [conj_sum]
  refine Finset.sum_congr rfl fun ν _ => ?_
  have h : plaquetteFormOf (conjugateAtOrigin u X) ν μ =
      fun y => ComplexMatrix2.conjugateBy (u y) (plaquetteFormOf X ν μ y) :=
    funext (plaquetteFormOf_conjugateAtOrigin u X ν μ)
  rw [h]
  exact covDerivAdjointComponent_gaugeTransform hU hu ν _ x
private theorem det_eq_one_of_compact {V : ComplexMatrix2} (h : V ∈ compactGaugeGroup) :
    V.det = 1 :=
  (Matrix.mem_specialUnitaryGroup_iff.1 h).2
abbrev _root_.YangMills.SharedProofs.p157 := @det_eq_one_of_compact
private theorem plaquetteHolonomy_mem {U : Bond L m j → ComplexMatrix2}
    (hU : IsGaugeField compactGaugeGroup univ U) (p : Plaquette L m j) :
    plaquetteHolonomy U p ∈ compactGaugeGroup := by
  unfold plaquetteHolonomy pathHolonomy
  refine Submonoid.list_prod_mem _ fun y hy => ?_
  obtain ⟨b, _, rfl⟩ := List.mem_map.1 hy
  exact hU.1 b (mem_univ b)
private theorem trace_inv_of_det_one {P : ComplexMatrix2} (h : P.det = 1) :
    Matrix.trace P⁻¹ = Matrix.trace P := by
  simp [Matrix.inv_def, h, Matrix.adjugate_fin_two, Matrix.trace_fin_two]
  ring
abbrev _root_.YangMills.DeltaSharedProofs.p7762 := @trace_inv_of_det_one
private theorem curvatureAt_mem (ξ : ℝ) {U : Bond L m j → ComplexMatrix2}
    (hU : IsGaugeField compactGaugeGroup univ U) (p : Plaquette L m j) :
    curvatureAt ξ U p ∈ complexLieAlgebra := by
  refine ComplexMatrix2.traceless.smul_mem _ (ComplexMatrix2.traceless.smul_mem _ ?_)
  show Matrix.trace _ = 0
  rw [Matrix.trace_sub, trace_inv_of_det_one (det_eq_one_of_compact (plaquetteHolonomy_mem hU p)),
    sub_self]
private theorem curvature_isPlaquetteForm (ξ : ℝ) {U : Bond L m j → ComplexMatrix2}
    (hU : IsGaugeField compactGaugeGroup univ U) :
    IsPlaquetteForm complexLieAlgebra (curvature ξ U) := by
  refine ⟨fun μ ν x h => ?_, plaquetteFormOf_antisymm _⟩
  unfold curvature plaquetteFormOf
  rw [dif_pos h]
  exact curvatureAt_mem ξ hU _
private theorem curvatureAt_gaugeTransform (ξ : ℝ) {U V : Bond L m j → ComplexMatrix2}
    {a : ComplexMatrix2} (ha : IsUnit a.det) {p : Plaquette L m j}
    (hp : plaquetteHolonomy V p = a * plaquetteHolonomy U p * a⁻¹) :
    curvatureAt ξ V p = ComplexMatrix2.conjugateBy a (curvatureAt ξ U p) := by
  unfold curvatureAt
  rw [conj_smul, conj_smul, conj_sub, hp]
  have h : (a * plaquetteHolonomy U p * a⁻¹)⁻¹ = a * (plaquetteHolonomy U p)⁻¹ * a⁻¹ := by
    rw [Matrix.mul_inv_rev, Matrix.mul_inv_rev, Matrix.nonsing_inv_nonsing_inv _ ha,
      Matrix.mul_assoc]
  rw [h]
  rfl
abbrev _root_.YangMills.SharedProofs.p91411 := @curvatureAt_gaugeTransform
private theorem gaugeCovariant_holds (hG : GaugeCovarianceOfHolonomy)
    (hOdd : Odd L) (hL : 13 ≤ L) (hm : 0 < m) (hj : -(m : ℤ) < j) [Fintype (Site L m j)]
    {ξ : ℝ} (hξ : ξ ≠ 0) {U : Bond L m j → ComplexMatrix2}
    (hU : IsGaugeField compactGaugeGroup univ U)
    {u : Site L m j → ComplexMatrix2} (hu : IsGaugeMap compactGaugeGroup u) :
    GaugeCovariant ξ U u := by
  have hUc : IsGaugeField complexGaugeGroup univ U :=
    ⟨fun b hb => det_eq_one_of_compact (hU.1 b hb), hU.2⟩
  have huc : IsGaugeMap complexGaugeGroup u := fun x => det_eq_one_of_compact (hu x)
  obtain ⟨⟨-, hreal, -⟩, -, hplaq⟩ := hG L m hOdd hL hm j hj.le univ U u u
    (fun _ _ => mem_univ _) hUc huc huc
  have hV : IsGaugeField compactGaugeGroup univ (gaugeTransform u U) := hreal hU hu
  have hUd : ∀ b, IsUnit (U b).det := fun b => by
    rw [det_eq_one_of_compact (hU.1 b (mem_univ b))]
    exact isUnit_one
  have hVd : ∀ b, IsUnit (gaugeTransform u U b).det := fun b => by
    rw [det_eq_one_of_compact (hV.1 b (mem_univ b))]
    exact isUnit_one
  have hud : ∀ x, IsUnit (u x).det := fun x => by
    rw [det_eq_one_of_compact (hu x)]
    exact isUnit_one
  intro b hb
  obtain ⟨x, μ, rfl⟩ : ∃ x μ, b = Bond.forwardFrom x μ := ⟨_, _, eq_forwardFrom hL hj hb⟩
  have clause : ∀ X : Plaquette L m j → ComplexMatrix2,
      matrixCovExteriorDerivTranspose ξ (gaugeTransform u U)
          (plaquetteFormOf (conjugateAtOrigin u X)) (Bond.forwardFrom x μ) =
        ComplexMatrix2.conjugateBy (u x) (matrixCovExteriorDerivTranspose ξ U
          (plaquetteFormOf X) (Bond.forwardFrom x μ)) := by
    intro X
    rw [matrixTranspose_eq_adjointBondForm hL hj hξ hVd (plaquetteFormOf_isPlaquetteForm _),
      matrixTranspose_eq_adjointBondForm hL hj hξ hUd (plaquetteFormOf_isPlaquetteForm _)]
    show bondFormComponent (adjointBondForm ξ (gaugeTransform u U)
        (plaquetteFormOf (conjugateAtOrigin u X))) μ x =
      ComplexMatrix2.conjugateBy (u x)
        (bondFormComponent (adjointBondForm ξ U (plaquetteFormOf X)) μ x)
    rw [adjointBondForm_component hL hj, adjointBondForm_component hL hj]
    exact covDerivAdjointSum_gaugeTransform hUd hud X μ x
  have hfield : curvature ξ (gaugeTransform u U) =
      plaquetteFormOf (conjugateAtOrigin u (curvatureAt ξ U)) :=
    congrArg plaquetteFormOf (funext fun p =>
      curvatureAt_gaugeTransform ξ (hud _) (hplaq p fun _ _ => mem_univ _))
  have hplaquettes : plaquetteFormOf (plaquetteHolonomy (gaugeTransform u U)) =
      plaquetteFormOf (conjugateAtOrigin u (plaquetteHolonomy U)) :=
    congrArg plaquetteFormOf (funext fun p => hplaq p fun _ _ => mem_univ _)
  refine ⟨clause, ?_, ?_⟩
  · unfold yangMillsCurrent
    rw [covExteriorDerivAdjoint_eq hL hj hξ hVd (curvature_isPlaquetteForm ξ hV),
      covExteriorDerivAdjoint_eq hL hj hξ hUd (curvature_isPlaquetteForm ξ hU)]
    show bondFormComponent (adjointBondForm ξ (gaugeTransform u U)
        (curvature ξ (gaugeTransform u U))) μ x =
      ComplexMatrix2.conjugateBy (u x)
        (bondFormComponent (adjointBondForm ξ U (curvature ξ U)) μ x)
    rw [adjointBondForm_component hL hj, adjointBondForm_component hL hj, hfield]
    exact covDerivAdjointSum_gaugeTransform hUd hud _ μ x
  · rw [hplaquettes]
    exact clause _
private theorem conj_inv_conj {W : ComplexMatrix2} (hW : IsUnit W.det) (Z : ComplexMatrix2) :
    ComplexMatrix2.conjugateBy W⁻¹ (ComplexMatrix2.conjugateBy W Z) = Z := by
  unfold ComplexMatrix2.conjugateBy
  rw [Matrix.nonsing_inv_nonsing_inv _ hW]
  have h₁ : W⁻¹ * W = 1 := Matrix.nonsing_inv_mul _ hW
  calc W⁻¹ * (W * Z * W⁻¹) * W = (W⁻¹ * W) * Z * (W⁻¹ * W) := by simp only [Matrix.mul_assoc]
    _ = Z := by rw [h₁]; simp
abbrev _root_.YangMills.SharedProofs.p32697 := @conj_inv_conj
private theorem covDerivAdjointComponent_eq_neg {ξ : ℝ} {U : Bond L m j → ComplexMatrix2}
    (hU : ∀ b, IsUnit (U b).det) (μ : Fin 4) (f : Site L m j → ComplexMatrix2)
    (x : Site L m j) :
    covDerivAdjointComponent ξ U μ f x =
      -ComplexMatrix2.conjugateBy (U (Bond.forwardFrom (x - unitStep L m j μ) μ))⁻¹
        (covDeriv ξ U μ f (x - unitStep L m j μ)) := by
  unfold covDerivAdjointComponent covDeriv
  rw [conj_smul, conj_sub, conj_inv_conj (hU _), sub_add_cancel, ← smul_neg, neg_sub]
private theorem covDerivSupBounds_holds
    (hN : ComplexMatrix2.OperatorNormUnderConjugation)
    [Finite (Site L m j)] {ξ : ℝ} (hξ : 0 < ξ) {U : Bond L m j → ComplexMatrix2}
    (hU : IsGaugeField compactGaugeGroup univ U) : CovDerivSupBounds ξ U := by
  have hfb : Finite (Bond L m j) := bond_finite
  have hUd : ∀ b, IsUnit (U b).det := fun b => by
    rw [det_eq_one_of_compact (hU.1 b (mem_univ b))]
    exact isUnit_one
  have hnorm : ∀ {V : ComplexMatrix2}, V ∈ compactGaugeGroup → ∀ Z : ComplexMatrix2,
      ComplexMatrix2.operatorNorm (ComplexMatrix2.conjugateBy V Z) =
        ComplexMatrix2.operatorNorm Z := fun hV Z =>
    hN.2.1 Z _ (Matrix.specialUnitaryGroup_le_unitaryGroup hV)
  have hinv : ∀ b : Bond L m j, (U b)⁻¹ ∈ compactGaugeGroup := fun b => by
    rw [← hU.2 b (mem_univ b)]
    exact hU.1 _ (mem_univ _)
  intro A _
  have hbdd : ∀ y : Site L m j, BddAbove (range fun p : Fin 4 × Fin 4 =>
      ComplexMatrix2.operatorNorm (covDeriv ξ U p.1 (bondFormComponent A p.2) y)) :=
    fun _ => (Set.finite_range _).bddAbove
  have hbdd' : BddAbove (range fun y : Site L m j => covDerivNorm ξ U A y) :=
    (Set.finite_range _).bddAbove
  constructor
  · unfold supOfOperatorNorms
    refine ciSup_le fun x => ?_
    unfold bondFormDivergenceSum
    calc ComplexMatrix2.operatorNorm
          (∑ μ : Fin 4, covDerivAdjointComponent ξ U μ (bondFormComponent A μ) x)
        ≤ ∑ μ : Fin 4, ComplexMatrix2.operatorNorm
            (covDerivAdjointComponent ξ U μ (bondFormComponent A μ) x) :=
          norm_sum_le _ _
      _ ≤ ∑ _μ : Fin 4, ⨆ y, covDerivNorm ξ U A y := by
          refine Finset.sum_le_sum fun μ _ => ?_
          rw [covDerivAdjointComponent_eq_neg hUd]
          show ‖-ComplexMatrix2.conjugateBy _ _‖ ≤ _
          rw [norm_neg]
          refine ((hnorm (hinv _) _).le).trans ?_
          refine le_trans ?_ (le_ciSup hbdd' (x - unitStep L m j μ))
          exact le_ciSup (hbdd (x - unitStep L m j μ)) (μ, μ)
      _ = 4 * ⨆ y, covDerivNorm ξ U A y := by simp
  · have hsup : ∀ b : Bond L m j, ComplexMatrix2.operatorNorm (A b) ≤ supOfOperatorNorms A :=
      fun b => le_ciSup (f := fun b : Bond L m j => ComplexMatrix2.operatorNorm (A b))
        (Set.finite_range _).bddAbove b
    rw [← le_div_iff₀' hξ]
    refine ciSup_le fun x => ciSup_le fun p => ?_
    unfold covDeriv bondFormComponent
    show ‖((ξ⁻¹ : ℝ) : ℂ) • _‖ ≤ _
    rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg (inv_pos.2 hξ).le, div_eq_inv_mul]
    refine mul_le_mul_of_nonneg_left ?_ (inv_pos.2 hξ).le
    refine (norm_sub_le _ _).trans ?_
    have h₁ := hsup (Bond.forwardFrom (x + unitStep L m j p.1) p.2)
    have h₂ := hsup (Bond.forwardFrom x p.2)
    have h₃ := hnorm (hU.1 (Bond.forwardFrom x p.1) (mem_univ _))
      (A (Bond.forwardFrom (x + unitStep L m j p.1) p.2))
    have h₄ : ‖ComplexMatrix2.conjugateBy (U (Bond.forwardFrom x p.1))
        (A (Bond.forwardFrom (x + unitStep L m j p.1) p.2))‖ =
        ‖A (Bond.forwardFrom (x + unitStep L m j p.1) p.2)‖ := h₃
    have h₅ : ‖A (Bond.forwardFrom (x + unitStep L m j p.1) p.2)‖ ≤ supOfOperatorNorms A := h₁
    have h₆ : ‖A (Bond.forwardFrom x p.2)‖ ≤ supOfOperatorNorms A := h₂
    rw [h₄]
    linarith
theorem explicitAdjointFormulas_holds (hG : GaugeCovarianceOfHolonomy)
    (hN : ComplexMatrix2.OperatorNormUnderConjugation) : ExplicitAdjointFormulas := by
  refine ⟨?_, ?_⟩
  · intro L m K k hOdd hL hm _ _ j hj ξ hξ
    have hfin : Finite (Site L m j) := site_finite hL hj
    have : Fintype (Site L m j) := Fintype.ofFinite _
    have hLpos : (0 : ℝ) < L := by linarith [one_lt_base hL]
    have hξpos : 0 < ξ := by
      rw [hξ]
      exact mul_pos (zpow_pos hLpos _) (meshSize_pos hL)
    refine ⟨fun U hU => ?_, fun U hU => ?_⟩
    · have hUd : ∀ b, IsUnit (U b).det := fun b => by
        have h : (U b).det = 1 := hU.1 b (mem_univ b)
        rw [h]
        exact isUnit_one
      exact ⟨lieFormsFormula hL hj hξpos.ne' hUd,
        fun A _ f _ => covGradient_inner hL hj ξ U hUd A f,
        matrixFormsFormula hL hj hξpos.ne' hUd⟩
    · exact ⟨fun u hu => gaugeCovariant_holds hG hOdd hL hm hj hξpos.ne' hU hu,
        covDerivSupBounds_holds hN hξpos hU⟩
  · intro L m K k _ hL hm _ _ U₀ hU₀
    have hj : -(m : ℤ) < levelDepth K 0 := by
      simp only [levelDepth]
      omega
    have hfin : Finite (Site L m (levelDepth K 0)) := site_finite hL hj
    have : Fintype (Site L m (levelDepth K 0)) := Fintype.ofFinite _
    have hLpos : (0 : ℝ) < L := by linarith [one_lt_base hL]
    have hξ : finestMeshInLevelUnits L k ≠ 0 := (zpow_pos hLpos _).ne'
    have hUd : ∀ b, IsUnit (U₀ b).det := fun b => by
      have h : (U₀ b).det = 1 := hU₀.1 b (mem_univ b)
      rw [h]
      exact isUnit_one
    exact finestIdentities hL hj hξ hUd
end TransposeFormulas
end PeriodicLattice
end YangMills.Construction
