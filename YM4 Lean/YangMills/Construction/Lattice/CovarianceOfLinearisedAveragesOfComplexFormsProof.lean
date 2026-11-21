import YangMills.Construction.Lattice.CovarianceOfLinearisedAveragesOfComplexForms
import YangMills.Construction.Lattice.CovarianceOfTheAveragingMaps
import YangMills.Construction.Lattice.LayerBondsCoarseSpacesAndAverages
import Mathlib
set_option autoImplicit false
open Set
open scoped Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction.PeriodicLattice
open Matrices
variable {L m : ℕ}
private theorem isLinearMap_bondFormSumAlong {j : ℤ} (γ : List (Bond L m j)) :
    IsLinearMap ℂ fun X : Bond L m j → ComplexMatrix2 => bondFormSumAlong X γ := by
  constructor
  · intro X Y
    induction γ with
    | nil => simp [bondFormSumAlong]
    | cons b γ ih =>
      simp only [bondFormSumAlong, List.map_cons, List.sum_cons, Pi.add_apply] at ih ⊢
      rw [ih]
      abel
  · intro z X
    induction γ with
    | nil => simp [bondFormSumAlong]
    | cons b γ ih =>
      simp only [bondFormSumAlong, List.map_cons, List.sum_cons, Pi.smul_apply] at ih ⊢
      rw [ih, smul_add]
private theorem isLinearMap_contourFormAverage {j j' : ℤ} (y : Site L m j) (x : Site L m j') :
    IsLinearMap ℂ fun X : Bond L m j' → ComplexMatrix2 => contourFormAverage X y x := by
  constructor
  · intro X Y
    simp only [contourFormAverage, (isLinearMap_bondFormSumAlong _).map_add,
      Finset.sum_add_distrib, smul_add]
  · intro z X
    simp only [contourFormAverage, (isLinearMap_bondFormSumAlong _).map_smul, ← Finset.smul_sum]
    rw [smul_comm]
private theorem isLinearMap_linearBlockSum {j j' : ℤ} (hfin : Finite (Site L m j'))
    (c : Bond L m j) :
    IsLinearMap ℂ fun X : Bond L m j' → ComplexMatrix2 => linearBlockSum X c := by
  have hs : (sitesInBlock j' c.source : Set (Site L m j')).Finite := Set.toFinite _
  constructor
  · intro X Y
    simp only [linearBlockSum, finsum_mem_eq_finite_toFinset_sum _ hs,
      (isLinearMap_contourFormAverage _ _).map_add, (isLinearMap_bondFormSumAlong _).map_add]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun x _ => ?_
    abel
  · intro z X
    simp only [linearBlockSum, finsum_mem_eq_finite_toFinset_sum _ hs,
      (isLinearMap_contourFormAverage _ _).map_smul, (isLinearMap_bondFormSumAlong _).map_smul]
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [smul_sub, smul_add]
private theorem isLinearMap_smul_linearBlockSum {j j' : ℤ} (hfin : Finite (Site L m j'))
    (s : ℂ) :
    IsLinearMap ℂ fun X : Bond L m j' → ComplexMatrix2 =>
      (fun c : Bond L m j => s • linearBlockSum X c) := by
  constructor
  · intro X Y
    funext c
    simp only [(isLinearMap_linearBlockSum hfin c).map_add, smul_add, Pi.add_apply]
  · intro z X
    funext c
    simp only [(isLinearMap_linearBlockSum hfin c).map_smul, Pi.smul_apply]
    rw [smul_comm]
private theorem isLinearMap_iterateFromLevel {K : ℕ}
    {f : ∀ k, (BondAtLevel L m K k → ComplexMatrix2) → BondAtLevel L m K (k + 1) → ComplexMatrix2}
    (hf : ∀ k, IsLinearMap ℂ (f k)) (k n : ℕ) : IsLinearMap ℂ (iterateFromLevel f k n) := by
  induction n with
  | zero => exact ⟨fun _ _ => rfl, fun _ _ => rfl⟩
  | succ n ih =>
    constructor
    · intro X Y
      show f (k + n) (iterateFromLevel f k n (X + Y)) = _
      rw [ih.map_add, (hf _).map_add]
      rfl
    · intro z X
      show f (k + n) (iterateFromLevel f k n (z • X)) = _
      rw [ih.map_smul, (hf _).map_smul]
      rfl
private theorem isLinearMap_transportForm {j : ℤ} (σ : FourTorus L m ≃ FourTorus L m) :
    IsLinearMap ℂ (transportForm σ : (Bond L m j → ComplexMatrix2) → Bond L m j → ComplexMatrix2) :=
  ⟨fun _ _ => rfl, fun _ _ => rfl⟩
private theorem isLinearMap_apply_bond {j : ℤ} (b : Bond L m j) :
    IsLinearMap ℂ fun X : Bond L m j → ComplexMatrix2 => X b :=
  ⟨fun _ _ => rfl, fun _ _ => rfl⟩
private theorem finite_bond_of_pos (hL : 0 < L) (j : ℤ) : Finite (Bond L m j) := by
  have := SeparatedSequences.BaseParameters.site_finite hL m j
  refine Finite.of_injective (fun b : Bond L m j => (b.source, b.target)) fun a b h => ?_
  simp only [Prod.mk.injEq] at h
  exact Bond.ext h.1 h.2
private theorem isAnalyticOnSupport_of_isLinearMap {j : ℤ} (hfin : Finite (Bond L m j))
    (P : Set (Bond L m j → ComplexMatrix2)) {f : (Bond L m j → ComplexMatrix2) → ComplexMatrix2}
    (hf : IsLinearMap ℂ f) :
    IsAnalyticOnSupport P (univ : Set (Bond L m j)) P f := by
  let _ : Fintype ↥(univ : Set (Bond L m j)) := Fintype.ofFinite _
  have hv : IsLinearMap ℂ fun w : ↥(univ : Set (Bond L m j)) → ComplexMatrix2 =>
      f (extendWithIdentity univ w) := by
    have hlin : IsLinearMap ℂ fun w : ↥(univ : Set (Bond L m j)) → ComplexMatrix2 =>
        extendWithIdentity univ w := by
      constructor
      · intro v w
        funext b
        simp only [extendWithIdentity, dif_pos (mem_univ b), Pi.add_apply]
      · intro z w
        funext b
        simp only [extendWithIdentity, dif_pos (mem_univ b), Pi.smul_apply]
    exact ⟨fun v w => by rw [hlin.map_add, hf.map_add],
      fun z w => by rw [hlin.map_smul, hf.map_smul]⟩
  refine IsHolomorphicOnFields.of_analytic_formula (fun w => f (extendWithIdentity univ w))
    subset_rfl (isRelativelyOpen_self _) (fun U _ => ?_) (fun U _ => ?_)
  · exact (LinearMap.toContinuousLinearMap (hv.mk' _)).analyticAt _
  · congr 1
    funext b
    exact (extendByOne_restrictToBonds U (mem_univ b)).symm
private theorem isHolomorphicEquation_of_isLinearMap {j : ℤ} (hfin : Finite (Bond L m j))
    (σ : FourTorus L m ≃ FourTorus L m) (P : Set (Bond L m j → ComplexMatrix2))
    {f₁ f₂ : (Bond L m j → ComplexMatrix2) → ComplexMatrix2}
    (h₁ : IsLinearMap ℂ f₁) (h₂ : IsLinearMap ℂ f₂)
    (h : ∀ X ∈ P, f₁ X = f₂ X) :
    IsHolomorphicEquation σ P (univ : Set (Bond L m j)) P P f₁ f₂ := by
  refine ⟨?_, ?_, ?_, fun _ => rfl⟩
  · rw [inter_self]
    exact isAnalyticOnSupport_of_isLinearMap hfin P h₁
  · rw [inter_self]
    exact isAnalyticOnSupport_of_isLinearMap hfin P h₂
  · rw [inter_self]
    exact h
theorem linearBlockIteratesEquivariant_of_averagingMapsEquivariant
    (hcov : AveragingMapsEquivariant) :
    LinearBlockIteratesEquivariant := by
  intro L m i σ hs hm hi hσ K k n hkn hik c
  have hL : 0 < L := lt_of_lt_of_le (by norm_num) hs.2
  have hsite : ∀ j : ℤ, Finite (Site L m j) := SeparatedSequences.BaseParameters.site_finite hL m
  have hfin := finite_bond_of_pos (m := m) hL (levelDepth K k)
  have hcomm := (hcov L m hs hm i hi σ hσ K).2.2.2.1 k n hkn hik
  have hstep : ∀ q, IsLinearMap ℂ (linearBlockStep (L := L) (m := m) (K := K) q) :=
    fun q => isLinearMap_smul_linearBlockSum (hsite _) _
  have hstep' : ∀ q, IsLinearMap ℂ (scaledLinearBlockStep (L := L) (m := m) (K := K) q) :=
    fun q => isLinearMap_smul_linearBlockSum (hsite _) _
  have hQ : IsLinearMap ℂ (linearBlockIterateBetween (L := L) (m := m) (K := K) k n) :=
    isLinearMap_iterateFromLevel hstep k n
  have hQ' : IsLinearMap ℂ (scaledLinearBlockIterateFrom (L := L) (m := m) (K := K) k n) :=
    isLinearMap_iterateFromLevel hstep' k n
  have comp : ∀ {X Y Z : Type} [AddCommMonoid X] [AddCommMonoid Y] [AddCommMonoid Z] [Module ℂ X]
      [Module ℂ Y] [Module ℂ Z] {g : Y → Z} {f : X → Y}, IsLinearMap ℂ g → IsLinearMap ℂ f →
      IsLinearMap ℂ (fun x => g (f x)) := fun hg hf =>
    ⟨fun x y => by rw [hf.map_add, hg.map_add], fun z x => by rw [hf.map_smul, hg.map_smul]⟩
  exact ⟨isHolomorphicEquation_of_isLinearMap hfin σ _
      (comp (isLinearMap_apply_bond _) (comp hQ (isLinearMap_transportForm σ)))
      (comp (isLinearMap_apply_bond _) (comp (isLinearMap_transportForm σ) hQ))
      fun X hX => congrFun (hcomm X hX).1 _,
    isHolomorphicEquation_of_isLinearMap hfin σ _
      (comp (isLinearMap_apply_bond _) (comp hQ' (isLinearMap_transportForm σ)))
      (comp (isLinearMap_apply_bond _) (comp (isLinearMap_transportForm σ) hQ'))
      fun X hX => congrFun (hcomm X hX).2 _⟩
end YangMills.Construction.PeriodicLattice
