import YangMills.Construction.DirichletOperator.ChainOfRemaindersProof
import YangMills.Construction.Dirichlet.BilinearForms
import YangMills.Construction.Dirichlet.CentresAndCells
import YangMills.Construction.Dirichlet.CommutatorBoundsProof
import YangMills.Construction.Dirichlet.CommutatorIdentity
import YangMills.Construction.Dirichlet.RegionEnergyEstimate
import YangMills.Construction.Dirichlet.ShellCrossingChainsOfPaths
import YangMills.Construction.Dirichlet.WeightRecursionBounds
import YangMills.Construction.DirichletOperator.FactsOfTheSettingInLevelUnits
import Mathlib
set_option autoImplicit false
open Set
open YangMills.Construction.Torus YangMills.Construction.Dirichlet YangMills.Construction.WeightedGreen
noncomputable section
namespace YangMills.Construction.LevelUnitFacts
section Numbers
variable {d L : ℕ} {aMinus aPlus : ℝ}
end Numbers
section Distance
variable {d : ℕ} {S : ℝ}
theorem lengthWithin_nonneg (Γ : List (TorusSegment d)) (X : Set (PeriodicTorus d S)) :
    0 ≤ lengthWithin Γ X := by apply _root_.YangMills.Construction.Dirichlet.Crossing.lengthWithin_nonneg <;> assumption
theorem lengthWithin_append (Γ Γ' : List (TorusSegment d)) (X : Set (PeriodicTorus d S)) :
    lengthWithin (Γ ++ Γ') X = lengthWithin Γ X + lengthWithin Γ' X := by
  simp [lengthWithin, List.map_append, List.sum_append]
theorem chainWeightedLength_nonneg {L : ℕ} {ξ : ℝ} (hL : 0 < L) (hξ : 0 < ξ) (t : ℕ)
    (Ω : ℕ → Set (PeriodicTorus d S)) (Γ : List (TorusSegment d)) :
    0 ≤ chainWeightedLength L ξ t Ω Γ := by
  have hL' : (0 : ℝ) < L := by exact_mod_cast hL
  have hs : ∀ n : ℤ, 0 ≤ (scaleSpacing L ξ n)⁻¹ := fun n =>
    inv_nonneg.2 (mul_pos (zpow_pos hL' _) hξ).le
  unfold chainWeightedLength
  exact add_nonneg (Finset.sum_nonneg fun n _ => mul_nonneg (hs n) (lengthWithin_nonneg _ _))
    (mul_nonneg (hs 0) (lengthWithin_nonneg _ _))
theorem chainWeightedLength_append {L : ℕ} {ξ : ℝ} (t : ℕ) (Ω : ℕ → Set (PeriodicTorus d S))
    (Γ Γ' : List (TorusSegment d)) :
    chainWeightedLength L ξ t Ω (Γ ++ Γ') =
      chainWeightedLength L ξ t Ω Γ + chainWeightedLength L ξ t Ω Γ' := by
  unfold chainWeightedLength
  simp only [lengthWithin_append, mul_add, Finset.sum_add_distrib]
  ring
theorem segmentUnion_append (Γ Γ' : List (TorusSegment d)) :
    segmentUnion S (Γ ++ Γ') = segmentUnion S Γ ∪ segmentUnion S Γ' := by
  ext p
  constructor
  · rintro ⟨s, hs, τ, hτ, rfl⟩
    rcases List.mem_append.1 hs with h | h
    · exact Or.inl ⟨s, h, τ, hτ, rfl⟩
    · exact Or.inr ⟨s, h, τ, hτ, rfl⟩
  · rintro (⟨s, h, τ, hτ, rfl⟩ | ⟨s, h, τ, hτ, rfl⟩)
    · exact ⟨s, List.mem_append_left _ h, τ, hτ, rfl⟩
    · exact ⟨s, List.mem_append_right _ h, τ, hτ, rfl⟩
theorem exists_torusProj_eq (p : PeriodicTorus d S) : ∃ v : Fin d → ℝ, torusProj d S v = p := by apply _root_.YangMills.Construction.Dirichlet.Commutator.exists_torusProj_eq <;> assumption
theorem pointAt_continuous (s : TorusSegment d) : Continuous (s.pointAt S) := by
  unfold TorusSegment.pointAt torusProj
  refine continuous_pi fun μ => ?_
  exact (AddCircle.continuous_mk' S).comp (by fun_prop)
theorem exists_connected_segmentUnion (p q : PeriodicTorus d S) :
    ∃ Γ : List (TorusSegment d),
      IsConnected (segmentUnion S Γ) ∧ p ∈ segmentUnion S Γ ∧ q ∈ segmentUnion S Γ := by
  obtain ⟨v, rfl⟩ := exists_torusProj_eq p
  obtain ⟨w, rfl⟩ := exists_torusProj_eq q
  let s : TorusSegment d := ⟨v, w - v⟩
  have hc : segmentUnion S [s] = s.pointAt S '' Icc 0 1 := by
    ext p
    constructor
    · rintro ⟨s', hs', τ, hτ, rfl⟩
      obtain rfl : s' = s := by simpa using hs'
      exact ⟨τ, hτ, rfl⟩
    · rintro ⟨τ, hτ, rfl⟩
      exact ⟨s, by simp, τ, hτ, rfl⟩
  refine ⟨[s], ?_, ?_, ?_⟩
  · rw [hc]
    exact (isConnected_Icc zero_le_one).image _ (pointAt_continuous s).continuousOn
  · exact ⟨s, by simp, 0, by simp, by simp [TorusSegment.pointAt, s]⟩
  · exact ⟨s, by simp, 1, by simp, by simp [TorusSegment.pointAt, s]⟩
def chainLengths (L : ℕ) (ξ : ℝ) (t : ℕ) (Ω : ℕ → Set (PeriodicTorus d S))
    (p q : PeriodicTorus d S) : Set ℝ :=
  {r | ∃ Γ : List (TorusSegment d), IsConnected (segmentUnion S Γ) ∧ p ∈ segmentUnion S Γ ∧
    q ∈ segmentUnion S Γ ∧ r = chainWeightedLength L ξ t Ω Γ}
theorem chainWeightedDist_triangle {L : ℕ} {ξ : ℝ} (hL : 0 < L) (hξ : 0 < ξ) (t : ℕ)
    (Ω : ℕ → Set (PeriodicTorus d S)) (p q q' : PeriodicTorus d S) :
    chainWeightedDist L ξ t Ω p q' ≤
      chainWeightedDist L ξ t Ω p q + chainWeightedDist L ξ t Ω q q' := by
  have hne : ∀ p q, (chainLengths L ξ t Ω p q).Nonempty := fun p q => by
    obtain ⟨Γ, h1, h2, h3⟩ := exists_connected_segmentUnion p q
    exact ⟨_, Γ, h1, h2, h3, rfl⟩
  have hbd : ∀ p q, BddBelow (chainLengths L ξ t Ω p q) := fun p q =>
    ⟨0, by
      rintro _ ⟨Γ, -, -, -, rfl⟩
      exact chainWeightedLength_nonneg hL hξ t Ω Γ⟩
  have key : ∀ a ∈ chainLengths L ξ t Ω p q, ∀ b ∈ chainLengths L ξ t Ω q q',
      sInf (chainLengths L ξ t Ω p q') ≤ a + b := by
    rintro _ ⟨Γ, c, hp, hq, rfl⟩ _ ⟨Γ', c', hq', hq'', rfl⟩
    refine csInf_le (hbd _ _) ⟨Γ ++ Γ', ?_, ?_, ?_, (chainWeightedLength_append t Ω Γ Γ').symm⟩
    · rw [segmentUnion_append]
      exact IsConnected.union ⟨q, hq, hq'⟩ c c'
    · rw [segmentUnion_append]
      exact Or.inl hp
    · rw [segmentUnion_append]
      exact Or.inr hq''
  have h1 : ∀ b ∈ chainLengths L ξ t Ω q q',
      sInf (chainLengths L ξ t Ω p q') - b ≤ sInf (chainLengths L ξ t Ω p q) := fun b hb =>
    le_csInf (hne _ _) fun a ha => by linarith [key a ha b hb]
  have h2 : sInf (chainLengths L ξ t Ω p q') - sInf (chainLengths L ξ t Ω p q) ≤
      sInf (chainLengths L ξ t Ω q q') :=
    le_csInf (hne _ _) fun b hb => by linarith [h1 b hb]
  change sInf (chainLengths L ξ t Ω p q') ≤
    sInf (chainLengths L ξ t Ω p q) + sInf (chainLengths L ξ t Ω q q')
  linarith
end Distance
section Pairings
variable {d : ℕ} {S ξ : ℝ}
theorem restrictTo_of_mem {X : Set (PeriodicTorus d S)} {f : LatticeSite d S ξ → ℝ}
    {x : LatticeSite d S ξ} (hx : (x : PeriodicTorus d S) ∈ X) : restrictTo X f x = f x :=
  Set.indicator_of_mem (s := {x : LatticeSite d S ξ | (x : PeriodicTorus d S) ∈ X}) hx f
theorem restrictTo_of_not_mem {X : Set (PeriodicTorus d S)} {f : LatticeSite d S ξ → ℝ}
    {x : LatticeSite d S ξ} (hx : (x : PeriodicTorus d S) ∉ X) : restrictTo X f x = 0 := by apply _root_.YangMills.Construction.Dirichlet.RemainderChains.restrictTo_of_not_mem <;> assumption
theorem innerSum_eq_sum [Fintype (LatticeSite d S ξ)] (f g : LatticeSite d S ξ → ℝ) :
    innerSum f g = ξ ^ d * ∑ x, f x * g x := by
  unfold innerSum
  rw [finsum_eq_sum_of_fintype]
end Pairings
section Facts
variable {d L : ℕ} {aMinus aPlus S : ℝ}
end Facts
section EvaluationMaps
open scoped Pointwise
variable {L : ℕ} {m K t : ℕ}
def levelUnitScale (L K t : ℕ) : ℝ := (L : ℝ) ^ ((K : ℤ) - (t : ℤ))
theorem levelUnitScale_pos (hL : 0 < L) : 0 < levelUnitScale L K t :=
  zpow_pos (by exact_mod_cast hL) _
theorem unitSide_eq_mul (hL : 0 < L) :
    unitSide L m K t = levelUnitScale L K t * PeriodicLattice.torusSide L m := by
  have hL' : (L : ℝ) ≠ 0 := by exact_mod_cast hL.ne'
  unfold unitSide levelUnitScale PeriodicLattice.torusSide
  rw [show (m : ℤ) + (K : ℤ) - (t : ℤ) = (m : ℤ) + ((K : ℤ) - (t : ℤ)) by ring,
    zpow_add₀ hL', zpow_natCast]
  ring
theorem levelUnitEquiv_torusProj (hL : 0 < L) (v : Fin 4 → ℝ) :
    levelUnitEquiv hL m K t (torusProj 4 (PeriodicLattice.torusSide L m) v) =
      torusProj 4 (unitSide L m K t) (levelUnitScale L K t • v) := by
  have hs := torusSide_ne_zero hL m
  funext μ
  change AddCircle.equivAddCircle _ _ hs (unitSide_ne_zero hL m K t)
    ((v μ : ℝ) : AddCircle (PeriodicLattice.torusSide L m)) = _
  have hk : (PeriodicLattice.torusSide L m)⁻¹ * unitSide L m K t = levelUnitScale L K t := by
    rw [unitSide_eq_mul hL]
    field_simp
  rw [AddCircle.equivAddCircle_apply_mk, hk, mul_comm]
  rfl
theorem supNormVec_eq_norm (v : Fin 4 → ℝ) : TorusMetric.supNormVec v = ‖v‖ := by
  unfold TorusMetric.supNormVec
  apply le_antisymm
  · exact Finset.sup'_le _ _ fun μ _ => by simpa [Real.norm_eq_abs] using norm_le_pi_norm v μ
  · have h0 : 0 ≤ Finset.univ.sup' Finset.univ_nonempty fun μ => |v μ| :=
      (abs_nonneg (v 0)).trans (Finset.le_sup' (fun μ => |v μ|) (Finset.mem_univ 0))
    refine (pi_norm_le_iff_of_nonneg h0).2 fun μ => ?_
    rw [Real.norm_eq_abs]
    exact Finset.le_sup' (fun μ => |v μ|) (Finset.mem_univ μ)
theorem supNorm_levelUnitEquiv (hL : 0 < L) (p : PeriodicLattice.FourTorus L m) :
    supNorm (levelUnitEquiv hL m K t p) = levelUnitScale L K t * TorusMetric.torusSupNorm p := by
  have hc := levelUnitScale_pos (K := K) (t := t) hL
  have hset : {r | ∃ v : Fin 4 → ℝ, torusProj 4 (unitSide L m K t) v =
        levelUnitEquiv hL m K t p ∧ r = ‖v‖} =
      levelUnitScale L K t • (TorusMetric.supNormVec ''
        (TorusMetric.torusProj (PeriodicLattice.torusSide L m) ⁻¹' {p})) := by
    ext r
    constructor
    · rintro ⟨w, hw, rfl⟩
      refine Set.mem_smul_set.2 ⟨‖(levelUnitScale L K t)⁻¹ • w‖,
        ⟨(levelUnitScale L K t)⁻¹ • w, ?_, supNormVec_eq_norm _⟩, ?_⟩
      · apply (levelUnitEquiv hL m K t).injective
        change levelUnitEquiv hL m K t (torusProj 4 _ _) = _
        rw [levelUnitEquiv_torusProj, smul_smul, mul_inv_cancel₀ hc.ne', one_smul, hw]
      · simp only [norm_smul, smul_eq_mul, norm_inv, Real.norm_of_nonneg hc.le]
        field_simp
    · intro hr
      obtain ⟨_, ⟨v, hv, rfl⟩, rfl⟩ := Set.mem_smul_set.1 hr
      have hv' : torusProj 4 (PeriodicLattice.torusSide L m) v = p := hv
      refine ⟨levelUnitScale L K t • v, ?_, ?_⟩
      · rw [← levelUnitEquiv_torusProj, hv']
      · rw [supNormVec_eq_norm, norm_smul, Real.norm_of_nonneg hc.le, smul_eq_mul]
  unfold supNorm TorusMetric.torusSupNorm
  rw [hset, Real.sInf_smul_of_nonneg hc.le, smul_eq_mul]
theorem image_cubeAround (hL : 0 < L) {i : ℤ} (y : PeriodicLattice.Site L m i) :
    levelUnitEquiv hL m K t '' PeriodicLattice.cubeAround y =
      cubeAt (levelUnitEquiv hL m K t y) (levelUnitScale L K t * PeriodicLattice.meshSize L i) := by
  have hc := levelUnitScale_pos (K := K) (t := t) hL
  ext q
  obtain ⟨p, rfl⟩ := (levelUnitEquiv hL m K t).surjective q
  rw [(levelUnitEquiv hL m K t).injective.mem_set_image]
  change TorusMetric.torusSupNorm (p - (y : PeriodicLattice.FourTorus L m)) ≤ _ ↔
    supNorm (levelUnitEquiv hL m K t p - levelUnitEquiv hL m K t y) ≤ _
  rw [← map_sub, supNorm_levelUnitEquiv, mul_div_assoc]
  exact ⟨fun h => mul_le_mul_of_nonneg_left h hc.le, fun h => le_of_mul_le_mul_left h hc⟩
end EvaluationMaps
section Sequences
variable {L : ℕ} {m K t e g : ℕ}
end Sequences
end YangMills.Construction.LevelUnitFacts
