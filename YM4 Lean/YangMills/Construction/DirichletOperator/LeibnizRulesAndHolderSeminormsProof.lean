import YangMills.Construction.DirichletOperator.BondsNearACubeCarriedToItsTorusProof
import YangMills.Construction.DirichletOperator.DivergenceRuleOnTheCubes
import YangMills.Construction.DirichletOperator.InequalitiesOnCubesOfTheFirstKindProof
import Mathlib
set_option autoImplicit false
open Set
open YangMills.Construction.Dirichlet YangMills.Construction.Torus YangMills.Construction.RegionSequence YangMills.Construction.RegionSequence.NestedRegions YangMills.Construction.PartitionCubes
noncomputable section
namespace YangMills.Construction.LeibnizHolder
theorem side_eq_nat_mul_ξ (𝒮 : NestedRegions) : ∃ N : ℕ, 0 < N ∧ 𝒮.side = (N : ℝ) * 𝒮.ξ := by
  obtain ⟨k, hk⟩ := 𝒮.side_mem_zmultiples
  have hL0 : 0 < 𝒮.L := by have := 𝒮.thirteen_le_L; omega
  have hL0' : (0 : ℝ) < 𝒮.L := by exact_mod_cast hL0
  have hsp : 0 < scaleSpacing 𝒮.L 𝒮.ξ (𝒮.s : ℤ) := mul_pos (zpow_pos hL0' _) 𝒮.ξ_pos
  have hk0 : (0 : ℝ) < k := by
    by_contra hneg
    have hle : 𝒮.side ≤ 0 := by
      rw [hk]
      exact mul_nonpos_of_nonpos_of_nonneg (not_lt.mp hneg) (by positivity)
    linarith [𝒮.side_pos]
  have hk1 : 0 < k := by exact_mod_cast hk0
  refine ⟨k.toNat * (2 * 𝒮.L ^ 𝒮.s), Nat.mul_pos (by omega) (by positivity), ?_⟩
  have hc : ((k.toNat : ℕ) : ℝ) = k := by exact_mod_cast Int.toNat_of_nonneg hk1.le
  rw [hk]
  push_cast
  rw [hc]
  simp only [scaleSpacing, zpow_natCast]
  ring
theorem finite_fineSite (hL : TorusLengthsStatement) (𝒮 : NestedRegions) : Finite 𝒮.FineSite := by apply _root_.YangMills.Construction.RegionSequence.DifferenceAdjointsByParts.finite_fineSite <;> assumption
theorem finite_fineBond {𝒮 : NestedRegions} [Finite 𝒮.FineSite] : Finite 𝒮.FineBond := by apply _root_.YangMills.Construction.FirstTypeGreenRegularity.finite_fineBond <;> assumption
section WeightedSums
variable {T : Type}
def weightedSum (c : ℝ) (f g : T → ℝ) : ℝ := c * ∑ᶠ x, f x * g x
theorem weightedSum_eq (c : ℝ) [Fintype T] (f g : T → ℝ) :
    weightedSum c f g = c * ∑ x, f x * g x := by
  rw [weightedSum, finsum_eq_sum_of_fintype]
theorem weightedSum_comm (c : ℝ) (f g : T → ℝ) : weightedSum c f g = weightedSum c g f := by
  simp only [weightedSum, mul_comm (f _)]
theorem weightedSum_sub_left [Finite T] (c : ℝ) (f f' g : T → ℝ) :
    weightedSum c (f - f') g = weightedSum c f g - weightedSum c f' g := by
  have := Fintype.ofFinite T
  simp only [weightedSum_eq, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib, mul_sub]
theorem weightedSum_mul_left [Finite T] (c : ℝ) (m f g : T → ℝ) :
    weightedSum c (m * f) g = weightedSum c f (m * g) := by
  have := Fintype.ofFinite T
  simp only [weightedSum_eq, Pi.mul_apply]
  congr 1
  exact Finset.sum_congr rfl fun x _ => by ring
theorem weightedSum_sum_left [Finite T] (c : ℝ) (u : Fin 4 → T → ℝ) (g : T → ℝ) :
    weightedSum c (∑ ν, u ν) g = ∑ ν, weightedSum c (u ν) g := by
  have := Fintype.ofFinite T
  simp only [weightedSum_eq, Finset.sum_apply, Finset.sum_mul, ← Finset.mul_sum]
  rw [Finset.sum_comm]
theorem weightedSum_laplace_symm [Finite T] (c : ℝ) (D Ds : Fin 4 → (T → ℝ) → T → ℝ)
    (h : ∀ ν f g, weightedSum c (D ν f) g = weightedSum c f (Ds ν g)) (f g : T → ℝ) :
    weightedSum c (∑ ν, Ds ν (D ν f)) g = weightedSum c f (∑ ν, Ds ν (D ν g)) := by
  rw [weightedSum_sum_left, weightedSum_comm c f, weightedSum_sum_left]
  refine Finset.sum_congr rfl fun ν _ => ?_
  rw [weightedSum_comm c _ g, ← h, weightedSum_comm c _ (D ν f), h, weightedSum_comm]
theorem weightedSum_commutator_antisymm [Finite T] (c : ℝ) (m : T → ℝ) (Lap : (T → ℝ) → T → ℝ)
    (h : ∀ f g, weightedSum c (Lap f) g = weightedSum c f (Lap g)) (f g : T → ℝ) :
    weightedSum c (m * Lap f - Lap (m * f)) g = -weightedSum c f (m * Lap g - Lap (m * g)) := by
  rw [weightedSum_sub_left, weightedSum_comm c f, weightedSum_sub_left, weightedSum_mul_left, h, h,
    weightedSum_mul_left, weightedSum_comm c (m * Lap g), weightedSum_comm c (Lap (m * g))]
  ring
end WeightedSums
variable {𝒮 : NestedRegions}
theorem latticeLaplacian_eq_sum (f : 𝒮.FineSite → ℝ) :
    latticeLaplacian f = ∑ ν, backwardDiff ν (forwardDiff ν f) := by
  funext x
  simp only [latticeLaplacian, latticeDiv, Dirichlet.grad, Finset.sum_apply]
theorem latticeLaplacian_apply (f : 𝒮.FineSite → ℝ) (x : 𝒮.FineSite) :
    latticeLaplacian f x = ∑ ν, 𝒮.ξ⁻¹ * (𝒮.ξ⁻¹ * (f x - f (x - unitStep 4 𝒮.side 𝒮.ξ ν)) -
      𝒮.ξ⁻¹ * (f (x + unitStep 4 𝒮.side 𝒮.ξ ν) - f x)) := by
  simp only [latticeLaplacian, latticeDiv, Dirichlet.grad, backwardDiff, forwardDiff, sub_add_cancel]
theorem site_forwardDiff_mul (φ f : 𝒮.FineSite → ℝ) (ν : Fin 4) :
    forwardDiff ν (φ * f) = translateForward ν φ * forwardDiff ν f + forwardDiff ν φ * f := by
  funext x
  simp only [forwardDiff, translateForward, Pi.mul_apply, Pi.add_apply]
  ring
theorem site_mul_backwardDiff (φ f : 𝒮.FineSite → ℝ) (ν : Fin 4) :
    φ * backwardDiff ν f = backwardDiff ν (φ * f) +
      translateBackward ν (forwardDiff ν φ) * translateBackward ν f := by
  funext x
  simp only [forwardDiff, backwardDiff, translateBackward, Pi.mul_apply, Pi.add_apply, sub_add_cancel]
  ring
theorem siteCommutator_eq_sum (φ f : 𝒮.FineSite → ℝ) :
    siteCommutator φ f =
      (∑ ν, (forwardDiff ν φ * forwardDiff ν f + backwardDiff ν φ * backwardDiff ν f)) -
        latticeLaplacian φ * f := by
  funext x
  simp only [siteCommutator, Pi.sub_apply, Pi.mul_apply, Pi.add_apply, Finset.sum_apply,
    latticeLaplacian_apply, forwardDiff, backwardDiff]
  rw [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun ν _ => ?_
  ring
theorem siteCommutator_eq_div (φ f : 𝒮.FineSite → ℝ) :
    siteCommutator φ f =
      -(∑ ν, backwardDiff ν (forwardDiff ν φ * (f + translateForward ν f))) +
        latticeLaplacian φ * f := by
  funext x
  simp only [siteCommutator, Pi.sub_apply, Pi.mul_apply, Pi.add_apply, Pi.neg_apply,
    Finset.sum_apply, latticeLaplacian_apply, forwardDiff, backwardDiff, translateForward,
    sub_add_cancel]
  rw [neg_add_eq_sub, Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib,
    ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun ν _ => ?_
  ring
theorem siteProductRules_holds [Finite 𝒮.FineSite] (hC : CellStructure.CellStructureClaim)
    (φ f : 𝒮.FineSite → ℝ) : SiteProductRules φ f where
  fwdDiff_mul := site_forwardDiff_mul φ f
  mul_bwdDiff := site_mul_backwardDiff φ f
  commutator_eq_sum := siteCommutator_eq_sum φ f
  commutator_eq_div := siteCommutator_eq_div φ f
  commutator_antisymm g := by
    have hsym : ∀ A B : 𝒮.FineSite → ℝ,
        weightedSum (𝒮.ξ ^ 4) (latticeLaplacian A) B =
          weightedSum (𝒮.ξ ^ 4) A (latticeLaplacian B) := by
      intro A B
      rw [latticeLaplacian_eq_sum, latticeLaplacian_eq_sum]
      exact weightedSum_laplace_symm _ (fun ν => forwardDiff ν) (fun ν => backwardDiff ν)
        (fun ν A B => (hC 𝒮).2.2.2.1.site_adjoint ν A B) A B
    exact weightedSum_commutator_antisymm (𝒮.ξ ^ 4) φ latticeLaplacian hsym f g
def bondSlice (f : 𝒮.FineBond → ℝ) (δ : Fin 4) : 𝒮.FineSite → ℝ := fun y => f ⟨y, δ⟩
theorem bondLap_eq_sum (A : 𝒮.FineBond → ℝ) :
    bondLap A = ∑ ν, NestedRegions.bwdDiff ν (NestedRegions.fwdDiff ν A) := by
  funext b
  simp only [bondLap, Finset.sum_apply]
theorem bondProductRules_holds [Finite 𝒮.FineBond] (hC : CellStructure.CellStructureClaim)
    (φ : 𝒮.FineSite → ℝ) (f : 𝒮.FineBond → ℝ) : BondProductRules φ f where
  fwdDiff_mul ν := by
    funext ⟨x, δ⟩
    exact congrFun (site_forwardDiff_mul φ (bondSlice f δ) ν) x
  mul_bwdDiff ν := by
    funext ⟨x, δ⟩
    exact congrFun (site_mul_backwardDiff φ (bondSlice f δ) ν) x
  commutator_eq_sum := by
    funext ⟨x, δ⟩
    have h := congrFun (siteCommutator_eq_sum φ (bondSlice f δ)) x
    simp only [Pi.sub_apply, Finset.sum_apply] at h ⊢
    exact h
  commutator_eq_div := by
    funext ⟨x, δ⟩
    have h := congrFun (siteCommutator_eq_div φ (bondSlice f δ)) x
    simp only [Pi.add_apply, Pi.neg_apply, Finset.sum_apply] at h ⊢
    exact h
  commutator_antisymm g := by
    have hsym : ∀ A B : 𝒮.FineBond → ℝ,
        weightedSum (𝒮.ξ ^ 4) (bondLap A) B = weightedSum (𝒮.ξ ^ 4) A (bondLap B) := by
      intro A B
      rw [bondLap_eq_sum, bondLap_eq_sum]
      exact weightedSum_laplace_symm _ (fun ν => NestedRegions.fwdDiff ν)
        (fun ν => NestedRegions.bwdDiff ν)
        (fun ν A B => (hC 𝒮).2.2.2.1.bond_adjoint ν A B) A B
    exact weightedSum_commutator_antisymm (𝒮.ξ ^ 4) (fun b : 𝒮.FineBond => φ b.source) bondLap
      hsym f g
section Lifts
variable {S : ℝ}
theorem torusProj_add (u v : Fin 4 → ℝ) :
    torusProj 4 S (u + v) = torusProj 4 S u + torusProj 4 S v := by apply _root_.YangMills.Construction.PartitionCubes.CubeTorusAveraging.torusProj_add <;> assumption
theorem torusProj_sub (u v : Fin 4 → ℝ) :
    torusProj 4 S (u - v) = torusProj 4 S u - torusProj 4 S v := by apply _root_.YangMills.Construction.PartitionCubes.CubeTorusBonds.torusProj_sub <;> assumption
theorem torusProj_neg (u : Fin 4 → ℝ) : torusProj 4 S (-u) = -torusProj 4 S u := by apply _root_.YangMills.Construction.PartitionCubes.TorusTransfer.torusProj_neg <;> assumption
theorem exists_lift_abs_le (hS : 0 < S) (hc : Function.Surjective (torusProj 4 S))
    (p : PeriodicTorus 4 S) :
    ∃ v : Fin 4 → ℝ, torusProj 4 S v = p ∧ ∀ u, torusProj 4 S u = p → ∀ μ, |v μ| ≤ |u μ| := by
  obtain ⟨w, rfl⟩ := hc p
  refine ⟨fun μ => w μ - round (S⁻¹ * w μ) * S, ?_, ?_⟩
  · funext μ
    have h0 : (((round (S⁻¹ * w μ) : ℝ) * S : ℝ) : AddCircle S) = 0 :=
      (AddCircle.coe_eq_zero_iff S).2 ⟨round (S⁻¹ * w μ), by simp⟩
    show ((w μ - round (S⁻¹ * w μ) * S : ℝ) : AddCircle S) = (w μ : AddCircle S)
    rw [AddCircle.coe_sub, h0, sub_zero]
  · intro u hu μ
    have h1 : ((u μ : ℝ) : AddCircle S) = (w μ : AddCircle S) := congrFun hu μ
    have h2 : |w μ - round (S⁻¹ * w μ) * S| = ‖(w μ : AddCircle S)‖ := (AddCircle.norm_eq S).symm
    show |w μ - round (S⁻¹ * w μ) * S| ≤ |u μ|
    rw [h2, ← h1, AddCircle.norm_eq' S hS]
    have h3 := round_le (S⁻¹ * u μ) 0
    have h4 : S * |S⁻¹ * u μ| = |u μ| := by
      rw [abs_mul, abs_inv, abs_of_pos hS, ← mul_assoc, mul_inv_cancel₀ hS.ne', one_mul]
    simp only [Int.cast_zero, sub_zero] at h3
    calc S * |S⁻¹ * u μ - (round (S⁻¹ * u μ) : ℝ)| ≤ S * |S⁻¹ * u μ| :=
          mul_le_mul_of_nonneg_left h3 hS.le
      _ = |u μ| := h4
theorem lOneNorm_eq_of_minimal {p : PeriodicTorus 4 S} {v : Fin 4 → ℝ} (hv : torusProj 4 S v = p)
    (hm : ∀ u, torusProj 4 S u = p → ∀ μ, |v μ| ≤ |u μ|) : lOneNorm p = ∑ μ, |v μ| := by
  refine le_antisymm (csInf_le ⟨0, ?_⟩ ⟨v, hv, rfl⟩) (le_csInf ⟨_, v, hv, rfl⟩ ?_)
  · rintro r ⟨u, -, rfl⟩
    exact Finset.sum_nonneg fun μ _ => abs_nonneg _
  · rintro r ⟨u, hu, rfl⟩
    exact Finset.sum_le_sum fun μ _ => hm u hu μ
theorem supNorm_le_norm_lift {p : PeriodicTorus 4 S} {v : Fin 4 → ℝ} (hv : torusProj 4 S v = p) :
    supNorm p ≤ ‖v‖ :=
  csInf_le ⟨0, by rintro r ⟨u, -, rfl⟩; exact norm_nonneg _⟩ ⟨v, hv, rfl⟩
theorem supNorm_eq_of_minimal {p : PeriodicTorus 4 S} {v : Fin 4 → ℝ} (hv : torusProj 4 S v = p)
    (hm : ∀ u, torusProj 4 S u = p → ∀ μ, |v μ| ≤ |u μ|) : supNorm p = ‖v‖ := by
  refine le_antisymm (supNorm_le_norm_lift hv) (le_csInf ⟨_, v, hv, rfl⟩ ?_)
  rintro r ⟨u, hu, rfl⟩
  refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun μ => ?_
  rw [Real.norm_eq_abs]
  exact (hm u hu μ).trans (by rw [← Real.norm_eq_abs]; exact norm_le_pi_norm u μ)
theorem exists_int_lift {ξ : ℝ} {N : ℕ} (hS : S = (N : ℝ) * ξ) {u : Fin 4 → ℝ}
    (hu : torusProj 4 S u ∈ spacingLattice 4 S ξ) : ∃ m : Fin 4 → ℤ, ∀ μ, u μ = (m μ : ℝ) * ξ := by
  obtain ⟨k, hk⟩ := hu
  have h : ∀ μ, ∃ n : ℤ, u μ = ((k μ : ℝ) + (n : ℝ) * (N : ℝ)) * ξ := by
    intro μ
    have h1 : ((u μ : ℝ) : AddCircle S) = (((k μ : ℝ) * ξ : ℝ) : AddCircle S) := congrFun hk μ
    have h2 : ((u μ - (k μ : ℝ) * ξ : ℝ) : AddCircle S) = 0 := by
      rw [AddCircle.coe_sub, h1, sub_self]
    obtain ⟨n, hn⟩ := (AddCircle.coe_eq_zero_iff S).1 h2
    refine ⟨n, ?_⟩
    rw [zsmul_eq_mul, hS] at hn
    linear_combination (-1 : ℝ) * hn
  choose n hn using h
  refine ⟨fun μ => k μ + n μ * (N : ℤ), fun μ => ?_⟩
  rw [hn μ]
  push_cast
  ring
end Lifts
theorem sum_natAbs_update (m : Fin 4 → ℤ) (μ : Fin 4) (k : ℤ) (hk : k.natAbs + 1 = (m μ).natAbs) :
    ∑ ν, (Function.update m μ k ν).natAbs + 1 = ∑ ν, (m ν).natAbs := by
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ μ),
    ← Finset.add_sum_erase (f := fun ν => (m ν).natAbs) _ (Finset.mem_univ μ)]
  have h : ∑ ν ∈ Finset.univ.erase μ, (Function.update m μ k ν).natAbs =
      ∑ ν ∈ Finset.univ.erase μ, (m ν).natAbs :=
    Finset.sum_congr rfl fun ν hν => by
      rw [Function.update_of_ne (Finset.ne_of_mem_erase hν)]
  rw [h, Function.update_self]
  omega
theorem coe_unitStep (ν : Fin 4) :
    ((unitStep 4 𝒮.side 𝒮.ξ ν : 𝒮.FineSite) : 𝒮.Point) = torusProj 4 𝒮.side (Pi.single ν 𝒮.ξ) :=
  rfl
theorem abs_sub_le_of_walk {g : 𝒮.FineSite → ℝ} {G : ℝ} (lo hi : Fin 4 → ℝ)
    (hG : ∀ (a : Fin 4 → ℝ) (y : 𝒮.FineSite), (∀ μ, a μ ∈ Icc (lo μ) (hi μ)) →
      (y : 𝒮.Point) = torusProj 4 𝒮.side a → ∀ ν, |forwardDiff ν g y| ≤ G) :
    ∀ (n : ℕ) (m : Fin 4 → ℤ) (a : Fin 4 → ℝ) (x x' : 𝒮.FineSite), ∑ μ, (m μ).natAbs = n →
      (∀ μ, a μ ∈ Icc (lo μ) (hi μ)) → (∀ μ, a μ + (m μ : ℝ) * 𝒮.ξ ∈ Icc (lo μ) (hi μ)) →
      (x : 𝒮.Point) = torusProj 4 𝒮.side a →
      (x' : 𝒮.Point) = torusProj 4 𝒮.side (fun μ => a μ + (m μ : ℝ) * 𝒮.ξ) →
      |g x' - g x| ≤ (n : ℝ) * 𝒮.ξ * G := by
  have hξ := 𝒮.ξ_pos
  intro n
  induction n with
  | zero =>
    intro m a x x' hs _ _ hx hx'
    have hm : ∀ μ, m μ = 0 := fun μ =>
      Int.natAbs_eq_zero.1 ((Finset.sum_eq_zero_iff.1 hs) μ (Finset.mem_univ _))
    have hxx : x' = x := Subtype.ext (by
      rw [hx', hx]
      congr 1
      funext μ
      simp [hm μ])
    simp [hxx]
  | succ n ih =>
    intro m a x x' hs ha ha' hx hx'
    obtain ⟨μ, hμ⟩ : ∃ μ, m μ ≠ 0 := by
      by_contra hne
      have hne' : ∀ μ, m μ = 0 := fun μ => by_contra fun h => hne ⟨μ, h⟩
      simp [hne'] at hs
    have hcast : ((n + 1 : ℕ) : ℝ) * 𝒮.ξ * G = (n : ℝ) * 𝒮.ξ * G + 𝒮.ξ * G := by
      push_cast
      ring
    rcases lt_or_gt_of_ne hμ with hneg | hpos
    · have hm1 : (m μ : ℝ) ≤ -1 := by exact_mod_cast (by omega : m μ ≤ -1)
      set a₁ : Fin 4 → ℝ := a - Pi.single μ 𝒮.ξ with ha₁
      set m₁ : Fin 4 → ℤ := Function.update m μ (m μ + 1) with hm₁
      have hs₁ : ∑ ν, (m₁ ν).natAbs = n := by
        have h := sum_natAbs_update m μ (m μ + 1) (by omega)
        rw [← hm₁] at h
        omega
      have hbox : ∀ ν, a₁ ν ∈ Icc (lo ν) (hi ν) := by
        intro ν
        by_cases h : ν = μ
        · subst h
          have h1 := ha ν
          have h2 := ha' ν
          simp only [ha₁, Pi.sub_apply, Pi.single_eq_same, mem_Icc] at h1 h2 ⊢
          have h3 : (m ν : ℝ) * 𝒮.ξ ≤ -𝒮.ξ := by nlinarith
          constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]
        · simpa [ha₁, Pi.single_eq_of_ne h] using ha ν
      have hsame : (fun ν => a₁ ν + (m₁ ν : ℝ) * 𝒮.ξ) = fun ν => a ν + (m ν : ℝ) * 𝒮.ξ := by
        funext ν
        by_cases h : ν = μ
        · subst h
          simp only [ha₁, hm₁, Pi.sub_apply, Pi.single_eq_same, Function.update_self]
          push_cast
          ring
        · simp [ha₁, hm₁, Pi.single_eq_of_ne h, Function.update_of_ne h]
      have hx₁ : ((x - unitStep 4 𝒮.side 𝒮.ξ μ : 𝒮.FineSite) : 𝒮.Point) =
          torusProj 4 𝒮.side a₁ := by
        rw [ha₁, torusProj_sub, ← hx, ← coe_unitStep]
        rfl
      have h1 := ih m₁ a₁ (x - unitStep 4 𝒮.side 𝒮.ξ μ) x' hs₁ hbox
        (fun ν => by
          have h : a₁ ν + (m₁ ν : ℝ) * 𝒮.ξ = a ν + (m ν : ℝ) * 𝒮.ξ := congrFun hsame ν
          rw [h]
          exact ha' ν) hx₁
        (by rw [hsame]; exact hx')
      have h2 := hG a₁ (x - unitStep 4 𝒮.side 𝒮.ξ μ) hbox hx₁ μ
      have h3 : |g x - g (x - unitStep 4 𝒮.side 𝒮.ξ μ)| ≤ 𝒮.ξ * G := by
        have e : g x - g (x - unitStep 4 𝒮.side 𝒮.ξ μ) =
            𝒮.ξ * forwardDiff μ g (x - unitStep 4 𝒮.side 𝒮.ξ μ) := by
          simp only [forwardDiff, sub_add_cancel]
          field_simp
        rw [e, abs_mul, abs_of_pos hξ]
        exact mul_le_mul_of_nonneg_left h2 hξ.le
      rw [hcast]
      calc |g x' - g x| ≤ |g x' - g (x - unitStep 4 𝒮.side 𝒮.ξ μ)| +
            |g (x - unitStep 4 𝒮.side 𝒮.ξ μ) - g x| := abs_sub_le _ _ _
        _ ≤ (n : ℝ) * 𝒮.ξ * G + 𝒮.ξ * G := by
            rw [abs_sub_comm (g (x - unitStep 4 𝒮.side 𝒮.ξ μ))]
            exact add_le_add h1 h3
    · have hm1 : (1 : ℝ) ≤ m μ := by exact_mod_cast (by omega : 1 ≤ m μ)
      set a₁ : Fin 4 → ℝ := a + Pi.single μ 𝒮.ξ with ha₁
      set m₁ : Fin 4 → ℤ := Function.update m μ (m μ - 1) with hm₁
      have hs₁ : ∑ ν, (m₁ ν).natAbs = n := by
        have h := sum_natAbs_update m μ (m μ - 1) (by omega)
        rw [← hm₁] at h
        omega
      have hbox : ∀ ν, a₁ ν ∈ Icc (lo ν) (hi ν) := by
        intro ν
        by_cases h : ν = μ
        · subst h
          have h1 := ha ν
          have h2 := ha' ν
          simp only [ha₁, Pi.add_apply, Pi.single_eq_same, mem_Icc] at h1 h2 ⊢
          have h3 : 𝒮.ξ ≤ (m ν : ℝ) * 𝒮.ξ := by nlinarith
          constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]
        · simpa [ha₁, Pi.single_eq_of_ne h] using ha ν
      have hsame : (fun ν => a₁ ν + (m₁ ν : ℝ) * 𝒮.ξ) = fun ν => a ν + (m ν : ℝ) * 𝒮.ξ := by
        funext ν
        by_cases h : ν = μ
        · subst h
          simp only [ha₁, hm₁, Pi.add_apply, Pi.single_eq_same, Function.update_self]
          push_cast
          ring
        · simp [ha₁, hm₁, Pi.single_eq_of_ne h, Function.update_of_ne h]
      have hx₁ : ((x + unitStep 4 𝒮.side 𝒮.ξ μ : 𝒮.FineSite) : 𝒮.Point) =
          torusProj 4 𝒮.side a₁ := by
        rw [ha₁, torusProj_add, ← hx, ← coe_unitStep]
        rfl
      have h1 := ih m₁ a₁ (x + unitStep 4 𝒮.side 𝒮.ξ μ) x' hs₁ hbox
        (fun ν => by
          have h : a₁ ν + (m₁ ν : ℝ) * 𝒮.ξ = a ν + (m ν : ℝ) * 𝒮.ξ := congrFun hsame ν
          rw [h]
          exact ha' ν) hx₁
        (by rw [hsame]; exact hx')
      have h2 := hG a x ha hx μ
      have h3 : |g (x + unitStep 4 𝒮.side 𝒮.ξ μ) - g x| ≤ 𝒮.ξ * G := by
        have e : g (x + unitStep 4 𝒮.side 𝒮.ξ μ) - g x = 𝒮.ξ * forwardDiff μ g x := by
          simp only [forwardDiff]
          field_simp
        rw [e, abs_mul, abs_of_pos hξ]
        exact mul_le_mul_of_nonneg_left h2 hξ.le
      rw [hcast]
      calc |g x' - g x| ≤ |g x' - g (x + unitStep 4 𝒮.side 𝒮.ξ μ)| +
            |g (x + unitStep 4 𝒮.side 𝒮.ξ μ) - g x| := abs_sub_le _ _ _
        _ ≤ (n : ℝ) * 𝒮.ξ * G + 𝒮.ξ * G := add_le_add h1 h3
theorem abs_sub_le_along {g : 𝒮.FineSite → ℝ} {G : ℝ} {X : Set 𝒮.Point} (x x' : 𝒮.FineSite)
    (a w : Fin 4 → ℝ) (hx : (x : 𝒮.Point) = torusProj 4 𝒮.side a)
    (hx' : (x' : 𝒮.Point) = torusProj 4 𝒮.side (a + w))
    (hbox : ∀ b : Fin 4 → ℝ, (∀ μ, b μ ∈ uIcc (a μ) (a μ + w μ)) → torusProj 4 𝒮.side b ∈ X)
    (hG : ∀ y : 𝒮.FineSite, (y : 𝒮.Point) ∈ X → ∀ ν, |forwardDiff ν g y| ≤ G) :
    |g x' - g x| ≤ (∑ μ, |w μ|) * G := by
  obtain ⟨N, -, hN⟩ := side_eq_nat_mul_ξ 𝒮
  have hξ := 𝒮.ξ_pos
  have hcw : torusProj 4 𝒮.side w = ((x' - x : 𝒮.FineSite) : 𝒮.Point) := by
    have h : ((x' - x : 𝒮.FineSite) : 𝒮.Point) = (x' : 𝒮.Point) - (x : 𝒮.Point) := rfl
    rw [h, hx', hx, torusProj_add]
    abel
  obtain ⟨m, hm⟩ := exists_int_lift hN (u := w) (by rw [hcw]; exact (x' - x).2)
  have hwalk := abs_sub_le_of_walk (g := g) (G := G) (fun μ => a μ ⊓ (a μ + w μ))
    (fun μ => a μ ⊔ (a μ + w μ))
    (fun b y hb hy ν => hG y (by rw [hy]; exact hbox b hb) ν) _ m a x x' rfl
    (fun μ => ⟨inf_le_left, le_sup_left⟩)
    (fun μ => by rw [← hm μ]; exact ⟨inf_le_right, le_sup_right⟩) hx
    (by
      rw [hx']
      congr 1
      funext μ
      simp [hm μ])
  have hsum : ((∑ μ, (m μ).natAbs : ℕ) : ℝ) * 𝒮.ξ = ∑ μ, |w μ| := by
    push_cast
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun μ _ => ?_
    rw [hm μ, abs_mul, abs_of_pos hξ, Nat.cast_natAbs, Int.cast_abs]
  rwa [hsum] at hwalk
theorem abs_sub_le_siteLOneDist_mul (hLen : LengthAxioms 4 𝒮.side) {lam : ℝ} {X : Set 𝒮.Point}
    (hX : IsTorusOrSmallCube lam X) {g : 𝒮.FineSite → ℝ} {G : ℝ}
    (hG : ∀ y : 𝒮.FineSite, (y : 𝒮.Point) ∈ X → ∀ ν, |forwardDiff ν g y| ≤ G)
    {x x' : 𝒮.FineSite} (hx : (x : 𝒮.Point) ∈ X) (hx' : (x' : 𝒮.Point) ∈ X)
    (h1 : siteLOneDist x x' ≤ lam) :
    |g x' - g x| ≤ siteLOneDist x x' * G := by
  have hS := 𝒮.side_pos
  have hsurj := hLen.torusProj_surjective
  obtain ⟨v, hv, hvm⟩ := exists_lift_abs_le hS hsurj ((x : 𝒮.Point) - (x' : 𝒮.Point))
  have hd : siteLOneDist x x' = ∑ μ, |v μ| := lOneNorm_eq_of_minimal hv hvm
  rcases hX with rfl | ⟨c, σ, hσ, hσs, rfl⟩
  · obtain ⟨a, ha⟩ := hsurj (x : 𝒮.Point)
    have h := abs_sub_le_along (g := g) (G := G) (X := univ) x x' a (-v) ha.symm
      (by rw [torusProj_add, torusProj_neg, ha, hv]; abel) (fun _ _ => mem_univ _) hG
    simp only [Pi.neg_apply, abs_neg] at h
    rwa [hd]
  · obtain ⟨cl, hc⟩ := hsurj c
    obtain ⟨u, hu, hum⟩ := exists_lift_abs_le hS hsurj ((x : 𝒮.Point) - c)
    obtain ⟨u', hu', hum'⟩ := exists_lift_abs_le hS hsurj ((x' : 𝒮.Point) - c)
    have hub : ∀ μ, |u μ| ≤ σ / 2 := fun μ => by
      have h : ‖u‖ ≤ σ / 2 := by
        rw [← supNorm_eq_of_minimal hu hum]
        exact hx
      rw [← Real.norm_eq_abs]
      exact (norm_le_pi_norm u μ).trans h
    have hub' : ∀ μ, |u' μ| ≤ σ / 2 := fun μ => by
      have h : ‖u'‖ ≤ σ / 2 := by
        rw [← supNorm_eq_of_minimal hu' hum']
        exact hx'
      rw [← Real.norm_eq_abs]
      exact (norm_le_pi_norm u' μ).trans h
    have hvle : ∀ μ, |v μ| ≤ lam := fun μ => by
      have h : |v μ| ≤ ∑ ν, |v ν| :=
        Finset.single_le_sum (f := fun ν => |v ν|) (fun ν _ => abs_nonneg _) (Finset.mem_univ μ)
      linarith
    have hcov : torusProj 4 𝒮.side (u - u') = (x : 𝒮.Point) - (x' : 𝒮.Point) := by
      rw [torusProj_sub, hu, hu']
      abel
    have hw : ∀ μ, |u' μ - u μ| = |v μ| := by
      intro μ
      have h1' : ((u μ - u' μ : ℝ) : AddCircle 𝒮.side) = (v μ : AddCircle 𝒮.side) :=
        (congrFun hcov μ).trans (congrFun hv μ).symm
      have h2 : ((u μ - u' μ - v μ : ℝ) : AddCircle 𝒮.side) = 0 := by
        rw [AddCircle.coe_sub, h1', sub_self]
      obtain ⟨n, hn⟩ := (AddCircle.coe_eq_zero_iff 𝒮.side).1 h2
      rw [zsmul_eq_mul] at hn
      by_cases hn0 : n = 0
      · have : v μ = -(u' μ - u μ) := by
          rw [hn0] at hn
          simp only [Int.cast_zero, zero_mul] at hn
          linarith
        rw [this, abs_neg]
      · exfalso
        have hn1 : (1 : ℝ) ≤ |(n : ℝ)| := by
          have : 1 ≤ |n| := Int.one_le_abs hn0
          exact_mod_cast this
        have hb : 𝒮.side ≤ |(n : ℝ) * 𝒮.side| := by
          rw [abs_mul, abs_of_pos hS]
          nlinarith
        rw [hn] at hb
        have h3 : |u μ - u' μ - v μ| ≤ |u μ| + |u' μ| + |v μ| :=
          (abs_sub _ _).trans (add_le_add_left (abs_sub _ _) _)
        linarith [hub μ, hub' μ, hvle μ]
    have hxa : (x : 𝒮.Point) = torusProj 4 𝒮.side (cl + u) := by
      rw [torusProj_add, hc, hu]
      abel
    have hxa' : (x' : 𝒮.Point) = torusProj 4 𝒮.side ((cl + u) + (u' - u)) := by
      have e : (cl + u) + (u' - u) = cl + u' := by abel
      rw [e, torusProj_add, hc, hu']
      abel
    have h := abs_sub_le_along (g := g) (G := G) (X := cubeAt c σ) x x' (cl + u) (u' - u) hxa hxa'
      (by
        intro b hb
        have hlift : torusProj 4 𝒮.side (b - cl) = torusProj 4 𝒮.side b - c := by
          rw [torusProj_sub, hc]
        show supNorm (torusProj 4 𝒮.side b - c) ≤ σ / 2
        refine (supNorm_le_norm_lift hlift).trans
          ((pi_norm_le_iff_of_nonneg (by positivity)).2 fun μ => ?_)
        have hbμ := hb μ
        simp only [Pi.add_apply, Pi.sub_apply] at hbμ
        rw [mem_uIcc] at hbμ
        have e1 := abs_le.1 (hub μ)
        have e2 := abs_le.1 (hub' μ)
        rw [Real.norm_eq_abs, abs_le]
        simp only [Pi.sub_apply]
        rcases hbμ with ⟨p, q⟩ | ⟨p, q⟩ <;> constructor <;> linarith [e1.1, e1.2, e2.1, e2.2])
      hG
    simp only [Pi.sub_apply, hw] at h
    rwa [hd]
section Seminorms
set_option linter.unusedSectionVars false
theorem bddAbove_of_forall_pair {P : Type} [Finite P] (g : P → P → ℝ) (A : Set ℝ)
    (h : ∀ r ∈ A, ∃ x x', r = g x x') : BddAbove A :=
  (Set.finite_range fun p : P × P => g p.1 p.2).bddAbove.mono fun r hr => by
    obtain ⟨x, x', rfl⟩ := h r hr
    exact ⟨(x, x'), rfl⟩
theorem bddAbove_of_forall_value {P : Type} [Finite P] (g : P → ℝ) (A : Set ℝ)
    (h : ∀ r ∈ A, ∃ x, r = g x) : BddAbove A :=
  (Set.finite_range g).bddAbove.mono fun r hr => by
    obtain ⟨x, rfl⟩ := h r hr
    exact ⟨x, rfl⟩
theorem ratio_rpow_nonneg {lam d α : ℝ} (h0 : 0 < d) (h1 : d ≤ lam) : 0 ≤ (lam / d) ^ α :=
  Real.rpow_nonneg (div_nonneg (h0.le.trans h1) h0.le) _
theorem ratio_rpow_mul_le {lam d α : ℝ} (hα : α < 1) (h0 : 0 < d) (h1 : d ≤ lam) :
    (lam / d) ^ α * d ≤ lam := by
  have hq : 1 ≤ lam / d := (one_le_div h0).2 h1
  have h : (lam / d) ^ α ≤ lam / d := by
    calc (lam / d) ^ α ≤ (lam / d) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hq hα.le
      _ = lam / d := Real.rpow_one _
  calc (lam / d) ^ α * d ≤ lam / d * d := mul_le_mul_of_nonneg_right h h0.le
    _ = lam := div_mul_cancel₀ _ h0.ne'
variable [Finite 𝒮.FineSite] [Finite 𝒮.FineBond]
theorem abs_le_supNormOn {X : Set 𝒮.Point} (f : 𝒮.FineSite → ℝ) {x : 𝒮.FineSite}
    (hx : (x : 𝒮.Point) ∈ X) : |f x| ≤ supNormOn X f :=
  le_csSup (bddAbove_of_forall_value (fun x => |f x|) _ (by rintro r ⟨x, -, rfl⟩; exact ⟨x, rfl⟩))
    ⟨x, hx, rfl⟩
theorem supNormOn_nonneg (X : Set 𝒮.Point) (f : 𝒮.FineSite → ℝ) : 0 ≤ supNormOn X f :=
  Real.sSup_nonneg (by rintro r ⟨x, -, rfl⟩; exact abs_nonneg _)
theorem abs_le_supBondOn {X : Set 𝒮.Point} (f : 𝒮.FineBond → ℝ) {b : 𝒮.FineBond}
    (hb : (b.source : 𝒮.Point) ∈ X) : |f b| ≤ supBondOn X f :=
  le_csSup (bddAbove_of_forall_value (fun b => |f b|) _ (by rintro r ⟨b, -, rfl⟩; exact ⟨b, rfl⟩))
    ⟨b, hb, rfl⟩
theorem supBondOn_nonneg (X : Set 𝒮.Point) (f : 𝒮.FineBond → ℝ) : 0 ≤ supBondOn X f :=
  Real.sSup_nonneg (by rintro r ⟨b, -, rfl⟩; exact abs_nonneg _)
theorem norm_le_supSite (f : 𝒮.FineSite → ℝ) (x : 𝒮.FineSite) : ‖f x‖ ≤ supSite f :=
  le_ciSup (f := fun x => ‖f x‖) (Set.finite_range _).bddAbove x
theorem supSite_nonneg (f : 𝒮.FineSite → ℝ) : 0 ≤ supSite f :=
  Real.iSup_nonneg fun _ => norm_nonneg _
theorem norm_le_supBond (f : 𝒮.FineBond → ℝ) (b : 𝒮.FineBond) : ‖f b‖ ≤ supBond f :=
  le_ciSup (f := fun b => ‖f b‖) (Set.finite_range _).bddAbove b
theorem supBond_nonneg (f : 𝒮.FineBond → ℝ) : 0 ≤ supBond f :=
  Real.iSup_nonneg fun _ => norm_nonneg _
theorem le_holderSite (α lam : ℝ) (f : 𝒮.FineSite → ℝ) {x x' : 𝒮.FineSite}
    (h0 : 0 < siteLOneDist x x') (h1 : siteLOneDist x x' ≤ lam) :
    (lam / siteLOneDist x x') ^ α * ‖f x' - f x‖ ≤ holderSite α lam f :=
  le_csSup (bddAbove_of_forall_pair (fun x x' => (lam / siteLOneDist x x') ^ α * ‖f x' - f x‖) _
    (by rintro r ⟨x, x', -, -, rfl⟩; exact ⟨x, x', rfl⟩)) ⟨x, x', h0, h1, rfl⟩
theorem holderSite_nonneg (α lam : ℝ) (f : 𝒮.FineSite → ℝ) : 0 ≤ holderSite α lam f :=
  Real.sSup_nonneg (by
    rintro r ⟨x, x', h0, h1, rfl⟩
    exact mul_nonneg (ratio_rpow_nonneg h0 h1) (norm_nonneg _))
theorem le_holderBond (α lam : ℝ) (f : 𝒮.FineBond → ℝ) {b b' : 𝒮.FineBond}
    (hd : b.dir = b'.dir) (h0 : 0 < siteLOneDist b.source b'.source)
    (h1 : siteLOneDist b.source b'.source ≤ lam) :
    (lam / siteLOneDist b.source b'.source) ^ α * ‖f b' - f b‖ ≤ holderBond α lam f :=
  le_csSup (bddAbove_of_forall_pair (fun b b' : 𝒮.FineBond =>
      (lam / siteLOneDist b.source b'.source) ^ α * ‖f b' - f b‖) _
    (by rintro r ⟨b, b', -, -, -, rfl⟩; exact ⟨b, b', rfl⟩)) ⟨b, b', hd, h0, h1, rfl⟩
theorem holderBond_nonneg (α lam : ℝ) (f : 𝒮.FineBond → ℝ) : 0 ≤ holderBond α lam f :=
  Real.sSup_nonneg (by
    rintro r ⟨b, b', -, h0, h1, rfl⟩
    exact mul_nonneg (ratio_rpow_nonneg h0 h1) (norm_nonneg _))
theorem le_holderSiteOn (α lam : ℝ) {X : Set 𝒮.Point} (f : 𝒮.FineSite → ℝ) {x x' : 𝒮.FineSite}
    (hx : (x : 𝒮.Point) ∈ X) (hx' : (x' : 𝒮.Point) ∈ X)
    (h0 : 0 < siteLOneDist x x') (h1 : siteLOneDist x x' ≤ lam) :
    (lam / siteLOneDist x x') ^ α * ‖f x' - f x‖ ≤ holderSiteOn α lam X f :=
  le_csSup (bddAbove_of_forall_pair (fun x x' => (lam / siteLOneDist x x') ^ α * ‖f x' - f x‖) _
    (by rintro r ⟨x, x', -, -, -, -, rfl⟩; exact ⟨x, x', rfl⟩)) ⟨x, x', hx, hx', h0, h1, rfl⟩
theorem holderSiteOn_nonneg (α lam : ℝ) (X : Set 𝒮.Point) (f : 𝒮.FineSite → ℝ) :
    0 ≤ holderSiteOn α lam X f :=
  Real.sSup_nonneg (by
    rintro r ⟨x, x', -, -, h0, h1, rfl⟩
    exact mul_nonneg (ratio_rpow_nonneg h0 h1) (norm_nonneg _))
theorem le_holderBondOn (α lam : ℝ) {X : Set 𝒮.Point} (f : 𝒮.FineBond → ℝ) {b b' : 𝒮.FineBond}
    (hb : (b.source : 𝒮.Point) ∈ X) (hb' : (b'.source : 𝒮.Point) ∈ X)
    (hd : b.dir = b'.dir) (h0 : 0 < siteLOneDist b.source b'.source)
    (h1 : siteLOneDist b.source b'.source ≤ lam) :
    (lam / siteLOneDist b.source b'.source) ^ α * ‖f b' - f b‖ ≤ holderBondOn α lam X f :=
  le_csSup (bddAbove_of_forall_pair (fun b b' : 𝒮.FineBond =>
      (lam / siteLOneDist b.source b'.source) ^ α * ‖f b' - f b‖) _
    (by rintro r ⟨b, b', -, -, -, -, -, rfl⟩; exact ⟨b, b', rfl⟩))
    ⟨b, b', hb, hb', hd, h0, h1, rfl⟩
theorem holderBondOn_nonneg (α lam : ℝ) (X : Set 𝒮.Point) (f : 𝒮.FineBond → ℝ) :
    0 ≤ holderBondOn α lam X f :=
  Real.sSup_nonneg (by
    rintro r ⟨b, b', -, -, -, h0, h1, rfl⟩
    exact mul_nonneg (ratio_rpow_nonneg h0 h1) (norm_nonneg _))
theorem mul_sub_mul_bound {a mx my fx fy F N B T : ℝ} (ha : 0 ≤ a) (hfy : |fy| ≤ F)
    (hmx : |mx| ≤ B) (hN : a * ‖my - mx‖ ≤ N) (hT : a * ‖fy - fx‖ ≤ T) :
    a * ‖my * fy - mx * fx‖ ≤ F * N + B * T := by
  have hB : 0 ≤ B := (abs_nonneg _).trans hmx
  have hN0 : 0 ≤ N := (mul_nonneg ha (norm_nonneg _)).trans hN
  have e : my * fy - mx * fx = (my - mx) * fy + mx * (fy - fx) := by ring
  have n1 : ‖my * fy - mx * fx‖ ≤ ‖my - mx‖ * |fy| + |mx| * ‖fy - fx‖ := by
    rw [e]
    exact (norm_add_le _ _).trans
      (by rw [norm_mul, norm_mul, Real.norm_eq_abs fy, Real.norm_eq_abs mx])
  calc a * ‖my * fy - mx * fx‖ ≤ a * (‖my - mx‖ * |fy| + |mx| * ‖fy - fx‖) :=
        mul_le_mul_of_nonneg_left n1 ha
    _ = (a * ‖my - mx‖) * |fy| + |mx| * (a * ‖fy - fx‖) := by ring
    _ ≤ N * F + B * T :=
        add_le_add (mul_le_mul hN hfy (abs_nonneg _) hN0)
          (mul_le_mul hmx hT (mul_nonneg ha (norm_nonneg _)) hB)
    _ = F * N + B * T := by ring
theorem mem_supThickening {X : Set 𝒮.Point} {lam : ℝ} {p q : 𝒮.Point} (hq : q ∈ X)
    (h : supNorm (p - q) ≤ lam) : p ∈ supThickening X lam := by
  show supSetDist {p} X ≤ ENNReal.ofReal lam
  unfold supSetDist
  exact iInf₂_le_of_le p rfl (iInf₂_le_of_le q hq (ENNReal.ofReal_le_ofReal h))
theorem weighted_mul_sub_le {P : Type} (hLen : LengthAxioms 4 𝒮.side) (tl : P → 𝒮.FineSite)
    (φ : 𝒮.FineSite → ℝ) (f : P → ℝ) (X : Set 𝒮.Point) {α lam F N B T : ℝ} {x y : P}
    (h0 : 0 < siteLOneDist (tl x) (tl y)) (h1 : siteLOneDist (tl x) (tl y) ≤ lam)
    (hsupp : ∀ z : 𝒮.FineSite, φ z ≠ 0 → (z : 𝒮.Point) ∈ X)
    (hF : ∀ z, (tl z : 𝒮.Point) ∈ supThickening X lam → |f z| ≤ F) (F0 : 0 ≤ F)
    (hB : ∀ z, |φ z| ≤ B) (B0 : 0 ≤ B)
    (hN : (lam / siteLOneDist (tl x) (tl y)) ^ α * ‖φ (tl y) - φ (tl x)‖ ≤ N) (N0 : 0 ≤ N)
    (hT : (tl x : 𝒮.Point) ∈ supThickening X lam →
      (tl y : 𝒮.Point) ∈ supThickening X lam →
      (lam / siteLOneDist (tl x) (tl y)) ^ α * ‖f y - f x‖ ≤ T) (T0 : 0 ≤ T) :
    (lam / siteLOneDist (tl x) (tl y)) ^ α * ‖φ (tl y) * f y - φ (tl x) * f x‖ ≤
      F * N + B * T := by
  have ha := ratio_rpow_nonneg (α := α) h0 h1
  have hlam : 0 ≤ lam := h0.le.trans h1
  have hself : ∀ p ∈ X, p ∈ supThickening X lam := fun p hp =>
    mem_supThickening hp (by rw [sub_self, hLen.supNorm_zero]; exact hlam)
  have hsup1 : supNorm ((tl x : 𝒮.Point) - (tl y : 𝒮.Point)) ≤ lam :=
    (hLen.supNorm_le_lOneNorm _).trans h1
  have hsup2 : supNorm ((tl y : 𝒮.Point) - (tl x : 𝒮.Point)) ≤ lam :=
    (hLen.supNorm_le_lOneNorm _).trans (by rw [← neg_sub, hLen.lOneNorm_neg]; exact h1)
  by_cases hx : φ (tl x) = 0
  · by_cases hy : φ (tl y) = 0
    · rw [hx, hy]
      simp only [zero_mul, sub_self, norm_zero, mul_zero]
      exact add_nonneg (mul_nonneg F0 N0) (mul_nonneg B0 T0)
    · have hyX := hsupp _ hy
      have hxn := mem_supThickening hyX hsup1
      have hyn := hself _ hyX
      have hN' : (lam / siteLOneDist (tl x) (tl y)) ^ α * ‖φ (tl x) - φ (tl y)‖ ≤ N := by
        rw [norm_sub_rev]
        exact hN
      have hT' : (lam / siteLOneDist (tl x) (tl y)) ^ α * ‖f x - f y‖ ≤ T := by
        rw [norm_sub_rev]
        exact hT hxn hyn
      have h := mul_sub_mul_bound ha (hF _ hxn) (hB _) hN' hT'
      rwa [norm_sub_rev] at h
  · have hxX := hsupp _ hx
    have hyn := mem_supThickening hxX hsup2
    have hxn := hself _ hxX
    exact mul_sub_mul_bound ha (hF _ hyn) (hB _) hN (hT hxn hyn)
theorem holderSite_mul_le (hLen : LengthAxioms 4 𝒮.side) (α lam : ℝ)
    (f φ : 𝒮.FineSite → ℝ) (X : Set 𝒮.Point)
    (hsupp : ∀ x, φ x ≠ 0 → (x : 𝒮.Point) ∈ X) :
    holderSite α lam (φ * f) ≤
      supNormOn (supThickening X lam) f * holderSite α lam φ +
        supSite φ * holderSiteOn α lam (supThickening X lam) f := by
  refine Real.sSup_le ?_ (add_nonneg (mul_nonneg (supNormOn_nonneg _ _) (holderSite_nonneg _ _ _))
    (mul_nonneg (supSite_nonneg _) (holderSiteOn_nonneg _ _ _ _)))
  rintro r ⟨x, x', h0, h1, rfl⟩
  exact weighted_mul_sub_le hLen (fun z => z) φ f X h0 h1 hsupp (fun z hz => abs_le_supNormOn f hz)
    (supNormOn_nonneg _ _) (fun z => by rw [← Real.norm_eq_abs]; exact norm_le_supSite φ z)
    (supSite_nonneg _) (le_holderSite α lam φ h0 h1) (holderSite_nonneg _ _ _)
    (fun hx hy => le_holderSiteOn α lam f hx hy h0 h1) (holderSiteOn_nonneg _ _ _ _)
theorem holderBond_smul_le (hLen : LengthAxioms 4 𝒮.side) (α lam : ℝ)
    (f : 𝒮.FineBond → ℝ) (φ : 𝒮.FineSite → ℝ) (X : Set 𝒮.Point)
    (hsupp : ∀ x, φ x ≠ 0 → (x : 𝒮.Point) ∈ X) {F T : ℝ} (F0 : 0 ≤ F) (T0 : 0 ≤ T)
    (hF : supBondOn (supThickening X lam) f ≤ F)
    (hT : holderBondOn α lam (supThickening X lam) f ≤ T) :
    holderBond α lam (smulSiteBond φ f) ≤ F * holderSite α lam φ + supSite φ * T := by
  refine Real.sSup_le ?_ (add_nonneg (mul_nonneg F0 (holderSite_nonneg _ _ _))
    (mul_nonneg (supSite_nonneg _) T0))
  rintro r ⟨b, b', hd, h0, h1, rfl⟩
  exact weighted_mul_sub_le hLen (fun z : 𝒮.FineBond => z.source) φ f X h0 h1 hsupp
    (fun z hz => (abs_le_supBondOn f hz).trans hF) F0
    (fun z => by rw [← Real.norm_eq_abs]; exact norm_le_supSite φ z)
    (supSite_nonneg _) (le_holderSite α lam φ h0 h1) (holderSite_nonneg _ _ _)
    (fun hx hy => (le_holderBondOn α lam f hx hy hd h0 h1).trans hT) T0
theorem holderSiteOn_le_forwardDiff (hLen : LengthAxioms 4 𝒮.side) {α lam : ℝ} (hα : α < 1)
    (hlam : 0 ≤ lam) (f : 𝒮.FineSite → ℝ) {X : Set 𝒮.Point} (hX : IsTorusOrSmallCube lam X) :
    holderSiteOn α lam X f ≤ lam * ⨆ ν, supNormOn X (forwardDiff ν f) := by
  have G0 : 0 ≤ ⨆ ν, supNormOn X (forwardDiff ν f) :=
    Real.iSup_nonneg fun ν => supNormOn_nonneg _ _
  have hG : ∀ y : 𝒮.FineSite, (y : 𝒮.Point) ∈ X → ∀ ν,
      |forwardDiff ν f y| ≤ ⨆ ν, supNormOn X (forwardDiff ν f) :=
    fun y hy ν => (abs_le_supNormOn _ hy).trans
      (le_ciSup (f := fun ν => supNormOn X (forwardDiff ν f)) (Set.finite_range _).bddAbove ν)
  refine Real.sSup_le ?_ (mul_nonneg hlam G0)
  rintro r ⟨x, x', hx, hx', h0, h1, rfl⟩
  have hb := abs_sub_le_siteLOneDist_mul hLen hX hG hx hx' h1
  calc (lam / siteLOneDist x x') ^ α * ‖f x' - f x‖
      ≤ (lam / siteLOneDist x x') ^ α *
          (siteLOneDist x x' * ⨆ ν, supNormOn X (forwardDiff ν f)) :=
        mul_le_mul_of_nonneg_left (by rw [Real.norm_eq_abs]; exact hb) (ratio_rpow_nonneg h0 h1)
    _ = ((lam / siteLOneDist x x') ^ α * siteLOneDist x x') *
          ⨆ ν, supNormOn X (forwardDiff ν f) := by ring
    _ ≤ lam * ⨆ ν, supNormOn X (forwardDiff ν f) :=
        mul_le_mul_of_nonneg_right (ratio_rpow_mul_le hα h0 h1) G0
theorem holderBondOn_le_of_fwdDiff (hLen : LengthAxioms 4 𝒮.side) {α lam G : ℝ} (hα : α < 1)
    (hlam : 0 ≤ lam) (f : 𝒮.FineBond → ℝ) {X : Set 𝒮.Point} (hX : IsTorusOrSmallCube lam X)
    (G0 : 0 ≤ G)
    (hG : ∀ ρ (b : 𝒮.FineBond), (b.source : 𝒮.Point) ∈ X →
      |NestedRegions.fwdDiff ρ f b| ≤ G) :
    holderBondOn α lam X f ≤ lam * G := by
  refine Real.sSup_le ?_ (mul_nonneg hlam G0)
  rintro r ⟨⟨x, δ⟩, ⟨x', δ'⟩, hx, hx', hdir, h0, h1, rfl⟩
  obtain rfl : δ = δ' := hdir
  have hb := abs_sub_le_siteLOneDist_mul hLen hX (g := bondSlice f δ) (G := G)
    (fun y hy ν => hG ν ⟨y, δ⟩ hy) hx hx' h1
  calc (lam / siteLOneDist x x') ^ α * ‖f ⟨x', δ⟩ - f ⟨x, δ⟩‖
      ≤ (lam / siteLOneDist x x') ^ α * (siteLOneDist x x' * G) :=
        mul_le_mul_of_nonneg_left (by rw [Real.norm_eq_abs]; exact hb) (ratio_rpow_nonneg h0 h1)
    _ = ((lam / siteLOneDist x x') ^ α * siteLOneDist x x') * G := by ring
    _ ≤ lam * G := mul_le_mul_of_nonneg_right (ratio_rpow_mul_le hα h0 h1) G0
theorem ratio_rpow_mono {α lam lam' d : ℝ} (hα : 0 ≤ α) (hll : lam' ≤ lam) (h0 : 0 < d)
    (h1 : d ≤ lam') : (lam' / d) ^ α ≤ (lam / d) ^ α :=
  Real.rpow_le_rpow (div_nonneg (h0.le.trans h1) h0.le)
    (div_le_div_of_nonneg_right hll h0.le) hα
theorem rescale_bound {α lam lam' d n A F : ℝ} (hα : 0 ≤ α) (hl : 0 < lam') (hll : lam' ≤ lam)
    (h0 : 0 < d) (hn : 0 ≤ n) (hA : d ≤ lam' → (lam' / d) ^ α * n ≤ A)
    (hB : n ≤ 2 * F) : (lam / d) ^ α * n ≤ (lam / lam') ^ α * max A (2 * F) := by
  have hlam : 0 < lam := hl.trans_le hll
  have hq : 0 ≤ (lam / lam') ^ α := Real.rpow_nonneg (div_nonneg hlam.le hl.le) _
  by_cases hd : d ≤ lam'
  · have e : (lam / d) ^ α = (lam / lam') ^ α * (lam' / d) ^ α := by
      rw [← Real.mul_rpow (div_nonneg hlam.le hl.le) (div_nonneg hl.le h0.le)]
      congr 1
      field_simp
    rw [e, mul_assoc]
    exact mul_le_mul_of_nonneg_left ((hA hd).trans (le_max_left _ _)) hq
  · have e : (lam / d) ^ α ≤ (lam / lam') ^ α :=
      Real.rpow_le_rpow (div_nonneg hlam.le h0.le)
        (div_le_div_of_nonneg_left hlam.le hl (not_le.mp hd).le) hα
    exact mul_le_mul e (hB.trans (le_max_right _ _)) hn hq
theorem rescale_bound_nonneg {α lam lam' A F : ℝ} (hl : 0 < lam') (hll : lam' ≤ lam)
    (F0 : 0 ≤ F) : 0 ≤ (lam / lam') ^ α * max A (2 * F) :=
  mul_nonneg (Real.rpow_nonneg (div_nonneg (hl.le.trans hll) hl.le) _)
    (le_max_of_le_right (by positivity))
theorem holderSite_mono {α lam lam' : ℝ} (hα : 0 ≤ α) (hll : lam' ≤ lam)
    (f : 𝒮.FineSite → ℝ) : holderSite α lam' f ≤ holderSite α lam f := by
  refine Real.sSup_le ?_ (holderSite_nonneg _ _ _)
  rintro r ⟨x, x', h0, h1, rfl⟩
  exact (mul_le_mul_of_nonneg_right (ratio_rpow_mono hα hll h0 h1) (norm_nonneg _)).trans
    (le_holderSite α lam f h0 (h1.trans hll))
theorem holderBond_mono {α lam lam' : ℝ} (hα : 0 ≤ α) (hll : lam' ≤ lam)
    (f : 𝒮.FineBond → ℝ) : holderBond α lam' f ≤ holderBond α lam f := by
  refine Real.sSup_le ?_ (holderBond_nonneg _ _ _)
  rintro r ⟨b, b', hd, h0, h1, rfl⟩
  exact (mul_le_mul_of_nonneg_right (ratio_rpow_mono hα hll h0 h1) (norm_nonneg _)).trans
    (le_holderBond α lam f hd h0 (h1.trans hll))
theorem holderSite_le_rescale {α lam lam' : ℝ} (hα : 0 ≤ α) (hl : 0 < lam') (hll : lam' ≤ lam)
    (f : 𝒮.FineSite → ℝ) : holderSite α lam f ≤
      (lam / lam') ^ α * max (holderSite α lam' f) (2 * supSite f) := by
  refine Real.sSup_le ?_ (rescale_bound_nonneg hl hll (supSite_nonneg f))
  rintro r ⟨x, x', h0, h1, rfl⟩
  refine rescale_bound hα hl hll h0 (norm_nonneg _) (fun hd => le_holderSite α lam' f h0 hd) ?_
  exact (norm_sub_le _ _).trans (by
    rw [two_mul]
    exact add_le_add (norm_le_supSite f x') (norm_le_supSite f x))
theorem holderBond_le_rescale {α lam lam' A F : ℝ} (hα : 0 ≤ α) (hl : 0 < lam') (hll : lam' ≤ lam)
    (f : 𝒮.FineBond → ℝ) (hA : holderBond α lam' f ≤ A) (hF : supBond f ≤ F) :
    holderBond α lam f ≤ (lam / lam') ^ α * max A (2 * F) := by
  refine Real.sSup_le ?_ (rescale_bound_nonneg hl hll ((supBond_nonneg f).trans hF))
  rintro r ⟨b, b', hd, h0, h1, rfl⟩
  refine rescale_bound hα hl hll h0 (norm_nonneg _)
    (fun hd' => (le_holderBond α lam' f hd h0 hd').trans hA) ?_
  exact (norm_sub_le _ _).trans (by
    rw [two_mul]
    exact add_le_add ((norm_le_supBond f b').trans hF) ((norm_le_supBond f b).trans hF))
theorem siteHolderBounds_holds (hLen : LengthAxioms 4 𝒮.side) {α lam lam' : ℝ} (h0 : 0 ≤ α)
    (h1 : α < 1) (hl : 0 < lam') (hll : lam' ≤ lam) (f : 𝒮.FineSite → ℝ) :
    SiteHolderBounds α lam lam' f where
  mul_le φ X hsupp := holderSite_mul_le hLen α lam f φ X hsupp
  le_fwdDiff _ hX := holderSiteOn_le_forwardDiff hLen h1 (hl.le.trans hll) f hX
  mono_scale := holderSite_mono h0 hll f
  le_rescale := holderSite_le_rescale h0 hl hll f
theorem bondHolderBounds_holds (hLen : LengthAxioms 4 𝒮.side) {α lam lam' : ℝ} (h0 : 0 ≤ α)
    (h1 : α < 1) (hl : 0 < lam') (hll : lam' ≤ lam) (f : 𝒮.FineBond → ℝ) :
    BondHolderBounds α lam lam' f where
  mul_le φ X hsupp := holderBond_smul_le hLen α lam f φ X hsupp (supBondOn_nonneg _ _)
    (holderBondOn_nonneg _ _ _ _) le_rfl le_rfl
  le_fwdDiff X hX := holderBondOn_le_of_fwdDiff hLen h1 (hl.le.trans hll) f hX
    (Real.iSup_nonneg fun _ => supBondOn_nonneg _ _)
    (fun ρ _ hb => (abs_le_supBondOn _ hb).trans
      (le_ciSup (f := fun ν => supBondOn X (NestedRegions.fwdDiff ν f))
        (Set.finite_range _).bddAbove ρ))
  mono_scale := holderBond_mono h0 hll f
  le_rescale := holderBond_le_rescale h0 hl hll f le_rfl le_rfl
theorem tensorHolderBounds_holds (hLen : LengthAxioms 4 𝒮.side) {α lam lam' : ℝ} (h0 : 0 ≤ α)
    (h1 : α < 1) (hl : 0 < lam') (hll : lam' ≤ lam) {r : ℕ} (J : 𝒮.Tensor r) :
    TensorHolderBounds α lam lam' J where
  mul_le φ X hsupp := ciSup_le fun ν => holderBond_smul_le hLen α lam (J ν) φ X hsupp
    (Real.iSup_nonneg fun _ => supBondOn_nonneg _ _)
    (Real.iSup_nonneg fun _ => holderBondOn_nonneg _ _ _ _)
    (le_ciSup (f := fun ν => supBondOn (supThickening X lam) (J ν))
      (Set.finite_range _).bddAbove ν)
    (le_ciSup (f := fun ν => holderBondOn α lam (supThickening X lam) (J ν))
      (Set.finite_range _).bddAbove ν)
  le_fwdDiff X hX := ciSup_le fun ν =>
    holderBondOn_le_of_fwdDiff hLen h1 (hl.le.trans hll) (J ν) hX
      (Real.iSup_nonneg fun _ => Real.iSup_nonneg fun _ => supBondOn_nonneg _ _)
      (fun ρ _ hb => (abs_le_supBondOn _ hb).trans
        ((le_ciSup (f := fun ν => supBondOn X (NestedRegions.fwdDiff ρ (J ν)))
          (Set.finite_range _).bddAbove ν).trans
          (le_ciSup (f := fun ρ => supTensorOn X fun ν => NestedRegions.fwdDiff ρ (J ν))
            (Set.finite_range _).bddAbove ρ)))
  mono_scale := ciSup_mono (Set.finite_range _).bddAbove fun ν =>
    holderBond_mono h0 hll (J ν)
  le_rescale := ciSup_le fun ν => holderBond_le_rescale h0 hl hll (J ν)
    (le_ciSup (f := fun ν => holderBond α lam' (J ν)) (Set.finite_range _).bddAbove ν)
    (le_ciSup (f := fun ν => supBond (J ν)) (Set.finite_range _).bddAbove ν)
end Seminorms
theorem statement_holds (hL : TorusLengthsStatement) (hC : CellStructure.CellStructureClaim)
    (hD : CubeDivergence.Claim) : Statement := by
  refine ⟨fun 𝒮 φ f => ?_, fun 𝒮 φ f => ?_, fun 𝒮 α lam lam' h0 h1 hl hll => ?_,
    fun K m M R₁ 𝒮 h hM Q hQ J => hD K m M R₁ 𝒮 h hM Q hQ J⟩
  · have := finite_fineSite hL 𝒮
    exact siteProductRules_holds hC φ f
  · have := finite_fineSite hL 𝒮
    have : Finite 𝒮.FineBond := finite_fineBond
    exact bondProductRules_holds hC φ f
  · have := finite_fineSite hL 𝒮
    have : Finite 𝒮.FineBond := finite_fineBond
    have hLen := (hL 4 𝒮.side 𝒮.side_pos).1
    exact ⟨fun f => siteHolderBounds_holds hLen h0 h1 hl hll f,
      fun f => bondHolderBounds_holds hLen h0 h1 hl hll f,
      fun r J => tensorHolderBounds_holds hLen h0 h1 hl hll J⟩
end YangMills.Construction.LeibnizHolder
