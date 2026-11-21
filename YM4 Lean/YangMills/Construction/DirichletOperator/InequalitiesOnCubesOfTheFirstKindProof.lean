import YangMills.Construction.DirichletOperator.CornerBoundsOnTheToriOfTheCubesProof
import YangMills.Construction.Lattice.ClosedFormsWithVanishingAveragesAreDifferencesProof
import YangMills.Construction.DirichletOperator.BondsCarriedToTheTorusOfACubeProof
import YangMills.Construction.DirichletOperator.InequalitiesOfALocalGreenOperator
import YangMills.Construction.DirichletOperator.LeibnizRulesAndHolderSeminorms
import YangMills.Construction.RegionSequence.BaseOperatorPositivityProof
import YangMills.Construction.RegionSequence.CellsAndAdjoints
import Mathlib
set_option autoImplicit false
open Set
open YangMills.Construction.Dirichlet YangMills.Construction.Torus
open YangMills.Construction.RegionSequence YangMills.Construction.RegionSequence.NestedRegions
open YangMills.Construction.PartitionCubes
open YangMills.Construction.GreenRegularity
open YangMills.Construction.CubeTorus (torusSetting levelSpacing TensorAnchorSupported tensorModulusAt)
noncomputable section
namespace YangMills.Construction.FirstTypeGreenRegularity
section Lengths
variable {S : ℝ}
theorem addCircle_norm_le_abs (x : ℝ) : ‖(x : AddCircle S)‖ ≤ |x| := by apply _root_.YangMills.Construction.TorusMetric.addCircle_norm_coe_le_abs <;> assumption
theorem exists_lift_abs_eq_norm (x : AddCircle S) : ∃ r : ℝ, (r : AddCircle S) = x ∧ |r| = ‖x‖ := by apply _root_.YangMills.Construction.TorusMetric.exists_coe_eq_abs_eq_norm <;> assumption
theorem supNorm_eq_norm (p : PeriodicTorus 4 S) : supNorm p = ‖p‖ := by apply _root_.YangMills.Construction.PartitionCubes.CubeTorusAveraging.supNorm_eq_norm <;> assumption
theorem lOneNorm_eq_sum (p : PeriodicTorus 4 S) : lOneNorm p = ∑ μ, ‖p μ‖ := by apply _root_.YangMills.Construction.PartitionCubes.TorusTransfer.lOneNorm_eq_sum_norm <;> assumption
theorem lOneNorm_sub_comm (p q : PeriodicTorus 4 S) : lOneNorm (p - q) = lOneNorm (q - p) := by apply _root_.YangMills.Construction.PartitionCubes.TorusTransfer.lOneNorm_sub_comm <;> assumption
theorem lOneNorm_sub_le (p q r : PeriodicTorus 4 S) :
    lOneNorm (p - r) ≤ lOneNorm (p - q) + lOneNorm (q - r) := by
  simp only [lOneNorm_eq_sum, ← Finset.sum_add_distrib, Pi.sub_apply]
  exact Finset.sum_le_sum fun μ _ => norm_sub_le_norm_sub_add_norm_sub _ _ _
theorem supNorm_sub_le (p q r : PeriodicTorus 4 S) :
    supNorm (p - r) ≤ supNorm (p - q) + supNorm (q - r) := by
  simp only [supNorm_eq_norm]
  exact norm_sub_le_norm_sub_add_norm_sub _ _ _
end Lengths
def tent (t : ℝ) : ℝ := max 0 (1 - t)
theorem tent_nonneg (t : ℝ) : 0 ≤ tent t := le_max_left _ _
theorem tent_le_one {t : ℝ} (ht : 0 ≤ t) : tent t ≤ 1 :=
  max_le zero_le_one (by linarith)
theorem abs_tent_sub_le (a b : ℝ) : |tent a - tent b| ≤ |a - b| := by
  have h := abs_max_sub_max_le_abs (1 - a) (1 - b) (0 : ℝ)
  have h2 : |(1 - a) - (1 - b)| = |a - b| := by
    rw [show (1 - a) - (1 - b) = -(a - b) by ring, abs_neg]
  rw [h2] at h
  simpa only [tent, max_comm (0 : ℝ)] using h
theorem abs_prod_sub_prod_le {ι : Type} (s : Finset ι) (a b : ι → ℝ)
    (ha : ∀ i ∈ s, 0 ≤ a i ∧ a i ≤ 1) (hb : ∀ i ∈ s, 0 ≤ b i ∧ b i ≤ 1) :
    |∏ i ∈ s, a i - ∏ i ∈ s, b i| ≤ ∑ i ∈ s, |a i - b i| := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.prod_insert hi, Finset.sum_insert hi]
    have ha' : ∀ j ∈ s, 0 ≤ a j ∧ a j ≤ 1 := fun j hj => ha j (Finset.mem_insert_of_mem hj)
    have hb' : ∀ j ∈ s, 0 ≤ b j ∧ b j ≤ 1 := fun j hj => hb j (Finset.mem_insert_of_mem hj)
    have hB0 : 0 ≤ ∏ j ∈ s, b j := Finset.prod_nonneg fun j hj => (hb' j hj).1
    have hB1 : ∏ j ∈ s, b j ≤ 1 := Finset.prod_le_one (fun j hj => (hb' j hj).1) fun j hj => (hb' j hj).2
    have hai := ha i (Finset.mem_insert_self _ _)
    have h := ih ha' hb'
    have e : a i * ∏ j ∈ s, a j - b i * ∏ j ∈ s, b j =
        a i * (∏ j ∈ s, a j - ∏ j ∈ s, b j) + (a i - b i) * ∏ j ∈ s, b j := by ring
    rw [e]
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_mul, abs_of_nonneg hai.1, abs_of_nonneg hB0]
    have h1 : a i * |∏ j ∈ s, a j - ∏ j ∈ s, b j| ≤ |∏ j ∈ s, a j - ∏ j ∈ s, b j| :=
      mul_le_of_le_one_left (abs_nonneg _) hai.2
    have h2 : |a i - b i| * ∏ j ∈ s, b j ≤ |a i - b i| :=
      mul_le_of_le_one_right (abs_nonneg _) hB1
    linarith
section TentProducts
variable {S : ℝ}
def tentProduct (σ : ℝ) (c x : PeriodicTorus 4 S) : ℝ := ∏ μ, tent (‖x μ - c μ‖ / σ)
theorem tentProduct_nonneg {σ : ℝ} (c x : PeriodicTorus 4 S) : 0 ≤ tentProduct σ c x :=
  Finset.prod_nonneg fun _ _ => tent_nonneg _
theorem tentProduct_le_one {σ : ℝ} (hσ : 0 < σ) (c x : PeriodicTorus 4 S) : tentProduct σ c x ≤ 1 :=
  Finset.prod_le_one (fun _ _ => tent_nonneg _) fun _ _ =>
    tent_le_one (div_nonneg (norm_nonneg _) hσ.le)
theorem abs_tentProduct_sub_le {σ : ℝ} (hσ : 0 < σ) (c x y : PeriodicTorus 4 S) :
    |tentProduct σ c x - tentProduct σ c y| ≤ σ⁻¹ * lOneNorm (x - y) := by
  refine (abs_prod_sub_prod_le _ _ _
    (fun μ _ => ⟨tent_nonneg _, tent_le_one (div_nonneg (norm_nonneg _) hσ.le)⟩)
    (fun μ _ => ⟨tent_nonneg _, tent_le_one (div_nonneg (norm_nonneg _) hσ.le)⟩)).trans ?_
  rw [lOneNorm_eq_sum, Finset.mul_sum]
  refine Finset.sum_le_sum fun μ _ => (abs_tent_sub_le _ _).trans ?_
  rw [← sub_div, abs_div, abs_of_pos hσ, div_eq_inv_mul]
  refine mul_le_mul_of_nonneg_left ?_ (inv_nonneg.2 hσ.le)
  refine (abs_norm_sub_norm_le _ _).trans ?_
  simp
theorem supNorm_lt_of_tentProduct_ne_zero {σ : ℝ} (hσ : 0 < σ) {c x : PeriodicTorus 4 S}
    (h : tentProduct σ c x ≠ 0) : supNorm (x - c) < σ := by
  rw [supNorm_eq_norm, pi_norm_lt_iff hσ]
  intro μ
  have h1 : tent (‖x μ - c μ‖ / σ) ≠ 0 := Finset.prod_ne_zero_iff.1 h μ (Finset.mem_univ _)
  by_contra h2
  apply h1
  have h3 : 1 ≤ ‖x μ - c μ‖ / σ := by
    rw [le_div_iff₀ hσ, one_mul]
    exact not_lt.1 h2
  rw [tent, max_eq_left (by linarith)]
def window (R : ℤ) : Finset (Fin 4 → ℤ) := Fintype.piFinset fun _ => Finset.Icc (-R) R
end TentProducts
section Seminorms
variable {𝒯 : NestedRegions} [Finite 𝒯.FineSite] [Finite 𝒯.FineBond]
theorem abs_le_supSite (f : 𝒯.FineSite → ℝ) (x : 𝒯.FineSite) : |f x| ≤ supSite f :=
  le_ciSup (f := fun x => ‖f x‖) (Set.finite_range _).bddAbove x
omit [Finite 𝒯.FineSite] [Finite 𝒯.FineBond] in
theorem supSite_nonneg (f : 𝒯.FineSite → ℝ) : 0 ≤ supSite f :=
  Real.iSup_nonneg fun _ => norm_nonneg _
omit [Finite 𝒯.FineSite] [Finite 𝒯.FineBond] in
theorem supSite_le {f : 𝒯.FineSite → ℝ} {C : ℝ} (hC : 0 ≤ C) (h : ∀ x, |f x| ≤ C) :
    supSite f ≤ C :=
  Real.iSup_le h hC
theorem abs_le_supBond (f : 𝒯.FineBond → ℝ) (b : 𝒯.FineBond) : |f b| ≤ supBond f :=
  le_ciSup (f := fun b => ‖f b‖) (Set.finite_range _).bddAbove b
omit [Finite 𝒯.FineSite] [Finite 𝒯.FineBond] in
theorem supBond_nonneg (f : 𝒯.FineBond → ℝ) : 0 ≤ supBond f := by apply _root_.YangMills.Construction.CornerGreen.supBond_nonneg' <;> assumption
omit [Finite 𝒯.FineSite] [Finite 𝒯.FineBond] in
theorem supBond_le {f : 𝒯.FineBond → ℝ} {C : ℝ} (hC : 0 ≤ C) (h : ∀ b, |f b| ≤ C) :
    supBond f ≤ C :=
  Real.iSup_le h hC
omit [Finite 𝒯.FineSite] [Finite 𝒯.FineBond] in
theorem supBond_le_supTensor {r : ℕ} (J : 𝒯.Tensor r) (ν : Fin r → Fin 4) :
    supBond (J ν) ≤ supTensor J :=
  le_ciSup (f := fun ν => supBond (J ν)) (Set.finite_range _).bddAbove ν
omit [Finite 𝒯.FineSite] [Finite 𝒯.FineBond] in
theorem supTensor_nonneg {r : ℕ} (J : 𝒯.Tensor r) : 0 ≤ supTensor J :=
  Real.iSup_nonneg fun _ => supBond_nonneg _
omit [Finite 𝒯.FineSite] [Finite 𝒯.FineBond] in
theorem supTensor_le {r : ℕ} {J : 𝒯.Tensor r} {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ ν b, |J ν b| ≤ C) : supTensor J ≤ C :=
  Real.iSup_le (fun ν => supBond_le hC (h ν)) hC
theorem abs_le_supTensor {r : ℕ} (J : 𝒯.Tensor r) (ν : Fin r → Fin 4) (b : 𝒯.FineBond) :
    |J ν b| ≤ supTensor J :=
  (abs_le_supBond _ b).trans (supBond_le_supTensor J ν)
omit [Finite 𝒯.FineSite] [Finite 𝒯.FineBond] in
theorem abs_le_tensorModulusAt {r : ℕ} (J : 𝒯.Tensor r) (ν : Fin r → Fin 4) (b : 𝒯.FineBond) :
    |J ν b| ≤ tensorModulusAt J b :=
  le_ciSup (f := fun ν => |J ν b|) (Set.finite_range _).bddAbove ν
omit [Finite 𝒯.FineSite] [Finite 𝒯.FineBond] in
theorem tensorModulusAt_nonneg {r : ℕ} (J : 𝒯.Tensor r) (b : 𝒯.FineBond) :
    0 ≤ tensorModulusAt J b :=
  Real.iSup_nonneg fun _ => abs_nonneg _
omit [Finite 𝒯.FineSite] [Finite 𝒯.FineBond] in
theorem tensorModulusAt_le {r : ℕ} {J : 𝒯.Tensor r} {b : 𝒯.FineBond} {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ ν, |J ν b| ≤ C) : tensorModulusAt J b ≤ C :=
  Real.iSup_le h hC
theorem le_holderSite {α lam : ℝ} (f : 𝒯.FineSite → ℝ) {x x' : 𝒯.FineSite}
    (h₀ : 0 < siteLOneDist x x') (h₁ : siteLOneDist x x' ≤ lam) :
    (lam / siteLOneDist x x') ^ α * |f x' - f x| ≤ holderSite α lam f := by
  refine le_csSup ?_ ⟨x, x', h₀, h₁, rfl⟩
  refine ((Set.finite_range fun p : 𝒯.FineSite × 𝒯.FineSite =>
    (lam / siteLOneDist p.1 p.2) ^ α * ‖f p.2 - f p.1‖).subset ?_).bddAbove
  rintro _ ⟨a, b, -, -, rfl⟩
  exact ⟨(a, b), rfl⟩
omit [Finite 𝒯.FineSite] [Finite 𝒯.FineBond] in
theorem holderSite_le {α lam C : ℝ} {f : 𝒯.FineSite → ℝ} (hC : 0 ≤ C)
    (h : ∀ x x' : 𝒯.FineSite, 0 < siteLOneDist x x' → siteLOneDist x x' ≤ lam →
      (lam / siteLOneDist x x') ^ α * |f x' - f x| ≤ C) : holderSite α lam f ≤ C := by
  refine Real.sSup_le ?_ hC
  rintro _ ⟨x, x', h₀, h₁, rfl⟩
  exact h x x' h₀ h₁
omit [Finite 𝒯.FineSite] [Finite 𝒯.FineBond] in
theorem holderSite_nonneg (α lam : ℝ) (f : 𝒯.FineSite → ℝ) : 0 ≤ holderSite α lam f := by
  refine Real.sSup_nonneg ?_
  rintro _ ⟨x, x', h₀, h₁, rfl⟩
  have : 0 ≤ lam / siteLOneDist x x' := div_nonneg (h₀.le.trans h₁) h₀.le
  exact mul_nonneg (Real.rpow_nonneg this _) (norm_nonneg _)
theorem le_holderBond {α lam : ℝ} (f : 𝒯.FineBond → ℝ) {b b' : 𝒯.FineBond}
    (hd : b.dir = b'.dir)
    (h₀ : 0 < siteLOneDist b.source b'.source) (h₁ : siteLOneDist b.source b'.source ≤ lam) :
    (lam / siteLOneDist b.source b'.source) ^ α * |f b' - f b| ≤ holderBond α lam f := by
  refine le_csSup ?_ ⟨b, b', hd, h₀, h₁, rfl⟩
  refine ((Set.finite_range fun p : 𝒯.FineBond × 𝒯.FineBond =>
    (lam / siteLOneDist p.1.source p.2.source) ^ α * ‖f p.2 - f p.1‖).subset ?_).bddAbove
  rintro _ ⟨a, c, -, -, -, rfl⟩
  exact ⟨(a, c), rfl⟩
omit [Finite 𝒯.FineSite] [Finite 𝒯.FineBond] in
theorem holderBond_le {α lam C : ℝ} {f : 𝒯.FineBond → ℝ} (hC : 0 ≤ C)
    (h : ∀ b b' : 𝒯.FineBond, b.dir = b'.dir → 0 < siteLOneDist b.source b'.source →
      siteLOneDist b.source b'.source ≤ lam →
      (lam / siteLOneDist b.source b'.source) ^ α * |f b' - f b| ≤ C) :
    holderBond α lam f ≤ C := by
  refine Real.sSup_le ?_ hC
  rintro _ ⟨b, b', hd, h₀, h₁, rfl⟩
  exact h b b' hd h₀ h₁
omit [Finite 𝒯.FineSite] [Finite 𝒯.FineBond] in
theorem holderBond_nonneg (α lam : ℝ) (f : 𝒯.FineBond → ℝ) : 0 ≤ holderBond α lam f := by
  refine Real.sSup_nonneg ?_
  rintro _ ⟨b, b', -, h₀, h₁, rfl⟩
  have : 0 ≤ lam / siteLOneDist b.source b'.source := div_nonneg (h₀.le.trans h₁) h₀.le
  exact mul_nonneg (Real.rpow_nonneg this _) (norm_nonneg _)
omit [Finite 𝒯.FineSite] [Finite 𝒯.FineBond] in
theorem holderBond_le_holderTensor {r : ℕ} (α lam : ℝ) (J : 𝒯.Tensor r) (ν : Fin r → Fin 4) :
    holderBond α lam (J ν) ≤ holderTensor α lam J :=
  le_ciSup (f := fun ν => holderBond α lam (J ν)) (Set.finite_range _).bddAbove ν
omit [Finite 𝒯.FineSite] [Finite 𝒯.FineBond] in
theorem holderTensor_nonneg {r : ℕ} (α lam : ℝ) (J : 𝒯.Tensor r) :
    0 ≤ holderTensor α lam J :=
  Real.iSup_nonneg fun _ => holderBond_nonneg _ _ _
theorem holderBond_add (α lam : ℝ) (f g : 𝒯.FineBond → ℝ) :
    holderBond α lam (f + g) ≤ holderBond α lam f + holderBond α lam g := by
  refine holderBond_le (add_nonneg (holderBond_nonneg _ _ _) (holderBond_nonneg _ _ _)) ?_
  intro b b' hd h₀ h₁
  have hr : 0 ≤ (lam / siteLOneDist b.source b'.source) ^ α :=
    Real.rpow_nonneg (div_nonneg (h₀.le.trans h₁) h₀.le) _
  have e : (f + g) b' - (f + g) b = (f b' - f b) + (g b' - g b) := by
    simp only [Pi.add_apply]; ring
  rw [e]
  calc _ ≤ (lam / siteLOneDist b.source b'.source) ^ α * (|f b' - f b| + |g b' - g b|) :=
        mul_le_mul_of_nonneg_left (abs_add_le _ _) hr
    _ = _ := mul_add _ _ _
    _ ≤ _ := add_le_add (le_holderBond f hd h₀ h₁) (le_holderBond g hd h₀ h₁)
omit [Finite 𝒯.FineSite] [Finite 𝒯.FineBond] in
theorem holderBond_zero (α lam : ℝ) : holderBond α lam (0 : 𝒯.FineBond → ℝ) ≤ 0 :=
  holderBond_le le_rfl fun b b' _ _ _ => by simp
theorem holderTensor_add {r : ℕ} (α lam : ℝ) (J J' : 𝒯.Tensor r) :
    holderTensor α lam (J + J') ≤ holderTensor α lam J + holderTensor α lam J' :=
  Real.iSup_le (fun ν => (holderBond_add α lam (J ν) (J' ν)).trans
    (add_le_add (holderBond_le_holderTensor α lam J ν) (holderBond_le_holderTensor α lam J' ν)))
    (add_nonneg (holderTensor_nonneg _ _ _) (holderTensor_nonneg _ _ _))
omit [Finite 𝒯.FineSite] [Finite 𝒯.FineBond] in
theorem holderTensor_zero {r : ℕ} (α lam : ℝ) :
    holderTensor α lam (0 : 𝒯.Tensor r) ≤ 0 :=
  Real.iSup_le (fun _ => holderBond_zero α lam) le_rfl
theorem holderSite_mul (a lam : ℝ) (φ f : 𝒯.FineSite → ℝ) :
    holderSite a lam (φ * f) ≤ supSite f * holderSite a lam φ + supSite φ * holderSite a lam f := by
  refine holderSite_le (add_nonneg (mul_nonneg (supSite_nonneg _) (holderSite_nonneg _ _ _))
    (mul_nonneg (supSite_nonneg _) (holderSite_nonneg _ _ _))) ?_
  intro x x' h₀ h₁
  have hr : 0 ≤ (lam / siteLOneDist x x') ^ a :=
    Real.rpow_nonneg (div_nonneg (h₀.le.trans h₁) h₀.le) _
  have e : (φ * f) x' - (φ * f) x = (φ x' - φ x) * f x' + φ x * (f x' - f x) := by
    simp only [Pi.mul_apply]; ring
  rw [e]
  have h1 := le_holderSite (α := a) φ h₀ h₁
  have h2 := le_holderSite (α := a) f h₀ h₁
  have h3 := abs_le_supSite f x'
  have h4 := abs_le_supSite φ x
  calc _ ≤ (lam / siteLOneDist x x') ^ a * (|φ x' - φ x| * |f x'| + |φ x| * |f x' - f x|) := by
        refine mul_le_mul_of_nonneg_left ?_ hr
        refine (abs_add_le _ _).trans ?_
        rw [abs_mul, abs_mul]
    _ = ((lam / siteLOneDist x x') ^ a * |φ x' - φ x|) * |f x'| +
        |φ x| * ((lam / siteLOneDist x x') ^ a * |f x' - f x|) := by ring
    _ ≤ holderSite a lam φ * supSite f + supSite φ * holderSite a lam f := by
        refine add_le_add ?_ ?_
        · exact mul_le_mul h1 h3 (abs_nonneg _) (holderSite_nonneg _ _ _)
        · exact mul_le_mul h4 h2 (mul_nonneg hr (abs_nonneg _)) (supSite_nonneg _)
    _ = _ := by ring
theorem holderBond_smul (a lam : ℝ) (φ : 𝒯.FineSite → ℝ) (f : 𝒯.FineBond → ℝ) :
    holderBond a lam (smulSiteBond φ f) ≤
      supBond f * holderSite a lam φ + supSite φ * holderBond a lam f := by
  refine holderBond_le (add_nonneg (mul_nonneg (supBond_nonneg _) (holderSite_nonneg _ _ _))
    (mul_nonneg (supSite_nonneg _) (holderBond_nonneg _ _ _))) ?_
  intro b b' hd h₀ h₁
  have hr : 0 ≤ (lam / siteLOneDist b.source b'.source) ^ a :=
    Real.rpow_nonneg (div_nonneg (h₀.le.trans h₁) h₀.le) _
  have e : smulSiteBond φ f b' - smulSiteBond φ f b =
      (φ b'.source - φ b.source) * f b' + φ b.source * (f b' - f b) := by
    simp only [smulSiteBond, smul_eq_mul]; ring
  rw [e]
  have h1 := le_holderSite (α := a) φ h₀ h₁
  have h2 := le_holderBond (α := a) f hd h₀ h₁
  have h3 := abs_le_supBond f b'
  have h4 := abs_le_supSite φ b.source
  calc _ ≤ (lam / siteLOneDist b.source b'.source) ^ a *
        (|φ b'.source - φ b.source| * |f b'| + |φ b.source| * |f b' - f b|) := by
        refine mul_le_mul_of_nonneg_left ?_ hr
        refine (abs_add_le _ _).trans ?_
        rw [abs_mul, abs_mul]
    _ = ((lam / siteLOneDist b.source b'.source) ^ a * |φ b'.source - φ b.source|) * |f b'| +
        |φ b.source| * ((lam / siteLOneDist b.source b'.source) ^ a * |f b' - f b|) := by ring
    _ ≤ holderSite a lam φ * supBond f + supSite φ * holderBond a lam f := by
        refine add_le_add ?_ ?_
        · exact mul_le_mul h1 h3 (abs_nonneg _) (holderSite_nonneg _ _ _)
        · exact mul_le_mul h4 h2 (mul_nonneg hr (abs_nonneg _)) (supSite_nonneg _)
    _ = _ := by ring
theorem holderTensor_smul {r : ℕ} (a lam : ℝ) (φ : 𝒯.FineSite → ℝ) (J : 𝒯.Tensor r) :
    holderTensor a lam (smulSiteTensor φ J) ≤
      supTensor J * holderSite a lam φ + supSite φ * holderTensor a lam J := by
  refine Real.iSup_le (fun ν => ?_)
    (add_nonneg (mul_nonneg (supTensor_nonneg _) (holderSite_nonneg _ _ _))
      (mul_nonneg (supSite_nonneg _) (holderTensor_nonneg _ _ _)))
  refine (holderBond_smul a lam φ (J ν)).trans (add_le_add ?_ ?_)
  · exact mul_le_mul_of_nonneg_right (supBond_le_supTensor J ν) (holderSite_nonneg _ _ _)
  · exact mul_le_mul_of_nonneg_left (holderBond_le_holderTensor a lam J ν) (supSite_nonneg _)
theorem holderSite_tentProduct_le {a σ : ℝ} (ha₀ : 0 ≤ a) (ha₁ : a ≤ 1) (hσ : 0 < σ)
    (c : 𝒯.Point) :
    holderSite a σ (fun x : 𝒯.FineSite => tentProduct σ c (x : 𝒯.Point)) ≤ 1 := by
  refine holderSite_le zero_le_one ?_
  intro x x' h₀ h₁
  have hq : 1 ≤ σ / siteLOneDist x x' := (one_le_div h₀).2 h₁
  have h2 : (σ / siteLOneDist x x') ^ a ≤ σ / siteLOneDist x x' := by
    simpa using Real.rpow_le_rpow_of_exponent_le hq ha₁
  have h3 : |tentProduct σ c (x' : 𝒯.Point) - tentProduct σ c (x : 𝒯.Point)| ≤
      σ⁻¹ * siteLOneDist x x' := by
    have := abs_tentProduct_sub_le hσ c (x' : 𝒯.Point) (x : 𝒯.Point)
    rwa [lOneNorm_sub_comm] at this
  calc _ ≤ (σ / siteLOneDist x x') * (σ⁻¹ * siteLOneDist x x') :=
        mul_le_mul h2 h3 (abs_nonneg _) (by positivity)
    _ = 1 := by
        have := h₀.ne'
        field_simp
omit [Finite 𝒯.FineSite] [Finite 𝒯.FineBond] in
theorem sqrt_sum_sq_add_le {ι : Type} [Fintype ι] (f g : ι → ℝ) :
    √(∑ i, (f i + g i) ^ 2) ≤ √(∑ i, f i ^ 2) + √(∑ i, g i ^ 2) := by
  have h := norm_add_le (WithLp.toLp 2 f : EuclideanSpace ℝ ι) (WithLp.toLp 2 g)
  simpa [EuclideanSpace.norm_eq] using h
theorem ltwoBond_eq [Fintype 𝒯.FineBond] (f : 𝒯.FineBond → ℝ) :
    ltwoBond f = 𝒯.ξ ^ 2 * √(∑ b, f b ^ 2) := by
  have hξ := 𝒯.ξ_pos
  simp only [ltwoBond, bondL2, bondInner]
  rw [finsum_eq_sum_of_fintype, Real.sqrt_mul (by positivity),
    show 𝒯.ξ ^ 4 = (𝒯.ξ ^ 2) ^ 2 by ring, Real.sqrt_sq (by positivity)]
  simp only [pow_two]
theorem ltwoTensor_eq [Fintype 𝒯.FineBond] {r : ℕ} (J : 𝒯.Tensor r) :
    ltwoTensor J = 𝒯.ξ ^ 2 * √(∑ p : (Fin r → Fin 4) × 𝒯.FineBond, J p.1 p.2 ^ 2) := by
  have hξ := 𝒯.ξ_pos
  simp only [ltwoTensor, tensorL2, tensorInner, bondInner]
  simp only [finsum_eq_sum_of_fintype, ← Finset.mul_sum]
  rw [Real.sqrt_mul (by positivity),
    show 𝒯.ξ ^ 4 = (𝒯.ξ ^ 2) ^ 2 by ring, Real.sqrt_sq (by positivity), Fintype.sum_prod_type]
  simp only [pow_two]
theorem ltwoBond_add (f g : 𝒯.FineBond → ℝ) :
    ltwoBond (f + g) ≤ ltwoBond f + ltwoBond g := by
  haveI := Fintype.ofFinite 𝒯.FineBond
  rw [ltwoBond_eq, ltwoBond_eq, ltwoBond_eq, ← mul_add]
  exact mul_le_mul_of_nonneg_left (sqrt_sum_sq_add_le f g) (by have := 𝒯.ξ_pos; positivity)
theorem ltwoTensor_add {r : ℕ} (J J' : 𝒯.Tensor r) :
    ltwoTensor (J + J') ≤ ltwoTensor J + ltwoTensor J' := by
  haveI := Fintype.ofFinite 𝒯.FineBond
  rw [ltwoTensor_eq, ltwoTensor_eq, ltwoTensor_eq, ← mul_add]
  exact mul_le_mul_of_nonneg_left
    (sqrt_sum_sq_add_le (fun p : (Fin r → Fin 4) × 𝒯.FineBond => J p.1 p.2)
      (fun p : (Fin r → Fin 4) × 𝒯.FineBond => J' p.1 p.2))
    (by have := 𝒯.ξ_pos; positivity)
theorem ltwoBond_zero : ltwoBond (0 : 𝒯.FineBond → ℝ) ≤ 0 := by
  haveI := Fintype.ofFinite 𝒯.FineBond
  rw [ltwoBond_eq]
  simp
theorem ltwoTensor_zero {r : ℕ} : ltwoTensor (0 : 𝒯.Tensor r) ≤ 0 := by
  haveI := Fintype.ofFinite 𝒯.FineBond
  rw [ltwoTensor_eq]
  simp
theorem ltwoBond_nonneg (f : 𝒯.FineBond → ℝ) : 0 ≤ ltwoBond f := Real.sqrt_nonneg _
theorem ltwoTensor_nonneg {r : ℕ} (J : 𝒯.Tensor r) : 0 ≤ ltwoTensor J :=
  Real.sqrt_nonneg _
theorem ltwoBond_smul_le {φ : 𝒯.FineSite → ℝ} (hφ : ∀ x, |φ x| ≤ 1) (f : 𝒯.FineBond → ℝ) :
    ltwoBond (smulSiteBond φ f) ≤ ltwoBond f := by
  haveI := Fintype.ofFinite 𝒯.FineBond
  rw [ltwoBond_eq, ltwoBond_eq]
  refine mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (Finset.sum_le_sum fun b _ => ?_))
    (by have := 𝒯.ξ_pos; positivity)
  simp only [smulSiteBond, smul_eq_mul, mul_pow]
  have : φ b.source ^ 2 ≤ 1 := by
    rw [← sq_abs]
    exact pow_le_one₀ (abs_nonneg _) (hφ _)
  exact mul_le_of_le_one_left (sq_nonneg _) this
theorem ltwoTensor_smul_le {r : ℕ} {φ : 𝒯.FineSite → ℝ} (hφ : ∀ x, |φ x| ≤ 1)
    (J : 𝒯.Tensor r) : ltwoTensor (smulSiteTensor φ J) ≤ ltwoTensor J := by
  haveI := Fintype.ofFinite 𝒯.FineBond
  rw [ltwoTensor_eq, ltwoTensor_eq]
  refine mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (Finset.sum_le_sum fun b _ => ?_))
    (by have := 𝒯.ξ_pos; positivity)
  simp only [smulSiteTensor, smulSiteBond, smul_eq_mul, mul_pow]
  have : φ b.2.source ^ 2 ≤ 1 := by
    rw [← sq_abs]
    exact pow_le_one₀ (abs_nonneg _) (hφ _)
  exact mul_le_of_le_one_left (sq_nonneg _) this
end Seminorms
theorem le_sum_of_subadditive {V ι : Type} [AddCommMonoid V] (N : V → ℝ) (h₀ : N 0 ≤ 0)
    (hadd : ∀ a b, N (a + b) ≤ N a + N b) (s : Finset ι) (f : ι → V) :
    N (∑ i ∈ s, f i) ≤ ∑ i ∈ s, N (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using h₀
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi]
    exact (hadd _ _).trans (add_le_add le_rfl ih)
theorem le_sq_mul_of_subadditive {V ι κ : Type} [AddCommMonoid V] (N : V → ℝ) (h₀ : N 0 ≤ 0)
    (hadd : ∀ a b, N (a + b) ≤ N a + N b) (s : Finset ι) (t : Finset κ) (F : ι → κ → V)
    {A : ℝ} (h : ∀ i ∈ s, ∀ j ∈ t, N (F i j) ≤ A) (hA : 0 ≤ A) {n : ℕ} (hs : s.card = n)
    (ht : t.card = n) : N (∑ i ∈ s, ∑ j ∈ t, F i j) ≤ (n : ℝ) ^ 2 * A := by
  refine (le_sum_of_subadditive N h₀ hadd s _).trans ?_
  have h1 : ∀ i ∈ s, N (∑ j ∈ t, F i j) ≤ (n : ℝ) * A := by
    intro i hi
    refine (le_sum_of_subadditive N h₀ hadd t _).trans ?_
    refine (Finset.sum_le_card_nsmul _ _ A (h i hi)).trans ?_
    rw [ht, nsmul_eq_mul]
  refine (Finset.sum_le_card_nsmul _ _ _ h1).trans ?_
  rw [hs, nsmul_eq_mul]
  exact le_of_eq (by ring)
theorem le_card_mul_of_subadditive {V κ : Type} [AddCommMonoid V] (N : V → ℝ) (h₀ : N 0 ≤ 0)
    (hadd : ∀ a b, N (a + b) ≤ N a + N b) (t : Finset κ) (f : κ → V)
    {A : ℝ} (h : ∀ j ∈ t, N (f j) ≤ A) {n : ℕ} (ht : t.card = n) :
    N (∑ j ∈ t, f j) ≤ (n : ℝ) * A := by
  refine (le_sum_of_subadditive N h₀ hadd t _).trans ?_
  refine (Finset.sum_le_card_nsmul _ _ A h).trans ?_
  rw [ht, nsmul_eq_mul]
theorem map_sum_of_map_add {A B ι : Type} [AddCommGroup A] [AddCommGroup B] (f : A → B)
    (h : ∀ a b, f (a + b) = f a + f b) (s : Finset ι) (g : ι → A) :
    f (∑ i ∈ s, g i) = ∑ i ∈ s, f (g i) :=
  map_sum (AddMonoidHom.mk' f h) g s
section Inner
variable {𝒯 : NestedRegions}
theorem finite_fineSite (hl : TorusLengthsStatement) (𝒯 : NestedRegions) : Finite 𝒯.FineSite := by apply _root_.YangMills.Construction.RegionSequence.DifferenceAdjointsByParts.finite_fineSite <;> assumption
theorem finite_fineBond (𝒯 : NestedRegions) [Finite 𝒯.FineSite] : Finite 𝒯.FineBond :=
  Finite.of_injective (fun b : 𝒯.FineBond => (b.source, b.dir)) (by
    rintro ⟨a, b⟩ ⟨c, d⟩ h
    simp only [Prod.mk.injEq] at h
    simp [h.1, h.2])
variable [Finite 𝒯.FineBond]
theorem bondInner_eq [Fintype 𝒯.FineBond] (A B : 𝒯.FineBond → ℝ) :
    bondInner A B = 𝒯.ξ ^ 4 * ∑ b, A b * B b := by
  rw [bondInner, finsum_eq_sum_of_fintype]
omit [Finite 𝒯.FineBond] in
theorem bondInner_comm (A B : 𝒯.FineBond → ℝ) : bondInner A B = bondInner B A := by apply _root_.YangMills.Construction.RegionSequence.GradientAdjointsOnTorus.bondInner_comm <;> assumption
theorem bondInner_add_left (A A' B : 𝒯.FineBond → ℝ) :
    bondInner (A + A') B = bondInner A B + bondInner A' B := by apply _root_.YangMills.Construction.RegionSequence.Positivity.bondInner_add_left <;> assumption
theorem bondInner_sum_left {κ : Type} (s : Finset κ) (A : κ → 𝒯.FineBond → ℝ)
    (B : 𝒯.FineBond → ℝ) : bondInner (∑ i ∈ s, A i) B = ∑ i ∈ s, bondInner (A i) B :=
  map_sum (AddMonoidHom.mk' (fun A : 𝒯.FineBond → ℝ => bondInner A B)
    fun a b => bondInner_add_left a b B) A s
theorem eq_of_bondInner {A A' : 𝒯.FineBond → ℝ} (h : ∀ B, bondInner A B = bondInner A' B) :
    A = A' := by
  haveI := Fintype.ofFinite 𝒯.FineBond
  have hξ := 𝒯.ξ_pos
  have h1 := h (A - A')
  simp only [bondInner_eq] at h1
  have h2 : ∑ b, (A b - A' b) ^ 2 = 0 := by
    have h3 : 𝒯.ξ ^ 4 * ∑ b, (A b - A' b) ^ 2 = 0 := by
      rw [Finset.mul_sum]
      have e : ∀ b, 𝒯.ξ ^ 4 * (A b - A' b) ^ 2 =
          𝒯.ξ ^ 4 * (A b * (A - A') b) - 𝒯.ξ ^ 4 * (A' b * (A - A') b) := by
        intro b
        simp only [Pi.sub_apply]
        ring
      simp only [e, Finset.sum_sub_distrib, ← Finset.mul_sum]
      linarith
    exact (mul_eq_zero.1 h3).resolve_left (by positivity)
  funext b
  have h3 := (Finset.sum_eq_zero_iff_of_nonneg fun b _ => sq_nonneg (A b - A' b)).1 h2 b
    (Finset.mem_univ _)
  have := pow_eq_zero_iff (two_ne_zero) |>.1 h3
  linarith
theorem divTwo_eq_sum (hb : ∀ A : 𝒯.FineBond → ℝ, A ∈ 𝒯.oneForms)
    (hadj : CellStructure.AdjointFacts 𝒯) (J : 𝒯.Tensor 2) :
    divTwo J = ∑ κ : Fin 2 → Fin 4, bwdDiff (κ 1) (bwdDiff (κ 0) (J κ)) := by
  set v : 𝒯.FineBond → ℝ :=
    ∑ κ : Fin 2 → Fin 4, bwdDiff (κ 1) (bwdDiff (κ 0) (J κ)) with hv
  have hvp : ∀ u : 𝒯.FineBond → ℝ,
      bondInner v u = tensorInner J (nablaTwo (nablaOne u)) := by
    intro u
    rw [hv, bondInner_sum_left, tensorInner]
    refine Finset.sum_congr rfl fun κ _ => ?_
    have e : nablaTwo (nablaOne u) κ = fwdDiff (κ 0) (fwdDiff (κ 1) u) := rfl
    rw [e, bondInner_comm (J κ), hadj.bond_adjoint, hadj.bond_adjoint, bondInner_comm]
  have hspec := Classical.epsilon_spec (p := fun x : 𝒯.FineBond → ℝ =>
    x ∈ ((𝒯.oneForms : Set (𝒯.FineBond → ℝ))) ∧
      ∀ u ∈ (𝒯.oneForms : Set (𝒯.FineBond → ℝ)), bondInner x u =
        tensorInner J ((fun A => nablaTwo (nablaOne A)) u))
    ⟨v, hb v, fun u _ => hvp u⟩
  refine eq_of_bondInner fun B => ?_
  rw [hvp]
  exact hspec.2 B (hb B)
end Inner
section Additivity
variable {𝒯 : NestedRegions}
theorem fwdDiff_add (ν : Fin 4) (a b : 𝒯.FineBond → ℝ) :
    fwdDiff ν (a + b) = fwdDiff ν a + fwdDiff ν b := by
  funext x
  simp only [NestedRegions.fwdDiff, Pi.add_apply]
  ring
theorem bwdDiff_add (ν : Fin 4) (a b : 𝒯.FineBond → ℝ) :
    bwdDiff ν (a + b) = bwdDiff ν a + bwdDiff ν b := by
  funext x
  simp only [bwdDiff, Pi.add_apply]
  ring
theorem nablaOne_add (a b : 𝒯.FineBond → ℝ) :
    nablaOne (a + b) = nablaOne a + nablaOne b := by
  funext ν
  simp only [nablaOne, Pi.add_apply, fwdDiff_add]
theorem nablaTwo_add (a b : 𝒯.Tensor 1) :
    nablaTwo (a + b) = nablaTwo a + nablaTwo b := by
  funext ν
  simp only [nablaTwo, Pi.add_apply, fwdDiff_add]
theorem divOne_add (a b : 𝒯.Tensor 1) :
    divOne (a + b) = divOne a + divOne b := by
  funext x
  by_cases hx : x ∈ 𝒯.bonds
  · simp [divOne, projBonds, hx, bwdDiff_add, Finset.sum_add_distrib]
  · simp [divOne, projBonds, hx]
theorem bondLap_add (a b : 𝒯.FineBond → ℝ) :
    bondLap (a + b) = bondLap a + bondLap b := by
  funext x
  simp only [bondLap, fwdDiff_add, bwdDiff_add, Pi.add_apply, Finset.sum_add_distrib]
theorem divTwo_add [Finite 𝒯.FineBond] (hb : ∀ A : 𝒯.FineBond → ℝ, A ∈ 𝒯.oneForms)
    (hadj : CellStructure.AdjointFacts 𝒯) (a b : 𝒯.Tensor 2) :
    divTwo (a + b) = divTwo a + divTwo b := by
  simp only [divTwo_eq_sum hb hadj, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun κ _ => ?_
  simp only [Pi.add_apply, bwdDiff_add]
end Additivity
section Pieces
variable {𝒯 : NestedRegions}
def siteTent (σ : ℝ) (c : 𝒯.Point) : 𝒯.FineSite → ℝ := fun x => tentProduct σ c (x : 𝒯.Point)
theorem abs_siteTent_le {σ : ℝ} (hσ : 0 < σ) (c : 𝒯.Point) (x : 𝒯.FineSite) :
    |siteTent σ c x| ≤ 1 := by
  show |tentProduct σ c (x : 𝒯.Point)| ≤ 1
  rw [abs_of_nonneg (tentProduct_nonneg _ _)]
  exact tentProduct_le_one hσ _ _
theorem anchor_eq_source (hΩ : 𝒯.Ω 0 = univ) (b : 𝒯.FineBond) : 𝒯.anchor b = b.source := by
  simp [anchor, hΩ]
theorem anchoredIn_iff (hΩ : 𝒯.Ω 0 = univ) {X : Set 𝒯.Point} {b : 𝒯.FineBond} :
    AnchoredIn X b ↔ (b.source : 𝒯.Point) ∈ X := by
  rw [AnchoredIn, anchor_eq_source hΩ]
theorem mem_cubeHalfSide_iff {o : 𝒯.Point} {lam : ℝ} {p : 𝒯.Point} :
    p ∈ cubeHalfSide o lam ↔ supNorm (p - o) ≤ lam := by
  simp [cubeHalfSide, cubeAt]
theorem sum_smul_siteTent_bond (hΩ : 𝒯.Ω 0 = univ) {σ r lam : ℝ} {o : 𝒯.Point}
    {ι : Finset (Fin 4 → ℤ)} {w : (Fin 4 → ℤ) → 𝒯.Point}
    (hsum : ∀ x, supNorm (x - o) ≤ r → ∑ i ∈ ι, tentProduct σ (w i) x = 1) (hr : lam ≤ r)
    {J : 𝒯.FineBond → ℝ} (hJ : AnchorSupported (cubeHalfSide o lam) J) :
    ∑ i ∈ ι, smulSiteBond (siteTent σ (w i)) J = J := by
  funext b
  rw [Finset.sum_apply]
  simp only [smulSiteBond, smul_eq_mul, ← Finset.sum_mul]
  by_cases h : AnchoredIn (cubeHalfSide o lam) b
  · have hb := mem_cubeHalfSide_iff.1 ((anchoredIn_iff hΩ).1 h)
    have := hsum _ (hb.trans hr)
    simp only [siteTent, this, one_mul]
  · simp [hJ b h]
theorem sum_smul_siteTent_tensor (hΩ : 𝒯.Ω 0 = univ) {σ r lam : ℝ} {o : 𝒯.Point}
    {ι : Finset (Fin 4 → ℤ)} {w : (Fin 4 → ℤ) → 𝒯.Point}
    (hsum : ∀ x, supNorm (x - o) ≤ r → ∑ i ∈ ι, tentProduct σ (w i) x = 1) (hr : lam ≤ r)
    {s : ℕ} {J : 𝒯.Tensor s} (hJ : TensorAnchorSupported (cubeHalfSide o lam) J) :
    ∑ i ∈ ι, smulSiteTensor (siteTent σ (w i)) J = J := by
  funext ν
  rw [Finset.sum_apply]
  exact sum_smul_siteTent_bond hΩ hsum hr (hJ ν)
theorem sum_siteTent_mul {σ r lam : ℝ} {o : 𝒯.Point}
    {ι : Finset (Fin 4 → ℤ)} {w : (Fin 4 → ℤ) → 𝒯.Point}
    (hsum : ∀ x, supNorm (x - o) ≤ r → ∑ i ∈ ι, tentProduct σ (w i) x = 1) (hr : lam ≤ r)
    {ζ : 𝒯.FineSite → ℝ} (hζ : VanishesOff (cubeHalfSide o lam) ζ) :
    ∑ i ∈ ι, siteTent σ (w i) * ζ = ζ := by
  funext x
  rw [Finset.sum_apply]
  simp only [Pi.mul_apply, ← Finset.sum_mul]
  by_cases h : (x : 𝒯.Point) ∈ cubeHalfSide o lam
  · have := hsum _ ((mem_cubeHalfSide_iff.1 h).trans hr)
    simp only [siteTent, this, one_mul]
  · simp [hζ x h]
theorem smul_siteTent_supported (hΩ : 𝒯.Ω 0 = univ) {σ : ℝ} (hσ : 0 < σ) (c : 𝒯.Point)
    (J : 𝒯.FineBond → ℝ) : AnchorSupported (cubeHalfSide c σ) (smulSiteBond (siteTent σ c) J) := by
  intro b hb
  by_contra h
  apply hb
  rw [anchoredIn_iff hΩ, mem_cubeHalfSide_iff]
  refine (supNorm_lt_of_tentProduct_ne_zero hσ fun h0 => h ?_).le
  simp [smulSiteBond, siteTent, h0]
theorem smul_siteTent_tensor_supported (hΩ : 𝒯.Ω 0 = univ) {σ : ℝ} (hσ : 0 < σ) (c : 𝒯.Point)
    {s : ℕ} (J : 𝒯.Tensor s) :
    TensorAnchorSupported (cubeHalfSide c σ) (smulSiteTensor (siteTent σ c) J) :=
  fun ν => smul_siteTent_supported hΩ hσ c (J ν)
theorem siteTent_mul_vanishesOff {σ : ℝ} (hσ : 0 < σ) (c : 𝒯.Point) (ζ : 𝒯.FineSite → ℝ) :
    VanishesOff {p : 𝒯.Point | supNorm (p - c) < σ} (siteTent σ c * ζ) := by
  intro x hx
  by_contra h
  apply hx
  refine supNorm_lt_of_tentProduct_ne_zero hσ fun h0 => h ?_
  simp [siteTent, h0]
theorem supNorm_lt_of_siteTent_mul_ne_zero {σ : ℝ} (hσ : 0 < σ) {c : 𝒯.Point}
    {ζ : 𝒯.FineSite → ℝ} {x : 𝒯.FineSite} (h : (siteTent σ c * ζ) x ≠ 0) :
    supNorm ((x : 𝒯.Point) - c) < σ := by
  by_contra h2
  exact h (siteTent_mul_vanishesOff hσ c ζ x h2)
variable [Finite 𝒯.FineSite] [Finite 𝒯.FineBond]
theorem supBond_smul_siteTent_le {σ : ℝ} (hσ : 0 < σ) (c : 𝒯.Point) (J : 𝒯.FineBond → ℝ) :
    supBond (smulSiteBond (siteTent σ c) J) ≤ supBond J := by
  refine supBond_le (supBond_nonneg _) fun b => ?_
  simp only [smulSiteBond, smul_eq_mul, abs_mul]
  exact (mul_le_of_le_one_left (abs_nonneg _) (abs_siteTent_le hσ c _)).trans (abs_le_supBond J b)
theorem supTensor_smul_siteTent_le {σ : ℝ} (hσ : 0 < σ) (c : 𝒯.Point) {s : ℕ} (J : 𝒯.Tensor s) :
    supTensor (smulSiteTensor (siteTent σ c) J) ≤ supTensor J := by
  refine supTensor_le (supTensor_nonneg _) fun ν b => ?_
  simp only [smulSiteTensor, smulSiteBond, smul_eq_mul, abs_mul]
  exact (mul_le_of_le_one_left (abs_nonneg _) (abs_siteTent_le hσ c _)).trans
    (abs_le_supTensor J ν b)
theorem supSite_siteTent_mul_le {σ : ℝ} (hσ : 0 < σ) (c : 𝒯.Point) (ζ : 𝒯.FineSite → ℝ) :
    supSite (siteTent σ c * ζ) ≤ supSite ζ := by
  refine supSite_le (supSite_nonneg _) fun x => ?_
  simp only [Pi.mul_apply, abs_mul]
  exact (mul_le_of_le_one_left (abs_nonneg _) (abs_siteTent_le hσ c _)).trans (abs_le_supSite ζ x)
theorem supSite_siteTent_le {σ : ℝ} (hσ : 0 < σ) (c : 𝒯.Point) : supSite (siteTent σ c) ≤ 1 :=
  supSite_le zero_le_one (abs_siteTent_le hσ c)
theorem siteTent_mul_norms_le (hlb : LeibnizHolder.Statement) {a σ lam : ℝ}
    (ha₀ : 0 ≤ a) (ha₁ : a < 1) (hσ : 0 < σ) (hlam : σ ≤ lam) (c : 𝒯.Point)
    (ζ : 𝒯.FineSite → ℝ) :
    holderSite a σ (siteTent σ c * ζ) + supSite (siteTent σ c * ζ) ≤
      2 * cutoffNormSum a lam ζ := by
  have h₁ := holderSite_mul a σ (siteTent σ c) ζ
  have h₂ : holderSite a σ (siteTent σ c) ≤ 1 := holderSite_tentProduct_le ha₀ ha₁.le hσ c
  have h₃ : holderSite a σ ζ ≤ holderSite a lam ζ :=
    ((hlb.2.2.1 𝒯 a lam σ ha₀ ha₁ hσ hlam).1 ζ).mono_scale
  have h₄ := supSite_siteTent_le hσ c
  have h₅ := supSite_siteTent_mul_le hσ c ζ
  have h₆ := supSite_nonneg ζ
  have h₇ := holderSite_nonneg a σ ζ
  have h₉ : supSite ζ * holderSite a σ (siteTent σ c) ≤ supSite ζ :=
    mul_le_of_le_one_right h₆ h₂
  have h₁₀ : supSite (siteTent σ c) * holderSite a σ ζ ≤ holderSite a σ ζ :=
    mul_le_of_le_one_left h₇ h₄
  simp only [cutoffNormSum]
  linarith
theorem smul_siteTent_norms_le (hlb : LeibnizHolder.Statement) {a σ lam : ℝ}
    (ha₀ : 0 ≤ a) (ha₁ : a < 1) (hσ : 0 < σ) (hlam : σ ≤ lam) (c : 𝒯.Point) {s : ℕ}
    (J : 𝒯.Tensor s) :
    holderTensor a σ (smulSiteTensor (siteTent σ c) J) +
        supTensor (smulSiteTensor (siteTent σ c) J) ≤ 2 * sourceNormSum a lam J := by
  have h₁ := holderTensor_smul a σ (siteTent σ c) J
  have h₂ : holderSite a σ (siteTent σ c) ≤ 1 := holderSite_tentProduct_le ha₀ ha₁.le hσ c
  have h₃ : holderTensor a σ J ≤ holderTensor a lam J :=
    ((hlb.2.2.1 𝒯 a lam σ ha₀ ha₁ hσ hlam).2.2 s J).mono_scale
  have h₄ := supSite_siteTent_le hσ c
  have h₅ := supTensor_smul_siteTent_le hσ c J
  have h₆ := supTensor_nonneg J
  have h₇ := holderTensor_nonneg a σ J
  have h₉ : supTensor J * holderSite a σ (siteTent σ c) ≤ supTensor J :=
    mul_le_of_le_one_right h₆ h₂
  have h₁₀ : supSite (siteTent σ c) * holderTensor a σ J ≤ holderTensor a σ J :=
    mul_le_of_le_one_left h₇ h₄
  simp only [sourceNormSum]
  linarith
theorem rpow_div_le_of_le_mul {a σ lam ℓ : ℝ} (ha₀ : 0 ≤ a) (ha₁ : a < 1) (hσ : 0 < σ)
    (hlam : σ ≤ lam) (hℓ : lam ≤ ℓ * σ) : (lam / σ) ^ a ≤ ℓ := by
  have h1 : 1 ≤ lam / σ := (one_le_div hσ).2 hlam
  have h2 : lam / σ ≤ ℓ := (div_le_iff₀ hσ).2 hℓ
  calc (lam / σ) ^ a ≤ (lam / σ) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le h1 ha₁.le
    _ = lam / σ := Real.rpow_one _
    _ ≤ ℓ := h2
theorem holderBond_rescale_le (hlb : LeibnizHolder.Statement) {a σ lam ℓ : ℝ}
    (ha₀ : 0 ≤ a) (ha₁ : a < 1) (hσ : 0 < σ) (hlam : σ ≤ lam) (hℓ : lam ≤ ℓ * σ)
    (F : 𝒯.FineBond → ℝ) :
    holderBond a lam F ≤ ℓ * (holderBond a σ F + 2 * supBond F) := by
  have h₁ := ((hlb.2.2.1 𝒯 a lam σ ha₀ ha₁ hσ hlam).2.1 F).le_rescale
  have h₂ := rpow_div_le_of_le_mul ha₀ ha₁ hσ hlam hℓ
  have h₃ := holderBond_nonneg a σ F
  have h₄ := supBond_nonneg F
  have h₅ : max (holderBond a σ F) (2 * supBond F) ≤ holderBond a σ F + 2 * supBond F :=
    max_le (by linarith) (by linarith)
  have h₆ : 0 ≤ (lam / σ) ^ a := Real.rpow_nonneg (div_nonneg (hσ.le.trans hlam) hσ.le) _
  exact h₁.trans (mul_le_mul h₂ h₅ (le_max_of_le_left h₃) (h₆.trans h₂))
theorem holderTensor_rescale_le (hlb : LeibnizHolder.Statement) {a σ lam ℓ : ℝ}
    (ha₀ : 0 ≤ a) (ha₁ : a < 1) (hσ : 0 < σ) (hlam : σ ≤ lam) (hℓ : lam ≤ ℓ * σ) {s : ℕ}
    (F : 𝒯.Tensor s) :
    holderTensor a lam F ≤ ℓ * (holderTensor a σ F + 2 * supTensor F) := by
  have h₁ := ((hlb.2.2.1 𝒯 a lam σ ha₀ ha₁ hσ hlam).2.2 s F).le_rescale
  have h₂ := rpow_div_le_of_le_mul ha₀ ha₁ hσ hlam hℓ
  have h₃ := holderTensor_nonneg a σ F
  have h₄ := supTensor_nonneg F
  have h₅ : max (holderTensor a σ F) (2 * supTensor F) ≤ holderTensor a σ F + 2 * supTensor F :=
    max_le (by linarith) (by linarith)
  have h₆ : 0 ≤ (lam / σ) ^ a := Real.rpow_nonneg (div_nonneg (hσ.le.trans hlam) hσ.le) _
  exact h₁.trans (mul_le_mul h₂ h₅ (le_max_of_le_left h₃) (h₆.trans h₂))
theorem supBond_smul_le {ζ : 𝒯.FineSite → ℝ} {g : 𝒯.FineBond → ℝ} {U : ℝ} (hU : 0 ≤ U)
    (h : ∀ b : 𝒯.FineBond, ζ b.source ≠ 0 → |g b| ≤ U) :
    supBond (smulSiteBond ζ g) ≤ supSite ζ * U := by
  refine supBond_le (mul_nonneg (supSite_nonneg _) hU) fun b => ?_
  simp only [smulSiteBond, smul_eq_mul, abs_mul]
  by_cases h0 : ζ b.source = 0
  · simp only [h0, abs_zero, zero_mul]
    exact mul_nonneg (supSite_nonneg _) hU
  · exact mul_le_mul (abs_le_supSite ζ _) (h b h0) (abs_nonneg _) (supSite_nonneg _)
theorem supTensor_smul_le {s : ℕ} {ζ : 𝒯.FineSite → ℝ} {g : 𝒯.Tensor s} {U : ℝ} (hU : 0 ≤ U)
    (h : ∀ b : 𝒯.FineBond, ζ b.source ≠ 0 → tensorModulusAt g b ≤ U) :
    supTensor (smulSiteTensor ζ g) ≤ supSite ζ * U := by
  refine Real.iSup_le (fun ν => supBond_smul_le hU fun b hb => ?_)
    (mul_nonneg (supSite_nonneg _) hU)
  exact (abs_le_tensorModulusAt g ν b).trans (h b hb)
end Pieces
section Products
variable {𝒯 : NestedRegions}
theorem smulSiteBond_sum_sum {ι κ : Type} (s : Finset ι) (t : Finset κ) (z : ι → 𝒯.FineSite → ℝ)
    (g : κ → 𝒯.FineBond → ℝ) :
    smulSiteBond (∑ i ∈ s, z i) (∑ j ∈ t, g j) =
      ∑ i ∈ s, ∑ j ∈ t, smulSiteBond (z i) (g j) := by
  funext b
  simp only [smulSiteBond, Finset.sum_apply, smul_eq_mul, Finset.sum_mul_sum]
theorem smulSiteTensor_sum_sum {ι κ : Type} {r : ℕ} (s : Finset ι) (t : Finset κ)
    (z : ι → 𝒯.FineSite → ℝ) (g : κ → 𝒯.Tensor r) :
    smulSiteTensor (∑ i ∈ s, z i) (∑ j ∈ t, g j) =
      ∑ i ∈ s, ∑ j ∈ t, smulSiteTensor (z i) (g j) := by
  funext ν
  simp only [smulSiteTensor, Finset.sum_apply]
  exact smulSiteBond_sum_sum s t z fun j => g j ν
end Products
open YangMills.Construction.CubeTorus (cornerBox cornerBoxInterior)
section CornerCovers
variable {𝒮 : NestedRegions} {M : ℕ}
theorem le_sq_mul_of_subadditive_single {V κ : Type} [AddCommMonoid V] (N : V → ℝ) (h₀ : N 0 ≤ 0)
    (hadd : ∀ a b, N (a + b) ≤ N a + N b) (t : Finset κ) (f : κ → V)
    {A : ℝ} (hA : 0 ≤ A) (h : ∀ j ∈ t, N (f j) ≤ A) {n : ℕ} (ht : t.card = n) (hn : 1 ≤ n) :
    N (∑ j ∈ t, f j) ≤ (n : ℝ) ^ 2 * A := by
  refine (le_card_mul_of_subadditive N h₀ hadd t f h ht).trans ?_
  have h1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have h2 : (n : ℝ) ≤ (n : ℝ) ^ 2 := by nlinarith
  exact mul_le_mul_of_nonneg_right h2 hA
theorem tensorModulusAt_add {𝒯 : NestedRegions} {s : ℕ} (a b : 𝒯.Tensor s) (x : 𝒯.FineBond) :
    tensorModulusAt (a + b) x ≤ tensorModulusAt a x + tensorModulusAt b x :=
  tensorModulusAt_le (add_nonneg (tensorModulusAt_nonneg _ _) (tensorModulusAt_nonneg _ _)) fun ν =>
    (abs_add_le _ _).trans (add_le_add (abs_le_tensorModulusAt a ν x) (abs_le_tensorModulusAt b ν x))
theorem tensorModulusAt_zero {𝒯 : NestedRegions} {s : ℕ} (x : 𝒯.FineBond) :
    tensorModulusAt (0 : 𝒯.Tensor s) x ≤ 0 :=
  tensorModulusAt_le le_rfl fun _ => by simp
theorem mul_mul_le_three {A e E s S : ℝ} (hA : 0 ≤ A) (he₀ : 0 ≤ e) (he : e ≤ E) (hs₀ : 0 ≤ s)
    (hs : s ≤ S) : A * e * s ≤ A * E * S :=
  mul_le_mul (mul_le_mul_of_nonneg_left he hA) hs hs₀ (mul_nonneg hA (he₀.trans he))
theorem mul_mul_mul_le_four {A e E s S t T : ℝ} (hA : 0 ≤ A) (he₀ : 0 ≤ e) (he : e ≤ E)
    (hs₀ : 0 ≤ s) (hs : s ≤ S) (ht₀ : 0 ≤ t) (ht : t ≤ T) : A * e * s * t ≤ A * E * S * T :=
  mul_le_mul (mul_mul_le_three hA he₀ he hs₀ hs) ht ht₀
    (mul_nonneg (mul_nonneg hA (he₀.trans he)) (hs₀.trans hs))
structure CornerCover (c₀ : CubeTorus.TorusConstants) (Q : LevelCube 𝒮 M) (ι : Finset (Fin 4 → ℤ))
    (w w' : (Fin 4 → ℤ) → (torusSetting Q).Point) (o o' : (torusSetting Q).Point)
    (r E ℓ lam₁ lam₂ : ℝ) (n : ℕ) : Prop where
  leibniz : LeibnizHolder.Statement
  regions_univ : (torusSetting Q).Ω 0 = univ
  spacing_pos : 0 < levelSpacing Q
  B_nonneg : 0 ≤ c₀.B
  E_nonneg : 0 ≤ E
  one_le_ℓ : 1 ≤ ℓ
  inv_additive : ∀ a b, Q.system.inv (a + b) = Q.system.inv a + Q.system.inv b
  divTwo_additive : ∀ a b : (torusSetting Q).Tensor 2, divTwo (a + b) = divTwo a + divTwo b
  card_eq : ι.card = n
  one_le_card : 1 ≤ n
  sum_left : ∀ x, supNorm (x - o) ≤ r → ∑ i ∈ ι, tentProduct (levelSpacing Q) (w i) x = 1
  sum_right : ∀ x, supNorm (x - o') ≤ r → ∑ i ∈ ι, tentProduct (levelSpacing Q) (w' i) x = 1
  corner_pair : ∀ i ∈ ι, ∀ j ∈ ι,
    c₀.CornerGreenBounds Q (w i) (w' j) ∧ c₀.cornerExpDecay Q (w i) (w' j) ≤ E
  near_corner : ∀ b : (torusSetting Q).FineBond, supNorm ((b.source : (torusSetting Q).Point) - o) ≤
      2 * lam₁ → ∃ u, AnchoredIn (cornerBox Q u) b ∧
        ∀ j ∈ ι, c₀.CornerGreenBounds Q u (w' j) ∧ c₀.cornerExpDecay Q u (w' j) ≤ E
  lam₁_le_r : lam₁ ≤ r
  lam₂_le_r : lam₂ ≤ r
  spacing_le_lam₁ : levelSpacing Q ≤ lam₁
  spacing_le_lam₂ : levelSpacing Q ≤ lam₂
  lam₁_le_mul : lam₁ ≤ ℓ * levelSpacing Q
  five_lam₁_lt_side : 4 * lam₁ + lam₁ < (torusSetting Q).side
variable {c₀ : CubeTorus.TorusConstants} {Q : LevelCube 𝒮 M} {ι : Finset (Fin 4 → ℤ)}
  {w w' : (Fin 4 → ℤ) → (torusSetting Q).Point} {o o' : (torusSetting Q).Point}
  {r E ℓ lam₁ lam₂ : ℝ} {n : ℕ}
namespace CornerCover
theorem cornerExpDecay_nonneg (c₀ : CubeTorus.TorusConstants) (Q : LevelCube 𝒮 M)
    (a b : (torusSetting Q).Point) : 0 ≤ c₀.cornerExpDecay Q a b := (Real.exp_pos _).le
variable (h : CornerCover c₀ Q ι w w' o o' r E ℓ lam₁ lam₂ n)
include h
theorem sum_bond_pieces {J : (torusSetting Q).FineBond → ℝ}
    (hJ : AnchorSupported (cubeHalfSide o' lam₂) J) :
    ∑ j ∈ ι, smulSiteBond (siteTent (levelSpacing Q) (w' j)) J = J :=
  sum_smul_siteTent_bond h.regions_univ h.sum_right h.lam₂_le_r hJ
theorem sum_tensor_pieces {s : ℕ} {J : (torusSetting Q).Tensor s}
    (hJ : TensorAnchorSupported (cubeHalfSide o' lam₂) J) :
    ∑ j ∈ ι, smulSiteTensor (siteTent (levelSpacing Q) (w' j)) J = J :=
  sum_smul_siteTent_tensor h.regions_univ h.sum_right h.lam₂_le_r hJ
theorem sum_site_pieces {ζ : (torusSetting Q).FineSite → ℝ}
    (hζ : VanishesOff (cubeHalfSide o lam₁) ζ) :
    ∑ i ∈ ι, siteTent (levelSpacing Q) (w i) * ζ = ζ :=
  sum_siteTent_mul h.sum_left h.lam₁_le_r hζ
theorem anchoredIn_of_piece {c : (torusSetting Q).Point} {ζ : (torusSetting Q).FineSite → ℝ}
    {b : (torusSetting Q).FineBond} (hb : (siteTent (levelSpacing Q) c * ζ) b.source ≠ 0) :
    AnchoredIn (cornerBox Q c) b :=
  (anchoredIn_iff h.regions_univ).2
    (mem_cubeHalfSide_iff.2 (supNorm_lt_of_siteTent_mul_ne_zero h.spacing_pos hb).le)
theorem bond_piece_supported (c : (torusSetting Q).Point) (J : (torusSetting Q).FineBond → ℝ) :
    AnchorSupported (cornerBox Q c) (smulSiteBond (siteTent (levelSpacing Q) c) J) :=
  smul_siteTent_supported h.regions_univ h.spacing_pos c J
theorem tensor_piece_supported {s : ℕ} (c : (torusSetting Q).Point)
    (J : (torusSetting Q).Tensor s) :
    TensorAnchorSupported (cornerBox Q c) (smulSiteTensor (siteTent (levelSpacing Q) c) J) :=
  smul_siteTent_tensor_supported h.regions_univ h.spacing_pos c J
theorem site_piece_vanishesOff (c : (torusSetting Q).Point) (ζ : (torusSetting Q).FineSite → ℝ) :
    VanishesOff (cornerBoxInterior Q c) (siteTent (levelSpacing Q) c * ζ) :=
  siteTent_mul_vanishesOff h.spacing_pos c ζ
theorem inv_eq_sum {J : (torusSetting Q).FineBond → ℝ}
    (hJ : AnchorSupported (cubeHalfSide o' lam₂) J) :
    Q.system.inv J =
      ∑ j ∈ ι, Q.system.inv (smulSiteBond (siteTent (levelSpacing Q) (w' j)) J) := by
  conv_lhs => rw [← h.sum_bond_pieces hJ]
  exact map_sum_of_map_add _ h.inv_additive _ _
theorem inv_divOne_eq_sum {J : (torusSetting Q).Tensor 1}
    (hJ : TensorAnchorSupported (cubeHalfSide o' lam₂) J) :
    Q.system.inv (divOne J) =
      ∑ j ∈ ι, Q.system.inv (divOne (smulSiteTensor (siteTent (levelSpacing Q) (w' j)) J)) := by
  conv_lhs => rw [← h.sum_tensor_pieces hJ]
  exact map_sum_of_map_add (fun K => Q.system.inv (divOne K))
    (fun a b => by simp only [divOne_add, h.inv_additive]) _ _
theorem inv_divTwo_eq_sum {J : (torusSetting Q).Tensor 2}
    (hJ : TensorAnchorSupported (cubeHalfSide o' lam₂) J) :
    Q.system.inv (divTwo J) =
      ∑ j ∈ ι, Q.system.inv (divTwo (smulSiteTensor (siteTent (levelSpacing Q) (w' j)) J)) := by
  conv_lhs => rw [← h.sum_tensor_pieces hJ]
  exact map_sum_of_map_add (fun K => Q.system.inv (divTwo K))
    (fun a b => by simp only [h.divTwo_additive, h.inv_additive]) _ _
variable [Finite (torusSetting Q).FineSite] [Finite (torusSetting Q).FineBond]
theorem value {J : (torusSetting Q).FineBond → ℝ} (hJ : AnchorSupported (cubeHalfSide o' lam₂) J)
    {x : (torusSetting Q).FineBond}
    (hx : supNorm ((x.source : (torusSetting Q).Point) - o) ≤ 2 * lam₁) :
    |Q.system.inv J x| ≤ (n : ℝ) ^ 2 * (c₀.B * levelSpacing Q ^ 2 * E * supBond J) := by
  obtain ⟨u, hu, hp⟩ := h.near_corner x hx
  have hσ := h.spacing_pos
  have hA : 0 ≤ c₀.B * levelSpacing Q ^ 2 := mul_nonneg h.B_nonneg (by positivity)
  rw [h.inv_eq_sum hJ, Finset.sum_apply]
  refine le_sq_mul_of_subadditive_single (fun t : ℝ => |t|) (by simp) (fun a b => abs_add_le a b) ι _
    (mul_nonneg (mul_nonneg hA h.E_nonneg) (supBond_nonneg _)) (fun j hj => ?_) h.card_eq
    h.one_le_card
  exact ((hp j hj).1.value _ (h.bond_piece_supported _ J) x hu).trans
    (mul_mul_le_three hA (cornerExpDecay_nonneg _ _ _ _) (hp j hj).2 (supBond_nonneg _)
      (supBond_smul_siteTent_le hσ _ J))
theorem difference {J : (torusSetting Q).FineBond → ℝ}
    (hJ : AnchorSupported (cubeHalfSide o' lam₂) J) {x : (torusSetting Q).FineBond}
    (hx : supNorm ((x.source : (torusSetting Q).Point) - o) ≤ 2 * lam₁) :
    tensorModulusAt (nablaOne (Q.system.inv J)) x ≤
      (n : ℝ) ^ 2 * (c₀.B * levelSpacing Q * E * supBond J) := by
  obtain ⟨u, hu, hp⟩ := h.near_corner x hx
  have hσ := h.spacing_pos
  have hA : 0 ≤ c₀.B * levelSpacing Q := mul_nonneg h.B_nonneg hσ.le
  rw [h.inv_eq_sum hJ, map_sum_of_map_add _ nablaOne_add]
  refine le_sq_mul_of_subadditive_single
    (fun t : (torusSetting Q).Tensor 1 => tensorModulusAt t x)
    (tensorModulusAt_zero x) (fun a b => tensorModulusAt_add a b x) ι _
    (mul_nonneg (mul_nonneg hA h.E_nonneg) (supBond_nonneg _)) (fun j hj => ?_) h.card_eq
    h.one_le_card
  exact ((hp j hj).1.difference _ (h.bond_piece_supported _ J) x hu).trans
    (mul_mul_le_three hA (cornerExpDecay_nonneg _ _ _ _) (hp j hj).2 (supBond_nonneg _)
      (supBond_smul_siteTent_le hσ _ J))
theorem source {J : (torusSetting Q).Tensor 1}
    (hJ : TensorAnchorSupported (cubeHalfSide o' lam₂) J) {x : (torusSetting Q).FineBond}
    (hx : supNorm ((x.source : (torusSetting Q).Point) - o) ≤ 2 * lam₁) :
    |Q.system.inv (divOne J) x| ≤ (n : ℝ) ^ 2 * (c₀.B * levelSpacing Q * E * supTensor J) := by
  obtain ⟨u, hu, hp⟩ := h.near_corner x hx
  have hσ := h.spacing_pos
  have hA : 0 ≤ c₀.B * levelSpacing Q := mul_nonneg h.B_nonneg hσ.le
  rw [h.inv_divOne_eq_sum hJ, Finset.sum_apply]
  refine le_sq_mul_of_subadditive_single (fun t : ℝ => |t|) (by simp) (fun a b => abs_add_le a b) ι _
    (mul_nonneg (mul_nonneg hA h.E_nonneg) (supTensor_nonneg _)) (fun j hj => ?_) h.card_eq
    h.one_le_card
  exact ((hp j hj).1.source _ (h.tensor_piece_supported _ J) x hu).trans
    (mul_mul_le_three hA (cornerExpDecay_nonneg _ _ _ _) (hp j hj).2 (supTensor_nonneg _)
      (supTensor_smul_siteTent_le hσ _ J))
theorem laplacian {J : (torusSetting Q).FineBond → ℝ}
    (hJ : AnchorSupported (cubeHalfSide o' lam₂) J) {x : (torusSetting Q).FineBond}
    (hx : supNorm ((x.source : (torusSetting Q).Point) - o) ≤ 2 * lam₁) :
    |bondLap (Q.system.inv J) x| ≤ (n : ℝ) ^ 2 * (c₀.B * E * supBond J) := by
  obtain ⟨u, hu, hp⟩ := h.near_corner x hx
  have hσ := h.spacing_pos
  rw [h.inv_eq_sum hJ, map_sum_of_map_add _ bondLap_add, Finset.sum_apply]
  refine le_sq_mul_of_subadditive_single (fun t : ℝ => |t|) (by simp) (fun a b => abs_add_le a b) ι _
    (mul_nonneg (mul_nonneg h.B_nonneg h.E_nonneg) (supBond_nonneg _)) (fun j hj => ?_) h.card_eq
    h.one_le_card
  exact ((hp j hj).1.laplacian _ (h.bond_piece_supported _ J) x hu).trans
    (mul_mul_le_three h.B_nonneg (cornerExpDecay_nonneg _ _ _ _) (hp j hj).2 (supBond_nonneg _)
      (supBond_smul_siteTent_le hσ _ J))
theorem source_difference {ε : ℝ} (hε₀ : 0 < ε) (hε₁ : ε < 1)
    {J : (torusSetting Q).Tensor 1}
    (hJ : TensorAnchorSupported (cubeHalfSide o' lam₂) J) {x : (torusSetting Q).FineBond}
    (hx : supNorm ((x.source : (torusSetting Q).Point) - o) ≤ 2 * lam₁) :
    tensorModulusAt (nablaOne (Q.system.inv (divOne J))) x ≤
      (n : ℝ) ^ 2 * (|c₀.Bε ε| * E * (2 * sourceNormSum ε lam₂ J)) := by
  obtain ⟨u, hu, hp⟩ := h.near_corner x hx
  have hσ := h.spacing_pos
  have hsf := fun j =>
    smul_siteTent_norms_le h.leibniz hε₀.le hε₁ hσ h.spacing_le_lam₂ (w' j) J
  have hS : 0 ≤ sourceNormSum ε lam₂ J :=
    add_nonneg (holderTensor_nonneg _ _ _) (supTensor_nonneg _)
  rw [h.inv_divOne_eq_sum hJ, map_sum_of_map_add _ nablaOne_add]
  refine le_sq_mul_of_subadditive_single
    (fun t : (torusSetting Q).Tensor 1 => tensorModulusAt t x)
    (tensorModulusAt_zero x) (fun a b => tensorModulusAt_add a b x) ι _
    (mul_nonneg (mul_nonneg (abs_nonneg _) h.E_nonneg) (by positivity)) (fun j hj => ?_) h.card_eq
    h.one_le_card
  refine ((hp j hj).1.source_difference ε hε₀ hε₁ _ (h.tensor_piece_supported _ J) x hu).trans ?_
  refine (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_abs_self _)
    (cornerExpDecay_nonneg _ _ _ _))
    (add_nonneg (holderTensor_nonneg _ _ _) (supTensor_nonneg _))).trans ?_
  exact mul_mul_le_three (abs_nonneg _) (cornerExpDecay_nonneg _ _ _ _) (hp j hj).2
    (add_nonneg (holderTensor_nonneg _ _ _) (supTensor_nonneg _)) (hsf j)
end CornerCover
end CornerCovers
open YangMills.Construction.LeibnizHolder
section CornerCovers
variable {𝒮 : NestedRegions} {M : ℕ}
variable {c₀ : CubeTorus.TorusConstants} {Q : LevelCube 𝒮 M} {ι : Finset (Fin 4 → ℤ)}
  {w w' : (Fin 4 → ℤ) → (torusSetting Q).Point} {o o' : (torusSetting Q).Point}
  {r E ℓ lam₁ lam₂ : ℝ} {n : ℕ}
theorem mul_mul_mul_le_four_of_le {A A' e E s S t T : ℝ} (hAA : A ≤ A') (hA : 0 ≤ A')
    (he₀ : 0 ≤ e) (he : e ≤ E) (hs₀ : 0 ≤ s) (hs : s ≤ S) (ht₀ : 0 ≤ t) (ht : t ≤ T) :
    A * e * s * t ≤ A' * E * S * T :=
  (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hAA he₀) hs₀) ht₀).trans
    (mul_mul_mul_le_four hA he₀ he hs₀ hs ht₀ ht)
theorem cutoffNormSum_nonneg {𝒯 : NestedRegions} (α lam : ℝ) (ζ : 𝒯.FineSite → ℝ) :
    0 ≤ cutoffNormSum α lam ζ :=
  add_nonneg (holderSite_nonneg _ _ _) (supSite_nonneg _)
theorem sourceNormSum_nonneg {𝒯 : NestedRegions} {s : ℕ} (α lam : ℝ) (J : 𝒯.Tensor s) :
    0 ≤ sourceNormSum α lam J :=
  add_nonneg (holderTensor_nonneg _ _ _) (supTensor_nonneg _)
theorem supSite_siteTent_mul_le_cutoffNormSum {𝒯 : NestedRegions} [Finite 𝒯.FineSite]
    [Finite 𝒯.FineBond] {σ : ℝ} (hσ : 0 < σ) (c : 𝒯.Point) (α lam : ℝ) (ζ : 𝒯.FineSite → ℝ) :
    supSite (siteTent σ c * ζ) ≤ cutoffNormSum α lam ζ :=
  (supSite_siteTent_mul_le hσ c ζ).trans (le_add_of_nonneg_left (holderSite_nonneg _ _ _))
theorem supBondOn_le {𝒯 : NestedRegions} {X : Set 𝒯.Point} {f : 𝒯.FineBond → ℝ} {C : ℝ}
    (hC : 0 ≤ C) (h : ∀ b : 𝒯.FineBond, (b.source : 𝒯.Point) ∈ X → |f b| ≤ C) :
    supBondOn X f ≤ C := by
  refine Real.sSup_le ?_ hC
  rintro _ ⟨b, hb, rfl⟩
  exact h b hb
theorem holderBondOn_mono {𝒯 : NestedRegions} [Finite 𝒯.FineBond] {X Y : Set 𝒯.Point}
    (hXY : X ⊆ Y) (α lam : ℝ) (f : 𝒯.FineBond → ℝ) :
    holderBondOn α lam X f ≤ holderBondOn α lam Y f := by
  have hbdd : BddAbove {t | ∃ b b' : 𝒯.FineBond, (b.source : 𝒯.Point) ∈ Y ∧
      (b'.source : 𝒯.Point) ∈ Y ∧ b.dir = b'.dir ∧
      0 < siteLOneDist b.source b'.source ∧ siteLOneDist b.source b'.source ≤ lam ∧
      t = (lam / siteLOneDist b.source b'.source) ^ α * ‖f b' - f b‖} := by
    refine ((Set.finite_range fun p : 𝒯.FineBond × 𝒯.FineBond =>
      (lam / siteLOneDist p.1.source p.2.source) ^ α * ‖f p.2 - f p.1‖).subset ?_).bddAbove
    rintro _ ⟨a, c, -, -, -, -, -, rfl⟩
    exact ⟨(a, c), rfl⟩
  refine Real.sSup_le ?_ ?_
  · rintro _ ⟨b, b', hb, hb', hd, h₀, h₁, rfl⟩
    exact le_csSup hbdd ⟨b, b', hXY hb, hXY hb', hd, h₀, h₁, rfl⟩
  · refine Real.sSup_nonneg ?_
    rintro _ ⟨b, b', -, -, -, h₀, h₁, rfl⟩
    have : 0 ≤ lam / siteLOneDist b.source b'.source := div_nonneg (h₀.le.trans h₁) h₀.le
    exact mul_nonneg (Real.rpow_nonneg this _) (norm_nonneg _)
theorem supThickening_subset_cubeAt {𝒯 : NestedRegions} {o : 𝒯.Point} {lam : ℝ} (hlam : 0 < lam) :
    supThickening (cubeHalfSide o lam) lam ⊆ cubeAt o (4 * lam) := by
  intro x hx
  have hx' : supSetDist {x} (cubeHalfSide o lam) ≤ ENNReal.ofReal lam := hx
  show supNorm (x - o) ≤ 4 * lam / 2
  by_contra hc
  have hc' : 2 * lam < supNorm (x - o) := by
    have : 4 * lam / 2 = 2 * lam := by ring
    linarith [not_le.1 hc]
  have hlow : ENNReal.ofReal (supNorm (x - o) - lam) ≤ supSetDist {x} (cubeHalfSide o lam) := by
    refine le_iInf₂ fun p hp => le_iInf₂ fun q hq => ENNReal.ofReal_le_ofReal ?_
    rw [Set.mem_singleton_iff.1 hp]
    have h₁ := supNorm_sub_le x q o
    have h₂ := mem_cubeHalfSide_iff.1 hq
    linarith
  have := (ENNReal.ofReal_le_ofReal_iff hlam.le).1 (hlow.trans hx')
  linarith
namespace CornerCover
theorem cornerExpDecay_nonneg' (c₀ : CubeTorus.TorusConstants) (Q : LevelCube 𝒮 M)
    (a b : (torusSetting Q).Point) : 0 ≤ c₀.cornerExpDecay Q a b := (Real.exp_pos _).le
variable (h : CornerCover c₀ Q ι w w' o o' r E ℓ lam₁ lam₂ n)
include h
variable [Finite (torusSetting Q).FineSite] [Finite (torusSetting Q).FineBond]
theorem difference_holder {α : ℝ} (hα₀ : 0 ≤ α) (hα₁ : α < 1)
    {ζ : (torusSetting Q).FineSite → ℝ} (hζ : VanishesOff (cubeHalfSide o lam₁) ζ)
    {J : (torusSetting Q).FineBond → ℝ} (hJ : AnchorSupported (cubeHalfSide o' lam₂) J) :
    holderTensor α lam₁ (smulSiteTensor ζ (nablaOne (Q.system.inv J))) ≤
      (n : ℝ) ^ 2 * (ℓ * (|c₀.Bα α| * levelSpacing Q * E *
          (2 * cutoffNormSum α lam₁ ζ) * supBond J +
        2 * (cutoffNormSum α lam₁ ζ * (c₀.B * levelSpacing Q * E * supBond J)))) := by
  have hσ := h.spacing_pos
  have hcf := cutoffNormSum_nonneg α lam₁ ζ
  have hA : 0 ≤ |c₀.Bα α| * levelSpacing Q := mul_nonneg (abs_nonneg _) hσ.le
  have hB : 0 ≤ c₀.B * levelSpacing Q := mul_nonneg h.B_nonneg hσ.le
  have hU : 0 ≤ c₀.B * levelSpacing Q * E * supBond J :=
    mul_nonneg (mul_nonneg hB h.E_nonneg) (supBond_nonneg _)
  have e : smulSiteTensor ζ (nablaOne (Q.system.inv J)) =
      ∑ i ∈ ι, ∑ j ∈ ι, smulSiteTensor (siteTent (levelSpacing Q) (w i) * ζ)
        (nablaOne (Q.system.inv (smulSiteBond (siteTent (levelSpacing Q) (w' j)) J))) := by
    rw [← smulSiteTensor_sum_sum, h.sum_site_pieces hζ, ← map_sum_of_map_add _ nablaOne_add,
      ← h.inv_eq_sum hJ]
  rw [e]
  refine le_sq_mul_of_subadditive (holderTensor α lam₁) (holderTensor_zero α lam₁)
    (holderTensor_add α lam₁) ι ι _ (fun i hi j hj => ?_)
    (mul_nonneg (by linarith [h.one_le_ℓ]) (add_nonneg (mul_nonneg (mul_nonneg
      (mul_nonneg hA h.E_nonneg) (by positivity)) (supBond_nonneg _)) (by positivity)))
    h.card_eq h.card_eq
  obtain ⟨hcb, hdec⟩ := h.corner_pair i hi j hj
  refine (holderTensor_rescale_le h.leibniz hα₀ hα₁ hσ h.spacing_le_lam₁ h.lam₁_le_mul _).trans
    (mul_le_mul_of_nonneg_left (add_le_add ?_ ?_) (by linarith [h.one_le_ℓ]))
  · refine (hcb.difference_holder α hα₀ hα₁ _ (h.site_piece_vanishesOff _ ζ) _
      (h.bond_piece_supported _ J)).trans ?_
    exact mul_mul_mul_le_four_of_le (mul_le_mul_of_nonneg_right (le_abs_self _) hσ.le) hA
      (cornerExpDecay_nonneg' _ _ _ _) hdec
      (add_nonneg (holderSite_nonneg _ _ _) (supSite_nonneg _))
      (siteTent_mul_norms_le h.leibniz hα₀ hα₁ hσ h.spacing_le_lam₁ _ ζ) (supBond_nonneg _)
      (supBond_smul_siteTent_le hσ _ J)
  · refine mul_le_mul_of_nonneg_left ?_ zero_le_two
    refine (supTensor_smul_le hU fun b hb => ?_).trans
      (mul_le_mul_of_nonneg_right (supSite_siteTent_mul_le_cutoffNormSum hσ _ α lam₁ ζ) hU)
    exact (hcb.difference _ (h.bond_piece_supported _ J) b (h.anchoredIn_of_piece hb)).trans
      (mul_mul_le_three hB (cornerExpDecay_nonneg' _ _ _ _) hdec (supBond_nonneg _)
        (supBond_smul_siteTent_le hσ _ J))
theorem source_holder {α : ℝ} (hα₀ : 0 ≤ α) (hα₁ : α < 1)
    {ζ : (torusSetting Q).FineSite → ℝ} (hζ : VanishesOff (cubeHalfSide o lam₁) ζ)
    {J : (torusSetting Q).Tensor 1} (hJ : TensorAnchorSupported (cubeHalfSide o' lam₂) J) :
    holderBond α lam₁ (smulSiteBond ζ (Q.system.inv (divOne J))) ≤
      (n : ℝ) ^ 2 * (ℓ * (|c₀.Bα α| * levelSpacing Q * E *
          (2 * cutoffNormSum α lam₁ ζ) * supTensor J +
        2 * (cutoffNormSum α lam₁ ζ * (c₀.B * levelSpacing Q * E * supTensor J)))) := by
  have hσ := h.spacing_pos
  have hcf := cutoffNormSum_nonneg α lam₁ ζ
  have hA : 0 ≤ |c₀.Bα α| * levelSpacing Q := mul_nonneg (abs_nonneg _) hσ.le
  have hB : 0 ≤ c₀.B * levelSpacing Q := mul_nonneg h.B_nonneg hσ.le
  have hU : 0 ≤ c₀.B * levelSpacing Q * E * supTensor J :=
    mul_nonneg (mul_nonneg hB h.E_nonneg) (supTensor_nonneg _)
  have e : smulSiteBond ζ (Q.system.inv (divOne J)) =
      ∑ i ∈ ι, ∑ j ∈ ι, smulSiteBond (siteTent (levelSpacing Q) (w i) * ζ)
        (Q.system.inv (divOne (smulSiteTensor (siteTent (levelSpacing Q) (w' j)) J))) := by
    rw [← smulSiteBond_sum_sum, h.sum_site_pieces hζ, ← h.inv_divOne_eq_sum hJ]
  rw [e]
  refine le_sq_mul_of_subadditive (holderBond α lam₁) (holderBond_zero α lam₁)
    (holderBond_add α lam₁) ι ι _ (fun i hi j hj => ?_)
    (mul_nonneg (by linarith [h.one_le_ℓ]) (add_nonneg (mul_nonneg (mul_nonneg
      (mul_nonneg hA h.E_nonneg) (by positivity)) (supTensor_nonneg _)) (by positivity)))
    h.card_eq h.card_eq
  obtain ⟨hcb, hdec⟩ := h.corner_pair i hi j hj
  refine (holderBond_rescale_le h.leibniz hα₀ hα₁ hσ h.spacing_le_lam₁ h.lam₁_le_mul _).trans
    (mul_le_mul_of_nonneg_left (add_le_add ?_ ?_) (by linarith [h.one_le_ℓ]))
  · refine (hcb.source_holder α hα₀ hα₁ _ (h.site_piece_vanishesOff _ ζ) _
      (h.tensor_piece_supported _ J)).trans ?_
    exact mul_mul_mul_le_four_of_le (mul_le_mul_of_nonneg_right (le_abs_self _) hσ.le) hA
      (cornerExpDecay_nonneg' _ _ _ _) hdec
      (add_nonneg (holderSite_nonneg _ _ _) (supSite_nonneg _))
      (siteTent_mul_norms_le h.leibniz hα₀ hα₁ hσ h.spacing_le_lam₁ _ ζ) (supTensor_nonneg _)
      (supTensor_smul_siteTent_le hσ _ J)
  · refine mul_le_mul_of_nonneg_left ?_ zero_le_two
    refine (supBond_smul_le hU fun b hb => ?_).trans
      (mul_le_mul_of_nonneg_right (supSite_siteTent_mul_le_cutoffNormSum hσ _ α lam₁ ζ) hU)
    exact (hcb.source _ (h.tensor_piece_supported _ J) b (h.anchoredIn_of_piece hb)).trans
      (mul_mul_le_three hB (cornerExpDecay_nonneg' _ _ _ _) hdec (supTensor_nonneg _)
        (supTensor_smul_siteTent_le hσ _ J))
theorem source_difference_holder {α ε : ℝ} (hα₀ : 0 ≤ α) (hα₁ : α < 1) (hε₀ : 0 < ε)
    (hαε : α + ε < 1)
    {ζ : (torusSetting Q).FineSite → ℝ} (hζ : VanishesOff (cubeHalfSide o lam₁) ζ)
    {J : (torusSetting Q).Tensor 1} (hJ : TensorAnchorSupported (cubeHalfSide o' lam₂) J) :
    holderTensor α lam₁ (smulSiteTensor ζ (nablaOne (Q.system.inv (divOne J)))) ≤
      (n : ℝ) ^ 2 * (ℓ * (|c₀.Bαε α ε| * E *
          (2 * cutoffNormSum α lam₁ ζ) * (2 * sourceNormSum (α + ε) lam₂ J) +
        2 * (cutoffNormSum α lam₁ ζ *
          (|c₀.Bε (α + ε)| * E * (2 * sourceNormSum (α + ε) lam₂ J))))) := by
  have hσ := h.spacing_pos
  have hcf := cutoffNormSum_nonneg α lam₁ ζ
  have hsf := sourceNormSum_nonneg (α + ε) lam₂ J
  have hε' : 0 < α + ε := by linarith
  have hA : 0 ≤ |c₀.Bαε α ε| := abs_nonneg _
  have hU : 0 ≤ |c₀.Bε (α + ε)| * E * (2 * sourceNormSum (α + ε) lam₂ J) :=
    mul_nonneg (mul_nonneg (abs_nonneg _) h.E_nonneg) (by positivity)
  have e : smulSiteTensor ζ (nablaOne (Q.system.inv (divOne J))) =
      ∑ i ∈ ι, ∑ j ∈ ι, smulSiteTensor (siteTent (levelSpacing Q) (w i) * ζ)
        (nablaOne (Q.system.inv (divOne
          (smulSiteTensor (siteTent (levelSpacing Q) (w' j)) J)))) := by
    rw [← smulSiteTensor_sum_sum, h.sum_site_pieces hζ, ← map_sum_of_map_add _ nablaOne_add,
      ← h.inv_divOne_eq_sum hJ]
  rw [e]
  refine le_sq_mul_of_subadditive (holderTensor α lam₁) (holderTensor_zero α lam₁)
    (holderTensor_add α lam₁) ι ι _ (fun i hi j hj => ?_)
    (mul_nonneg (by linarith [h.one_le_ℓ]) (add_nonneg (mul_nonneg (mul_nonneg
      (mul_nonneg hA h.E_nonneg) (by positivity)) (by positivity)) (by positivity)))
    h.card_eq h.card_eq
  obtain ⟨hcb, hdec⟩ := h.corner_pair i hi j hj
  have hpf := smul_siteTent_norms_le h.leibniz hε'.le hαε hσ h.spacing_le_lam₂ (w' j) J
  refine (holderTensor_rescale_le h.leibniz hα₀ hα₁ hσ h.spacing_le_lam₁ h.lam₁_le_mul _).trans
    (mul_le_mul_of_nonneg_left (add_le_add ?_ ?_) (by linarith [h.one_le_ℓ]))
  · refine (hcb.source_difference_holder α ε hα₀ hα₁ hε₀ hαε _ (h.site_piece_vanishesOff _ ζ) _
      (h.tensor_piece_supported _ J)).trans ?_
    exact mul_mul_mul_le_four_of_le (le_abs_self _) hA (cornerExpDecay_nonneg' c₀ Q (w i) (w' j))
      hdec (add_nonneg (holderSite_nonneg _ _ _) (supSite_nonneg _))
      (siteTent_mul_norms_le h.leibniz hα₀ hα₁ hσ h.spacing_le_lam₁ (w i) ζ)
      (add_nonneg (holderTensor_nonneg _ _ _) (supTensor_nonneg _)) hpf
  · refine mul_le_mul_of_nonneg_left ?_ zero_le_two
    refine (supTensor_smul_le hU fun b hb => ?_).trans
      (mul_le_mul_of_nonneg_right (supSite_siteTent_mul_le_cutoffNormSum hσ _ α lam₁ ζ) hU)
    refine (hcb.source_difference (α + ε) hε' hαε _ (h.tensor_piece_supported _ J) b
      (h.anchoredIn_of_piece hb)).trans ?_
    refine (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_abs_self _)
      (cornerExpDecay_nonneg' _ _ _ _)) (add_nonneg (holderTensor_nonneg _ _ _)
        (supTensor_nonneg _))).trans ?_
    exact mul_mul_le_three (abs_nonneg _) (cornerExpDecay_nonneg' _ _ _ _) hdec
      (add_nonneg (holderTensor_nonneg _ _ _) (supTensor_nonneg _)) hpf
theorem value_holder {α : ℝ} (hα₀ : 0 ≤ α) (hα₁ : α < 1)
    {ζ : (torusSetting Q).FineSite → ℝ} (hζ : VanishesOff (cubeHalfSide o lam₁) ζ)
    {J : (torusSetting Q).FineBond → ℝ} (hJ : AnchorSupported (cubeHalfSide o' lam₂) J) :
    (levelSpacing Q)⁻¹ * holderBond α lam₁ (smulSiteBond ζ (Q.system.inv J)) ≤
      (n : ℝ) ^ 2 * (ℓ * (c₀.B * levelSpacing Q * E * supBond J) * cutoffNormSum α lam₁ ζ) := by
  have hσ := h.spacing_pos
  have hlam : 0 < lam₁ := hσ.trans_le h.spacing_le_lam₁
  set g := Q.system.inv J with hg
  set Y : Set (torusSetting Q).Point := cubeAt o (4 * lam₁) with hY
  have hYm : ∀ p ∈ Y, supNorm (p - o) ≤ 2 * lam₁ := by
    intro p hp
    have : supNorm (p - o) ≤ 4 * lam₁ / 2 := hp
    linarith
  have hb := (h.leibniz.2.2.1 (torusSetting Q) α lam₁ lam₁ hα₀ hα₁ hlam le_rfl).2.1 g
  have hU₀ : 0 ≤ (n : ℝ) ^ 2 * (c₀.B * levelSpacing Q ^ 2 * E * supBond J) :=
    mul_nonneg (by positivity) (mul_nonneg (mul_nonneg (mul_nonneg h.B_nonneg (by positivity))
      h.E_nonneg) (supBond_nonneg _))
  have hU₁ : 0 ≤ (n : ℝ) ^ 2 * (c₀.B * levelSpacing Q * E * supBond J) :=
    mul_nonneg (by positivity) (mul_nonneg (mul_nonneg (mul_nonneg h.B_nonneg hσ.le) h.E_nonneg)
      (supBond_nonneg _))
  have h₁ := hb.mul_le ζ (cubeHalfSide o lam₁) (fun x hx => by
    by_contra hc
    exact hx (hζ x hc))
  have hsub := supThickening_subset_cubeAt (o := o) hlam
  have h₂ : supBondOn (supThickening (cubeHalfSide o lam₁) lam₁) g ≤
      (n : ℝ) ^ 2 * (c₀.B * levelSpacing Q ^ 2 * E * supBond J) :=
    supBondOn_le hU₀ fun b hbm => h.value hJ (hYm _ (hsub hbm))
  have h₃ : holderBondOn α lam₁ (supThickening (cubeHalfSide o lam₁) lam₁) g ≤
      lam₁ * ((n : ℝ) ^ 2 * (c₀.B * levelSpacing Q * E * supBond J)) := by
    refine (holderBondOn_mono hsub α lam₁ g).trans ?_
    refine (hb.le_fwdDiff Y (Or.inr ⟨o, 4 * lam₁, by positivity, h.five_lam₁_lt_side, rfl⟩)).trans ?_
    refine mul_le_mul_of_nonneg_left (Real.iSup_le (fun ν => ?_) hU₁) hlam.le
    refine supBondOn_le hU₁ fun b hbm => ?_
    exact (abs_le_tensorModulusAt (nablaOne g) (constIdx ν) b).trans (h.difference hJ (hYm _ hbm))
  have h₄ : lam₁ * ((n : ℝ) ^ 2 * (c₀.B * levelSpacing Q * E * supBond J)) ≤
      ℓ * ((n : ℝ) ^ 2 * (c₀.B * levelSpacing Q ^ 2 * E * supBond J)) := by
    have e : ℓ * ((n : ℝ) ^ 2 * (c₀.B * levelSpacing Q ^ 2 * E * supBond J)) =
        (ℓ * levelSpacing Q) * ((n : ℝ) ^ 2 * (c₀.B * levelSpacing Q * E * supBond J)) := by ring
    rw [e]
    exact mul_le_mul_of_nonneg_right h.lam₁_le_mul hU₁
  set U := (n : ℝ) ^ 2 * (c₀.B * levelSpacing Q ^ 2 * E * supBond J) with hUdef
  have hsemi := holderSite_nonneg α lam₁ ζ
  have hsup := supSite_nonneg ζ
  have hℓ := h.one_le_ℓ
  have h₅ : holderBond α lam₁ (smulSiteBond ζ g) ≤ ℓ * U * cutoffNormSum α lam₁ ζ := by
    refine h₁.trans ?_
    have t₁ : supBondOn (supThickening (cubeHalfSide o lam₁) lam₁) g * holderSite α lam₁ ζ ≤
        U * holderSite α lam₁ ζ :=
      mul_le_mul_of_nonneg_right h₂ hsemi
    have t₂ : supSite ζ * holderBondOn α lam₁ (supThickening (cubeHalfSide o lam₁) lam₁) g ≤
        supSite ζ * (ℓ * U) := mul_le_mul_of_nonneg_left (h₃.trans h₄) hsup
    have t₃ : U * holderSite α lam₁ ζ ≤ ℓ * U * holderSite α lam₁ ζ := by
      refine mul_le_mul_of_nonneg_right ?_ hsemi
      nlinarith
    simp only [cutoffNormSum]
    nlinarith
  have h₆ : (levelSpacing Q)⁻¹ * (ℓ * U * cutoffNormSum α lam₁ ζ) =
      (n : ℝ) ^ 2 * (ℓ * (c₀.B * levelSpacing Q * E * supBond J) * cutoffNormSum α lam₁ ζ) := by
    rw [hUdef]
    field_simp
  rw [← h₆]
  exact mul_le_mul_of_nonneg_left h₅ (inv_nonneg.2 hσ.le)
theorem value_two {ζ : (torusSetting Q).FineSite → ℝ} (hζ : VanishesOff (cubeHalfSide o lam₁) ζ)
    {J : (torusSetting Q).FineBond → ℝ} (hJ : AnchorSupported (cubeHalfSide o' lam₂) J) :
    ltwoBond (smulSiteBond ζ (Q.system.inv J)) ≤
      (n : ℝ) ^ 2 * ((c₀.B * levelSpacing Q ^ 2) * E * supSite ζ * ltwoBond J) := by
  have hσ := h.spacing_pos
  have hA : 0 ≤ (c₀.B * levelSpacing Q ^ 2) := mul_nonneg h.B_nonneg (by positivity)
  have e : smulSiteBond ζ (Q.system.inv J) =
      ∑ i ∈ ι, ∑ j ∈ ι, smulSiteBond (siteTent (levelSpacing Q) (w i) * ζ)
        (Q.system.inv (smulSiteBond (siteTent (levelSpacing Q) (w' j)) J)) := by
    rw [← smulSiteBond_sum_sum, h.sum_site_pieces hζ, ← h.inv_eq_sum hJ]
  rw [e]
  refine le_sq_mul_of_subadditive ltwoBond ltwoBond_zero ltwoBond_add ι ι _ (fun i hi j hj => ?_)
    (mul_nonneg (mul_nonneg (mul_nonneg hA h.E_nonneg) (supSite_nonneg _)) (ltwoBond_nonneg _))
    h.card_eq h.card_eq
  have hφ : ∀ x : (torusSetting Q).FineSite, |siteTent (levelSpacing Q) (w' j) x| ≤ 1 :=
    abs_siteTent_le hσ _
  exact ((h.corner_pair i hi j hj).1.value_two _ (h.site_piece_vanishesOff _ ζ) _
    (h.bond_piece_supported _ J)).trans
    (mul_mul_mul_le_four hA (cornerExpDecay_nonneg' _ _ _ _) (h.corner_pair i hi j hj).2
      (supSite_nonneg _) (supSite_siteTent_mul_le hσ _ ζ) (ltwoBond_nonneg _)
      (ltwoBond_smul_le hφ J))
theorem difference_two {ζ : (torusSetting Q).FineSite → ℝ}
    (hζ : VanishesOff (cubeHalfSide o lam₁) ζ)
    {J : (torusSetting Q).FineBond → ℝ} (hJ : AnchorSupported (cubeHalfSide o' lam₂) J) :
    ltwoTensor (smulSiteTensor ζ (nablaOne (Q.system.inv J))) ≤
      (n : ℝ) ^ 2 * ((c₀.B * levelSpacing Q) * E * supSite ζ * ltwoBond J) := by
  have hσ := h.spacing_pos
  have hA : 0 ≤ (c₀.B * levelSpacing Q) := mul_nonneg h.B_nonneg hσ.le
  have e : smulSiteTensor ζ (nablaOne (Q.system.inv J)) =
      ∑ i ∈ ι, ∑ j ∈ ι, smulSiteTensor (siteTent (levelSpacing Q) (w i) * ζ)
        (nablaOne (Q.system.inv (smulSiteBond (siteTent (levelSpacing Q) (w' j)) J))) := by
    rw [← smulSiteTensor_sum_sum, h.sum_site_pieces hζ, ← map_sum_of_map_add _ nablaOne_add,
      ← h.inv_eq_sum hJ]
  rw [e]
  refine le_sq_mul_of_subadditive ltwoTensor ltwoTensor_zero ltwoTensor_add ι ι _
    (fun i hi j hj => ?_)
    (mul_nonneg (mul_nonneg (mul_nonneg hA h.E_nonneg) (supSite_nonneg _)) (ltwoBond_nonneg _))
    h.card_eq h.card_eq
  have hφ : ∀ x : (torusSetting Q).FineSite, |siteTent (levelSpacing Q) (w' j) x| ≤ 1 :=
    abs_siteTent_le hσ _
  exact ((h.corner_pair i hi j hj).1.difference_two _ (h.site_piece_vanishesOff _ ζ) _
    (h.bond_piece_supported _ J)).trans
    (mul_mul_mul_le_four hA (cornerExpDecay_nonneg' _ _ _ _) (h.corner_pair i hi j hj).2
      (supSite_nonneg _) (supSite_siteTent_mul_le hσ _ ζ) (ltwoBond_nonneg _)
      (ltwoBond_smul_le hφ J))
theorem source_two {ζ : (torusSetting Q).FineSite → ℝ} (hζ : VanishesOff (cubeHalfSide o lam₁) ζ)
    {J : (torusSetting Q).Tensor 1} (hJ : TensorAnchorSupported (cubeHalfSide o' lam₂) J) :
    ltwoBond (smulSiteBond ζ (Q.system.inv (divOne J))) ≤
      (n : ℝ) ^ 2 * ((c₀.B * levelSpacing Q) * E * supSite ζ * ltwoTensor J) := by
  have hσ := h.spacing_pos
  have hA : 0 ≤ (c₀.B * levelSpacing Q) := mul_nonneg h.B_nonneg hσ.le
  have e : smulSiteBond ζ (Q.system.inv (divOne J)) =
      ∑ i ∈ ι, ∑ j ∈ ι, smulSiteBond (siteTent (levelSpacing Q) (w i) * ζ)
        (Q.system.inv (divOne (smulSiteTensor (siteTent (levelSpacing Q) (w' j)) J))) := by
    rw [← smulSiteBond_sum_sum, h.sum_site_pieces hζ, ← h.inv_divOne_eq_sum hJ]
  rw [e]
  refine le_sq_mul_of_subadditive ltwoBond ltwoBond_zero ltwoBond_add ι ι _ (fun i hi j hj => ?_)
    (mul_nonneg (mul_nonneg (mul_nonneg hA h.E_nonneg) (supSite_nonneg _)) (ltwoTensor_nonneg _))
    h.card_eq h.card_eq
  have hφ : ∀ x : (torusSetting Q).FineSite, |siteTent (levelSpacing Q) (w' j) x| ≤ 1 :=
    abs_siteTent_le hσ _
  exact ((h.corner_pair i hi j hj).1.source_two _ (h.site_piece_vanishesOff _ ζ) _
    (h.tensor_piece_supported _ J)).trans
    (mul_mul_mul_le_four hA (cornerExpDecay_nonneg' _ _ _ _) (h.corner_pair i hi j hj).2
      (supSite_nonneg _) (supSite_siteTent_mul_le hσ _ ζ) (ltwoTensor_nonneg _)
      (ltwoTensor_smul_le hφ J))
theorem source_difference_two {ζ : (torusSetting Q).FineSite → ℝ}
    (hζ : VanishesOff (cubeHalfSide o lam₁) ζ)
    {J : (torusSetting Q).Tensor 1} (hJ : TensorAnchorSupported (cubeHalfSide o' lam₂) J) :
    ltwoTensor (smulSiteTensor ζ (nablaOne (Q.system.inv (divOne J)))) ≤
      (n : ℝ) ^ 2 * (c₀.B * E * supSite ζ * ltwoTensor J) := by
  have hσ := h.spacing_pos
  have hA : 0 ≤ c₀.B := h.B_nonneg
  have e : smulSiteTensor ζ (nablaOne (Q.system.inv (divOne J))) =
      ∑ i ∈ ι, ∑ j ∈ ι, smulSiteTensor (siteTent (levelSpacing Q) (w i) * ζ)
        (nablaOne (Q.system.inv (divOne
          (smulSiteTensor (siteTent (levelSpacing Q) (w' j)) J)))) := by
    rw [← smulSiteTensor_sum_sum, h.sum_site_pieces hζ, ← map_sum_of_map_add _ nablaOne_add,
      ← h.inv_divOne_eq_sum hJ]
  rw [e]
  refine le_sq_mul_of_subadditive ltwoTensor ltwoTensor_zero ltwoTensor_add ι ι _
    (fun i hi j hj => ?_)
    (mul_nonneg (mul_nonneg (mul_nonneg hA h.E_nonneg) (supSite_nonneg _)) (ltwoTensor_nonneg _))
    h.card_eq h.card_eq
  have hφ : ∀ x : (torusSetting Q).FineSite, |siteTent (levelSpacing Q) (w' j) x| ≤ 1 :=
    abs_siteTent_le hσ _
  exact ((h.corner_pair i hi j hj).1.source_difference_two _ (h.site_piece_vanishesOff _ ζ) _
    (h.tensor_piece_supported _ J)).trans
    (mul_mul_mul_le_four hA (cornerExpDecay_nonneg' _ _ _ _) (h.corner_pair i hi j hj).2
      (supSite_nonneg _) (supSite_siteTent_mul_le hσ _ ζ) (ltwoTensor_nonneg _)
      (ltwoTensor_smul_le hφ J))
theorem second_difference_two {ζ : (torusSetting Q).FineSite → ℝ}
    (hζ : VanishesOff (cubeHalfSide o lam₁) ζ)
    {J : (torusSetting Q).FineBond → ℝ} (hJ : AnchorSupported (cubeHalfSide o' lam₂) J) :
    ltwoTensor (smulSiteTensor ζ (nablaTwo (nablaOne (Q.system.inv J)))) ≤
      (n : ℝ) ^ 2 * (c₀.B * E * supSite ζ * ltwoBond J) := by
  have hσ := h.spacing_pos
  have hA : 0 ≤ c₀.B := h.B_nonneg
  have e : smulSiteTensor ζ (nablaTwo (nablaOne (Q.system.inv J))) =
      ∑ i ∈ ι, ∑ j ∈ ι, smulSiteTensor (siteTent (levelSpacing Q) (w i) * ζ)
        (nablaTwo (nablaOne
          (Q.system.inv (smulSiteBond (siteTent (levelSpacing Q) (w' j)) J)))) := by
    rw [← smulSiteTensor_sum_sum, h.sum_site_pieces hζ,
      ← map_sum_of_map_add (fun a => nablaTwo (nablaOne a))
        (fun a b => by simp only [nablaOne_add, nablaTwo_add]), ← h.inv_eq_sum hJ]
  rw [e]
  refine le_sq_mul_of_subadditive ltwoTensor ltwoTensor_zero ltwoTensor_add ι ι _
    (fun i hi j hj => ?_)
    (mul_nonneg (mul_nonneg (mul_nonneg hA h.E_nonneg) (supSite_nonneg _)) (ltwoBond_nonneg _))
    h.card_eq h.card_eq
  have hφ : ∀ x : (torusSetting Q).FineSite, |siteTent (levelSpacing Q) (w' j) x| ≤ 1 :=
    abs_siteTent_le hσ _
  exact ((h.corner_pair i hi j hj).1.second_difference_two _ (h.site_piece_vanishesOff _ ζ) _
    (h.bond_piece_supported _ J)).trans
    (mul_mul_mul_le_four hA (cornerExpDecay_nonneg' _ _ _ _) (h.corner_pair i hi j hj).2
      (supSite_nonneg _) (supSite_siteTent_mul_le hσ _ ζ) (ltwoBond_nonneg _)
      (ltwoBond_smul_le hφ J))
theorem second_source_two {ζ : (torusSetting Q).FineSite → ℝ}
    (hζ : VanishesOff (cubeHalfSide o lam₁) ζ)
    {J : (torusSetting Q).Tensor 2} (hJ : TensorAnchorSupported (cubeHalfSide o' lam₂) J) :
    ltwoBond (smulSiteBond ζ (Q.system.inv (divTwo J))) ≤
      (n : ℝ) ^ 2 * (c₀.B * E * supSite ζ * ltwoTensor J) := by
  have hσ := h.spacing_pos
  have hA : 0 ≤ c₀.B := h.B_nonneg
  have e : smulSiteBond ζ (Q.system.inv (divTwo J)) =
      ∑ i ∈ ι, ∑ j ∈ ι, smulSiteBond (siteTent (levelSpacing Q) (w i) * ζ)
        (Q.system.inv (divTwo (smulSiteTensor (siteTent (levelSpacing Q) (w' j)) J))) := by
    rw [← smulSiteBond_sum_sum, h.sum_site_pieces hζ, ← h.inv_divTwo_eq_sum hJ]
  rw [e]
  refine le_sq_mul_of_subadditive ltwoBond ltwoBond_zero ltwoBond_add ι ι _ (fun i hi j hj => ?_)
    (mul_nonneg (mul_nonneg (mul_nonneg hA h.E_nonneg) (supSite_nonneg _)) (ltwoTensor_nonneg _))
    h.card_eq h.card_eq
  have hφ : ∀ x : (torusSetting Q).FineSite, |siteTent (levelSpacing Q) (w' j) x| ≤ 1 :=
    abs_siteTent_le hσ _
  exact ((h.corner_pair i hi j hj).1.second_source_two _ (h.site_piece_vanishesOff _ ζ) _
    (h.tensor_piece_supported _ J)).trans
    (mul_mul_mul_le_four hA (cornerExpDecay_nonneg' _ _ _ _) (h.corner_pair i hi j hj).2
      (supSite_nonneg _) (supSite_siteTent_mul_le hσ _ ζ) (ltwoTensor_nonneg _)
      (ltwoTensor_smul_le hφ J))
end CornerCover
end CornerCovers
open YangMills.Construction.CubeTorus (cornerBox cornerBoxInterior corners)
section Assembly
variable {𝒮 : NestedRegions} {M : ℕ}
variable {c₀ : CubeTorus.TorusConstants} {Q : LevelCube 𝒮 M} {ι : Finset (Fin 4 → ℤ)}
  {w w' : (Fin 4 → ℤ) → (torusSetting Q).Point} {o o' : (torusSetting Q).Point}
  {r ℓ K lam₁ lam₂ : ℝ} {n : ℕ}
end Assembly
end YangMills.Construction.FirstTypeGreenRegularity
