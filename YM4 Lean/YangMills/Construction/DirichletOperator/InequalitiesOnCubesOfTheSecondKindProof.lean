import YangMills.Construction.DirichletOperator.InequalitiesOfALocalGreenOperator
import Mathlib
set_option autoImplicit false
open Set
open YangMills.Construction.Dirichlet YangMills.Construction.Torus YangMills.Construction.RegionSequence YangMills.Construction.RegionSequence.NestedRegions YangMills.Construction.PartitionCubes
open YangMills.Construction.GreenRegularity
open YangMills.Construction.CubeTorus (TensorAnchorSupported tensorModulusAt)
noncomputable section
namespace YangMills.Construction.SecondTypeGreenRegularity
section Abstract
variable {ι : Type} [Fintype ι]
end Abstract
section Lengths
variable {S ξ : ℝ}
theorem lOneNorm_eq_sum (p : PeriodicTorus 4 S) : lOneNorm p = ∑ μ, ‖p μ‖ := by
  choose b hb hb' using fun μ => TorusMetric.exists_coe_eq_abs_eq_norm (p μ)
  have hcov : torusProj 4 S b = p := funext hb
  apply le_antisymm
  · refine csInf_le ⟨0, ?_⟩ ⟨b, hcov, ?_⟩
    · rintro _ ⟨v, -, rfl⟩
      exact Finset.sum_nonneg fun _ _ => abs_nonneg _
    · simp [hb']
  · refine le_csInf ⟨_, b, hcov, rfl⟩ ?_
    rintro _ ⟨v, hv, rfl⟩
    refine Finset.sum_le_sum fun μ _ => ?_
    rw [← hv]
    exact TorusMetric.addCircle_norm_coe_le_abs _
theorem supNorm_eq_norm (p : PeriodicTorus 4 S) : supNorm p = ‖p‖ := by
  choose b hb hb' using fun μ => TorusMetric.exists_coe_eq_abs_eq_norm (p μ)
  have hcov : torusProj 4 S b = p := funext hb
  apply le_antisymm
  · have h : supNorm p ≤ ‖b‖ := by
      refine csInf_le ⟨0, ?_⟩ ⟨b, hcov, rfl⟩
      rintro _ ⟨v, -, rfl⟩
      exact norm_nonneg _
    refine h.trans ((pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun μ => ?_)
    rw [Real.norm_eq_abs, hb']
    exact norm_le_pi_norm p μ
  · refine le_csInf ⟨_, b, hcov, rfl⟩ ?_
    rintro _ ⟨v, hv, rfl⟩
    refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun μ => ?_
    rw [← hv]
    refine (TorusMetric.addCircle_norm_coe_le_abs _).trans ?_
    rw [← Real.norm_eq_abs]
    exact norm_le_pi_norm v μ
theorem lOneNorm_nonneg (p : PeriodicTorus 4 S) : 0 ≤ lOneNorm p := by
  rw [lOneNorm_eq_sum]
  exact Finset.sum_nonneg fun _ _ => norm_nonneg _
theorem lOneNorm_add_le (p q : PeriodicTorus 4 S) : lOneNorm (p + q) ≤ lOneNorm p + lOneNorm q := by
  simp only [lOneNorm_eq_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun μ _ => norm_add_le _ _
theorem lOneNorm_neg (p : PeriodicTorus 4 S) : lOneNorm (-p) = lOneNorm p := by
  simp [lOneNorm_eq_sum]
theorem lOneNorm_zero : lOneNorm (0 : PeriodicTorus 4 S) = 0 := by
  simp [lOneNorm_eq_sum]
theorem lOneNorm_sub_comm (p q : PeriodicTorus 4 S) : lOneNorm (p - q) = lOneNorm (q - p) := by
  rw [← lOneNorm_neg, neg_sub]
theorem supNorm_le_lOneNorm (p : PeriodicTorus 4 S) : supNorm p ≤ lOneNorm p := by
  rw [lOneNorm_eq_sum, supNorm_eq_norm]
  refine (pi_norm_le_iff_of_nonneg (Finset.sum_nonneg fun _ _ => norm_nonneg _)).2 fun μ => ?_
  exact Finset.single_le_sum (f := fun μ => ‖p μ‖) (fun _ _ => norm_nonneg _) (Finset.mem_univ μ)
theorem supNorm_sub_le_add (p q r : PeriodicTorus 4 S) :
    supNorm (p - r) ≤ supNorm (p - q) + supNorm (q - r) := by
  have : p - r = (p - q) + (q - r) := by abel
  rw [this]
  simp only [supNorm_eq_norm]
  exact norm_add_le _ _
theorem supNorm_sub_comm (p q : PeriodicTorus 4 S) : supNorm (p - q) = supNorm (q - p) := by
  simp only [supNorm_eq_norm]
  exact norm_sub_rev _ _
theorem lOneNorm_unitStep_le (hξ : 0 < ξ) (ν : Fin 4) :
    lOneNorm ((unitStep 4 S ξ ν : LatticeSite 4 S ξ) : PeriodicTorus 4 S) ≤ ξ := by
  rw [lOneNorm_eq_sum]
  calc ∑ μ, ‖((unitStep 4 S ξ ν : LatticeSite 4 S ξ) : PeriodicTorus 4 S) μ‖
      ≤ ∑ μ, |(Pi.single ν ξ : Fin 4 → ℝ) μ| :=
        Finset.sum_le_sum fun μ _ => TorusMetric.addCircle_norm_coe_le_abs _
    _ = ξ := by
        simp [Pi.single_apply, abs_of_pos hξ, apply_ite]
theorem supNorm_unitStep_le (hξ : 0 < ξ) (ν : Fin 4) :
    supNorm ((unitStep 4 S ξ ν : LatticeSite 4 S ξ) : PeriodicTorus 4 S) ≤ ξ :=
  (supNorm_le_lOneNorm _).trans (lOneNorm_unitStep_le hξ ν)
theorem exists_int_coord_lift {K : ℤ} (hS : S = K * ξ) (y : LatticeSite 4 S ξ) :
    ∃ n : Fin 4 → ℤ, (y : PeriodicTorus 4 S) = torusProj 4 S (fun μ => (n μ : ℝ) * ξ) ∧
      ∀ μ, |((n μ : ℤ) : ℝ) * ξ| = ‖(y : PeriodicTorus 4 S) μ‖ := by
  obtain ⟨k, hk⟩ := y.2
  let r : Fin 4 → ℤ := fun μ => round (S⁻¹ * ((k μ : ℝ) * ξ))
  have hcoord : ∀ μ, (y : PeriodicTorus 4 S) μ = (((k μ : ℝ) * ξ : ℝ) : AddCircle S) := fun μ => by
    rw [hk]; rfl
  refine ⟨fun μ => k μ - r μ * K, ?_, fun μ => ?_⟩
  · rw [hk]
    funext μ
    have h0 : (((r μ : ℝ) * S : ℝ) : AddCircle S) = 0 := by
      rw [AddCircle.coe_eq_zero_iff]
      exact ⟨r μ, by simp⟩
    have : (((k μ - r μ * K : ℤ) : ℝ) * ξ) = (k μ : ℝ) * ξ - (r μ : ℝ) * S := by
      rw [hS]; push_cast; ring
    simp only [torusProj]
    rw [this, AddCircle.coe_sub, h0, sub_zero]
  · rw [hcoord, AddCircle.norm_eq]
    have : (((k μ - r μ * K : ℤ) : ℝ) * ξ) = (k μ : ℝ) * ξ - (r μ : ℝ) * S := by
      rw [hS]; push_cast; ring
    rw [this]
theorem le_lOneNorm_sub_of_ne {K : ℤ} (hS : S = K * ξ) (hξ : 0 < ξ) {x y : LatticeSite 4 S ξ}
    (h : x ≠ y) : ξ ≤ lOneNorm ((x : PeriodicTorus 4 S) - (y : PeriodicTorus 4 S)) := by
  obtain ⟨n, hn, hn'⟩ := exists_int_coord_lift hS (x - y)
  have hne : n ≠ 0 := by
    rintro rfl
    apply h
    have : ((x - y : LatticeSite 4 S ξ) : PeriodicTorus 4 S) = 0 := by
      rw [hn]
      funext μ
      simp [torusProj]
    exact sub_eq_zero.1 (Subtype.ext this)
  obtain ⟨μ, hμ⟩ := Function.ne_iff.1 hne
  have h1 : (1 : ℝ) ≤ |((n μ : ℤ) : ℝ)| := by
    have : 1 ≤ |n μ| := Int.one_le_abs hμ
    exact_mod_cast this
  have h2 : ξ ≤ ‖((x - y : LatticeSite 4 S ξ) : PeriodicTorus 4 S) μ‖ := by
    rw [← hn', abs_mul, abs_of_pos hξ]
    nlinarith
  rw [lOneNorm_eq_sum]
  have h3 : ((x - y : LatticeSite 4 S ξ) : PeriodicTorus 4 S) =
      (x : PeriodicTorus 4 S) - (y : PeriodicTorus 4 S) := rfl
  rw [h3] at h2
  exact h2.trans (Finset.single_le_sum
    (f := fun μ => ‖((x : PeriodicTorus 4 S) - (y : PeriodicTorus 4 S)) μ‖)
    (fun _ _ => norm_nonneg _) (Finset.mem_univ μ))
theorem finite_latticeSite {K : ℤ} (hS : S = K * ξ) (hξ : 0 < ξ) (hS0 : S ≠ 0) :
    Finite (LatticeSite 4 S ξ) := by
  choose n hn hn' using exists_int_coord_lift (ξ := ξ) hS
  let B : Finset (Fin 4 → ℤ) := Fintype.piFinset fun _ => Finset.Icc (-|K|) |K|
  have hB : ∀ y, n y ∈ B := by
    intro y
    refine Fintype.mem_piFinset.2 fun μ => ?_
    have h1 := hn' y μ
    have h2 : ‖(y : PeriodicTorus 4 S) μ‖ ≤ |S| / 2 := AddCircle.norm_le_half_period S hS0
    rw [← h1, abs_mul, abs_of_pos hξ, hS, abs_mul, abs_of_pos hξ] at h2
    have h3 : |((n y μ : ℤ) : ℝ)| ≤ |(K : ℝ)| := by
      have : |((n y μ : ℤ) : ℝ)| * ξ ≤ |(K : ℝ)| * ξ := by nlinarith [abs_nonneg (K : ℝ)]
      exact le_of_mul_le_mul_right this hξ
    have h4 : |n y μ| ≤ |K| := by exact_mod_cast h3
    exact Finset.mem_Icc.2 (abs_le.1 h4)
  refine Finite.of_injective (fun y => (⟨n y, hB y⟩ : {m // m ∈ B})) fun x y hxy => ?_
  have : n x = n y := congrArg Subtype.val hxy
  apply Subtype.ext
  rw [hn x, hn y, this]
end Lengths
open scoped Classical
section Adjoints
variable {ι κ : Type} [Fintype ι] [Fintype κ]
def transposeMap (T : (ι → ℝ) →ₗ[ℝ] (κ → ℝ)) : (κ → ℝ) →ₗ[ℝ] (ι → ℝ) where
  toFun F := fun b => dotProduct F (T (Pi.single b 1))
  map_add' F G := by funext b; simp [add_dotProduct]
  map_smul' c F := by funext b; simp [smul_dotProduct]
end Adjoints
section Setting
variable (𝒮 : NestedRegions)
theorem exists_side_eq_int_mul : ∃ K : ℤ, 𝒮.side = K * 𝒮.ξ := by
  obtain ⟨k, hk⟩ := 𝒮.side_mem_zmultiples
  refine ⟨k * (2 * (𝒮.L : ℤ) ^ 𝒮.s), ?_⟩
  rw [hk]
  simp [scaleSpacing]
  ring
theorem finite_fineSite : Finite 𝒮.FineSite := by
  obtain ⟨K, hK⟩ := exists_side_eq_int_mul 𝒮
  exact finite_latticeSite hK 𝒮.ξ_pos 𝒮.side_pos.ne'
@[reducible] def fineSiteFintype : Fintype 𝒮.FineSite := @Fintype.ofFinite _ (finite_fineSite 𝒮)
def fineBondEquiv : 𝒮.FineBond ≃ 𝒮.FineSite × Fin 4 where
  toFun b := (b.source, b.dir)
  invFun p := ⟨p.1, p.2⟩
  left_inv b := by cases b; rfl
  right_inv p := by cases p; rfl
@[reducible] def fineBondFintype : Fintype 𝒮.FineBond :=
  letI := fineSiteFintype 𝒮
  Fintype.ofEquiv _ (fineBondEquiv 𝒮).symm
attribute [local instance] fineSiteFintype fineBondFintype
variable {𝒮}
theorem bondInner_eq (A A' : 𝒮.FineBond → ℝ) : bondInner A A' = 𝒮.ξ ^ 4 * dotProduct A A' := by
  simp [bondInner, finsum_eq_sum_of_fintype, dotProduct]
def shiftEquiv (ν : Fin 4) : 𝒮.FineBond ≃ 𝒮.FineBond where
  toFun := shiftUp ν
  invFun := shiftDown ν
  left_inv b := by cases b; simp [shiftUp, shiftDown]
  right_inv b := by cases b; simp [shiftUp, shiftDown]
def plaqEdges (p : 𝒮.FinePlaquette) : Fin 4 → 𝒮.FineBond :=
  ![⟨p.1 + unitStep 4 𝒮.side 𝒮.ξ p.2.1.1, p.2.1.2⟩, ⟨p.1, p.2.1.2⟩,
    ⟨p.1 + unitStep 4 𝒮.side 𝒮.ξ p.2.1.2, p.2.1.1⟩, ⟨p.1, p.2.1.1⟩]
section Cubes
variable {M : ℕ} (Q : LevelCube 𝒮 M)
def bondDist (b c : 𝒮.FineBond) : ℝ :=
  𝒮.ξ⁻¹ * lOneNorm ((b.source : 𝒮.Point) - (c.source : 𝒮.Point))
end Cubes
end Setting
section Setting
attribute [local instance] fineSiteFintype fineBondFintype
variable {𝒮 : NestedRegions}
end Setting
section Setting
attribute [local instance] fineSiteFintype fineBondFintype
variable {𝒮 : NestedRegions}
theorem abs_le_supSite (f : 𝒮.FineSite → ℝ) (x : 𝒮.FineSite) : |f x| ≤ supSite f :=
  le_ciSup (f := fun x => ‖f x‖) (Set.finite_range _).bddAbove x
theorem abs_le_supBond (f : 𝒮.FineBond → ℝ) (b : 𝒮.FineBond) : |f b| ≤ supBond f :=
  le_ciSup (f := fun b => ‖f b‖) (Set.finite_range _).bddAbove b
theorem abs_le_supTensor {r : ℕ} (J : 𝒮.Tensor r) (ν : Fin r → Fin 4) (b : 𝒮.FineBond) :
    |J ν b| ≤ supTensor J :=
  (abs_le_supBond (J ν) b).trans
    (le_ciSup (f := fun ν => supBond (J ν)) (Set.finite_range _).bddAbove ν)
theorem supSite_nonneg (f : 𝒮.FineSite → ℝ) : 0 ≤ supSite f :=
  Real.iSup_nonneg fun _ => norm_nonneg _
theorem supBond_nonneg (f : 𝒮.FineBond → ℝ) : 0 ≤ supBond f :=
  Real.iSup_nonneg fun _ => norm_nonneg _
theorem supTensor_nonneg {r : ℕ} (J : 𝒮.Tensor r) : 0 ≤ supTensor J :=
  Real.iSup_nonneg fun _ => supBond_nonneg _
theorem holderSite_nonneg (α lam : ℝ) (f : 𝒮.FineSite → ℝ) : 0 ≤ holderSite α lam f := by
  apply Real.sSup_nonneg
  rintro r ⟨x, x', h₀, h₁, rfl⟩
  have : 0 ≤ lam / siteLOneDist x x' := div_nonneg (h₀.le.trans h₁) h₀.le
  exact mul_nonneg (Real.rpow_nonneg this _) (norm_nonneg _)
theorem holderBond_nonneg (α lam : ℝ) (f : 𝒮.FineBond → ℝ) : 0 ≤ holderBond α lam f := by
  apply Real.sSup_nonneg
  rintro r ⟨b, b', _, h₀, h₁, rfl⟩
  have : 0 ≤ lam / siteLOneDist b.source b'.source := div_nonneg (h₀.le.trans h₁) h₀.le
  exact mul_nonneg (Real.rpow_nonneg this _) (norm_nonneg _)
theorem holderTensor_nonneg {r : ℕ} (α lam : ℝ) (J : 𝒮.Tensor r) :
    0 ≤ holderTensor α lam J :=
  Real.iSup_nonneg fun _ => holderBond_nonneg _ _ _
section Cubes
variable {M : ℕ} (Q : LevelCube 𝒮 M)
end Cubes
theorem holderBond_le {h : 𝒮.FineBond → ℝ} {H : ℝ} (hH : 0 ≤ H) (hb : ∀ b, |h b| ≤ H)
    {α lam : ℝ} (hα₁ : α < 1) (hlam : lam ≤ (𝒮.L : ℝ) * 𝒮.ξ) :
    holderBond α lam h ≤ 2 * (𝒮.L : ℝ) * H := by
  have hL : (1 : ℝ) ≤ 𝒮.L := by
    have := 𝒮.thirteen_le_L
    exact_mod_cast (by omega : 1 ≤ 𝒮.L)
  obtain ⟨K, hK⟩ := exists_side_eq_int_mul 𝒮
  have hξ := 𝒮.ξ_pos
  refine Real.sSup_le ?_ (by positivity)
  rintro _ ⟨b, b', _, h₀, h₁, rfl⟩
  have hne : b.source ≠ b'.source := by
    intro e
    simp [siteLOneDist, e, lOneNorm_zero] at h₀
  have hd : 𝒮.ξ ≤ siteLOneDist b.source b'.source := le_lOneNorm_sub_of_ne hK hξ hne
  have ht1 : 1 ≤ lam / siteLOneDist b.source b'.source := (one_le_div₀ h₀).2 h₁
  have ht2 : lam / siteLOneDist b.source b'.source ≤ 𝒮.L := by
    rw [div_le_iff₀ h₀]
    nlinarith
  have hr : (lam / siteLOneDist b.source b'.source) ^ α ≤ 𝒮.L := by
    calc (lam / siteLOneDist b.source b'.source) ^ α
          ≤ (lam / siteLOneDist b.source b'.source) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le ht1 hα₁.le
      _ = lam / siteLOneDist b.source b'.source := Real.rpow_one _
      _ ≤ 𝒮.L := ht2
  have hn : ‖h b' - h b‖ ≤ 2 * H := by
    rw [Real.norm_eq_abs]
    have := abs_sub (h b') (h b)
    linarith [hb b, hb b']
  calc (lam / siteLOneDist b.source b'.source) ^ α * ‖h b' - h b‖ ≤ (𝒮.L : ℝ) * (2 * H) :=
        mul_le_mul hr hn (norm_nonneg _) (by positivity)
    _ = 2 * (𝒮.L : ℝ) * H := by ring
end Setting
section Setting
attribute [local instance] fineSiteFintype fineBondFintype
variable {𝒮 : NestedRegions}
section Ball
variable {u : 𝒮.FineBond → ℝ} {Y : ℝ} {o : 𝒮.Point}
theorem tensorModulusAt_le {r : ℕ} {J : 𝒮.Tensor r} {x : 𝒮.FineBond} {H : ℝ} (hH : 0 ≤ H)
    (h : ∀ ν, |J ν x| ≤ H) : tensorModulusAt J x ≤ H :=
  Real.iSup_le h hH
variable {lam : ℝ} {ζ : 𝒮.FineSite → ℝ}
variable {α : ℝ}
end Ball
section Cube
variable {M : ℕ} (Q : LevelCube 𝒮 M) {o o' : 𝒮.Point} {lam₁ lam₂ : ℝ}
def decayFactor (o o' : 𝒮.Point) : ℝ := Real.exp (-(1 / 514) * (𝒮.ξ⁻¹ * lOneNorm (o - o')))
theorem decayFactor_pos (o o' : 𝒮.Point) : 0 < decayFactor o o' := Real.exp_pos _
end Cube
end Setting
section Setting
attribute [local instance] fineSiteFintype fineBondFintype
variable {𝒮 : NestedRegions}
end Setting
end YangMills.Construction.SecondTypeGreenRegularity
