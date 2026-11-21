import YangMills.Construction.DirichletOperator.LeibnizRulesAndHolderSeminormsProof
import YangMills.Construction.DirichletOperator.TransferOfSeminormsToThePropagatorProof
import YangMills.Construction.DirichletOperator.TransferProductsOfTheRemainderProof
import Mathlib
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Set Filter Topology
noncomputable section
namespace YangMills.Construction
open Dirichlet Torus RegionSequence RegionSequence.NestedRegions Weighted
namespace BlockCalculus
theorem le_mul_of_coordinate_bounds {V κ : Type} [AddCommGroup V] [Module ℝ V] [Fintype κ]
    (c : κ → V → ℝ) (b : κ → V) (K : κ → ℝ) (n : V → ℝ)
    (hsum : ∀ f, f = ∑ i, c i f • b i) (hK : ∀ i f, |c i f| ≤ K i * n f)
    (g : V → ℝ) (hadd : ∀ f h, g (f + h) ≤ g f + g h) (hsmul : ∀ (t : ℝ) f, g (t • f) = |t| * g f) :
    ∃ C, ∀ f, g f ≤ C * n f := by
  have hzero : g 0 = 0 := by simpa using hsmul 0 0
  have hnn : ∀ f, 0 ≤ g f := by
    intro f
    have h₁ := hadd f ((-1 : ℝ) • f)
    have h₂ := hsmul (-1) f
    simp only [abs_neg, abs_one, one_mul] at h₂
    rw [h₂] at h₁
    have h₃ : f + (-1 : ℝ) • f = 0 := by simp
    rw [h₃, hzero] at h₁
    linarith
  have hsumle : ∀ (s : Finset κ) (u : κ → V), g (∑ i ∈ s, u i) ≤ ∑ i ∈ s, g (u i) := by
    classical
    intro s u
    induction s using Finset.induction_on with
    | empty => simp [hzero]
    | insert i s hi ih =>
      rw [Finset.sum_insert hi, Finset.sum_insert hi]
      exact (hadd _ _).trans (by linarith)
  refine ⟨∑ i, K i * g (b i), fun f => ?_⟩
  calc g f = g (∑ i, c i f • b i) := by rw [← hsum f]
    _ ≤ ∑ i, g (c i f • b i) := hsumle _ _
    _ = ∑ i, |c i f| * g (b i) := by simp only [hsmul]
    _ ≤ ∑ i, K i * n f * g (b i) :=
        Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right (hK i f) (hnn _)
    _ = (∑ i, K i * g (b i)) * n f := by
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl fun i _ => by ring
variable {𝒮 : NestedRegions}
section Regular
variable [Fintype ↥𝒮.allCentres]
structure RegularCutSpace (X : CutSpace 𝒮) : Prop where
  finite : FiniteDimensional ℝ X.space
  nonneg : ∀ (p : NormExponent) (f : X.Carrier), 0 ≤ X.pNorm p f
  add_le : ∀ (p : NormExponent) (f g : X.Carrier), X.pNorm p (f + g) ≤ X.pNorm p f + X.pNorm p g
  smul : ∀ (p : NormExponent) (t : ℝ) (f : X.Carrier), X.pNorm p (t • f) = |t| * X.pNorm p f
  eq_zero : ∀ (p : NormExponent) (f : X.Carrier), X.pNorm p f = 0 → f = 0
  cut_add : ∀ (y : 𝒮.allCentres) (f g : X.Carrier), X.cut y (f + g) = X.cut y f + X.cut y g
  cut_smul : ∀ (y : 𝒮.allCentres) (t : ℝ) (f : X.Carrier), X.cut y (t • f) = t • X.cut y f
  cut_mem : ∀ (y : 𝒮.allCentres) (f : X.Carrier), f ∈ X.space → X.cut y f ∈ X.space
  cut_cut : ∀ (y : 𝒮.allCentres) (f : X.Carrier), X.cut y (X.cut y f) = X.cut y f
  cut_other : ∀ y y' : 𝒮.allCentres, y ≠ y' → ∀ f ∈ X.space, X.cut y (X.cut y' f) = 0
  sum_cut : ∀ f ∈ X.space, ∑ y : ↥𝒮.allCentres, X.cut y f = f
  nonzero : ∃ f ∈ X.space, f ≠ 0
  bound : ∀ (p : NormExponent) (g : X.space → ℝ), (∀ f h, g (f + h) ≤ g f + g h) →
    (∀ (t : ℝ) f, g (t • f) = |t| * g f) → ∃ C, ∀ f : X.space, g f ≤ C * X.pNorm p f
namespace RegularCutSpace
variable {X X' X'' : CutSpace 𝒮}
end RegularCutSpace
end Regular
section FiniteNorms
variable {ι : Type} [Fintype ι]
theorem indicator_smul_fun {ι : Type} (C : Set ι) (t : ℝ) (f : ι → ℝ) :
    C.indicator (t • f) = t • C.indicator f := by
  funext i
  by_cases h : i ∈ C <;> simp [h]
def sqrtWeightedSum (w f : ι → ℝ) : ℝ := √(∑ i, w i * f i ^ 2)
theorem weightedSqSum_nonneg (w f : ι → ℝ) (hw : ∀ i, 0 ≤ w i) : 0 ≤ ∑ i, w i * f i ^ 2 :=
  Finset.sum_nonneg fun i _ => mul_nonneg (hw i) (sq_nonneg _)
theorem weightedSum_mul_le (w u v : ι → ℝ) (hw : ∀ i, 0 ≤ w i) :
    ∑ i, w i * (u i * v i) ≤ sqrtWeightedSum w u * sqrtWeightedSum w v := by
  have h := Real.sum_mul_le_sqrt_mul_sqrt Finset.univ (fun i => √(w i) * u i)
    (fun i => √(w i) * v i)
  have h₁ : ∀ i, √(w i) * u i * (√(w i) * v i) = w i * (u i * v i) := by
    intro i
    have := Real.mul_self_sqrt (hw i)
    calc √(w i) * u i * (√(w i) * v i) = (√(w i) * √(w i)) * (u i * v i) := by ring
      _ = _ := by rw [this]
  have h₂ : ∀ (g : ι → ℝ) i, (√(w i) * g i) ^ 2 = w i * g i ^ 2 := by
    intro g i
    rw [mul_pow, Real.sq_sqrt (hw i)]
  simp only [h₁, h₂] at h
  exact h
theorem sqrtWeightedSum_add_le (w u v : ι → ℝ) (hw : ∀ i, 0 ≤ w i) :
    sqrtWeightedSum w (u + v) ≤ sqrtWeightedSum w u + sqrtWeightedSum w v := by
  have hu := weightedSqSum_nonneg w u hw
  have hv := weightedSqSum_nonneg w v hw
  have hc := weightedSum_mul_le w u v hw
  have hsu : sqrtWeightedSum w u ^ 2 = ∑ i, w i * u i ^ 2 := Real.sq_sqrt hu
  have hsv : sqrtWeightedSum w v ^ 2 = ∑ i, w i * v i ^ 2 := Real.sq_sqrt hv
  refine Real.sqrt_le_iff.2 ⟨add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _), ?_⟩
  have hexp : ∑ i, w i * (u + v) i ^ 2 =
      ∑ i, w i * u i ^ 2 + 2 * ∑ i, w i * (u i * v i) + ∑ i, w i * v i ^ 2 := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by simp only [Pi.add_apply]; ring
  rw [hexp]
  nlinarith
theorem sqrtWeightedSum_smul (w f : ι → ℝ) (hw : ∀ i, 0 ≤ w i) (t : ℝ) :
    sqrtWeightedSum w (t • f) = |t| * sqrtWeightedSum w f := by
  have h : ∑ i, w i * (t • f) i ^ 2 = t ^ 2 * ∑ i, w i * f i ^ 2 := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by simp only [Pi.smul_apply, smul_eq_mul]; ring
  simp only [sqrtWeightedSum]
  rw [h, Real.sqrt_mul (sq_nonneg t), Real.sqrt_sq_eq_abs]
theorem abs_le_sqrtWeightedSum (w f : ι → ℝ) (hw : ∀ i, 0 < w i) (i : ι) :
    |f i| ≤ (√(w i))⁻¹ * sqrtWeightedSum w f := by
  have hs : 0 < √(w i) := Real.sqrt_pos.2 (hw i)
  rw [inv_mul_eq_div, le_div_iff₀ hs]
  have h₁ : w i * f i ^ 2 ≤ ∑ j, w j * f j ^ 2 :=
    Finset.single_le_sum (f := fun j => w j * f j ^ 2)
      (fun j _ => mul_nonneg (hw j).le (sq_nonneg _)) (Finset.mem_univ i)
  have h₂ : |f i| * √(w i) = √(w i * f i ^ 2) := by
    rw [Real.sqrt_mul (hw i).le, Real.sqrt_sq_eq_abs, mul_comm]
  rw [h₂]
  exact Real.sqrt_le_sqrt h₁
theorem eq_zero_of_sqrtWeightedSum_eq_zero (w f : ι → ℝ) (hw : ∀ i, 0 < w i)
    (h : sqrtWeightedSum w f = 0) : f = 0 := by
  funext i
  have := abs_le_sqrtWeightedSum w f hw i
  rw [h, mul_zero] at this
  simpa using abs_nonpos_iff.1 this
end FiniteNorms
structure CoordSystem (X : CutSpace 𝒮) (ι : Type) [Fintype ι] where
  e : X.Carrier ≃ₗ[ℝ] (ι → ℝ)
  D : Set ι
  w : ι → ℝ
  C : 𝒮.allCentres → Set ι
  w_pos : ∀ i, 0 < w i
  mem_space : ∀ f, f ∈ X.space ↔ ∀ i, i ∉ D → e f i = 0
  cut_eq : ∀ y f, e (X.cut y f) = (C y).indicator (e f)
  two_eq : ∀ f, X.twoNorm f = sqrtWeightedSum w (e f)
  infty_ge : ∀ f i, |e f i| ≤ X.supNorm f
  infty_le : ∀ f c, 0 ≤ c → (∀ i, |e f i| ≤ c) → X.supNorm f ≤ c
  cover : ∀ i ∈ D, ∃ y, i ∈ C y ∧ ∀ y', i ∈ C y' → y' = y
  nonempty : D.Nonempty
namespace CoordSystem
variable {X : CutSpace 𝒮} {ι : Type} [Fintype ι] (R : CoordSystem X ι)
include R
theorem w_nonneg (i : ι) : 0 ≤ R.w i := (R.w_pos i).le
theorem supNorm_nonneg (f : X.Carrier) : 0 ≤ X.supNorm f := by
  obtain ⟨i, -⟩ := R.nonempty
  exact (abs_nonneg _).trans (R.infty_ge f i)
theorem supNorm_smul_le (t : ℝ) (f : X.Carrier) :
    X.supNorm (t • f) ≤ |t| * X.supNorm f := by
  refine R.infty_le _ _ (mul_nonneg (abs_nonneg _) (R.supNorm_nonneg f)) fun i => ?_
  rw [map_smul, Pi.smul_apply, smul_eq_mul, abs_mul]
  exact mul_le_mul_of_nonneg_left (R.infty_ge f i) (abs_nonneg _)
theorem supNorm_smul (t : ℝ) (f : X.Carrier) :
    X.supNorm (t • f) = |t| * X.supNorm f := by
  by_cases ht : t = 0
  · subst ht
    refine le_antisymm ?_ ?_
    · simpa using R.supNorm_smul_le 0 f
    · simpa using R.supNorm_nonneg ((0 : ℝ) • f)
  · refine le_antisymm (R.supNorm_smul_le t f) ?_
    have h := R.supNorm_smul_le t⁻¹ (t • f)
    rw [smul_smul, inv_mul_cancel₀ ht, one_smul, abs_inv] at h
    have hpos : 0 < |t| := abs_pos.2 ht
    calc |t| * X.supNorm f ≤ |t| * (|t|⁻¹ * X.supNorm (t • f)) :=
          mul_le_mul_of_nonneg_left h hpos.le
      _ = _ := by rw [← mul_assoc, mul_inv_cancel₀ hpos.ne', one_mul]
theorem pNorm_nonneg (p : NormExponent) (f : X.Carrier) : 0 ≤ X.pNorm p f := by
  cases p
  · change 0 ≤ X.twoNorm f
    rw [R.two_eq]
    exact Real.sqrt_nonneg _
  · exact R.supNorm_nonneg f
theorem abs_coord_le (p : NormExponent) :
    ∃ K : ι → ℝ, ∀ i f, |R.e f i| ≤ K i * X.pNorm p f := by
  cases p
  · refine ⟨fun i => (√(R.w i))⁻¹, fun i f => ?_⟩
    change _ ≤ _ * X.twoNorm f
    rw [R.two_eq]
    exact abs_le_sqrtWeightedSum _ _ R.w_pos i
  · refine ⟨fun _ => 1, fun i f => ?_⟩
    rw [one_mul]
    exact R.infty_ge f i
open Classical in
def basisVec (i : ι) : X.space :=
  if h : i ∈ R.D then
    ⟨R.e.symm (Pi.single i 1), (R.mem_space _).2 fun j hj => by
      have hji : j ≠ i := fun hji => hj (hji ▸ h)
      simp [Pi.single_eq_of_ne hji]⟩
  else 0
open Classical in
theorem e_basisVec_of_mem {i : ι} (h : i ∈ R.D) : R.e (R.basisVec i : X.Carrier) = Pi.single i 1 := by
  simp [basisVec, h]
theorem e_basisVec_of_not_mem {i : ι} (h : i ∉ R.D) : R.e (R.basisVec i : X.Carrier) = 0 := by
  simp [basisVec, h]
theorem eq_sum_basisVec (f : X.space) : f = ∑ i, R.e f i • R.basisVec i := by
  classical
  apply Subtype.ext
  apply R.e.injective
  funext j
  rw [Submodule.coe_sum, map_sum, Finset.sum_apply]
  have key : ∀ i, R.e ((R.e f i • R.basisVec i : X.space) : X.Carrier) j =
      if i = j then R.e f j else 0 := by
    intro i
    rw [Submodule.coe_smul, map_smul, Pi.smul_apply, smul_eq_mul]
    by_cases hi : i ∈ R.D
    · rw [R.e_basisVec_of_mem hi]
      by_cases hij : i = j
      · subst hij
        simp
      · simp [hij]
    · rw [R.e_basisVec_of_not_mem hi, (R.mem_space _).1 f.2 i hi]
      by_cases hij : i = j
      · subst hij
        simp [(R.mem_space _).1 f.2 i hi]
      · simp [hij]
  simp only [key]
  simp
theorem regular [Fintype ↥𝒮.allCentres] : RegularCutSpace X where
  finite := by
    have hinj : Function.Injective (R.e.toLinearMap ∘ₗ X.space.subtype) :=
      R.e.injective.comp Subtype.val_injective
    exact FiniteDimensional.of_injective _ hinj
  nonneg := R.pNorm_nonneg
  add_le := by
    intro p f g
    cases p
    · change X.twoNorm _ ≤ X.twoNorm _ + X.twoNorm _
      simp only [R.two_eq, map_add]
      exact sqrtWeightedSum_add_le _ _ _ R.w_nonneg
    · change X.supNorm _ ≤ X.supNorm _ + X.supNorm _
      refine R.infty_le _ _ (add_nonneg (R.supNorm_nonneg f) (R.supNorm_nonneg g)) fun i => ?_
      rw [map_add, Pi.add_apply]
      exact (abs_add_le _ _).trans (add_le_add (R.infty_ge f i) (R.infty_ge g i))
  smul := by
    intro p t f
    cases p
    · change X.twoNorm _ = _ * X.twoNorm _
      simp only [R.two_eq, map_smul]
      exact sqrtWeightedSum_smul _ _ R.w_nonneg t
    · exact R.supNorm_smul t f
  eq_zero := by
    intro p f h
    apply R.e.injective
    rw [map_zero]
    cases p
    · change X.twoNorm f = 0 at h
      rw [R.two_eq] at h
      exact eq_zero_of_sqrtWeightedSum_eq_zero _ _ R.w_pos h
    · change X.supNorm f = 0 at h
      funext i
      have := R.infty_ge f i
      rw [h] at this
      simpa using abs_nonpos_iff.1 this
  cut_add := by
    intro y f g
    apply R.e.injective
    simp only [R.cut_eq, map_add, indicator_add']
  cut_smul := by
    intro y t f
    apply R.e.injective
    simp only [R.cut_eq, map_smul, indicator_smul_fun]
  cut_mem := by
    intro y f hf
    refine (R.mem_space _).2 fun i hi => ?_
    rw [R.cut_eq]
    by_cases hy : i ∈ R.C y
    · rw [indicator_of_mem hy]
      exact (R.mem_space _).1 hf i hi
    · exact indicator_of_notMem hy _
  cut_cut := by
    intro y f
    apply R.e.injective
    simp only [R.cut_eq, indicator_indicator, inter_self]
  cut_other := by
    intro y y' hne f hf
    apply R.e.injective
    rw [map_zero]
    funext i
    simp only [R.cut_eq]
    by_cases hy : i ∈ R.C y
    · rw [indicator_of_mem hy]
      by_cases hy' : i ∈ R.C y'
      · rw [indicator_of_mem hy']
        by_cases hD : i ∈ R.D
        · obtain ⟨z, -, hz⟩ := R.cover i hD
          exact absurd ((hz y hy).trans (hz y' hy').symm) hne
        · simpa using (R.mem_space _).1 hf i hD
      · simp [indicator_of_notMem hy']
    · simp [indicator_of_notMem hy]
  sum_cut := by
    intro f hf
    apply R.e.injective
    funext i
    rw [map_sum, Finset.sum_apply]
    simp only [R.cut_eq]
    by_cases hD : i ∈ R.D
    · obtain ⟨z, hzi, hz⟩ := R.cover i hD
      rw [Finset.sum_eq_single z]
      · exact indicator_of_mem hzi _
      · intro y _ hy
        exact indicator_of_notMem (fun hi => hy (hz y hi)) _
      · simp
    · have h0 := (R.mem_space _).1 hf i hD
      rw [h0]
      refine Finset.sum_eq_zero fun y _ => ?_
      by_cases hy : i ∈ R.C y
      · rw [indicator_of_mem hy, h0]
      · exact indicator_of_notMem hy _
  nonzero := by
    obtain ⟨i, hi⟩ := R.nonempty
    refine ⟨R.basisVec i, (R.basisVec i).2, fun h0 => ?_⟩
    have h₁ := R.e_basisVec_of_mem hi
    rw [h0, map_zero] at h₁
    have := congrFun h₁ i
    simp at this
  bound := by
    intro p g hadd hsmul
    obtain ⟨K, hK⟩ := R.abs_coord_le p
    exact le_mul_of_coordinate_bounds (fun i (f : X.space) => R.e f i) R.basisVec K
      (fun f => X.pNorm p f) R.eq_sum_basisVec (fun i f => hK i f) g hadd hsmul
end CoordSystem
theorem finite_fineSite (𝒯 : NestedRegions) : Finite 𝒯.FineSite := by apply _root_.YangMills.Construction.RegionSequence.AvgOpWeightSum.finite_fineSite <;> assumption
theorem finite_fineBond (𝒯 : NestedRegions) : Finite 𝒯.FineBond := by apply _root_.YangMills.Construction.RegionSequence.AvgOpWeightSum.finite_fineBond <;> assumption
theorem levelScale_pos (𝒯 : NestedRegions) (y : 𝒯.Point) : 0 < 𝒯.levelScale y := by apply _root_.YangMills.Construction.RegionSequence.OperatorEstimates.levelScale_pos <;> assumption
structure CellPartition (𝒮 : NestedRegions) : Prop where
  site : ∀ x : 𝒮.FineSite, (x : 𝒮.Point) ∈ 𝒮.Ω 0 → ∃ y : 𝒮.allCentres,
    (x : 𝒮.Point) ∈ 𝒮.cellOf y ∧ ∀ y' : 𝒮.allCentres, (x : 𝒮.Point) ∈ 𝒮.cellOf y' → y' = y
  base : ∀ b ∈ 𝒮.bonds, (𝒮.anchor b : 𝒮.Point) ∈ 𝒮.Ω 0
  bond : 𝒮.bonds.Nonempty
theorem scaledInner_eq_sum {ι : Type} [Fintype ι] (ξ : ℝ) (f g : ι → ℝ) :
    scaledInner ξ f g = ξ ^ 4 * ∑ i, f i * g i := by
  simp only [scaledInner, finsum_eq_sum_of_fintype]
section StandardEvaluations
variable (hc : CellPartition 𝒮)
include hc
end StandardEvaluations
section Kernels
variable {ι ι' : Type} [Fintype ι] [Fintype ι'] {D : Set ι} {D' : Set ι'} {ξ : ℝ}
open Classical in
def basisOn (D : Set ι) (i : ι) : supportedOn D :=
  if h : i ∈ D then
    ⟨Pi.single i 1, fun j hj => Pi.single_eq_of_ne (fun hji : j = i => hj (by rw [hji]; exact h)) _⟩
  else 0
open Classical in
theorem coe_basisOn_of_mem {i : ι} (h : i ∈ D) : (basisOn D i : ι → ℝ) = Pi.single i 1 := by
  simp [basisOn, h]
theorem basisOn_of_not_mem {i : ι} (h : i ∉ D) : basisOn D i = 0 := by
  simp [basisOn, h]
theorem eq_sum_basisOn (f : supportedOn D) : f = ∑ i, (f : ι → ℝ) i • basisOn D i := by
  classical
  apply Subtype.ext
  funext j
  rw [Submodule.coe_sum, Finset.sum_apply]
  have key : ∀ i, ((((f : ι → ℝ) i • basisOn D i : supportedOn D)) : ι → ℝ) j =
      if i = j then (f : ι → ℝ) j else 0 := by
    intro i
    rw [Submodule.coe_smul, Pi.smul_apply, smul_eq_mul]
    by_cases hi : i ∈ D
    · rw [coe_basisOn_of_mem hi]
      by_cases hij : i = j
      · subst hij
        simp
      · simp [hij]
    · rw [f.2 i hi]
      by_cases hij : i = j
      · subst hij
        simp [f.2 i hi]
      · simp [hij]
  simp only [key]
  simp
def matrixEntry (O : supportedOn D' →ₗ[ℝ] supportedOn D) (x : ι) (x' : ι') : ℝ :=
  (O (basisOn D' x') : ι → ℝ) x
theorem apply_eq_sum_matrixEntry (O : supportedOn D' →ₗ[ℝ] supportedOn D) (f : supportedOn D') (x : ι) :
    (O f : ι → ℝ) x = ∑ x', matrixEntry O x x' * (f : ι' → ℝ) x' := by
  conv_lhs => rw [eq_sum_basisOn f]
  rw [map_sum, Submodule.coe_sum, Finset.sum_apply]
  refine Finset.sum_congr rfl fun x' _ => ?_
  rw [map_smul, Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, mul_comm]
  rfl
theorem matrixEntry_adjoint (hξ : 0 < ξ) (O' : supportedOn D →ₗ[ℝ] supportedOn D')
    (O : supportedOn D' →ₗ[ℝ] supportedOn D) (h : IsScaledAdjoint ξ O' O) (x : ι) (x' : ι') :
    matrixEntry O x x' = matrixEntry O' x' x := by
  classical
  by_cases hx : x ∈ D
  · by_cases hx' : x' ∈ D'
    · have h₁ := h (basisOn D' x') (basisOn D x)
      rw [scaledInner_eq_sum, scaledInner_eq_sum, coe_basisOn_of_mem hx, coe_basisOn_of_mem hx'] at h₁
      have hne : ξ ^ 4 ≠ 0 := (pow_pos hξ 4).ne'
      have h₂ := mul_left_cancel₀ hne h₁
      simpa [Pi.single_apply, matrixEntry, coe_basisOn_of_mem hx, coe_basisOn_of_mem hx'] using h₂
    · have h₁ : matrixEntry O x x' = 0 := by simp [matrixEntry, basisOn_of_not_mem hx']
      have h₂ : matrixEntry O' x' x = 0 := (O' (basisOn D x)).2 x' hx'
      rw [h₁, h₂]
  · have h₁ : matrixEntry O x x' = 0 := (O (basisOn D' x')).2 x hx
    have h₂ : matrixEntry O' x' x = 0 := by simp [matrixEntry, basisOn_of_not_mem hx]
    rw [h₁, h₂]
end Kernels
section Transport
variable {X X' : CutSpace 𝒮} {ι ι' : Type} [Fintype ι] [Fintype ι']
end Transport
section Rules
open RegionSequence.OperatorEstimates RegularCutSpace
variable [Fintype ↥𝒮.allCentres] {M R₁ : ℕ} {X X' X'' : CutSpace 𝒮}
end Rules
end BlockCalculus
end YangMills.Construction
