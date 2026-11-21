import YangMills.Construction.JointSpectrum.FamilyPolynomialCalculus
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.FamilyPolynomials
open YangMills.Construction.JointSpectrum Set
open scoped ComplexConjugate ComplexOrder
private abbrev MonomialAlgebra (J : Type) : Type := AddMonoidAlgebra ℂ (ℕ × (J → ℤ))
section Functions
variable {J : Type} [Fintype J]
private def monomialChar (i : ℕ × (J → ℤ)) : SpectralDomain J →* ℂ where
  toFun := spectralMonomial i.1 i.2
  map_one' := by simp [spectralMonomial, torusMonomial]
  map_mul' p p' := by
    simp only [spectralMonomial, torusMonomial, Prod.fst_mul, Prod.snd_mul, Pi.mul_apply,
      Circle.coe_mul, Set.Icc.coe_mul, Complex.ofReal_mul, mul_pow, mul_zpow,
      Finset.prod_mul_distrib]
    ring
private def monomialMonoidHom : Multiplicative (ℕ × (J → ℤ)) →* (SpectralDomain J → ℂ) where
  toFun i := spectralMonomial i.toAdd.1 i.toAdd.2
  map_one' := by funext p; simp [spectralMonomial, torusMonomial]
  map_mul' i i' := by
    funext p
    have h : ∀ α, ((p.2 α : Circle) : ℂ) ≠ 0 := fun α => Circle.coe_ne_zero _
    simp only [spectralMonomial, torusMonomial, toAdd_mul, Prod.fst_add, Prod.snd_add,
      Pi.add_apply, Pi.mul_apply, zpow_add₀ (h _), Finset.prod_mul_distrib, pow_add]
    ring
private lemma torusMonomial_update [DecidableEq J] (α : J) (w : Circle) (y : J → ℤ) :
    torusMonomial (Function.update (1 : J → Circle) α w) y = (w : ℂ) ^ y α := by
  unfold torusMonomial
  rw [Finset.prod_eq_single α]
  · simp
  · intro β _ hβ
    simp [Function.update_of_ne hβ]
  · simp
private lemma eq_of_circle_zpow_eq (k l : ℤ) (h : ∀ w : Circle, (w : ℂ) ^ k = (w : ℂ) ^ l) :
    k = l := by
  by_contra hkl
  have hm : ((k - l : ℤ) : ℂ) ≠ 0 := by exact_mod_cast sub_ne_zero.mpr hkl
  have hw := h (Circle.exp (Real.pi / ((k - l : ℤ) : ℝ)))
  have hne : ((Circle.exp (Real.pi / ((k - l : ℤ) : ℝ)) : Circle) : ℂ) ≠ 0 :=
    Circle.coe_ne_zero _
  have h1 : ((Circle.exp (Real.pi / ((k - l : ℤ) : ℝ)) : Circle) : ℂ) ^ (k - l) = 1 := by
    rw [zpow_sub₀ hne, hw, div_self (zpow_ne_zero _ hne)]
  rw [Circle.coe_exp, ← Complex.exp_int_mul] at h1
  have h2 : (((k - l : ℤ) : ℂ) * (((Real.pi / ((k - l : ℤ) : ℝ) : ℝ) : ℂ) * Complex.I)) =
      Real.pi * Complex.I := by
    push_cast at hm ⊢
    field_simp
  rw [h2, Complex.exp_pi_mul_I] at h1
  norm_num at h1
private lemma monomialChar_injective : Function.Injective (monomialChar (J := J)) := by
  classical
  rintro ⟨n, y⟩ ⟨n', y'⟩ h
  have hn : n = n' := by
    have h1 := DFunLike.congr_fun h ((⟨1 / 2, by norm_num, by norm_num⟩ : unitInterval), 1)
    have h2 := congrArg norm h1
    simp [monomialChar, spectralMonomial, torusMonomial] at h2
    exact h2
  have hy : y = y' := by
    funext α
    refine eq_of_circle_zpow_eq _ _ fun w => ?_
    have h1 := DFunLike.congr_fun h ((1 : unitInterval), Function.update (1 : J → Circle) α w)
    simpa [monomialChar, spectralMonomial, torusMonomial_update] using h1
  exact Prod.ext hn hy
private lemma linearIndependent_spectralMonomial :
    LinearIndependent ℂ fun i : ℕ × (J → ℤ) =>
      (spectralMonomial i.1 i.2 : SpectralDomain J → ℂ) :=
  by
    have h := (linearIndependent_monoidHom (SpectralDomain J) ℂ).comp
      (monomialChar (J := J)) monomialChar_injective
    exact h
private def evalFunction : MonomialAlgebra J →ₐ[ℂ] (SpectralDomain J → ℂ) :=
  AddMonoidAlgebra.lift ℂ (SpectralDomain J → ℂ) (ℕ × (J → ℤ)) monomialMonoidHom
private lemma evalFunction_single (i : ℕ × (J → ℤ)) (a : ℂ) :
    evalFunction (AddMonoidAlgebra.single i a : MonomialAlgebra J) =
      a • spectralMonomial i.1 i.2 := by
  simp only [evalFunction, AddMonoidAlgebra.lift_single]
  rfl
private lemma evalFunction_eq_spectralSum (f : MonomialAlgebra J) :
    evalFunction f = spectralSum f.coeff.support f.coeff := by
  funext p
  simp [evalFunction, AddMonoidAlgebra.lift_apply, Finsupp.sum, spectralSum, monomialMonoidHom]
private lemma evalFunction_injective : Function.Injective (evalFunction (J := J)) := by
  intro f g h
  apply AddMonoidAlgebra.coeff_injective
  apply linearIndependent_spectralMonomial (J := J)
  simpa [evalFunction, AddMonoidAlgebra.lift_apply, Finsupp.linearCombination_apply,
    monomialMonoidHom] using h
private def ofFinset (s : Finset (ℕ × (J → ℤ))) (c : ℕ × (J → ℤ) → ℂ) : MonomialAlgebra J :=
  ∑ i ∈ s, AddMonoidAlgebra.single i (c i)
private lemma evalFunction_ofFinset (s : Finset (ℕ × (J → ℤ))) (c : ℕ × (J → ℤ) → ℂ) :
    evalFunction (ofFinset s c) = spectralSum s c := by
  funext p
  simp [ofFinset, map_sum, evalFunction_single, spectralSum, Finset.sum_apply]
private lemma coeff_ofFinset (s : Finset (ℕ × (J → ℤ))) (c : ℕ × (J → ℤ) → ℂ)
    (i : ℕ × (J → ℤ)) : (ofFinset s c).coeff i = (s : Set (ℕ × (J → ℤ))).indicator c i := by
  classical
  simp [ofFinset, AddMonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply,
    AddMonoidAlgebra.coeff_single, Finsupp.single_apply, Set.indicator_apply]
private lemma mem_spectralPolynomials_iff {q : SpectralDomain J → ℂ} :
    q ∈ spectralPolynomials J ↔ ∃ f : MonomialAlgebra J, evalFunction f = q := by
  constructor
  · rintro ⟨s, c, h⟩
    refine ⟨ofFinset s c, ?_⟩
    rw [evalFunction_ofFinset]
    funext p
    simp [h, spectralSum]
  · rintro ⟨f, rfl⟩
    refine ⟨f.coeff.support, f.coeff, fun p => ?_⟩
    rw [evalFunction_eq_spectralSum]
    rfl
private lemma continuous_evalFunction (f : MonomialAlgebra J) : Continuous (evalFunction f) := by
  rw [evalFunction_eq_spectralSum]
  unfold spectralSum
  refine continuous_finsetSum _ fun i _ => continuous_const.mul ?_
  unfold spectralMonomial torusMonomial
  refine Continuous.mul (by fun_prop) (continuous_finsetProd _ fun α _ => ?_)
  exact Continuous.zpow₀ (by fun_prop) _ fun p => Or.inl (Circle.coe_ne_zero _)
end Functions
section Commutative
variable {𝔄 : Type*} [CommCStarAlgebra 𝔄] {J : Type} [Fintype J]
private def unitaryProd (b : J → unitary 𝔄) (y : J → ℤ) : unitary 𝔄 := ∏ α, b α ^ y α
private lemma unitaryProd_add (b : J → unitary 𝔄) (y y' : J → ℤ) :
    unitaryProd b (y + y') = unitaryProd b y * unitaryProd b y' := by
  simp only [unitaryProd, Pi.add_apply, zpow_add, Finset.prod_mul_distrib]
private lemma unitaryProd_neg (b : J → unitary 𝔄) (y : J → ℤ) :
    unitaryProd b (-y) = (unitaryProd b y)⁻¹ := by
  simp only [unitaryProd, Pi.neg_apply, zpow_neg, Finset.prod_inv_distrib]
private def evalMonoidHom (a : 𝔄) (b : J → unitary 𝔄) :
    Multiplicative (ℕ × (J → ℤ)) →* 𝔄 where
  toFun i := a ^ i.toAdd.1 * ((unitaryProd b i.toAdd.2 : unitary 𝔄) : 𝔄)
  map_one' := by simp [unitaryProd]
  map_mul' i i' := by
    simp only [toAdd_mul, Prod.fst_add, Prod.snd_add, pow_add, unitaryProd_add,
      Submonoid.coe_mul]
    ring
private def evalElement (a : 𝔄) (b : J → unitary 𝔄) : MonomialAlgebra J →ₐ[ℂ] 𝔄 :=
  AddMonoidAlgebra.lift ℂ 𝔄 (ℕ × (J → ℤ)) (evalMonoidHom a b)
private lemma evalElement_single (a : 𝔄) (b : J → unitary 𝔄) (i : ℕ × (J → ℤ)) (r : ℂ) :
    evalElement a b (AddMonoidAlgebra.single i r : MonomialAlgebra J) =
      r • (a ^ i.1 * ((unitaryProd b i.2 : unitary 𝔄) : 𝔄)) := by
  simp only [evalElement, AddMonoidAlgebra.lift_single]
  rfl
private lemma exists_conj (a : 𝔄) (ha : IsSelfAdjoint a) (b : J → unitary 𝔄)
    (f : MonomialAlgebra J) : ∃ g : MonomialAlgebra J,
      evalFunction g = (fun p => conj (evalFunction f p)) ∧
        evalElement a b g = star (evalElement a b f) := by
  induction f using AddMonoidAlgebra.induction_linear with
  | zero => exact ⟨0, by funext p; simp, by simp⟩
  | add f f' hf hf' =>
    obtain ⟨g, hg, hg'⟩ := hf
    obtain ⟨g', hk, hk'⟩ := hf'
    refine ⟨g + g', ?_, by simp [hg', hk']⟩
    funext p
    simp [hg, hk]
  | single i r =>
    refine ⟨AddMonoidAlgebra.single (i.1, -i.2) (conj r), ?_, ?_⟩
    · funext p
      simp only [evalFunction_single, Pi.smul_apply, smul_eq_mul, map_mul]
      congr 1
      simp only [spectralMonomial, torusMonomial, map_mul, map_pow, Complex.conj_ofReal,
        map_prod, map_zpow₀, ← Circle.coe_inv_eq_conj, Pi.neg_apply, zpow_neg, Circle.coe_inv,
        inv_zpow]
    · simp only [evalElement_single, star_smul, star_mul', star_pow, ha.star_eq,
        unitaryProd_neg]
      rfl
private lemma character_unitary_mem_unitSphere (φ : WeakDual.characterSpace ℂ 𝔄)
    (u : unitary 𝔄) : φ (u : 𝔄) ∈ Submonoid.unitSphere ℂ := by
  have h : ((u : 𝔄)) ∈ unitary 𝔄 := u.2
  have : Nontrivial 𝔄 := by
    by_contra hn
    rw [not_nontrivial_iff_subsingleton] at hn
    have h0 := map_one φ
    rw [Subsingleton.elim (1 : 𝔄) 0, map_zero] at h0
    exact zero_ne_one h0
  exact spectrum.subset_circle_of_unitary (𝕜 := ℂ) h (AlgHom.apply_mem_spectrum φ (u : 𝔄))
private def characterToCircle (φ : WeakDual.characterSpace ℂ 𝔄) : unitary 𝔄 →* Circle where
  toFun u := ⟨φ (u : 𝔄), character_unitary_mem_unitSphere φ u⟩
  map_one' := by
    apply Circle.ext
    simp
  map_mul' u v := by
    apply Circle.ext
    change φ ((u * v : unitary 𝔄) : 𝔄) = φ (u : 𝔄) * φ (v : 𝔄)
    rw [Submonoid.coe_mul, map_mul]
private lemma coe_characterToCircle (φ : WeakDual.characterSpace ℂ 𝔄) (u : unitary 𝔄) :
    ((characterToCircle φ u : Circle) : ℂ) = φ (u : 𝔄) := rfl
private lemma exists_point_of_character (a : 𝔄) (b : J → unitary 𝔄)
    (ha : ∀ z ∈ spectrum ℂ a, ∃ t : unitInterval, z = ((t : ℝ) : ℂ))
    (φ : WeakDual.characterSpace ℂ 𝔄) :
    ∃ p : SpectralDomain J, ∀ f : MonomialAlgebra J, φ (evalElement a b f) = evalFunction f p := by
  obtain ⟨t, ht⟩ := ha (φ a) (AlgHom.apply_mem_spectrum φ a)
  refine ⟨(t, fun α => characterToCircle φ (b α)), fun f => ?_⟩
  induction f using AddMonoidAlgebra.induction_linear with
  | zero => simp
  | add f f' hf hf' => simp [hf, hf']
  | single i r =>
    rw [evalElement_single, evalFunction_single]
    simp only [map_smul, map_mul, map_pow, ht, Pi.smul_apply, smul_eq_mul]
    congr 2
    rw [← coe_characterToCircle, unitaryProd, map_prod]
    simp only [torusMonomial, map_zpow]
    exact (map_prod Circle.coeHom _ _).trans
      (Finset.prod_congr rfl fun x _ => Circle.coe_zpow _ _)
private lemma spectrum_evalElement_subset (a : 𝔄) (b : J → unitary 𝔄)
    (ha : ∀ z ∈ spectrum ℂ a, ∃ t : unitInterval, z = ((t : ℝ) : ℂ)) (f : MonomialAlgebra J)
    {z : ℂ} (hz : z ∈ spectrum ℂ (evalElement a b f)) :
    ∃ p : SpectralDomain J, z = evalFunction f p := by
  rcases subsingleton_or_nontrivial 𝔄 with h | h
  · simp [spectrum.of_subsingleton] at hz
  · obtain ⟨φ, rfl⟩ := WeakDual.CharacterSpace.mem_spectrum_iff_exists.mp hz
    obtain ⟨p, hp⟩ := exists_point_of_character a b ha φ
    exact ⟨p, hp f⟩
private lemma norm_evalElement_le (a : 𝔄) (b : J → unitary 𝔄)
    (ha : ∀ z ∈ spectrum ℂ a, ∃ t : unitInterval, z = ((t : ℝ) : ℂ)) (f : MonomialAlgebra J)
    {c : ℝ} (hc : 0 ≤ c) (h : ∀ p, ‖evalFunction f p‖ ≤ c) : ‖evalElement a b f‖ ≤ c := by
  rw [← (gelfandTransform_isometry (A := 𝔄)).norm_map_of_map_zero (map_zero _)]
  rw [ContinuousMap.norm_le _ hc]
  intro φ
  obtain ⟨p, hp⟩ := exists_point_of_character a b ha φ
  have : (WeakDual.gelfandTransform ℂ 𝔄 (evalElement a b f)) φ = φ (evalElement a b f) := rfl
  rw [this, hp f]
  exact h p
end Commutative
section Operators
variable {𝒦 : Type} [NormedAddCommGroup 𝒦] [InnerProductSpace ℂ 𝒦] [CompleteSpace 𝒦]
  {J : Type} [Fintype J] [Nonempty J]
private lemma commute_unitary_inv {C : 𝒦 →L[ℂ] 𝒦} {u : unitary (𝒦 →L[ℂ] 𝒦)}
    (h : Commute C (u : 𝒦 →L[ℂ] 𝒦)) :
    Commute C ((u⁻¹ : unitary (𝒦 →L[ℂ] 𝒦)) : 𝒦 →L[ℂ] 𝒦) := by
  have h₁ : ((u⁻¹ : unitary (𝒦 →L[ℂ] 𝒦)) : 𝒦 →L[ℂ] 𝒦) * u = 1 := by
    rw [← Submonoid.coe_mul, inv_mul_cancel]
    rfl
  have h₂ : (u : 𝒦 →L[ℂ] 𝒦) * ((u⁻¹ : unitary (𝒦 →L[ℂ] 𝒦)) : 𝒦 →L[ℂ] 𝒦) = 1 := by
    rw [← Submonoid.coe_mul, mul_inv_cancel]
    rfl
  generalize ((u⁻¹ : unitary (𝒦 →L[ℂ] 𝒦)) : 𝒦 →L[ℂ] 𝒦) = v at h₁ h₂ ⊢
  change C * v = v * C
  calc C * v = (v * u) * (C * v) := by rw [h₁, one_mul]
    _ = v * (u * C) * v := by simp only [mul_assoc]
    _ = v * (C * u) * v := by rw [h.eq]
    _ = v * C * (u * v) := by simp only [mul_assoc]
    _ = v * C := by rw [h₂, mul_one]
private lemma generatorSet_commute (S : CommutingFamily 𝒦 J) :
    ∀ C ∈ generatorSet S, ∀ D ∈ generatorSet S, Commute C D := by
  have h₀ : ∀ C ∈ generatorSet S, Commute C S.A ∧ ∀ α, Commute C (S.B α : 𝒦 →L[ℂ] 𝒦) := by
    intro C hC
    simp only [generatorSet, mem_union, mem_singleton_iff, mem_range] at hC
    rcases hC with (rfl | ⟨α, rfl⟩) | ⟨α, rfl⟩
    · exact ⟨Commute.refl _, S.commute_A_B⟩
    · exact ⟨(S.commute_A_B α).symm, S.commute_B_B α⟩
    · exact ⟨(commute_unitary_inv (S.commute_A_B α)).symm,
        fun α' => (commute_unitary_inv (S.commute_B_B α' α)).symm⟩
  intro C hC D hD
  obtain ⟨hA, hB⟩ := h₀ C hC
  simp only [generatorSet, mem_union, mem_singleton_iff, mem_range] at hD
  rcases hD with (rfl | ⟨α, rfl⟩) | ⟨α, rfl⟩
  · exact hA
  · exact hB α
  · exact commute_unitary_inv (hB α)
private lemma star_mem_generatorSet (S : CommutingFamily 𝒦 J) {C : 𝒦 →L[ℂ] 𝒦}
    (hC : C ∈ generatorSet S) : star C ∈ generatorSet S := by
  simp only [generatorSet, mem_union, mem_singleton_iff, mem_range] at hC ⊢
  rcases hC with (rfl | ⟨α, rfl⟩) | ⟨α, rfl⟩
  · exact Or.inl (Or.inl S.isSelfAdjoint_A.star_eq)
  · exact Or.inr ⟨α, rfl⟩
  · refine Or.inl (Or.inr ⟨α, ?_⟩)
    change (S.B α : 𝒦 →L[ℂ] 𝒦) = star (star (S.B α : 𝒦 →L[ℂ] 𝒦))
    rw [star_star]
private def generatedAlgebra (S : CommutingFamily 𝒦 J) : StarSubalgebra ℂ (𝒦 →L[ℂ] 𝒦) :=
  (StarAlgebra.adjoin ℂ (generatorSet S)).topologicalClosure
private instance (S : CommutingFamily 𝒦 J) :
    IsClosed (generatedAlgebra S : Set (𝒦 →L[ℂ] 𝒦)) :=
  StarSubalgebra.isClosed_topologicalClosure _
private lemma adjoin_mul_comm (S : CommutingFamily 𝒦 J)
    (x y : StarAlgebra.adjoin ℂ (generatorSet S)) : x * y = y * x :=
  (StarAlgebra.isMulCommutative_adjoin ℂ (s := generatorSet S)
    (fun a ha b hb => (generatorSet_commute S a ha b hb).eq)
    (fun a ha _ hb => (generatorSet_commute S a ha _ (star_mem_generatorSet S hb)).eq)).is_comm.comm
      x y
private instance (S : CommutingFamily 𝒦 J) : CommCStarAlgebra (generatedAlgebra S) :=
  { StarSubalgebra.cstarAlgebra (generatedAlgebra S) with
    mul_comm := fun x y =>
      (StarSubalgebra.commRingTopologicalClosure _ (adjoin_mul_comm S)).mul_comm x y }
private lemma mem_generatedAlgebra (S : CommutingFamily 𝒦 J) {C : 𝒦 →L[ℂ] 𝒦}
    (hC : C ∈ generatorSet S) : C ∈ generatedAlgebra S :=
  StarSubalgebra.le_topologicalClosure _ (StarAlgebra.subset_adjoin ℂ _ hC)
private def algebraA (S : CommutingFamily 𝒦 J) : generatedAlgebra S :=
  ⟨S.A, mem_generatedAlgebra S (Or.inl (Or.inl rfl))⟩
private def algebraB (S : CommutingFamily 𝒦 J) (α : J) : unitary (generatedAlgebra S) :=
  ⟨⟨(S.B α : 𝒦 →L[ℂ] 𝒦), mem_generatedAlgebra S (Or.inl (Or.inr ⟨α, rfl⟩))⟩, by
    rw [Unitary.mem_iff]
    constructor <;> apply Subtype.ext
    · exact Unitary.coe_star_mul_self (S.B α)
    · exact Unitary.coe_mul_star_self (S.B α)⟩
private def unitaryToOperator (S : CommutingFamily 𝒦 J) :
    unitary (generatedAlgebra S) →* unitary (𝒦 →L[ℂ] 𝒦) where
  toFun u := ⟨((u : generatedAlgebra S) : 𝒦 →L[ℂ] 𝒦), by
    rw [Unitary.mem_iff]
    exact ⟨congrArg Subtype.val (Unitary.coe_star_mul_self u),
      congrArg Subtype.val (Unitary.coe_mul_star_self u)⟩⟩
  map_one' := rfl
  map_mul' _ _ := rfl
private lemma coe_unitaryProd (S : CommutingFamily 𝒦 J) (y : J → ℤ) :
    (((unitaryProd (algebraB S) y : unitary (generatedAlgebra S)) : generatedAlgebra S) :
      𝒦 →L[ℂ] 𝒦) = S.unitaryMonomial y := by
  have h : unitaryToOperator S (unitaryProd (algebraB S) y) =
      Finset.univ.noncommProd (fun α => S.B α ^ y α)
        (fun α _ α' _ _ => S.commute_zpow_unitary y α α') := by
    rw [unitaryProd, ← Finset.noncommProd_eq_prod]
    refine (Finset.map_noncommProd _ _ _ (unitaryToOperator S)).trans ?_
    refine Finset.noncommProd_congr rfl (fun α _ => ?_) _
    rw [map_zpow]
    rfl
  exact congrArg Subtype.val h
private def evalOperator (S : CommutingFamily 𝒦 J) (f : MonomialAlgebra J) : 𝒦 →L[ℂ] 𝒦 :=
  ((evalElement (algebraA S) (algebraB S) f : generatedAlgebra S) : 𝒦 →L[ℂ] 𝒦)
private lemma evalOperator_ofFinset (S : CommutingFamily 𝒦 J) (s : Finset (ℕ × (J → ℤ)))
    (c : ℕ × (J → ℤ) → ℂ) : evalOperator S (ofFinset s c) = familySum S s c := by
  unfold evalOperator ofFinset familySum
  rw [map_sum]
  refine (map_sum (generatedAlgebra S).subtype _ _).trans (Finset.sum_congr rfl fun i _ => ?_)
  rw [evalElement_single]
  change c i • (S.A ^ i.1 * _) = _
  rw [coe_unitaryProd]
  rfl
private lemma polynomialCalculus_evalFunction (S : CommutingFamily 𝒦 J) (f : MonomialAlgebra J) :
    polynomialCalculus S (evalFunction f) = evalOperator S f := by
  have hex : ∃ r : Finset (ℕ × (J → ℤ)) × (ℕ × (J → ℤ) → ℂ),
      evalFunction f = spectralSum r.1 r.2 := ⟨(_, _), evalFunction_eq_spectralSum f⟩
  have hr := Classical.epsilon_spec hex
  unfold polynomialCalculus
  simp only
  generalize Classical.epsilon (fun r : Finset (ℕ × (J → ℤ)) × (ℕ × (J → ℤ) → ℂ) =>
    evalFunction f = spectralSum r.1 r.2) = r at hr
  rw [← evalFunction_ofFinset] at hr
  rw [← evalOperator_ofFinset, ← evalFunction_injective hr]
private lemma spectrum_algebraA (S : CommutingFamily 𝒦 J) :
    ∀ z ∈ spectrum ℂ (algebraA S), ∃ t : unitInterval, z = ((t : ℝ) : ℂ) := by
  intro z hz
  have hz' : z ∈ spectrum ℂ S.A := (generatedAlgebra S).mem_spectrum_iff.mp hz
  have hre := S.isSelfAdjoint_A.mem_spectrum_eq_re hz'
  have hz₂ : z.re ∈ spectrum ℝ S.A := by
    obtain ⟨r, hr, rfl⟩ := S.isSelfAdjoint_A.spectrumRestricts.algebraMap_image.symm ▸ hz'
    simpa using hr
  have h₀ : 0 ≤ z.re := spectrum_nonneg_of_nonneg S.zero_le_A hz₂
  have h₁ : 0 ≤ 1 - z.re := by
    have h₃ : (1 : ℝ) - z.re ∈ spectrum ℝ (algebraMap ℝ (𝒦 →L[ℂ] 𝒦) 1 - S.A) := by
      rw [← spectrum.singleton_sub_eq]
      exact Set.sub_mem_sub rfl hz₂
    rw [map_one] at h₃
    exact spectrum_nonneg_of_nonneg (sub_nonneg.mpr S.A_le_one) h₃
  exact ⟨⟨z.re, h₀, by linarith⟩, hre⟩
end Operators
theorem polynomialCalculusStatement_holds : PolynomialCalculusStatement := by
  intro 𝒦 _ _ _ J _ _ S
  have hA : IsSelfAdjoint (algebraA S) := Subtype.ext S.isSelfAdjoint_A.star_eq
  have hspec := spectrum_algebraA S
  have hconj : ∀ f : MonomialAlgebra J, ∃ g : MonomialAlgebra J,
      evalFunction g = (fun p => conj (evalFunction f p)) ∧
        evalOperator S g = star (evalOperator S f) := by
    intro f
    obtain ⟨g, hg, hg'⟩ := exists_conj (algebraA S) hA (algebraB S) f
    exact ⟨g, hg, congrArg Subtype.val hg'⟩
  have hadd : ∀ f g : MonomialAlgebra J,
      evalOperator S (f + g) = evalOperator S f + evalOperator S g := by
    intro f g
    simp [evalOperator]
  have hsmul : ∀ (a : ℂ) (f : MonomialAlgebra J),
      evalOperator S (a • f) = a • evalOperator S f := by
    intro a f
    simp [evalOperator]
  have hmul : ∀ f g : MonomialAlgebra J,
      evalOperator S (f * g) = evalOperator S f * evalOperator S g := by
    intro f g
    simp [evalOperator]
  refine ⟨generatorSet_commute S, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro s s' c c' h
    rw [← evalFunction_ofFinset, ← evalFunction_ofFinset] at h
    funext i
    rw [← coeff_ofFinset, ← coeff_ofFinset, evalFunction_injective h]
  · intro s c
    rw [← evalFunction_ofFinset, polynomialCalculus_evalFunction, evalOperator_ofFinset]
  · exact mem_spectralPolynomials_iff.mpr ⟨0, map_zero _⟩
  · intro q hq q' hq'
    obtain ⟨f, rfl⟩ := mem_spectralPolynomials_iff.mp hq
    obtain ⟨g, rfl⟩ := mem_spectralPolynomials_iff.mp hq'
    exact mem_spectralPolynomials_iff.mpr ⟨f + g, map_add _ _ _⟩
  · intro a q hq
    obtain ⟨f, rfl⟩ := mem_spectralPolynomials_iff.mp hq
    exact mem_spectralPolynomials_iff.mpr ⟨a • f, map_smul _ _ _⟩
  · intro q hq q' hq'
    obtain ⟨f, rfl⟩ := mem_spectralPolynomials_iff.mp hq
    obtain ⟨g, rfl⟩ := mem_spectralPolynomials_iff.mp hq'
    exact mem_spectralPolynomials_iff.mpr ⟨f * g, map_mul _ _ _⟩
  · intro q hq
    obtain ⟨f, rfl⟩ := mem_spectralPolynomials_iff.mp hq
    obtain ⟨g, hg, -⟩ := hconj f
    exact mem_spectralPolynomials_iff.mpr ⟨g, hg⟩
  · intro q hq q' hq'
    obtain ⟨f, rfl⟩ := mem_spectralPolynomials_iff.mp hq
    obtain ⟨g, rfl⟩ := mem_spectralPolynomials_iff.mp hq'
    rw [← map_add, polynomialCalculus_evalFunction, polynomialCalculus_evalFunction,
      polynomialCalculus_evalFunction, hadd]
  · intro a q hq
    obtain ⟨f, rfl⟩ := mem_spectralPolynomials_iff.mp hq
    rw [← map_smul, polynomialCalculus_evalFunction, polynomialCalculus_evalFunction, hsmul]
  · intro q hq q' hq'
    obtain ⟨f, rfl⟩ := mem_spectralPolynomials_iff.mp hq
    obtain ⟨g, rfl⟩ := mem_spectralPolynomials_iff.mp hq'
    rw [← map_mul, polynomialCalculus_evalFunction, polynomialCalculus_evalFunction,
      polynomialCalculus_evalFunction, hmul]
  · intro q hq
    obtain ⟨f, rfl⟩ := mem_spectralPolynomials_iff.mp hq
    obtain ⟨g, hg, hg'⟩ := hconj f
    rw [← hg, polynomialCalculus_evalFunction, polynomialCalculus_evalFunction, hg']
  · intro q hq hpos
    obtain ⟨f, rfl⟩ := mem_spectralPolynomials_iff.mp hq
    rw [polynomialCalculus_evalFunction]
    have hsa : IsSelfAdjoint (evalOperator S f) := by
      obtain ⟨g, hg, hg'⟩ := hconj f
      have hfg : g = f := by
        apply evalFunction_injective
        rw [hg]
        funext p
        exact Complex.conj_eq_iff_real.mpr ⟨(evalFunction f p).re,
          (Complex.eq_re_of_ofReal_le (hpos p)).symm ▸ by simp⟩
      rw [hfg] at hg'
      exact hg'.symm
    refine (StarOrderedRing.nonneg_iff_spectrum_nonneg (R := ℝ) _ hsa).mpr fun r hr => ?_
    have hc : (r : ℂ) ∈ spectrum ℂ (evalOperator S f) := by
      rw [← hsa.spectrumRestricts.algebraMap_image]
      exact ⟨r, hr, rfl⟩
    obtain ⟨p, hp⟩ := spectrum_evalElement_subset (algebraA S) (algebraB S) hspec f
      ((generatedAlgebra S).mem_spectrum_iff.mpr hc)
    have := hpos p
    rw [← hp] at this
    exact Complex.zero_le_real.mp this
  · intro q hq
    obtain ⟨f, rfl⟩ := mem_spectralPolynomials_iff.mp hq
    rw [polynomialCalculus_evalFunction]
    have hb : BddAbove (range fun p => ‖evalFunction f p‖) :=
      (isCompact_range (continuous_evalFunction f).norm).bddAbove
    exact norm_evalElement_le (algebraA S) (algebraB S) hspec f
      (Real.iSup_nonneg fun _ => norm_nonneg _) fun p => le_ciSup hb p
end YangMills.Construction.FamilyPolynomials
