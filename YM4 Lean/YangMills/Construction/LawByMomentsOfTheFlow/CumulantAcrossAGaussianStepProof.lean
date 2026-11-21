import YangMills.Construction.LawInAState.MomentsOfWickPolynomialsProof
import YangMills.Construction.LawByMomentsOfTheFlow.CumulantAcrossAGaussianStep
import YangMills.Construction.LawByMomentsOfTheFlow.CyclicFormulaOfGaussianSquaresProof
import YangMills.Construction.LawByMomentsOfTheFlow.LawInTheComponentsProof
import Mathlib
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
open MeasureTheory ProbabilityTheory
namespace YangMills.Construction.MomentLaw
namespace GaussianStepCumulant
section
open Finset
section Partitions
variable {ι : Type} [DecidableEq ι]
private def IsSetPartition (S : Finset ι) (P : Finset (Finset ι)) : Prop :=
  (∀ D ∈ P, D.Nonempty) ∧ (∀ D ∈ P, ∀ E ∈ P, D ≠ E → Disjoint D E) ∧ P.biUnion id = S
open Classical in
private def setPartitions (S : Finset ι) : Finset (Finset (Finset ι)) :=
  S.powerset.powerset.filter (IsSetPartition S)
private lemma subset_of_isSetPartition {S : Finset ι} {P : Finset (Finset ι)} (h : IsSetPartition S P) {D : Finset ι}
    (hD : D ∈ P) : D ⊆ S := by
  rw [← h.2.2]
  exact subset_biUnion_of_mem id hD
private lemma mem_setPartitions {S : Finset ι} {P : Finset (Finset ι)} : P ∈ setPartitions S ↔ IsSetPartition S P := by apply _root_.YangMills.DeltaSharedProofs.p500779 <;> assumption
private lemma sum_finpartition_eq_sum_setPartitions (S : Finset ι) (g : Finset (Finset ι) → ℝ) :
    ∑ π : Finpartition S, g π.parts = ∑ P ∈ setPartitions S, g P := by apply _root_.YangMills.DeltaSharedProofs.p502077 <;> assumption
private def signedFactorial (k : ℕ) : ℝ := (-1) ^ k * (k.factorial : ℝ)
variable (M : Finset ι → ℝ)
private def momentInverse (S : Finset ι) : ℝ := ∑ P ∈ setPartitions S, signedFactorial P.card * ∏ D ∈ P, M D
private def partitionCumulant (S : Finset ι) : ℝ :=
  ∑ P ∈ setPartitions S, signedFactorial (P.card - 1) * ∏ D ∈ P, M D
private lemma card_pos_of_mem_setPartitions {S : Finset ι} (hS : S.Nonempty) {P : Finset (Finset ι)}
    (hP : P ∈ setPartitions S) : 0 < P.card := by apply _root_.YangMills.DeltaSharedProofs.p502120 <;> assumption
private lemma momentInverse_eq {S : Finset ι} (hS : S.Nonempty) :
    momentInverse M S = - ∑ D ∈ S.powerset.erase ∅, M D * momentInverse M (S \ D) := by apply _root_.YangMills.DeltaSharedProofs.p502140 <;> assumption
private lemma sum_powerset_mul_momentInverse {S : Finset ι} (hS : S.Nonempty) (h0 : M ∅ = 1) :
    ∑ D ∈ S.powerset, M D * momentInverse M (S \ D) = 0 := by apply _root_.YangMills.DeltaSharedProofs.p501735 <;> assumption
private def subsetsContaining (i : ι) (S : Finset ι) : Finset (Finset ι) := S.powerset.filter (i ∈ ·)
private lemma partitionCumulant_eq {i : ι} {S : Finset ι} (hi : i ∈ S) :
    partitionCumulant M S = ∑ B ∈ subsetsContaining i S, M B * momentInverse M (S \ B) := by apply _root_.YangMills.DeltaSharedProofs.p502294 <;> assumption
private lemma momentInverse_congr (M M' : Finset ι → ℝ) {S : Finset ι} (h : ∀ D, D ⊆ S → M D = M' D) :
    momentInverse M S = momentInverse M' S := by
  unfold momentInverse
  refine Finset.sum_congr rfl fun P hP => ?_
  congr 1
  exact Finset.prod_congr rfl fun D hD => h D (subset_of_isSetPartition (mem_setPartitions.1 hP) hD)
private lemma partitionCumulant_shift (h0 : M ∅ = 1) (c : ℝ) {S : Finset ι} {i : ι} (hi : i ∈ S)
    (hne : (S.erase i).Nonempty) :
    partitionCumulant (fun D => if i ∈ D then M D + c * M (D.erase i) else M D) S = partitionCumulant M S := by
  rw [partitionCumulant_eq _ hi, partitionCumulant_eq M hi]
  have h1 : ∀ B ∈ subsetsContaining i S, (fun D => if i ∈ D then M D + c * M (D.erase i) else M D) B *
      momentInverse (fun D => if i ∈ D then M D + c * M (D.erase i) else M D) (S \ B) =
      M B * momentInverse M (S \ B) + c * (M (B.erase i) * momentInverse M (S \ B)) := by
    intro B hB
    have hiB := (Finset.mem_filter.1 hB).2
    rw [momentInverse_congr _ M (S := S \ B) (fun D hD => ?_)]
    · simp only [if_pos hiB]
      ring
    · have : i ∉ D := fun h => (Finset.mem_sdiff.1 (hD h)).2 hiB
      simp only [if_neg this]
  rw [Finset.sum_congr rfl h1, Finset.sum_add_distrib, ← Finset.mul_sum]
  have h2 : ∑ B ∈ subsetsContaining i S, M (B.erase i) * momentInverse M (S \ B) =
      ∑ D ∈ (S.erase i).powerset, M D * momentInverse M ((S.erase i) \ D) := by
    refine Finset.sum_bij (fun B _ => B.erase i) ?_ ?_ ?_ ?_
    · intro B hB
      exact Finset.mem_powerset.2
        (Finset.erase_subset_erase i (Finset.mem_powerset.1 (Finset.mem_filter.1 hB).1))
    · intro B hB B' hB' h
      have e1 := Finset.insert_erase (Finset.mem_filter.1 hB).2
      have e2 := Finset.insert_erase (Finset.mem_filter.1 hB').2
      have h' : B.erase i = B'.erase i := h
      rw [← e1, ← e2, h']
    · intro D hD
      have hD' := Finset.mem_powerset.1 hD
      have hiD : i ∉ D := fun h => (Finset.mem_erase.1 (hD' h)).1 rfl
      refine ⟨insert i D, Finset.mem_filter.2 ⟨Finset.mem_powerset.2 ?_, Finset.mem_insert_self _ _⟩, ?_⟩
      · exact Finset.insert_subset hi (hD'.trans (Finset.erase_subset _ _))
      · exact Finset.erase_insert hiD
    · intro B hB
      have e : S \ B = (S.erase i) \ (B.erase i) := by
        have hiB := (Finset.mem_filter.1 hB).2
        ext x
        simp only [Finset.mem_sdiff, Finset.mem_erase]
        constructor
        · rintro ⟨h1, h2⟩
          exact ⟨⟨fun h => h2 (h ▸ hiB), h1⟩, fun h => h2 h.2⟩
        · rintro ⟨⟨h1, h2⟩, h3⟩
          exact ⟨h2, fun h => h3 ⟨h1, h⟩⟩
      rw [e]
  rw [h2, sum_powerset_mul_momentInverse M hne h0]
  ring
end Partitions
end
section Shift
variable {k : ℕ} {Ω : Type} [MeasurableSpace Ω] {μ : Measure Ω}
private def blockMoment (μ : Measure Ω) (X : Fin k → Ω → ℝ) (J : Finset (Fin k)) : ℝ :=
  ∫ ω, ∏ i ∈ J, X i ω ∂μ
private lemma jointCumulant_eq_partitionCumulant (X : Fin k → Ω → ℝ) :
    jointCumulant μ X = partitionCumulant (blockMoment μ X) Finset.univ := by
  rw [partitionCumulant, ← sum_finpartition_eq_sum_setPartitions Finset.univ
    (fun P => signedFactorial (P.card - 1) * ∏ D ∈ P, blockMoment μ X D)]
  simp only [jointCumulant, blockMoment, signedFactorial]
private lemma jointCumulant_add_const_single [IsProbabilityMeasure μ] (hk : 2 ≤ k) (X : Fin k → Ω → ℝ)
    (i : Fin k) (c : ℝ)
    (hI : ∀ D : Finset (Fin k), Integrable (fun ω => ∏ j ∈ D, X j ω) μ) :
    jointCumulant μ (fun j ω => X j ω + (if j = i then c else 0)) = jointCumulant μ X := by
  have hne : ((Finset.univ : Finset (Fin k)).erase i).Nonempty := by
    rw [← Finset.card_pos, Finset.card_erase_of_mem (Finset.mem_univ i)]
    simp only [Finset.card_univ, Fintype.card_fin]
    omega
  rw [jointCumulant_eq_partitionCumulant, jointCumulant_eq_partitionCumulant,
    ← partitionCumulant_shift (blockMoment μ X) (by simp [blockMoment]) c (Finset.mem_univ i) hne]
  congr 1
  funext D
  split_ifs with hD
  · have e : ∀ ω, ∏ j ∈ D, (X j ω + if j = i then c else 0) =
        ∏ j ∈ D, X j ω + c * ∏ j ∈ D.erase i, X j ω := by
      intro ω
      rw [← Finset.mul_prod_erase D _ hD, ← Finset.mul_prod_erase D (fun j => X j ω) hD]
      have e2 : ∏ j ∈ D.erase i, (X j ω + if j = i then c else 0) = ∏ j ∈ D.erase i, X j ω :=
        Finset.prod_congr rfl fun j hj => by simp [Finset.ne_of_mem_erase hj]
      rw [e2]
      simp only [if_true]
      ring
    simp only [blockMoment, e]
    rw [integral_add (hI D) ((hI _).const_mul c), integral_const_mul]
  · simp only [blockMoment]
    refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
    refine Finset.prod_congr rfl fun j hj => ?_
    have : j ≠ i := fun h => hD (h ▸ hj)
    simp [this]
private lemma jointCumulant_add_const [IsProbabilityMeasure μ] (hk : 2 ≤ k) (X : Fin k → Ω → ℝ)
    (c : Fin k → ℝ)
    (hI : ∀ (a : Fin k → ℝ) (D : Finset (Fin k)), Integrable (fun ω => ∏ j ∈ D, (X j ω + a j)) μ) :
    jointCumulant μ (fun j ω => X j ω + c j) = jointCumulant μ X := by
  have key : ∀ I : Finset (Fin k),
      jointCumulant μ (fun j ω => X j ω + (if j ∈ I then c j else 0)) = jointCumulant μ X := by
    intro I
    induction I using Finset.induction_on with
    | empty => simp
    | insert i I hi ih =>
      rw [← ih, ← jointCumulant_add_const_single hk (fun j ω => X j ω + (if j ∈ I then c j else 0)) i (c i)
        (fun D => hI _ D)]
      congr 1
      funext j ω
      by_cases h : j = i
      · subst h
        simp [hi]
      · simp [h]
  simpa using key Finset.univ
end Shift
section
open Finset
section Moments
private def gaussianMoment (k : ℕ) : ℝ := ∫ x, x ^ k ∂(gaussianReal 0 1)
private lemma integrable_pow_gaussianReal (k : ℕ) : Integrable (fun x : ℝ => x ^ k) (gaussianReal 0 1) := by apply _root_.YangMills.SharedProofs.p8958 <;> assumption
private lemma gaussianMoment_one : gaussianMoment 1 = 0 := by simp [gaussianMoment]
private lemma hasDerivAt_gaussianPDFReal_std (x : ℝ) :
    HasDerivAt (gaussianPDFReal 0 1) (- x * gaussianPDFReal 0 1 x) x := by apply _root_.YangMills.SharedProofs.p43829 <;> assumption
private lemma gaussianMoment_add_two (k : ℕ) : gaussianMoment (k + 2) = (k + 1) * gaussianMoment k := by apply _root_.YangMills.DeltaSharedProofs.p500965 <;> assumption
end Moments
section Functional
open MvPolynomial
variable {σ : Type} [Fintype σ] [DecidableEq σ]
private def gaussianExpectation : MvPolynomial σ ℝ →ₗ[ℝ] ℝ :=
  (basisMonomials σ ℝ).constr ℝ fun m => ∏ s, gaussianMoment (m s)
private lemma gaussianExpectation_monomial (m : σ →₀ ℕ) (c : ℝ) :
    gaussianExpectation (monomial m c) = c * ∏ s, gaussianMoment (m s) := by
  have : (monomial m c : MvPolynomial σ ℝ) = c • basisMonomials σ ℝ m := by
    simp [MvPolynomial.smul_monomial]
  rw [this, map_smul, gaussianExpectation, Module.Basis.constr_basis, smul_eq_mul]
private lemma gaussianExpectation_X_mul (a : σ) (H : MvPolynomial σ ℝ) :
    gaussianExpectation (X a * H) = gaussianExpectation (pderiv a H) := by
  induction H using MvPolynomial.induction_on' with
  | add p q hp hq => rw [mul_add, map_add, map_add, map_add, hp, hq]
  | monomial u c =>
    have h1 : (X a * monomial u c : MvPolynomial σ ℝ) = monomial (Finsupp.single a 1 + u) c := by
      rw [X, monomial_mul, one_mul]
    rw [h1, pderiv_monomial, gaussianExpectation_monomial, gaussianExpectation_monomial,
      ← Finset.mul_prod_erase _ _ (Finset.mem_univ a), ← Finset.mul_prod_erase _ _ (Finset.mem_univ a)]
    have h2 : ∏ s ∈ Finset.univ.erase a, gaussianMoment ((Finsupp.single a 1 + u : σ →₀ ℕ) s) =
        ∏ s ∈ Finset.univ.erase a, gaussianMoment ((u - Finsupp.single a 1 : σ →₀ ℕ) s) := by
      refine Finset.prod_congr rfl fun s hs => ?_
      have hne : a ≠ s := fun h => by simp [h] at hs
      simp [Finsupp.single_apply, hne]
    rw [h2]
    rcases hk : u a with _ | k
    · simp [hk, gaussianMoment_one]
    · simp only [Finsupp.add_apply, Finsupp.single_eq_same, Finsupp.tsub_apply, hk]
      rw [show 1 + (k + 1) = k + 2 by ring, gaussianMoment_add_two, Nat.add_sub_cancel]
      push_cast
      ring
private structure IsStdGaussianFamily {Ω : Type} [MeasurableSpace Ω] (ν : Measure Ω) (z : Ω → σ → ℝ) :
    Prop where
  integrable : ∀ m : σ → ℕ, Integrable (fun ω => ∏ s, z ω s ^ m s) ν
  integral : ∀ m : σ → ℕ, ∫ ω, ∏ s, z ω s ^ m s ∂ν = ∏ s, gaussianMoment (m s)
variable {Ω : Type} [MeasurableSpace Ω] {ν : Measure Ω} {z : Ω → σ → ℝ}
private lemma IsStdGaussianFamily.eval_poly (h : IsStdGaussianFamily ν z) (H : MvPolynomial σ ℝ) :
    Integrable (fun ω => MvPolynomial.eval (z ω) H) ν ∧
      ∫ ω, MvPolynomial.eval (z ω) H ∂ν = gaussianExpectation H := by
  induction H using MvPolynomial.induction_on' with
  | add p q hp hq =>
    simp only [map_add]
    exact ⟨hp.1.add hq.1, by rw [integral_add hp.1 hq.1, hp.2, hq.2]⟩
  | monomial u c =>
    have e : ∀ ω, MvPolynomial.eval (z ω) (monomial u c) = c * ∏ s, z ω s ^ u s := by
      intro ω
      rw [eval_monomial, Finsupp.prod_fintype _ _ (by simp)]
    simp only [e]
    exact ⟨(h.integrable u).const_mul c, by
      rw [integral_const_mul, h.integral u, gaussianExpectation_monomial]⟩
end Functional
end
section
open MvPolynomial
variable {σ : Type} [Fintype σ] [DecidableEq σ]
private def quadraticFormPoly (P : Matrix σ σ ℝ) : MvPolynomial σ ℝ :=
  C (1 / 2) * ∑ a, ∑ b, C (P a b) * (X a * X b)
private lemma pderiv_quadraticFormPoly {Q : Matrix σ σ ℝ} (hQ : Q.IsSymm) (c : σ) :
    pderiv c (quadraticFormPoly Q) = ∑ b, C (Q c b) * X b := by
  have h1 : ∀ a b, pderiv c (C (Q a b) * (X a * X b) : MvPolynomial σ ℝ) =
      (if a = c then C (Q a b) * X b else 0) + (if b = c then C (Q a b) * X a else 0) := by
    intro a b
    rw [pderiv_C_mul, pderiv_mul, pderiv_X, pderiv_X]
    by_cases ha : a = c <;> by_cases hb : b = c <;> simp [ha, hb, mul_add]
  have h2 : ∑ a, ∑ b, ((if a = c then C (Q a b) * X b else 0) +
      (if b = c then C (Q a b) * X a else 0) : MvPolynomial σ ℝ) =
      C 2 * ∑ b, C (Q c b) * X b := by
    simp only [Finset.sum_add_distrib]
    have e1 : ∑ a, ∑ b, (if a = c then C (Q a b) * X b else 0 : MvPolynomial σ ℝ) =
        ∑ b, C (Q c b) * X b := by
      rw [Finset.sum_eq_single c]
      · simp
      · intro a _ ha
        simp [ha]
      · simp
    have e2 : ∑ a, ∑ b, (if b = c then C (Q a b) * X a else 0 : MvPolynomial σ ℝ) =
        ∑ b, C (Q c b) * X b := by
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [Finset.sum_eq_single c]
      · simp [hQ.apply a c]
      · intro b _ hb
        simp [hb]
      · simp
    rw [e1, e2, ← two_mul]
    simp [map_ofNat]
  rw [quadraticFormPoly, pderiv_C_mul, map_sum]
  simp only [map_sum, h1]
  rw [h2, ← mul_assoc, ← C_mul]
  norm_num
private lemma pderiv_prod_eq_sum (c : σ) {ι : Type} [DecidableEq ι] (S : Finset ι) (f : ι → MvPolynomial σ ℝ) :
    pderiv c (∏ j ∈ S, f j) = ∑ j ∈ S, pderiv c (f j) * ∏ l ∈ S.erase j, f l := by apply _root_.YangMills.SharedProofs.p117859 <;> assumption
private lemma isStdGaussianFamily_pi (τ : Type) [Fintype τ] [DecidableEq τ] :
    IsStdGaussianFamily (Measure.pi fun _ : τ => gaussianReal 0 1) (fun w : τ → ℝ => w) where
  integrable m := Integrable.fintype_prod (f := fun s x => x ^ m s)
    (fun s => integrable_pow_gaussianReal (m s))
  integral m := integral_fintype_prod_eq_prod (fun s (x : ℝ) => x ^ m s)
end
section Polys
open MvPolynomial Matrix
open scoped MatrixOrder
variable {σ : Type} [Fintype σ] [DecidableEq σ]
private lemma linearMap_C_mul (E : MvPolynomial σ ℝ →ₗ[ℝ] ℝ) (r : ℝ) (H : MvPolynomial σ ℝ) :
    E (C r * H) = r * E H := by
  rw [← MvPolynomial.smul_eq_C_mul, map_smul, smul_eq_mul]
private def sqrtCoordPoly (A : Matrix σ σ ℝ) (b : σ) : MvPolynomial σ ℝ := ∑ a, C (A b a) * X a
private lemma pderiv_sqrtCoordPoly (A : Matrix σ σ ℝ) (a b : σ) :
    pderiv a (sqrtCoordPoly A b) = C (A b a) := by
  rw [sqrtCoordPoly, map_sum, Finset.sum_eq_single a]
  · simp [pderiv_C_mul, pderiv_X]
  · intro c _ hc
    simp [pderiv_C_mul, pderiv_X, Pi.single_apply, hc.symm]
  · simp
private lemma pderiv_bind₁_sqrtCoordPoly (A : Matrix σ σ ℝ) (a : σ) (F : MvPolynomial σ ℝ) :
    pderiv a (bind₁ (sqrtCoordPoly A) F) = ∑ b, bind₁ (sqrtCoordPoly A) (pderiv b F) * C (A b a) := by
  induction F using MvPolynomial.induction_on with
  | C r => simp
  | add p q hp hq => simp only [map_add, hp, hq, add_mul, Finset.sum_add_distrib]
  | mul_X p n hp =>
    rw [map_mul, bind₁_X_right, pderiv_mul, hp, pderiv_sqrtCoordPoly]
    have e : ∀ b, bind₁ (sqrtCoordPoly A) (pderiv b (p * X n)) * C (A b a) =
        bind₁ (sqrtCoordPoly A) (pderiv b p) * C (A b a) * sqrtCoordPoly A n +
          (if b = n then bind₁ (sqrtCoordPoly A) p * C (A b a) else 0) := by
      intro b
      rw [pderiv_mul, pderiv_X, map_add, map_mul, map_mul, bind₁_X_right]
      by_cases h : b = n
      · subst h
        simp only [Pi.single_eq_same, map_one, mul_one, if_true]
        ring
      · have h' : n ≠ b := fun e => h e.symm
        simp [Pi.single_apply, h, h']
        ring
    simp only [e, Finset.sum_add_distrib, Finset.sum_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
private def gaussianMeanAt (A : Matrix σ σ ℝ) : MvPolynomial σ ℝ →ₗ[ℝ] ℝ :=
  gaussianExpectation ∘ₗ (bind₁ (sqrtCoordPoly A)).toLinearMap
private lemma gaussianMeanAt_apply (A : Matrix σ σ ℝ) (H : MvPolynomial σ ℝ) :
    gaussianMeanAt A H = gaussianExpectation (bind₁ (sqrtCoordPoly A) H) := rfl
private lemma gaussianMeanAt_X_mul {A G : Matrix σ σ ℝ} (hA : A.IsSymm) (hG : A * A = G) (b : σ)
    (F : MvPolynomial σ ℝ) :
    gaussianMeanAt A (X b * F) = ∑ c, G b c * gaussianMeanAt A (pderiv c F) := by
  rw [gaussianMeanAt_apply, map_mul, bind₁_X_right, sqrtCoordPoly, Finset.sum_mul, map_sum]
  have h1 : ∀ a, gaussianExpectation (C (A b a) * X a * bind₁ (sqrtCoordPoly A) F) =
      A b a * ∑ c, A c a * gaussianMeanAt A (pderiv c F) := by
    intro a
    rw [mul_assoc, linearMap_C_mul, gaussianExpectation_X_mul, pderiv_bind₁_sqrtCoordPoly, map_sum]
    congr 1
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [mul_comm, linearMap_C_mul, gaussianMeanAt_apply]
  simp only [h1, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [← hG, Matrix.mul_apply, Finset.sum_mul]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [hA.apply a c]
  ring
private def sqrtMap (A : Matrix σ σ ℝ) (w : σ → ℝ) : EuclideanSpace ℝ σ :=
  toEuclideanCLM (𝕜 := ℝ) A (WithLp.toLp 2 w)
private lemma measurable_sqrtMap (A : Matrix σ σ ℝ) : Measurable (sqrtMap A) := by
  unfold sqrtMap
  fun_prop
private lemma multivariateGaussian_zero_eq_map (G : Matrix σ σ ℝ) :
    multivariateGaussian 0 G =
      (Measure.pi fun _ : σ => gaussianReal 0 1).map (sqrtMap (CFC.sqrt G)) := by
  rw [multivariateGaussian, ← map_pi_eq_stdGaussian, Measure.map_map (by fun_prop) (by fun_prop)]
  congr 1
  ext1 w
  simp [sqrtMap]
private lemma sqrtMap_apply (A : Matrix σ σ ℝ) (w : σ → ℝ) (b : σ) :
    sqrtMap A w b = ∑ a, A b a * w a := by
  simp [sqrtMap, Matrix.mulVec, dotProduct]
private lemma eval_bind₁_sqrtCoordPoly (A : Matrix σ σ ℝ) (g : σ → ℝ) (H : MvPolynomial σ ℝ) :
    eval g (bind₁ (sqrtCoordPoly A) H) = eval (fun b => sqrtMap A g b) H := by
  induction H using MvPolynomial.induction_on with
  | C r => simp
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p n hp =>
    simp only [map_mul, hp, bind₁_X_right, eval_X]
    congr 1
    simp [sqrtCoordPoly, sqrtMap_apply]
private lemma measurable_eval_coords (H : MvPolynomial σ ℝ) :
    Measurable (fun η : EuclideanSpace ℝ σ => eval (fun b => η b) H) := by
  have h1 : Continuous (fun η : EuclideanSpace ℝ σ => (fun b => η b : σ → ℝ)) := by fun_prop
  exact ((MvPolynomial.continuous_eval H).comp h1).measurable
private lemma integral_eval_multivariateGaussian (G : Matrix σ σ ℝ) (H : MvPolynomial σ ℝ) :
    Integrable (fun η : EuclideanSpace ℝ σ => eval (fun b => η b) H) (multivariateGaussian 0 G) ∧
      ∫ η, eval (fun b => η b) H ∂(multivariateGaussian 0 G) = gaussianMeanAt (CFC.sqrt G) H := by
  have hm := measurable_eval_coords H
  rw [multivariateGaussian_zero_eq_map]
  have h := (isStdGaussianFamily_pi σ).eval_poly (bind₁ (sqrtCoordPoly (CFC.sqrt G)) H)
  simp only [eval_bind₁_sqrtCoordPoly] at h
  refine ⟨(integrable_map_measure hm.aestronglyMeasurable (measurable_sqrtMap _).aemeasurable).2 h.1, ?_⟩
  rw [integral_map (measurable_sqrtMap _).aemeasurable hm.aestronglyMeasurable]
  exact h.2
variable (G : Matrix σ σ ℝ)
private def centeredQuadPoly (l : σ → ℝ) (S : Matrix σ σ ℝ) : MvPolynomial σ ℝ :=
  ∑ b, C (l b) * X b + quadraticFormPoly S - C ((1 / 2) * (S * G).trace)
private def halfGradPoly (l : σ → ℝ) (S : Matrix σ σ ℝ) (b : σ) : MvPolynomial σ ℝ :=
  C (l b) + C (1 / 2) * ∑ b', C (S b b') * X b'
private def gradPoly (l : σ → ℝ) (S : Matrix σ σ ℝ) (b : σ) : MvPolynomial σ ℝ :=
  C (l b) + ∑ b', C (S b b') * X b'
private lemma pderiv_centeredQuadPoly {S : Matrix σ σ ℝ} (hS : S.IsSymm) (l : σ → ℝ) (c : σ) :
    pderiv c (centeredQuadPoly G l S) = gradPoly l S c := by
  rw [centeredQuadPoly, map_sub, map_add, pderiv_quadraticFormPoly hS, map_sum, gradPoly, pderiv_C,
    sub_zero]
  congr 1
  rw [Finset.sum_eq_single c]
  · simp [pderiv_C_mul, pderiv_X]
  · intro b _ hb
    simp [pderiv_C_mul, pderiv_X, Pi.single_apply, hb.symm]
  · simp
variable (E : MvPolynomial σ ℝ →ₗ[ℝ] ℝ) (hE : ∀ b F, E (X b * F) = ∑ c, G b c * E (pderiv c F))
include hE in
private lemma linearMap_X_mul_X_mul (a b : σ) (F : MvPolynomial σ ℝ) :
    E (X a * X b * F) = G a b * E F + ∑ c, G a c * E (X b * pderiv c F) := by
  rw [mul_assoc, hE]
  have h : ∀ c, pderiv c (X b * F) = (if c = b then F else 0) + X b * pderiv c F := by
    intro c
    rw [pderiv_mul, pderiv_X]
    by_cases h : c = b
    · subst h
      simp
    · have h' : b ≠ c := fun e => h e.symm
      simp [Pi.single_apply, h, h']
  simp only [h, map_add, mul_add, Finset.sum_add_distrib]
  congr 1
  rw [Finset.sum_eq_single b]
  · simp
  · intro c _ hc
    simp [hc]
  · simp
include hE in
private lemma linearMap_centeredQuadPoly_mul (hG : G.IsSymm) (l : σ → ℝ) (S : Matrix σ σ ℝ)
    (F : MvPolynomial σ ℝ) :
    E (centeredQuadPoly G l S * F) = ∑ b, ∑ c, G b c * E (halfGradPoly l S b * pderiv c F) := by
  have h1 : E ((∑ b, C (l b) * X b) * F) = ∑ b, ∑ c, G b c * (l b * E (pderiv c F)) := by
    rw [Finset.sum_mul, map_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [mul_assoc, linearMap_C_mul, hE, Finset.mul_sum]
    exact Finset.sum_congr rfl fun c _ => by ring
  have h2 : E (quadraticFormPoly S * F) = (1 / 2) * ((S * G).trace * E F) +
      ∑ b, ∑ c, G b c * ((1 / 2) * ∑ b', S b b' * E (X b' * pderiv c F)) := by
    have h3 : (S * G).trace = ∑ b, ∑ b', S b b' * G b b' := by
      simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply]
      exact Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun b' _ => by rw [hG.apply b b']
    rw [quadraticFormPoly, mul_assoc, linearMap_C_mul, Finset.sum_mul, map_sum]
    have h4 : ∀ b, E ((∑ b', C (S b b') * (X b * X b')) * F) =
        (∑ b', S b b' * G b b') * E F + ∑ c, G b c * ∑ b', S b b' * E (X b' * pderiv c F) := by
      intro b
      rw [Finset.sum_mul, map_sum]
      have h5 : ∀ b', E (C (S b b') * (X b * X b') * F) =
          S b b' * G b b' * E F + ∑ c, G b c * (S b b' * E (X b' * pderiv c F)) := by
        intro b'
        rw [mul_assoc, linearMap_C_mul, linearMap_X_mul_X_mul G E hE, mul_add, Finset.mul_sum]
        congr 1
        · ring
        · exact Finset.sum_congr rfl fun c _ => by ring
      simp only [h5, Finset.sum_add_distrib]
      rw [Finset.sum_mul, Finset.sum_comm]
      congr 1
      exact Finset.sum_congr rfl fun c _ => by rw [Finset.mul_sum]
    simp only [h4, Finset.sum_add_distrib]
    rw [mul_add, h3, Finset.sum_mul]
    congr 1
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    ring
  have h6 : ∀ b c, E (halfGradPoly l S b * pderiv c F) =
      l b * E (pderiv c F) + (1 / 2) * ∑ b', S b b' * E (X b' * pderiv c F) := by
    intro b c
    rw [halfGradPoly, add_mul, map_add, linearMap_C_mul, mul_assoc, linearMap_C_mul, Finset.sum_mul, map_sum]
    congr 2
    refine Finset.sum_congr rfl fun b' _ => ?_
    rw [mul_assoc, linearMap_C_mul]
  rw [centeredQuadPoly, sub_mul, add_mul, map_sub, map_add, h1, h2, linearMap_C_mul]
  simp only [h6, mul_add, Finset.sum_add_distrib]
  ring
private lemma integral_centeredQuadPoly_mul_prod {k : ℕ} (hG : G.PosSemidef) (l : Fin k → σ → ℝ)
    (S : Fin k → Matrix σ σ ℝ) (hS : ∀ i, (S i).IsSymm) (i₀ : Fin k) (U : Finset (Fin k)) :
    ∫ η, eval (fun b => η b) (centeredQuadPoly G (l i₀) (S i₀) * ∏ j ∈ U, centeredQuadPoly G (l j) (S j))
        ∂(multivariateGaussian 0 G) =
      ∑ j ∈ U, ∑ b, ∑ c, G b c * ∫ η, eval (fun b => η b)
        (halfGradPoly (l i₀) (S i₀) b * gradPoly (l j) (S j) c *
          ∏ m ∈ U.erase j, centeredQuadPoly G (l m) (S m)) ∂(multivariateGaussian 0 G) := by
  have hA : (CFC.sqrt G).IsSymm := by
    have h1 : IsSelfAdjoint (CFC.sqrt G) := (CFC.sqrt_nonneg G).isSelfAdjoint
    have h2 : (CFC.sqrt G).conjTranspose = CFC.sqrt G := h1
    rw [Matrix.IsSymm, ← Matrix.conjTranspose_eq_transpose_of_trivial, h2]
  have hAA : CFC.sqrt G * CFC.sqrt G = G := CFC.sqrt_mul_sqrt_self _ hG.nonneg
  have hGs : G.IsSymm := by
    have h2 : G.conjTranspose = G := hG.isHermitian
    rw [Matrix.IsSymm, ← Matrix.conjTranspose_eq_transpose_of_trivial, h2]
  simp only [(integral_eval_multivariateGaussian G _).2]
  rw [linearMap_centeredQuadPoly_mul G (gaussianMeanAt (CFC.sqrt G)) (gaussianMeanAt_X_mul hA hAA) hGs]
  simp only [pderiv_prod_eq_sum, pderiv_centeredQuadPoly G (hS _), Finset.mul_sum, map_sum]
  refine (Finset.sum_congr rfl fun b _ => Finset.sum_comm).trans (Finset.sum_comm.trans ?_)
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun c _ => ?_
  congr 2
  ring
end Polys
section Sized
variable {Ω : Type} [MeasurableSpace Ω]
private structure MomentBounded (k : ℕ) (μ : Measure Ω) (f : Ω → ℝ) (B : ℝ) : Prop where
  meas : Measurable f
  int : Integrable (fun x => |f x| ^ k) μ
  le : ∫ x, |f x| ^ k ∂μ ≤ B ^ k
variable {k : ℕ} {μ : Measure Ω}
private lemma MomentBounded.mono {f : Ω → ℝ} {B B' : ℝ} (h : MomentBounded k μ f B) (hB : 0 ≤ B)
    (hBB : B ≤ B') : MomentBounded k μ f B' :=
  ⟨h.meas, h.int, h.le.trans (pow_le_pow_left₀ hB hBB k)⟩
private lemma prod_le_one_add_sum_pow {α : Type} [DecidableEq α] (J : Finset α) (x : α → ℝ)
    (hx : ∀ j, 0 ≤ x j) (hJ : J.card ≤ k) :
    ∏ j ∈ J, x j ≤ 1 + ∑ j ∈ J, (1 + x j ^ k) := by
  rcases J.eq_empty_or_nonempty with rfl | hne
  · simp
  obtain ⟨j₀, hj₀, hmax⟩ := J.exists_max_image x hne
  have h1 : ∏ j ∈ J, x j ≤ x j₀ ^ J.card := by
    calc ∏ j ∈ J, x j ≤ ∏ _j ∈ J, x j₀ := Finset.prod_le_prod (fun j _ => hx j) hmax
      _ = x j₀ ^ J.card := by simp
  have h2 : x j₀ ^ J.card ≤ 1 + x j₀ ^ k := by
    rcases le_total (x j₀) 1 with h | h
    · have := pow_le_one₀ (n := J.card) (hx j₀) h
      have h3 := pow_nonneg (hx j₀) k
      linarith
    · have := pow_le_pow_right₀ h hJ
      linarith
  have h3 : 1 + x j₀ ^ k ≤ ∑ j ∈ J, (1 + x j ^ k) :=
    Finset.single_le_sum (f := fun j => 1 + x j ^ k)
      (fun j _ => by have := pow_nonneg (hx j) k; linarith) hj₀
  linarith
private lemma MomentBounded.prod [IsProbabilityMeasure μ] {α : Type} [DecidableEq α] {J : Finset α}
    {f : α → Ω → ℝ} {B : α → ℝ}
    (hB : ∀ j ∈ J, 0 < B j) (hf : ∀ j ∈ J, MomentBounded k μ (f j) (B j)) (hJ : J.card ≤ k) :
    Integrable (fun x => ∏ j ∈ J, f j x) μ ∧
      |∫ x, ∏ j ∈ J, f j x ∂μ| ≤ (1 + 2 * (k : ℝ)) * ∏ j ∈ J, B j := by
  classical
  have hP : 0 < ∏ j ∈ J, B j := Finset.prod_pos hB
  let g : Ω → ℝ := fun x => 1 + ∑ j ∈ J, (1 + (|f j x| / B j) ^ k)
  have hpt : ∀ x, |∏ j ∈ J, f j x| ≤ (∏ j ∈ J, B j) * g x := by
    intro x
    have h1 := prod_le_one_add_sum_pow (k := k) J (fun j => if j ∈ J then |f j x| / B j else 0)
      (fun j => by
        by_cases h : j ∈ J
        · simp only [if_pos h]
          exact div_nonneg (abs_nonneg _) (hB j h).le
        · simp [h]) hJ
    have h2 : ∏ j ∈ J, (if j ∈ J then |f j x| / B j else 0) = ∏ j ∈ J, (|f j x| / B j) :=
      Finset.prod_congr rfl fun j hj => by simp [hj]
    have h3 : ∑ j ∈ J, (1 + (if j ∈ J then |f j x| / B j else 0) ^ k) =
        ∑ j ∈ J, (1 + (|f j x| / B j) ^ k) :=
      Finset.sum_congr rfl fun j hj => by simp [hj]
    rw [h2, h3] at h1
    rw [Finset.abs_prod]
    have h4 : ∏ j ∈ J, |f j x| = (∏ j ∈ J, B j) * ∏ j ∈ J, (|f j x| / B j) := by
      rw [← Finset.prod_mul_distrib]
      exact Finset.prod_congr rfl fun j hj => by
        have := (hB j hj).ne'
        field_simp
    rw [h4]
    exact mul_le_mul_of_nonneg_left h1 hP.le
  have hint : ∀ j ∈ J, Integrable (fun x => 1 + (|f j x| / B j) ^ k) μ := by
    intro j hj
    refine (integrable_const 1).add ?_
    have := (hf j hj).int.mul_const (B j ^ k)⁻¹
    refine this.congr (Filter.Eventually.of_forall fun x => ?_)
    show |f j x| ^ k * (B j ^ k)⁻¹ = (|f j x| / B j) ^ k
    rw [div_pow, div_eq_mul_inv]
  have hgi : Integrable g μ := (integrable_const 1).add (integrable_finset_sum _ hint)
  have hm : AEStronglyMeasurable (fun x => ∏ j ∈ J, f j x) μ :=
    (Finset.measurable_fun_prod _ fun j hj => (hf j hj).meas).aestronglyMeasurable
  have hI : Integrable (fun x => ∏ j ∈ J, f j x) μ :=
    (hgi.const_mul (∏ j ∈ J, B j)).mono' hm (Filter.Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs]
      exact hpt x)
  refine ⟨hI, ?_⟩
  have hg : ∫ x, g x ∂μ ≤ 1 + 2 * (k : ℝ) := by
    have h1 : ∫ x, g x ∂μ = 1 + ∑ j ∈ J, ∫ x, (1 + (|f j x| / B j) ^ k) ∂μ := by
      simp only [g]
      rw [integral_add (integrable_const 1) (integrable_finset_sum _ hint), integral_finset_sum _ hint]
      simp
    have h2 : ∀ j ∈ J, ∫ x, (1 + (|f j x| / B j) ^ k) ∂μ ≤ 2 := by
      intro j hj
      have hb := hB j hj
      have hi : Integrable (fun x => (|f j x| / B j) ^ k) μ := by
        have := (hf j hj).int.mul_const (B j ^ k)⁻¹
        refine this.congr (Filter.Eventually.of_forall fun x => ?_)
        show |f j x| ^ k * (B j ^ k)⁻¹ = (|f j x| / B j) ^ k
        rw [div_pow, div_eq_mul_inv]
      rw [integral_add (integrable_const 1) hi]
      have e : ∫ x, (|f j x| / B j) ^ k ∂μ = (∫ x, |f j x| ^ k ∂μ) / B j ^ k := by
        simp only [div_pow]
        rw [integral_div]
      rw [e]
      have h3 : (∫ x, |f j x| ^ k ∂μ) / B j ^ k ≤ 1 := by
        rw [div_le_one (pow_pos hb k)]
        exact (hf j hj).le
      simp only [integral_const, probReal_univ, smul_eq_mul, mul_one]
      linarith
    rw [h1]
    have h3 := Finset.sum_le_sum h2
    have h4 : ((J.card : ℝ)) ≤ k := by exact_mod_cast hJ
    simp only [Finset.sum_const, nsmul_eq_mul] at h3
    linarith
  calc |∫ x, ∏ j ∈ J, f j x ∂μ| ≤ ∫ x, |∏ j ∈ J, f j x| ∂μ := abs_integral_le_integral_abs
    _ ≤ ∫ x, (∏ j ∈ J, B j) * g x ∂μ := integral_mono hI.abs (hgi.const_mul _) hpt
    _ = (∏ j ∈ J, B j) * ∫ x, g x ∂μ := integral_const_mul _ _
    _ ≤ (∏ j ∈ J, B j) * (1 + 2 * (k : ℝ)) := mul_le_mul_of_nonneg_left hg hP.le
    _ = _ := mul_comm _ _
private lemma MomentBounded.add {f g : Ω → ℝ} {B B' : ℝ} (hk : k ≠ 0) (hB : 0 ≤ B) (hB' : 0 ≤ B')
    (hf : MomentBounded k μ f B) (hg : MomentBounded k μ g B') :
    MomentBounded k μ (fun x => f x + g x) (2 * (B + B')) := by
  have hpt : ∀ x, |f x + g x| ^ k ≤ 2 ^ k * (|f x| ^ k + |g x| ^ k) := by
    intro x
    calc |f x + g x| ^ k ≤ (|f x| + |g x|) ^ k := pow_le_pow_left₀ (abs_nonneg _) (abs_add_le _ _) k
      _ ≤ 2 ^ (k - 1) * (|f x| ^ k + |g x| ^ k) := add_pow_le (abs_nonneg _) (abs_nonneg _) k
      _ ≤ 2 ^ k * (|f x| ^ k + |g x| ^ k) :=
        mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) (Nat.sub_le _ _)) (by positivity)
  have hm : Measurable fun x => f x + g x := hf.meas.add hg.meas
  have hi : Integrable (fun x => 2 ^ k * (|f x| ^ k + |g x| ^ k)) μ := (hf.int.add hg.int).const_mul _
  have hI : Integrable (fun x => |f x + g x| ^ k) μ :=
    hi.mono' (hm.abs.pow_const k).aestronglyMeasurable (Filter.Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      exact hpt x)
  refine ⟨hm, hI, (integral_mono hI hi hpt).trans ?_⟩
  rw [integral_const_mul, integral_add hf.int hg.int, mul_pow]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  exact (add_le_add hf.le hg.le).trans (pow_add_pow_le hB hB' hk)
private lemma MomentBounded.const [IsProbabilityMeasure μ] (c : ℝ) {B : ℝ} (h : |c| ≤ B) :
    MomentBounded k μ (fun _ => c) B := by
  refine ⟨measurable_const, integrable_const _, ?_⟩
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
  exact pow_le_pow_left₀ (abs_nonneg _) h k
private lemma MomentBounded.mul_const {f : Ω → ℝ} {B : ℝ} (hf : MomentBounded k μ f B) (c : ℝ)
    (hc : |c| ≤ 1) (hB : 0 ≤ B) :
    MomentBounded k μ (fun x => c * f x) B := by
  have hpt : ∀ x, |c * f x| ^ k ≤ |f x| ^ k := by
    intro x
    rw [abs_mul]
    exact pow_le_pow_left₀ (by positivity) (mul_le_of_le_one_left (abs_nonneg _) hc) k
  have hm : Measurable fun x => c * f x := hf.meas.const_mul c
  have hI : Integrable (fun x => |c * f x| ^ k) μ :=
    hf.int.mono' (hm.abs.pow_const k).aestronglyMeasurable (Filter.Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      exact hpt x)
  exact ⟨hm, hI, (integral_mono hI hf.int hpt).trans hf.le⟩
end Sized
section Blocks
variable {k : ℕ} {Ω E ι : Type} [MeasurableSpace Ω] [MeasurableSpace E] [Fintype ι] [DecidableEq ι]
  {ρ : Measure Ω} [IsProbabilityMeasure ρ] {γ : Measure E} [IsProbabilityMeasure γ]
private lemma abs_integral_block_le (T : Fin k → Ω × E → ℝ) (W : Fin k → Ω → ℝ)
    (U₀ V₀ : Fin k → ι → Ω × E → ℝ) (G : ι → ι → ℝ)
    (τ ε : ℝ) (w : Fin k → ι → ℝ) (hτ : 1 ≤ τ) (hε₀ : 0 ≤ ε) (hw : ∀ i b, 0 < w i b)
    (sT : ∀ i, MomentBounded k (ρ.prod γ) (T i) τ)
    (sW : ∀ i, MomentBounded k (ρ.prod γ) (fun x => W i x.1) τ)
    (sU : ∀ i b, MomentBounded k (ρ.prod γ) (U₀ i b) (4 * w i b))
    (sV : ∀ i b, MomentBounded k (ρ.prod γ) (V₀ i b) (w i b))
    (hε : ∀ i j, i ≠ j → ∑ b, ∑ c, w i b * |G b c| * w j c ≤ ε)
    (stein : ∀ (ξ : Ω) (i₀ : Fin k) (U' : Finset (Fin k)),
      ∫ η, T i₀ (ξ, η) * ∏ j ∈ U', T j (ξ, η) ∂γ =
        ∑ j ∈ U', ∑ b, ∑ c, G b c * ∫ η, U₀ i₀ b (ξ, η) * V₀ j c (ξ, η) * ∏ m ∈ U'.erase j, T m (ξ, η) ∂γ)
    (J U : Finset (Fin k)) (hUJ : U ⊆ J) (hne : U.Nonempty) :
    Integrable (fun x => (∏ i ∈ U, T i x) * ∏ i ∈ J \ U, W i x.1) (ρ.prod γ) ∧
    |∫ x, (∏ i ∈ U, T i x) * ∏ i ∈ J \ U, W i x.1 ∂(ρ.prod γ)| ≤
      (k : ℝ) * ((1 + 2 * (k : ℝ)) * (4 * ε * τ ^ J.card)) := by
  classical
  have hτ0 : 0 < τ := by linarith
  have hJk : J.card ≤ k := by simpa using Finset.card_le_univ J
  obtain ⟨i₀, hi₀⟩ := hne
  have hi₀J := hUJ hi₀
  have hsplit : ∀ (x : Ω × E) (J' U' : Finset (Fin k)), U' ⊆ J' →
      ∏ i ∈ J', (if i ∈ U' then T i x else W i x.1) = (∏ i ∈ U', T i x) * ∏ i ∈ J' \ U', W i x.1 := by
    intro x J' U' h
    rw [Finset.prod_ite]
    have e1 : J'.filter (· ∈ U') = U' := by
      ext i
      simp only [Finset.mem_filter]
      exact ⟨fun h' => h'.2, fun h' => ⟨h h', h'⟩⟩
    have e2 : J'.filter (· ∉ U') = J' \ U' := by
      ext i
      simp [Finset.mem_sdiff]
    rw [e1, e2]
  have I0 : Integrable (fun x => (∏ i ∈ U, T i x) * ∏ i ∈ J \ U, W i x.1) (ρ.prod γ) := by
    have h := (MomentBounded.prod (J := J) (f := fun i x => if i ∈ U then T i x else W i x.1)
      (B := fun _ => τ)
      (fun _ _ => hτ0) (fun i _ => by
        by_cases hi : i ∈ U
        · simpa only [if_pos hi] using sT i
        · simpa only [if_neg hi] using sW i) hJk).1
    exact h.congr (Filter.Eventually.of_forall fun x => hsplit x J U hUJ)
  refine ⟨I0, ?_⟩
  let U' := U.erase i₀
  let H : Fin k → ι → ι → Ω × E → ℝ := fun j b c x =>
    (U₀ i₀ b x * V₀ j c x * ∏ m ∈ U'.erase j, T m x) * ∏ i ∈ J \ U, W i x.1
  have hjJ : ∀ j ∈ U', j ∈ J ∧ j ≠ i₀ := fun j hj =>
    ⟨hUJ (Finset.mem_of_mem_erase hj), Finset.ne_of_mem_erase hj⟩
  have hF : ∀ j ∈ U', ∀ (b c : ι), Integrable (H j b c) (ρ.prod γ) ∧
      |∫ x, H j b c x ∂(ρ.prod γ)| ≤ (1 + 2 * (k : ℝ)) * (4 * w i₀ b * w j c * τ ^ J.card) := by
    intro j hj b c
    obtain ⟨hjm, hjne⟩ := hjJ j hj
    let F : Fin k → Ω × E → ℝ := fun i x =>
      if i = i₀ then U₀ i₀ b x else if i = j then V₀ j c x else if i ∈ U then T i x else W i x.1
    let Bd : Fin k → ℝ := fun i => if i = i₀ then 4 * w i₀ b else if i = j then w j c else τ
    have hmem : j ∈ J.erase i₀ := Finset.mem_erase.2 ⟨hjne, hjm⟩
    have hprod : ∀ x, ∏ i ∈ J, F i x = H j b c x := by
      intro x
      rw [← Finset.mul_prod_erase J _ hi₀J, ← Finset.mul_prod_erase (J.erase i₀) _ hmem]
      have e1 : F i₀ x = U₀ i₀ b x := by simp [F]
      have e2 : F j x = V₀ j c x := by simp [F, hjne]
      have e3 : ∏ i ∈ (J.erase i₀).erase j, F i x =
          ∏ i ∈ (J.erase i₀).erase j, (if i ∈ U'.erase j then T i x else W i x.1) := by
        refine Finset.prod_congr rfl fun i hi => ?_
        have h1 : i ≠ j := Finset.ne_of_mem_erase hi
        have h2 : i ≠ i₀ := Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hi)
        simp only [F, if_neg h1, if_neg h2]
        by_cases h3 : i ∈ U
        · have : i ∈ U'.erase j := Finset.mem_erase.2 ⟨h1, Finset.mem_erase.2 ⟨h2, h3⟩⟩
          simp [h3, this]
        · have : i ∉ U'.erase j := fun h => h3 (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase h))
          simp [h3, this]
      have hsub : U'.erase j ⊆ (J.erase i₀).erase j := by
        intro i hi
        have h1 := Finset.mem_erase.1 hi
        have h2 := Finset.mem_erase.1 h1.2
        exact Finset.mem_erase.2 ⟨h1.1, Finset.mem_erase.2 ⟨h2.1, hUJ h2.2⟩⟩
      have e4 : (J.erase i₀).erase j \ U'.erase j = J \ U := by
        ext i
        simp only [Finset.mem_sdiff, Finset.mem_erase, U']
        constructor
        · rintro ⟨⟨h1, h2, h3⟩, h4⟩
          exact ⟨h3, fun h => h4 ⟨h1, h2, h⟩⟩
        · rintro ⟨h1, h2⟩
          have hne1 : i ≠ j := fun h => h2 (by
            rw [h]
            exact Finset.mem_of_mem_erase hj)
          have hne2 : i ≠ i₀ := fun h => h2 (h ▸ hi₀)
          exact ⟨⟨hne1, hne2, h1⟩, fun h => h2 h.2.2⟩
      rw [e1, e2, e3, hsplit x _ _ hsub, e4]
      simp only [H]
      ring
    have hpos : ∀ i ∈ J, 0 < Bd i := by
      intro i _
      simp only [Bd]
      split_ifs
      · have := hw i₀ b
        positivity
      · exact hw j c
      · exact hτ0
    have hs : ∀ i ∈ J, MomentBounded k (ρ.prod γ) (F i) (Bd i) := by
      intro i _
      by_cases h1 : i = i₀
      · subst h1
        simpa only [F, Bd, if_true] using sU i b
      · by_cases h2 : i = j
        · subst h2
          simpa only [F, Bd, if_neg h1, if_true] using sV i c
        · by_cases h3 : i ∈ U
          · simpa only [F, Bd, if_neg h1, if_neg h2, if_pos h3] using sT i
          · simpa only [F, Bd, if_neg h1, if_neg h2, if_neg h3] using sW i
    have hres := MomentBounded.prod hpos hs hJk
    have hB : ∏ i ∈ J, Bd i ≤ 4 * w i₀ b * w j c * τ ^ J.card := by
      rw [← Finset.mul_prod_erase J _ hi₀J, ← Finset.mul_prod_erase (J.erase i₀) _ hmem]
      have e1 : Bd i₀ = 4 * w i₀ b := by simp [Bd]
      have e2 : Bd j = w j c := by simp [Bd, hjne]
      have e3 : ∏ i ∈ (J.erase i₀).erase j, Bd i ≤ τ ^ J.card := by
        have h1 : ∏ i ∈ (J.erase i₀).erase j, Bd i = τ ^ ((J.erase i₀).erase j).card := by
          rw [← Finset.prod_const]
          refine Finset.prod_congr rfl fun i hi => ?_
          have h1 : i ≠ j := Finset.ne_of_mem_erase hi
          have h2 : i ≠ i₀ := Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hi)
          simp [Bd, h1, h2]
        rw [h1]
        exact pow_le_pow_right₀ hτ
          ((Finset.card_le_card ((Finset.erase_subset _ _).trans (Finset.erase_subset _ _))))
      rw [e1, e2]
      have h4 := hw i₀ b
      have h5 := hw j c
      calc 4 * w i₀ b * (w j c * ∏ i ∈ (J.erase i₀).erase j, Bd i)
          ≤ 4 * w i₀ b * (w j c * τ ^ J.card) := by gcongr
        _ = _ := by ring
    refine ⟨hres.1.congr (Filter.Eventually.of_forall hprod), ?_⟩
    have e : ∫ x, H j b c x ∂(ρ.prod γ) = ∫ x, ∏ i ∈ J, F i x ∂(ρ.prod γ) :=
      integral_congr_ae (Filter.Eventually.of_forall fun x => (hprod x).symm)
    rw [e]
    refine hres.2.trans (mul_le_mul_of_nonneg_left hB (by positivity))
  have hmain : ∫ x, (∏ i ∈ U, T i x) * ∏ i ∈ J \ U, W i x.1 ∂(ρ.prod γ) =
      ∑ j ∈ U', ∑ b, ∑ c, G b c * ∫ x, H j b c x ∂(ρ.prod γ) := by
    rw [integral_prod _ I0]
    have hin : ∀ ξ, ∫ η, (∏ i ∈ U, T i (ξ, η)) * ∏ i ∈ J \ U, W i ξ ∂γ =
        ∑ j ∈ U', ∑ b, ∑ c, G b c * ∫ η, H j b c (ξ, η) ∂γ := by
      intro ξ
      rw [integral_mul_const]
      have e1 : ∫ η, ∏ i ∈ U, T i (ξ, η) ∂γ = ∫ η, T i₀ (ξ, η) * ∏ j ∈ U', T j (ξ, η) ∂γ :=
        integral_congr_ae (Filter.Eventually.of_forall fun η => by
          simp only [U']
          rw [Finset.mul_prod_erase U (fun i => T i (ξ, η)) hi₀])
      rw [e1, stein ξ i₀ U', Finset.sum_mul]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun c _ => ?_
      simp only [H]
      rw [integral_mul_const, mul_assoc]
    simp only [hin]
    rw [integral_finset_sum]
    · refine Finset.sum_congr rfl fun j hj => ?_
      rw [integral_finset_sum]
      · refine Finset.sum_congr rfl fun b _ => ?_
        rw [integral_finset_sum]
        · refine Finset.sum_congr rfl fun c _ => ?_
          rw [integral_const_mul, integral_prod _ (hF j hj b c).1]
        · exact fun c _ => ((hF j hj b c).1.integral_prod_left).const_mul _
      · exact fun b _ => integrable_finset_sum _ fun c _ => ((hF j hj b c).1.integral_prod_left).const_mul _
    · exact fun j hj => integrable_finset_sum _ fun b _ => integrable_finset_sum _ fun c _ =>
        ((hF j hj b c).1.integral_prod_left).const_mul _
  rw [hmain]
  have hterm : ∀ j ∈ U', |∑ b, ∑ c, G b c * ∫ x, H j b c x ∂(ρ.prod γ)| ≤
      (1 + 2 * (k : ℝ)) * (4 * ε * τ ^ J.card) := by
    intro j hj
    have hne' : i₀ ≠ j := fun h => (hjJ j hj).2 h.symm
    calc |∑ b, ∑ c, G b c * ∫ x, H j b c x ∂(ρ.prod γ)|
        ≤ ∑ b, ∑ c, |G b c| * ((1 + 2 * (k : ℝ)) * (4 * w i₀ b * w j c * τ ^ J.card)) := by
          refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun b _ => ?_)
          refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun c _ => ?_)
          rw [abs_mul]
          exact mul_le_mul_of_nonneg_left (hF j hj b c).2 (abs_nonneg _)
      _ = (1 + 2 * (k : ℝ)) * (4 * (∑ b, ∑ c, w i₀ b * |G b c| * w j c) * τ ^ J.card) := by
          simp only [Finset.mul_sum, Finset.sum_mul]
          refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun c _ => ?_
          ring
      _ ≤ _ := by
          have := hε i₀ j hne'
          have h6 : (0 : ℝ) ≤ τ ^ J.card := by positivity
          gcongr
  calc |∑ j ∈ U', ∑ b, ∑ c, G b c * ∫ x, H j b c x ∂(ρ.prod γ)|
      ≤ ∑ j ∈ U', (1 + 2 * (k : ℝ)) * (4 * ε * τ ^ J.card) :=
        (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum hterm)
    _ = (U'.card : ℝ) * ((1 + 2 * (k : ℝ)) * (4 * ε * τ ^ J.card)) := by simp
    _ ≤ _ := by
        have : (U'.card : ℝ) ≤ k := by
          have := Finset.card_le_univ U'
          simp only [Fintype.card_fin] at this
          exact_mod_cast this
        have h6 : (0 : ℝ) ≤ τ ^ J.card := by positivity
        gcongr
end Blocks
section Main
open MvPolynomial Matrix
open scoped MatrixOrder
private theorem abs_prod_sub_prod_le_card_mul {α : Type} [DecidableEq α] (s : Finset α) (a b u : α → ℝ)
    (w : ℝ) (hw : 0 ≤ w)
    (ha : ∀ i ∈ s, |a i| ≤ u i) (hb : ∀ i ∈ s, |b i| ≤ u i) (hd : ∀ i ∈ s, |a i - b i| ≤ w * u i) :
    |∏ i ∈ s, a i - ∏ i ∈ s, b i| ≤ (s.card : ℝ) * w * ∏ i ∈ s, u i := by apply _root_.YangMills.SharedProofs.p34157 <;> assumption
private lemma abs_integral_pow_le_integral {E : Type} [MeasurableSpace E] {γ : Measure E}
    [IsProbabilityMeasure γ] {f : E → ℝ} {k : ℕ}
    (hf : Integrable f γ) (hk : Integrable (fun η => |f η| ^ k) γ) :
    |∫ η, f η ∂γ| ^ k ≤ ∫ η, |f η| ^ k ∂γ := by
  have h := (convexOn_pow (𝕜 := ℝ) k).map_integral_le (f := fun η => |f η|) (μ := γ)
    (continuous_pow k).continuousOn isClosed_Ici
    (Filter.Eventually.of_forall fun η => Set.mem_Ici.2 (abs_nonneg _)) hf.abs hk
  exact (pow_le_pow_left₀ (abs_nonneg _) (abs_integral_le_integral_abs) k).trans h
variable {Ω ι : Type} [MeasurableSpace Ω] [Fintype ι] [DecidableEq ι]
private lemma integral_coord_multivariateGaussian {G : Matrix ι ι ℝ} (hG : G.PosSemidef) (b : ι) :
    ∫ η, (η : EuclideanSpace ℝ ι) b ∂(multivariateGaussian 0 G) = 0 := by
  have hA : (CFC.sqrt G).IsSymm := by
    have h1 : IsSelfAdjoint (CFC.sqrt G) := (CFC.sqrt_nonneg G).isSelfAdjoint
    have h2 : (CFC.sqrt G).conjTranspose = CFC.sqrt G := h1
    rw [Matrix.IsSymm, ← Matrix.conjTranspose_eq_transpose_of_trivial, h2]
  have hAA : CFC.sqrt G * CFC.sqrt G = G := CFC.sqrt_mul_sqrt_self _ hG.nonneg
  have h := (integral_eval_multivariateGaussian G (X b * 1 : MvPolynomial ι ℝ)).2
  rw [gaussianMeanAt_X_mul hA hAA] at h
  simpa using h
private def gaussianStepConstant (k : ℕ) : ℝ :=
  ∑ π : Finpartition (Finset.univ : Finset (Fin k)),
    ((π.parts.card - 1).factorial : ℝ) * (π.parts.card : ℝ) * (1 + 2 * (k : ℝ)) ^ π.parts.card *
      (2 ^ k * ((k : ℝ) * ((1 + 2 * (k : ℝ)) * 4)) * (34 * (1 + 2 * (k : ℝ))) ^ k)
private lemma gaussianStepConstant_nonneg (k : ℕ) : 0 ≤ gaussianStepConstant k :=
  Finset.sum_nonneg fun _ _ => by positivity
private theorem abs_jointCumulant_sub_le {k : ℕ} (hk : 2 ≤ k) (ρ : Measure Ω) [IsProbabilityMeasure ρ]
    (G : Matrix ι ι ℝ) (S : Fin k → Matrix ι ι ℝ) (W : Fin k → Ω → ℝ) (l : Fin k → Ω → ι → ℝ)
    (c : Fin k → ℝ) (w : Fin k → ι → ℝ) (A ε : ℝ)
    (hG : G.PosSemidef) (hS : ∀ i, (S i).IsSymm) (hA : 1 ≤ A) (hw : ∀ i b, 0 < w i b)
    (hWm : ∀ i, Measurable (W i)) (hlm : ∀ i b, Measurable fun ξ => l i ξ b)
    (hW : ∀ i, Integrable (fun ξ => |W i ξ| ^ k) ρ ∧ ∫ ξ, |W i ξ| ^ k ∂ρ ≤ A ^ k)
    (hΦ : ∀ i, Integrable (fun x => |gaussianStepQuadratic (S i) (W i) (l i) (c i) x| ^ k)
          (ρ.prod (multivariateGaussian 0 G)) ∧
        ∫ x, |gaussianStepQuadratic (S i) (W i) (l i) (c i) x| ^ k ∂(ρ.prod (multivariateGaussian 0 G)) ≤ A ^ k)
    (hv : ∀ i b, Integrable (fun x => |gaussianStepGradient (S i) (l i) b x| ^ k)
          (ρ.prod (multivariateGaussian 0 G)) ∧
        ∫ x, |gaussianStepGradient (S i) (l i) b x| ^ k ∂(ρ.prod (multivariateGaussian 0 G)) ≤ w i b ^ k)
    (hε : ∀ i j, i ≠ j → ∑ b, ∑ b', w i b * |G b b'| * w j b' ≤ ε) :
    |jointCumulant (ρ.prod (multivariateGaussian 0 G)) (fun i => gaussianStepQuadratic (S i) (W i) (l i) (c i)) -
        jointCumulant ρ W| ≤ gaussianStepConstant k * A ^ k * ε := by
  obtain ⟨γ, hγ⟩ : ∃ γ, γ = multivariateGaussian (0 : EuclideanSpace ℝ ι) G := ⟨_, rfl⟩
  rw [← hγ] at hΦ hv ⊢
  haveI : IsProbabilityMeasure γ := hγ ▸ inferInstance
  have hk0 : k ≠ 0 := by omega
  have hk1 : 1 ≤ k := by omega
  obtain ⟨K₁, hK₁⟩ : ∃ K₁ : ℝ, K₁ = 1 + 2 * (k : ℝ) := ⟨_, rfl⟩
  have hK1 : 1 ≤ K₁ := by
    rw [hK₁]
    have : (0 : ℝ) ≤ k := by positivity
    linarith
  have hA0 : 0 < A := by linarith
  have hε₀ : 0 ≤ ε := by
    have i₀ : Fin k := ⟨0, by omega⟩
    have h01 : (⟨0, by omega⟩ : Fin k) ≠ ⟨1, by omega⟩ := by simp [Fin.ext_iff]
    refine le_trans ?_ (hε _ _ h01)
    exact Finset.sum_nonneg fun b _ => Finset.sum_nonneg fun c _ =>
      mul_nonneg (mul_nonneg (hw _ b).le (abs_nonneg _)) (hw _ c).le
  let Tf : Fin k → Ω × EuclideanSpace ℝ ι → ℝ := fun i x =>
    eval (fun b => x.2 b) (centeredQuadPoly G (l i x.1) (S i))
  let Uf : Fin k → ι → Ω × EuclideanSpace ℝ ι → ℝ := fun i b x =>
    eval (fun b => x.2 b) (halfGradPoly (l i x.1) (S i) b)
  let Vf : Fin k → ι → Ω × EuclideanSpace ℝ ι → ℝ := fun i b => gaussianStepGradient (S i) (l i) b
  have hVe : ∀ i b x, eval (fun b => x.2 b) (gradPoly (l i x.1) (S i) b) = Vf i b x := by
    intro i b x
    simp [gradPoly, Vf, gaussianStepGradient]
  have hUe : ∀ i b x, Uf i b x = (1 / 2) * (Vf i b x + l i x.1 b) := by
    intro i b x
    simp only [Uf, Vf, halfGradPoly, gaussianStepGradient, map_add, map_mul, map_sum, eval_C, eval_X]
    ring
  have hTe : ∀ i x, Tf i x = ∑ b, l i x.1 b * x.2 b + (1 / 2) * ∑ b, ∑ b', S i b b' * x.2 b * x.2 b' -
      (1 / 2) * (S i * G).trace := by
    intro i x
    simp only [Tf, centeredQuadPoly, quadraticFormPoly, map_sub, map_add, map_mul, map_sum, eval_C, eval_X,
      mul_assoc]
  obtain ⟨n, hn⟩ : ∃ n : Fin k → ℝ, n = fun i => c i + (1 / 2) * (S i * G).trace := ⟨_, rfl⟩
  have hΦe : ∀ i x, gaussianStepQuadratic (S i) (W i) (l i) (c i) x = (Tf i x + W i x.1) + n i := by
    intro i x
    rw [hTe, hn]
    simp only [gaussianStepQuadratic]
    ring
  have hxb : ∀ b, Measurable fun x : Ω × EuclideanSpace ℝ ι => x.2 b := fun b => by fun_prop
  have hmL : ∀ i b, Measurable fun x : Ω × EuclideanSpace ℝ ι => l i x.1 b :=
    fun i b => (hlm i b).comp measurable_fst
  have hmV : ∀ i b, Measurable (Vf i b) := fun i b =>
    (hmL i b).add (Finset.measurable_fun_sum _ fun b' _ => (hxb b').const_mul _)
  have hmT : ∀ i, Measurable (Tf i) := by
    intro i
    have : Tf i = fun x => ∑ b, l i x.1 b * x.2 b + (1 / 2) * ∑ b, ∑ b', S i b b' * x.2 b * x.2 b' -
      (1 / 2) * (S i * G).trace := funext (hTe i)
    rw [this]
    refine ((Finset.measurable_fun_sum _ fun b _ => (hmL i b).mul (hxb b)).add
      ((Finset.measurable_fun_sum _ fun b _ => Finset.measurable_fun_sum _ fun b' _ =>
        ((hxb b).const_mul _).mul (hxb b')).const_mul _)).sub measurable_const
  have hmW : ∀ i, Measurable fun x : Ω × EuclideanSpace ℝ ι => W i x.1 := fun i => (hWm i).comp measurable_fst
  have hmΦ : ∀ i, Measurable (gaussianStepQuadratic (S i) (W i) (l i) (c i)) := by
    intro i
    have : gaussianStepQuadratic (S i) (W i) (l i) (c i) = fun x => (Tf i x + W i x.1) + n i :=
      funext (hΦe i)
    rw [this]
    exact ((hmT i).add (hmW i)).add measurable_const
  have hmap : (ρ.prod γ).map Prod.fst = ρ := by
    rw [Measure.map_fst_prod]
    simp
  have fst_int : ∀ f : Ω → ℝ, Measurable f → ∫ x, f x.1 ∂(ρ.prod γ) = ∫ ξ, f ξ ∂ρ := by
    intro f hf
    have h := integral_map (μ := ρ.prod γ) measurable_fst.aemeasurable hf.aestronglyMeasurable
    rw [hmap] at h
    exact h.symm
  have fst_integrable : ∀ f : Ω → ℝ, Measurable f → Integrable f ρ →
      Integrable (fun x : Ω × EuclideanSpace ℝ ι => f x.1) (ρ.prod γ) := by
    intro f hf h
    rw [← hmap] at h
    exact (integrable_map_measure hf.aestronglyMeasurable measurable_fst.aemeasurable).1 h
  have sW : ∀ i, MomentBounded k (ρ.prod γ) (fun x => W i x.1) A := by
    intro i
    refine ⟨hmW i, fst_integrable (fun ξ => |W i ξ| ^ k) (((hWm i).abs).pow_const k) (hW i).1, ?_⟩
    rw [fst_int (fun ξ => |W i ξ| ^ k) (((hWm i).abs).pow_const k)]
    exact (hW i).2
  have sW₀ : ∀ i, MomentBounded k ρ (W i) A := fun i => ⟨hWm i, (hW i).1, (hW i).2⟩
  have sΦ : ∀ i, MomentBounded k (ρ.prod γ) (gaussianStepQuadratic (S i) (W i) (l i) (c i)) A :=
    fun i => ⟨hmΦ i, (hΦ i).1, (hΦ i).2⟩
  have sV : ∀ i b, MomentBounded k (ρ.prod γ) (Vf i b) (w i b) :=
    fun i b => ⟨hmV i b, (hv i b).1, (hv i b).2⟩
  have hVint : ∀ i b ξ, Integrable (fun η => Vf i b (ξ, η)) γ ∧ ∫ η, Vf i b (ξ, η) ∂γ = l i ξ b := by
    intro i b ξ
    have h1 := integral_eval_multivariateGaussian G (gradPoly (l i ξ) (S i) b)
    rw [← hγ] at h1
    have e : ∀ η : EuclideanSpace ℝ ι, eval (fun b => η b) (gradPoly (l i ξ) (S i) b) = Vf i b (ξ, η) :=
      fun η => hVe i b (ξ, η)
    simp only [e] at h1
    refine ⟨h1.1, ?_⟩
    have hc : ∀ b', Integrable (fun η : EuclideanSpace ℝ ι => η b') γ ∧
        ∫ η : EuclideanSpace ℝ ι, η b' ∂γ = 0 := by
      intro b'
      have h2 := (integral_eval_multivariateGaussian G (X b' : MvPolynomial ι ℝ)).1
      rw [← hγ] at h2
      simp only [eval_X] at h2
      refine ⟨h2, ?_⟩
      rw [hγ]
      exact integral_coord_multivariateGaussian hG b'
    simp only [Vf, gaussianStepGradient]
    rw [integral_add (integrable_const _) (integrable_finset_sum _ fun b' _ => (hc b').1.const_mul _),
      integral_finset_sum _ fun b' _ => (hc b').1.const_mul _]
    simp [integral_const_mul, (hc _).2]
  have sL : ∀ i b, MomentBounded k (ρ.prod γ) (fun x => l i x.1 b) (w i b) := by
    intro i b
    have hpt : ∀ᵐ ξ ∂ρ, |l i ξ b| ^ k ≤ ∫ η, |Vf i b (ξ, η)| ^ k ∂γ := by
      filter_upwards [(hv i b).1.prod_right_ae] with ξ hξ
      have h := abs_integral_pow_le_integral (hVint i b ξ).1 hξ
      rwa [(hVint i b ξ).2] at h
    have hdom : Integrable (fun ξ => ∫ η, |Vf i b (ξ, η)| ^ k ∂γ) ρ := (hv i b).1.integral_prod_left
    have hm : Measurable fun ξ => |l i ξ b| ^ k := ((hlm i b).abs).pow_const k
    have hint : Integrable (fun ξ => |l i ξ b| ^ k) ρ :=
      hdom.mono' hm.aestronglyMeasurable (hpt.mono fun ξ h => by
        rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
        exact h)
    refine ⟨hmL i b, fst_integrable _ hm hint, ?_⟩
    rw [fst_int (fun ξ => |l i ξ b| ^ k) hm]
    refine (integral_mono_ae hint hdom hpt).trans ?_
    rw [← integral_prod (fun x => |Vf i b x| ^ k) (hv i b).1]
    exact (hv i b).2
  have sU : ∀ i b, MomentBounded k (ρ.prod γ) (Uf i b) (4 * w i b) := by
    intro i b
    have h1 := MomentBounded.add hk0 (hw i b).le (hw i b).le (sV i b) (sL i b)
    have h2 := h1.mul_const (1 / 2) (by norm_num [abs_of_pos]) (by have := hw i b; positivity)
    have e : Uf i b = fun x => (1 / 2) * (Vf i b x + l i x.1 b) := funext (hUe i b)
    rw [e]
    exact h2.mono (by have := hw i b; positivity) (by linarith)
  have hst : ∀ (ξ : Ω) (i₀ : Fin k) (U' : Finset (Fin k)),
      ∫ η, Tf i₀ (ξ, η) * ∏ j ∈ U', Tf j (ξ, η) ∂γ =
        ∑ j ∈ U', ∑ b, ∑ c, G b c *
          ∫ η, Uf i₀ b (ξ, η) * Vf j c (ξ, η) * ∏ m ∈ U'.erase j, Tf m (ξ, η) ∂γ := by
    intro ξ i₀ U'
    have h := integral_centeredQuadPoly_mul_prod G hG (fun i => l i ξ) S hS i₀ U'
    rw [← hγ] at h
    simp only [map_mul, map_prod] at h
    have e : ∀ (j : Fin k) (c : ι) (η : EuclideanSpace ℝ ι),
        eval (fun b => η b) (gradPoly (l j ξ) (S j) c) = Vf j c (ξ, η) := fun j c η => hVe j c (ξ, η)
    simp only [e] at h
    exact h
  have sAbs : ∀ {μ' : Measure (Ω × EuclideanSpace ℝ ι)} [IsProbabilityMeasure μ']
      {f : Ω × EuclideanSpace ℝ ι → ℝ} {B : ℝ},
      0 < B → MomentBounded k μ' f B → Integrable f μ' ∧ |∫ x, f x ∂μ'| ≤ K₁ * B := by
    intro μ' _ f B hB hf
    have h := MomentBounded.prod (μ := μ') (k := k) (J := ({()} : Finset Unit)) (f := fun _ => f)
      (B := fun _ => B) (fun _ _ => hB) (fun _ _ => hf) (by simpa using hk1)
    simp only [Finset.prod_singleton] at h
    rw [hK₁]
    exact h
  have hT0 : ∀ i ξ, ∫ η, Tf i (ξ, η) ∂γ = 0 := by
    intro i ξ
    have h := hst ξ i ∅
    simpa using h
  have hTint : ∀ i, Integrable (Tf i) (ρ.prod γ) := by
    intro i
    have h1 := (sAbs hA0 (sΦ i)).1
    have h2 := (sAbs hA0 (sW i)).1
    have e : Tf i = fun x => gaussianStepQuadratic (S i) (W i) (l i) (c i) x - W i x.1 - n i := by
      funext x
      rw [hΦe]
      ring
    rw [e]
    exact (h1.sub h2).sub (integrable_const _)
  have hnb : ∀ i, |n i| ≤ 2 * K₁ * A := by
    intro i
    have h1 := sAbs hA0 (sΦ i)
    have h2 := sAbs hA0 (sW i)
    have hz : ∫ x, Tf i x ∂(ρ.prod γ) = 0 := by
      rw [integral_prod _ (hTint i)]
      simp [hT0]
    have e : ∫ x, gaussianStepQuadratic (S i) (W i) (l i) (c i) x ∂(ρ.prod γ) =
        ∫ x, W i x.1 ∂(ρ.prod γ) + n i := by
      simp only [hΦe]
      have hi : Integrable (fun x => Tf i x + W i x.1) (ρ.prod γ) := (hTint i).add h2.1
      have e1 : ∫ x, (Tf i x + W i x.1) + n i ∂(ρ.prod γ) =
          (∫ x, Tf i x + W i x.1 ∂(ρ.prod γ)) + ∫ _x, n i ∂(ρ.prod γ) :=
        integral_add hi (integrable_const _)
      have e2 : ∫ x, Tf i x + W i x.1 ∂(ρ.prod γ) =
          (∫ x, Tf i x ∂(ρ.prod γ)) + ∫ x, W i x.1 ∂(ρ.prod γ) :=
        integral_add (hTint i) h2.1
      rw [e1, e2, hz]
      simp
    have e2 : n i = ∫ x, gaussianStepQuadratic (S i) (W i) (l i) (c i) x ∂(ρ.prod γ) -
        ∫ x, W i x.1 ∂(ρ.prod γ) := by
      rw [e]
      ring
    rw [e2]
    calc _ ≤ |∫ x, gaussianStepQuadratic (S i) (W i) (l i) (c i) x ∂(ρ.prod γ)| +
          |∫ x, W i x.1 ∂(ρ.prod γ)| := abs_sub _ _
      _ ≤ K₁ * A + K₁ * A := add_le_add h1.2 h2.2
      _ = _ := by ring
  obtain ⟨τ, hτdef⟩ : ∃ τ : ℝ, τ = 16 * K₁ * A := ⟨_, rfl⟩
  have hKA : 1 ≤ K₁ * A := by nlinarith
  have hτ1 : 1 ≤ τ := by rw [hτdef]; nlinarith
  have hτ0 : 0 < τ := by linarith
  have hAτ : A ≤ τ := by rw [hτdef]; nlinarith
  have sT : ∀ i, MomentBounded k (ρ.prod γ) (Tf i) τ := by
    intro i
    have h1 := (sW i).mul_const (-1) (by simp) hA0.le
    have h2 := MomentBounded.add hk0 hA0.le hA0.le (sΦ i) h1
    have hc : |-(n i)| ≤ 2 * K₁ * A := by rw [abs_neg]; exact hnb i
    have h3 := MomentBounded.add hk0 (by positivity) (by positivity) h2
      (MomentBounded.const (μ := ρ.prod γ) (k := k) (-(n i)) hc)
    have e : Tf i = fun x => (gaussianStepQuadratic (S i) (W i) (l i) (c i) x + -1 * W i x.1) + -(n i) := by
      funext x
      rw [hΦe]
      ring
    rw [e]
    refine h3.mono (by positivity) ?_
    rw [hτdef]
    nlinarith
  have sWτ : ∀ i, MomentBounded k (ρ.prod γ) (fun x => W i x.1) τ := fun i => (sW i).mono hA0.le hAτ
  obtain ⟨X, hX⟩ : ∃ X : Fin k → Ω × EuclideanSpace ℝ ι → ℝ, X = fun i x => Tf i x + W i x.1 := ⟨_, rfl⟩
  obtain ⟨σ₀, hσ₀⟩ : ∃ σ₀ : ℝ, σ₀ = 34 * K₁ * A := ⟨_, rfl⟩
  have hσpos : 0 < σ₀ := by rw [hσ₀]; nlinarith
  have sX : ∀ i, MomentBounded k (ρ.prod γ) (X i) σ₀ := by
    intro i
    have h := MomentBounded.add hk0 hτ0.le hA0.le (sT i) (sW i)
    rw [hX]
    refine h.mono (by positivity) ?_
    rw [hσ₀, hτdef]
    nlinarith
  have hτσ : τ ≤ σ₀ := by rw [hσ₀, hτdef]; nlinarith
  have hAσ : A ≤ σ₀ := hAτ.trans hτσ
  have hJcard : ∀ J : Finset (Fin k), J.card ≤ k := fun J => by simpa using Finset.card_le_univ J
  have hshift : jointCumulant (ρ.prod γ) (fun i => gaussianStepQuadratic (S i) (W i) (l i) (c i)) =
      jointCumulant (ρ.prod γ) X := by
    have e : (fun i => gaussianStepQuadratic (S i) (W i) (l i) (c i)) = fun i x => X i x + n i := by
      funext i x
      rw [hΦe, hX]
    rw [e]
    refine jointCumulant_add_const hk X n fun a D => ?_
    refine (MomentBounded.prod (J := D) (f := fun j x => X j x + a j) (B := fun j => 2 * (σ₀ + (|a j| + 1)))
      (fun j _ => by positivity) (fun j _ => ?_) (hJcard D)).1
    exact MomentBounded.add hk0 hσpos.le (by positivity) (sX j) (MomentBounded.const (a j) (by linarith))
  rw [hshift]
  obtain ⟨u, hu⟩ : ∃ u : Finset (Fin k) → ℝ, u = fun J => K₁ * σ₀ ^ J.card := ⟨_, rfl⟩
  obtain ⟨w₀, hw₀⟩ : ∃ w₀ : ℝ, w₀ = 2 ^ k * ((k : ℝ) * (K₁ * 4)) * ε := ⟨_, rfl⟩
  have hw₀0 : 0 ≤ w₀ := by rw [hw₀]; positivity
  have ha : ∀ J : Finset (Fin k), |∫ x, ∏ i ∈ J, X i x ∂(ρ.prod γ)| ≤ u J := by
    intro J
    have h := (MomentBounded.prod (J := J) (f := X) (B := fun _ => σ₀) (fun _ _ => hσpos)
      (fun j _ => sX j) (hJcard J)).2
    rw [hu]
    simpa only [Finset.prod_const, hK₁] using h
  have hb : ∀ J : Finset (Fin k), |∫ ξ, ∏ i ∈ J, W i ξ ∂ρ| ≤ u J := by
    intro J
    have h := (MomentBounded.prod (J := J) (f := W) (B := fun _ => σ₀) (fun _ _ => hσpos)
      (fun j _ => (sW₀ j).mono hA0.le hAσ) (hJcard J)).2
    rw [hu]
    simpa only [Finset.prod_const, hK₁] using h
  have hd : ∀ J : Finset (Fin k),
      |∫ x, ∏ i ∈ J, X i x ∂(ρ.prod γ) - ∫ ξ, ∏ i ∈ J, W i ξ ∂ρ| ≤ w₀ * u J := by
    intro J
    have hblock := fun U (hU : U ∈ J.powerset.erase ∅) =>
      abs_integral_block_le (ρ := ρ) (γ := γ) Tf W Uf Vf (fun b c => G b c) τ ε w hτ1 hε₀ hw
        sT sWτ sU sV hε hst J U (Finset.mem_powerset.1 (Finset.mem_of_mem_erase hU))
        (Finset.nonempty_iff_ne_empty.2 (Finset.ne_of_mem_erase hU))
    have hW0 : Integrable (fun x : Ω × EuclideanSpace ℝ ι => ∏ i ∈ J, W i x.1) (ρ.prod γ) :=
      (MomentBounded.prod (J := J) (f := fun i (x : Ω × EuclideanSpace ℝ ι) => W i x.1) (B := fun _ => τ)
        (fun _ _ => hτ0) (fun i _ => sWτ i) (hJcard J)).1
    have hexp : ∀ x, ∏ i ∈ J, X i x = ∏ i ∈ J, W i x.1 +
        ∑ U ∈ J.powerset.erase ∅, (∏ i ∈ U, Tf i x) * ∏ i ∈ J \ U, W i x.1 := by
      intro x
      rw [hX]
      simp only
      rw [Finset.prod_add, ← Finset.add_sum_erase _ _ (Finset.empty_mem_powerset J)]
      simp
    have e : ∫ x, ∏ i ∈ J, X i x ∂(ρ.prod γ) - ∫ ξ, ∏ i ∈ J, W i ξ ∂ρ =
        ∑ U ∈ J.powerset.erase ∅, ∫ x, (∏ i ∈ U, Tf i x) * ∏ i ∈ J \ U, W i x.1 ∂(ρ.prod γ) := by
      simp only [hexp]
      rw [integral_add hW0 (integrable_finset_sum _ fun U hU => (hblock U hU).1),
        integral_finset_sum _ fun U hU => (hblock U hU).1,
        fst_int (fun ξ => ∏ i ∈ J, W i ξ) (Finset.measurable_fun_prod _ fun i _ => hWm i)]
      ring
    rw [e]
    have hcard : ((J.powerset.erase ∅).card : ℝ) ≤ 2 ^ k := by
      have h1 : (J.powerset.erase ∅).card ≤ 2 ^ J.card := by
        refine (Finset.card_le_card (Finset.erase_subset _ _)).trans ?_
        rw [Finset.card_powerset]
      have h2 : 2 ^ J.card ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (hJcard J)
      exact_mod_cast h1.trans h2
    have hτJ : τ ^ J.card ≤ u J := by
      rw [hu]
      calc τ ^ J.card ≤ σ₀ ^ J.card := pow_le_pow_left₀ hτ0.le hτσ _
        _ ≤ K₁ * σ₀ ^ J.card := le_mul_of_one_le_left (by positivity) hK1
    calc |∑ U ∈ J.powerset.erase ∅, ∫ x, (∏ i ∈ U, Tf i x) * ∏ i ∈ J \ U, W i x.1 ∂(ρ.prod γ)|
        ≤ ∑ U ∈ J.powerset.erase ∅, (k : ℝ) * ((1 + 2 * (k : ℝ)) * (4 * ε * τ ^ J.card)) :=
          (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun U hU => (hblock U hU).2)
      _ = ((J.powerset.erase ∅).card : ℝ) * ((k : ℝ) * (K₁ * 4)) * ε * τ ^ J.card := by
          rw [Finset.sum_const, nsmul_eq_mul, ← hK₁]
          ring
      _ ≤ 2 ^ k * ((k : ℝ) * (K₁ * 4)) * ε * τ ^ J.card := by gcongr
      _ ≤ 2 ^ k * ((k : ℝ) * (K₁ * 4)) * ε * u J := by gcongr
      _ = w₀ * u J := by rw [hw₀]
  unfold jointCumulant gaussianStepConstant
  rw [← Finset.sum_sub_distrib, Finset.sum_mul, Finset.sum_mul]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun π _ => ?_)
  have hsum : ∑ J ∈ π.parts, J.card = k := by
    simpa using π.sum_card_parts
  obtain ⟨p, hp⟩ : ∃ p, p = π.parts.card := ⟨_, rfl⟩
  have hbound := abs_prod_sub_prod_le_card_mul π.parts (fun J => ∫ x, ∏ i ∈ J, X i x ∂(ρ.prod γ))
    (fun J => ∫ ξ, ∏ i ∈ J, W i ξ ∂ρ) u w₀ hw₀0 (fun J _ => ha J) (fun J _ => hb J) (fun J _ => hd J)
  have hU : ∏ J ∈ π.parts, u J = K₁ ^ p * σ₀ ^ k := by
    rw [hu, Finset.prod_mul_distrib, Finset.prod_const, Finset.prod_pow_eq_pow_sum, hsum, hp]
  rw [hU, ← hp] at hbound
  rw [← mul_sub, abs_mul, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul, Nat.abs_cast, ← hp, ← hK₁]
  have hf : (0 : ℝ) ≤ ((p - 1).factorial : ℝ) := by positivity
  calc ((p - 1).factorial : ℝ) *
        |∏ J ∈ π.parts, ∫ x, ∏ i ∈ J, X i x ∂(ρ.prod γ) - ∏ J ∈ π.parts, ∫ ξ, ∏ i ∈ J, W i ξ ∂ρ|
      ≤ ((p - 1).factorial : ℝ) * ((p : ℝ) * w₀ * (K₁ ^ p * σ₀ ^ k)) := mul_le_mul_of_nonneg_left hbound hf
    _ = _ := by
        rw [hw₀, hσ₀, mul_pow, mul_pow]
        ring
end Main
end GaussianStepCumulant
theorem cumulantAcrossGaussianStep : cumulantAcrossGaussianStepStatement := by
  intro k hk
  refine ⟨GaussianStepCumulant.gaussianStepConstant k, GaussianStepCumulant.gaussianStepConstant_nonneg k, ?_⟩
  intro Ω ι _ _ _ ρ _ G S W l c w A ε hG hS hA hw hWm hlm hW hΦ hv hε
  exact GaussianStepCumulant.abs_jointCumulant_sub_le (by omega) ρ G S W l c w A ε hG hS hA hw hWm hlm hW hΦ hv hε
end YangMills.Construction.MomentLaw
end
