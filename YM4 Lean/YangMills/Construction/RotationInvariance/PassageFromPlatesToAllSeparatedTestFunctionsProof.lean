import YangMills.Construction.EuclideanFunctionals.ElementAboveAHeightAndItsPulledDownElementProof
import YangMills.Construction.EuclideanFunctionals.RoomForTheInsertionProof
import YangMills.Construction.EuclideanFunctionals.SharpNormOnFunctionsOfClassC1Proof
import YangMills.Construction.RotationInvariance.DensityOfThePlateFunctionsAtDistinctPointsProof
import YangMills.Construction.RotationInvariance.FiniteSumsOfPlatesApproximateInC1
import YangMills.Construction.RotationInvariance.InvariantTwoPointFunctionHasTopFrequencyZeroProof
import YangMills.Construction.RotationInvariance.PassageFromPlatesToAllSeparatedTestFunctions
import YangMills.Construction.RotationInvariance.WhatAnOrthogonalMapPreserves
import Mathlib
set_option autoImplicit false
open YangMills.Construction.EuclideanBalls YangMills.Construction.TestFunctions YangMills.Construction.DisjointTuples YangMills.Construction.RealPlane YangMills.Construction.ForwardTube MeasureTheory
noncomputable section
namespace YangMills.Construction.EuclideanFunctionals.RotationFromProductsProof
abbrev sigmaAt (S : ConnFamily) {n : ℕ} (h : Fin n → R4 → ℂ) : ℂ :=
  centeredFnFree S (complexTuple h)
theorem supp_eq_tsupport (f : R4 → ℂ) : supp f = tsupport f := by apply _root_.YangMills.Construction.EuclideanFunctionals.AboveHeight.supp_eq_tsupport <;> assumption
theorem mem_disjointSupportTuples_iff_mem {n : ℕ} (h : Fin n → R4 → ℂ) :
    h ∈ disjointSupportTuples 4 n ↔ h ∈ disjointComplexTuples n := by
  constructor
  · intro hh
    refine ⟨fun l => (mem_C1c_iff_mem_compactC1 _).2 (hh.1 l), fun k l hkl => ?_⟩
    show Disjoint (supp (h k)) (supp (h l))
    rw [supp_eq_tsupport, supp_eq_tsupport]
    exact hh.2 hkl
  · intro hh
    refine ⟨fun l => (mem_C1c_iff_mem_compactC1 _).1 (hh.1 l), fun k l hkl => ?_⟩
    have : Disjoint (supp (h k)) (supp (h l)) := hh.2 hkl
    rw [supp_eq_tsupport, supp_eq_tsupport] at this
    exact this
theorem sigmaAt_comp_equiv (S : ConnFamily) (hsym : MomentSymmetry.PermInvariant S)
    {N n : ℕ} (hn : 2 ≤ n) (ε : Fin N ≃ Fin n) (h : Fin n → R4 → ℂ)
    (hh : h ∈ disjointComplexTuples n) : sigmaAt S (h ∘ ε) = sigmaAt S h := by
  have hN : N = n := by simpa using Fintype.card_congr ε
  subst hN
  exact hsym N hn ε h ((mem_disjointComplexTuples_iff (by omega) h).1 hh)
theorem exists_orthogonalMatrix_eq_rotateMotion (hiso : OrthogonalInvariance.RotationRules) (t : ℝ) :
    ∃ Q : Matrix.orthogonalGroup (Fin 4) ℝ, EuclidMotion.ofOrthogonalMatrix Q = rotateMotion t := by
  have h := (hiso t).1
  rw [Matrix.mem_specialOrthogonalGroup_iff] at h
  refine ⟨⟨_, h.1⟩, EuclidMotion.ext_of_apply fun x => ?_⟩
  rw [EuclidMotion.ofOrthogonalMatrix_apply]
  simp [rotateMotion, LinearMap.toMatrix'_mulVec]
theorem exists_pos_forall_le {ι : Type*} [Finite ι] (P : ι → Prop) (g : ι → ℝ)
    (hg : ∀ i, P i → 0 < g i) : ∃ ρ : ℝ, 0 < ρ ∧ ∀ i, P i → ρ ≤ g i := by
  classical
  cases nonempty_fintype ι
  have key : ∀ s : Finset ι, ∃ ρ : ℝ, 0 < ρ ∧ ∀ i ∈ s, P i → ρ ≤ g i := by
    intro s
    induction s using Finset.induction_on with
    | empty => exact ⟨1, one_pos, by simp⟩
    | insert a s _ ih =>
      obtain ⟨ρ, hρ, h⟩ := ih
      by_cases ha : P a
      · refine ⟨min ρ (g a), lt_min hρ (hg a ha), fun i hi hP => ?_⟩
        rcases Finset.mem_insert.1 hi with rfl | hi
        · exact min_le_right _ _
        · exact (min_le_left _ _).trans (h i hi hP)
      · refine ⟨ρ, hρ, fun i hi hP => ?_⟩
        rcases Finset.mem_insert.1 hi with rfl | hi
        · exact absurd hP ha
        · exact h i hi hP
  obtain ⟨ρ, hρ, h⟩ := key Finset.univ
  exact ⟨ρ, hρ, fun i => h i (Finset.mem_univ i)⟩
theorem exists_equiv_split {n : ℕ} (P : Fin n → Prop) :
    ∃ (p p' : ℕ) (ε : Fin (p + p') ≃ Fin n),
      (∀ k : Fin p, ¬P (ε (Fin.castAdd p' k))) ∧ (∀ k : Fin p', P (ε (Fin.natAdd p k))) ∧
      ((∃ i, ¬P i) → 1 ≤ p) ∧ ((∃ i, P i) → 1 ≤ p') := by
  classical
  let e₁ := Fintype.equivFin {i // ¬P i}
  let e₂ := Fintype.equivFin {i // P i}
  let ε : Fin (Fintype.card {i // ¬P i} + Fintype.card {i // P i}) ≃ Fin n :=
    finSumFinEquiv.symm.trans ((Equiv.sumCongr e₁.symm e₂.symm).trans
      ((Equiv.sumComm _ _).trans (Equiv.sumCompl P)))
  refine ⟨_, _, ε, fun k => ?_, fun k => ?_, ?_, ?_⟩
  · have : ε (Fin.castAdd _ k) = (e₁.symm k).1 := by simp [ε]
    rw [this]
    exact (e₁.symm k).2
  · have : ε (Fin.natAdd _ k) = (e₂.symm k).1 := by simp [ε]
    rw [this]
    exact (e₂.symm k).2
  · rintro ⟨i, hi⟩
    exact Fintype.card_pos_iff.2 ⟨⟨i, hi⟩⟩
  · rintro ⟨i, hi⟩
    exact Fintype.card_pos_iff.2 ⟨⟨i, hi⟩⟩
theorem rotate_neg_rotate (t : ℝ) (y : RealPlane) :
    RealPlane.rotate (-t) (RealPlane.rotate t y) = y := by apply _root_.YangMills.Construction.EuclideanFunctionals.TwoPointTopFrequency.rotate_neg_rotate <;> assumption
def rotateLinearIsometryEquiv (t : ℝ) : RealPlane ≃ₗᵢ[ℝ] RealPlane where
  toFun := RealPlane.rotate t
  invFun := RealPlane.rotate (-t)
  left_inv := rotate_neg_rotate t
  right_inv y := by simpa using rotate_neg_rotate (-t) y
  map_add' y y' := by
    ext i
    fin_cases i <;> simp [RealPlane.rotate] <;> ring
  map_smul' c y := by
    ext i
    fin_cases i <;> simp [RealPlane.rotate] <;> ring
  norm_map' y := by
    have h := Real.sin_sq_add_cos_sq t
    simp only [LinearEquiv.coe_mk, LinearMap.coe_mk, AddHom.coe_mk]
    rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
    congr 1
    simp [Fin.sum_univ_two, RealPlane.rotate]
    linear_combination (y 0 ^ 2 + y 1 ^ 2) * h
theorem sigmaAt_products_rotate
    (hsing : HarmonicDensity.Holds)
    (hrot : OrthogonalInvariance.PlateRotation)
    {m : SharpScale} {S : ConnFamily} (d : ProductPlaneData m S) (φ₀ : openingAngles) {q : ℕ}
    (hq : 1 ≤ q) (htop : maxFrequency S φ₀ (q + 1) = 0) (t : ℝ)
    (α : Fin (q + 1) → RealPlane → ℂ) (hα : ∀ i, α i ∈ complexProfiles)
    (hdis : Pairwise fun i j => Disjoint (tsupport (α i)) (tsupport (α j)))
    (φ : Fin (q + 1) → realLabels) :
    sigmaAt S (fun l => (rotateMotion t).actFn (productFunction (α l) (φ l))) =
      sigmaAt S (fun l => productFunction (α l) (φ l)) := by
  have hR := fun l => hrot t (α l) (φ l) (hα l) (φ l).2
  have e0 : (fun l => (rotateMotion t).actFn (productFunction (α l) (φ l))) =
      fun l => productFunction (α l ∘ RealPlane.rotate (-t)) (φ l) := funext fun l => (hR l).1
  rw [e0]
  obtain ⟨-, -, h3, h4⟩ := hsing m S d φ₀ q hq φ
  have hinj : Function.Injective (RealPlane.rotate t) := (rotateLinearIsometryEquiv t).injective
  have hdis' : Pairwise fun i j => Disjoint (tsupport (α i ∘ RealPlane.rotate (-t)))
      (tsupport (α j ∘ RealPlane.rotate (-t))) := by
    intro i j hij
    rw [(hR i).2.2, (hR j).2.2]
    exact (Set.disjoint_image_iff hinj).2 (hdis hij)
  have e1 := (h3 (fun l => α l ∘ RealPlane.rotate (-t)) (fun l => (hR l).2.1) hdis').2
  have e2 := (h3 α hα hdis).2
  change centeredFnAtProducts S _ φ = centeredFnAtProducts S α φ
  rw [e1, e2]
  set K := harmonicSum S φ₀ (q + 1) φ with hK
  let Φ : (Fin (q + 1) → RealPlane) → Fin (q + 1) → RealPlane :=
    fun y i => rotateLinearIsometryEquiv t (y i)
  have hΦ : MeasurePreserving Φ volume volume :=
    volume_preserving_pi fun _ => (rotateLinearIsometryEquiv t).measurePreserving
  have hemb : MeasurableEmbedding Φ :=
    (Homeomorph.piCongrRight fun _ => (rotateLinearIsometryEquiv t).toHomeomorph).measurableEmbedding
  unfold profileIntegral
  rw [← hΦ.integral_comp hemb]
  congr 1
  funext y
  have hmem : Φ y ∈ Set.univ.pi (fun i => tsupport (α i ∘ RealPlane.rotate (-t))) ↔
      y ∈ Set.univ.pi fun i => tsupport (α i) := by
    simp only [Set.mem_pi, Set.mem_univ, forall_true_left]
    refine forall_congr' fun i => ?_
    rw [(hR i).2.2]
    exact hinj.mem_set_image
  unfold profileIntegrand
  by_cases hy : y ∈ Set.univ.pi fun i => tsupport (α i)
  · rw [Set.indicator_of_mem (hmem.2 hy), Set.indicator_of_mem hy]
    have hyd : y ∈ injectivePointTuples (q + 1) := by
      intro i j hij
      by_contra hne
      exact Set.disjoint_left.1 (hdis hne) (hy i (Set.mem_univ _)) (hij ▸ hy j (Set.mem_univ _))
    have hturn := h4 y hyd t
    have hKy : K y = pointHarmonic S φ₀ 0 (q + 1) φ y := by
      simp [hK, harmonicSum, htop]
    have hKΦ : K (Φ y) = K y := by
      have : Φ y = mapPoints (RealPlane.rotate t) y := rfl
      rw [this]
      refine hturn.trans ?_
      rw [hKy]
      simp [htop]
    rw [hKΦ]
    congr 1
    refine Finset.prod_congr rfl fun i _ => ?_
    simp only [Function.comp, Φ]
    exact congrArg (α i) (rotate_neg_rotate t (y i))
  · rw [Set.indicator_of_notMem (fun h => hy (hmem.1 h)), Set.indicator_of_notMem hy]
section Difference
variable (S : ConnFamily) (Q : EuclidMotion)
def rotationDefect {n : ℕ} (h : Fin n → R4 → ℂ) : ℂ :=
  sigmaAt S (fun l => Q.actFn (h l)) - sigmaAt S h
theorem actFn_update {n : ℕ} (h : Fin n → R4 → ℂ) (i : Fin n) (g : R4 → ℂ) :
    (fun l => Q.actFn (Function.update h i g l)) =
      Function.update (fun l => Q.actFn (h l)) i (Q.actFn g) := by
  funext l
  by_cases hl : l = i
  · subst hl; simp
  · simp [Function.update_of_ne hl]
variable {S Q}
theorem rotationDefect_add_smul
    (hlin : OrthogonalInvariance.EntrywiseLinear S)
    (hQ : ∀ n, ∀ h ∈ disjointComplexTuples n, (fun l => Q.actFn (h l)) ∈ disjointComplexTuples n)
    {n : ℕ} (i : Fin n) (lam : ℂ) (h : Fin n → R4 → ℂ) (g : R4 → ℂ)
    (hh : h ∈ disjointComplexTuples n) (hg : Function.update h i g ∈ disjointComplexTuples n) :
    rotationDefect S Q (Function.update h i (h i + lam • g)) =
      rotationDefect S Q h + lam * rotationDefect S Q (Function.update h i g) := by
  have hg' : Function.update (fun l => Q.actFn (h l)) i (Q.actFn g) ∈
      disjointComplexTuples n := by
    rw [← actFn_update]
    exact hQ n _ hg
  have eA := (hlin n i lam h g hh hg).2
  have eB := (hlin n i lam _ _ (hQ n h hh) hg').2
  have e : Q.actFn (h i + lam • g) = Q.actFn (h i) + lam • Q.actFn g := rfl
  simp only [rotationDefect, sigmaAt, actFn_update, e, eA, eB]
  ring
end Difference
theorem eq_zero_of_sums_of_generators {n : ℕ} {X : Type*} [AddCommMonoid X]
    (Dt : (Fin n → X) → ℂ)
    (C G : Fin n → Set X) (hGC : ∀ i, G i ⊆ C i)
    (hCadd : ∀ i g g', g ∈ C i → g' ∈ C i → g + g' ∈ C i)
    (hadd : ∀ h : Fin n → X, (∀ i, h i ∈ C i) → ∀ i g g', g ∈ C i → g' ∈ C i →
      Dt (Function.update h i (g + g')) =
        Dt (Function.update h i g) + Dt (Function.update h i g'))
    (hG : ∀ h : Fin n → X, (∀ i, h i ∈ G i) → Dt h = 0)
    (h : Fin n → X)
    (hS : ∀ i, ∃ p : ℕ, 1 ≤ p ∧ ∃ g : Fin p → X, (∀ b, g b ∈ G i) ∧ h i = ∑ b, g b) :
    Dt h = 0 := by
  classical
  have hsumC : ∀ i p, 1 ≤ p → ∀ g : Fin p → X, (∀ b, g b ∈ G i) → ∑ b, g b ∈ C i := by
    intro i p hp
    induction p, hp using Nat.le_induction with
    | base => intro g hg; simpa using hGC i (hg 0)
    | succ p hp ih =>
      intro g hg
      rw [Fin.sum_univ_castSucc]
      exact hCadd i _ _ (ih _ fun b => hg _) (hGC i (hg _))
  have key : ∀ s : Finset (Fin n), ∀ h : Fin n → X,
      (∀ i, ∃ p : ℕ, 1 ≤ p ∧ ∃ g : Fin p → X, (∀ b, g b ∈ G i) ∧ h i = ∑ b, g b) →
      (∀ i, i ∉ s → h i ∈ G i) → Dt h = 0 := by
    intro s
    induction s using Finset.induction_on with
    | empty => exact fun h _ hO => hG h fun i => hO i (by simp)
    | insert a s ha ih =>
      intro h hS hO
      have hC : ∀ i, h i ∈ C i := by
        intro i
        obtain ⟨p, hp, g, hg, he⟩ := hS i
        rw [he]
        exact hsumC i p hp g hg
      have inner : ∀ p, 1 ≤ p → ∀ g : Fin p → X, (∀ b, g b ∈ G a) →
          Dt (Function.update h a (∑ b, g b)) = 0 := by
        intro p hp
        induction p, hp using Nat.le_induction with
        | base =>
          intro g hg
          have : ∑ b, g b = g 0 := by simp
          rw [this]
          refine ih _ (fun i => ?_) (fun i hi => ?_)
          · by_cases hia : i = a
            · subst hia
              exact ⟨1, le_rfl, g, hg, by simp⟩
            · simpa [Function.update_of_ne hia] using hS i
          · by_cases hia : i = a
            · subst hia
              simpa using hg 0
            · rw [Function.update_of_ne hia]
              exact hO i (by simp [hia, hi])
        | succ p hp ihp =>
          intro g hg
          rw [Fin.sum_univ_castSucc, hadd h hC a _ _ (hsumC a p hp _ fun b => hg _) (hGC a (hg _)),
            ihp _ fun b => hg _, zero_add]
          refine ih _ (fun i => ?_) (fun i hi => ?_)
          · by_cases hia : i = a
            · subst hia
              exact ⟨1, le_rfl, fun _ => g (Fin.last p), fun _ => hg _, by simp⟩
            · simpa [Function.update_of_ne hia] using hS i
          · by_cases hia : i = a
            · subst hia
              simpa using hg _
            · rw [Function.update_of_ne hia]
              exact hO i (by simp [hia, hi])
      obtain ⟨p, hp, g, hg, he⟩ := hS a
      have := inner p hp g hg
      rwa [← he, Function.update_eq_self] at this
  exact key Finset.univ h hS fun i hi => absurd (Finset.mem_univ i) hi
theorem planeComponent_sub (x x' : R4) :
    planeComponent (x - x') = planeComponent x - planeComponent x' := by
  ext i
  fin_cases i <;> simp [planeComponent]
theorem orthogonalComponent_sub (x x' : R4) :
    orthogonalComponent (x - x') = orthogonalComponent x - orthogonalComponent x' := by
  ext i
  fin_cases i <;> simp [orthogonalComponent]
theorem euclidNormVec_sq (v : R4) :
    TorusMetric.euclidNormVec v ^ 2 = ‖planeComponent v‖ ^ 2 + ‖orthogonalComponent v‖ ^ 2 := by
  rw [TorusMetric.euclidNormVec, Real.sq_sqrt (by positivity), EuclideanSpace.norm_eq,
    EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity)]
  simp [Fin.sum_univ_two, Fin.sum_univ_four, planeComponent, orthogonalComponent]
  ring
theorem euclidNormVec_nonneg (v : R4) : 0 ≤ TorusMetric.euclidNormVec v := Real.sqrt_nonneg _
theorem norm_planeComponent_le (v : R4) : ‖planeComponent v‖ ≤ TorusMetric.euclidNormVec v := by
  have h := euclidNormVec_sq v
  exact abs_le_of_sq_le_sq' (by nlinarith [sq_nonneg ‖orthogonalComponent v‖])
    (euclidNormVec_nonneg v) |>.2
theorem norm_orthogonalComponent_le (v : R4) :
    ‖orthogonalComponent v‖ ≤ TorusMetric.euclidNormVec v := by
  have h := euclidNormVec_sq v
  exact abs_le_of_sq_le_sq' (by nlinarith [sq_nonneg ‖planeComponent v‖])
    (euclidNormVec_nonneg v) |>.2
theorem partialDerivR4_eq_fderiv {f : R4 → ℂ} (hf : ContDiff ℝ 1 f) (μ : Fin 4) (x : R4) :
    partialDerivR4 μ f x = fderiv ℝ f x (Pi.single μ 1) := by apply _root_.YangMills.Construction.EuclideanFunctionals.SharpNormC1.partialDerivR4_eq_fderiv <;> assumption
theorem tendstoUniformly_linear_combination {X : Type*} {ι : Type*} [Fintype ι] (c : ι → ℂ)
    (a : ℕ → ι → X → ℂ) (a' : ι → X → ℂ)
    (h : ∀ ν, TendstoUniformly (fun j x => a j ν x) (a' ν) Filter.atTop) :
    TendstoUniformly (fun j x => ∑ ν, c ν * a j ν x) (fun x => ∑ ν, c ν * a' ν x)
      Filter.atTop := by
  rw [Metric.tendstoUniformly_iff]
  intro ε hε
  have hC : 0 < ∑ ν, ‖c ν‖ + 1 := by positivity
  have hall : ∀ ν, ∀ᶠ j in Filter.atTop, ∀ x, dist (a' ν x) (a j ν x) < ε / (∑ ν, ‖c ν‖ + 1) :=
    fun ν => Metric.tendstoUniformly_iff.1 (h ν) _ (div_pos hε hC)
  filter_upwards [Filter.eventually_all.2 hall] with j hj x
  rw [dist_eq_norm, ← Finset.sum_sub_distrib]
  calc ‖∑ ν, (c ν * a' ν x - c ν * a j ν x)‖
      ≤ ∑ ν, ‖c ν * a' ν x - c ν * a j ν x‖ := norm_sum_le _ _
    _ ≤ ∑ ν, ‖c ν‖ * (ε / (∑ ν, ‖c ν‖ + 1)) := by
        refine Finset.sum_le_sum fun ν _ => ?_
        rw [← mul_sub, norm_mul]
        have := hj ν x
        rw [dist_eq_norm] at this
        exact mul_le_mul_of_nonneg_left this.le (norm_nonneg _)
    _ = (∑ ν, ‖c ν‖) / (∑ ν, ‖c ν‖ + 1) * ε := by
        rw [← Finset.sum_mul]; ring
    _ < ε := by
        have : (∑ ν, ‖c ν‖) / (∑ ν, ‖c ν‖ + 1) < 1 := by
          rw [div_lt_one hC]; linarith
        nlinarith
theorem tendstoC1_actFn (hgrad : OrthogonalInvariance.GradientTransform)
    (hact : OrthogonalInvariance.FunctionAction)
    (Q : Matrix.orthogonalGroup (Fin 4) ℝ) (hs : ℕ → R4 → ℂ) (h : R4 → ℂ)
    (hhs : ∀ j, hs j ∈ C1c ℂ) (hh : h ∈ C1c ℂ)
    (hc : TendstoC1 hs h) :
    TendstoC1 (fun j => (EuclidMotion.ofOrthogonalMatrix Q).actFn (hs j))
      ((EuclidMotion.ofOrthogonalMatrix Q).actFn h) := by
  set r := EuclidMotion.ofOrthogonalMatrix Q with hr
  have hC : ∀ {f : R4 → ℂ}, f ∈ C1c ℂ → ContDiff ℝ 1 f := fun hf =>
    ((mem_C1c_iff_mem_compactC1 _).1 hf).1
  have hd : ∀ {f : R4 → ℂ}, f ∈ C1c ℂ → ∀ (μ : Fin 4) (x : R4),
      fderiv ℝ (r.actFn f) x (Pi.single μ 1) =
        ∑ ν, (Q.1 μ ν : ℂ) * fderiv ℝ f (r⁻¹ x) (Pi.single ν 1) := by
    intro f hf μ x
    have hrf : r.actFn f ∈ C1c ℂ := (hact Q Q f hf).1
    rw [← partialDerivR4_eq_fderiv (hC hrf), hgrad Q f x μ hf]
    exact Finset.sum_congr rfl fun ν _ => by rw [partialDerivR4_eq_fderiv (hC hf)]
  refine ⟨hc.1.comp (fun x => r⁻¹ x), fun μ => ?_⟩
  have e₁ : (fun j x => fderiv ℝ (r.actFn (hs j)) x (Pi.single μ 1)) =
      fun j x => ∑ ν, (Q.1 μ ν : ℂ) * fderiv ℝ (hs j) (r⁻¹ x) (Pi.single ν 1) :=
    funext fun j => funext fun x => hd (hhs j) μ x
  have e₂ : (fun x => fderiv ℝ (r.actFn h) x (Pi.single μ 1)) =
      fun x => ∑ ν, (Q.1 μ ν : ℂ) * fderiv ℝ h (r⁻¹ x) (Pi.single ν 1) :=
    funext fun x => hd hh μ x
  rw [e₁, e₂]
  exact tendstoUniformly_linear_combination (fun ν => (Q.1 μ ν : ℂ))
    (fun j ν x => fderiv ℝ (hs j) (r⁻¹ x) (Pi.single ν 1))
    (fun ν x => fderiv ℝ h (r⁻¹ x) (Pi.single ν 1))
    fun ν => (hc.2 ν).comp (fun x => r⁻¹ x)
theorem separatedInBalls_image {n : ℕ} (r : EuclidMotion) {A : Fin n → Set R4} {R d : ℝ}
    (h : Moments.SeparatedInBalls A R d) :
    Moments.SeparatedInBalls (fun l => r '' A l) R d := by
  refine ⟨fun l => ?_, fun k l hkl => ?_⟩
  · obtain ⟨c, hc⟩ := h.1 l
    refine ⟨r c, ?_⟩
    rintro _ ⟨a, ha, rfl⟩
    have := hc ha
    show TorusMetric.euclidNormVec (r a - r c) ≤ R
    rw [EuclidMotion.euclidNormVec_sub]
    exact this
  · have hkl' := h.2 hkl
    refine le_iInf₂ fun a' ha' => le_iInf₂ fun b' hb' => ?_
    obtain ⟨a, ha, rfl⟩ := ha'
    obtain ⟨b, hb, rfl⟩ := hb'
    rw [EuclidMotion.euclidNormVec_sub]
    exact hkl'.trans (iInf₂_le_of_le a ha (iInf₂_le b hb))
theorem tsupport_finset_sum_subset {ι : Type*} (s : Finset ι) (g : ι → R4 → ℂ) (W : Set R4)
    (h : ∀ i ∈ s, tsupport (g i) ⊆ W) : tsupport (∑ i ∈ s, g i) ⊆ W := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [tsupport]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    have := tsupport_add_smul_subset_union (k := 4) (g a) (∑ i ∈ s, g i) 1
    rw [one_smul] at this
    exact this.trans (Set.union_subset (h a (by simp))
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi)))
def productCell (x : R4) (ρ : ℝ) : Set R4 :=
  {z | ‖planeComponent z - planeComponent x‖ < 2 * ρ ∧
    ‖orthogonalComponent z - orthogonalComponent x‖ < 2 * ρ}
theorem productCell_separatedInBalls {n : ℕ} (x : Fin n → R4) {ρ : ℝ} (hρ : 0 < ρ)
    (h5 : ∀ k l, k ≠ l → 5 * ρ ≤ ‖planeComponent (x k) - planeComponent (x l)‖) :
    Moments.SeparatedInBalls (fun l => productCell (x l) ρ) (3 * ρ) ρ := by
  refine ⟨fun l => ⟨x l, fun z hz => ?_⟩, fun k l hkl => ?_⟩
  · show TorusMetric.euclidNormVec (z - x l) ≤ 3 * ρ
    have h := euclidNormVec_sq (z - x l)
    rw [planeComponent_sub, orthogonalComponent_sub] at h
    obtain ⟨h₁, h₂⟩ := hz
    have h₁' : ‖planeComponent z - planeComponent (x l)‖ ^ 2 < (2 * ρ) ^ 2 :=
      pow_lt_pow_left₀ h₁ (norm_nonneg _) two_ne_zero
    have h₂' : ‖orthogonalComponent z - orthogonalComponent (x l)‖ ^ 2 < (2 * ρ) ^ 2 :=
      pow_lt_pow_left₀ h₂ (norm_nonneg _) two_ne_zero
    by_contra hcon
    rw [not_le] at hcon
    have : (3 * ρ) ^ 2 < TorusMetric.euclidNormVec (z - x l) ^ 2 :=
      pow_lt_pow_left₀ hcon (by positivity) two_ne_zero
    nlinarith
  · refine le_iInf₂ fun a ha => le_iInf₂ fun b hb => ENNReal.ofReal_le_ofReal ?_
    have h := h5 k l hkl
    have e : planeComponent (x k) - planeComponent (x l) = (planeComponent (x k) - planeComponent a) +
        (planeComponent a - planeComponent b) + (planeComponent b - planeComponent (x l)) := by abel
    have h₁ : ‖planeComponent (x k) - planeComponent a‖ < 2 * ρ := by
      rw [norm_sub_rev]; exact ha.1
    have h₂ := hb.1
    have h₃ : ‖planeComponent a - planeComponent b‖ ≤ TorusMetric.euclidNormVec (a - b) := by
      rw [← planeComponent_sub]; exact norm_planeComponent_le _
    have h₄ := norm_add₃_le (a := planeComponent (x k) - planeComponent a)
      (b := planeComponent a - planeComponent b) (c := planeComponent b - planeComponent (x l))
    rw [← e] at h₄
    linarith
theorem openDiscAt_disjoint {n : ℕ} (x : Fin n → R4) {ρ : ℝ} (hρ : 0 < ρ)
    (h5 : ∀ k l, k ≠ l → 5 * ρ ≤ ‖planeComponent (x k) - planeComponent (x l)‖) {k l : Fin n}
    (hkl : k ≠ l) :
    Disjoint (openDiscAt (planeComponent (x k)) (2 * ρ)) (openDiscAt (planeComponent (x l)) (2 * ρ)) := by
  rw [Set.disjoint_left]
  intro y hk hl
  have h := h5 k l hkl
  have hk' : ‖y - planeComponent (x k)‖ < 2 * ρ := hk
  have hl' : ‖y - planeComponent (x l)‖ < 2 * ρ := hl
  have e : planeComponent (x k) - planeComponent (x l) =
      -(y - planeComponent (x k)) + (y - planeComponent (x l)) := by
    abel
  have := norm_add_le (-(y - planeComponent (x k))) (y - planeComponent (x l))
  rw [← e, norm_neg] at this
  linarith
theorem productCell_disjoint {n : ℕ} (x : Fin n → R4) {ρ : ℝ} (hρ : 0 < ρ)
    (h5 : ∀ k l, k ≠ l → 5 * ρ ≤ ‖planeComponent (x k) - planeComponent (x l)‖) {k l : Fin n}
    (hkl : k ≠ l) : Disjoint (productCell (x k) ρ) (productCell (x l) ρ) := by
  rw [Set.disjoint_left]
  intro z hk hl
  exact Set.disjoint_left.1 (openDiscAt_disjoint x hρ h5 hkl) hk.1 hl.1
theorem mem_disjointComplexTuples_of_tsupport_subset {n : ℕ} {W : Fin n → Set R4}
    (hW : Pairwise fun k l => Disjoint (W k) (W l)) {h : Fin n → R4 → ℂ}
    (hC : ∀ i, h i ∈ C1c ℂ) (hs : ∀ i, tsupport (h i) ⊆ W i) :
    h ∈ disjointComplexTuples n := by
  refine ⟨hC, fun k l hkl => ?_⟩
  show Disjoint (supp (h k)) (supp (h l))
  rw [supp_eq_tsupport, supp_eq_tsupport]
  exact (hW hkl).mono (hs k) (hs l)
theorem add_mem_C1c {f g : R4 → ℂ} (hf : f ∈ C1c ℂ) (hg : g ∈ C1c ℂ) : f + g ∈ C1c ℂ := by
  rw [mem_C1c_iff_mem_compactC1] at hf hg ⊢
  exact ⟨hf.1.add hg.1, hf.2.add hg.2⟩
theorem rotationDefect_eq_zero_of_injective_planeComponent
    {m : SharpScale} {S : ConnFamily} (σ : EuclidFunctionalWithRecon m S)
    (Q : Matrix.orthogonalGroup (Fin 4) ℝ)
    (hb : Moments.MomentBoundsTheorem)
    (happ : ProductSumApprox.ProductSumsDenseC1)
    (hpl : TranslationRules.ProductFunctionsInC1c)
    (hgrad : OrthogonalInvariance.GradientTransform)
    (hact : OrthogonalInvariance.FunctionAction)
    (hsupp : OrthogonalInvariance.SupportBallDistanceTuple)
    (hlin : OrthogonalInvariance.EntrywiseLinear S)
    (hQ : ∀ n, ∀ h ∈ disjointComplexTuples n,
      (fun l => (EuclidMotion.ofOrthogonalMatrix Q).actFn (h l)) ∈ disjointComplexTuples n)
    {n : ℕ} (hn : 2 ≤ n)
    (hplates : ∀ α : Fin n → RealPlane → ℂ, (∀ i, α i ∈ complexProfiles) →
      (Pairwise fun i j => Disjoint (tsupport (α i)) (tsupport (α j))) →
      ∀ φ : Fin n → realLabels,
        rotationDefect S (EuclidMotion.ofOrthogonalMatrix Q) (fun l => productFunction (α l) (φ l)) = 0)
    (x : Fin n → R4) (hx : Function.Injective fun i => planeComponent (x i)) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ f ∈ disjointComplexTuples n, (∀ i, tsupport (f i) ⊆ euclidBall (x i) ρ) →
      rotationDefect S (EuclidMotion.ofOrthogonalMatrix Q) f = 0 := by
  classical
  set r := EuclidMotion.ofOrthogonalMatrix Q with hr
  obtain ⟨ρ, hρ, hlow⟩ := exists_pos_forall_le (ι := Fin n × Fin n) (fun p => p.1 ≠ p.2)
    (fun p => ‖planeComponent (x p.1) - planeComponent (x p.2)‖ / 5)
    (fun p hp => by
      have : planeComponent (x p.1) - planeComponent (x p.2) ≠ 0 :=
        sub_ne_zero.2 fun e => hp (hx e)
      positivity)
  have h5 : ∀ k l, k ≠ l → 5 * ρ ≤ ‖planeComponent (x k) - planeComponent (x l)‖ := by
    intro k l hkl
    have := hlow (k, l) hkl
    simp only at this
    linarith
  refine ⟨ρ, hρ, fun f hf hsup => ?_⟩
  have hcell : ∀ i, tsupport (f i) ⊆ productCell (x i) ρ := by
    intro i z hz
    have hz' : TorusMetric.euclidNormVec (z - x i) < ρ := hsup i hz
    have h₁ := norm_planeComponent_le (z - x i)
    have h₂ := norm_orthogonalComponent_le (z - x i)
    rw [planeComponent_sub] at h₁
    rw [orthogonalComponent_sub] at h₂
    exact ⟨by linarith, by linarith⟩
  choose fs hfsC hconv hsum using fun i =>
    happ (x i) ρ hρ (f i) (hf.1 i) (hsup i)
  let g : ℕ → Fin n → R4 → ℂ := fun j l => fs l j.succPNat
  let Cs : Fin n → Set (R4 → ℂ) := fun l =>
    {u | u ∈ C1c ℂ ∧ tsupport u ⊆ productCell (x l) ρ}
  let Gs : Fin n → Set (R4 → ℂ) := fun l =>
    {u | ∃ (α : RealPlane → ℂ) (φ : realLabels), α ∈ complexProfiles ∧
      tsupport α ⊆ openDiscAt (planeComponent (x l)) (2 * ρ) ∧
      tsupport φ.1 ⊆ openDiscAt (orthogonalComponent (x l)) (2 * ρ) ∧ u = productFunction α φ.1}
  have hGC : ∀ l, Gs l ⊆ Cs l := by
    rintro l _ ⟨α, φ, hα, hsα, hsφ, rfl⟩
    have hp := hpl α hα φ.1 φ.2
    refine ⟨hp.1, ?_⟩
    rw [← supp_eq_tsupport]
    intro z hz
    obtain ⟨h₁, h₂⟩ := hp.2 hz
    exact ⟨hsα h₁, hsφ h₂⟩
  have hCadd : ∀ l u u', u ∈ Cs l → u' ∈ Cs l → u + u' ∈ Cs l := by
    intro l u u' hu hu'
    refine ⟨add_mem_C1c hu.1 hu'.1, ?_⟩
    have := tsupport_add_smul_subset_union (k := 4) u u' 1
    rw [one_smul] at this
    exact this.trans (Set.union_subset hu.2 hu'.2)
  have hdis : Pairwise fun k l => Disjoint (productCell (x k) ρ) (productCell (x l) ρ) :=
    fun k l hkl => productCell_disjoint x hρ h5 hkl
  have hmemT : ∀ h : Fin n → R4 → ℂ, (∀ i, h i ∈ Cs i) → h ∈ disjointComplexTuples n :=
    fun h hh => mem_disjointComplexTuples_of_tsupport_subset hdis (fun i => (hh i).1)
      (fun i => (hh i).2)
  have hupd : ∀ (h : Fin n → R4 → ℂ), (∀ i, h i ∈ Cs i) → ∀ i u, u ∈ Cs i →
      ∀ l, Function.update h i u l ∈ Cs l := by
    intro h hh i u hu l
    by_cases hl : l = i
    · subst hl; simpa using hu
    · simpa [Function.update_of_ne hl] using hh l
  have hadd : ∀ h : Fin n → R4 → ℂ, (∀ i, h i ∈ Cs i) → ∀ i u u', u ∈ Cs i → u' ∈ Cs i →
      rotationDefect S r (Function.update h i (u + u')) =
        rotationDefect S r (Function.update h i u) + rotationDefect S r (Function.update h i u') := by
    intro h hh i u u' hu hu'
    have h₁ := hupd h hh i u hu
    have h₂ := hupd (Function.update h i u) h₁ i u' hu'
    have := rotationDefect_add_smul hlin hQ i 1 (Function.update h i u) u' (hmemT _ h₁) (hmemT _ h₂)
    simpa using this
  have hG : ∀ h : Fin n → R4 → ℂ, (∀ i, h i ∈ Gs i) → rotationDefect S r h = 0 := by
    intro h hh
    choose α φ hα hsα hsφ he using hh
    have e : h = fun l => productFunction (α l) (φ l) := funext he
    rw [e]
    exact hplates α hα (fun k l hkl => (openDiscAt_disjoint x hρ h5 hkl).mono (hsα k) (hsα l)) φ
  have hzero : ∀ j, rotationDefect S r (g j) = 0 := by
    intro j
    refine eq_zero_of_sums_of_generators (rotationDefect S r) Cs Gs hGC hCadd hadd hG (g j)
      fun l => ?_
    obtain ⟨p, hp, α, φ, hall, he⟩ := hsum l j.succPNat
    refine ⟨p, hp, fun b => productFunction (α b) (φ b), fun b => ?_, ?_⟩
    · exact ⟨α b, ⟨φ b, (hall b).2.1⟩, (hall b).1, (hall b).2.2.1, (hall b).2.2.2, rfl⟩
    · exact he
  have hgC : ∀ j l, g j l ∈ Cs l := by
    intro j l
    obtain ⟨p, hp, α, φ, hall, he⟩ := hsum l j.succPNat
    refine ⟨hfsC l _, ?_⟩
    show tsupport (fs l j.succPNat) ⊆ _
    rw [he]
    exact tsupport_finset_sum_subset _ _ _ fun b _ =>
      (hGC l ⟨α b, ⟨φ b, (hall b).2.1⟩, (hall b).1, (hall b).2.2.1, (hall b).2.2.2, rfl⟩).2
  have hsep := productCell_separatedInBalls x hρ h5
  have hsep' := separatedInBalls_image r hsep
  have hentries : Moments.EntriesSupportedIn (fun l => productCell (x l) ρ) f :=
    fun l => ⟨hf.1 l, by rw [supp_eq_tsupport]; exact hcell l⟩
  have hgentries : ∀ j, Moments.EntriesSupportedIn (fun l => productCell (x l) ρ) (g j) :=
    fun j l => ⟨(hgC j l).1, by rw [supp_eq_tsupport]; exact (hgC j l).2⟩
  have himg : ∀ {u : R4 → ℂ} {W : Set R4}, u ∈ C1c ℂ → supp u ⊆ W →
      r.actFn u ∈ C1c ℂ ∧ supp (r.actFn u) ⊆ r '' W := by
    intro u W hu hW
    refine ⟨(hact Q Q u hu).1, ?_⟩
    rw [(hsupp Q).1 u hu]
    exact Set.image_mono hW
  have hlim₁ := (hb m S σ n hn (3 * ρ) ρ (by positivity) hρ _ hsep f f hentries hentries).2.2.1
  have hlim₂ := (hb m S σ n hn (3 * ρ) ρ (by positivity) hρ _ hsep'
    (fun l => r.actFn (f l)) (fun l => r.actFn (f l))
    (fun l => himg (hentries l).1 (hentries l).2)
    (fun l => himg (hentries l).1 (hentries l).2)).2.2.1
  have t₁ := hlim₁ g (fun j _ => hgentries j) (fun l => hconv l)
  have t₂ := hlim₂ (fun j l => r.actFn (g j l))
    (fun j _ l => himg (hgentries j l).1 (hgentries j l).2)
    (fun l => tendstoC1_actFn hgrad hact Q _ _ (fun j => (hgC j l).1) (hf.1 l) (hconv l))
  have t₃ := t₂.sub t₁
  have t₄ : Filter.Tendsto (fun j => rotationDefect S r (g j)) Filter.atTop
      (nhds (rotationDefect S r f)) := t₃
  simp only [hzero] at t₄
  exact (tendsto_nhds_unique t₄ tendsto_const_nhds)
theorem differentiableAt_of_holomorphicOnComplex {O : Set ℂ} {G : ℂ → ℂ}
    (h : HolomorphicOnComplex O G) {z : ℂ} (hz : z ∈ O) : DifferentiableAt ℂ G z := by apply _root_.YangMills.Construction.EuclideanFunctionals.HarmonicDensity.differentiableAt_of_holomorphicOnComplex <;> assumption
theorem sigmaAt_shiftedComponents_holomorphic
    (hslide : TangentialAnalyticity.Holds)
    {m : SharpScale} {S : ConnFamily} (σ : EuclidFunctionalWithRecon m S)
    (hcone : σ.ConeCondition) (μ : Fin 4) (c δ : ℝ) (hδ : 0 < δ) {p p' : ℕ} (hp : 1 ≤ p)
    (hp' : 1 ≤ p') {a : Fin p → R4 → ℂ} (ha : a ∈ disjointComplexTuples p)
    {b : Fin p' → R4 → ℂ} (hb : b ∈ disjointComplexTuples p')
    (hsa : ∀ l, supp (a l) ⊆ {x | x μ < c - δ})
    (hsb : ∀ k, supp (b k) ⊆ {x | c + δ < x μ}) {u : R4} (hu : u μ = 0) :
    (∀ r : ℝ, TangentialAnalyticity.shiftedComponents a b u r ∈ disjointComplexTuples (p + p')) ∧
    ∃ ρ : ℝ, 0 < ρ ∧ ∃ G : ℂ → ℂ,
      (∀ r₀ : ℝ, DifferentiableOn ℂ G (Metric.ball (r₀ : ℂ) ρ)) ∧
      ∀ r : ℝ, G r = sigmaAt S (TangentialAnalyticity.shiftedComponents a b u r) := by
  obtain ⟨h1, ⟨G, hG, hGr⟩, -, -⟩ := hslide m S σ hcone μ c δ hδ p p' hp hp' a ha b hb hsa hsb u hu
  refine ⟨fun r => (h1 r).2.1, ?_⟩
  set s := TangentialAnalyticity.tangentialNorm μ u with hs
  have hs0 : 0 ≤ s := Finset.sum_nonneg fun _ _ => abs_nonneg _
  refine ⟨2 * δ / (s + 1), by positivity, G, fun r₀ z hz => ?_, fun r => ?_⟩
  · refine (differentiableAt_of_holomorphicOnComplex hG ?_).differentiableWithinAt
    show |z.im| * s < 2 * δ
    have hz' : ‖z - (r₀ : ℂ)‖ < 2 * δ / (s + 1) := by simpa [dist_eq_norm] using hz
    have him : |z.im| ≤ ‖z - (r₀ : ℂ)‖ := by
      have := Complex.abs_im_le_norm (z - (r₀ : ℂ))
      simpa using this
    have hlt : |z.im| < 2 * δ / (s + 1) := him.trans_lt hz'
    have h3 : |z.im| * (s + 1) < 2 * δ := (lt_div_iff₀ (by positivity)).1 hlt
    nlinarith [abs_nonneg z.im]
  · rw [hGr r]
    exact (h1 r).2.2
theorem comp_mem_disjointComplexTuples {N M : ℕ} {h : Fin N → R4 → ℂ}
    (hh : h ∈ disjointComplexTuples N) (ι : Fin M → Fin N) (hι : Function.Injective ι) :
    h ∘ ι ∈ disjointComplexTuples M :=
  ⟨fun _ => hh.1 _, fun _ _ hkl => hh.2 (hι.ne hkl)⟩
theorem mem_tsupport_actFn_transl (v z : R4) (f : R4 → ℂ) :
    z ∈ tsupport ((EuclidMotion.transl v).actFn f) ↔ z - v ∈ tsupport f := by
  have e : (EuclidMotion.transl v).actFn f = f ∘ (Homeomorph.subRight v) :=
    funext fun x => EuclidMotion.actFn_transl v f x
  rw [e, tsupport_comp_eq_preimage]
  rfl
theorem abs_apply_le_euclidNormVec (v : R4) (μ : Fin 4) : |v μ| ≤ TorusMetric.euclidNormVec v := by apply _root_.YangMills.Construction.EuclideanFunctionals.InsertionRoom.abs_coord_le_euclidNormVec <;> assumption
theorem euclidNormVec_add_smul_timeVec_le (v : R4) (s : ℝ) :
    TorusMetric.euclidNormVec (v + s • timeVec) ≤ TorusMetric.euclidNormVec v + |s| := by
  have hE : ∀ w : R4, TorusMetric.euclidNormVec w =
      ‖(WithLp.toLp 2 w : EuclideanSpace ℝ (Fin 4))‖ := by
    intro w
    rw [EuclideanSpace.norm_eq]
    simp [TorusMetric.euclidNormVec]
  have h2 : TorusMetric.euclidNormVec (s • timeVec) = |s| := by
    rw [TorusMetric.euclidNormVec, Fin.sum_univ_four]
    simp [PeriodicLattice.coordVec, Real.sqrt_sq_eq_abs]
  rw [← h2, hE, hE, hE, WithLp.toLp_add]
  exact norm_add_le _ _
def liftAbove {n : ℕ} (x : Fin n → R4) (μ : Fin 4) (c r : ℝ) (i : Fin n) : R4 :=
  open Classical in if c < x i μ then x i + r • timeVec else x i
theorem actFn_shiftedEntries (Q : Matrix.orthogonalGroup (Fin 4) ℝ)
    (htr : OrthogonalInvariance.TranslationCompat) {p p' : ℕ}
    (a : Fin p → R4 → ℂ) (b : Fin p' → R4 → ℂ) (hb : ∀ k, b k ∈ C1c ℂ)
    (u : R4) (s : ℝ) :
    (fun l => (EuclidMotion.ofOrthogonalMatrix Q).actFn
        (TangentialAnalyticity.shiftedComponents a b u s l)) =
      TangentialAnalyticity.shiftedComponents
        (fun l => (EuclidMotion.ofOrthogonalMatrix Q).actFn (a l))
        (fun k => (EuclidMotion.ofOrthogonalMatrix Q).actFn (b k))
        (EuclidMotion.ofOrthogonalMatrix Q u) s := by
  funext l
  have hsm : EuclidMotion.ofOrthogonalMatrix Q (s • u) = s • EuclidMotion.ofOrthogonalMatrix Q u := by
    rw [EuclidMotion.ofOrthogonalMatrix_apply, EuclidMotion.ofOrthogonalMatrix_apply,
      Matrix.mulVec_smul]
  refine Fin.addCases (fun k => ?_) (fun k => ?_) l
  · simp [TangentialAnalyticity.shiftedComponents]
  · simp only [TangentialAnalyticity.shiftedComponents, Fin.append_right]
    rw [htr Q (b k) (s • u) (hb k), hsm]
def DefectVanishesNear (S : ConnFamily) (r : EuclidMotion) {n : ℕ} (x : Fin n → R4) : Prop :=
  ∃ ρ : ℝ, 0 < ρ ∧ ∀ f ∈ disjointComplexTuples n, (∀ i, tsupport (f i) ⊆ euclidBall (x i) ρ) →
    rotationDefect S r f = 0
set_option maxHeartbeats 1000000 in
theorem defectVanishesNear_liftAbove
    (hslide : TangentialAnalyticity.Holds)
    (hone : ComplexAnalysis.HolomorphicAndRealAnalyticFacts)
    (htr : OrthogonalInvariance.TranslationCompat)
    (hsupp : OrthogonalInvariance.SupportBallDistanceTuple)
    (himg : OrthogonalInvariance.ComplexTupleImages)
    {m : SharpScale} {S : ConnFamily} (σ : EuclidFunctionalWithRecon m S)
    (hcone : σ.ConeCondition)
    (hsym : MomentSymmetry.PermInvariant S)
    (Q : Matrix.orthogonalGroup (Fin 4) ℝ) {n : ℕ}
    (x : Fin n → R4) (μ : Fin 4) (hμ : ∀ z, EuclidMotion.ofOrthogonalMatrix Q z μ = z μ)
    (he : (timeVec : R4) μ = 0) (c : ℝ) (hne : ∀ i, x i μ ≠ c)
    (hJ : ∃ i, c < x i μ) (hI : ∃ i, x i μ < c) (r₀ r₁ : ℝ)
    (hv : DefectVanishesNear S (EuclidMotion.ofOrthogonalMatrix Q) (liftAbove x μ c r₀)) :
    DefectVanishesNear S (EuclidMotion.ofOrthogonalMatrix Q) (liftAbove x μ c r₁) := by
  classical
  set r := EuclidMotion.ofOrthogonalMatrix Q with hr
  obtain ⟨ρ₁, hρ₁, hv⟩ := hv
  obtain ⟨hh, hh0, hlow⟩ := exists_pos_forall_le (ι := Fin n) (fun _ => True)
    (fun i => |x i μ - c|) (fun i _ => abs_pos.2 (sub_ne_zero.2 (hne i)))
  set ρ := min (ρ₁ / 2) (hh / 2) with hρdef
  have hρ : 0 < ρ := lt_min (by positivity) (by positivity)
  have hρ₂ : ρ ≤ ρ₁ / 2 := min_le_left _ _
  have hρ₃ : ρ ≤ hh / 2 := min_le_right _ _
  set δ := hh - ρ with hδdef
  have hδ : 0 < δ := by rw [hδdef]; linarith
  refine ⟨ρ, hρ, fun g hg hsup => ?_⟩
  let P : Fin n → Prop := fun i => c < x i μ
  obtain ⟨p, p', ε, hIε, hJε, hp, hp'⟩ := exists_equiv_split P
  have hp1 : 1 ≤ p := hp (by
    obtain ⟨i, hi⟩ := hI
    exact ⟨i, not_lt.2 hi.le⟩)
  have hp1' : 1 ≤ p' := hp' hJ
  have hnotP : ∀ i, ¬P i → x i μ ≤ c - hh := by
    intro i hi
    have h1 : x i μ < c := lt_of_le_of_ne (not_lt.1 hi) (hne i)
    have h2 := hlow i trivial
    rw [abs_of_neg (by linarith)] at h2
    linarith
  have hyesP : ∀ i, P i → c + hh ≤ x i μ := by
    intro i hi
    have h2 := hlow i trivial
    rw [abs_of_pos (sub_pos.2 hi)] at h2
    linarith
  have hmovedI : ∀ i s, ¬P i → liftAbove x μ c s i = x i := fun i s hi => if_neg hi
  have hmovedJ : ∀ i s, P i → liftAbove x μ c s i = x i + s • timeVec := fun i s hi => if_pos hi
  set v : R4 := (r₀ - r₁) • timeVec with hvdef
  let G : Fin (p + p') → R4 → ℂ := g ∘ ε
  have hG : G ∈ disjointComplexTuples (p + p') := comp_mem_disjointComplexTuples hg ε ε.injective
  let a : Fin p → R4 → ℂ := fun k => G (Fin.castAdd p' k)
  let b₀ : Fin p' → R4 → ℂ := fun k => G (Fin.natAdd p k)
  let b : Fin p' → R4 → ℂ := fun k => (EuclidMotion.transl v).actFn (b₀ k)
  have ha : a ∈ disjointComplexTuples p :=
    comp_mem_disjointComplexTuples hG _ (Fin.castAdd_injective p p')
  have hb₀ : b₀ ∈ disjointComplexTuples p' :=
    comp_mem_disjointComplexTuples hG _ (Fin.natAdd_injective p' p)
  have hb : b ∈ disjointComplexTuples p' := (himg Q v p' b₀ hb₀).2.2.1
  have hcoord : ∀ {z w : R4}, TorusMetric.euclidNormVec (z - w) < ρ → |z μ - w μ| < ρ :=
    fun {z w} h => (abs_apply_le_euclidNormVec (z - w) μ).trans_lt h
  have hsa : ∀ l, supp (a l) ⊆ {z | z μ < c - δ} := by
    intro l z hz
    rw [supp_eq_tsupport] at hz
    have hi := hIε l
    have hz' := hsup (ε (Fin.castAdd p' l)) hz
    rw [hmovedI _ _ hi] at hz'
    have h1 := abs_lt.1 (hcoord hz')
    have h2 := hnotP _ hi
    show z μ < c - δ
    rw [hδdef]
    linarith [h1.2]
  have hsb : ∀ k, supp (b k) ⊆ {z | c + δ < z μ} := by
    intro k z hz
    rw [supp_eq_tsupport] at hz
    have hi := hJε k
    have hz₁ := (mem_tsupport_actFn_transl v z _).1 hz
    have hz' := hsup (ε (Fin.natAdd p k)) hz₁
    rw [hmovedJ _ _ hi] at hz'
    have h1 := abs_lt.1 (hcoord hz')
    have h2 := hyesP _ hi
    have h3 : (z - v) μ = z μ := by simp [hvdef, he]
    have h4 : (x (ε (Fin.natAdd p k)) + r₁ • timeVec) μ = x (ε (Fin.natAdd p k)) μ := by
      simp [he]
    rw [h3, h4] at h1
    show c + δ < z μ
    rw [hδdef]
    linarith [h1.1]
  let ra : Fin p → R4 → ℂ := fun l => r.actFn (a l)
  let rb : Fin p' → R4 → ℂ := fun k => r.actFn (b k)
  have hra : ra ∈ disjointComplexTuples p := (himg Q 0 p a ha).1
  have hrb : rb ∈ disjointComplexTuples p' := (himg Q 0 p' b hb).1
  have hsra : ∀ l, supp (ra l) ⊆ {z | z μ < c - δ} := by
    intro l z hz
    have : supp (ra l) = r '' supp (a l) := (hsupp Q).1 _ (ha.1 l)
    rw [this] at hz
    obtain ⟨w, hw, rfl⟩ := hz
    show r w μ < c - δ
    rw [hμ]
    exact hsa l hw
  have hsrb : ∀ k, supp (rb k) ⊆ {z | c + δ < z μ} := by
    intro k z hz
    have : supp (rb k) = r '' supp (b k) := (hsupp Q).1 _ (hb.1 k)
    rw [this] at hz
    obtain ⟨w, hw, rfl⟩ := hz
    show c + δ < r w μ
    rw [hμ]
    exact hsb k hw
  have hru : r timeVec μ = 0 := by rw [hμ, he]
  obtain ⟨hA, ρa, hρa, Ga, hGa, hGav⟩ :=
    sigmaAt_shiftedComponents_holomorphic hslide σ hcone μ c δ hδ hp1 hp1' ha hb hsa hsb he
  obtain ⟨-, ρb, hρb, Gb, hGb, hGbv⟩ :=
    sigmaAt_shiftedComponents_holomorphic hslide σ hcone μ c δ hδ hp1 hp1' hra hrb hsra hsrb hru
  let A : ℝ → Fin (p + p') → R4 → ℂ := TangentialAnalyticity.shiftedComponents a b timeVec
  let w : ℝ → Fin n → R4 → ℂ := fun s => A s ∘ ε.symm
  have hwT : ∀ s, w s ∈ disjointComplexTuples n := fun s =>
    comp_mem_disjointComplexTuples (hA s) ε.symm ε.symm.injective
  have hw : ∀ s i, w s i = if P i then
      (EuclidMotion.transl (s • timeVec)).actFn ((EuclidMotion.transl v).actFn (g i))
      else g i := by
    intro s i
    obtain ⟨k, rfl⟩ := ε.surjective i
    show A s (ε.symm (ε k)) = _
    rw [Equiv.symm_apply_apply]
    refine Fin.addCases (fun l => ?_) (fun l => ?_) k
    · rw [if_neg (hIε l)]
      simp [A, TangentialAnalyticity.shiftedComponents, a, G]
    · rw [if_pos (hJε l)]
      simp [A, TangentialAnalyticity.shiftedComponents, b, b₀, G]
  have h2 : 2 ≤ p + p' := by omega
  have hsig : ∀ s, rotationDefect S r (w s) = Gb s - Ga s := by
    intro s
    have e₁ : sigmaAt S (w s) = sigmaAt S (A s) := sigmaAt_comp_equiv S hsym h2 ε.symm _ (hA s)
    have hrA : (fun l => r.actFn (A s l)) =
        TangentialAnalyticity.shiftedComponents ra rb (r timeVec) s :=
      actFn_shiftedEntries Q htr a b hb.1 timeVec s
    have hrAm : (fun l => r.actFn (A s l)) ∈ disjointComplexTuples (p + p') :=
      (himg Q 0 _ (A s) (hA s)).1
    have e₂ : sigmaAt S (fun l => r.actFn (w s l)) =
        sigmaAt S (fun l => r.actFn (A s l)) := by
      have e₃ : (fun l => r.actFn (w s l)) = (fun l => r.actFn (A s l)) ∘ ε.symm := rfl
      rw [e₃]
      exact sigmaAt_comp_equiv S hsym h2 ε.symm _ hrAm
    rw [rotationDefect, e₁, e₂, hrA, hGav, hGbv]
  have hsmall : ∀ s ∈ Set.Ioo (-ρ) ρ, rotationDefect S r (w s) = 0 := by
    intro s hs
    refine hv (w s) (hwT s) fun i z hz => ?_
    have hs' : |s| < ρ := abs_lt.2 hs
    rw [hw s i] at hz
    show TorusMetric.euclidNormVec (z - liftAbove x μ c r₀ i) < ρ₁
    by_cases hi : P i
    · rw [if_pos hi] at hz
      have hz₁ := (mem_tsupport_actFn_transl _ _ _).1 hz
      have hz₂ := (mem_tsupport_actFn_transl _ _ _).1 hz₁
      have hz₃ : TorusMetric.euclidNormVec (z - s • timeVec - v - liftAbove x μ c r₁ i) < ρ :=
        hsup i hz₂
      rw [hmovedJ i _ hi] at hz₃
      rw [hmovedJ i _ hi]
      have e : z - (x i + r₀ • timeVec) =
          (z - s • timeVec - v - (x i + r₁ • timeVec)) + s • timeVec := by
        rw [hvdef, sub_smul]
        abel
      rw [e]
      have := euclidNormVec_add_smul_timeVec_le (z - s • timeVec - v - (x i + r₁ • timeVec)) s
      linarith
    · rw [if_neg hi] at hz
      have hz₃ : TorusMetric.euclidNormVec (z - liftAbove x μ c r₁ i) < ρ := hsup i hz
      rw [hmovedI i _ hi] at hz₃
      rw [hmovedI i _ hi]
      linarith
  have hall : ∀ s, rotationDefect S r (w s) = 0 := by
    refine hone.2.1 (fun s => rotationDefect S r (w s)) (fun s₀ => ?_) ⟨-ρ, ρ, by linarith, hsmall⟩
    refine ⟨min ρa ρb, lt_min hρa hρb, fun z => Gb z - Ga z, ?_, fun s _ => (hsig s).symm⟩
    exact ((hGb s₀).mono (Metric.ball_subset_ball (min_le_right _ _))).sub
      ((hGa s₀).mono (Metric.ball_subset_ball (min_le_left _ _)))
  have hfinal : w (r₁ - r₀) = g := by
    funext i
    rw [hw]
    by_cases hi : P i
    · rw [if_pos hi]
      funext y
      rw [EuclidMotion.actFn_transl, EuclidMotion.actFn_transl]
      congr 1
      rw [hvdef, sub_smul, sub_smul]
      abel
    · rw [if_neg hi]
  have := hall (r₁ - r₀)
  rwa [hfinal] at this
theorem planeComponent_eq_iff (z z' : R4) :
    planeComponent z = planeComponent z' ↔ z 3 = z' 3 ∧ z 0 = z' 0 := by
  constructor
  · intro h
    have h0 := congrArg (fun y : RealPlane => y 0) h
    have h1 := congrArg (fun y : RealPlane => y 1) h
    exact ⟨by simpa [planeComponent] using h0, by simpa [planeComponent] using h1⟩
  · rintro ⟨h0, h1⟩
    simp [planeComponent, h0, h1]
def coincidentPairs {n : ℕ} (x : Fin n → R4) : Finset (Fin n × Fin n) :=
  open Classical in
  Finset.univ.filter fun q => q.1 ≠ q.2 ∧ planeComponent (x q.1) = planeComponent (x q.2)
theorem liftAbove_zero {n : ℕ} (x : Fin n → R4) (μ : Fin 4) (c : ℝ) : liftAbove x μ c 0 = x := by
  funext i
  simp [liftAbove]
theorem forall_injective_of_coincidentPairs {n : ℕ} (V : (Fin n → R4) → Prop)
    (hbase : ∀ x, Function.Injective (fun i => planeComponent (x i)) → V x)
    (hclaim : ∀ (x : Fin n → R4) (μ : Fin 4), (μ = 1 ∨ μ = 2) → ∀ c : ℝ, (∀ i, x i μ ≠ c) →
      (∃ i, c < x i μ) → (∃ i, x i μ < c) → ∀ r₀ r₁ : ℝ,
      V (liftAbove x μ c r₀) → V (liftAbove x μ c r₁)) :
    ∀ x : Fin n → R4, Function.Injective x → V x := by
  classical
  have key : ∀ N : ℕ, ∀ x : Fin n → R4, Function.Injective x →
      (coincidentPairs x).card = N → V x := by
    intro N
    induction N using Nat.strong_induction_on with
    | _ N ih =>
      intro x hx hN
      by_cases hinj : Function.Injective (fun i => planeComponent (x i))
      · exact hbase x hinj
      have step : ∀ (i i' : Fin n) (μ : Fin 4), (μ = 1 ∨ μ = 2) → i ≠ i' →
          planeComponent (x i) = planeComponent (x i') → x i μ < x i' μ → V x := by
        intro i i' μ hμ hne hplane hlt
        obtain ⟨c, hc, hcn⟩ := (Set.Ioo_infinite hlt).exists_notMem_finset
          (Finset.univ.image fun l => x l μ)
        have hcne : ∀ l, x l μ ≠ c := fun l e =>
          hcn (Finset.mem_image.2 ⟨l, Finset.mem_univ _, e⟩)
        obtain ⟨r₀, hr₀, hrn⟩ := (Set.Ioo_infinite (zero_lt_one' ℝ)).exists_notMem_finset
          (Finset.univ.image fun q : Fin n × Fin n => x q.1 3 - x q.2 3)
        have hrne : ∀ l l', x l' 3 ≠ x l 3 + r₀ := fun l l' e =>
          hrn (Finset.mem_image.2 ⟨(l', l), Finset.mem_univ _, by simp [e]⟩)
        have hμ3 : μ ≠ 3 := by rcases hμ with rfl | rfl <;> decide
        have hμ0 : μ ≠ 0 := by rcases hμ with rfl | rfl <;> decide
        have he : (timeVec : R4) μ = 0 := by
          simp [PeriodicLattice.coordVec, hμ3]
        have h30 : (timeVec : R4) 3 = 1 := by simp [PeriodicLattice.coordVec]
        have h00 : (timeVec : R4) 0 = 0 := by simp [PeriodicLattice.coordVec]
        set y := liftAbove x μ c r₀ with hy
        have hyP : ∀ l, c < x l μ → y l = x l + r₀ • timeVec := fun l hl => if_pos hl
        have hyN : ∀ l, ¬c < x l μ → y l = x l := fun l hl => if_neg hl
        have hcross : ∀ l l', c < x l μ → ¬c < x l' μ →
            planeComponent (y l) ≠ planeComponent (y l') := by
          intro l l' hl hl' e
          rw [hyP l hl, hyN l' hl', planeComponent_eq_iff] at e
          have := e.1
          simp [h30] at this
          exact hrne l l' this.symm
        have hyinj : Function.Injective y := by
          intro l l' e
          by_cases hl : c < x l μ <;> by_cases hl' : c < x l' μ
          · rw [hyP l hl, hyP l' hl'] at e
            exact hx (add_right_cancel e)
          · exact absurd (congrArg planeComponent e) (hcross l l' hl hl')
          · exact absurd (congrArg planeComponent e).symm (hcross l' l hl' hl)
          · rw [hyN l hl, hyN l' hl'] at e
            exact hx e
        have hsub : coincidentPairs y ⊂ coincidentPairs x := by
          refine Finset.ssubset_iff_of_subset ?_ |>.2 ⟨(i, i'), ?_, ?_⟩
          · intro q hq
            simp only [coincidentPairs, Finset.mem_filter, Finset.mem_univ, true_and] at hq ⊢
            refine ⟨hq.1, ?_⟩
            by_cases hl : c < x q.1 μ <;> by_cases hl' : c < x q.2 μ
            · have e := hq.2
              rw [hyP _ hl, hyP _ hl', planeComponent_eq_iff] at e
              rw [planeComponent_eq_iff]
              refine ⟨?_, ?_⟩
              · have := e.1
                simpa using this
              · have := e.2
                simpa [h00] using this
            · exact absurd hq.2 (hcross _ _ hl hl')
            · exact absurd hq.2.symm (hcross _ _ hl' hl)
            · have e := hq.2
              rwa [hyN _ hl, hyN _ hl'] at e
          · simp only [coincidentPairs, Finset.mem_filter, Finset.mem_univ, true_and]
            exact ⟨hne, hplane⟩
          · simp only [coincidentPairs, Finset.mem_filter, Finset.mem_univ, true_and, not_and]
            intro _ e
            exact hcross i' i hc.2 (not_lt.2 hc.1.le) e.symm
        have hlt' : (coincidentPairs y).card < N := hN ▸ Finset.card_lt_card hsub
        have hVy : V y := ih _ hlt' y hyinj rfl
        have := hclaim x μ hμ c hcne ⟨i', hc.2⟩ ⟨i, hc.1⟩ r₀ 0 hVy
        rwa [liftAbove_zero] at this
      obtain ⟨i, i', hpl, hne⟩ : ∃ i i', planeComponent (x i) = planeComponent (x i') ∧ i ≠ i' := by
        simpa [Function.Injective] using hinj
      have hxne : x i ≠ x i' := hx.ne hne
      have hex : ∃ μ : Fin 4, (μ = 1 ∨ μ = 2) ∧ x i μ ≠ x i' μ := by
        by_contra hcon
        push Not at hcon
        have hp := (planeComponent_eq_iff _ _).1 hpl
        apply hxne
        funext ν
        fin_cases ν
        · exact hp.2
        · exact hcon 1 (Or.inl rfl)
        · exact hcon 2 (Or.inr rfl)
        · exact hp.1
      obtain ⟨μ, hμ, hμne⟩ := hex
      rcases lt_or_gt_of_ne hμne with h | h
      · exact step i i' μ hμ hne hpl h
      · exact step i' i μ hμ hne.symm hpl.symm h
  exact fun x hx => key _ x hx rfl
theorem invariantOnComplexTuples
    (hsing : HarmonicDensity.Holds)
    (hiso : OrthogonalInvariance.Holds)
    (hmom : OrthogonalInvariance.OrthogonalMapStatement)
    (hslide : TangentialAnalyticity.Holds)
    (hglobal : LocalVanishing.VanishingFromLocalVanishing)
    (hone : ComplexAnalysis.HolomorphicAndRealAnalyticFacts)
    (happ : ProductSumApprox.ProductSumsDenseC1)
    (hb : Moments.MomentBoundsTheorem)
    (hpl : TranslationRules.TranslationAndMotionFacts)
    (hinv : MomentSymmetry.ReductionHolds) :
    RotationFromProducts.InvariantOnComplexTuples := by
  intro m S d φ₀ htop n hn t f hf
  obtain ⟨hact, hsupp, -, htr, hrules, hrot, himg, -, -, hgrad, -⟩ := hiso
  obtain ⟨Q, hQ⟩ := exists_orthogonalMatrix_eq_rotateMotion hrules t
  have hlin : OrthogonalInvariance.EntrywiseLinear S :=
    (hmom m S d.fnl Q).2.2.2.1
  have hsym := (hinv m S d.fnl).1
  set r := EuclidMotion.ofOrthogonalMatrix Q with hr
  have hQ' : ∀ n, ∀ h ∈ disjointComplexTuples n,
      (fun l => r.actFn (h l)) ∈ disjointComplexTuples n :=
    fun n h hh => (himg Q 0 n h hh).1
  have hfix : ∀ (z : R4) (μ : Fin 4), (μ = 1 ∨ μ = 2) → r z μ = z μ := by
    rintro z μ (rfl | rfl)
    · have h := ((hrules t).2.2.1 z).1
      rw [← hQ] at h
      exact h
    · have h := ((hrules t).2.2.1 z).2
      rw [← hQ] at h
      exact h
  have hplates : ∀ α : Fin n → RealPlane → ℂ, (∀ i, α i ∈ complexProfiles) →
      (Pairwise fun i j => Disjoint (tsupport (α i)) (tsupport (α j))) →
      ∀ φ : Fin n → realLabels, rotationDefect S r (fun l => productFunction (α l) (φ l)) = 0 := by
    obtain ⟨q, rfl⟩ : ∃ q, n = q + 1 := ⟨n - 1, by omega⟩
    intro α hα hdis φ
    have h := sigmaAt_products_rotate hsing hrot d φ₀ (by omega) (htop _ hn) t α hα hdis φ
    rw [← hQ] at h
    exact sub_eq_zero.2 h
  have hV : ∀ x : Fin n → R4, Function.Injective x → DefectVanishesNear S r x := by
    refine forall_injective_of_coincidentPairs _ (fun x hx => ?_) ?_
    · exact rotationDefect_eq_zero_of_injective_planeComponent d.fnl Q hb happ hpl.2.2.1 hgrad
        hact hsupp hlin hQ' hn hplates x hx
    · intro x μ hμ c hne hJ hI r₀ r₁ hv
      have hμ3 : μ ≠ 3 := by rcases hμ with rfl | rfl <;> decide
      exact defectVanishesNear_liftAbove hslide hone htr hsupp himg d.fnl d.coneCond hsym Q x μ
        (fun z => hfix z μ hμ) (by simp [PeriodicLattice.coordVec, hμ3]) c hne hJ hI r₀ r₁ hv
  let D : disjointSupportTuples 4 n → ℂ := fun u => rotationDefect S r u.1
  have hDlin : IsSeparatelyLinear D := by
    intro i lam u g hu hg
    exact rotationDefect_add_smul hlin hQ' i lam u g ((mem_disjointSupportTuples_iff_mem _).1 hu)
      ((mem_disjointSupportTuples_iff_mem _).1 hg)
  have hnear : ∀ x : injectiveTuples (Fin 4 → ℝ) n, VanishesNearConfig D x := by
    intro x
    obtain ⟨ρ, hρ, h⟩ := hV x.1 x.2
    exact ⟨ρ, hρ, fun u hu => h u.1 ((mem_disjointSupportTuples_iff_mem _).1 u.2) hu⟩
  have hzero := (hglobal 4 (Or.inr rfl) n hn D hDlin).2 hnear
    ⟨f, (mem_disjointSupportTuples_iff_mem _).2 hf⟩
  have hz : sigmaAt S (fun l => r.actFn (f l)) - sigmaAt S f = 0 := hzero
  have hz' := sub_eq_zero.1 hz
  rw [hQ] at hz'
  exact hz'
end YangMills.Construction.EuclideanFunctionals.RotationFromProductsProof
end
