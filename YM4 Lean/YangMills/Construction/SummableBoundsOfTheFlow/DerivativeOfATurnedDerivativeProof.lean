import YangMills.Construction.ClusterExpansionOfAStep.PlaquettesUnderGaugesAndMoves
import YangMills.Construction.ColdStepAtMirrorFrames.LogarithmOfAMovedExponential
import YangMills.Construction.SummableBoundsOfTheFlow.DerivativeOfATurnedDerivative
import YangMills.Construction.SummableBoundsOfTheFlow.DerivativesAlongAList
import YangMills.Construction.SummableBoundsOfTheFlow.ExpansionAlongAMotion
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion Topology
namespace YangMills.Construction
open BlockAverages ColdStepAtMirrorFrames IteratedDerivative Estimates
namespace TranslatedDerivative
variable {F : BlockFrame} {j k : ℕ}
def paramMap (c : F.Site j × Fin 4) (X : imaginaryQuaternions) (c' : Fin k → F.Site j × Fin 4)
    (X' : Fin k → imaginaryQuaternions) (y : F.Site j) (i : Fin 4) :
    (Fin (k + 1) → ℝ) →L[ℝ] imaginaryQuaternions × imaginaryQuaternions × imaginaryQuaternions := by
  classical
  exact ContinuousLinearMap.prod
    ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (k + 1) => ℝ) 0).smulRight
      (if c = (y, i) then X else 0))
    (ContinuousLinearMap.prod
      (∑ l : Fin k, (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (k + 1) => ℝ) l.succ).smulRight
        (if c' l = (y, i) then X' l else 0)) 0)
theorem paramMap_apply (c : F.Site j × Fin 4) (X : imaginaryQuaternions) (c' : Fin k → F.Site j × Fin 4)
    (X' : Fin k → imaginaryQuaternions) (y : F.Site j) (i : Fin 4) (τ : Fin (k + 1) → ℝ) :
    paramMap c X c' X' y i τ = (bondSpread (fun _ : Fin 1 => c) (fun _ => X) (fun _ => τ 0) y i,
      bondSpread c' X' (Fin.tail τ) y i, 0) := by
  classical
  simp only [paramMap, ColdStepAtMirrorFrames.bondSpread, ContinuousLinearMap.prod_apply, ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.proj_apply, ContinuousLinearMap.zero_apply]
  refine Prod.ext ?_ (Prod.ext ?_ rfl)
  · simp
  · simp only [Fin.tail]
    simp
def paramBond (c : F.Site j × Fin 4) (c' : Fin k → F.Site j × Fin 4) : Fin (k + 1) → F.Site j × Fin 4 :=
  Fin.cons c c'
theorem paramMap_single_zero (c : F.Site j × Fin 4) (X : imaginaryQuaternions) (c' : Fin k → F.Site j × Fin 4)
    (X' : Fin k → imaginaryQuaternions) (y : F.Site j) (i : Fin 4) : open Classical in
    paramMap c X c' X' y i (Pi.single 0 1) = (if c = (y, i) then X else 0, 0, 0) := by
  classical
  simp only [paramMap, ContinuousLinearMap.prod_apply, ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.proj_apply, ContinuousLinearMap.zero_apply]
  refine Prod.ext ?_ (Prod.ext ?_ rfl)
  · simp
  · have : ∀ l : Fin k, (Pi.single (0 : Fin (k + 1)) (1 : ℝ) : Fin (k + 1) → ℝ) l.succ = 0 := fun l =>
      Pi.single_eq_of_ne (Fin.succ_ne_zero l) _
    simp [this]
theorem paramMap_single_succ (c : F.Site j × Fin 4) (X : imaginaryQuaternions) (c' : Fin k → F.Site j × Fin 4)
    (X' : Fin k → imaginaryQuaternions) (y : F.Site j) (i : Fin 4) (l : Fin k) : open Classical in
    paramMap c X c' X' y i (Pi.single l.succ 1) = (0, if c' l = (y, i) then X' l else 0, 0) := by
  classical
  simp only [paramMap, ContinuousLinearMap.prod_apply, ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.proj_apply, ContinuousLinearMap.zero_apply]
  refine Prod.ext ?_ (Prod.ext ?_ rfl)
  · have : (Pi.single l.succ (1 : ℝ) : Fin (k + 1) → ℝ) 0 = 0 :=
      Pi.single_eq_of_ne (Fin.succ_ne_zero l).symm _
    simp [this]
  · simp only [ContinuousLinearMap.coe_sum', Finset.sum_apply, ContinuousLinearMap.smulRight_apply,
      ContinuousLinearMap.proj_apply]
    rw [Finset.sum_eq_single l]
    · simp
    · intro l' _ hl
      have : l'.succ ≠ l.succ := fun h => hl (Fin.succ_injective _ h)
      simp [Pi.single_eq_of_ne this]
    · simp
theorem paramMap_single_eq_zero (c : F.Site j × Fin 4) (X : imaginaryQuaternions)
    (c' : Fin k → F.Site j × Fin 4) (X' : Fin k → imaginaryQuaternions)
    (y : F.Site j) (i : Fin 4) (l : Fin (k + 1)) (h : paramBond c c' l ≠ (y, i)) :
    paramMap c X c' X' y i (Pi.single l 1) = 0 := by
  classical
  refine Fin.cases (motive := fun l => paramBond c c' l ≠ (y, i) → paramMap c X c' X' y i (Pi.single l 1) = 0)
    (fun h => ?_) (fun l' h => ?_) l h
  · rw [paramMap_single_zero, if_neg (by simpa [paramBond] using h)]
    rfl
  · rw [paramMap_single_succ, if_neg (by simpa [paramBond] using h)]
    rfl
theorem norm_paramMap_single_le (c : F.Site j × Fin 4) (X : imaginaryQuaternions)
    (c' : Fin k → F.Site j × Fin 4) (X' : Fin k → imaginaryQuaternions)
    (hX : ‖X‖ = 1) (hX' : AreUnitVectors X') (y : F.Site j) (i : Fin 4) (l : Fin (k + 1)) :
    ‖paramMap c X c' X' y i (Pi.single l 1)‖ ≤ 1 := by
  classical
  refine Fin.cases (motive := fun l => ‖paramMap c X c' X' y i (Pi.single l 1)‖ ≤ 1) ?_ (fun l' => ?_) l
  · rw [paramMap_single_zero]
    simp only [Prod.norm_def, norm_zero]
    split_ifs <;> simp [hX]
  · rw [paramMap_single_succ]
    simp only [Prod.norm_def, norm_zero]
    split_ifs <;> simp [hX' l']
def pairedMotion (Θ : imaginaryQuaternions × imaginaryQuaternions × imaginaryQuaternions → imaginaryQuaternions)
    (c : F.Site j × Fin 4) (X : imaginaryQuaternions) (c' : Fin k → F.Site j × Fin 4)
    (X' : Fin k → imaginaryQuaternions) (τ : Fin (k + 1) → ℝ) (y : F.Site j) (i : Fin 4) :
    imaginaryQuaternions :=
  Θ (paramMap c X c' X' y i τ)
variable {Θ : imaginaryQuaternions × imaginaryQuaternions × imaginaryQuaternions → imaginaryQuaternions}
theorem motionComponent_pairedMotion (hL : DerivAlongRulesHold) (c : F.Site j × Fin 4) (X : imaginaryQuaternions)
    (c' : Fin k → F.Site j × Fin 4) (X' : Fin k → imaginaryQuaternions) (y : F.Site j) (i : Fin 4) (r : ℕ)
    (e : Fin r → Fin (k + 1)) (hs : ContDiffAt ℝ (r : WithTop ℕ∞) Θ 0) :
    motionComponent (pairedMotion Θ c X c' X') e y i =
      iteratedFDeriv ℝ r Θ 0 fun l => paramMap c X c' X' y i (Pi.single (e l) 1) := by
  have hc : ContDiffAt ℝ (r : WithTop ℕ∞) (fun τ => Θ (paramMap c X c' X' y i τ))
      (0 : Fin (k + 1) → ℝ) := by
    have h0 : ContDiffAt ℝ (r : WithTop ℕ∞) Θ (paramMap c X c' X' y i 0) := by simpa using hs
    exact ContDiffAt.comp (0 : Fin (k + 1) → ℝ) h0 (paramMap c X c' X' y i).contDiff.contDiffAt
  unfold motionComponent
  simp only [pairedMotion]
  rw [(hL.1 _ imaginaryQuaternions).iteratedFDeriv_eq _ _ _ _ hc,
    (hL.1 _ imaginaryQuaternions).iteratedFDeriv_eq _ _ _ _ hs]
  have e1 := hL.2 _ _ imaginaryQuaternions Θ (paramMap c X c' X' y i) 0 0
    (List.ofFn fun l => (Pi.single (e l) (1 : ℝ) : Fin (k + 1) → ℝ)) (by simpa using hs)
  simp only [zero_add, map_zero] at e1
  rw [e1, List.map_ofFn]
  rfl
theorem norm_motionComponent_le (hL : DerivAlongRulesHold) {C₀ : ℝ} (c : F.Site j × Fin 4)
    (X : imaginaryQuaternions) (c' : Fin k → F.Site j × Fin 4) (X' : Fin k → imaginaryQuaternions)
    (hX : ‖X‖ = 1) (hX' : AreUnitVectors X') (y : F.Site j) (i : Fin 4) (r : ℕ) (e : Fin r → Fin (k + 1))
    (hs : ContDiffAt ℝ (r : WithTop ℕ∞) Θ 0) (hb : ‖iteratedFDeriv ℝ r Θ 0‖ ≤ C₀) :
    ‖motionComponent (pairedMotion Θ c X c' X') e y i‖ ≤ C₀ := by
  rw [motionComponent_pairedMotion hL c X c' X' y i r e hs]
  refine ((iteratedFDeriv ℝ r Θ 0).le_opNorm _).trans ?_
  have h1 : ∏ l, ‖paramMap c X c' X' y i (Pi.single (e l) 1)‖ ≤ 1 :=
    Finset.prod_le_one (fun _ _ => norm_nonneg _) fun l _ => norm_paramMap_single_le c X c' X' hX hX' y i (e l)
  calc _ ≤ ‖iteratedFDeriv ℝ r Θ 0‖ * 1 :=
        mul_le_mul_of_nonneg_left h1 (ContinuousMultilinearMap.opNorm_nonneg _)
    _ ≤ C₀ := by simpa using hb
theorem motionComponent_eq_zero (hL : DerivAlongRulesHold) (c : F.Site j × Fin 4) (X : imaginaryQuaternions)
    (c' : Fin k → F.Site j × Fin 4) (X' : Fin k → imaginaryQuaternions) (y : F.Site j) (i : Fin 4) (r : ℕ)
    (e : Fin r → Fin (k + 1)) (hs : ContDiffAt ℝ (r : WithTop ℕ∞) Θ 0) (l : Fin r)
    (h : paramBond c c' (e l) ≠ (y, i)) : motionComponent (pairedMotion Θ c X c' X') e y i = 0 := by
  rw [motionComponent_pairedMotion hL c X c' X' y i r e hs]
  exact (iteratedFDeriv ℝ r Θ 0).map_coord_zero l (paramMap_single_eq_zero c X c' X' y i (e l) h)
theorem abs_mixedDerivAlong_le (hL : DerivAlongRulesHold) (hExp : expansionAlongMotionStatement) {C₀ : ℝ}
    (hs3 : ContDiffAt ℝ ((3 : ℕ) : WithTop ℕ∞) Θ 0) (hb : ∀ r : ℕ, r ≤ 3 → ‖iteratedFDeriv ℝ r Θ 0‖ ≤ C₀)
    (g : F.GaugeField j → ℝ) (W : F.GaugeField j) (c : F.Site j × Fin 4) (X : imaginaryQuaternions)
    (c' : Fin k → F.Site j × Fin 4) (X' : Fin k → imaginaryQuaternions)
    (Bd : ∀ i : ℕ, (Fin i → F.Site j × Fin 4) → ℝ) (R : ℝ) (hk : k ≤ 2)
    (hper : ∀ i, F.period j i ≠ 0) (hX : ‖X‖ = 1) (hX' : AreUnitVectors X') (hR : 0 ≤ R)
    (hsm : ∀ (q : ℕ) (c'' : Fin q → F.Site j × Fin 4) (X'' : Fin q → imaginaryQuaternions),
      ContDiffAt ℝ ((3 : ℕ) : WithTop ℕ∞) (fun τ : Fin q → ℝ => g (leftTranslate (bondSpread c'' X'' τ) W)) 0)
    (hBd : ∀ (i : ℕ) (bs : Fin i → F.Site j × Fin 4) (Xs : Fin i → imaginaryQuaternions), 1 ≤ i → i ≤ 3 →
      AreUnitVectors Xs → |bondDeriv g W bs Xs| ≤ Bd i bs)
    (hRd : ∀ (i : ℕ) (bs : Fin i → F.Site j × Fin 4), 1 ≤ i → i ≤ 3 →
      (∀ l : Fin (k + 1), ∃ m, paramBond c c' l = bs m) → Bd i bs ≤ R)
    (o : OrderedFinpartition (k + 1)) :
    |mixedDerivAlong g W (fun m => motionComponent (pairedMotion Θ c X c' X') (o.emb m))| ≤ (C₀ + 1) ^ 3 * R := by
  classical
  have hC₀ : 0 ≤ C₀ := (ContinuousMultilinearMap.opNorm_nonneg _).trans (hb 0 (by omega))
  have hfin : Finite (F.Site j) := by
    have : ∀ i, Finite (ZMod (F.period j i)) := fun i => by
      have : NeZero (F.period j i) := ⟨hper i⟩
      infer_instance
    exact Pi.finite
  have hft : Fintype (F.Site j × Fin 4) := Fintype.ofFinite _
  have hi1 : 1 ≤ o.length := by
    obtain ⟨m, -⟩ := o.cover 0
    exact Nat.one_le_iff_ne_zero.2 fun h => by
      have := m.isLt
      omega
  have hi3 : o.length ≤ 3 := o.length_le.trans (by omega)
  have hr3 : ∀ m, o.partSize m ≤ 3 := fun m => (o.partSize_le m).trans (by omega)
  have hsr : ∀ m, ContDiffAt ℝ ((o.partSize m : ℕ) : WithTop ℕ∞) Θ 0 := fun m =>
    hs3.of_le (by exact_mod_cast hr3 m)
  set A : ∀ m : Fin o.length, F.Site j → Fin 4 → imaginaryQuaternions :=
    fun m => motionComponent (pairedMotion Θ c X c' X') (o.emb m) with hA
  have h1 := hExp.2 F j o.length g W A Finset.univ (Bd o.length) hper (fun b => Finset.mem_univ b)
    (fun q c'' X'' => (hsm q c'' X'').of_le (by exact_mod_cast hi3))
    (fun bs Xs hXs => hBd _ bs Xs hi1 hi3 hXs)
  refine h1.trans ?_
  have hterm : ∀ bs ∈ Fintype.piFinset fun _ : Fin o.length => (Finset.univ : Finset (F.Site j × Fin 4)),
      Bd o.length bs * ∏ l, ‖A l (bs l).1 (bs l).2‖ ≤ R * ∏ l, ‖A l (bs l).1 (bs l).2‖ := by
    intro bs _
    by_cases hz : ∀ m, A m (bs m).1 (bs m).2 ≠ 0
    · have hall : ∀ m (a : Fin (o.partSize m)), paramBond c c' (o.emb m a) = bs m := by
        intro m a
        by_contra hne
        exact hz m (motionComponent_eq_zero hL c X c' X' _ _ _ (o.emb m) (hsr m) a hne)
      have hcont : ∀ l : Fin (k + 1), ∃ m, paramBond c c' l = bs m := by
        intro l
        obtain ⟨m, a, rfl⟩ := o.cover l
        exact ⟨m, hall m a⟩
      exact mul_le_mul_of_nonneg_right (hRd _ bs hi1 hi3 hcont)
        (Finset.prod_nonneg fun _ _ => norm_nonneg _)
    · push_neg at hz
      obtain ⟨m, hm⟩ := hz
      have : ∏ l, ‖A l (bs l).1 (bs l).2‖ = 0 :=
        Finset.prod_eq_zero (Finset.mem_univ m) (by rw [hm, norm_zero])
      rw [this, mul_zero, mul_zero]
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [← Finset.mul_sum, mul_comm]
  refine mul_le_mul_of_nonneg_right ?_ hR
  rw [← Finset.prod_univ_sum (fun _ : Fin o.length => (Finset.univ : Finset (F.Site j × Fin 4)))
    (fun l b => ‖A l b.1 b.2‖)]
  have hone : ∀ m : Fin o.length, ∑ b : F.Site j × Fin 4, ‖A m b.1 b.2‖ ≤ C₀ + 1 := by
    intro m
    have hp := o.partSize_pos m
    set a₀ : Fin (o.partSize m) := ⟨0, hp⟩
    rw [Finset.sum_eq_single (paramBond c c' (o.emb m a₀))]
    · have := norm_motionComponent_le hL c X c' X' hX hX' (paramBond c c' (o.emb m a₀)).1
        (paramBond c c' (o.emb m a₀)).2 _ (o.emb m) (hsr m) (hb _ (hr3 m))
      linarith
    · intro b _ hne
      have := motionComponent_eq_zero hL c X c' X' b.1 b.2 _ (o.emb m) (hsr m) a₀ (fun h => hne (by rw [h]))
      simp only [hA]
      rw [this, norm_zero]
    · simp
  have h2 : ∏ m : Fin o.length, ∑ b : F.Site j × Fin 4, ‖A m b.1 b.2‖ ≤ ∏ _m : Fin o.length, (C₀ + 1) :=
    Finset.prod_le_prod (fun m _ => Finset.sum_nonneg fun _ _ => norm_nonneg _) fun m _ => hone m
  refine h2.trans ?_
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  exact pow_le_pow_right₀ (by linarith) hi3
def twoStepTranslate (c : F.Site j × Fin 4) (X : imaginaryQuaternions) (c' : Fin k → F.Site j × Fin 4)
    (X' : Fin k → imaginaryQuaternions) (W : F.GaugeField j) (τ : Fin (k + 1) → ℝ) : F.GaugeField j :=
  leftTranslate (bondSpread (fun _ : Fin 1 => c) (fun _ => X) (fun _ => τ 0))
    (leftTranslate (bondSpread c' X' (Fin.tail τ)) W)
theorem expUnit_zero : expUnit (0 : imaginaryQuaternions) = 1 := by apply _root_.YangMills.Construction.TorusFields.expUnit_zero <;> assumption
theorem twoStepTranslate_eq {U : Set (imaginaryQuaternions × imaginaryQuaternions × imaginaryQuaternions)}
    (hexp : ∀ z ∈ U, expUnit (Θ z) = expUnit z.1 * expUnit z.2.1 * (expUnit z.2.2)⁻¹)
    (c : F.Site j × Fin 4) (X : imaginaryQuaternions) (c' : Fin k → F.Site j × Fin 4)
    (X' : Fin k → imaginaryQuaternions) (W : F.GaugeField j)
    (τ : Fin (k + 1) → ℝ) (h : ∀ y i, paramMap c X c' X' y i τ ∈ U) :
    twoStepTranslate c X c' X' W τ = leftTranslate (pairedMotion Θ c X c' X' τ) W := by
  funext y i
  simp only [twoStepTranslate, leftTranslate, pairedMotion]
  rw [hexp _ (h y i), paramMap_apply]
  simp [expUnit_zero, mul_assoc]
theorem realValued_bound (hL : DerivAlongRulesHold) (hExp : expansionAlongMotionStatement)
    {U : Set (imaginaryQuaternions × imaginaryQuaternions × imaginaryQuaternions)} {C₀ : ℝ} (hU : IsOpen U)
    (h0U : (0 : imaginaryQuaternions × imaginaryQuaternions × imaginaryQuaternions) ∈ U)
    (hexp : ∀ z ∈ U, expUnit (Θ z) = expUnit z.1 * expUnit z.2.1 * (expUnit z.2.2)⁻¹) (hΘ0 : Θ 0 = 0)
    (hs3 : ContDiffAt ℝ ((3 : ℕ) : WithTop ℕ∞) Θ 0) (hb : ∀ r : ℕ, r ≤ 3 → ‖iteratedFDeriv ℝ r Θ 0‖ ≤ C₀)
    (g : F.GaugeField j → ℝ) (W : F.GaugeField j) (c : F.Site j × Fin 4) (X : imaginaryQuaternions)
    (c' : Fin k → F.Site j × Fin 4) (X' : Fin k → imaginaryQuaternions) (hk : k ≤ 2)
    (hper : ∀ i, F.period j i ≠ 0)
    (hsm : ∀ (q : ℕ) (c'' : Fin q → F.Site j × Fin 4) (X'' : Fin q → imaginaryQuaternions),
      ContDiffAt ℝ ((3 : ℕ) : WithTop ℕ∞) (fun τ : Fin q → ℝ => g (leftTranslate (bondSpread c'' X'' τ) W)) 0) :
    ContDiffAt ℝ ((k + 1 : ℕ) : WithTop ℕ∞) (fun τ => g (twoStepTranslate c X c' X' W τ)) 0 ∧
    ∀ (Bd : ∀ i : ℕ, (Fin i → F.Site j × Fin 4) → ℝ) (R : ℝ), ‖X‖ = 1 → AreUnitVectors X' → 0 ≤ R →
      (∀ (i : ℕ) (bs : Fin i → F.Site j × Fin 4) (Xs : Fin i → imaginaryQuaternions), 1 ≤ i → i ≤ 3 →
        AreUnitVectors Xs → |bondDeriv g W bs Xs| ≤ Bd i bs) →
      (∀ (i : ℕ) (bs : Fin i → F.Site j × Fin 4), 1 ≤ i → i ≤ 3 →
        (∀ l : Fin (k + 1), ∃ m, paramBond c c' l = bs m) → Bd i bs ≤ R) →
      |iteratedFDeriv ℝ (k + 1) (fun τ => g (twoStepTranslate c X c' X' W τ)) 0 (fun l => Pi.single l 1)| ≤
        (∑ p ∈ Finset.range 4, (Fintype.card (OrderedFinpartition p) : ℝ)) * ((C₀ + 1) ^ 3 * R) := by
  classical
  have hfin : Finite (F.Site j) := by
    have : ∀ i, Finite (ZMod (F.period j i)) := fun i => by
      have : NeZero (F.period j i) := ⟨hper i⟩
      infer_instance
    exact Pi.finite
  have hnear : ∀ᶠ τ in 𝓝 (0 : Fin (k + 1) → ℝ), ∀ y i, paramMap c X c' X' y i τ ∈ U := by
    refine Filter.eventually_all.2 fun y => Filter.eventually_all.2 fun i => ?_
    exact (paramMap c X c' X' y i).continuous.continuousAt.eventually
      (hU.mem_nhds (by simpa using h0U))
  have hαs : ∀ x b, ContDiffAt ℝ ((k + 1 : ℕ) : WithTop ℕ∞) (fun τ => pairedMotion Θ c X c' X' τ x b) 0 := by
    intro x b
    have h0 : ContDiffAt ℝ ((k + 1 : ℕ) : WithTop ℕ∞) Θ (paramMap c X c' X' x b 0) := by
      rw [map_zero]
      exact hs3.of_le (by exact_mod_cast (show k + 1 ≤ 3 by omega))
    exact ContDiffAt.comp (0 : Fin (k + 1) → ℝ) h0 (paramMap c X c' X' x b).contDiff.contDiffAt
  have hα0 : ∀ x b, pairedMotion Θ c X c' X' 0 x b = 0 := by
    intro x b
    simp [pairedMotion, hΘ0]
  have E := hExp.1 F j (k + 1) g W (pairedMotion Θ c X c' X') hper
    (fun q c'' X'' => (hsm q c'' X'').of_le (by exact_mod_cast (show k + 1 ≤ 3 by omega))) hαs hα0
  have ev : (fun τ => g (twoStepTranslate c X c' X' W τ)) =ᶠ[𝓝 0]
      fun τ => g (leftTranslate (pairedMotion Θ c X c' X' τ) W) := by
    filter_upwards [hnear] with τ hτ
    rw [twoStepTranslate_eq hexp c X c' X' W τ hτ]
  refine ⟨E.1.congr_of_eventuallyEq ev, fun Bd R hX hX' hR hBd hRd => ?_⟩
  rw [(Filter.EventuallyEq.iteratedFDeriv ℝ ev (k + 1)).self_of_nhds, E.2]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ((Finset.sum_le_sum fun o _ =>
    abs_mixedDerivAlong_le hL hExp hs3 hb g W c X c' X' Bd R hk hper hX hX' hR hsm hBd hRd o).trans ?_)
  rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ]
  have hC₀ : 0 ≤ C₀ := (ContinuousMultilinearMap.opNorm_nonneg _).trans (hb 0 (by omega))
  refine mul_le_mul_of_nonneg_right ?_ (by positivity)
  exact Finset.single_le_sum (f := fun p => (Fintype.card (OrderedFinpartition p) : ℝ))
    (fun _ _ => Nat.cast_nonneg _) (Finset.mem_range.2 (by omega))
def innerParams (k : ℕ) : (Fin k → ℝ) →L[ℝ] (Fin (k + 1) → ℝ) :=
  ContinuousLinearMap.pi fun l =>
    Fin.cases 0 (fun l' => ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin k => ℝ) l') l
theorem innerParams_zero (τ : Fin k → ℝ) : innerParams k τ 0 = 0 := rfl
theorem innerParams_succ (τ : Fin k → ℝ) (l : Fin k) : innerParams k τ l.succ = τ l := rfl
theorem innerParams_single (l : Fin k) : innerParams k (Pi.single l 1) = Pi.single l.succ 1 := by
  funext m
  refine Fin.cases ?_ (fun m' => ?_) m
  · rw [innerParams_zero, Pi.single_eq_of_ne (Fin.succ_ne_zero l).symm]
  · rw [innerParams_succ]
    by_cases h : m' = l
    · subst h
      simp
    · rw [Pi.single_eq_of_ne h, Pi.single_eq_of_ne (fun e => h (Fin.succ_injective _ e))]
theorem translatedDerivativeBound_holds (hL : DerivAlongRulesHold)
    (hExp : expansionAlongMotionStatement) (hLog : ConjugatedExpLogSmooth) :
    TranslatedDerivativeBound := by
  classical
  obtain ⟨Θ, U, C₀, hU, hC₀, hdiag, hsm, hexp, hzero, hbnd, -, -⟩ := hLog
  have h00 : diagonalTriple 0 = (0 : imaginaryQuaternions × imaginaryQuaternions × imaginaryQuaternions) := rfl
  have h0U : (0 : imaginaryQuaternions × imaginaryQuaternions × imaginaryQuaternions) ∈ U := by
    rw [← h00]
    exact hdiag 0
  have hs3 : ContDiffAt ℝ ((3 : ℕ) : WithTop ℕ∞) Θ 0 := hsm.contDiffAt (hU.mem_nhds h0U)
  have hb : ∀ r : ℕ, r ≤ 3 → ‖iteratedFDeriv ℝ r Θ 0‖ ≤ C₀ := fun r hr => by
    have := hbnd 0 r (by simp) hr
    rwa [h00] at this
  have hΘ0 : Θ 0 = 0 := by
    rw [← h00]
    exact hzero 0
  refine ⟨(∑ p ∈ Finset.range 4, (Fintype.card (OrderedFinpartition p) : ℝ)) * (C₀ + 1) ^ 3,
    by positivity, ?_⟩
  intro F j k f W c X c' X' Bd R hk hper hX hX' hR hsm₃ hBd hRd
  have hkk : ((k + 1 : ℕ) : WithTop ℕ∞) ≤ ((3 : ℕ) : WithTop ℕ∞) := by
    exact_mod_cast (show k + 1 ≤ 3 by omega)
  have hsmℓ : ∀ (ℓ : imaginaryQuaternions →L[ℝ] ℝ) (q : ℕ) (c'' : Fin q → F.Site j × Fin 4)
      (X'' : Fin q → imaginaryQuaternions),
      ContDiffAt ℝ ((3 : ℕ) : WithTop ℕ∞) (fun τ : Fin q → ℝ => ℓ (f (leftTranslate (bondSpread c'' X'' τ) W))) 0 :=
    fun ℓ q c'' X'' => ℓ.contDiff.contDiffAt.comp (0 : Fin q → ℝ) (hsm₃ q c'' X'')
  have part := fun ℓ : imaginaryQuaternions →L[ℝ] ℝ => realValued_bound hL hExp hU h0U hexp hΘ0 hs3 hb
    (fun W' => ℓ (f W')) W c X c' X' hk hper (hsmℓ ℓ)
  set Qf : (Fin (k + 1) → ℝ) → imaginaryQuaternions := fun τ => f (twoStepTranslate c X c' X' W τ) with hQf
  have hQ : ContDiffAt ℝ ((k + 1 : ℕ) : WithTop ℕ∞) Qf 0 := by
    let e := (Module.finBasis ℝ imaginaryQuaternions).equivFunL
    have h1 : ContDiffAt ℝ ((k + 1 : ℕ) : WithTop ℕ∞) (e ∘ Qf) 0 := by
      refine contDiffAt_pi.2 fun a => ?_
      exact (part ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ => ℝ) a).comp
        (e : imaginaryQuaternions →L[ℝ] _))).1
    exact e.comp_contDiffAt_iff.1 h1
  have R' := hL.1 (Fin (k + 1) → ℝ) imaginaryQuaternions
  have Rk := hL.1 (Fin k → ℝ) imaginaryQuaternions
  set e₀ : Fin (k + 1) → ℝ := Pi.single 0 1 with he₀
  have hH : ContDiffAt ℝ (k : WithTop ℕ∞) (derivAlong Qf [e₀]) 0 := R'.contDiffAt _ _ k _ (by simpa using hQ)
  have hH' : ContDiffAt ℝ (k : WithTop ℕ∞) (fun τ' => derivAlong Qf [e₀] (0 + innerParams k τ')) 0 := by
    have h0 : ContDiffAt ℝ (k : WithTop ℕ∞) (derivAlong Qf [e₀]) (0 + innerParams k 0) := by simpa using hH
    exact ContDiffAt.comp (g := derivAlong Qf [e₀]) (f := fun τ' => 0 + innerParams k τ') (0 : Fin k → ℝ) h0
      (contDiff_const.add (innerParams k).contDiff).contDiffAt
  have hev : (fun τ' : Fin k → ℝ => bondDeriv f (leftTranslate (bondSpread c' X' τ') W)
      (fun _ : Fin 1 => c) (fun _ => X)) =ᶠ[𝓝 0]
      fun τ' => derivAlong Qf [e₀] (0 + innerParams k τ') := by
    have hdq : ∀ᶠ q in 𝓝 (0 : Fin (k + 1) → ℝ), ContDiffAt ℝ ((k + 1 : ℕ) : WithTop ℕ∞) Qf q :=
      hQ.eventually (by simp)
    have hc : Filter.Tendsto (innerParams k) (𝓝 0) (𝓝 0) := by
      have := (innerParams k).continuous.tendsto 0
      simpa using this
    filter_upwards [hc.eventually hdq] with τ' hτ'
    have hd : DifferentiableAt ℝ Qf (innerParams k τ') := hτ'.differentiableAt (by simp)
    have hline : HasFDerivAt (fun σ : Fin 1 → ℝ => innerParams k τ' + σ 0 • e₀)
        ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 1 => ℝ) 0).smulRight e₀) 0 :=
      ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 1 => ℝ) 0).smulRight e₀).hasFDerivAt.const_add _
    have hd' : HasFDerivAt Qf (fderiv ℝ Qf (innerParams k τ')) (innerParams k τ' + (0 : Fin 1 → ℝ) 0 • e₀) := by
      simpa using hd.hasFDerivAt
    have hcomp := (hd'.comp (0 : Fin 1 → ℝ) hline).fderiv
    have efun : (fun σ : Fin 1 → ℝ => f (leftTranslate (bondSpread (fun _ : Fin 1 => c) (fun _ => X) σ)
        (leftTranslate (bondSpread c' X' τ') W))) = Qf ∘ fun σ : Fin 1 → ℝ => innerParams k τ' + σ 0 • e₀ := by
      funext σ
      have e1 : (fun _ : Fin 1 => (innerParams k τ' + σ 0 • e₀) 0) = σ := by
        funext l
        rw [Subsingleton.elim l 0]
        simp [he₀, innerParams_zero]
      have e2 : Fin.tail (innerParams k τ' + σ 0 • e₀) = τ' := by
        funext l
        simp only [Fin.tail, Pi.add_apply, Pi.smul_apply, innerParams_succ, he₀]
        rw [Pi.single_eq_of_ne (Fin.succ_ne_zero l)]
        simp
      simp only [hQf, Function.comp, twoStepTranslate]
      rw [e1, e2]
    unfold bondDeriv
    rw [iteratedFDeriv_one_apply, efun, hcomp]
    simp [derivAlong]
  refine ⟨hH'.congr_of_eventuallyEq hev, ?_⟩
  have hmain : bondDeriv (fun W' => bondDeriv f W' (fun _ : Fin 1 => c) (fun _ => X)) W c' X' =
      iteratedFDeriv ℝ (k + 1) Qf 0 (fun l => Pi.single l 1) := by
    change iteratedFDeriv ℝ k (fun τ' : Fin k → ℝ => bondDeriv f (leftTranslate (bondSpread c' X' τ') W)
      (fun _ : Fin 1 => c) (fun _ => X)) 0 (fun l => Pi.single l 1) = _
    rw [(Filter.EventuallyEq.iteratedFDeriv ℝ hev k).self_of_nhds, Rk.iteratedFDeriv_eq _ _ _ _ hH']
    have e1 := hL.2 (Fin (k + 1) → ℝ) (Fin k → ℝ) imaginaryQuaternions (derivAlong Qf [e₀]) (innerParams k) 0 0
      (List.ofFn fun l : Fin k => (Pi.single l (1 : ℝ) : Fin k → ℝ)) (by simpa using hH)
    rw [e1]
    simp only [map_zero, add_zero]
    rw [← R'.append]
    have hlen : ((((List.map (innerParams k) (List.ofFn fun l : Fin k => (Pi.single l (1 : ℝ) : Fin k → ℝ))) ++
        [e₀]).length : ℕ) : WithTop ℕ∞) = ((k + 1 : ℕ) : WithTop ℕ∞) := by simp
    rw [R'.perm Qf 0 _ (e₀ :: List.map (innerParams k)
        (List.ofFn fun l : Fin k => (Pi.single l (1 : ℝ) : Fin k → ℝ)))
      (List.perm_append_singleton _ _) (by rw [hlen]; exact hQ), R'.iteratedFDeriv_eq _ _ _ _ hQ,
      List.ofFn_succ, List.map_ofFn]
    congr 2
    congr 1
    funext l
    exact innerParams_single l
  rw [hmain]
  set I := iteratedFDeriv ℝ (k + 1) Qf 0 (fun l => Pi.single l 1) with hI
  obtain ⟨ℓ, hℓ1, hℓ2⟩ := exists_dual_vector'' ℝ I
  have hℓI : ℓ I = ‖I‖ := by simpa using hℓ2
  have hc := ContinuousLinearMap.iteratedFDeriv_comp_left ℓ hQ (i := k + 1) le_rfl
  have e2 : iteratedFDeriv ℝ (k + 1) (fun τ => ℓ (f (twoStepTranslate c X c' X' W τ))) 0
      (fun l => Pi.single l 1) = ℓ I := by
    exact show (iteratedFDeriv ℝ (k + 1) (ℓ ∘ Qf) 0) (fun l => Pi.single l 1) = ℓ I from by
      rw [hc]
      rfl
  have hBdℓ : ∀ (i : ℕ) (bs : Fin i → F.Site j × Fin 4) (Xs : Fin i → imaginaryQuaternions), 1 ≤ i → i ≤ 3 →
      AreUnitVectors Xs → |bondDeriv (fun W' => ℓ (f W')) W bs Xs| ≤ Bd i bs := by
    intro i bs Xs h1 h3 hXs
    have hc2 := ContinuousLinearMap.iteratedFDeriv_comp_left ℓ (hsm₃ i bs Xs) (i := i) (by exact_mod_cast h3)
    have e3 : bondDeriv (fun W' => ℓ (f W')) W bs Xs = ℓ (bondDeriv f W bs Xs) := by
      exact show (iteratedFDeriv ℝ i (ℓ ∘ fun τ : Fin i → ℝ => f (leftTranslate (bondSpread bs Xs τ) W)) 0)
          (fun l => Pi.single l 1) = ℓ (bondDeriv f W bs Xs) from by
        rw [hc2]
        rfl
    rw [e3]
    have h4 := ℓ.le_opNorm (bondDeriv f W bs Xs)
    have h5 : ‖ℓ‖ * ‖bondDeriv f W bs Xs‖ ≤ ‖bondDeriv f W bs Xs‖ := by
      have := mul_le_mul_of_nonneg_right hℓ1 (norm_nonneg (bondDeriv f W bs Xs))
      simpa using this
    have h6 := hBd i bs Xs h1 h3 hXs
    rw [Real.norm_eq_abs] at h4
    linarith
  have hb2 := (part ℓ).2 Bd R hX hX' hR hBdℓ (fun i bs h1 h3 h => hRd i bs h1 h3 h)
  rw [e2, hℓI, abs_of_nonneg (norm_nonneg _)] at hb2
  rw [mul_assoc]
  exact hb2
end TranslatedDerivative
end YangMills.Construction
end
