import YangMills.Construction.SummableBoundsOfTheFlow.GaugeOfAMotionProof
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction
open BlockAverages ColdStepAtMirrorFrames
namespace Estimates
section
variable {E₁ E₂ : Type*} [NormedAddCommGroup E₁] [NormedSpace ℝ E₁] [NormedAddCommGroup E₂]
  [NormedSpace ℝ E₂]
theorem exists_isOpen_contDiffOn_of_contDiffAt {f : E₁ → E₂} {x : E₁} {n : ℕ}
    (hf : ContDiffAt ℝ n f x) :
    ∃ U : Set E₁, IsOpen U ∧ x ∈ U ∧ ContDiffOn ℝ n f U := by apply _root_.YangMills.Construction.GaugeAlongMotion.exists_isOpen_contDiffOn_of_contDiffAt <;> assumption
theorem iteratedFDeriv_comp_eq_sum_orderedFinpartition {E₃ : Type*} [NormedAddCommGroup E₃]
    [NormedSpace ℝ E₃] {g : E₂ → E₃} {β : E₁ → E₂} {x : E₁} {n : ℕ}
    (hg : ContDiffAt ℝ n g (β x)) (hβ : ContDiffAt ℝ n β x) (v : Fin n → E₁) :
    iteratedFDeriv ℝ n (g ∘ β) x v = ∑ c : OrderedFinpartition n,
      iteratedFDeriv ℝ c.length g (β x)
        (c.applyOrderedFinpartition (fun m => iteratedFDeriv ℝ (c.partSize m) β x) v) := by apply _root_.YangMills.Construction.GaugeAlongMotion.iteratedFDeriv_comp_eq_sum_orderedFinpartition <;> assumption
theorem iteratedFDeriv_comp_continuousLinearMap {E₃ : Type*} [NormedAddCommGroup E₃]
    [NormedSpace ℝ E₃] (Λ : E₁ →L[ℝ] E₂) {f : E₂ → E₃} {x : E₁} {n : ℕ}
    (hf : ContDiffAt ℝ n f (Λ x)) (v : Fin n → E₁) :
    iteratedFDeriv ℝ n (f ∘ Λ) x v = iteratedFDeriv ℝ n f (Λ x) fun l => Λ (v l) := by
  obtain ⟨U, hU, hxU, hfU⟩ := exists_isOpen_contDiffOn_of_contDiffAt hf
  have hΛ : IsOpen (Λ ⁻¹' U) := hU.preimage Λ.continuous
  have h := Λ.iteratedFDerivWithin_comp_right hfU hU.uniqueDiffOn hΛ.uniqueDiffOn
    (x := x) hxU (i := n) le_rfl
  rw [iteratedFDerivWithin_of_isOpen n hΛ (show x ∈ Λ ⁻¹' U from hxU),
    iteratedFDerivWithin_of_isOpen n hU hxU] at h
  rw [h]
  rfl
end
section
def imBasis (r : Fin 3) : imaginaryQuaternions :=
  ![⟨(⟨0, 1, 0, 0⟩ : ℍ[ℝ]), rfl⟩, ⟨(⟨0, 0, 1, 0⟩ : ℍ[ℝ]), rfl⟩, ⟨(⟨0, 0, 0, 1⟩ : ℍ[ℝ]), rfl⟩] r
def imCoord (r : Fin 3) (w : imaginaryQuaternions) : ℝ :=
  ![(w : ℍ[ℝ]).imI, (w : ℍ[ℝ]).imJ, (w : ℍ[ℝ]).imK] r
theorem sum_imCoord_smul_imBasis (w : imaginaryQuaternions) :
    ∑ r, imCoord r w • imBasis r = w := by
  apply Subtype.ext
  have hw : (w : ℍ[ℝ]).re = 0 := w.2
  simp only [Fin.sum_univ_three, imCoord, imBasis]
  apply Quaternion.ext
  · change (w : ℍ[ℝ]).imI * 0 + (w : ℍ[ℝ]).imJ * 0 + (w : ℍ[ℝ]).imK * 0 = (w : ℍ[ℝ]).re
    simp [hw]
  · change (w : ℍ[ℝ]).imI * 1 + (w : ℍ[ℝ]).imJ * 0 + (w : ℍ[ℝ]).imK * 0 = (w : ℍ[ℝ]).imI
    simp
  · change (w : ℍ[ℝ]).imI * 0 + (w : ℍ[ℝ]).imJ * 1 + (w : ℍ[ℝ]).imK * 0 = (w : ℍ[ℝ]).imJ
    simp
  · change (w : ℍ[ℝ]).imI * 0 + (w : ℍ[ℝ]).imJ * 0 + (w : ℍ[ℝ]).imK * 1 = (w : ℍ[ℝ]).imK
    simp
variable {F : BlockFrame} {j : ℕ} [∀ i, NeZero (F.period j i)]
def bondCurry (A : F.Site j × Fin 4 → imaginaryQuaternions) :
    F.Site j → Fin 4 → imaginaryQuaternions := fun x b => A (x, b)
def chartPullback (G : F.GaugeField j → ℝ) (W : F.GaugeField j)
    (A : F.Site j × Fin 4 → imaginaryQuaternions) : ℝ :=
  G (leftTranslate (bondCurry A) W)
def imCoordsCLM {q : ℕ} (e : (F.Site j × Fin 4) × Fin 3 ≃ Fin q) :
    (F.Site j × Fin 4 → imaginaryQuaternions) →L[ℝ] (Fin q → ℝ) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun A l => imCoord (e.symm l).2 (A (e.symm l).1)
      map_add' := fun A A' => by
        funext l
        have h : ∀ r (w w' : imaginaryQuaternions),
            imCoord r (w + w') = imCoord r w + imCoord r w' := by
          intro r w w'
          fin_cases r <;> simp [imCoord]
        simp [h]
      map_smul' := fun u A => by
        funext l
        have h : ∀ r (w : imaginaryQuaternions), imCoord r (u • w) = u * imCoord r w := by
          intro r w
          fin_cases r <;> simp [imCoord]
        simp [h] }
theorem bondSpread_imCoordsCLM {q : ℕ} (e : (F.Site j × Fin 4) × Fin 3 ≃ Fin q)
    (A : F.Site j × Fin 4 → imaginaryQuaternions) :
    bondSpread (F := F) (j := j) (fun l => (e.symm l).1) (fun l => imBasis (e.symm l).2)
      (imCoordsCLM e A) = bondCurry A := by
  funext x b
  simp only [ColdStepAtMirrorFrames.bondSpread, bondCurry]
  have h1 : (∑ l, if (e.symm l).1 = (x, b) then imCoordsCLM e A l • imBasis (e.symm l).2
      else 0) =
      ∑ z : (F.Site j × Fin 4) × Fin 3,
        if z.1 = (x, b) then imCoord z.2 (A z.1) • imBasis z.2 else 0 :=
    Equiv.sum_comp e.symm
      (fun z : (F.Site j × Fin 4) × Fin 3 =>
        if z.1 = (x, b) then imCoord z.2 (A z.1) • imBasis z.2 else 0)
  rw [h1, Fintype.sum_prod_type]
  have h2 : ∀ d : F.Site j × Fin 4,
      (∑ r, if d = (x, b) then imCoord r (A d) • imBasis r else 0) =
        if d = (x, b) then ∑ r, imCoord r (A d) • imBasis r else 0 := by
    intro d
    split_ifs <;> simp
  simp only [h2]
  rw [Finset.sum_ite_eq' Finset.univ (x, b)]
  simpa using sum_imCoord_smul_imBasis (A (x, b))
theorem contDiffAt_chartPullback {p : ℕ} {G : F.GaugeField j → ℝ} {W : F.GaugeField j}
    (hG : ∀ (q : ℕ) (c : Fin q → F.Site j × Fin 4) (X : Fin q → imaginaryQuaternions),
      ContDiffAt ℝ p (fun τ : Fin q → ℝ => G (leftTranslate (bondSpread c X τ) W)) 0) :
    ContDiffAt ℝ p (chartPullback G W) 0 := by
  let e := Fintype.equivFin ((F.Site j × Fin 4) × Fin 3)
  have h := hG _ (fun l => (e.symm l).1) (fun l => imBasis (e.symm l).2)
  have hc : ContDiffAt ℝ p (imCoordsCLM e) (0 : F.Site j × Fin 4 → imaginaryQuaternions) :=
    (imCoordsCLM e).contDiff.contDiffAt
  have h0 : imCoordsCLM e (0 : F.Site j × Fin 4 → imaginaryQuaternions) = 0 := map_zero _
  have hcomp := ContDiffAt.comp (0 : F.Site j × Fin 4 → imaginaryQuaternions) (h0 ▸ h) hc
  refine hcomp.congr_of_eventuallyEq (Filter.Eventually.of_forall fun A => ?_)
  simp only [chartPullback, Function.comp]
  rw [bondSpread_imCoordsCLM]
def polarizationCLM {i : ℕ} (A : Fin i → F.Site j × Fin 4 → imaginaryQuaternions) :
    (Fin i → ℝ) →L[ℝ] (F.Site j × Fin 4 → imaginaryQuaternions) :=
  ∑ l, (ContinuousLinearMap.proj l : (Fin i → ℝ) →L[ℝ] ℝ).smulRight (A l)
omit [∀ i, NeZero (F.period j i)] in
theorem polarizationCLM_apply {i : ℕ} (A : Fin i → F.Site j × Fin 4 → imaginaryQuaternions)
    (τ : Fin i → ℝ) : polarizationCLM A τ = ∑ l, τ l • A l := by
  simp [polarizationCLM]
omit [∀ i, NeZero (F.period j i)] in
theorem polarizationCLM_single {i : ℕ} (A : Fin i → F.Site j × Fin 4 → imaginaryQuaternions)
    (l : Fin i) : polarizationCLM A (Pi.single l 1) = A l := by
  rw [polarizationCLM_apply]
  simp [Pi.single_apply]
theorem mixedDerivAlong_eq_iteratedFDeriv {i : ℕ} {G : F.GaugeField j → ℝ} {W : F.GaugeField j}
    (hG : ContDiffAt ℝ i (chartPullback G W) 0)
    (A : Fin i → F.Site j → Fin 4 → imaginaryQuaternions) :
    mixedDerivAlong G W A = iteratedFDeriv ℝ i (chartPullback G W) 0 fun l d => A l d.1 d.2 := by
  let A' : Fin i → F.Site j × Fin 4 → imaginaryQuaternions := fun l d => A l d.1 d.2
  have hfun : (fun τ : Fin i → ℝ => G (leftTranslate (fun x b => ∑ l, τ l • A l x b) W)) =
      chartPullback G W ∘ polarizationCLM A' := by
    funext τ
    have hcur : bondCurry (polarizationCLM A' τ) = fun x b => ∑ l, τ l • A l x b := by
      funext x b
      simp [bondCurry, polarizationCLM_apply, A', Finset.sum_apply]
    simp only [chartPullback, Function.comp, hcur]
  have hz : polarizationCLM A' 0 = 0 := map_zero _
  have h := iteratedFDeriv_comp_continuousLinearMap (polarizationCLM A') (x := 0) (n := i)
    (hz ▸ hG) (fun l => Pi.single l 1)
  rw [mixedDerivAlong, hfun, h, hz]
  simp only [polarizationCLM_single, A']
end
theorem faaDiBrunoAlongMotion_holds : FaaDiBrunoAlongMotion := by
  intro F j p G W α hper hG hα h0
  have : ∀ i, NeZero (F.period j i) := fun i => ⟨hper i⟩
  have hc := contDiffAt_chartPullback hG
  let β : (Fin p → ℝ) → F.Site j × Fin 4 → imaginaryQuaternions := fun τ d => α τ d.1 d.2
  have hβ : ContDiffAt ℝ p β 0 := contDiffAt_pi.2 fun d => hα d.1 d.2
  have hβ0 : β 0 = 0 := by
    funext d
    exact h0 d.1 d.2
  have hfun : (fun τ => G (leftTranslate (α τ) W)) = chartPullback G W ∘ β := rfl
  constructor
  · rw [hfun]
    exact ContDiffAt.comp (0 : Fin p → ℝ) (hβ0 ▸ hc) hβ
  · rw [hfun, iteratedFDeriv_comp_eq_sum_orderedFinpartition (hβ0 ▸ hc) hβ, hβ0]
    refine Finset.sum_congr rfl fun c _ => ?_
    have hl : ContDiffAt ℝ c.length (chartPullback G W) 0 :=
      hc.of_le (by exact_mod_cast c.length_le)
    rw [mixedDerivAlong_eq_iteratedFDeriv hl]
    congr 1
    funext m d
    simp only [OrderedFinpartition.applyOrderedFinpartition_apply, motionComponent]
    have hm : ContDiffAt ℝ (c.partSize m) β 0 := hβ.of_le (by exact_mod_cast c.partSize_le m)
    have h := (ContinuousLinearMap.proj d :
      (F.Site j × Fin 4 → imaginaryQuaternions) →L[ℝ] imaginaryQuaternions).iteratedFDeriv_comp_left
      hm (i := c.partSize m) le_rfl
    have h2 := congrArg (fun M => M fun l => (Pi.single (c.emb m l) 1 : Fin p → ℝ)) h
    simpa [β, Function.comp_def] using h2.symm
theorem mixedDerivBound_holds : MixedDerivBound := by
  intro F j i G W A T B hper hT hG hB
  have : ∀ l, NeZero (F.period j l) := fun l => ⟨hper l⟩
  have hc := contDiffAt_chartPullback hG
  have hTu : T = Finset.univ := Finset.eq_univ_iff_forall.2 hT
  subst hTu
  rw [mixedDerivAlong_eq_iteratedFDeriv hc]
  set M := iteratedFDeriv ℝ i (chartPullback G W) 0 with hM
  have hA : (fun l (d : F.Site j × Fin 4) => A l d.1 d.2) =
      fun l => ∑ d, Pi.single d (A l d.1 d.2) := by
    funext l d
    simp [Finset.sum_apply, Pi.single_apply]
  rw [hA, ContinuousMultilinearMap.map_sum_finset]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun b _ => ?_)
  by_cases hz : ∃ l, A l (b l).1 (b l).2 = 0
  · obtain ⟨l, hl⟩ := hz
    have h0 : (Pi.single (b l) (A l (b l).1 (b l).2) :
        F.Site j × Fin 4 → imaginaryQuaternions) = 0 := by
      rw [hl]; simp
    rw [M.map_coord_zero l h0, abs_zero, Finset.prod_eq_zero (Finset.mem_univ l) (by simp [hl])]
    simp
  · push Not at hz
    let u : Fin i → imaginaryQuaternions := fun l => ‖A l (b l).1 (b l).2‖⁻¹ • A l (b l).1 (b l).2
    have hu : AreUnitVectors u := by
      intro l
      have : ‖A l (b l).1 (b l).2‖ ≠ 0 := norm_ne_zero_iff.2 (hz l)
      simp only [u, norm_smul, norm_inv, norm_norm]
      field_simp
    have hsm : (fun l => (Pi.single (b l) (A l (b l).1 (b l).2) :
        F.Site j × Fin 4 → imaginaryQuaternions)) =
        fun l => ‖A l (b l).1 (b l).2‖ •
          (Pi.single (b l) (u l) : F.Site j × Fin 4 → imaginaryQuaternions) := by
      funext l
      rw [← Pi.single_smul]
      congr 1
      simp only [u, smul_smul]
      have : ‖A l (b l).1 (b l).2‖ ≠ 0 := norm_ne_zero_iff.2 (hz l)
      field_simp
      simp
    have hd : bondDeriv G W b u = M fun l => Pi.single (b l) (u l) := by
      have hs := mixedDerivAlong_eq_iteratedFDeriv hc
        (fun l x y => (Pi.single (b l) (u l) : F.Site j × Fin 4 → imaginaryQuaternions) (x, y))
      have hspread : (fun τ : Fin i → ℝ => leftTranslate (bondSpread b u τ) W) =
          fun τ => leftTranslate (fun x y => ∑ l, τ l •
            (Pi.single (b l) (u l) : F.Site j × Fin 4 → imaginaryQuaternions) (x, y)) W := by
        funext τ
        congr 1
        funext x y
        simp only [ColdStepAtMirrorFrames.bondSpread]
        refine Finset.sum_congr rfl fun l _ => ?_
        by_cases h : b l = (x, y)
        · simp [h]
        · have h' : (x, y) ≠ b l := fun e => h e.symm
          simp [h, h']
      have : bondDeriv G W b u = mixedDerivAlong G W
          (fun l x y => (Pi.single (b l) (u l) :
            F.Site j × Fin 4 → imaginaryQuaternions) (x, y)) := by
        have hG2 : (fun τ : Fin i → ℝ => G (leftTranslate (bondSpread b u τ) W)) =
            fun τ => G (leftTranslate (fun x y => ∑ l, τ l •
              (Pi.single (b l) (u l) : F.Site j × Fin 4 → imaginaryQuaternions) (x, y)) W) :=
          funext fun τ => congrArg G (congrFun hspread τ)
        simp only [bondDeriv, mixedDerivAlong]
        rw [hG2]
      rw [this, hs]
    have hfin : M (fun l => Pi.single (b l) (A l (b l).1 (b l).2)) =
        (∏ l, ‖A l (b l).1 (b l).2‖) • bondDeriv G W b u := by
      rw [hsm, M.map_smul_univ, hd]
    show |M fun l => Pi.single (b l) (A l (b l).1 (b l).2)| ≤ _
    rw [hfin, smul_eq_mul, abs_mul, abs_of_nonneg (Finset.prod_nonneg fun _ _ => norm_nonneg _),
      mul_comm]
    exact mul_le_mul_of_nonneg_right (hB b u hu) (Finset.prod_nonneg fun _ _ => norm_nonneg _)
theorem expansionAlongMotionStatement_holds : expansionAlongMotionStatement :=
  ⟨faaDiBrunoAlongMotion_holds, mixedDerivBound_holds⟩
end Estimates
end YangMills.Construction
end
