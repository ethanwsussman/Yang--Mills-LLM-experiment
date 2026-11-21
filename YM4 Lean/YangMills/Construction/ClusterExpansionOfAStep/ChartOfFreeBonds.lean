import YangMills.Construction.ClusterExpansionOfAStep.LocalLogarithmOfTheGroup
import YangMills.Construction.ClusterExpansionOfAStep.MovesOfAField
import YangMills.Construction.ClusterExpansionOfAStep.SettingsOfAStep
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction
open BlockAverages ColdStepAtMirrorFrames TorusFields FieldMoves StepSettings
namespace ImaginaryQuaternion
def coordCLM (j : Fin 3) : imaginaryQuaternions →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun w => ![(w : ℍ[ℝ]).imI, (w : ℍ[ℝ]).imJ, (w : ℍ[ℝ]).imK] j
      map_add' := by
        intro a b
        fin_cases j <;> simp
      map_smul' := by
        intro c a
        fin_cases j <;> simp }
def basisVec (j : Fin 3) : imaginaryQuaternions := toImaginary (EuclideanSpace.single j 1)
theorem toImaginary_re (v : EuclideanSpace ℝ (Fin 3)) :
    ((toImaginary v : imaginaryQuaternions) : ℍ[ℝ]).re = 0 := rfl
theorem toImaginary_imI (v : EuclideanSpace ℝ (Fin 3)) :
    ((toImaginary v : imaginaryQuaternions) : ℍ[ℝ]).imI = v 0 := rfl
theorem toImaginary_imJ (v : EuclideanSpace ℝ (Fin 3)) :
    ((toImaginary v : imaginaryQuaternions) : ℍ[ℝ]).imJ = v 1 := rfl
theorem toImaginary_imK (v : EuclideanSpace ℝ (Fin 3)) :
    ((toImaginary v : imaginaryQuaternions) : ℍ[ℝ]).imK = v 2 := rfl
theorem sum_coordCLM_smul_basisVec (w : imaginaryQuaternions) : ∑ j, coordCLM j w • basisVec j = w := by
  have hw : (w : ℍ[ℝ]).re = 0 := w.2
  have c0 : coordCLM 0 w = (w : ℍ[ℝ]).imI := rfl
  have c1 : coordCLM 1 w = (w : ℍ[ℝ]).imJ := rfl
  have c2 : coordCLM 2 w = (w : ℍ[ℝ]).imK := rfl
  rw [Fin.sum_univ_three, c0, c1, c2]
  apply Subtype.ext
  refine Quaternion.ext _ _ ?_ ?_ ?_ ?_ <;>
  simp [basisVec, toImaginary_re, toImaginary_imI, toImaginary_imJ, toImaginary_imK, hw]
end ImaginaryQuaternion
namespace StepSettings.ChartSetting
open ImaginaryQuaternion
variable {R : StepSetup} {n : ℕ} [NeZero n] {s : ChartSetting R n}
open Classical in
def expOnFree (s : ChartSetting R n) (A : s.free → imaginaryQuaternions) (W : TorusField (n * R.params.side)) :
    TorusField (n * R.params.side) := fun x i =>
  if h : (x, i) ∈ s.free then expUnit (A ⟨(x, i), h⟩) * W x i else W x i
open Classical in
theorem perturb_eq_expOnFree {k : ℕ} (c : Fin k → s.free) (X : Fin k → imaginaryQuaternions) (σ : Fin k → ℝ)
    (A : s.free → imaginaryQuaternions)
    (hA : ∀ b : s.free, A b = ∑ l, if c l = b then σ l • X l else 0) (W : TorusField (n * R.params.side)) :
    perturb (fun l => (c l).1) X σ W = s.expOnFree A W := by
  funext x i
  unfold ChartSetting.expOnFree
  by_cases h : (x, i) ∈ s.free
  · rw [dif_pos h, perturb_apply, hA]
    congr 2
    unfold bondShift
    refine Finset.sum_congr rfl fun l _ => ?_
    by_cases e : c l = ⟨(x, i), h⟩
    · rw [if_pos e, if_pos (show ((c l : s.free) : TorusBond (n * R.params.side)) = (x, i) from congrArg Subtype.val e)]
    · rw [if_neg e, if_neg fun e' => e (Subtype.ext e')]
  · rw [dif_neg h]
    exact perturb_apply_of_ne _ X σ W (x, i) fun l e => h (e ▸ (c l).2)
def chartFn (s : ChartSetting R n) (F : TorusField (n * R.params.side) → ℝ) (W : TorusField (n * R.params.side))
    (A : s.free → imaginaryQuaternions) : ℝ :=
  F (s.expOnFree A W)
def freeBasisIndex (s : ChartSetting R n) : Fin (Fintype.card (s.free × Fin 3)) ≃ s.free × Fin 3 :=
  (Fintype.equivFin (s.free × Fin 3)).symm
def freeBasisCoord (s : ChartSetting R n) :
    (s.free → imaginaryQuaternions) →L[ℝ] (Fin (Fintype.card (s.free × Fin 3)) → ℝ) :=
  ContinuousLinearMap.pi fun l =>
    (coordCLM (s.freeBasisIndex l).2).comp (ContinuousLinearMap.proj (s.freeBasisIndex l).1)
open Classical in
theorem eq_sum_freeBasisCoord (s : ChartSetting R n) (A : s.free → imaginaryQuaternions) (b : s.free) :
    A b = ∑ l, if (s.freeBasisIndex l).1 = b then s.freeBasisCoord A l • basisVec (s.freeBasisIndex l).2 else 0 := by
  have e : ∀ l, s.freeBasisCoord A l = coordCLM (s.freeBasisIndex l).2 (A (s.freeBasisIndex l).1) := fun l => rfl
  simp only [e]
  rw [Equiv.sum_comp s.freeBasisIndex (fun p : s.free × Fin 3 =>
    if p.1 = b then coordCLM p.2 (A p.1) • basisVec p.2 else 0), Fintype.sum_prod_type,
    Finset.sum_eq_single b]
  · simp [sum_coordCLM_smul_basisVec]
  · intro b' _ hb
    simp [hb]
  · simp
theorem contDiffAt_chartFn {F : TorusField (n * R.params.side) → ℝ} {W : TorusField (n * R.params.side)}
    (hF : ∀ (k : ℕ) (c : Fin k → TorusBond (n * R.params.side)) (X : Fin k → imaginaryQuaternions),
      (∀ l, c l ∈ s.free) → ContDiffAt ℝ 3 (fun σ : Fin k → ℝ => F (perturb c X σ W)) 0) :
    ContDiffAt ℝ 3 (s.chartFn F W) 0 := by
  classical
  have h1 := hF _ (fun l => ((s.freeBasisIndex l).1 : TorusBond (n * R.params.side)))
    (fun l => basisVec (s.freeBasisIndex l).2) (fun l => (s.freeBasisIndex l).1.2)
  have e : s.chartFn F W = (fun σ => F (perturb (fun l => ((s.freeBasisIndex l).1 : TorusBond (n * R.params.side)))
      (fun l => basisVec (s.freeBasisIndex l).2) σ W)) ∘ s.freeBasisCoord := by
    funext A
    simp only [ChartSetting.chartFn, Function.comp]
    rw [perturb_eq_expOnFree (fun l => (s.freeBasisIndex l).1) _ _ A (s.eq_sum_freeBasisCoord A)]
  rw [e]
  have h2 : ContDiffAt ℝ 3 (fun σ => F (perturb (fun l => ((s.freeBasisIndex l).1 : TorusBond (n * R.params.side)))
      (fun l => basisVec (s.freeBasisIndex l).2) σ W)) (s.freeBasisCoord 0) := by
    simpa using h1
  exact h2.comp _ s.freeBasisCoord.contDiff.contDiffAt
open Classical in
def pairMove (b : Fin 2 → s.free) (X : Fin 2 → imaginaryQuaternions) :
    (Fin 2 → ℝ) →L[ℝ] (s.free → imaginaryQuaternions) :=
  ∑ l, (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) l).smulRight (Pi.single (b l) (X l))
open Classical in
theorem pairMove_apply (b : Fin 2 → s.free) (X : Fin 2 → imaginaryQuaternions) (σ : Fin 2 → ℝ) (b' : s.free) :
    pairMove b X σ b' = ∑ l, if b l = b' then σ l • X l else 0 := by
  unfold pairMove
  simp only [ContinuousLinearMap.sum_apply, Finset.sum_apply, ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.proj_apply, Pi.smul_apply, Pi.single_apply]
  refine Finset.sum_congr rfl fun l _ => ?_
  by_cases e : b l = b'
  · rw [if_pos e, if_pos e.symm]
  · rw [if_neg e, if_neg fun e' => e e'.symm]
    simp
theorem alongPair_eq_chartFn_comp (F : TorusField (n * R.params.side) → ℝ) (b : Fin 2 → s.free)
    (X : Fin 2 → imaginaryQuaternions) (W : TorusField (n * R.params.side)) :
    alongPair F (fun l => (b l).1) X W = s.chartFn F W ∘ pairMove b X := by
  classical
  funext σ
  simp only [alongPair, ChartSetting.chartFn, Function.comp]
  rw [perturb_eq_expOnFree b X σ (pairMove b X σ) (pairMove_apply b X σ)]
open Classical in
theorem pairMove_single (b : Fin 2 → s.free) (X : Fin 2 → imaginaryQuaternions) (l : Fin 2) :
    pairMove b X (Pi.single l 1) = Pi.single (b l) (X l) := by
  funext b'
  rw [pairMove_apply, Fin.sum_univ_two]
  fin_cases l <;> simp [Pi.single_apply] <;> split_ifs <;> simp_all
open Classical in
theorem iteratedFDeriv_two_alongPair {F : TorusField (n * R.params.side) → ℝ} {W : TorusField (n * R.params.side)}
    (hC : ContDiffAt ℝ 3 (s.chartFn F W) 0) (b : Fin 2 → s.free) (X : Fin 2 → imaginaryQuaternions) :
    (iteratedFDeriv ℝ 2 (alongPair F (fun l => (b l).1) X W) 0 fun l => Pi.single l 1) =
      fderiv ℝ (fderiv ℝ (s.chartFn F W)) 0 (Pi.single (b 0) (X 0)) (Pi.single (b 1) (X 1)) := by
  have hC2 : ContDiffAt ℝ ((2 : ℕ) : WithTop ℕ∞) (s.chartFn F W) (pairMove b X 0) := by
    rw [map_zero]
    exact hC.of_le (by norm_num)
  rw [alongPair_eq_chartFn_comp, iteratedFDeriv_comp_continuousLinearMap (pairMove b X) hC2, map_zero]
  simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply, pairMove_single]
  rw [iteratedFDeriv_two_apply]
open Classical in
theorem iteratedFDeriv_one_alongPair {F : TorusField (n * R.params.side) → ℝ} {W : TorusField (n * R.params.side)}
    (hC : ContDiffAt ℝ 3 (s.chartFn F W) 0) (b : Fin 2 → s.free) (X : Fin 2 → imaginaryQuaternions) :
    (iteratedFDeriv ℝ 1 (alongPair F (fun l => (b l).1) X W) 0 fun _ => Pi.single 0 1) =
      fderiv ℝ (s.chartFn F W) 0 (Pi.single (b 0) (X 0)) := by
  have hC1 : ContDiffAt ℝ ((1 : ℕ) : WithTop ℕ∞) (s.chartFn F W) (pairMove b X 0) := by
    rw [map_zero]
    exact hC.of_le (by norm_num)
  rw [alongPair_eq_chartFn_comp, iteratedFDeriv_comp_continuousLinearMap (pairMove b X) hC1, map_zero]
  simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply, pairMove_single]
  rw [iteratedFDeriv_one_apply]
end StepSettings.ChartSetting
namespace BilinearBound
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
theorem abs_le_mul_norm_mul_norm {T : V → V → ℝ} (hs : ∀ (a : ℝ) u v, T (a • u) v = a * T u v)
    (hs' : ∀ (a : ℝ) u v, T u (a • v) = a * T u v) {M : ℝ}
    (hM : ∀ u v, ‖u‖ = 1 → ‖v‖ = 1 → |T u v| ≤ M) (u v : V) : |T u v| ≤ M * ‖u‖ * ‖v‖ := by
  by_cases hu : u = 0
  · have := hs 0 u v
    simp [hu] at this ⊢
    simp [this]
  by_cases hv : v = 0
  · have := hs' 0 u v
    simp [hv] at this ⊢
    simp [this]
  have nu : ‖u‖ ≠ 0 := norm_ne_zero_iff.mpr hu
  have nv : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hv
  have eu : u = ‖u‖ • (‖u‖⁻¹ • u) := by rw [smul_smul, mul_inv_cancel₀ nu, one_smul]
  have ev : v = ‖v‖ • (‖v‖⁻¹ • v) := by rw [smul_smul, mul_inv_cancel₀ nv, one_smul]
  have h1 := hM (‖u‖⁻¹ • u) (‖v‖⁻¹ • v) (by rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ nu])
    (by rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ nv])
  have e : T u v = ‖u‖ * (‖v‖ * T (‖u‖⁻¹ • u) (‖v‖⁻¹ • v)) := by
    conv_lhs => rw [eu, ev]
    rw [hs, hs']
  rw [e, abs_mul, abs_mul, abs_norm, abs_norm]
  calc ‖u‖ * (‖v‖ * |T (‖u‖⁻¹ • u) (‖v‖⁻¹ • v)|) ≤ ‖u‖ * (‖v‖ * M) := by gcongr
    _ = _ := by ring
theorem abs_le_two_mul_of_abs_diag_le {T : V → V → ℝ} (ha : ∀ u u' v, T (u + u') v = T u v + T u' v)
    (ha' : ∀ u v v', T u (v + v') = T u v + T u v')
    (hs : ∀ (a : ℝ) u v, T (a • u) v = a * T u v) (hs' : ∀ (a : ℝ) u v, T u (a • v) = a * T u v)
    (hsym : ∀ u v, T u v = T v u) {M : ℝ} (hM : ∀ z, ‖z‖ = 1 → |T z z| ≤ M) {u v : V} (hu : ‖u‖ = 1)
    (hv : ‖v‖ = 1) : |T u v| ≤ 2 * M := by
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM u hu)
  have diag : ∀ z, |T z z| ≤ M * ‖z‖ * ‖z‖ := by
    intro z
    by_cases hz : z = 0
    · have := hs 0 z z
      simp [hz] at this ⊢
      simp [this]
    have nz : ‖z‖ ≠ 0 := norm_ne_zero_iff.mpr hz
    have ez : z = ‖z‖ • (‖z‖⁻¹ • z) := by rw [smul_smul, mul_inv_cancel₀ nz, one_smul]
    have h1 := hM (‖z‖⁻¹ • z) (by rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ nz])
    have e : T z z = ‖z‖ * (‖z‖ * T (‖z‖⁻¹ • z) (‖z‖⁻¹ • z)) := by
      conv_lhs => rw [ez]
      rw [hs, hs']
    rw [e, abs_mul, abs_mul, abs_norm]
    have n1 := norm_nonneg z
    calc ‖z‖ * (‖z‖ * |T (‖z‖⁻¹ • z) (‖z‖⁻¹ • z)|) ≤ ‖z‖ * (‖z‖ * M) := by gcongr
      _ = _ := by ring
  have hneg : ∀ z w, T (-z) w = - T z w := by
    intro z w
    have := hs (-1) z w
    simpa using this
  have hneg' : ∀ z w, T z (-w) = - T z w := by
    intro z w
    have := hs' (-1) z w
    simpa using this
  have id4 : T (u + v) (u + v) - T (u - v) (u - v) = 4 * T u v := by
    rw [sub_eq_add_neg u v]
    simp only [ha, ha', hneg, hneg']
    rw [hsym v u]
    ring
  have n1 : ‖u + v‖ ≤ 2 := (norm_add_le _ _).trans (by rw [hu, hv]; norm_num)
  have n2 : ‖u - v‖ ≤ 2 := (norm_sub_le _ _).trans (by rw [hu, hv]; norm_num)
  have b1 : |T (u + v) (u + v)| ≤ 4 * M := by
    refine (diag _).trans ?_
    have h0 := norm_nonneg (u + v)
    have h4 : ‖u + v‖ * ‖u + v‖ ≤ 4 := by nlinarith
    calc M * ‖u + v‖ * ‖u + v‖ = M * (‖u + v‖ * ‖u + v‖) := by ring
      _ ≤ M * 4 := mul_le_mul_of_nonneg_left h4 hM0
      _ = 4 * M := by ring
  have b2 : |T (u - v) (u - v)| ≤ 4 * M := by
    refine (diag _).trans ?_
    have h0 := norm_nonneg (u - v)
    have h4 : ‖u - v‖ * ‖u - v‖ ≤ 4 := by nlinarith
    calc M * ‖u - v‖ * ‖u - v‖ = M * (‖u - v‖ * ‖u - v‖) := by ring
      _ ≤ M * 4 := mul_le_mul_of_nonneg_left h4 hM0
      _ = 4 * M := by ring
  have e : T u v = (T (u + v) (u + v) - T (u - v) (u - v)) / 4 := by
    rw [id4]
    ring
  rw [e, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 4)]
  have := abs_sub (T (u + v) (u + v)) (T (u - v) (u - v))
  rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 4)]
  linarith
end BilinearBound
namespace StepSettings.ChartSetting
variable {R : StepSetup} {n : ℕ} [NeZero n] {s : ChartSetting R n}
open Classical in
theorem abs_secondDeriv_single_le {f : (s.free → imaginaryQuaternions) → ℝ} (hC : ContDiffAt ℝ 3 f 0) {M : ℝ}
    (b b' : s.free)
    (hM : ∀ X X' : imaginaryQuaternions, ‖X‖ = 1 → ‖X'‖ = 1 → (b ≠ b' ∨ X = X') →
      |fderiv ℝ (fderiv ℝ f) 0 (Pi.single b X) (Pi.single b' X')| ≤ M) (hM0 : 0 ≤ M)
    (P P' : imaginaryQuaternions) :
    |fderiv ℝ (fderiv ℝ f) 0 (Pi.single b P) (Pi.single b' P')| ≤ 2 * M * ‖P‖ * ‖P'‖ := by
  set Q := fderiv ℝ (fderiv ℝ f) 0 with hQ
  have hsym : ∀ u v, Q u v = Q v u := by
    intro u v
    exact (hC.isSymmSndFDerivAt (by simp; norm_num)).eq u v
  have sa : ∀ (c : s.free) (u u' : imaginaryQuaternions),
      (Pi.single c (u + u') : s.free → imaginaryQuaternions) = Pi.single c u + Pi.single c u' :=
    fun c u u' => by
      funext c'
      simp only [Pi.add_apply, Pi.single_apply]
      split_ifs <;> simp
  have sm : ∀ (c : s.free) (a : ℝ) (u : imaginaryQuaternions),
      (Pi.single c (a • u) : s.free → imaginaryQuaternions) = a • Pi.single c u :=
    fun c a u => by
      funext c'
      simp only [Pi.smul_apply, Pi.single_apply]
      split_ifs <;> simp
  by_cases hbb : b = b'
  · subst hbb
    refine BilinearBound.abs_le_mul_norm_mul_norm (T := fun u v => Q (Pi.single b u) (Pi.single b v)) ?_ ?_ ?_ P P'
    · intro a u v
      simp [sm]
    · intro a u v
      simp [sm]
    · intro u v hu hv
      refine BilinearBound.abs_le_two_mul_of_abs_diag_le (T := fun u v => Q (Pi.single b u) (Pi.single b v))
        ?_ ?_ ?_ ?_ ?_ (fun z hz => hM z z hz hz (Or.inr rfl)) hu hv
      · intro u u' v
        simp [sa]
      · intro u v v'
        simp [sa]
      · intro a u v
        simp [sm]
      · intro a u v
        simp [sm]
      · intro u v
        exact hsym _ _
  · have := BilinearBound.abs_le_mul_norm_mul_norm (T := fun u v => Q (Pi.single b u) (Pi.single b' v))
      (by intro a u v; simp [sm]) (by intro a u v; simp [sm]) (fun u v hu hv => hM u v hu hv (Or.inl hbb)) P P'
    refine this.trans ?_
    have : 0 ≤ M * ‖P‖ * ‖P'‖ := by positivity
    nlinarith
open Classical in
theorem abs_firstDeriv_single_le {f : (s.free → imaginaryQuaternions) → ℝ} {K : ℝ} (b : s.free)
    (hK : ∀ X : imaginaryQuaternions, ‖X‖ = 1 → |fderiv ℝ f 0 (Pi.single b X)| ≤ K) (P : imaginaryQuaternions) :
    |fderiv ℝ f 0 (Pi.single b P)| ≤ K * ‖P‖ := by
  by_cases hP : P = 0
  · simp [hP]
  have nz : ‖P‖ ≠ 0 := norm_ne_zero_iff.mpr hP
  have ez : P = ‖P‖ • (‖P‖⁻¹ • P) := by rw [smul_smul, mul_inv_cancel₀ nz, one_smul]
  have h1 := hK (‖P‖⁻¹ • P) (by rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ nz])
  have e : fderiv ℝ f 0 (Pi.single b P) = ‖P‖ * fderiv ℝ f 0 (Pi.single b (‖P‖⁻¹ • P)) := by
    conv_lhs => rw [ez]
    have sm : (Pi.single b (‖P‖ • (‖P‖⁻¹ • P)) : s.free → imaginaryQuaternions) =
        ‖P‖ • Pi.single b (‖P‖⁻¹ • P) := by
      funext c'
      simp only [Pi.smul_apply, Pi.single_apply]
      split_ifs <;> simp
    rw [sm, map_smul, smul_eq_mul]
  rw [e, abs_mul, abs_norm]
  calc _ ≤ ‖P‖ * K := by gcongr
    _ = _ := by ring
end StepSettings.ChartSetting
end YangMills.Construction
end
