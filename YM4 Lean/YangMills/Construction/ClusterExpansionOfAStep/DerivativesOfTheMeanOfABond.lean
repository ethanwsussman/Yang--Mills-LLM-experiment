import YangMills.Construction.ClusterExpansionOfAStep.MovesOfAField
import YangMills.Construction.ClusterExpansionOfAStep.SlopeOfTheLogOfASettingProof
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion Topology
open Filter
namespace YangMills.Construction
open BlockAverages LumpContours ColdStepAtMirrorFrames TorusFields TorusLumps StepSettings StepCosts
namespace BondMeans
section Bounds
variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup W] [NormedSpace ℝ W]
theorem exists_bound_fderiv_of_isCompact {f : V → W} {S : Set V} (hS : IsCompact S)
    (hf : ∀ z ∈ S, ContDiffAt ℝ 3 f z) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ z ∈ S, ‖fderiv ℝ f z‖ ≤ K ∧ ‖fderiv ℝ (fderiv ℝ f) z‖ ≤ K := by
  obtain ⟨C₁, h₁⟩ := hS.exists_bound_of_continuousOn (f := fderiv ℝ f) fun z hz =>
    ((hf z hz).fderiv_right (m := 2) (by norm_num)).continuousAt.continuousWithinAt
  obtain ⟨C₂, h₂⟩ := hS.exists_bound_of_continuousOn (f := fderiv ℝ (fderiv ℝ f)) fun z hz =>
    (((hf z hz).fderiv_right (m := 2) (by norm_num)).fderiv_right (m := 1)
      (by norm_num)).continuousAt.continuousWithinAt
  refine ⟨max 0 (max C₁ C₂), le_max_left _ _, fun z hz => ⟨?_, ?_⟩⟩
  · exact (h₁ z hz).trans ((le_max_left _ _).trans (le_max_right _ _))
  · exact (h₂ z hz).trans ((le_max_right _ _).trans (le_max_right _ _))
theorem norm_iteratedFDeriv_two_eq (f : V → W) (z : V) :
    ‖iteratedFDeriv ℝ 2 f z‖ = ‖fderiv ℝ (fderiv ℝ f) z‖ := by
  rw [← norm_iteratedFDeriv_fderiv, norm_iteratedFDeriv_one]
theorem iteratedFDeriv_shift (f : V → W) (a : V) (k : ℕ) :
    iteratedFDeriv ℝ k (fun z => f (a + z)) = fun z => iteratedFDeriv ℝ k f (a + z) := by apply _root_.YangMills.Construction.FieldMoves.iteratedFDeriv_comp_const_add <;> assumption
end Bounds
section Tame
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
structure IsTame (f : E → ℍ[ℝ]) (p : E) (A B : ℝ) : Prop where
  smooth : ContDiff ℝ 3 f
  norm_le_one : ‖f p‖ ≤ 1
  firstDeriv_le : ‖iteratedFDeriv ℝ 1 f p‖ ≤ A
  secondDeriv_le : ‖iteratedFDeriv ℝ 2 f p‖ ≤ B
variable {f g : E → ℍ[ℝ]} {p : E} {A A' B B' : ℝ}
theorem IsTame.mono (h : IsTame f p A B) (hA : A ≤ A') (hB : B ≤ B') : IsTame f p A' B' :=
  ⟨h.smooth, h.norm_le_one, h.firstDeriv_le.trans hA, h.secondDeriv_le.trans hB⟩
theorem IsTame.congr (h : IsTame g p A B) (e : ∀ y, f y = g y) : IsTame f p A B := by
  have : f = g := funext e
  rw [this]
  exact h
theorem isTame_const (c : ℍ[ℝ]) (hc : ‖c‖ ≤ 1) (p : E) : IsTame (fun _ : E => c) p 0 0 := by
  refine ⟨contDiff_const, hc, ?_, ?_⟩
  · rw [iteratedFDeriv_const_of_ne (by norm_num)]
    simp
  · rw [iteratedFDeriv_const_of_ne (by norm_num)]
    simp
theorem IsTame.mul (hf : IsTame f p A B) (hg : IsTame g p A' B') :
    IsTame (fun y => f y * g y) p (A + A') (B + B' + 2 * A * A') := by
  have f0 : ‖iteratedFDeriv ℝ 0 f p‖ ≤ 1 := by
    rw [norm_iteratedFDeriv_zero]
    exact hf.norm_le_one
  have g0 : ‖iteratedFDeriv ℝ 0 g p‖ ≤ 1 := by
    rw [norm_iteratedFDeriv_zero]
    exact hg.norm_le_one
  have hA : 0 ≤ A := (norm_nonneg _).trans hf.firstDeriv_le
  refine ⟨hf.smooth.mul hg.smooth, ?_, ?_, ?_⟩
  · rw [norm_mul]
    exact mul_le_one₀ hf.norm_le_one (norm_nonneg _) hg.norm_le_one
  · have h := norm_iteratedFDeriv_mul_le (𝕜 := ℝ) (n := 1) hf.smooth hg.smooth p (by norm_num)
    have h' : ‖iteratedFDeriv ℝ 1 (fun y => f y * g y) p‖ ≤ ‖iteratedFDeriv ℝ 0 f p‖ * ‖iteratedFDeriv ℝ 1 g p‖ +
        ‖iteratedFDeriv ℝ 1 f p‖ * ‖iteratedFDeriv ℝ 0 g p‖ := by
      simpa [Finset.sum_range_succ] using h
    refine h'.trans ?_
    have h1 := mul_le_of_le_one_left (norm_nonneg (iteratedFDeriv ℝ 1 g p)) f0
    have h2 := mul_le_of_le_one_right (norm_nonneg (iteratedFDeriv ℝ 1 f p)) g0
    linarith [hf.firstDeriv_le, hg.firstDeriv_le]
  · have h := norm_iteratedFDeriv_mul_le (𝕜 := ℝ) (n := 2) hf.smooth hg.smooth p (by norm_num)
    have h' : ‖iteratedFDeriv ℝ 2 (fun y => f y * g y) p‖ ≤ ‖iteratedFDeriv ℝ 0 f p‖ * ‖iteratedFDeriv ℝ 2 g p‖ +
        2 * ‖iteratedFDeriv ℝ 1 f p‖ * ‖iteratedFDeriv ℝ 1 g p‖ +
        ‖iteratedFDeriv ℝ 2 f p‖ * ‖iteratedFDeriv ℝ 0 g p‖ := by
      simpa [Finset.sum_range_succ, Nat.choose] using h
    refine h'.trans ?_
    have h1 := mul_le_of_le_one_left (norm_nonneg (iteratedFDeriv ℝ 2 g p)) f0
    have h2 := mul_le_of_le_one_right (norm_nonneg (iteratedFDeriv ℝ 2 f p)) g0
    have h3 : ‖iteratedFDeriv ℝ 1 f p‖ * ‖iteratedFDeriv ℝ 1 g p‖ ≤ A * A' :=
      mul_le_mul hf.firstDeriv_le hg.firstDeriv_le (norm_nonneg _) hA
    linarith [hf.secondDeriv_le, hg.secondDeriv_le]
theorem IsTame.comp_clm (L : ℍ[ℝ] →L[ℝ] ℍ[ℝ]) (hL : ‖L‖ ≤ 1) (h : IsTame f p A B) :
    IsTame (fun y => L (f y)) p A B := by
  have key : ∀ k : ℕ, k ≤ 3 → ‖iteratedFDeriv ℝ k (fun y => L (f y)) p‖ ≤ ‖iteratedFDeriv ℝ k f p‖ := by
    intro k hk
    have e := L.iteratedFDeriv_comp_left (h.smooth.contDiffAt (x := p)) (i := k) (by exact_mod_cast hk)
    have e' : (fun y => L (f y)) = L ∘ f := rfl
    rw [e', e]
    refine (L.norm_compContinuousMultilinearMap_le _).trans ?_
    exact mul_le_of_le_one_left (norm_nonneg _) hL
  refine ⟨L.contDiff.comp h.smooth, ?_, (key 1 (by norm_num)).trans h.firstDeriv_le,
    (key 2 (by norm_num)).trans h.secondDeriv_le⟩
  calc ‖L (f p)‖ ≤ ‖L‖ * ‖f p‖ := L.le_opNorm _
    _ ≤ 1 * 1 := mul_le_mul hL h.norm_le_one (norm_nonneg _) (by norm_num)
    _ = 1 := by norm_num
theorem norm_iteratedFDeriv_average_le {ι : Type*} (S : Finset ι) (F : ι → E → ℍ[ℝ])
    (hF : ∀ e ∈ S, ContDiff ℝ 3 (F e)) {k : ℕ}
    (hk : k ≤ 3) {M : ℝ} (hM0 : 0 ≤ M) (hM : ∀ e ∈ S, ‖iteratedFDeriv ℝ k (F e) p‖ ≤ M) :
    ‖iteratedFDeriv ℝ k (fun y => (1 / (S.card : ℝ)) • ∑ e ∈ S, F e y) p‖ ≤ M := by
  have hk' : (k : WithTop ℕ∞) ≤ 3 := by exact_mod_cast hk
  have hs : ContDiffAt ℝ k (fun y => ∑ e ∈ S, F e y) p :=
    (ContDiff.sum hF).contDiffAt.of_le hk'
  rw [iteratedFDeriv_const_smul_apply' hs,
    iteratedFDeriv_fun_sum_apply fun e he => (hF e he).contDiffAt.of_le hk']
  rw [norm_smul]
  have h1 : ‖∑ e ∈ S, iteratedFDeriv ℝ k (F e) p‖ ≤ (S.card : ℝ) * M := by
    refine (norm_sum_le _ _).trans ?_
    calc _ ≤ ∑ _e ∈ S, M := Finset.sum_le_sum hM
      _ = _ := by simp
  rcases Nat.eq_zero_or_pos S.card with h0 | h0
  · simp [h0, hM0]
  · have hc : (0 : ℝ) < S.card := by exact_mod_cast h0
    rw [Real.norm_of_nonneg (by positivity)]
    calc _ ≤ 1 / (S.card : ℝ) * ((S.card : ℝ) * M) := by gcongr
      _ = M := by field_simp
def conjCLM : ℍ[ℝ] →L[ℝ] ℍ[ℝ] := LinearMap.toContinuousLinearMap
  { toFun := star
    map_add' := star_add
    map_smul' := fun c a => by
      apply Quaternion.ext <;> simp }
theorem conjCLM_apply (z : ℍ[ℝ]) : conjCLM z = star z := rfl
theorem norm_conjCLM_le : ‖conjCLM‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by norm_num) fun z => ?_
  rw [conjCLM_apply, norm_star, one_mul]
def sandwichCLM (a b : ℍ[ℝ]) : ℍ[ℝ] →L[ℝ] ℍ[ℝ] :=
  (ContinuousLinearMap.mul ℝ ℍ[ℝ] a).comp ((ContinuousLinearMap.mul ℝ ℍ[ℝ]).flip b)
theorem sandwichCLM_apply (a b z : ℍ[ℝ]) : sandwichCLM a b z = a * (z * b) := rfl
theorem norm_sandwichCLM_le {a b : ℍ[ℝ]} (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) : ‖sandwichCLM a b‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by norm_num) fun z => ?_
  rw [sandwichCLM_apply, norm_mul, norm_mul, ha, hb]
  simp
theorem contDiff_quaternionExp {k : WithTop ℕ∞} : ContDiff ℝ k (NormedSpace.exp : ℍ[ℝ] → ℍ[ℝ]) :=
  AnalyticOnNhd.contDiff fun x _ => NormedSpace.exp_analytic x
theorem exists_bound_quaternionExp : ∃ K : ℝ, 0 ≤ K ∧ ∀ z : ℍ[ℝ], ‖z‖ ≤ 2 →
    ‖iteratedFDeriv ℝ 1 (NormedSpace.exp : ℍ[ℝ] → ℍ[ℝ]) z‖ ≤ K ∧
      ‖iteratedFDeriv ℝ 2 (NormedSpace.exp : ℍ[ℝ] → ℍ[ℝ]) z‖ ≤ K := by
  obtain ⟨K, hK, h⟩ := exists_bound_fderiv_of_isCompact (f := (NormedSpace.exp : ℍ[ℝ] → ℍ[ℝ]))
    (isCompact_closedBall (0 : ℍ[ℝ]) 2) fun z _ => contDiff_quaternionExp.contDiffAt
  refine ⟨K, hK, fun z hz => ?_⟩
  have hz' : z ∈ Metric.closedBall (0 : ℍ[ℝ]) 2 := by simpa using hz
  rw [norm_iteratedFDeriv_one, norm_iteratedFDeriv_two_eq]
  exact h z hz'
theorem isTame_exp_affine {K : ℝ}
    (hexp : ∀ z : ℍ[ℝ], ‖z‖ ≤ 2 → ‖iteratedFDeriv ℝ 1 (NormedSpace.exp : ℍ[ℝ] → ℍ[ℝ]) z‖ ≤ K ∧
      ‖iteratedFDeriv ℝ 2 (NormedSpace.exp : ℍ[ℝ] → ℍ[ℝ]) z‖ ≤ K)
    (w : ℍ[ℝ]) (Λ : E →L[ℝ] ℍ[ℝ]) (hΛ : ‖Λ‖ ≤ 1) (hp : ‖w + Λ p‖ ≤ 2)
    (hu : ‖NormedSpace.exp (w + Λ p)‖ ≤ 1) : IsTame (fun y => NormedSpace.exp (w + Λ y)) p K K := by
  have hs : ContDiff ℝ 3 (fun z : ℍ[ℝ] => NormedSpace.exp (w + z)) :=
    contDiff_quaternionExp.comp (contDiff_const.add contDiff_id)
  have key : ∀ k : ℕ, k ≤ 3 → ‖iteratedFDeriv ℝ k (fun y => NormedSpace.exp (w + Λ y)) p‖ ≤
      ‖iteratedFDeriv ℝ k (NormedSpace.exp : ℍ[ℝ] → ℍ[ℝ]) (w + Λ p)‖ := by
    intro k hk
    have e : (fun y => NormedSpace.exp (w + Λ y)) = (fun z : ℍ[ℝ] => NormedSpace.exp (w + z)) ∘ Λ := rfl
    rw [e, Λ.iteratedFDeriv_comp_right hs p (by exact_mod_cast hk), iteratedFDeriv_shift]
    refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
    refine mul_le_of_le_one_right (norm_nonneg _) ?_
    exact Finset.prod_le_one (fun _ _ => norm_nonneg _) fun _ _ => hΛ
  exact ⟨hs.comp Λ.contDiff, hu, (key 1 (by norm_num)).trans (hexp _ hp).1,
    (key 2 (by norm_num)).trans (hexp _ hp).2⟩
theorem isTame_pathHolonomy {F : BlockFrame} {j : ℕ} (X : E → F.GaugeField j) {K : ℝ} (hK : 0 ≤ K)
    (hb : ∀ x i, IsTame (fun y => ((X y x i : UnitQuaternion) : ℍ[ℝ])) p K K) (l : List PathStep) :
    ∀ x, IsTame (fun y => ((pathHolonomy (X y) x l : UnitQuaternion) : ℍ[ℝ])) p (K * l.length)
      (K * l.length + (K * l.length) ^ 2) := by
  induction l with
  | nil =>
    intro x
    have h := isTame_const (E := E) (1 : ℍ[ℝ]) (by simp) p
    simpa [pathHolonomy] using h
  | cons st r ih =>
    intro x
    have hs : IsTame (fun y => ((linkValue (X y) x st : UnitQuaternion) : ℍ[ℝ])) p K K := by
      by_cases hst : st.2 = true
      · simpa [linkValue, hst] using hb x st.1
      · have h := (hb (x - BlockAverages.unitStep j st.1) st.1).comp_clm conjCLM norm_conjCLM_le
        have e : (fun y => ((linkValue (X y) x st : UnitQuaternion) : ℍ[ℝ])) =
            fun y => conjCLM (((X y (x - BlockAverages.unitStep j st.1) st.1 : UnitQuaternion) : ℍ[ℝ])) := by
          funext y
          simp only [linkValue, hst, Bool.false_eq_true, if_false]
          rw [conjCLM_apply]
          exact coe_inv_unitQuaternion _
        rw [e]
        exact h
    have hm := hs.mul (ih (x + stepDisplacement j st))
    have e : (fun y => ((pathHolonomy (X y) x (st :: r) : UnitQuaternion) : ℍ[ℝ])) = fun y =>
        ((linkValue (X y) x st : UnitQuaternion) : ℍ[ℝ]) *
          ((pathHolonomy (X y) (x + stepDisplacement j st) r : UnitQuaternion) : ℍ[ℝ]) := by
      funext y
      simp [pathHolonomy]
    rw [e]
    have hl : ((st :: r).length : ℝ) = r.length + 1 := by simp
    rw [hl]
    refine hm.mono (by linarith) ?_
    nlinarith
theorem isTame_contourMean {F : BlockFrame} (X : E → F.GaugeField F.depth) {K : ℝ} (hK : 0 ≤ K)
    (hb : ∀ x i, IsTame (fun y => ((X y x i : UnitQuaternion) : ℍ[ℝ])) p K K) (J₀ : ℕ)
    (h : Finset (Finset (F.Site F.depth)))
    (b : F.Cell → F.Site F.depth) (c : F.Cell × Fin 4) (M : ℕ)
    (hM : ∀ e ∈ usedContours J₀ h b c, (contourPath b c e.1 e.2).length ≤ M) :
    IsTame (fun y => contourMean J₀ h b (X y) c) p (K * M) (K * M + (K * M) ^ 2) := by
  have hKM : 0 ≤ K * (M : ℝ) := by positivity
  have hall : ∀ e ∈ usedContours J₀ h b c, IsTame
      (fun y => ((pathHolonomy (X y) (b c.1) (contourPath b c e.1 e.2) : UnitQuaternion) : ℍ[ℝ])) p (K * M)
      (K * M + (K * M) ^ 2) := by
    intro e he
    have h0 := isTame_pathHolonomy X hK hb (contourPath b c e.1 e.2) (b c.1)
    have hl : ((contourPath b c e.1 e.2).length : ℝ) ≤ M := by exact_mod_cast hM e he
    have h1 : K * ((contourPath b c e.1 e.2).length : ℝ) ≤ K * M := mul_le_mul_of_nonneg_left hl hK
    have h2 : 0 ≤ K * ((contourPath b c e.1 e.2).length : ℝ) := by positivity
    exact h0.mono h1 (by nlinarith)
  have hsm : ∀ e ∈ usedContours J₀ h b c, ContDiff ℝ 3
      (fun y => ((pathHolonomy (X y) (b c.1) (contourPath b c e.1 e.2) : UnitQuaternion) : ℍ[ℝ])) :=
    fun e he => (hall e he).smooth
  refine ⟨ContDiff.const_smul _ (ContDiff.sum hsm), ?_, ?_, ?_⟩
  · have h0 := norm_iteratedFDeriv_average_le (p := p) (usedContours J₀ h b c)
      (fun e y => ((pathHolonomy (X y) (b c.1) (contourPath b c e.1 e.2) : UnitQuaternion) : ℍ[ℝ])) hsm
      (k := 0) (by norm_num) (M := 1) (by norm_num) fun e he => by
        rw [norm_iteratedFDeriv_zero]
        exact (hall e he).norm_le_one
    rw [norm_iteratedFDeriv_zero] at h0
    exact h0
  · exact norm_iteratedFDeriv_average_le (p := p) (usedContours J₀ h b c)
      (fun e y => ((pathHolonomy (X y) (b c.1) (contourPath b c e.1 e.2) : UnitQuaternion) : ℍ[ℝ])) hsm
      (k := 1) (by norm_num) hKM fun e he => (hall e he).firstDeriv_le
  · exact norm_iteratedFDeriv_average_le (p := p) (usedContours J₀ h b c)
      (fun e y => ((pathHolonomy (X y) (b c.1) (contourPath b c e.1 e.2) : UnitQuaternion) : ℍ[ℝ])) hsm
      (k := 2) (by norm_num) (by positivity) fun e he => (hall e he).secondDeriv_le
end Tame
section Setting
open TorusContours ContourOffsets
variable {R : StepSetup} {n : ℕ}
def imaginaryCLM : EuclideanSpace ℝ (Fin 3) →L[ℝ] ℍ[ℝ] := LinearMap.toContinuousLinearMap
  { toFun := fun v => ((toImaginary v : imaginaryQuaternions) : ℍ[ℝ])
    map_add' := by
      intro a b
      refine Quaternion.ext _ _ ?_ ?_ ?_ ?_
      · show (0 : ℝ) = 0 + 0
        simp
      · show (a + b) 0 = a 0 + b 0
        simp
      · show (a + b) 1 = a 1 + b 1
        simp
      · show (a + b) 2 = a 2 + b 2
        simp
    map_smul' := by
      intro c a
      refine Quaternion.ext _ _ ?_ ?_ ?_ ?_
      · show (0 : ℝ) = c * 0
        simp
      · show (c • a) 0 = c * a 0
        simp
      · show (c • a) 1 = c * a 1
        simp
      · show (c • a) 2 = c * a 2
        simp }
theorem norm_toImaginary (v : EuclideanSpace ℝ (Fin 3)) :
    ‖((toImaginary v : imaginaryQuaternions) : ℍ[ℝ])‖ = ‖v‖ := by apply _root_.YangMills.Construction.BlockTrees.norm_toImaginary <;> assumption
def coordCLM {N : ℕ} {free : Finset (TorusBond N)} (b : free) : FreeCoords free →L[ℝ] ℍ[ℝ] :=
  imaginaryCLM.comp (ContinuousLinearMap.proj b)
theorem coordCLM_apply {N : ℕ} {free : Finset (TorusBond N)} (b : free) (η : FreeCoords free) :
    coordCLM b η = ((toImaginary (η b) : imaginaryQuaternions) : ℍ[ℝ]) := rfl
theorem norm_coordCLM_le {N : ℕ} {free : Finset (TorusBond N)} (b : free) : ‖coordCLM b‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by norm_num) fun η => ?_
  rw [coordCLM_apply, norm_toImaginary, one_mul]
  exact norm_le_pi_norm η b
open Classical in
theorem isTame_field (s : ChartSetting R n) {K : ℝ} (hK : 0 ≤ K)
    (hexp : ∀ z : ℍ[ℝ], ‖z‖ ≤ 2 → ‖iteratedFDeriv ℝ 1 (NormedSpace.exp : ℍ[ℝ] → ℍ[ℝ]) z‖ ≤ K ∧
      ‖iteratedFDeriv ℝ 2 (NormedSpace.exp : ℍ[ℝ] → ℍ[ℝ]) z‖ ≤ K)
    (p : FreeCoords s.free)
    (hsize : ∀ b : s.free, ‖((s.frame b.1 + toImaginary (p b) : imaginaryQuaternions) : ℍ[ℝ])‖ ≤ 2)
    (x : TorusSite (n * R.params.side)) (i : Fin 4) :
    IsTame (fun η : FreeCoords s.free => ((s.field η x i : UnitQuaternion) : ℍ[ℝ])) p K K := by
  by_cases h : (x, i) ∈ s.free
  · set b : s.free := ⟨(x, i), h⟩ with hb
    have hline : IsTame (fun η => NormedSpace.exp
        (((s.frame (x, i) : imaginaryQuaternions) : ℍ[ℝ]) + coordCLM b η)) p K K := by
      refine isTame_exp_affine hexp _ _ (norm_coordCLM_le b) (hsize b) ?_
      exact (norm_unitQuaternion (expUnit (s.frame (x, i) + toImaginary (p b)))).le
    by_cases hc : IsCrossingBond (F := stepBlockFrame R.params.side n)
        (torusSiteInFrame (stepBlockFrame R.params.side n) 0 x, i)
    · have ha : ‖(((gaugeAt s.fine x)⁻¹ : UnitQuaternion) : ℍ[ℝ])‖ = 1 := norm_unitQuaternion _
      have hb' : ‖(((s.coarse (parentBlock R.params.side x) i *
          gaugeAt s.fine (x + TorusFields.unitStep (n * R.params.side) i) : UnitQuaternion)) : ℍ[ℝ])‖ = 1 :=
        norm_unitQuaternion _
      have h1 := hline.comp_clm _ (norm_sandwichCLM_le ha hb')
      refine h1.congr fun η => ?_
      have e1 : s.field η x i = chartLink s x i (s.frame (x, i) + toImaginary (η b)) := dif_pos h
      rw [e1, sandwichCLM_apply]
      unfold chartLink
      rw [if_pos hc]
      simp only [Submonoid.coe_mul, mul_assoc]
      rfl
    · have ha : ‖(((gaugeAt s.fine x)⁻¹ : UnitQuaternion) : ℍ[ℝ])‖ = 1 := norm_unitQuaternion _
      have hb' : ‖((gaugeAt s.fine (x + TorusFields.unitStep (n * R.params.side) i) : UnitQuaternion) :
          ℍ[ℝ])‖ = 1 := norm_unitQuaternion _
      have h1 := hline.comp_clm _ (norm_sandwichCLM_le ha hb')
      refine h1.congr fun η => ?_
      have e1 : s.field η x i = chartLink s x i (s.frame (x, i) + toImaginary (η b)) := dif_pos h
      rw [e1, sandwichCLM_apply]
      unfold chartLink
      rw [if_neg hc]
      simp only [Submonoid.coe_mul, mul_assoc]
      rfl
  · have e : (fun η : FreeCoords s.free => ((s.field η x i : UnitQuaternion) : ℍ[ℝ])) =
        fun _ => ((s.fine x i : UnitQuaternion) : ℍ[ℝ]) := by
      funext η
      have e1 : s.field η x i = s.fine x i := dif_neg h
      rw [e1]
    rw [e]
    exact (isTame_const _ (norm_unitQuaternion _).le p).mono hK hK
theorem length_contourSteps_le {L : ℕ} {z₀ z₁ ξ : Fin 4 → ℤ} (h₀ : z₀ ∈ centredCube L)
    (h₁ : z₁ ∈ centredCube L) (hξ : ξ ∈ centredCube L)
    (π : Equiv.Perm (Fin 4)) (i : Fin 4) : (contourSteps L z₀ z₁ ξ π i).length ≤ 9 * L := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.LogJacobianSlope.length_contourSteps_le <;> assumption
theorem length_contourPath_le {L : ℕ} [NeZero L] [NeZero n] (hn : 2 ≤ n) {J₀ J₀' : ℕ}
    {h : Finset (Finset ((stepBlockFrame L n).Site 0))} {b : BaseChoice L n}
    (hb : IsBaseChoice (F := stepBlockFrame L n) J₀ h b) (c : (stepBlockFrame L n).Cell × Fin 4)
    (h' : Finset (Finset ((stepBlockFrame L n).Site 0))) (e : (Fin 4 → ℤ) × Equiv.Perm (Fin 4))
    (he : e ∈ usedContours (F := stepBlockFrame L n) J₀' h' b c) :
    (contourPath (F := stepBlockFrame L n) b c e.1 e.2).length ≤ 9 * L := by
  classical
  have hL : 1 ≤ (stepBlockFrame L n).blockSide := Nat.pos_of_ne_zero (NeZero.ne L)
  obtain ⟨z₀, h₀, e₀⟩ := exists_centredCube_of_isBaseChoice hL hb c.1
  obtain ⟨z₁, h₁, e₁⟩ := exists_centredCube_of_isBaseChoice hL hb
    (c.1 + BlockAverages.unitStep (stepBlockFrame L n).top c.2)
  have he' : e ∈ allContours (stepBlockFrame L n) := by
    unfold usedContours at he
    split_ifs at he
    · exact he
    · exact (Finset.mem_filter.mp he).1
  have hξ : e.1 ∈ centredCube (stepBlockFrame L n).blockSide := (Finset.mem_product.mp he').1
  have hbig : ∀ i, 2 * (((stepBlockFrame L n).blockSide : ℕ) : ℤ) ≤
      (((stepBlockFrame L n).period (stepBlockFrame L n).depth i : ℕ) : ℤ) := by
    intro i
    have h1 : (stepBlockFrame L n).period (stepBlockFrame L n).depth i = n * L :=
      stepBlockFrame_period_zero i
    rw [h1]
    show 2 * (L : ℤ) ≤ ((n * L : ℕ) : ℤ)
    push_cast
    nlinarith
  have hs := contourPath_eq_contourSteps hbig h₀ h₁ hξ e₀ e₁ e.2
  have hs' : contourPath (F := stepBlockFrame L n) b c e.1 e.2 = _ := hs
  rw [hs']
  exact length_contourSteps_le h₀ h₁ hξ _ _
def bondMean (s : ChartSetting R n) (h : Finset (Finset ((stepBlockFrame R.params.side n).Site 0)))
    (c : TorusBond n) (η : FreeCoords s.free) : ℍ[ℝ] :=
  contourMean R.params.baseDepth h s.bases
    (readAtLevel (stepBlockFrame R.params.side n) 0 (s.field η))
    (torusSiteInFrame (stepBlockFrame R.params.side n) 1 c.1, c.2)
theorem isTame_bondMean [NeZero n] (s : ChartSetting R n) {K : ℝ} (hK : 0 ≤ K)
    (hexp : ∀ z : ℍ[ℝ], ‖z‖ ≤ 2 → ‖iteratedFDeriv ℝ 1 (NormedSpace.exp : ℍ[ℝ] → ℍ[ℝ]) z‖ ≤ K ∧
      ‖iteratedFDeriv ℝ 2 (NormedSpace.exp : ℍ[ℝ] → ℍ[ℝ]) z‖ ≤ K)
    (p : FreeCoords s.free)
    (hsize : ∀ b : s.free, ‖((s.frame b.1 + toImaginary (p b) : imaginaryQuaternions) : ℍ[ℝ])‖ ≤ 2)
    (hn : 2 ≤ n) {J₀ : ℕ}
    {h₁ : Finset (Finset ((stepBlockFrame R.params.side n).Site 0))}
    (hb : IsBaseChoice (F := stepBlockFrame R.params.side n) J₀ h₁ s.bases)
    (h : Finset (Finset ((stepBlockFrame R.params.side n).Site 0))) (c : TorusBond n) :
    IsTame (bondMean s h c) p (K * (9 * R.params.side : ℕ))
      (K * (9 * R.params.side : ℕ) + (K * (9 * R.params.side : ℕ)) ^ 2) :=
  isTame_contourMean (F := stepBlockFrame R.params.side n)
    (fun η => readAtLevel (stepBlockFrame R.params.side n) 0 (s.field η)) hK
    (fun x i => isTame_field s hK hexp p hsize _ i) R.params.baseDepth h s.bases _ (9 * R.params.side)
    (fun e he => length_contourPath_le hn hb _ h e he)
end Setting
end BondMeans
end YangMills.Construction
end
