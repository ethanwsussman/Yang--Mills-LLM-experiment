import YangMills.Construction.ClusterExpansionOfAStep.CumulantsOfABoundedExponent
import YangMills.Construction.ClusterExpansionOfAStep.CumulantsOfTheKernelsAtMovedBonds
import YangMills.Construction.ResponseInTheExpansion.SizeOfTheMeanOfABond
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion ContDiff Nat
open MeasureTheory
namespace YangMills.Construction
open BlockAverages LumpContours TorusFields TorusLumps Cumulants
namespace KernelCumulants
theorem norm_coe_unitQuaternion (g : UnitQuaternion) : ‖((g : UnitQuaternion) : ℍ[ℝ])‖ = 1 := by apply _root_.YangMills.Construction.BlockAverages.norm_coe_unitQuaternion <;> assumption
theorem norm_contourMean_le {F : BlockFrame} (J₀ : ℕ) (h : Finset (Finset (F.Site F.depth)))
    (b : F.Cell → F.Site F.depth) (W : F.GaugeField F.depth) (c : F.Cell × Fin 4) :
    ‖contourMean J₀ h b W c‖ ≤ 1 := by apply _root_.YangMills.Construction.WeightedResponses.norm_contourMean_le <;> assumption
theorem coe_inv_expUnit (w : imaginaryQuaternions) :
    (((expUnit w)⁻¹ : UnitQuaternion) : ℍ[ℝ]) = NormedSpace.exp (-(w : ℍ[ℝ])) := by
  have h : (((expUnit w)⁻¹ * expUnit w : UnitQuaternion) : ℍ[ℝ]) = 1 := by simp
  have h2 : (((expUnit w)⁻¹ : UnitQuaternion) : ℍ[ℝ]) * NormedSpace.exp (w : ℍ[ℝ]) = 1 := h
  have h3 : star (NormedSpace.exp (w : ℍ[ℝ])) * NormedSpace.exp (w : ℍ[ℝ]) = 1 :=
    (Unitary.mem_iff.mp (exp_imaginary_mem_unitary w)).1
  have hne : NormedSpace.exp (w : ℍ[ℝ]) ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at h3
    exact zero_ne_one h3
  have h4 : (((expUnit w)⁻¹ : UnitQuaternion) : ℍ[ℝ]) = star (NormedSpace.exp (w : ℍ[ℝ])) :=
    mul_right_cancel₀ hne (h2.trans h3.symm)
  rw [h4, NormedSpace.star_exp]
  congr 1
  have hw : (w : ℍ[ℝ]).re = 0 := w.2
  ext <;> simp [hw]
theorem norm_iteratedFDeriv_exp_zero_le {𝔸 : Type} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [Algebra ℚ 𝔸]
    [CompleteSpace 𝔸] {i : ℕ} (hi : 1 ≤ i) :
    ‖iteratedFDeriv ℝ i (NormedSpace.exp : 𝔸 → 𝔸) 0‖ ≤ 1 := by
  have hs := NormedSpace.exp_hasFPowerSeriesOnBall (𝕂 := ℝ) (𝔸 := 𝔸)
  refine ContinuousMultilinearMap.opNorm_le_bound zero_le_one fun m => ?_
  rw [hs.iteratedFDeriv_eq_sum_of_completeSpace, one_mul]
  have hp : ∀ v : Fin i → 𝔸, ‖NormedSpace.expSeries ℝ 𝔸 i v‖ ≤ (i ! : ℝ)⁻¹ * ∏ l, ‖v l‖ := by
    intro v
    have hn : ‖NormedSpace.expSeries ℝ 𝔸 i‖ ≤ (i ! : ℝ)⁻¹ := by
      unfold NormedSpace.expSeries
      have := ContinuousMultilinearMap.norm_mkPiAlgebraFin_le_of_pos (𝕜 := ℝ) (A := 𝔸) (n := i) hi
      refine (norm_smul_le ((i ! : ℝ)⁻¹) (ContinuousMultilinearMap.mkPiAlgebraFin ℝ i 𝔸)).trans ?_
      rw [norm_inv, Real.norm_natCast]
      calc _ ≤ (i ! : ℝ)⁻¹ * 1 := by gcongr
        _ = _ := mul_one _
    refine ((NormedSpace.expSeries ℝ 𝔸 i).le_opNorm v).trans ?_
    gcongr
  calc ‖∑ σ : Equiv.Perm (Fin i), NormedSpace.expSeries ℝ 𝔸 i (fun l => m (σ l))‖
      ≤ ∑ σ : Equiv.Perm (Fin i), (i ! : ℝ)⁻¹ * ∏ l, ‖m l‖ := by
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun σ _ => ?_)
        refine (hp _).trans (le_of_eq ?_)
        congr 1
        exact Equiv.prod_comp σ fun l => ‖m l‖
    _ = ∏ l, ‖m l‖ := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin, nsmul_eq_mul]
        have : (i ! : ℝ) ≠ 0 := by exact_mod_cast i.factorial_ne_zero
        field_simp
def quatCoord (e : Fin 4) (q : ℍ[ℝ]) : ℝ := ![q.re, q.imI, q.imJ, q.imK] e
def reSign (e : Fin 4) : ℝ := ![1, -1, -1, -1] e
theorem re_mul_eq_sum_coord (p q : ℍ[ℝ]) :
    (p * q).re = ∑ e, quatCoord e p * (reSign e * quatCoord e q) := by
  simp [Fin.sum_univ_four, quatCoord, reSign, Quaternion.re_mul]
  ring
theorem abs_quatCoord_le (e : Fin 4) (q : ℍ[ℝ]) : |quatCoord e q| ≤ ‖q‖ := by
  have h : ‖q‖ ^ 2 = q.re ^ 2 + q.imI ^ 2 + q.imJ ^ 2 + q.imK ^ 2 := by
    rw [sq, ← Quaternion.normSq_eq_norm_mul_self, Quaternion.normSq_def']
  refine abs_le_of_sq_le_sq ?_ (norm_nonneg q)
  fin_cases e <;> simp [quatCoord] <;>
    nlinarith [sq_nonneg q.re, sq_nonneg q.imI, sq_nonneg q.imJ, sq_nonneg q.imK]
theorem abs_re_le_norm (q : ℍ[ℝ]) : |q.re| ≤ ‖q‖ := abs_quatCoord_le 0 q
def quatCoordLinear (e : Fin 4) : ℍ[ℝ] →ₗ[ℝ] ℝ where
  toFun := quatCoord e
  map_add' p q := by fin_cases e <;> simp [quatCoord]
  map_smul' r q := by fin_cases e <;> simp [quatCoord]
theorem exp_pi_eval {ι : Type} [Fintype ι] (y : ι → ℍ[ℝ]) (c : ι) :
    (NormedSpace.exp y : ι → ℍ[ℝ]) c = NormedSpace.exp (y c) := by
  have h1 := NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) y
  have h2 := NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) (y c)
  have h3 := h1.map (Pi.evalAddMonoidHom (fun _ : ι => ℍ[ℝ]) c) (continuous_apply c)
  refine h3.unique ?_
  convert h2 using 1
  funext m
  simp [Pi.evalAddMonoidHom]
theorem factorial_mul_pow_le {k : ℕ} (h1 : 1 ≤ k) (h3 : k ≤ 3) {s : ℝ} (hs : 0 < s) :
    (k ! : ℝ) * 6 * (((k : ℝ) + 1) * s) ^ k ≤ (32 * s) ^ k := by
  have hs2 : 0 < s ^ 2 := by positivity
  have hs3 : 0 < s ^ 3 := by positivity
  interval_cases k
  · norm_num [Nat.factorial]
    nlinarith
  · norm_num [Nat.factorial]
    nlinarith
  · norm_num [Nat.factorial]
    nlinarith
abbrev StepBond (ℓ : StepParameters) (n : ℕ) : Type := (stepBlockFrame ℓ.side n).Cell × Fin 4
abbrev BondQuaternions (ℓ : StepParameters) (n : ℕ) : Type := StepBond ℓ n → ℍ[ℝ]
variable {ℓ : StepParameters} {n : ℕ}
def stepBondToTorus (c' : StepBond ℓ n) : TorusBond n := (toTorusSite n c'.1, c'.2)
theorem eq_of_intCast_cast_eq {p m : ℕ} (h : p = m) (a b : ZMod p)
    (hab : (((ZMod.cast a : ℤ)) : ZMod m) = (((ZMod.cast b : ℤ)) : ZMod m)) : a = b := by
  subst h
  rcases p with _ | p
  · simpa using hab
  · simpa [ZMod.intCast_cast, ZMod.cast_id] using hab
theorem stepBondToTorus_injective : Function.Injective (stepBondToTorus (ℓ := ℓ) (n := n)) := by
  intro p q h
  have h1 : toTorusSite n p.1 = toTorusSite n q.1 := congrArg (fun b : TorusBond n => b.1) h
  have h2 : p.2 = q.2 := congrArg (fun b : TorusBond n => b.2) h
  refine Prod.ext (funext fun i => ?_) h2
  have h3 := congrFun h1 i
  have hper : (stepBlockFrame ℓ.side n).period (stepBlockFrame ℓ.side n).top i = n := by
    simp [stepBlockFrame, BlockFrame.period, BlockFrame.top]
  exact eq_of_intCast_cast_eq hper _ _ h3
def moveAt {k : ℕ} (c : Fin k → TorusBond n) (X : Fin k → imaginaryQuaternions) (σ : Fin k → ℝ)
    (b : TorusBond n) : imaginaryQuaternions :=
  ∑ l, if c l = b then σ l • X l else 0
def invField (V : TorusField n) (c' : StepBond ℓ n) : ℍ[ℝ] :=
  (((readAtLevel (stepBlockFrame ℓ.side n) 1 V c'.1 c'.2)⁻¹ : UnitQuaternion) : ℍ[ℝ])
def contourWeight (W : (stepBlockFrame ℓ.side n).GaugeField 0)
    (b : (stepBlockFrame ℓ.side n).Cell → (stepBlockFrame ℓ.side n).Site 0)
    (c' : StepBond ℓ n) : ℍ[ℝ] :=
  contourMean ℓ.baseDepth (hotLumps ℓ.grid ℓ.threshold (levelSites (stepBlockFrame ℓ.side n) 0) W) b W c'
theorem norm_invField (V : TorusField n) (c' : StepBond ℓ n) : ‖invField (ℓ := ℓ) V c'‖ = 1 :=
  norm_coe_unitQuaternion _
theorem norm_contourWeight_le (W : (stepBlockFrame ℓ.side n).GaugeField 0)
    (b : (stepBlockFrame ℓ.side n).Cell → (stepBlockFrame ℓ.side n).Site 0) (c' : StepBond ℓ n) :
    ‖contourWeight W b c'‖ ≤ 1 :=
  norm_contourMean_le _ _ _ _ _
theorem bondKernel_perturb (x : ℝ) (W : (stepBlockFrame ℓ.side n).GaugeField 0)
    (b : (stepBlockFrame ℓ.side n).Cell → (stepBlockFrame ℓ.side n).Site 0) (V : TorusField n) {k : ℕ}
    (c : Fin k → TorusBond n) (X : Fin k → imaginaryQuaternions) (σ : Fin k → ℝ) (c' : StepBond ℓ n) :
    bondKernel ℓ x W (readAtLevel (stepBlockFrame ℓ.side n) 1 (perturb c X σ V)) b c' =
      bondKernel ℓ x W (readAtLevel (stepBlockFrame ℓ.side n) 1 V) b c' *
        Real.exp (ℓ.coupling * x * ((contourWeight W b c' * (invField V c' *
            NormedSpace.exp (-((moveAt c X σ (stepBondToTorus c') : imaginaryQuaternions) : ℍ[ℝ])))).re -
          (contourWeight W b c' * (invField V c' * 1)).re)) := by
  have e : (((readAtLevel (stepBlockFrame ℓ.side n) 1 (perturb c X σ V) c'.1 c'.2)⁻¹ : UnitQuaternion) : ℍ[ℝ]) =
      invField V c' * NormedSpace.exp (-((moveAt c X σ (stepBondToTorus c') : imaginaryQuaternions) : ℍ[ℝ])) := by
    have h : readAtLevel (stepBlockFrame ℓ.side n) 1 (perturb c X σ V) c'.1 c'.2 =
        expUnit (moveAt c X σ (stepBondToTorus c')) * readAtLevel (stepBlockFrame ℓ.side n) 1 V c'.1 c'.2 := rfl
    rw [h, mul_inv_rev, ← coe_inv_expUnit]
    rfl
  simp only [bondKernel]
  rw [e, mul_one, div_mul_eq_mul_div, ← Real.exp_add]
  simp only [contourWeight, invField, mul_assoc]
  congr 2
  ring
theorem zero_le_partitionFn (s : ℝ) : 0 ≤ partitionFn s := integral_nonneg fun _ => (Real.exp_pos _).le
theorem zero_le_bondKernel (x : ℝ) (W : (stepBlockFrame ℓ.side n).GaugeField 0)
    (V : (stepBlockFrame ℓ.side n).GaugeField 1)
    (b : (stepBlockFrame ℓ.side n).Cell → (stepBlockFrame ℓ.side n).Site 0) (c' : StepBond ℓ n) :
    0 ≤ bondKernel ℓ x W V b c' :=
  div_nonneg (Real.exp_pos _).le (zero_le_partitionFn _)
variable [NeZero n]
def coordForm (V : TorusField n) (p : StepBond ℓ n × Fin 4) : BondQuaternions ℓ n →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap (reSign p.2 • ((quatCoordLinear p.2) ∘ₗ
    (LinearMap.mulLeft ℝ (invField (ℓ := ℓ) V p.1)) ∘ₗ (LinearMap.proj p.1)))
theorem coordForm_apply (V : TorusField n) (p : StepBond ℓ n × Fin 4) (θ : BondQuaternions ℓ n) :
    coordForm V p θ = reSign p.2 * quatCoord p.2 (invField V p.1 * θ p.1) := by
  simp [coordForm, quatCoordLinear]
def coordCoeff {Ξ : Type} (Cs : Finset (StepBond ℓ n)) (N : ℝ) (Wf : Ξ → (stepBlockFrame ℓ.side n).GaugeField 0)
    (bf : Ξ → (stepBlockFrame ℓ.side n).Cell → (stepBlockFrame ℓ.side n).Site 0) (p : StepBond ℓ n × Fin 4)
    (ξ : Ξ) : ℝ :=
  (if p.1 ∈ Cs then 1 / N else 0) * quatCoord p.2 (contourWeight (Wf ξ) (bf ξ) p.1)
theorem sum_coordCoeff_mul_coordForm {Ξ : Type} (Cs : Finset (StepBond ℓ n)) (N : ℝ)
    (Wf : Ξ → (stepBlockFrame ℓ.side n).GaugeField 0)
    (bf : Ξ → (stepBlockFrame ℓ.side n).Cell → (stepBlockFrame ℓ.side n).Site 0) (V : TorusField n) (ξ : Ξ)
    (θ : BondQuaternions ℓ n) :
    ∑ p, coordCoeff Cs N Wf bf p ξ * coordForm V p θ =
      1 / N * ∑ c' ∈ Cs, (contourWeight (Wf ξ) (bf ξ) c' * (invField V c' * θ c')).re := by
  rw [Fintype.sum_prod_type]
  have h : ∀ c' : StepBond ℓ n, ∑ e, coordCoeff Cs N Wf bf (c', e) ξ * coordForm V (c', e) θ =
      (if c' ∈ Cs then 1 / N else 0) * (contourWeight (Wf ξ) (bf ξ) c' * (invField V c' * θ c')).re := by
    intro c'
    rw [re_mul_eq_sum_coord, Finset.mul_sum]
    refine Finset.sum_congr rfl fun e _ => ?_
    rw [coordForm_apply]
    simp only [coordCoeff]
    ring
  simp only [h, ite_mul, zero_mul, Finset.sum_ite_mem, Finset.univ_inter, Finset.mul_sum]
theorem measurable_quatCoord {Ξ : Type} [MeasurableSpace Ξ] {f : Ξ → ℍ[ℝ]} (hf : MeasurableQuaternion f)
    (e : Fin 4) : Measurable fun ξ => quatCoord e (f ξ) := by
  obtain ⟨h0, h1, h2, h3⟩ := hf
  fin_cases e
  · exact h0
  · exact h1
  · exact h2
  · exact h3
theorem abs_re_contourWeight_mul_le (W : (stepBlockFrame ℓ.side n).GaugeField 0)
    (b : (stepBlockFrame ℓ.side n).Cell → (stepBlockFrame ℓ.side n).Site 0) (V : TorusField n)
    (c' : StepBond ℓ n) (θ : BondQuaternions ℓ n) :
    |(contourWeight W b c' * (invField V c' * θ c')).re| ≤ ‖θ‖ := by
  refine (abs_re_le_norm _).trans ?_
  rw [norm_mul, norm_mul, norm_invField, one_mul]
  calc ‖contourWeight W b c'‖ * ‖θ c'‖ ≤ 1 * ‖θ‖ :=
        mul_le_mul (norm_contourWeight_le W b c') (norm_le_pi_norm θ c') (norm_nonneg _) zero_le_one
    _ = ‖θ‖ := one_mul _
def moveMap {k : ℕ} (c : Fin k → TorusBond n) (X : Fin k → imaginaryQuaternions) :
    (Fin k → ℝ) →L[ℝ] BondQuaternions ℓ n :=
  ∑ l, (ContinuousLinearMap.proj l : (Fin k → ℝ) →L[ℝ] ℝ).smulRight
    (fun c' : StepBond ℓ n => if c l = stepBondToTorus c' then -((X l : imaginaryQuaternions) : ℍ[ℝ]) else 0)
theorem moveMap_apply {k : ℕ} (c : Fin k → TorusBond n) (X : Fin k → imaginaryQuaternions) (σ : Fin k → ℝ)
    (c' : StepBond ℓ n) :
    moveMap c X σ c' = -((moveAt c X σ (stepBondToTorus c') : imaginaryQuaternions) : ℍ[ℝ]) := by
  simp only [moveMap, moveAt]
  rw [ContinuousLinearMap.sum_apply, Finset.sum_apply, Submodule.coe_sum, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun l _ => ?_
  by_cases h : c l = stepBondToTorus c' <;> simp [h]
theorem norm_moveMap_single_le {k : ℕ} (c : Fin k → TorusBond n) (X : Fin k → imaginaryQuaternions)
    (hX : AreUnitVectors X) (l : Fin k) :
    ‖moveMap (ℓ := ℓ) c X (Pi.single l 1)‖ ≤ 1 := by
  refine (pi_norm_le_iff_of_nonneg zero_le_one).mpr fun c' => ?_
  rw [moveMap_apply]
  have e : moveAt c X (Pi.single l 1) (stepBondToTorus (ℓ := ℓ) c') =
      if c l = stepBondToTorus c' then X l else 0 := by
    simp only [moveAt]
    rw [Finset.sum_eq_single l]
    · by_cases h : c l = stepBondToTorus c' <;> simp [h]
    · intro l' _ hl
      simp [Pi.single_eq_of_ne hl]
    · simp
  rw [e]
  by_cases h : c l = stepBondToTorus c'
  · simp only [h, if_true, norm_neg]
    exact (hX l).le
  · simp [h]
end KernelCumulants
open KernelCumulants in
theorem TorusLumps.kernelCumulantBound_of_cumulantBounds (hL : CumulantBounds) :
    KernelCumulantBound := by
  intro ℓ x n _ Ξ _ μ A W b V hs hA0 hm hint hpos k c X
  classical
  set s : ℝ := ℓ.coupling * x with hsdef
  set N : ℝ := (k : ℝ) + 1 with hN
  have hNpos : 0 < N := by positivity
  set lam : ℝ := N * s with hlam
  have hs0 : 0 < s := lt_of_lt_of_le one_pos hs
  have hN1 : 1 ≤ N := by
    have : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    linarith
  have hlam1 : 1 ≤ lam := by nlinarith
  set Cs : Finset (StepBond ℓ n) := Finset.univ.filter fun c' => ∃ l, c l = stepBondToTorus c' with hCs
  have hcard : (Cs.card : ℝ) ≤ N := by
    have h1 : Cs.card ≤ k := by
      have h2 : Cs.image stepBondToTorus ⊆ Finset.univ.image c := by
        intro b' hb'
        obtain ⟨c', hc', rfl⟩ := Finset.mem_image.mp hb'
        obtain ⟨l, hl⟩ := (Finset.mem_filter.mp hc').2
        exact Finset.mem_image.mpr ⟨l, Finset.mem_univ _, hl⟩
      calc Cs.card = (Cs.image stepBondToTorus).card :=
            (Finset.card_image_of_injective _ stepBondToTorus_injective).symm
        _ ≤ (Finset.univ.image c).card := Finset.card_le_card h2
        _ ≤ (Finset.univ : Finset (Fin k)).card := Finset.card_image_le
        _ = k := by simp
    have h3 : (Cs.card : ℝ) ≤ k := by exact_mod_cast h1
    linarith
  let ex : Ξ → BondQuaternions ℓ n → ℝ := fun ξ θ => ∑ p, coordCoeff Cs N W b p ξ * coordForm V p θ
  have hex : ∀ ξ θ, ex ξ θ =
      1 / N * ∑ c' ∈ Cs, (contourWeight (W ξ) (b ξ) c' * (invField V c' * θ c')).re :=
    fun ξ θ => sum_coordCoeff_mul_coordForm Cs N W b V ξ θ
  have hexb : ∀ ξ θ, |ex ξ θ| ≤ ‖θ‖ := by
    intro ξ θ
    rw [hex, abs_mul, abs_of_pos (by positivity : 0 < 1 / N)]
    have h1 : |∑ c' ∈ Cs, (contourWeight (W ξ) (b ξ) c' * (invField V c' * θ c')).re| ≤
        (Cs.card : ℝ) * ‖θ‖ := by
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      calc _ ≤ ∑ _c' ∈ Cs, ‖θ‖ := Finset.sum_le_sum fun c' _ => abs_re_contourWeight_mul_le _ _ V c' θ
        _ = (Cs.card : ℝ) * ‖θ‖ := by simp
    calc 1 / N * _ ≤ 1 / N * (N * ‖θ‖) := by
          gcongr
          exact h1.trans (by gcongr)
      _ = ‖θ‖ := by field_simp
  have hum : ∀ p, Measurable (coordCoeff Cs N W b p) := fun p =>
    (measurable_quatCoord (hm p.1) p.2).const_mul _
  have hub : ∀ p ξ, |coordCoeff Cs N W b p ξ| ≤ 1 := by
    intro p ξ
    simp only [coordCoeff]
    rw [abs_mul]
    have h1 : |if p.1 ∈ Cs then 1 / N else 0| ≤ 1 := by
      split_ifs
      · rw [abs_of_pos (by positivity)]
        exact (div_le_one hNpos).mpr hN1
      · simp
    have h2 : |quatCoord p.2 (contourWeight (W ξ) (b ξ) p.1)| ≤ 1 :=
      (abs_quatCoord_le _ _).trans (norm_contourWeight_le _ _ _)
    calc _ ≤ (1 : ℝ) * 1 := mul_le_mul h1 h2 (abs_nonneg _) zero_le_one
      _ = 1 := one_mul _
  have hexm : ∀ θ, Measurable fun ξ => ex ξ θ := fun θ =>
    Finset.measurable_fun_sum _ fun p _ => (hum p).mul_const _
  set G0 : ℝ := kernelProductMean ℓ x μ A W b V with hG0
  let K : Ξ → ℝ := fun ξ => A ξ * ∏ c' : StepBond ℓ n,
    bondKernel ℓ x (W ξ) (readAtLevel (stepBlockFrame ℓ.side n) 1 V) (b ξ) c'
  have hK0 : ∀ ξ, 0 ≤ K ξ := fun ξ =>
    mul_nonneg (hA0 ξ) (Finset.prod_nonneg fun c' _ => zero_le_bondKernel _ _ _ _ _)
  set θ0 : BondQuaternions ℓ n := lam • (1 : BondQuaternions ℓ n) with hθ0
  let wt : Ξ → ℝ := fun ξ => G0⁻¹ * K ξ * Real.exp (-ex ξ θ0)
  have hwt0 : ∀ ξ, 0 ≤ wt ξ := fun ξ =>
    mul_nonneg (mul_nonneg (inv_nonneg.mpr hpos.le) (hK0 ξ)) (Real.exp_pos _).le
  have hwti : Integrable wt μ := by
    refine (hint.const_mul (G0⁻¹ * Real.exp ‖θ0‖)).mono'
      ((hint.aestronglyMeasurable.const_mul _).mul
        (Real.measurable_exp.comp (hexm θ0).neg).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun ξ => ?_)
    have h1 : Real.exp (-ex ξ θ0) ≤ Real.exp ‖θ0‖ :=
      Real.exp_le_exp.mpr ((neg_le_abs _).trans (hexb ξ θ0))
    rw [Real.norm_of_nonneg (hwt0 ξ)]
    have h2 : 0 ≤ G0⁻¹ * K ξ := mul_nonneg (inv_nonneg.mpr hpos.le) (hK0 ξ)
    calc G0⁻¹ * K ξ * Real.exp (-ex ξ θ0) ≤ G0⁻¹ * K ξ * Real.exp ‖θ0‖ := by gcongr
      _ = G0⁻¹ * Real.exp ‖θ0‖ * K ξ := by ring
  have hone : ∫ ξ, wt ξ * Real.exp (ex ξ θ0) ∂μ = 1 := by
    have e : ∀ ξ, wt ξ * Real.exp (ex ξ θ0) = G0⁻¹ * K ξ := fun ξ => by
      simp only [wt]
      rw [mul_assoc, ← Real.exp_add]
      simp
    simp only [e]
    rw [integral_const_mul]
    exact inv_mul_cancel₀ hpos.ne'
  have hintE : ∀ θ, Integrable (fun ξ => wt ξ * Real.exp (ex ξ θ)) μ := fun θ => by
    refine (hwti.const_mul (Real.exp ‖θ‖)).mono'
      (hwti.aestronglyMeasurable.mul (Real.measurable_exp.comp (hexm θ)).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun ξ => ?_)
    have h1 : Real.exp (ex ξ θ) ≤ Real.exp ‖θ‖ :=
      Real.exp_le_exp.mpr ((le_abs_self _).trans (hexb ξ θ))
    rw [Real.norm_of_nonneg (mul_nonneg (hwt0 ξ) (Real.exp_pos _).le), mul_comm]
    gcongr
    exact hwt0 ξ
  have hwtp : 0 < ∫ ξ, wt ξ ∂μ := by
    have h1 : (1 : ℝ) ≤ Real.exp ‖θ0‖ * ∫ ξ, wt ξ ∂μ := by
      rw [← hone, ← integral_const_mul]
      refine integral_mono (hintE θ0) (hwti.const_mul _) fun ξ => ?_
      have h2 : Real.exp (ex ξ θ0) ≤ Real.exp ‖θ0‖ :=
        Real.exp_le_exp.mpr ((le_abs_self _).trans (hexb ξ θ0))
      show wt ξ * Real.exp (ex ξ θ0) ≤ Real.exp ‖θ0‖ * wt ξ
      rw [mul_comm]
      gcongr
      exact hwt0 ξ
    by_contra hcon
    have h3 : ∫ ξ, wt ξ ∂μ ≤ 0 := not_lt.mp hcon
    have h4 : Real.exp ‖θ0‖ * ∫ ξ, wt ξ ∂μ ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos _).le h3
    linarith
  have hIpos : ∀ θ, 0 < ∫ ξ, wt ξ * Real.exp (ex ξ θ) ∂μ := by
    intro θ
    have h1 : Real.exp (-‖θ‖) * ∫ ξ, wt ξ ∂μ ≤ ∫ ξ, wt ξ * Real.exp (ex ξ θ) ∂μ := by
      rw [← integral_const_mul]
      refine integral_mono (hwti.const_mul _) (hintE θ) fun ξ => ?_
      have h2 : Real.exp (-‖θ‖) ≤ Real.exp (ex ξ θ) :=
        Real.exp_le_exp.mpr (neg_le_of_abs_le (hexb ξ θ))
      show Real.exp (-‖θ‖) * wt ξ ≤ wt ξ * Real.exp (ex ξ θ)
      rw [mul_comm]
      gcongr
      exact hwt0 ξ
    exact lt_of_lt_of_le (mul_pos (Real.exp_pos _) hwtp) h1
  obtain ⟨hsm, hbd⟩ := hL Ξ (StepBond ℓ n × Fin 4) (BondQuaternions ℓ n) μ wt (coordCoeff Cs N W b)
    (coordForm V) 1 hum hub hexb hwti hwt0 hwtp
  set g : BondQuaternions ℓ n → ℝ := logLaplaceTransform μ wt (coordCoeff Cs N W b) (coordForm V) with hg
  have hgexp : ∀ θ, ∫ ξ, wt ξ * Real.exp (ex ξ θ) ∂μ = Real.exp (g θ) := fun θ =>
    (Real.exp_log (hIpos θ)).symm
  have hg0 : g θ0 = 0 := by
    have : g θ0 = Real.log (∫ ξ, wt ξ * Real.exp (ex ξ θ0) ∂μ) := rfl
    rw [this, hone, Real.log_one]
  let f : BondQuaternions ℓ n → BondQuaternions ℓ n := lam • NormedSpace.exp
  have hf0 : f 0 = θ0 := by
    simp [f, NormedSpace.exp_zero, hθ0]
  have hform : ∀ σ : Fin k → ℝ, kernelProductMean ℓ x μ A W b (perturb c X σ V) =
      G0 * Real.exp (g (f (moveMap c X σ))) := by
    intro σ
    rw [← hgexp, ← integral_const_mul]
    unfold kernelProductMean
    refine integral_congr_ae (Filter.Eventually.of_forall fun ξ => ?_)
    show A ξ * _ = G0 * (G0⁻¹ * K ξ * Real.exp (-ex ξ θ0) * Real.exp (ex ξ (f (moveMap c X σ))))
    have hprod : ∏ c' : StepBond ℓ n,
        bondKernel ℓ x (W ξ) (readAtLevel (stepBlockFrame ℓ.side n) 1 (perturb c X σ V)) (b ξ) c' =
        (∏ c' : StepBond ℓ n, bondKernel ℓ x (W ξ) (readAtLevel (stepBlockFrame ℓ.side n) 1 V) (b ξ) c') *
          Real.exp (∑ c' : StepBond ℓ n, s * ((contourWeight (W ξ) (b ξ) c' * (invField V c' *
            NormedSpace.exp (-((moveAt c X σ (stepBondToTorus c') : imaginaryQuaternions) : ℍ[ℝ])))).re -
              (contourWeight (W ξ) (b ξ) c' * (invField V c' * 1)).re)) := by
      rw [Real.exp_sum, ← Finset.prod_mul_distrib]
      exact Finset.prod_congr rfl fun c' _ => bondKernel_perturb x (W ξ) (b ξ) V c X σ c'
    have hsum : ∑ c' : StepBond ℓ n, s * ((contourWeight (W ξ) (b ξ) c' * (invField V c' *
            NormedSpace.exp (-((moveAt c X σ (stepBondToTorus c') : imaginaryQuaternions) : ℍ[ℝ])))).re -
              (contourWeight (W ξ) (b ξ) c' * (invField V c' * 1)).re) =
        ex ξ (f (moveMap c X σ)) - ex ξ θ0 := by
      rw [hex, hex, ← mul_sub, ← Finset.sum_sub_distrib]
      have e1 : ∀ c' ∈ Cs, (contourWeight (W ξ) (b ξ) c' * (invField V c' * f (moveMap c X σ) c')).re -
          (contourWeight (W ξ) (b ξ) c' * (invField V c' * θ0 c')).re =
          lam * ((contourWeight (W ξ) (b ξ) c' * (invField V c' *
            NormedSpace.exp (-((moveAt c X σ (stepBondToTorus c') : imaginaryQuaternions) : ℍ[ℝ])))).re -
              (contourWeight (W ξ) (b ξ) c' * (invField V c' * 1)).re) := by
        intro c' _
        have e2 : f (moveMap c X σ) c' =
            lam • NormedSpace.exp (-((moveAt c X σ (stepBondToTorus c') : imaginaryQuaternions) : ℍ[ℝ])) := by
          show lam • (NormedSpace.exp (moveMap c X σ) : BondQuaternions ℓ n) c' = _
          rw [← moveMap_apply]
          congr 1
          exact exp_pi_eval _ c'
        have e3 : θ0 c' = lam • (1 : ℍ[ℝ]) := rfl
        rw [e2, e3]
        simp only [mul_smul_comm, Quaternion.re_smul, smul_eq_mul]
        ring
      rw [Finset.sum_congr rfl e1, ← Finset.mul_sum, ← Finset.mul_sum]
      have e4 : ∀ T : ℝ, 1 / N * (lam * T) = s * T := fun T => by
        simp only [hlam]
        field_simp
      rw [e4]
      congr 1
      refine (Finset.sum_subset (Finset.subset_univ Cs) fun c' _ hc' => ?_).symm
      have hS : moveAt c X σ (stepBondToTorus (ℓ := ℓ) c') = 0 := by
        simp only [moveAt]
        refine Finset.sum_eq_zero fun l _ => ?_
        rw [if_neg]
        intro hl
        exact hc' (Finset.mem_filter.mpr ⟨Finset.mem_univ _, l, hl⟩)
      simp [hS, NormedSpace.exp_zero]
    rw [hprod, hsum]
    have e5 : K ξ = A ξ * ∏ c' : StepBond ℓ n,
        bondKernel ℓ x (W ξ) (readAtLevel (stepBlockFrame ℓ.side n) 1 V) (b ξ) c' := rfl
    rw [e5, Real.exp_sub, Real.exp_neg]
    have e6 := (Real.exp_pos (ex ξ θ0)).ne'
    field_simp
  have hexp : ContDiff ℝ ∞ (NormedSpace.exp : BondQuaternions ℓ n → BondQuaternions ℓ n) :=
    AnalyticOnNhd.contDiff fun y _ => NormedSpace.exp_analytic (𝕂 := ℝ) y
  have hfs : ContDiff ℝ ∞ f := hexp.const_smul lam
  have hQ : ContDiff ℝ ∞ (g ∘ f) := hsm.comp hfs
  have hL' : ContDiff ℝ ∞ (moveMap (ℓ := ℓ) c X) := ContinuousLinearMap.contDiff (moveMap (ℓ := ℓ) c X)
  refine ⟨?_, fun hk1 hk3 hX => ?_⟩
  · have e : (fun σ : Fin k → ℝ => kernelProductMean ℓ x μ A W b (perturb c X σ V)) =
        fun σ => G0 * Real.exp ((g ∘ f) (moveMap c X σ)) := funext hform
    rw [e]
    exact contDiff_const.mul ((hQ.comp hL').exp)
  · have hlog : (fun σ : Fin k → ℝ => Real.log (kernelProductMean ℓ x μ A W b (perturb c X σ V))) =
        fun σ => Real.log G0 + ((g ∘ f) ∘ moveMap c X) σ := by
      funext σ
      rw [hform, Real.log_mul hpos.ne' (Real.exp_pos _).ne', Real.log_exp]
      rfl
    have hQbound : ‖iteratedFDeriv ℝ k (g ∘ f) 0‖ ≤ (k ! : ℝ) * 6 * lam ^ k := by
      refine norm_iteratedFDeriv_comp_le hsm hfs (by exact_mod_cast le_top) 0 (fun i hi => ?_)
        fun i hi hik => ?_
      · rw [hf0]
        obtain ⟨b1, b2, b3⟩ := hbd θ0
        have hi3 : i ≤ 3 := hi.trans hk3
        interval_cases i
        · rw [norm_iteratedFDeriv_zero, hg0]
          simp
        · linarith
        · linarith
        · exact b3
      · have e : iteratedFDeriv ℝ i f 0 = lam • iteratedFDeriv ℝ i NormedSpace.exp (0 : BondQuaternions ℓ n) :=
          iteratedFDeriv_const_smul_apply (hexp.contDiffAt.of_le (by exact_mod_cast le_top))
        rw [e]
        refine (ContinuousMultilinearMap.opNorm_smul_le lam _).trans ?_
        rw [Real.norm_of_nonneg (by linarith)]
        calc lam * _ ≤ lam * 1 := by
              gcongr
              exact norm_iteratedFDeriv_exp_zero_le hi
          _ = lam := mul_one _
          _ ≤ lam ^ i := le_self_pow₀ hlam1 (by omega)
    have hval : mixedDeriv (fun V' => Real.log (kernelProductMean ℓ x μ A W b V')) V c X =
        iteratedFDeriv ℝ k (g ∘ f) 0 (fun l => moveMap c X (Pi.single l 1)) := by
      unfold mixedDeriv
      obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
      have hc : fderiv ℝ (fun σ : Fin (j + 1) → ℝ => Real.log G0 + ((g ∘ f) ∘ moveMap c X) σ) =
          fderiv ℝ ((g ∘ f) ∘ moveMap c X) := by
        funext σ
        exact fderiv_const_add _
      have e1 : iteratedFDeriv ℝ (j + 1)
          (fun σ : Fin (j + 1) → ℝ => Real.log G0 + ((g ∘ f) ∘ moveMap c X) σ) =
          iteratedFDeriv ℝ (j + 1) ((g ∘ f) ∘ moveMap c X) := by
        funext σ
        rw [iteratedFDeriv_succ_eq_comp_right, iteratedFDeriv_succ_eq_comp_right, hc]
      rw [hlog, e1, (moveMap c X).iteratedFDeriv_comp_right hQ 0 (by exact_mod_cast le_top)]
      simp
    rw [hval, ← Real.norm_eq_abs]
    have h1 := (iteratedFDeriv ℝ k (g ∘ f) 0).le_opNorm (fun l => moveMap (ℓ := ℓ) c X (Pi.single l 1))
    have h2 : ∏ l, ‖moveMap (ℓ := ℓ) c X (Pi.single l 1)‖ ≤ 1 :=
      Finset.prod_le_one (fun _ _ => norm_nonneg _) fun l _ => norm_moveMap_single_le c X hX l
    have h3 : ‖iteratedFDeriv ℝ k (g ∘ f) 0 (fun l => moveMap (ℓ := ℓ) c X (Pi.single l 1))‖ ≤
        (k ! : ℝ) * 6 * lam ^ k :=
      h1.trans ((mul_le_of_le_one_right (norm_nonneg _) h2).trans hQbound)
    exact h3.trans (factorial_mul_pow_le hk1 hk3 hs0)
end YangMills.Construction
end
