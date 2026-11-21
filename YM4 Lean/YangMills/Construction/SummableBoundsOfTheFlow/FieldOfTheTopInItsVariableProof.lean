import YangMills.Construction.SummableBoundsOfTheFlow.BlockExpansionHasTheConditionsOfThirdOrderProof
import YangMills.Construction.SummableBoundsOfTheFlow.DerivativeOfATurnedDerivative
import YangMills.Construction.SummableBoundsOfTheFlow.FieldOfTheTopInItsVariable
import YangMills.Construction.SummableBoundsOfTheFlow.TopFieldDecays
import Mathlib
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
noncomputable section
open scoped Quaternion Topology
open YangMills.Construction.BlockAverages hiding bondSpread
open YangMills.Construction.ColdStepAtMirrorFrames
open YangMills.Construction.IteratedDerivative YangMills.Construction.Estimates
namespace YangMills.Construction.Interpolation
namespace CoordsSmoothness
instance finiteDimensionalImaginary : FiniteDimensional ℝ imaginaryQuaternions :=
  FiniteDimensional.finiteDimensional_submodule _
instance normedEnd : NormedAddCommGroup (imaginaryQuaternions →L[ℝ] imaginaryQuaternions) := inferInstance
instance normedSpaceEnd : NormedSpace ℝ (imaginaryQuaternions →L[ℝ] imaginaryQuaternions) := inferInstance
instance normedBilin :
    NormedAddCommGroup (imaginaryQuaternions →L[ℝ] imaginaryQuaternions →L[ℝ] imaginaryQuaternions) :=
  inferInstance
instance normedSpaceBilin :
    NormedSpace ℝ (imaginaryQuaternions →L[ℝ] imaginaryQuaternions →L[ℝ] imaginaryQuaternions) :=
  inferInstance
theorem norm_toImaginary (v : EuclideanSpace ℝ (Fin 3)) : ‖toImaginary v‖ = ‖v‖ := by apply _root_.YangMills.Construction.Interpolation.ExponentBoundSteps.norm_toImaginary <;> assumption
theorem norm_imaginaryCoords (w : imaginaryQuaternions) : ‖_root_.YangMills.Construction.Interpolation.imaginaryCoords w‖ = ‖w‖ := by apply _root_.YangMills.SharedProofs.p6124 <;> assumption
def toImaginaryCLM : BondVector →L[ℝ] imaginaryQuaternions :=
  LinearMap.toContinuousLinearMap
    { toFun := toImaginary
      map_add' := fun x y => Subtype.ext (by ext <;> first | rfl | (show (0 : ℝ) = 0 + 0; simp))
      map_smul' := fun r x => Subtype.ext (by ext <;> first | rfl | (show (0 : ℝ) = r * 0; simp)) }
theorem toImaginaryCLM_apply (v : BondVector) : toImaginaryCLM v = toImaginary v := rfl
def imaginaryCoordsCLM : imaginaryQuaternions →L[ℝ] BondVector :=
  LinearMap.toContinuousLinearMap
    { toFun := _root_.YangMills.Construction.Interpolation.imaginaryCoords
      map_add' := fun x y => by
        ext i
        fin_cases i <;> simp [_root_.YangMills.Construction.Interpolation.imaginaryCoords]
      map_smul' := fun r x => by
        ext i
        fin_cases i <;> simp [_root_.YangMills.Construction.Interpolation.imaginaryCoords] }
theorem imaginaryCoordsCLM_apply (w : imaginaryQuaternions) : imaginaryCoordsCLM w = _root_.YangMills.Construction.Interpolation.imaginaryCoords w := rfl
section Slices
variable {E W : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup W] [NormedSpace ℝ W] {k : ℕ}
def unitDirections (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (k : ℕ) : List (E × (Fin k → ℝ)) :=
  (List.ofFn fun l : Fin k => (Pi.single l (1 : ℝ) : Fin k → ℝ)).map (ContinuousLinearMap.inr ℝ E (Fin k → ℝ))
theorem length_unitDirections : (unitDirections E k).length = k := by simp [unitDirections]
theorem iteratedFDeriv_slice_eq_derivAlong (hL : DerivAlongRulesHold) (Q : E × (Fin k → ℝ) → W) (v : E)
    (hQ : ContDiffAt ℝ (k : WithTop ℕ∞) Q (v, 0)) :
    iteratedFDeriv ℝ k (fun τ : Fin k → ℝ => Q (v, τ)) 0 (fun l => Pi.single l 1) =
      derivAlong Q (unitDirections E k) (v, 0) := by
  have hc : ContDiffAt ℝ (k : WithTop ℕ∞) (fun τ : Fin k → ℝ => Q (v, τ)) 0 :=
    ContDiffAt.comp (g := Q) (f := fun τ : Fin k → ℝ => (v, τ)) (0 : Fin k → ℝ) hQ
      (contDiff_const.prodMk contDiff_id).contDiffAt
  rw [(hL.1 _ W).iteratedFDeriv_eq _ _ _ _ hc]
  have e := hL.2 (E × (Fin k → ℝ)) (Fin k → ℝ) W Q (ContinuousLinearMap.inr ℝ _ _) (v, 0) 0
    (List.ofFn fun l : Fin k => Pi.single l 1) (by simpa using hQ)
  have e1 : (fun t' : Fin k → ℝ => Q ((v, 0) + ContinuousLinearMap.inr ℝ E (Fin k → ℝ) t')) =
      fun τ => Q (v, τ) := by
    funext t'
    simp
  rw [e1] at e
  rw [e]
  simp only [map_zero, add_zero]
  rfl
theorem slice_contDiffAt_and_fderiv (hL : DerivAlongRulesHold) (Q : E × (Fin k → ℝ) → W) (v₀ : E)
    (hQ : ∀ᶠ v in 𝓝 v₀, ContDiffAt ℝ ((k + 1 : ℕ) : WithTop ℕ∞) Q (v, 0)) :
    ContDiffAt ℝ ((1 : ℕ) : WithTop ℕ∞)
      (fun v => iteratedFDeriv ℝ k (fun τ : Fin k → ℝ => Q (v, τ)) 0 (fun l => Pi.single l 1)) v₀ ∧
    ∀ e : E, fderiv ℝ (fun v => iteratedFDeriv ℝ k (fun τ : Fin k → ℝ => Q (v, τ)) 0 (fun l => Pi.single l 1)) v₀ e =
      iteratedFDeriv ℝ k (fun τ : Fin k → ℝ => fderiv ℝ (fun v' => Q (v', τ)) v₀ e) 0 (fun l => Pi.single l 1) := by
  have R := hL.1 (E × (Fin k → ℝ)) W
  have h0 := hQ.self_of_nhds
  have ev : (fun v => iteratedFDeriv ℝ k (fun τ : Fin k → ℝ => Q (v, τ)) 0 (fun l => Pi.single l 1)) =ᶠ[𝓝 v₀]
      fun v => derivAlong Q (unitDirections E k) (v, 0) := by
    filter_upwards [hQ] with v hv
    exact iteratedFDeriv_slice_eq_derivAlong hL Q v (hv.of_le (by exact_mod_cast Nat.le_succ k))
  have hA : ContDiffAt ℝ ((1 : ℕ) : WithTop ℕ∞) (derivAlong Q (unitDirections E k)) (v₀, 0) :=
    R.contDiffAt _ _ 1 _ (by rw [length_unitDirections, add_comm]; exact h0)
  have hin : ContDiffAt ℝ ((1 : ℕ) : WithTop ℕ∞) (fun v : E => ((v, 0) : E × (Fin k → ℝ))) v₀ :=
    (contDiff_id.prodMk contDiff_const).contDiffAt
  have hc : ContDiffAt ℝ ((1 : ℕ) : WithTop ℕ∞) (fun v => derivAlong Q (unitDirections E k) (v, 0)) v₀ :=
    ContDiffAt.comp (g := derivAlong Q (unitDirections E k)) (f := fun v => ((v, 0) : E × (Fin k → ℝ))) v₀ hA hin
  refine ⟨hc.congr_of_eventuallyEq ev, fun e => ?_⟩
  rw [ev.fderiv_eq]
  have hd : DifferentiableAt ℝ (derivAlong Q (unitDirections E k)) (v₀, 0) := hA.differentiableAt (by simp)
  have h1 := (HasFDerivAt.comp (g := derivAlong Q (unitDirections E k)) (f := fun v => ((v, 0) : E × (Fin k → ℝ)))
    v₀ hd.hasFDerivAt (hasFDerivAt_prodMk_left v₀ 0)).fderiv
  have h2 : fderiv ℝ (fun v => derivAlong Q (unitDirections E k) (v, 0)) v₀ e =
      derivAlong Q ((e, 0) :: unitDirections E k) (v₀, 0) := by
    change fderiv ℝ (derivAlong Q (unitDirections E k) ∘ fun v => ((v, 0) : E × (Fin k → ℝ))) v₀ e = _
    rw [h1]
    simp [derivAlong]
  rw [h2]
  have hev := h0.eventually (by simp)
  have hcT : Filter.Tendsto (fun τ : Fin k → ℝ => ((v₀, τ) : E × (Fin k → ℝ))) (𝓝 0) (𝓝 (v₀, 0)) :=
    (by fun_prop : Continuous fun τ : Fin k → ℝ => ((v₀, τ) : E × (Fin k → ℝ))).tendsto 0
  have e1 : (fun τ : Fin k → ℝ => fderiv ℝ (fun v' => Q (v', τ)) v₀ e) =ᶠ[𝓝 0]
      fun τ => derivAlong Q [(e, 0)] (v₀, τ) := by
    filter_upwards [hcT.eventually hev] with τ hτ
    have hd' : DifferentiableAt ℝ Q (v₀, τ) := hτ.differentiableAt (by simp)
    have := (HasFDerivAt.comp (g := Q) (f := fun v' => ((v', τ) : E × (Fin k → ℝ))) v₀ hd'.hasFDerivAt
      (hasFDerivAt_prodMk_left v₀ τ)).fderiv
    change fderiv ℝ (Q ∘ fun v' => ((v', τ) : E × (Fin k → ℝ))) v₀ e = _
    rw [this]
    simp [derivAlong]
  have hH : ContDiffAt ℝ (k : WithTop ℕ∞) (derivAlong Q [((e, 0) : E × (Fin k → ℝ))]) (v₀, 0) :=
    R.contDiffAt _ _ k _ (by simpa using h0)
  rw [(Filter.EventuallyEq.iteratedFDeriv ℝ e1 k).self_of_nhds, iteratedFDeriv_slice_eq_derivAlong hL _ v₀ hH,
    ← R.append]
  exact R.perm Q _ _ _ (List.perm_append_singleton _ _).symm
    (by rw [List.length_cons, length_unitDirections]; exact h0)
theorem iteratedFDeriv_imaginaryCoords (g : (Fin k → ℝ) → imaginaryQuaternions)
    (hg : ContDiffAt ℝ (k : WithTop ℕ∞) g 0) (m : Fin k → Fin k → ℝ) :
    iteratedFDeriv ℝ k (fun τ => _root_.YangMills.Construction.Interpolation.imaginaryCoords (g τ)) 0 m = _root_.YangMills.Construction.Interpolation.imaginaryCoords (iteratedFDeriv ℝ k g 0 m) := by
  have hc := ContinuousLinearMap.iteratedFDeriv_comp_left imaginaryCoordsCLM hg (i := k) le_rfl
  exact show (iteratedFDeriv ℝ k (imaginaryCoordsCLM ∘ g) 0) m =
      imaginaryCoordsCLM (iteratedFDeriv ℝ k g 0 m) from by
    rw [hc]
    rfl
end Slices
section Shift
variable {k : ℕ}
def shiftedField (Th : imaginaryQuaternions → imaginaryQuaternions →L[ℝ] imaginaryQuaternions)
    (Ψ : (Fin k → ℝ) → imaginaryQuaternions) (X : imaginaryQuaternions) (p : BondVector × (Fin k → ℝ)) :
    imaginaryQuaternions :=
  Th (Ψ p.2 + toImaginaryCLM p.1) X
theorem shiftedField_contDiffAt {Th : imaginaryQuaternions → imaginaryQuaternions →L[ℝ] imaginaryQuaternions}
    {Ψ : (Fin k → ℝ) → imaginaryQuaternions} (X : imaginaryQuaternions)
    (hTh : ∀ w : imaginaryQuaternions, ‖w‖ < Real.pi → ContDiffAt ℝ ((3 : ℕ) : WithTop ℕ∞) Th w)
    (hΨ : ContDiffAt ℝ ((3 : ℕ) : WithTop ℕ∞) Ψ 0) (v : BondVector) (hv : ‖Ψ 0 + toImaginaryCLM v‖ < Real.pi) :
    ContDiffAt ℝ ((3 : ℕ) : WithTop ℕ∞) (shiftedField Th Ψ X) (v, 0) := by
  have h1 : ContDiffAt ℝ ((3 : ℕ) : WithTop ℕ∞)
      (fun p : BondVector × (Fin k → ℝ) => Ψ p.2 + toImaginaryCLM p.1) (v, 0) :=
    (ContDiffAt.comp (g := Ψ) (f := Prod.snd) (v, 0) hΨ contDiffAt_snd).add
      (toImaginaryCLM.contDiff.contDiffAt.comp _ contDiffAt_fst)
  exact (ContDiffAt.comp (g := Th) (f := fun p : BondVector × (Fin k → ℝ) => Ψ p.2 + toImaginaryCLM p.1) (v, 0)
    (hTh _ hv) h1).clm_apply contDiffAt_const
theorem shiftedField_jets (hL : DerivAlongRulesHold)
    {Th : imaginaryQuaternions → imaginaryQuaternions →L[ℝ] imaginaryQuaternions}
    {Ψ : (Fin k → ℝ) → imaginaryQuaternions} (X : imaginaryQuaternions)
    (hTh : ∀ w : imaginaryQuaternions, ‖w‖ < Real.pi → ContDiffAt ℝ ((3 : ℕ) : WithTop ℕ∞) Th w)
    (hΨ : ContDiffAt ℝ ((3 : ℕ) : WithTop ℕ∞) Ψ 0) (v₀ : BondVector) (hv : ‖Ψ 0 + toImaginaryCLM v₀‖ < Real.pi)
    (hk : k ≤ 2) :
    ContDiffAt ℝ ((1 : ℕ) : WithTop ℕ∞)
      (fun v => iteratedFDeriv ℝ k (fun τ : Fin k → ℝ => shiftedField Th Ψ X (v, τ)) 0 (fun l => Pi.single l 1)) v₀ ∧
    ∀ e : BondVector, fderiv ℝ (fun v => iteratedFDeriv ℝ k (fun τ : Fin k → ℝ => shiftedField Th Ψ X (v, τ)) 0
        (fun l => Pi.single l 1)) v₀ e =
      iteratedFDeriv ℝ k (fun τ : Fin k → ℝ => fderiv ℝ Th (Ψ τ + toImaginaryCLM v₀) (toImaginaryCLM e) X) 0
        (fun l => Pi.single l 1) := by
  have hcont : ContinuousAt (fun v => ‖Ψ 0 + toImaginaryCLM v‖) v₀ := by fun_prop
  have hnear : ∀ᶠ v in 𝓝 v₀, ContDiffAt ℝ ((k + 1 : ℕ) : WithTop ℕ∞) (shiftedField Th Ψ X) (v, 0) := by
    filter_upwards [hcont.eventually (gt_mem_nhds hv)] with v hv'
    exact (shiftedField_contDiffAt X hTh hΨ v hv').of_le (by exact_mod_cast (show k + 1 ≤ 3 by omega))
  obtain ⟨h1, h2⟩ := slice_contDiffAt_and_fderiv hL (shiftedField Th Ψ X) v₀ hnear
  refine ⟨h1, fun e => ?_⟩
  rw [h2]
  have hcΨ : ContinuousAt (fun τ => ‖Ψ τ + toImaginaryCLM v₀‖) 0 := by
    have := hΨ.continuousAt
    fun_prop
  have e1 : (fun τ : Fin k → ℝ => fderiv ℝ (fun v' => shiftedField Th Ψ X (v', τ)) v₀ e) =ᶠ[𝓝 0]
      fun τ => fderiv ℝ Th (Ψ τ + toImaginaryCLM v₀) (toImaginaryCLM e) X := by
    filter_upwards [hcΨ.eventually (gt_mem_nhds hv)] with τ hτ
    have hd : DifferentiableAt ℝ Th (Ψ τ + toImaginaryCLM v₀) := (hTh _ hτ).differentiableAt (by simp)
    have hpt : HasFDerivAt (fun v' => Ψ τ + toImaginaryCLM v') toImaginaryCLM v₀ :=
      toImaginaryCLM.hasFDerivAt.const_add _
    have hA : HasFDerivAt (fun v' => Th (Ψ τ + toImaginaryCLM v'))
        ((fderiv ℝ Th (Ψ τ + toImaginaryCLM v₀)).comp toImaginaryCLM) v₀ :=
      HasFDerivAt.comp (g := Th) (f := fun v' => Ψ τ + toImaginaryCLM v') v₀ hd.hasFDerivAt hpt
    have h3 := hA.clm_apply (hasFDerivAt_const X v₀)
    change fderiv ℝ (fun v' => Th (Ψ τ + toImaginaryCLM v') X) v₀ e = _
    rw [h3.fderiv]
    simp
  exact (Filter.EventuallyEq.iteratedFDeriv ℝ e1 k).self_of_nhds ▸ rfl
end Shift
section Derived
theorem fderiv_apply_contDiffAt {Th : imaginaryQuaternions → imaginaryQuaternions →L[ℝ] imaginaryQuaternions}
    (e : imaginaryQuaternions)
    (hTh : ∀ w : imaginaryQuaternions, ‖w‖ < Real.pi → ContDiffAt ℝ ((3 : ℕ) : WithTop ℕ∞) Th w)
    (w : imaginaryQuaternions) (hw : ‖w‖ < Real.pi) :
    ContDiffAt ℝ ((2 : ℕ) : WithTop ℕ∞) (fun w' => fderiv ℝ Th w' e) w :=
  ((hTh w hw).fderiv_right (m := 2) (by norm_num)).clm_apply contDiffAt_const
theorem norm_iteratedFDeriv_fderiv_apply_le
    {Th : imaginaryQuaternions → imaginaryQuaternions →L[ℝ] imaginaryQuaternions} {CT : ℝ}
    (e : imaginaryQuaternions) (he : ‖e‖ = 1)
    (hTh : ∀ w : imaginaryQuaternions, ‖w‖ < Real.pi → ContDiffAt ℝ ((3 : ℕ) : WithTop ℕ∞) Th w)
    (hb : ∀ (w : imaginaryQuaternions) (j : ℕ), ‖w‖ ≤ 1 → j ≤ 3 → ‖iteratedFDeriv ℝ j Th w‖ ≤ CT)
    (w : imaginaryQuaternions) (j : ℕ) (hw : ‖w‖ ≤ 1) (hj : j ≤ 2) :
    ‖iteratedFDeriv ℝ j (fun w' => fderiv ℝ Th w' e) w‖ ≤ CT := by
  have hπ : ‖w‖ < Real.pi := lt_of_le_of_lt hw (by linarith [Real.pi_gt_three])
  set ev : (imaginaryQuaternions →L[ℝ] imaginaryQuaternions →L[ℝ] imaginaryQuaternions) →L[ℝ]
      (imaginaryQuaternions →L[ℝ] imaginaryQuaternions) :=
    ContinuousLinearMap.apply ℝ (imaginaryQuaternions →L[ℝ] imaginaryQuaternions) e with hev
  have hD : ContDiffAt ℝ (j : WithTop ℕ∞) (fderiv ℝ Th) w :=
    ((hTh w hπ).fderiv_right (m := 2) (by norm_num)).of_le (by exact_mod_cast hj)
  have hc := ContinuousLinearMap.iteratedFDeriv_comp_left ev hD (i := j) le_rfl
  have e1 : (fun w' => fderiv ℝ Th w' e) = ev ∘ fderiv ℝ Th := rfl
  rw [e1, hc]
  refine (ContinuousLinearMap.norm_compContinuousMultilinearMap_le _ _).trans ?_
  have hn : ‖ev‖ ≤ 1 := by
    refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun T => ?_
    have := T.le_opNorm e
    simpa [hev, he] using this
  have h2 : ‖iteratedFDeriv ℝ j (fderiv ℝ Th) w‖ ≤ CT := by
    rw [norm_iteratedFDeriv_fderiv]
    exact hb w (j + 1) hw (by omega)
  calc _ ≤ 1 * ‖iteratedFDeriv ℝ j (fderiv ℝ Th) w‖ := mul_le_mul_of_nonneg_right hn (norm_nonneg _)
    _ ≤ CT := by linarith
end Derived
end CoordsSmoothness
open CoordsSmoothness in
set_option maxHeartbeats 1600000 in
theorem topVariationCoordsSmooth_of_bounds (hL : DerivAlongRulesHold) (hT : topVariationFieldDecayStatement)
    (hD : TranslatedDerivativeBound) : TopVariationCoordsSmooth := by
  classical
  obtain ⟨M, hM0, hM⟩ := hT
  obtain ⟨M₂, hM₂0, hM₂⟩ := hD
  refine ⟨M, hM0, ?_⟩
  intro F s a ρA r CT m V Th K b c X v hper hr hK hCT hThs hThb hAn hdec hvb hX
  set f := interpolatedFrame s a ρA m b with hf
  set z : F.Cell := enclosingCell b.1 with hz
  have hπ : ∀ w : imaginaryQuaternions, ‖w‖ ≤ 1 → ‖w‖ < Real.pi := fun w hw =>
    lt_of_le_of_lt hw (by linarith [Real.pi_gt_three])
  have hTh2 : ∀ w : imaginaryQuaternions, ‖w‖ ≤ 1 → ContDiffAt ℝ ((2 : ℕ) : WithTop ℕ∞) Th w := fun w hw =>
    (hThs w (hπ w hw)).of_le (by norm_num)
  have hThb2 : ∀ (w : imaginaryQuaternions) (j : ℕ), ‖w‖ ≤ 1 → j ≤ 2 → ‖iteratedFDeriv ℝ j Th w‖ ≤ CT :=
    fun w j hw hj => hThb w j hw (by omega)
  have h3 : ∀ (q : ℕ) (c'' : Fin q → F.Site F.top × Fin 4) (X'' : Fin q → imaginaryQuaternions),
      ContDiffAt ℝ ((3 : ℕ) : WithTop ℕ∞)
        (fun τ : Fin q → ℝ => f (leftTranslate (bondSpread c'' X'' τ) V)) 0 :=
    fun q c'' X'' => (hAn q c'' X'').contDiffAt
  have hu : ‖f V + toImaginary v‖ ≤ 1 := by
    have := norm_add_le (f V) (toImaginary v)
    rw [norm_toImaginary] at this
    linarith
  have hK1 := hK 1
  have hK2 := hK 2
  have hK3 := hK 3
  have hKs : 0 ≤ K 1 + K 2 + K 3 := by positivity
  have hB0 : 0 ≤ M * (K 1 + K 2 + K 3) := mul_nonneg hM0 hKs
  have hC0 : 0 ≤ CT * (1 + K 1 + K 1 ^ 2 + K 2) := by positivity
  have hA : ∀ (k : ℕ) (c' : Fin k → F.Site F.top × Fin 4) (X' : Fin k → imaginaryQuaternions), k ≤ 2 →
      AreUnitVectors X' →
      ContDiffAt ℝ (k : WithTop ℕ∞) (fun τ : Fin k → ℝ => bondDeriv f (leftTranslate (bondSpread c' X' τ) V)
        (fun _ : Fin 1 => c) (fun _ => X)) 0 := by
    intro k c' X' hk hX'
    refine (hM₂ F F.top k f V c X c' X' (fun i bs => K i * Real.exp (-(r * bondListDistance z bs)))
      (K 1 + K 2 + K 3) hk hper hX hX' hKs h3 (fun i bs Xs h1 _ hXs => hdec i bs Xs h1 hXs)
      (fun i bs h1 h3' _ => ?_)).1
    have hKi : K i ≤ K 1 + K 2 + K 3 := by
      interval_cases i <;> linarith
    have hex : Real.exp (-(r * (bondListDistance z bs : ℝ))) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      have : (0 : ℝ) ≤ bondListDistance z bs := Nat.cast_nonneg _
      nlinarith
    have hKi0 := hK i
    calc K i * Real.exp (-(r * (bondListDistance z bs : ℝ))) ≤ K i * 1 := mul_le_mul_of_nonneg_left hex hKi0
      _ ≤ _ := by linarith
  refine ⟨fun k c' X' hk hX' => ?_, ?_⟩
  · set Ψ : (Fin k → ℝ) → imaginaryQuaternions := fun τ => f (leftTranslate (bondSpread c' X' τ) V) with hΨd
    have hΨ : ContDiffAt ℝ ((3 : ℕ) : WithTop ℕ∞) Ψ 0 := h3 k c' X'
    have hΨ0 : Ψ 0 = f V := by
      have : leftTranslate (bondSpread c' X' (0 : Fin k → ℝ)) V = V := by
        funext y i
        have e0 : expUnit (0 : imaginaryQuaternions) = 1 := by
          apply Subtype.ext
          simp [expUnit]
        simp [leftTranslate, bondSpread, e0]
      simp only [hΨd, this]
    set A : (Fin k → ℝ) → imaginaryQuaternions := fun τ =>
      bondDeriv f (leftTranslate (bondSpread c' X' τ) V) (fun _ : Fin 1 => c) (fun _ => X) with hAd
    have hAk := hA k c' X' hk hX'
    set Ed : ℝ := Real.exp (-(r * bondListDistance z (Fin.cons c c' : Fin (k + 1) → F.Site F.top × Fin 4)))
      with hEd
    have hE0 : 0 < Ed := Real.exp_pos _
    have hbv := hM F s a ρA r CT m V Th K b c X (toImaginary v) k c' X' hper hr hK hCT hTh2 hThb2 hAn hdec hu hX
      hk hX'
    by_cases hcr : IsCrossingBond b ∧ (enclosingCell b.1, b.2) = c
    · have eT : ∀ (The : imaginaryQuaternions → imaginaryQuaternions →L[ℝ] imaginaryQuaternions)
          (u : imaginaryQuaternions),
          (fun τ : Fin k → ℝ => topVariationField (fun w X' => The w X') s a ρA m c X b u
            (leftTranslate (bondSpread c' X' τ) V)) = fun τ => A τ + The (Ψ τ + u) X := by
        intro The u
        funext τ
        simp only [topVariationField, if_pos hcr]
        rfl
      have hpi : ∀ v' : BondVector, ‖Ψ 0 + toImaginaryCLM v'‖ < Real.pi → ContDiffAt ℝ (k : WithTop ℕ∞)
          (fun τ : Fin k → ℝ => shiftedField Th Ψ X (v', τ)) 0 := by
        intro v' hv'
        have h1 := shiftedField_contDiffAt X hThs hΨ v' hv'
        exact (ContDiffAt.comp (g := shiftedField Th Ψ X)
          (f := fun τ : Fin k → ℝ => ((v', τ) : BondVector × (Fin k → ℝ)))
          (0 : Fin k → ℝ) h1 (contDiff_const.prodMk contDiff_id).contDiffAt).of_le
          (by exact_mod_cast (show k ≤ 3 by omega))
      have hv0 : ‖Ψ 0 + toImaginaryCLM v‖ < Real.pi := by
        rw [hΨ0]
        exact hπ _ hu
      have eJ : ∀ v' : BondVector, ‖Ψ 0 + toImaginaryCLM v'‖ < Real.pi →
          bondDeriv (fun V' => topVariationCoords Th s a ρA m c X b V' v') V c' X' =
            _root_.YangMills.Construction.Interpolation.imaginaryCoords (iteratedFDeriv ℝ k A 0 (fun l => Pi.single l 1) +
              iteratedFDeriv ℝ k (fun τ : Fin k → ℝ => shiftedField Th Ψ X (v', τ)) 0 (fun l => Pi.single l 1)) := by
        intro v' hv'
        have e1 : (fun τ : Fin k → ℝ =>
            topVariationCoords Th s a ρA m c X b (leftTranslate (bondSpread c' X' τ) V) v') =
            fun τ => _root_.YangMills.Construction.Interpolation.imaginaryCoords (A τ + shiftedField Th Ψ X (v', τ)) := by
          funext τ
          have := congrFun (eT Th (toImaginary v')) τ
          exact congrArg imaginaryCoords this
        change iteratedFDeriv ℝ k (fun τ : Fin k → ℝ =>
          topVariationCoords Th s a ρA m c X b (leftTranslate (bondSpread c' X' τ) V) v') 0
          (fun l => Pi.single l 1) = _
        rw [e1, iteratedFDeriv_imaginaryCoords _ (hAk.add (hpi v' hv'))]
        congr 1
        exact DFunLike.congr_fun (iteratedFDeriv_add_apply hAk (hpi v' hv')) _
      obtain ⟨hj1, hj2⟩ := shiftedField_jets hL X hThs hΨ v hv0 hk
      have hnear : ∀ᶠ v' in 𝓝 v, ‖Ψ 0 + toImaginaryCLM v'‖ < Real.pi := by
        have hcont : ContinuousAt (fun v' => ‖Ψ 0 + toImaginaryCLM v'‖) v := by fun_prop
        exact hcont.eventually (gt_mem_nhds hv0)
      have evJ : (fun v' => bondDeriv (fun V' => topVariationCoords Th s a ρA m c X b V' v') V c' X') =ᶠ[𝓝 v]
          fun v' => imaginaryCoordsCLM (iteratedFDeriv ℝ k A 0 (fun l => Pi.single l 1) +
            iteratedFDeriv ℝ k (fun τ : Fin k → ℝ => shiftedField Th Ψ X (v', τ)) 0 (fun l => Pi.single l 1)) := by
        filter_upwards [hnear] with v' hv'
        exact eJ v' hv'
      have hG1 : ContDiffAt ℝ ((1 : ℕ) : WithTop ℕ∞) (fun v' =>
          imaginaryCoordsCLM (iteratedFDeriv ℝ k A 0 (fun l => Pi.single l 1) +
            iteratedFDeriv ℝ k (fun τ : Fin k → ℝ => shiftedField Th Ψ X (v', τ)) 0 (fun l => Pi.single l 1))) v :=
        imaginaryCoordsCLM.contDiff.contDiffAt.comp v (contDiffAt_const.add hj1)
      refine ⟨?_, hG1.congr_of_eventuallyEq evJ, ?_, ?_⟩
      · have e1 : (fun τ : Fin k → ℝ =>
            topVariationCoords Th s a ρA m c X b (leftTranslate (bondSpread c' X' τ) V) v) =
            fun τ => imaginaryCoordsCLM (A τ + shiftedField Th Ψ X (v, τ)) := by
          funext τ
          have := congrFun (eT Th (toImaginary v)) τ
          exact congrArg imaginaryCoords this
        rw [e1]
        exact imaginaryCoordsCLM.contDiff.contDiffAt.comp (0 : Fin k → ℝ) (hAk.add (hpi v hv0))
      · have hvt : bondDeriv (fun V' => topVariationCoords Th s a ρA m c X b V' v) V c' X' =
            imaginaryCoords (bondDeriv (topVariationField (fun w X' => Th w X') s a ρA m c X b (toImaginary v))
              V c' X') := by
          change iteratedFDeriv ℝ k (fun τ : Fin k → ℝ => _root_.YangMills.Construction.Interpolation.imaginaryCoords (topVariationField (fun w X' => Th w X')
            s a ρA m c X b (toImaginary v) (leftTranslate (bondSpread c' X' τ) V))) 0 (fun l => Pi.single l 1) = _
          rw [iteratedFDeriv_imaginaryCoords]
          · rfl
          · rw [eT Th (toImaginary v)]
            exact hAk.add (hpi v hv0)
        rw [hvt, norm_imaginaryCoords]
        refine hbv.trans (mul_le_mul_of_nonneg_right ?_ hE0.le)
        unfold variationFieldConstant
        nlinarith
      · rw [evJ.fderiv_eq]
        refine ContinuousLinearMap.opNorm_le_of_unit_norm (mul_nonneg ?_ hE0.le) fun e he => ?_
        · unfold variationFieldConstant
          nlinarith
        · have hd1 : DifferentiableAt ℝ (fun v' => iteratedFDeriv ℝ k
              (fun τ : Fin k → ℝ => shiftedField Th Ψ X (v', τ)) 0 (fun l => Pi.single l 1)) v :=
            hj1.differentiableAt (by simp)
          have hd2 : HasFDerivAt (fun v' => iteratedFDeriv ℝ k A 0 (fun l => Pi.single l 1) +
              iteratedFDeriv ℝ k (fun τ : Fin k → ℝ => shiftedField Th Ψ X (v', τ)) 0 (fun l => Pi.single l 1))
              (fderiv ℝ (fun v' => iteratedFDeriv ℝ k (fun τ : Fin k → ℝ => shiftedField Th Ψ X (v', τ)) 0
                (fun l => Pi.single l 1)) v) v := hd1.hasFDerivAt.const_add _
          have hd3 := (imaginaryCoordsCLM.hasFDerivAt.comp v hd2).fderiv
          change ‖fderiv ℝ (imaginaryCoordsCLM ∘ fun v' => iteratedFDeriv ℝ k A 0 (fun l => Pi.single l 1) +
              iteratedFDeriv ℝ k (fun τ : Fin k → ℝ => shiftedField Th Ψ X (v', τ)) 0 (fun l => Pi.single l 1))
              v e‖ ≤ _
          rw [hd3]
          simp only [ContinuousLinearMap.comp_apply, imaginaryCoordsCLM_apply, norm_imaginaryCoords]
          rw [hj2 e]
          set u' : imaginaryQuaternions := toImaginaryCLM e with hu'
          have hu'1 : ‖u'‖ = 1 := by
            rw [hu', toImaginaryCLM_apply, norm_toImaginary, he]
          set The : imaginaryQuaternions → imaginaryQuaternions →L[ℝ] imaginaryQuaternions :=
            fun w => fderiv ℝ Th w u' with hThe
          have hThe2 : ∀ w : imaginaryQuaternions, ‖w‖ ≤ 1 → ContDiffAt ℝ ((2 : ℕ) : WithTop ℕ∞) The w :=
            fun w hw => fderiv_apply_contDiffAt u' hThs w (hπ w hw)
          have hTheb : ∀ (w : imaginaryQuaternions) (j : ℕ), ‖w‖ ≤ 1 → j ≤ 2 →
              ‖iteratedFDeriv ℝ j The w‖ ≤ CT := fun w j hw hj =>
            norm_iteratedFDeriv_fderiv_apply_le u' hu'1 hThs hThb w j hw hj
          have hb1 := hM F s a ρA r CT m V The K b c X (toImaginary v) k c' X' hper hr hK hCT hThe2 hTheb hAn hdec
            hu hX hk hX'
          have hb2 := hM F s a ρA r 0 m V (fun _ => 0) K b c X (toImaginary v) k c' X' hper hr hK le_rfl
            (fun _ _ => contDiffAt_const) (fun w j _ _ => by
              rcases j with _ | j
              · simp
              · rw [iteratedFDeriv_succ_const]
                simp) hAn hdec hu hX hk hX'
          have hYs : ContDiffAt ℝ (k : WithTop ℕ∞) (fun τ : Fin k → ℝ => The (Ψ τ + toImaginaryCLM v) X) 0 := by
            have h1 : ContDiffAt ℝ ((2 : ℕ) : WithTop ℕ∞) (fun τ : Fin k → ℝ => Ψ τ + toImaginaryCLM v) 0 :=
              (hΨ.of_le (by norm_num)).add contDiffAt_const
            have h2 := (ContDiffAt.comp (g := The) (f := fun τ : Fin k → ℝ => Ψ τ + toImaginaryCLM v)
              (0 : Fin k → ℝ) (hThe2 _ (by simpa [hΨ0, toImaginaryCLM_apply] using hu)) h1).clm_apply
              (contDiffAt_const (c := X))
            exact h2.of_le (by exact_mod_cast hk)
          have e1 : bondDeriv (topVariationField (fun w X' => The w X') s a ρA m c X b (toImaginary v)) V c' X' =
              iteratedFDeriv ℝ k A 0 (fun l => Pi.single l 1) +
                iteratedFDeriv ℝ k (fun τ : Fin k → ℝ => The (Ψ τ + toImaginaryCLM v) X) 0
                  (fun l => Pi.single l 1) := by
            change iteratedFDeriv ℝ k (fun τ : Fin k → ℝ => topVariationField (fun w X' => The w X')
              s a ρA m c X b (toImaginary v) (leftTranslate (bondSpread c' X' τ) V)) 0 (fun l => Pi.single l 1) = _
            rw [eT The (toImaginary v)]
            exact DFunLike.congr_fun (iteratedFDeriv_add_apply hAk hYs) _
          have e2 : bondDeriv (topVariationField (fun w X' => (0 : imaginaryQuaternions →L[ℝ] imaginaryQuaternions) X')
              s a ρA m c X b (toImaginary v)) V c' X' = iteratedFDeriv ℝ k A 0 (fun l => Pi.single l 1) := by
            change iteratedFDeriv ℝ k (fun τ : Fin k → ℝ => topVariationField
              (fun w X' => (0 : imaginaryQuaternions →L[ℝ] imaginaryQuaternions) X') s a ρA m c X b (toImaginary v)
              (leftTranslate (bondSpread c' X' τ) V)) 0 (fun l => Pi.single l 1) = _
            congr 2
            funext τ
            simp only [topVariationField, if_pos hcr]
            simp
            rfl
          have e3 : iteratedFDeriv ℝ k (fun τ : Fin k → ℝ => fderiv ℝ Th (Ψ τ + toImaginaryCLM v) u' X) 0
              (fun l => Pi.single l 1) =
              bondDeriv (topVariationField (fun w X' => The w X') s a ρA m c X b (toImaginary v)) V c' X' -
                bondDeriv (topVariationField (fun w X' => (0 : imaginaryQuaternions →L[ℝ] imaginaryQuaternions) X')
                  s a ρA m c X b (toImaginary v)) V c' X' := by
            rw [e1, e2]
            simp [hThe]
          rw [e3]
          refine (norm_sub_le _ _).trans ((add_le_add hb1 hb2).trans ?_)
          have : (M * (K 1 + K 2 + K 3) + CT * (1 + K 1 + K 1 ^ 2 + K 2)) * Ed +
              (M * (K 1 + K 2 + K 3) + 0 * (1 + K 1 + K 1 ^ 2 + K 2)) * Ed = variationFieldConstant M CT K * Ed := by
            unfold variationFieldConstant
            ring
          exact le_of_eq this
    · have eT : (fun τ : Fin k → ℝ => topVariationField (fun w X' => Th w X') s a ρA m c X b (toImaginary v)
          (leftTranslate (bondSpread c' X' τ) V)) = A := by
        funext τ
        simp only [topVariationField, if_neg hcr, add_zero]
        rfl
      have eJ : ∀ v' : BondVector, (fun τ : Fin k → ℝ =>
          topVariationCoords Th s a ρA m c X b (leftTranslate (bondSpread c' X' τ) V) v') =
          fun τ => _root_.YangMills.Construction.Interpolation.imaginaryCoords (A τ) := by
        intro v'
        funext τ
        simp only [topVariationCoords, topVariationField, if_neg hcr, add_zero]
        rfl
      have eC : (fun v' => bondDeriv (fun V' => topVariationCoords Th s a ρA m c X b V' v') V c' X') =
          fun _ => iteratedFDeriv ℝ k (fun τ : Fin k → ℝ => _root_.YangMills.Construction.Interpolation.imaginaryCoords (A τ)) 0 (fun l => Pi.single l 1) := by
        funext v'
        change iteratedFDeriv ℝ k (fun τ : Fin k → ℝ =>
          topVariationCoords Th s a ρA m c X b (leftTranslate (bondSpread c' X' τ) V) v') 0
          (fun l => Pi.single l 1) = _
        rw [eJ]
      refine ⟨?_, ?_, ?_, ?_⟩
      · rw [eJ v]
        exact imaginaryCoordsCLM.contDiff.contDiffAt.comp (0 : Fin k → ℝ) hAk
      · rw [eC]
        exact contDiffAt_const
      · have hn : 0 ≤ variationFieldConstant M CT K := by
          unfold variationFieldConstant
          nlinarith
        have hvt : bondDeriv (fun V' => topVariationCoords Th s a ρA m c X b V' v) V c' X' =
            imaginaryCoords (bondDeriv (topVariationField (fun w X' => Th w X') s a ρA m c X b (toImaginary v))
              V c' X') := by
          have := congrFun eC v
          refine this.trans ?_
          rw [iteratedFDeriv_imaginaryCoords _ hAk]
          change _ = _root_.YangMills.Construction.Interpolation.imaginaryCoords (iteratedFDeriv ℝ k (fun τ : Fin k → ℝ => topVariationField
            (fun w X' => Th w X') s a ρA m c X b (toImaginary v) (leftTranslate (bondSpread c' X' τ) V)) 0
            (fun l => Pi.single l 1))
          rw [eT]
        rw [hvt, norm_imaginaryCoords]
        refine hbv.trans (mul_le_mul_of_nonneg_right ?_ hE0.le)
        unfold variationFieldConstant
        nlinarith
      · rw [eC]
        simp only [fderiv_fun_const, Pi.zero_apply, norm_zero]
        unfold variationFieldConstant
        have : 0 ≤ 2 * M * (K 1 + K 2 + K 3) + CT * (1 + K 1 + K 1 ^ 2 + K 2) := by nlinarith
        positivity
  · set A0 : imaginaryQuaternions := bondDeriv f V (fun _ : Fin 1 => c) (fun _ => X) with hA0
    set w₀ : imaginaryQuaternions := f V with hw₀
    by_cases hcr : IsCrossingBond b ∧ (enclosingCell b.1, b.2) = c
    · have eG : topVariationCoords Th s a ρA m c X b V =
          fun v' => imaginaryCoordsCLM (A0 + Th (w₀ + toImaginaryCLM v') X) := by
        funext v'
        simp only [topVariationCoords, topVariationField, if_pos hcr]
        rfl
      rw [eG]
      have hw1 : ‖w₀ + toImaginaryCLM v‖ ≤ 1 := hu
      have hptd : ∀ v', HasFDerivAt (fun v'' => w₀ + toImaginaryCLM v'') toImaginaryCLM v' := fun v' =>
        toImaginaryCLM.hasFDerivAt.const_add _
      refine ⟨?_, fun e e' => ?_⟩
      · have h1 : ContDiffAt ℝ ((2 : ℕ) : WithTop ℕ∞) (fun v' : BondVector => w₀ + toImaginaryCLM v') v :=
          contDiffAt_const.add toImaginaryCLM.contDiff.contDiffAt
        have h2 := (ContDiffAt.comp (g := Th) (f := fun v' : BondVector => w₀ + toImaginaryCLM v') v
          (hTh2 _ hw1) h1).clm_apply (contDiffAt_const (c := X))
        exact imaginaryCoordsCLM.contDiff.contDiffAt.comp v (contDiffAt_const.add h2)
      · have hnear : ∀ᶠ v' in 𝓝 v, ‖w₀ + toImaginaryCLM v'‖ < Real.pi := by
          have hcont : ContinuousAt (fun v' => ‖w₀ + toImaginaryCLM v'‖) v := by fun_prop
          exact hcont.eventually (gt_mem_nhds (hπ _ hw1))
        have ev : (fun v' => fderiv ℝ (fun v'' => imaginaryCoordsCLM (A0 + Th (w₀ + toImaginaryCLM v'') X)) v' e')
            =ᶠ[𝓝 v] fun v' => imaginaryCoordsCLM (fderiv ℝ Th (w₀ + toImaginaryCLM v') (toImaginaryCLM e') X) := by
          filter_upwards [hnear] with v' hv'
          have hd : DifferentiableAt ℝ Th (w₀ + toImaginaryCLM v') := (hThs _ hv').differentiableAt (by simp)
          have h1 : HasFDerivAt (fun v'' => Th (w₀ + toImaginaryCLM v''))
              ((fderiv ℝ Th (w₀ + toImaginaryCLM v')).comp toImaginaryCLM) v' :=
            HasFDerivAt.comp (g := Th) (f := fun v'' => w₀ + toImaginaryCLM v'') v' hd.hasFDerivAt (hptd v')
          have h2 := h1.clm_apply (hasFDerivAt_const X v')
          have h3 : HasFDerivAt (fun v'' => A0 + Th (w₀ + toImaginaryCLM v'') X) _ v' := h2.const_add A0
          have h4 := (imaginaryCoordsCLM.hasFDerivAt.comp v' h3).fderiv
          change fderiv ℝ (imaginaryCoordsCLM ∘ fun v'' => A0 + Th (w₀ + toImaginaryCLM v'') X) v' e' = _
          rw [h4]
          simp
        rw [ev.fderiv_eq]
        have hd : DifferentiableAt ℝ (fderiv ℝ Th) (w₀ + toImaginaryCLM v) :=
          ((hThs _ (hπ _ hw1)).fderiv_right (m := 2) (by norm_num)).differentiableAt (by simp)
        have h1 : HasFDerivAt (fun v' => fderiv ℝ Th (w₀ + toImaginaryCLM v'))
            ((fderiv ℝ (fderiv ℝ Th) (w₀ + toImaginaryCLM v)).comp toImaginaryCLM) v :=
          HasFDerivAt.comp (g := fderiv ℝ Th) (f := fun v'' => w₀ + toImaginaryCLM v'') v hd.hasFDerivAt (hptd v)
        have h2 := h1.clm_apply (hasFDerivAt_const (toImaginaryCLM e') v)
        have h3 := h2.clm_apply (hasFDerivAt_const X v)
        have h4 := (imaginaryCoordsCLM.hasFDerivAt.comp v h3).fderiv
        change ‖fderiv ℝ (imaginaryCoordsCLM ∘ fun v' => fderiv ℝ Th (w₀ + toImaginaryCLM v') (toImaginaryCLM e') X)
          v e‖ ≤ _
        rw [h4]
        simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.add_apply, ContinuousLinearMap.flip_apply,
          ContinuousLinearMap.zero_apply, map_zero, add_zero, zero_add, imaginaryCoordsCLM_apply,
          norm_imaginaryCoords, map_add, ContinuousLinearMap.zero_comp]
        have n2 : ‖fderiv ℝ (fderiv ℝ Th) (w₀ + toImaginaryCLM v)‖ ≤ CT := by
          rw [← norm_iteratedFDeriv_one, norm_iteratedFDeriv_fderiv]
          exact hThb _ 2 hw1 (by omega)
        have ne : ‖toImaginaryCLM e‖ = ‖e‖ := norm_toImaginary e
        have ne' : ‖toImaginaryCLM e'‖ = ‖e'‖ := norm_toImaginary e'
        have a1 := ContinuousLinearMap.le_opNorm
          (fderiv ℝ (fderiv ℝ Th) (w₀ + toImaginaryCLM v) (toImaginaryCLM e) (toImaginaryCLM e')) X
        have a2 := ContinuousLinearMap.le_opNorm
          (fderiv ℝ (fderiv ℝ Th) (w₀ + toImaginaryCLM v) (toImaginaryCLM e)) (toImaginaryCLM e')
        have a3 := ContinuousLinearMap.le_opNorm (fderiv ℝ (fderiv ℝ Th) (w₀ + toImaginaryCLM v)) (toImaginaryCLM e)
        rw [hX, mul_one] at a1
        rw [ne'] at a2
        rw [ne] at a3
        have hone : Real.exp (-(r * (cellSupDist (enclosingCell b.1) c.1 : ℝ))) = 1 := by
          have hc : c.1 = enclosingCell b.1 := by rw [← hcr.2]
          have : cellSupDist (enclosingCell b.1) c.1 = 0 := by
            rw [hc]
            simp [cellSupDist]
          rw [this]
          simp
        rw [hone, mul_one]
        refine a1.trans (a2.trans ?_)
        calc _ ≤ ‖fderiv ℝ (fderiv ℝ Th) (w₀ + toImaginaryCLM v)‖ * ‖e‖ * ‖e'‖ :=
              mul_le_mul_of_nonneg_right a3 (norm_nonneg _)
          _ ≤ CT * ‖e‖ * ‖e'‖ :=
              mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right n2 (norm_nonneg _)) (norm_nonneg _)
    · have eG : topVariationCoords Th s a ρA m c X b V = fun _ => _root_.YangMills.Construction.Interpolation.imaginaryCoords A0 := by
        funext v'
        simp only [topVariationCoords, topVariationField, if_neg hcr, add_zero]
        rfl
      rw [eG]
      refine ⟨contDiffAt_const, fun e e' => ?_⟩
      simp only [fderiv_fun_const, Pi.zero_apply, ContinuousLinearMap.zero_apply, norm_zero]
      positivity
end YangMills.Construction.Interpolation
end
