import YangMills.Construction.ClusterExpansionOfAStep.PlaquettesUnderGaugesAndMoves
import YangMills.Construction.SummableBoundsOfTheFlow.DerivativeAlongAMovingField
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Topology
namespace YangMills.Construction
open BlockAverages hiding bondSpread
open ColdStepAtMirrorFrames BondIntegration
namespace IteratedDerivative
namespace MovingField
section Pairing
variable {P E : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [NormedAddCommGroup E] [NormedSpace ℝ E]
theorem fderiv_apply_eval (L : P → E →L[ℝ] ℝ) (w : E) (r a : P) (h : DifferentiableAt ℝ L r) :
    (fderiv ℝ L r a) w = fderiv ℝ (fun r' => L r' w) r a := by
  have := (h.hasFDerivAt.clm_apply (hasFDerivAt_const w r)).fderiv
  rw [this]
  simp
theorem fderiv_pairing_second (L : P → E →L[ℝ] ℝ) (v : P → E) (a b : P) (hL : ContDiffAt ℝ ((2 : ℕ) : WithTop ℕ∞) L 0)
    (hv : ContDiffAt ℝ ((2 : ℕ) : WithTop ℕ∞) v 0) :
    fderiv ℝ (fun r => fderiv ℝ (fun r' => L r' (v r')) r b) 0 a =
      (fderiv ℝ (fun r => fderiv ℝ L r b) 0 a) (v 0) + (fderiv ℝ L 0 b) (fderiv ℝ v 0 a) +
        (fderiv ℝ L 0 a) (fderiv ℝ v 0 b) + L 0 (fderiv ℝ (fun r => fderiv ℝ v r b) 0 a) := by
  have dL : ∀ᶠ r in 𝓝 (0 : P), DifferentiableAt ℝ L r := by
    filter_upwards [hL.eventually (by simp)] with r hr
    exact hr.differentiableAt (by simp)
  have dv : ∀ᶠ r in 𝓝 (0 : P), DifferentiableAt ℝ v r := by
    filter_upwards [hv.eventually (by simp)] with r hr
    exact hr.differentiableAt (by simp)
  have e : (fun r => fderiv ℝ (fun r' => L r' (v r')) r b) =ᶠ[𝓝 0]
      fun r => (fderiv ℝ L r b) (v r) + L r (fderiv ℝ v r b) := by
    filter_upwards [dL, dv] with r h1 h2
    have := (h1.hasFDerivAt.clm_apply h2.hasFDerivAt).fderiv
    rw [this]
    simp [add_comm]
  rw [e.fderiv_eq]
  have dL0 : DifferentiableAt ℝ L 0 := hL.differentiableAt (by simp)
  have dv0 : DifferentiableAt ℝ v 0 := hv.differentiableAt (by simp)
  have dLb : DifferentiableAt ℝ (fun r => fderiv ℝ L r b) 0 := by
    have h1 : DifferentiableAt ℝ (fderiv ℝ L) 0 := (hL.fderiv_right (m := 1) (by norm_num)).differentiableAt (by simp)
    exact h1.clm_apply (differentiableAt_const b)
  have dvb : DifferentiableAt ℝ (fun r => fderiv ℝ v r b) 0 := by
    have h1 : DifferentiableAt ℝ (fderiv ℝ v) 0 := (hv.fderiv_right (m := 1) (by norm_num)).differentiableAt (by simp)
    exact h1.clm_apply (differentiableAt_const b)
  have d1 := dLb.hasFDerivAt.clm_apply dv0.hasFDerivAt
  have d2 := dL0.hasFDerivAt.clm_apply dvb.hasFDerivAt
  have d3 : HasFDerivAt (fun r => (fderiv ℝ L r b) (v r) + L r (fderiv ℝ v r b)) _ 0 := d1.add d2
  rw [d3.fderiv]
  simp
  abel
end Pairing
variable {F : BlockFrame}
abbrev PointParam (F : BlockFrame) : Type := StepVariable (finiteCells F) × (Fin 2 → ℝ)
abbrev paramDir (F : BlockFrame) (a : Fin 2 → ℝ) : PointParam F := (0, a)
theorem derivAlong_param (hL : DerivAlongRulesHold) (g : PointParam F → ℝ) (η : StepVariable (finiteCells F))
    (l : List (Fin 2 → ℝ)) (h : ContDiffAt ℝ (l.length : WithTop ℕ∞) g (η, 0)) :
    derivAlong (fun t => g (η, t)) l 0 = derivAlong g (l.map (paramDir F)) (η, 0) := by
  have e := hL.2 (PointParam F) (Fin 2 → ℝ) ℝ g (ContinuousLinearMap.inr ℝ _ _) (η, 0) 0 l (by simpa using h)
  have e1 : (fun t' : Fin 2 → ℝ => g ((η, 0) + ContinuousLinearMap.inr ℝ (StepVariable (finiteCells F)) (Fin 2 → ℝ) t')) =
      fun t => g (η, t) := by
    funext t'
    simp
  rw [e1] at e
  rw [e]
  simp only [map_zero, add_zero]
  rfl
theorem derivAlong_finset_sum {E W : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup W] [NormedSpace ℝ W]
    (R : DerivAlongRules E W) {α : Type} (S : Finset α) (g : α → E → W) (p : E) (l : List E)
    (h : ∀ a ∈ S, ContDiffAt ℝ (l.length : WithTop ℕ∞) (g a) p) :
    derivAlong (fun q => ∑ a ∈ S, g a q) l p = ∑ a ∈ S, derivAlong (g a) l p := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    have := R.smul 0 (fun _ : E => (0 : W)) p l contDiffAt_const
    simpa using this
  | insert a S ha ih =>
    have h1 := h a (Finset.mem_insert_self _ _)
    have h2 : ∀ a' ∈ S, ContDiffAt ℝ (l.length : WithTop ℕ∞) (g a') p := fun a' m => h a' (Finset.mem_insert_of_mem m)
    have e : (fun q => ∑ a' ∈ insert a S, g a' q) = fun q => g a q + ∑ a' ∈ S, g a' q := by
      funext q
      rw [Finset.sum_insert ha]
    rw [e, R.add _ _ _ _ h1 (ContDiffAt.sum fun a' m => h2 a' m), Finset.sum_insert ha, ih h2]
theorem expUnit_zero : expUnit (0 : imaginaryQuaternions) = 1 := by apply _root_.YangMills.Construction.TorusFields.expUnit_zero <;> assumption
theorem translateAlongPair_zero (V : F.GaugeField F.top) (c : Fin 2 → F.Site F.top × Fin 4) (X : Fin 2 → imaginaryQuaternions) :
    translateAlongPair V c X 0 = V := by
  funext y i
  simp [translateAlongPair, leftTranslate, bondSpread, expUnit_zero]
theorem fderiv_single_eq_bondDeriv {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] (f : F.GaugeField F.top → E)
    (V : F.GaugeField F.top) (c : Fin 2 → F.Site F.top × Fin 4) (X : Fin 2 → imaginaryQuaternions) (l : Fin 2)
    (hd : DifferentiableAt ℝ (fun τ : Fin 2 → ℝ => f (leftTranslate (bondSpread c X τ) V)) 0) :
    fderiv ℝ (fun τ : Fin 2 → ℝ => f (leftTranslate (bondSpread c X τ) V)) 0 (Pi.single l 1) =
      bondDeriv f V (fun _ : Fin 1 => c l) (fun _ => X l) := by
  classical
  unfold bondDeriv
  rw [iteratedFDeriv_one_apply]
  have e : (fun σ : Fin 1 → ℝ => f (leftTranslate (bondSpread (fun _ : Fin 1 => c l) (fun _ => X l) σ) V)) =
      (fun τ : Fin 2 → ℝ => f (leftTranslate (bondSpread c X τ) V)) ∘
        fun σ : Fin 1 → ℝ => σ 0 • (Pi.single l 1 : Fin 2 → ℝ) := by
    funext σ
    have e1 : bondSpread (fun _ : Fin 1 => c l) (fun _ => X l) σ =
        bondSpread c X (σ 0 • (Pi.single l 1 : Fin 2 → ℝ)) := by
      funext y i
      simp only [bondSpread, Finset.univ_unique, Finset.sum_singleton, Pi.smul_apply]
      rw [Finset.sum_eq_single l]
      · simp
      · intro l' _ hl
        simp [Pi.single_eq_of_ne hl]
      · simp
    simp only [Function.comp]
    rw [e1]
  rw [e]
  have hline : HasFDerivAt (fun σ : Fin 1 → ℝ => σ 0 • (Pi.single l 1 : Fin 2 → ℝ))
      ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 1 => ℝ) 0).smulRight (Pi.single l 1)) 0 :=
    ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 1 => ℝ) 0).smulRight
      (Pi.single l 1 : Fin 2 → ℝ)).hasFDerivAt
  have hd' : HasFDerivAt (fun τ : Fin 2 → ℝ => f (leftTranslate (bondSpread c X τ) V))
      (fderiv ℝ (fun τ : Fin 2 → ℝ => f (leftTranslate (bondSpread c X τ) V)) 0)
      ((fun σ : Fin 1 → ℝ => σ 0 • (Pi.single l 1 : Fin 2 → ℝ)) 0) := by
    simpa using hd.hasFDerivAt
  rw [(hd'.comp (0 : Fin 1 → ℝ) hline).fderiv]
  simp
theorem fderiv_eq_derivAlong_cons (hL : DerivAlongRulesHold) (f : PointParam F → ℝ) (η : StepVariable (finiteCells F))
    (l : List (PointParam F)) (O : StepVariable (finiteCells F) → ℝ) (hl : l.length ≤ 2)
    (h3 : ContDiffAt ℝ ((3 : ℕ) : WithTop ℕ∞) f (η, 0))
    (hO : O =ᶠ[𝓝 η] fun ζ => derivAlong f l (ζ, 0)) (u : StepVariable (finiteCells F)) :
    fderiv ℝ O η u = derivAlong f ((u, 0) :: l) (η, 0) := by
  have R := hL.1 (PointParam F) ℝ
  have hA : ContDiffAt ℝ ((1 : ℕ) : WithTop ℕ∞) (derivAlong f l) (η, 0) :=
    R.contDiffAt _ _ 1 _ (h3.of_le (by exact_mod_cast (show 1 + l.length ≤ 3 by omega)))
  have hd : DifferentiableAt ℝ (derivAlong f l) (η, 0) := hA.differentiableAt (by simp)
  rw [hO.fderiv_eq]
  have := (HasFDerivAt.comp (g := derivAlong f l) (f := fun ζ => ((ζ, 0) : PointParam F)) η hd.hasFDerivAt
    (hasFDerivAt_prodMk_left η 0)).fderiv
  change fderiv ℝ (derivAlong f l ∘ fun ζ => ((ζ, 0) : PointParam F)) η u = _
  rw [this]
  simp [derivAlong]
end MovingField
open MovingField in
set_option maxHeartbeats 1000000 in
theorem movingFieldSecondDeriv_holds (hL : DerivAlongRulesHold) :
    MovingFieldSecondDeriv := by
  intro F V G Z D c X η hf hZ hD
  set f := rotatedEval G V c X with hfd
  have h3 : ContDiffAt ℝ ((3 : ℕ) : WithTop ℕ∞) f (η, 0) := hf.self_of_nhds
  have R := hL.1 (PointParam F) ℝ
  have R2 := hL.1 (Fin 2 → ℝ) ℝ
  set e0 : Fin 2 → ℝ := Pi.single 0 1 with he0
  set e1 : Fin 2 → ℝ := Pi.single 1 1 with he1
  have hin : ContDiffAt ℝ ((2 : ℕ) : WithTop ℕ∞) (fun r : Fin 2 → ℝ => ((η, r) : PointParam F)) 0 :=
    (contDiff_const.prodMk contDiff_id).contDiffAt
  have hnear : ∀ᶠ r in 𝓝 (0 : Fin 2 → ℝ), DifferentiableAt ℝ f (η, r) := by
    have hc : Filter.Tendsto (fun r : Fin 2 → ℝ => ((η, r) : PointParam F)) (𝓝 0) (𝓝 (η, 0)) :=
      (by fun_prop : Continuous fun r : Fin 2 → ℝ => ((η, r) : PointParam F)).tendsto 0
    filter_upwards [hc.eventually (h3.eventually (by simp))] with r hr
    exact hr.differentiableAt (by simp)
  set Lm : (Fin 2 → ℝ) → (PointParam F →L[ℝ] ℝ) := fun r => fderiv ℝ f (η, r) with hLmd
  have hLm : ContDiffAt ℝ ((2 : ℕ) : WithTop ℕ∞) Lm 0 := by
    have h1 : ContDiffAt ℝ ((2 : ℕ) : WithTop ℕ∞) (fderiv ℝ f) (η, 0) := h3.fderiv_right (by norm_num)
    exact ContDiffAt.comp (g := fderiv ℝ f) (f := fun r : Fin 2 → ℝ => ((η, r) : PointParam F)) (0 : Fin 2 → ℝ) h1 hin
  set J : ↥(chordBonds (finiteCells F)) → BondVector →L[ℝ] PointParam F := fun b =>
    (ContinuousLinearMap.inl ℝ (StepVariable (finiteCells F)) (Fin 2 → ℝ)).comp
      (ContinuousLinearMap.single ℝ (fun _ : ↥(chordBonds (finiteCells F)) => BondVector) b) with hJ
  have hJa : ∀ b e, J b e = ((bondVariation b e, 0) : PointParam F) := fun b e => rfl
  set zz : ↥(chordBonds (finiteCells F)) → (Fin 2 → ℝ) → BondVector := fun b r => Z b (translateAlongPair V c X r) (η b) with hzz
  have hpart : ∀ᶠ r in 𝓝 (0 : Fin 2 → ℝ), ∀ b e,
      bondPartialDeriv (fun ζ => G ζ (translateAlongPair V c X r)) b η e = Lm r (J b e) := by
    filter_upwards [hnear] with r hr b e
    have h1 := (HasFDerivAt.comp (g := f) (f := fun ζ => ((ζ, r) : PointParam F)) η hr.hasFDerivAt
      (hasFDerivAt_prodMk_left η r)).fderiv
    unfold bondPartialDeriv
    change fderiv ℝ (f ∘ fun ζ => ((ζ, r) : PointParam F)) η (bondVariation b e) = _
    rw [h1]
    simp [hLmd, hJa]
  have hDe : (fun r => D (translateAlongPair V c X r)) =ᶠ[𝓝 0] fun r => ∑ b, Lm r (J b (zz b r)) := by
    filter_upwards [hD, hpart] with r h1 h2
    rw [h1]
    exact Finset.sum_congr rfl fun b _ => h2 b _
  have hv : ∀ b, ContDiffAt ℝ ((2 : ℕ) : WithTop ℕ∞) (fun r => J b (zz b r)) 0 := fun b =>
    (J b).contDiff.contDiffAt.comp (0 : Fin 2 → ℝ) (hZ b)
  have hsm : ∀ b, ContDiffAt ℝ ((2 : ℕ) : WithTop ℕ∞) (fun r => Lm r (J b (zz b r))) 0 := fun b =>
    hLm.clm_apply (hv b)
  have hsum : ContDiffAt ℝ ((2 : ℕ) : WithTop ℕ∞) (fun r => ∑ b, Lm r (J b (zz b r))) 0 :=
    ContDiffAt.sum fun b _ => hsm b
  have h1 : bondDeriv D V c X = derivAlong (fun r => ∑ b, Lm r (J b (zz b r))) [e0, e1] 0 := by
    change iteratedFDeriv ℝ 2 (fun r => D (translateAlongPair V c X r)) 0 (fun l => Pi.single l 1) = _
    rw [(Filter.EventuallyEq.iteratedFDeriv ℝ hDe 2).self_of_nhds, R2.iteratedFDeriv_eq _ _ _ _ hsum]
    simp [List.ofFn_succ, he0, he1]
  rw [h1, derivAlong_finset_sum R2 Finset.univ _ 0 [e0, e1] fun b _ => by simpa using hsm b]
  have obs2 : (fun ζ => bondDeriv (G ζ) V c X) =ᶠ[𝓝 η] fun ζ => derivAlong f [paramDir F e0, paramDir F e1] (ζ, 0) := by
    filter_upwards [hf] with ζ hζ
    have h2 : ContDiffAt ℝ ((2 : ℕ) : WithTop ℕ∞) (fun t => f (ζ, t)) 0 :=
      ContDiffAt.comp (g := f) (f := fun t : Fin 2 → ℝ => ((ζ, t) : PointParam F)) (0 : Fin 2 → ℝ)
        (hζ.of_le (by norm_num)) (contDiff_const.prodMk contDiff_id).contDiffAt
    change iteratedFDeriv ℝ 2 (fun t => f (ζ, t)) 0 (fun l => Pi.single l 1) = _
    rw [R2.iteratedFDeriv_eq _ _ _ _ h2]
    have := derivAlong_param hL f ζ [e0, e1] (by simpa using hζ.of_le (by norm_num))
    simpa [List.ofFn_succ, he0, he1] using this
  have obs1 : ∀ l : Fin 2, (fun ζ => bondDeriv (G ζ) V (fun _ : Fin 1 => c l) (fun _ => X l)) =ᶠ[𝓝 η]
      fun ζ => derivAlong f [paramDir F (Pi.single l 1)] (ζ, 0) := by
    intro l
    filter_upwards [hf] with ζ hζ
    have hd : DifferentiableAt ℝ (fun t => f (ζ, t)) 0 :=
      (ContDiffAt.comp (g := f) (f := fun t : Fin 2 → ℝ => ((ζ, t) : PointParam F)) (0 : Fin 2 → ℝ)
        hζ (contDiff_const.prodMk contDiff_id).contDiffAt).differentiableAt (by simp)
    rw [← fderiv_single_eq_bondDeriv (G ζ) V c X l hd]
    exact derivAlong_param hL f ζ [Pi.single l 1] (by simpa using hζ.of_le (by norm_num))
  have obs0 : (fun ζ => G ζ V) =ᶠ[𝓝 η] fun ζ => derivAlong f [] (ζ, 0) := by
    refine Filter.Eventually.of_forall fun ζ => ?_
    simp only [derivAlong, hfd, rotatedEval]
    have : leftTranslate (bondSpread c X (0 : Fin 2 → ℝ)) V = V := translateAlongPair_zero V c X
    rw [this]
  have perm3 : ∀ w : PointParam F, derivAlong f [w, paramDir F e0, paramDir F e1] (η, 0) =
      derivAlong f [paramDir F e0, paramDir F e1, w] (η, 0) :=
    fun w => R.perm f _ _ _ (((List.Perm.swap _ _ _).trans ((List.Perm.swap _ _ _).cons _))) (by simpa using h3)
  have perm2 : ∀ (a : Fin 2 → ℝ) (w : PointParam F), derivAlong f [w, paramDir F a] (η, 0) =
      derivAlong f [paramDir F a, w] (η, 0) :=
    fun a w => R.perm f _ _ _ (List.Perm.swap _ _ _) (by simpa using h3.of_le (by norm_num))
  have hone : ∀ (w : PointParam F) (l : List (Fin 2 → ℝ)), l.length ≤ 2 →
      derivAlong (fun r => Lm r w) l 0 = derivAlong f (l.map (paramDir F) ++ [w]) (η, 0) := by
    intro w l hl
    have hw : ContDiffAt ℝ ((l.length : ℕ) : WithTop ℕ∞) (derivAlong f [w]) (η, 0) :=
      R.contDiffAt _ _ _ _ (h3.of_le (by exact_mod_cast (show l.length + [w].length ≤ 3 by simp; omega)))
    have := derivAlong_param hL (derivAlong f [w]) η l hw
    rw [← R.append] at this
    exact this
  have evalA : ∀ w : PointParam F, (fderiv ℝ (fun r => fderiv ℝ Lm r e1) 0 e0) w =
      derivAlong f [paramDir F e0, paramDir F e1, w] (η, 0) := by
    intro w
    have d1 : DifferentiableAt ℝ (fderiv ℝ Lm) 0 := (hLm.fderiv_right (m := 1) (by norm_num)).differentiableAt (by simp)
    have d2 : DifferentiableAt ℝ (fun r => fderiv ℝ Lm r e1) 0 := d1.clm_apply (differentiableAt_const e1)
    rw [fderiv_apply_eval _ w 0 e0 d2]
    have dL : ∀ᶠ r in 𝓝 (0 : Fin 2 → ℝ), DifferentiableAt ℝ Lm r := by
      filter_upwards [hLm.eventually (by simp)] with r hr
      exact hr.differentiableAt (by simp)
    have e : (fun r => (fderiv ℝ Lm r e1) w) =ᶠ[𝓝 0] fun r => fderiv ℝ (fun r' => Lm r' w) r e1 := by
      filter_upwards [dL] with r hr
      exact fderiv_apply_eval Lm w r e1 hr
    rw [e.fderiv_eq]
    exact hone w [e0, e1] (by simp)
  have evalB : ∀ (a : Fin 2 → ℝ) (w : PointParam F), (fderiv ℝ Lm 0 a) w = derivAlong f [paramDir F a, w] (η, 0) := by
    intro a w
    rw [fderiv_apply_eval Lm w 0 a (hLm.differentiableAt (by simp))]
    exact hone w [a] (by simp)
  have evalC : ∀ w : PointParam F, Lm 0 w = derivAlong f [w] (η, 0) := fun w => rfl
  have hbond : ∀ b, derivAlong (fun r => Lm r (J b (zz b r))) [e0, e1] 0 =
      fieldDerivative b (Z b V) (fun ζ => bondDeriv (G ζ) V c X) η +
        (fieldDerivative b (vectorFieldDerivSingle (Z b) V c X 0) (fun ζ => bondDeriv (G ζ) V (fun _ : Fin 1 => c 1) (fun _ => X 1)) η +
          fieldDerivative b (vectorFieldDerivSingle (Z b) V c X 1) (fun ζ => bondDeriv (G ζ) V (fun _ : Fin 1 => c 0) (fun _ => X 0)) η +
          fieldDerivative b (vectorFieldDerivPair (Z b) V c X) (fun ζ => G ζ V) η) := by
    intro b
    have hp := fderiv_pairing_second Lm (fun r => J b (zz b r)) e0 e1 hLm (hv b)
    change fderiv ℝ (fun r => fderiv ℝ (fun r' => Lm r' (J b (zz b r'))) r e1) 0 e0 = _
    rw [hp]
    have dz : DifferentiableAt ℝ (zz b) 0 := (hZ b).differentiableAt (by simp)
    have v0 : J b (zz b 0) = J b (Z b V (η b)) := by
      simp only [hzz, translateAlongPair_zero]
    have vd : ∀ r, DifferentiableAt ℝ (zz b) r → ∀ a, fderiv ℝ (fun r' => J b (zz b r')) r a = J b (fderiv ℝ (zz b) r a) := by
      intro r hr a
      have := ((J b).hasFDerivAt.comp r hr.hasFDerivAt).fderiv
      change fderiv ℝ (J b ∘ zz b) r a = _
      rw [this]
      simp
    have v1 : ∀ l, fderiv ℝ (fun r => J b (zz b r)) 0 (Pi.single l 1) = J b (vectorFieldDerivSingle (Z b) V c X l (η b)) := by
      intro l
      rw [vd 0 dz]
      congr 1
      exact fderiv_single_eq_bondDeriv (fun V' => Z b V' (η b)) V c X l dz
    have v2 : fderiv ℝ (fun r => fderiv ℝ (fun r' => J b (zz b r')) r e1) 0 e0 = J b (vectorFieldDerivPair (Z b) V c X (η b)) := by
      have dzz : ∀ᶠ r in 𝓝 (0 : Fin 2 → ℝ), DifferentiableAt ℝ (zz b) r := by
        filter_upwards [(hZ b).eventually (by simp)] with r hr
        exact hr.differentiableAt (by simp)
      have e : (fun r => fderiv ℝ (fun r' => J b (zz b r')) r e1) =ᶠ[𝓝 0] fun r => J b (fderiv ℝ (zz b) r e1) := by
        filter_upwards [dzz] with r hr
        exact vd r hr e1
      rw [e.fderiv_eq]
      have d1 : DifferentiableAt ℝ (fderiv ℝ (zz b)) 0 := ((hZ b).fderiv_right (m := 1) (by norm_num)).differentiableAt (by simp)
      have d2 : DifferentiableAt ℝ (fun r => fderiv ℝ (zz b) r e1) 0 := d1.clm_apply (differentiableAt_const e1)
      have := ((J b).hasFDerivAt.comp (0 : Fin 2 → ℝ) d2.hasFDerivAt).fderiv
      have e2 : (fun r => J b (fderiv ℝ (zz b) r e1)) = J b ∘ fun r => fderiv ℝ (zz b) r e1 := rfl
      rw [e2, this]
      simp only [ContinuousLinearMap.comp_apply]
      congr 1
      change _ = iteratedFDeriv ℝ 2 (zz b) 0 (fun l => Pi.single l 1)
      rw [(hL.1 (Fin 2 → ℝ) BondVector).iteratedFDeriv_eq _ _ _ _ (hZ b)]
      simp [List.ofFn_succ, he0, he1, derivAlong]
      rfl
    have t2 := fderiv_eq_derivAlong_cons hL f η _ _ (by simp) h3 obs2 (bondVariation b (Z b V (η b)))
    have t1a := fderiv_eq_derivAlong_cons hL f η _ _ (by simp) h3 (obs1 1) (bondVariation b (vectorFieldDerivSingle (Z b) V c X 0 (η b)))
    have t1b := fderiv_eq_derivAlong_cons hL f η _ _ (by simp) h3 (obs1 0) (bondVariation b (vectorFieldDerivSingle (Z b) V c X 1 (η b)))
    have t0 := fderiv_eq_derivAlong_cons hL f η _ _ (by simp) h3 obs0 (bondVariation b (vectorFieldDerivPair (Z b) V c X (η b)))
    have f2 : fieldDerivative b (Z b V) (fun ζ => bondDeriv (G ζ) V c X) η =
        derivAlong f [J b (Z b V (η b)), paramDir F e0, paramDir F e1] (η, 0) := t2
    have f1a : fieldDerivative b (vectorFieldDerivSingle (Z b) V c X 0) (fun ζ => bondDeriv (G ζ) V (fun _ : Fin 1 => c 1) (fun _ => X 1)) η =
        derivAlong f [J b (vectorFieldDerivSingle (Z b) V c X 0 (η b)), paramDir F e1] (η, 0) := t1a
    have f1b : fieldDerivative b (vectorFieldDerivSingle (Z b) V c X 1) (fun ζ => bondDeriv (G ζ) V (fun _ : Fin 1 => c 0) (fun _ => X 0)) η =
        derivAlong f [J b (vectorFieldDerivSingle (Z b) V c X 1 (η b)), paramDir F e0] (η, 0) := t1b
    have f0 : fieldDerivative b (vectorFieldDerivPair (Z b) V c X) (fun ζ => G ζ V) η =
        derivAlong f [J b (vectorFieldDerivPair (Z b) V c X (η b))] (η, 0) := t0
    rw [f2, f1a, f1b, f0, perm3, perm2, perm2, v2]
    simp only [v0, he0, he1, v1]
    rw [evalA, evalB, evalB, evalC]
    ring
  simp only [hbond]
  rw [Finset.sum_add_distrib]
  rfl
end IteratedDerivative
end YangMills.Construction
end
