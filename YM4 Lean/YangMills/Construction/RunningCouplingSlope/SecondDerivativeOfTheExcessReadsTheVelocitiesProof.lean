import YangMills.Construction.ColdChainAtEveryLevel.LeastValuesOfAChain
import YangMills.Construction.ColdChainAtEveryLevel.UnitPartsOfQuaternions
import YangMills.Construction.RunningCouplingSlope.ExcessOfAStepIsTwiceDifferentiable
import YangMills.Construction.RunningCouplingSlope.LeastFieldNearTheFlatField
import YangMills.Construction.RunningCouplingSlope.SecondDerivativeOfTheExcessReadsTheVelocities
import Mathlib
set_option autoImplicit false
open Filter
open scoped Topology Quaternion
noncomputable section
namespace YangMills.Construction.RunningCouplingSlope
open BlockAverages ColdStepAtMirrorFrames TorusFields
namespace ExcessHessianAux
section Calculus
variable {Y : Type} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
private theorem secondDeriv_comp_of_fderiv_eq_zero {f : Y → ℝ} (hf : ContDiffAt ℝ 2 f 0)
    (hf₁ : fderiv ℝ f 0 = 0)
    {γ : ℝ → Y} (hγ : ContDiffAt ℝ 2 γ 0) (hγ₀ : γ 0 = 0) {w : Y} (hw : HasDerivAt γ w 0) :
    deriv (deriv fun s => f (γ s)) 0 = fderiv ℝ (fderiv ℝ f) 0 w w := by
  have hfDiff : ∀ᶠ y in 𝓝 (0 : Y), DifferentiableAt ℝ f y :=
    (hf.eventually (by simp)).mono fun y hy => hy.differentiableAt (by norm_num)
  have hγDiff : ∀ᶠ s in 𝓝 (0 : ℝ), DifferentiableAt ℝ γ s :=
    (hγ.eventually (by simp)).mono fun y hy => hy.differentiableAt (by norm_num)
  have hfγ : ∀ᶠ s in 𝓝 (0 : ℝ), DifferentiableAt ℝ f (γ s) := by
    apply hγ.continuousAt.eventually
    rw [hγ₀]
    exact hfDiff
  have hderiv : deriv (fun s => f (γ s)) =ᶠ[𝓝 0] fun s => fderiv ℝ f (γ s) (deriv γ s) := by
    filter_upwards [hfγ, hγDiff] with s hs₁ hs₂
    exact (hs₁.hasFDerivAt.comp_hasDerivAt s hs₂.hasDerivAt).deriv
  have hγ' : HasDerivAt (deriv γ) (deriv (deriv γ) 0) 0 := by
    have hone : ContDiffAt ℝ 1 (deriv γ) 0 := by
      have hfd := hγ.fderiv_right (m := 1) (by norm_num)
      have heq : deriv γ = fun s => fderiv ℝ γ s 1 := by
        funext s
        simp
      rw [heq]
      exact hfd.clm_apply contDiffAt_const
    exact (hone.differentiableAt (by norm_num)).hasDerivAt
  have hfd₁ : DifferentiableAt ℝ (fderiv ℝ f) (γ 0) := by
    rw [hγ₀]
    exact (hf.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hcomp : HasDerivAt (fun s => fderiv ℝ f (γ s)) (fderiv ℝ (fderiv ℝ f) (γ 0) w) 0 :=
    hfd₁.hasFDerivAt.comp_hasDerivAt 0 hw
  have happ := hcomp.clm_apply hγ'
  rw [hderiv.deriv_eq, happ.deriv, hγ₀, hf₁, hw.deriv]
  simp
end Calculus
section Units
private theorem norm_coe_unitQuaternion (g : UnitQuaternion) : ‖(g : ℍ[ℝ])‖ = 1 := by apply _root_.YangMills.Construction.BlockAverages.norm_coe_unitQuaternion <;> assumption
private theorem inv_norm_smul_mem_unitary {q : ℍ[ℝ]} (hq : q ≠ 0) :
    (‖q‖⁻¹ : ℝ) • q ∈ unitary ℍ[ℝ] := by apply _root_.YangMills.Construction.BlockAverages.smul_inv_norm_mem_unitary <;> assumption
open Classical in
private def normalize (q : ℍ[ℝ]) : UnitQuaternion :=
  if hq : q = 0 then 1 else ⟨(‖q‖⁻¹ : ℝ) • q, inv_norm_smul_mem_unitary hq⟩
private theorem normalize_coe_of_ne_zero {q : ℍ[ℝ]} (hq : q ≠ 0) :
    ((normalize q : UnitQuaternion) : ℍ[ℝ]) = (‖q‖⁻¹ : ℝ) • q := by
  simp [normalize, hq]
private theorem coe_unitQuaternion_ne_zero (g : UnitQuaternion) : (g : ℍ[ℝ]) ≠ 0 := by apply _root_.YangMills.Construction.BlockAverages.coe_unitQuaternion_ne_zero <;> assumption
private theorem normalize_coe (g : UnitQuaternion) : normalize (g : ℍ[ℝ]) = g := by
  apply Subtype.ext
  rw [normalize_coe_of_ne_zero (coe_unitQuaternion_ne_zero g), norm_coe_unitQuaternion]
  simp
private theorem contDiffAt_normalize {q : ℍ[ℝ]} (hq : q ≠ 0) :
    ContDiffAt ℝ 2 (fun p : ℍ[ℝ] => ((normalize p : UnitQuaternion) : ℍ[ℝ])) q := by
  have heq : (fun p : ℍ[ℝ] => ((normalize p : UnitQuaternion) : ℍ[ℝ])) =ᶠ[𝓝 q]
      fun p => (‖p‖⁻¹ : ℝ) • p := by
    filter_upwards [isOpen_ne.mem_nhds hq] with p hp
    exact normalize_coe_of_ne_zero hp
  have hnorm : ContDiffAt ℝ 2 (fun p : ℍ[ℝ] => ‖p‖) q := contDiffAt_norm ℝ hq
  exact ((hnorm.inv (norm_ne_zero_iff.2 hq)).smul contDiffAt_id).congr_of_eventuallyEq heq
end Units
section Moves
private theorem contDiffAt_exp_smul_mul (b w : ℍ[ℝ]) :
    ContDiffAt ℝ 2 (fun s : ℝ => NormedSpace.exp (s • b) * w) 0 := by
  have hlin : ContDiffAt ℝ 2 (fun s : ℝ => s • b) 0 := contDiffAt_id.smul contDiffAt_const
  have hexp : ContDiffAt ℝ 2 (NormedSpace.exp : ℍ[ℝ] → ℍ[ℝ]) ((0 : ℝ) • b) :=
    (NormedSpace.exp_analytic (𝕂 := ℝ) _).contDiffAt
  exact (hexp.comp (0 : ℝ) hlin).mul contDiffAt_const
private theorem hasDerivAt_exp_smul_mul (b w : ℍ[ℝ]) :
    HasDerivAt (fun s : ℝ => NormedSpace.exp (s • b) * w) (b * w) 0 := by
  have hd := (hasDerivAt_exp_smul_const (𝕂 := ℝ) b (0 : ℝ)).mul_const w
  simpa using hd
private theorem leftExpAction_zero_smul {F : BlockFrame} {j : ℕ}
    (A : F.Site j → Fin 4 → imaginaryQuaternions) (W : F.GaugeField j) :
    leftExpAction ((0 : ℝ) • A) W = W := by
  funext x i
  apply Subtype.ext
  show NormedSpace.exp ((((0 : ℝ) • A) x i : imaginaryQuaternions) : ℍ[ℝ]) * (W x i : ℍ[ℝ]) =
    (W x i : ℍ[ℝ])
  simp
end Moves
private theorem secondDeriv_eq_excessHessian_of_nonneg {F : BlockFrame}
    [Fintype (F.Site F.depth)] [Fintype (F.Site F.top)] {a : ℝ}
    (W₀ : F.GaugeField F.depth) (V₀ : F.GaugeField F.top)
    (hnonneg : ∀ (W : F.GaugeField F.depth) (V : F.GaugeField F.top), 0 ≤ excessEnergy a W V)
    (hzero : excessEnergy a W₀ V₀ = 0)
    (hsmooth : ∀ (Y : Type) [NormedAddCommGroup Y] [NormedSpace ℝ Y] [FiniteDimensional ℝ Y] (y₀ : Y)
      (Φ : Y → F.GaugeField F.depth) (Ψ : Y → F.GaugeField F.top),
      Φ y₀ = W₀ → Ψ y₀ = V₀ →
      (∀ x i, ContDiffAt ℝ 2 (fun y => ((Φ y x i : UnitQuaternion) : ℍ[ℝ])) y₀) →
      (∀ x i, ContDiffAt ℝ 2 (fun y => ((Ψ y x i : UnitQuaternion) : ℍ[ℝ])) y₀) →
      ContDiffAt ℝ 2 (fun y => excessEnergy a (Φ y) (Ψ y)) y₀)
    (Φ : ℝ → F.GaugeField F.depth) (Ψ : ℝ → F.GaugeField F.top)
    (A : F.Site F.depth → Fin 4 → imaginaryQuaternions) (B : F.Site F.top → Fin 4 → imaginaryQuaternions)
    (hΦ₀ : Φ 0 = W₀) (hΨ₀ : Ψ 0 = V₀)
    (hΦ : ∀ x i, ContDiffAt ℝ 2 (fun s => ((Φ s x i : UnitQuaternion) : ℍ[ℝ])) 0)
    (hΨ : ∀ x i, ContDiffAt ℝ 2 (fun s => ((Ψ s x i : UnitQuaternion) : ℍ[ℝ])) 0)
    (hΦ' : ∀ x i, HasDerivAt (fun s => ((Φ s x i : UnitQuaternion) : ℍ[ℝ]))
      ((A x i : ℍ[ℝ]) * ((W₀ x i : UnitQuaternion) : ℍ[ℝ])) 0)
    (hΨ' : ∀ x i, HasDerivAt (fun s => ((Ψ s x i : UnitQuaternion) : ℍ[ℝ]))
      ((B x i : ℍ[ℝ]) * ((V₀ x i : UnitQuaternion) : ℍ[ℝ])) 0) :
    ContDiffAt ℝ 2 (fun s => excessEnergy a (Φ s) (Ψ s)) 0 ∧
      deriv (deriv fun s => excessEnergy a (Φ s) (Ψ s)) 0 = excessHessian a W₀ V₀ A B := by
  let Y : Type := (F.Site F.depth → Fin 4 → ℍ[ℝ]) × (F.Site F.top → Fin 4 → ℍ[ℝ])
  let lower : Y → F.GaugeField F.depth := fun y x i => normalize ((W₀ x i : ℍ[ℝ]) + y.1 x i)
  let upper : Y → F.GaugeField F.top := fun y x i => normalize ((V₀ x i : ℍ[ℝ]) + y.2 x i)
  let f : Y → ℝ := fun y => excessEnergy a (lower y) (upper y)
  have hlower : lower 0 = W₀ := by
    funext x i
    show normalize ((W₀ x i : ℍ[ℝ]) + 0) = W₀ x i
    rw [add_zero, normalize_coe]
  have hupper : upper 0 = V₀ := by
    funext x i
    show normalize ((V₀ x i : ℍ[ℝ]) + 0) = V₀ x i
    rw [add_zero, normalize_coe]
  have hf : ContDiffAt ℝ 2 f 0 := by
    refine hsmooth Y 0 lower upper hlower hupper (fun x i => ?_) (fun x i => ?_)
    · have hg : ContDiff ℝ 2 (fun y : Y => (W₀ x i : ℍ[ℝ]) + y.1 x i) :=
        contDiff_const.add ((contDiff_apply_apply ℝ ℍ[ℝ] x i).comp contDiff_fst)
      have hn : ContDiffAt ℝ 2 (fun p : ℍ[ℝ] => ((normalize p : UnitQuaternion) : ℍ[ℝ]))
          ((W₀ x i : ℍ[ℝ]) + (0 : Y).1 x i) :=
        contDiffAt_normalize (by simpa using coe_unitQuaternion_ne_zero (W₀ x i))
      exact ContDiffAt.comp (g := fun p : ℍ[ℝ] => ((normalize p : UnitQuaternion) : ℍ[ℝ]))
        (f := fun y : Y => (W₀ x i : ℍ[ℝ]) + y.1 x i) (0 : Y) hn hg.contDiffAt
    · have hg : ContDiff ℝ 2 (fun y : Y => (V₀ x i : ℍ[ℝ]) + y.2 x i) :=
        contDiff_const.add ((contDiff_apply_apply ℝ ℍ[ℝ] x i).comp contDiff_snd)
      have hn : ContDiffAt ℝ 2 (fun p : ℍ[ℝ] => ((normalize p : UnitQuaternion) : ℍ[ℝ]))
          ((V₀ x i : ℍ[ℝ]) + (0 : Y).2 x i) :=
        contDiffAt_normalize (by simpa using coe_unitQuaternion_ne_zero (V₀ x i))
      exact ContDiffAt.comp (g := fun p : ℍ[ℝ] => ((normalize p : UnitQuaternion) : ℍ[ℝ]))
        (f := fun y : Y => (V₀ x i : ℍ[ℝ]) + y.2 x i) (0 : Y) hn hg.contDiffAt
  have hf₀ : f 0 = 0 := by
    show excessEnergy a (lower 0) (upper 0) = 0
    rw [hlower, hupper, hzero]
  have hmin : IsLocalMin f 0 :=
    Eventually.of_forall fun y => by
      rw [hf₀]
      exact hnonneg _ _
  have hf₁ : fderiv ℝ f 0 = 0 := hmin.fderiv_eq_zero
  let w : Y := (fun x i => (A x i : ℍ[ℝ]) * (W₀ x i : ℍ[ℝ]), fun x i => (B x i : ℍ[ℝ]) * (V₀ x i : ℍ[ℝ]))
  have hkey : ∀ (P : ℝ → F.GaugeField F.depth) (Q : ℝ → F.GaugeField F.top), P 0 = W₀ → Q 0 = V₀ →
      (∀ x i, ContDiffAt ℝ 2 (fun s => ((P s x i : UnitQuaternion) : ℍ[ℝ])) 0) →
      (∀ x i, ContDiffAt ℝ 2 (fun s => ((Q s x i : UnitQuaternion) : ℍ[ℝ])) 0) →
      (∀ x i, HasDerivAt (fun s => ((P s x i : UnitQuaternion) : ℍ[ℝ])) ((A x i : ℍ[ℝ]) * (W₀ x i : ℍ[ℝ])) 0) →
      (∀ x i, HasDerivAt (fun s => ((Q s x i : UnitQuaternion) : ℍ[ℝ])) ((B x i : ℍ[ℝ]) * (V₀ x i : ℍ[ℝ])) 0) →
      deriv (deriv fun s => excessEnergy a (P s) (Q s)) 0 = fderiv ℝ (fderiv ℝ f) 0 w w := by
    intro P Q hP₀ hQ₀ hP hQ hP' hQ'
    let γ : ℝ → Y := fun s => (fun x i => (P s x i : ℍ[ℝ]) - (W₀ x i : ℍ[ℝ]),
      fun x i => (Q s x i : ℍ[ℝ]) - (V₀ x i : ℍ[ℝ]))
    have hγ : ContDiffAt ℝ 2 γ 0 :=
      ContDiffAt.prodMk (contDiffAt_pi.2 fun x => contDiffAt_pi.2 fun i => (hP x i).sub contDiffAt_const)
        (contDiffAt_pi.2 fun x => contDiffAt_pi.2 fun i => (hQ x i).sub contDiffAt_const)
    have hγ₀ : γ 0 = 0 := by
      apply Prod.ext
      · funext x i
        show (P 0 x i : ℍ[ℝ]) - (W₀ x i : ℍ[ℝ]) = 0
        rw [hP₀, sub_self]
      · funext x i
        show (Q 0 x i : ℍ[ℝ]) - (V₀ x i : ℍ[ℝ]) = 0
        rw [hQ₀, sub_self]
    have hw : HasDerivAt γ w 0 :=
      HasDerivAt.prodMk (hasDerivAt_pi.2 fun x => hasDerivAt_pi.2 fun i => (hP' x i).sub_const _)
        (hasDerivAt_pi.2 fun x => hasDerivAt_pi.2 fun i => (hQ' x i).sub_const _)
    have heq : (fun s => excessEnergy a (P s) (Q s)) = fun s => f (γ s) := by
      funext s
      have hl : lower (γ s) = P s := by
        funext x i
        show normalize ((W₀ x i : ℍ[ℝ]) + ((P s x i : ℍ[ℝ]) - (W₀ x i : ℍ[ℝ]))) = P s x i
        rw [add_sub_cancel, normalize_coe]
      have hu : upper (γ s) = Q s := by
        funext x i
        show normalize ((V₀ x i : ℍ[ℝ]) + ((Q s x i : ℍ[ℝ]) - (V₀ x i : ℍ[ℝ]))) = Q s x i
        rw [add_sub_cancel, normalize_coe]
      show excessEnergy a (P s) (Q s) = excessEnergy a (lower (γ s)) (upper (γ s))
      rw [hl, hu]
    rw [heq]
    exact secondDeriv_comp_of_fderiv_eq_zero hf hf₁ hγ hγ₀ hw
  refine ⟨hsmooth ℝ 0 Φ Ψ hΦ₀ hΨ₀ hΦ hΨ, ?_⟩
  rw [hkey Φ Ψ hΦ₀ hΨ₀ hΦ hΨ hΦ' hΨ']
  unfold excessHessian
  symm
  refine hkey (fun s => leftExpAction (s • A) W₀) (fun s => leftExpAction (s • B) V₀)
    (leftExpAction_zero_smul A W₀) (leftExpAction_zero_smul B V₀)
    (fun x i => ?_) (fun x i => ?_) (fun x i => ?_) (fun x i => ?_)
  · exact contDiffAt_exp_smul_mul (A x i : ℍ[ℝ]) (W₀ x i : ℍ[ℝ])
  · exact contDiffAt_exp_smul_mul (B x i : ℍ[ℝ]) (V₀ x i : ℍ[ℝ])
  · exact hasDerivAt_exp_smul_mul (A x i : ℍ[ℝ]) (W₀ x i : ℍ[ℝ])
  · exact hasDerivAt_exp_smul_mul (B x i : ℍ[ℝ]) (V₀ x i : ℍ[ℝ])
private theorem stepMinimizer_eq_chartedField {F : BlockFrame} (a ρ : ℝ) (V : F.GaugeField F.top) :
    stepMinimizer a ρ V = chartedField (minimizingCoordinates a (finiteCells F) V ρ) V := by
  have heq : coordsAboveFrame true a ρ 0 V 0 = minimizingCoordinates a (finiteCells F) V ρ := by
    funext x i
    have hz : stepCoordinates (0 : StepVariable (finiteCells F)) x i = 0 := by
      unfold stepCoordinates
      split_ifs with h
      · exact Subtype.ext (by ext <;> simp [toImaginary])
      · rfl
    simp [coordsAboveFrame, stepFrame, minimizingBondCoordinate, hz]
  show chartedField (coordsAboveFrame true a ρ 0 V 0) V = _
  rw [heq]
end ExcessHessianAux
open ExcessHessianAux in
theorem secondDeriv_excessEnergy_eq_excessHessian
    (hE : ExcessEnergyIsContDiffTwo)
    (hN : MinimizerNearTrivialField)
    (hV : minimalChainExistenceStatement) :
    SecondDerivExcessEnergyEqExcessHessian := by
  intro a ha L hL t m ρ hm r0 r1
  filter_upwards [(hN a ha L hL t m ρ hm r0 r1).2, hE a ha L hL t m ρ hm r0 r1] with V₀ hl hc
  intro Φ Ψ A B hΦ hΨ cΦ cΨ dΦ dΨ
  have hLpos : 0 < L := hL.1.pos
  have hmpos : 0 < m := by
    have := hL.2
    omega
  have : ∀ (j : ℕ) (i : Fin 4), NeZero ((torusFrame L t m).period j i) := fun j i => ⟨by
    unfold BlockFrame.period
    exact (Nat.mul_pos hmpos (pow_pos hLpos _)).ne'⟩
  obtain ⟨-, -, hex, -⟩ := hV (torusFrame L t m) a (finiteCells (torusFrame L t m)) ha.le
  have hnonneg : ∀ (W : (torusFrame L t m).GaugeField (torusFrame L t m).depth)
      (V : (torusFrame L t m).GaugeField (torusFrame L t m).top), 0 ≤ excessEnergy a W V := by
    intro W V
    obtain ⟨W₁, he, hmin⟩ := hex (torusFrame L t m).depth V
    have h2 := hmin W
    unfold excessEnergy
    linarith
  have hzero : excessEnergy a (Φ 0) (Ψ 0) = 0 := by
    rw [hΦ, hΨ, stepMinimizer_eq_chartedField]
    obtain ⟨w, hw⟩ := hl.1
    have hs : IsMinimizingChart a (finiteCells (torusFrame L t m))
        (readAtLevel (torusFrame L t m) (torusFrame L t m).top V₀) ρ
        (minimizingCoordinates a (finiteCells (torusFrame L t m))
          (readAtLevel (torusFrame L t m) (torusFrame L t m).top V₀) ρ) := by
      unfold minimizingCoordinates
      rw [dif_pos ⟨w, hw⟩]
      exact Exists.choose_spec (p := fun w => IsMinimizingChart a (finiteCells (torusFrame L t m))
        (readAtLevel (torusFrame L t m) (torusFrame L t m).top V₀) ρ w) ⟨w, hw⟩
    obtain ⟨W₁, he, hmin⟩ := hex (torusFrame L t m).depth
      (readAtLevel (torusFrame L t m) (torusFrame L t m).top V₀)
    have h2 := hmin (chartedField (minimizingCoordinates a (finiteCells (torusFrame L t m))
      (readAtLevel (torusFrame L t m) (torusFrame L t m).top V₀) ρ)
      (readAtLevel (torusFrame L t m) (torusFrame L t m).top V₀))
    have h3 := hs.2.2 W₁
    unfold excessEnergy
    linarith
  exact secondDeriv_eq_excessHessian_of_nonneg (Φ 0) (Ψ 0) hnonneg hzero
    (fun Y _ _ _ y₀ P Q hP hQ => hc Y y₀ P Q (hP.trans hΦ) (hQ.trans hΨ)) Φ Ψ A B rfl rfl cΦ cΨ dΦ dΨ
end YangMills.Construction.RunningCouplingSlope
end
