import YangMills.Construction.ResponseInTheExpansion.GapLessCostIsASlope
import YangMills.Construction.SummableBoundsOfTheFlow.ObservablesInTheLawsBetweenProof
import YangMills.Construction.SummableBoundsOfTheFlow.PartsBetweenAreSmoothInTheParameters
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction
open BlockAverages hiding bondSpread
open ColdStepAtMirrorFrames Interpolation WeightedResponses
namespace ResponseInTheExpansion
variable {F : BlockFrame}
private theorem expUnit_zero' : expUnit (0 : imaginaryQuaternions) = 1 := Subtype.ext (by simp [expUnit])
private theorem leftTranslate_empty {j : ℕ} (V : F.GaugeField j) (τ : Fin 0 → ℝ) :
    leftTranslate (bondSpread (Fin.elim0 : Fin 0 → F.Site j × Fin 4) (Fin.elim0 : Fin 0 → imaginaryQuaternions) τ) V = V := by
  funext y i
  simp [leftTranslate, bondSpread, expUnit_zero']
private theorem contDiffAt_one_of_displaced (G : StepVariable (finiteCells F) → F.GaugeField F.top → ℝ) (V : F.GaugeField F.top)
    (η : StepVariable (finiteCells F))
    (h : ∀ (l : ℕ) (b : Fin l → ↥(chordBonds (finiteCells F))) (u : Fin l → EuclideanSpace ℝ (Fin 3)), 2 ≤ l →
      (∀ i, ‖u i‖ = 1) → ContDiffAt ℝ ((l + 0 : ℕ)) (jointDisplacement (j := 0) G η V b u Fin.elim0 Fin.elim0) 0) :
    ContDiffAt ℝ 1 (fun ζ => G ζ V) η := by
  classical
  by_cases hι : IsEmpty ↥(chordBonds (finiteCells F))
  · have : (fun ζ : StepVariable (finiteCells F) => G ζ V) = fun _ => G η V :=
      funext fun ζ => by rw [Subsingleton.elim ζ η]
    rw [this]
    exact contDiffAt_const
  · obtain ⟨b₀⟩ := not_isEmpty_iff.1 hι
    let n := Fintype.card (↥(chordBonds (finiteCells F)) × Fin 3)
    let e : Fin n ≃ ↥(chordBonds (finiteCells F)) × Fin 3 := (Fintype.equivFin _).symm
    have hn : 2 ≤ n := by
      have h0 : 0 < Fintype.card ↥(chordBonds (finiteCells F)) := Fintype.card_pos_iff.2 ⟨b₀⟩
      simp only [n, Fintype.card_prod, Fintype.card_fin]
      omega
    let b : Fin n → ↥(chordBonds (finiteCells F)) := fun k => (e k).1
    let u : Fin n → EuclideanSpace ℝ (Fin 3) := fun k => EuclideanSpace.single (e k).2 1
    have hu : ∀ i, ‖u i‖ = 1 := fun i => by simp [u]
    have hm := h n b u hn hu
    let φ : StepVariable (finiteCells F) → (Fin (n + 0) → ℝ) := fun ζ k => (ζ (b k) - η (b k)) ((e k).2)
    have hφ : ContDiff ℝ 1 φ := by
      refine contDiff_pi.2 fun k => ?_
      have h1 : ContDiff ℝ 1 fun ζ : StepVariable (finiteCells F) => ζ (b k) - η (b k) :=
        (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ↥(chordBonds (finiteCells F)) => EuclideanSpace ℝ (Fin 3)) (b k)).contDiff.sub
          contDiff_const
      exact (EuclideanSpace.proj (𝕜 := ℝ) ((e k).2)).contDiff.comp h1
    have hφ0 : φ η = 0 := by
      funext k
      simp [φ]
    have hpoint : ∀ ζ : StepVariable (finiteCells F),
        displacedPoint η b u (fun i => φ ζ (Fin.castAdd 0 i)) = ζ := fun ζ => by
      have hs : (∑ k : Fin n, Pi.single (b k) ((φ ζ (Fin.castAdd 0 k)) • u k)) =
          ∑ q : ↥(chordBonds (finiteCells F)) × Fin 3,
            (Pi.single q.1 ((ζ q.1 - η q.1) q.2 • EuclideanSpace.single q.2 (1 : ℝ)) : StepVariable (finiteCells F)) :=
        Equiv.sum_comp e (fun q : ↥(chordBonds (finiteCells F)) × Fin 3 =>
          (Pi.single q.1 ((ζ q.1 - η q.1) q.2 • EuclideanSpace.single q.2 (1 : ℝ)) : StepVariable (finiteCells F)))
      unfold displacedPoint
      rw [hs, Fintype.sum_prod_type]
      funext b₁
      simp only [Pi.add_apply, Finset.sum_apply]
      have hv : ∀ v : EuclideanSpace ℝ (Fin 3), ∑ i : Fin 3, v i • EuclideanSpace.single i (1 : ℝ) = v := fun v => by
        ext j
        simp [Finset.sum_apply, Pi.single_apply]
      have h2 : ∑ c : ↥(chordBonds (finiteCells F)), ∑ i : Fin 3,
          (Pi.single c ((ζ c - η c) i • EuclideanSpace.single i (1 : ℝ)) : StepVariable (finiteCells F)) b₁ =
          ζ b₁ - η b₁ := by
        rw [Finset.sum_eq_single b₁]
        · simp only [Pi.single_eq_same]
          exact hv _
        · intro c _ hc
          simp [Pi.single_eq_of_ne (Ne.symm hc)]
        · intro hb
          exact absurd (Finset.mem_univ _) hb
      rw [h2]
      simp
    have hid : ∀ ζ : StepVariable (finiteCells F),
        jointDisplacement (j := 0) G η V b u Fin.elim0 Fin.elim0 (φ ζ) = G ζ V := fun ζ => by
      unfold jointDisplacement
      rw [hpoint ζ, leftTranslate_empty]
    have hn1 : (1 : WithTop ℕ∞) ≤ ((n + 0 : ℕ) : WithTop ℕ∞) := by
      exact_mod_cast (by omega : 1 ≤ n + 0)
    have hc : ContDiffAt ℝ 1 (jointDisplacement (j := 0) G η V b u Fin.elim0 Fin.elim0) (φ η) := by
      rw [hφ0]
      exact hm.of_le hn1
    have := ContDiffAt.comp η hc hφ.contDiffAt
    exact this.congr_of_eventuallyEq (Filter.Eventually.of_forall fun ζ => (hid ζ).symm)
abbrev _root_.YangMills.SharedProofs.p65438 := @contDiffAt_one_of_displaced
private theorem toImaginary_add (v w : EuclideanSpace ℝ (Fin 3)) : toImaginary (v + w) = toImaginary v + toImaginary w := by apply _root_.YangMills.Construction.Interpolation.TopVariation.toImaginary_add <;> assumption
private theorem toImaginary_smul (u : ℝ) (v : EuclideanSpace ℝ (Fin 3)) : toImaginary (u • v) = u • toImaginary v := by apply _root_.YangMills.Construction.Interpolation.TopVariation.toImaginary_smul <;> assumption
private theorem interpolatedCoords_add_bondVariation (a ρA : ℝ) (m : ℕ) (V : F.GaugeField F.top) (η : StepVariable (finiteCells F))
    (b : ↥(chordBonds (finiteCells F))) (e : EuclideanSpace ℝ (Fin 3)) (u : ℝ) :
    interpolatedCoords 1 a ρA m V (η + u • bondVariation b e) =
      Function.update (interpolatedCoords 1 a ρA m V η) b.1.1
        (Function.update (interpolatedCoords 1 a ρA m V η b.1.1) b.1.2
          (interpolatedCoords 1 a ρA m V η b.1.1 b.1.2 + u • toImaginary e)) := by
  classical
  funext z i
  have key : stepCoordinates (η + u • bondVariation b e) z i =
      stepCoordinates η z i + if (z, i) = b.1 then u • toImaginary e else 0 := by
    unfold stepCoordinates
    by_cases h : (z, i) ∈ chordBonds (finiteCells F)
    · rw [dif_pos h, dif_pos h]
      by_cases hb : (z, i) = b.1
      · have hbb : (⟨(z, i), h⟩ : ↥(chordBonds (finiteCells F))) = b := Subtype.ext hb
        rw [if_pos hb, hbb]
        simp [bondVariation, toImaginary_add, toImaginary_smul]
      · have hne : (⟨(z, i), h⟩ : ↥(chordBonds (finiteCells F))) ≠ b := fun hh => hb (congrArg Subtype.val hh)
        rw [if_neg hb]
        simp [bondVariation, Pi.single_eq_of_ne hne]
    · have hb : (z, i) ≠ b.1 := fun hh => h (hh ▸ b.2)
      rw [dif_neg h, dif_neg h, if_neg hb]
      simp
  by_cases hz : z = b.1.1
  · subst hz
    by_cases hi : i = b.1.2
    · subst hi
      simp only [Function.update_self]
      show interpolatedFrame 1 a ρA m _ V + stepCoordinates (η + u • bondVariation b e) _ _ =
        interpolatedFrame 1 a ρA m _ V + stepCoordinates η _ _ + _
      rw [key, if_pos rfl, add_assoc]
    · have hb : (b.1.1, i) ≠ b.1 := fun hh => hi (congrArg Prod.snd hh)
      simp only [Function.update_self, Function.update_of_ne hi]
      show interpolatedFrame 1 a ρA m _ V + stepCoordinates (η + u • bondVariation b e) _ _ =
        interpolatedFrame 1 a ρA m _ V + stepCoordinates η _ _
      rw [key, if_neg hb, add_zero]
  · have hb : (z, i) ≠ b.1 := fun hh => hz (congrArg Prod.fst hh)
    simp only [Function.update_of_ne hz]
    show interpolatedFrame 1 a ρA m _ V + stepCoordinates (η + u • bondVariation b e) _ _ =
      interpolatedFrame 1 a ρA m _ V + stepCoordinates η _ _
    rw [key, if_neg hb, add_zero]
private theorem bondPartialDeriv_eq_chartedSlope (Q : ColdHalfLaw) (V : F.GaugeField F.top) (η : StepVariable (finiteCells F))
    (hS : DifferentiableAt ℝ (fun ζ => Q.totalCost ζ V) η) (b : ↥(chordBonds (finiteCells F)))
    (e : EuclideanSpace ℝ (Fin 3)) :
    bondPartialDeriv (fun ζ => Q.totalCost ζ V) b η e =
      chartedSlope Q.a (interpolatedCoords 1 Q.a Q.chartRadius Q.mirrorRadius V η) V b.1 (toImaginary e) := by
  have h := (hS.hasFDerivAt.hasLineDerivAt (bondVariation b e)).deriv
  unfold bondPartialDeriv chartedSlope
  rw [← h]
  congr 1
  funext u
  show chartedEnergy Q.a (interpolatedCoords 1 Q.a Q.chartRadius Q.mirrorRadius V (η + u • bondVariation b e)) V = _
  rw [interpolatedCoords_add_bondVariation]
abbrev _root_.YangMills.SharedProofs.p18260 := @bondPartialDeriv_eq_chartedSlope
private theorem slopeTerm_eq (Q : ColdHalfLaw) (Y : F.Cell) (η : StepVariable (finiteCells F)) (V : F.GaugeField F.top) :
    Q.slopeTerm Y η V = Q.coupling * ColdHalfLaw.sumOverBlock Y (fun b =>
        chartedSlope Q.a (interpolatedCoords 1 Q.a Q.chartRadius Q.mirrorRadius V η) V b.1 (toImaginary (η b))) -
      2 * Q.linearBlockPart Y η V := by
  classical
  unfold ColdHalfLaw.slopeTerm ColdHalfLaw.linearBlockPart ColdHalfLaw.sumOverBlock ColdHalfLaw.slopeRemainder
  have h : ∀ (A I : ↥(chordBonds (finiteCells F)) → ℝ),
      (∑ b : ↥(chordBonds (finiteCells F)), if enclosingCell b.1.1 = Y then A b - 2 * I b else 0) =
        (∑ b : ↥(chordBonds (finiteCells F)), if enclosingCell b.1.1 = Y then A b else 0) -
          2 * ∑ b : ↥(chordBonds (finiteCells F)), if enclosingCell b.1.1 = Y then I b else 0 := fun A I => by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun b _ => ?_
    split_ifs <;> simp
  rw [h]
  ring
abbrev _root_.YangMills.SharedProofs.p90711 := @slopeTerm_eq
private theorem isOpen_bondBalls (ρ : ℝ) : IsOpen {η : StepVariable (finiteCells F) | ∀ b, ‖η b‖ < ρ} := by apply _root_.YangMills.Construction.Interpolation.ObservableSizes.isOpen_bondBall <;> assumption
private theorem contDiffAt_of_untranslated {k : WithTop ℕ∞} (G : StepVariable (finiteCells F) → F.GaugeField F.top → ℝ)
    (V : F.GaugeField F.top) (η : StepVariable (finiteCells F))
    (h : ContDiffAt ℝ k (fun q : (Fin 0 → ℝ) × StepVariable (finiteCells F) =>
      G q.2 (leftTranslate (bondSpread (Fin.elim0 : Fin 0 → F.Site F.top × Fin 4)
        (Fin.elim0 : Fin 0 → imaginaryQuaternions) q.1) V)) (0, η)) :
    ContDiffAt ℝ k (fun ζ => G ζ V) η := by
  have hin : ContDiffAt ℝ k (fun ζ : StepVariable (finiteCells F) => ((0 : Fin 0 → ℝ), ζ)) η :=
    contDiffAt_const.prodMk contDiffAt_id
  have h2 := ContDiffAt.comp η h hin
  refine h2.congr_of_eventuallyEq (Filter.Eventually.of_forall fun ζ => ?_)
  show G ζ V = G ζ (leftTranslate _ V)
  rw [leftTranslate_empty]
abbrev _root_.YangMills.SharedProofs.p43393 := @contDiffAt_of_untranslated
private theorem interpolatedExponent_eq (Q : ColdHalfLaw) (V : F.GaugeField F.top) (ζ : StepVariable (finiteCells F)) :
    interpolatedExponent 1 Q.a Q.chartRadius Q.coupling Q.mirrorRadius V ζ =
      Q.coupling * (Q.totalCost ζ V - Q.totalCost 0 V) - Q.gapHaarExcess ζ V := by
  simp only [interpolatedExponent, ColdHalfLaw.totalCost, ColdHalfLaw.gapHaarExcess]
  ring
private theorem gapTerm_sub_slopeTerm (Q : ColdHalfLaw) (Y : F.Cell) (V : F.GaugeField F.top) (η : StepVariable (finiteCells F))
    (hS : DifferentiableAt ℝ (fun ζ => Q.totalCost ζ V) η)
    (hΨ : DifferentiableAt ℝ (interpolatedExponent 1 Q.a Q.chartRadius Q.coupling Q.mirrorRadius V) η) :
    Q.gapTerm Y η V - Q.slopeTerm Y η V = 2 * Q.linearBlockPart Y η V - Q.exponentRadialPart Y η V := by
  classical
  have hfun : (fun ζ => Q.gapHaarExcess ζ V) = fun ζ => Q.coupling * (Q.totalCost ζ V - Q.totalCost 0 V) -
      interpolatedExponent 1 Q.a Q.chartRadius Q.coupling Q.mirrorRadius V ζ := by
    funext ζ
    rw [interpolatedExponent_eq]
    ring
  have hc := (hS.hasFDerivAt.sub_const (Q.totalCost 0 V)).const_mul Q.coupling
  have hd := hc.sub hΨ.hasFDerivAt
  have hJ : ∀ (b : ↥(chordBonds (finiteCells F))) (e : EuclideanSpace ℝ (Fin 3)),
      bondPartialDeriv (fun ζ => Q.gapHaarExcess ζ V) b η e =
        Q.coupling * chartedSlope Q.a (interpolatedCoords 1 Q.a Q.chartRadius Q.mirrorRadius V η) V b.1 (toImaginary e) -
          bondPartialDeriv (interpolatedExponent 1 Q.a Q.chartRadius Q.coupling Q.mirrorRadius V) b η e := fun b e => by
    rw [hfun, ← bondPartialDeriv_eq_chartedSlope Q V η hS b e]
    unfold bondPartialDeriv
    have hd' : HasFDerivAt (fun ζ => Q.coupling * (Q.totalCost ζ V - Q.totalCost 0 V) -
        interpolatedExponent 1 Q.a Q.chartRadius Q.coupling Q.mirrorRadius V ζ) _ η := hd
    rw [hd'.fderiv]
    simp [smul_eq_mul]
  rw [slopeTerm_eq]
  have e1 : Q.gapTerm Y η V = Q.coupling * ColdHalfLaw.sumOverBlock Y (fun b =>
      chartedSlope Q.a (interpolatedCoords 1 Q.a Q.chartRadius Q.mirrorRadius V η) V b.1 (toImaginary (η b))) -
        Q.exponentRadialPart Y η V := by
    unfold ColdHalfLaw.gapTerm ColdHalfLaw.exponentRadialPart radialPart ColdHalfLaw.sumOverBlock
    simp_rw [hJ]
    rw [Finset.sum_filter, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun b _ => ?_
    split_ifs <;> simp
  rw [e1]
  ring
theorem gapMinusSlopeIsRadial_of_kernels (hK : interpolationKernelBoundsStatement)
    (hPS : interpolatedPartsSmoothStatement)
    (hJ : EventuallyInParametersCombines) : GapMinusSlopeIsRadial := by
  obtain ⟨join, weaken⟩ := hJ
  obtain ⟨Kf, Df, -, -, hKt⟩ := hK
  refine weaken _ _ ?_ (join _ _ hPS hKt)
  rintro T hDr ⟨hP, hKT⟩
  intro t x f F V Y η hst hη
  have hcl : ∀ b, ‖η b‖ ≤ T.ballRadius := fun b => (hη b).le
  have hK' := hKT x t F V 1 η hst.coupling_le hst.torus hst.small_curvature zero_le_one le_rfl hcl
  have hu : AreUnitVectors (Fin.elim0 : Fin 0 → imaginaryQuaternions) := fun i => i.elim0
  have hS : ContDiffAt ℝ 1 (fun ζ => interpolatedEnergy 1 T.a T.chainParams.ρA (frameRadius x) ζ V) η :=
    contDiffAt_one_of_displaced (interpolatedEnergy 1 T.a T.chainParams.ρA (frameRadius x)) V η fun l b u hl hu' =>
      (hK'.energy l 0 b u Fin.elim0 Fin.elim0 hl hu' hu).1
  have hPB := hP t x F V 1 hst.coupling_le hst.torus hst.small_curvature zero_le_one le_rfl
  have hsum : ContDiffAt ℝ 2 (fun ζ => ∑ z ∈ finiteCells F,
      interpolatedBlockExponent 1 T.a T.chainParams.ρA x (frameRadius x) z V ζ) η :=
    ContDiffAt.sum fun z _ => (contDiffAt_of_untranslated
      (fun ζ V' => interpolatedBlockExponent 1 T.a T.chainParams.ρA x (frameRadius x) z V' ζ) V η
      (hPB.smooth z η 0 Fin.elim0 Fin.elim0 hcl)).of_le (by norm_num)
  have hev : interpolatedExponent 1 T.a T.chainParams.ρA x (frameRadius x) V =ᶠ[nhds η]
      fun ζ => ∑ z ∈ finiteCells F, interpolatedBlockExponent 1 T.a T.chainParams.ρA x (frameRadius x) z V ζ := by
    filter_upwards [(isOpen_bondBalls T.ballRadius).mem_nhds hη] with ζ hζ
    exact hPB.sum_eq ζ hζ
  exact gapTerm_sub_slopeTerm (coldHalfLawAt T x f) Y V η (hS.differentiableAt (by norm_num))
    ((hsum.congr_of_eventuallyEq hev).differentiableAt (by norm_num))
end ResponseInTheExpansion
end YangMills.Construction
end
