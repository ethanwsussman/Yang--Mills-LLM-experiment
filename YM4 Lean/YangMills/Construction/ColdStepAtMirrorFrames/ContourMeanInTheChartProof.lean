import YangMills.Construction.ClusterExpansionOfAStep.MovesAlongLinearDirections
import YangMills.Construction.ClusterExpansionOfAStep.TreesOfABlock
import YangMills.Construction.ColdChainAtEveryLevel.HolonomiesOnTheHullOfABond
import YangMills.Construction.ColdStepAtMirrorFrames.ContourMeanInTheChart
import YangMills.Construction.SummableBoundsOfTheFlow.MoveOfTheTopAlongItsFieldProof
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction
open BlockAverages
namespace ColdStepAtMirrorFrames.ChartedContourAverage
section DerivativeBounds
variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
private structure DerivBoundsAt (A B : ℝ) (f : P → ℍ[ℝ]) (p : P) : Prop where
  smooth : ContDiff ℝ 3 f
  first : ∀ u, ‖fderiv ℝ f p u‖ ≤ A * ‖u‖
  second : ∀ u v, ‖fderiv ℝ (fun z => fderiv ℝ f z u) p v‖ ≤ B * ‖u‖ * ‖v‖
private theorem differentiable_of_contDiff_three {f : P → ℍ[ℝ]} (h : ContDiff ℝ 3 f) : Differentiable ℝ f :=
  h.differentiable (by norm_num)
private theorem contDiff_fderiv_apply {f : P → ℍ[ℝ]} (h : ContDiff ℝ 3 f) (u : P) :
    ContDiff ℝ 2 (fun z => fderiv ℝ f z u) :=
  (h.fderiv_right (m := 2) (by norm_num)).clm_apply contDiff_const
private theorem differentiable_fderiv_apply {f : P → ℍ[ℝ]} (h : ContDiff ℝ 3 f) (u : P) :
    Differentiable ℝ (fun z => fderiv ℝ f z u) :=
  (contDiff_fderiv_apply h u).differentiable (by norm_num)
private theorem DerivBoundsAt.mono {A B A' B' : ℝ} {f : P → ℍ[ℝ]} {p : P} (h : DerivBoundsAt A B f p)
    (hA : A ≤ A') (hB : B ≤ B') : DerivBoundsAt A' B' f p :=
  ⟨h.smooth, fun u => (h.first u).trans (mul_le_mul_of_nonneg_right hA (norm_nonneg _)),
    fun u v => (h.second u v).trans (by
      have := norm_nonneg u
      have := norm_nonneg v
      gcongr)⟩
private theorem fderiv_quat_mul_apply {f g : P → ℍ[ℝ]} (hf : Differentiable ℝ f) (hg : Differentiable ℝ g)
    (z u : P) :
    fderiv ℝ (fun y => f y * g y) z u = f z * fderiv ℝ g z u + fderiv ℝ f z u * g z := by
  have h := ((hf z).hasFDerivAt.mul' (hg z).hasFDerivAt).fderiv
  have e : (fun y => f y * g y) = f * g := rfl
  rw [e, h]
  simp
private theorem DerivBoundsAt.const (c : ℍ[ℝ]) (p : P) : DerivBoundsAt 0 0 (fun _ => c) p := by
  refine ⟨contDiff_const, fun u => by simp, fun u v => ?_⟩
  simp
private theorem DerivBoundsAt.mul {A B A' B' : ℝ} {f g : P → ℍ[ℝ]} {p : P} (hf : DerivBoundsAt A B f p)
    (hg : DerivBoundsAt A' B' g p) (hfp : ‖f p‖ ≤ 1) (hgp : ‖g p‖ ≤ 1) :
    DerivBoundsAt (A + A') (B + B' + 2 * (A * A')) (fun z => f z * g z) p := by
  have df := differentiable_of_contDiff_three hf.smooth
  have dg := differentiable_of_contDiff_three hg.smooth
  refine ⟨hf.smooth.mul hg.smooth, fun u => ?_, fun u v => ?_⟩
  · rw [fderiv_quat_mul_apply df dg]
    have h1 := hf.first u
    have h2 := hg.first u
    calc _ ≤ ‖f p * fderiv ℝ g p u‖ + ‖fderiv ℝ f p u * g p‖ := norm_add_le _ _
      _ ≤ ‖f p‖ * ‖fderiv ℝ g p u‖ + ‖fderiv ℝ f p u‖ * ‖g p‖ := by
        gcongr <;> exact norm_mul_le _ _
      _ ≤ 1 * (A' * ‖u‖) + (A * ‖u‖) * 1 := by
        have : 0 ≤ A * ‖u‖ := (norm_nonneg _).trans h1
        gcongr
      _ = (A + A') * ‖u‖ := by ring
  · have e : (fun z => fderiv ℝ (fun y => f y * g y) z u) =
        fun z => f z * fderiv ℝ g z u + fderiv ℝ f z u * g z := by
      funext z
      exact fderiv_quat_mul_apply df dg z u
    rw [e]
    have d2f := differentiable_fderiv_apply hf.smooth u
    have d2g := differentiable_fderiv_apply hg.smooth u
    have e2 : fderiv ℝ (fun z => f z * fderiv ℝ g z u + fderiv ℝ f z u * g z) p v =
        (f p * fderiv ℝ (fun z => fderiv ℝ g z u) p v + fderiv ℝ f p v * fderiv ℝ g p u) +
          (fderiv ℝ f p u * fderiv ℝ g p v + fderiv ℝ (fun z => fderiv ℝ f z u) p v * g p) := by
      have a1 : DifferentiableAt ℝ (fun z => f z * fderiv ℝ g z u) p := (df p).mul (d2g p)
      have a2 : DifferentiableAt ℝ (fun z => fderiv ℝ f z u * g z) p := (d2f p).mul (dg p)
      rw [fderiv_fun_add a1 a2]
      simp only [add_apply]
      rw [fderiv_quat_mul_apply df d2g, fderiv_quat_mul_apply d2f dg]
    rw [e2]
    have h1 := hf.first u
    have h2 := hg.first u
    have h3 := hf.first v
    have h4 := hg.first v
    have h5 := hf.second u v
    have h6 := hg.second u v
    have nu := norm_nonneg u
    have nv := norm_nonneg v
    have hA : 0 ≤ A * ‖v‖ := (norm_nonneg _).trans h3
    have hA2 : 0 ≤ A * ‖u‖ := (norm_nonneg _).trans h1
    have hB : 0 ≤ A' * ‖u‖ := (norm_nonneg _).trans h2
    have hB2 : 0 ≤ A' * ‖v‖ := (norm_nonneg _).trans h4
    have t1 : ‖f p * fderiv ℝ (fun z => fderiv ℝ g z u) p v‖ ≤ B' * ‖u‖ * ‖v‖ :=
      (norm_mul_le _ _).trans (by
        calc _ ≤ 1 * (B' * ‖u‖ * ‖v‖) := by gcongr
          _ = _ := one_mul _)
    have t2 : ‖fderiv ℝ f p v * fderiv ℝ g p u‖ ≤ (A * ‖v‖) * (A' * ‖u‖) :=
      (norm_mul_le _ _).trans (by gcongr)
    have t3 : ‖fderiv ℝ f p u * fderiv ℝ g p v‖ ≤ (A * ‖u‖) * (A' * ‖v‖) :=
      (norm_mul_le _ _).trans (by gcongr)
    have t4 : ‖fderiv ℝ (fun z => fderiv ℝ f z u) p v * g p‖ ≤ B * ‖u‖ * ‖v‖ :=
      (norm_mul_le _ _).trans (by
        calc _ ≤ (B * ‖u‖ * ‖v‖) * 1 := by
              have : 0 ≤ B * ‖u‖ * ‖v‖ := (norm_nonneg _).trans h5
              gcongr
          _ = _ := mul_one _)
    calc _ ≤ (‖f p * fderiv ℝ (fun z => fderiv ℝ g z u) p v‖ + ‖fderiv ℝ f p v * fderiv ℝ g p u‖) +
          (‖fderiv ℝ f p u * fderiv ℝ g p v‖ + ‖fderiv ℝ (fun z => fderiv ℝ f z u) p v * g p‖) :=
          (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) (norm_add_le _ _))
      _ ≤ _ := by nlinarith
private theorem DerivBoundsAt.comp_isometry {A B : ℝ} {f : P → ℍ[ℝ]} {p : P} (T : ℍ[ℝ] →L[ℝ] ℍ[ℝ])
    (hT : ∀ y, ‖T y‖ = ‖y‖) (hf : DerivBoundsAt A B f p) : DerivBoundsAt A B (fun z => T (f z)) p := by
  have df := differentiable_of_contDiff_three hf.smooth
  have e1 : ∀ z u, fderiv ℝ (fun y => T (f y)) z u = T (fderiv ℝ f z u) := fun z u => by
    have h := (T.hasFDerivAt.comp z (df z).hasFDerivAt).fderiv
    have e : (fun y => T (f y)) = T ∘ f := rfl
    rw [e, h]
    rfl
  refine ⟨T.contDiff.comp hf.smooth, fun u => ?_, fun u v => ?_⟩
  · rw [e1, hT]
    exact hf.first u
  · have e2 : (fun z => fderiv ℝ (fun y => T (f y)) z u) = fun z => T (fderiv ℝ f z u) := by
      funext z
      exact e1 z u
    have h := (T.hasFDerivAt.comp p (differentiable_fderiv_apply hf.smooth u p).hasFDerivAt).fderiv
    have e3 : (fun z => T (fderiv ℝ f z u)) = T ∘ (fun z => fderiv ℝ f z u) := rfl
    rw [e2, e3, h]
    change ‖T _‖ ≤ _
    rw [hT]
    exact hf.second u v
private theorem DerivBoundsAt.add {A B A' B' : ℝ} {f g : P → ℍ[ℝ]} {p : P} (hf : DerivBoundsAt A B f p)
    (hg : DerivBoundsAt A' B' g p) : DerivBoundsAt (A + A') (B + B') (fun z => f z + g z) p := by
  have df := differentiable_of_contDiff_three hf.smooth
  have dg := differentiable_of_contDiff_three hg.smooth
  have e1 : ∀ z u, fderiv ℝ (fun y => f y + g y) z u = fderiv ℝ f z u + fderiv ℝ g z u := fun z u => by
    rw [fderiv_fun_add (df z) (dg z)]
    rfl
  refine ⟨hf.smooth.add hg.smooth, fun u => ?_, fun u v => ?_⟩
  · rw [e1]
    have := hf.first u
    have := hg.first u
    calc _ ≤ ‖fderiv ℝ f p u‖ + ‖fderiv ℝ g p u‖ := norm_add_le _ _
      _ ≤ _ := by linarith
  · have e2 : (fun z => fderiv ℝ (fun y => f y + g y) z u) = fun z => fderiv ℝ f z u + fderiv ℝ g z u := by
      funext z
      exact e1 z u
    rw [e2, fderiv_fun_add (differentiable_fderiv_apply hf.smooth u p)
      (differentiable_fderiv_apply hg.smooth u p)]
    have := hf.second u v
    have := hg.second u v
    calc _ ≤ ‖fderiv ℝ (fun z => fderiv ℝ f z u) p v‖ + ‖fderiv ℝ (fun z => fderiv ℝ g z u) p v‖ :=
          norm_add_le _ _
      _ ≤ _ := by linarith
private theorem DerivBoundsAt.smul {A B : ℝ} {f : P → ℍ[ℝ]} {p : P} (c : ℝ) (hc : 0 ≤ c)
    (hf : DerivBoundsAt A B f p) : DerivBoundsAt (c * A) (c * B) (fun z => c • f z) p := by
  have df := differentiable_of_contDiff_three hf.smooth
  have e1 : ∀ z u, fderiv ℝ (fun y => c • f y) z u = c • fderiv ℝ f z u := fun z u => by
    rw [fderiv_fun_const_smul (df z)]
    rfl
  refine ⟨hf.smooth.const_smul c, fun u => ?_, fun u v => ?_⟩
  · rw [e1, norm_smul, Real.norm_of_nonneg hc, mul_assoc]
    exact mul_le_mul_of_nonneg_left (hf.first u) hc
  · have e2 : (fun z => fderiv ℝ (fun y => c • f y) z u) = fun z => c • fderiv ℝ f z u := by
      funext z
      exact e1 z u
    rw [e2, fderiv_fun_const_smul (differentiable_fderiv_apply hf.smooth u p), smul_apply, norm_smul,
      Real.norm_of_nonneg hc, mul_assoc, mul_assoc]
    have := mul_le_mul_of_nonneg_left (hf.second u v) hc
    rw [mul_assoc] at this
    exact this
private theorem DerivBoundsAt.sum {α : Type} (s : Finset α) {A B : ℝ} {f : α → P → ℍ[ℝ]} {p : P}
    (hf : ∀ a ∈ s, DerivBoundsAt A B (f a) p) :
    DerivBoundsAt (s.card * A) (s.card * B) (fun z => ∑ a ∈ s, f a z) p := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simpa using DerivBoundsAt.const (P := P) 0 p
  | insert a s ha ih =>
    have h1 := (hf a (Finset.mem_insert_self _ _)).add (ih fun b hb => hf b (Finset.mem_insert_of_mem hb))
    have e : (fun z => ∑ b ∈ insert a s, f b z) = fun z => f a z + ∑ b ∈ s, f b z := by
      funext z
      exact Finset.sum_insert ha
    rw [e, Finset.card_insert_of_notMem ha]
    push_cast
    have e1 : ((s.card : ℝ) + 1) * A = A + s.card * A := by ring
    have e2 : ((s.card : ℝ) + 1) * B = B + s.card * B := by ring
    rw [e1, e2]
    exact h1
private def quatExp : ℍ[ℝ] → ℍ[ℝ] := fun y => NormedSpace.exp y
private theorem contDiff_quatExp : ContDiff ℝ 3 quatExp := by
  refine contDiff_iff_contDiffAt.2 fun y => ?_
  exact (NormedSpace.exp_analytic (𝕂 := ℝ) y).contDiffAt
private theorem fderiv_bounds_on_unitBall {Q R : Type} [NormedAddCommGroup Q] [NormedSpace ℝ Q]
    [ProperSpace Q] [NormedAddCommGroup R] [NormedSpace ℝ R] {G : Q → R} (hG : ContDiff ℝ 3 G) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y : Q, ‖y‖ ≤ 1 → ∀ e e' : Q,
      ‖fderiv ℝ G y e‖ ≤ C * ‖e‖ ∧ ‖fderiv ℝ (fun z => fderiv ℝ G z e) y e'‖ ≤ C * ‖e‖ * ‖e'‖ := by
  have h1 : ContDiff ℝ 2 (fderiv ℝ G) := hG.fderiv_right (m := 2) (by norm_num)
  have h2 : ContDiff ℝ 1 (fderiv ℝ (fderiv ℝ G)) := h1.fderiv_right (m := 1) (by norm_num)
  have K : IsCompact (Metric.closedBall (0 : Q) 1) := isCompact_closedBall 0 1
  obtain ⟨C₁, hC₁⟩ := K.exists_bound_of_continuousOn (f := fderiv ℝ G) h1.continuous.continuousOn
  obtain ⟨C₂, hC₂⟩ := K.exists_bound_of_continuousOn (f := fderiv ℝ (fderiv ℝ G)) h2.continuous.continuousOn
  refine ⟨max (max C₁ C₂) 0, le_max_right _ _, fun y hy e e' => ?_⟩
  have hy' : y ∈ Metric.closedBall (0 : Q) 1 := by simpa using hy
  have a1 : ‖fderiv ℝ G y‖ ≤ max (max C₁ C₂) 0 :=
    (hC₁ y hy').trans ((le_max_left _ _).trans (le_max_left _ _))
  have a2 : ‖fderiv ℝ (fderiv ℝ G) y‖ ≤ max (max C₁ C₂) 0 :=
    (hC₂ y hy').trans ((le_max_right _ _).trans (le_max_left _ _))
  refine ⟨((fderiv ℝ G y).le_opNorm e).trans (mul_le_mul_of_nonneg_right a1 (norm_nonneg _)), ?_⟩
  have d1 : Differentiable ℝ (fderiv ℝ G) := h1.differentiable (by norm_num)
  have e1 : fderiv ℝ (fun z => fderiv ℝ G z e) y e' = fderiv ℝ (fderiv ℝ G) y e' e := by
    have h := ((d1 y).hasFDerivAt.clm_apply (hasFDerivAt_const e y)).fderiv
    rw [h]
    simp
  rw [e1]
  calc _ ≤ ‖fderiv ℝ (fderiv ℝ G) y e'‖ * ‖e‖ := ContinuousLinearMap.le_opNorm _ _
    _ ≤ (‖fderiv ℝ (fderiv ℝ G) y‖ * ‖e'‖) * ‖e‖ := by
      gcongr
      exact ContinuousLinearMap.le_opNorm _ _
    _ ≤ (max (max C₁ C₂) 0 * ‖e'‖) * ‖e‖ := by gcongr
    _ = _ := by ring
private theorem quatExp_fderiv_bounds : ∃ C : ℝ, 0 ≤ C ∧ ∀ y : ℍ[ℝ], ‖y‖ ≤ 1 → ∀ e e' : ℍ[ℝ],
    ‖fderiv ℝ quatExp y e‖ ≤ C * ‖e‖ ∧
      ‖fderiv ℝ (fun z => fderiv ℝ quatExp z e) y e'‖ ≤ C * ‖e‖ * ‖e'‖ :=
  fderiv_bounds_on_unitBall contDiff_quatExp
private theorem DerivBoundsAt.quatExp_affine {C : ℝ}
    (hC : ∀ y : ℍ[ℝ], ‖y‖ ≤ 1 → ∀ e e' : ℍ[ℝ],
      ‖fderiv ℝ quatExp y e‖ ≤ C * ‖e‖ ∧
        ‖fderiv ℝ (fun z => fderiv ℝ quatExp z e) y e'‖ ≤ C * ‖e‖ * ‖e'‖)
    (hC0 : 0 ≤ C) (a : ℍ[ℝ]) (Λ : P →L[ℝ] ℍ[ℝ]) (hΛ : ∀ u, ‖Λ u‖ ≤ ‖u‖) (p : P)
    (hp : ‖a + Λ p‖ ≤ 1) : DerivBoundsAt C C (fun z => quatExp (a + Λ z)) p := by
  have dE : Differentiable ℝ quatExp := differentiable_of_contDiff_three contDiff_quatExp
  have hg : ∀ z, HasFDerivAt (fun y => a + Λ y) Λ z := fun z => (Λ.hasFDerivAt).const_add a
  have e1 : ∀ z u, fderiv ℝ (fun y => quatExp (a + Λ y)) z u = fderiv ℝ quatExp (a + Λ z) (Λ u) :=
    fun z u => by
      have h := ((dE (a + Λ z)).hasFDerivAt.comp z (hg z)).fderiv
      have e : (fun y => quatExp (a + Λ y)) = quatExp ∘ fun y => a + Λ y := rfl
      rw [e, h]
      rfl
  refine ⟨contDiff_quatExp.comp (contDiff_const.add Λ.contDiff), fun u => ?_, fun u v => ?_⟩
  · rw [e1]
    exact ((hC _ hp (Λ u) 0).1).trans (mul_le_mul_of_nonneg_left (hΛ u) hC0)
  · have e2 : (fun z => fderiv ℝ (fun y => quatExp (a + Λ y)) z u) =
        (fun y => fderiv ℝ quatExp y (Λ u)) ∘ fun y => a + Λ y := by
      funext z
      exact e1 z u
    have d2 : DifferentiableAt ℝ (fun y => fderiv ℝ quatExp y (Λ u)) (a + Λ p) :=
      differentiable_fderiv_apply contDiff_quatExp (Λ u) _
    have h := (d2.hasFDerivAt.comp p (hg p)).fderiv
    rw [e2, h]
    change ‖fderiv ℝ (fun y => fderiv ℝ quatExp y (Λ u)) (a + Λ p) (Λ v)‖ ≤ _
    refine ((hC _ hp (Λ u) (Λ v)).2).trans ?_
    have := hΛ u
    have := hΛ v
    gcongr
end DerivativeBounds
section Chart
variable {F : BlockFrame}
private theorem toImaginary_add (u v : EuclideanSpace ℝ (Fin 3)) :
    toImaginary (u + v) = toImaginary u + toImaginary v := by apply _root_.YangMills.Construction.Interpolation.TopVariation.toImaginary_add <;> assumption
private theorem toImaginary_smul (c : ℝ) (v : EuclideanSpace ℝ (Fin 3)) :
    toImaginary (c • v) = c • toImaginary v := by apply _root_.YangMills.Construction.Interpolation.TopVariation.toImaginary_smul <;> assumption
private theorem norm_toImaginary (v : EuclideanSpace ℝ (Fin 3)) :
    ‖((toImaginary v : imaginaryQuaternions) : ℍ[ℝ])‖ = ‖v‖ := by apply _root_.YangMills.Construction.BlockTrees.norm_toImaginary <;> assumption
private def imaginaryEmbedding : EuclideanSpace ℝ (Fin 3) →L[ℝ] ℍ[ℝ] :=
  LinearMap.toContinuousLinearMap
    { toFun := fun v => ((toImaginary v : imaginaryQuaternions) : ℍ[ℝ])
      map_add' := fun u v => by rw [toImaginary_add]; rfl
      map_smul' := fun c v => by rw [toImaginary_smul]; rfl }
private theorem imaginaryEmbedding_apply (v : EuclideanSpace ℝ (Fin 3)) :
    imaginaryEmbedding v = ((toImaginary v : imaginaryQuaternions) : ℍ[ℝ]) := rfl
open Classical in
private def bondCoordinate (x : F.Site F.depth) (i : Fin 4) : StepVariable (finiteCells F) →L[ℝ] ℍ[ℝ] :=
  if h : (x, i) ∈ chordBonds (finiteCells F) then
    imaginaryEmbedding.comp (ContinuousLinearMap.proj (⟨(x, i), h⟩ : ↥(chordBonds (finiteCells F))))
  else 0
private theorem coe_stepCoordinates (ζ : StepVariable (finiteCells F)) (x : F.Site F.depth) (i : Fin 4) :
    ((stepCoordinates ζ x i : imaginaryQuaternions) : ℍ[ℝ]) = bondCoordinate x i ζ := by
  classical
  by_cases h : (x, i) ∈ chordBonds (finiteCells F)
  · simp only [stepCoordinates, bondCoordinate, dif_pos h]
    rfl
  · simp only [stepCoordinates, bondCoordinate, dif_neg h]
    rfl
private theorem norm_bondCoordinate_le (u : StepVariable (finiteCells F)) (x : F.Site F.depth) (i : Fin 4) :
    ‖bondCoordinate x i u‖ ≤ ‖u‖ := by
  classical
  by_cases h : (x, i) ∈ chordBonds (finiteCells F)
  · simp only [bondCoordinate, dif_pos h]
    change ‖imaginaryEmbedding (u ⟨(x, i), h⟩)‖ ≤ _
    rw [imaginaryEmbedding_apply, norm_toImaginary]
    exact norm_le_pi_norm u _
  · simp only [bondCoordinate, dif_neg h]
    simp
private theorem mem_chordBonds_of_not_tree (hL : Odd F.blockSide) (hs : ∀ i, 2 ≤ F.extent i)
    (x : F.Site F.depth) (i : Fin 4) (ht : ¬ IsAxialTreeBond (x, i)) :
    (x, i) ∈ chordBonds (finiteCells F) := by apply _root_.YangMills.Construction.LinearDirections.mem_chordBonds_finiteCells <;> assumption
private theorem coe_expUnit (v : imaginaryQuaternions) :
    ((expUnit v : UnitQuaternion) : ℍ[ℝ]) = quatExp (v : ℍ[ℝ]) := rfl
private abbrev perturbedField (w : F.Site F.depth → Fin 4 → imaginaryQuaternions) (V : F.GaugeField F.top)
    (ζ : StepVariable (finiteCells F)) : F.GaugeField F.depth :=
  chartedField (fun x i => w x i + stepCoordinates ζ x i) V
private theorem derivBoundsAt_bond {C : ℝ}
    (hC : ∀ y : ℍ[ℝ], ‖y‖ ≤ 1 → ∀ e e' : ℍ[ℝ],
      ‖fderiv ℝ quatExp y e‖ ≤ C * ‖e‖ ∧
        ‖fderiv ℝ (fun z => fderiv ℝ quatExp z e) y e'‖ ≤ C * ‖e‖ * ‖e'‖)
    (hC0 : 0 ≤ C) (hL : Odd F.blockSide) (hs : ∀ i, 2 ≤ F.extent i)
    (w : F.Site F.depth → Fin 4 → imaginaryQuaternions) (V : F.GaugeField F.top)
    (p : StepVariable (finiteCells F))
    (hp : ∀ b ∈ chordBonds (finiteCells F), ‖w b.1 b.2 + stepCoordinates p b.1 b.2‖ ≤ 1)
    (x : F.Site F.depth) (i : Fin 4) :
    DerivBoundsAt C C (fun ζ => ((perturbedField w V ζ x i : UnitQuaternion) : ℍ[ℝ])) p := by
  have e0 : ∀ ζ : StepVariable (finiteCells F),
      ((expUnit (w x i + stepCoordinates ζ x i) : UnitQuaternion) : ℍ[ℝ]) =
        quatExp ((w x i : ℍ[ℝ]) + bondCoordinate x i ζ) := fun ζ => by
    rw [coe_expUnit, ← coe_stepCoordinates]
    rfl
  have key : ¬ IsAxialTreeBond (x, i) →
      DerivBoundsAt C C (fun ζ => quatExp ((w x i : ℍ[ℝ]) + bondCoordinate x i ζ)) p := fun ht =>
    DerivBoundsAt.quatExp_affine hC hC0 _ _ (fun u => norm_bondCoordinate_le u x i) p (by
      rw [← coe_stepCoordinates]
      exact hp (x, i) (mem_chordBonds_of_not_tree hL hs x i ht))
  by_cases hc : IsCrossingBond (x, i)
  · have hk := key (fun ht => ht.1 hc)
    have h1 := hk.mul (DerivBoundsAt.const ((V (enclosingCell x) i : UnitQuaternion) : ℍ[ℝ]) p)
      (by rw [← e0]; exact (BlockOffsets.norm_coe_unitQuaternion _).le)
      (BlockOffsets.norm_coe_unitQuaternion _).le
    have e : (fun ζ => ((perturbedField w V ζ x i : UnitQuaternion) : ℍ[ℝ])) =
        fun ζ => quatExp ((w x i : ℍ[ℝ]) + bondCoordinate x i ζ) *
          ((V (enclosingCell x) i : UnitQuaternion) : ℍ[ℝ]) := by
      funext ζ
      simp only [perturbedField, chartedField, if_pos hc]
      rw [← e0]
      rfl
    rw [e]
    exact h1.mono (by simp) (by simp)
  · by_cases ht : IsAxialTreeBond (x, i)
    · have e : (fun ζ => ((perturbedField w V ζ x i : UnitQuaternion) : ℍ[ℝ])) = fun _ => (1 : ℍ[ℝ]) := by
        funext ζ
        simp only [perturbedField, chartedField, if_neg hc, if_pos ht]
        rfl
      rw [e]
      exact (DerivBoundsAt.const 1 p).mono hC0 hC0
    · have e : (fun ζ => ((perturbedField w V ζ x i : UnitQuaternion) : ℍ[ℝ])) =
          fun ζ => quatExp ((w x i : ℍ[ℝ]) + bondCoordinate x i ζ) := by
        funext ζ
        simp only [perturbedField, chartedField, if_neg hc, if_neg ht]
        exact e0 ζ
      rw [e]
      exact key ht
private def quatConj : ℍ[ℝ] →L[ℝ] ℍ[ℝ] :=
  LinearMap.toContinuousLinearMap
    { toFun := fun y => star y
      map_add' := fun u v => star_add u v
      map_smul' := fun c v => by
        refine Quaternion.ext _ _ ?_ ?_ ?_ ?_ <;> simp }
private theorem quatConj_apply (y : ℍ[ℝ]) : quatConj y = star y := rfl
private theorem derivBoundsAt_linkValue {C : ℝ}
    (hC : ∀ y : ℍ[ℝ], ‖y‖ ≤ 1 → ∀ e e' : ℍ[ℝ],
      ‖fderiv ℝ quatExp y e‖ ≤ C * ‖e‖ ∧
        ‖fderiv ℝ (fun z => fderiv ℝ quatExp z e) y e'‖ ≤ C * ‖e‖ * ‖e'‖)
    (hC0 : 0 ≤ C) (hL : Odd F.blockSide) (hs : ∀ i, 2 ≤ F.extent i)
    (w : F.Site F.depth → Fin 4 → imaginaryQuaternions) (V : F.GaugeField F.top)
    (p : StepVariable (finiteCells F))
    (hp : ∀ b ∈ chordBonds (finiteCells F), ‖w b.1 b.2 + stepCoordinates p b.1 b.2‖ ≤ 1)
    (x : F.Site F.depth) (st : PathStep) :
    DerivBoundsAt C C (fun ζ => ((linkValue (perturbedField w V ζ) x st : UnitQuaternion) : ℍ[ℝ])) p := by
  rcases st with ⟨i, b⟩
  cases b
  · have h := (derivBoundsAt_bond hC hC0 hL hs w V p hp (x - unitStep F.depth i) i).comp_isometry quatConj
      (fun y => by rw [quatConj_apply, Quaternion.norm_star])
    have e : (fun ζ => ((linkValue (perturbedField w V ζ) x (i, false) : UnitQuaternion) : ℍ[ℝ])) =
        fun ζ => quatConj ((perturbedField w V ζ (x - unitStep F.depth i) i : UnitQuaternion) : ℍ[ℝ]) := by
      funext ζ
      simp only [linkValue, Bool.false_eq_true, if_false]
      rfl
    rw [e]
    exact h
  · have e : (fun ζ => ((linkValue (perturbedField w V ζ) x (i, true) : UnitQuaternion) : ℍ[ℝ])) =
        fun ζ => ((perturbedField w V ζ x i : UnitQuaternion) : ℍ[ℝ]) := by
      funext ζ
      simp only [linkValue, if_true]
    rw [e]
    exact derivBoundsAt_bond hC hC0 hL hs w V p hp x i
private theorem derivBoundsAt_pathHolonomy {C : ℝ}
    (hC : ∀ y : ℍ[ℝ], ‖y‖ ≤ 1 → ∀ e e' : ℍ[ℝ],
      ‖fderiv ℝ quatExp y e‖ ≤ C * ‖e‖ ∧
        ‖fderiv ℝ (fun z => fderiv ℝ quatExp z e) y e'‖ ≤ C * ‖e‖ * ‖e'‖)
    (hC0 : 0 ≤ C) (hL : Odd F.blockSide) (hs : ∀ i, 2 ≤ F.extent i)
    (w : F.Site F.depth → Fin 4 → imaginaryQuaternions) (V : F.GaugeField F.top)
    (p : StepVariable (finiteCells F))
    (hp : ∀ b ∈ chordBonds (finiteCells F), ‖w b.1 b.2 + stepCoordinates p b.1 b.2‖ ≤ 1)
    (l : List PathStep) :
    ∀ x : F.Site F.depth, DerivBoundsAt (l.length * C) (l.length * C + (l.length : ℝ) ^ 2 * C ^ 2)
      (fun ζ => ((pathHolonomy (perturbedField w V ζ) x l : UnitQuaternion) : ℍ[ℝ])) p := by
  induction l with
  | nil =>
    intro x
    have e : (fun ζ => ((pathHolonomy (perturbedField w V ζ) x [] : UnitQuaternion) : ℍ[ℝ])) =
        fun _ => (1 : ℍ[ℝ]) := by
      funext ζ
      rfl
    rw [e]
    exact (DerivBoundsAt.const 1 p).mono (by simp) (by simp)
  | cons st r ih =>
    intro x
    have h1 := (derivBoundsAt_linkValue hC hC0 hL hs w V p hp x st).mul
      (ih (x + stepDisplacement F.depth st))
      (BlockOffsets.norm_coe_unitQuaternion _).le (BlockOffsets.norm_coe_unitQuaternion _).le
    have e : (fun ζ => ((pathHolonomy (perturbedField w V ζ) x (st :: r) : UnitQuaternion) : ℍ[ℝ])) =
        fun ζ => ((linkValue (perturbedField w V ζ) x st : UnitQuaternion) : ℍ[ℝ]) *
          ((pathHolonomy (perturbedField w V ζ) (x + stepDisplacement F.depth st) r : UnitQuaternion) :
            ℍ[ℝ]) := by
      funext ζ
      simp only [pathHolonomy]
      rfl
    rw [e]
    refine h1.mono ?_ ?_
    · rw [List.length_cons]
      push_cast
      linarith
    · rw [List.length_cons]
      push_cast
      nlinarith [sq_nonneg C]
private theorem length_bondContour_le_five_mul {L : ℕ} {h : Fin 4 → ℤ} (hh : h ∈ centredCube L)
    (π : Equiv.Perm (Fin 4)) (i : Fin 4) :
    ((bondContour L h π i).length : ℝ) ≤ 5 * L := by
  have h1 := BondHull.length_axisPath_le hh π
  have e : ((bondContour L h π i).length : ℝ) = 2 * (axisPath h π).length + L := by
    simp only [bondContour, reversePath, List.length_append, List.length_replicate, List.length_map,
      List.length_reverse]
    push_cast
    ring
  rw [e]
  linarith
theorem chartedContourAverageSmooth : ChartedContourAverageSmooth := by
  intro L hL
  obtain ⟨C, hC0, hC⟩ := quatExp_fderiv_bounds
  set A : ℝ := 5 * L * C with hA
  set B : ℝ := 5 * L * C + (5 * L) ^ 2 * C ^ 2 with hB
  set n : ℝ := (1 / (24 * (L : ℝ) ^ 4)) *
    (((centredCube L).card : ℝ) * (Fintype.card (Equiv.Perm (Fin 4)) : ℝ)) with hn
  refine ⟨n * A + n * B + 1, by positivity, fun F w V c p hF hs hp => ?_⟩
  have hLF : Odd F.blockSide := by rw [hF]; exact hL
  have hterm : ∀ h ∈ centredCube L, ∀ π : Equiv.Perm (Fin 4), DerivBoundsAt A B
      (fun ζ => ((pathHolonomy (perturbedField w V ζ) (_root_.YangMills.Construction.BlockAverages.refineSite c.1) (bondContour L h π c.2) :
        UnitQuaternion) : ℍ[ℝ])) p := by
    intro h hh π
    have hl := length_bondContour_le_five_mul hh π c.2
    refine (derivBoundsAt_pathHolonomy hC hC0 hLF hs w V p hp _ _).mono ?_ ?_
    · exact mul_le_mul_of_nonneg_right hl hC0
    · have := mul_le_mul_of_nonneg_right hl hC0
      have h2 : ((bondContour L h π c.2).length : ℝ) ^ 2 ≤ (5 * L) ^ 2 := by gcongr
      have := mul_le_mul_of_nonneg_right h2 (sq_nonneg C)
      rw [hB]
      linarith
  have hsum : DerivBoundsAt (n * A) (n * B) (chartedContourAverage w V c) p := by
    have h1 : DerivBoundsAt
        (((centredCube L).card : ℝ) * ((Finset.univ : Finset (Equiv.Perm (Fin 4))).card * A))
        (((centredCube L).card : ℝ) * ((Finset.univ : Finset (Equiv.Perm (Fin 4))).card * B))
        (fun ζ => ∑ h ∈ centredCube L, ∑ π : Equiv.Perm (Fin 4),
          ((pathHolonomy (perturbedField w V ζ) (refineSite c.1) (bondContour L h π c.2) :
            UnitQuaternion) : ℍ[ℝ])) p :=
      DerivBoundsAt.sum _ fun h hh => DerivBoundsAt.sum _ fun π _ => hterm h hh π
    have h2 := h1.smul (1 / (24 * (L : ℝ) ^ 4)) (by positivity)
    have e : chartedContourAverage w V c = fun ζ => (1 / (24 * (L : ℝ) ^ 4)) •
        ∑ h ∈ centredCube L, ∑ π : Equiv.Perm (Fin 4),
          ((pathHolonomy (perturbedField w V ζ) (refineSite c.1) (bondContour L h π c.2) :
            UnitQuaternion) : ℍ[ℝ]) := by
      funext ζ
      unfold chartedContourAverage _root_.YangMills.Construction.BlockAverages.contourAverage
      rw [hF]
    rw [e]
    refine h2.mono ?_ ?_
    · rw [hn, Finset.card_univ]
      exact le_of_eq (by ring)
    · rw [hn, Finset.card_univ]
      exact le_of_eq (by ring)
  refine ⟨hsum.smooth, fun u v => ⟨?_, ?_⟩⟩
  · refine (hsum.first u).trans ?_
    have : 0 ≤ n * B := by positivity
    exact mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _)
  · refine (hsum.second u v).trans ?_
    have : 0 ≤ n * A := by positivity
    have h3 : n * B ≤ n * A + n * B + 1 := by linarith
    gcongr
end Chart
end ColdStepAtMirrorFrames.ChartedContourAverage
end YangMills.Construction
end
