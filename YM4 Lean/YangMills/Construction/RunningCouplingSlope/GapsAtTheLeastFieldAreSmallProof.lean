import YangMills.Construction.ClusterExpansionOfAStep.TopFieldOffTheHull
import YangMills.Construction.ClusterExpansionOfAStep.TopFrameOfATorus
import YangMills.Construction.ColdChainAtEveryLevel.FlatTopCostsNothing
import YangMills.Construction.ColdStepAtMirrorFrames.OneLeastChart
import YangMills.Construction.RunningCouplingSlope.CurvesOfFieldsAtOne
import YangMills.Construction.RunningCouplingSlope.GapsAtTheLeastFieldAreSmall
import YangMills.Construction.RunningCouplingSlope.GroupGapAgainstItsLogarithm
import YangMills.Construction.SummableBoundsOfTheFlow.CoordinatesAtTheFlatField
import YangMills.Construction.SummableBoundsOfTheFlow.GroupGapHasItsTail
import YangMills.Construction.SummableBoundsOfTheFlow.TheTailOfTheGapIsSmooth
import Mathlib
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
noncomputable section
open scoped Quaternion Topology ContDiff
namespace YangMills.Construction
open BlockAverages ColdStepAtMirrorFrames TorusFields
namespace RunningCouplingSlope
namespace HaarGapSecondDeriv
section Calculus
variable {E E' : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup E'] [NormedSpace ℝ E']
private abbrev Params : Type := Fin 2 → ℝ
private abbrev paramBasis (l : Fin 2) : Params := Pi.single l 1
private def dirDeriv (f : Params → E) (l : Fin 2) : E := fderiv ℝ f 0 (paramBasis l)
private def crossDeriv (f : Params → E) : E := iteratedFDeriv ℝ 2 f 0 (fun l => paramBasis l)
private theorem crossDeriv_eq (f : Params → E) :
    crossDeriv f = fderiv ℝ (fderiv ℝ f) 0 (paramBasis 0) (paramBasis 1) := by
  unfold crossDeriv
  rw [iteratedFDeriv_two_apply]
private theorem differentiableAt_of_two {G : E → E'} {x : E} (h : ContDiffAt ℝ 2 G x) : DifferentiableAt ℝ G x :=
  h.differentiableAt (by norm_num)
private theorem dirDeriv_comp {Φ : E → E'} {f : Params → E} (hΦ : ContDiffAt ℝ 2 Φ (f 0)) (hf : ContDiffAt ℝ 2 f 0)
    (l : Fin 2) : dirDeriv (fun τ => Φ (f τ)) l = fderiv ℝ Φ (f 0) (dirDeriv f l) := by
  unfold dirDeriv
  have h := (differentiableAt_of_two hΦ).hasFDerivAt.comp (0 : Params) (differentiableAt_of_two hf).hasFDerivAt
  have e : fderiv ℝ (fun τ => Φ (f τ)) 0 = (fderiv ℝ Φ (f 0)).comp (fderiv ℝ f 0) := h.fderiv
  rw [e]
  rfl
private theorem crossDeriv_comp {Φ : E → E'} {f : Params → E} (hΦ : ContDiffAt ℝ 2 Φ (f 0)) (hf : ContDiffAt ℝ 2 f 0) :
    crossDeriv (fun τ => Φ (f τ)) =
      fderiv ℝ (fderiv ℝ Φ) (f 0) (dirDeriv f 0) (dirDeriv f 1) + fderiv ℝ Φ (f 0) (crossDeriv f) := by
  have hΦ' : ∀ᶠ τ in 𝓝 (0 : Params), DifferentiableAt ℝ Φ (f τ) := by
    have h1 : ∀ᶠ y in 𝓝 (f 0), ContDiffAt ℝ 2 Φ y := hΦ.eventually (by simp)
    exact (hf.continuousAt.eventually h1).mono fun τ h => differentiableAt_of_two h
  have hf' : ∀ᶠ τ in 𝓝 (0 : Params), DifferentiableAt ℝ f τ :=
    (hf.eventually (by simp)).mono fun τ h => differentiableAt_of_two h
  have e : fderiv ℝ (fun τ => Φ (f τ)) =ᶠ[𝓝 0] fun τ => (fderiv ℝ Φ (f τ)).comp (fderiv ℝ f τ) := by
    filter_upwards [hΦ', hf'] with τ h1 h2
    exact (h1.hasFDerivAt.comp τ h2.hasFDerivAt).fderiv
  have hA : DifferentiableAt ℝ (fderiv ℝ Φ) (f 0) :=
    (hΦ.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hB : DifferentiableAt ℝ (fderiv ℝ f) 0 :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hA' : HasFDerivAt (fun τ => fderiv ℝ Φ (f τ)) ((fderiv ℝ (fderiv ℝ Φ) (f 0)).comp (fderiv ℝ f 0)) 0 :=
    hA.hasFDerivAt.comp (0 : Params) (differentiableAt_of_two hf).hasFDerivAt
  have hC := hA'.clm_comp hB.hasFDerivAt
  rw [crossDeriv_eq, e.fderiv_eq, hC.fderiv, crossDeriv_eq]
  simp only [dirDeriv, add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.compL_apply, ContinuousLinearMap.flip_apply]
  rw [add_comm]
private theorem dirDeriv_clm (A : E →L[ℝ] E') {f : Params → E} (hf : ContDiffAt ℝ 2 f 0) (l : Fin 2) :
    dirDeriv (fun τ => A (f τ)) l = A (dirDeriv f l) := by
  rw [dirDeriv_comp A.contDiff.contDiffAt hf, A.fderiv]
private theorem crossDeriv_clm (A : E →L[ℝ] E') {f : Params → E} (hf : ContDiffAt ℝ 2 f 0) :
    crossDeriv (fun τ => A (f τ)) = A (crossDeriv f) := by
  have h : fderiv ℝ (A : E → E') = fun _ => A := funext fun _ => A.fderiv
  rw [crossDeriv_comp A.contDiff.contDiffAt hf, h]
  simp
private structure C2Bounded (v : E) (K : ℝ) (f : Params → E) : Prop where
  contDiffAt : ContDiffAt ℝ 2 f 0
  apply_zero : f 0 = v
  dirDeriv_le : ∀ l, ‖dirDeriv f l‖ ≤ K
  crossDeriv_le : ‖crossDeriv f‖ ≤ K
private theorem C2Bounded.nonneg {v : E} {K : ℝ} {f : Params → E} (h : C2Bounded v K f) : 0 ≤ K :=
  le_trans (norm_nonneg _) h.crossDeriv_le
private theorem C2Bounded.mono {v : E} {K K' : ℝ} {f : Params → E} (h : C2Bounded v K f) (hK : K ≤ K') :
    C2Bounded v K' f :=
  ⟨h.contDiffAt, h.apply_zero, fun l => (h.dirDeriv_le l).trans hK, h.crossDeriv_le.trans hK⟩
private theorem C2Bounded.const (v : E) : C2Bounded v 0 (fun _ => v) := by
  refine ⟨contDiffAt_const, rfl, fun l => ?_, ?_⟩
  · simp [dirDeriv]
  · rw [crossDeriv_eq]
    simp
private theorem C2Bounded.clm (A : Params →L[ℝ] E) {K : ℝ} (hK : 0 ≤ K) (h : ∀ l, ‖A (paramBasis l)‖ ≤ K) :
    C2Bounded (0 : E) K (fun τ => A τ) := by
  have hd : fderiv ℝ (A : Params → E) = fun _ => A := funext fun _ => A.fderiv
  refine ⟨A.contDiff.contDiffAt, by simp, fun l => ?_, ?_⟩
  · simp only [dirDeriv]
    rw [A.fderiv]
    exact h l
  · rw [crossDeriv_eq]
    simpa [hd] using hK
private def chainRuleBound (Φ : E → E') (v : E) (K : ℝ) : ℝ :=
  ‖fderiv ℝ (fderiv ℝ Φ) v‖ * K ^ 2 + ‖fderiv ℝ Φ v‖ * K
private theorem C2Bounded.comp {Φ : E → E'} {v : E} {v' : E'} {K : ℝ} {f : Params → E} (h : C2Bounded v K f)
    (hΦ : ContDiffAt ℝ 2 Φ v) (hv' : Φ v = v') : C2Bounded v' (chainRuleBound Φ v K) (fun τ => Φ (f τ)) := by
  have hv := h.apply_zero
  have hΦ0 : ContDiffAt ℝ 2 Φ (f 0) := by rwa [hv]
  have hK := h.nonneg
  have hA := norm_nonneg (fderiv ℝ (fderiv ℝ Φ) v)
  have hB := norm_nonneg (fderiv ℝ Φ v)
  refine ⟨ContDiffAt.comp (0 : Params) hΦ0 h.contDiffAt, by simp [hv, hv'], fun l => ?_, ?_⟩
  · rw [dirDeriv_comp hΦ0 h.contDiffAt, hv]
    calc ‖fderiv ℝ Φ v (dirDeriv f l)‖ ≤ ‖fderiv ℝ Φ v‖ * ‖dirDeriv f l‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ ‖fderiv ℝ Φ v‖ * K := mul_le_mul_of_nonneg_left (h.dirDeriv_le l) hB
      _ ≤ chainRuleBound Φ v K := by
          unfold chainRuleBound
          have : 0 ≤ ‖fderiv ℝ (fderiv ℝ Φ) v‖ * K ^ 2 := by positivity
          linarith
  · rw [crossDeriv_comp hΦ0 h.contDiffAt, hv]
    have h0 := h.dirDeriv_le 0
    have h1 := h.dirDeriv_le 1
    have hm := h.crossDeriv_le
    calc _ ≤ ‖fderiv ℝ (fderiv ℝ Φ) v (dirDeriv f 0) (dirDeriv f 1)‖ + ‖fderiv ℝ Φ v (crossDeriv f)‖ := norm_add_le _ _
      _ ≤ ‖fderiv ℝ (fderiv ℝ Φ) v‖ * ‖dirDeriv f 0‖ * ‖dirDeriv f 1‖ + ‖fderiv ℝ Φ v‖ * ‖crossDeriv f‖ :=
          add_le_add (ContinuousLinearMap.le_opNorm₂ _ _ _) (ContinuousLinearMap.le_opNorm _ _)
      _ ≤ ‖fderiv ℝ (fderiv ℝ Φ) v‖ * K * K + ‖fderiv ℝ Φ v‖ * K := by
          refine add_le_add ?_ (mul_le_mul_of_nonneg_left hm hB)
          exact mul_le_mul (mul_le_mul_of_nonneg_left h0 hA) h1 (norm_nonneg _) (by positivity)
      _ = chainRuleBound Φ v K := by
          unfold chainRuleBound
          ring
private theorem C2Bounded.prod {u : E} {v : E'} {K : ℝ} {f : Params → E} {g : Params → E'} (hf : C2Bounded u K f)
    (hg : C2Bounded v K g) : C2Bounded (u, v) K (fun τ => (f τ, g τ)) := by
  have hs : ContDiffAt ℝ 2 (fun τ => (f τ, g τ)) 0 := hf.contDiffAt.prodMk hg.contDiffAt
  have h1 : ∀ l, (dirDeriv (fun τ => (f τ, g τ)) l).1 = dirDeriv f l := fun l =>
    (dirDeriv_clm (ContinuousLinearMap.fst ℝ E E') hs l).symm
  have h2 : ∀ l, (dirDeriv (fun τ => (f τ, g τ)) l).2 = dirDeriv g l := fun l =>
    (dirDeriv_clm (ContinuousLinearMap.snd ℝ E E') hs l).symm
  have h3 : (crossDeriv (fun τ => (f τ, g τ))).1 = crossDeriv f :=
    (crossDeriv_clm (ContinuousLinearMap.fst ℝ E E') hs).symm
  have h4 : (crossDeriv (fun τ => (f τ, g τ))).2 = crossDeriv g :=
    (crossDeriv_clm (ContinuousLinearMap.snd ℝ E E') hs).symm
  refine ⟨hs, by simp [hf.apply_zero, hg.apply_zero], fun l => ?_, ?_⟩
  · rw [Prod.norm_def, h1, h2]
    exact max_le (hf.dirDeriv_le l) (hg.dirDeriv_le l)
  · rw [Prod.norm_def, h3, h4]
    exact max_le hf.crossDeriv_le hg.crossDeriv_le
private theorem C2Bounded.add {u v : E} {K K' : ℝ} {f g : Params → E} (hf : C2Bounded u K f) (hg : C2Bounded v K' g) :
    C2Bounded (u + v) (K + K') (fun τ => f τ + g τ) := by
  have hK := hf.nonneg
  have hK' := hg.nonneg
  have hp : C2Bounded (u, v) (K + K') (fun τ => (f τ, g τ)) :=
    (hf.mono (by linarith)).prod (hg.mono (by linarith))
  have hs := hf.contDiffAt.add hg.contDiffAt
  set A : E × E →L[ℝ] E := ContinuousLinearMap.fst ℝ E E + ContinuousLinearMap.snd ℝ E E with hA
  have hfirst : ∀ l, dirDeriv (fun τ => f τ + g τ) l = dirDeriv f l + dirDeriv g l := fun l => by
    have h1 := dirDeriv_clm A hp.contDiffAt l
    have h2 := dirDeriv_clm (ContinuousLinearMap.fst ℝ E E) hp.contDiffAt l
    have h3 := dirDeriv_clm (ContinuousLinearMap.snd ℝ E E) hp.contDiffAt l
    simp only [hA, add_apply, ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd'] at h1 h2 h3
    rw [h1, ← h2, ← h3]
  have hmixed : crossDeriv (fun τ => f τ + g τ) = crossDeriv f + crossDeriv g := by
    have h1 := crossDeriv_clm A hp.contDiffAt
    have h2 := crossDeriv_clm (ContinuousLinearMap.fst ℝ E E) hp.contDiffAt
    have h3 := crossDeriv_clm (ContinuousLinearMap.snd ℝ E E) hp.contDiffAt
    simp only [hA, add_apply, ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd'] at h1 h2 h3
    rw [h1, ← h2, ← h3]
  refine ⟨hs, by simp [hf.apply_zero, hg.apply_zero], fun l => ?_, ?_⟩
  · rw [hfirst]
    exact (norm_add_le _ _).trans (add_le_add (hf.dirDeriv_le l) (hg.dirDeriv_le l))
  · rw [hmixed]
    exact (norm_add_le _ _).trans (add_le_add hf.crossDeriv_le hg.crossDeriv_le)
private theorem C2Bounded.sum {ι : Type} (S : Finset ι) {v : ι → E} {K : ι → ℝ} {f : ι → Params → E}
    (h : ∀ i ∈ S, C2Bounded (v i) (K i) (f i)) :
    C2Bounded (∑ i ∈ S, v i) (∑ i ∈ S, K i) (fun τ => ∑ i ∈ S, f i τ) := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa using C2Bounded.const (0 : E)
  | insert i S hi ih =>
    simp only [Finset.sum_insert hi]
    exact (h i (Finset.mem_insert_self _ _)).add (ih fun j hj => h j (Finset.mem_insert_of_mem hj))
private theorem C2Bounded.smul {v : E} {K : ℝ} {f : Params → E} (h : C2Bounded v K f) (c : ℝ) :
    C2Bounded (c • v) (|c| * K) (fun τ => c • f τ) := by
  set A : E →L[ℝ] E := c • ContinuousLinearMap.id ℝ E with hA
  have hs : ContDiffAt ℝ 2 (fun τ => A (f τ)) 0 := ContDiffAt.comp (0 : Params) A.contDiff.contDiffAt h.contDiffAt
  have e : (fun τ => c • f τ) = fun τ => A (f τ) := by
    funext τ
    simp [hA]
  have hn : ∀ u : E, ‖A u‖ = |c| * ‖u‖ := fun u => by
    simp [hA, norm_smul]
  rw [e]
  refine ⟨hs, by simp [hA, h.apply_zero], fun l => ?_, ?_⟩
  · rw [dirDeriv_clm A h.contDiffAt, hn]
    exact mul_le_mul_of_nonneg_left (h.dirDeriv_le l) (abs_nonneg _)
  · rw [crossDeriv_clm A h.contDiffAt, hn]
    exact mul_le_mul_of_nonneg_left h.crossDeriv_le (abs_nonneg _)
end Calculus
section Holonomy
private def quatMul (p : ℍ[ℝ] × ℍ[ℝ]) : ℍ[ℝ] := p.1 * p.2
private theorem contDiffAt_quatMul : ContDiffAt ℝ 2 quatMul ((1 : ℍ[ℝ]), (1 : ℍ[ℝ])) := contDiff_mul.contDiffAt
private theorem C2Bounded.mul {K : ℝ} {f g : Params → ℍ[ℝ]} (hf : C2Bounded (1 : ℍ[ℝ]) K f)
    (hg : C2Bounded (1 : ℍ[ℝ]) K g) :
    C2Bounded (1 : ℍ[ℝ]) (chainRuleBound quatMul ((1 : ℍ[ℝ]), (1 : ℍ[ℝ])) K) (fun τ => f τ * g τ) :=
  (hf.prod hg).comp contDiffAt_quatMul (by simp [quatMul])
private def quatConj (q : ℍ[ℝ]) : ℍ[ℝ] := star q
private theorem contDiffAt_quatConj : ContDiffAt ℝ 2 quatConj (1 : ℍ[ℝ]) :=
  (analyticAt_quat_star (analyticAt_id (𝕜 := ℝ) (z := (1 : ℍ[ℝ])))).contDiffAt
private theorem C2Bounded.conj {K : ℝ} {f : Params → ℍ[ℝ]} (h : C2Bounded (1 : ℍ[ℝ]) K f) :
    C2Bounded (1 : ℍ[ℝ]) (chainRuleBound quatConj (1 : ℍ[ℝ]) K) (fun τ => quatConj (f τ)) :=
  h.comp contDiffAt_quatConj (by simp [quatConj])
private def holonomyBound (K : ℝ) : List PathStep → ℝ
  | [] => 0
  | _ :: r => chainRuleBound quatMul ((1 : ℍ[ℝ]), (1 : ℍ[ℝ]))
      (max (K + chainRuleBound quatConj (1 : ℍ[ℝ]) K) (holonomyBound K r))
private def contourAverageBound (L : ℕ) (K : ℝ) : ℝ :=
  ∑ i : Fin 4, |1 / (24 * (L : ℝ) ^ 4)| *
    ∑ h ∈ centredCube L, ∑ π : Equiv.Perm (Fin 4), holonomyBound K (bondContour L h π i)
variable {F : BlockFrame} {j : ℕ} {Wc : Params → F.GaugeField j} {K : ℝ}
private theorem c2Bounded_linkValue
    (hW : ∀ x i, C2Bounded (1 : ℍ[ℝ]) K (fun τ => ((Wc τ x i : UnitQuaternion) : ℍ[ℝ])))
    (x : F.Site j) (st : PathStep) :
    C2Bounded (1 : ℍ[ℝ]) (K + chainRuleBound quatConj (1 : ℍ[ℝ]) K)
      (fun τ => ((linkValue (Wc τ) x st : UnitQuaternion) : ℍ[ℝ])) := by
  have hs : 0 ≤ chainRuleBound quatConj (1 : ℍ[ℝ]) K := (C2Bounded.conj (hW x st.1)).nonneg
  have hK := (hW x st.1).nonneg
  by_cases h : st.2 = true
  · simp only [linkValue, h, if_true]
    exact (hW x st.1).mono (by linarith)
  · simp only [linkValue, h]
    exact (C2Bounded.conj (hW (x - BlockAverages.unitStep j st.1) st.1)).mono (by linarith)
private theorem c2Bounded_pathHolonomy
    (hW : ∀ x i, C2Bounded (1 : ℍ[ℝ]) K (fun τ => ((Wc τ x i : UnitQuaternion) : ℍ[ℝ])))
    (l : List PathStep) :
    ∀ x, C2Bounded (1 : ℍ[ℝ]) (holonomyBound K l)
      (fun τ => ((pathHolonomy (Wc τ) x l : UnitQuaternion) : ℍ[ℝ])) := by
  induction l with
  | nil =>
    intro x
    exact C2Bounded.const (1 : ℍ[ℝ])
  | cons st r ih =>
    intro x
    have h1 := c2Bounded_linkValue hW x st
    have h2 := ih (x + stepDisplacement j st)
    exact (h1.mono (le_max_left _ (holonomyBound K r))).mul
      (h2.mono (le_max_right (K + chainRuleBound quatConj (1 : ℍ[ℝ]) K) _))
private theorem c2Bounded_contourAverage {Wc : Params → F.GaugeField j}
    (hW : ∀ x i, C2Bounded (1 : ℍ[ℝ]) K (fun τ => ((Wc τ x i : UnitQuaternion) : ℍ[ℝ])))
    (hL : Odd F.blockSide) (h0 : Wc 0 = trivialBlockField F j) (c : F.Site (j + 1) × Fin 4) :
    C2Bounded (1 : ℍ[ℝ]) (contourAverageBound F.blockSide K) (fun τ => contourAverage (Wc τ) c) := by
  have h1 : ∀ (h : Fin 4 → ℤ) (π : Equiv.Perm (Fin 4)),
      C2Bounded (1 : ℍ[ℝ]) (holonomyBound K (bondContour F.blockSide h π c.2))
        (fun τ => ((pathHolonomy (Wc τ) (refineSite c.1) (bondContour F.blockSide h π c.2) : UnitQuaternion) : ℍ[ℝ])) :=
    fun h π => c2Bounded_pathHolonomy hW _ _
  have h2 := (C2Bounded.sum (centredCube F.blockSide)
    (fun h _ => C2Bounded.sum Finset.univ (fun π _ => h1 h π))).smul (1 / (24 * (F.blockSide : ℝ) ^ 4))
  have hterm : ∀ i : Fin 4, 0 ≤ |1 / (24 * (F.blockSide : ℝ) ^ 4)| *
      ∑ h ∈ centredCube F.blockSide, ∑ π : Equiv.Perm (Fin 4), holonomyBound K (bondContour F.blockSide h π i) :=
    fun i => mul_nonneg (abs_nonneg _) (Finset.sum_nonneg fun h _ => Finset.sum_nonneg fun π _ =>
      (c2Bounded_pathHolonomy hW (bondContour F.blockSide h π i) (refineSite c.1)).nonneg)
  have h3 : C2Bounded _ (contourAverageBound F.blockSide K) _ := h2.mono (Finset.single_le_sum (f := fun i : Fin 4 =>
    |1 / (24 * (F.blockSide : ℝ) ^ 4)| *
      ∑ h ∈ centredCube F.blockSide, ∑ π : Equiv.Perm (Fin 4), holonomyBound K (bondContour F.blockSide h π i))
    (fun i _ => hterm i) (Finset.mem_univ c.2))
  refine ⟨h3.contDiffAt, ?_, h3.dirDeriv_le, h3.crossDeriv_le⟩
  show contourAverage (Wc 0) c = 1
  rw [h0]
  exact contourAverage_trivial hL c
end Holonomy
section Chain
variable {F : BlockFrame} {a ρ δ lam σA cg : ℝ} {N : ℕ → ℝ} {L t n : ℕ}
private theorem isCold_flatTopField {s : ℝ} (hs : 0 < s) (S : Finset F.Cell) :
    IsCold S F.top s (flatTopField : F.GaugeField F.top) := by
  intro p _
  simpa [plaquetteDefect, plaquetteHolonomy, pathHolonomy, linkValue, flatTopField] using hs
abbrev _root_.YangMills.SharedProofs.p30906 := @isCold_flatTopField
private theorem minimizingBondCoordinate_of_not_mem {S : Finset F.Cell} {b : F.Site F.depth × Fin 4}
    (hb : b ∉ chordBonds S) (V : F.GaugeField F.top) : minimizingBondCoordinate a ρ S b V = 0 := by
  unfold minimizingBondCoordinate minimizingCoordinates
  split_ifs with h
  · exact h.choose_spec.1 b hb
  · rfl
abbrev _root_.YangMills.SharedProofs.p70322 := @minimizingBondCoordinate_of_not_mem
private theorem hasRegularCoordinates_torus (hc : ColdChain.ColdChainConstants a δ L lam ρ σA cg N) {u m : ℕ}
    [NeZero m] (hm : 64 ≤ m) :
    HasRegularCoordinates a δ ρ N (finiteCells (torusFrame L u m)) flatTopField := by
  obtain ⟨_, _, _, _, _, hσ, _, _, hmain⟩ := hc
  have pos : ∀ i, 0 < (torusFrame L u m).extent i := fun _ => (show 0 < m by omega)
  exact (hmain (torusFrame L u m) 1024 (finiteCells _) rfl (Or.inr fun _ => hm) le_rfl
    (TopLevelSites.isOrthantRegular_finiteCells pos 1024) σA flatTopField hσ le_rfl
    (isCold_flatTopField hσ _)).2.2.2.1
private theorem hasColdMinimizer_of_cold (hc : ColdChain.ColdChainConstants a δ L lam ρ σA cg N) {F : BlockFrame}
    (hFL : F.blockSide = L) (hamb : IsAdmissibleAmbient F) (S : Finset F.Cell) (hS : ∀ z, z ∈ S) (s : ℝ)
    (hs : 0 < s) (hsA : s ≤ σA) (V : F.GaugeField F.top) (hV : IsCold S F.top s V) :
    HasColdMinimizer a ρ (N 0) s S V := by
  obtain ⟨-, -, -, -, -, -, -, -, h⟩ := hc
  have hreg : IsOrthantRegular S 1024 := fun z =>
    ⟨fun _ => 1, fun _ => Or.inl rfl, fun _ _ _ _ _ _ => hS _⟩
  exact (h F 1024 S hFL hamb le_rfl hreg s V hs hsA hV).1
private theorem isMinimizingChart_zero (hc : ColdChain.ColdChainConstants a δ L lam ρ σA cg N) (ha : 0 ≤ a)
    (hLodd : Odd L) (hFlat : flatTopVanishingStatement) (hOne : MinimizingChartUnique) {F : BlockFrame}
    (hFL : F.blockSide = L) (hside : ∀ i, 64 ≤ F.extent i) :
    IsMinimizingChart a (finiteCells F) (BlockAverages.flatField F F.top) ρ fun _ _ => 0 := by
  have hodd : Odd F.blockSide := hFL ▸ hLodd
  obtain ⟨-, -, -, hρ0, hρ1, hσ, -, hN, -⟩ := id hc
  have h2 : ∀ i, 2 ≤ F.extent i := fun i => le_trans (by norm_num) (hside i)
  have hall : ∀ z, z ∈ finiteCells F := BlockOffsets.mem_finiteCells h2
  have hfl := hFlat F a (finiteCells F) ha hodd
  have hch : ∀ s, 0 < s → s ≤ σA →
      HasColdMinimizer a ρ (N 0) s (finiteCells F) (BlockAverages.flatField F F.top) :=
    fun s hs hsA => hasColdMinimizer_of_cold hc hFL (Or.inr hside) _ hall s hs hsA _ (hfl.1 F.top s hs)
  have hwide : ∀ (w : F.Site F.depth → Fin 4 → imaginaryQuaternions) (r : ℝ),
      IsMinimizingChart a (finiteCells F) (BlockAverages.flatField F F.top) (min ρ r) w →
      IsMinimizingChart a (finiteCells F) (BlockAverages.flatField F F.top) ρ w := fun w r h =>
    ⟨h.1, fun b hb => le_trans (h.2.1 b hb) (min_le_left _ _), h.2.2⟩
  obtain ⟨w, hw, -, -⟩ := hch σA hσ le_rfl
  have hw' := hwide w _ hw
  have huniq := (hOne F a ρ (N 0) σA (BlockAverages.flatField F F.top) w hodd h2 hρ1 (hch σA hσ le_rfl) hw').1
  have hsmall : ∀ b ∈ chordBonds (finiteCells F), ∀ s, 0 < s → s ≤ σA → ‖w b.1 b.2‖ ≤ N 0 * s := by
    intro b hb s hs hsA
    obtain ⟨ws, hws, -, -⟩ := hch s hs hsA
    have e := huniq ws (hwide ws _ hws)
    rw [← e]
    exact le_trans (hws.2.1 b hb) (min_le_right _ _)
  have hz : w = fun _ _ => 0 := by
    funext x i
    by_cases hb : (x, i) ∈ chordBonds (finiteCells F)
    · by_contra hne
      have hp : 0 < ‖w x i‖ := norm_pos_iff.2 hne
      have hN0 := hN 0
      have hs : 0 < min σA (‖w x i‖ / (2 * N 0)) := lt_min hσ (by positivity)
      have h1 := hsmall (x, i) hb _ hs (min_le_left _ _)
      have h3 : N 0 * min σA (‖w x i‖ / (2 * N 0)) ≤ N 0 * (‖w x i‖ / (2 * N 0)) :=
        mul_le_mul_of_nonneg_left (min_le_right _ _) hN0.le
      have h4 : N 0 * (‖w x i‖ / (2 * N 0)) = ‖w x i‖ / 2 := by
        field_simp
      have h5 : ‖w x i‖ ≤ ‖w x i‖ / 2 := le_trans h1 (by rw [← h4]; exact h3)
      linarith
    · exact hw.1 (x, i) hb
  rw [← hz]
  exact hw'
private theorem minimizingCoordinates_flat (hc : ColdChain.ColdChainConstants a δ L lam ρ σA cg N) (ha : 0 ≤ a)
    (hLodd : Odd L) (hFlat : flatTopVanishingStatement) (hOne : MinimizingChartUnique) {u m : ℕ} (hm : 64 ≤ m) :
    minimizingCoordinates a (finiteCells (torusFrame L u m))
        (BlockAverages.flatField (torusFrame L u m) (torusFrame L u m).top) ρ =
      fun _ _ => 0 := by
  obtain ⟨-, -, -, hρ0, hρ1, hσ, -, hN, -⟩ := id hc
  have hside : ∀ i, 64 ≤ (torusFrame L u m).extent i := fun _ => hm
  have h2 : ∀ i, 2 ≤ (torusFrame L u m).extent i := fun i => le_trans (by norm_num) (hside i)
  have hodd : Odd (torusFrame L u m).blockSide := hLodd
  have hl := isMinimizingChart_zero hc ha hLodd hFlat hOne (F := torusFrame L u m) rfl hside
  have h1 := hasColdMinimizer_of_cold hc (F := torusFrame L u m) rfl (Or.inr hside) _
    (BlockOffsets.mem_finiteCells h2) σA hσ le_rfl
    (BlockAverages.flatField (torusFrame L u m) (torusFrame L u m).top)
    ((hFlat (torusFrame L u m) a (finiteCells _) ha hodd).1 _ σA hσ)
  have huniq := (hOne _ a ρ (N 0) σA _ _ hodd h2 hρ1 h1 hl).1
  have hex : ∃ w, IsMinimizingChart a (finiteCells (torusFrame L u m))
      (BlockAverages.flatField (torusFrame L u m) (torusFrame L u m).top) ρ w :=
    ⟨_, hl⟩
  unfold minimizingCoordinates
  rw [dif_pos hex]
  exact huniq _ hex.choose_spec
variable [NeZero n]
private abbrev perturbedTop (L t n : ℕ) {k : ℕ} (c : Fin k → TorusBond n) (X : Fin k → imaginaryQuaternions)
    (τ : Fin k → ℝ) : (torusFrame L t n).GaugeField (torusFrame L t n).top :=
  readAtLevel (torusFrame L t n) (torusFrame L t n).top (perturb c X τ (trivialField n))
private def frameBonds {k : ℕ} (L t : ℕ) (c : Fin k → TorusBond n) :
    Fin k → (torusFrame L t n).Site (torusFrame L t n).top × Fin 4 :=
  fun l => (StepCosts.torusSiteInFrame (torusFrame L t n) (torusFrame L t n).top (c l).1, (c l).2)
private theorem perturbedTop_eq {k : ℕ} (c : Fin k → TorusBond n) (X : Fin k → imaginaryQuaternions)
    (σ : Fin k → ℝ) :
    perturbedTop L t n c X σ = rotatedField (BlockAverages.bondSpread (frameBonds L t c) X σ) flatTopField := by
  funext x i
  have e : (∑ l, if c l = (TorusFrame.siteOfCell x, i) then σ l • X l else 0) =
      BlockAverages.bondSpread (frameBonds L t c) X σ x i := by
    unfold BlockAverages.bondSpread
    refine Finset.sum_congr rfl fun l _ => ?_
    have : c l = (TorusFrame.siteOfCell x, i) ↔ frameBonds L t c l = (x, i) := by
      constructor
      · intro h
        simp only [frameBonds, h, TorusFrame.torusSiteInFrame_siteOfCell]
      · intro h
        have h1 := congrArg Prod.fst h
        have h2 := congrArg Prod.snd h
        simp only [frameBonds] at h1 h2
        refine Prod.ext ?_ h2
        rw [← h1, TorusFrame.siteOfCell_torusSiteInFrame]
    simp only [this]
  show expUnit (∑ l, if c l = (TorusFrame.siteOfCell x, i) then σ l • X l else 0) * (1 : UnitQuaternion) = _
  rw [e]
  rfl
private theorem perturbedTop_zero {k : ℕ} (c : Fin k → TorusBond n) (X : Fin k → imaginaryQuaternions) :
    perturbedTop L t n c X 0 = BlockAverages.flatField (torusFrame L t n) (torusFrame L t n).top := by
  funext x i
  show perturb c X 0 (trivialField n) (TorusFrame.siteOfCell x) i = 1
  simp [perturb, trivialField, TorusFields.expUnit_zero]
private theorem perturb_single (c : Fin 2 → TorusBond n) (X : Fin 2 → imaginaryQuaternions) (l : Fin 2)
    (σ : Fin 1 → ℝ) :
    perturb ![c l] ![X l] σ (trivialField n) = perturb c X (σ 0 • paramBasis l) (trivialField n) := by
  funext x i
  unfold perturb
  congr 2
  rw [Fin.sum_univ_two]
  fin_cases l <;> simp
private theorem exp_neg_mul_le_one {d : ℝ} (hδ : 0 < δ) (hd : 0 ≤ d) : Real.exp (-δ * d) ≤ 1 := by
  rw [Real.exp_le_one_iff]
  nlinarith
private theorem c2Bounded_bondCoordinate (hc : ColdChain.ColdChainConstants a δ L lam ρ σA cg N) (hn : 64 ≤ n)
    (hz : minimizingCoordinates a (finiteCells (torusFrame L t n))
      (BlockAverages.flatField (torusFrame L t n) (torusFrame L t n).top) ρ = fun _ _ => 0)
    (c : Fin 2 → TorusBond n) {X : Fin 2 → imaginaryQuaternions} (hX : AreUnitVectors X)
    (b : (torusFrame L t n).Site (torusFrame L t n).depth × Fin 4) :
    C2Bounded (0 : imaginaryQuaternions) (N 1 + N 2)
      (fun τ => minimizingBondCoordinate a ρ (finiteCells (torusFrame L t n)) b (perturbedTop L t n c X τ)) := by
  have hδ : 0 < δ := hc.2.1 |> fun _ => hc.1
  have hN : ∀ k, 0 < N k := hc.2.2.2.2.2.2.2.1
  have h1 := hN 1
  have h2 := hN 2
  by_cases hb : b ∈ chordBonds (finiteCells (torusFrame L t n))
  swap
  · have e : (fun τ => minimizingBondCoordinate a ρ (finiteCells (torusFrame L t n)) b (perturbedTop L t n c X τ)) =
        fun _ => 0 :=
      funext fun τ => minimizingBondCoordinate_of_not_mem hb _
    rw [e]
    exact (C2Bounded.const (0 : imaginaryQuaternions)).mono (by positivity)
  obtain ⟨han, hbd⟩ := hasRegularCoordinates_torus (u := t) hc hn b hb
  set w : Params → imaginaryQuaternions :=
    fun τ => minimizingBondCoordinate a ρ (finiteCells (torusFrame L t n)) b (perturbedTop L t n c X τ) with hw
  have hwe : w = fun σ => minimizingBondCoordinate a ρ (finiteCells (torusFrame L t n)) b
      (rotatedField (BlockAverages.bondSpread (frameBonds L t c) X σ) flatTopField) :=
    funext fun σ => by simp only [hw, perturbedTop_eq]
  have hsm : ContDiffAt ℝ 2 w 0 := by
    rw [hwe]
    exact (han 2 _ X).contDiffAt
  refine ⟨hsm, ?_, fun l => ?_, ?_⟩
  · show minimizingBondCoordinate a ρ (finiteCells (torusFrame L t n)) b (perturbedTop L t n c X 0) = 0
    rw [perturbedTop_zero]
    unfold minimizingBondCoordinate
    rw [hz]
  · set ι : (Fin 1 → ℝ) →L[ℝ] Params := (ContinuousLinearMap.proj (0 : Fin 1)).smulRight (paramBasis l) with hι
    have e1 : (fun σ : Fin 1 → ℝ => minimizingBondCoordinate a ρ (finiteCells (torusFrame L t n)) b
        (rotatedField (BlockAverages.bondSpread (frameBonds L t ![c l]) ![X l] σ) flatTopField)) = fun σ => w (ι σ) := by
      funext σ
      rw [← perturbedTop_eq]
      simp only [hw]
      show minimizingBondCoordinate a ρ (finiteCells (torusFrame L t n)) b
        (readAtLevel _ _ (perturb ![c l] ![X l] σ (trivialField n))) = _
      rw [perturb_single]
      rfl
    have hu : AreUnitVectors ![X l] := fun m => by
      fin_cases m
      exact hX l
    have hb1 := hbd 1 (frameBonds L t ![c l]) ![X l] le_rfl hu
    unfold mixedBondDerivative at hb1
    rw [e1, iteratedFDeriv_one_apply] at hb1
    have hι0 : ι 0 = 0 := map_zero ι
    have hd : HasFDerivAt w (fderiv ℝ w 0) (ι 0) := by
      rw [hι0]
      exact (differentiableAt_of_two hsm).hasFDerivAt
    have hcomp : fderiv ℝ (fun σ => w (ι σ)) 0 = (fderiv ℝ w 0).comp ι :=
      (hd.comp (0 : Fin 1 → ℝ) ι.hasFDerivAt).fderiv
    rw [hcomp] at hb1
    have hs1 : ι (Pi.single 0 1) = paramBasis l := by
      simp [hι]
    simp only [ContinuousLinearMap.comp_apply, hs1] at hb1
    refine hb1.trans ?_
    have := exp_neg_mul_le_one (δ := δ)
      (d := (bondListDistance (enclosingCell b.1) (frameBonds L t ![c l]) : ℝ)) hδ (by positivity)
    nlinarith
  · have hb2 := hbd 2 (frameBonds L t c) X (by norm_num) hX
    have e2 : crossDeriv w = mixedBondDerivative (minimizingBondCoordinate a ρ (finiteCells (torusFrame L t n)) b)
        flatTopField (frameBonds L t c) X := by
      unfold crossDeriv mixedBondDerivative
      rw [hwe]
    rw [e2]
    refine hb2.trans ?_
    have := exp_neg_mul_le_one (δ := δ)
      (d := (bondListDistance (enclosingCell b.1) (frameBonds L t c) : ℝ)) hδ (by positivity)
    nlinarith
private def imagExp (w : imaginaryQuaternions) : ℍ[ℝ] := NormedSpace.exp (w : ℍ[ℝ])
private theorem contDiffAt_imagExp : ContDiffAt ℝ 2 imagExp (0 : imaginaryQuaternions) := by
  have h1 : ContDiffAt ℝ 2 (fun w : imaginaryQuaternions => (w : ℍ[ℝ])) 0 :=
    imaginaryQuaternions.subtypeL.contDiff.contDiffAt
  exact ContDiffAt.comp (g := (NormedSpace.exp : ℍ[ℝ] → ℍ[ℝ])) (0 : imaginaryQuaternions)
    (NormedSpace.exp_analytic (𝕂 := ℝ) _).contDiffAt h1
private theorem C2Bounded.exp {K : ℝ} {w : Params → imaginaryQuaternions}
    (h : C2Bounded (0 : imaginaryQuaternions) K w) :
    C2Bounded (1 : ℍ[ℝ]) (chainRuleBound imagExp (0 : imaginaryQuaternions) K)
      (fun τ => ((expUnit (w τ) : UnitQuaternion) : ℍ[ℝ])) :=
  h.comp contDiffAt_imagExp (by simp [imagExp])
private theorem c2Bounded_perturbedTop (c : Fin 2 → TorusBond n) {X : Fin 2 → imaginaryQuaternions}
    (hX : AreUnitVectors X) {K : ℝ} (hK : 1 ≤ K) (y : (torusFrame L t n).Cell) (i : Fin 4) :
    C2Bounded (1 : ℍ[ℝ]) (chainRuleBound imagExp (0 : imaginaryQuaternions) K)
      (fun τ => ((perturbedTop L t n c X τ y i : UnitQuaternion) : ℍ[ℝ])) := by
  set A : Params →L[ℝ] imaginaryQuaternions :=
    (ContinuousLinearMap.proj ((TorusFrame.siteOfCell y, i) : TorusBond n)).comp
      (FlatFieldJets.perturbationForm c X) with hA
  have e : (fun τ => ((perturbedTop L t n c X τ y i : UnitQuaternion) : ℍ[ℝ])) =
      fun τ => ((expUnit (A τ) : UnitQuaternion) : ℍ[ℝ]) := by
    funext τ
    have h1 : perturbedTop L t n c X τ y i = perturb c X τ (trivialField n) (TorusFrame.siteOfCell y) i := rfl
    rw [h1, FlatFieldJets.perturb_trivialField]
    rfl
  rw [e]
  refine C2Bounded.exp (C2Bounded.clm A (by linarith) fun l => ?_)
  simp only [hA, ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply,
    FlatFieldJets.perturbationForm_single]
  by_cases h : ((TorusFrame.siteOfCell y, i) : TorusBond n) = c l
  · rw [h, Pi.single_eq_same, hX l]
    exact hK
  · rw [Pi.single_eq_of_ne h, norm_zero]
    linarith
private theorem fieldAboveFrame_zero (V : (torusFrame L t n).GaugeField (torusFrame L t n).top) :
    fieldAboveFrame true a ρ 0 V 0 =
      chartedField (fun x i => minimizingBondCoordinate a ρ (finiteCells (torusFrame L t n)) (x, i) V) V := by
  unfold fieldAboveFrame
  congr 1
  funext x i
  show ColdStepAtMirrorFrames.stepFrame true a ρ 0 _ _ +
    stepCoordinates (0 : StepVariable (finiteCells (torusFrame L t n))) _ _ = _
  have e0 : stepCoordinates (0 : StepVariable (finiteCells (torusFrame L t n))) x i = 0 := by
    unfold stepCoordinates
    split_ifs
    · apply Subtype.ext
      simp [toImaginary]
      rfl
    · rfl
  rw [e0, add_zero]
  simp [ColdStepAtMirrorFrames.stepFrame]
private def chartedFieldBound (N : ℕ → ℝ) : ℝ :=
  chainRuleBound imagExp (0 : imaginaryQuaternions) (N 1 + N 2 + 1) +
    chainRuleBound quatMul ((1 : ℍ[ℝ]), (1 : ℍ[ℝ])) (chainRuleBound imagExp (0 : imaginaryQuaternions) (N 1 + N 2 + 1))
private theorem c2Bounded_chartedField (hc : ColdChain.ColdChainConstants a δ L lam ρ σA cg N) (hn : 64 ≤ n)
    (hz : minimizingCoordinates a (finiteCells (torusFrame L t n))
      (BlockAverages.flatField (torusFrame L t n) (torusFrame L t n).top) ρ = fun _ _ => 0)
    (c : Fin 2 → TorusBond n) {X : Fin 2 → imaginaryQuaternions} (hX : AreUnitVectors X)
    (x : (torusFrame L t n).Site (torusFrame L t n).depth) (i : Fin 4) :
    C2Bounded (1 : ℍ[ℝ]) (chartedFieldBound N)
      (fun τ => ((fieldAboveFrame true a ρ 0 (perturbedTop L t n c X τ) 0 x i : UnitQuaternion) : ℍ[ℝ])) := by
  have hN : ∀ k, 0 < N k := hc.2.2.2.2.2.2.2.1
  have h1 := hN 1
  have h2 := hN 2
  have hK : 1 ≤ N 1 + N 2 + 1 := by linarith
  have hw := C2Bounded.exp ((c2Bounded_bondCoordinate hc hn hz c hX (x, i)).mono (K' := N 1 + N 2 + 1) (by linarith))
  have hv := c2Bounded_perturbedTop (L := L) (t := t) c hX hK (enclosingCell x) i
  have hm := hw.mul hv
  have hk1 : 0 ≤ chainRuleBound imagExp (0 : imaginaryQuaternions) (N 1 + N 2 + 1) := hw.nonneg
  have hk2 : 0 ≤ chainRuleBound quatMul ((1 : ℍ[ℝ]), (1 : ℍ[ℝ]))
      (chainRuleBound imagExp (0 : imaginaryQuaternions) (N 1 + N 2 + 1)) := hm.nonneg
  simp only [fieldAboveFrame_zero]
  unfold chartedField
  by_cases hcr : IsCrossingBond (x, i)
  · simp only [if_pos hcr]
    exact hm.mono (by unfold chartedFieldBound; linarith)
  · simp only [if_neg hcr]
    by_cases htr : IsAxialTreeBond (x, i)
    · simp only [if_pos htr]
      exact (C2Bounded.const (1 : ℍ[ℝ])).mono (by unfold chartedFieldBound; linarith)
    · simp only [if_neg htr]
      exact hw.mono (by unfold chartedFieldBound; linarith)
private theorem c2Bounded_contourAverageNorm (hc : ColdChain.ColdChainConstants a δ L lam ρ σA cg N) (hodd : Odd L)
    (hn : 64 ≤ n)
    (hz : minimizingCoordinates a (finiteCells (torusFrame L t n))
      (BlockAverages.flatField (torusFrame L t n) (torusFrame L t n).top) ρ = fun _ _ => 0)
    (c : Fin 2 → TorusBond n) {X : Fin 2 → imaginaryQuaternions} (hX : AreUnitVectors X)
    (b : (torusFrame L t n).Site (torusFrame L t n).top × Fin 4) :
    C2Bounded (1 : ℝ) (chainRuleBound (norm : ℍ[ℝ] → ℝ) (1 : ℍ[ℝ]) (contourAverageBound L (chartedFieldBound N)))
      (fun τ => ‖contourAverage (fieldAboveFrame true a ρ 0 (perturbedTop L t n c X τ) 0) b‖) := by
  have hW := c2Bounded_chartedField hc hn hz c hX
  have h0 : fieldAboveFrame true a ρ 0 (perturbedTop L t n c X 0) 0 =
      trivialBlockField (torusFrame L t n) (torusFrame L t n).depth := by
    funext x i
    exact Subtype.ext (hW x i).apply_zero
  have hm : C2Bounded (1 : ℍ[ℝ]) (contourAverageBound L (chartedFieldBound N))
      (fun τ => contourAverage (fieldAboveFrame true a ρ 0 (perturbedTop L t n c X τ) 0) b) :=
    c2Bounded_contourAverage (F := torusFrame L t n)
      (Wc := fun τ => fieldAboveFrame true a ρ 0 (perturbedTop L t n c X τ) 0) hW hodd h0 b
  exact hm.comp (contDiffAt_norm ℝ one_ne_zero) norm_one
private theorem card_innerBonds_le (S : Finset (torusFrame L t n).Cell) :
    ((innerBonds S (torusFrame L t n).top).card : ℝ) ≤ 4 * (n : ℝ) ^ 4 := by
  have h : (innerBonds S (torusFrame L t n).top).card ≤ (Finset.univ : Finset (TorusBond n)).card := by
    refine Finset.card_le_card_of_injOn (fun b => (TorusFrame.siteOfCell b.1, b.2))
      (fun _ _ => Finset.mem_coe.2 (Finset.mem_univ _)) ?_
    intro b _ b' _ e
    have h1 := congrArg Prod.fst e
    have h2 := congrArg Prod.snd e
    exact Prod.ext (TorusFrame.siteOfCell_injective h1) h2
  have h2 : (Finset.univ : Finset (TorusBond n)).card = n ^ 4 * 4 := by
    simp [Finset.card_univ, ZMod.card]
  have h3 : ((innerBonds S (torusFrame L t n).top).card : ℝ) ≤ ((n ^ 4 * 4 : ℕ) : ℝ) := by
    exact_mod_cast h2 ▸ h
  push_cast at h3
  linarith
end Chain
section Gap
private theorem contDiffAt_haarGapSubLog (hG : ScaledVariables.HaarGapLogTail)
    (hS : ScaledVariables.HaarGapTailSmooth) {s : ℝ} (hs : 0 < s) :
    ContDiffAt ℝ 2 LaplaceAsymptotics.haarGapSubLog s := by
  obtain ⟨h, hsm, hpos, hlog⟩ := hS
  have hinv : 0 < s⁻¹ := inv_pos.2 hs
  have hsm2 : ContDiff ℝ 2 h := by simpa using contDiff_infty.1 hsm 2
  have hh : ContDiffAt ℝ 2 h s⁻¹ := hsm2.contDiffAt
  have hg : ContDiffAt ℝ 2 (fun u => -Real.log (h u)) s⁻¹ := (hh.log (hpos _ hinv.le).ne').neg
  have hc : ContDiffAt ℝ 2 (fun y : ℝ => -Real.log (h y⁻¹)) s :=
    ContDiffAt.comp (g := fun u => -Real.log (h u)) s hg (contDiffAt_inv ℝ hs.ne')
  refine hc.congr_of_eventuallyEq ?_
  filter_upwards [Ioi_mem_nhds hs] with y hy
  have hy0 : (0 : ℝ) < y := hy
  unfold LaplaceAsymptotics.haarGapSubLog
  rw [hG y hy0, hlog (1 / y) (by positivity)]
  simp
private theorem secondFDeriv_real {g : ℝ → ℝ} (s p q : ℝ) :
    fderiv ℝ (fderiv ℝ g) s p q = p * (q * iteratedDeriv 2 g s) := by
  have e : iteratedDeriv 2 g s = fderiv ℝ (fderiv ℝ g) s 1 1 := by
    rw [iteratedDeriv_eq_iteratedFDeriv, iteratedFDeriv_two_apply]
  rw [e]
  have hp : p = p • (1 : ℝ) := by simp
  have hq : q = q • (1 : ℝ) := by simp
  calc fderiv ℝ (fderiv ℝ g) s p q = fderiv ℝ (fderiv ℝ g) s (p • (1 : ℝ)) (q • (1 : ℝ)) := by rw [← hp, ← hq]
    _ = p * (q * fderiv ℝ (fderiv ℝ g) s 1 1) := by
      rw [map_smul, map_smul, smul_apply, smul_eq_mul, smul_eq_mul]
      ring
open LaplaceAsymptotics in
private theorem c2Bounded_haarGapSubLog {C s K : ℝ} {r : Params → ℝ} (hC : 0 < C) (hs : 0 < s)
    (hg : ContDiffAt ℝ 2 haarGapSubLog s) (h1 : |s * deriv haarGapSubLog s| ≤ C / s)
    (h2 : |s ^ 2 * iteratedDeriv 2 haarGapSubLog s| ≤ C / s) (hr : C2Bounded (1 : ℝ) K r) :
    C2Bounded (haarGapSubLog s) (C / s * (K ^ 2 + K)) (fun τ => haarGapSubLog (s * r τ)) := by
  have hK := hr.nonneg
  set A : ℝ →L[ℝ] ℝ := s • ContinuousLinearMap.id ℝ ℝ with hA
  have hAv : ∀ u, A u = s * u := fun u => by simp [hA]
  have hsm : ContDiffAt ℝ 2 (fun τ => A (r τ)) 0 := ContDiffAt.comp (0 : Params) A.contDiff.contDiffAt hr.contDiffAt
  have e0 : A (r 0) = s := by rw [hAv, hr.apply_zero, mul_one]
  have hf : (fun τ => haarGapSubLog (s * r τ)) = fun τ => haarGapSubLog (A (r τ)) := by
    funext τ
    rw [hAv]
  have hg0 : ContDiffAt ℝ 2 haarGapSubLog ((fun τ => A (r τ)) 0) := by
    show ContDiffAt ℝ 2 haarGapSubLog (A (r 0))
    rwa [e0]
  have hCs : 0 < C / s := by positivity
  rw [hf]
  refine ⟨ContDiffAt.comp (g := haarGapSubLog) (f := fun τ => A (r τ)) (0 : Params) hg0 hsm, by simp only [e0],
    fun l => ?_, ?_⟩
  · rw [dirDeriv_comp hg0 hsm]
    show ‖fderiv ℝ haarGapSubLog (A (r 0)) (dirDeriv (fun τ => A (r τ)) l)‖ ≤ _
    rw [e0, dirDeriv_clm A hr.contDiffAt, hAv, fderiv_eq_smul_deriv, smul_eq_mul, Real.norm_eq_abs]
    have e : s * dirDeriv r l * deriv haarGapSubLog s = dirDeriv r l * (s * deriv haarGapSubLog s) := by ring
    rw [e, abs_mul]
    have h3 : |dirDeriv r l| ≤ K := hr.dirDeriv_le l
    calc |dirDeriv r l| * |s * deriv haarGapSubLog s| ≤ K * (C / s) :=
          mul_le_mul h3 h1 (abs_nonneg _) hK
      _ ≤ C / s * (K ^ 2 + K) := by nlinarith [sq_nonneg K, mul_nonneg hCs.le (sq_nonneg K)]
  · rw [crossDeriv_comp hg0 hsm]
    show ‖fderiv ℝ (fderiv ℝ haarGapSubLog) (A (r 0)) (dirDeriv (fun τ => A (r τ)) 0)
        (dirDeriv (fun τ => A (r τ)) 1) +
      fderiv ℝ haarGapSubLog (A (r 0)) (crossDeriv (fun τ => A (r τ)))‖ ≤ _
    rw [e0, dirDeriv_clm A hr.contDiffAt, dirDeriv_clm A hr.contDiffAt, crossDeriv_clm A hr.contDiffAt, hAv, hAv, hAv,
      secondFDeriv_real, fderiv_eq_smul_deriv, smul_eq_mul, Real.norm_eq_abs]
    have e : s * dirDeriv r 0 * (s * dirDeriv r 1 * iteratedDeriv 2 haarGapSubLog s) +
        s * crossDeriv r * deriv haarGapSubLog s =
        dirDeriv r 0 * dirDeriv r 1 * (s ^ 2 * iteratedDeriv 2 haarGapSubLog s) +
          crossDeriv r * (s * deriv haarGapSubLog s) := by ring
    rw [e]
    have h3 : |dirDeriv r 0| ≤ K := hr.dirDeriv_le 0
    have h4 : |dirDeriv r 1| ≤ K := hr.dirDeriv_le 1
    have h5 : |crossDeriv r| ≤ K := hr.crossDeriv_le
    calc _ ≤ |dirDeriv r 0 * dirDeriv r 1 * (s ^ 2 * iteratedDeriv 2 haarGapSubLog s)| +
          |crossDeriv r * (s * deriv haarGapSubLog s)| := abs_add_le _ _
      _ = |dirDeriv r 0| * |dirDeriv r 1| * |s ^ 2 * iteratedDeriv 2 haarGapSubLog s| +
          |crossDeriv r| * |s * deriv haarGapSubLog s| := by
            rw [abs_mul (dirDeriv r 0 * dirDeriv r 1), abs_mul (dirDeriv r 0), abs_mul (crossDeriv r)]
      _ ≤ K * K * (C / s) + K * (C / s) := by
          refine add_le_add ?_ (mul_le_mul h5 h1 (abs_nonneg _) hK)
          exact mul_le_mul (mul_le_mul h3 h4 (abs_nonneg _) hK) h2 (abs_nonneg _) (by positivity)
      _ = C / s * (K ^ 2 + K) := by ring
end Gap
end HaarGapSecondDeriv
open HaarGapSecondDeriv LaplaceAsymptotics in
theorem haarGapSumSecondDerivStatement_holds (hLog : HaarGapSubLogDerivBounds)
    (hG : ScaledVariables.HaarGapLogTail) (hS : ScaledVariables.HaarGapTailSmooth)
    (hFlat : flatTopVanishingStatement) (hOne : MinimizingChartUnique) :
    haarGapSumSecondDerivStatement := by
  intro T hT
  obtain ⟨C0, hC0, hg⟩ := hLog
  set K : ℝ := chainRuleBound (norm : ℍ[ℝ] → ℝ) (1 : ℍ[ℝ]) (contourAverageBound T.side (chartedFieldBound T.N)) with hKdef
  set K' : ℝ := K ^ 2 + |K| with hK'
  have hK'0 : 0 ≤ K' := by positivity
  refine ⟨4 * C0 * K' + 1, 4, by positivity, by norm_num, ?_⟩
  intro y R hy hR n _ c X hn hX
  have hL : R.params.side = T.side := by rw [hR.params_eq]; rfl
  have ha : R.params.coupling = T.coupling := by rw [hR.params_eq]; rfl
  have hc : ColdChain.ColdChainConstants R.params.coupling T.δ₁ R.params.side T.lam R.anchorRadius T.σA T.cg T.N := by
    rw [ha, hL, hR.anchorRadius_eq]
    exact hT.chain
  have hodd : Odd R.params.side := hL ▸ hT.L_odd
  have ha1 : 1 ≤ R.params.coupling := ha ▸ hT.a_ge
  have hn64 : 64 ≤ n := by
    have := hT.n₀_ge
    omega
  have hx1 : 1 ≤ R.coupling := by
    have h1 : (1 : ℝ) ≤ T.floorMin := by
      unfold RenormalizationStepParameters.ParameterAssignment.floorMin
      refine le_trans ?_ (le_max_right _ _)
      exact one_le_pow₀ (by norm_num)
    exact h1.trans (hy.trans hR.le_coupling)
  have hx0 : 0 < R.coupling := by linarith
  set s : ℝ := R.params.coupling * R.coupling with hs
  have hs1 : 1 ≤ s := by nlinarith
  have hs0 : 0 < s := by linarith
  have hz := minimizingCoordinates_flat hc (by linarith) hodd hFlat hOne (u := R.depth) hn64
  obtain ⟨hg1, hg2⟩ := hg s hs1
  have hgs := contDiffAt_haarGapSubLog hG hS hs0
  have hterm : ∀ b ∈ innerBonds (finiteCells (torusFrame R.params.side R.depth n)) (torusFrame R.params.side R.depth n).top,
      C2Bounded (haarGapSubLog s) (C0 / s * K')
        (fun τ => haarGapSubLog (s * contourAverageNorm R n c X b τ)) := by
    intro b _
    have hl := c2Bounded_contourAverageNorm (a := R.params.coupling) (ρ := R.anchorRadius) (t := R.depth)
      hc hodd hn64 hz c hX b
    have hm : contourAverageBound R.params.side (chartedFieldBound T.N) =
        contourAverageBound T.side (chartedFieldBound T.N) := by rw [hL]
    rw [hm] at hl
    have h := c2Bounded_haarGapSubLog hC0 hs0 hgs hg1 hg2 hl
    refine h.mono ?_
    have hK0 := le_abs_self K
    exact mul_le_mul_of_nonneg_left (by rw [hK']; linarith) (by positivity)
  have hsum := C2Bounded.sum _ hterm
  have hgaps : haarGapSumAlongCurve R n c X = fun τ =>
      ∑ b ∈ innerBonds (finiteCells (torusFrame R.params.side R.depth n)) (torusFrame R.params.side R.depth n).top,
        haarGapSubLog (s * contourAverageNorm R n c X b τ) := rfl
  rw [hgaps]
  refine ⟨hsum.contDiffAt, ?_⟩
  have hb := hsum.crossDeriv_le
  rw [Finset.sum_const, nsmul_eq_mul] at hb
  have hcard := card_innerBonds_le (L := R.params.side) (t := R.depth) (n := n)
    (finiteCells (torusFrame R.params.side R.depth n))
  have hsx : C0 / s ≤ C0 * R.coupling⁻¹ := by
    rw [div_eq_mul_inv]
    refine mul_le_mul_of_nonneg_left ?_ hC0.le
    exact inv_anti₀ hx0 (by nlinarith)
  have hpow : (n : ℝ) ^ (4 : ℝ) = (n : ℝ) ^ 4 := by
    rw [show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  rw [← Real.norm_eq_abs, hpow]
  refine hb.trans ?_
  calc _ ≤ (4 * (n : ℝ) ^ 4) * (C0 * R.coupling⁻¹ * K') :=
        mul_le_mul hcard (mul_le_mul_of_nonneg_right hsx hK'0) (by positivity) (by positivity)
    _ ≤ (4 * C0 * K' + 1) * (n : ℝ) ^ 4 * R.coupling⁻¹ := by
        have : 0 ≤ (n : ℝ) ^ 4 * R.coupling⁻¹ := by positivity
        nlinarith
end RunningCouplingSlope
end YangMills.Construction
end
