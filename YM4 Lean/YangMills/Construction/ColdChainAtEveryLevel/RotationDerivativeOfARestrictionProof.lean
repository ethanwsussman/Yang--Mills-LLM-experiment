import YangMills.Construction.ColdChainAtEveryLevel.AnalyticSharesOfAColdTopProof
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion Topology
namespace YangMills.Construction.BlockAverages
namespace DerivAlongRotation
variable {F : BlockFrame}
section Calculus
variable {X Y G : Type} [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup Y]
  [NormedSpace ℝ Y] [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]
theorem iteratedFDeriv_comp_clm_of_analyticAt (L : X →L[ℝ] Y) {f : Y → G} {x : X} (hf : AnalyticAt ℝ f (L x)) (m : ℕ)
    (v : Fin m → X) : iteratedFDeriv ℝ m (f ∘ L) x v = iteratedFDeriv ℝ m f (L x) (fun l => L (v l)) := by
  have cf : ContDiffAt ℝ m f (L x) := hf.contDiffAt.of_le (by exact_mod_cast le_top)
  obtain ⟨s, hs, hx, hc⟩ : ∃ s : Set Y, IsOpen s ∧ L x ∈ s ∧ ContDiffOn ℝ m f s := by
    obtain ⟨u, hu, hc⟩ := cf.contDiffOn (m := m) le_rfl (by simp)
    obtain ⟨s, hsu, hs, hx⟩ := mem_nhds_iff.1 hu
    exact ⟨s, hs, hx, hc.mono (by simpa using hsu)⟩
  have hpre : IsOpen (L ⁻¹' s) := hs.preimage L.continuous
  have hL := L.iteratedFDerivWithin_comp_right hc hs.uniqueDiffOn hpre.uniqueDiffOn (x := x) hx (i := m) le_rfl
  rw [iteratedFDerivWithin_of_isOpen m hpre hx, iteratedFDerivWithin_of_isOpen m hs hx] at hL
  rw [hL]
  rfl
theorem iteratedFDeriv_succ_eq_iteratedFDeriv_fderiv_perm (m : ℕ) {f : (Fin (m + 1) → ℝ) → G} (hf : AnalyticAt ℝ f 0)
    (σ : Equiv.Perm (Fin (m + 1))) :
    iteratedFDeriv ℝ (m + 1) f 0 (fun l => Pi.single l 1) =
      iteratedFDeriv ℝ m (fun ζ => fderiv ℝ f ζ (Pi.single (σ (Fin.last m)) 1)) 0
        (fun l => Pi.single (σ l.castSucc) 1) := by apply _root_.YangMills.Construction.BlockAverages.AnalyticCellShares.iteratedFDeriv_succ_eq_fderiv_perm <;> assumption
end Calculus
section EvaluationMaps
variable {G : Type} [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G] {S : Finset F.Cell} {R : F.FieldChain}
  {z : F.Cell} {B : Finset (F.Site F.top × Fin 4)} {Ck : ℕ → ℝ} {U : ChainChart F}
  {Φ : ChainChart F → (F.Site F.top → Fin 4 → imaginaryQuaternions) → G}
  {e : F.Site F.top → Fin 4 → imaginaryQuaternions}
def zeroChart (F : BlockFrame) : ChainChart F := ⟨fun _ _ => 0, fun _ _ _ => 0⟩
theorem fderiv_eventuallyEq_derivAlongRotation {ι κ : Type} [Fintype ι] [Fintype κ] (h : IsLocalRepresentation S R z B Ck U Φ)
    (A : ι → ChainChart F) (e' : ι → F.Site F.top → Fin 4 → imaginaryQuaternions) (A' : κ → ChainChart F)
    (e'' : κ → F.Site F.top → Fin 4 → imaginaryQuaternions) (P : (ι → ℝ) →L[ℝ] (κ → ℝ)) (d : κ → ℝ)
    (h1 : ∀ (t : ι → ℝ) (τ : ℝ), chartShiftAlong U A' (P t + τ • d) = chartShiftAlong U A t)
    (h2 : ∀ (t : ι → ℝ) (τ : ℝ), topVariationAlong e'' (P t + τ • d) = fun y i => topVariationAlong e' t y i + τ • e y i) :
    (fun t : ι → ℝ => fderiv ℝ (fun x : κ → ℝ => Φ (chartShiftAlong U A' x) (topVariationAlong e'' x)) (P t) d) =ᶠ[𝓝 0]
      fun t => derivAlongRotation Φ e (chartShiftAlong U A t) (topVariationAlong e' t) := by
  have hH := h.analyticAt A' e''
  have hc : Filter.Tendsto P (𝓝 0) (𝓝 0) := by
    have := P.continuous.tendsto 0
    simpa using this
  filter_upwards [hc.eventually hH.eventually_analyticAt] with t ht
  have hd := ht.differentiableAt.lineDeriv_eq_fderiv (v := d)
  rw [← hd]
  unfold lineDeriv derivAlongRotation
  congr 1
  funext τ
  show Φ (chartShiftAlong U A' (P t + τ • d)) (topVariationAlong e'' (P t + τ • d)) = _
  rw [h1, h2]
end EvaluationMaps
end DerivAlongRotation
theorem localEvaluation_derivAlongRotation : localEvaluation_derivAlongRotationStatement := by
  classical
  open DerivAlongRotation in
  intro F G _ _ _ S R z B Ck U Φ e h
  refine ⟨fun U' U'' v hs => ?_, ?_, ?_⟩
  · unfold derivAlongRotation
    have : (fun τ : ℝ => Φ U' (fun y i => v y i + τ • e y i)) = fun τ : ℝ => Φ U'' (fun y i => v y i + τ • e y i) :=
      funext fun τ => h.congr_of_agree _ _ _ hs
    rw [this]
  · intro ι _ A e'
    let A' : Option ι → ChainChart F := fun o => o.elim (zeroChart F) A
    let e'' : Option ι → F.Site F.top → Fin 4 → imaginaryQuaternions := fun o => o.elim e e'
    let P : (ι → ℝ) →L[ℝ] (Option ι → ℝ) :=
      ContinuousLinearMap.pi fun o => o.elim 0 fun i => ContinuousLinearMap.proj i
    let d : Option ι → ℝ := Pi.single none 1
    have hP : ∀ t : ι → ℝ, ∀ τ : ℝ, ∀ o, (P t + τ • d) o = o.elim τ t := by
      intro t τ o
      cases o with
      | none => simp [P, d]
      | some i => simp [P, d]
    have h1 : ∀ (t : ι → ℝ) (τ : ℝ), chartShiftAlong U A' (P t + τ • d) = chartShiftAlong U A t := by
      intro t τ
      simp only [chartShiftAlong, Fintype.sum_option, hP, A', Option.elim, zeroChart, smul_zero, zero_add]
    have h2 : ∀ (t : ι → ℝ) (τ : ℝ), topVariationAlong e'' (P t + τ • d) = fun y i => topVariationAlong e' t y i + τ • e y i := by
      intro t τ
      funext y i
      simp only [topVariationAlong, Fintype.sum_option, hP, e'', Option.elim]
      rw [add_comm]
    have hH := h.analyticAt A' e''
    have hd : AnalyticAt ℝ (fun t : ι → ℝ =>
        fderiv ℝ (fun x : Option ι → ℝ => Φ (chartShiftAlong U A' x) (topVariationAlong e'' x)) (P t) d) 0 := by
      have a1 : AnalyticAt ℝ (fderiv ℝ fun x : Option ι → ℝ => Φ (chartShiftAlong U A' x) (topVariationAlong e'' x)) (P 0) := by
        rw [map_zero]
        exact hH.fderiv
      have a2 := a1.comp (P.analyticAt 0)
      exact (ContinuousLinearMap.apply ℝ G d).analyticAt _ |>.comp a2
    exact hd.congr (fderiv_eventuallyEq_derivAlongRotation h A e' A' e'' P d h1 h2)
  · intro m A e'
    let A' : Fin (m + 1) → ChainChart F := Fin.snoc (α := fun _ => ChainChart F) A (zeroChart F)
    let e'' : Fin (m + 1) → F.Site F.top → Fin 4 → imaginaryQuaternions :=
      Fin.snoc (α := fun _ => F.Site F.top → Fin 4 → imaginaryQuaternions) e' e
    let P : (Fin m → ℝ) →L[ℝ] (Fin (m + 1) → ℝ) :=
      ContinuousLinearMap.pi fun o => Fin.lastCases 0 (fun i => ContinuousLinearMap.proj i) o
    let d : Fin (m + 1) → ℝ := Pi.single (Fin.last m) 1
    have hPc : ∀ (t : Fin m → ℝ) (τ : ℝ) (l : Fin m), (P t + τ • d) l.castSucc = t l := by
      intro t τ l
      simp [P, d, Fin.castSucc_ne_last]
    have hPl : ∀ (t : Fin m → ℝ) (τ : ℝ), (P t + τ • d) (Fin.last m) = τ := by
      intro t τ
      simp [P, d]
    have h1 : ∀ (t : Fin m → ℝ) (τ : ℝ), chartShiftAlong U A' (P t + τ • d) = chartShiftAlong U A t := by
      intro t τ
      simp only [chartShiftAlong, Fin.sum_univ_castSucc, hPc, hPl, A', Fin.snoc_castSucc, Fin.snoc_last, zeroChart,
        smul_zero, add_zero]
    have h2 : ∀ (t : Fin m → ℝ) (τ : ℝ), topVariationAlong e'' (P t + τ • d) = fun y i => topVariationAlong e' t y i + τ • e y i := by
      intro t τ
      funext y i
      simp only [topVariationAlong, Fin.sum_univ_castSucc, hPc, hPl, e'', Fin.snoc_castSucc, Fin.snoc_last]
    have hH := h.analyticAt A' e''
    have hb := h.iteratedDeriv_le (m + 1) A' e''
    have hsplit := iteratedFDeriv_succ_eq_iteratedFDeriv_fderiv_perm m hH 1
    have e1 : localIteratedDeriv (derivAlongRotation Φ e) U A e' = localIteratedDeriv Φ U A' e'' := by
      unfold localIteratedDeriv
      rw [hsplit]
      simp only [Equiv.Perm.coe_one, id]
      have hG : AnalyticAt ℝ (fun ζ => fderiv ℝ (fun x : Fin (m + 1) → ℝ => Φ (chartShiftAlong U A' x) (topVariationAlong e'' x)) ζ
          (Pi.single (Fin.last m) 1)) (P 0) := by
        rw [map_zero]
        exact (ContinuousLinearMap.apply ℝ G d).analyticAt _ |>.comp hH.fderiv
      have hcomp := iteratedFDeriv_comp_clm_of_analyticAt P hG m (fun l => Pi.single l 1)
      have hPs : (fun l : Fin m => P (Pi.single l 1)) = fun l => Pi.single l.castSucc 1 := by
        funext l
        funext o
        induction o using Fin.lastCases with
        | last => simp [P, (Fin.castSucc_ne_last _).symm]
        | cast o => simp [P, Pi.single_apply]
      rw [hPs, map_zero] at hcomp
      rw [← hcomp]
      have hev := (Filter.EventuallyEq.iteratedFDeriv ℝ (fderiv_eventuallyEq_derivAlongRotation h A e' A' e'' P d h1 h2) m).self_of_nhds
      rw [← hev]
      rfl
    rw [e1]
    refine hb.trans (le_of_eq ?_)
    rw [Fin.prod_univ_castSucc]
    simp only [A', e'', Fin.snoc_castSucc, Fin.snoc_last]
    have e2 : localDirectionSize S R B z (zeroChart F) e = topVariationNorm B e := by
      have : localNorm S R (zeroChart F) (oneSiteWeights F) z = 0 := by
        simp [localNorm, localNormSq, zeroChart, linearizedCurl, adjointAction]
      simp [localDirectionSize, this]
    rw [e2]
    ring
end YangMills.Construction.BlockAverages
end
