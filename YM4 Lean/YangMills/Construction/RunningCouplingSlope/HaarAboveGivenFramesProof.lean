import YangMills.Construction.ColdStepAtMirrorFrames.GapOfANormNearOneProof
import YangMills.Construction.Matrices.HaarExpChartDensityProof
import YangMills.Construction.RunningCouplingSlope.EnergyAtTheLeastFieldHasKernelsProof
import YangMills.Construction.RunningCouplingSlope.HaarAboveGivenFrames
import YangMills.Construction.RunningCouplingSlope.HaarDensityAtTheLeastFieldHasKernelsProof
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion Topology
namespace YangMills.Construction
open ColdStepAtMirrorFrames Interpolation Filter
open BlockAverages hiding bondSpread
namespace RunningCouplingSlope
namespace HaarLogRatio
section haar
private abbrev topOrder : WithTop ℕ∞ := ((⊤ : ℕ∞) : WithTop ℕ∞)
private theorem natCast_le_topOrder (j : ℕ) : (j : WithTop ℕ∞) ≤ topOrder := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.NormNearOne.natCast_le_smoothTop <;> assumption
private def sincCoeff (n : ℕ) : ℝ := (-1) ^ n / ((2 * n + 1).factorial : ℝ)
private def sincOfSq (s : ℝ) : ℝ := FormalMultilinearSeries.ofScalarsSum (E := ℝ) sincCoeff s
private theorem contDiff_sincOfSq : ContDiff ℝ topOrder sincOfSq := by apply _root_.YangMills.DeltaSharedProofs.p502125 <;> assumption
private theorem sincOfSq_sq (u : ℝ) : sincOfSq (u ^ 2) = Real.sinc u := by apply _root_.YangMills.DeltaSharedProofs.p500885 <;> assumption
private def sincNorm (v : imaginaryQuaternions) : ℝ := sincOfSq (‖v‖ ^ 2)
private theorem sincNorm_eq (v : imaginaryQuaternions) : sincNorm v = Real.sinc ‖v‖ := sincOfSq_sq _
private theorem contDiff_sincNorm : ContDiff ℝ topOrder sincNorm :=
  contDiff_sincOfSq.comp (contDiff_norm_sq ℝ)
private theorem sincNorm_pos {v : imaginaryQuaternions} (hv : ‖v‖ < Real.pi) : 0 < sincNorm v := by apply _root_.YangMills.DeltaSharedProofs.p500794 <;> assumption
private theorem haarLogRatio_eq_log {v : imaginaryQuaternions} (hv : ‖v‖ < Real.pi) :
    haarLogRatio v = Real.log (sincNorm v ^ 2) := by apply _root_.YangMills.DeltaSharedProofs.p501611 <;> assumption
private theorem haarLogRatio_contDiffAt {v : imaginaryQuaternions} (hv : ‖v‖ < Real.pi) :
    ContDiffAt ℝ topOrder haarLogRatio v := by apply _root_.YangMills.DeltaSharedProofs.p502052 <;> assumption
private theorem exists_uniform_iteratedFDeriv_bound (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ k, k ≤ n → ∀ v : imaginaryQuaternions, ‖v‖ ≤ 1 →
      ‖iteratedFDeriv ℝ k haarLogRatio v‖ ≤ C := by apply _root_.YangMills.SharedProofs.p34910 <;> assumption
end haar
section calculus
variable {E₁ E₂ : Type*} [NormedAddCommGroup E₁] [NormedSpace ℝ E₁] [NormedAddCommGroup E₂]
  [NormedSpace ℝ E₂]
private theorem exists_isOpen_contDiffOn {f : E₁ → E₂} {x : E₁} {n : ℕ} (hf : ContDiffAt ℝ n f x) :
    ∃ U : Set E₁, IsOpen U ∧ x ∈ U ∧ ContDiffOn ℝ n f U := by apply _root_.YangMills.Construction.GaugeAlongMotion.exists_isOpen_contDiffOn_of_contDiffAt <;> assumption
private theorem iteratedFDeriv_comp_eq_sum {E₃ : Type*} [NormedAddCommGroup E₃] [NormedSpace ℝ E₃]
    {g : E₂ → E₃} {β : E₁ → E₂} {x : E₁} {n : ℕ} (hg : ContDiffAt ℝ n g (β x))
    (hβ : ContDiffAt ℝ n β x) (v : Fin n → E₁) :
    iteratedFDeriv ℝ n (g ∘ β) x v = ∑ c : OrderedFinpartition n,
      iteratedFDeriv ℝ c.length g (β x)
        (c.applyOrderedFinpartition (fun m => iteratedFDeriv ℝ (c.partSize m) β x) v) := by apply _root_.YangMills.Construction.GaugeAlongMotion.iteratedFDeriv_comp_eq_sum_orderedFinpartition <;> assumption
private theorem iteratedFDeriv_comp_linear {E₃ : Type*} [NormedAddCommGroup E₃] [NormedSpace ℝ E₃]
    (Λ : E₁ →L[ℝ] E₂) {f : E₂ → E₃} {x : E₁} {n : ℕ} (hf : ContDiffAt ℝ n f (Λ x)) (v : Fin n → E₁) :
    iteratedFDeriv ℝ n (f ∘ Λ) x v = iteratedFDeriv ℝ n f (Λ x) fun l => Λ (v l) := by
  obtain ⟨U, hU, hxU, hfU⟩ := exists_isOpen_contDiffOn hf
  have hΛ : IsOpen (Λ ⁻¹' U) := hU.preimage Λ.continuous
  have h := Λ.iteratedFDerivWithin_comp_right hfU hU.uniqueDiffOn hΛ.uniqueDiffOn
    (x := x) hxU (i := n) le_rfl
  rw [iteratedFDerivWithin_of_isOpen n hΛ (show x ∈ Λ ⁻¹' U from hxU),
    iteratedFDerivWithin_of_isOpen n hU hxU] at h
  rw [h]
  rfl
private theorem fderiv_const_add_linear (a₀ : E₂) (Λ : E₁ →L[ℝ] E₂) :
    (fun y => fderiv ℝ (fun τ => a₀ + Λ τ) y) = fun _ => Λ := by
  funext y
  exact (Λ.hasFDerivAt.const_add a₀).fderiv
private theorem iteratedFDeriv_one_const_add_linear (a₀ : E₂) (Λ : E₁ →L[ℝ] E₂) (x : E₁)
    (v : Fin 1 → E₁) : iteratedFDeriv ℝ 1 (fun τ => a₀ + Λ τ) x v = Λ (v 0) := by
  rw [iteratedFDeriv_one_apply]
  exact congrFun (congrArg DFunLike.coe (congrFun (fderiv_const_add_linear a₀ Λ) x)) (v 0)
private theorem iteratedFDeriv_const_add_linear_of_two_le (a₀ : E₂) (Λ : E₁ →L[ℝ] E₂) (x : E₁)
    {q : ℕ} (v : Fin (q + 2) → E₁) : iteratedFDeriv ℝ (q + 2) (fun τ => a₀ + Λ τ) x v = 0 := by
  rw [iteratedFDeriv_succ_apply_right, fderiv_const_add_linear, iteratedFDeriv_const_of_ne (by omega)]
  simp
end calculus
section composite
variable {l j : ℕ}
private def topProj (l j : ℕ) : (Fin (l + j) → ℝ) →L[ℝ] (Fin j → ℝ) :=
  ContinuousLinearMap.pi fun i => ContinuousLinearMap.proj (Fin.natAdd l i)
private def pointSlope (d : Fin l → imaginaryQuaternions) : (Fin (l + j) → ℝ) →L[ℝ] imaginaryQuaternions :=
  ∑ i, (ContinuousLinearMap.proj (Fin.castAdd j i) : (Fin (l + j) → ℝ) →L[ℝ] ℝ).smulRight (d i)
private theorem pointSlope_apply (d : Fin l → imaginaryQuaternions) (τ : Fin (l + j) → ℝ) :
    pointSlope (j := j) d τ = ∑ i, τ (Fin.castAdd j i) • d i := by
  simp [pointSlope]
private def jointCoord (a₀ : imaginaryQuaternions) (d : Fin l → imaginaryQuaternions)
    (A : (Fin j → ℝ) → imaginaryQuaternions) (τ : Fin (l + j) → ℝ) : imaginaryQuaternions :=
  (a₀ + pointSlope d τ) + A (topProj l j τ)
private theorem jointCoord_zero (a₀ : imaginaryQuaternions) (d : Fin l → imaginaryQuaternions)
    (A : (Fin j → ℝ) → imaginaryQuaternions) : jointCoord a₀ d A 0 = a₀ + A 0 := by
  simp [jointCoord]
private theorem jointCoord_contDiffAt (a₀ : imaginaryQuaternions) (d : Fin l → imaginaryQuaternions)
    (A : (Fin j → ℝ) → imaginaryQuaternions)
    {n : WithTop ℕ∞} (hA : ContDiffAt ℝ n A 0) : ContDiffAt ℝ n (jointCoord a₀ d A) 0 := by
  have h1 : ContDiffAt ℝ n (fun τ => a₀ + pointSlope (j := j) d τ) (0 : Fin (l + j) → ℝ) :=
    contDiffAt_const.add (pointSlope d).contDiff.contDiffAt
  have h0 : ContDiffAt ℝ n A (topProj l j 0) := by simpa using hA
  have h2 : ContDiffAt ℝ n (A ∘ topProj l j) (0 : Fin (l + j) → ℝ) :=
    ContDiffAt.comp _ h0 (topProj l j).contDiff.contDiffAt
  exact h1.add h2
private theorem topProj_natAdd (i : Fin j) :
    topProj l j (Pi.single (Fin.natAdd l i) (1 : ℝ)) = Pi.single i (1 : ℝ) := by apply _root_.YangMills.DeltaSharedProofs.p501018 <;> assumption
private theorem topProj_castAdd (m : Fin l) :
    topProj l j (Pi.single (Fin.castAdd j m) (1 : ℝ)) = 0 := by apply _root_.YangMills.DeltaSharedProofs.p501334 <;> assumption
private theorem pointSlope_natAdd (d : Fin l → imaginaryQuaternions) (i : Fin j) :
    pointSlope (j := j) d (Pi.single (Fin.natAdd l i) (1 : ℝ)) = 0 := by
  rw [pointSlope_apply]
  refine Finset.sum_eq_zero fun m _ => ?_
  have h' : Fin.castAdd j m ≠ Fin.natAdd l i := by
    intro e
    have := congrArg Fin.val e
    simp at this
    omega
  simp [h']
private theorem pointSlope_castAdd (d : Fin l → imaginaryQuaternions) (m : Fin l) :
    pointSlope (j := j) d (Pi.single (Fin.castAdd j m) (1 : ℝ)) = d m := by
  rw [pointSlope_apply, Finset.sum_eq_single m]
  · simp
  · intro m' _ h
    have h' : Fin.castAdd j m' ≠ Fin.castAdd j m := fun e => h (Fin.castAdd_injective _ _ e)
    simp [h']
  · simp
private theorem castAdd_or_natAdd (x : Fin (l + j)) :
    (∃ m, x = Fin.castAdd j m) ∨ ∃ i, x = Fin.natAdd l i := by apply _root_.YangMills.SharedProofs.p14800 <;> assumption
private theorem part_bound (a₀ : imaginaryQuaternions) (d : Fin l → imaginaryQuaternions)
    (A : (Fin j → ℝ) → imaginaryQuaternions) (B : ℝ)
    (ω : Fin (l + j) → ℝ) (hAs : ContDiffAt ℝ ((l + j : ℕ) : WithTop ℕ∞) A 0) (hB : 1 ≤ B)
    (hω : ∀ m, 0 ≤ ω m) (hd : ∀ m, ‖d m‖ ≤ ω (Fin.castAdd j m))
    (hA : ∀ (q : ℕ) (ι : Fin q → Fin j), 1 ≤ q → q ≤ l + j → ∀ r,
      ‖iteratedFDeriv ℝ q A 0 (fun s => Pi.single (ι s) (1 : ℝ))‖ ≤ B * ω (Fin.natAdd l (ι r)))
    {q : ℕ} (e : Fin q → Fin (l + j)) (hq : 1 ≤ q) (hql : q ≤ l + j) (r : Fin q) :
    ‖iteratedFDeriv ℝ q (jointCoord a₀ d A) 0 (fun s => Pi.single (e s) (1 : ℝ))‖ ≤ B * ω (e r) := by
  have hqA : ContDiffAt ℝ (q : WithTop ℕ∞) A 0 := hAs.of_le (by exact_mod_cast hql)
  have hs1 : ContDiffAt ℝ (q : WithTop ℕ∞) (fun τ => a₀ + pointSlope (j := j) d τ)
      (0 : Fin (l + j) → ℝ) := contDiffAt_const.add (pointSlope d).contDiff.contDiffAt
  have h0 : ContDiffAt ℝ (q : WithTop ℕ∞) A (topProj l j 0) := by simpa using hqA
  have hs2 : ContDiffAt ℝ (q : WithTop ℕ∞) (A ∘ topProj l j) (0 : Fin (l + j) → ℝ) :=
    ContDiffAt.comp _ h0 (topProj l j).contDiff.contDiffAt
  have e1 : jointCoord a₀ d A = (fun τ => a₀ + pointSlope (j := j) d τ) + A ∘ topProj l j := rfl
  have hBω : ∀ m, 0 ≤ B * ω m := fun m => mul_nonneg (by linarith) (hω m)
  rw [e1, iteratedFDeriv_add_apply hs1 hs2, _root_.add_apply,
    iteratedFDeriv_comp_linear (topProj l j) h0]
  by_cases hall : ∀ s, ∃ i, e s = Fin.natAdd l i
  · choose ι hι using hall
    have h2 : (fun s => topProj l j (Pi.single (e s) (1 : ℝ))) =
        fun s => Pi.single (ι s) (1 : ℝ) := by
      funext s
      rw [hι s, topProj_natAdd]
    have h3 : iteratedFDeriv ℝ q (fun τ => a₀ + pointSlope (j := j) d τ) 0
        (fun s => Pi.single (e s) (1 : ℝ)) = 0 := by
      obtain rfl | ⟨q', rfl⟩ : q = 1 ∨ ∃ q', q = q' + 2 := by
        rcases q with _ | _ | q'
        · omega
        · exact Or.inl rfl
        · exact Or.inr ⟨q', rfl⟩
      · rw [iteratedFDeriv_one_const_add_linear, hι 0, pointSlope_natAdd]
      · exact iteratedFDeriv_const_add_linear_of_two_le _ _ _ _
    have h4 := hA q ι hq hql r
    rw [h2, h3, zero_add]
    have : topProj l j 0 = 0 := map_zero _
    rw [this, hι r]
    exact h4
  · push Not at hall
    obtain ⟨s₀, hs₀⟩ := hall
    obtain ⟨m, hm⟩ : ∃ m, e s₀ = Fin.castAdd j m := by
      rcases castAdd_or_natAdd (e s₀) with h | ⟨i, h⟩
      · exact h
      · exact absurd h (hs₀ i)
    have h2 : iteratedFDeriv ℝ q A (topProj l j 0)
        (fun s => topProj l j (Pi.single (e s) (1 : ℝ))) = 0 :=
      ContinuousMultilinearMap.map_coord_zero _ s₀ (by rw [hm, topProj_castAdd])
    rw [h2, add_zero]
    obtain rfl | ⟨q', rfl⟩ : q = 1 ∨ ∃ q', q = q' + 2 := by
      rcases q with _ | _ | q'
      · omega
      · exact Or.inl rfl
      · exact Or.inr ⟨q', rfl⟩
    · have hr : r = s₀ := Subsingleton.elim _ _
      have hs0 : s₀ = 0 := Subsingleton.elim _ _
      rw [iteratedFDeriv_one_const_add_linear, ← hs0, hm, pointSlope_castAdd, hr, hm]
      calc ‖d m‖ ≤ ω (Fin.castAdd j m) := hd m
        _ ≤ B * ω (Fin.castAdd j m) := le_mul_of_one_le_left (hω _) hB
    · rw [iteratedFDeriv_const_add_linear_of_two_le, norm_zero]
      exact hBω _
private theorem mul_mul_pow_pred (B w : ℝ) {n : ℕ} (hn : 1 ≤ n) : B * w * B ^ (n - 1) = B ^ n * w := by apply _root_.YangMills.SharedProofs.p73735 <;> assumption
private theorem mixedDeriv_comp_bound (a₀ : imaginaryQuaternions) (d : Fin l → imaginaryQuaternions)
    (A : (Fin j → ℝ) → imaginaryQuaternions) (H : imaginaryQuaternions → ℝ)
    (B Hm : ℝ) (ω : Fin (l + j) → ℝ) (hAs : ContDiffAt ℝ ((l + j : ℕ) : WithTop ℕ∞) A 0)
    (hH : ContDiffAt ℝ ((l + j : ℕ) : WithTop ℕ∞) H (a₀ + A 0))
    (hHm : ∀ k, k ≤ l + j → ‖iteratedFDeriv ℝ k H (a₀ + A 0)‖ ≤ Hm) (hHm0 : 0 ≤ Hm)
    (hB : 1 ≤ B) (hω : ∀ m, 0 ≤ ω m) (hω1 : ∀ m, ω m ≤ 1)
    (hd : ∀ m, ‖d m‖ ≤ ω (Fin.castAdd j m))
    (hA : ∀ (q : ℕ) (ι : Fin q → Fin j), 1 ≤ q → q ≤ l + j → ∀ r,
      ‖iteratedFDeriv ℝ q A 0 (fun s => Pi.single (ι s) (1 : ℝ))‖ ≤ B * ω (Fin.natAdd l (ι r)))
    (m : Fin (l + j)) :
    |iteratedFDeriv ℝ (l + j) (H ∘ jointCoord a₀ d A) 0 (fun i => Pi.single i (1 : ℝ))| ≤
      (Fintype.card (OrderedFinpartition (l + j)) : ℝ) * Hm * B ^ (l + j) * ω m := by
  have hφ := jointCoord_contDiffAt a₀ d A hAs
  have hB0 : 0 ≤ B := by linarith
  rw [iteratedFDeriv_comp_eq_sum (by rw [jointCoord_zero]; exact hH) hφ]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have term : ∀ c : OrderedFinpartition (l + j),
      |iteratedFDeriv ℝ c.length H (jointCoord a₀ d A 0)
        (c.applyOrderedFinpartition (fun m => iteratedFDeriv ℝ (c.partSize m) (jointCoord a₀ d A) 0)
          (fun i => Pi.single i (1 : ℝ)))| ≤ Hm * B ^ (l + j) * ω m := by
    intro c
    have e1 : c.applyOrderedFinpartition (fun m => iteratedFDeriv ℝ (c.partSize m) (jointCoord a₀ d A) 0)
        (fun i => Pi.single i (1 : ℝ)) = fun i => iteratedFDeriv ℝ (c.partSize i) (jointCoord a₀ d A) 0
          (fun s => Pi.single (c.emb i s) (1 : ℝ)) := by
      funext i
      rfl
    rw [e1, jointCoord_zero]
    have hop := (iteratedFDeriv ℝ c.length H (a₀ + A 0)).le_opNorm
      (fun i => iteratedFDeriv ℝ (c.partSize i) (jointCoord a₀ d A) 0
        (fun s => Pi.single (c.emb i s) (1 : ℝ)))
    rw [Real.norm_eq_abs] at hop
    refine hop.trans ?_
    have hslot : ∀ (i : Fin c.length) (s : Fin (c.partSize i)),
        ‖iteratedFDeriv ℝ (c.partSize i) (jointCoord a₀ d A) 0
          (fun s => Pi.single (c.emb i s) (1 : ℝ))‖ ≤ B * ω (c.emb i s) := fun i s =>
      part_bound a₀ d A B ω hAs hB hω hd hA (c.emb i) (c.partSize_pos i) (c.partSize_le i) s
    set i₀ := c.index m with hi₀
    have hlen : 1 ≤ c.length := by
      have := i₀.2
      omega
    have hprod : ∏ i, ‖iteratedFDeriv ℝ (c.partSize i) (jointCoord a₀ d A) 0
        (fun s => Pi.single (c.emb i s) (1 : ℝ))‖ ≤ B ^ (l + j) * ω m := by
      rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i₀)]
      have h1 : ‖iteratedFDeriv ℝ (c.partSize i₀) (jointCoord a₀ d A) 0
          (fun s => Pi.single (c.emb i₀ s) (1 : ℝ))‖ ≤ B * ω m := by
        have h0 := hslot i₀ (c.invEmbedding m)
        have e : c.emb i₀ (c.invEmbedding m) = m := c.emb_invEmbedding m
        rwa [e] at h0
      have h2 : ∏ i ∈ Finset.univ.erase i₀, ‖iteratedFDeriv ℝ (c.partSize i) (jointCoord a₀ d A) 0
          (fun s => Pi.single (c.emb i s) (1 : ℝ))‖ ≤ B ^ (c.length - 1) := by
        have hc : (Finset.univ.erase i₀).card = c.length - 1 := by
          rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin]
        rw [← hc, ← Finset.prod_const]
        refine Finset.prod_le_prod (fun _ _ => norm_nonneg _) fun i _ => ?_
        have hpos := c.partSize_pos i
        refine (hslot i ⟨0, hpos⟩).trans ?_
        exact mul_le_of_le_one_right hB0 (hω1 _)
      have h3 : B * ω m * B ^ (c.length - 1) ≤ B ^ (l + j) * ω m := by
        rw [mul_mul_pow_pred B (ω m) hlen]
        exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hB c.length_le) (hω m)
      calc _ ≤ B * ω m * B ^ (c.length - 1) :=
            mul_le_mul h1 h2 (Finset.prod_nonneg fun _ _ => norm_nonneg _)
              (mul_nonneg hB0 (hω m))
        _ ≤ _ := h3
    calc _ ≤ Hm * ∏ i, ‖iteratedFDeriv ℝ (c.partSize i) (jointCoord a₀ d A) 0
          (fun s => Pi.single (c.emb i s) (1 : ℝ))‖ :=
          mul_le_mul_of_nonneg_right (hHm _ c.length_le)
            (Finset.prod_nonneg fun _ _ => norm_nonneg _)
      _ ≤ Hm * (B ^ (l + j) * ω m) := mul_le_mul_of_nonneg_left hprod hHm0
      _ = _ := by ring
  calc _ ≤ ∑ _c : OrderedFinpartition (l + j), Hm * B ^ (l + j) * ω m :=
        Finset.sum_le_sum fun c _ => term c
    _ = _ := by
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      ring
end composite
section pull
private def reindexMap {q k : ℕ} (ι : Fin q → Fin k) : (Fin q → ℝ) →L[ℝ] (Fin k → ℝ) :=
  ContinuousLinearMap.pi fun i => ∑ r, if ι r = i then
    (ContinuousLinearMap.proj r : (Fin q → ℝ) →L[ℝ] ℝ) else 0
private theorem reindexMap_apply {q k : ℕ} (ι : Fin q → Fin k) (τ : Fin q → ℝ) (i : Fin k) :
    reindexMap ι τ i = ∑ r, if ι r = i then τ r else 0 := by
  simp only [reindexMap, ContinuousLinearMap.coe_pi', _root_.sum_apply]
  refine Finset.sum_congr rfl fun r _ => ?_
  split_ifs <;> simp
private theorem reindexMap_single {q k : ℕ} (ι : Fin q → Fin k) (r : Fin q) :
    reindexMap ι (Pi.single r (1 : ℝ)) = Pi.single (ι r) (1 : ℝ) := by
  ext i
  rw [reindexMap_apply, Finset.sum_eq_single r]
  · by_cases h : ι r = i
    · subst h
      simp
    · have h' : i ≠ ι r := fun e => h e.symm
      simp [h, h']
  · intro s _ hs
    simp [hs]
  · simp
private theorem bondSpread_reindex {F : BlockFrame} {J q k : ℕ} (c : Fin k → F.Site J × Fin 4)
    (X : Fin k → imaginaryQuaternions) (ι : Fin q → Fin k) (τ : Fin q → ℝ) :
    bondSpread (fun r => c (ι r)) (fun r => X (ι r)) τ = bondSpread c X (reindexMap ι τ) := by
  funext y i
  simp only [bondSpread, reindexMap_apply]
  calc _ = ∑ r, ∑ n, if ι r = n then (if c n = (y, i) then τ r • X n else 0) else 0 := by
        refine Finset.sum_congr rfl fun r _ => ?_
        rw [Finset.sum_ite_eq]
        simp
    _ = ∑ n, ∑ r, if ι r = n then (if c n = (y, i) then τ r • X n else 0) else 0 := Finset.sum_comm
    _ = _ := by
        refine Finset.sum_congr rfl fun n _ => ?_
        by_cases h : c n = (y, i)
        · simp only [h, if_true]
          rw [Finset.sum_smul]
          refine Finset.sum_congr rfl fun r _ => ?_
          split_ifs <;> simp
        · simp [h]
end pull
section frames
variable {F : BlockFrame}
private theorem toImaginary_add (u v : EuclideanSpace ℝ (Fin 3)) :
    toImaginary (u + v) = toImaginary u + toImaginary v := by apply _root_.YangMills.Construction.Interpolation.TopVariation.toImaginary_add <;> assumption
private theorem toImaginary_smul (r : ℝ) (v : EuclideanSpace ℝ (Fin 3)) :
    toImaginary (r • v) = r • toImaginary v := by apply _root_.YangMills.Construction.Interpolation.TopVariation.toImaginary_smul <;> assumption
private def toImaginaryLinear : EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] imaginaryQuaternions where
  toFun := toImaginary
  map_add' := toImaginary_add
  map_smul' := toImaginary_smul
private theorem norm_toImaginary (v : EuclideanSpace ℝ (Fin 3)) : ‖toImaginary v‖ = ‖v‖ := by apply _root_.YangMills.Construction.Interpolation.ExponentBoundSteps.norm_toImaginary <;> assumption
private theorem leftTranslate_bondSpread_zero {k : ℕ} (c : Fin k → F.Site F.top × Fin 4)
    (X : Fin k → imaginaryQuaternions) (V : F.GaugeField F.top) :
    leftTranslate (bondSpread c X 0) V = V := by apply _root_.YangMills.SharedProofs.p2043 <;> assumption
private theorem cellSetDiameter_le {P : Finset F.Cell} {y : F.Cell} {d : ℕ}
    (h : ∀ u ∈ P, cellSupDist y u ≤ d) : cellSetDiameter P ≤ 2 * d := by apply _root_.YangMills.SharedProofs.p92193 <;> assumption
open Classical in
private def pointDirection {l : ℕ} (b₀ : ↥(chordBonds (finiteCells F)))
    (b : Fin l → ↥(chordBonds (finiteCells F))) (u : Fin l → EuclideanSpace ℝ (Fin 3)) (i : Fin l) :
    imaginaryQuaternions :=
  if b i = b₀ then toImaginary (u i) else 0
private def frameAlongTop {j : ℕ} (s a ρA : ℝ) (m : ℕ) (b₀ : ↥(chordBonds (finiteCells F)))
    (V : F.GaugeField F.top) (c : Fin j → F.Site F.top × Fin 4) (X : Fin j → imaginaryQuaternions)
    (τ : Fin j → ℝ) : imaginaryQuaternions :=
  interpolatedFrame s a ρA m b₀.1 (leftTranslate (bondSpread c X τ) V)
private theorem jointDisplacement_eq {l j : ℕ} (s a ρA : ℝ) (m : ℕ) (V : F.GaugeField F.top)
    (η : StepVariable (finiteCells F)) (b₀ : ↥(chordBonds (finiteCells F)))
    (b : Fin l → ↥(chordBonds (finiteCells F))) (u : Fin l → EuclideanSpace ℝ (Fin 3))
    (c : Fin j → F.Site F.top × Fin 4) (X : Fin j → imaginaryQuaternions) :
    jointDisplacement (fun ζ V' => haarLogRatio (interpolatedCoords s a ρA m V' ζ b₀.1.1 b₀.1.2))
        η V b u c X =
      haarLogRatio ∘ jointCoord (toImaginary (η b₀)) (pointDirection b₀ b u)
        (frameAlongTop s a ρA m b₀ V c X) := by
  classical
  funext τ
  have hco : stepCoordinates (displacedPoint η b u fun i => τ (Fin.castAdd j i)) b₀.1.1 b₀.1.2 =
      toImaginary (η b₀) + pointSlope (j := j) (pointDirection b₀ b u) τ := by
    have hb : (b₀.1.1, b₀.1.2) ∈ chordBonds (finiteCells F) := b₀.2
    unfold stepCoordinates
    rw [dif_pos hb, pointSlope_apply]
    have e0 : (⟨(b₀.1.1, b₀.1.2), hb⟩ : ↥(chordBonds (finiteCells F))) = b₀ := rfl
    rw [e0]
    have e1 : displacedPoint η b u (fun i => τ (Fin.castAdd j i)) b₀ =
        η b₀ + ∑ i, (if b i = b₀ then τ (Fin.castAdd j i) • u i else 0) := by
      simp only [displacedPoint, Pi.add_apply, Finset.sum_apply]
      congr 1
      refine Finset.sum_congr rfl fun i _ => ?_
      by_cases h : b i = b₀
      · subst h
        simp
      · have h' : b₀ ≠ b i := fun e => h e.symm
        simp [h, h']
    rw [e1, toImaginary_add]
    congr 1
    show toImaginaryLinear _ = _
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases h : b i = b₀
    · simp only [h, if_true, pointDirection]
      exact toImaginary_smul _ _
    · simp only [h, if_false, pointDirection, smul_zero]
      exact map_zero toImaginaryLinear
  show haarLogRatio (interpolatedFrame s a ρA m (b₀.1.1, b₀.1.2) _ +
      stepCoordinates (displacedPoint η b u fun i => τ (Fin.castAdd j i)) b₀.1.1 b₀.1.2) =
    haarLogRatio (jointCoord _ _ _ τ)
  rw [hco]
  congr 1
  exact add_comm _ _
private def partConstant (K : ℕ → ℝ) (p : ℕ) : ℝ :=
  1 + ∑ q ∈ Finset.range (p + 1), 16 ^ q * |K q|
private theorem one_le_partConstant (K : ℕ → ℝ) (p : ℕ) : 1 ≤ partConstant K p := by
  have : 0 ≤ ∑ q ∈ Finset.range (p + 1), (16 : ℝ) ^ q * |K q| :=
    Finset.sum_nonneg fun _ _ => by positivity
  unfold partConstant
  linarith
private theorem le_partConstant (K : ℕ → ℝ) {p q : ℕ} (h : q ≤ p) :
    (16 : ℝ) ^ q * K q ≤ partConstant K p := by
  have h1 : (16 : ℝ) ^ q * |K q| ≤ ∑ q ∈ Finset.range (p + 1), (16 : ℝ) ^ q * |K q| :=
    Finset.single_le_sum (f := fun q => (16 : ℝ) ^ q * |K q|) (fun _ _ => by positivity)
      (Finset.mem_range.2 (by omega))
  have h2 : (16 : ℝ) ^ q * K q ≤ 16 ^ q * |K q| :=
    mul_le_mul_of_nonneg_left (le_abs_self _) (by positivity)
  unfold partConstant
  linarith
private def paramWeight {l j : ℕ} (r : ℝ) (y : F.Cell) (b₀ : ↥(chordBonds (finiteCells F)))
    (b : Fin l → ↥(chordBonds (finiteCells F))) (c : Fin j → F.Site F.top × Fin 4) :
    Fin (l + j) → ℝ :=
  open Classical in
  Fin.addCases (motive := fun _ => ℝ) (fun i => if b i = b₀ then 1 else 0)
    (fun i => Real.exp (-(r * cellSupDist y (c i).1)))
private theorem bound_at_frame {l j : ℕ} (s a ρA r κ Hm : ℝ) (m : ℕ) (K : ℕ → ℝ)
    (V : F.GaugeField F.top)
    (η : StepVariable (finiteCells F)) (b₀ : ↥(chordBonds (finiteCells F)))
    (b : Fin l → ↥(chordBonds (finiteCells F))) (u : Fin l → EuclideanSpace ℝ (Fin 3))
    (c : Fin j → F.Site F.top × Fin 4) (X : Fin j → imaginaryQuaternions) (hlj : 1 ≤ l + j)
    (hu : ∀ i, ‖u i‖ = 1)
    (hX : AreUnitVectors X) (hr : 0 ≤ r) (hκ : 0 ≤ κ) (hκr : 2 ^ 9 * κ ≤ r)
    (hsize : ‖toImaginary (η b₀) + interpolatedFrame s a ρA m b₀.1 V‖ ≤ 1)
    (hAn : IsBondAnalyticAt (interpolatedFrame s a ρA m b₀.1) V)
    (hdec : ∀ (k : ℕ) (c' : Fin k → F.Site F.top × Fin 4) (X' : Fin k → imaginaryQuaternions),
      1 ≤ k → AreUnitVectors X' →
      ‖bondDeriv (interpolatedFrame s a ρA m b₀.1) V c' X'‖ ≤
        16 ^ k * K k * Real.exp (-(r * bondListDistance (enclosingCell b₀.1.1) c')))
    (hHm0 : 0 ≤ Hm)
    (hHm : ∀ k, k ≤ l + j → ∀ v : imaginaryQuaternions, ‖v‖ ≤ 1 →
      ‖iteratedFDeriv ℝ k haarLogRatio v‖ ≤ Hm) :
    ContDiffAt ℝ (l + j : ℕ) (jointDisplacement
        (fun ζ V' => haarLogRatio (interpolatedCoords s a ρA m V' ζ b₀.1.1 b₀.1.2)) η V b u c X) 0 ∧
      |jointMixedDeriv (fun ζ V' => haarLogRatio (interpolatedCoords s a ρA m V' ζ b₀.1.1 b₀.1.2))
          η V b u c X| ≤
        ((Fintype.card (OrderedFinpartition (l + j)) : ℝ) * Hm * partConstant K (l + j) ^ (l + j) + 1) *
          Real.exp (-(2 ^ 8 * κ * cellSetDiameter
            ({enclosingCell b₀.1.1} ∪ chordBondCells b ∪ topBondCells c))) := by
  classical
  have : CompleteSpace imaginaryQuaternions := FiniteDimensional.complete ℝ imaginaryQuaternions
  set A := frameAlongTop s a ρA m b₀ V c X with hAdef
  set a₀ := toImaginary (η b₀) with ha₀
  set d := pointDirection b₀ b u with hd₀
  set y := enclosingCell b₀.1.1 with hy
  set B := partConstant K (l + j) with hBdef
  have hB : 1 ≤ B := one_le_partConstant _ _
  have hA0 : A 0 = interpolatedFrame s a ρA m b₀.1 V := by
    simp only [hAdef, frameAlongTop, leftTranslate_bondSpread_zero]
  have hAsm : ∀ n : WithTop ℕ∞, ContDiffAt ℝ n A 0 := fun n => (hAn j c X).contDiffAt
  have hpt : ‖a₀ + A 0‖ ≤ 1 := by rw [hA0]; exact hsize
  have hlt : ‖a₀ + A 0‖ < Real.pi := by linarith [Real.pi_gt_three]
  have hHs : ContDiffAt ℝ ((l + j : ℕ) : WithTop ℕ∞) haarLogRatio (a₀ + A 0) :=
    (haarLogRatio_contDiffAt hlt).of_le (natCast_le_topOrder _)
  have hφ := jointCoord_contDiffAt a₀ d A (hAsm ((l + j : ℕ) : WithTop ℕ∞))
  have hmv := jointDisplacement_eq s a ρA m V η b₀ b u c X
  refine ⟨?_, ?_⟩
  · rw [hmv]
    exact ContDiffAt.comp _ (by rw [jointCoord_zero]; exact hHs) hφ
  set ω : Fin (l + j) → ℝ := paramWeight r y b₀ b c with hω
  have hωl : ∀ i, ω (Fin.castAdd j i) = if b i = b₀ then 1 else 0 := fun i => by
    simp only [hω, paramWeight, Fin.addCases_left]
  have hωr : ∀ i, ω (Fin.natAdd l i) = Real.exp (-(r * cellSupDist y (c i).1)) := fun i => by
    simp only [hω, paramWeight, Fin.addCases_right]
  have hω0 : ∀ n, 0 ≤ ω n := fun n => by
    rcases castAdd_or_natAdd n with ⟨i, rfl⟩ | ⟨i, rfl⟩
    · rw [hωl]
      split_ifs <;> norm_num
    · rw [hωr]
      exact (Real.exp_pos _).le
  have hω1 : ∀ n, ω n ≤ 1 := fun n => by
    rcases castAdd_or_natAdd n with ⟨i, rfl⟩ | ⟨i, rfl⟩
    · rw [hωl]
      split_ifs <;> norm_num
    · rw [hωr]
      apply Real.exp_le_one_iff.2
      have : 0 ≤ r * (cellSupDist y (c i).1 : ℝ) := mul_nonneg hr (Nat.cast_nonneg _)
      linarith
  have hdω : ∀ i, ‖d i‖ ≤ ω (Fin.castAdd j i) := fun i => by
    rw [hωl]
    by_cases h : b i = b₀
    · simp only [hd₀, pointDirection, h, if_true, norm_toImaginary, hu i, le_refl]
    · simp [hd₀, pointDirection, h]
  have hAslot : ∀ (q : ℕ) (ι : Fin q → Fin j), 1 ≤ q → q ≤ l + j → ∀ r',
      ‖iteratedFDeriv ℝ q A 0 (fun s' => Pi.single (ι s') (1 : ℝ))‖ ≤
        B * ω (Fin.natAdd l (ι r')) := by
    intro q ι hq hql r'
    have e1 : bondDeriv (interpolatedFrame s a ρA m b₀.1) V (fun t => c (ι t)) (fun t => X (ι t)) =
        iteratedFDeriv ℝ q A 0 (fun s' => Pi.single (ι s') (1 : ℝ)) := by
      have e2 : (fun τ : Fin q → ℝ => interpolatedFrame s a ρA m b₀.1
          (leftTranslate (bondSpread (fun t => c (ι t)) (fun t => X (ι t)) τ) V)) = A ∘ reindexMap ι := by
        funext τ
        simp only [Function.comp, hAdef, frameAlongTop, bondSpread_reindex]
      have h0 : ContDiffAt ℝ (q : WithTop ℕ∞) A (reindexMap ι 0) := by
        simpa using hAsm (q : WithTop ℕ∞)
      unfold bondDeriv
      rw [e2, iteratedFDeriv_comp_linear (reindexMap ι) h0]
      have e3 : reindexMap ι 0 = 0 := map_zero _
      rw [e3]
      congr 1
      funext s'
      exact reindexMap_single ι s'
    rw [← e1, hωr]
    refine (hdec q _ _ hq fun t => hX (ι t)).trans ?_
    have h1 : (cellSupDist y (c (ι r')).1 : ℝ) ≤ bondListDistance y (fun t => c (ι t)) := by
      exact_mod_cast Finset.le_sup (f := fun t => cellSupDist y (c (ι t)).1) (Finset.mem_univ r')
    have h2 : Real.exp (-(r * bondListDistance y (fun t => c (ι t)))) ≤
        Real.exp (-(r * cellSupDist y (c (ι r')).1)) := by
      apply Real.exp_le_exp.2
      have := mul_le_mul_of_nonneg_left h1 hr
      linarith
    exact mul_le_mul (le_partConstant K hql) h2 (Real.exp_pos _).le (by linarith)
  have hmain := mixedDeriv_comp_bound a₀ d A haarLogRatio B Hm ω (hAsm _) hHs
    (fun k hk => hHm k hk _ hpt) hHm0 hB hω0 hω1 hdω hAslot
  unfold jointMixedDeriv
  rw [hmv]
  set Kc : ℝ := (Fintype.card (OrderedFinpartition (l + j)) : ℝ) * Hm * B ^ (l + j) with hKc
  have hKc0 : 0 ≤ Kc := by
    have : 0 ≤ B := by linarith
    positivity
  set P := {y} ∪ chordBondCells b ∪ topBondCells c with hP
  have hexp := Real.exp_pos (-(2 ^ 8 * κ * (cellSetDiameter P : ℝ)))
  by_cases hb : ∃ i, b i ≠ b₀
  · obtain ⟨i, hi⟩ := hb
    have h1 := hmain (Fin.castAdd j i)
    rw [hωl, if_neg hi, mul_zero] at h1
    exact h1.trans (by positivity)
  · push Not at hb
    obtain ⟨dS, mS, hdS, hmS⟩ : ∃ (dS : ℕ) (mS : Fin (l + j)), (∀ i, cellSupDist y (c i).1 ≤ dS) ∧
        ω mS ≤ Real.exp (-(r * dS)) := by
      by_cases hj : Nonempty (Fin j)
      · obtain ⟨i, -, hi⟩ := Finset.exists_max_image Finset.univ (fun i => cellSupDist y (c i).1)
          ⟨hj.some, Finset.mem_univ _⟩
        exact ⟨cellSupDist y (c i).1, Fin.natAdd l i, fun i' => hi i' (Finset.mem_univ _), by rw [hωr]⟩
      · have hj0 : j = 0 := by
          by_contra h
          exact hj ⟨⟨0, Nat.pos_of_ne_zero h⟩⟩
        have hl : 0 < l := by omega
        refine ⟨0, Fin.castAdd j ⟨0, hl⟩, fun i => (hj ⟨i⟩).elim, ?_⟩
        rw [hωl, if_pos (hb _)]
        simp
    have hself : cellSupDist y y = 0 := by simp [cellSupDist]
    have hspan : cellSetDiameter P ≤ 2 * dS := by
      refine cellSetDiameter_le (y := y) fun v hv => ?_
      simp only [hP, Finset.mem_union, Finset.mem_singleton, chordBondCells, topBondCells,
        Finset.mem_image, Finset.mem_univ, true_and] at hv
      rcases hv with (rfl | ⟨i, rfl⟩) | ⟨i, rfl⟩
      · rw [hself]
        omega
      · rw [hb i, hself]
        omega
      · exact hdS i
    have hle : Real.exp (-(r * dS)) ≤ Real.exp (-(2 ^ 8 * κ * (cellSetDiameter P : ℝ))) := by
      apply Real.exp_le_exp.2
      have h1 : (cellSetDiameter P : ℝ) ≤ 2 * dS := by exact_mod_cast hspan
      have h2 : 2 ^ 8 * κ * (cellSetDiameter P : ℝ) ≤ 2 ^ 8 * κ * (2 * dS) :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
      have h3 : (2 ^ 9 * κ) * (dS : ℝ) ≤ r * dS :=
        mul_le_mul_of_nonneg_right hκr (Nat.cast_nonneg _)
      nlinarith
    have h1 := hmain mS
    calc _ ≤ Kc * ω mS := h1
      _ ≤ Kc * Real.exp (-(2 ^ 8 * κ * (cellSetDiameter P : ℝ))) :=
        mul_le_mul_of_nonneg_left (hmS.trans hle) hKc0
      _ ≤ _ := by nlinarith
end frames
end HaarLogRatio
open HaarLogRatio in
theorem haarLogRatioDerivBounds_holds : HaarLogRatioDerivBounds := by
  choose Hm hHm0 hHm using exists_uniform_iteratedFDeriv_bound
  intro K r κ hK hr hκ hκr
  set K' : ℕ → ℝ := fun k => K k / 16 ^ k with hK'
  refine ⟨fun l j => (Fintype.card (OrderedFinpartition (l + j)) : ℝ) * Hm (l + j) *
      partConstant K' (l + j) ^ (l + j) + 1, fun l j => ?_, ?_⟩
  · have h1 := hHm0 (l + j)
    have h2 := one_le_partConstant K' (l + j)
    positivity
  intro F s a ρA m V η b₀ hsize hAn hdec l j b u c X hlj hu hX
  refine bound_at_frame s a ρA r κ (Hm (l + j)) m K' V η b₀ b u c X hlj hu hX hr hκ hκr hsize hAn
    (fun k c' X' hk hX' => ?_) (hHm0 _) (hHm _)
  have e : (16 : ℝ) ^ k * K' k = K k := by
    simp only [hK']
    field_simp
  rw [e]
  exact hdec k c' X' hk hX'
end RunningCouplingSlope
end YangMills.Construction
end
