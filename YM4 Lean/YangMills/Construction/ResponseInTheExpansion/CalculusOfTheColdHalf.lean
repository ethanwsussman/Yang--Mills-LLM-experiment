import YangMills.Construction.SummableBoundsOfTheFlow.TheBirthsBetweenProof
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Topology
open MeasureTheory
namespace YangMills.Construction
open BlockAverages hiding bondSpread
open ColdStepAtMirrorFrames Interpolation
namespace ResponseInTheExpansion
variable {F : BlockFrame}
theorem hasLocalSize_congr_density {ι : Type} [Fintype ι] [DecidableEq ι] {ρ x κ h : ℝ} {r : ℝ → ℝ}
    {Ψ Ψ' : BondField ι → ℝ} {Cq : ℕ → ℝ} {dZ : ι → ℝ} {H : BondField ι → ℝ}
    (hd : ballDensity r Ψ = ballDensity r Ψ') (hs : HasLocalSize ρ r Ψ Cq x κ h dZ H) :
    HasLocalSize ρ r Ψ' Cq x κ h dZ H := by
  have hm : ∀ (G : BondField ι → ℝ) (q : ℕ) (B : ℝ), MomentBound r Ψ G q B →
      MomentBound r Ψ' G q B := by
    intro G q B h1
    unfold MomentBound ballExpectation at *
    rw [← hd]
    exact h1
  obtain ⟨h1, H₀, h2⟩ := hs
  exact ⟨h1, H₀, fun q hq => ⟨hm _ _ _ (h2 q hq).1, fun b => hm _ _ _ ((h2 q hq).2 b)⟩⟩
theorem hasLocalSize_congr_of_eqOn_balls {ι : Type} [Fintype ι] [DecidableEq ι] {ρ x κ h : ℝ} {r : ℝ → ℝ}
    {Ψ : BondField ι → ℝ} {Cq : ℕ → ℝ} {dZ : ι → ℝ} {H H' : BondField ι → ℝ}
    (hO : IsOpen {η : BondField ι | ∀ b, ‖η b‖ < ρ})
    (hz : ∀ η : BondField ι, ¬ (∀ b, ‖η b‖ < ρ) → ballDensity r Ψ η = 0)
    (he : ∀ η : BondField ι, (∀ b, ‖η b‖ < ρ) → H η = H' η)
    (hs : HasLocalSize ρ r Ψ Cq x κ h dZ H) : HasLocalSize ρ r Ψ Cq x κ h dZ H' := by
  have hev : ∀ η : BondField ι, (∀ b, ‖η b‖ < ρ) → H =ᶠ[𝓝 η] H' := fun η hη =>
    Filter.eventually_of_mem (hO.mem_nhds hη) fun ζ hζ => he ζ hζ
  have hm : ∀ (G G' : BondField ι → ℝ) (q : ℕ) (B : ℝ), (∀ η : BondField ι, (∀ b, ‖η b‖ < ρ) → G η = G' η) →
      MomentBound r Ψ G q B → MomentBound r Ψ G' q B := by
    intro G G' q B hG h1
    have e : (fun η => |G' η| ^ q * ballDensity r Ψ η) = fun η => |G η| ^ q * ballDensity r Ψ η := by
      funext η
      by_cases hη : ∀ b, ‖η b‖ < ρ
      · rw [hG η hη]
      · rw [hz η hη]; simp
    unfold MomentBound ballExpectation at *
    rw [e]
    exact h1
  obtain ⟨h1, H₀, h2⟩ := hs
  refine ⟨fun η hη => (h1 η hη).congr_of_eventuallyEq (hev η hη).symm, H₀, fun q hq => ⟨?_, fun b => ?_⟩⟩
  · exact hm _ _ _ _ (fun η hη => by rw [he η hη]) (h2 q hq).1
  · refine hm _ _ _ _ (fun η hη => ?_) ((h2 q hq).2 b)
    unfold bondGradNorm
    rw [(hev η hη).fderiv_eq]
theorem hasLocalSize_mono {ι : Type} [Fintype ι] [DecidableEq ι] {ρ x κ h h' : ℝ} {r : ℝ → ℝ}
    {Ψ : BondField ι → ℝ} {Cq Cq' : ℕ → ℝ} {dZ : ι → ℝ} {H : BondField ι → ℝ}
    (hCq : ∀ q, |Cq q| ≤ Cq' q) (h0 : 0 ≤ h) (hh : h ≤ h')
    (hs : HasLocalSize ρ r Ψ Cq x κ h dZ H) :
    HasLocalSize ρ r Ψ Cq' x κ h' dZ H := by
  have hm : ∀ (G : BondField ι → ℝ) (q : ℕ) (B B' : ℝ), |B| ≤ B' →
      MomentBound r Ψ G q B → MomentBound r Ψ G q B' := fun G q B B' h2 h3 => by
    refine ⟨h3.1, h3.2.trans ?_⟩
    calc B ^ q ≤ |B ^ q| := le_abs_self _
      _ = |B| ^ q := abs_pow _ _
      _ ≤ B' ^ q := pow_le_pow_left₀ (abs_nonneg _) h2 _
  have hCq0 : ∀ q, 0 ≤ Cq' q := fun q => (abs_nonneg _).trans (hCq q)
  obtain ⟨h1, H₀, h2⟩ := hs
  refine ⟨h1, H₀, fun q hq' => ⟨?_, fun b => ?_⟩⟩
  · refine hm _ _ _ _ ?_ (h2 q hq').1
    rw [abs_mul, abs_of_nonneg h0]
    exact mul_le_mul (hCq q) hh h0 (hCq0 q)
  · have hs0 := Real.sqrt_nonneg x
    have he := (Real.exp_pos (-(2 * κ * dZ b))).le
    refine hm _ _ _ _ ?_ ((h2 q hq').2 b)
    rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg hs0, abs_of_nonneg h0, abs_of_nonneg he]
    exact mul_le_mul_of_nonneg_right (mul_le_mul (mul_le_mul_of_nonneg_right (hCq q) hs0) hh h0
      (mul_nonneg (hCq0 q) hs0)) he
theorem hasLocalSize_neg {ι : Type} [Fintype ι] [DecidableEq ι] {ρ x κ h : ℝ} {r : ℝ → ℝ}
    {Ψ : BondField ι → ℝ} {Cq : ℕ → ℝ} {dZ : ι → ℝ} {H : BondField ι → ℝ}
    (hs : HasLocalSize ρ r Ψ Cq x κ h dZ H) : HasLocalSize ρ r Ψ Cq x κ h dZ fun η => - H η := by
  obtain ⟨h1, H₀, h2⟩ := hs
  refine ⟨fun η hη => (h1 η hη).fun_neg, -H₀, fun q hq => ⟨?_, fun b => ?_⟩⟩
  · have e : ∀ η, |- H η - -H₀| = |H η - H₀| := fun η => by
      rw [show - H η - -H₀ = -(H η - H₀) by ring, abs_neg]
    have := (h2 q hq).1
    unfold MomentBound at this ⊢
    simp only [e]
    exact this
  · have e : bondGradNorm (fun η => - H η) b = bondGradNorm H b := by
      funext η
      unfold bondGradNorm
      have : fderiv ℝ (fun η => - H η) η = - fderiv ℝ H η := fderiv_fun_neg
      rw [this, ContinuousLinearMap.neg_comp, norm_neg]
    rw [e]
    exact (h2 q hq).2 b
theorem iteratedFDeriv_finsetSum_apply {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {J : Type}
    (S : Finset J) (k : ℕ)
    (g : J → E → ℝ) (x : E) (hs : ∀ j ∈ S, ContDiffAt ℝ k (g j) x) (v : Fin k → E) :
    iteratedFDeriv ℝ k (fun τ => ∑ j ∈ S, g j τ) x v = ∑ j ∈ S, iteratedFDeriv ℝ k (g j) x v := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    have : iteratedFDeriv ℝ k (fun _ : E => (0 : ℝ)) = 0 := iteratedFDeriv_fun_zero
    rw [this]
    rfl
  | insert a S ha ih =>
    simp only [Finset.sum_insert ha]
    have h1 := hs a (Finset.mem_insert_self _ _)
    have h2 : ∀ j ∈ S, ContDiffAt ℝ k (g j) x := fun j hj => hs j (Finset.mem_insert_of_mem hj)
    have h3 : ContDiffAt ℝ k (fun τ => ∑ j ∈ S, g j τ) x := ContDiffAt.sum fun j hj => h2 j hj
    have := iteratedFDeriv_add_apply (i := k) h1 h3
    have e : (fun τ => g a τ + ∑ j ∈ S, g j τ) = g a + fun τ => ∑ j ∈ S, g j τ := rfl
    rw [e, this]
    simp only [_root_.add_apply]
    rw [ih h2]
theorem expUnit_zero : expUnit (0 : imaginaryQuaternions) = 1 := by apply _root_.YangMills.Construction.TorusFields.expUnit_zero <;> assumption
theorem leftTranslate_bondSpread_zero {k : ℕ} (c : Fin k → F.Site F.top × Fin 4)
    (X : Fin k → imaginaryQuaternions) (V : F.GaugeField F.top) :
    leftTranslate (bondSpread c X 0) V = V := by apply _root_.YangMills.SharedProofs.p2043 <;> assumption
theorem continuous_expUnit : Continuous expUnit := by apply _root_.YangMills.Construction.TorusFields.continuous_expUnit <;> assumption
theorem eventually_isSmallCurvature_leftTranslate {k : ℕ} (hfin : Finite F.Cell) {s : ℝ}
    (c : Fin k → F.Site F.top × Fin 4)
    (X : Fin k → imaginaryQuaternions) {V : F.GaugeField F.top} (hV : IsSmallCurvature s V) :
    ∀ᶠ τ : Fin k → ℝ in 𝓝 0, IsSmallCurvature s (leftTranslate (bondSpread c X τ) V) := by apply _root_.YangMills.Construction.InterpolatedBirths.eventually_isSmallCurvature_translate <;> assumption
def sublistEmbedding {j k : ℕ} (ι : Fin j → Fin k) : (Fin j → ℝ) →L[ℝ] (Fin k → ℝ) :=
  ∑ l : Fin j, (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin j => ℝ) l).smulRight
    (Pi.single (ι l) (1 : ℝ))
theorem sublistEmbedding_single {j k : ℕ} (ι : Fin j → Fin k) (l : Fin j) :
    sublistEmbedding ι (Pi.single l 1) = Pi.single (ι l) 1 := by
  classical
  simp only [sublistEmbedding, _root_.sum_apply, ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.proj_apply]
  rw [Finset.sum_eq_single l]
  · simp
  · intro b _ hb
    simp [Pi.single_eq_of_ne hb]
  · simp
theorem bondSpread_comp {j k n : ℕ} (c : Fin k → F.Site n × Fin 4) (X : Fin k → imaginaryQuaternions)
    (ι : Fin j → Fin k)
    (τ : Fin j → ℝ) : bondSpread (c ∘ ι) (X ∘ ι) τ = bondSpread c X (sublistEmbedding ι τ) := by
  classical
  funext y i
  simp only [bondSpread, sublistEmbedding, _root_.sum_apply,
    ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.proj_apply, Function.comp]
  have e : ∀ m : Fin k, (∑ l : Fin j, τ l • (Pi.single (ι l) (1 : ℝ) : Fin k → ℝ)) m =
      ∑ l : Fin j, if ι l = m then τ l else 0 := fun m => by
    rw [Finset.sum_apply]
    refine Finset.sum_congr rfl fun l _ => ?_
    by_cases h : ι l = m
    · subst h; simp
    · simp [h]
  simp only [e]
  have : ∀ m : Fin k, (if c m = (y, i) then (∑ l : Fin j, if ι l = m then τ l else 0) • X m else 0) =
      ∑ l : Fin j, if ι l = m then (if c m = (y, i) then τ l • X m else 0) else 0 := fun m => by
    split_ifs with h
    · rw [Finset.sum_smul]
      refine Finset.sum_congr rfl fun l _ => ?_
      split_ifs <;> simp
    · simp
  simp only [this]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [Finset.sum_eq_single (ι l)]
  · simp
  · intro b _ hb
    simp [Ne.symm hb]
  · simp
theorem iteratedFDeriv_comp_continuousLinearMap_apply {E₁ E₂ : Type*} [NormedAddCommGroup E₁]
    [NormedSpace ℝ E₁] [NormedAddCommGroup E₂]
    [NormedSpace ℝ E₂] (Λ : E₁ →L[ℝ] E₂) {f : E₂ → ℝ} {x : E₁} {n : ℕ} (hf : ContDiffAt ℝ n f (Λ x))
    (v : Fin n → E₁) :
    iteratedFDeriv ℝ n (f ∘ Λ) x v = iteratedFDeriv ℝ n f (Λ x) fun l => Λ (v l) := by
  obtain ⟨u, hu, h⟩ := hf.contDiffOn (m := n) le_rfl (by simp)
  obtain ⟨U, hUu, hU, hxU⟩ := mem_nhds_iff.1 hu
  have hfU := h.mono hUu
  have hΛ : IsOpen (Λ ⁻¹' U) := hU.preimage Λ.continuous
  have h' := Λ.iteratedFDerivWithin_comp_right hfU hU.uniqueDiffOn hΛ.uniqueDiffOn
    (x := x) hxU (i := n) le_rfl
  rw [iteratedFDerivWithin_of_isOpen n hΛ (show x ∈ Λ ⁻¹' U from hxU),
    iteratedFDerivWithin_of_isOpen n hU hxU] at h'
  rw [h']
  rfl
theorem iteratedFDeriv_single_eq_bondDeriv {j k : ℕ} (G : F.GaugeField F.top → ℝ)
    (V : F.GaugeField F.top) (c : Fin k → F.Site F.top × Fin 4)
    (X : Fin k → imaginaryQuaternions) (ι : Fin j → Fin k)
    (hs : ContDiffAt ℝ j (fun τ : Fin k → ℝ => G (leftTranslate (bondSpread c X τ) V)) 0) :
    iteratedFDeriv ℝ j (fun τ : Fin k → ℝ => G (leftTranslate (bondSpread c X τ) V)) 0
        (fun l => Pi.single (ι l) 1) = bondDeriv G V (c ∘ ι) (X ∘ ι) := by
  have e : (fun τ : Fin j → ℝ => G (leftTranslate (bondSpread (c ∘ ι) (X ∘ ι) τ) V)) =
      (fun τ : Fin k → ℝ => G (leftTranslate (bondSpread c X τ) V)) ∘ sublistEmbedding ι := by
    funext τ
    simp only [Function.comp, bondSpread_comp]
  have h0 : sublistEmbedding ι (0 : Fin j → ℝ) = 0 := map_zero _
  unfold bondDeriv
  rw [e, iteratedFDeriv_comp_continuousLinearMap_apply (sublistEmbedding ι) (by rw [h0]; exact hs), h0]
  simp only [sublistEmbedding_single]
theorem extendByZero_id (ζ : StepVariable (finiteCells F)) :
    extendByZero (id : ↥(chordBonds (finiteCells F)) → _) Finset.univ ζ = ζ := by apply _root_.YangMills.Construction.InterpolatedBirths.extendByZero_id <;> assumption
def lawAtTop (V : F.GaugeField F.top) (Ψ : StepVariable (finiteCells F) → ℝ) :
    LawOnBondVariables ↥(chordBonds (finiteCells F)) := ⟨F, V, id, Finset.univ, Ψ⟩
theorem convexCombinationExponent_lawAtTop (lam x : ℝ) (V : F.GaugeField F.top)
    (Ψ : StepVariable (finiteCells F) → ℝ) :
    convexCombinationExponent lam x (fun _ : Fin 1 => (1 : ℝ)) (fun _ => lawAtTop V Ψ) = Ψ := by
  funext ζ
  simp only [convexCombinationExponent, LawOnBondVariables.exponent, frozenExponent, lawAtTop,
    Fin.sum_univ_one]
  rw [extendByZero_id, Finset.sdiff_self]
  simp
end ResponseInTheExpansion
end YangMills.Construction
end
