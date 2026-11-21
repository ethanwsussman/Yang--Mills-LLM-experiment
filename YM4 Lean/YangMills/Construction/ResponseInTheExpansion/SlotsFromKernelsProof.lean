import YangMills.Construction.ClusterExpansionOfAStep.LawsOnProductsOfBalls
import YangMills.Construction.ResponseInTheExpansion.CalculusOfTheColdHalf
import YangMills.Construction.ResponseInTheExpansion.SizeOfASumOfObservables
import YangMills.Construction.ResponseInTheExpansion.SlotsFromKernels
import YangMills.Construction.SummableBoundsOfTheFlow.DerivativeInTheTopAlongASegmentProof
import YangMills.Construction.SummableBoundsOfTheFlow.ObservablesInTheLawsBetweenProof
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Topology
open MeasureTheory
namespace YangMills.Construction
open BlockAverages hiding bondSpread
open ColdStepAtMirrorFrames Interpolation TorusComparison ConvexObservables SmoothSlices ResponseInTheExpansion
namespace WeightedResponses
namespace KernelSlots
section BallLaw
variable {ι : Type} [Fintype ι] [DecidableEq ι]
def bondBall (ι : Type) (ρ : ℝ) : Set (BondField ι) := {η | ∀ b, ‖η b‖ < ρ}
theorem isOpen_bondBall (ρ : ℝ) : IsOpen (bondBall ι ρ) := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.BallLaws.isOpen_ballProduct <;> assumption
variable {ρ : ℝ} {p : ℝ → ℝ} {Ψ : BondField ι → ℝ}
structure BallLawFacts (ρ : ℝ) (p : ℝ → ℝ) (Ψ : BondField ι → ℝ) : Prop where
  isProbability : IsProbabilityMeasure (normalizedBallLaw (cutoffFactor ρ p) Ψ)
  integral_eq : ∀ f : BondField ι → ℝ, ∫ η, f η ∂normalizedBallLaw (cutoffFactor ρ p) Ψ = ballExpectation (cutoffFactor ρ p) Ψ f
  integrable_iff : ∀ f : BondField ι → ℝ, Integrable f (normalizedBallLaw (cutoffFactor ρ p) Ψ) ↔
    Integrable fun η => f η * ballDensity (cutoffFactor ρ p) Ψ η
  ae_mem_ball : ∀ᵐ η ∂normalizedBallLaw (cutoffFactor ρ p) Ψ, ∀ b, ‖η b‖ < ρ
theorem aestronglyMeasurable_of_continuousOn_ball (hL : BallLawFacts ρ p Ψ) {g : BondField ι → ℝ}
    (hg : ContinuousOn g (bondBall ι ρ)) :
    AEStronglyMeasurable g (normalizedBallLaw (cutoffFactor ρ p) Ψ) := by
  have hm : MeasurableSet (bondBall ι ρ) := (isOpen_bondBall ρ).measurableSet
  have h1 := hg.aestronglyMeasurable (μ := normalizedBallLaw (cutoffFactor ρ p) Ψ) hm
  rwa [Measure.restrict_eq_self_of_ae_mem (by exact hL.ae_mem_ball)] at h1
theorem pow_weighted_sum_le (E : ℝ) (w t : ι → ℝ) (hE : 0 ≤ E) (hw : ∀ b, 0 ≤ w b) (ht : ∀ b, 0 ≤ t b) (q : ℕ) (hq : 1 ≤ q) :
    (E + ∑ b, w b * t b) ^ q ≤ (E + ∑ b, w b) ^ (q - 1) * (E + ∑ b, w b * t b ^ q) := by
  set W := E + ∑ b, w b with hW
  have hs0 : 0 ≤ ∑ b, w b := Finset.sum_nonneg fun b _ => hw b
  have hW0 : 0 ≤ W := add_nonneg hE hs0
  rcases hW0.eq_or_lt with h0 | hpos
  · have hE0 : E = 0 := by linarith
    have hs : ∑ b, w b = 0 := by linarith
    have hw0 : ∀ b, w b = 0 := fun b =>
      (Finset.sum_eq_zero_iff_of_nonneg fun b _ => hw b).1 hs b (Finset.mem_univ b)
    simp [hE0, hw0, show q ≠ 0 by omega]
  · have hsum : ∑ o : Option ι, (o.elim E w) / W = 1 := by
      rw [Fintype.sum_option]
      simp only [Option.elim]
      rw [← Finset.sum_div, ← add_div, ← hW, div_self hpos.ne']
    have hJ := Real.pow_arith_mean_le_arith_mean_pow (Finset.univ : Finset (Option ι))
      (fun o => (o.elim E w) / W) (fun o => o.elim 1 t)
      (fun o _ => by
        cases o with
        | none => exact div_nonneg hE hW0
        | some b => exact div_nonneg (hw b) hW0) hsum
      (fun o _ => by
        cases o with
        | none => exact zero_le_one
        | some b => exact ht b) q
    rw [Fintype.sum_option, Fintype.sum_option] at hJ
    simp only [Option.elim, mul_one, one_pow] at hJ
    have e1 : E / W + ∑ b, w b / W * t b = (E + ∑ b, w b * t b) / W := by
      rw [add_div, Finset.sum_div]
      congr 1
      exact Finset.sum_congr rfl fun b _ => by ring
    have e2 : E / W + ∑ b, w b / W * t b ^ q = (E + ∑ b, w b * t b ^ q) / W := by
      rw [add_div, Finset.sum_div]
      congr 1
      exact Finset.sum_congr rfl fun b _ => by ring
    rw [e1, e2, div_pow, div_le_div_iff₀ (pow_pos hpos q) hpos] at hJ
    obtain ⟨n, rfl⟩ : ∃ n, q = n + 1 := ⟨q - 1, by omega⟩
    simp only [Nat.add_sub_cancel]
    have : (E + ∑ b, w b * t b) ^ (n + 1) * W ≤ W ^ n * (E + ∑ b, w b * t b ^ (n + 1)) * W := by
      calc _ ≤ _ := hJ
        _ = _ := by rw [pow_succ]; ring
    exact le_of_mul_le_mul_right this hpos
theorem momentBound_of_quadratic (hL : BallLawFacts ρ p Ψ) {x : ℝ} (hx : 0 < x) {m : ℕ → ℝ} (hm : ∀ q, 0 ≤ m q) (hρ : 0 < ρ)
    (hmom : ∀ (q : ℕ) (b : ι), ballExpectation (cutoffFactor ρ p) Ψ (fun η => ‖η b‖ ^ (2 * q)) ≤ m q * (x ^ q)⁻¹)
    {f : BondField ι → ℝ} (hf : ContinuousOn f (bondBall ι ρ)) {E β : ℝ} {w : ι → ℝ} (hE : 0 ≤ E) (hβ : 0 ≤ β)
    (hw : ∀ b, 0 ≤ w b) (hb : ∀ η ∈ bondBall ι ρ, |f η| ≤ β * (E + ∑ b, w b * (x * ‖η b‖ ^ 2))) (q : ℕ) (hq : 1 ≤ q) :
    MomentBound (cutoffFactor ρ p) Ψ f q ((1 + m q) * β * (E + ∑ b, w b)) := by
  have := hL.isProbability
  set μ := normalizedBallLaw (cutoffFactor ρ p) Ψ with hμ
  set W := E + ∑ b, w b with hW
  have hW0 : 0 ≤ W := add_nonneg hE (Finset.sum_nonneg fun b _ => hw b)
  have hI : ∀ b : ι, Integrable (fun η : BondField ι => ‖η b‖ ^ (2 * q)) μ := fun b => by
    refine Integrable.of_bound (aestronglyMeasurable_of_continuousOn_ball hL ?_) (ρ ^ (2 * q)) ?_
    · exact ((continuous_norm.comp (continuous_apply b)).pow _).continuousOn
    · filter_upwards [hL.ae_mem_ball] with η hη
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      exact pow_le_pow_left₀ (norm_nonneg _) (hη b).le _
  let g : BondField ι → ℝ := fun η => β ^ q * (W ^ (q - 1) * (E + ∑ b, w b * (x ^ q * ‖η b‖ ^ (2 * q))))
  have hgI : Integrable g μ := by
    refine ((integrable_const E).add (integrable_finsetSum _ fun b _ => ((hI b).const_mul _).const_mul _)).const_mul _
      |>.const_mul _
  have hpt : ∀ η ∈ bondBall ι ρ, |f η| ^ q ≤ g η := fun η hη => by
    have ht : ∀ b, 0 ≤ x * ‖η b‖ ^ 2 := fun b => by positivity
    have h1 := pow_weighted_sum_le E w (fun b => x * ‖η b‖ ^ 2) hE hw ht q hq
    have e : ∀ b, (x * ‖η b‖ ^ 2) ^ q = x ^ q * ‖η b‖ ^ (2 * q) := fun b => by
      rw [mul_pow, ← pow_mul]
    simp only [e] at h1
    calc |f η| ^ q ≤ (β * (E + ∑ b, w b * (x * ‖η b‖ ^ 2))) ^ q := pow_le_pow_left₀ (abs_nonneg _) (hb η hη) _
      _ = β ^ q * (E + ∑ b, w b * (x * ‖η b‖ ^ 2)) ^ q := mul_pow _ _ _
      _ ≤ g η := mul_le_mul_of_nonneg_left h1 (by positivity)
  have hae : AEStronglyMeasurable (fun η => |f η| ^ q) μ := aestronglyMeasurable_of_continuousOn_ball hL (hf.abs.pow q)
  have hle : ∀ᵐ η ∂μ, |f η| ^ q ≤ g η := by
    filter_upwards [hL.ae_mem_ball] with η hη using hpt η hη
  have hfi : Integrable (fun η => |f η| ^ q) μ := by
    refine Integrable.mono' hgI hae ?_
    filter_upwards [hle] with η hη
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact hη
  refine ⟨(hL.integrable_iff _).1 hfi, ?_⟩
  rw [← hL.integral_eq]
  have h1 : ∫ η, |f η| ^ q ∂μ ≤ ∫ η, g η ∂μ := integral_mono_ae hfi hgI hle
  refine h1.trans ?_
  have h2 : ∫ η, g η ∂μ = β ^ q * (W ^ (q - 1) * (E + ∑ b, w b * (x ^ q * ∫ η, ‖η b‖ ^ (2 * q) ∂μ))) := by
    simp only [g]
    rw [integral_const_mul, integral_const_mul, integral_add (integrable_const E)
      (integrable_finsetSum _ fun b _ => ((hI b).const_mul _).const_mul _),
      integral_finsetSum _ fun b _ => ((hI b).const_mul _).const_mul _]
    simp only [integral_const_mul, integral_const, probReal_univ, one_smul]
  rw [h2]
  have hmq := hm q
  have hb1 : ∀ b, x ^ q * ∫ η, ‖η b‖ ^ (2 * q) ∂μ ≤ m q := fun b => by
    rw [hL.integral_eq]
    have hxq : 0 < x ^ q := pow_pos hx q
    calc x ^ q * ballExpectation (cutoffFactor ρ p) Ψ (fun η => ‖η b‖ ^ (2 * q)) ≤ x ^ q * (m q * (x ^ q)⁻¹) :=
          mul_le_mul_of_nonneg_left (hmom q b) hxq.le
      _ = m q := by field_simp
  have h3 : E + ∑ b, w b * (x ^ q * ∫ η, ‖η b‖ ^ (2 * q) ∂μ) ≤ (1 + m q) * W := by
    have h4 : ∑ b, w b * (x ^ q * ∫ η, ‖η b‖ ^ (2 * q) ∂μ) ≤ ∑ b, w b * m q :=
      Finset.sum_le_sum fun b _ => mul_le_mul_of_nonneg_left (hb1 b) (hw b)
    rw [← Finset.sum_mul] at h4
    have h5 : 0 ≤ (∑ b, w b) := Finset.sum_nonneg fun b _ => hw b
    have h6 : 0 ≤ E * m q := mul_nonneg hE hmq
    have h7 : (1 + m q) * W = E + (∑ b, w b) + E * m q + (∑ b, w b) * m q := by rw [hW]; ring
    rw [h7]
    linarith
  obtain ⟨n, rfl⟩ : ∃ n, q = n + 1 := ⟨q - 1, by omega⟩
  simp only [Nat.add_sub_cancel] at *
  have h8 : 1 ≤ (1 + m (n + 1)) ^ n := one_le_pow₀ (by linarith)
  calc β ^ (n + 1) * (W ^ n * (E + ∑ b, w b * (x ^ (n + 1) * ∫ η, ‖η b‖ ^ (2 * (n + 1)) ∂μ)))
      ≤ β ^ (n + 1) * (W ^ n * ((1 + m (n + 1)) * W)) := by gcongr
    _ = (β * W) ^ (n + 1) * (1 + m (n + 1)) := by rw [mul_pow, pow_succ W]; ring
    _ ≤ (β * W) ^ (n + 1) * ((1 + m (n + 1)) * (1 + m (n + 1)) ^ n) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        nlinarith
    _ = ((1 + m (n + 1)) * β * W) ^ (n + 1) := by
        rw [mul_pow, mul_pow, mul_pow, pow_succ (1 + m (n + 1))]
        ring
theorem abs_ballExpectation_le_of_momentBound (hL : BallLawFacts ρ p Ψ) {f : BondField ι → ℝ} {B : ℝ}
    (h : MomentBound (cutoffFactor ρ p) Ψ f 1 B) : |ballExpectation (cutoffFactor ρ p) Ψ f| ≤ B := by
  obtain ⟨h1, h2⟩ := h
  rw [← hL.integral_eq]
  have e : (fun η => |f η| ^ 1) = fun η => |f η| := by
    funext η
    rw [pow_one]
  refine (abs_integral_le_integral_abs).trans ?_
  rw [e] at h2
  rw [hL.integral_eq]
  simpa using h2
theorem momentBound_congr {f f' : BondField ι → ℝ} {q : ℕ} {B : ℝ}
    (hz : ∀ η : BondField ι, ¬ (∀ b, ‖η b‖ < ρ) → ballDensity (cutoffFactor ρ p) Ψ η = 0)
    (he : ∀ η : BondField ι, (∀ b, ‖η b‖ < ρ) → f η = f' η) (h : MomentBound (cutoffFactor ρ p) Ψ f q B) :
    MomentBound (cutoffFactor ρ p) Ψ f' q B := by
  have e : (fun η => |f' η| ^ q * ballDensity (cutoffFactor ρ p) Ψ η) =
      fun η => |f η| ^ q * ballDensity (cutoffFactor ρ p) Ψ η := by
    funext η
    by_cases hη : ∀ b, ‖η b‖ < ρ
    · rw [he η hη]
    · rw [hz η hη]; simp
  unfold MomentBound ballExpectation at *
  rw [e]
  exact h
end BallLaw
section TopDerivatives
variable {F : BlockFrame}
theorem iteratedFDeriv_cast {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {n m : ℕ} (h : n = m) (f : E → ℝ) (x : E)
    (v : Fin n → E) :
    iteratedFDeriv ℝ n f x v = iteratedFDeriv ℝ m f x (fun i => v (Fin.cast h.symm i)) := by apply _root_.YangMills.Construction.FieldDerivSegment.iteratedFDeriv_order_cast <;> assumption
def incrementMap {k : ℕ} (b : ↥(chordBonds (finiteCells F))) (u : EuclideanSpace ℝ (Fin 3)) :
    (Fin (1 + k) → ℝ) →L[ℝ] (Fin k → ℝ) × StepVariable (finiteCells F) :=
  (ContinuousLinearMap.pi fun i => ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (1 + k) => ℝ) (Fin.natAdd 1 i)).prod
    ((ContinuousLinearMap.single ℝ (fun _ : ↥(chordBonds (finiteCells F)) => EuclideanSpace ℝ (Fin 3)) b).comp
      ((ContinuousLinearMap.toSpanSingleton ℝ u).comp
        (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (1 + k) => ℝ) (Fin.castAdd k 0))))
theorem incrementMap_apply {k : ℕ} (b : ↥(chordBonds (finiteCells F))) (u : EuclideanSpace ℝ (Fin 3))
    (σ : Fin (1 + k) → ℝ) :
    incrementMap b u σ = (fun i => σ (Fin.natAdd 1 i), Pi.single b (σ (Fin.castAdd k 0) • u)) := rfl
theorem jointDisplacement_eq {k : ℕ} (G : StepVariable (finiteCells F) → F.GaugeField F.top → ℝ) (ζ : StepVariable (finiteCells F))
    (V : F.GaugeField F.top) (b : ↥(chordBonds (finiteCells F))) (u : EuclideanSpace ℝ (Fin 3))
    (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions) :
    jointDisplacement G ζ V ![b] ![u] c X = fun σ =>
      (fun q : (Fin k → ℝ) × StepVariable (finiteCells F) => G q.2 (leftTranslate (bondSpread c X q.1) V))
        ((0, ζ) + incrementMap b u σ) := by
  funext σ
  unfold jointDisplacement displacedPoint
  rw [incrementMap_apply]
  simp
abbrev topDeriv {k : ℕ} (G : AboveFrames F) (V : F.GaugeField F.top) (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions) :
    StepVariable (finiteCells F) → ℝ := fun η => bondDeriv (G η) V c X
theorem fderiv_topDeriv_single (hS : IteratedFDerivSlices) {V : F.GaugeField F.top} {G : AboveFrames F} {k : ℕ} (hk : k ≤ 3)
    (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions) {ζ : StepVariable (finiteCells F)}
    (hJ : ContDiffAt ℝ 4 (fun q : (Fin k → ℝ) × StepVariable (finiteCells F) =>
      G q.2 (leftTranslate (bondSpread c X q.1) V)) (0, ζ))
    (b : ↥(chordBonds (finiteCells F))) (u : EuclideanSpace ℝ (Fin 3)) :
    fderiv ℝ (topDeriv G V c X) ζ (Pi.single b u) = jointMixedDeriv G ζ V ![b] ![u] c X := by
  set J : (Fin k → ℝ) × StepVariable (finiteCells F) → ℝ := fun q => G q.2 (leftTranslate (bondSpread c X q.1) V) with hJdef
  have hJk : ContDiffAt ℝ (k + 1 : ℕ) J (0, ζ) := ContDiffAt.of_le hJ (by exact_mod_cast (by omega : k + 1 ≤ 4))
  have hJk' : ContDiffAt ℝ (1 + k : ℕ) J ((0, ζ) + incrementMap b u 0) := by
    rw [map_zero, add_zero]
    exact ContDiffAt.of_le hJ (by exact_mod_cast (by omega : 1 + k ≤ 4))
  have h1 := hS.2.2 (Fin k → ℝ) (StepVariable (finiteCells F)) J k (fun l => Pi.single l 1) ζ (Pi.single b u) hJk
  have h2 := hS.1 ((Fin k → ℝ) × StepVariable (finiteCells F)) (Fin (1 + k) → ℝ) J (incrementMap b u) (0, ζ) 0 (1 + k)
    (fun i => Pi.single i 1) hJk'
  have e1 : jointMixedDeriv G ζ V ![b] ![u] c X = iteratedFDeriv ℝ (1 + k) (fun σ => J ((0, ζ) + incrementMap b u σ)) 0
      (fun i => Pi.single i 1) := by
    unfold jointMixedDeriv
    rw [jointDisplacement_eq]
  rw [e1, h2, map_zero, add_zero, iteratedFDeriv_cast (Nat.add_comm 1 k)]
  refine h1.trans ?_
  congr 1
  funext i
  refine Fin.cases ?_ (fun i => ?_) i
  · rw [Fin.cons_zero, incrementMap_apply]
    have e0 : Fin.cast (Nat.add_comm 1 k).symm (0 : Fin (k + 1)) = Fin.castAdd k 0 := Fin.ext rfl
    refine Prod.ext ?_ ?_
    · funext l
      rw [e0]
      have : Fin.natAdd 1 l ≠ Fin.castAdd k 0 := fun h => by
        have := congrArg Fin.val h
        simp at this
      simp [Pi.single_apply, this]
    · rw [e0]
      simp
  · rw [Fin.cons_succ, incrementMap_apply]
    have e0 : Fin.cast (Nat.add_comm 1 k).symm (Fin.succ i) = Fin.natAdd 1 i := Fin.ext (by simp; omega)
    refine Prod.ext ?_ ?_
    · funext l
      rw [e0]
      by_cases hl : l = i
      · subst hl
        simp
      · have : Fin.natAdd 1 l ≠ Fin.natAdd 1 i := fun h => hl (by
          have := congrArg Fin.val h
          simp at this
          exact Fin.ext this)
        simp [Pi.single_apply, this, hl]
    · rw [e0]
      have : Fin.castAdd k (0 : Fin 1) ≠ Fin.natAdd 1 i := fun h => by
        have := congrArg Fin.val h
        simp at this
        omega
      simp [Pi.single_apply, this]
theorem contDiffAt_topDeriv (hS : IteratedFDerivSlices) {V : F.GaugeField F.top} {G : AboveFrames F} {k : ℕ} (hk : k ≤ 3)
    (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions) {ζ : StepVariable (finiteCells F)}
    (hJ : ContDiffAt ℝ 4 (fun q : (Fin k → ℝ) × StepVariable (finiteCells F) =>
      G q.2 (leftTranslate (bondSpread c X q.1) V)) (0, ζ)) : ContDiffAt ℝ 1 (topDeriv G V c X) ζ := by
  have h := hS.2.1 (Fin k → ℝ) (StepVariable (finiteCells F))
    (fun q => G q.2 (leftTranslate (bondSpread c X q.1) V)) k 1 (fun l => Pi.single l 1) ζ
    (ContDiffAt.of_le hJ (by exact_mod_cast (by omega : 1 + k ≤ 4)))
  exact h
theorem abs_apply_le_of_unit {ℓ : BondVector →L[ℝ] ℝ} {D : ℝ} (h : ∀ u : BondVector, ‖u‖ = 1 → |ℓ u| ≤ D) (e : BondVector)
    (hD : 0 ≤ D) : |ℓ e| ≤ D * ‖e‖ := by
  by_cases h0 : e = 0
  · simp [h0]
  · have hn : ‖e‖ ≠ 0 := norm_ne_zero_iff.mpr h0
    have hu1 : ‖‖e‖⁻¹ • e‖ = 1 := by
      rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hn]
    have hdec : e = ‖e‖ • (‖e‖⁻¹ • e) := by
      rw [smul_smul, mul_inv_cancel₀ hn, one_smul]
    conv_lhs => rw [hdec]
    rw [map_smul, smul_eq_mul, abs_mul, abs_norm, mul_comm]
    exact mul_le_mul_of_nonneg_right (h _ hu1) (norm_nonneg _)
theorem abs_sub_le_of_single_fderiv {ρ : ℝ} {g : StepVariable (finiteCells F) → ℝ} {D : ↥(chordBonds (finiteCells F)) → ℝ}
    (hD0 : ∀ b, 0 ≤ D b)
    (hdiff : ∀ ζ : StepVariable (finiteCells F), (∀ b, ‖ζ b‖ ≤ ρ) → DifferentiableAt ℝ g ζ)
    (hD : ∀ ζ : StepVariable (finiteCells F), (∀ b, ‖ζ b‖ ≤ ρ) → ∀ (b : ↥(chordBonds (finiteCells F))) (u : BondVector),
      ‖u‖ = 1 → |fderiv ℝ g ζ (Pi.single b u)| ≤ D b)
    {η : StepVariable (finiteCells F)} (hη : ∀ b, ‖η b‖ ≤ ρ) : |g η - g 0| ≤ ∑ b, ‖η b‖ * D b := by
  classical
  have hseg : ∀ v ∈ Set.Icc (0 : ℝ) 1, ∀ b, ‖(v • η) b‖ ≤ ρ := fun v hv b => by
    rw [Pi.smul_apply, norm_smul, Real.norm_of_nonneg hv.1]
    calc v * ‖η b‖ ≤ 1 * ‖η b‖ := mul_le_mul_of_nonneg_right hv.2 (norm_nonneg _)
      _ = ‖η b‖ := one_mul _
      _ ≤ ρ := hη b
  have hbound : ∀ ζ : StepVariable (finiteCells F), (∀ b, ‖ζ b‖ ≤ ρ) →
      ‖fderiv ℝ g ζ η‖ ≤ ∑ b, ‖η b‖ * D b := fun ζ hζ => by
    have hsum : η = ∑ b, Pi.single b (η b) := (Finset.univ_sum_single η).symm
    conv_lhs => rw [hsum, map_sum]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun b _ => ?_)
    have h1 := abs_apply_le_of_unit (ℓ := (fderiv ℝ g ζ).comp
      (ContinuousLinearMap.single ℝ (fun _ : ↥(chordBonds (finiteCells F)) => BondVector) b))
      (D := D b) (fun u hu => hD ζ hζ b u hu) (η b) (hD0 b)
    rw [Real.norm_eq_abs, mul_comm]
    exact h1
  have hder : ∀ v ∈ Set.Icc (0 : ℝ) 1,
      HasDerivWithinAt (fun v : ℝ => g (v • η)) (fderiv ℝ g (v • η) η) (Set.Icc (0 : ℝ) 1) v := fun v hv => by
    have h1 : HasDerivAt (fun v : ℝ => v • η) ((1 : ℝ) • η) v := (hasDerivAt_id v).smul_const η
    rw [one_smul] at h1
    exact ((hdiff _ (hseg v hv)).hasFDerivAt.comp_hasDerivAt v h1).hasDerivWithinAt
  have := norm_image_sub_le_of_norm_deriv_le_segment_01' hder
    (fun v hv => hbound _ (hseg v ⟨hv.1, hv.2.le⟩))
  simpa using this
theorem bondGradNorm_le_of_unit {g : StepVariable (finiteCells F) → ℝ} {ζ : StepVariable (finiteCells F)}
    {b : ↥(chordBonds (finiteCells F))} {D : ℝ} (hD0 : 0 ≤ D)
    (h : ∀ u : BondVector, ‖u‖ = 1 → |fderiv ℝ g ζ (Pi.single b u)| ≤ D) : bondGradNorm g b ζ ≤ D := by
  unfold bondGradNorm
  refine ContinuousLinearMap.opNorm_le_bound _ hD0 fun e => ?_
  have h1 := abs_apply_le_of_unit (ℓ := (fderiv ℝ g ζ).comp
    (ContinuousLinearMap.single ℝ (fun _ : ↥(chordBonds (finiteCells F)) => BondVector) b))
    (D := D) h e hD0
  rwa [Real.norm_eq_abs]
theorem jointMixedDeriv_two (hS : IteratedFDerivSlices) {V : F.GaugeField F.top} {G : AboveFrames F}
    {ζ : StepVariable (finiteCells F)} (hA : ContDiffAt ℝ 2 (fun η => G η V) ζ)
    (b₀ b₁ : ↥(chordBonds (finiteCells F))) (u₀ u₁ : BondVector) :
    jointMixedDeriv G ζ V ![b₀, b₁] ![u₀, u₁] ![] ![] =
      fderiv ℝ (fderiv ℝ fun η => G η V) ζ (Pi.single b₀ u₀) (Pi.single b₁ u₁) := by
  classical
  set A : StepVariable (finiteCells F) → ℝ := fun η => G η V with hAdef
  let L : (Fin (2 + 0) → ℝ) →L[ℝ] StepVariable (finiteCells F) :=
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (2 + 0) => ℝ) 0).smulRight (Pi.single b₀ u₀) +
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (2 + 0) => ℝ) 1).smulRight (Pi.single b₁ u₁)
  have hturn : ∀ τ : Fin 0 → ℝ, leftTranslate (bondSpread ![] ![] τ) V = V := fun τ => by
    have : τ = 0 := Subsingleton.elim _ _
    rw [this]
    exact leftTranslate_bondSpread_zero _ _ V
  have hm : jointDisplacement G ζ V ![b₀, b₁] ![u₀, u₁] ![] ![] = fun σ => A (ζ + L σ) := by
    funext σ
    unfold jointDisplacement displacedPoint
    rw [hturn]
    simp only [hAdef, L, Fin.sum_univ_two, ContinuousLinearMap.add_apply, ContinuousLinearMap.smulRight_apply,
      ContinuousLinearMap.proj_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
    congr 2
    refine congrArg₂ (· + ·) ?_ ?_
    · funext b
      by_cases hb : b = b₀
      · subst hb
        simp
      · simp [Pi.single_eq_of_ne hb]
    · funext b
      by_cases hb : b = b₁
      · subst hb
        simp
      · simp [Pi.single_eq_of_ne hb]
  have hA' : ContDiffAt ℝ ((2 : ℕ) : WithTop ℕ∞) A (ζ + L 0) := by
    rw [map_zero, add_zero]
    exact_mod_cast hA
  have h2 := hS.1 (StepVariable (finiteCells F)) (Fin (2 + 0) → ℝ) A L ζ 0 2 (fun i => Pi.single i 1) hA'
  unfold jointMixedDeriv
  rw [hm]
  refine h2.trans ?_
  rw [map_zero, add_zero, iteratedFDeriv_two_apply]
  have e0 : L (Pi.single 0 1) = Pi.single b₀ u₀ := by
    simp [L]
  have e1 : L (Pi.single 1 1) = Pi.single b₁ u₁ := by
    simp [L]
  simp [e0, e1]
end TopDerivatives
section AlongOneBond
variable {ι : Type} [Fintype ι] [DecidableEq ι]
theorem fderiv_bondPartial_along {A : BondField ι → ℝ} {z : BondVector → BondVector} (b : ι) {η : BondField ι}
    (hA : ContDiffAt ℝ 2 A η) (hz : ContDiffAt ℝ 1 z (η b)) :
    ContDiffAt ℝ 1 (fun ζ => bondPartialDeriv A b ζ (z (ζ b))) η ∧
    ∀ (b' : ι) (e : BondVector), fderiv ℝ (fun ζ => bondPartialDeriv A b ζ (z (ζ b))) η (Pi.single b' e) =
      fderiv ℝ (fderiv ℝ A) η (Pi.single b' e) (Pi.single b (z (η b))) +
        if b' = b then fderiv ℝ A η (Pi.single b (fderiv ℝ z (η b) e)) else 0 := by
  have hD : ContDiffAt ℝ 1 (fderiv ℝ A) η := hA.fderiv_right (by norm_num)
  let Sb : BondVector →L[ℝ] BondField ι := ContinuousLinearMap.single ℝ (fun _ : ι => BondVector) b
  let P : BondField ι →L[ℝ] BondVector := ContinuousLinearMap.proj b
  have hzP : ContDiffAt ℝ 1 (fun ζ : BondField ι => z (P ζ)) η :=
    ContDiffAt.comp (g := z) (f := P) η hz P.contDiff.contDiffAt
  have hξ : ContDiffAt ℝ 1 (fun ζ : BondField ι => Sb (z (P ζ))) η :=
    ContDiffAt.comp (g := Sb) (f := fun ζ => z (P ζ)) η Sb.contDiff.contDiffAt hzP
  have e : (fun ζ => bondPartialDeriv A b ζ (z (ζ b))) = fun ζ => fderiv ℝ A ζ (Sb (z (P ζ))) := rfl
  have hder : HasFDerivAt (fun ζ : BondField ι => Sb (z (P ζ)))
      (Sb.comp ((fderiv ℝ z (η b)).comp P)) η := by
    have h1 : HasFDerivAt z (fderiv ℝ z (P η)) (P η) := (hz.differentiableAt (by norm_num)).hasFDerivAt
    exact Sb.hasFDerivAt.comp η (h1.comp η P.hasFDerivAt)
  refine ⟨e ▸ hD.clm_apply hξ, fun b' e' => ?_⟩
  have h1 := (hD.differentiableAt (by norm_num)).hasFDerivAt.clm_apply hder
  rw [e, h1.fderiv]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.flip_apply]
  rw [add_comm]
  congr 1
  by_cases hb : b' = b
  · subst hb
    simp [Sb, P]
  · have h0 : P (Pi.single b' e') = 0 := by
      simp [P, Pi.single_eq_of_ne (Ne.symm hb)]
    simp [hb, h0]
theorem abs_bilinear_le_of_unit {Bm : BondField ι →L[ℝ] BondField ι →L[ℝ] ℝ} {b₀ b₁ : ι} {S : ℝ} (hS0 : 0 ≤ S)
    (h : ∀ u u' : BondVector, ‖u‖ = 1 → ‖u'‖ = 1 → |Bm (Pi.single b₀ u) (Pi.single b₁ u')| ≤ S)
    (e e' : BondVector) : |Bm (Pi.single b₀ e) (Pi.single b₁ e')| ≤ S * ‖e'‖ * ‖e‖ := by
  have h1 : ∀ u : BondVector, ‖u‖ = 1 → |Bm (Pi.single b₀ u) (Pi.single b₁ e')| ≤ S * ‖e'‖ := fun u hu =>
    abs_apply_le_of_unit (ℓ := (Bm (Pi.single b₀ u)).comp (ContinuousLinearMap.single ℝ (fun _ : ι => BondVector) b₁))
      (fun u' hu' => h u u' hu hu') e' hS0
  exact abs_apply_le_of_unit (ℓ := (Bm.flip (Pi.single b₁ e')).comp (ContinuousLinearMap.single ℝ (fun _ : ι => BondVector) b₀))
    h1 e (mul_nonneg hS0 (norm_nonneg _))
theorem momentBound_mono {r : ℝ → ℝ} {Ψ f : BondField ι → ℝ} {q : ℕ} {B B' : ℝ} (h : MomentBound r Ψ f q B)
    (hB : 0 ≤ B) (hBB : B ≤ B') : MomentBound r Ψ f q B' :=
  ⟨h.1, h.2.trans (pow_le_pow_left₀ hB hBB _)⟩
theorem momentBound_of_bounded {ρ : ℝ} {p : ℝ → ℝ} {Ψ : BondField ι → ℝ} (hL : BallLawFacts ρ p Ψ) {x : ℝ} (hx : 0 < x) {m : ℕ → ℝ}
    (hm : ∀ q, 0 ≤ m q) (hρ : 0 < ρ)
    (hmom : ∀ (q : ℕ) (b : ι), ballExpectation (cutoffFactor ρ p) Ψ (fun η => ‖η b‖ ^ (2 * q)) ≤ m q * (x ^ q)⁻¹)
    {f : BondField ι → ℝ} (hf : ContinuousOn f (bondBall ι ρ)) {M : ℝ} (hM : 0 ≤ M)
    (hb : ∀ η ∈ bondBall ι ρ, |f η| ≤ M) (q : ℕ) (hq : 1 ≤ q) :
    MomentBound (cutoffFactor ρ p) Ψ f q ((1 + m q) * M) := by
  have h := momentBound_of_quadratic hL hx hm hρ hmom hf (E := 1) (β := M) (w := fun _ => 0) zero_le_one hM (fun _ => le_rfl)
    (fun η hη => by simpa using hb η hη) q hq
  simpa using h
end AlongOneBond
section SpanBounds
variable {F : BlockFrame}
theorem cellSupDist_le_cellSetDiameter {P : Finset F.Cell} {u v : F.Cell} (hu : u ∈ P) (hv : v ∈ P) :
    cellSupDist u v ≤ cellSetDiameter P := by apply _root_.YangMills.Construction.Interpolation.ObservableSizes.cellSupDist_le_cellSetDiameter <;> assumption
theorem bondSpan_le_cellSetDiameter {k : ℕ} {Y : F.Cell} {c : Fin k → F.Site F.top × Fin 4} {P : Finset F.Cell} (hY : Y ∈ P)
    (hc : ∀ l, (c l).1 ∈ P) : bondSpan Y c ≤ cellSetDiameter P :=
  max_le (Finset.sup_le fun l _ => cellSupDist_le_cellSetDiameter hY (hc l))
    (Finset.sup_le fun l _ => Finset.sup_le fun l' _ => cellSupDist_le_cellSetDiameter (hc l) (hc l'))
theorem exp_neg_le_mul_halves {r s a d : ℝ} (hr : 0 ≤ r) (ha : a ≤ s) (hd : d ≤ s) :
    Real.exp (-(r * s)) ≤ Real.exp (-(r / 2 * a)) * Real.exp (-(r / 2 * d)) := by
  rw [← Real.exp_add, Real.exp_le_exp]
  nlinarith [mul_nonneg hr (sub_nonneg.2 ha), mul_nonneg hr (sub_nonneg.2 hd)]
theorem topDeriv_nil (G : AboveFrames F) (V : F.GaugeField F.top) : topDeriv G V ![] ![] = fun η => G η V := by
  funext η
  simp only [topDeriv, bondDeriv, iteratedFDeriv_zero_apply]
  rw [leftTranslate_bondSpread_zero]
theorem contDiffAt_alongSpread {V : F.GaugeField F.top} {G : AboveFrames F} {k : ℕ} {c : Fin k → F.Site F.top × Fin 4} {X : Fin k → imaginaryQuaternions}
    {η : StepVariable (finiteCells F)}
    (hJ : ContDiffAt ℝ 4 (fun q : (Fin k → ℝ) × StepVariable (finiteCells F) =>
      G q.2 (leftTranslate (bondSpread c X q.1) V)) (0, η)) :
    ContDiffAt ℝ 4 (fun τ : Fin k → ℝ => G η (leftTranslate (bondSpread c X τ) V)) 0 :=
  ContDiffAt.comp (g := fun q : (Fin k → ℝ) × StepVariable (finiteCells F) => G q.2 (leftTranslate (bondSpread c X q.1) V))
    (f := fun τ : Fin k → ℝ => (τ, η)) 0 hJ (contDiff_id.prodMk contDiff_const).contDiffAt
theorem bondDeriv_sub_eq {V : F.GaugeField F.top} {G : AboveFrames F} {k : ℕ} (hk : k ≤ 3) {c : Fin k → F.Site F.top × Fin 4} {X : Fin k → imaginaryQuaternions}
    {η : StepVariable (finiteCells F)}
    (hJ : ContDiffAt ℝ 4 (fun q : (Fin k → ℝ) × StepVariable (finiteCells F) =>
      G q.2 (leftTranslate (bondSpread c X q.1) V)) (0, η))
    (hJ0 : ContDiffAt ℝ 4 (fun q : (Fin k → ℝ) × StepVariable (finiteCells F) =>
      G q.2 (leftTranslate (bondSpread c X q.1) V)) (0, 0)) :
    bondDeriv (fun V' => G η V' - G 0 V') V c X = topDeriv G V c X η - topDeriv G V c X 0 := by
  have h1 : ContDiffAt ℝ k (fun τ : Fin k → ℝ => G η (leftTranslate (bondSpread c X τ) V)) 0 :=
    (contDiffAt_alongSpread hJ).of_le (by exact_mod_cast (by omega : k ≤ 4))
  have h0 : ContDiffAt ℝ k (fun τ : Fin k → ℝ => G 0 (leftTranslate (bondSpread c X τ) V)) 0 :=
    (contDiffAt_alongSpread hJ0).of_le (by exact_mod_cast (by omega : k ≤ 4))
  have e := iteratedFDeriv_sub_apply (i := k) h1 h0
  have e3 : (fun τ : Fin k → ℝ => G η (leftTranslate (bondSpread c X τ) V) - G 0 (leftTranslate (bondSpread c X τ) V)) =
      (fun τ : Fin k → ℝ => G η (leftTranslate (bondSpread c X τ) V)) - fun τ => G 0 (leftTranslate (bondSpread c X τ) V) := rfl
  simp only [topDeriv, bondDeriv]
  rw [e3, e]
  rfl
end SpanBounds
section Sizes
variable {F : BlockFrame}
theorem rpow_neg_half {x : ℝ} (hx : 0 < x) : x ^ (-(1 / 2) : ℝ) = (Real.sqrt x)⁻¹ := by
  rw [Real.rpow_neg hx.le, ← Real.sqrt_eq_rpow]
theorem le_rpow_neg_half_mul {x a : ℝ} (hx : 0 < x) (ha : 0 ≤ a) : a ≤ x ^ (-(1 / 2) : ℝ) * (1 + x * a ^ 2) := by
  rw [rpow_neg_half hx]
  have hs : 0 < Real.sqrt x := Real.sqrt_pos.2 hx
  have hq : Real.sqrt x ^ 2 = x := Real.sq_sqrt hx.le
  rw [inv_mul_eq_div, le_div_iff₀ hs]
  nlinarith [sq_nonneg (Real.sqrt x * a - 1), mul_nonneg hs.le ha]
structure SizeData (Q : ColdHalfLaw) (m : ℕ → ℝ) (Ψ : StepVariable (finiteCells F) → ℝ) (B r Wt C : ℝ) : Prop where
  law : BallLawFacts Q.ballRadius Q.cutoff Ψ
  coupling_pos : 0 < Q.coupling
  one_le_coupling : 1 ≤ Q.coupling
  moment_nonneg : ∀ q, 0 ≤ m q
  ballRadius_pos : 0 < Q.ballRadius
  moments : ∀ (q : ℕ) (b : ↥(chordBonds (finiteCells F))),
    ballExpectation (cutoffFactor Q.ballRadius Q.cutoff) Ψ (fun η => ‖η b‖ ^ (2 * q)) ≤ m q * (Q.coupling ^ q)⁻¹
  kernel_nonneg : 0 ≤ B
  rate_pos : 0 < Q.rate
  rate_le : 2 ^ 6 * Q.rate ≤ r
  one_le_weight : 1 ≤ Wt
  weight_sum_le : ∀ Y' : F.Cell, ∑ b : ↥(chordBonds (finiteCells F)), Real.exp (-(r / 2 * bondDistToCell Y' b)) ≤ Wt
  amplitude_le : 2 * B * Wt ≤ C
variable {Q : ColdHalfLaw} {m : ℕ → ℝ} {Ψ : StepVariable (finiteCells F) → ℝ} {B r Wt C : ℝ}
  {V : F.GaugeField F.top} {Y : F.Cell} {G : AboveFrames F}
theorem topDeriv_moments (hS : IteratedFDerivSlices) (hf : SizeData Q m Ψ B r Wt C)
    (hK : HasDecayingKernels Q.ballRadius B r Y G V) {k : ℕ} (hk : k ≤ 3) (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions)
    (hX : AreUnitVectors X) :
    ContDiffOn ℝ 1 (topDeriv G V c X) (bondBall _ Q.ballRadius) ∧
    (∀ q : ℕ, 1 ≤ q → MomentBound (cutoffFactor Q.ballRadius Q.cutoff) Ψ (fun η => topDeriv G V c X η - topDeriv G V c X 0) q
      ((1 + m q) * (C * Q.coupling ^ (-(1 / 2) : ℝ) * Real.exp (-(2 ^ 5 * Q.rate * bondSpan Y c))))) ∧
    ∀ (q : ℕ) (b : ↥(chordBonds (finiteCells F))), 1 ≤ q →
      MomentBound (cutoffFactor Q.ballRadius Q.cutoff) Ψ (bondGradNorm (topDeriv G V c X) b) q
        ((1 + m q) * Real.sqrt Q.coupling * (C * Q.coupling ^ (-(1 / 2) : ℝ) * Real.exp (-(2 ^ 5 * Q.rate * bondSpan Y c))) *
          Real.exp (-(2 * Q.rate * (cellSupDist (enclosingCell b.1.1) Y : ℝ)))) := by
  classical
  have hx := hf.coupling_pos
  have hB := hf.kernel_nonneg
  have hκ := hf.rate_pos
  have hr0 : 0 ≤ r := le_trans (by positivity) hf.rate_le
  set g := topDeriv G V c X with hg
  set y := Q.coupling ^ (-(1 / 2) : ℝ) with hy
  have hy0 : 0 < y := Real.rpow_pos_of_pos hx _
  have hsy : Real.sqrt Q.coupling * y = 1 := by
    rw [hy, rpow_neg_half hx]
    exact mul_inv_cancel₀ (Real.sqrt_pos.2 hx).ne'
  let s : ↥(chordBonds (finiteCells F)) → ℝ := fun b =>
    (cellSetDiameter ({Y} ∪ chordBondCells ![b] ∪ topBondCells c) : ℕ)
  let D : ↥(chordBonds (finiteCells F)) → ℝ := fun b => B * Real.exp (-(r * s b))
  have hD0 : ∀ b, 0 ≤ D b := fun b => mul_nonneg hB (Real.exp_pos _).le
  have hJ : ∀ ζ : StepVariable (finiteCells F), (∀ b, ‖ζ b‖ ≤ Q.ballRadius) → _ := fun ζ hζ => hK.smooth k c X ζ hζ
  have hc1 : ∀ ζ : StepVariable (finiteCells F), (∀ b, ‖ζ b‖ ≤ Q.ballRadius) → ContDiffAt ℝ 1 g ζ := fun ζ hζ =>
    contDiffAt_topDeriv hS hk c X (hJ ζ hζ)
  have hOn : ContDiffOn ℝ 1 g (bondBall _ Q.ballRadius) := fun ζ hζ =>
    (hc1 ζ fun b => (hζ b).le).contDiffWithinAt
  have hDb : ∀ ζ : StepVariable (finiteCells F), (∀ b, ‖ζ b‖ ≤ Q.ballRadius) → ∀ (b : ↥(chordBonds (finiteCells F))) (u : BondVector),
      ‖u‖ = 1 → |fderiv ℝ g ζ (Pi.single b u)| ≤ D b := fun ζ hζ b u hu => by
    rw [hg, fderiv_topDeriv_single hS hk c X (hJ ζ hζ) b u]
    exact hK.deriv_one k c X ζ b u hk hζ hu hX
  have hmemY : ∀ b : ↥(chordBonds (finiteCells F)), Y ∈ ({Y} ∪ chordBondCells ![b] ∪ topBondCells c : Finset F.Cell) :=
    fun b => by simp
  have hmemb : ∀ b : ↥(chordBonds (finiteCells F)),
      enclosingCell b.1.1 ∈ ({Y} ∪ chordBondCells ![b] ∪ topBondCells c : Finset F.Cell) := fun b => by
    simp [chordBondCells]
  have hmemc : ∀ (b : ↥(chordBonds (finiteCells F))) (l : Fin k),
      (c l).1 ∈ ({Y} ∪ chordBondCells ![b] ∪ topBondCells c : Finset F.Cell) := fun b l => by
    simp only [Finset.mem_union, topBondCells, Finset.mem_image, Finset.mem_univ, true_and]
    exact Or.inr ⟨l, rfl⟩
  have hsp : ∀ b, (bondSpan Y c : ℝ) ≤ s b := fun b => by
    exact Nat.cast_le.2 (bondSpan_le_cellSetDiameter (hmemY b) (hmemc b))
  have hdb : ∀ b : ↥(chordBonds (finiteCells F)), (cellSupDist (enclosingCell b.1.1) Y : ℝ) ≤ s b := fun b => by
    exact Nat.cast_le.2 (cellSupDist_le_cellSetDiameter (hmemb b) (hmemY b))
  have hsplit : ∀ b, D b ≤ B * Real.exp (-(r / 2 * bondSpan Y c)) *
      Real.exp (-(r / 2 * (cellSupDist (enclosingCell b.1.1) Y : ℝ))) := fun b => by
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left (exp_neg_le_mul_halves hr0 (hsp b) (hdb b)) hB
  have hΔ : ∑ b, D b ≤ B * Wt * Real.exp (-(r / 2 * bondSpan Y c)) := by
    calc ∑ b, D b ≤ ∑ b : ↥(chordBonds (finiteCells F)), B * Real.exp (-(r / 2 * bondSpan Y c)) *
          Real.exp (-(r / 2 * (cellSupDist (enclosingCell b.1.1) Y : ℝ))) := Finset.sum_le_sum fun b _ => hsplit b
      _ = B * Real.exp (-(r / 2 * bondSpan Y c)) * ∑ b : ↥(chordBonds (finiteCells F)),
          Real.exp (-(r / 2 * bondDistToCell Y b)) := by
          rw [Finset.mul_sum]
          rfl
      _ ≤ B * Real.exp (-(r / 2 * bondSpan Y c)) * Wt :=
          mul_le_mul_of_nonneg_left (hf.weight_sum_le Y) (mul_nonneg hB (Real.exp_pos _).le)
      _ = _ := by ring
  have hsp0 : (0 : ℝ) ≤ bondSpan Y c := Nat.cast_nonneg _
  have hrate : Real.exp (-(r / 2 * bondSpan Y c)) ≤ Real.exp (-(2 ^ 5 * Q.rate * bondSpan Y c)) := by
    rw [Real.exp_le_exp]
    have := hf.rate_le
    nlinarith [mul_nonneg (sub_nonneg.2 this) hsp0]
  have hBW : B ≤ B * Wt := le_mul_of_one_le_right hB hf.one_le_weight
  have hC0 : 0 ≤ C := le_trans (by have := hf.one_le_weight; positivity) hf.amplitude_le
  refine ⟨hOn, fun q hq => ?_, fun q b hq => ?_⟩
  · have hcont : ContinuousOn (fun η => g η - g 0) (bondBall _ Q.ballRadius) := hOn.continuousOn.sub continuousOn_const
    have hb : ∀ η ∈ bondBall _ Q.ballRadius, |g η - g 0| ≤ y * (∑ b, D b + ∑ b, D b * (Q.coupling * ‖η b‖ ^ 2)) := fun η hη => by
      have h1 := abs_sub_le_of_single_fderiv (ρ := Q.ballRadius) (g := g) hD0 (fun ζ hζ => (hc1 ζ hζ).differentiableAt (by norm_num)) hDb
        (fun b => (hη b).le)
      refine h1.trans ?_
      rw [← Finset.sum_add_distrib, Finset.mul_sum]
      refine Finset.sum_le_sum fun b _ => ?_
      have h2 := le_rpow_neg_half_mul hx (norm_nonneg (η b))
      calc ‖η b‖ * D b ≤ (y * (1 + Q.coupling * ‖η b‖ ^ 2)) * D b := mul_le_mul_of_nonneg_right h2 (hD0 b)
        _ = y * (D b + D b * (Q.coupling * ‖η b‖ ^ 2)) := by ring
    have h3 := momentBound_of_quadratic hf.law hx hf.moment_nonneg hf.ballRadius_pos hf.moments hcont (E := ∑ b, D b) (β := y) (w := D)
      (Finset.sum_nonneg fun b _ => hD0 b) hy0.le hD0 hb q hq
    have hmq : 0 ≤ 1 + m q := by linarith [hf.moment_nonneg q]
    refine momentBound_mono h3 (mul_nonneg (mul_nonneg hmq hy0.le)
      (add_nonneg (Finset.sum_nonneg fun b _ => hD0 b) (Finset.sum_nonneg fun b _ => hD0 b))) ?_
    have h4 : ∑ b, D b + ∑ b, D b ≤ C * Real.exp (-(2 ^ 5 * Q.rate * bondSpan Y c)) := by
      have hexp := (Real.exp_pos (-(r / 2 * bondSpan Y c))).le
      have hexp' := (Real.exp_pos (-(2 ^ 5 * Q.rate * bondSpan Y c))).le
      calc ∑ b, D b + ∑ b, D b ≤ 2 * B * Wt * Real.exp (-(r / 2 * bondSpan Y c)) := by linarith
        _ ≤ C * Real.exp (-(2 ^ 5 * Q.rate * bondSpan Y c)) :=
          mul_le_mul hf.amplitude_le hrate hexp hC0
    calc (1 + m q) * y * (∑ b, D b + ∑ b, D b) ≤ (1 + m q) * y * (C * Real.exp (-(2 ^ 5 * Q.rate * bondSpan Y c))) :=
          mul_le_mul_of_nonneg_left h4 (mul_nonneg hmq hy0.le)
      _ = _ := by ring
  · have hcont : ContinuousOn (bondGradNorm g b) (bondBall _ Q.ballRadius) := by
      unfold bondGradNorm
      exact ((hOn.continuousOn_fderiv_of_isOpen (isOpen_bondBall _) le_rfl).clm_comp continuousOn_const).norm
    have hb : ∀ η ∈ bondBall _ Q.ballRadius, |bondGradNorm g b η| ≤ D b := fun η hη => by
      have h1 : bondGradNorm g b η ≤ D b := bondGradNorm_le_of_unit (hD0 b) fun u hu => hDb η (fun b => (hη b).le) b u hu
      have h2 : 0 ≤ bondGradNorm g b η := norm_nonneg _
      rwa [abs_of_nonneg h2]
    have h3 := momentBound_of_bounded hf.law hx hf.moment_nonneg hf.ballRadius_pos hf.moments hcont (hD0 b) hb q hq
    have hmq : 0 ≤ 1 + m q := by linarith [hf.moment_nonneg q]
    refine momentBound_mono h3 (mul_nonneg hmq (hD0 b)) ?_
    have hd0 : (0 : ℝ) ≤ cellSupDist (enclosingCell b.1.1) Y := Nat.cast_nonneg _
    have hrate2 : Real.exp (-(r / 2 * (cellSupDist (enclosingCell b.1.1) Y : ℝ))) ≤
        Real.exp (-(2 * Q.rate * (cellSupDist (enclosingCell b.1.1) Y : ℝ))) := by
      rw [Real.exp_le_exp]
      have : 2 * Q.rate ≤ r / 2 := by have := hf.rate_le; nlinarith
      nlinarith [mul_nonneg (sub_nonneg.2 this) hd0]
    have h4 : D b ≤ C * Real.exp (-(2 ^ 5 * Q.rate * bondSpan Y c)) *
        Real.exp (-(2 * Q.rate * (cellSupDist (enclosingCell b.1.1) Y : ℝ))) := by
      have hBC : B ≤ C := by nlinarith [hf.amplitude_le]
      refine (hsplit b).trans ?_
      exact mul_le_mul (mul_le_mul hBC hrate (Real.exp_pos _).le hC0) hrate2 (Real.exp_pos _).le
        (mul_nonneg hC0 (Real.exp_pos _).le)
    have e : (1 + m q) * Real.sqrt Q.coupling * (C * y * Real.exp (-(2 ^ 5 * Q.rate * bondSpan Y c))) *
        Real.exp (-(2 * Q.rate * (cellSupDist (enclosingCell b.1.1) Y : ℝ))) = (1 + m q) * (C * Real.exp (-(2 ^ 5 * Q.rate * bondSpan Y c)) *
        Real.exp (-(2 * Q.rate * (cellSupDist (enclosingCell b.1.1) Y : ℝ)))) := by
      calc _ = (1 + m q) * (Real.sqrt Q.coupling * y) * (C * Real.exp (-(2 ^ 5 * Q.rate * bondSpan Y c)) *
              Real.exp (-(2 * Q.rate * (cellSupDist (enclosingCell b.1.1) Y : ℝ)))) := by ring
        _ = _ := by rw [hsy, mul_one]
    rw [e]
    exact mul_le_mul_of_nonneg_left h4 hmq
end Sizes
section BondFields
variable {F : BlockFrame}
variable {Q : ColdHalfLaw} {m : ℕ → ℝ} {Ψ : StepVariable (finiteCells F) → ℝ} {B r Wt C : ℝ}
  {V : F.GaugeField F.top} {Y : F.Cell} {G : AboveFrames F}
theorem contDiffAt_top (hK : HasDecayingKernels Q.ballRadius B r Y G V) {ζ : StepVariable (finiteCells F)} (hζ : ∀ b, ‖ζ b‖ ≤ Q.ballRadius) :
    ContDiffAt ℝ 4 (fun η => G η V) ζ := by
  have h1 := hK.smooth 0 ![] ![] ζ hζ
  have h2 : ContDiffAt ℝ 4 (fun η : StepVariable (finiteCells F) =>
      (fun q : (Fin 0 → ℝ) × StepVariable (finiteCells F) => G q.2 (leftTranslate (bondSpread ![] ![] q.1) V)) (0, η)) ζ :=
    ContDiffAt.comp (g := fun q : (Fin 0 → ℝ) × StepVariable (finiteCells F) => G q.2 (leftTranslate (bondSpread ![] ![] q.1) V))
      (f := fun η : StepVariable (finiteCells F) => ((0 : Fin 0 → ℝ), η)) ζ h1
      (contDiff_const.prodMk contDiff_id).contDiffAt
  have e : (fun η : StepVariable (finiteCells F) =>
      (fun q : (Fin 0 → ℝ) × StepVariable (finiteCells F) => G q.2 (leftTranslate (bondSpread ![] ![] q.1) V)) (0, η)) =
      fun η => G η V := by
    funext η
    simp only []
    rw [leftTranslate_bondSpread_zero]
  rwa [e] at h2
theorem bondPartial_along_bounds (hS : IteratedFDerivSlices) (hK : HasDecayingKernels Q.ballRadius B r Y G V) (hB : 0 ≤ B)
    (b : ↥(chordBonds (finiteCells F))) {z : BondVector → BondVector} {Zd : ℝ} (hZd : 0 ≤ Zd)
    (hz : ∀ v : BondVector, ‖v‖ < Q.ballRadius → ContDiffAt ℝ 1 z v ∧ ‖z v‖ ≤ Zd ∧ ‖fderiv ℝ z v‖ ≤ Zd) :
    ContDiffOn ℝ 1 (fun ζ => bondPartialDeriv (fun η => G η V) b ζ (z (ζ b))) (bondBall _ Q.ballRadius) ∧
    (∀ ζ ∈ bondBall _ Q.ballRadius, |bondPartialDeriv (fun η => G η V) b ζ (z (ζ b))| ≤
      Zd * (B * Real.exp (-(r * (cellSetDiameter ({Y} ∪ chordBondCells ![b] ∪ topBondCells ![]) : ℕ))))) ∧
    ∀ ζ ∈ bondBall _ Q.ballRadius, ∀ b' : ↥(chordBonds (finiteCells F)),
      bondGradNorm (fun ζ => bondPartialDeriv (fun η => G η V) b ζ (z (ζ b))) b' ζ ≤
      Zd * (B * Real.exp (-(r * (cellSetDiameter ({Y} ∪ chordBondCells ![b', b]) : ℕ)))) +
      if b' = b then Zd * (B * Real.exp (-(r * (cellSetDiameter ({Y} ∪ chordBondCells ![b] ∪ topBondCells ![]) : ℕ))))
      else 0 := by
  classical
  set A : StepVariable (finiteCells F) → ℝ := fun η => G η V with hA
  set P : ℝ := B * Real.exp (-(r * (cellSetDiameter ({Y} ∪ chordBondCells ![b] ∪ topBondCells ![]) : ℕ))) with hP
  have hP0 : 0 ≤ P := mul_nonneg hB (Real.exp_pos _).le
  have hJ0 : ∀ ζ : StepVariable (finiteCells F), (∀ b, ‖ζ b‖ ≤ Q.ballRadius) → ContDiffAt ℝ 4 A ζ := fun ζ hζ => contDiffAt_top hK hζ
  have hfirst : ∀ ζ : StepVariable (finiteCells F), (∀ b, ‖ζ b‖ ≤ Q.ballRadius) → ∀ (u : BondVector), ‖u‖ = 1 →
      |fderiv ℝ A ζ (Pi.single b u)| ≤ P := fun ζ hζ u hu => by
    have h1 := fderiv_topDeriv_single hS (by omega : 0 ≤ 3) ![] ![] (hK.smooth 0 ![] ![] ζ hζ) b u
    rw [topDeriv_nil] at h1
    rw [hA, h1]
    exact hK.deriv_one 0 ![] ![] ζ b u (by omega) hζ hu (fun l => l.elim0)
  have hsecond : ∀ (ζ : StepVariable (finiteCells F)) (b₀ b₁ : ↥(chordBonds (finiteCells F))), (∀ b, ‖ζ b‖ ≤ Q.ballRadius) →
      ∀ u u' : BondVector, ‖u‖ = 1 → ‖u'‖ = 1 → |fderiv ℝ (fderiv ℝ A) ζ (Pi.single b₀ u) (Pi.single b₁ u')| ≤
        B * Real.exp (-(r * (cellSetDiameter ({Y} ∪ chordBondCells ![b₀, b₁]) : ℕ))) := fun ζ b₀ b₁ hζ u u' hu hu' => by
    have h1 := jointMixedDeriv_two hS (G := G) (V := V) (ζ := ζ) ((hJ0 ζ hζ).of_le (by norm_num)) b₀ b₁ u u'
    rw [hA, ← h1]
    exact hK.deriv_two ζ b₀ b₁ u u' hζ hu hu'
  have hlift : ∀ ζ ∈ bondBall ↥(chordBonds (finiteCells F)) Q.ballRadius, ∀ b, ‖ζ b‖ ≤ Q.ballRadius := fun ζ hζ b => (hζ b).le
  have hone : ∀ ζ ∈ bondBall ↥(chordBonds (finiteCells F)) Q.ballRadius, ContDiffAt ℝ 1 (fun ζ => bondPartialDeriv A b ζ (z (ζ b))) ζ ∧
      ∀ (b' : ↥(chordBonds (finiteCells F))) (e : BondVector),
        fderiv ℝ (fun ζ => bondPartialDeriv A b ζ (z (ζ b))) ζ (Pi.single b' e) =
          fderiv ℝ (fderiv ℝ A) ζ (Pi.single b' e) (Pi.single b (z (ζ b))) +
            if b' = b then fderiv ℝ A ζ (Pi.single b (fderiv ℝ z (ζ b) e)) else 0 := fun ζ hζ =>
    fderiv_bondPartial_along b ((hJ0 ζ (hlift ζ hζ)).of_le (by norm_num)) (hz _ (hζ b)).1
  refine ⟨fun ζ hζ => (hone ζ hζ).1.contDiffWithinAt, fun ζ hζ => ?_, fun ζ hζ b' => ?_⟩
  · have h1 := abs_apply_le_of_unit (ℓ := (fderiv ℝ A ζ).comp
      (ContinuousLinearMap.single ℝ (fun _ : ↥(chordBonds (finiteCells F)) => BondVector) b))
      (D := P) (fun u hu => hfirst ζ (hlift ζ hζ) u hu) (z (ζ b)) hP0
    have h2 := (hz _ (hζ b)).2.1
    calc |bondPartialDeriv A b ζ (z (ζ b))| ≤ P * ‖z (ζ b)‖ := h1
      _ ≤ P * Zd := mul_le_mul_of_nonneg_left h2 hP0
      _ = Zd * P := mul_comm _ _
  · have hS0 : 0 ≤ B * Real.exp (-(r * (cellSetDiameter ({Y} ∪ chordBondCells ![b', b]) : ℕ))) :=
      mul_nonneg hB (Real.exp_pos _).le
    have hbound : 0 ≤ Zd * (B * Real.exp (-(r * (cellSetDiameter ({Y} ∪ chordBondCells ![b', b]) : ℕ)))) +
        if b' = b then Zd * P else 0 := by
      refine add_nonneg (mul_nonneg hZd hS0) ?_
      split_ifs
      · exact mul_nonneg hZd hP0
      · exact le_rfl
    refine bondGradNorm_le_of_unit hbound fun e he => ?_
    rw [(hone ζ hζ).2 b' e]
    refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
    · have h1 := abs_bilinear_le_of_unit (Bm := fderiv ℝ (fderiv ℝ A) ζ) hS0
        (fun u u' hu hu' => hsecond ζ b' b (hlift ζ hζ) u u' hu hu') e (z (ζ b))
      rw [he, mul_one] at h1
      have h2 := (hz _ (hζ b)).2.1
      calc _ ≤ _ := h1
        _ ≤ B * Real.exp (-(r * (cellSetDiameter ({Y} ∪ chordBondCells ![b', b]) : ℕ))) * Zd :=
          mul_le_mul_of_nonneg_left h2 hS0
        _ = _ := mul_comm _ _
    · split_ifs with hb
      · have h1 := abs_apply_le_of_unit (ℓ := (fderiv ℝ A ζ).comp
          (ContinuousLinearMap.single ℝ (fun _ : ↥(chordBonds (finiteCells F)) => BondVector) b))
          (D := P) (fun u hu => hfirst ζ (hlift ζ hζ) u hu) (fderiv ℝ z (ζ b) e) hP0
        have h2 : ‖fderiv ℝ z (ζ b) e‖ ≤ Zd := by
          have := (fderiv ℝ z (ζ b)).le_opNorm e
          rw [he, mul_one] at this
          exact this.trans (hz _ (hζ b)).2.2
        calc _ ≤ P * ‖fderiv ℝ z (ζ b) e‖ := h1
          _ ≤ P * Zd := mul_le_mul_of_nonneg_left h2 hP0
          _ = _ := mul_comm _ _
      · simp
end BondFields
theorem kernelIncrementIsSlot (hLaw : normalizedBallLawIsProbabilityStatement)
    (hS : IteratedFDerivSlices) : KernelIncrementIsSlot := by
  intro F Q m V Y G B r Wt Z C hA hm hK hZ hB hZ0 hκ hr hWt1 hWt hC
  classical
  obtain ⟨Ψ, hΨc, hdens⟩ := hA.continuous_exponent
  have hρ := hA.ballRadius_pos
  have hx1 := hA.one_le_coupling
  have hx : 0 < Q.coupling := by linarith
  obtain ⟨hprob, hmean, hint, hball, -, -, -, -, -, hnz, -⟩ := hLaw _ Q.ballRadius Q.cutoff Ψ hρ hA.isCutoff hΨc
  have hd : ballDensity (cutoffFactor Q.ballRadius Q.cutoff) (Q.exponent V) = ballDensity (cutoffFactor Q.ballRadius Q.cutoff) Ψ := hdens
  have hmean_eq : ∀ f, ballExpectation (cutoffFactor Q.ballRadius Q.cutoff) (Q.exponent V) f = ballExpectation (cutoffFactor Q.ballRadius Q.cutoff) Ψ f := fun f => by
    unfold ballExpectation
    rw [hd]
  have hL : BallLawFacts Q.ballRadius Q.cutoff Ψ := ⟨hprob, hmean, hint, hball⟩
  have hW0 : 0 ≤ Wt := by linarith
  have hBW : 0 ≤ B * Wt := mul_nonneg hB hW0
  have hBWZ : 0 ≤ B * Wt * Z := mul_nonneg hBW hZ0
  have hC2 : 2 * B * Wt ≤ C := by nlinarith
  have hZB : 2 * (Z * B) ≤ C := by nlinarith [mul_nonneg (mul_nonneg hB hZ0) (sub_nonneg.2 hWt1)]
  have hC0 : 0 ≤ C := by nlinarith
  have hf : SizeData Q m Ψ B r Wt C :=
    ⟨hL, hx, hx1, hm, hρ, fun q b => by rw [← hmean_eq]; exact hA.moments q b, hB, hκ, hr, hWt1, hWt, hC2⟩
  have hz0 : ∀ η : StepVariable (finiteCells F), ¬ (∀ b, ‖η b‖ < Q.ballRadius) →
      ballDensity (cutoffFactor Q.ballRadius Q.cutoff) Ψ η = 0 := fun η hη => by
    by_contra hne
    exact hη ((hnz η).1 hne)
  have hO : IsOpen {η : StepVariable (finiteCells F) | ∀ b, ‖η b‖ < Q.ballRadius} := isOpen_bondBall Q.ballRadius
  have h00 : ∀ b : ↥(chordBonds (finiteCells F)), ‖(0 : StepVariable (finiteCells F)) b‖ ≤ Q.ballRadius := fun b => by
    simpa using hρ.le
  have hmd : ∀ (k : ℕ) (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions), k ≤ 3 →
      ∀ η : StepVariable (finiteCells F), (∀ b, ‖η b‖ < Q.ballRadius) →
      topDeriv G V c X η - topDeriv G V c X 0 = bondDeriv (fun V' => G η V' - G 0 V') V c X := fun k c X hk η hη =>
    (bondDeriv_sub_eq hk (hK.smooth k c X η fun b => (hη b).le) (hK.smooth k c X 0 h00)).symm
  have hsq : Real.sqrt Q.coupling * Q.coupling ^ (-(1 / 2) : ℝ) = 1 := by
    rw [rpow_neg_half hx]
    exact mul_inv_cancel₀ (Real.sqrt_pos.2 hx).ne'
  have hs1 : 1 ≤ Real.sqrt Q.coupling := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_le_sqrt hx1
  have hκ0 := hκ.le
  have hr0 : 0 ≤ r := le_trans (by positivity) hr
  refine ⟨⟨⟨fun η k c X hη => ?_, fun k c X hk hX => ?_⟩, fun η hη => ?_, ?_⟩, fun k c X hk1 hk3 hX => ?_⟩
  · have h1 : ContDiffAt ℝ 3 (fun q : (Fin k → ℝ) × StepVariable (finiteCells F) => G q.2 (leftTranslate (bondSpread c X q.1) V)) (0, η) :=
      (hK.smooth k c X η hη).of_le (by norm_num)
    have h0 : ContDiffAt ℝ 3 (fun q : (Fin k → ℝ) × StepVariable (finiteCells F) => G 0 (leftTranslate (bondSpread c X q.1) V)) (0, η) :=
      ContDiffAt.comp (g := fun q : (Fin k → ℝ) × StepVariable (finiteCells F) => G q.2 (leftTranslate (bondSpread c X q.1) V))
        (f := fun q : (Fin k → ℝ) × StepVariable (finiteCells F) => (q.1, (0 : StepVariable (finiteCells F)))) (0, η)
        ((hK.smooth k c X 0 h00).of_le (by norm_num)) (contDiff_fst.prodMk contDiff_const).contDiffAt
    exact_mod_cast h1.sub h0
  · obtain ⟨hOn, hmom, hgr⟩ := topDeriv_moments hS hf hK (by omega : k ≤ 3) c X hX
    have hs : HasLocalSize Q.ballRadius (cutoffFactor Q.ballRadius Q.cutoff) Ψ (fun q => 1 + m q) Q.coupling Q.rate
        (C * Q.coupling ^ (-(1 / 2) : ℝ) * Real.exp (-(2 ^ 5 * Q.rate * bondSpan Y c))) (fun b => cellSupDist (enclosingCell b.1.1) Y)
        (fun η => topDeriv G V c X η - topDeriv G V c X 0) := by
      refine ⟨fun η hη => ((hOn.contDiffAt (hO.mem_nhds hη)).differentiableAt (by norm_num)).sub_const _, 0,
        fun q hq => ⟨?_, fun b => ?_⟩⟩
      · simpa using hmom q hq
      · have e : bondGradNorm (fun η => topDeriv G V c X η - topDeriv G V c X 0) b = bondGradNorm (topDeriv G V c X) b := by
          funext η
          unfold bondGradNorm
          rw [fderiv_sub_const]
        rw [e]
        exact hgr q b hq
    exact hasLocalSize_congr_density hd.symm (hasLocalSize_congr_of_eqOn_balls hO hz0 (hmd k c X (by omega)) hs)
  · have h1 := (contDiffAt_top hK (fun b => (hη b).le)).of_le (show (2 : WithTop ℕ∞) ≤ 4 by norm_num)
    exact h1.sub contDiffAt_const
  · intro Th hTh c X b hX
    set z : BondVector → BondVector := fun v => _root_.YangMills.Construction.Interpolation.imaginaryCoords (topVariationField Th 1 Q.a Q.chartRadius Q.mirrorRadius c X b.1 (toImaginary v) V) with hzdef
    set dc : ℝ := bondDistToTopBond b c with hdc
    set dY : ℝ := bondDistToCell Y b with hdY
    set Zd : ℝ := Z * Real.exp (-(2 ^ 8 * Q.rate * dc)) with hZd
    have hZd0 : 0 ≤ Zd := mul_nonneg hZ0 (Real.exp_pos _).le
    have hzb : ∀ v : BondVector, ‖v‖ < Q.ballRadius → ContDiffAt ℝ 1 z v ∧ ‖z v‖ ≤ Zd ∧ ‖fderiv ℝ z v‖ ≤ Zd := fun v hv =>
      hZ Th hTh c X b v hX hv
    obtain ⟨hc, hval, hgrad⟩ := bondPartial_along_bounds hS hK hB b hZd0 hzb
    set φ : StepVariable (finiteCells F) → ℝ := fun ζ => bondPartialDeriv (fun η => G η V) b ζ (z (ζ b)) with hφ
    have hφe : topFieldPartial Th 1 Q.a Q.chartRadius Q.mirrorRadius c X V b (fun η => G η V - G 0 V) = φ := by
      funext ζ
      unfold topFieldPartial bondPartialDeriv
      simp only [hφ, bondPartialDeriv, hzdef]
      rw [fderiv_sub_const]
    rw [hφe]
    set s1 : ℝ := ((cellSetDiameter ({Y} ∪ chordBondCells ![b] ∪ topBondCells ![]) : ℕ) : ℝ) with hs1d
    have hdY0 : 0 ≤ dY := Nat.cast_nonneg _
    have hdc0 : 0 ≤ dc := Nat.cast_nonneg _
    have hdYs : dY ≤ s1 := Nat.cast_le.2 (cellSupDist_le_cellSetDiameter (by simp [chordBondCells]) (by simp))
    set e1 : ℝ := Real.exp (-(2 ^ 4 * Q.rate * dY) - 2 ^ 6 * Q.rate * dc) with he1
    have he1p : 0 < e1 := Real.exp_pos _
    have hr4 : 2 ^ 4 * Q.rate ≤ r / 2 := by nlinarith
    have hr2 : 2 * Q.rate ≤ r / 2 := by nlinarith
    have hcdec : Real.exp (-(2 ^ 8 * Q.rate * dc)) * Real.exp (-(2 ^ 4 * Q.rate * dY)) ≤ e1 := by
      rw [← Real.exp_add, he1, Real.exp_le_exp]
      nlinarith [mul_nonneg hκ0 hdc0]
    have hmono : ∀ {a a' d : ℝ}, a' ≤ a → 0 ≤ d → Real.exp (-(a * d)) ≤ Real.exp (-(a' * d)) := fun {a a' d} h h' => by
      rw [Real.exp_le_exp]
      nlinarith [mul_nonneg (sub_nonneg.2 h) h']
    have hP1 : Real.exp (-(r * s1)) ≤ Real.exp (-(2 ^ 4 * Q.rate * dY)) * Real.exp (-(2 * Q.rate * dY)) :=
      (exp_neg_le_mul_halves hr0 hdYs hdYs).trans (mul_le_mul (hmono hr4 hdY0) (hmono hr2 hdY0) (Real.exp_pos _).le (Real.exp_pos _).le)
    have hP2 : Real.exp (-(2 * Q.rate * dY)) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      nlinarith [mul_nonneg hκ0 hdY0]
    have hval2 : ∀ ζ ∈ bondBall ↥(chordBonds (finiteCells F)) Q.ballRadius, |φ ζ| ≤ C * e1 := fun ζ hζ => by
      refine (hval ζ hζ).trans ?_
      have h1 : Real.exp (-(2 ^ 8 * Q.rate * dc)) * Real.exp (-(r * s1)) ≤ e1 := by
        refine le_trans (mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le) hcdec
        calc _ ≤ Real.exp (-(2 ^ 4 * Q.rate * dY)) * Real.exp (-(2 * Q.rate * dY)) := hP1
          _ ≤ Real.exp (-(2 ^ 4 * Q.rate * dY)) * 1 := mul_le_mul_of_nonneg_left hP2 (Real.exp_pos _).le
          _ = _ := mul_one _
      calc Zd * (B * Real.exp (-(r * s1))) = Z * B * (Real.exp (-(2 ^ 8 * Q.rate * dc)) * Real.exp (-(r * s1))) := by
            rw [hZd]; ring
        _ ≤ Z * B * e1 := mul_le_mul_of_nonneg_left h1 (mul_nonneg hZ0 hB)
        _ ≤ C * e1 := mul_le_mul_of_nonneg_right (by nlinarith [mul_nonneg hZ0 hB]) he1p.le
    have hgrad2 : ∀ ζ ∈ bondBall ↥(chordBonds (finiteCells F)) Q.ballRadius, ∀ b' : ↥(chordBonds (finiteCells F)),
        bondGradNorm φ b' ζ ≤ C * e1 * Real.exp (-(2 * Q.rate * bondDistToCell Y b')) := fun ζ hζ b' => by
      refine (hgrad ζ hζ b').trans ?_
      set d' : ℝ := bondDistToCell Y b' with hd'
      have hd'0 : 0 ≤ d' := Nat.cast_nonneg _
      set s2 : ℝ := ((cellSetDiameter ({Y} ∪ chordBondCells ![b', b]) : ℕ) : ℝ) with hs2
      have hds2 : dY ≤ s2 := Nat.cast_le.2 (cellSupDist_le_cellSetDiameter (by simp [chordBondCells]) (by simp))
      have hds2' : d' ≤ s2 := Nat.cast_le.2 (cellSupDist_le_cellSetDiameter (by simp [chordBondCells]) (by simp))
      have h1 : Real.exp (-(2 ^ 8 * Q.rate * dc)) * Real.exp (-(r * s2)) ≤ e1 * Real.exp (-(2 * Q.rate * d')) := by
        have h2 : Real.exp (-(r * s2)) ≤ Real.exp (-(2 ^ 4 * Q.rate * dY)) * Real.exp (-(2 * Q.rate * d')) :=
          (exp_neg_le_mul_halves hr0 hds2 hds2').trans
            (mul_le_mul (hmono hr4 hdY0) (hmono hr2 hd'0) (Real.exp_pos _).le (Real.exp_pos _).le)
        calc _ ≤ Real.exp (-(2 ^ 8 * Q.rate * dc)) * (Real.exp (-(2 ^ 4 * Q.rate * dY)) * Real.exp (-(2 * Q.rate * d'))) :=
              mul_le_mul_of_nonneg_left h2 (Real.exp_pos _).le
          _ = (Real.exp (-(2 ^ 8 * Q.rate * dc)) * Real.exp (-(2 ^ 4 * Q.rate * dY))) * Real.exp (-(2 * Q.rate * d')) := by ring
          _ ≤ _ := mul_le_mul_of_nonneg_right hcdec (Real.exp_pos _).le
      have h3 : (if b' = b then Zd * (B * Real.exp (-(r * s1))) else 0) ≤
          Z * B * (e1 * Real.exp (-(2 * Q.rate * d'))) := by
        split_ifs with hb
        · have hdd : d' = dY := by rw [hd', hdY, hb]
          rw [hdd]
          calc Zd * (B * Real.exp (-(r * s1))) = Z * B * (Real.exp (-(2 ^ 8 * Q.rate * dc)) * Real.exp (-(r * s1))) := by
                rw [hZd]; ring
            _ ≤ Z * B * (Real.exp (-(2 ^ 8 * Q.rate * dc)) *
                  (Real.exp (-(2 ^ 4 * Q.rate * dY)) * Real.exp (-(2 * Q.rate * dY)))) :=
                mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hP1 (Real.exp_pos _).le) (mul_nonneg hZ0 hB)
            _ = Z * B * ((Real.exp (-(2 ^ 8 * Q.rate * dc)) * Real.exp (-(2 ^ 4 * Q.rate * dY))) *
                  Real.exp (-(2 * Q.rate * dY))) := by ring
            _ ≤ _ := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hcdec (Real.exp_pos _).le)
                (mul_nonneg hZ0 hB)
        · exact mul_nonneg (mul_nonneg hZ0 hB) (mul_nonneg he1p.le (Real.exp_pos _).le)
      have h4 : Zd * (B * Real.exp (-(r * s2))) ≤ Z * B * (e1 * Real.exp (-(2 * Q.rate * d'))) := by
        calc Zd * (B * Real.exp (-(r * s2))) = Z * B * (Real.exp (-(2 ^ 8 * Q.rate * dc)) * Real.exp (-(r * s2))) := by
              rw [hZd]; ring
          _ ≤ _ := mul_le_mul_of_nonneg_left h1 (mul_nonneg hZ0 hB)
      calc _ ≤ Z * B * (e1 * Real.exp (-(2 * Q.rate * d'))) + Z * B * (e1 * Real.exp (-(2 * Q.rate * d'))) := add_le_add h4 h3
        _ = (2 * (Z * B)) * (e1 * Real.exp (-(2 * Q.rate * d'))) := by ring
        _ ≤ C * (e1 * Real.exp (-(2 * Q.rate * d'))) :=
          mul_le_mul_of_nonneg_right hZB (mul_nonneg he1p.le (Real.exp_pos _).le)
        _ = _ := by ring
    have hcont : ContinuousOn φ (bondBall _ Q.ballRadius) := hc.continuousOn
    have hs : HasLocalSize Q.ballRadius (cutoffFactor Q.ballRadius Q.cutoff) Ψ (fun q => 1 + m q) Q.coupling Q.rate
        (Real.sqrt Q.coupling * (C * Q.coupling ^ (-(1 / 2) : ℝ)) * e1) (bondDistToCell Y) φ := by
      have hamp : Real.sqrt Q.coupling * (C * Q.coupling ^ (-(1 / 2) : ℝ)) = C := by
        calc _ = C * (Real.sqrt Q.coupling * Q.coupling ^ (-(1 / 2) : ℝ)) := by ring
          _ = C := by rw [hsq, mul_one]
      rw [hamp]
      refine ⟨fun η hη => (hc.contDiffAt (hO.mem_nhds hη)).differentiableAt (by norm_num), 0, fun q hq => ⟨?_, fun b' => ?_⟩⟩
      · have h1 := momentBound_of_bounded hL hx hm hρ hf.moments (f := fun η => φ η - 0) (hcont.sub continuousOn_const)
          (mul_nonneg hC0 he1p.le) (fun η hη => by simpa using hval2 η hη) q hq
        exact h1
      · have hc' : ContinuousOn (bondGradNorm φ b') (bondBall _ Q.ballRadius) := by
          unfold bondGradNorm
          exact ((hc.continuousOn_fderiv_of_isOpen (isOpen_bondBall _) le_rfl).clm_comp continuousOn_const).norm
        have hB' : 0 ≤ C * e1 * Real.exp (-(2 * Q.rate * bondDistToCell Y b')) :=
          mul_nonneg (mul_nonneg hC0 he1p.le) (Real.exp_pos _).le
        have h1 := momentBound_of_bounded hL hx hm hρ hf.moments hc' hB' (fun η hη => by
          rw [abs_of_nonneg (show 0 ≤ bondGradNorm φ b' η from norm_nonneg _)]
          exact hgrad2 η hη b') q hq
        have hmq : 0 ≤ 1 + m q := by linarith [hm q]
        refine momentBound_mono h1 (mul_nonneg hmq hB') ?_
        calc (1 + m q) * (C * e1 * Real.exp (-(2 * Q.rate * bondDistToCell Y b'))) =
              (1 + m q) * 1 * C * e1 * Real.exp (-(2 * Q.rate * bondDistToCell Y b')) := by ring
          _ ≤ (1 + m q) * Real.sqrt Q.coupling * C * e1 * Real.exp (-(2 * Q.rate * bondDistToCell Y b')) := by gcongr
          _ = _ := by ring
    exact hasLocalSize_congr_density hd.symm hs
  · obtain ⟨-, hmom, -⟩ := topDeriv_moments hS hf hK hk3 c X hX
    have h1 := momentBound_congr hz0 (hmd k c X hk3) (hmom 1 le_rfl)
    have h2 := abs_ballExpectation_le_of_momentBound hL h1
    unfold ColdHalfLaw.expectation
    change |ballExpectation (cutoffFactor Q.ballRadius Q.cutoff) (Q.exponent V) _| ≤ _
    rw [hmean_eq]
    refine h2.trans (le_of_eq ?_)
    ring
section SumOfTwo
variable {ι : Type} [Fintype ι] [DecidableEq ι]
theorem hasLocalSize_add (hS2 : FiniteSumSizeBound) {ρ x κ h₁ h₂ : ℝ} {p : ℝ → ℝ} {Ψ : BondField ι → ℝ}
    {Cq : ℕ → ℝ} {dZ : ι → ℝ} {H₁ H₂ : BondField ι → ℝ} (hρ : 0 < ρ) (hp : IsCutoff ρ p) (hΨ : Continuous Ψ)
    (hx : 0 < x) (hCq : ∀ q, 0 < Cq q) (h1 : 0 < h₁) (h2 : 0 < h₂) (c1 : ContDiffOn ℝ 1 H₁ {η | ∀ b, ‖η b‖ < ρ})
    (c2 : ContDiffOn ℝ 1 H₂ {η | ∀ b, ‖η b‖ < ρ}) (s1 : HasLocalSize ρ (cutoffFactor ρ p) Ψ Cq x κ h₁ dZ H₁)
    (s2 : HasLocalSize ρ (cutoffFactor ρ p) Ψ Cq x κ h₂ dZ H₂) :
    HasLocalSize ρ (cutoffFactor ρ p) Ψ Cq x κ (h₁ + h₂) dZ fun η => H₁ η + H₂ η := by
  have := hS2 ι Bool Finset.univ ρ x κ (h₁ + h₂) p Ψ Cq (fun j => if j then H₁ else H₂) (fun j => if j then h₁ else h₂)
    (fun _ => dZ) dZ hρ hp hΨ hx hCq (fun j => by cases j <;> simpa) (fun j => by cases j <;> simpa)
    (fun j _ => by cases j <;> simpa) (by simp [add_comm]) (fun b => by
      simp only [Fintype.sum_bool, if_true, Bool.false_eq_true, if_false]
      rw [add_mul, add_comm])
  simpa [Fintype.sum_bool, add_comm] using this
theorem hasLocalSize_add_const {ρ x κ h : ℝ} {r : ℝ → ℝ} {Ψ : BondField ι → ℝ} {Cq : ℕ → ℝ} {dZ : ι → ℝ}
    {H : BondField ι → ℝ} (a : ℝ) (s : HasLocalSize ρ r Ψ Cq x κ h dZ H) :
    HasLocalSize ρ r Ψ Cq x κ h dZ fun η => H η + a := by
  obtain ⟨h1, H₀, h2⟩ := s
  refine ⟨fun η hη => (h1 η hη).add_const a, H₀ + a, fun q hq => ⟨?_, fun b => ?_⟩⟩
  · have e : (fun η => H η + a - (H₀ + a)) = fun η => H η - H₀ := by
      funext η
      ring
    rw [e]
    exact (h2 q hq).1
  · have e : bondGradNorm (fun η => H η + a) b = bondGradNorm H b := by
      funext η
      unfold bondGradNorm
      rw [fderiv_add_const]
    rw [e]
    exact (h2 q hq).2 b
end SumOfTwo
section BlockExponentAlong
variable {ι : Type} [Fintype ι] [DecidableEq ι]
theorem fderiv_fderiv_apply_swap {A : BondField ι → ℝ} {ζ : BondField ι}
    (h : DifferentiableAt ℝ (fderiv ℝ A) ζ) (u v : BondField ι) :
    fderiv ℝ (fun ζ' => fderiv ℝ A ζ' u) ζ v = fderiv ℝ (fderiv ℝ A) ζ v u := by
  have := (h.hasFDerivAt.clm_apply (hasFDerivAt_const u ζ)).fderiv
  rw [this]
  simp
theorem mul_sqrt_add_one_le {x sq : ℝ} (hx1 : 1 ≤ x) (hsq : 0 ≤ sq) : x * Real.sqrt sq + 1 ≤ Real.sqrt x * (2 + x * sq) := by
  have hx : 0 ≤ x := by linarith
  have hs : 1 ≤ Real.sqrt x := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_le_sqrt hx1
  have hq : Real.sqrt x ^ 2 = x := Real.sq_sqrt hx
  have hu : Real.sqrt sq ^ 2 = sq := Real.sq_sqrt hsq
  set s := Real.sqrt x
  set u := Real.sqrt sq
  have h1 : s * u ≤ 1 + (s * u) ^ 2 := by nlinarith [sq_nonneg (s * u - 1)]
  have e : x * sq = (s * u) ^ 2 := by rw [mul_pow, hq, hu]
  have e2 : x * u = s * (s * u) := by rw [← hq]; ring
  rw [e, e2]
  nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ s) (sq_nonneg (s * u)), mul_le_mul_of_nonneg_left h1 (by linarith : (0 : ℝ) ≤ s)]
theorem bondPartial_along_moments {ρ x : ℝ} {p : ℝ → ℝ} {Ψ : BondField ι → ℝ} {m : ℕ → ℝ} (hL : BallLawFacts ρ p Ψ) (hx : 0 < x)
    (hm : ∀ q, 0 ≤ m q) (hρ : 0 < ρ)
    (hmom : ∀ (q : ℕ) (b : ι), ballExpectation (cutoffFactor ρ p) Ψ (fun η => ‖η b‖ ^ (2 * q)) ≤ m q * (x ^ q)⁻¹)
    {A : BondField ι → ℝ} (b : ι) {z : BondVector → BondVector} {Zd Pc β₀ : ℝ} {w Sc β₁ : ι → ℝ}
    (hw : ∀ b, 0 ≤ w b) (hZd : 0 ≤ Zd) (hPc : 0 ≤ Pc) (hSc : ∀ b, 0 ≤ Sc b)
    (hA : ∀ ζ ∈ bondBall ι ρ, ContDiffAt ℝ 2 A ζ)
    (hz : ∀ v : BondVector, ‖v‖ < ρ → ContDiffAt ℝ 1 z v ∧ ‖z v‖ ≤ Zd ∧ ‖fderiv ℝ z v‖ ≤ Zd)
    (hP : ∀ ζ ∈ bondBall ι ρ, ∀ e : BondVector,
      |fderiv ℝ A ζ (Pi.single b e)| ≤ Pc * (2 + ∑ b, w b * (x * ‖ζ b‖ ^ 2)) * ‖e‖)
    (hSec : ∀ ζ ∈ bondBall ι ρ, ∀ (b₀ : ι) (e e' : BondVector),
      |fderiv ℝ (fderiv ℝ A) ζ (Pi.single b₀ e) (Pi.single b e')| ≤ Sc b₀ * ‖e'‖ * ‖e‖)
    (hv : Zd * Pc ≤ β₀) (hg : ∀ b₀, Zd * Sc b₀ ≤ β₁ b₀) (hg' : Zd * Pc ≤ β₁ b) :
    ContDiffOn ℝ 1 (fun ζ => bondPartialDeriv A b ζ (z (ζ b))) (bondBall ι ρ) ∧
    (∀ q : ℕ, 1 ≤ q → MomentBound (cutoffFactor ρ p) Ψ (fun ζ => bondPartialDeriv A b ζ (z (ζ b))) q
      ((1 + m q) * β₀ * (2 + ∑ b, w b))) ∧
    ∀ (q : ℕ) (b₀ : ι), 1 ≤ q → MomentBound (cutoffFactor ρ p) Ψ (bondGradNorm (fun ζ => bondPartialDeriv A b ζ (z (ζ b))) b₀) q
      ((1 + m q) * β₁ b₀ * (3 + ∑ b, w b)) := by
  classical
  set φ : BondField ι → ℝ := fun ζ => bondPartialDeriv A b ζ (z (ζ b)) with hφ
  have hone : ∀ ζ ∈ bondBall ι ρ, ContDiffAt ℝ 1 φ ζ ∧
      ∀ (b' : ι) (e : BondVector), fderiv ℝ φ ζ (Pi.single b' e) =
        fderiv ℝ (fderiv ℝ A) ζ (Pi.single b' e) (Pi.single b (z (ζ b))) +
          if b' = b then fderiv ℝ A ζ (Pi.single b (fderiv ℝ z (ζ b) e)) else 0 := fun ζ hζ =>
    fderiv_bondPartial_along b (hA ζ hζ) (hz _ (hζ b)).1
  have hOn : ContDiffOn ℝ 1 φ (bondBall ι ρ) := fun ζ hζ => (hone ζ hζ).1.contDiffWithinAt
  have ht : ∀ ζ : BondField ι, 0 ≤ ∑ b, w b * (x * ‖ζ b‖ ^ 2) := fun ζ =>
    Finset.sum_nonneg fun b _ => mul_nonneg (hw b) (by positivity)
  have hβ0 : 0 ≤ β₀ := (mul_nonneg hZd hPc).trans hv
  have hβ1 : ∀ b₀, 0 ≤ β₁ b₀ := fun b₀ => (mul_nonneg hZd (hSc b₀)).trans (hg b₀)
  refine ⟨hOn, fun q hq => ?_, fun q b₀ hq => ?_⟩
  · refine momentBound_of_quadratic hL hx hm hρ hmom hOn.continuousOn (E := 2) (β := β₀) (w := w) (by norm_num) hβ0 hw
      (fun ζ hζ => ?_) q hq
    have h1 := hP ζ hζ (z (ζ b))
    have h2 := (hz _ (hζ b)).2.1
    have h3 := ht ζ
    calc |φ ζ| ≤ Pc * (2 + ∑ b, w b * (x * ‖ζ b‖ ^ 2)) * ‖z (ζ b)‖ := h1
      _ ≤ Pc * (2 + ∑ b, w b * (x * ‖ζ b‖ ^ 2)) * Zd := by gcongr
      _ = (Zd * Pc) * (2 + ∑ b, w b * (x * ‖ζ b‖ ^ 2)) := by ring
      _ ≤ β₀ * (2 + ∑ b, w b * (x * ‖ζ b‖ ^ 2)) := by gcongr
  · have hc : ContinuousOn (bondGradNorm φ b₀) (bondBall ι ρ) := by
      unfold bondGradNorm
      exact ((hOn.continuousOn_fderiv_of_isOpen (isOpen_bondBall _) le_rfl).clm_comp continuousOn_const).norm
    refine momentBound_of_quadratic hL hx hm hρ hmom hc (E := 3) (β := β₁ b₀) (w := w) (by norm_num) (hβ1 b₀) hw
      (fun ζ hζ => ?_) q hq
    have h3 := ht ζ
    have hb0 := hβ1 b₀
    set T := ∑ b, w b * (x * ‖ζ b‖ ^ 2) with hT
    rw [abs_of_nonneg (show 0 ≤ bondGradNorm φ b₀ ζ from norm_nonneg _)]
    have hB0 : 0 ≤ β₁ b₀ * (3 + T) := by positivity
    unfold bondGradNorm
    refine ContinuousLinearMap.opNorm_le_bound _ hB0 fun e => ?_
    have hD : ∀ u : BondVector, ‖u‖ = 1 → |fderiv ℝ φ ζ (Pi.single b₀ u)| ≤ β₁ b₀ * (3 + T) := fun u hu => by
      rw [(hone ζ hζ).2 b₀ u]
      have h4 : |fderiv ℝ (fderiv ℝ A) ζ (Pi.single b₀ u) (Pi.single b (z (ζ b)))| ≤ β₁ b₀ := by
        have h5 := hSec ζ hζ b₀ u (z (ζ b))
        rw [hu, mul_one] at h5
        have h6 := (hz _ (hζ b)).2.1
        calc _ ≤ Sc b₀ * ‖z (ζ b)‖ := h5
          _ ≤ Sc b₀ * Zd := mul_le_mul_of_nonneg_left h6 (hSc b₀)
          _ = Zd * Sc b₀ := mul_comm _ _
          _ ≤ _ := hg b₀
      have h7 : |if b₀ = b then fderiv ℝ A ζ (Pi.single b (fderiv ℝ z (ζ b) u)) else 0| ≤ β₁ b₀ * (2 + T) := by
        split_ifs with hb
        · subst hb
          have h8 : ‖fderiv ℝ z (ζ b₀) u‖ ≤ Zd := by
            have := (fderiv ℝ z (ζ b₀)).le_opNorm u
            rw [hu, mul_one] at this
            exact this.trans (hz _ (hζ b₀)).2.2
          have h9 := hP ζ hζ (fderiv ℝ z (ζ b₀) u)
          calc _ ≤ Pc * (2 + T) * ‖fderiv ℝ z (ζ b₀) u‖ := h9
            _ ≤ Pc * (2 + T) * Zd := by gcongr
            _ = (Zd * Pc) * (2 + T) := by ring
            _ ≤ _ := by gcongr
        · simp only [abs_zero]
          positivity
      calc _ ≤ _ := abs_add_le _ _
        _ ≤ β₁ b₀ + β₁ b₀ * (2 + T) := add_le_add h4 h7
        _ = _ := by ring
    have h1 := abs_apply_le_of_unit (ℓ := (fderiv ℝ φ ζ).comp
      (ContinuousLinearMap.single ℝ (fun _ : ι => BondVector) b₀)) (D := β₁ b₀ * (3 + T)) hD e hB0
    rwa [Real.norm_eq_abs]
end BlockExponentAlong
section BlockExponentFrames
variable {F : BlockFrame}
theorem contDiffAt_top_of_joint {n : WithTop ℕ∞} {V : F.GaugeField F.top} {G : AboveFrames F} {ζ : StepVariable (finiteCells F)}
    (h1 : ContDiffAt ℝ n (fun q : (Fin 0 → ℝ) × StepVariable (finiteCells F) =>
      G q.2 (leftTranslate (bondSpread ![] ![] q.1) V)) (0, ζ)) : ContDiffAt ℝ n (fun η => G η V) ζ := by
  have h2 : ContDiffAt ℝ n (fun η : StepVariable (finiteCells F) =>
      (fun q : (Fin 0 → ℝ) × StepVariable (finiteCells F) => G q.2 (leftTranslate (bondSpread ![] ![] q.1) V)) (0, η)) ζ :=
    ContDiffAt.comp (g := fun q : (Fin 0 → ℝ) × StepVariable (finiteCells F) => G q.2 (leftTranslate (bondSpread ![] ![] q.1) V))
      (f := fun η : StepVariable (finiteCells F) => ((0 : Fin 0 → ℝ), η)) ζ h1
      (contDiff_const.prodMk contDiff_id).contDiffAt
  have e : (fun η : StepVariable (finiteCells F) =>
      (fun q : (Fin 0 → ℝ) × StepVariable (finiteCells F) => G q.2 (leftTranslate (bondSpread ![] ![] q.1) V)) (0, η)) =
      fun η => G η V := by
    funext η
    simp only []
    rw [leftTranslate_bondSpread_zero]
  rwa [e] at h2
theorem cellSupDist_le_bondSpanWithCell (Y z : F.Cell) : cellSupDist Y z ≤ bondSpanWithCell Y z ![] := by
  unfold bondSpanWithCell bondSpan
  refine le_trans ?_ (le_max_left _ _)
  exact Finset.le_sup (f := fun l : Fin (0 + 1) =>
    siteSupDist Y ((Fin.cons (z, 0) ![] : Fin (0 + 1) → F.Site F.top × Fin 4) l).1) (Finset.mem_univ (0 : Fin (0 + 1)))
theorem exp_decay_combine {κ dc dY d M : ℝ} (hκ : 0 < κ) (hdc : 0 ≤ dc) (hM0 : 0 ≤ M) (h1 : dY ≤ M) (h2 : d ≤ M) :
    Real.exp (-(2 ^ 8 * κ * dc)) * Real.exp (-(2 ^ 6 * κ * M)) ≤
      Real.exp (-(2 ^ 4 * κ * dY) - 2 ^ 6 * κ * dc) * Real.exp (-(2 * κ * d)) := by
  rw [← Real.exp_add, ← Real.exp_add, Real.exp_le_exp]
  nlinarith [mul_nonneg hκ.le hdc, mul_nonneg hκ.le (sub_nonneg.2 h1), mul_nonneg hκ.le (sub_nonneg.2 h2), mul_nonneg hκ.le hM0]
variable {Q : ColdHalfLaw} {V : F.GaugeField F.top} {Y : F.Cell}
theorem blockExponent_fderiv_single_le {Cs : ℝ} (hCs : 0 < Cs) (hx1 : 1 ≤ Q.coupling) (hκ : 0 < Q.rate) (hsym : ∀ u v : F.Cell, cellSupDist u v = cellSupDist v u)
    (hE : InterpolatedExponentBounds 1 Q.a Q.chartRadius Q.ballRadius Q.coupling Q.rate Cs Q.mirrorRadius V) (b : ↥(chordBonds (finiteCells F)))
    {ζ : StepVariable (finiteCells F)} (hζ : ζ ∈ bondBall ↥(chordBonds (finiteCells F)) Q.ballRadius) (e : BondVector) :
    |fderiv ℝ (fun η => Q.blockExponent Y η V) ζ (Pi.single b e)| ≤
      Cs * Real.sqrt Q.coupling * Real.exp (-(2 ^ 6 * Q.rate * bondDistToCell Y b)) *
        (2 + ∑ b', Real.exp (-(2 ^ 6 * Q.rate * bondDistToCell Y b')) * (Q.coupling * ‖ζ b'‖ ^ 2)) * ‖e‖ := by
  classical
  have hsq0 : 0 ≤ localSqNorm Q.rate Y ζ :=
    Finset.sum_nonneg fun b _ => mul_nonneg (Real.exp_pos _).le (by positivity)
  have ht : ∑ b', Real.exp (-(2 ^ 6 * Q.rate * bondDistToCell Y b')) * (Q.coupling * ‖ζ b'‖ ^ 2) =
      Q.coupling * localSqNorm Q.rate Y ζ := by
    simp only [localSqNorm, Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    simp only [bondDistToCell]
    ring
  rw [ht]
  have hD0 : 0 ≤ Cs * Real.sqrt Q.coupling * Real.exp (-(2 ^ 6 * Q.rate * bondDistToCell Y b)) * (2 + Q.coupling * localSqNorm Q.rate Y ζ) := by
    positivity
  refine abs_apply_le_of_unit (ℓ := (fderiv ℝ (fun η => Q.blockExponent Y η V) ζ).comp
    (ContinuousLinearMap.single ℝ (fun _ : ↥(chordBonds (finiteCells F)) => BondVector) b))
    (fun u hu => ?_) e hD0
  have h1 := hE.deriv_top_partial Y ζ b u 0 ![] ![] hζ (by omega) (fun l => l.elim0) hu
  have e0 : bondDeriv (fun V' => bondPartialDeriv (interpolatedBlockExponent 1 Q.a Q.chartRadius Q.coupling Q.mirrorRadius Y V') b ζ u) V ![] ![] =
      bondPartialDeriv (interpolatedBlockExponent 1 Q.a Q.chartRadius Q.coupling Q.mirrorRadius Y V) b ζ u := by
    simp only [bondDeriv, iteratedFDeriv_zero_apply]
    rw [leftTranslate_bondSpread_zero]
  rw [e0] at h1
  have h2 : bondDistToCell Y b ≤ (bondSpanWithCell Y (enclosingCell b.1.1) ![] : ℕ) := by
    have h3 := cellSupDist_le_bondSpanWithCell Y (enclosingCell b.1.1)
    rw [hsym] at h3
    exact Nat.cast_le.2 h3
  have h4 : Real.exp (-(2 ^ 6 * Q.rate * (bondSpanWithCell Y (enclosingCell b.1.1) ![] : ℕ))) ≤
      Real.exp (-(2 ^ 6 * Q.rate * bondDistToCell Y b)) := by
    rw [Real.exp_le_exp]
    have h5 : 0 ≤ 2 ^ 6 * Q.rate := by positivity
    nlinarith
  have h5 := mul_sqrt_add_one_le hx1 hsq0
  calc _ ≤ _ := h1
    _ ≤ Cs * (Real.sqrt Q.coupling * (2 + Q.coupling * localSqNorm Q.rate Y ζ)) * Real.exp (-(2 ^ 6 * Q.rate * bondDistToCell Y b)) := by
        gcongr
    _ = _ := by ring
theorem blockExponent_second_le {Cs : ℝ} (hCs : 0 < Cs) (hx1 : 1 ≤ Q.coupling) (hκ : 0 < Q.rate)
    (hsym : ∀ u v : F.Cell, cellSupDist u v = cellSupDist v u) (hE : InterpolatedExponentBounds 1 Q.a Q.chartRadius Q.ballRadius Q.coupling Q.rate Cs Q.mirrorRadius V) (b b₀ : ↥(chordBonds (finiteCells F)))
    {ζ : StepVariable (finiteCells F)} (hζ : ζ ∈ bondBall ↥(chordBonds (finiteCells F)) Q.ballRadius)
    (hA : ContDiffAt ℝ 3 (fun η => Q.blockExponent Y η V) ζ) (e e' : BondVector) :
    |fderiv ℝ (fderiv ℝ fun η => Q.blockExponent Y η V) ζ (Pi.single b₀ e) (Pi.single b e')| ≤
      Cs * Q.coupling * Real.exp (-(2 ^ 6 * Q.rate * max (bondDistToCell Y b) (bondDistToCell Y b₀))) * ‖e'‖ * ‖e‖ := by
  have hEm0 : 0 ≤ Cs * Q.coupling * Real.exp (-(2 ^ 6 * Q.rate * max (bondDistToCell Y b) (bondDistToCell Y b₀))) := by
    positivity
  refine abs_bilinear_le_of_unit (Bm := fderiv ℝ (fderiv ℝ fun η => Q.blockExponent Y η V) ζ) hEm0 (fun u u' hu hu' => ?_) e e'
  have hdiff : DifferentiableAt ℝ (fderiv ℝ fun η => Q.blockExponent Y η V) ζ :=
    (hA.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have h1 := hE.second_deriv Y ζ b b₀ u' u hζ hu' hu
  have e0 : secondDerivAlong (interpolatedBlockExponent 1 Q.a Q.chartRadius Q.coupling Q.mirrorRadius Y V) ζ (bondVariation b u') (bondVariation b₀ u) =
      fderiv ℝ (fderiv ℝ fun η => Q.blockExponent Y η V) ζ (Pi.single b₀ u) (Pi.single b u') := fderiv_fderiv_apply_swap hdiff _ _
  rw [e0] at h1
  refine h1.trans ?_
  have h2 : max (bondDistToCell Y b) (bondDistToCell Y b₀) ≤
      ((max (cellSupDist Y (enclosingCell b.1.1)) (max (cellSupDist Y (enclosingCell b₀.1.1)) (cellSupDist (enclosingCell b.1.1) (enclosingCell b₀.1.1))) : ℕ) : ℝ) := by
    push_cast
    simp only [bondDistToCell]
    rw [hsym (enclosingCell b.1.1) Y, hsym (enclosingCell b₀.1.1) Y]
    exact max_le (le_max_left _ _) ((le_max_left _ _).trans (le_max_right _ _))
  have hκ6 : 0 ≤ 2 ^ 6 * Q.rate := by positivity
  have h3 := mul_le_mul_of_nonneg_left h2 hκ6
  have h4 : Real.exp (-(2 ^ 6 * Q.rate * ((max (cellSupDist Y (enclosingCell b.1.1)) (max (cellSupDist Y (enclosingCell b₀.1.1)) (cellSupDist (enclosingCell b.1.1) (enclosingCell b₀.1.1))) : ℕ) : ℝ))) ≤
      Real.exp (-(2 ^ 6 * Q.rate * max (bondDistToCell Y b) (bondDistToCell Y b₀))) := by
    rw [Real.exp_le_exp]
    linarith
  exact mul_le_mul_of_nonneg_left h4 (by positivity)
variable {m : ℕ → ℝ} {Ψ : StepVariable (finiteCells F) → ℝ}
theorem blockExponent_along_size (hL : BallLawFacts Q.ballRadius Q.cutoff Ψ) (hm : ∀ q, 0 ≤ m q) (hρ : 0 < Q.ballRadius) (hx1 : 1 ≤ Q.coupling) (hκ : 0 < Q.rate)
    (hmom : ∀ (q : ℕ) (b : ↥(chordBonds (finiteCells F))),
      ballExpectation (cutoffFactor Q.ballRadius Q.cutoff) Ψ (fun η => ‖η b‖ ^ (2 * q)) ≤ m q * (Q.coupling ^ q)⁻¹)
    {W Cs Z C₃ : ℝ} (hCs : 0 < Cs) (hZ0 : 0 ≤ Z) (hC₃ : Z * Cs * (3 + W) ≤ C₃)
    (hsym : ∀ u v : F.Cell, cellSupDist u v = cellSupDist v u)
    (hW : ∑ b : ↥(chordBonds (finiteCells F)), Real.exp (-(2 ^ 6 * Q.rate * bondDistToCell Y b)) ≤ W)
    (hE : InterpolatedExponentBounds 1 Q.a Q.chartRadius Q.ballRadius Q.coupling Q.rate Cs Q.mirrorRadius V)
    (hA : ∀ ζ : StepVariable (finiteCells F), (∀ b, ‖ζ b‖ ≤ Q.ballRadius) → ContDiffAt ℝ 3 (fun η => Q.blockExponent Y η V) ζ)
    (b : ↥(chordBonds (finiteCells F))) {z : BondVector → BondVector} {dc : ℝ} (hdc : 0 ≤ dc)
    (hz : ∀ v : BondVector, ‖v‖ < Q.ballRadius → ContDiffAt ℝ 1 z v ∧ ‖z v‖ ≤ Z * Real.exp (-(2 ^ 8 * Q.rate * dc)) ∧
      ‖fderiv ℝ z v‖ ≤ Z * Real.exp (-(2 ^ 8 * Q.rate * dc))) :
    ContDiffOn ℝ 1 (fun ζ => bondPartialDeriv (fun η => Q.blockExponent Y η V) b ζ (z (ζ b))) (bondBall _ Q.ballRadius) ∧
    HasLocalSize Q.ballRadius (cutoffFactor Q.ballRadius Q.cutoff) Ψ (fun q => 1 + m q) Q.coupling Q.rate
      (Real.sqrt Q.coupling * C₃ * Real.exp (-(2 ^ 4 * Q.rate * bondDistToCell Y b) - 2 ^ 6 * Q.rate * dc)) (bondDistToCell Y)
      (fun ζ => bondPartialDeriv (fun η => Q.blockExponent Y η V) b ζ (z (ζ b))) := by
  classical
  have hx : 0 < Q.coupling := by linarith
  have hs0 : 0 < Real.sqrt Q.coupling := Real.sqrt_pos.2 hx
  have hsqq : Real.sqrt Q.coupling * Real.sqrt Q.coupling = Q.coupling := Real.mul_self_sqrt hx.le
  have hs1 : 1 ≤ Real.sqrt Q.coupling := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_le_sqrt hx1
  have hsx : Real.sqrt Q.coupling ≤ Q.coupling := by nlinarith
  set dY : ℝ := bondDistToCell Y b with hdY
  have hdY0 : 0 ≤ dY := Nat.cast_nonneg _
  set e1 : ℝ := Real.exp (-(2 ^ 4 * Q.rate * dY) - 2 ^ 6 * Q.rate * dc) with he1
  have he1p : 0 < e1 := Real.exp_pos _
  set Zd : ℝ := Z * Real.exp (-(2 ^ 8 * Q.rate * dc)) with hZd
  have hZd0 : 0 ≤ Zd := mul_nonneg hZ0 (Real.exp_pos _).le
  set ew : ℝ := Real.exp (-(2 ^ 6 * Q.rate * dY)) with hew
  have hew0 : 0 < ew := Real.exp_pos _
  let w : ↥(chordBonds (finiteCells F)) → ℝ := fun b => Real.exp (-(2 ^ 6 * Q.rate * bondDistToCell Y b))
  let Sc : ↥(chordBonds (finiteCells F)) → ℝ := fun b₀ =>
    Cs * Q.coupling * Real.exp (-(2 ^ 6 * Q.rate * max dY (bondDistToCell Y b₀)))
  let β₁ : ↥(chordBonds (finiteCells F)) → ℝ := fun b₀ => Z * Cs * Q.coupling * e1 * Real.exp (-(2 * Q.rate * bondDistToCell Y b₀))
  have hSc : ∀ b₀, 0 ≤ Sc b₀ := fun b₀ => by
    simp only [Sc]
    positivity
  have hw0 : ∀ b, 0 ≤ w b := fun b => (Real.exp_pos _).le
  have hA2 : ∀ ζ ∈ bondBall ↥(chordBonds (finiteCells F)) Q.ballRadius, ContDiffAt ℝ 2 (fun η => Q.blockExponent Y η V) ζ := fun ζ hζ =>
    (hA ζ fun b => (hζ b).le).of_le (by norm_num)
  have hcore : Real.exp (-(2 ^ 8 * Q.rate * dc)) * ew ≤ e1 * Real.exp (-(2 * Q.rate * dY)) :=
    exp_decay_combine hκ hdc hdY0 le_rfl le_rfl
  have hcore0 : Real.exp (-(2 ^ 8 * Q.rate * dc)) * ew ≤ e1 := by
    have h1 : Real.exp (-(2 * Q.rate * dY)) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      nlinarith [mul_nonneg hκ.le hdY0]
    exact hcore.trans (mul_le_of_le_one_right he1p.le h1)
  obtain ⟨hOn, hm1, hm2⟩ := bondPartial_along_moments (A := fun η => Q.blockExponent Y η V) (b := b) (z := z) (Zd := Zd)
    (Pc := Cs * Real.sqrt Q.coupling * ew) (β₀ := Z * Cs * Real.sqrt Q.coupling * e1) (w := w) (Sc := Sc) (β₁ := β₁)
    hL hx hm hρ hmom hw0 hZd0 (by positivity) hSc hA2 hz
    (fun ζ hζ e => blockExponent_fderiv_single_le hCs hx1 hκ hsym hE b hζ e)
    (fun ζ hζ b₀ e e' => blockExponent_second_le hCs hx1 hκ hsym hE b b₀ hζ (hA ζ fun b => (hζ b).le) e e')
    (by
      calc Zd * (Cs * Real.sqrt Q.coupling * ew) = Z * Cs * Real.sqrt Q.coupling * (Real.exp (-(2 ^ 8 * Q.rate * dc)) * ew) := by
            rw [hZd]; ring
        _ ≤ Z * Cs * Real.sqrt Q.coupling * e1 := mul_le_mul_of_nonneg_left hcore0 (by positivity))
    (fun b₀ => by
      have hd0 : (0 : ℝ) ≤ bondDistToCell Y b₀ := Nat.cast_nonneg _
      have h1 := exp_decay_combine (M := max dY (bondDistToCell Y b₀)) hκ hdc (le_max_of_le_left hdY0) (le_max_left _ _) (le_max_right _ _)
      calc Zd * Sc b₀ = Z * Cs * Q.coupling * (Real.exp (-(2 ^ 8 * Q.rate * dc)) *
            Real.exp (-(2 ^ 6 * Q.rate * max dY (bondDistToCell Y b₀)))) := by
            simp only [hZd, Sc]; ring
        _ ≤ Z * Cs * Q.coupling * (e1 * Real.exp (-(2 * Q.rate * bondDistToCell Y b₀))) :=
            mul_le_mul_of_nonneg_left h1 (by positivity)
        _ = β₁ b₀ := by simp only [β₁]; ring)
    (by
      calc Zd * (Cs * Real.sqrt Q.coupling * ew) = Z * Cs * Real.sqrt Q.coupling * (Real.exp (-(2 ^ 8 * Q.rate * dc)) * ew) := by
            rw [hZd]; ring
        _ ≤ Z * Cs * Q.coupling * (e1 * Real.exp (-(2 * Q.rate * dY))) := by
            refine mul_le_mul (mul_le_mul_of_nonneg_left hsx (by positivity)) hcore (by positivity) (by positivity)
        _ = β₁ b := by simp only [β₁, hdY]; ring)
  have hSum : ∑ b, w b ≤ W := hW
  have hSum0 : 0 ≤ ∑ b, w b := Finset.sum_nonneg fun b _ => hw0 b
  have hC₃0 : 0 ≤ C₃ := le_trans (mul_nonneg (mul_nonneg hZ0 hCs.le) (by linarith)) hC₃
  refine ⟨hOn, fun η hη => (hOn.contDiffAt ((isOpen_bondBall _).mem_nhds hη)).differentiableAt (by norm_num), 0,
    fun q hq => ⟨?_, fun b₀ => ?_⟩⟩
  · have hmq : 0 ≤ 1 + m q := by linarith [hm q]
    have h1 := hm1 q hq
    simp only [sub_zero]
    refine momentBound_mono h1 (by positivity) ?_
    calc (1 + m q) * (Z * Cs * Real.sqrt Q.coupling * e1) * (2 + ∑ b, w b)
        ≤ (1 + m q) * (Z * Cs * Real.sqrt Q.coupling * e1) * (3 + W) := by
          refine mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      _ = (1 + m q) * (Real.sqrt Q.coupling * (Z * Cs * (3 + W)) * e1) := by ring
      _ ≤ (1 + m q) * (Real.sqrt Q.coupling * C₃ * e1) := by gcongr
  · have hmq : 0 ≤ 1 + m q := by linarith [hm q]
    have h1 := hm2 q b₀ hq
    have hb0 : 0 ≤ β₁ b₀ := by
      simp only [β₁]
      positivity
    refine momentBound_mono h1 (by positivity) ?_
    set e' := Real.exp (-(2 * Q.rate * bondDistToCell Y b₀)) with he'
    have he'p : 0 < e' := Real.exp_pos _
    calc (1 + m q) * β₁ b₀ * (3 + ∑ b, w b) ≤ (1 + m q) * β₁ b₀ * (3 + W) := by
          refine mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      _ = (1 + m q) * Q.coupling * (Z * Cs * (3 + W)) * e1 * e' := by simp only [β₁]; ring
      _ ≤ (1 + m q) * Q.coupling * C₃ * e1 * e' := by gcongr
      _ = (1 + m q) * (Real.sqrt Q.coupling * Real.sqrt Q.coupling) * C₃ * e1 * e' := by rw [hsqq]
      _ = _ := by ring
end BlockExponentFrames
section FirstMomentSum
variable {ι : Type} [Fintype ι] [DecidableEq ι]
theorem momentBound_one_add {ρ : ℝ} {p : ℝ → ℝ} {Ψ : BondField ι → ℝ} (hL : BallLawFacts ρ p Ψ) {f g : BondField ι → ℝ}
    (hf : ContinuousOn f (bondBall ι ρ)) (hg : ContinuousOn g (bondBall ι ρ)) {B₁ B₂ : ℝ}
    (h1 : MomentBound (cutoffFactor ρ p) Ψ f 1 B₁) (h2 : MomentBound (cutoffFactor ρ p) Ψ g 1 B₂) :
    MomentBound (cutoffFactor ρ p) Ψ (fun η => f η + g η) 1 (B₁ + B₂) := by
  have := hL.isProbability
  have i1 : Integrable (fun η => |f η| ^ 1) (normalizedBallLaw (cutoffFactor ρ p) Ψ) := (hL.integrable_iff _).2 h1.1
  have i2 : Integrable (fun η => |g η| ^ 1) (normalizedBallLaw (cutoffFactor ρ p) Ψ) := (hL.integrable_iff _).2 h2.1
  have hae : AEStronglyMeasurable (fun η => |f η + g η| ^ 1) (normalizedBallLaw (cutoffFactor ρ p) Ψ) :=
    aestronglyMeasurable_of_continuousOn_ball hL ((hf.add hg).abs.pow 1)
  have hpt : ∀ η, |f η + g η| ^ 1 ≤ |f η| ^ 1 + |g η| ^ 1 := fun η => by
    simp only [pow_one]
    exact abs_add_le _ _
  have hfi : Integrable (fun η => |f η + g η| ^ 1) (normalizedBallLaw (cutoffFactor ρ p) Ψ) := by
    refine Integrable.mono' (i1.add i2) hae (Filter.Eventually.of_forall fun η => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact hpt η
  refine ⟨(hL.integrable_iff _).1 hfi, ?_⟩
  rw [← hL.integral_eq]
  have h3 := integral_mono hfi (i1.add i2) hpt
  have h4 : ∫ η, ((fun η => |f η| ^ 1) + fun η => |g η| ^ 1) η ∂normalizedBallLaw (cutoffFactor ρ p) Ψ =
      (∫ η, |f η| ^ 1 ∂normalizedBallLaw (cutoffFactor ρ p) Ψ) + ∫ η, |g η| ^ 1 ∂normalizedBallLaw (cutoffFactor ρ p) Ψ := integral_add i1 i2
  rw [h4] at h3
  have a1 : ∫ η, |f η| ^ 1 ∂normalizedBallLaw (cutoffFactor ρ p) Ψ ≤ B₁ :=
    (hL.integral_eq _).le.trans (h1.2.trans (le_of_eq (pow_one _)))
  have a2 : ∫ η, |g η| ^ 1 ∂normalizedBallLaw (cutoffFactor ρ p) Ψ ≤ B₂ :=
    (hL.integral_eq _).le.trans (h2.2.trans (le_of_eq (pow_one _)))
  rw [pow_one]
  exact h3.trans (add_le_add a1 a2)
end FirstMomentSum
section BlockExponentSlot
variable {F : BlockFrame}
theorem bondDeriv_add_eq {V : F.GaugeField F.top} {G₁ G₂ : AboveFrames F} {k : ℕ} (hk : k ≤ 3) {c : Fin k → F.Site F.top × Fin 4} {X : Fin k → imaginaryQuaternions}
    {η : StepVariable (finiteCells F)}
    (h1 : ContDiffAt ℝ 3 (fun q : (Fin k → ℝ) × StepVariable (finiteCells F) =>
      G₁ q.2 (leftTranslate (bondSpread c X q.1) V)) (0, η))
    (h2 : ContDiffAt ℝ 3 (fun q : (Fin k → ℝ) × StepVariable (finiteCells F) =>
      G₂ q.2 (leftTranslate (bondSpread c X q.1) V)) (0, η)) :
    bondDeriv (fun V' => G₁ η V' + G₂ η V') V c X = topDeriv G₁ V c X η + topDeriv G₂ V c X η := by
  have l : ∀ {G : AboveFrames F}, ContDiffAt ℝ 3 (fun q : (Fin k → ℝ) × StepVariable (finiteCells F) =>
      G q.2 (leftTranslate (bondSpread c X q.1) V)) (0, η) →
      ContDiffAt ℝ k (fun τ : Fin k → ℝ => G η (leftTranslate (bondSpread c X τ) V)) 0 := fun {G} h =>
    (ContDiffAt.comp (g := fun q : (Fin k → ℝ) × StepVariable (finiteCells F) => G q.2 (leftTranslate (bondSpread c X q.1) V))
      (f := fun τ : Fin k → ℝ => (τ, η)) 0 h (contDiff_id.prodMk contDiff_const).contDiffAt).of_le
      (by exact_mod_cast hk)
  have e := iteratedFDeriv_add_apply (i := k) (l h1) (l h2)
  have e3 : (fun τ : Fin k → ℝ => G₁ η (leftTranslate (bondSpread c X τ) V) + G₂ η (leftTranslate (bondSpread c X τ) V)) =
      (fun τ : Fin k → ℝ => G₁ η (leftTranslate (bondSpread c X τ) V)) + fun τ => G₂ η (leftTranslate (bondSpread c X τ) V) := rfl
  simp only [topDeriv, bondDeriv]
  rw [e3, e]
  rfl
theorem blockExponentAddKernelIsSlot (hLaw : normalizedBallLawIsProbabilityStatement) (hS : IteratedFDerivSlices)
    (hS2 : FiniteSumSizeBound) : BlockExponentAddKernelIsSlot := by
  intro F Q m Cz V Y R B r Wt W Z Cs C hA hm hCz hK hZ hB hZ0 hκ hr hWt1 hW0 hCs hsym hWt hW hE hsm hsz hR0 hC
  classical
  obtain ⟨Ψ, hΨc, hdens⟩ := hA.continuous_exponent
  have hρ := hA.ballRadius_pos
  have hx1 := hA.one_le_coupling
  have hx : 0 < Q.coupling := by linarith
  obtain ⟨hprob, hmean, hint, hball, -, -, -, -, -, hnz, -⟩ := hLaw _ Q.ballRadius Q.cutoff Ψ hρ hA.isCutoff hΨc
  have hd : ballDensity (cutoffFactor Q.ballRadius Q.cutoff) (Q.exponent V) = ballDensity (cutoffFactor Q.ballRadius Q.cutoff) Ψ := hdens
  have hmean_eq : ∀ f, ballExpectation (cutoffFactor Q.ballRadius Q.cutoff) (Q.exponent V) f = ballExpectation (cutoffFactor Q.ballRadius Q.cutoff) Ψ f := fun f => by
    unfold ballExpectation
    rw [hd]
  have hL : BallLawFacts Q.ballRadius Q.cutoff Ψ := ⟨hprob, hmean, hint, hball⟩
  have hmomΨ : ∀ (q : ℕ) (b : ↥(chordBonds (finiteCells F))),
      ballExpectation (cutoffFactor Q.ballRadius Q.cutoff) Ψ (fun η => ‖η b‖ ^ (2 * q)) ≤ m q * (Q.coupling ^ q)⁻¹ := fun q b => by
    rw [← hmean_eq]
    exact hA.moments q b
  have hz0 : ∀ η : StepVariable (finiteCells F), ¬ (∀ b, ‖η b‖ < Q.ballRadius) →
      ballDensity (cutoffFactor Q.ballRadius Q.cutoff) Ψ η = 0 := fun η hη => by
    by_contra hne
    exact hη ((hnz η).1 hne)
  have hO : IsOpen {η : StepVariable (finiteCells F) | ∀ b, ‖η b‖ < Q.ballRadius} := isOpen_bondBall Q.ballRadius
  have h00 : ∀ b : ↥(chordBonds (finiteCells F)), ‖(0 : StepVariable (finiteCells F)) b‖ ≤ Q.ballRadius := fun b => by
    simpa using hρ.le
  have hB0 := hB.le
  have hW1 : 0 < Wt := by linarith
  set C₂ : ℝ := 4 * B * Wt * (1 + Z) with hC₂
  set C₃ : ℝ := Cs * (3 + W) * (1 + Z) with hC₃
  have hC₂p : 0 < C₂ := by positivity
  have hC₃p : 0 < C₃ := by positivity
  have hC23 : C₃ + C₂ ≤ C := by linarith
  have hCpos : 0 < C := by linarith
  obtain ⟨hM, -⟩ := kernelIncrementIsSlot hLaw hS F Q m V Y R B r Wt Z C₂ hA hm hK hZ hB0 hZ0 hκ hr hWt1 hWt le_rfl
  have hf : SizeData Q m Ψ B r Wt C₂ := ⟨hL, hx, hx1, hm, hρ, hmomΨ, hB0, hκ, hr, hWt1, hWt, by
    have : 0 ≤ B * Wt * Z := by positivity
    simp only [hC₂]
    nlinarith [mul_pos hB hW1]⟩
  set Cq : ℕ → ℝ := fun q => 1 + m q + Cz q with hCq
  have hCqp : ∀ q, 0 < Cq q := fun q => by
    have := hm q
    have := hCz q
    simp only [hCq]
    linarith
  have hCq1 : ∀ q, |1 + m q| ≤ Cq q := fun q => by
    have := hm q
    have := hCz q
    rw [abs_of_nonneg (by linarith)]
    simp only [hCq]
    linarith
  have hCq2 : ∀ q, |Cz q| ≤ Cq q := fun q => by
    have := hm q
    have := hCz q
    rw [abs_of_nonneg (by linarith)]
    simp only [hCq]
    linarith
  have hψA : ∀ ζ : StepVariable (finiteCells F), (∀ b, ‖ζ b‖ ≤ Q.ballRadius) → ContDiffAt ℝ 3 (fun η => Q.blockExponent Y η V) ζ :=
    fun ζ hζ => contDiffAt_top_of_joint (hsm 0 ![] ![] ζ hζ)
  have hRA : ∀ ζ : StepVariable (finiteCells F), (∀ b, ‖ζ b‖ ≤ Q.ballRadius) → ContDiffAt ℝ 4 (fun η => R η V) ζ :=
    fun ζ hζ => contDiffAt_top hK hζ
  have hsq : Real.sqrt Q.coupling * Q.coupling ^ (-(1 / 2) : ℝ) = 1 := by
    rw [rpow_neg_half hx]
    exact mul_inv_cancel₀ (Real.sqrt_pos.2 hx).ne'
  have hs1 : 1 ≤ Real.sqrt Q.coupling := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_le_sqrt hx1
  have hs0 : 0 < Real.sqrt Q.coupling := by linarith
  have hy0 : 0 < Q.coupling ^ (-(1 / 2) : ℝ) := Real.rpow_pos_of_pos hx _
  have hy1 : Q.coupling ^ (-(1 / 2) : ℝ) ≤ 1 := by
    rw [rpow_neg_half hx]
    exact inv_le_one_of_one_le₀ hs1
  have hmd : ∀ (k : ℕ) (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions), k ≤ 3 →
      ∀ η : StepVariable (finiteCells F), (∀ b, ‖η b‖ < Q.ballRadius) →
      topDeriv R V c X η - topDeriv R V c X 0 = bondDeriv (fun V' => R η V' - R 0 V') V c X := fun k c X hk η hη =>
    (bondDeriv_sub_eq hk (hK.smooth k c X η fun b => (hη b).le) (hK.smooth k c X 0 h00)).symm
  have hsumd : ∀ (k : ℕ) (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions), k ≤ 3 →
      ∀ η : StepVariable (finiteCells F), (∀ b, ‖η b‖ < Q.ballRadius) →
      bondDeriv (fun V' => Q.blockExponent Y η V' + R η V') V c X = topDeriv (Q.blockExponent Y) V c X η + topDeriv R V c X η :=
    fun k c X hk η hη => bondDeriv_add_eq hk (hsm k c X η fun b => (hη b).le)
      ((hK.smooth k c X η fun b => (hη b).le).of_le (by norm_num))
  refine ⟨⟨⟨fun η k c X hη => ?_, fun k c X hk hX => ?_⟩, fun η hη => ?_, ?_⟩, fun k c X hk1 hk3 hX => ?_⟩
  · have h1 := hsm k c X η hη
    have h2 : ContDiffAt ℝ 3 (fun q : (Fin k → ℝ) × StepVariable (finiteCells F) => R q.2 (leftTranslate (bondSpread c X q.1) V)) (0, η) :=
      (hK.smooth k c X η hη).of_le (by norm_num)
    exact_mod_cast h1.add h2
  · set e5 : ℝ := Real.exp (-(2 ^ 5 * Q.rate * bondSpan Y c)) with he5
    have he5p : 0 < e5 := Real.exp_pos _
    obtain ⟨hOn, -, -⟩ := topDeriv_moments hS hf hK (by omega : k ≤ 3) c X hX
    have s1 : HasLocalSize Q.ballRadius (cutoffFactor Q.ballRadius Q.cutoff) Ψ Cq Q.coupling Q.rate (Cs * e5) (fun b => cellSupDist (enclosingCell b.1.1) Y)
        (topDeriv (Q.blockExponent Y) V c X) :=
      hasLocalSize_mono hCq2 (by positivity) le_rfl (hasLocalSize_congr_density hd (hsz k c X (by omega) hX))
    have s2 : HasLocalSize Q.ballRadius (cutoffFactor Q.ballRadius Q.cutoff) Ψ Cq Q.coupling Q.rate (C₂ * Q.coupling ^ (-(1 / 2) : ℝ) * e5)
        (fun b => cellSupDist (enclosingCell b.1.1) Y) (fun η => topDeriv R V c X η - topDeriv R V c X 0) := by
      refine hasLocalSize_mono hCq1 (by positivity) le_rfl ?_
      exact hasLocalSize_congr_of_eqOn_balls (H := fun η => bondDeriv (fun V' => R η V' - R 0 V') V c X)
        (H' := fun η => topDeriv R V c X η - topDeriv R V c X 0) hO hz0 (fun η hη => (hmd k c X (by omega) η hη).symm)
        (hasLocalSize_congr_density hd (hM.smoothBounded.deriv_bound k c X hk hX))
    have c1 : ContDiffOn ℝ 1 (topDeriv (Q.blockExponent Y) V c X) {η | ∀ b, ‖η b‖ < Q.ballRadius} := fun η hη => by
      have h := hS.2.1 (Fin k → ℝ) (StepVariable (finiteCells F))
        (fun q => Q.blockExponent Y q.2 (leftTranslate (bondSpread c X q.1) V)) k 1 (fun l => Pi.single l 1) η
        (ContDiffAt.of_le (hsm k c X η fun b => (hη b).le) (by exact_mod_cast (by omega : 1 + k ≤ 3)))
      exact ContDiffAt.contDiffWithinAt h
    have c2 : ContDiffOn ℝ 1 (fun η => topDeriv R V c X η - topDeriv R V c X 0) {η | ∀ b, ‖η b‖ < Q.ballRadius} :=
      ContDiffOn.sub hOn contDiffOn_const
    have s3 := hasLocalSize_add hS2 hρ hA.isCutoff hΨc hx hCqp (by positivity) (by positivity) c1 c2 s1 s2
    have s4 := hasLocalSize_add_const (topDeriv R V c X 0) s3
    have hamp : Cs * e5 + C₂ * Q.coupling ^ (-(1 / 2) : ℝ) * e5 ≤ C * e5 := by
      have h6 : Cs ≤ C₃ := by
        simp only [hC₃]
        nlinarith [mul_nonneg hCs.le hW0, mul_nonneg (mul_nonneg hCs.le (by linarith : (0 : ℝ) ≤ 3 + W)) hZ0]
      have h7 : C₂ * Q.coupling ^ (-(1 / 2) : ℝ) ≤ C₂ := mul_le_of_le_one_right hC₂p.le hy1
      have h8 : Cs + C₂ * Q.coupling ^ (-(1 / 2) : ℝ) ≤ C := by linarith
      calc _ = (Cs + C₂ * Q.coupling ^ (-(1 / 2) : ℝ)) * e5 := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_right h8 he5p.le
    have s5 := hasLocalSize_mono (Cq' := Cq) (fun q => le_of_eq (abs_of_pos (hCqp q))) (by positivity) hamp s4
    refine hasLocalSize_congr_density hd.symm (hasLocalSize_congr_of_eqOn_balls hO hz0 (fun η hη => ?_) s5)
    rw [hsumd k c X (by omega) η hη]
    ring
  · have h1 := (hψA η fun b => (hη b).le).of_le (show (2 : WithTop ℕ∞) ≤ 3 by norm_num)
    have h2 := (hRA η fun b => (hη b).le).of_le (show (2 : WithTop ℕ∞) ≤ 4 by norm_num)
    exact h1.add h2
  · intro Th hTh c X b hX
    set z : BondVector → BondVector := fun v => _root_.YangMills.Construction.Interpolation.imaginaryCoords (topVariationField Th 1 Q.a Q.chartRadius Q.mirrorRadius c X b.1 (toImaginary v) V) with hzdef
    set dc : ℝ := bondDistToTopBond b c with hdc
    have hdc0 : 0 ≤ dc := Nat.cast_nonneg _
    have hzb : ∀ v : BondVector, ‖v‖ < Q.ballRadius → ContDiffAt ℝ 1 z v ∧ ‖z v‖ ≤ Z * Real.exp (-(2 ^ 8 * Q.rate * dc)) ∧
        ‖fderiv ℝ z v‖ ≤ Z * Real.exp (-(2 ^ 8 * Q.rate * dc)) := fun v hv => hZ Th hTh c X b v hX hv
    have hC₃' : Z * Cs * (3 + W) ≤ C₃ := by
      simp only [hC₃]
      nlinarith [mul_nonneg hCs.le (by linarith : (0 : ℝ) ≤ 3 + W)]
    obtain ⟨cψ, sψ⟩ := blockExponent_along_size hL hm hρ hx1 hκ hmomΨ hCs hZ0 hC₃' hsym (hW Y) hE hψA b hdc0 hzb
    set e1 : ℝ := Real.exp (-(2 ^ 4 * Q.rate * bondDistToCell Y b) - 2 ^ 6 * Q.rate * dc) with he1
    have he1p : 0 < e1 := Real.exp_pos _
    have hZd0 : 0 ≤ Z * Real.exp (-(2 ^ 8 * Q.rate * dc)) := mul_nonneg hZ0 (Real.exp_pos _).le
    have cM := (bondPartial_along_bounds hS hK hB0 b hZd0 hzb).1
    have sM := hM.decaysAlongTopField Th hTh c X b hX
    have hφM : topFieldPartial Th 1 Q.a Q.chartRadius Q.mirrorRadius c X V b (fun η => (fun η V' => R η V' - R 0 V') η V) =
        fun ζ => bondPartialDeriv (fun η => R η V) b ζ (z (ζ b)) := by
      funext ζ
      unfold topFieldPartial bondPartialDeriv
      simp only [hzdef]
      rw [fderiv_sub_const]
    rw [hφM] at sM
    have s1 : HasLocalSize Q.ballRadius (cutoffFactor Q.ballRadius Q.cutoff) Ψ Cq Q.coupling Q.rate (Real.sqrt Q.coupling * C₃ * e1) (bondDistToCell Y)
        (fun ζ => bondPartialDeriv (fun η => Q.blockExponent Y η V) b ζ (z (ζ b))) :=
      hasLocalSize_mono hCq1 (by positivity) le_rfl sψ
    have s2 : HasLocalSize Q.ballRadius (cutoffFactor Q.ballRadius Q.cutoff) Ψ Cq Q.coupling Q.rate (Real.sqrt Q.coupling * (C₂ * Q.coupling ^ (-(1 / 2) : ℝ)) * e1) (bondDistToCell Y)
        (fun ζ => bondPartialDeriv (fun η => R η V) b ζ (z (ζ b))) :=
      hasLocalSize_mono hCq1 (by positivity) le_rfl (hasLocalSize_congr_density hd sM)
    have s3 := hasLocalSize_add hS2 hρ hA.isCutoff hΨc hx hCqp (by positivity) (by positivity) cψ cM s1 s2
    have hamp : Real.sqrt Q.coupling * C₃ * e1 + Real.sqrt Q.coupling * (C₂ * Q.coupling ^ (-(1 / 2) : ℝ)) * e1 ≤ Real.sqrt Q.coupling * C * e1 := by
      have h7 : C₂ * Q.coupling ^ (-(1 / 2) : ℝ) ≤ C₂ := mul_le_of_le_one_right hC₂p.le hy1
      have h8 : C₃ + C₂ * Q.coupling ^ (-(1 / 2) : ℝ) ≤ C := by linarith
      calc _ = Real.sqrt Q.coupling * (C₃ + C₂ * Q.coupling ^ (-(1 / 2) : ℝ)) * e1 := by ring
        _ ≤ _ := by gcongr
    have s5 := hasLocalSize_mono (Cq' := Cq) (fun q => le_of_eq (abs_of_pos (hCqp q))) (by positivity) hamp s3
    refine hasLocalSize_congr_density hd.symm (hasLocalSize_congr_of_eqOn_balls hO hz0 (fun ζ hζ => ?_) s5)
    unfold topFieldPartial bondPartialDeriv
    have d1 : DifferentiableAt ℝ (fun η => Q.blockExponent Y η V) ζ :=
      (hψA ζ fun b => (hζ b).le).differentiableAt (by norm_num)
    have d2 : DifferentiableAt ℝ (fun η => R η V) ζ := (hRA ζ fun b => (hζ b).le).differentiableAt (by norm_num)
    rw [fderiv_fun_add d1 d2]
    simp only [hzdef, ContinuousLinearMap.add_apply]
  · set e5 : ℝ := Real.exp (-(2 ^ 5 * Q.rate * bondSpan Y c)) with he5
    have he5p : 0 < e5 := Real.exp_pos _
    set e6 : ℝ := Real.exp (-(2 ^ 6 * Q.rate * bondSpan Y c)) with he6
    have he6p : 0 < e6 := Real.exp_pos _
    have he65 : e6 ≤ e5 := by
      rw [he5, he6, Real.exp_le_exp]
      have hsp0 : (0 : ℝ) ≤ bondSpan Y c := Nat.cast_nonneg _
      nlinarith [mul_nonneg hκ.le hsp0]
    obtain ⟨hOn, hmom, -⟩ := topDeriv_moments hS hf hK hk3 c X hX
    let w : ↥(chordBonds (finiteCells F)) → ℝ := fun b => Real.exp (-(2 ^ 6 * Q.rate * bondDistToCell Y b))
    have hw0 : ∀ b, 0 ≤ w b := fun b => (Real.exp_pos _).le
    have cont1 : ContinuousOn (topDeriv (Q.blockExponent Y) V c X) (bondBall _ Q.ballRadius) := fun η hη => by
      have h := hS.2.1 (Fin k → ℝ) (StepVariable (finiteCells F))
        (fun q => Q.blockExponent Y q.2 (leftTranslate (bondSpread c X q.1) V)) k 0 (fun l => Pi.single l 1) η
        (ContDiffAt.of_le (hsm k c X η fun b => (hη b).le) (by exact_mod_cast (by omega : 0 + k ≤ 3)))
      exact h.continuousAt.continuousWithinAt
    have m1 := momentBound_of_quadratic hL hx hm hρ hmomΨ cont1 (E := 1) (β := Cs * e6) (w := w) zero_le_one (by positivity) hw0
      (fun η hη => by
        have h1 := hE.deriv_top Y η k c X hη hk3 hX
        have ht : ∑ b, w b * (Q.coupling * ‖η b‖ ^ 2) = Q.coupling * localSqNorm Q.rate Y η := by
          simp only [localSqNorm, Finset.mul_sum]
          refine Finset.sum_congr rfl fun b _ => ?_
          simp only [w, bondDistToCell]
          ring
        rw [ht]
        calc _ ≤ _ := h1
          _ = _ := by simp only [he6]; ring) 1 le_rfl
    have m2 := hmom 1 le_rfl
    have m3 := momentBound_of_bounded hL hx hm hρ hmomΨ (f := fun _ => topDeriv R V c X 0) continuousOn_const
      (M := B * e5) (by positivity) (fun _ _ => hR0 k c X hk1 hk3 hX) 1 le_rfl
    have m4 := momentBound_one_add hL (cont1.add (hOn.continuousOn.sub continuousOn_const)) continuousOn_const
      (momentBound_one_add hL cont1 (hOn.continuousOn.sub continuousOn_const) m1 m2) m3
    have m5 := momentBound_congr (f' := fun η => bondDeriv (fun V' => Q.blockExponent Y η V' + R η V') V c X) hz0
      (fun η hη => by
        rw [hsumd k c X hk3 η hη]
        show topDeriv (Q.blockExponent Y) V c X η + (topDeriv R V c X η - topDeriv R V c X 0) + topDeriv R V c X 0 = _
        ring) m4
    have m6 := abs_ballExpectation_le_of_momentBound hL m5
    unfold ColdHalfLaw.expectation
    change |ballExpectation (cutoffFactor Q.ballRadius Q.cutoff) (Q.exponent V) _| ≤ _
    rw [hmean_eq]
    refine m6.trans ?_
    have hm1 : 0 ≤ 1 + m 1 := by linarith [hm 1]
    have hSw : ∑ b, w b ≤ W := hW Y
    have hSw0 : 0 ≤ ∑ b, w b := Finset.sum_nonneg fun b _ => hw0 b
    have b1 : Cs * e6 * (1 + ∑ b, w b) ≤ C₃ * e5 := by
      have h6 : Cs * (1 + ∑ b, w b) ≤ C₃ := by
        simp only [hC₃]
        nlinarith [mul_nonneg hCs.le (by linarith : (0 : ℝ) ≤ 3 + W), mul_nonneg (mul_nonneg hCs.le (by linarith : (0 : ℝ) ≤ 3 + W)) hZ0]
      calc _ = (Cs * (1 + ∑ b, w b)) * e6 := by ring
        _ ≤ C₃ * e5 := mul_le_mul h6 he65 he6p.le hC₃p.le
    have b2 : C₂ * Q.coupling ^ (-(1 / 2) : ℝ) * e5 ≤ C₂ * e5 :=
      mul_le_mul_of_nonneg_right (mul_le_of_le_one_right hC₂p.le hy1) he5p.le
    have b3 : C₃ * e5 + C₂ * e5 + B * e5 ≤ C * e5 := by
      have : C₃ + C₂ + B ≤ C := by linarith
      calc _ = (C₃ + C₂ + B) * e5 := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_right this he5p.le
    calc (1 + m 1) * (Cs * e6) * (1 + ∑ b, w b) + (1 + m 1) * (C₂ * Q.coupling ^ (-(1 / 2) : ℝ) * e5) + (1 + m 1) * (B * e5)
        = (1 + m 1) * (Cs * e6 * (1 + ∑ b, w b) + C₂ * Q.coupling ^ (-(1 / 2) : ℝ) * e5 + B * e5) := by ring
      _ ≤ (1 + m 1) * (C * e5) := by
        refine mul_le_mul_of_nonneg_left ?_ hm1
        linarith
      _ = _ := by ring
end BlockExponentSlot
end KernelSlots
open KernelSlots in
theorem slotsFromKernels_proof (hLaw : normalizedBallLawIsProbabilityStatement) (hS : IteratedFDerivSlices)
    (hS2 : FiniteSumSizeBound) : slotsFromKernelsStatement :=
  ⟨kernelIncrementIsSlot hLaw hS, blockExponentAddKernelIsSlot hLaw hS hS2⟩
end WeightedResponses
end YangMills.Construction
end
