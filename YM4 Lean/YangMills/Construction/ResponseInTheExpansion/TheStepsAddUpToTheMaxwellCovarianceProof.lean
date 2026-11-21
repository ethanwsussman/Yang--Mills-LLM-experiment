import YangMills.Construction.ClusterExpansionOfAStep.TopFieldOffTheHull
import YangMills.Construction.ClusterExpansionOfAStep.TreesOfABlock
import YangMills.Construction.ColdStepAtMirrorFrames.BlockEnergyOnTwoToriProof
import YangMills.Construction.ResponseInTheExpansion.GradientsUnderTheMaxwellForm
import YangMills.Construction.ResponseInTheExpansion.OneStepOfTheMaxwellForm
import YangMills.Construction.ResponseInTheExpansion.RowSumsOfTheFunctionals
import YangMills.Construction.ResponseInTheExpansion.TheHessianOfAStepIsDefinite
import YangMills.Construction.ResponseInTheExpansion.TheStepsAddUpToTheMaxwellCovariance
import YangMills.Construction.SystemOfAdmissibleConstants.TheLawAtALevelProof
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ResponseInTheExpansion
open WeightedResponses TorusFields
section Abstract
variable {ι : Type*} [Fintype ι]
private def kernelPair (M : ι → ι → ℝ) (A B : ι → ℝ) : ℝ := ∑ b, ∑ b', A b * M b b' * B b'
private def symmPart (M : ι → ι → ℝ) : Matrix ι ι ℝ := fun b b' => (M b b' + M b' b) / 2
private theorem kernelPair_add_left (M : ι → ι → ℝ) (A A' B : ι → ℝ) :
    kernelPair M (A + A') B = kernelPair M A B + kernelPair M A' B := by
  simp only [kernelPair, Pi.add_apply, add_mul, Finset.sum_add_distrib]
private theorem kernelPair_add_right (M : ι → ι → ℝ) (A B B' : ι → ℝ) :
    kernelPair M A (B + B') = kernelPair M A B + kernelPair M A B' := by
  simp only [kernelPair, Pi.add_apply, mul_add, Finset.sum_add_distrib]
private theorem kernelPair_smul_left (M : ι → ι → ℝ) (t : ℝ) (A B : ι → ℝ) :
    kernelPair M (t • A) B = t * kernelPair M A B := by
  simp only [kernelPair, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun b' _ => by ring
private theorem kernelPair_smul_right (M : ι → ι → ℝ) (t : ℝ) (A B : ι → ℝ) :
    kernelPair M A (t • B) = t * kernelPair M A B := by
  simp only [kernelPair, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun b' _ => by ring
private theorem dotProduct_symmPart_mulVec_self (M : ι → ι → ℝ) (A : ι → ℝ) :
    A ⬝ᵥ (symmPart M).mulVec A = kernelPair M A A := by
  have h : kernelPair M A A = ∑ b, ∑ b', A b * M b' b * A b' := by
    unfold kernelPair
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun b' _ => by ring
  have h2 : A ⬝ᵥ (symmPart M).mulVec A = (kernelPair M A A + ∑ b, ∑ b', A b * M b' b * A b') / 2 := by
    simp only [dotProduct, Matrix.mulVec, symmPart, kernelPair, Finset.mul_sum, ← Finset.sum_add_distrib,
      Finset.sum_div]
    exact Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun b' _ => by ring
  rw [h2, ← h]
  ring
private theorem symmPart_dotProduct_comm (M : ι → ι → ℝ) (u v : ι → ℝ) :
    u ⬝ᵥ (symmPart M).mulVec v = v ⬝ᵥ (symmPart M).mulVec u := by
  have ht : (symmPart M).transpose = symmPart M := by
    ext b b'
    simp only [Matrix.transpose_apply, symmPart]
    ring
  rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, ht, dotProduct_comm]
private theorem exists_symmPart_mulVec_eq (M : ι → ι → ℝ) (g : ι → ℝ)
    (hg : ∀ A, kernelPair M A A = 0 → g ⬝ᵥ A = 0) :
    ∃ x, (symmPart M).mulVec x = g := by
  classical
  by_contra hne
  have hv : g ∉ LinearMap.range (symmPart M).mulVecLin := by
    rintro ⟨x, hx⟩
    exact hne ⟨x, by simpa using hx⟩
  obtain ⟨f, hfg, hpf⟩ := Submodule.exists_le_ker_of_notMem hv
  set z : ι → ℝ := fun i => f (Pi.single i 1) with hz
  have hf : ∀ v : ι → ℝ, f v = z ⬝ᵥ v := by
    intro v
    have : v = ∑ i, v i • (Pi.single i (1 : ℝ) : ι → ℝ) := by
      funext j
      simp [Finset.sum_apply, Pi.single_apply]
    conv_lhs => rw [this]
    simp only [map_sum, map_smul, dotProduct, hz, smul_eq_mul]
    exact Finset.sum_congr rfl fun i _ => by ring
  have h0 : z ⬝ᵥ (symmPart M).mulVec z = 0 := by
    rw [← hf]
    exact hpf ⟨z, rfl⟩
  rw [dotProduct_symmPart_mulVec_self] at h0
  have h1 := hg z h0
  apply hfg
  rw [hf, dotProduct_comm, h1]
private theorem gap_eq_sub_kernelPair (M : ι → ι → ℝ) {x g : ι → ℝ} (hx : (symmPart M).mulVec x = g)
    (A : ι → ℝ) :
    2 * (g ⬝ᵥ A) - kernelPair M A A = g ⬝ᵥ x - kernelPair M (A - x) (A - x) := by
  rw [← dotProduct_symmPart_mulVec_self, ← dotProduct_symmPart_mulVec_self]
  have e1 : (A - x) ⬝ᵥ (symmPart M).mulVec (A - x) =
      A ⬝ᵥ (symmPart M).mulVec A - A ⬝ᵥ (symmPart M).mulVec x - x ⬝ᵥ (symmPart M).mulVec A +
        x ⬝ᵥ (symmPart M).mulVec x := by
    rw [Matrix.mulVec_sub, sub_dotProduct, dotProduct_sub, dotProduct_sub]
    ring
  rw [e1, symmPart_dotProduct_comm M x A, hx, dotProduct_comm A g, dotProduct_comm x g]
  ring
private theorem isLUB_gap_symmPart (M : ι → ι → ℝ) (hpos : ∀ A, 0 ≤ kernelPair M A A) {x g : ι → ℝ}
    (hx : (symmPart M).mulVec x = g) :
    IsLUB (Set.range fun A => 2 * (g ⬝ᵥ A) - kernelPair M A A) (g ⬝ᵥ x) := by
  constructor
  · rintro _ ⟨A, rfl⟩
    have := gap_eq_sub_kernelPair M hx A
    have h2 := hpos (A - x)
    simp only
    linarith
  · intro b hb
    have h := hb ⟨x, rfl⟩
    have := gap_eq_sub_kernelPair M hx x
    simp only [sub_self] at this
    have h0 : kernelPair M (0 : ι → ℝ) 0 = 0 := by simp [kernelPair]
    rw [h0] at this
    simp only at h
    linarith
private theorem kernelPair_right_eq_zero (M : ι → ι → ℝ) (hpos : ∀ A, 0 ≤ kernelPair M A A) (D : ι → ℝ)
    (hD : ∀ A, kernelPair M D A = 0) (W : ι → ℝ) : kernelPair M W D = 0 := by
  by_contra hne
  set c := kernelPair M W D with hc
  have h := hpos (W + (-(kernelPair M W W + 1) / c) • D)
  rw [kernelPair_add_left, kernelPair_add_right, kernelPair_add_right, kernelPair_smul_left, hD,
    kernelPair_smul_right, ← hc, kernelPair_smul_right, kernelPair_smul_left, hD] at h
  have e : -(kernelPair M W W + 1) / c * c = -(kernelPair M W W + 1) := div_mul_cancel₀ _ hne
  nlinarith
variable {c : Type*} [Fintype c] [DecidableEq c]
private theorem mulVec_inv_mulVec_of_posDef {H : Matrix c c ℝ} (hH : H.PosDef) (l : c → ℝ) :
    H.mulVec (H⁻¹.mulVec l) = l := by
  have hu : IsUnit H.det := (Matrix.isUnit_iff_isUnit_det H).1 hH.isUnit
  rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv H hu, Matrix.one_mulVec]
omit [DecidableEq c] in
private theorem dotProduct_mulVec_comm_of_posDef {H : Matrix c c ℝ} (hH : H.PosDef) (u v : c → ℝ) :
    u ⬝ᵥ H.mulVec v = v ⬝ᵥ H.mulVec u := by
  have ht : H.transpose = H := by
    have := hH.isHermitian
    rwa [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial] at this
  rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, ht, dotProduct_comm]
private theorem dotProduct_inv_mulVec_comm_of_posDef {H : Matrix c c ℝ} (hH : H.PosDef) (u v : c → ℝ) :
    u ⬝ᵥ H⁻¹.mulVec v = v ⬝ᵥ H⁻¹.mulVec u := by
  have e1 := mulVec_inv_mulVec_of_posDef hH u
  have e2 := mulVec_inv_mulVec_of_posDef hH v
  calc u ⬝ᵥ H⁻¹.mulVec v = H.mulVec (H⁻¹.mulVec u) ⬝ᵥ H⁻¹.mulVec v := by rw [e1]
    _ = H⁻¹.mulVec v ⬝ᵥ H.mulVec (H⁻¹.mulVec u) := dotProduct_comm _ _
    _ = H⁻¹.mulVec u ⬝ᵥ H.mulVec (H⁻¹.mulVec v) := dotProduct_mulVec_comm_of_posDef hH _ _
    _ = v ⬝ᵥ H⁻¹.mulVec u := by rw [e2, dotProduct_comm]
private theorem gap_le_inv_of_posDef {H : Matrix c c ℝ} (hH : H.PosDef) (l v : c → ℝ) :
    2 * (l ⬝ᵥ v) - v ⬝ᵥ H.mulVec v ≤ l ⬝ᵥ H⁻¹.mulVec l := by
  set x := H⁻¹.mulVec l with hx
  have hHx : H.mulVec x = l := mulVec_inv_mulVec_of_posDef hH l
  have h0 : 0 ≤ (v - x) ⬝ᵥ H.mulVec (v - x) := by
    by_cases h : v - x = 0
    · rw [h]; simp
    · exact (hH.dotProduct_mulVec_pos h).le
  have e1 : (v - x) ⬝ᵥ H.mulVec (v - x) =
      v ⬝ᵥ H.mulVec v - v ⬝ᵥ H.mulVec x - x ⬝ᵥ H.mulVec v + x ⬝ᵥ H.mulVec x := by
    rw [Matrix.mulVec_sub, sub_dotProduct, dotProduct_sub, dotProduct_sub]
    ring
  rw [e1, dotProduct_mulVec_comm_of_posDef hH x v, hHx, dotProduct_comm v l, dotProduct_comm x l] at h0
  linarith
private theorem gap_inv_eq_of_posDef {H : Matrix c c ℝ} (hH : H.PosDef) (l : c → ℝ) :
    2 * (l ⬝ᵥ H⁻¹.mulVec l) - H⁻¹.mulVec l ⬝ᵥ H.mulVec (H⁻¹.mulVec l) = l ⬝ᵥ H⁻¹.mulVec l := by
  rw [mulVec_inv_mulVec_of_posDef hH l, dotProduct_comm (H⁻¹.mulVec l) l]
  ring
end Abstract
section Step
variable {m : ℕ} [NeZero m]
private def gapAt (a : ℝ) (L u : ℕ) (g A : TorusBond m → ℝ) : ℝ := 2 * (g ⬝ᵥ A) - maxwellForm a L u A A
omit [NeZero m] in
private theorem curl_latticeGradient (φ : TorusSite m → ℝ) (p : TorusPlaquette m) :
    curl (latticeGradient φ) p = 0 := by
  unfold curl latticeGradient
  have : p.1 + TorusFields.unitStep m p.2.2 + TorusFields.unitStep m p.2.1 =
      p.1 + TorusFields.unitStep m p.2.1 + TorusFields.unitStep m p.2.2 := add_right_comm _ _ _
  simp only [this]
  ring
abbrev _root_.YangMills.DeltaSharedProofs.p500719 := @curl_latticeGradient
private theorem curlFunctional_dotProduct (p : TorusPlaquette m) (A : TorusBond m → ℝ) :
    curlFunctional p ⬝ᵥ A = curl A p := by
  classical
  unfold curlFunctional curl dotProduct
  simp [add_mul, sub_mul, Finset.sum_add_distrib, Finset.sum_sub_distrib]
private theorem curlFunctional_dotProduct_latticeGradient (p : TorusPlaquette m) (φ : TorusSite m → ℝ) :
    curlFunctional p ⬝ᵥ latticeGradient φ = 0 := by
  rw [curlFunctional_dotProduct, curl_latticeGradient]
end Step
section Response
variable (a ρA : ℝ) (L u : ℕ) {n : ℕ} [NeZero n] [NeZero L]
private theorem responseAdjoint_dotProduct (g : TorusBond (n * L) → ℝ) (B : TorusBond n → ℝ) :
    responseAdjoint a ρA L u g ⬝ᵥ B = g ⬝ᵥ responseMap a ρA L u B := by
  simp only [dotProduct, responseAdjoint, responseMap, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun b _ => by ring
private theorem responseAdjoint_add (h h' : TorusBond (n * L) → ℝ) :
    responseAdjoint a ρA L u (h + h') = responseAdjoint a ρA L u h + responseAdjoint a ρA L u h' := by
  funext c
  simp only [responseAdjoint, Pi.add_apply, add_mul, Finset.sum_add_distrib]
private theorem chartRestriction_add (h h' : TorusBond (n * L) → ℝ) :
    chartRestriction L u n (h + h') = chartRestriction L u n h + chartRestriction L u n h' := by
  funext b
  simp only [chartRestriction, Pi.add_apply]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun c _ => ?_
  split_ifs <;> simp
private theorem stepCovariance_def (h h' : TorusBond (n * L) → ℝ) :
    stepCovariance a L u n h h' =
      chartRestriction L u n h ⬝ᵥ (trivialHessian a L u n)⁻¹.mulVec (chartRestriction L u n h') := rfl
private theorem stepCovariance_add_self (hH : (trivialHessian a L u n).PosDef) (h h' : TorusBond (n * L) → ℝ) :
    stepCovariance a L u n (h + h') (h + h') =
      stepCovariance a L u n h h + stepCovariance a L u n h' h' + 2 * stepCovariance a L u n h h' := by
  simp only [stepCovariance_def, chartRestriction_add, Matrix.mulVec_add, add_dotProduct, dotProduct_add]
  rw [dotProduct_inv_mulVec_comm_of_posDef hH (chartRestriction L u n h') (chartRestriction L u n h)]
  ring
end Response
section Transport
variable {a ρA : ℝ} {L : ℕ} [NeZero L]
private theorem adjointTransport_add (k : ℕ) (d : ℕ) :
    ∀ (n : ℕ) [NeZero n] (h h' : TorusBond (fineSide L d n) → ℝ),
      adjointTransport a ρA L k d n (h + h') =
        adjointTransport a ρA L k d n h + adjointTransport a ρA L k d n h' := by
  induction d with
  | zero => intro n _ h h'; rfl
  | succ d ih =>
    intro n _
    exact show ∀ h h' : TorusBond (fineSide L d (n * L)) → ℝ,
        responseAdjoint a ρA L (k + d) (adjointTransport a ρA L k d (n * L) (h + h')) =
          responseAdjoint a ρA L (k + d) (adjointTransport a ρA L k d (n * L) h) +
            responseAdjoint a ρA L (k + d) (adjointTransport a ρA L k d (n * L) h') from by
      intro h h'
      rw [ih (n * L) h h', responseAdjoint_add]
omit [NeZero L] in
private theorem le_mul_side {n₀ n : ℕ} (hL : 0 < L) (hn : n₀ ≤ n) : n₀ ≤ n * L :=
  hn.trans (Nat.le_mul_of_pos_right n hL)
private theorem accumulatedCovariance_add_self {n₀ : ℕ} (hL : 0 < L)
    (hH : ∀ (u n : ℕ) [NeZero n], n₀ ≤ n → (trivialHessian a L u n).PosDef) (k : ℕ) (d : ℕ) :
    ∀ (n : ℕ) [NeZero n], n₀ ≤ n → ∀ h h' : TorusBond (fineSide L d n) → ℝ,
      accumulatedCovariance a ρA L k d n (h + h') (h + h') =
        accumulatedCovariance a ρA L k d n h h + accumulatedCovariance a ρA L k d n h' h' +
          2 * accumulatedCovariance a ρA L k d n h h' := by
  induction d with
  | zero => intro n _ _ h h'; simp [accumulatedCovariance]
  | succ d ih =>
    intro n _ hn
    exact show ∀ h h' : TorusBond (fineSide L d (n * L)) → ℝ,
        accumulatedCovariance a ρA L k d (n * L) (h + h') (h + h') +
            stepCovariance a L (k + d) n (adjointTransport a ρA L k d (n * L) (h + h'))
              (adjointTransport a ρA L k d (n * L) (h + h')) =
          (accumulatedCovariance a ρA L k d (n * L) h h +
              stepCovariance a L (k + d) n (adjointTransport a ρA L k d (n * L) h)
                (adjointTransport a ρA L k d (n * L) h)) +
            (accumulatedCovariance a ρA L k d (n * L) h' h' +
              stepCovariance a L (k + d) n (adjointTransport a ρA L k d (n * L) h')
                (adjointTransport a ρA L k d (n * L) h')) +
            2 * (accumulatedCovariance a ρA L k d (n * L) h h' +
              stepCovariance a L (k + d) n (adjointTransport a ρA L k d (n * L) h)
                (adjointTransport a ρA L k d (n * L) h')) from by
      intro h h'
      rw [ih (n * L) (le_mul_side hL hn) h h', adjointTransport_add,
        stepCovariance_add_self a L (k + d) (hH (k + d) n hn)]
      ring
end Transport
section StepHypothesesSection
private structure StepHypotheses (a ρA : ℝ) (L u n : ℕ) [NeZero L] [NeZero n] : Prop where
  a_nonneg : 0 ≤ a
  one_step : ∀ (W : TorusBond (n * L) → ℝ) (B : TorusBond n → ℝ), (∀ b, b ∉ StepCosts.chartBonds L n → W b = 0) →
    maxwellForm a L u W W + a * ∑ c : TorusBond n, (contourMeanSlope L n W c - B c) ^ 2 =
      maxwellForm a L (u + 1) B B + stepHessianForm a L u n (W - responseMap a ρA L u B)
  definite : (trivialHessian a L u n).PosDef
  off_trees : ∀ (B : TorusBond n → ℝ) (b : TorusBond (n * L)), b ∉ StepCosts.chartBonds L n →
    responseMap a ρA L u B b = 0
  gauge : ∀ A : TorusBond (n * L) → ℝ, ∃ φ : TorusSite (n * L) → ℝ,
    ∀ b, b ∉ StepCosts.chartBonds L n → A b = latticeGradient φ b
  form_pos : ∀ A : TorusBond (n * L) → ℝ, 0 ≤ maxwellForm a L u A A
  kills : ∀ (φ : TorusSite (n * L) → ℝ) (A : TorusBond (n * L) → ℝ), maxwellForm a L u (latticeGradient φ) A = 0
  pairing : ∀ g W : TorusBond (n * L) → ℝ, (∀ b, b ∉ StepCosts.chartBonds L n → W b = 0) →
    g ⬝ᵥ W = chartRestriction L u n g ⬝ᵥ chartRestriction L u n W
  extend : ∀ v : ↥(BlockAverages.chordBonds (ColdStepAtMirrorFrames.finiteCells (torusFrame L u n))) → ℝ,
    ∃ W : TorusBond (n * L) → ℝ, (∀ b, b ∉ StepCosts.chartBonds L n → W b = 0) ∧ chartRestriction L u n W = v
variable {a ρA : ℝ} {L u n : ℕ} [NeZero L] [NeZero n]
private theorem isLUB_gapAt_step (S : StepHypotheses a ρA L u n) (g : TorusBond (n * L) → ℝ)
    (hg : ∀ φ, g ⬝ᵥ latticeGradient φ = 0) {s : ℝ}
    (hs : IsLUB (Set.range (gapAt a L (u + 1) (responseAdjoint a ρA L u g))) s) :
    IsLUB (Set.range (gapAt a L u g)) (stepCovariance a L u n g g + s) := by
  have hH := S.definite
  rw [stepCovariance_def]
  have key : ∀ (W : TorusBond (n * L) → ℝ) (B : TorusBond n → ℝ), (∀ b, b ∉ StepCosts.chartBonds L n → W b = 0) →
      gapAt a L u g W - a * ∑ c : TorusBond n, (contourMeanSlope L n W c - B c) ^ 2 =
        gapAt a L (u + 1) (responseAdjoint a ρA L u g) B +
          (2 * (chartRestriction L u n g ⬝ᵥ chartRestriction L u n (W - responseMap a ρA L u B)) -
            chartRestriction L u n (W - responseMap a ρA L u B) ⬝ᵥ
              (trivialHessian a L u n).mulVec (chartRestriction L u n (W - responseMap a ρA L u B))) := by
    intro W B hW
    have h1 := S.one_step W B hW
    have hρ : ∀ b, b ∉ StepCosts.chartBonds L n → (W - responseMap a ρA L u B) b = 0 := fun b hb => by
      simp [hW b hb, S.off_trees B b hb]
    have h2 := S.pairing g _ hρ
    have h3 : g ⬝ᵥ W = g ⬝ᵥ responseMap a ρA L u B + g ⬝ᵥ (W - responseMap a ρA L u B) := by
      rw [dotProduct_sub]
      ring
    have h4 := responseAdjoint_dotProduct a ρA L u g B
    unfold stepHessianForm at h1
    unfold gapAt
    rw [h3, ← h4, h2]
    linarith
  constructor
  · rintro _ ⟨A, rfl⟩
    obtain ⟨φ, hφ⟩ := S.gauge A
    have hW : ∀ b, b ∉ StepCosts.chartBonds L n → (A - latticeGradient φ) b = 0 := fun b hb => by
      simp [hφ b hb]
    have hA : A = (A - latticeGradient φ) + latticeGradient φ := by simp
    have hgap : gapAt a L u g A = gapAt a L u g (A - latticeGradient φ) := by
      have hq : maxwellForm a L u A A = maxwellForm a L u (A - latticeGradient φ) (A - latticeGradient φ) := by
        have hpos : ∀ A' : TorusBond (n * L) → ℝ, 0 ≤ kernelPair (maxwellKernel a L u) A' A' := S.form_pos
        have hz := kernelPair_right_eq_zero (maxwellKernel a L u) hpos (latticeGradient φ) (S.kills φ)
          (A - latticeGradient φ)
        have hk : ∀ A', kernelPair (maxwellKernel a L u) (latticeGradient φ) A' = 0 := S.kills φ
        show kernelPair (maxwellKernel a L u) A A =
          kernelPair (maxwellKernel a L u) (A - latticeGradient φ) (A - latticeGradient φ)
        conv_lhs => rw [hA]
        rw [kernelPair_add_left, kernelPair_add_right, kernelPair_add_right, hz, hk, hk]
        ring
      unfold gapAt
      rw [hq, dotProduct_sub, hg φ]
      ring
    have h := key (A - latticeGradient φ) (contourMeanSlope L n (A - latticeGradient φ)) hW
    have h0 : ∑ c : TorusBond n, (contourMeanSlope L n (A - latticeGradient φ) c -
        contourMeanSlope L n (A - latticeGradient φ) c) ^ 2 = 0 := by
      simp
    rw [h0, mul_zero, sub_zero] at h
    have h1 : gapAt a L (u + 1) (responseAdjoint a ρA L u g) (contourMeanSlope L n (A - latticeGradient φ)) ≤ s :=
      hs.1 ⟨_, rfl⟩
    have h2 := gap_le_inv_of_posDef hH (chartRestriction L u n g)
      (chartRestriction L u n ((A - latticeGradient φ) -
        responseMap a ρA L u (contourMeanSlope L n (A - latticeGradient φ))))
    show gapAt a L u g A ≤ _
    rw [hgap, h]
    linarith
  · intro b hb
    have hs2 : s ≤ b - chartRestriction L u n g ⬝ᵥ (trivialHessian a L u n)⁻¹.mulVec (chartRestriction L u n g) := by
      apply hs.2
      rintro _ ⟨B, rfl⟩
      obtain ⟨W₀, hW₀, hv⟩ := S.extend ((trivialHessian a L u n)⁻¹.mulVec (chartRestriction L u n g))
      have hW : ∀ c, c ∉ StepCosts.chartBonds L n → (responseMap a ρA L u B + W₀) c = 0 := fun c hc => by
        simp [hW₀ c hc, S.off_trees B c hc]
      have h := key _ B hW
      have e : responseMap a ρA L u B + W₀ - responseMap a ρA L u B = W₀ := by simp
      rw [e, hv, gap_inv_eq_of_posDef hH] at h
      have h1 : gapAt a L u g (responseMap a ρA L u B + W₀) ≤ b := hb ⟨_, rfl⟩
      have h2 : 0 ≤ a * ∑ c : TorusBond n, (contourMeanSlope L n (responseMap a ρA L u B + W₀) c - B c) ^ 2 :=
        mul_nonneg S.a_nonneg (Finset.sum_nonneg fun _ _ => sq_nonneg _)
      show gapAt a L (u + 1) (responseAdjoint a ρA L u g) B ≤ _
      linarith
    linarith
end StepHypothesesSection
section Chain
variable {a ρA : ℝ} {L n₀ : ℕ} [NeZero L]
private theorem adjointTransport_kills_gradients (hL : 0 < L)
    (hG : ∀ (u n : ℕ) [NeZero n], n₀ ≤ n → ∀ φ : TorusSite n → ℝ,
      responseMap a ρA L u (latticeGradient φ) = latticeGradient fun x => φ (TorusLumps.parentBlock L x))
    (k d : ℕ) :
    ∀ (n : ℕ) [NeZero n], n₀ ≤ n → ∀ g : TorusBond (fineSide L d n) → ℝ, (∀ φ, g ⬝ᵥ latticeGradient φ = 0) →
      ∀ φ, adjointTransport a ρA L k d n g ⬝ᵥ latticeGradient φ = 0 := by
  induction d with
  | zero => intro n _ _ g hg; exact hg
  | succ d ih =>
    intro n _ hn g hg φ
    show responseAdjoint a ρA L (k + d) (adjointTransport a ρA L k d (n * L) g) ⬝ᵥ latticeGradient φ = 0
    rw [responseAdjoint_dotProduct, hG _ n hn φ]
    exact ih (n * L) (le_mul_side hL hn) g hg _
private theorem isLUB_gapAt_chain (hL : 0 < L)
    (hS : ∀ (u n : ℕ) [NeZero n], n₀ ≤ n → StepHypotheses a ρA L u n)
    (hG : ∀ (u n : ℕ) [NeZero n], n₀ ≤ n → ∀ φ : TorusSite n → ℝ,
      responseMap a ρA L u (latticeGradient φ) = latticeGradient fun x => φ (TorusLumps.parentBlock L x))
    (k d : ℕ) :
    ∀ (n : ℕ) [NeZero n], n₀ ≤ n → ∀ g : TorusBond (fineSide L d n) → ℝ, (∀ φ, g ⬝ᵥ latticeGradient φ = 0) →
      ∀ s, IsLUB (Set.range (gapAt a L (k + d) (adjointTransport a ρA L k d n g))) s →
        IsLUB (Set.range (gapAt a L k g)) (accumulatedCovariance a ρA L k d n g g + s) := by
  induction d with
  | zero =>
    intro n _ _ g _ s hs
    have e : accumulatedCovariance a ρA L k 0 n g g + s = s := by simp [accumulatedCovariance]
    rw [e]
    exact hs
  | succ d ih =>
    intro n _ hn g hg s hs
    have hn' := le_mul_side hL hn (L := L)
    have hk := adjointTransport_kills_gradients hL hG k d (n * L) hn' g hg
    have hstep := isLUB_gapAt_step (hS (k + d) n hn) (adjointTransport a ρA L k d (n * L) g) hk hs
    have h := ih (n * L) hn' g hg _ hstep
    have e : accumulatedCovariance a ρA L k (d + 1) n g g =
        accumulatedCovariance a ρA L k d (n * L) g g +
          stepCovariance a L (k + d) n (adjointTransport a ρA L k d (n * L) g)
            (adjointTransport a ρA L k d (n * L) g) := rfl
    rw [e, add_assoc]
    exact h
end Chain
section Trees
private def signedSum (f : ℤ → ℝ) (a : ℤ) : ℝ := ∑ s ∈ Finset.Ico 0 a, f s - ∑ s ∈ Finset.Ico a 0, f s
private theorem signedSum_zero (f : ℤ → ℝ) : signedSum f 0 = 0 := by simp [signedSum]
private theorem signedSum_add_one (f : ℤ → ℝ) (a : ℤ) : signedSum f (a + 1) = signedSum f a + f a := by
  unfold signedSum
  rcases lt_or_ge a 0 with h | h
  · have e1 : Finset.Ico (0 : ℤ) (a + 1) = ∅ := Finset.Ico_eq_empty (by omega)
    have e2 : Finset.Ico (0 : ℤ) a = ∅ := Finset.Ico_eq_empty (by omega)
    have e3 : Finset.Ico a 0 = insert a (Finset.Ico (a + 1) 0) := by
      ext s
      simp only [Finset.mem_Ico, Finset.mem_insert]
      omega
    rw [e1, e2, e3, Finset.sum_insert (by simp)]
    simp
  · have e1 : Finset.Ico (a + 1) (0 : ℤ) = ∅ := Finset.Ico_eq_empty (by omega)
    have e2 : Finset.Ico a (0 : ℤ) = ∅ := Finset.Ico_eq_empty (by omega)
    have e3 : Finset.Ico 0 (a + 1) = insert a (Finset.Ico 0 a) := by
      ext s
      simp only [Finset.mem_Ico, Finset.mem_insert]
      omega
    rw [e1, e2, e3, Finset.sum_insert (by simp)]
    simp
    ring
private def axisOffset (o : Fin 4 → ℤ) (i : Fin 4) (s : ℤ) : Fin 4 → ℤ :=
  fun l => if l < i then o l else if l = i then s else 0
variable {F : BlockAverages.BlockFrame}
private def treePotential (A : F.Site F.depth → Fin 4 → ℝ) (c : F.Site F.depth) (o : Fin 4 → ℤ) : ℝ :=
  ∑ l, signedSum (fun s => A (c + BlockAverages.siteOfCoords F.depth (axisOffset o l s)) l) (o l)
private theorem treePotential_add_single (A : F.Site F.depth → Fin 4 → ℝ) (c : F.Site F.depth) (o : Fin 4 → ℤ)
    (i : Fin 4) (hz : ∀ l, i < l → o l = 0) :
    treePotential A c (o + Pi.single i 1) =
      treePotential A c o + A (c + BlockAverages.siteOfCoords F.depth o) i := by
  unfold treePotential
  rw [← sub_eq_iff_eq_add', ← Finset.sum_sub_distrib]
  rw [Finset.sum_eq_single i]
  · have e1 : (o + Pi.single i (1 : ℤ) : Fin 4 → ℤ) i = o i + 1 := by simp
    have e2 : ∀ s, axisOffset (o + Pi.single i (1 : ℤ)) i s = axisOffset o i s := by
      intro s
      funext l
      unfold axisOffset
      split_ifs with h1 h2
      · simp [Pi.single_eq_of_ne (ne_of_lt h1)]
      · rfl
      · rfl
    have e3 : axisOffset o i (o i) = o := by
      funext l
      unfold axisOffset
      split_ifs with h1 h2
      · rfl
      · rw [h2]
      · exact (hz l (lt_of_le_of_ne (not_lt.mp h1) (Ne.symm h2))).symm
    simp only [e1, e2, signedSum_add_one]
    rw [e3]
    ring
  · intro l _ hl
    rcases lt_or_gt_of_ne hl with h | h
    · have e1 : (o + Pi.single i (1 : ℤ) : Fin 4 → ℤ) l = o l := by simp [Pi.single_eq_of_ne hl]
      have e2 : ∀ s, axisOffset (o + Pi.single i (1 : ℤ)) l s = axisOffset o l s := by
        intro s
        funext m
        unfold axisOffset
        split_ifs with h1 h2
        · simp [Pi.single_eq_of_ne (ne_of_lt (h1.trans h))]
        · rfl
        · rfl
      simp only [e1, e2, sub_self]
    · have e1 : (o + Pi.single i (1 : ℤ) : Fin 4 → ℤ) l = 0 := by simp [Pi.single_eq_of_ne hl, hz l h]
      simp only [e1, hz l h, signedSum_zero, sub_self]
  · simp
private theorem exists_treeGauge_frame (hL : Odd F.blockSide) (hs : ∀ i, 2 ≤ F.extent i)
    (A : F.Site F.depth → Fin 4 → ℝ) :
    ∃ φ : F.Site F.depth → ℝ, ∀ x i, BlockAverages.IsAxialTreeBond (x, i) →
      φ (x + BlockAverages.unitStep F.depth i) = φ x + A x i := by
  refine ⟨fun x => treePotential A (BlockAverages.cellCentre F.depth (BlockAverages.enclosingCell x))
    (BlockAverages.cellOffset x), fun x i ht => ?_⟩
  have hc : BlockAverages.enclosingCell (x + BlockAverages.unitStep F.depth i) = BlockAverages.enclosingCell x :=
    not_not.mp ht.1
  simp only
  rw [hc, BlockTrees.cellOffset_add_unitStep hL hs x i hc, treePotential_add_single A _ _ i ht.2,
    ← BlockTrees.eq_cellCentre_add_cellOffset]
private theorem mem_sitesOfCells (hL : Odd F.blockSide) (hs : ∀ i, 2 ≤ F.extent i) (x : F.Site F.depth) :
    x ∈ BlockAverages.sitesOfCells (ColdStepAtMirrorFrames.finiteCells F) F.depth := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.TwoTori.mem_sitesOfCells_finiteCells <;> assumption
private theorem mem_innerBonds (hL : Odd F.blockSide) (hs : ∀ i, 2 ≤ F.extent i) (b : F.Site F.depth × Fin 4) :
    b ∈ BlockAverages.innerBonds (ColdStepAtMirrorFrames.finiteCells F) F.depth := by
  unfold BlockAverages.innerBonds
  exact Finset.mem_filter.2 ⟨Finset.mem_product.2 ⟨mem_sitesOfCells hL hs _, Finset.mem_univ _⟩,
    mem_sitesOfCells hL hs _⟩
end Trees
section Chart
variable {L n : ℕ} [NeZero L] [NeZero n]
private theorem isAxialTreeBond_of_not_mem {b : TorusBond (n * L)} (hb : b ∉ StepCosts.chartBonds L n) :
    BlockAverages.IsAxialTreeBond (F := TorusLumps.stepBlockFrame L n)
      (StepCosts.torusSiteInFrame (TorusLumps.stepBlockFrame L n) 0 b.1, b.2) := by
  classical
  by_contra h
  exact hb (Finset.mem_filter.2 ⟨Finset.mem_univ _, h⟩)
abbrev _root_.YangMills.SharedProofs.p36150 := @isAxialTreeBond_of_not_mem
private theorem exists_treeGauge_torus (hL : Odd L) (hn : 2 ≤ n) (A : TorusBond (n * L) → ℝ) :
    ∃ φ : TorusSite (n * L) → ℝ, ∀ b, b ∉ StepCosts.chartBonds L n → A b = latticeGradient φ b := by
  have hp : ∀ i, (TorusLumps.stepBlockFrame L n).period (TorusLumps.stepBlockFrame L n).depth i = n * L :=
    fun i => TopLevelSites.period_depth_of_extent (F := TorusLumps.stepBlockFrame L n) (n := n) (fun _ => rfl) i
  obtain ⟨φ, hφ⟩ := exists_treeGauge_frame (F := TorusLumps.stepBlockFrame L n) hL (fun _ => hn)
    (fun s i => A (TorusLumps.toTorusSite (n * L) s, i))
  refine ⟨fun x => φ (StepCosts.torusSiteInFrame (TorusLumps.stepBlockFrame L n)
    (TorusLumps.stepBlockFrame L n).depth x), fun b hb => ?_⟩
  have h := hφ (StepCosts.torusSiteInFrame (TorusLumps.stepBlockFrame L n) (TorusLumps.stepBlockFrame L n).depth b.1)
    b.2 (isAxialTreeBond_of_not_mem hb)
  have hnext : StepCosts.torusSiteInFrame (TorusLumps.stepBlockFrame L n) (TorusLumps.stepBlockFrame L n).depth
        (b.1 + TorusFields.unitStep (n * L) b.2) =
      StepCosts.torusSiteInFrame (TorusLumps.stepBlockFrame L n) (TorusLumps.stepBlockFrame L n).depth b.1 +
        BlockAverages.unitStep (TorusLumps.stepBlockFrame L n).depth b.2 := by
    apply TopLevelSites.toTorusSite_injective hp
    rw [TopLevelSites.toTorusSite_torusSiteInFrame hp, TopLevelSites.toTorusSite_add hp,
      TopLevelSites.toTorusSite_torusSiteInFrame hp, TopLevelSites.toTorusSite_unitStep hp]
  have hA : TorusLumps.toTorusSite (n * L)
      (StepCosts.torusSiteInFrame (TorusLumps.stepBlockFrame L n) (TorusLumps.stepBlockFrame L n).depth b.1) = b.1 :=
    TopLevelSites.toTorusSite_torusSiteInFrame hp _
  simp only [hA, Prod.mk.eta] at h
  show A b = φ (StepCosts.torusSiteInFrame (TorusLumps.stepBlockFrame L n) (TorusLumps.stepBlockFrame L n).depth
      (b.1 + TorusFields.unitStep (n * L) b.2)) -
    φ (StepCosts.torusSiteInFrame (TorusLumps.stepBlockFrame L n) (TorusLumps.stepBlockFrame L n).depth b.1)
  rw [hnext, h]
  ring
abbrev _root_.YangMills.SharedProofs.p87081 := @exists_treeGauge_torus
private theorem isAxialTreeBond_torusFrame_iff (hL : Odd L) (hn : 2 ≤ n) (u : ℕ) (x : TorusSite (n * L))
    (i : Fin 4) :
    BlockAverages.IsAxialTreeBond (F := torusFrame L u n)
        (StepCosts.torusSiteInFrame (torusFrame L u n) (torusFrame L u n).depth x, i) ↔
      BlockAverages.IsAxialTreeBond (F := TorusLumps.stepBlockFrame L n)
        (StepCosts.torusSiteInFrame (TorusLumps.stepBlockFrame L n) 0 x, i) := by
  have : NeZero (n * (torusFrame L u n).blockSide) := inferInstanceAs (NeZero (n * L))
  have : NeZero (n * (TorusLumps.stepBlockFrame L n).blockSide) := inferInstanceAs (NeZero (n * L))
  have h1 := TopLevelSites.isAxialTreeBond_torusSiteInFrame_iff (F := torusFrame L u n) (n := n) (fun _ => rfl)
    hL hn x i
  have h2 := TopLevelSites.isAxialTreeBond_torusSiteInFrame_iff (F := TorusLumps.stepBlockFrame L n) (n := n)
    (fun _ => rfl) hL hn x i
  exact h1.trans h2.symm
private theorem responseKernel_eq_zero_of_tree (hL : Odd L) (hn : 2 ≤ n) (a ρA : ℝ) (u : ℕ)
    {b : TorusBond (n * L)} (c : TorusBond n) (hb : b ∉ StepCosts.chartBonds L n) :
    responseKernel a ρA L u b c = 0 := by
  classical
  have ht := (isAxialTreeBond_torusFrame_iff hL hn u b.1 b.2).2 (isAxialTreeBond_of_not_mem hb)
  have hw : (ColdStepAtMirrorFrames.torusCoordinate a ρA
      (StepCosts.torusSiteInFrame (torusFrame L u n) (torusFrame L u n).depth b.1, b.2) :
      (torusFrame L u n).GaugeField (torusFrame L u n).top → BlockAverages.imaginaryQuaternions) = fun _ => 0 := by
    funext V
    unfold ColdStepAtMirrorFrames.torusCoordinate BlockAverages.minimizingBondCoordinate
      BlockAverages.minimizingCoordinates
    split_ifs with h
    · refine h.choose_spec.1 (StepCosts.torusSiteInFrame (torusFrame L u n) (torusFrame L u n).depth b.1, b.2)
        fun hm => ?_
      exact (Finset.mem_filter.1 hm).2 ht
    · rfl
  unfold responseKernel ColdStepAtMirrorFrames.minimizerResponse
  rw [hw, if_neg (fun h => ht.1 h.1)]
  unfold ColdStepAtMirrorFrames.bondDeriv
  simp [iteratedFDeriv_const_of_ne]
  rfl
abbrev _root_.YangMills.SharedProofs.p23899 := @responseKernel_eq_zero_of_tree
private theorem responseMap_eq_zero_of_tree (hL : Odd L) (hn : 2 ≤ n) (a ρA : ℝ) (u : ℕ) (B : TorusBond n → ℝ)
    (b : TorusBond (n * L)) (hb : b ∉ StepCosts.chartBonds L n) : responseMap a ρA L u B b = 0 := by
  unfold responseMap
  exact Finset.sum_eq_zero fun c _ => by rw [responseKernel_eq_zero_of_tree hL hn a ρA u c hb, zero_mul]
private def bondToFrame (L u n : ℕ) (b : TorusBond (n * L)) :
    (torusFrame L u n).Site (torusFrame L u n).depth × Fin 4 :=
  (StepCosts.torusSiteInFrame (torusFrame L u n) (torusFrame L u n).depth b.1, b.2)
private def bondFromFrame (L u n : ℕ) (b : (torusFrame L u n).Site (torusFrame L u n).depth × Fin 4) :
    TorusBond (n * L) :=
  (TorusLumps.toTorusSite (n * L) b.1, b.2)
private theorem torusFrame_period (u : ℕ) (i : Fin 4) :
    (torusFrame L u n).period (torusFrame L u n).depth i = n * L :=
  TopLevelSites.period_depth_of_extent (F := torusFrame L u n) (n := n) (fun _ => rfl) i
private theorem bondFromFrame_bondToFrame (u : ℕ) (b : TorusBond (n * L)) :
    bondFromFrame L u n (bondToFrame L u n b) = b :=
  Prod.ext (TopLevelSites.toTorusSite_torusSiteInFrame (torusFrame_period u) _) rfl
private theorem bondToFrame_bondFromFrame (u : ℕ) (b : (torusFrame L u n).Site (torusFrame L u n).depth × Fin 4) :
    bondToFrame L u n (bondFromFrame L u n b) = b :=
  Prod.ext (TopLevelSites.torusSiteInFrame_toTorusSite (torusFrame_period u) _) rfl
private theorem chartRestriction_apply (u : ℕ) (h : TorusBond (n * L) → ℝ)
    (b : ↥(BlockAverages.chordBonds (ColdStepAtMirrorFrames.finiteCells (torusFrame L u n)))) :
    chartRestriction L u n h b = h (bondFromFrame L u n b.1) := by
  classical
  unfold chartRestriction
  rw [Finset.sum_eq_single (bondFromFrame L u n b.1)]
  · exact if_pos (bondToFrame_bondFromFrame u b.1)
  · intro c _ hc
    rw [if_neg]
    intro he
    apply hc
    have : bondToFrame L u n c = b.1 := he
    rw [← this, bondFromFrame_bondToFrame]
  · simp
private theorem mem_chartBonds_iff (hL : Odd L) (hn : 2 ≤ n) (u : ℕ) (c : TorusBond (n * L)) :
    c ∈ StepCosts.chartBonds L n ↔
      bondToFrame L u n c ∈ BlockAverages.chordBonds (ColdStepAtMirrorFrames.finiteCells (torusFrame L u n)) := by
  classical
  constructor
  · intro h
    have h1 : ¬ BlockAverages.IsAxialTreeBond (F := TorusLumps.stepBlockFrame L n)
        (StepCosts.torusSiteInFrame (TorusLumps.stepBlockFrame L n) 0 c.1, c.2) :=
      (Finset.mem_filter.1 h).2
    unfold BlockAverages.chordBonds
    exact Finset.mem_filter.2 ⟨mem_innerBonds (F := torusFrame L u n) hL (fun _ => hn) _,
      fun ht => h1 ((isAxialTreeBond_torusFrame_iff hL hn u c.1 c.2).1 ht)⟩
  · intro h
    unfold BlockAverages.chordBonds at h
    have h2 := (Finset.mem_filter.1 h).2
    exact Finset.mem_filter.2 ⟨Finset.mem_univ _,
      fun ht => h2 ((isAxialTreeBond_torusFrame_iff hL hn u c.1 c.2).2 ht)⟩
private theorem dotProduct_eq_chartRestriction (hL : Odd L) (hn : 2 ≤ n) (u : ℕ) (g W : TorusBond (n * L) → ℝ)
    (hW : ∀ b, b ∉ StepCosts.chartBonds L n → W b = 0) :
    g ⬝ᵥ W = chartRestriction L u n g ⬝ᵥ chartRestriction L u n W := by
  classical
  have e1 : g ⬝ᵥ W = ∑ c ∈ StepCosts.chartBonds L n, g c * W c := by
    unfold dotProduct
    symm
    apply Finset.sum_subset (Finset.subset_univ _)
    intro c _ hc
    rw [hW c hc, mul_zero]
  have e2 : chartRestriction L u n g ⬝ᵥ chartRestriction L u n W =
      ∑ b ∈ BlockAverages.chordBonds (ColdStepAtMirrorFrames.finiteCells (torusFrame L u n)),
        g (bondFromFrame L u n b) * W (bondFromFrame L u n b) := by
    unfold dotProduct
    simp only [chartRestriction_apply]
    exact Finset.sum_coe_sort (BlockAverages.chordBonds (ColdStepAtMirrorFrames.finiteCells (torusFrame L u n)))
      (fun b => g (bondFromFrame L u n b) * W (bondFromFrame L u n b))
  rw [e1, e2]
  refine Finset.sum_nbij' (bondToFrame L u n) (bondFromFrame L u n) ?_ ?_ ?_ ?_ ?_
  · intro c hc
    exact (mem_chartBonds_iff hL hn u c).1 hc
  · intro b hb
    refine (mem_chartBonds_iff hL hn u _).2 ?_
    rw [bondToFrame_bondFromFrame]
    exact hb
  · intro c _
    exact bondFromFrame_bondToFrame u c
  · intro b _
    exact bondToFrame_bondFromFrame u b
  · intro c _
    rw [bondFromFrame_bondToFrame]
private theorem exists_extension_chartRestriction (hL : Odd L) (hn : 2 ≤ n) (u : ℕ)
    (v : ↥(BlockAverages.chordBonds (ColdStepAtMirrorFrames.finiteCells (torusFrame L u n))) → ℝ) :
    ∃ W : TorusBond (n * L) → ℝ, (∀ b, b ∉ StepCosts.chartBonds L n → W b = 0) ∧ chartRestriction L u n W = v := by
  classical
  refine ⟨fun c => if h : bondToFrame L u n c ∈
      BlockAverages.chordBonds (ColdStepAtMirrorFrames.finiteCells (torusFrame L u n)) then v ⟨_, h⟩ else 0, ?_, ?_⟩
  · intro b hb
    exact dif_neg (fun h => hb ((mem_chartBonds_iff hL hn u b).2 h))
  · funext b
    rw [chartRestriction_apply]
    have h : bondToFrame L u n (bondFromFrame L u n b.1) ∈
        BlockAverages.chordBonds (ColdStepAtMirrorFrames.finiteCells (torusFrame L u n)) := by
      rw [bondToFrame_bondFromFrame]
      exact b.2
    simp only [dif_pos h]
    congr 1
    exact Subtype.ext (bondToFrame_bondFromFrame u b.1)
end Chart
section Main
private structure ChainHypotheses (a ρA cK : ℝ) (L n₀ : ℕ) [NeZero L] : Prop where
  L_pos : 0 < L
  cK_pos : 0 < cK
  step : ∀ (u n : ℕ) [NeZero n], n₀ ≤ n → StepHypotheses a ρA L u n
  gradient : ∀ (u n : ℕ) [NeZero n], n₀ ≤ n → ∀ φ : TorusSite n → ℝ,
    responseMap a ρA L u (latticeGradient φ) = latticeGradient fun x => φ (TorusLumps.parentBlock L x)
  coercive : ∀ (u n : ℕ) [NeZero n], n₀ ≤ n → ∀ A : TorusBond n → ℝ,
    2 * cK * ∑ p ∈ plaquettesIn (Finset.univ : Finset (TorusSite n)), curl A p ^ 2 ≤ maxwellForm a L u A A
  standingConstraints : ∀ (k d n : ℕ) [NeZero n], n₀ ≤ n →
    ∀ p ∈ plaquettesIn (Finset.univ : Finset (TorusSite (fineSide L d n))), ∀ (B : TorusBond n → ℝ) (s : ℝ),
      (∀ p' ∈ plaquettesIn (Finset.univ : Finset (TorusSite n)), |curl B p'| ≤ s) →
        |∑ c, adjointTransport a ρA L k d n (curlFunctional p) c * B c| ≤ (1 / 2 : ℝ) ^ d * s
variable {a ρA cK : ℝ} {L n₀ : ℕ} [NeZero L]
private theorem kernelPair_maxwell_nonneg (hF : ChainHypotheses a ρA cK L n₀) (u n : ℕ) [NeZero n] (hn : n₀ ≤ n)
    (A : TorusBond n → ℝ) :
    0 ≤ kernelPair (maxwellKernel (m := n) a L u) A A := by
  have h := hF.coercive u n hn A
  have h0 : 0 ≤ 2 * cK * ∑ p ∈ plaquettesIn (Finset.univ : Finset (TorusSite n)), curl A p ^ 2 :=
    mul_nonneg (by linarith [hF.cK_pos]) (Finset.sum_nonneg fun _ _ => sq_nonneg _)
  exact h0.trans h
private theorem coercive_curl_sq_le (hF : ChainHypotheses a ρA cK L n₀) (u n : ℕ) [NeZero n] (hn : n₀ ≤ n)
    (A : TorusBond n → ℝ) {p : TorusPlaquette n} (hp : p ∈ plaquettesIn (Finset.univ : Finset (TorusSite n))) :
    2 * cK * curl A p ^ 2 ≤ kernelPair (maxwellKernel (m := n) a L u) A A := by
  have h := hF.coercive u n hn A
  have h1 : curl A p ^ 2 ≤ ∑ p ∈ plaquettesIn (Finset.univ : Finset (TorusSite n)), curl A p ^ 2 :=
    Finset.single_le_sum (f := fun p => curl A p ^ 2) (fun _ _ => sq_nonneg _) hp
  have h2 : 2 * cK * curl A p ^ 2 ≤
      2 * cK * ∑ p ∈ plaquettesIn (Finset.univ : Finset (TorusSite n)), curl A p ^ 2 :=
    mul_le_mul_of_nonneg_left h1 (by linarith [hF.cK_pos])
  exact h2.trans h
private theorem curl_eq_zero_of_kernelPair (hF : ChainHypotheses a ρA cK L n₀) (u n : ℕ) [NeZero n]
    (hn : n₀ ≤ n) (A : TorusBond n → ℝ)
    (hA : kernelPair (maxwellKernel (m := n) a L u) A A = 0) {p : TorusPlaquette n}
    (hp : p ∈ plaquettesIn (Finset.univ : Finset (TorusSite n))) : curl A p = 0 := by
  have h := coercive_curl_sq_le hF u n hn A hp
  rw [hA] at h
  have hc := hF.cK_pos
  have h3 : curl A p ^ 2 ≤ 0 := by
    by_contra hne
    have : 0 < 2 * cK * curl A p ^ 2 := mul_pos (by linarith) (not_le.mp hne)
    linarith
  exact pow_eq_zero_iff (two_ne_zero) |>.1 (le_antisymm h3 (sq_nonneg _))
private theorem le_fineSide (hL : 0 < L) (d n : ℕ) (hn : n₀ ≤ n) : n₀ ≤ fineSide L d n := by
  rw [fineSide_eq]
  exact hn.trans (Nat.le_mul_of_pos_right n (pow_pos hL d))
private theorem accumulatedCovariance_approx (hF : ChainHypotheses a ρA cK L n₀) (k d n : ℕ) [NeZero n]
    (hn : n₀ ≤ n) :
    ∃ Tt : TorusPlaquette (fineSide L d n) → TorusPlaquette (fineSide L d n) → ℝ,
      IsMaxwellCovariance a L k Tt ∧
      ∀ p ∈ plaquettesIn (Finset.univ : Finset (TorusSite (fineSide L d n))),
        ∀ p' ∈ plaquettesIn (Finset.univ : Finset (TorusSite (fineSide L d n))),
          |accumulatedCovariance a ρA L k d n (curlFunctional p) (curlFunctional p') - Tt p p'| ≤
            1 / (2 * cK) * (4 : ℝ) ^ (-(d : ℤ)) := by
  classical
  have hc := hF.cK_pos
  have hm : n₀ ≤ fineSide L d n := le_fineSide hF.L_pos d n hn
  have hposb := kernelPair_maxwell_nonneg hF k (fineSide L d n) hm
  have hpost := kernelPair_maxwell_nonneg hF (k + d) n hn
  obtain ⟨G, hG⟩ : ∃ G : TorusPlaquette (fineSide L d n) → TorusBond (fineSide L d n) → ℝ,
      G = fun p => if p ∈ plaquettesIn (Finset.univ : Finset (TorusSite (fineSide L d n))) then
        curlFunctional p else 0 := ⟨_, rfl⟩
  obtain ⟨Ct, hCt⟩ : ∃ Ct : TorusPlaquette (fineSide L d n) → TorusBond n → ℝ,
      Ct = fun p => if p ∈ plaquettesIn (Finset.univ : Finset (TorusSite (fineSide L d n))) then
        adjointTransport a ρA L k d n (curlFunctional p) else 0 := ⟨_, rfl⟩
  have hGp : ∀ p ∈ plaquettesIn (Finset.univ : Finset (TorusSite (fineSide L d n))), G p = curlFunctional p :=
    fun p hp => by
      rw [hG]; exact if_pos hp
  have hCp : ∀ p ∈ plaquettesIn (Finset.univ : Finset (TorusSite (fineSide L d n))),
      Ct p = adjointTransport a ρA L k d n (curlFunctional p) := fun p hp => by
    rw [hCt]; exact if_pos hp
  have hsolveb : ∀ p, ∃ x, (symmPart (maxwellKernel (m := fineSide L d n) a L k)).mulVec x = G p := by
    intro p
    refine exists_symmPart_mulVec_eq _ _ fun A hA => ?_
    by_cases hp : p ∈ plaquettesIn (Finset.univ : Finset (TorusSite (fineSide L d n)))
    · rw [hGp p hp, curlFunctional_dotProduct]
      exact curl_eq_zero_of_kernelPair hF k _ hm A hA hp
    · have : G p = 0 := by rw [hG]; exact if_neg hp
      rw [this, zero_dotProduct]
  have hsolvet : ∀ p, ∃ y, (symmPart (maxwellKernel (m := n) a L (k + d))).mulVec y = Ct p := by
    intro p
    refine exists_symmPart_mulVec_eq _ _ fun B hB => ?_
    by_cases hp : p ∈ plaquettesIn (Finset.univ : Finset (TorusSite (fineSide L d n)))
    · have h := hF.standingConstraints k d n hn p hp B 0 fun p' hp' => by
        rw [curl_eq_zero_of_kernelPair hF (k + d) n hn B hB hp']
        simp
      rw [mul_zero] at h
      rw [hCp p hp]
      exact abs_eq_zero.1 (le_antisymm h (abs_nonneg _))
    · have : Ct p = 0 := by rw [hCt]; exact if_neg hp
      rw [this, zero_dotProduct]
  choose X hX using hsolveb
  choose Y hY using hsolvet
  have hTs : ∀ p p', G p ⬝ᵥ X p' = G p' ⬝ᵥ X p := by
    intro p p'
    rw [← hX p, ← hX p', dotProduct_comm, symmPart_dotProduct_comm, dotProduct_comm]
  have hRs : ∀ p p', Ct p ⬝ᵥ Y p' = Ct p' ⬝ᵥ Y p := by
    intro p p'
    rw [← hY p, ← hY p', dotProduct_comm, symmPart_dotProduct_comm, dotProduct_comm]
  have eqn : ∀ (g x : TorusBond (fineSide L d n) → ℝ) (y : TorusBond n → ℝ),
      (symmPart (maxwellKernel (m := fineSide L d n) a L k)).mulVec x = g →
      (symmPart (maxwellKernel (m := n) a L (k + d))).mulVec y = adjointTransport a ρA L k d n g →
      (∀ φ, g ⬝ᵥ latticeGradient φ = 0) →
      g ⬝ᵥ x = accumulatedCovariance a ρA L k d n g g + adjointTransport a ρA L k d n g ⬝ᵥ y := by
    intro g x y hx hy hk
    have h1 := isLUB_gap_symmPart _ hposb hx
    have h2 := isLUB_gap_symmPart _ hpost hy
    have h3 := isLUB_gapAt_chain hF.L_pos hF.step hF.gradient k d n hn g hk _ h2
    exact h1.unique h3
  have entry : ∀ p ∈ plaquettesIn (Finset.univ : Finset (TorusSite (fineSide L d n))),
      ∀ p' ∈ plaquettesIn (Finset.univ : Finset (TorusSite (fineSide L d n))),
      G p ⬝ᵥ X p' = accumulatedCovariance a ρA L k d n (curlFunctional p) (curlFunctional p') + Ct p ⬝ᵥ Y p' := by
    intro p hp p' hp'
    have hb := fun (q : TorusPlaquette (fineSide L d n))
        (hq : q ∈ plaquettesIn (Finset.univ : Finset (TorusSite (fineSide L d n)))) =>
      eqn (curlFunctional q) (X q) (Y q) (by rw [hX, hGp q hq]) (by rw [hY, hCp q hq])
        (curlFunctional_dotProduct_latticeGradient q)
    have e1 := hb p hp
    have e2 := hb p' hp'
    have e3 := eqn (curlFunctional p + curlFunctional p') (X p + X p') (Y p + Y p')
      (by rw [Matrix.mulVec_add, hX, hX, hGp p hp, hGp p' hp'])
      (by rw [Matrix.mulVec_add, hY, hY, hCp p hp, hCp p' hp', adjointTransport_add])
      (fun φ => by
        rw [add_dotProduct, curlFunctional_dotProduct_latticeGradient,
          curlFunctional_dotProduct_latticeGradient, add_zero])
    rw [accumulatedCovariance_add_self hF.L_pos (fun u n _ hn => (hF.step u n hn).definite) k d n hn,
      adjointTransport_add, ← hCp p hp, ← hCp p' hp'] at e3
    simp only [add_dotProduct, dotProduct_add] at e3
    rw [← hCp p hp] at e1
    rw [← hCp p' hp'] at e2
    have s1 := hTs p p'
    rw [hGp p hp, hGp p' hp'] at s1
    have s2 := hRs p p'
    rw [hGp p hp]
    linarith
  refine ⟨fun p p' => G p ⬝ᵥ X p', ⟨fun p p' => hTs p p', fun h => ?_⟩, ?_⟩
  · have hx : (symmPart (maxwellKernel (m := fineSide L d n) a L k)).mulVec
        (∑ p ∈ plaquettesIn (Finset.univ : Finset (TorusSite (fineSide L d n))), h p • X p) =
          ∑ p ∈ plaquettesIn (Finset.univ : Finset (TorusSite (fineSide L d n))), h p • G p := by
      have := map_sum (symmPart (maxwellKernel (m := fineSide L d n) a L k)).mulVecLin (fun p => h p • X p)
        (plaquettesIn (Finset.univ : Finset (TorusSite (fineSide L d n))))
      simp only [Matrix.mulVecLin_apply, Matrix.mulVec_smul, hX] at this
      exact this
    have h1 := isLUB_gap_symmPart _ hposb hx
    have eA : maxwellDefect a L k h = fun A =>
        2 * ((∑ p ∈ plaquettesIn (Finset.univ : Finset (TorusSite (fineSide L d n))), h p • G p) ⬝ᵥ A) -
          kernelPair (maxwellKernel (m := fineSide L d n) a L k) A A := by
      funext A
      unfold maxwellDefect
      have : (∑ p ∈ plaquettesIn (Finset.univ : Finset (TorusSite (fineSide L d n))), h p • G p) ⬝ᵥ A =
          ∑ p ∈ plaquettesIn (Finset.univ : Finset (TorusSite (fineSide L d n))), h p * curl A p := by
        rw [sum_dotProduct]
        refine Finset.sum_congr rfl fun p hp => ?_
        rw [smul_dotProduct, hGp p hp, curlFunctional_dotProduct, smul_eq_mul]
      rw [this]
      rfl
    have eV : (∑ p ∈ plaquettesIn (Finset.univ : Finset (TorusSite (fineSide L d n))), h p • G p) ⬝ᵥ
        (∑ p ∈ plaquettesIn (Finset.univ : Finset (TorusSite (fineSide L d n))), h p • X p) =
        ∑ p ∈ plaquettesIn (Finset.univ : Finset (TorusSite (fineSide L d n))),
          ∑ p' ∈ plaquettesIn (Finset.univ : Finset (TorusSite (fineSide L d n))),
            h p * (G p ⬝ᵥ X p') * h p' := by
      rw [sum_dotProduct]
      refine Finset.sum_congr rfl fun p _ => ?_
      rw [dotProduct_sum]
      refine Finset.sum_congr rfl fun p' _ => ?_
      rw [smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul]
      ring
    rw [eA]
    simp only
    rw [← eV]
    exact h1
  · intro p hp p' hp'
    have hq0 : 0 ≤ kernelPair (maxwellKernel (m := n) a L (k + d)) (Y p') (Y p') := hpost _
    obtain ⟨q, hq⟩ : ∃ q, q = kernelPair (maxwellKernel (m := n) a L (k + d)) (Y p') (Y p') := ⟨_, rfl⟩
    rw [← hq] at hq0
    have hR : Ct p' ⬝ᵥ Y p' = q := by
      rw [hq, ← dotProduct_symmPart_mulVec_self, hY, dotProduct_comm]
    obtain ⟨t, ht⟩ : ∃ t, t = Real.sqrt (q / (2 * cK)) := ⟨_, rfl⟩
    have ht0 : 0 ≤ t := by rw [ht]; exact Real.sqrt_nonneg _
    have h2c : 0 < 2 * cK := by linarith
    have ht2 : t ^ 2 = q / (2 * cK) := by
      rw [ht]; exact Real.sq_sqrt (div_nonneg hq0 h2c.le)
    have hcurl : ∀ p'' ∈ plaquettesIn (Finset.univ : Finset (TorusSite n)), |curl (Y p') p''| ≤ t := by
      intro p'' hp''
      rw [ht]
      apply Real.abs_le_sqrt
      rw [le_div_iff₀ h2c]
      have := coercive_curl_sq_le hF (k + d) n hn (Y p') hp''
      rw [← hq] at this
      linarith
    have hrow : ∀ r ∈ plaquettesIn (Finset.univ : Finset (TorusSite (fineSide L d n))),
        |Ct r ⬝ᵥ Y p'| ≤ (1 / 2 : ℝ) ^ d * t := by
      intro r hr
      rw [hCp r hr]
      exact hF.standingConstraints k d n hn r hr (Y p') t hcurl
    have hqle : q ≤ (1 / 2 : ℝ) ^ d * t := by
      rw [← hR]
      exact (le_abs_self _).trans (hrow p' hp')
    have hpow : (0 : ℝ) < (1 / 2 : ℝ) ^ d := by positivity
    have htle : t ≤ (1 / 2 : ℝ) ^ d / (2 * cK) := by
      rw [le_div_iff₀ h2c]
      have hq2 : q = t ^ 2 * (2 * cK) := by
        rw [ht2]
        field_simp
      rcases ht0.eq_or_lt with h0 | h0
      · rw [← h0]
        simp only [zero_mul]
        exact hpow.le
      · have h5 : t * (t * (2 * cK)) ≤ t * (1 / 2 : ℝ) ^ d := by
          have : t * (t * (2 * cK)) = q := by rw [hq2]; ring
          rw [this, mul_comm t]
          exact hqle
        exact le_of_mul_le_mul_left h5 h0
    have e4 : (4 : ℝ) ^ (-(d : ℤ)) = (1 / 2 : ℝ) ^ d * (1 / 2 : ℝ) ^ d := by
      rw [zpow_neg, zpow_natCast, ← mul_pow, ← inv_pow]
      norm_num
    have hfin : (1 / 2 : ℝ) ^ d * t ≤ 1 / (2 * cK) * (4 : ℝ) ^ (-(d : ℤ)) := by
      rw [e4]
      have := mul_le_mul_of_nonneg_left htle hpow.le
      calc (1 / 2 : ℝ) ^ d * t ≤ (1 / 2 : ℝ) ^ d * ((1 / 2 : ℝ) ^ d / (2 * cK)) := this
        _ = 1 / (2 * cK) * ((1 / 2 : ℝ) ^ d * (1 / 2 : ℝ) ^ d) := by ring
    have h6 := entry p hp p' hp'
    have h7 : accumulatedCovariance a ρA L k d n (curlFunctional p) (curlFunctional p') - G p ⬝ᵥ X p' =
        -(Ct p ⬝ᵥ Y p') := by
      rw [h6]
      ring
    show |accumulatedCovariance a ρA L k d n (curlFunctional p) (curlFunctional p') - G p ⬝ᵥ X p'| ≤ _
    rw [h7, abs_neg]
    exact (hrow p hp).trans hfin
end Main
section ParameterChoices
private theorem holdsOnParameters_and {P Q : RenormalizationStepParameters.ParameterAssignment → ℝ → Prop}
    (hP : HoldsOnParameterFamilies P) (hQ : HoldsOnParameterFamilies Q) :
    HoldsOnParameterFamilies fun T y => P T y ∧ Q T y := by apply _root_.YangMills.SharedProofs.p24215 <;> assumption
private theorem holdsOnParameters_mono {P Q : RenormalizationStepParameters.ParameterAssignment → ℝ → Prop}
    (hP : HoldsOnParameterFamilies P) (h : ∀ T y, T.Admissible → P T y → Q T y) : HoldsOnParameterFamilies Q := by
  intro a ha
  obtain ⟨L1, r1, C1, hr1, h1⟩ := hP a ha
  refine ⟨L1, r1, C1, hr1, ?_⟩
  intro L hodd hL T hTa hTL hD hCS hCH hrt hC
  obtain ⟨y1, hy1⟩ := h1 L hodd hL T hTa hTL hD hCS hCH hrt hC
  exact ⟨y1, fun y hy hR hW => h T y hD (hy1 y hy hR hW)⟩
private theorem chainHypotheses_of_stepParameters (Tb : RenormalizationStepParameters.ParameterAssignment) (y : ℝ) (hD : Tb.Admissible)
    (h₁ : maxwellFormStepIdentityAt Tb y) (h₂ : GradientMaxwellPropertiesAt Tb y)
    (h₃ : transportedCurlFunctionalBoundsAt Tb y) (h₄ : StepHessianPosDefAt Tb y) :
    ChainHypotheses Tb.coupling Tb.ρA Tb.coercivity (Tb.stepParameters y).side Tb.n₀ := by
  have hodd : Odd (Tb.stepParameters y).side := hD.L_odd
  have hLp : 0 < (Tb.stepParameters y).side := hodd.pos
  have hn2 : ∀ n, Tb.n₀ ≤ n → 2 ≤ n := fun n hn => by
    have := hD.n₀_ge
    omega
  have hpos : ∀ (u n : ℕ) [NeZero n], Tb.n₀ ≤ n → ∀ A : TorusBond n → ℝ,
      0 ≤ maxwellForm Tb.coupling (Tb.stepParameters y).side u A A := by
    intro u n _ hn A
    have h := (h₂ u n hn).2.2 A
    have h0 : 0 ≤ 2 * Tb.coercivity * ∑ p ∈ plaquettesIn (Finset.univ : Finset (TorusSite n)), curl A p ^ 2 :=
      mul_nonneg (by linarith [hD.cK_pos]) (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    exact h0.trans h
  refine ⟨hLp, hD.cK_pos, ?_, fun u n _ hn φ => (h₂ u n hn).1 φ, fun u n _ hn A => (h₂ u n hn).2.2 A, ?_⟩
  · intro u n _ hn
    have hnL : Tb.n₀ ≤ n * (Tb.stepParameters y).side := le_mul_side hLp hn
    exact
      { a_nonneg := by linarith [hD.a_ge]
        one_step := fun W B hW => h₁ u n hn W B hW
        definite := h₄ u n hn
        off_trees := fun B b hb => responseMap_eq_zero_of_tree hodd (hn2 n hn) _ _ u B b hb
        gauge := exists_treeGauge_torus hodd (hn2 n hn)
        form_pos := hpos u _ hnL
        kills := fun φ A => (h₂ u _ hnL).2.1 φ A
        pairing := dotProduct_eq_chartRestriction hodd (hn2 n hn) u
        extend := exists_extension_chartRestriction hodd (hn2 n hn) u }
  · intro k d n _ hn p hp B s hs
    exact (h₃.1 k d n hn p hp).1 B s hs
end ParameterChoices
theorem stepCovariancesSumToMaxwell (h₁ : maxwellFormStepIdentityStatement)
    (h₂ : gradientMaxwellStatement) (h₃ : transportedCurlFunctionalBoundsStatement)
    (h₄ : stepHessianPosDefStatement) : StepCovariancesSumToMaxwellStatement :=
  holdsOnParameters_mono
    (holdsOnParameters_and h₁ (holdsOnParameters_and h₂ (holdsOnParameters_and h₃ h₄)))
    fun Tb y hD h =>
      ⟨1 / (2 * Tb.coercivity), fun k d n _ hn =>
        accumulatedCovariance_approx (chainHypotheses_of_stepParameters Tb y hD h.1 h.2.1 h.2.2.1 h.2.2.2) k d n hn⟩
end YangMills.Construction.ResponseInTheExpansion
end
