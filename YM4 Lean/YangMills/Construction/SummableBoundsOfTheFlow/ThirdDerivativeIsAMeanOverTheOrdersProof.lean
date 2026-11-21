import YangMills.Construction.ClusterExpansionOfAStep.PlaquettesUnderGaugesAndMoves
import YangMills.Construction.ColdStepAtMirrorFrames.LogarithmOfAMovedExponential
import YangMills.Construction.SummableBoundsOfTheFlow.DerivativesAlongAList
import YangMills.Construction.SummableBoundsOfTheFlow.SmoothAlongAMotion
import YangMills.Construction.SummableBoundsOfTheFlow.ThirdDerivativeIsAMeanOverTheOrders
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion Topology
namespace YangMills.Construction
open BlockAverages ColdStepAtMirrorFrames IteratedDerivative
namespace ThirdDerivative
namespace MeanOverOrders
variable {F : BlockFrame} {j : ℕ}
abbrev TripleParam : Type := Fin 3 → ℝ
abbrev PairParam : Type := TripleParam × TripleParam
def polarizationSum {E : Type} (T : E → E → E → ℝ) (a b d : E) : ℝ :=
  T a b d + T a d b + T b a d + T b d a + T d a b + T d b a
theorem cube_sum_expand {E : Type} [AddCommGroup E] (T : E → E → E → ℝ)
    (h1 : ∀ x x' y z, T (x + x') y z = T x y z + T x' y z)
    (h2 : ∀ x y y' z, T x (y + y') z = T x y z + T x y' z)
    (h3 : ∀ x y z z', T x y (z + z') = T x y z + T x y z') (a b d : E) :
    T (a + b + d) (a + b + d) (a + b + d) - T (a + b) (a + b) (a + b) - T (a + d) (a + d) (a + d) -
      T (b + d) (b + d) (b + d) + T a a a + T b b b + T d d d = polarizationSum T a b d := by
  simp only [h1, h2, h3, polarizationSum]
  ring
theorem polarizationSum_eq {E : Type} [AddCommGroup E] (T T' : E → E → E → ℝ)
    (h1 : ∀ x x' y z, T (x + x') y z = T x y z + T x' y z)
    (h2 : ∀ x y y' z, T x (y + y') z = T x y z + T x y' z)
    (h3 : ∀ x y z z', T x y (z + z') = T x y z + T x y z')
    (h1' : ∀ x x' y z, T' (x + x') y z = T' x y z + T' x' y z)
    (h2' : ∀ x y y' z, T' x (y + y') z = T' x y z + T' x y' z)
    (h3' : ∀ x y z z', T' x y (z + z') = T' x y z + T' x y z')
    (h : ∀ x, T x x x = T' x x x) (a b d : E) : polarizationSum T a b d = polarizationSum T' a b d := by
  rw [← cube_sum_expand T h1 h2 h3, ← cube_sum_expand T' h1' h2' h3']
  simp only [h]
theorem sum_perm_fin_three (f : Equiv.Perm (Fin 3) → ℝ) :
    ∑ π, f π = f 1 + f (Equiv.swap 1 2) + f (Equiv.swap 0 1) + f (Equiv.swap 0 1 * Equiv.swap 1 2) +
      f (Equiv.swap 1 2 * Equiv.swap 0 1) + f (Equiv.swap 0 2) := by
  have e : (Finset.univ : Finset (Equiv.Perm (Fin 3))) = {1, Equiv.swap 1 2, Equiv.swap 0 1,
      Equiv.swap 0 1 * Equiv.swap 1 2, Equiv.swap 1 2 * Equiv.swap 0 1, Equiv.swap 0 2} := by decide
  rw [e]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  ring
theorem sum_perm_eq_polarizationSum (T : Fin 3 → Fin 3 → Fin 3 → ℝ) :
    ∑ π : Equiv.Perm (Fin 3), T (π 0) (π 1) (π 2) = polarizationSum T 0 1 2 := by
  rw [sum_perm_fin_three]
  have e1 : (1 : Equiv.Perm (Fin 3)) 0 = 0 ∧ (1 : Equiv.Perm (Fin 3)) 1 = 1 ∧ (1 : Equiv.Perm (Fin 3)) 2 = 2 := by decide
  have e2 : (Equiv.swap (1 : Fin 3) 2) 0 = 0 ∧ (Equiv.swap (1 : Fin 3) 2) 1 = 2 ∧ (Equiv.swap (1 : Fin 3) 2) 2 = 1 := by decide
  have e3 : (Equiv.swap (0 : Fin 3) 1) 0 = 1 ∧ (Equiv.swap (0 : Fin 3) 1) 1 = 0 ∧ (Equiv.swap (0 : Fin 3) 1) 2 = 2 := by decide
  have e4 : (Equiv.swap (0 : Fin 3) 1 * Equiv.swap 1 2 : Equiv.Perm (Fin 3)) 0 = 1 ∧
      (Equiv.swap (0 : Fin 3) 1 * Equiv.swap 1 2 : Equiv.Perm (Fin 3)) 1 = 2 ∧
      (Equiv.swap (0 : Fin 3) 1 * Equiv.swap 1 2 : Equiv.Perm (Fin 3)) 2 = 0 := by decide
  have e5 : (Equiv.swap (1 : Fin 3) 2 * Equiv.swap 0 1 : Equiv.Perm (Fin 3)) 0 = 2 ∧
      (Equiv.swap (1 : Fin 3) 2 * Equiv.swap 0 1 : Equiv.Perm (Fin 3)) 1 = 0 ∧
      (Equiv.swap (1 : Fin 3) 2 * Equiv.swap 0 1 : Equiv.Perm (Fin 3)) 2 = 1 := by decide
  have e6 : (Equiv.swap (0 : Fin 3) 2) 0 = 2 ∧ (Equiv.swap (0 : Fin 3) 2) 1 = 1 ∧ (Equiv.swap (0 : Fin 3) 2) 2 = 0 := by decide
  rw [e1.1, e1.2.1, e1.2.2, e2.1, e2.2.1, e2.2.2, e3.1, e3.2.1, e3.2.2, e4.1, e4.2.1, e4.2.2, e5.1, e5.2.1, e5.2.2,
    e6.1, e6.2.1, e6.2.2]
  unfold polarizationSum
  ring
theorem expUnit_zero : expUnit (0 : imaginaryQuaternions) = 1 := by apply _root_.YangMills.Construction.TorusFields.expUnit_zero <;> assumption
theorem expUnit_mul_smul (α β : ℝ) (z : imaginaryQuaternions) :
    expUnit (α • z) * expUnit (β • z) = expUnit ((α + β) • z) := by
  let +nondep : NormedAlgebra ℚ ℍ[ℝ] := .restrictScalars ℚ ℝ ℍ[ℝ]
  apply Subtype.ext
  have hc : Commute (((α • z : imaginaryQuaternions)) : ℍ[ℝ]) ((β • z : imaginaryQuaternions) : ℍ[ℝ]) := by
    have : Commute (z : ℍ[ℝ]) (z : ℍ[ℝ]) := Commute.refl _
    simpa using (this.smul_left α).smul_right β
  have h := NormedSpace.exp_add_of_commute hc
  have e : (((α + β) • z : imaginaryQuaternions) : ℍ[ℝ]) =
      ((α • z : imaginaryQuaternions) : ℍ[ℝ]) + ((β • z : imaginaryQuaternions) : ℍ[ℝ]) := by
    simp [add_smul]
  change NormedSpace.exp ((α • z : imaginaryQuaternions) : ℍ[ℝ]) *
      NormedSpace.exp ((β • z : imaginaryQuaternions) : ℍ[ℝ]) =
    NormedSpace.exp (((α + β) • z : imaginaryQuaternions) : ℍ[ℝ])
  rw [e, h]
theorem bondSpread_smul (c : Fin 3 → F.Site j × Fin 4) (X : Fin 3 → imaginaryQuaternions) (α : ℝ)
    (v : TripleParam) (y : F.Site j) (i : Fin 4) :
    bondSpread c X (α • v) y i = α • bondSpread c X v y i := by
  simp only [ColdStepAtMirrorFrames.bondSpread, Finset.smul_sum, Pi.smul_apply, smul_eq_mul]
  refine Finset.sum_congr rfl fun l _ => ?_
  split_ifs
  · rw [mul_smul]
  · simp
def bondSpreadCLM (c : Fin 3 → F.Site j × Fin 4) (X : Fin 3 → imaginaryQuaternions) (y : F.Site j) (i : Fin 4) :
    TripleParam →L[ℝ] imaginaryQuaternions :=
  ∑ l : Fin 3, (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 3 => ℝ) l).smulRight
    (if c l = (y, i) then X l else 0)
theorem bondSpreadCLM_apply (c : Fin 3 → F.Site j × Fin 4) (X : Fin 3 → imaginaryQuaternions) (y : F.Site j)
    (i : Fin 4) (τ : TripleParam) :
    bondSpreadCLM c X y i τ = bondSpread c X τ y i := by
  simp only [bondSpreadCLM, ColdStepAtMirrorFrames.bondSpread, ContinuousLinearMap.sum_apply, ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.proj_apply]
  refine Finset.sum_congr rfl fun l _ => ?_
  split_ifs <;> simp
def firstHalf : (Fin (3 + 3) → ℝ) →L[ℝ] TripleParam :=
  ContinuousLinearMap.pi fun i => ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (3 + 3) => ℝ) (Fin.castAdd 3 i)
def secondHalf : (Fin (3 + 3) → ℝ) →L[ℝ] TripleParam :=
  ContinuousLinearMap.pi fun i => ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (3 + 3) => ℝ) (Fin.natAdd 3 i)
def joinHalves : PairParam →L[ℝ] (Fin (3 + 3) → ℝ) :=
  ContinuousLinearMap.pi fun l => Fin.addCases
    (motive := fun _ => PairParam →L[ℝ] ℝ)
    (fun i => (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 3 => ℝ) i).comp
      (ContinuousLinearMap.fst ℝ TripleParam TripleParam))
    (fun i => (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 3 => ℝ) i).comp
      (ContinuousLinearMap.snd ℝ TripleParam TripleParam)) l
theorem firstHalf_joinHalves (q : PairParam) : firstHalf (joinHalves q) = q.1 := by
  funext i
  simp [firstHalf, joinHalves]
theorem secondHalf_joinHalves (q : PairParam) : secondHalf (joinHalves q) = q.2 := by
  funext i
  simp only [secondHalf, joinHalves, ContinuousLinearMap.coe_pi', ContinuousLinearMap.proj_apply, Fin.addCases_right]
  rfl
def pairSpreadCLM (c : Fin 3 → F.Site j × Fin 4) (X : Fin 3 → imaginaryQuaternions) (y : F.Site j) (i : Fin 4) :
    (Fin (3 + 3) → ℝ) →L[ℝ] imaginaryQuaternions × imaginaryQuaternions × imaginaryQuaternions :=
  ((bondSpreadCLM c X y i).comp firstHalf).prod (((bondSpreadCLM c X y i).comp secondHalf).prod 0)
def composedMotion (Θ : imaginaryQuaternions × imaginaryQuaternions × imaginaryQuaternions → imaginaryQuaternions)
    (c : Fin 3 → F.Site j × Fin 4) (X : Fin 3 → imaginaryQuaternions)
    (τ : Fin (3 + 3) → ℝ) : F.Site j → Fin 4 → imaginaryQuaternions :=
  fun y i => Θ (pairSpreadCLM c X y i τ)
def doubleTranslate (G : F.GaugeField j → ℝ) (W : F.GaugeField j) (c : Fin 3 → F.Site j × Fin 4)
    (X : Fin 3 → imaginaryQuaternions) (q : PairParam) : ℝ :=
  G (leftTranslate (bondSpread c X q.1) (leftTranslate (bondSpread c X q.2) W))
theorem contDiffAt_doubleTranslate (hL : Estimates.SmoothAlongMotion)
    (hLog : ColdStepAtMirrorFrames.ConjugatedExpLogSmooth)
    (G : F.GaugeField j → ℝ) (W : F.GaugeField j) (c : Fin 3 → F.Site j × Fin 4) (X : Fin 3 → imaginaryQuaternions)
    (hper : ∀ i, F.period j i ≠ 0)
    (hG : ∀ (q : ℕ) (c' : Fin q → F.Site j × Fin 4) (X' : Fin q → imaginaryQuaternions),
      ContDiffAt ℝ 3 (fun τ : Fin q → ℝ => G (leftTranslate (bondSpread c' X' τ) W)) 0) :
    ContDiffAt ℝ ((3 : ℕ) : WithTop ℕ∞) (doubleTranslate G W c X) 0 := by
  classical
  obtain ⟨Θ, U, C₀, hU, hC₀, hdiag, hsm, hexp, hzero, -, -, -⟩ := hLog
  have h00 : diagonalTriple 0 = (0 : imaginaryQuaternions × imaginaryQuaternions × imaginaryQuaternions) := rfl
  have h0U : (0 : imaginaryQuaternions × imaginaryQuaternions × imaginaryQuaternions) ∈ U := by
    rw [← h00]
    exact hdiag 0
  have hs3 : ContDiffAt ℝ ((3 : ℕ) : WithTop ℕ∞) Θ 0 := hsm.contDiffAt (hU.mem_nhds h0U)
  have hΘ0 : Θ 0 = 0 := by
    rw [← h00]
    exact hzero 0
  have hfin : Finite (F.Site j) := by
    have : ∀ i, Finite (ZMod (F.period j i)) := fun i => by
      have : NeZero (F.period j i) := ⟨hper i⟩
      infer_instance
    exact Pi.finite
  have hαs : ∀ x b, ContDiffAt ℝ ((3 : ℕ) : WithTop ℕ∞) (fun τ => composedMotion Θ c X τ x b) 0 := by
    intro x b
    have h0 : ContDiffAt ℝ ((3 : ℕ) : WithTop ℕ∞) Θ (pairSpreadCLM c X x b 0) := by
      rw [map_zero]
      exact hs3
    exact ContDiffAt.comp (0 : Fin (3 + 3) → ℝ) h0 (pairSpreadCLM c X x b).contDiff.contDiffAt
  have hα0 : ∀ x b, composedMotion Θ c X 0 x b = 0 := by
    intro x b
    simp [composedMotion, hΘ0]
  have hS := hL F j 3 (3 + 3) G W (composedMotion Θ c X) hper (fun q c' X' => hG q c' X') hαs hα0
  have hcomp : ContDiffAt ℝ ((3 : ℕ) : WithTop ℕ∞)
      (fun q : PairParam => G (leftTranslate (composedMotion Θ c X (joinHalves q)) W)) 0 := by
    have h0 : ContDiffAt ℝ ((3 : ℕ) : WithTop ℕ∞) (fun τ => G (leftTranslate (composedMotion Θ c X τ) W))
        (joinHalves (0 : PairParam)) := by
      rw [map_zero]
      exact hS
    exact ContDiffAt.comp (g := fun τ => G (leftTranslate (composedMotion Θ c X τ) W)) (f := joinHalves)
      (0 : PairParam) h0 joinHalves.contDiff.contDiffAt
  have hnear : ∀ᶠ q in 𝓝 (0 : PairParam), ∀ y i, pairSpreadCLM c X y i (joinHalves q) ∈ U := by
    refine Filter.eventually_all.2 fun y => Filter.eventually_all.2 fun i => ?_
    exact ((pairSpreadCLM c X y i).comp joinHalves).continuous.continuousAt.eventually
      (hU.mem_nhds (by simpa using h0U))
  refine hcomp.congr_of_eventuallyEq ?_
  filter_upwards [hnear] with q hq
  have : leftTranslate (bondSpread c X q.1) (leftTranslate (bondSpread c X q.2) W) =
      leftTranslate (composedMotion Θ c X (joinHalves q)) W := by
    funext y i
    simp only [leftTranslate, composedMotion]
    rw [hexp _ (hq y i)]
    simp only [pairSpreadCLM, ContinuousLinearMap.prod_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.zero_apply, firstHalf_joinHalves, secondHalf_joinHalves, bondSpreadCLM_apply,
      expUnit_zero, inv_one, mul_one, mul_assoc]
  unfold doubleTranslate
  rw [this]
theorem bondSpread_single (c : Fin 3 → F.Site j × Fin 4) (X : Fin 3 → imaginaryQuaternions) (l : Fin 3)
    (y : F.Site j) (i : Fin 4) :
    bondSpread c X (Pi.single l 1) y i = if c l = (y, i) then X l else 0 := by
  simp only [ColdStepAtMirrorFrames.bondSpread]
  rw [Finset.sum_eq_single l]
  · simp
  · intro l' _ hl
    simp [Pi.single_eq_of_ne hl]
  · simp
theorem bondSpread_one_eq (c : Fin 3 → F.Site j × Fin 4) (X : Fin 3 → imaginaryQuaternions) (l : Fin 3)
    (σ : Fin 1 → ℝ) :
    bondSpread (fun _ : Fin 1 => c l) (fun _ => X l) σ = bondSpread c X (σ 0 • (Pi.single l 1 : TripleParam)) := by
  funext y i
  rw [bondSpread_smul, bondSpread_single]
  simp only [ColdStepAtMirrorFrames.bondSpread, Finset.univ_unique, Finset.sum_singleton]
  have e : (default : Fin 1) = 0 := rfl
  rw [e]
  split_ifs <;> simp
theorem bondSpread_two_eq (c : Fin 3 → F.Site j × Fin 4) (X : Fin 3 → imaginaryQuaternions) (l₁ l₂ : Fin 3)
    (r : Fin 2 → ℝ) :
    bondSpread ![c l₁, c l₂] ![X l₁, X l₂] r =
      bondSpread c X (r 0 • (Pi.single l₁ 1 : TripleParam) + r 1 • (Pi.single l₂ 1 : TripleParam)) := by
  funext y i
  rw [← bondSpreadCLM_apply, map_add, bondSpreadCLM_apply, bondSpreadCLM_apply, bondSpread_smul, bondSpread_smul,
    bondSpread_single, bondSpread_single]
  have e : bondSpread ![c l₁, c l₂] ![X l₁, X l₂] r y i = (if c l₁ = (y, i) then r 0 • X l₁ else 0) +
      (if c l₂ = (y, i) then r 1 • X l₂ else 0) := by
    simp only [ColdStepAtMirrorFrames.bondSpread]
    rw [Fin.sum_univ_two]
    rfl
  rw [e]
  congr 1 <;> split_ifs <;> simp
theorem doubleTranslate_smul_smul (G : F.GaugeField j → ℝ) (W : F.GaugeField j) (c : Fin 3 → F.Site j × Fin 4)
    (X : Fin 3 → imaginaryQuaternions) (v : TripleParam) (α β : ℝ) :
    doubleTranslate G W c X (α • v, β • v) = G (leftTranslate (bondSpread c X ((α + β) • v)) W) := by
  unfold doubleTranslate
  congr 1
  funext y i
  simp only [leftTranslate, bondSpread_smul]
  rw [← mul_assoc, expUnit_mul_smul, add_smul]
def diagonalLineCLM (v : TripleParam) : ℝ × ℝ →L[ℝ] PairParam :=
  ((ContinuousLinearMap.fst ℝ ℝ ℝ).smulRight v).prod ((ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight v)
def sumLineCLM (v : TripleParam) : ℝ × ℝ →L[ℝ] TripleParam :=
  (ContinuousLinearMap.fst ℝ ℝ ℝ + ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight v
def outerSlotsCLM (l₁ l₂ : Fin 3) : (Fin 2 → ℝ) →L[ℝ] PairParam :=
  (0 : (Fin 2 → ℝ) →L[ℝ] TripleParam).prod
    ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) 0).smulRight (Pi.single l₁ 1) +
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) 1).smulRight (Pi.single l₂ 1))
theorem derivAlong_ordered_eq (hL : DerivAlongRulesHold) (G : F.GaugeField j → ℝ) (W : F.GaugeField j)
    (c : Fin 3 → F.Site j × Fin 4) (X : Fin 3 → imaginaryQuaternions)
    (hA : ContDiffAt ℝ ((3 : ℕ) : WithTop ℕ∞) (doubleTranslate G W c X) 0)
    (l₀ l₁ l₂ : Fin 3) :
    derivAlong (doubleTranslate G W c X) [((Pi.single l₀ 1 : TripleParam), (0 : TripleParam)),
      ((0 : TripleParam), (Pi.single l₁ 1 : TripleParam)), ((0 : TripleParam), (Pi.single l₂ 1 : TripleParam))] 0 =
    bondDeriv (fun W' => bondDeriv G W' (fun _ : Fin 1 => c l₀) (fun _ => X l₀)) W ![c l₁, c l₂] ![X l₁, X l₂] := by
  set A := doubleTranslate G W c X with hAd
  set h0 : PairParam := ((Pi.single l₀ 1 : TripleParam), (0 : TripleParam)) with hh0
  have R := hL.1 PairParam ℝ
  have R2 := hL.1 (Fin 2 → ℝ) ℝ
  have hH : ContDiffAt ℝ ((2 : ℕ) : WithTop ℕ∞) (derivAlong A [h0]) 0 := R.contDiffAt A 0 2 [h0] (by simpa using hA)
  set ρ := outerSlotsCLM l₁ l₂ with hρ
  have hdq : ∀ᶠ q in 𝓝 (0 : PairParam), ContDiffAt ℝ ((3 : ℕ) : WithTop ℕ∞) A q := hA.eventually (by simp)
  have hc : Filter.Tendsto ρ (𝓝 0) (𝓝 0) := by
    have := ρ.continuous.tendsto 0
    simpa using this
  have hev : (fun r' : Fin 2 → ℝ => bondDeriv G (leftTranslate (bondSpread ![c l₁, c l₂] ![X l₁, X l₂] r') W)
      (fun _ : Fin 1 => c l₀) (fun _ => X l₀)) =ᶠ[𝓝 0] fun r' => derivAlong A [h0] (0 + ρ r') := by
    filter_upwards [hc.eventually hdq] with r' hr'
    have hd : DifferentiableAt ℝ A (ρ r') := hr'.differentiableAt (by simp)
    have hline : HasFDerivAt (fun σ : Fin 1 → ℝ => ρ r' + σ 0 • h0)
        ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 1 => ℝ) 0).smulRight h0) 0 :=
      ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 1 => ℝ) 0).smulRight h0).hasFDerivAt.const_add _
    have hd' : HasFDerivAt A (fderiv ℝ A (ρ r')) (ρ r' + (0 : Fin 1 → ℝ) 0 • h0) := by
      simpa using hd.hasFDerivAt
    have hcomp := (hd'.comp (0 : Fin 1 → ℝ) hline).fderiv
    have efun : (fun σ : Fin 1 → ℝ => G (leftTranslate (bondSpread (fun _ : Fin 1 => c l₀) (fun _ => X l₀) σ)
        (leftTranslate (bondSpread ![c l₁, c l₂] ![X l₁, X l₂] r') W))) =
        A ∘ fun σ : Fin 1 → ℝ => ρ r' + σ 0 • h0 := by
      funext σ
      simp only [Function.comp, hAd, doubleTranslate, hρ, outerSlotsCLM, hh0, Prod.fst_add, Prod.snd_add,
        Prod.smul_fst, Prod.smul_snd, ContinuousLinearMap.prod_apply, zero_add, smul_zero, add_zero]
      rw [bondSpread_one_eq, bondSpread_two_eq]
      simp
    unfold bondDeriv
    rw [iteratedFDeriv_one_apply, efun, hcomp]
    simp [derivAlong]
  have hH' : ContDiffAt ℝ ((2 : ℕ) : WithTop ℕ∞) (fun r' => derivAlong A [h0] (0 + ρ r')) 0 := by
    have h0' : ContDiffAt ℝ ((2 : ℕ) : WithTop ℕ∞) (derivAlong A [h0]) (0 + ρ 0) := by simpa using hH
    exact ContDiffAt.comp (g := derivAlong A [h0]) (f := fun r' => 0 + ρ r') (0 : Fin 2 → ℝ) h0'
      (contDiff_const.add ρ.contDiff).contDiffAt
  have eR : bondDeriv (fun W' => bondDeriv G W' (fun _ : Fin 1 => c l₀) (fun _ => X l₀)) W ![c l₁, c l₂]
      ![X l₁, X l₂] =
      iteratedFDeriv ℝ 2 (fun r' : Fin 2 → ℝ => bondDeriv G
        (leftTranslate (bondSpread ![c l₁, c l₂] ![X l₁, X l₂] r') W)
        (fun _ : Fin 1 => c l₀) (fun _ => X l₀)) 0 (fun l => Pi.single l 1) := rfl
  rw [eR, (Filter.EventuallyEq.iteratedFDeriv ℝ hev 2).self_of_nhds, R2.iteratedFDeriv_eq _ _ _ _ hH']
  have e1 := hL.2 PairParam (Fin 2 → ℝ) ℝ (derivAlong A [h0]) ρ 0 0
    (List.ofFn fun l : Fin 2 => (Pi.single l (1 : ℝ) : Fin 2 → ℝ)) (by simpa using hH)
  rw [e1]
  simp only [map_zero, add_zero]
  rw [← R.append]
  have hlen : ((((List.map ρ (List.ofFn fun l : Fin 2 => (Pi.single l (1 : ℝ) : Fin 2 → ℝ))) ++ [h0]).length : ℕ) :
      WithTop ℕ∞) = ((3 : ℕ) : WithTop ℕ∞) := by simp
  rw [R.perm A 0 _ (h0 :: List.map ρ (List.ofFn fun l : Fin 2 => (Pi.single l (1 : ℝ) : Fin 2 → ℝ)))
    (List.perm_append_singleton _ _) (by rw [hlen]; exact hA)]
  have e2 : List.map ρ (List.ofFn fun l : Fin 2 => (Pi.single l (1 : ℝ) : Fin 2 → ℝ)) =
      [((0 : TripleParam), (Pi.single l₁ 1 : TripleParam)), ((0 : TripleParam), (Pi.single l₂ 1 : TripleParam))] := by
    simp [List.ofFn_succ, hρ, outerSlotsCLM]
  rw [e2]
end MeanOverOrders
open MeanOverOrders in
theorem thirdDerivEqMeanOverOrders (hL : DerivAlongRulesHold)
    (hM : Estimates.SmoothAlongMotion) (hLog : ColdStepAtMirrorFrames.ConjugatedExpLogSmooth) :
    ThirdDerivEqMeanOverOrders := by
  intro F j G W c X hper hG
  set A := doubleTranslate G W c X with hAd
  have hA : ContDiffAt ℝ ((3 : ℕ) : WithTop ℕ∞) A 0 := contDiffAt_doubleTranslate hM hLog G W c X hper hG
  set g : TripleParam → ℝ := fun τ => G (leftTranslate (bondSpread c X τ) W) with hgd
  have hg : ContDiffAt ℝ ((3 : ℕ) : WithTop ℕ∞) g 0 := hG 3 c X
  have R := hL.1 PairParam ℝ
  have R3 := hL.1 TripleParam ℝ
  set T : TripleParam → TripleParam → TripleParam → ℝ := fun a b d =>
    derivAlong A [(a, (0 : TripleParam)), ((0 : TripleParam), b), ((0 : TripleParam), d)] 0 with hT
  set T' : TripleParam → TripleParam → TripleParam → ℝ := fun a b d => derivAlong g [a, b, d] 0 with hT'
  have h1 : ∀ x x' y z, T (x + x') y z = T x y z + T x' y z := by
    intro x x' y z
    have := R.add_slot A 0 [] [((0 : TripleParam), y), ((0 : TripleParam), z)] (x, (0 : TripleParam))
      (x', (0 : TripleParam)) (by simpa using hA)
    simpa [hT, Prod.mk_add_mk] using this
  have h2 : ∀ x y y' z, T x (y + y') z = T x y z + T x y' z := by
    intro x y y' z
    have := R.add_slot A 0 [(x, (0 : TripleParam))] [((0 : TripleParam), z)] ((0 : TripleParam), y)
      ((0 : TripleParam), y') (by simpa using hA)
    simpa [hT, Prod.mk_add_mk] using this
  have h3 : ∀ x y z z', T x y (z + z') = T x y z + T x y z' := by
    intro x y z z'
    have := R.add_slot A 0 [(x, (0 : TripleParam)), ((0 : TripleParam), y)] [] ((0 : TripleParam), z)
      ((0 : TripleParam), z') (by simpa using hA)
    simpa [hT, Prod.mk_add_mk] using this
  have h1' : ∀ x x' y z, T' (x + x') y z = T' x y z + T' x' y z := by
    intro x x' y z
    have := R3.add_slot g 0 [] [y, z] x x' (by simpa using hg)
    simpa [hT'] using this
  have h2' : ∀ x y y' z, T' x (y + y') z = T' x y z + T' x y' z := by
    intro x y y' z
    have := R3.add_slot g 0 [x] [z] y y' (by simpa using hg)
    simpa [hT'] using this
  have h3' : ∀ x y z z', T' x y (z + z') = T' x y z + T' x y z' := by
    intro x y z z'
    have := R3.add_slot g 0 [x, y] [] z z' (by simpa using hg)
    simpa [hT'] using this
  have hdiag : ∀ v, T v v v = T' v v v := by
    intro v
    have a1 := hL.2 PairParam (ℝ × ℝ) ℝ A (diagonalLineCLM v) 0 0
      [((1 : ℝ), (0 : ℝ)), ((0 : ℝ), (1 : ℝ)), ((0 : ℝ), (1 : ℝ))] (by simpa using hA)
    have a2 := hL.2 TripleParam (ℝ × ℝ) ℝ g (sumLineCLM v) 0 0
      [((1 : ℝ), (0 : ℝ)), ((0 : ℝ), (1 : ℝ)), ((0 : ℝ), (1 : ℝ))] (by simpa using hg)
    have e : (fun t' : ℝ × ℝ => A (0 + diagonalLineCLM v t')) = fun t' => g (0 + sumLineCLM v t') := by
      funext t'
      simp only [zero_add, diagonalLineCLM, sumLineCLM, hAd, hgd, ContinuousLinearMap.prod_apply,
        ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.add_apply, ContinuousLinearMap.coe_fst',
        ContinuousLinearMap.coe_snd']
      exact doubleTranslate_smul_smul G W c X v t'.1 t'.2
    rw [e, a2] at a1
    simpa [diagonalLineCLM, sumLineCLM, hT, hT', Prod.mk_zero_zero] using a1.symm
  set e : Fin 3 → TripleParam := fun l => Pi.single l 1 with he
  have hp := polarizationSum_eq T T' h1 h2 h3 h1' h2' h3' hdiag (e 0) (e 1) (e 2)
  have s1 : ∀ a b d, T' a b d = T' b a d := by
    intro a b d
    exact R3.perm g 0 _ _ (List.Perm.swap _ _ _) (by simpa using hg)
  have s2 : ∀ a b d, T' a b d = T' a d b := by
    intro a b d
    exact R3.perm g 0 _ _ ((List.Perm.swap _ _ _).cons _) (by simpa using hg)
  have hs : polarizationSum T' (e 0) (e 1) (e 2) = 6 * T' (e 0) (e 1) (e 2) := by
    have a2 : T' (e 0) (e 2) (e 1) = T' (e 0) (e 1) (e 2) := (s2 _ _ _).symm
    have a3 : T' (e 1) (e 0) (e 2) = T' (e 0) (e 1) (e 2) := (s1 _ _ _).symm
    have a4 : T' (e 1) (e 2) (e 0) = T' (e 0) (e 1) (e 2) := (s2 _ _ _).trans a3
    have a5 : T' (e 2) (e 0) (e 1) = T' (e 0) (e 1) (e 2) := (s1 _ _ _).trans a2
    have a6 : T' (e 2) (e 1) (e 0) = T' (e 0) (e 1) (e 2) := (s1 _ _ _).trans a4
    unfold polarizationSum
    rw [a2, a3, a4, a5, a6]
    ring
  have hm : bondDeriv G W c X = T' (e 0) (e 1) (e 2) := by
    change iteratedFDeriv ℝ 3 g 0 (fun l => Pi.single l 1) = _
    rw [R3.iteratedFDeriv_eq _ _ _ _ hg]
    simp [List.ofFn_succ, hT', he]
  have ht : ∑ π : Equiv.Perm (Fin 3), bondDeriv (fun W' => bondDeriv G W' (fun _ : Fin 1 => c (π 0))
      (fun _ => X (π 0))) W ![c (π 1), c (π 2)] ![X (π 1), X (π 2)] = polarizationSum T (e 0) (e 1) (e 2) := by
    have : ∀ π : Equiv.Perm (Fin 3), bondDeriv (fun W' => bondDeriv G W' (fun _ : Fin 1 => c (π 0))
        (fun _ => X (π 0))) W ![c (π 1), c (π 2)] ![X (π 1), X (π 2)] = T (e (π 0)) (e (π 1)) (e (π 2)) :=
      fun π => (derivAlong_ordered_eq hL G W c X hA _ _ _).symm
    simp only [this]
    exact sum_perm_eq_polarizationSum fun a b d => T (e a) (e b) (e d)
  rw [hm, ht, hp, hs]
  ring
end ThirdDerivative
end YangMills.Construction
end
