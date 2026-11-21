import YangMills.Construction.ClusterExpansionOfAStep.TopFamiliesOnToriProof
import YangMills.Construction.FreeEnergiesOfTheFlow.MeansGivenAStateReadTheCasesProof
import YangMills.Construction.ClusterExpansionOfAStep.ShareOfALevelIsTheShareBelow
import YangMills.Construction.ColdStepAtMirrorFrames.ColdExpansionIsAnExpansionBelow
import YangMills.Construction.ResponseInTheExpansion.ColdImageIsLinear
import YangMills.Construction.ResponseInTheExpansion.ImageOfOneAtABlockProof
import YangMills.Construction.ResponseInTheExpansion.MeanOfARemainderProof
import YangMills.Construction.ResponseInTheExpansion.RemainderOfTheResponseReturns
import YangMills.Construction.ResponseInTheExpansion.RemaindersOfAResponseOnOneTorus
import Mathlib
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
noncomputable section
open scoped Quaternion Topology
open MeasureTheory Filter
open YangMills.Construction.BlockAverages hiding bondSpread
open YangMills.Construction.ColdStepAtMirrorFrames
open YangMills.Construction.Interpolation YangMills.Construction.TorusFields YangMills.Construction.TorusLumps
open YangMills.Construction.StepCosts YangMills.Construction.StepSettings YangMills.Construction.StepGas
open YangMills.Construction.RenormalizationStepParameters YangMills.Construction.WeightedResponses
namespace YangMills.Construction.ResponseInTheExpansion
namespace RemainderBounds
section Frame
variable {F : BlockFrame}
theorem bondDeriv_add {G₁ G₂ : F.GaugeField F.top → ℝ} {V : F.GaugeField F.top} {k : ℕ}
    {c : Fin k → F.Site F.top × Fin 4} {X : Fin k → imaginaryQuaternions}
    (h₁ : ContDiffAt ℝ k (fun τ : Fin k → ℝ => G₁ (leftTranslate (bondSpread c X τ) V)) 0)
    (h₂ : ContDiffAt ℝ k (fun τ : Fin k → ℝ => G₂ (leftTranslate (bondSpread c X τ) V)) 0) :
    bondDeriv (fun V => G₁ V + G₂ V) V c X = bondDeriv G₁ V c X + bondDeriv G₂ V c X := by
  unfold bondDeriv
  have e : (fun τ : Fin k → ℝ => G₁ (leftTranslate (bondSpread c X τ) V) + G₂ (leftTranslate (bondSpread c X τ) V)) =
      (fun τ : Fin k → ℝ => G₁ (leftTranslate (bondSpread c X τ) V)) +
        fun τ => G₂ (leftTranslate (bondSpread c X τ) V) := rfl
  rw [e, iteratedFDeriv_add_apply h₁ h₂]
  rfl
theorem bondDeriv_const_mul (a : ℝ) {G : F.GaugeField F.top → ℝ} {V : F.GaugeField F.top} {k : ℕ}
    {c : Fin k → F.Site F.top × Fin 4} {X : Fin k → imaginaryQuaternions}
    (h : ContDiffAt ℝ k (fun τ : Fin k → ℝ => G (leftTranslate (bondSpread c X τ) V)) 0) :
    bondDeriv (fun V => a * G V) V c X = a * bondDeriv G V c X := by
  unfold bondDeriv
  have e : (fun τ : Fin k → ℝ => a * G (leftTranslate (bondSpread c X τ) V)) =
      a • fun τ : Fin k → ℝ => G (leftTranslate (bondSpread c X τ) V) := by
    funext τ
    simp
  rw [e, iteratedFDeriv_const_smul_apply h]
  simp
theorem natCast_le_three {k : ℕ} (hk : k ≤ 3) : (k : WithTop ℕ∞) ≤ 3 := by
  exact_mod_cast hk
theorem abs_mul_le_two_mul {a u b : ℝ} (ha : |a| ≤ 2) (hu : |u| ≤ b) : |a * u| ≤ 2 * b := by
  rw [abs_mul]
  exact mul_le_mul ha hu (abs_nonneg _) (by norm_num)
theorem abs_add_four_le (a b c d : ℝ) : |a + b + c + d| ≤ |a| + |b| + |c| + |d| :=
  (abs_add_le _ _).trans (add_le_add_left ((abs_add_le _ _).trans (add_le_add_left (abs_add_le _ _) _)) _)
def fourTermSum (Q : ColdHalfLaw) (al : ℝ) (r r₂ : F.Site F.depth → F.GaugeField F.depth → ℝ)
    (w : F.Site F.depth → ℝ) (Y : F.Cell) (V : F.GaugeField F.top) : ℝ :=
  Q.expectationOf (Q.blockSum r Y) V + al * Q.weightedFrameShares w Y V +
    al * Q.expectationOf (Q.weightedShareIncrement w Y) V + Q.expectationOf (Q.blockSum r₂ Y) V
theorem fourTermSum_contDiff {Q : ColdHalfLaw} {al : ℝ} {r r₂ : F.Site F.depth → F.GaugeField F.depth → ℝ}
    {w : F.Site F.depth → ℝ} {Y : F.Cell} {V : F.GaugeField F.top}
    (h₁ : ContDiffThreeAlongBonds (Q.expectationOf (Q.blockSum r Y)) V)
    (h₂ : ContDiffThreeAlongBonds (Q.weightedFrameShares w Y) V)
    (h₃ : ContDiffThreeAlongBonds (Q.expectationOf (Q.weightedShareIncrement w Y)) V)
    (h₄ : ContDiffThreeAlongBonds (Q.expectationOf (Q.blockSum r₂ Y)) V) :
    ContDiffThreeAlongBonds (fourTermSum Q al r r₂ w Y) V := fun k c X =>
  (((h₁ k c X).add (contDiffAt_const.mul (h₂ k c X))).add (contDiffAt_const.mul (h₃ k c X))).add (h₄ k c X)
theorem bondDeriv_fourTermSum {Q : ColdHalfLaw} {al : ℝ} {r r₂ : F.Site F.depth → F.GaugeField F.depth → ℝ}
    {w : F.Site F.depth → ℝ} {Y : F.Cell} {V : F.GaugeField F.top}
    (h₁ : ContDiffThreeAlongBonds (Q.expectationOf (Q.blockSum r Y)) V)
    (h₂ : ContDiffThreeAlongBonds (Q.weightedFrameShares w Y) V)
    (h₃ : ContDiffThreeAlongBonds (Q.expectationOf (Q.weightedShareIncrement w Y)) V)
    (h₄ : ContDiffThreeAlongBonds (Q.expectationOf (Q.blockSum r₂ Y)) V) {k : ℕ} (hk : k ≤ 3)
    (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions) :
    bondDeriv (fourTermSum Q al r r₂ w Y) V c X = bondDeriv (Q.expectationOf (Q.blockSum r Y)) V c X +
      al * bondDeriv (Q.weightedFrameShares w Y) V c X +
      al * bondDeriv (Q.expectationOf (Q.weightedShareIncrement w Y)) V c X +
      bondDeriv (Q.expectationOf (Q.blockSum r₂ Y)) V c X := by
  have d₁ := (h₁ k c X).of_le (natCast_le_three hk)
  have d₂ := (h₂ k c X).of_le (natCast_le_three hk)
  have d₃ := (h₃ k c X).of_le (natCast_le_three hk)
  have d₄ := (h₄ k c X).of_le (natCast_le_three hk)
  have e₂ := bondDeriv_const_mul al d₂
  have e₃ := bondDeriv_const_mul al d₃
  have s₂ : ContDiffAt ℝ k
      (fun τ : Fin k → ℝ => al * Q.weightedFrameShares w Y (leftTranslate (bondSpread c X τ) V)) 0 :=
    contDiffAt_const.mul d₂
  have s₃ : ContDiffAt ℝ k
      (fun τ : Fin k → ℝ => al * Q.expectationOf (Q.weightedShareIncrement w Y) (leftTranslate (bondSpread c X τ) V)) 0 :=
    contDiffAt_const.mul d₃
  have a₁ := bondDeriv_add (G₁ := Q.expectationOf (Q.blockSum r Y))
    (G₂ := fun V => al * Q.weightedFrameShares w Y V) d₁ s₂
  have a₂ := bondDeriv_add (G₁ := fun V => Q.expectationOf (Q.blockSum r Y) V + al * Q.weightedFrameShares w Y V)
    (G₂ := fun V => al * Q.expectationOf (Q.weightedShareIncrement w Y) V) (d₁.add s₂) s₃
  have a₃ := bondDeriv_add (G₁ := fun V => Q.expectationOf (Q.blockSum r Y) V + al * Q.weightedFrameShares w Y V +
    al * Q.expectationOf (Q.weightedShareIncrement w Y) V) (G₂ := Q.expectationOf (Q.blockSum r₂ Y))
    ((d₁.add s₂).add s₃) d₄
  show bondDeriv (fun V => Q.expectationOf (Q.blockSum r Y) V + al * Q.weightedFrameShares w Y V +
    al * Q.expectationOf (Q.weightedShareIncrement w Y) V + Q.expectationOf (Q.blockSum r₂ Y) V) V c X = _
  rw [a₃, a₂, a₁, e₂, e₃]
theorem fourTermSum_bounds (T : ColdStepAtMirrorFrames.StepParameters) (hT : ColdRegimeEstimatesAt T)
    (hσ : 0 < T.σ) {t : ℕ} {x e e₂ B al : ℝ} {f : LocalFamily} (hx : T.coupling ≤ x)
    (hrow : IsRegularFamily T.L t T.n₀ T.σ T.decayRate T.E T.energyRatio f) (htop : IsCubicTopTorus T.L t T.n₀ F)
    (he : 0 ≤ e) (he₂ : 0 ≤ e₂) (hB : 0 ≤ B) (hal : |al| ≤ 2) {w : F.Site F.depth → ℝ} (hw : ∀ y, |w y| ≤ B)
    {r r₂ : F.Site F.depth → F.GaugeField F.depth → ℝ}
    (hr : IsTorusRemainder T.L T.σ T.decayRate e (e / T.η₃) r)
    (hr₂ : IsTorusRemainder T.L T.σ T.decayRate e₂ (e₂ / T.η₃) r₂) (Y : F.Cell) :
    (∀ V : F.GaugeField F.top, IsSmallCurvature (5 / 4 * T.σ) V →
      ContDiffThreeAlongBonds (fourTermSum (coldHalfLawAt T x f) al r r₂ w Y) V ∧
      ∀ (k : ℕ) (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions), 1 ≤ k → k ≤ 3 →
        AreUnitVectors X →
        |bondDeriv (fourTermSum (coldHalfLawAt T x f) al r r₂ w Y) V c X| ≤
          2⁻¹ ^ 7 * ((T.L : ℝ) * (if k = 3 then e / T.η₃ else e)) / torusDecayFactor T.L T.decayRate (bondSpan Y c) +
            T.CE * ((T.L : ℝ) * e / T.η₃) * x ^ (-(1 / 2) : ℝ) * Real.exp (-(T.κ / 2 ^ 5 * bondSpan Y c)) +
            2 * (T.Cs * B / torusDecayFactor T.L T.decayRate (bondSpan Y c)) +
            2 * (T.CE * (B * x ^ (-(1 / 2) : ℝ)) * Real.exp (-(T.κ / 2 ^ 5 * bondSpan Y c))) +
            T.CE * (e₂ / T.η₃) / torusDecayFactor T.L T.decayRate (bondSpan Y c)) ∧
    ∀ (V V' : F.GaugeField F.top) (q k : ℕ) (b : Fin k → (Fin 4 → ℤ) × Fin 4) (X : Fin k → imaginaryQuaternions),
      IsSmallCurvature (9 / 8 * T.σ) V → IsSmallCurvature (9 / 8 * T.σ) V' →
      AgreeOnBall (finiteCells F) V (finiteCells F) V' Y Y q → k ≤ 2 →
      (∀ l, BlockAverages.BondWithinRadius q (b l)) → AreUnitVectors X →
      |bondDeriv (fourTermSum (coldHalfLawAt T x f) al r r₂ w Y) V (bondsAt Y b) X -
          bondDeriv (fourTermSum (coldHalfLawAt T x f) al r r₂ w Y) V' (bondsAt Y b) X| ≤
        2⁻¹ ^ 5 * ((T.L : ℝ) * e) / torusDecayFactor T.L T.decayRate q +
          2 * (T.Cs * B / torusDecayFactor T.L T.decayRate q) +
          2 * (T.CE * (B * x ^ (-(1 / 2) : ℝ)) * Real.exp (-(2 * T.decayRate * q))) +
          T.CE * (e₂ / T.η₃) / torusDecayFactor T.L T.decayRate q := by
  obtain ⟨b1, b2⟩ := hT.blockRemainder t x e f F r Y hx hrow htop he hr
  obtain ⟨s1, s2⟩ := hT.frameShares t x B f F Y w hx htop hB hw
  obtain ⟨m1, m2⟩ := (hT.smoothIncrements t x f hx hrow).2.2.2.2.2 F Y w B hB hw htop
  obtain ⟨r1, r2⟩ := hT.meanRemainder t x e₂ f F r₂ Y hx hrow htop he₂ hr₂
  have hcold : ∀ {V : F.GaugeField F.top}, IsSmallCurvature (9 / 8 * T.σ) V →
      IsSmallCurvature (5 / 4 * T.σ) V := by
    intro V hV p hp
    exact (hV p hp).trans (by linarith)
  refine ⟨fun V hV => ⟨fourTermSum_contDiff (b1 V hV).1 (s1 V hV).1 (m1 V hV).1 (r1 V hV).1,
    fun k c X h1 h3 hX => ?_⟩, fun V V' q k b X hV hV' hA hk hb hX => ?_⟩
  · rw [bondDeriv_fourTermSum (b1 V hV).1 (s1 V hV).1 (m1 V hV).1 (r1 V hV).1 h3]
    have t₁ := (b1 V hV).2 k c X h1 h3 hX
    have t₂ := (s1 V hV).2 k c X h1 h3 hX
    have t₃ := (m1 V hV).2 k c X h1 h3 hX
    have t₄ := (r1 V hV).2 k c X h1 h3 hX
    have u₂ := abs_mul_le_two_mul hal t₂
    have u₃ := abs_mul_le_two_mul hal t₃
    refine (abs_add_four_le _ _ _ _).trans ?_
    linarith
  · have c₁ := hcold hV
    have c₂ := hcold hV'
    have hk3 : k ≤ 3 := by omega
    rw [bondDeriv_fourTermSum (b1 V c₁).1 (s1 V c₁).1 (m1 V c₁).1 (r1 V c₁).1 hk3,
      bondDeriv_fourTermSum (b1 V' c₂).1 (s1 V' c₂).1 (m1 V' c₂).1 (r1 V' c₂).1 hk3]
    have t₁ := b2 V V' q k b X hV hV' hA hk hb hX
    have t₂ := s2 V V' q k b X hV hV' hA hk hb hX
    have t₃ := m2 V V' q k b X hV hV' hA hk hb hX
    have t₄ := r2 V V' q k b X hV hV' hA hk hb hX
    have u₂ := abs_mul_le_two_mul hal t₂
    have u₃ := abs_mul_le_two_mul hal t₃
    have e : ∀ A₁ A₂ A₃ A₄ B₁ B₂ B₃ B₄ : ℝ, A₁ + al * A₂ + al * A₃ + A₄ - (B₁ + al * B₂ + al * B₃ + B₄) =
        (A₁ - B₁) + al * (A₂ - B₂) + al * (A₃ - B₃) + (A₄ - B₄) := by
      intros
      ring
    rw [e]
    refine (abs_add_four_le _ _ _ _).trans ?_
    linarith
end Frame
section Weights
theorem abs_clamp_sub_le (b u v : ℝ) : |max (-b) (min b u) - max (-b) (min b v)| ≤ |u - v| := by
  have h1 := abs_max_sub_max_le_abs (min b u) (min b v) (-b)
  have h2 := abs_min_sub_min_le_max b u b v
  rw [max_comm (-b), max_comm (-b)]
  refine h1.trans (h2.trans ?_)
  simp
theorem abs_clamp_le {b : ℝ} (hb : 0 ≤ b) (u : ℝ) : |max (-b) (min b u)| ≤ b :=
  abs_le.2 ⟨le_max_left _ _, max_le (by linarith) (min_le_left _ _)⟩
theorem clamp_eq_of_abs_le {b u : ℝ} (hu : |u| ≤ b) : max (-b) (min b u) = u := by apply _root_.YangMills.DeltaSharedProofs.p15858 <;> assumption
def clampedShift {m : ℕ} (b c : ℝ) (h : PlaquetteWeight m) : PlaquetteWeight m :=
  fun p => max (-b) (min b (h p - c))
variable {L t m : ℕ}
theorem barycentreDist_nonneg (p p' : TorusPlaquette m) : 0 ≤ barycentreDist L t p p' := by
  unfold barycentreDist
  positivity
theorem weightLipschitz_clampedShift_le (b c : ℝ) (h : PlaquetteWeight m) [Finite (TorusPlaquette m)] :
    weightLipschitz L t (clampedShift b c h) ≤ weightLipschitz L t h := by
  unfold weightLipschitz
  rcases isEmpty_or_nonempty (OrientedPlaquette m × OrientedPlaquette m) with he | hne
  · simp
  · refine ciSup_mono (Set.finite_range _).bddAbove fun pp => ?_
    refine div_le_div_of_nonneg_right ?_ (barycentreDist_nonneg _ _)
    have h1 := abs_clamp_sub_le b (h pp.1.1 - c) (h pp.2.1 - c)
    have e : h pp.1.1 - c - (h pp.2.1 - c) = h pp.1.1 - h pp.2.1 := by ring
    rwa [e] at h1
theorem weightSup_clampedShift_le {b : ℝ} (hb : 0 ≤ b) (c : ℝ) (h : PlaquetteWeight m) :
    weightSup (clampedShift b c h) ≤ b :=
  Real.iSup_le (fun _ => abs_clamp_le hb _) hb
theorem side_mul_weightLipschitz (hL : 0 < L) (h : PlaquetteWeight m) :
    (L : ℝ) * weightLipschitz L t h = weightLipschitz L (t + 1) h := by
  have hL' : (0 : ℝ) < L := by exact_mod_cast hL
  unfold weightLipschitz
  rw [Real.mul_iSup_of_nonneg hL'.le]
  refine congrArg _ (funext fun pp => ?_)
  have e : barycentreDist L (t + 1) pp.1.1 pp.2.1 = barycentreDist L t pp.1.1 pp.2.1 / L := by
    unfold barycentreDist
    rw [pow_succ]
    field_simp
  rw [e, div_div_eq_mul_div]
  ring
end Weights
section Means
open YangMills.Construction.Dilation
variable {ι : Type} [Fintype ι] [DecidableEq ι] {ρ : ℝ} {r : ℝ → ℝ} {Ψ : BondField ι → ℝ}
def IntegrableAgainst (r : ℝ → ℝ) (Ψ g : BondField ι → ℝ) : Prop :=
  Integrable fun η => g η * ballDensity r Ψ η
theorem ballExpectation_congr_on_balls (hL : IsBallLaw ρ r Ψ) {f g : BondField ι → ℝ}
    (h : ∀ η : BondField ι, (∀ b, ‖η b‖ < ρ) → f η = g η) : ballExpectation r Ψ f = ballExpectation r Ψ g := by
  unfold ballExpectation
  congr 1
  refine integral_congr_ae (Eventually.of_forall fun η => ?_)
  by_cases hη : ∀ b, ‖η b‖ < ρ
  · simp only [h η hη]
  · simp only [hL.eq_zero_outside η hη, mul_zero]
theorem IntegrableAgainst.congr {f g : BondField ι → ℝ} (hL : IsBallLaw ρ r Ψ) (hf : IntegrableAgainst r Ψ f)
    (h : ∀ η : BondField ι, (∀ b, ‖η b‖ < ρ) → f η = g η) : IntegrableAgainst r Ψ g := by
  refine Integrable.congr hf (Eventually.of_forall fun η => ?_)
  by_cases hη : ∀ b, ‖η b‖ < ρ
  · simp only [h η hη]
  · simp only [hL.eq_zero_outside η hη, mul_zero]
theorem IntegrableAgainst.add {f g : BondField ι → ℝ} (hf : IntegrableAgainst r Ψ f)
    (hg : IntegrableAgainst r Ψ g) : IntegrableAgainst r Ψ fun η => f η + g η := by
  refine Integrable.congr (Integrable.add hf hg) (Eventually.of_forall fun η => ?_)
  simp only [Pi.add_apply, add_mul]
theorem IntegrableAgainst.const_mul {f : BondField ι → ℝ} (a : ℝ) (hf : IntegrableAgainst r Ψ f) :
    IntegrableAgainst r Ψ fun η => a * f η := by
  refine Integrable.congr (Integrable.const_mul hf a) (Eventually.of_forall fun η => ?_)
  simp only [mul_assoc]
theorem IntegrableAgainst.const (hL : IsBallLaw ρ r Ψ) (a : ℝ) : IntegrableAgainst r Ψ fun _ => a :=
  hL.integrable.const_mul a
theorem IntegrableAgainst.sum {J : Type} (S : Finset J) {f : J → BondField ι → ℝ} (hL : IsBallLaw ρ r Ψ)
    (h : ∀ j ∈ S, IntegrableAgainst r Ψ (f j)) : IntegrableAgainst r Ψ fun η => ∑ j ∈ S, f j η := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa using IntegrableAgainst.const hL 0
  | insert a S ha ih =>
    simp only [Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self _ _)).add (ih fun j hj => h j (Finset.mem_insert_of_mem hj))
theorem ballExpectation_finset_sum {J : Type} (S : Finset J) {f : J → BondField ι → ℝ} (hL : IsBallLaw ρ r Ψ)
    (h : ∀ j ∈ S, IntegrableAgainst r Ψ (f j)) :
    ballExpectation r Ψ (fun η => ∑ j ∈ S, f j η) = ∑ j ∈ S, ballExpectation r Ψ (f j) := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa using ballExpectation_const hL 0
  | insert a S ha ih =>
    simp only [Finset.sum_insert ha]
    have h₁ := h a (Finset.mem_insert_self _ _)
    have h₂ : ∀ j ∈ S, IntegrableAgainst r Ψ (f j) := fun j hj => h j (Finset.mem_insert_of_mem hj)
    rw [ballExpectation_add hL h₁ (IntegrableAgainst.sum S hL h₂), ih h₂]
theorem integrableAgainst_of_bounded (hL : IsBallLaw ρ r Ψ) {H g : BondField ι → ℝ} (hg : Measurable g) {C : ℝ}
    (hb : ∀ η : BondField ι, (∀ b, ‖η b‖ < ρ) → |H η| ≤ C)
    (he : ∀ η : BondField ι, (∀ b, ‖η b‖ < ρ) → H η = g η) : IntegrableAgainst r Ψ H := by
  set O : Set (BondField ι) := {η | ∀ b, ‖η b‖ < ρ} with hO
  have hOm : MeasurableSet O := (isOpen_openBallProduct ρ).measurableSet
  have hG : AEStronglyMeasurable (O.indicator g) volume := (hg.indicator hOm).aestronglyMeasurable
  have hbd : ∀ η, ‖O.indicator g η‖ ≤ |C| := by
    intro η
    by_cases h : η ∈ O
    · rw [Set.indicator_of_mem h, Real.norm_eq_abs, ← he η h]
      exact (hb η h).trans (le_abs_self C)
    · rw [Set.indicator_of_notMem h, norm_zero]
      exact abs_nonneg C
  have h1 := hL.integrable.bdd_mul (c := |C|) hG (Eventually.of_forall hbd)
  refine h1.congr (Eventually.of_forall fun η => ?_)
  by_cases h : η ∈ O
  · simp only [Set.indicator_of_mem h, he η h]
  · simp only [Set.indicator_of_notMem h, hL.eq_zero_outside η h, mul_zero, zero_mul]
end Means
section Torus
variable {n : ℕ}
theorem perturb_zero {k : ℕ} (c : Fin k → TorusBond n) (X : Fin k → imaginaryQuaternions) (W : TorusField n) :
    perturb c X 0 W = W := by apply _root_.YangMills.Construction.TorusFields.perturb_zero <;> assumption
theorem abs_centered_le {ℓ : TorusLumps.StepParameters} {E E₃ : ℝ} {f : LocalDensity}
    (hf : ColdDensityBounds ℓ E E₃ f) (hσ : 0 < ℓ.threshold) {m : ℕ} [NeZero m]
    (hm : ℓ.n₀ ≤ m) (h3 : 2 < m) (y : TorusSite m) {W : TorusField m} (hW : IsCold ℓ.threshold W) :
    |centered f m y W| ≤ E / ℓ.weight 0 := by apply _root_.YangMills.Construction.ResponseInTheExpansion.BlockImageOfOne.abs_centered_le_of_isCold <;> assumption
end Torus
section Step
open YangMills.Construction.Dilation
variable {R : StepSetup} {n : ℕ} [NeZero n]
abbrev stepFrame (R : StepSetup) (n : ℕ) : BlockFrame := torusFrame R.params.side R.depth n
theorem period_depth_eq (i : Fin 4) :
    (stepFrame R n).period (stepFrame R n).depth i = n * R.params.side :=
  TopLevelSites.period_depth i
theorem readAtLevel_restrictToTorus (W : (stepFrame R n).GaugeField (stepFrame R n).depth) :
    readAtLevel (stepFrame R n) (stepFrame R n).depth (restrictToTorus (n * R.params.side) W) = W := by
  funext y i
  show W (torusSiteInFrame (stepFrame R n) (stepFrame R n).depth (toTorusSite (n * R.params.side) y)) i = W y i
  rw [TopLevelSites.torusSiteInFrame_toTorusSite period_depth_eq]
def levelWeight (h : PlaquetteWeight (fineSide R.params.side R.depth (n * R.params.side)))
    (y : (stepFrame R n).Site (stepFrame R n).depth) : ℝ :=
  blockMean R.params.side R.depth (n * R.params.side) (toTorusSite (n * R.params.side) y) h
theorem blockExpectations_eq_fourTermSum (A : ResponseSetup R) (hr : A.IsAdmissible) (hσ : 0 < R.params.threshold)
    (hm : R.params.n₀ ≤ n * R.params.side) (hm3 : 2 < n * R.params.side) (V : TorusField n)
    (hlaw : IsBallLaw R.ballRadius (coldHalfLawOf R).radialWeight
      ((coldHalfLawOf R).exponent (coldTopField R V)))
    (hcont : Continuous (coldFieldAboveFrames R V))
    (hcold : ∀ k : StepVariable (finiteCells (stepFrame R n)), (∀ b, ‖k b‖ < R.ballRadius) →
      IsCold R.params.threshold (coldFieldAboveFrames R V k))
    (hC : ∀ G : TorusField (n * R.params.side) → ℝ,
      (∀ W, IsCold R.params.threshold W → ContDiffThreeAt G W) →
      ContinuousOn (fun k => G (coldFieldAboveFrames R V k))
        {k : StepVariable (finiteCells (stepFrame R n)) | ∀ b, ‖k b‖ < R.ballRadius})
    (hsum : open Classical in ∀ (g : (stepFrame R n).Site (stepFrame R n).depth → ℝ) (Y : TorusSite n),
      ∑ y ∈ (sitesOfCells (finiteCells (stepFrame R n)) (stepFrame R n).depth).filter
          (fun y => enclosingCell y = torusSiteInFrame (stepFrame R n) (stepFrame R n).top Y), g y =
        ∑ x ∈ sitesInBlocks R.params.side {Y}, g (torusSiteInFrame (stepFrame R n) (stepFrame R n).depth x))
    (hshare : ∀ W : TorusField (n * R.params.side), IsCold R.params.threshold W →
      ∀ y : TorusSite (n * R.params.side),
      levelShare R.params.coupling R.params.side R.depth Finset.univ y W =
        minimalSiteShare (F := stepFrame R n) R.params.coupling
          (torusSiteInFrame (stepFrame R n) (stepFrame R n).depth y)
          (readAtLevel (stepFrame R n) (stepFrame R n).depth W))
    (hρ : 0 < R.ballRadius) (Y : TorusSite n)
    (h : PlaquetteWeight (fineSide R.params.side R.depth (n * R.params.side))) :
    ∑ x ∈ sitesInBlocks R.params.side {Y},
        coldExpectationAbove R V (fun W => centeredResponse A.cold (n * R.params.side) x W h) +
        ∑ x ∈ sitesInBlocks R.params.side {Y}, A.cold (n * R.params.side) x (trivialField (n * R.params.side)) h =
      fourTermSum (coldHalfLawOf R) A.coeff (remainderOnFrame A.cold (stepFrame R n) (n * R.params.side) h)
          (weightedCenteredOnFrame A.siteRemainder (stepFrame R n) (n * R.params.side) (levelWeight h))
          (levelWeight h) (torusSiteInFrame (stepFrame R n) (stepFrame R n).top Y) (coldTopField R V) +
        ∑ x ∈ sitesInBlocks R.params.side {Y}, blockMean R.params.side R.depth (n * R.params.side) x h *
          A.cold (n * R.params.side) x (trivialField (n * R.params.side)) (constOneWeight _) := by
  classical
  have hwt : ∀ x : TorusSite (n * R.params.side),
      levelWeight h (torusSiteInFrame (stepFrame R n) (stepFrame R n).depth x) =
      blockMean R.params.side R.depth (n * R.params.side) x h := fun x => by
    unfold levelWeight
    rw [TopLevelSites.toTorusSite_torusSiteInFrame period_depth_eq]
  have fA : ∀ (x : TorusSite (n * R.params.side))
      (g : PlaquetteWeight (fineSide R.params.side R.depth (n * R.params.side))),
      IntegrableAgainst (coldHalfLawOf R).radialWeight ((coldHalfLawOf R).exponent (coldTopField R V))
        (fun k => centeredResponse A.cold (n * R.params.side) x (coldFieldAboveFrames R V k) g) := by
    intro x g
    refine integrableAgainst_of_bounded hlaw
      (g := fun k => (if IsCold R.params.threshold (coldFieldAboveFrames R V k) then
        A.cold (n * R.params.side) x (coldFieldAboveFrames R V k) g else 0) -
          A.cold (n * R.params.side) x (trivialField (n * R.params.side)) g)
      (((hr.bounds.cold_borel (n * R.params.side) hm x g).comp hcont.measurable).sub_const _)
      (C := A.responseParams.C₀ * weightNorm R.params.side R.depth g)
      (fun k hk => hr.bounds.size_cold _ hm x _ (hcold k hk) g) (fun k hk => ?_)
    simp only [if_pos (hcold k hk)]
    rfl
  have fD : ∀ x : TorusSite (n * R.params.side),
      IntegrableAgainst (coldHalfLawOf R).radialWeight ((coldHalfLawOf R).exponent (coldTopField R V))
      (fun k => centered A.siteRemainder (n * R.params.side) x (coldFieldAboveFrames R V k)) := by
    intro x
    refine integrable_mul_density_of_bounded hlaw (hC _ fun W hW k c X => ?_)
      (R := A.responseParams.Ka * R.coupling ^ (-(1 / 2) : ℝ) / R.params.weight 0)
      (fun k hk => abs_centered_le hr.bounds.site_family hσ hm hm3 x (hcold k hk))
    exact ((hr.bounds.site_family.smooth _ hm x W hW) k c X).sub contDiffAt_const
  have hk0 : ∀ b, ‖(0 : StepVariable (finiteCells (stepFrame R n))) b‖ < R.ballRadius := fun b => by
    simpa using hρ
  have shr : ∀ k : StepVariable (finiteCells (stepFrame R n)), (∀ b, ‖k b‖ < R.ballRadius) →
      ∀ x : TorusSite (n * R.params.side),
      minimalSiteShare (F := stepFrame R n) R.params.coupling
          (torusSiteInFrame (stepFrame R n) (stepFrame R n).depth x)
        (interpolatedField 1 R.params.coupling R.anchorRadius R.frameReach (coldTopField R V) k) =
        levelShare R.params.coupling R.params.side R.depth Finset.univ x (coldFieldAboveFrames R V k) := by
    intro k hk x
    rw [hshare _ (hcold k hk) x]
    show _ = minimalSiteShare _ _ (readAtLevel _ _ (restrictToTorus _ _))
    rw [readAtLevel_restrictToTorus]
  have sB1 : ∀ k : StepVariable (finiteCells (stepFrame R n)),
      (coldHalfLawOf R).blockSum (remainderOnFrame A.cold (stepFrame R n) (n * R.params.side) h)
        (torusSiteInFrame (stepFrame R n) (stepFrame R n).top Y) k (coldTopField R V) =
        ∑ x ∈ sitesInBlocks R.params.side {Y},
          responseRemainder A.cold (n * R.params.side) x h (coldFieldAboveFrames R V k) := by
    intro k
    refine (hsum (fun y => remainderOnFrame A.cold (stepFrame R n) (n * R.params.side) h y
      (interpolatedField 1 R.params.coupling R.anchorRadius R.frameReach (coldTopField R V) k)) Y).trans
      (Finset.sum_congr rfl fun x _ => ?_)
    show responseRemainder A.cold _ (toTorusSite _ (torusSiteInFrame _ _ x)) h _ = _
    rw [TopLevelSites.toTorusSite_torusSiteInFrame period_depth_eq]
    rfl
  have sB2 : ∀ k : StepVariable (finiteCells (stepFrame R n)),
      (coldHalfLawOf R).blockSum
        (weightedCenteredOnFrame A.siteRemainder (stepFrame R n) (n * R.params.side) (levelWeight h))
        (torusSiteInFrame (stepFrame R n) (stepFrame R n).top Y) k (coldTopField R V) =
        ∑ x ∈ sitesInBlocks R.params.side {Y}, blockMean R.params.side R.depth (n * R.params.side) x h *
          centered A.siteRemainder (n * R.params.side) x (coldFieldAboveFrames R V k) := by
    intro k
    refine (hsum (fun y => weightedCenteredOnFrame A.siteRemainder (stepFrame R n) (n * R.params.side)
      (levelWeight h) y
      (interpolatedField 1 R.params.coupling R.anchorRadius R.frameReach (coldTopField R V) k)) Y).trans
      (Finset.sum_congr rfl fun x _ => ?_)
    show levelWeight h _ * centered A.siteRemainder _ (toTorusSite _ (torusSiteInFrame _ _ x)) _ = _
    rw [TopLevelSites.toTorusSite_torusSiteInFrame period_depth_eq, hwt]
    rfl
  have sS : (coldHalfLawOf R).weightedFrameShares (levelWeight h)
        (torusSiteInFrame (stepFrame R n) (stepFrame R n).top Y) (coldTopField R V) =
      ∑ x ∈ sitesInBlocks R.params.side {Y}, blockMean R.params.side R.depth (n * R.params.side) x h *
        levelShare R.params.coupling R.params.side R.depth Finset.univ x (coldFieldAboveFrames R V 0) := by
    refine (hsum (fun y => levelWeight h y * minimalSiteShare (F := stepFrame R n) R.params.coupling y
      (interpolatedField 1 R.params.coupling R.anchorRadius R.frameReach (coldTopField R V) 0)) Y).trans
      (Finset.sum_congr rfl fun x _ => ?_)
    show levelWeight h _ * minimalSiteShare _ _ _ = _
    rw [hwt, shr 0 hk0]
  have sM : ∀ k : StepVariable (finiteCells (stepFrame R n)), (∀ b, ‖k b‖ < R.ballRadius) →
      (coldHalfLawOf R).weightedShareIncrement (levelWeight h)
        (torusSiteInFrame (stepFrame R n) (stepFrame R n).top Y) k (coldTopField R V) =
        ∑ x ∈ sitesInBlocks R.params.side {Y}, blockMean R.params.side R.depth (n * R.params.side) x h *
          (levelShare R.params.coupling R.params.side R.depth Finset.univ x (coldFieldAboveFrames R V k) -
            levelShare R.params.coupling R.params.side R.depth Finset.univ x (coldFieldAboveFrames R V 0)) := by
    intro k hk
    refine (hsum (fun y => levelWeight h y * (minimalSiteShare (F := stepFrame R n) R.params.coupling y
      (interpolatedField 1 R.params.coupling R.anchorRadius R.frameReach (coldTopField R V) k) -
      minimalSiteShare (F := stepFrame R n) R.params.coupling y
      (interpolatedField 1 R.params.coupling R.anchorRadius R.frameReach (coldTopField R V) 0))) Y).trans
      (Finset.sum_congr rfl fun x _ => ?_)
    show levelWeight h _ * (minimalSiteShare _ _ _ - minimalSiteShare _ _ _) = _
    rw [hwt, shr k hk, shr 0 hk0]
  have hone : ∀ k : StepVariable (finiteCells (stepFrame R n)), (∀ b, ‖k b‖ < R.ballRadius) →
      ∀ x : TorusSite (n * R.params.side),
      centeredResponse A.cold (n * R.params.side) x (coldFieldAboveFrames R V k) (constOneWeight _) =
        A.coeff * levelShare R.params.coupling R.params.side R.depth Finset.univ x (coldFieldAboveFrames R V k) +
          centered A.siteRemainder (n * R.params.side) x (coldFieldAboveFrames R V k) :=
    fun k hk x => hr.bounds.share_site _ hm x _ (hcold k hk)
  have hpt : ∀ k : StepVariable (finiteCells (stepFrame R n)), (∀ b, ‖k b‖ < R.ballRadius) →
      ∑ x ∈ sitesInBlocks R.params.side {Y},
          centeredResponse A.cold (n * R.params.side) x (coldFieldAboveFrames R V k) h =
        (coldHalfLawOf R).blockSum (remainderOnFrame A.cold (stepFrame R n) (n * R.params.side) h)
            (torusSiteInFrame (stepFrame R n) (stepFrame R n).top Y) k (coldTopField R V) +
          A.coeff * (coldHalfLawOf R).weightedFrameShares (levelWeight h)
            (torusSiteInFrame (stepFrame R n) (stepFrame R n).top Y) (coldTopField R V) +
          A.coeff * (coldHalfLawOf R).weightedShareIncrement (levelWeight h)
            (torusSiteInFrame (stepFrame R n) (stepFrame R n).top Y) k (coldTopField R V) +
          (coldHalfLawOf R).blockSum
            (weightedCenteredOnFrame A.siteRemainder (stepFrame R n) (n * R.params.side) (levelWeight h))
            (torusSiteInFrame (stepFrame R n) (stepFrame R n).top Y) k (coldTopField R V) +
          ∑ x ∈ sitesInBlocks R.params.side {Y}, (blockMean R.params.side R.depth (n * R.params.side) x h *
            A.cold (n * R.params.side) x (trivialField (n * R.params.side)) (constOneWeight _) -
              A.cold (n * R.params.side) x (trivialField (n * R.params.side)) h) := by
    intro k hk
    rw [sB1, sS, sM k hk, sB2, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib,
      ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun x _ => ?_
    have hs := hone k hk x
    unfold centeredResponse at hs ⊢
    unfold responseRemainder
    linear_combination (blockMean R.params.side R.depth (n * R.params.side) x h) * hs
  have f1 : IntegrableAgainst (coldHalfLawOf R).radialWeight ((coldHalfLawOf R).exponent (coldTopField R V))
      fun k => (coldHalfLawOf R).blockSum (remainderOnFrame A.cold (stepFrame R n) (n * R.params.side) h)
        (torusSiteInFrame (stepFrame R n) (stepFrame R n).top Y) k (coldTopField R V) := by
    have g1 := IntegrableAgainst.sum (sitesInBlocks R.params.side {Y}) hlaw (f := fun x k =>
      (centeredResponse A.cold (n * R.params.side) x (coldFieldAboveFrames R V k) h +
        A.cold (n * R.params.side) x (trivialField (n * R.params.side)) h) +
      (-blockMean R.params.side R.depth (n * R.params.side) x h) *
        (centeredResponse A.cold (n * R.params.side) x (coldFieldAboveFrames R V k) (constOneWeight _) +
          A.cold (n * R.params.side) x (trivialField (n * R.params.side)) (constOneWeight _))) fun x _ =>
      ((fA x h).add (IntegrableAgainst.const hlaw _)).add
        (((fA x _).add (IntegrableAgainst.const hlaw _)).const_mul _)
    refine g1.congr hlaw fun k _ => ?_
    rw [sB1]
    refine Finset.sum_congr rfl fun x _ => ?_
    unfold centeredResponse responseRemainder
    ring
  have f2 : IntegrableAgainst (coldHalfLawOf R).radialWeight ((coldHalfLawOf R).exponent (coldTopField R V))
      fun k => (coldHalfLawOf R).blockSum
        (weightedCenteredOnFrame A.siteRemainder (stepFrame R n) (n * R.params.side) (levelWeight h))
        (torusSiteInFrame (stepFrame R n) (stepFrame R n).top Y) k (coldTopField R V) := by
    have g1 := IntegrableAgainst.sum (sitesInBlocks R.params.side {Y}) hlaw (f := fun x k =>
      blockMean R.params.side R.depth (n * R.params.side) x h *
        centered A.siteRemainder (n * R.params.side) x (coldFieldAboveFrames R V k)) fun x _ =>
      (fD x).const_mul _
    exact g1.congr hlaw fun k _ => (sB2 k).symm
  have f3 : IntegrableAgainst (coldHalfLawOf R).radialWeight ((coldHalfLawOf R).exponent (coldTopField R V))
      fun k => A.coeff * (coldHalfLawOf R).weightedShareIncrement (levelWeight h)
        (torusSiteInFrame (stepFrame R n) (stepFrame R n).top Y) k (coldTopField R V) := by
    have g1 := IntegrableAgainst.sum (sitesInBlocks R.params.side {Y}) hlaw (f := fun x k =>
      blockMean R.params.side R.depth (n * R.params.side) x h *
        ((centeredResponse A.cold (n * R.params.side) x (coldFieldAboveFrames R V k) (constOneWeight _) +
          (-1) * centered A.siteRemainder (n * R.params.side) x (coldFieldAboveFrames R V k)) +
        -(A.coeff * levelShare R.params.coupling R.params.side R.depth Finset.univ x
          (coldFieldAboveFrames R V 0)))) fun x _ =>
      (((fA x _).add ((fD x).const_mul _)).add (IntegrableAgainst.const hlaw _)).const_mul _
    refine g1.congr hlaw fun k hk => ?_
    rw [sM k hk, Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [hone k hk x]
    ring
  have hmean := ballExpectation_finset_sum (sitesInBlocks R.params.side {Y}) hlaw
    (f := fun x k => centeredResponse A.cold (n * R.params.side) x (coldFieldAboveFrames R V k) h)
    fun x _ => fA x h
  have e0 := ballExpectation_congr_on_balls hlaw hpt
  have c1 := IntegrableAgainst.const (ρ := R.ballRadius) (r := (coldHalfLawOf R).radialWeight)
    (Ψ := (coldHalfLawOf R).exponent (coldTopField R V)) hlaw
  rw [ballExpectation_add hlaw (((f1.add (c1 _)).add f3).add f2) (c1 _),
    ballExpectation_add hlaw ((f1.add (c1 _)).add f3) f2, ballExpectation_add hlaw (f1.add (c1 _)) f3,
    ballExpectation_add hlaw f1 (c1 _), ballExpectation_const hlaw, ballExpectation_const hlaw,
    ballExpectation_const_mul] at e0
  have e1 : ∑ x ∈ sitesInBlocks R.params.side {Y},
      coldExpectationAbove R V (fun W => centeredResponse A.cold (n * R.params.side) x W h) =
      ∑ x ∈ sitesInBlocks R.params.side {Y},
        ballExpectation (coldHalfLawOf R).radialWeight ((coldHalfLawOf R).exponent (coldTopField R V))
        (fun k => centeredResponse A.cold (n * R.params.side) x (coldFieldAboveFrames R V k) h) := rfl
  rw [e1, ← hmean, e0, Finset.sum_sub_distrib]
  show _ = (coldHalfLawOf R).expectation (coldTopField R V) _ + _ + _ + _ + _
  simp only [ColdHalfLaw.expectation, ColdHalfLaw.expectationOf]
  ring
end Step
section Read
open YangMills.Construction.TopLevelSites
variable {L t n : ℕ}
theorem period_top_eq (i : Fin 4) : (torusFrame L t n).period (torusFrame L t n).top i = n := period_top i
def bondsOnTop {k : ℕ} (L t : ℕ) (c : Fin k → TorusBond n) :
    Fin k → (torusFrame L t n).Site (torusFrame L t n).top × Fin 4 :=
  fun l => (torusSiteInFrame (torusFrame L t n) (torusFrame L t n).top (c l).1, (c l).2)
theorem readAtLevel_perturb [NeZero n] {k : ℕ} (c : Fin k → TorusBond n) (X : Fin k → imaginaryQuaternions)
    (σ : Fin k → ℝ) (V : TorusField n) :
    readAtLevel (torusFrame L t n) (torusFrame L t n).top (perturb c X σ V) =
      leftTranslate (bondSpread (bondsOnTop L t c) X σ) (readAtLevel (torusFrame L t n) (torusFrame L t n).top V) := by apply _root_.YangMills.Construction.TopFamilyEvaluations.readAtLevel_perturb <;> assumption
theorem mixedDeriv_readAtLevel [NeZero n] (G : (torusFrame L t n).GaugeField (torusFrame L t n).top → ℝ) {k : ℕ}
    (V : TorusField n) (c : Fin k → TorusBond n) (X : Fin k → imaginaryQuaternions) :
    mixedDeriv (fun W => G (readAtLevel (torusFrame L t n) (torusFrame L t n).top W)) V c X =
      bondDeriv G (readAtLevel (torusFrame L t n) (torusFrame L t n).top V) (bondsOnTop L t c) X := by apply _root_.YangMills.Construction.TopFamilyEvaluations.mixedDeriv_readAtLevel <;> assumption
theorem contDiffThreeAt_readAtLevel [NeZero n] {G : (torusFrame L t n).GaugeField (torusFrame L t n).top → ℝ}
    {V : TorusField n}
    (h : ContDiffThreeAlongBonds G (readAtLevel (torusFrame L t n) (torusFrame L t n).top V)) :
    ContDiffThreeAt (fun W => G (readAtLevel (torusFrame L t n) (torusFrame L t n).top W)) V := by
  intro k c X
  have e : (fun σ : Fin k → ℝ => G (readAtLevel (torusFrame L t n) (torusFrame L t n).top (perturb c X σ V))) =
      fun σ => G (leftTranslate (bondSpread (bondsOnTop L t c) X σ)
        (readAtLevel (torusFrame L t n) (torusFrame L t n).top V)) := by
    funext σ
    rw [readAtLevel_perturb]
  rw [e]
  exact h k _ X
theorem bondSpan_bondsOnTop [NeZero n] {k : ℕ} (y : TorusSite n) (c : Fin k → TorusBond n) :
    bondSpan (torusSiteInFrame (torusFrame L t n) (torusFrame L t n).top y) (bondsOnTop L t c) =
      supportDiam y c := by apply _root_.YangMills.Construction.TopFamilyEvaluations.bondSpan_frameBonds <;> assumption
theorem isSmallCurvature_readAtLevel [NeZero n] {s : ℝ} {V : TorusField n} (hV : IsCold s V) :
    IsSmallCurvature (F := torusFrame L t n) s (readAtLevel (torusFrame L t n) (torusFrame L t n).top V) := by apply _root_.YangMills.SharedProofs.p2155 <;> assumption
theorem mem_finiteCells_top [NeZero n] (z : (torusFrame L t n).Cell) : z ∈ finiteCells (torusFrame L t n) :=
  _root_.YangMills.Construction.TopLevelSites.mem_finiteCells (fun _ => Nat.pos_of_ne_zero (NeZero.ne n)) z
theorem agreeOnBall_readAtLevel [NeZero n] {W W' : TorusField n} {y : TorusSite n} {m : ℕ} (h1 : 2 * m + 2 < n)
    (hA : FieldsAgreeNear W W' y y m) :
    AgreeOnBall (finiteCells (torusFrame L t n)) (readAtLevel (torusFrame L t n) (torusFrame L t n).top W)
      (finiteCells (torusFrame L t n)) (readAtLevel (torusFrame L t n) (torusFrame L t n).top W')
      (torusSiteInFrame (torusFrame L t n) (torusFrame L t n).top y)
      (torusSiteInFrame (torusFrame L t n) (torusFrame L t n).top y) m := by
  refine ⟨fun _ => Or.inr h1, fun _ => Or.inr h1,
    fun _ _ => ⟨fun _ => _root_.YangMills.Construction.ResponseInTheExpansion.RemainderBounds.mem_finiteCells_top _, fun _ => _root_.YangMills.Construction.ResponseInTheExpansion.RemainderBounds.mem_finiteCells_top _⟩, fun c hc => ?_⟩
  have := hA c hc
  show W (toTorusSite n _) c.2 = W' (toTorusSite n _) c.2
  rw [toTorusSite_add period_top_eq, toTorusSite_torusSiteInFrame period_top_eq,
    toTorusSite_siteOfCoords period_top_eq]
  exact this
theorem bondsOnTop_bondFrom [NeZero n] {k : ℕ} (v : TorusSite n) (b : Fin k → (Fin 4 → ℤ) × Fin 4) :
    (bondsOnTop L t fun l => bondFrom v (b l)) =
      bondsAt (torusSiteInFrame (torusFrame L t n) (torusFrame L t n).top v) b := by apply _root_.YangMills.Construction.TopFamilyEvaluations.frameBonds_bondFrom <;> assumption
theorem eventually_isCold_perturb [NeZero n] {s : ℝ} {W : TorusField n} (hW : IsCold s W) {k : ℕ}
    (c : Fin k → TorusBond n) (X : Fin k → imaginaryQuaternions) :
    ∀ᶠ σ : Fin k → ℝ in 𝓝 0, IsCold s (perturb c X σ W) := by
  have hc : ∀ (x : TorusSite n) (i : Fin 4), Continuous fun σ : Fin k → ℝ => perturb c X σ W x i := fun x i => by
    unfold perturb
    refine (ResponseInTheExpansion.continuous_expUnit.comp ?_).mul continuous_const
    refine continuous_finsetSum _ fun l _ => ?_
    split_ifs
    · exact (continuous_apply l).smul continuous_const
    · exact continuous_const
  have hcv : ∀ (x : TorusSite n) (μ ν : Fin 4),
      Continuous fun σ : Fin k → ℝ => curvature (perturb c X σ W) x μ ν :=
    fun x μ ν => by
      unfold curvature holonomy
      exact ((continuous_subtype_val.comp ((((hc _ _).mul (hc _ _)).mul (hc _ _).inv).mul (hc _ _).inv)).sub
        continuous_const).norm
  refine Filter.eventually_all.2 fun x => Filter.eventually_all.2 fun μ => Filter.eventually_all.2 fun ν => ?_
  by_cases hμ : μ < ν
  · have h0 : curvature (perturb c X (0 : Fin k → ℝ) W) x μ ν < s := by
      rw [perturb_zero]
      exact hW x μ ν hμ
    filter_upwards [(hcv x μ ν).continuousAt.eventually_lt continuousAt_const h0] with σ hσ _ using hσ
  · exact Eventually.of_forall fun σ h => absurd h hμ
theorem decomposition_contDiff_mixedDeriv [NeZero n] {G A B : TorusField n → ℝ} {d s : ℝ} {W : TorusField n}
    (hW : IsCold s W) (hkey : ∀ V, IsCold s V → G V = A V + B V + d) (hA : ContDiffThreeAt A W)
    (hB : ContDiffThreeAt B W) :
    ContDiffThreeAt G W ∧ ∀ (k : ℕ) (c : Fin k → TorusBond n) (X : Fin k → imaginaryQuaternions), k ≤ 3 →
      mixedDeriv G W c X = mixedDeriv A W c X + mixedDeriv B W c X + mixedDeriv (fun _ => d) W c X := by
  have hev : ∀ {k : ℕ} (c : Fin k → TorusBond n) (X : Fin k → imaginaryQuaternions),
      (fun σ : Fin k → ℝ => G (perturb c X σ W)) =ᶠ[𝓝 0]
      fun σ => A (perturb c X σ W) + B (perturb c X σ W) + d := fun c X =>
    (eventually_isCold_perturb hW c X).mono fun σ h => hkey _ h
  refine ⟨fun k c X => (((hA k c X).add (hB k c X)).add contDiffAt_const).congr_of_eventuallyEq (hev c X),
    fun k c X hk => ?_⟩
  unfold mixedDeriv
  rw [((hev c X).iteratedFDeriv ℝ k).self_of_nhds]
  have a := (hA k c X).of_le (natCast_le_three hk)
  have b := (hB k c X).of_le (natCast_le_three hk)
  have e : (fun σ : Fin k → ℝ => A (perturb c X σ W) + B (perturb c X σ W) + d) =
      ((fun σ : Fin k → ℝ => A (perturb c X σ W)) + fun σ => B (perturb c X σ W)) + fun _ => d := rfl
  have ab : ContDiffAt ℝ k ((fun σ : Fin k → ℝ => A (perturb c X σ W)) + fun σ => B (perturb c X σ W)) 0 :=
    a.add b
  rw [e, iteratedFDeriv_add_apply ab contDiffAt_const, iteratedFDeriv_add_apply a b]
  rfl
theorem mixedDeriv_const {d : ℝ} {k : ℕ} (hk : k ≠ 0) (W : TorusField n) (c : Fin k → TorusBond n)
    (X : Fin k → imaginaryQuaternions) : mixedDeriv (fun _ => d) W c X = 0 := by
  unfold mixedDeriv
  rw [iteratedFDeriv_const_of_ne hk]
  rfl
end Read
section Numbers
theorem rpow_neg_half_mul_le {x M : ℝ} (hM : 0 ≤ M) (hx : (4 * M + 1) ^ 2 ≤ x) :
    x ^ (-(1 / 2) : ℝ) * M ≤ 1 / 4 := by
  have hx0 : 0 < x := lt_of_lt_of_le (by positivity) hx
  have h1 : 4 * M + 1 ≤ Real.sqrt x := (Real.le_sqrt' (by positivity)).2 hx
  have h2 : 0 < Real.sqrt x := by linarith
  rw [Real.rpow_neg hx0.le, ← Real.sqrt_eq_rpow, inv_mul_eq_div, div_le_iff₀ h2]
  linarith
theorem exp_neg_le_one_twelfth {u : ℝ} (hu : 11 ≤ u) : Real.exp (-u) ≤ 1 / 12 := by
  rw [Real.exp_neg, inv_eq_one_div]
  refine one_div_le_one_div_of_le (by norm_num) ?_
  have := Real.add_one_le_exp u
  linarith
theorem torusDecayFactor_pos (L : ℕ) (δ u : ℝ) : 0 < torusDecayFactor L δ u := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.AdmissibleParameters.torusDecayFactor_pos <;> assumption
theorem exp_neg_le_div_torusDecayFactor {L : ℕ} {δ Cw κ u : ℝ}
    (hw : torusDecayFactor L δ u ≤ Cw * Real.exp (2 * δ * u)) (hκ : 2 * δ ≤ κ) (hu : 0 ≤ u) :
    Real.exp (-(κ * u)) ≤ Cw / torusDecayFactor L δ u := by apply _root_.YangMills.Construction.ResponseInTheExpansion.RemainderExpectation.exp_neg_le_div_torusDecayFactor <;> assumption
theorem derivative_estimate {Kk Kc lip G Le Lek η Cs CE Cw Ka xs ex g : ℝ} (hG : 0 < G) (hlip : 0 ≤ lip)
    (hη : 0 < η) (hKc : 0 ≤ Kc) (hCE : 0 ≤ CE) (hxs : 0 ≤ xs) (hLe : Le ≤ Kc * lip) (hLek : Lek ≤ Kk * lip)
    (hex : ex ≤ Cw / G) (hex0 : 0 ≤ ex)
    (hbr : 2⁻¹ ^ 7 * Kk + xs * (CE * Kc / η * Cw + 6 * CE * Cw + 3 * CE * Ka / η) + 6 * Cs + 3 * g ≤ Kk) :
    2⁻¹ ^ 7 * Lek / G + CE * (Le / η) * xs * ex + 2 * (Cs * (3 * lip) / G) + 2 * (CE * (3 * lip * xs) * ex) +
      CE * (3 * lip * (Ka * xs) / η) / G + g * (3 * lip) / G ≤ Kk * lip / G := by
  have hP : 0 ≤ lip / G := div_nonneg hlip hG.le
  have t₁ : 2⁻¹ ^ 7 * Lek / G ≤ 2⁻¹ ^ 7 * (Kk * lip) / G := by gcongr
  have t₂ : CE * (Le / η) * xs * ex ≤ CE * (Kc * lip / η) * xs * (Cw / G) := by gcongr
  have t₄ : 2 * (CE * (3 * lip * xs) * ex) ≤ 2 * (CE * (3 * lip * xs) * (Cw / G)) := by gcongr
  have e : 2⁻¹ ^ 7 * (Kk * lip) / G + CE * (Kc * lip / η) * xs * (Cw / G) + 2 * (Cs * (3 * lip) / G) +
      2 * (CE * (3 * lip * xs) * (Cw / G)) + CE * (3 * lip * (Ka * xs) / η) / G + g * (3 * lip) / G =
      (lip / G) * (2⁻¹ ^ 7 * Kk + xs * (CE * Kc / η * Cw + 6 * CE * Cw + 3 * CE * Ka / η) + 6 * Cs + 3 * g) := by
    field_simp
    ring
  have e₂ : Kk * lip / G = (lip / G) * Kk := by ring
  have h := mul_le_mul_of_nonneg_left hbr hP
  rw [e₂]
  linarith
theorem difference_le_of_bounds {Kc lip G Le η Cs CE Cw Ka xs ex g : ℝ} (hG : 0 < G) (hlip : 0 ≤ lip) (hη : 0 < η)
    (hCE : 0 ≤ CE) (hxs : 0 ≤ xs) (hLe : Le ≤ Kc * lip) (hex : ex ≤ Cw / G)
    (hbr : 2⁻¹ ^ 5 * Kc + xs * (6 * CE * Cw + 3 * CE * Ka / η) + 6 * Cs + 3 * g ≤ Kc) :
    2⁻¹ ^ 5 * Le / G + 2 * (Cs * (3 * lip) / G) + 2 * (CE * (3 * lip * xs) * ex) +
      CE * (3 * lip * (Ka * xs) / η) / G + g * (3 * lip) / G ≤ Kc * lip / G := by
  have hP : 0 ≤ lip / G := div_nonneg hlip hG.le
  have t₁ : 2⁻¹ ^ 5 * Le / G ≤ 2⁻¹ ^ 5 * (Kc * lip) / G := by gcongr
  have t₄ : 2 * (CE * (3 * lip * xs) * ex) ≤ 2 * (CE * (3 * lip * xs) * (Cw / G)) := by gcongr
  have e : 2⁻¹ ^ 5 * (Kc * lip) / G + 2 * (Cs * (3 * lip) / G) + 2 * (CE * (3 * lip * xs) * (Cw / G)) +
      CE * (3 * lip * (Ka * xs) / η) / G + g * (3 * lip) / G =
      (lip / G) * (2⁻¹ ^ 5 * Kc + xs * (6 * CE * Cw + 3 * CE * Ka / η) + 6 * Cs + 3 * g) := by
    field_simp
    ring
  have e₂ : Kc * lip / G = (lip / G) * Kc := by ring
  have h := mul_le_mul_of_nonneg_left hbr hP
  rw [e₂]
  linarith
end Numbers
end RemainderBounds
open RemainderBounds YangMills.Construction.TopLevelSites YangMills.Construction.Dilation in
theorem responseRemainderBounds_holds (hImg : coldStepAboveFramesStatement)
    (hLaw : coldHalfLawIsLawStatement) (hLin : coldStepLinearLocalStatement)
    (hOne : ResponseRemaindersOnTorus) (hGas : WeightedResponses.GasTermAtColdFields)
    (hWN : WeightedResponses.WeightsCloseToBlockMeans) (hMW : WeightedResponses.BlockMeanIsLinearAndLocal)
    (hExp : LinearResponse.DecayFactorExpBound) (hSh : ShareEvaluation.LevelShareEqMinimalSiteShare)
    (hRow : ColdStepAtMirrorFrames.ColdExpansionRegular) (hCS : StepSettings.ColdChartSettingIsCold) :
    responseRemainderBoundsStatement := by
  classical
  intro a _
  obtain ⟨r₁, hr₁, hI⟩ := hImg
  obtain ⟨r₂, hr₂, hL⟩ := hLin
  obtain ⟨r₃, hr₃, hG⟩ := hGas
  refine ⟨0, fun c => min (r₁ c) (min (r₂ c) (r₃ c)), fun c => lt_min (hr₁ c) (lt_min (hr₂ c) (hr₃ c)), ?_⟩
  intro T _ _ hD hCold hCH hrt
  obtain ⟨cn, nss, hties, hall⟩ := hCH
  obtain ⟨-, -, e_ρ, -, -, -, -, -⟩ := hties
  have hTs : ColdRegimeEstimatesAt (T.stepParamsAt cn nss T.yC) := hall T.yC le_rfl
  have hLpos : 0 < T.side := lt_of_lt_of_le (by norm_num) hD.L_ge
  have hδ : 0 < T.rt / 2 ^ 10 := by
    have := hD.rt_pos
    positivity
  obtain ⟨Cw, hCw1, hCw⟩ := hExp T.side (T.rt / 2 ^ 10) hLpos hδ
  refine ⟨12 * T.Cs + 2, fun K hKc => ?_⟩
  obtain ⟨y₁, hy₁⟩ := hI T hD (hrt.trans (min_le_left _ _)) K
  obtain ⟨y₂, hy₂⟩ := hL T hD (hrt.trans ((min_le_right _ _).trans (min_le_left _ _))) K
  obtain ⟨y₃, hy₃⟩ := hG T hD (hrt.trans ((min_le_right _ _).trans (min_le_right _ _))) K
  obtain ⟨y₄, hy₄⟩ := hLaw T hD hCold
  obtain ⟨y₅, hy₅⟩ := hCS T hD
  let Ts : ColdStepAtMirrorFrames.StepParameters := T.stepParamsAt cn nss T.yC
  let Mx : ℝ := Ts.CE * K.Kc / Ts.η₃ * Cw + 6 * Ts.CE * Cw + 3 * Ts.CE * K.Ka / Ts.η₃
  have hch : 0 < T.gasRate := by
    have h1 := hD.cE_pos
    have h2 : 0 < T.threshold := hD.σ_pos
    have h3 : 0 < T.κ := hD.κ_pos
    have h4 : 0 < T.κ₁ := lt_min (by positivity) (by positivity)
    have h5 : 0 < min T.cE (min (T.κ * T.threshold ^ 2) (T.κ₁ * T.threshold ^ 2)) :=
      lt_min h1 (lt_min (by positivity) (by positivity))
    unfold RenormalizationStepParameters.ParameterAssignment.gasRate
    positivity
  refine ⟨max (max y₁ y₂) (max (max y₃ y₄) (max (max y₅ T.yC)
    (max T.floorMin (max ((4 * |Mx| + 1) ^ 2) (22 / T.gasRate))))), ?_⟩
  intro y hy R A hK hA hArr
  have f₁ : y₁ ≤ y := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hy
  have f₂ : y₂ ≤ y := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hy
  have g₁ := le_trans (le_max_right _ _) hy
  have f₃ : y₃ ≤ y := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) g₁
  have f₄ : y₄ ≤ y := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) g₁
  have g₂ := le_trans (le_max_right _ _) g₁
  have f₅ : y₅ ≤ y := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) g₂
  have fC : T.yC ≤ y := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) g₂
  have g₃ := le_trans (le_max_right _ _) g₂
  have f₀ : T.floorMin ≤ y := le_trans (le_max_left _ _) g₃
  have g₄ := le_trans (le_max_right _ _) g₃
  have fM : (4 * |Mx| + 1) ^ 2 ≤ y := le_trans (le_max_left _ _) g₄
  have fh : 22 / T.gasRate ≤ y := le_trans (le_max_right _ _) g₄
  have hI' := hy₁ y f₁ R A hK hA hCold
  have hL' := hy₂ y f₂ R A hK hA
  have hG' := hy₃ y f₃ R A hK hA hArr
  have hlaw' := hy₄ y f₄ R hA.onFamily
  have hcs' := hy₅ y f₅ R hA.onFamily
  have hresp := hA.admissible
  have hstep := hA.onFamily.isStep
  have hx : y ≤ R.coupling := hA.onFamily.le_coupling
  obtain ⟨ℓ, t, x, x', D, f, Λ, Dq, Φ, φ, ρA, p⟩ := R
  have e1 : ℓ = T.stepParameters y := hA.onFamily.params_eq
  have e2 : ρA = T.ρA := hA.onFamily.anchorRadius_eq
  have e3 : p = T.cutoff := hA.onFamily.barrierFn_eq
  subst e1 e2 e3
  let R : StepSetup := ⟨T.stepParameters y, t, x, x', D, f, Λ, Dq, Φ, φ, T.ρA, T.cutoff⟩
  have hσ : 0 < T.threshold := hD.σ_pos
  have hfits := hD.fits y f₀
  have hyx : y ≤ x := hx
  have hbelow : IsRegularFamily Ts.L t Ts.n₀ Ts.σ Ts.decayRate Ts.E Ts.energyRatio (localFamilyOfDensity f) :=
    hRow (T.stepParameters y) t x D f hfits rfl hstep.1.1
  have hxT : Ts.coupling ≤ x := fC.trans hx
  have hq : coldHalfLawAt Ts x (localFamilyOfDensity f) = coldHalfLawOf R := by
    show ColdHalfLaw.mk T.coupling cn.ρA _ x T.rt (frameRadius x) T.cutoff _ =
      ColdHalfLaw.mk T.coupling T.ρA _ x T.rt _ T.cutoff _
    rw [e_ρ]
    rfl
  have hKf : K.Admissible R.params := hK ▸ hresp.params_admissible
  have hrowK : ResponseBounds R.params K R.depth R.coupling A.coeff R.labels R.labelWeight A.score A.cold A.hull
      A.siteRemainder A.totalRemainder := hK ▸ hresp.bounds
  have hη₃ : K.η₃ = Ts.η₃ := by
    have h1 : T.E₃ = T.E / K.η₃ := hKf.E₃_eq
    have h2 : T.E₃ = T.E / T.η₃ := rfl
    have hE : 0 < T.E := hfits.E_pos
    have h3 := hKf.η₃_pos
    have h4 := hD.η₃_pos
    rw [h2, div_eq_div_iff h4.ne' h3.ne'] at h1
    exact mul_left_cancel₀ hE.ne' h1
  have hη₀ : 0 < Ts.η₃ := hD.η₃_pos
  have hη₁ : Ts.η₃ ≤ 1 := hD.η₃_le
  have hKc1 : 1 ≤ K.Kc := hKf.Kc_ge
  have hKa : 0 ≤ K.Ka := hKf.Ka_nonneg
  have hCE : 0 ≤ Ts.CE := hD.CE_pos.le
  have hCs : 0 < Ts.Cs := hD.Cs_pos
  have hCw0 : 0 ≤ Cw := by linarith
  have hx0 : 0 < x := by
    have h1 : 0 < (4 * |Mx| + 1) ^ 2 := by positivity
    linarith
  have hxs : 0 ≤ x ^ (-(1 / 2) : ℝ) := Real.rpow_nonneg hx0.le _
  have hMx : x ^ (-(1 / 2) : ℝ) * Mx ≤ 1 / 4 := by
    have h1 := rpow_neg_half_mul_le (abs_nonneg Mx) (fM.trans hx)
    exact (mul_le_mul_of_nonneg_left (le_abs_self Mx) hxs).trans h1
  have hg : Real.exp (-(T.gasRate * x / 2)) ≤ 1 / 12 := by
    refine exp_neg_le_one_twelfth ?_
    have h1 : 22 ≤ y * T.gasRate := (div_le_iff₀ hch).1 fh
    nlinarith
  have hg0 : 0 ≤ Real.exp (-(T.gasRate * x / 2)) := (Real.exp_pos _).le
  have hal := hresp.abs_coeff_le
  have hwgt : ∀ s : ℕ, torusDecayFactor (T.stepParameters y).side Ts.decayRate s = (T.stepParameters y).weight s :=
    fun s => rfl
  have hLodd : Odd R.params.side := hD.L_odd
  have hL1 : (1 : ℝ) ≤ (T.side : ℝ) := by exact_mod_cast hLpos
  have hn₀ : 4096 ≤ T.n₀ := hD.n₀_ge
  have main : ∀ (n : ℕ) [NeZero n], R.params.n₀ ≤ n → ∀ (Y : TorusSite n)
      (h : PlaquetteWeight (fineSide R.params.side (R.depth + 1) n)),
      ∃ (H : (torusFrame R.params.side R.depth n).GaugeField (torusFrame R.params.side R.depth n).top → ℝ)
        (h₁ : PlaquetteWeight (fineSide R.params.side (R.depth + 1) n)) (d : ℝ),
        (∀ V : TorusField n, IsCold R.params.threshold V → responseRemainder A.coldStep n Y h V =
          H (readAtLevel (torusFrame R.params.side R.depth n) (torusFrame R.params.side R.depth n).top V) +
            gasTermAtBlock A (coldCaseGround R V) Y h₁ + d) ∧
        weightNorm R.params.side R.depth h₁ ≤ 3 * weightLipschitz R.params.side (R.depth + 1) h ∧
        0 ≤ weightLipschitz R.params.side (R.depth + 1) h ∧
        (∀ V : TorusField n, IsCold R.params.threshold V →
          ContDiffThreeAlongBonds H
            (readAtLevel (torusFrame R.params.side R.depth n) (torusFrame R.params.side R.depth n).top V)) ∧
        (∀ V : TorusField n, IsCold R.params.threshold V → ∀ (k : ℕ)
          (c : Fin k → (torusFrame R.params.side R.depth n).Site (torusFrame R.params.side R.depth n).top × Fin 4)
          (X : Fin k → imaginaryQuaternions), 1 ≤ k → k ≤ 3 → AreUnitVectors X →
          |bondDeriv H (readAtLevel (torusFrame R.params.side R.depth n) (torusFrame R.params.side R.depth n).top V)
              c X| +
            Real.exp (-(T.gasRate * x / 2)) * (3 * weightLipschitz R.params.side (R.depth + 1) h) /
              torusDecayFactor Ts.L Ts.decayRate
                (bondSpan (torusSiteInFrame (torusFrame R.params.side R.depth n)
                  (torusFrame R.params.side R.depth n).top Y) c) ≤
            (if k = 3 then K.Kc / K.η₃ else K.Kc) * weightLipschitz R.params.side (R.depth + 1) h /
              torusDecayFactor Ts.L Ts.decayRate
                (bondSpan (torusSiteInFrame (torusFrame R.params.side R.depth n)
                  (torusFrame R.params.side R.depth n).top Y) c)) ∧
        ∀ (V V' : TorusField n) (q k : ℕ) (b : Fin k → (Fin 4 → ℤ) × Fin 4) (X : Fin k → imaginaryQuaternions),
          IsCold R.params.threshold V → IsCold R.params.threshold V' →
          AgreeOnBall (finiteCells (torusFrame R.params.side R.depth n))
            (readAtLevel (torusFrame R.params.side R.depth n) (torusFrame R.params.side R.depth n).top V)
            (finiteCells (torusFrame R.params.side R.depth n))
            (readAtLevel (torusFrame R.params.side R.depth n) (torusFrame R.params.side R.depth n).top V')
            (torusSiteInFrame (torusFrame R.params.side R.depth n) (torusFrame R.params.side R.depth n).top Y)
            (torusSiteInFrame (torusFrame R.params.side R.depth n) (torusFrame R.params.side R.depth n).top Y) q →
          k ≤ 2 → (∀ l, BlockAverages.BondWithinRadius q (b l)) → AreUnitVectors X →
          |bondDeriv H (readAtLevel (torusFrame R.params.side R.depth n) (torusFrame R.params.side R.depth n).top V)
              (bondsAt (torusSiteInFrame (torusFrame R.params.side R.depth n)
                (torusFrame R.params.side R.depth n).top Y) b) X -
            bondDeriv H
              (readAtLevel (torusFrame R.params.side R.depth n) (torusFrame R.params.side R.depth n).top V')
              (bondsAt (torusSiteInFrame (torusFrame R.params.side R.depth n)
                (torusFrame R.params.side R.depth n).top Y) b) X| +
            Real.exp (-(T.gasRate * x / 2)) * (3 * weightLipschitz R.params.side (R.depth + 1) h) /
              torusDecayFactor Ts.L Ts.decayRate q ≤
            K.Kc * weightLipschitz R.params.side (R.depth + 1) h / torusDecayFactor Ts.L Ts.decayRate q := by
    intro n _ hn Y h
    have hnT : T.n₀ ≤ n := hn
    have hm : R.params.n₀ ≤ n * R.params.side := hn.trans (Nat.le_mul_of_pos_right n hLpos)
    have hm3 : 2 < n * R.params.side := by
      have h4 : T.n₀ ≤ n * R.params.side := hm
      omega
    have hlip0 : 0 ≤ weightLipschitz R.params.side (R.depth + 1) h :=
      Real.iSup_nonneg fun _ => div_nonneg (abs_nonneg _) (barycentreDist_nonneg _ _)
    obtain ⟨lip, hlipdef⟩ : ∃ lip, lip = weightLipschitz R.params.side (R.depth + 1) h := ⟨_, rfl⟩
    rw [← hlipdef] at hlip0 ⊢
    obtain ⟨c, hcdef⟩ : ∃ c, c = blockMean R.params.side (R.depth + 1) n Y h := ⟨_, rfl⟩
    obtain ⟨h₁, hh₁⟩ : ∃ h₁ : PlaquetteWeight (fineSide R.params.side (R.depth + 1) n),
      h₁ = clampedShift (3 * lip) c h := ⟨_, rfl⟩
    have hB : 0 ≤ 3 * lip := by linarith
    have wn₁ := hWN R.params.side hLodd (R.depth + 1) n Y
    have hat_eq : ∀ p, IsPlaquetteAt R.params.side (R.depth + 1) Y p → h₁ p = h p - c := fun p hp => by
      rw [hh₁]
      refine clamp_eq_of_abs_le ?_
      rw [hcdef, hlipdef]
      exact wn₁.2.1 h p hp
    have hat₀ : blockMean R.params.side (R.depth + 1) n Y h₁ = 0 := by
      have m₁ := hMW R.params.side hLodd (R.depth + 1) n Y
      have e₁ := m₁.2.2 h₁ (fun p => 1 * h p + (-c) * constOneWeight _ p) (fun p hp => by
        rw [hat_eq p hp]
        simp only [constOneWeight]
        ring)
      rw [e₁, m₁.2.1 1 (-c) h (constOneWeight _), m₁.1, ← hcdef]
      ring
    have hsup : weightSup h₁ ≤ 3 * lip := by
      rw [hh₁]
      exact weightSup_clampedShift_le hB c h
    have hlip₁ : weightLipschitz R.params.side R.depth h₁ ≤ weightLipschitz R.params.side R.depth h := by
      rw [hh₁]
      exact weightLipschitz_clampedShift_le _ _ h
    have hlevel : (T.side : ℝ) * weightLipschitz R.params.side R.depth h = lip := by
      rw [hlipdef]
      exact side_mul_weightLipschitz hLpos h
    have hlip₁0 : 0 ≤ weightLipschitz R.params.side R.depth h₁ :=
      Real.iSup_nonneg fun _ => div_nonneg (abs_nonneg _) (barycentreDist_nonneg _ _)
    have hLe₁ : (T.side : ℝ) * weightLipschitz R.params.side R.depth h₁ ≤ lip := by
      rw [← hlevel]
      exact mul_le_mul_of_nonneg_left hlip₁ (by linarith)
    have hsize : weightNorm R.params.side R.depth h₁ ≤ 3 * lip := by
      refine max_le hsup ?_
      have h2 : weightLipschitz R.params.side R.depth h₁ ≤ (T.side : ℝ) * weightLipschitz R.params.side R.depth h₁ :=
        le_mul_of_one_le_left hlip₁0 hL1
      linarith
    have hw : ∀ z, |levelWeight (R := R) (n := n) h₁ z| ≤ 3 * lip := fun z =>
      ((hWN R.params.side hLodd R.depth (n * R.params.side) (toTorusSite _ z)).1 h₁).trans hsup
    have one := hOne (T.stepParameters y) R.depth (stepFrame R n) (n * R.params.side) Ts.decayRate hwgt
      period_depth_eq hm
    have he : 0 ≤ K.Kc * weightLipschitz R.params.side R.depth h₁ := mul_nonneg (by linarith) hlip₁0
    have he₂ : 0 ≤ 3 * lip * (K.Ka * x ^ (-(1 / 2) : ℝ)) := mul_nonneg hB (mul_nonneg hKa hxs)
    have hr : IsTorusRemainder Ts.L Ts.σ Ts.decayRate (K.Kc * weightLipschitz R.params.side R.depth h₁)
        (K.Kc * weightLipschitz R.params.side R.depth h₁ / Ts.η₃)
        (remainderOnFrame A.cold (stepFrame R n) (n * R.params.side) h₁) := by
      have h2 := one.1 K A.cold (fun z g W hW h' => hrowK.cold_gauge _ hm z g W hW h')
        ⟨hrowK.remainder_smooth, hrowK.remainder_decay, hrowK.remainder_local⟩ h₁
      rw [hη₃] at h2
      exact h2
    have hr₂ : IsTorusRemainder Ts.L Ts.σ Ts.decayRate (3 * lip * (K.Ka * x ^ (-(1 / 2) : ℝ)))
        (3 * lip * (K.Ka * x ^ (-(1 / 2) : ℝ)) / Ts.η₃)
        (weightedCenteredOnFrame A.siteRemainder (stepFrame R n) (n * R.params.side)
          (levelWeight (R := R) (n := n) h₁)) := by
      have h2 := one.2 _ _ (3 * lip) A.siteRemainder _ hrowK.site_family hB hw
      rw [hη₃, ← mul_div_assoc] at h2
      exact h2
    have htop : IsCubicTopTorus Ts.L R.depth Ts.n₀ (stepFrame R n) := ⟨rfl, rfl, n, fun _ => rfl, hn⟩
    have parts := fourTermSum_bounds Ts hTs hσ hxT hbelow htop he he₂ hB hal hw hr hr₂
      (torusSiteInFrame (stepFrame R n) (stepFrame R n).top Y)
    rw [hq] at parts
    have c54 : ∀ {V : TorusField n}, IsCold R.params.threshold V →
        IsSmallCurvature (5 / 4 * Ts.σ) (readAtLevel (stepFrame R n) (stepFrame R n).top V) :=
      fun hV => isSmallCurvature_readAtLevel fun z μ ν hμ =>
        (hV z μ ν hμ).trans (by show T.threshold < 5 / 4 * T.threshold; linarith)
    have c98 : ∀ {V : TorusField n}, IsCold R.params.threshold V →
        IsSmallCurvature (9 / 8 * Ts.σ) (readAtLevel (stepFrame R n) (stepFrame R n).top V) :=
      fun hV => isSmallCurvature_readAtLevel fun z μ ν hμ =>
        (hV z μ ν hμ).trans (by show T.threshold < 9 / 8 * T.threshold; linarith)
    have hKc' : 12 * Ts.Cs + 2 ≤ K.Kc := hKc
    refine ⟨fourTermSum (coldHalfLawOf R) A.coeff (remainderOnFrame A.cold (stepFrame R n) (n * R.params.side) h₁)
      (weightedCenteredOnFrame A.siteRemainder (stepFrame R n) (n * R.params.side)
        (levelWeight (R := R) (n := n) h₁))
      (levelWeight (R := R) (n := n) h₁) (torusSiteInFrame (stepFrame R n) (stepFrame R n).top Y), h₁,
      ∑ z ∈ sitesInBlocks R.params.side {Y}, blockMean R.params.side R.depth (n * R.params.side) z h₁ *
        A.cold (n * R.params.side) z (trivialField (n * R.params.side)) (constOneWeight _), ?_, hsize, hlip0,
      fun V hV => (parts.1 _ (c54 hV)).1, ?_, ?_⟩
    · intro V hV
      have hV9 : IsCold (9 / 8 * T.threshold) V := fun z μ ν hμ =>
        (hV z μ ν hμ).trans (by show T.threshold < 9 / 8 * T.threshold; linarith)
      obtain ⟨L1, L2, L3, L4, L5⟩ := hlaw' n hnT V hV9
      have hcoldk : ∀ k : StepVariable (finiteCells (stepFrame R n)), (∀ b, ‖k b‖ < R.ballRadius) →
          IsCold R.params.threshold (coldFieldAboveFrames R V k) := by
        intro k hk
        obtain ⟨η, hηb, e⟩ := L3 k hk
        have h2 := hcs' n hnT V hV9 η fun b => (hηb b).le
        rw [← e]
        intro z μ ν hμ
        exact (h2 z μ ν hμ).trans (by show T.threshold / 4 < T.threshold; linarith)
      have hρ : 0 < R.ballRadius := by
        show 0 < T.threshold / 64
        positivity
      have mp := blockExpectations_eq_fourTermSum A hresp hfits.σ_pos hm hm3 V L1 L2 hcoldk L4 L5
        (fun W hW z => hSh T hD R.depth n hnT W hW z) hρ Y h₁
      have lin := hL' n hn Y V hV
      have l1 := lin.1 (-c) (constOneWeight _) h
      have l2 := lin.2 ((-c) • constOneWeight _ + h) h₁ (fun p hp => by
        rw [hat_eq p hp]
        simp only [Pi.add_apply, Pi.smul_apply, constOneWeight, smul_eq_mul]
        ring)
      have img := hI' n hn Y V hV h₁
      have e₀ : responseRemainder A.coldStep n Y h V = A.coldStep n Y V h₁ := by
        unfold responseRemainder
        rw [← l2, l1, ← hcdef]
        ring
      rw [e₀, img]
      unfold coldTermAbove
      rw [hat₀]
      simp only [mul_zero, zero_mul, add_zero]
      linarith
    · intro V hV k c' X h1 h3 hX
      have t₀ := (parts.1 _ (c54 hV)).2 k c' X h1 h3 hX
      have hGp := torusDecayFactor_pos Ts.L Ts.decayRate
        (bondSpan (torusSiteInFrame (stepFrame R n) (stepFrame R n).top Y) c' : ℝ)
      have hu : (0 : ℝ) ≤ (bondSpan (torusSiteInFrame (stepFrame R n) (stepFrame R n).top Y) c' : ℝ) :=
        Nat.cast_nonneg _
      have hex : Real.exp (-(Ts.κ / 2 ^ 5 *
            (bondSpan (torusSiteInFrame (stepFrame R n) (stepFrame R n).top Y) c' : ℝ))) ≤
          Cw / torusDecayFactor Ts.L Ts.decayRate
            (bondSpan (torusSiteInFrame (stepFrame R n) (stepFrame R n).top Y) c') :=
        exp_neg_le_div_torusDecayFactor (hCw _ hu) (by
          show 2 * (T.rt / 2 ^ 10) ≤ T.rt / 2 ^ 5
          have := hD.rt_pos
          linarith) hu
      have hKk : K.Kc ≤ (if k = 3 then K.Kc / K.η₃ else K.Kc) := by
        split_ifs
        · rw [hη₃, le_div_iff₀ hη₀]
          exact mul_le_of_le_one_right (by linarith) hη₁
        · exact le_rfl
      have hLeq : (Ts.L : ℝ) * (K.Kc * weightLipschitz R.params.side R.depth h₁) ≤ K.Kc * lip := by
        have e : (Ts.L : ℝ) * (K.Kc * weightLipschitz R.params.side R.depth h₁) =
            K.Kc * ((T.side : ℝ) * weightLipschitz R.params.side R.depth h₁) := by
          show (T.side : ℝ) * _ = _
          ring
        rw [e]
        exact mul_le_mul_of_nonneg_left hLe₁ (by linarith)
      have hLek : (Ts.L : ℝ) * (if k = 3 then K.Kc * weightLipschitz R.params.side R.depth h₁ / Ts.η₃
          else K.Kc * weightLipschitz R.params.side R.depth h₁) ≤
          (if k = 3 then K.Kc / K.η₃ else K.Kc) * lip := by
        split_ifs
        · rw [hη₃, ← mul_div_assoc, div_mul_eq_mul_div]
          exact div_le_div_of_nonneg_right hLeq hη₀.le
        · exact hLeq
      have hbr : 2⁻¹ ^ 7 * (if k = 3 then K.Kc / K.η₃ else K.Kc) + x ^ (-(1 / 2) : ℝ) * Mx + 6 * Ts.Cs +
          3 * Real.exp (-(T.gasRate * x / 2)) ≤ (if k = 3 then K.Kc / K.η₃ else K.Kc) := by
        have e : ((2 : ℝ)⁻¹) ^ 7 = 1 / 128 := by norm_num
        rw [e]
        linarith
      have hs := derivative_estimate hGp hlip0 hη₀ (by linarith : (0 : ℝ) ≤ K.Kc) hCE hxs hLeq hLek hex
        (Real.exp_pos _).le hbr
      linarith
    · intro V V' q k b X hV hV' hA' hk hb hX
      have t₀ := parts.2 _ _ q k b X (c98 hV) (c98 hV') hA' hk hb hX
      have hGp := torusDecayFactor_pos Ts.L Ts.decayRate (q : ℝ)
      have hu : (0 : ℝ) ≤ (q : ℝ) := Nat.cast_nonneg _
      have hex : Real.exp (-(2 * Ts.decayRate * (q : ℝ))) ≤ Cw / torusDecayFactor Ts.L Ts.decayRate q :=
        exp_neg_le_div_torusDecayFactor (hCw _ hu) le_rfl hu
      have hLeq : (Ts.L : ℝ) * (K.Kc * weightLipschitz R.params.side R.depth h₁) ≤ K.Kc * lip := by
        have e : (Ts.L : ℝ) * (K.Kc * weightLipschitz R.params.side R.depth h₁) =
            K.Kc * ((T.side : ℝ) * weightLipschitz R.params.side R.depth h₁) := by
          show (T.side : ℝ) * _ = _
          ring
        rw [e]
        exact mul_le_mul_of_nonneg_left hLe₁ (by linarith)
      have hbr : 2⁻¹ ^ 5 * K.Kc + x ^ (-(1 / 2) : ℝ) * (6 * Ts.CE * Cw + 3 * Ts.CE * K.Ka / Ts.η₃) +
          6 * Ts.Cs + 3 * Real.exp (-(T.gasRate * x / 2)) ≤ K.Kc := by
        have e : ((2 : ℝ)⁻¹) ^ 5 = 1 / 32 := by norm_num
        have h0 : 0 ≤ Ts.CE * K.Kc / Ts.η₃ * Cw := by
          have : 0 ≤ K.Kc := by linarith
          positivity
        have h1 : x ^ (-(1 / 2) : ℝ) * (6 * Ts.CE * Cw + 3 * Ts.CE * K.Ka / Ts.η₃) ≤
            x ^ (-(1 / 2) : ℝ) * Mx := by
          refine mul_le_mul_of_nonneg_left ?_ hxs
          show _ ≤ Ts.CE * K.Kc / Ts.η₃ * Cw + 6 * Ts.CE * Cw + 3 * Ts.CE * K.Ka / Ts.η₃
          linarith
        rw [e]
        linarith
      have hs := difference_le_of_bounds hGp hlip0 hη₀ hCE hxs hLeq hex hbr
      linarith
  have hweight : ∀ s : ℕ, R.params.weight s = torusDecayFactor Ts.L Ts.decayRate s := fun s => rfl
  refine ⟨fun n _ hn Y V hV h => ?_, fun n _ hn Y V hV h k c X h1 h3 hX => ?_,
    fun n _ hn Y W W' m hm hW hW' hA' h k b X hk hb hX => ?_⟩
  · obtain ⟨H, h₁, d, key, -, -, hsm, -, -⟩ := main n hn Y h
    exact (decomposition_contDiff_mixedDeriv hV key (contDiffThreeAt_readAtLevel (hsm V hV))
      (hG'.1 n hn Y V hV h₁).2.1).1
  · obtain ⟨H, h₁, d, key, hsize, hlip0, hsm, hdec, -⟩ := main n hn Y h
    have hgas := hG'.1 n hn Y V hV h₁
    have pr := (decomposition_contDiff_mixedDeriv hV key (contDiffThreeAt_readAtLevel (hsm V hV))
      hgas.2.1).2 k c X h3
    rw [pr, mixedDeriv_readAtLevel, mixedDeriv_const (by omega), add_zero]
    have dd := hdec V hV k (bondsOnTop _ _ c) X h1 h3 hX
    rw [bondSpan_bondsOnTop] at dd
    have gs : |mixedDeriv (fun V' : TorusField n => gasTermAtBlock A (coldCaseGround R V') Y h₁) V c X| ≤
        Real.exp (-(T.gasRate * x / 2)) * weightNorm R.params.side R.depth h₁ /
          torusDecayFactor Ts.L Ts.decayRate (supportDiam Y c) := hgas.2.2 k c X h1 h3 hX
    rw [hweight]
    have hG0 := torusDecayFactor_pos Ts.L Ts.decayRate (supportDiam Y c : ℝ)
    have gs' : Real.exp (-(T.gasRate * x / 2)) * weightNorm R.params.side R.depth h₁ /
          torusDecayFactor Ts.L Ts.decayRate (supportDiam Y c) ≤
        Real.exp (-(T.gasRate * x / 2)) * (3 * weightLipschitz R.params.side (R.depth + 1) h) /
          torusDecayFactor Ts.L Ts.decayRate (supportDiam Y c) := by
      gcongr
    refine (abs_add_le _ _).trans ?_
    linarith
  · obtain ⟨H, h₁, d, key, hsize, hlip0, hsm, -, hcmp⟩ := main n hn Y h
    have hcancelled' : ∀ V : TorusField n, IsCold R.params.threshold V → centeredRemainder A.coldStep n Y h V =
        H (readAtLevel (torusFrame R.params.side R.depth n) (torusFrame R.params.side R.depth n).top V) +
          gasTermAtBlock A (coldCaseGround R V) Y h₁ +
          (d - responseRemainder A.coldStep n Y h (trivialField n)) := fun V hV => by
      unfold centeredRemainder
      rw [key V hV]
      ring
    have p₁ := (decomposition_contDiff_mixedDeriv hW hcancelled' (contDiffThreeAt_readAtLevel (hsm W hW))
      (hG'.1 n hn Y W hW h₁).2.1).2 k (fun l => bondFrom Y (b l)) X (by omega)
    have p₂ := (decomposition_contDiff_mixedDeriv hW' hcancelled' (contDiffThreeAt_readAtLevel (hsm W' hW'))
      (hG'.1 n hn Y W' hW' h₁).2.1).2 k (fun l => bondFrom Y (b l)) X (by omega)
    rw [p₁, p₂, mixedDeriv_readAtLevel, mixedDeriv_readAtLevel, bondsOnTop_bondFrom]
    have dd := hcmp W W' m k b X hW hW' (agreeOnBall_readAtLevel hm hA') hk hb hX
    have gs : |mixedDeriv (fun U : TorusField n => gasTermAtBlock A (coldCaseGround R U) Y h₁) W
          (fun l => bondFrom Y (b l)) X -
        mixedDeriv (fun U : TorusField n => gasTermAtBlock A (coldCaseGround R U) Y h₁) W'
          (fun l => bondFrom Y (b l)) X| ≤
        Real.exp (-(T.gasRate * x / 2)) * weightNorm R.params.side R.depth h₁ /
          torusDecayFactor Ts.L Ts.decayRate m :=
      hG'.2 n n hn hn Y Y W W' m hm hm hW hW' hA' h₁ h₁ (fun _ _ _ _ _ => rfl) k b X hk hb hX
    rw [hweight]
    have hG0 := torusDecayFactor_pos Ts.L Ts.decayRate (m : ℝ)
    have gs' : Real.exp (-(T.gasRate * x / 2)) * weightNorm R.params.side R.depth h₁ /
          torusDecayFactor Ts.L Ts.decayRate m ≤
        Real.exp (-(T.gasRate * x / 2)) * (3 * weightLipschitz R.params.side (R.depth + 1) h) /
          torusDecayFactor Ts.L Ts.decayRate m := by
      gcongr
    have e : ∀ a₁ a₂ a₃ b₁ b₂ : ℝ, a₁ + b₁ + a₃ - (a₂ + b₂ + a₃) = (a₁ - a₂) + (b₁ - b₂) := by
      intros
      ring
    rw [show mixedDeriv (fun _ : TorusField n => d - responseRemainder A.coldStep n Y h (trivialField n)) W'
        (fun l => bondFrom Y (b l)) X =
      mixedDeriv (fun _ : TorusField n => d - responseRemainder A.coldStep n Y h (trivialField n)) W
        (fun l => bondFrom Y (b l)) X from rfl, e]
    refine (abs_add_le _ _).trans ?_
    linarith
end YangMills.Construction.ResponseInTheExpansion
end
