import YangMills.Construction.ChessboardTori.ElementaryPropertiesOfAGrid
import YangMills.Construction.ClusterExpansionOfAStep.FlowWhereTheExpansionReturns
import YangMills.Construction.FreeEnergiesOfTheFlow.ScoredTowerOfTheFlow
import YangMills.Construction.LawInAState.ConcentrationInOneBox
import YangMills.Construction.LawInAState.CovarianceBelowTheAverages
import YangMills.Construction.LawInAState.FromSixteenCopiesToOneBoxProof
import YangMills.Construction.LawInAState.ResponsesAlongTheChainAreBounded
import YangMills.Construction.LawInAState.TheCouplingOfTheLevelGrows
import YangMills.Construction.LawInAState.TheLawInAState
import YangMills.Construction.LawInAState.TheLevelOfTheLaw
import YangMills.Construction.LawInAState.TheNumberOfAPairUnderTheGroup
import YangMills.Construction.ResponseInTheExpansion.NumbersOfAScoredTowerAreTheChain
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Filter Topology
namespace YangMills.Construction.StateLaws
open InfiniteLattice (AmbientSpace)
open TorusMetric (euclidNormVec)
private structure IsSignedAffine (r : AmbientSpace → AmbientSpace) (σ : Fin 4 → ℤ) (w : AmbientSpace) : Prop where
  signs : ∀ μ, σ μ = 1 ∨ σ μ = -1
  apply : ∀ x μ, r x μ = (σ μ : ℝ) * x μ + w μ
private theorem signs_mul_self {σ : Fin 4 → ℤ} (h : ∀ μ, σ μ = 1 ∨ σ μ = -1) (μ : Fin 4) : (σ μ : ℝ) * (σ μ : ℝ) = 1 := by
  rcases h μ with h | h <;> simp [h]
private theorem IsSignedAffine.symm {e : Equiv.Perm AmbientSpace} {σ : Fin 4 → ℤ} {w : AmbientSpace} (h : IsSignedAffine e σ w) :
    IsSignedAffine e.symm σ (fun μ => -((σ μ : ℝ) * w μ)) := by
  refine ⟨h.signs, fun x μ => ?_⟩
  have h1 := h.apply (e.symm x) μ
  rw [Equiv.apply_symm_apply] at h1
  have h2 := signs_mul_self h.signs μ
  have : (σ μ : ℝ) * x μ = (σ μ : ℝ) * (σ μ : ℝ) * e.symm x μ + (σ μ : ℝ) * w μ := by rw [h1]; ring
  rw [h2] at this
  linarith
private theorem IsSignedAffine.euclidNormVec_sub {r : AmbientSpace → AmbientSpace} {σ : Fin 4 → ℤ} {w : AmbientSpace}
    (h : IsSignedAffine r σ w) (x y : AmbientSpace) :
    euclidNormVec (r x - r y) = euclidNormVec (x - y) := by
  simp only [euclidNormVec]
  congr 1
  refine Finset.sum_congr rfl fun μ _ => ?_
  have h2 := signs_mul_self h.signs μ
  simp only [Pi.sub_apply, h.apply]
  have : ((σ μ : ℝ) * x μ + w μ - ((σ μ : ℝ) * y μ + w μ)) ^ 2 = (σ μ : ℝ) * (σ μ : ℝ) * (x μ - y μ) ^ 2 := by ring
  rw [this, h2, one_mul]
private theorem IsSignedAffine.continuous {r : AmbientSpace → AmbientSpace} {σ : Fin 4 → ℤ} {w : AmbientSpace}
    (h : IsSignedAffine r σ w) : Continuous r := by
  refine continuous_pi fun μ => ?_
  simp only [h.apply]
  fun_prop
private def IsSignedAffine.toHomeomorph {e : Equiv.Perm AmbientSpace} {σ : Fin 4 → ℤ} {w : AmbientSpace}
    (h : IsSignedAffine e σ w) : AmbientSpace ≃ₜ AmbientSpace where
  toEquiv := e
  continuous_toFun := h.continuous
  continuous_invFun := h.symm.continuous
private theorem IsSignedAffine.tsupport_comp_symm {e : Equiv.Perm AmbientSpace} {σ : Fin 4 → ℤ} {w : AmbientSpace}
    (h : IsSignedAffine e σ w) (f : AmbientSpace → ℝ) : tsupport (fun x => f (e.symm x)) = e '' tsupport f := by
  have hs : (fun x => f (e.symm x)) = f ∘ h.toHomeomorph.symm := rfl
  have he : e '' _root_.tsupport f = h.toHomeomorph '' _root_.tsupport f := rfl
  rw [he, hs, _root_.tsupport, Function.support_comp_eq_preimage, ← h.toHomeomorph.symm.preimage_closure, _root_.tsupport,
    Homeomorph.image_eq_preimage_symm]
private theorem IsSignedAffine.measurePreserving {r : AmbientSpace → AmbientSpace} {σ : Fin 4 → ℤ} {w : AmbientSpace}
    (h : IsSignedAffine r σ w) : MeasurePreserving r volume volume := by
  have hr : r = fun x μ => (fun (μ : Fin 4) (t : ℝ) => (σ μ : ℝ) * t + w μ) μ (x μ) := by
    funext x μ
    exact h.apply x μ
  have hc : ∀ μ : Fin 4, MeasurePreserving (fun t : ℝ => (σ μ : ℝ) * t + w μ) volume volume := by
    intro μ
    rcases h.signs μ with hs | hs
    · simp only [hs, Int.cast_one, one_mul]
      exact measurePreserving_add_right volume (w μ)
    · simp only [hs, Int.cast_neg, Int.cast_one, neg_mul, one_mul]
      exact (measurePreserving_add_right volume (w μ)).comp (Measure.measurePreserving_neg volume)
  rw [hr]
  exact volume_preserving_pi (α' := fun _ : Fin 4 => ℝ) (β' := fun _ : Fin 4 => ℝ) hc
private theorem IsSignedAffine.integral_comp_symm {e : Equiv.Perm AmbientSpace} {σ : Fin 4 → ℤ} {w : AmbientSpace}
    (h : IsSignedAffine e σ w) (f : AmbientSpace → ℝ) : ∫ x, f (e.symm x) = ∫ x, f x :=
  h.symm.measurePreserving.integral_comp h.toHomeomorph.symm.measurableEmbedding f
private theorem uniformNorm_comp_symm (e : Equiv.Perm AmbientSpace) (f : AmbientSpace → ℝ) :
    TestFunctions.uniformNorm (fun x => f (e.symm x)) = TestFunctions.uniformNorm f :=
  e.symm.iSup_comp (g := fun x => ‖f x‖)
private theorem IsSignedAffine.bestLipschitzConstant_comp_symm {e : Equiv.Perm AmbientSpace} {σ : Fin 4 → ℤ}
    {w : AmbientSpace} (h : IsSignedAffine e σ w) (f : AmbientSpace → ℝ) :
    TestFunctions.bestLipschitzConstant TestFunctions.euclidDistR4 (fun x => f (e.symm x)) =
      TestFunctions.bestLipschitzConstant TestFunctions.euclidDistR4 f := by
  unfold TestFunctions.bestLipschitzConstant
  congr 1
  ext C
  refine and_congr_right fun _ => ⟨fun hC x y => ?_, fun hC x y => ?_⟩
  · have := hC (e x) (e y)
    simpa [TestFunctions.euclidDistR4, h.euclidNormVec_sub] using this
  · have := hC (e.symm x) (e.symm y)
    simpa [TestFunctions.euclidDistR4, h.symm.euclidNormVec_sub] using this
private theorem IsSignedAffine.isShapedBump_comp_symm {e : Equiv.Perm AmbientSpace} {σ : Fin 4 → ℤ} {w : AmbientSpace}
    (h : IsSignedAffine e σ w) {d vt : ℝ} {x : AmbientSpace} {f : AmbientSpace → ℝ}
    (hf : TestFunctions.IsShapedBump TestFunctions.euclidDistR4 TestFunctions.closedBallR4 (fun w => ∫ x, w x) d vt x f) :
    TestFunctions.IsShapedBump TestFunctions.euclidDistR4 TestFunctions.closedBallR4 (fun w => ∫ x, w x) d vt (e x)
      (fun z => f (e.symm z)) := by
  obtain ⟨⟨C, hC0, hC⟩, h0, ⟨z, hz⟩, hb, hi, hl⟩ := hf
  refine ⟨⟨C, hC0, fun a b => ?_⟩, fun a => h0 _, ⟨e z, by simpa using hz⟩, ?_, ?_, ?_⟩
  · have := hC (e.symm a) (e.symm b)
    simpa [TestFunctions.euclidDistR4, h.symm.euclidNormVec_sub] using this
  · rw [h.tsupport_comp_symm]
    rintro _ ⟨a, ha, rfl⟩
    have := hb ha
    simpa [TestFunctions.closedBallR4, h.euclidNormVec_sub] using this
  · simp only [uniformNorm_comp_symm, h.integral_comp_symm]
    exact hi
  · rw [h.bestLipschitzConstant_comp_symm, uniformNorm_comp_symm]
    exact hl
private theorem setDistR4_image {e : Equiv.Perm AmbientSpace} {σ : Fin 4 → ℤ} {w : AmbientSpace} (h : IsSignedAffine e σ w)
    (A B : Set AmbientSpace) : TestFunctions.setDistR4 (e '' A) (e '' B) = TestFunctions.setDistR4 A B := by
  simp only [TestFunctions.setDistR4, iInf_image, h.euclidNormVec_sub]
private theorem IsSignedAffine.isNormalizedTestPair_comp_symm {e : Equiv.Perm AmbientSpace} {σ : Fin 4 → ℤ}
    {w : AmbientSpace} (h : IsSignedAffine e σ w) {d vt : ℝ} {f g : AmbientSpace → ℝ} (hp : IsNormalizedTestPair d vt f g) :
    IsNormalizedTestPair d vt (fun x => f (e.symm x)) (fun x => g (e.symm x)) := by
  obtain ⟨x₁, x₂, h₁, h₂, hlo, hhi⟩ := hp.mem_class
  refine ⟨⟨e x₁, e x₂, h.isShapedBump_comp_symm h₁, h.isShapedBump_comp_symm h₂, ?_, ?_⟩, ?_, ?_⟩
  · simp only [h.tsupport_comp_symm, setDistR4_image h]
    exact hlo
  · simp only [h.tsupport_comp_symm, setDistR4_image h]
    exact hhi
  · rw [uniformNorm_comp_symm]; exact hp.norm_left
  · rw [uniformNorm_comp_symm]; exact hp.norm_right
private def addPerm (s : AmbientSpace) : Equiv.Perm AmbientSpace where
  toFun x := x + s
  invFun x := x - s
  left_inv x := by simp
  right_inv x := by simp
private theorem addPerm_isSignedAffine (s : AmbientSpace) : IsSignedAffine (addPerm s) (fun _ => 1) s :=
  ⟨fun _ => Or.inl rfl, fun x μ => by simp [addPerm]⟩
private theorem abs_apply_le_euclidNormVec (v : AmbientSpace) (μ : Fin 4) : |v μ| ≤ euclidNormVec v := by apply _root_.YangMills.SharedProofs.p10398 <;> assumption
private theorem exists_common_centre {d vt : ℝ} {f h : AmbientSpace → ℝ} (hd : 0 < d) (hp : IsNormalizedTestPair d vt f h) :
    ∃ x₀ : AmbientSpace, ∀ w, (w = f ∨ w = h) → ∀ z ∈ tsupport w, ∀ μ, |z μ - x₀ μ| ≤ 10 * d := by
  obtain ⟨x₁, x₂, h₁, h₂, -, hhi⟩ := hp.mem_class
  have hb₁ : tsupport f ⊆ TestFunctions.closedBallR4 x₁ d := h₁.2.2.2.1
  have hb₂ : tsupport h ⊆ TestFunctions.closedBallR4 x₂ d := h₂.2.2.2.1
  have hlt : TestFunctions.setDistR4 (tsupport f) (tsupport h) < ENNReal.ofReal (7 * d) :=
    lt_of_le_of_lt hhi ((ENNReal.ofReal_lt_ofReal_iff (by positivity)).2 (by linarith))
  simp only [TestFunctions.setDistR4, iInf_lt_iff] at hlt
  obtain ⟨a, ha, b, hb, hab⟩ := hlt
  have hab' : euclidNormVec (a - b) < 7 * d := (ENNReal.ofReal_lt_ofReal_iff (by positivity)).1 hab
  have near₁ : ∀ z ∈ tsupport f, ∀ μ, |z μ - x₁ μ| ≤ d := fun z hz μ =>
    (abs_apply_le_euclidNormVec (z - x₁) μ).trans (hb₁ hz)
  have near₂ : ∀ z ∈ tsupport h, ∀ μ, |z μ - x₂ μ| ≤ d := fun z hz μ =>
    (abs_apply_le_euclidNormVec (z - x₂) μ).trans (hb₂ hz)
  refine ⟨x₁, ?_⟩
  rintro w (rfl | rfl) z hz μ
  · have := near₁ z hz μ
    linarith
  · have h1 := abs_le.1 (near₂ z hz μ)
    have h2 := abs_le.1 (near₂ b hb μ)
    have h3 := abs_le.1 (near₁ a ha μ)
    have h4 := abs_le.1 ((abs_apply_le_euclidNormVec (a - b) μ).trans hab'.le)
    simp only [Pi.sub_apply] at h4
    rw [abs_le]
    constructor <;> linarith [h1.1, h1.2, h2.1, h2.2, h3.1, h3.2, h4.1, h4.2]
private theorem euclidNormVec_le_two_mul_norm (v : AmbientSpace) : euclidNormVec v ≤ 2 * ‖v‖ := by apply _root_.YangMills.SharedProofs.p8643 <;> assumption
private theorem isBoundedBorel_of_shapedBump {d vt : ℝ} {x : AmbientSpace} {f : AmbientSpace → ℝ}
    (hf : TestFunctions.IsShapedBump TestFunctions.euclidDistR4 TestFunctions.closedBallR4 (fun w => ∫ x, w x) d vt x f) :
    InfiniteLattice.IsBoundedBorelCompactlySupported f := by
  obtain ⟨⟨C, hC0, hC⟩, -, -, hb, -, -⟩ := hf
  have hL : LipschitzWith (Real.toNNReal (C * 2)) f := LipschitzWith.of_dist_le_mul fun a b => by
    rw [Real.coe_toNNReal _ (by positivity), Real.dist_eq, dist_eq_norm]
    calc |f a - f b| ≤ C * euclidNormVec (a - b) := hC a b
      _ ≤ C * (2 * ‖a - b‖) := mul_le_mul_of_nonneg_left (euclidNormVec_le_two_mul_norm _) hC0
      _ = C * 2 * ‖a - b‖ := by ring
  have hc := hL.continuous
  have hcs : HasCompactSupport f := by
    refine Metric.isCompact_of_isClosed_isBounded (isClosed_tsupport f) ?_
    refine (Metric.isBounded_closedBall (x := x) (r := d)).subset fun z hz => ?_
    have hz' : euclidNormVec (z - x) ≤ d := hb hz
    rw [Metric.mem_closedBall, dist_eq_norm]
    have hd : 0 ≤ d := (Real.sqrt_nonneg _).trans hz'
    exact (pi_norm_le_iff_of_nonneg hd).2 fun μ => (abs_apply_le_euclidNormVec (z - x) μ).trans hz'
  exact ⟨hc.measurable, hc.bounded_above_of_compact_support hcs, hcs⟩
private theorem isBoundedBorel_of_testPair {d vt : ℝ} {f h : AmbientSpace → ℝ} (hp : IsNormalizedTestPair d vt f h) :
    InfiniteLattice.IsBoundedBorelCompactlySupported f ∧ InfiniteLattice.IsBoundedBorelCompactlySupported h := by
  obtain ⟨x₁, x₂, h₁, h₂, -, -⟩ := hp.mem_class
  exact ⟨isBoundedBorel_of_shapedBump h₁, isBoundedBorel_of_shapedBump h₂⟩
private theorem exists_reflectionGrid_centred (D : ChessboardTori.ChessboardSetup) {d vt ρ : ℝ} {f h : AmbientSpace → ℝ}
    (hd : 0 < d) (hp : IsNormalizedTestPair d vt f h) :
    ∃ g : ChessboardTori.ReflectionGrid D, g.q = 0 ∧ ∀ δ : ℝ, 10 * d + ρ + D.mesh + δ ≤ 1 / 2 → ∀ s : AmbientSpace,
      (∀ μ, |s μ| ≤ ρ) → ∀ w, (w = f ∨ w = h) → IsInteriorBy g δ (fun x => w (x - s)) := by
  obtain ⟨x₀, hx₀⟩ := exists_common_centre hd hp
  have ha := D.mesh_pos
  refine ⟨⟨0, ?_, fun μ => D.mesh * ((⌊(x₀ μ - 1 / 2) / D.mesh⌋ : ℝ) + 1 / 2), fun μ => ⟨_, rfl⟩⟩, rfl, ?_⟩
  · have := D.K.pos
    omega
  intro δ hρ s hs w hw x hx μ
  have h2 : x ∈ addPerm s '' tsupport w := ((addPerm_isSignedAffine s).tsupport_comp_symm w).subset hx
  obtain ⟨z, hz, rfl⟩ := h2
  have hb := abs_le.1 (hx₀ w hw z hz μ)
  have hsμ := abs_le.1 (hs μ)
  have e1 : D.mesh * ((x₀ μ - 1 / 2) / D.mesh) = x₀ μ - 1 / 2 := by field_simp
  have lo := mul_le_mul_of_nonneg_left (Int.floor_le ((x₀ μ - 1 / 2) / D.mesh)) ha.le
  have hi := mul_lt_mul_of_pos_left (Int.lt_floor_add_one ((x₀ μ - 1 / 2) / D.mesh)) ha
  rw [e1] at lo hi
  show δ ≤ (z + s) μ - D.mesh * ((⌊(x₀ μ - 1 / 2) / D.mesh⌋ : ℝ) + 1 / 2) ∧
    (z + s) μ - D.mesh * ((⌊(x₀ μ - 1 / 2) / D.mesh⌋ : ℝ) + 1 / 2) ≤ 1 - δ
  have e2 : (z + s) μ = z μ + s μ := rfl
  rw [e2, mul_add]
  rw [mul_add, mul_one] at hi
  constructor <;> linarith [hb.1, hb.2, hsμ.1, hsμ.2]
private theorem sum_shiftSet_signs {σ : Fin 4 → ℤ} (hσ : ∀ μ, σ μ = 1 ∨ σ μ = -1) (m : ℕ) (F : (Fin 4 → ℤ) → ℝ) :
    ∑ v ∈ shiftSet m, F (fun μ => σ μ * v μ) = ∑ v ∈ shiftSet m, F v := by
  have hsq : ∀ μ, σ μ * σ μ = 1 := fun μ => by rcases hσ μ with h | h <;> simp [h]
  have hmem : ∀ v ∈ shiftSet m, (fun μ => σ μ * v μ) ∈ shiftSet m := by
    intro v hv
    simp only [shiftSet, Fintype.mem_piFinset, Finset.mem_Icc] at hv ⊢
    intro μ
    have := hv μ
    rcases hσ μ with h | h <;> simp only [h] <;> constructor <;> linarith [this.1, this.2]
  refine Finset.sum_nbij' (fun v μ => σ μ * v μ) (fun v μ => σ μ * v μ) hmem hmem ?_ ?_ (fun _ _ => rfl)
  · intro v _
    funext μ
    rw [← mul_assoc, hsq, one_mul]
  · intro v _
    funext μ
    rw [← mul_assoc, hsq, one_mul]
private theorem translateBy_comp_symm {e : Equiv.Perm AmbientSpace} {σ : Fin 4 → ℤ} {w : AmbientSpace}
    (h : IsSignedAffine e σ w) (L K k : ℕ) (v : Fin 4 → ℤ) (f : AmbientSpace → ℝ) :
    (fun x => translateBy L K k v f (e.symm x)) = translateBy L K k (fun μ => σ μ * v μ) (fun x => f (e.symm x)) := by
  funext x
  simp only [translateBy]
  congr 1
  funext μ
  have h1 := h.symm.apply (x - latticeShift L K k fun μ => σ μ * v μ) μ
  have h2 := h.symm.apply x μ
  have h3 := signs_mul_self h.signs μ
  rw [h1]
  simp only [Pi.sub_apply, latticeShift, h2]
  push_cast
  linear_combination ((v μ : ℝ) * ((L : ℝ) ^ k / (L : ℝ) ^ K)) * h3
section Box
variable {ℓ : TorusLumps.StepParameters}
private theorem shiftAveragedProduct_comp_symm {e : Equiv.Perm AmbientSpace} {σ : Fin 4 → ℤ} {w : AmbientSpace}
    (h : IsSignedAffine e σ w) (T : WeightedResponses.StageTower ℓ) (β : ℝ) (al : ℕ → ℝ) (K k m : ℕ)
    (f g : AmbientSpace → ℝ) (u : WeightedResponses.MarkedSample ℓ k (BoxResponses.boxSide ℓ.side K k)) :
    BoxResponses.shiftAveragedProduct T β al K k m (fun v x => translateBy ℓ.side K k v f (e.symm x))
        (fun v x => translateBy ℓ.side K k v g (e.symm x)) u =
      BoxResponses.shiftAveragedProduct T β al K k m (fun v => translateBy ℓ.side K k v fun x => f (e.symm x))
        (fun v => translateBy ℓ.side K k v fun x => g (e.symm x)) u := by
  unfold BoxResponses.shiftAveragedProduct
  congr 1
  simp only [translateBy_comp_symm h]
  exact sum_shiftSet_signs h.signs m (fun v =>
    BoxResponses.centeredBoxResponse T β al K k (translateBy ℓ.side K k v fun x => f (e.symm x)) u *
      BoxResponses.centeredBoxResponse T β al K k (translateBy ℓ.side K k v fun x => g (e.symm x)) u)
private theorem shiftAveragedResponse_comp_symm {e : Equiv.Perm AmbientSpace} {σ : Fin 4 → ℤ} {w : AmbientSpace}
    (h : IsSignedAffine e σ w) (T : WeightedResponses.StageTower ℓ) (β : ℝ) (al : ℕ → ℝ) (K k m : ℕ)
    (f : AmbientSpace → ℝ) :
    BoxResponses.shiftAveragedResponse T β al K k m (fun v x => translateBy ℓ.side K k v f (e.symm x)) =
      BoxResponses.shiftAveragedResponse T β al K k m (fun v => translateBy ℓ.side K k v fun x => f (e.symm x)) := by
  funext u
  unfold BoxResponses.shiftAveragedResponse
  congr 1
  simp only [translateBy_comp_symm h]
  exact sum_shiftSet_signs h.signs m
    (fun v => BoxResponses.centeredBoxResponse T β al K k (translateBy ℓ.side K k v fun x => f (e.symm x)) u)
end Box
private theorem abs_integral_le_of_eLpNorm_sixteen {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {F : Ω → ℝ} (hF : AEStronglyMeasurable F μ) {b : ℝ} (hb : 0 ≤ b) (h : eLpNorm F 16 μ ≤ ENNReal.ofReal b) :
    |∫ u, F u ∂μ| ≤ b := by
  have h1 : eLpNorm F 1 μ ≤ eLpNorm F 16 μ := eLpNorm_le_eLpNorm_of_exponent_le (by norm_num) hF
  have h2 : eLpNorm F 1 μ ≤ ENNReal.ofReal b := h1.trans h
  rw [eLpNorm_one_eq_lintegral_enorm] at h2
  have h3 : ‖∫ u, F u ∂μ‖ₑ ≤ ENNReal.ofReal b := (enorm_integral_le_lintegral_enorm F).trans h2
  rw [Real.enorm_eq_ofReal_abs, ENNReal.ofReal_le_ofReal_iff hb] at h3
  exact h3
private theorem eLpNorm_average_sub_le {Ω ι : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {Q : Finset ι} (hQ : Q.Nonempty) {P : ι → Ω → ℝ} (hint : ∀ v ∈ Q, Integrable (P v) μ) {κ κ' b e : ℝ} (hb : 0 ≤ b)
    (he : 0 ≤ e) (hZ : eLpNorm (fun u => (Q.card : ℝ)⁻¹ * ∑ v ∈ Q, P v u - κ') 16 μ ≤ ENNReal.ofReal b)
    (hv : ∀ v ∈ Q, |κ - ∫ u, P v u ∂μ| ≤ e) :
    eLpNorm (fun u => (Q.card : ℝ)⁻¹ * ∑ v ∈ Q, P v u - κ) 16 μ ≤ ENNReal.ofReal (2 * b + e) := by
  have hZi : Integrable (fun u => (Q.card : ℝ)⁻¹ * ∑ v ∈ Q, P v u) μ := (integrable_finsetSum Q hint).const_mul _
  have hcard : (0 : ℝ) < Q.card := by exact_mod_cast hQ.card_pos
  have hmean : ∫ u, (Q.card : ℝ)⁻¹ * ∑ v ∈ Q, P v u ∂μ = (Q.card : ℝ)⁻¹ * ∑ v ∈ Q, ∫ u, P v u ∂μ := by
    rw [integral_const_mul, integral_finsetSum _ hint]
  have h1 : |κ - ∫ u, (Q.card : ℝ)⁻¹ * ∑ v ∈ Q, P v u ∂μ| ≤ e := by
    have e1 : κ - ∫ u, (Q.card : ℝ)⁻¹ * ∑ v ∈ Q, P v u ∂μ = (Q.card : ℝ)⁻¹ * ∑ v ∈ Q, (κ - ∫ u, P v u ∂μ) := by
      rw [hmean, Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
      field_simp
    rw [e1, abs_mul, abs_of_pos (inv_pos.2 hcard)]
    calc (Q.card : ℝ)⁻¹ * |∑ v ∈ Q, (κ - ∫ u, P v u ∂μ)| ≤ (Q.card : ℝ)⁻¹ * ∑ _v ∈ Q, e :=
          mul_le_mul_of_nonneg_left ((Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum hv)) (inv_pos.2 hcard).le
      _ = e := by
          rw [Finset.sum_const, nsmul_eq_mul]
          field_simp
  have hm : AEStronglyMeasurable (fun u => (Q.card : ℝ)⁻¹ * ∑ v ∈ Q, P v u - κ') μ :=
    hZi.aestronglyMeasurable.sub aestronglyMeasurable_const
  have h2 := abs_integral_le_of_eLpNorm_sixteen hm hb hZ
  have h3 : ∫ u, ((Q.card : ℝ)⁻¹ * ∑ v ∈ Q, P v u - κ') ∂μ = ∫ u, (Q.card : ℝ)⁻¹ * ∑ v ∈ Q, P v u ∂μ - κ' := by
    rw [integral_sub hZi (integrable_const _)]
    simp
  rw [h3] at h2
  have h4 : |κ' - κ| ≤ b + e := by
    have a1 := abs_le.1 h1
    have a2 := abs_le.1 h2
    rw [abs_le]
    constructor <;> linarith [a1.1, a1.2, a2.1, a2.2]
  have h5 : (fun u => (Q.card : ℝ)⁻¹ * ∑ v ∈ Q, P v u - κ) =
      (fun u => (Q.card : ℝ)⁻¹ * ∑ v ∈ Q, P v u - κ') + fun _ => κ' - κ := by
    funext u
    simp
  rw [h5]
  refine (eLpNorm_add_le hm aestronglyMeasurable_const (by norm_num)).trans ?_
  have h6 : eLpNorm (fun _ : Ω => κ' - κ) 16 μ ≤ ENNReal.ofReal (b + e) := by
    rw [eLpNorm_const _ (by norm_num) (IsProbabilityMeasure.ne_zero μ), measure_univ, ENNReal.one_rpow, mul_one,
      Real.enorm_eq_ofReal_abs]
    exact ENNReal.ofReal_le_ofReal h4
  calc _ ≤ ENNReal.ofReal b + ENNReal.ofReal (b + e) := add_le_add hZ h6
    _ = ENNReal.ofReal (2 * b + e) := by
      rw [← ENNReal.ofReal_add hb (by positivity)]
      congr 1
      ring
private theorem eventually_rpow_mul_exp_clusterRange_le {rt : ℝ} (hrt : 0 < rt) (C : ℝ) :
    ∀ᶠ x : ℝ in atTop, x ^ C * Real.exp (-(4 * rt * (TorusLumps.clusterRange x : ℝ))) ≤ x ^ (-33 : ℝ) := by
  have h1 := (isLittleO_rpow_exp_pos_mul_atTop (100 * (C + 33)) (by positivity : 0 < 4 * rt)).bound
    (by norm_num : (0 : ℝ) < 1)
  have h2 : Tendsto (fun x : ℝ => x ^ ((1 : ℝ) / 100)) atTop atTop := tendsto_rpow_atTop (by norm_num)
  filter_upwards [h2.eventually h1, eventually_gt_atTop (0 : ℝ)] with x hx hx0
  have e1 : (x ^ ((1 : ℝ) / 100)) ^ (100 * (C + 33)) = x ^ (C + 33) := by
    rw [← Real.rpow_mul hx0.le]
    congr 1
    ring
  rw [e1, Real.norm_of_nonneg (Real.rpow_nonneg hx0.le _), Real.norm_of_nonneg (Real.exp_pos _).le, one_mul] at hx
  have hr : x ^ ((1 : ℝ) / 100) ≤ (TorusLumps.clusterRange x : ℝ) := Nat.le_ceil _
  have h3 : Real.exp (4 * rt * x ^ ((1 : ℝ) / 100)) ≤ Real.exp (4 * rt * (TorusLumps.clusterRange x : ℝ)) :=
    Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left hr (by positivity))
  have e2 : x ^ C = x ^ (C + 33) * x ^ (-33 : ℝ) := by
    rw [← Real.rpow_add hx0]
    congr 1
    ring
  rw [e2, Real.exp_neg]
  have hpos := Real.exp_pos (4 * rt * (TorusLumps.clusterRange x : ℝ))
  have hq : 0 < x ^ (-33 : ℝ) := Real.rpow_pos_of_pos hx0 _
  have h4 : x ^ (C + 33) * (Real.exp (4 * rt * (TorusLumps.clusterRange x : ℝ)))⁻¹ ≤ 1 := by
    rw [← div_eq_mul_inv, div_le_one hpos]
    exact hx.trans h3
  calc x ^ (C + 33) * x ^ (-33 : ℝ) * (Real.exp (4 * rt * (TorusLumps.clusterRange x : ℝ)))⁻¹ =
        x ^ (-33 : ℝ) * (x ^ (C + 33) * (Real.exp (4 * rt * (TorusLumps.clusterRange x : ℝ)))⁻¹) := by ring
    _ ≤ x ^ (-33 : ℝ) := mul_le_of_le_one_right hq.le h4
private theorem exists_averagingRadius_mul_inv_pow_le {L : ℝ} (hL : 2 ≤ L) (Xi : ℝ) {B : ℝ} (hB : 0 < B) :
    ∃ X₀ : ℝ, ∀ x, X₀ ≤ x → ∀ t : ℕ, x ≤ Xi + 2 * B * t → (averagingRadius x : ℝ) * (L ^ t)⁻¹ ≤ 1 / 8 := by
  have h1 : Tendsto (fun n : ℕ => (n : ℝ) ^ 1 / L ^ n) atTop (𝓝 0) :=
    tendsto_pow_const_div_const_pow_of_one_lt 1 (by linarith)
  have h2 : Tendsto (fun n : ℕ => (L⁻¹) ^ n) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity) (inv_lt_one_of_one_lt₀ (by linarith))
  have h3 : Tendsto (fun n : ℕ => (|Xi| + 2) * (L⁻¹) ^ n + 2 * B * ((n : ℝ) ^ 1 / L ^ n)) atTop (𝓝 0) := by
    simpa using (h2.const_mul (|Xi| + 2)).add (h1.const_mul (2 * B))
  obtain ⟨T₀, hT₀⟩ := eventually_atTop.1 (h3.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 8)))
  refine ⟨max 2 (Xi + 2 * B * T₀ + 1), fun x hx t hxt => ?_⟩
  have hx2 : 2 ≤ x := (le_max_left _ _).trans hx
  have hx3 : Xi + 2 * B * T₀ + 1 ≤ x := (le_max_right _ _).trans hx
  have ht : T₀ ≤ t := by
    have : (T₀ : ℝ) ≤ t := by
      have : 2 * B * T₀ ≤ 2 * B * t := by linarith
      exact le_of_mul_le_mul_left this (by positivity)
    exact_mod_cast this
  have h4 := hT₀ t ht
  have hm : (averagingRadius x : ℝ) ≤ x + 1 := by
    have e1 : averagingRadius x ≤ boxRadius x := Nat.div_le_self _ _
    have e2 : (boxRadius x : ℝ) ≤ x ^ ((1 : ℝ) / 27) + 1 := (Nat.ceil_lt_add_one (by positivity)).le
    have e3 : x ^ ((1 : ℝ) / 27) ≤ x ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
    rw [Real.rpow_one] at e3
    have e1' : (averagingRadius x : ℝ) ≤ boxRadius x := by exact_mod_cast e1
    linarith
  have h5 : x + 1 ≤ |Xi| + 2 + 2 * B * t := by linarith [le_abs_self Xi]
  calc (averagingRadius x : ℝ) * (L ^ t)⁻¹ ≤ (|Xi| + 2 + 2 * B * t) * (L ^ t)⁻¹ :=
        mul_le_mul_of_nonneg_right (hm.trans h5) (by positivity)
    _ = (|Xi| + 2) * (L⁻¹) ^ t + 2 * B * ((t : ℝ) ^ 1 / L ^ t) := by
        rw [inv_pow]
        field_simp
    _ ≤ 1 / 8 := h4.le
private theorem covariance_le_of_parts {x Rn C E mF mA mB N : ℝ} (hx : 1 ≤ x) (hRn : 1 ≤ Rn) (hC : 0 ≤ C) (hE0 : 0 ≤ E)
    (hE : E ≤ x ^ (-33 : ℝ))
    (hF : mF ≤ 2 * (C * x ^ (-(2 + 1 / 130) : ℝ)) + E + E ^ (1 / 16 : ℝ))
    (hA : mA ≤ C * x ^ (-(1 + 1 / 130) : ℝ) + E ^ (1 / 16 : ℝ))
    (hB : mB ≤ C * x ^ (-(1 + 1 / 130) : ℝ) + E ^ (1 / 16 : ℝ)) (hB0 : 0 ≤ mB)
    (hN : N ≤ Rn * mF + Rn ^ 2 * mA * mB) :
    N ≤ (Rn * (2 * C + 2) + Rn ^ 2 * (C + 1) ^ 2) * x ^ (-(2 + 1 / 130) : ℝ) := by
  have hx0 : 0 < x := by linarith
  have h1 : E ≤ x ^ (-(2 + 1 / 130) : ℝ) :=
    hE.trans (Real.rpow_le_rpow_of_exponent_le hx (by norm_num))
  have h2 : E ^ (1 / 16 : ℝ) ≤ x ^ (-(2 + 1 / 130) : ℝ) := by
    have e1 : E ^ (1 / 16 : ℝ) ≤ (x ^ (-33 : ℝ)) ^ (1 / 16 : ℝ) :=
      Real.rpow_le_rpow hE0 hE (by norm_num)
    rw [← Real.rpow_mul hx0.le] at e1
    exact e1.trans (Real.rpow_le_rpow_of_exponent_le hx (by norm_num))
  have h3 : x ^ (-(2 + 1 / 130) : ℝ) ≤ x ^ (-(1 + 1 / 130) : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hx (by norm_num)
  have h4 : x ^ (-(1 + 1 / 130) : ℝ) * x ^ (-(1 + 1 / 130) : ℝ) ≤ x ^ (-(2 + 1 / 130) : ℝ) := by
    rw [← Real.rpow_add hx0]
    exact Real.rpow_le_rpow_of_exponent_le hx (by norm_num)
  have hF' : mF ≤ (2 * C + 2) * x ^ (-(2 + 1 / 130) : ℝ) := by nlinarith
  have hA' : mA ≤ (C + 1) * x ^ (-(1 + 1 / 130) : ℝ) := by nlinarith
  have hB' : mB ≤ (C + 1) * x ^ (-(1 + 1 / 130) : ℝ) := by nlinarith
  have hAB : mA * mB ≤ (C + 1) ^ 2 * x ^ (-(2 + 1 / 130) : ℝ) := by
    calc mA * mB ≤ ((C + 1) * x ^ (-(1 + 1 / 130) : ℝ)) * ((C + 1) * x ^ (-(1 + 1 / 130) : ℝ)) :=
          mul_le_mul hA' hB' hB0 (by positivity)
      _ = (C + 1) ^ 2 * (x ^ (-(1 + 1 / 130) : ℝ) * x ^ (-(1 + 1 / 130) : ℝ)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left h4 (by positivity)
  have hR2 : 0 ≤ Rn ^ 2 := by positivity
  calc N ≤ Rn * mF + Rn ^ 2 * mA * mB := hN
    _ = Rn * mF + Rn ^ 2 * (mA * mB) := by ring
    _ ≤ Rn * ((2 * C + 2) * x ^ (-(2 + 1 / 130) : ℝ)) + Rn ^ 2 * ((C + 1) ^ 2 * x ^ (-(2 + 1 / 130) : ℝ)) :=
        add_le_add (mul_le_mul_of_nonneg_left hF' (by linarith)) (mul_le_mul_of_nonneg_left hAB hR2)
    _ = _ := by ring
private theorem flowHasExpansion_onParameters (h : ClusterExpansionOfAStep.FlowWhereExpansionReturns) :
    ResponseInTheExpansion.HoldsOnParameterFamilies fun T y => (T.stepParameters y).Admissible → ∀ β : ℝ,
      (T.stepParameters y).y₁ ≤ β → ClusterExpansionOfAStep.FlowHasExpansionAt (T.stepParameters y) β := by
  obtain ⟨C₀, h⟩ := h
  intro a _
  refine ⟨0, fun _ => 1, C₀, fun _ => one_pos, ?_⟩
  intro L _ _ T _ _ _ _ _ _ hCd
  exact ⟨0, fun y _ hR _ hF β hβ => ((h (T.stepParameters y) hF hCd hR).2 β hβ).1⟩
private theorem exists_isSignedAffine {D : ChessboardTori.ChessboardSetup} (g : ChessboardTori.ReflectionGrid D)
    (r : AmbientSpace → AmbientSpace) (h : g.IsProductOfCoordMaps r) :
    ∃ (σ : Fin 4 → ℤ) (w : AmbientSpace), IsSignedAffine r σ w := by
  have h1 : ∀ μ, ∃ (s : ℤ) (c : ℝ), (s = 1 ∨ s = -1) ∧ ∀ x, r x μ = (s : ℝ) * x μ + c := by
    intro μ
    rcases h μ with ⟨t, ht⟩ | ⟨k, hk⟩
    · refine ⟨1, 2 * t * g.cellSide, Or.inl rfl, fun x => ?_⟩
      have := ht x
      simp only [ChessboardTori.ReflectionGrid.coordShift] at this
      push_cast
      linarith
    · refine ⟨-1, 2 * g.origin μ + 2 * k * g.cellSide, Or.inr rfl, fun x => ?_⟩
      have := hk x
      simp only [ChessboardTori.ReflectionGrid.coordReflect] at this
      push_cast
      linarith
  choose σ c hσ hc using h1
  exact ⟨σ, c, hσ, fun x μ => hc μ x⟩
private def chessboardSetupOf (L : ℕ) (hL : Conventions.IsAdmissibleBlockingFactor L) (K : ℕ) (hK : 0 < K) (β : ℝ)
    (hβ : 0 < β) : ChessboardTori.ChessboardSetup :=
  ⟨⟨L, hL, ⟨K, hK⟩, 1⟩, β, hβ⟩
theorem covarianceApproxStatement_holds (h₁ : covarianceBoundByAveragesStatement) (h₂ : reflectionNormToBoxStatement)
    (h₃ : boxConcentrationStatement) (h₄ : separationLevelStatement) (h₅ : couplingAtSeparation_tendsto_statement)
    (h₆ : WeightedResponses.ResponsesBounded) (h₇ : covarianceReflectionInvariantStatement)
    (h₈ : FreeEnergies.scoredTowerExistsStatement) (h₉ : ResponseInTheExpansion.scoredTowerCoeffsAreChainStatement)
    (h₁₀ : ClusterExpansionOfAStep.FlowWhereExpansionReturns) (h₁₁ : ChessboardTori.GridBasicProperties.Statement)
    (h₁₂ : ResponseInTheExpansion.TwoPointByTotalCovarianceStatement) : covarianceApproxStatement := by
  have hQ := HoldsForShapes.and (HoldsForShapes.of_holdsOnParameters h₁) (HoldsForShapes.and h₂ (HoldsForShapes.and h₃
    (HoldsForShapes.and (HoldsForShapes.of_holdsOnParameters h₄) (HoldsForShapes.and (HoldsForShapes.of_holdsOnParameters h₅)
      (HoldsForShapes.and (HoldsForShapes.of_holdsOnParameters h₉)
        (HoldsForShapes.and (HoldsForShapes.of_holdsOnParameters (flowHasExpansion_onParameters h₁₀))
          HoldsForShapes.params))))))
  intro a ha
  obtain ⟨L₁, r₁, C₁, hr₁, H₁⟩ := hQ a ha
  obtain ⟨L₂, r₂, C₂', hr₂, H₂⟩ := h₈ a ha
  refine ⟨max L₁ L₂, fun c => min (r₁ c) (r₂ c), max C₁ C₂', fun c => lt_min (hr₁ c) (hr₂ c), ?_⟩
  intro L hodd hL Tb hTa hTL hD hCs hO hrt hCd
  obtain ⟨Kr, y₂, G₂⟩ := H₂ L hodd (le_of_max_le_right hL) Tb hTa hTL hD hCs hO (hrt.trans (min_le_right _ _))
    ((le_max_right _ _).trans hCd)
  obtain ⟨y₁, G₁⟩ := H₁ L hodd (le_of_max_le_left hL) Tb hTa hTL hD hCs hO (hrt.trans (min_le_left _ _))
    ((le_max_left _ _).trans hCd) Kr
  refine ⟨max y₁ y₂, fun y hy hR hW => ?_⟩
  have hRS : FreeEnergies.ExpansionHolds (Tb.stepParameters y) := ⟨hR, hW⟩
  have hSc := G₂ y (le_of_max_le_right hy) hRS
  have hKr : Kr.Admissible (Tb.stepParameters y) := by
    obtain ⟨T₀, S₀, hK₀, hr₀⟩ := hSc y 0 (fun j hj => by
      obtain rfl : j = 0 := by omega
      exact le_refl _)
    have h1 := (hr₀.isAdmissible 0 le_rfl).params_admissible
    rw [hr₀.params_eq 0, hK₀] at h1
    exact h1
  intro Xi hXi vt hvt hvt1
  obtain ⟨c1, c2, c3, c4, c5, c9, c10, hDr, hy0, -, -, -, -, -⟩ :=
    G₁ y (le_of_max_le_left hy) hRS hKr Xi hXi vt hvt hvt1
  have hFits : (Tb.stepParameters y).Admissible := hDr.fits y hy0
  have hJ : 11 * 2 ^ 12 * (Tb.stepParameters y).baseDepth < (Tb.stepParameters y).side := hFits.depth_lt
  have hScaleFlow := c10 hFits
  obtain ⟨Rn, hRn, hCov⟩ := c1 Xi hXi
  obtain ⟨C₂, d₂, hd₂, hS⟩ := c2
  obtain ⟨C₃, d₃, hd₃, hC⟩ := c3
  have hL16 : 2 ^ 16 ≤ (Tb.stepParameters y).side := hFits.L_ge
  have hL2 : (2 : ℝ) ≤ ((Tb.stepParameters y).side : ℝ) := by
    have : 2 ≤ (Tb.stepParameters y).side := by omega
    exact_mod_cast this
  obtain ⟨X₁, hX₁⟩ := exists_averagingRadius_mul_inv_pow_le hL2 Xi hFits.B_pos
  obtain ⟨X₂, hX₂⟩ := eventually_atTop.1
    ((eventually_rpow_mul_exp_clusterRange_le hFits.rt_pos C₂).and (eventually_ge_atTop (1 : ℝ)))
  obtain ⟨d₁, hd₁, hG⟩ := c5 Xi hXi (max X₁ X₂)
  obtain ⟨C', hC'⟩ : ∃ C', C' = max C₃ 0 := ⟨_, rfl⟩
  have hC'0 : 0 ≤ C' := hC' ▸ le_max_right _ _
  have hC'3 : C₃ ≤ C' := hC' ▸ le_max_left _ _
  refine ⟨Rn * (2 * C' + 2) + Rn ^ 2 * (C' + 1) ^ 2, min (min d₁ (1 / 80)) (min d₂ d₃),
    lt_min (lt_min hd₁ (by norm_num)) (lt_min hd₂ hd₃), ?_⟩
  intro d hd hdd K β hDat hcut f h hp μ hμ
  have hdd₁ : d ≤ d₁ := hdd.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hdd80 : d ≤ 1 / 80 := hdd.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hdd₂ : d ≤ d₂ := hdd.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hdd₃ : d ≤ d₃ := hdd.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hxX := hG d hd hdd₁ K β hDat hcut
  obtain ⟨-, hkK, -⟩ := c4 Xi hXi d hd (by linarith) K β hDat hcut
  obtain ⟨k, hk⟩ : ∃ k, k = separationLevel (Tb.stepParameters y) β K d := ⟨_, rfl⟩
  obtain ⟨x, hx⟩ : ∃ x, x = couplingAtSeparation (Tb.stepParameters y) β K d := ⟨_, rfl⟩
  obtain ⟨m, hm⟩ : ∃ m, m = averagingRadius x := ⟨_, rfl⟩
  rw [← hx]
  rw [← hk] at hkK
  rw [← hx] at hxX
  have hxk : x = ResponseInTheExpansion.flowCouplings (Tb.stepParameters y) β k := by rw [hx, hk]; rfl
  have hxe := hX₂ x ((le_max_right _ _).trans hxX)
  have hx1 : 1 ≤ x := hxe.2
  have hK2 := hDat.two_le
  have hβ1 : (Tb.stepParameters y).y₁ ≤ β := hDat.le_coupling 0 (Nat.zero_le _)
  have hβ : 0 < β := by linarith [hFits.y₁_ge]
  have hLs : Conventions.IsAdmissibleBlockingFactor (Tb.stepParameters y).side := ⟨hFits.L_odd, by omega⟩
  let D : ChessboardTori.ChessboardSetup := chessboardSetupOf (Tb.stepParameters y).side hLs K (by omega) β hβ
  obtain ⟨T, S, hSK, hSr⟩ := hSc β (K - 1) (fun j hj => hDat.le_coupling j (by omega))
  have hcu := hSr.isCutoff_bottom
  have hco := hSr.marksMeasurable
  have hst : ResponseInTheExpansion.IsTowerAtParameters Tb y T β (K - 1) := by
    refine ⟨hSr.startsAtWilson, fun j hj => ?_, fun j hj => (hSr.isFlowStep j hj).onFamily⟩
    cases j with
    | zero => exact (hSr.isFlowStep 0 (Nat.zero_le _)).coupling_eq
    | succ i => exact (hSr.isFlowStep i (by omega)).nextCoupling_eq
  obtain ⟨al, hala⟩ : ∃ al, al = S.coeffs := ⟨_, rfl⟩
  have hal : ResponseInTheExpansion.IsChainResponseCoeff (Tb.stepParameters y) Kr β k al := by
    have h1 := c9 β (K - 1) T S hSr
    rw [hSK, ← hala] at h1
    exact ⟨h1.zero_eq, fun j hj => h1.bounds j (by omega)⟩
  have hch : BoxResponses.IsStateChain Tb y Kr Xi d K β al T :=
    ⟨hDat, hcut, hk ▸ hal, hst, hcu, hco, ⟨S, hSK, hSr, hala.symm⟩⟩
  have : IsProbabilityMeasure (BoxResponses.stageLaw T β K k) :=
    (h₁₂ (Tb.stepParameters y) hFits hJ T hcu hco β al k (BoxResponses.boxSide (Tb.stepParameters y).side K k)).1
  have hup : ∀ t, t ≤ K →
      ResponseInTheExpansion.flowCouplings (Tb.stepParameters y) β (K - t) ≤ Xi + 2 * (Tb.stepParameters y).B * t := by
    intro t
    induction t with
    | zero =>
      intro _
      simpa using hDat.coupling_le_top
    | succ t ih =>
      intro ht
      have h1 := ih (by omega)
      have h2 := ((hScaleFlow β hβ1) (K - (t + 1))).2 (fun j hj => hDat.le_coupling j (by omega))
      rw [show K - (t + 1) + 1 = K - t by omega] at h2
      have h3 := (abs_le.1 h2).1
      have e1 : ResponseInTheExpansion.flowCouplings (Tb.stepParameters y) β (K - (t + 1)) =
          ClusterExpansionOfAStep.flowCoupling (Tb.stepParameters y) β (K - (t + 1)) := rfl
      have e2 : ResponseInTheExpansion.flowCouplings (Tb.stepParameters y) β (K - t) =
          ClusterExpansionOfAStep.flowCoupling (Tb.stepParameters y) β (K - t) := rfl
      rw [e2] at h1
      rw [e1]
      push_cast
      linarith
  have hxt : x ≤ Xi + 2 * (Tb.stepParameters y).B * ((K - k : ℕ) : ℝ) := by
    have := hup (K - k) (by omega)
    rwa [show K - (K - k) = k by omega, ← hxk] at this
  have hρ := hX₁ x ((le_max_left _ _).trans hxX) (K - k) hxt
  rw [← hm] at hρ
  obtain ⟨ρ, hρdef⟩ : ∃ ρ, ρ = (m : ℝ) * (((Tb.stepParameters y).side : ℝ) ^ (K - k))⁻¹ := ⟨_, rfl⟩
  rw [← hρdef] at hρ
  have hLpos : (0 : ℝ) < (Tb.stepParameters y).side := by linarith
  have hshift : ∀ v ∈ shiftSet m, ∀ μ, |latticeShift (Tb.stepParameters y).side K k v μ| ≤ ρ := by
    intro v hv μ
    simp only [shiftSet, Fintype.mem_piFinset, Finset.mem_Icc] at hv
    have h1 : |(v μ : ℝ)| ≤ m := by
      have h2 := hv μ
      rw [abs_le]
      constructor
      · exact_mod_cast h2.1
      · exact_mod_cast h2.2
    have e : ((Tb.stepParameters y).side : ℝ) ^ k / ((Tb.stepParameters y).side : ℝ) ^ K =
        (((Tb.stepParameters y).side : ℝ) ^ (K - k))⁻¹ := by
      have e1 : ((Tb.stepParameters y).side : ℝ) ^ K =
          ((Tb.stepParameters y).side : ℝ) ^ k * ((Tb.stepParameters y).side : ℝ) ^ (K - k) := by
        rw [← pow_add]
        congr 1
        omega
      rw [e1]
      field_simp
    simp only [latticeShift]
    rw [e, abs_mul, abs_of_pos (by positivity : 0 < (((Tb.stepParameters y).side : ℝ) ^ (K - k))⁻¹), hρdef]
    exact mul_le_mul_of_nonneg_right h1 (by positivity)
  have ha : 3 * D.mesh ≤ 1 / 4 := by
    have e1 : D.mesh = (((Tb.stepParameters y).side : ℝ) ^ K)⁻¹ := by
      simp [D, chessboardSetupOf, ChessboardTori.ChessboardSetup.mesh, PeriodicLattice.meshSize]
    rw [e1]
    have h1 : ((Tb.stepParameters y).side : ℝ) ≤ ((Tb.stepParameters y).side : ℝ) ^ K := le_self_pow₀ (by linarith) (by omega)
    have h2 : (12 : ℝ) ≤ (Tb.stepParameters y).side := by
      have : 12 ≤ (Tb.stepParameters y).side := by omega
      exact_mod_cast this
    have h3 : (((Tb.stepParameters y).side : ℝ) ^ K)⁻¹ ≤ 12⁻¹ := inv_anti₀ (by norm_num) (h2.trans h1)
    linarith
  have grid : ∀ F G : AmbientSpace → ℝ, IsNormalizedTestPair d vt F G → ∃ g : ChessboardTori.ReflectionGrid D, g.q = 0 ∧
      ∀ v ∈ shiftSet m, (CellAverages.IsDeepInCell g (translateBy D.L D.K k v F) ∧
          CellAverages.IsDeepInCell g (translateBy D.L D.K k v G)) ∧
        IsInteriorBy g (d / 2) (translateBy D.L D.K k v F) ∧ IsInteriorBy g (d / 2) (translateBy D.L D.K k v G) := by
    intro F G hFG
    obtain ⟨g, hq, hg⟩ := exists_reflectionGrid_centred D (ρ := ρ) hd hFG
    have h1 : 10 * d + ρ + D.mesh + 2 * D.mesh ≤ 1 / 2 := by linarith
    have h2 : 10 * d + ρ + D.mesh + d / 2 ≤ 1 / 2 := by linarith
    exact ⟨g, hq, fun v hv => ⟨⟨hg _ h1 _ (hshift v hv) F (Or.inl rfl), hg _ h1 _ (hshift v hv) G (Or.inr rfl)⟩,
      hg _ h2 _ (hshift v hv) F (Or.inl rfl), hg _ h2 _ (hshift v hv) G (Or.inr rfl)⟩⟩
  obtain ⟨g, hq, hin₀⟩ := grid f h hp
  have hin := fun v hv => (hin₀ v hv).1
  have hin₂ := fun v hv => (hin₀ v hv).2
  have hform := (h₁₁ D g).2.2.2.1
  have hx0 : 0 < x := by linarith
  have hE0 : 0 ≤ BoxResponses.markError (Tb.stepParameters y) C₂ x :=
    mul_nonneg (Real.rpow_nonneg hx0.le _) (Real.exp_pos _).le
  have hEx : BoxResponses.markError (Tb.stepParameters y) C₂ x ≤ x ^ (-33 : ℝ) := hxe.1
  have ht0 : 0 < x ^ (-(2 + 1 / 130) : ℝ) := Real.rpow_pos_of_pos hx0 _
  have hs0 : 0 < x ^ (-(1 + 1 / 130) : ℝ) := Real.rpow_pos_of_pos hx0 _
  have hS' := hS d hd hdd₂ D al T rfl hch k m x hk hx hm g hq f h hp hin₂
  have square : ∀ F : AmbientSpace → ℝ,
      MemLp (BoxResponses.boxResponse T β al K k F) 2 (BoxResponses.stageLaw T β K k) := by
    intro F
    obtain ⟨hmF, C, hCF⟩ := h₆ (Tb.stepParameters y) hFits hJ T hcu hco β al k
      (BoxResponses.boxSide (Tb.stepParameters y).side K k)
      (BoxResponses.unitTorusWeight (Tb.stepParameters y).side K k F)
    exact MemLp.of_bound hmF.aestronglyMeasurable C (hCF.mono fun u hu => hu)
  have centred : ∀ F G : AmbientSpace → ℝ,
      Integrable (fun u => BoxResponses.centeredBoxResponse T β al K k F u * BoxResponses.centeredBoxResponse T β al K k G u)
        (BoxResponses.stageLaw T β K k) :=
    fun F G => ((square F).sub (memLp_const _)).integrable_mul ((square G).sub (memLp_const _))
  obtain ⟨hbf, hbh⟩ := isBoundedBorel_of_testPair hp
  have hne : (shiftSet m).Nonempty := ⟨0, by simp [shiftSet]⟩
  have img : ∀ c ∈ (ReflectedCopies.minimalCounts D).indexBox,
      eLpNorm (fun u => BoxResponses.shiftAveragedProduct T β al K k m
          (fun v => gridImage g c (translateBy (Tb.stepParameters y).side K k v f))
          (fun v => gridImage g c (translateBy (Tb.stepParameters y).side K k v h)) u -
            unitTorusCovariance (Tb.stepParameters y).side K β f h) 16 (BoxResponses.stageLaw T β K k) ≤
        ENNReal.ofReal (2 * (C' * x ^ (-(2 + 1 / 130) : ℝ)) + BoxResponses.markError (Tb.stepParameters y) C₂ x) ∧
      ∀ w, (w = f ∨ w = h) →
        eLpNorm (BoxResponses.shiftAveragedResponse T β al K k m fun v =>
            gridImage g c (translateBy (Tb.stepParameters y).side K k v w)) 16 (BoxResponses.stageLaw T β K k) ≤
          ENNReal.ofReal (C' * x ^ (-(1 + 1 / 130) : ℝ)) := by
    intro c _
    obtain ⟨r, hr⟩ : ∃ r, r = g.mover (g.cell 0) (g.cell c) := ⟨_, rfl⟩
    obtain ⟨σ, w, hsw⟩ := exists_isSignedAffine g r.1 (hform.1 r.1 r.2)
    have hp' := hsw.isNormalizedTestPair_comp_symm hp
    obtain ⟨κ, hκ1, hκ2, hκ3⟩ := hC d hd hdd₃ K β al T hch k m x hk hx hm _ _ hp'
    obtain ⟨g', hq', hin'⟩ := grid _ _ hp'
    have h3 := (hS d hd hdd₂ D al T rfl hch k m x hk hx hm g' hq' _ _ hp' fun v hv => (hin' v hv).2).2.2
    have hnum := h₇ D g r f h hbf hbh
    have mono : ∀ B : ℝ, 0 < B → ENNReal.ofReal (C₃ * B) ≤ ENNReal.ofReal (C' * B) := fun B hB =>
      ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hC'3 hB.le)
    have key := eLpNorm_average_sub_le (Q := shiftSet m) (μ := BoxResponses.stageLaw T β K k)
      (P := fun v u =>
        BoxResponses.centeredBoxResponse T β al K k
            (translateBy (Tb.stepParameters y).side K k v fun x => f (r.1.symm x)) u *
          BoxResponses.centeredBoxResponse T β al K k
            (translateBy (Tb.stepParameters y).side K k v fun x => h (r.1.symm x)) u)
      hne (fun v _ => centred _ _)
      (κ := unitTorusCovariance (Tb.stepParameters y).side K β (fun x => f (r.1.symm x)) (fun x => h (r.1.symm x)))
      (κ' := κ) (b := C' * x ^ (-(2 + 1 / 130) : ℝ)) (e := BoxResponses.markError (Tb.stepParameters y) C₂ x)
      (mul_nonneg hC'0 ht0.le) hE0 (hκ1.trans (mono _ ht0)) h3
    refine ⟨?_, ?_⟩
    · have e1 : (fun u => BoxResponses.shiftAveragedProduct T β al K k m
            (fun v => gridImage g c (translateBy (Tb.stepParameters y).side K k v f))
            (fun v => gridImage g c (translateBy (Tb.stepParameters y).side K k v h)) u -
              unitTorusCovariance (Tb.stepParameters y).side K β f h) =
          fun u => BoxResponses.shiftAveragedProduct T β al K k m
              (fun v => translateBy (Tb.stepParameters y).side K k v fun x => f (r.1.symm x))
              (fun v => translateBy (Tb.stepParameters y).side K k v fun x => h (r.1.symm x)) u -
            unitTorusCovariance (Tb.stepParameters y).side K β (fun x => f (r.1.symm x)) (fun x => h (r.1.symm x)) := by
        funext u
        have e2 : unitTorusCovariance (Tb.stepParameters y).side K β (fun x => f (r.1.symm x)) (fun x => h (r.1.symm x)) =
          unitTorusCovariance (Tb.stepParameters y).side K β f h := hnum
        rw [e2]
        congr 1
        subst hr
        exact shiftAveragedProduct_comp_symm hsw T β al K k m f h u
      rw [e1]
      exact key
    · rintro w' (rfl | rfl)
      · have e1 : (BoxResponses.shiftAveragedResponse T β al K k m fun v =>
              gridImage g c (translateBy (Tb.stepParameters y).side K k v w')) =
            BoxResponses.shiftAveragedResponse T β al K k m fun v =>
              translateBy (Tb.stepParameters y).side K k v fun x => w' (r.1.symm x) := by
          subst hr
          exact shiftAveragedResponse_comp_symm hsw T β al K k m w'
        rw [e1]
        exact hκ2.trans (mono _ hs0)
      · have e1 : (BoxResponses.shiftAveragedResponse T β al K k m fun v =>
              gridImage g c (translateBy (Tb.stepParameters y).side K k v w')) =
            BoxResponses.shiftAveragedResponse T β al K k m fun v =>
              translateBy (Tb.stepParameters y).side K k v fun x => w' (r.1.symm x) := by
          subst hr
          exact shiftAveragedResponse_comp_symm hsw T β al K k m w'
        rw [e1]
        exact hκ3.trans (mono _ hs0)
  have hF := hS'.1 _ (add_nonneg (mul_nonneg zero_le_two (mul_nonneg hC'0 ht0.le)) hE0) (fun c hc => (img c hc).1)
  have hA := hS'.2.1 _ f (mul_nonneg hC'0 hs0.le) (Or.inl rfl) (fun c hc => (img c hc).2 f (Or.inl rfl))
  have hB := hS'.2.1 _ h (mul_nonneg hC'0 hs0.le) (Or.inr rfl) (fun c hc => (img c hc).2 h (Or.inr rfl))
  have hfin := hCov D rfl hDat g hq k m d vt hkK.le hd hvt hvt1 f h hp hin μ hμ
  exact covariance_le_of_parts hx1 hRn hC'0 hE0 hEx hF hA hB (Real.rpow_nonneg (norm_nonneg _) _) hfin
end YangMills.Construction.StateLaws
end
