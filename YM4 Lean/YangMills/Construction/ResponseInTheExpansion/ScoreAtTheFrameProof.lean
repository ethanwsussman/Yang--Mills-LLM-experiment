import YangMills.Construction.ColdChainAtEveryLevel.ChartsOfCellsAndSites
import YangMills.Construction.ColdStepAtMirrorFrames.LabelsOfTwoTops
import YangMills.Construction.ClusterExpansionOfAStep.MovesOfAField
import YangMills.Construction.ColdStepAtMirrorFrames.BlockMeansOfFormsOnATorus
import YangMills.Construction.ColdStepAtMirrorFrames.ThreeDerivativesOfAComposite
import YangMills.Construction.ResponseInTheExpansion.CalculusOfTheColdHalf
import YangMills.Construction.SummableBoundsOfTheFlow.BondsNearACellPairByOffsetsProof
import YangMills.Construction.SummableBoundsOfTheFlow.KernelsOfTheGapAboveTheFramesProof
import YangMills.Construction.SummableBoundsOfTheFlow.TheDensitiesAreNearTheirLimitsProof
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion Topology
namespace YangMills.Construction
open BlockAverages ColdStepAtMirrorFrames Interpolation WeightedResponses
namespace ResponseInTheExpansion
namespace ScoreRemainderAux
section Calculus
variable {P D : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [NormedAddCommGroup D] [NormedSpace ℝ D]
private structure DerivBoundedOn (g : D → ℝ) (U : Set D) (M : ℝ) : Prop where
  smooth : ∀ y ∈ U, ContDiffAt ℝ 3 g y
  bound : ∀ y ∈ U, ∀ j : ℕ, j ≤ 3 → ‖iteratedFDeriv ℝ j g y‖ ≤ M
private theorem DerivBoundedOn.norm_sub_le_mul {g : D → ℝ} {U : Set D} {M : ℝ} (h : DerivBoundedOn g U M)
    (hU : Convex ℝ U) {j : ℕ} (hj : j ≤ 2) {y y' : D} (hy : y ∈ U) (hy' : y' ∈ U) :
    ‖iteratedFDeriv ℝ j g y - iteratedFDeriv ℝ j g y'‖ ≤ M * ‖y - y'‖ := by
  have hd : ∀ z ∈ U, DifferentiableAt ℝ (iteratedFDeriv ℝ j g) z := fun z hz => by
    have h1 : ContDiffAt ℝ 1 (iteratedFDeriv ℝ j g) z :=
      (h.smooth z hz).iteratedFDeriv_right (m := 1) (i := j) (by
        have : ((1 + j : ℕ) : WithTop ℕ∞) ≤ ((3 : ℕ) : WithTop ℕ∞) := by
          exact_mod_cast (by omega : 1 + j ≤ 3)
        simpa using this)
    exact h1.differentiableAt (by norm_num)
  refine hU.norm_image_sub_le_of_norm_fderiv_le hd (fun z hz => ?_) hy' hy
  rw [norm_fderiv_iteratedFDeriv]
  exact h.bound z hz (j + 1) (by omega)
private theorem norm_apply_two_le {T : ContinuousMultilinearMap ℝ (fun _ : Fin 2 => D) ℝ} (a b : D) :
    ‖T ![a, b]‖ ≤ ‖T‖ * (‖a‖ * ‖b‖) := by
  have := T.le_opNorm ![a, b]
  simpa [Fin.prod_univ_two] using this
private theorem norm_apply_one_le {T : ContinuousMultilinearMap ℝ (fun _ : Fin 1 => D) ℝ} (a : D) :
    ‖T ![a]‖ ≤ ‖T‖ * ‖a‖ := by
  have := T.le_opNorm ![a]
  simpa using this
private theorem norm_apply_three_le {T : ContinuousMultilinearMap ℝ (fun _ : Fin 3 => D) ℝ} (a b c : D) :
    ‖T ![a, b, c]‖ ≤ ‖T‖ * (‖a‖ * ‖b‖ * ‖c‖) := by
  have := T.le_opNorm ![a, b, c]
  simpa [Fin.prod_univ_three] using this
private theorem norm_apply_two_sub_le {T : ContinuousMultilinearMap ℝ (fun _ : Fin 2 => D) ℝ} {a b a' b' : D}
    {B ε : ℝ} (ha : ‖a‖ ≤ B) (hb : ‖b‖ ≤ B) (ha' : ‖a'‖ ≤ B) (hb' : ‖b'‖ ≤ B) (h1 : ‖a - a'‖ ≤ ε)
    (h2 : ‖b - b'‖ ≤ ε) :
    ‖T ![a, b] - T ![a', b']‖ ≤ ‖T‖ * (2 * B * ε) := by
  have hB : 0 ≤ B := (norm_nonneg _).trans ha
  have hε : 0 ≤ ε := (norm_nonneg _).trans h1
  have e1 : ‖(![a, b] : Fin 2 → D)‖ ≤ B := by
    refine (pi_norm_le_iff_of_nonneg hB).mpr fun i => ?_
    fin_cases i <;> simpa
  have e2 : ‖(![a', b'] : Fin 2 → D)‖ ≤ B := by
    refine (pi_norm_le_iff_of_nonneg hB).mpr fun i => ?_
    fin_cases i <;> simpa
  have e3 : ‖(![a, b] : Fin 2 → D) - ![a', b']‖ ≤ ε := by
    refine (pi_norm_le_iff_of_nonneg hε).mpr fun i => ?_
    fin_cases i <;> simpa
  have := T.norm_image_sub_le ![a, b] ![a', b']
  refine this.trans ?_
  simp only [Fintype.card_fin, Nat.cast_ofNat, Nat.add_one_sub_one, pow_one]
  have h3 : max ‖(![a, b] : Fin 2 → D)‖ ‖(![a', b'] : Fin 2 → D)‖ ≤ B := max_le e1 e2
  calc ‖T‖ * 2 * max ‖(![a, b] : Fin 2 → D)‖ ‖(![a', b'] : Fin 2 → D)‖ * ‖(![a, b] : Fin 2 → D) - ![a', b']‖
      ≤ ‖T‖ * 2 * B * ε := by gcongr
    _ = ‖T‖ * (2 * B * ε) := by ring
private structure SecondOrderClose (α α' : P → D) (u v : P) (ε B : ℝ) : Prop where
  smooth : ContDiffAt ℝ 3 α 0
  smooth' : ContDiffAt ℝ 3 α' 0
  v0 : ‖α 0 - α' 0‖ ≤ ε
  d1u : ‖iteratedFDeriv ℝ 1 α 0 ![u] - iteratedFDeriv ℝ 1 α' 0 ![u]‖ ≤ ε
  d1v : ‖iteratedFDeriv ℝ 1 α 0 ![v] - iteratedFDeriv ℝ 1 α' 0 ![v]‖ ≤ ε
  d2 : ‖iteratedFDeriv ℝ 2 α 0 ![u, v] - iteratedFDeriv ℝ 2 α' 0 ![u, v]‖ ≤ ε
  b1u : ‖iteratedFDeriv ℝ 1 α 0 ![u]‖ ≤ B
  b1v : ‖iteratedFDeriv ℝ 1 α 0 ![v]‖ ≤ B
  b2 : ‖iteratedFDeriv ℝ 2 α 0 ![u, v]‖ ≤ B
  b1u' : ‖iteratedFDeriv ℝ 1 α' 0 ![u]‖ ≤ B
  b1v' : ‖iteratedFDeriv ℝ 1 α' 0 ![v]‖ ≤ B
  b2' : ‖iteratedFDeriv ℝ 2 α' 0 ![u, v]‖ ≤ B
end Calculus
section Composite
variable {P D : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [NormedAddCommGroup D] [NormedSpace ℝ D]
private theorem SecondOrderClose.comp (hC : ThirdOrderChainRule) {α α' : P → D} {u v : P} {ε B M : ℝ}
    {g : D → ℝ} {U : Set D} (h : SecondOrderClose α α' u v ε B) (hg : DerivBoundedOn g U M) (hU : Convex ℝ U)
    (hp : α 0 ∈ U) (hp' : α' 0 ∈ U) (hB : 1 ≤ B) :
    SecondOrderClose (g ∘ α) (g ∘ α') u v (8 * M * B ^ 2 * ε) (8 * M * B ^ 2) := by
  have hM : 0 ≤ M := (norm_nonneg _).trans (hg.bound _ hp 0 (by norm_num))
  have hε : 0 ≤ ε := (norm_nonneg _).trans h.v0
  have hB0 : 0 ≤ B := by linarith
  obtain ⟨s, e1, e2, -⟩ := hC g α 0 (hg.smooth _ hp) h.smooth
  obtain ⟨s', e1', e2', -⟩ := hC g α' 0 (hg.smooth _ hp') h.smooth'
  have m1 : ‖iteratedFDeriv ℝ 1 g (α 0)‖ ≤ M := hg.bound _ hp 1 (by norm_num)
  have m1' : ‖iteratedFDeriv ℝ 1 g (α' 0)‖ ≤ M := hg.bound _ hp' 1 (by norm_num)
  have m2 : ‖iteratedFDeriv ℝ 2 g (α 0)‖ ≤ M := hg.bound _ hp 2 (by norm_num)
  have m2' : ‖iteratedFDeriv ℝ 2 g (α' 0)‖ ≤ M := hg.bound _ hp' 2 (by norm_num)
  have l0 : ‖iteratedFDeriv ℝ 0 g (α 0) - iteratedFDeriv ℝ 0 g (α' 0)‖ ≤ M * ε :=
    (hg.norm_sub_le_mul hU (by norm_num) hp hp').trans (by gcongr; exact h.v0)
  have l1 : ‖iteratedFDeriv ℝ 1 g (α 0) - iteratedFDeriv ℝ 1 g (α' 0)‖ ≤ M * ε :=
    (hg.norm_sub_le_mul hU (by norm_num) hp hp').trans (by gcongr; exact h.v0)
  have l2 : ‖iteratedFDeriv ℝ 2 g (α 0) - iteratedFDeriv ℝ 2 g (α' 0)‖ ≤ M * ε :=
    (hg.norm_sub_le_mul hU (by norm_num) hp hp').trans (by gcongr; exact h.v0)
  have B2 : B ≤ B ^ 2 := by nlinarith
  have B1 : 1 ≤ B ^ 2 := by nlinarith
  have first : ∀ w : P, ‖iteratedFDeriv ℝ 1 α 0 ![w]‖ ≤ B →
      ‖iteratedFDeriv ℝ 1 α 0 ![w] - iteratedFDeriv ℝ 1 α' 0 ![w]‖ ≤ ε →
      ‖iteratedFDeriv ℝ 1 (g ∘ α) 0 ![w] - iteratedFDeriv ℝ 1 (g ∘ α') 0 ![w]‖ ≤ 8 * M * B ^ 2 * ε := by
    intro w hw hd
    rw [e1, e1']
    set a := iteratedFDeriv ℝ 1 α 0 ![w]
    set a' := iteratedFDeriv ℝ 1 α' 0 ![w]
    have t1 : ‖(iteratedFDeriv ℝ 1 g (α 0) - iteratedFDeriv ℝ 1 g (α' 0)) ![a]‖ ≤ M * ε * B :=
      (norm_apply_one_le a).trans (by gcongr)
    have t2 : ‖iteratedFDeriv ℝ 1 g (α' 0) ![a] - iteratedFDeriv ℝ 1 g (α' 0) ![a']‖ ≤ M * ε := by
      have : iteratedFDeriv ℝ 1 g (α' 0) ![a] - iteratedFDeriv ℝ 1 g (α' 0) ![a'] =
          iteratedFDeriv ℝ 1 g (α' 0) ![a - a'] := by
        have := (iteratedFDeriv ℝ 1 g (α' 0)).map_update_sub ![a] 0 a a'
        simpa [Function.update_apply] using this.symm
      rw [this]
      exact (norm_apply_one_le _).trans (by gcongr)
    have e : iteratedFDeriv ℝ 1 g (α 0) ![a] - iteratedFDeriv ℝ 1 g (α' 0) ![a'] =
        (iteratedFDeriv ℝ 1 g (α 0) - iteratedFDeriv ℝ 1 g (α' 0)) ![a] +
          (iteratedFDeriv ℝ 1 g (α' 0) ![a] - iteratedFDeriv ℝ 1 g (α' 0) ![a']) := by
      simp
    rw [e]
    refine (norm_add_le _ _).trans ?_
    have : M * ε * B + M * ε ≤ 8 * M * B ^ 2 * ε := by
      have h0 : 0 ≤ M * ε := mul_nonneg hM hε
      nlinarith
    linarith
  have bound1 : ∀ (w : P) (f : P → D), ContDiffAt ℝ 3 g (f 0) → ‖iteratedFDeriv ℝ 1 g (f 0)‖ ≤ M →
      (iteratedFDeriv ℝ 1 (g ∘ f) 0 ![w] = iteratedFDeriv ℝ 1 g (f 0) ![iteratedFDeriv ℝ 1 f 0 ![w]]) →
      ‖iteratedFDeriv ℝ 1 f 0 ![w]‖ ≤ B → ‖iteratedFDeriv ℝ 1 (g ∘ f) 0 ![w]‖ ≤ 8 * M * B ^ 2 := by
    intro w f _ hm he hw
    rw [he]
    refine (norm_apply_one_le _).trans ?_
    have : ‖iteratedFDeriv ℝ 1 g (f 0)‖ * ‖iteratedFDeriv ℝ 1 f 0 ![w]‖ ≤ M * B := by gcongr
    nlinarith [mul_nonneg hM hB0]
  have bound2 : ∀ (f : P → D), ‖iteratedFDeriv ℝ 1 g (f 0)‖ ≤ M → ‖iteratedFDeriv ℝ 2 g (f 0)‖ ≤ M →
      (iteratedFDeriv ℝ 2 (g ∘ f) 0 ![u, v] =
        iteratedFDeriv ℝ 2 g (f 0) ![iteratedFDeriv ℝ 1 f 0 ![u], iteratedFDeriv ℝ 1 f 0 ![v]] +
        iteratedFDeriv ℝ 1 g (f 0) ![iteratedFDeriv ℝ 2 f 0 ![u, v]]) →
      ‖iteratedFDeriv ℝ 1 f 0 ![u]‖ ≤ B → ‖iteratedFDeriv ℝ 1 f 0 ![v]‖ ≤ B →
      ‖iteratedFDeriv ℝ 2 f 0 ![u, v]‖ ≤ B → ‖iteratedFDeriv ℝ 2 (g ∘ f) 0 ![u, v]‖ ≤ 8 * M * B ^ 2 := by
    intro f h1 h2 he hu hv huv
    rw [he]
    refine (norm_add_le _ _).trans ?_
    have t1 := norm_apply_two_le (T := iteratedFDeriv ℝ 2 g (f 0)) (iteratedFDeriv ℝ 1 f 0 ![u])
      (iteratedFDeriv ℝ 1 f 0 ![v])
    have t2 := norm_apply_one_le (T := iteratedFDeriv ℝ 1 g (f 0)) (iteratedFDeriv ℝ 2 f 0 ![u, v])
    have t3 : ‖iteratedFDeriv ℝ 2 g (f 0)‖ * (‖iteratedFDeriv ℝ 1 f 0 ![u]‖ * ‖iteratedFDeriv ℝ 1 f 0 ![v]‖) ≤
        M * (B * B) := by gcongr
    have t4 : ‖iteratedFDeriv ℝ 1 g (f 0)‖ * ‖iteratedFDeriv ℝ 2 f 0 ![u, v]‖ ≤ M * B := by gcongr
    nlinarith [mul_nonneg hM hB0, mul_nonneg hM (mul_nonneg hB0 hB0)]
  refine ⟨s, s', ?_, first u h.b1u h.d1u, first v h.b1v h.d1v, ?_,
    bound1 u α (hg.smooth _ hp) m1 (e1 u) h.b1u, bound1 v α (hg.smooth _ hp) m1 (e1 v) h.b1v,
    bound2 α m1 m2 (e2 u v) h.b1u h.b1v h.b2,
    bound1 u α' (hg.smooth _ hp') m1' (e1' u) h.b1u', bound1 v α' (hg.smooth _ hp') m1' (e1' v) h.b1v',
    bound2 α' m1' m2' (e2' u v) h.b1u' h.b1v' h.b2'⟩
  · have e0 : ‖g (α 0) - g (α' 0)‖ ≤ M * ε := by
      have h0 := (iteratedFDeriv ℝ 0 g (α 0) - iteratedFDeriv ℝ 0 g (α' 0)).le_opNorm ![]
      simp only [ContinuousMultilinearMap.sub_apply, iteratedFDeriv_zero_apply, Finset.univ_eq_empty,
        Finset.prod_empty, mul_one] at h0
      exact h0.trans l0
    simp only [Function.comp]
    refine e0.trans ?_
    have h0 : 0 ≤ M * ε := mul_nonneg hM hε
    nlinarith
  · rw [e2, e2']
    set a := iteratedFDeriv ℝ 1 α 0 ![u]
    set a' := iteratedFDeriv ℝ 1 α' 0 ![u]
    set b := iteratedFDeriv ℝ 1 α 0 ![v]
    set b' := iteratedFDeriv ℝ 1 α' 0 ![v]
    set c := iteratedFDeriv ℝ 2 α 0 ![u, v]
    set c' := iteratedFDeriv ℝ 2 α' 0 ![u, v]
    have t1 : ‖(iteratedFDeriv ℝ 2 g (α 0) - iteratedFDeriv ℝ 2 g (α' 0)) ![a, b]‖ ≤ M * ε * (B * B) :=
      (norm_apply_two_le a b).trans (by gcongr; exacts [h.b1u, h.b1v])
    have t2 : ‖iteratedFDeriv ℝ 2 g (α' 0) ![a, b] - iteratedFDeriv ℝ 2 g (α' 0) ![a', b']‖ ≤
        M * (2 * B * ε) :=
      (norm_apply_two_sub_le h.b1u h.b1v h.b1u' h.b1v' h.d1u h.d1v).trans (by gcongr)
    have t3 : ‖(iteratedFDeriv ℝ 1 g (α 0) - iteratedFDeriv ℝ 1 g (α' 0)) ![c]‖ ≤ M * ε * B :=
      (norm_apply_one_le c).trans (by gcongr; exact h.b2)
    have t4 : ‖iteratedFDeriv ℝ 1 g (α' 0) ![c] - iteratedFDeriv ℝ 1 g (α' 0) ![c']‖ ≤ M * ε := by
      have : iteratedFDeriv ℝ 1 g (α' 0) ![c] - iteratedFDeriv ℝ 1 g (α' 0) ![c'] =
          iteratedFDeriv ℝ 1 g (α' 0) ![c - c'] := by
        have := (iteratedFDeriv ℝ 1 g (α' 0)).map_update_sub ![c] 0 c c'
        simpa [Function.update_apply] using this.symm
      rw [this]
      exact (norm_apply_one_le _).trans (by gcongr; exact h.d2)
    have e : iteratedFDeriv ℝ 2 g (α 0) ![a, b] + iteratedFDeriv ℝ 1 g (α 0) ![c] -
          (iteratedFDeriv ℝ 2 g (α' 0) ![a', b'] + iteratedFDeriv ℝ 1 g (α' 0) ![c']) =
        (iteratedFDeriv ℝ 2 g (α 0) - iteratedFDeriv ℝ 2 g (α' 0)) ![a, b] +
          (iteratedFDeriv ℝ 2 g (α' 0) ![a, b] - iteratedFDeriv ℝ 2 g (α' 0) ![a', b']) +
        ((iteratedFDeriv ℝ 1 g (α 0) - iteratedFDeriv ℝ 1 g (α' 0)) ![c] +
          (iteratedFDeriv ℝ 1 g (α' 0) ![c] - iteratedFDeriv ℝ 1 g (α' 0) ![c'])) := by
      simp only [ContinuousMultilinearMap.sub_apply]
      ring
    rw [e]
    refine (norm_add_le _ _).trans ?_
    refine (add_le_add ((norm_add_le _ _).trans (add_le_add t1 t2))
      ((norm_add_le _ _).trans (add_le_add t3 t4))).trans ?_
    have h0 : 0 ≤ M * ε := mul_nonneg hM hε
    nlinarith [mul_nonneg h0 hB0, mul_nonneg h0 (mul_nonneg hB0 hB0)]
end Composite
section Bounds
variable {D : Type} [NormedAddCommGroup D] [NormedSpace ℝ D]
private theorem DerivBoundedOn.mono {g : D → ℝ} {U U' : Set D} {M M' : ℝ} (h : DerivBoundedOn g U M)
    (hU : U' ⊆ U) (hM : M ≤ M') : DerivBoundedOn g U' M' :=
  ⟨fun y hy => h.smooth y (hU hy), fun y hy j hj => (h.bound y (hU hy) j hj).trans hM⟩
private theorem DerivBoundedOn.union {g : D → ℝ} {U U' : Set D} {M : ℝ} (h : DerivBoundedOn g U M)
    (h' : DerivBoundedOn g U' M) : DerivBoundedOn g (U ∪ U') M :=
  ⟨fun y hy => hy.elim (h.smooth y) (h'.smooth y),
    fun y hy j hj => hy.elim (fun e => h.bound y e j hj) fun e => h'.bound y e j hj⟩
private theorem derivBoundedOn_of_isCompact {g : D → ℝ} {K : Set D} (hK : IsCompact K)
    (hs : ∀ y ∈ K, ContDiffAt ℝ 3 g y) : ∃ M : ℝ, 1 ≤ M ∧ DerivBoundedOn g K M := by
  have hc : ∀ j : ℕ, j ≤ 3 → ∃ C : ℝ, ∀ y ∈ K, ‖iteratedFDeriv ℝ j g y‖ ≤ C := fun j hj =>
    hK.exists_bound_of_continuousOn fun y hy => by
      have h1 : ContDiffAt ℝ 0 (iteratedFDeriv ℝ j g) y :=
        (hs y hy).iteratedFDeriv_right (m := 0) (i := j) (by
          have : ((0 + j : ℕ) : WithTop ℕ∞) ≤ ((3 : ℕ) : WithTop ℕ∞) := by
            exact_mod_cast (by omega : 0 + j ≤ 3)
          simpa using this)
      exact h1.continuousAt.continuousWithinAt
  obtain ⟨C0, h0⟩ := hc 0 (by norm_num)
  obtain ⟨C1, h1⟩ := hc 1 (by norm_num)
  obtain ⟨C2, h2⟩ := hc 2 (by norm_num)
  obtain ⟨C3, h3⟩ := hc 3 (by norm_num)
  refine ⟨max 1 (max (max C0 C1) (max C2 C3)), le_max_left _ _, hs, fun y hy j hj => ?_⟩
  interval_cases j
  · exact (h0 y hy).trans (by simp)
  · exact (h1 y hy).trans (by simp)
  · exact (h2 y hy).trans (by simp)
  · exact (h3 y hy).trans (by simp)
end Bounds
private theorem DerivBoundedOn.comp_real (hC : ThirdOrderChainRule) {g h : ℝ → ℝ} {U K : Set ℝ} {M N : ℝ}
    (hg : DerivBoundedOn g U M) (hh : DerivBoundedOn h K N) (hm : ∀ y ∈ K, h y ∈ U) (hN : 1 ≤ N) :
    DerivBoundedOn (g ∘ h) K (5 * M * N ^ 3) := by
  have key : ∀ y ∈ K, ContDiffAt ℝ 3 (g ∘ h) y ∧
      ∀ j : ℕ, j ≤ 3 → ‖iteratedFDeriv ℝ j (g ∘ h) y‖ ≤ 5 * M * N ^ 3 := by
    intro y hy
    have hM : 0 ≤ M := (norm_nonneg _).trans (hg.bound _ (hm y hy) 0 (by norm_num))
    have hN0 : 0 ≤ N := by linarith
    have N1 : 1 ≤ N ^ 3 := one_le_pow₀ hN
    have N2 : N ≤ N ^ 3 := by nlinarith [mul_nonneg hN0 hN0]
    have N3 : N ^ 2 ≤ N ^ 3 := by nlinarith [mul_nonneg hN0 hN0]
    obtain ⟨s, e1, e2, e3⟩ := hC g h y (hg.smooth _ (hm y hy)) (hh.smooth y hy)
    have m1 := hg.bound _ (hm y hy) 1 (by norm_num)
    have m2 := hg.bound _ (hm y hy) 2 (by norm_num)
    have m3 := hg.bound _ (hm y hy) 3 (by norm_num)
    have n1 := hh.bound y hy 1 (by norm_num)
    have n2 := hh.bound y hy 2 (by norm_num)
    have n3 := hh.bound y hy 3 (by norm_num)
    have p1 : ∀ a : ℝ, ‖iteratedFDeriv ℝ 1 h y ![a]‖ ≤ N * ‖a‖ := fun a =>
      (norm_apply_one_le a).trans (by gcongr)
    have p2 : ∀ a b : ℝ, ‖iteratedFDeriv ℝ 2 h y ![a, b]‖ ≤ N * (‖a‖ * ‖b‖) := fun a b =>
      (norm_apply_two_le a b).trans (by gcongr)
    have p3 : ∀ a b c : ℝ, ‖iteratedFDeriv ℝ 3 h y ![a, b, c]‖ ≤ N * (‖a‖ * ‖b‖ * ‖c‖) := fun a b c =>
      (norm_apply_three_le a b c).trans (by gcongr)
    refine ⟨s, fun j hj => ?_⟩
    interval_cases j
    · have e0 : ‖iteratedFDeriv ℝ 0 (g ∘ h) y‖ = ‖g (h y)‖ := by
        rw [norm_iteratedFDeriv_zero]; rfl
      rw [e0]
      have := hg.bound _ (hm y hy) 0 (by norm_num)
      rw [norm_iteratedFDeriv_zero] at this
      refine this.trans ?_
      nlinarith
    · refine ContinuousMultilinearMap.opNorm_le_bound (by positivity) fun m => ?_
      have em : m = ![m 0] := by ext i; fin_cases i; rfl
      have t1 : ‖iteratedFDeriv ℝ 1 g (h y) ![iteratedFDeriv ℝ 1 h y ![m 0]]‖ ≤ M * (N * ‖m 0‖) :=
        (norm_apply_one_le _).trans (by gcongr; exact p1 _)
      have hA := norm_nonneg (m 0)
      have hq := mul_nonneg hM hA
      rw [Fin.prod_univ_one]
      have e0 : iteratedFDeriv ℝ 1 (g ∘ h) y m = iteratedFDeriv ℝ 1 (g ∘ h) y ![m 0] := by rw [← em]
      rw [e0, e1]
      refine t1.trans ?_
      have := mul_le_mul_of_nonneg_left N2 hq
      have h5 : 0 ≤ M * ‖m 0‖ * N ^ 3 := by positivity
      nlinarith
    · refine ContinuousMultilinearMap.opNorm_le_bound (by positivity) fun m => ?_
      have em : m = ![m 0, m 1] := by ext i; fin_cases i <;> rfl
      have hA := norm_nonneg (m 0)
      have hB := norm_nonneg (m 1)
      have t1 : ‖iteratedFDeriv ℝ 2 g (h y) ![iteratedFDeriv ℝ 1 h y ![m 0], iteratedFDeriv ℝ 1 h y ![m 1]]‖ ≤
          M * ((N * ‖m 0‖) * (N * ‖m 1‖)) :=
        (norm_apply_two_le _ _).trans (by gcongr <;> exact p1 _)
      have t2 : ‖iteratedFDeriv ℝ 1 g (h y) ![iteratedFDeriv ℝ 2 h y ![m 0, m 1]]‖ ≤
          M * (N * (‖m 0‖ * ‖m 1‖)) :=
        (norm_apply_one_le _).trans (by gcongr; exact p2 _ _)
      rw [Fin.prod_univ_two]
      have e0 : iteratedFDeriv ℝ 2 (g ∘ h) y m = iteratedFDeriv ℝ 2 (g ∘ h) y ![m 0, m 1] := by rw [← em]
      rw [e0, e2]
      refine (norm_add_le _ _).trans ((add_le_add t1 t2).trans ?_)
      have hq := mul_nonneg hM (mul_nonneg hA hB)
      have a1 := mul_le_mul_of_nonneg_left N2 hq
      have a2 := mul_le_mul_of_nonneg_left N3 hq
      have a3 : 0 ≤ M * (‖m 0‖ * ‖m 1‖) * N ^ 3 := by positivity
      nlinarith
    · refine ContinuousMultilinearMap.opNorm_le_bound (by positivity) fun m => ?_
      have em : m = ![m 0, m 1, m 2] := by ext i; fin_cases i <;> rfl
      have hA := norm_nonneg (m 0)
      have hB := norm_nonneg (m 1)
      have hD := norm_nonneg (m 2)
      have t1 : ‖iteratedFDeriv ℝ 3 g (h y) ![iteratedFDeriv ℝ 1 h y ![m 0], iteratedFDeriv ℝ 1 h y ![m 1],
          iteratedFDeriv ℝ 1 h y ![m 2]]‖ ≤ M * ((N * ‖m 0‖) * (N * ‖m 1‖) * (N * ‖m 2‖)) :=
        (norm_apply_three_le _ _ _).trans (by gcongr <;> exact p1 _)
      have t2 : ∀ a b c : ℝ,
          ‖iteratedFDeriv ℝ 2 g (h y) ![iteratedFDeriv ℝ 2 h y ![a, b], iteratedFDeriv ℝ 1 h y ![c]]‖ ≤
          M * ((N * (‖a‖ * ‖b‖)) * (N * ‖c‖)) := fun a b c =>
        (norm_apply_two_le _ _).trans (by gcongr; exacts [p2 _ _, p1 _])
      have t3 : ‖iteratedFDeriv ℝ 1 g (h y) ![iteratedFDeriv ℝ 3 h y ![m 0, m 1, m 2]]‖ ≤
          M * (N * (‖m 0‖ * ‖m 1‖ * ‖m 2‖)) :=
        (norm_apply_one_le _).trans (by gcongr; exact p3 _ _ _)
      rw [Fin.prod_univ_three]
      have e0 : iteratedFDeriv ℝ 3 (g ∘ h) y m = iteratedFDeriv ℝ 3 (g ∘ h) y ![m 0, m 1, m 2] := by
        rw [← em]
      rw [e0, e3]
      refine (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans
        (add_le_add ((norm_add_le _ _).trans (add_le_add t1 (t2 _ _ _))) (t2 _ _ _))) (t2 _ _ _))) t3 |>.trans ?_)
      have hq := mul_nonneg hM (mul_nonneg (mul_nonneg hA hB) hD)
      have a1 := mul_le_mul_of_nonneg_left N2 hq
      have a2 := mul_le_mul_of_nonneg_left N3 hq
      have a3 : 0 ≤ M * (‖m 0‖ * ‖m 1‖ * ‖m 2‖) * N ^ 3 := by positivity
      nlinarith
  exact ⟨fun y hy => (key y hy).1, fun y hy => (key y hy).2⟩
private theorem scoreRemainder_bounded_inner (hT : ScoreRemainderExpansion) {a : ℝ} (ha : 1 ≤ a) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ Q : ColdHalfLaw, Q.a = a → 2 / a ≤ Q.coupling →
      DerivBoundedOn Q.scoreRemainder (Set.Icc (9 / 16) (15 / 16)) M := by
  obtain ⟨C0, h0⟩ := hT.2 a ha 0
  obtain ⟨C1, h1⟩ := hT.2 a ha 1
  obtain ⟨C2, h2⟩ := hT.2 a ha 2
  obtain ⟨C3, h3⟩ := hT.2 a ha 3
  refine ⟨max 0 (max (max C0 C1) (max C2 C3)), le_max_left _ _, fun Q hQa hQx => ?_⟩
  have nb : ∀ r ∈ Set.Icc (9 / 16 : ℝ) (15 / 16), Set.Icc (1 / 2 : ℝ) 1 ∈ nhds r := fun r hr =>
    Icc_mem_nhds (by linarith [hr.1]) (by linarith [hr.2])
  have mem : ∀ r ∈ Set.Icc (9 / 16 : ℝ) (15 / 16), r ∈ Set.Icc (1 / 2 : ℝ) 1 := fun r hr =>
    ⟨by linarith [hr.1], by linarith [hr.2]⟩
  have hs : ∀ r ∈ Set.Icc (9 / 16 : ℝ) (15 / 16), ContDiffAt ℝ 3 Q.scoreRemainder r := fun r hr =>
    (h3 Q hQa hQx).1.contDiffAt (nb r hr)
  have bd : ∀ (j : ℕ) (C : ℝ), j ≤ 3 → (∀ r ∈ Set.Icc (1 / 2 : ℝ) 1,
      |iteratedDerivWithin j Q.scoreRemainder (Set.Icc (1 / 2) 1) r| ≤ C) →
      ∀ r ∈ Set.Icc (9 / 16 : ℝ) (15 / 16), ‖iteratedFDeriv ℝ j Q.scoreRemainder r‖ ≤ C := by
    intro j C hj hb r hr
    rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv]
    have e : iteratedDerivWithin j Q.scoreRemainder (Set.Icc (1 / 2) 1) r =
        iteratedDeriv j Q.scoreRemainder r := by
      have hj' : (j : WithTop ℕ∞) ≤ 3 := by exact_mod_cast hj
      exact iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc (by norm_num)) ((hs r hr).of_le hj')
        (mem r hr)
    rw [← e]
    exact hb r (mem r hr)
  refine ⟨hs, fun r hr j hj => ?_⟩
  interval_cases j
  · exact (bd 0 C0 (by norm_num) (h0 Q hQa hQx).2 r hr).trans (by simp)
  · exact (bd 1 C1 (by norm_num) (h1 Q hQa hQx).2 r hr).trans (by simp)
  · exact (bd 2 C2 (by norm_num) (h2 Q hQa hQx).2 r hr).trans (by simp)
  · exact (bd 3 C3 (by norm_num) (h3 Q hQa hQx).2 r hr).trans (by simp)
private def rescaled (Q : ColdHalfLaw) (l : ℝ) : ColdHalfLaw := { Q with coupling := l * Q.coupling }
private theorem scoreRemainder_rescaled (Q : ColdHalfLaw) {l : ℝ} (hl : 0 < l) (r : ℝ) :
    Q.scoreRemainder r = l⁻¹ * (rescaled Q l).scoreRemainder (r / l) := by
  unfold ColdHalfLaw.scoreRemainder rescaled
  simp only
  have hl' : l ≠ 0 := hl.ne'
  have e : Q.a * (l * Q.coupling) * (r / l) = Q.a * Q.coupling * r := by field_simp
  rw [e]
  by_cases ha : Q.a = 0
  · simp [ha]
  by_cases hr : r = 0
  · simp [hr]
  field_simp
private theorem DerivBoundedOn.const_mul {g : ℝ → ℝ} {U : Set ℝ} {M : ℝ} (h : DerivBoundedOn g U M) (c : ℝ) :
    DerivBoundedOn (fun r => c * g r) U (|c| * M) := by
  refine ⟨fun y hy => contDiffAt_const.mul (h.smooth y hy), fun y hy j hj => ?_⟩
  have hj' : (j : WithTop ℕ∞) ≤ 3 := by exact_mod_cast hj
  have e : iteratedFDeriv ℝ j (fun r => c * g r) y = c • iteratedFDeriv ℝ j g y := by
    have := iteratedFDeriv_const_smul_apply (𝕜 := ℝ) (i := j) (a := c) (f := g) (x := y)
      ((h.smooth y hy).of_le hj')
    simpa [Pi.smul_def] using this
  rw [e, norm_smul, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_left (h.bound y hy j hj) (abs_nonneg _)
private theorem scoreRemainder_bounded (hC : ThirdOrderChainRule) (hT : ScoreRemainderExpansion) {a : ℝ}
    (ha : 1 ≤ a) :
    ∃ M : ℝ, 1 ≤ M ∧ ∀ Q : ColdHalfLaw, Q.a = a → 3 / a ≤ Q.coupling →
      DerivBoundedOn Q.scoreRemainder (Set.Icc (1 / 2) 1) M ∧
      DerivBoundedOn (Q.scoreRemainder ∘ Real.exp) (Set.Icc (Real.log (1 / 2)) 0) M ∧
      DerivBoundedOn (Q.scoreRemainder ∘ Real.sqrt) (Set.Icc (1 / 4) 1) M := by
  obtain ⟨M₀, hM₀, hin⟩ := scoreRemainder_bounded_inner hT ha
  have ha0 : 0 < a := by linarith
  have hdiv : ∀ l : ℝ, 0 < l → ∃ N : ℝ, 1 ≤ N ∧
      DerivBoundedOn (fun r : ℝ => r / l) (Set.Icc (l * (9 / 16)) (l * (15 / 16))) N := by
    intro l hl
    refine derivBoundedOn_of_isCompact isCompact_Icc fun y _ => ?_
    exact (contDiffAt_id.div_const l)
  obtain ⟨N₁, hN₁, b₁⟩ := hdiv (8 / 9) (by norm_num)
  obtain ⟨N₂, hN₂, b₂⟩ := hdiv (4 / 3) (by norm_num)
  obtain ⟨Ne, hNe, be⟩ := derivBoundedOn_of_isCompact (g := Real.exp)
    (isCompact_Icc (a := Real.log (1 / 2)) (b := 0)) fun y _ => Real.contDiff_exp.contDiffAt
  obtain ⟨Nq, hNq, bq⟩ := derivBoundedOn_of_isCompact (g := Real.sqrt) (isCompact_Icc (a := (1 / 4 : ℝ)) (b := 1))
    fun y hy => Real.contDiffAt_sqrt (by have := hy.1; intro h0; rw [h0] at this; norm_num at this)
  have scaledAt : ∀ (l N : ℝ), 8 / 9 ≤ l → 1 ≤ N →
      DerivBoundedOn (fun r : ℝ => r / l) (Set.Icc (l * (9 / 16)) (l * (15 / 16))) N →
      ∀ Q : ColdHalfLaw, Q.a = a → 3 / a ≤ Q.coupling →
      DerivBoundedOn Q.scoreRemainder (Set.Icc (l * (9 / 16)) (l * (15 / 16))) (5 * (|l⁻¹| * M₀) * N ^ 3) := by
    intro l N hl hN hb Q hQa hQx
    have hl0 : 0 < l := by linarith
    have hx : 2 / a ≤ (rescaled Q l).coupling := by
      have e0 : (rescaled Q l).coupling = l * Q.coupling := rfl
      rw [e0]
      have h1 : 3 / a * (8 / 9) ≤ Q.coupling * l := by
        have : 0 ≤ 3 / a := by positivity
        nlinarith
      have h2 : 2 / a ≤ 3 / a * (8 / 9) := by
        rw [div_mul_eq_mul_div, div_le_div_iff_of_pos_right ha0]
        norm_num
      linarith
    have h1 := (hin (rescaled Q l) hQa hx).const_mul l⁻¹
    have h2 := DerivBoundedOn.comp_real hC h1 hb (fun y hy => by
      refine ⟨?_, ?_⟩
      · rw [le_div_iff₀ hl0]; linarith [hy.1]
      · rw [div_le_iff₀ hl0]; linarith [hy.2]) hN
    have e : Q.scoreRemainder = (fun s => l⁻¹ * (rescaled Q l).scoreRemainder s) ∘ fun r : ℝ => r / l := by
      funext r
      exact scoreRemainder_rescaled Q hl0 r
    rw [e]
    exact h2
  set M₁ := 5 * (|(8 / 9 : ℝ)⁻¹| * M₀) * N₁ ^ 3 with hM₁
  set M₂ := 5 * (|(4 / 3 : ℝ)⁻¹| * M₀) * N₂ ^ 3 with hM₂
  set Mt := max M₁ M₂ with hMt
  refine ⟨max 1 (max Mt (max (5 * Mt * Ne ^ 3) (5 * Mt * Nq ^ 3))), le_max_left _ _, fun Q hQa hQx => ?_⟩
  have t1 := (scaledAt (8 / 9) N₁ le_rfl hN₁ b₁ Q hQa hQx).mono subset_rfl (le_max_left M₁ M₂)
  have t2 := (scaledAt (4 / 3) N₂ (by norm_num) hN₂ b₂ Q hQa hQx).mono subset_rfl (le_max_right M₁ M₂)
  have t3 : DerivBoundedOn Q.scoreRemainder (Set.Icc (1 / 2) 1) Mt := (t1.union t2).mono (fun r hr => by
    by_cases h : r ≤ 5 / 6
    · exact Or.inl ⟨by norm_num; linarith [hr.1], by norm_num; linarith⟩
    · exact Or.inr ⟨by norm_num; linarith, by norm_num; linarith [hr.2]⟩) le_rfl
  refine ⟨t3.mono subset_rfl ?_, (DerivBoundedOn.comp_real hC t3 be ?_ hNe).mono subset_rfl ?_,
    (DerivBoundedOn.comp_real hC t3 bq ?_ hNq).mono subset_rfl ?_⟩
  · exact (le_max_left _ _).trans (le_max_right _ _)
  · intro y hy
    refine ⟨?_, Real.exp_le_one_iff.mpr hy.2⟩
    have := Real.exp_le_exp.mpr hy.1
    rwa [Real.exp_log (by norm_num)] at this
  · exact (le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  · intro y hy
    refine ⟨?_, Real.sqrt_le_one.mpr hy.2⟩
    have h4 : (1 / 2 : ℝ) = Real.sqrt (1 / 4) := by
      rw [show (1 / 4 : ℝ) = (1 / 2) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
    rw [h4]
    exact Real.sqrt_le_sqrt hy.1
  · exact (le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
private abbrev Offset : Type := Fin 4 → ℤ
private abbrev OffsetBond : Type := Offset × Fin 4
private def bondWord : Offset → List PathStep → List (OffsetBond × Bool)
  | _, [] => []
  | z, st :: r =>
    if st.2 then ((z, st.1), true) :: bondWord (z + Pi.single st.1 1) r
    else ((z - Pi.single st.1 1, st.1), false) :: bondWord (z - Pi.single st.1 1) r
private def wordProduct (A : OffsetBond → ℍ[ℝ]) : List (OffsetBond × Bool) → ℍ[ℝ]
  | [] => 1
  | e :: r => (if e.2 then A e.1 else star (A e.1)) * wordProduct A r
private theorem siteCoords_add {F : BlockFrame} (j : ℕ) (a b : Offset) :
    (siteOfCoords j (a + b) : F.Site j) = siteOfCoords j a + siteOfCoords j b := by apply _root_.YangMills.Construction.BlockAverages.siteOfCoords_add <;> assumption
private theorem siteCoords_neg {F : BlockFrame} (j : ℕ) (a : Offset) :
    (siteOfCoords j (-a) : F.Site j) = - siteOfCoords j a := by apply _root_.YangMills.Construction.BlockAverages.siteOfCoords_neg <;> assumption
private theorem siteCoords_zero {F : BlockFrame} (j : ℕ) : (siteOfCoords j (0 : Offset) : F.Site j) = 0 := by apply _root_.YangMills.Construction.BlockAverages.siteOfCoords_zero <;> assumption
private theorem wordProduct_congr {A A' : OffsetBond → ℍ[ℝ]} {l : List (OffsetBond × Bool)}
    (h : ∀ e ∈ l, A e.1 = A' e.1) : wordProduct A l = wordProduct A' l := by
  induction l with
  | nil => rfl
  | cons e r ih =>
    simp only [wordProduct]
    rw [h e (by simp), ih fun e' he' => h e' (by simp [he'])]
private theorem pathHolonomy_eq_wordProduct {F : BlockFrame} {j : ℕ} (X : F.GaugeField j) (s : F.Site j)
    (l : List PathStep) (z : Offset) :
    ((pathHolonomy X (s + siteOfCoords j z) l : UnitQuaternion) : ℍ[ℝ]) =
      wordProduct (fun b => ((X (s + siteOfCoords j b.1) b.2 : UnitQuaternion) : ℍ[ℝ])) (bondWord z l) := by
  induction l generalizing z with
  | nil => simp [pathHolonomy, bondWord, wordProduct]
  | cons st r ih =>
    rcases st with ⟨d, fw⟩
    have eu : (unitStep j d : F.Site j) = siteOfCoords j (Pi.single d 1) := rfl
    cases fw
    · have e1 : (s + siteOfCoords j z + stepDisplacement j (d, false) : F.Site j) =
          s + siteOfCoords j (z - Pi.single d 1) := by
        simp only [stepDisplacement, Bool.false_eq_true, if_false, eu, sub_eq_add_neg, siteCoords_add,
          siteCoords_neg, add_assoc]
      have e2 : (s + siteOfCoords j z - unitStep j d : F.Site j) = s + siteOfCoords j (z - Pi.single d 1) := by
        simp only [eu, sub_eq_add_neg, siteCoords_add, siteCoords_neg, add_assoc]
      simp only [pathHolonomy, linkValue, bondWord, wordProduct, Bool.false_eq_true, if_false, e1, e2]
      rw [Submonoid.coe_mul, ih]
      simp [TorusFields.coe_inv_unitQuaternion]
    · have e1 : (s + siteOfCoords j z + stepDisplacement j (d, true) : F.Site j) =
          s + siteOfCoords j (z + Pi.single d 1) := by
        simp only [stepDisplacement, if_true, eu, siteCoords_add, add_assoc]
      simp only [pathHolonomy, linkValue, bondWord, wordProduct, if_true, e1]
      rw [Submonoid.coe_mul, ih]
private theorem bondWord_near (l : List PathStep) (z : Offset) :
    ∀ e ∈ bondWord z l, ∀ i, |e.1.1 i - z i| ≤ l.length := by
  induction l generalizing z with
  | nil => simp [bondWord]
  | cons st r ih =>
    rcases st with ⟨d, fw⟩
    have hs : ∀ i, |(Pi.single d 1 : Offset) i| ≤ 1 := fun i => by
      by_cases h : i = d
      · subst h; simp
      · simp [Pi.single_eq_of_ne h]
    intro e he i
    cases fw
    · simp only [bondWord, Bool.false_eq_true, if_false, List.mem_cons] at he
      rcases he with rfl | he
      · have := hs i
        simp only [List.length_cons, Nat.cast_add, Nat.cast_one, Pi.sub_apply]
        rw [show z i - (Pi.single d 1 : Offset) i - z i = -(Pi.single d 1 : Offset) i by ring, abs_neg]
        linarith
      · have h1 := ih _ e he i
        have h2 := hs i
        simp only [Pi.sub_apply] at h1
        simp only [List.length_cons, Nat.cast_add, Nat.cast_one]
        have h3 : e.1.1 i - z i =
            (e.1.1 i - (z i - (Pi.single d 1 : Offset) i)) + -(Pi.single d 1 : Offset) i := by ring
        rw [h3]
        refine (abs_add_le _ _).trans ?_
        rw [abs_neg]
        linarith
    · simp only [bondWord, if_true, List.mem_cons] at he
      rcases he with rfl | he
      · simp only [List.length_cons, Nat.cast_add, Nat.cast_one, sub_self, abs_zero]
        positivity
      · have h1 := ih _ e he i
        have h2 := hs i
        simp only [Pi.add_apply] at h1
        simp only [List.length_cons, Nat.cast_add, Nat.cast_one]
        have h3 : e.1.1 i - z i =
            (e.1.1 i - (z i + (Pi.single d 1 : Offset) i)) + (Pi.single d 1 : Offset) i := by ring
        rw [h3]
        refine (abs_add_le _ _).trans ?_
        linarith
private theorem axisPath_length_le (h : Offset) (π : Equiv.Perm (Fin 4)) {L : ℕ} (hh : h ∈ centredCube L) :
    (axisPath h π).length ≤ 4 * L := by
  have hb : ∀ i, (h i).natAbs ≤ L := fun i => by
    have := (BlockOffsets.mem_centredCube_iff h).mp hh i
    unfold BlockOffsets.halfSide at this
    omega
  have h0 := hb (π 0)
  have h1 := hb (π 1)
  have h2 := hb (π 2)
  have h3 := hb (π 3)
  simp [axisPath, List.finRange_succ]
  omega
private theorem bondContour_length_le (L : ℕ) (h : Offset) (π : Equiv.Perm (Fin 4)) (i : Fin 4)
    (hh : h ∈ centredCube L) : (bondContour L h π i).length ≤ 9 * L := by
  have := axisPath_length_le h π hh
  simp [bondContour, reversePath]
  omega
private def contourBox (L : ℕ) : Finset OffsetBond :=
  (Fintype.piFinset fun _ : Fin 4 => Finset.Icc (-(9 * L : ℤ)) (9 * L)) ×ˢ Finset.univ
private theorem bondWord_mem_contourBox {L : ℕ} {h : Offset} (hh : h ∈ centredCube L) (π : Equiv.Perm (Fin 4))
    (i : Fin 4) {e : OffsetBond × Bool} (he : e ∈ bondWord 0 (bondContour L h π i)) : e.1 ∈ contourBox L := by
  have h1 := bondWord_near _ _ e he
  have h2 := bondContour_length_le L h π i hh
  simp only [contourBox, Finset.mem_product, Fintype.mem_piFinset, Finset.mem_Icc, Finset.mem_univ, and_true]
  intro l
  have h3 := h1 l
  have h4 : ((bondContour L h π i).length : ℤ) ≤ 9 * L := by exact_mod_cast h2
  simp only [Pi.zero_apply, sub_zero] at h3
  exact abs_le.mp (h3.trans h4)
private abbrev BoxSlot (L : ℕ) : Type := ↥(contourBox L) × Fin 3
private abbrev BoxData (L : ℕ) : Type := BoxSlot L → ℍ[ℝ]
private def boxLink {L : ℕ} (A : BoxData L) (b : OffsetBond) : ℍ[ℝ] :=
  if h : b ∈ contourBox L then
    NormedSpace.exp (A (⟨b, h⟩, 0)) * NormedSpace.exp (A (⟨b, h⟩, 1)) * A (⟨b, h⟩, 2)
  else 1
private def boxContourAverage (L : ℕ) (i : Fin 4) (A : BoxData L) : ℍ[ℝ] :=
  (1 / (24 * (L : ℝ) ^ 4)) • ∑ h ∈ centredCube L, ∑ π : Equiv.Perm (Fin 4),
    wordProduct (boxLink A) (bondWord 0 (bondContour L h π i))
private def boxSizeSq (L : ℕ) (i : Fin 4) (A : BoxData L) : ℝ := ‖boxContourAverage L i A‖ ^ 2
private theorem contDiff_quaternionExp : ContDiff ℝ 3 (NormedSpace.exp : ℍ[ℝ] → ℍ[ℝ]) :=
  contDiff_iff_contDiffAt.2 fun x => (NormedSpace.exp_analytic (𝕂 := ℝ) x).contDiffAt
private theorem contDiff_quaternionStar : ContDiff ℝ 3 (star : ℍ[ℝ] → ℍ[ℝ]) :=
  (LinearMap.toContinuousLinearMap
    ({ toFun := star, map_add' := star_add, map_smul' := fun r x => Quaternion.star_smul r x } :
      ℍ[ℝ] →ₗ[ℝ] ℍ[ℝ])).contDiff
private theorem contDiff_boxLink {L : ℕ} (b : OffsetBond) : ContDiff ℝ 3 fun A : BoxData L => boxLink A b := by
  unfold boxLink
  by_cases h : b ∈ contourBox L
  · simp only [h, dif_pos]
    have p : ∀ s : BoxSlot L, ContDiff ℝ 3 fun A : BoxData L => A s := fun s => contDiff_apply ℝ ℍ[ℝ] s
    exact ((contDiff_quaternionExp.comp (p _)).mul (contDiff_quaternionExp.comp (p _))).mul (p _)
  · simp only [h, dif_neg, not_false_eq_true]
    exact contDiff_const
private theorem contDiff_wordProduct {L : ℕ} (l : List (OffsetBond × Bool)) :
    ContDiff ℝ 3 fun A : BoxData L => wordProduct (boxLink A) l := by
  induction l with
  | nil => exact contDiff_const
  | cons e r ih =>
    simp only [wordProduct]
    refine ContDiff.mul ?_ ih
    cases e.2
    · simp only [Bool.false_eq_true, if_false]
      exact contDiff_quaternionStar.comp (contDiff_boxLink e.1)
    · simp only [if_true]
      exact contDiff_boxLink e.1
private theorem contDiff_boxSizeSq (L : ℕ) (i : Fin 4) : ContDiff ℝ 3 (boxSizeSq L i) := by
  unfold boxSizeSq
  refine (contDiff_norm_sq ℝ).comp ?_
  unfold boxContourAverage
  refine ContDiff.const_smul _ ?_
  refine ContDiff.sum fun h _ => ContDiff.sum fun π _ => contDiff_wordProduct _
section FrameData
variable {F : BlockFrame}
private def spreadCLM {k : ℕ} (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions) (y : F.Cell)
    (i : Fin 4) : (Fin k → ℝ) →L[ℝ] ℍ[ℝ] :=
  ∑ l, if c l = (y, i) then
    (ContinuousLinearMap.proj l : (Fin k → ℝ) →L[ℝ] ℝ).smulRight (X l : ℍ[ℝ]) else 0
private theorem spreadCLM_apply {k : ℕ} (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions)
    (y : F.Cell) (i : Fin 4) (τ : Fin k → ℝ) :
    spreadCLM c X y i τ = ((ColdStepAtMirrorFrames.bondSpread c X τ y i : imaginaryQuaternions) : ℍ[ℝ]) := by
  rw [spreadCLM, _root_.sum_apply]
  simp only [ColdStepAtMirrorFrames.bondSpread]
  rw [AddSubmonoidClass.coe_finsetSum]
  refine Finset.sum_congr rfl fun l _ => ?_
  split_ifs <;> simp
private theorem norm_spreadCLM_le {k : ℕ} (c : Fin k → F.Site F.top × Fin 4) {X : Fin k → imaginaryQuaternions}
    (hX : AreUnitVectors X) (y : F.Cell) (i : Fin 4) : ‖spreadCLM c X y i‖ ≤ k := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun σ => ?_
  rw [spreadCLM_apply]
  simp only [ColdStepAtMirrorFrames.bondSpread]
  rw [AddSubmonoidClass.coe_finsetSum]
  calc ‖∑ l, (((if c l = (y, i) then σ l • X l else 0 : imaginaryQuaternions)) : ℍ[ℝ])‖
      ≤ ∑ l, ‖(((if c l = (y, i) then σ l • X l else 0 : imaginaryQuaternions)) : ℍ[ℝ])‖ := norm_sum_le _ _
    _ ≤ ∑ _l : Fin k, ‖σ‖ := by
        refine Finset.sum_le_sum fun l _ => ?_
        split_ifs
        · have h1 : ‖((X l : imaginaryQuaternions) : ℍ[ℝ])‖ = 1 := hX l
          have h2 : (((σ l • X l : imaginaryQuaternions)) : ℍ[ℝ]) = σ l • ((X l : imaginaryQuaternions) : ℍ[ℝ]) :=
            rfl
          rw [h2, norm_smul, h1, mul_one]
          exact norm_le_pi_norm σ l
        · simp
    _ = k * ‖σ‖ := by simp
open Classical in
private def frameSlot (w : F.Site F.depth × Fin 4 → F.GaugeField F.top → imaginaryQuaternions)
    (V : F.GaugeField F.top) {k : ℕ} (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions)
    (x : F.Site F.depth) (d : Fin 4) (τ : Fin k → ℝ) : ℍ[ℝ] :=
  if IsAxialTreeBond (x, d) then 0
  else ((w (x, d) (leftTranslate (ColdStepAtMirrorFrames.bondSpread c X τ) V) : imaginaryQuaternions) : ℍ[ℝ])
open Classical in
private def moveSlot {k : ℕ} (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions)
    (x : F.Site F.depth) (d : Fin 4) (τ : Fin k → ℝ) : ℍ[ℝ] :=
  if IsCrossingBond (x, d) then spreadCLM c X (enclosingCell x) d τ else 0
open Classical in
private def topSlot (V : F.GaugeField F.top) (x : F.Site F.depth) (d : Fin 4) : ℍ[ℝ] :=
  if IsCrossingBond (x, d) then ((V (enclosingCell x) d : UnitQuaternion) : ℍ[ℝ]) else 1
private def boxSite (Z : F.Cell) (z : Offset) : F.Site F.depth := refineSite Z + siteOfCoords F.depth z
private def boxData (L : ℕ) (w : F.Site F.depth × Fin 4 → F.GaugeField F.top → imaginaryQuaternions) (Z : F.Cell)
    (V : F.GaugeField F.top) {k : ℕ} (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions)
    (τ : Fin k → ℝ) : BoxData L :=
  fun s => (![frameSlot w V c X (boxSite Z s.1.1.1) s.1.1.2 τ, moveSlot c X (boxSite Z s.1.1.1) s.1.1.2 τ,
    topSlot V (boxSite Z s.1.1.1) s.1.1.2] : Fin 3 → ℍ[ℝ]) s.2
private theorem boxLink_boxData {L : ℕ} (w : F.Site F.depth × Fin 4 → F.GaugeField F.top → imaginaryQuaternions)
    (Z : F.Cell) (V : F.GaugeField F.top) {k : ℕ} (c : Fin k → F.Site F.top × Fin 4)
    (X : Fin k → imaginaryQuaternions) (τ : Fin k → ℝ) {b : OffsetBond} (hb : b ∈ contourBox L) :
    boxLink (boxData L w Z V c X τ) b =
      ((chartedField (fun z i => w (z, i) (leftTranslate (ColdStepAtMirrorFrames.bondSpread c X τ) V))
        (leftTranslate (ColdStepAtMirrorFrames.bondSpread c X τ) V)
        (boxSite Z b.1) b.2 : UnitQuaternion) : ℍ[ℝ]) := by
  classical
  simp only [boxLink, hb, dif_pos]
  simp only [boxData, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
  unfold frameSlot moveSlot topSlot chartedField
  by_cases hc : IsCrossingBond (boxSite Z b.1, b.2)
  · have ht : ¬ IsAxialTreeBond (boxSite Z b.1, b.2) := fun h => h.1 hc
    simp only [hc, ht, if_true, if_false]
    rw [spreadCLM_apply]
    simp only [leftTranslate, Submonoid.coe_mul]
    rw [mul_assoc]
    rfl
  · by_cases ht : IsAxialTreeBond (boxSite Z b.1, b.2)
    · simp [hc, ht, NormedSpace.exp_zero]
    · simp only [hc, ht, if_false]
      simp only [NormedSpace.exp_zero, mul_one]
      rfl
end FrameData
section EvaluationMaps
variable {F : BlockFrame}
private theorem interpolatedField_zero (a ρA : ℝ) (m : ℕ) (V : F.GaugeField F.top) :
    interpolatedField 1 a ρA m V 0 = chartedField (fun z i => interpolatedFrame 1 a ρA m (z, i) V) V := by
  have e : interpolatedCoords 1 a ρA m V (0 : StepVariable (finiteCells F)) =
      fun z i => interpolatedFrame 1 a ρA m (z, i) V := by
    funext z i
    unfold interpolatedCoords stepCoordinates
    split_ifs
    · have : toImaginary ((0 : StepVariable (finiteCells F)) ⟨(z, i), ‹_›⟩) = 0 := by
        apply Subtype.ext
        simp [toImaginary]
        rfl
      rw [this, add_zero]
    · rw [add_zero]
  unfold interpolatedField
  rw [e]
private theorem contourAverage_eq_box {L : ℕ} (hL : F.blockSide = L) (a ρA : ℝ) (m : ℕ) (Z : F.Cell) (i : Fin 4)
    (V : F.GaugeField F.top) {k : ℕ} (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions)
    (τ : Fin k → ℝ) :
    _root_.YangMills.Construction.BlockAverages.contourAverage (interpolatedField 1 a ρA m (leftTranslate (ColdStepAtMirrorFrames.bondSpread c X τ) V) 0)
        (Z, i) =
      boxContourAverage L i (boxData L (interpolatedFrame 1 a ρA m) Z V c X τ) := by
  subst hL
  rw [interpolatedField_zero]
  unfold BlockAverages.contourAverage boxContourAverage
  congr 1
  refine Finset.sum_congr rfl fun h hh => Finset.sum_congr rfl fun π _ => ?_
  have e := pathHolonomy_eq_wordProduct (chartedField (fun z i => interpolatedFrame 1 a ρA m (z, i)
    (leftTranslate (ColdStepAtMirrorFrames.bondSpread c X τ) V))
    (leftTranslate (ColdStepAtMirrorFrames.bondSpread c X τ) V)) (refineSite Z) (bondContour F.blockSide h π i) 0
  rw [siteCoords_zero, add_zero] at e
  simp only
  rw [e]
  refine wordProduct_congr fun e he => ?_
  exact (boxLink_boxData _ Z V c X τ (bondWord_mem_contourBox hh π i he)).symm
end EvaluationMaps
section Slots
variable {F F' : BlockFrame} {k : ℕ}
private theorem iteratedFDeriv_pi_apply {P S : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [Fintype S]
    {α : P → S → ℍ[ℝ]} (hα : ContDiffAt ℝ 3 α 0) {j : ℕ} (hj : j ≤ 3) (m : Fin j → P) (s : S) :
    iteratedFDeriv ℝ j α 0 m s = iteratedFDeriv ℝ j (fun τ => α τ s) 0 m := by
  have hj' : (j : WithTop ℕ∞) ≤ 3 := by exact_mod_cast hj
  have h := (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : S => ℍ[ℝ]) s).iteratedFDeriv_comp_left hα hj'
  have h2 := congrArg (fun T => T m) h
  simpa [Function.comp_def] using h2.symm
private theorem iteratedFDeriv_single_eq_bondDeriv' {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {j : ℕ}
    (G : F.GaugeField F.top → E) (V : F.GaugeField F.top) (c : Fin k → F.Site F.top × Fin 4)
    (X : Fin k → imaginaryQuaternions) (ι : Fin j → Fin k)
    (hs : ContDiffAt ℝ j
      (fun τ : Fin k → ℝ => G (leftTranslate (ColdStepAtMirrorFrames.bondSpread c X τ) V)) 0) :
    iteratedFDeriv ℝ j (fun τ : Fin k → ℝ => G (leftTranslate (ColdStepAtMirrorFrames.bondSpread c X τ) V)) 0
        (fun l => Pi.single (ι l) 1) = bondDeriv G V (c ∘ ι) (X ∘ ι) := by
  have e : (fun τ : Fin j → ℝ => G (leftTranslate (ColdStepAtMirrorFrames.bondSpread (c ∘ ι) (X ∘ ι) τ) V)) =
      (fun τ : Fin k → ℝ => G (leftTranslate (ColdStepAtMirrorFrames.bondSpread c X τ) V)) ∘
        sublistEmbedding ι := by
    funext τ
    simp only [Function.comp, bondSpread_comp]
  have h0 : sublistEmbedding ι (0 : Fin j → ℝ) = 0 := map_zero _
  unfold bondDeriv
  rw [e, FieldMoves.iteratedFDeriv_comp_continuousLinearMap (sublistEmbedding ι) (by rw [h0]; exact hs), h0]
  simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply, sublistEmbedding_single]
private theorem frameSlot_deriv (w : F.Site F.depth × Fin 4 → F.GaugeField F.top → imaginaryQuaternions)
    (V : F.GaugeField F.top) (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions)
    {x : F.Site F.depth} {d : Fin 4} (ht : ¬ IsAxialTreeBond (x, d))
    (hs : ContDiffAt ℝ 3
      (fun τ : Fin k → ℝ => w (x, d) (leftTranslate (ColdStepAtMirrorFrames.bondSpread c X τ) V)) 0)
    {j : ℕ} (hj : j ≤ 3) (ι : Fin j → Fin k) :
    iteratedFDeriv ℝ j (frameSlot w V c X x d) 0 (fun l => Pi.single (ι l) 1) =
      ((bondDeriv (w (x, d)) V (c ∘ ι) (X ∘ ι) : imaginaryQuaternions) : ℍ[ℝ]) := by
  have hj' : (j : WithTop ℕ∞) ≤ 3 := by exact_mod_cast hj
  have e : frameSlot w V c X x d = imaginaryQuaternions.subtypeL ∘
      fun τ : Fin k → ℝ => w (x, d) (leftTranslate (ColdStepAtMirrorFrames.bondSpread c X τ) V) := by
    funext τ
    simp [frameSlot, ht]
  rw [e, imaginaryQuaternions.subtypeL.iteratedFDeriv_comp_left hs hj']
  rw [ContinuousLinearMap.compContinuousMultilinearMap_coe]
  simp only [Function.comp]
  rw [iteratedFDeriv_single_eq_bondDeriv' (w (x, d)) V c X ι (hs.of_le hj')]
  rfl
private theorem iteratedFDeriv_const_apply' {P E : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup E] [NormedSpace ℝ E] (e : E) {j : ℕ} (hj : 1 ≤ j) (m : Fin j → P) :
    iteratedFDeriv ℝ j (fun _ : P => e) 0 m = 0 := by
  rw [iteratedFDeriv_const_of_ne (by omega)]
  rfl
private theorem clm_iteratedFDeriv_one {P E : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup E] [NormedSpace ℝ E] (Λ : P →L[ℝ] E) (m : Fin 1 → P) :
    iteratedFDeriv ℝ 1 Λ 0 m = Λ (m 0) := by
  rw [iteratedFDeriv_one_apply, Λ.fderiv]
private theorem clm_iteratedFDeriv_two {P E : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup E] [NormedSpace ℝ E] (Λ : P →L[ℝ] E) (m : Fin 2 → P) :
    iteratedFDeriv ℝ 2 Λ 0 m = 0 := by
  rw [iteratedFDeriv_two_apply]
  have e : fderiv ℝ (⇑Λ) = fun _ => Λ := by
    funext y
    exact Λ.fderiv
  rw [e]
  simp
private theorem moveSlot_deriv_le {c : Fin k → F.Site F.top × Fin 4} {X : Fin k → imaginaryQuaternions} {B : ℝ}
    (hB0 : 0 ≤ B) (hB : ∀ y i, ‖spreadCLM c X y i‖ ≤ B) (x : F.Site F.depth) (d : Fin 4) {j : ℕ} (h1 : 1 ≤ j)
    (h2 : j ≤ 2) (ι : Fin j → Fin k) :
    ‖iteratedFDeriv ℝ j (moveSlot c X x d) 0 (fun l => (Pi.single (ι l) 1 : Fin k → ℝ))‖ ≤ B := by
  classical
  by_cases hc : IsCrossingBond (x, d)
  · have e : moveSlot c X x d = ⇑(spreadCLM c X (enclosingCell x) d) := by
      funext τ
      simp [moveSlot, hc]
    rw [e]
    interval_cases j
    · rw [clm_iteratedFDeriv_one]
      refine (ContinuousLinearMap.le_opNorm _ _).trans ?_
      rw [Pi.norm_single, norm_one, mul_one]
      exact hB _ _
    · rw [clm_iteratedFDeriv_two, norm_zero]
      exact hB0
  · have e : moveSlot c X x d = fun _ => 0 := by
      funext τ
      simp [moveSlot, hc]
    rw [e, iteratedFDeriv_const_apply' _ h1, norm_zero]
    exact hB0
private structure BoxMatch (L : ℕ) (w : F.Site F.depth × Fin 4 → F.GaugeField F.top → imaginaryQuaternions)
    (w' : F'.Site F'.depth × Fin 4 → F'.GaugeField F'.top → imaginaryQuaternions) (Z : F.Cell) (Z' : F'.Cell)
    (V : F.GaugeField F.top) (V' : F'.GaugeField F'.top) (c : Fin k → F.Site F.top × Fin 4)
    (c' : Fin k → F'.Site F'.top × Fin 4) (X : Fin k → imaginaryQuaternions) (ε B : ℝ) : Prop where
  ε_nonneg : 0 ≤ ε
  B_nonneg : 0 ≤ B
  tree : ∀ b ∈ contourBox L, (IsAxialTreeBond (boxSite Z b.1, b.2) ↔ IsAxialTreeBond (boxSite Z' b.1, b.2))
  cross : ∀ b ∈ contourBox L, (IsCrossingBond (boxSite Z b.1, b.2) ↔ IsCrossingBond (boxSite Z' b.1, b.2))
  top : ∀ b ∈ contourBox L, IsCrossingBond (boxSite Z b.1, b.2) →
    V (enclosingCell (boxSite Z b.1)) b.2 = V' (enclosingCell (boxSite Z' b.1)) b.2
  spread : ∀ b ∈ contourBox L, IsCrossingBond (boxSite Z b.1, b.2) →
    ∀ τ, spreadCLM c X (enclosingCell (boxSite Z b.1)) b.2 τ = spreadCLM c' X (enclosingCell (boxSite Z' b.1)) b.2 τ
  smooth : ∀ b ∈ contourBox L, ¬ IsAxialTreeBond (boxSite Z b.1, b.2) →
    ContDiffAt ℝ 3 (fun τ : Fin k → ℝ =>
      w (boxSite Z b.1, b.2) (leftTranslate (ColdStepAtMirrorFrames.bondSpread c X τ) V)) 0
  smooth' : ∀ b ∈ contourBox L, ¬ IsAxialTreeBond (boxSite Z' b.1, b.2) →
    ContDiffAt ℝ 3 (fun τ : Fin k → ℝ =>
      w' (boxSite Z' b.1, b.2) (leftTranslate (ColdStepAtMirrorFrames.bondSpread c' X τ) V')) 0
  value : ∀ b ∈ contourBox L, ¬ IsAxialTreeBond (boxSite Z b.1, b.2) →
    ‖((w (boxSite Z b.1, b.2) V : imaginaryQuaternions) : ℍ[ℝ]) -
      ((w' (boxSite Z' b.1, b.2) V' : imaginaryQuaternions) : ℍ[ℝ])‖ ≤ ε
  deriv : ∀ b ∈ contourBox L, ¬ IsAxialTreeBond (boxSite Z b.1, b.2) →
    ∀ (j : ℕ) (ι : Fin j → Fin k), 1 ≤ j → j ≤ 2 →
    ‖((bondDeriv (w (boxSite Z b.1, b.2)) V (c ∘ ι) (X ∘ ι) : imaginaryQuaternions) : ℍ[ℝ]) -
      ((bondDeriv (w' (boxSite Z' b.1, b.2)) V' (c' ∘ ι) (X ∘ ι) : imaginaryQuaternions) : ℍ[ℝ])‖ ≤ ε
  size : ∀ b ∈ contourBox L, ¬ IsAxialTreeBond (boxSite Z b.1, b.2) →
    ∀ (j : ℕ) (ι : Fin j → Fin k), 1 ≤ j → j ≤ 2 →
    ‖((bondDeriv (w (boxSite Z b.1, b.2)) V (c ∘ ι) (X ∘ ι) : imaginaryQuaternions) : ℍ[ℝ])‖ ≤ B
  size' : ∀ b ∈ contourBox L, ¬ IsAxialTreeBond (boxSite Z' b.1, b.2) →
    ∀ (j : ℕ) (ι : Fin j → Fin k), 1 ≤ j → j ≤ 2 →
    ‖((bondDeriv (w' (boxSite Z' b.1, b.2)) V' (c' ∘ ι) (X ∘ ι) : imaginaryQuaternions) : ℍ[ℝ])‖ ≤ B
  bound : ∀ y i, ‖spreadCLM c X y i‖ ≤ B
  bound' : ∀ y i, ‖spreadCLM c' X y i‖ ≤ B
private theorem contDiffAt_boxData (L : ℕ) (w : F.Site F.depth × Fin 4 → F.GaugeField F.top → imaginaryQuaternions)
    (Z : F.Cell) (V : F.GaugeField F.top) (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions)
    (hs : ∀ b ∈ contourBox L, ¬ IsAxialTreeBond (boxSite Z b.1, b.2) →
      ContDiffAt ℝ 3 (fun τ : Fin k → ℝ =>
        w (boxSite Z b.1, b.2) (leftTranslate (ColdStepAtMirrorFrames.bondSpread c X τ) V)) 0) :
    ContDiffAt ℝ 3 (boxData L w Z V c X) 0 := by
  classical
  refine contDiffAt_pi.mpr fun s => ?_
  obtain ⟨⟨b, hb⟩, sl⟩ := s
  fin_cases sl
  · show ContDiffAt ℝ 3 (frameSlot w V c X (boxSite Z b.1) b.2) 0
    by_cases ht : IsAxialTreeBond (boxSite Z b.1, b.2)
    · have e : frameSlot w V c X (boxSite Z b.1) b.2 = fun _ => 0 := by
        funext τ
        simp [frameSlot, ht]
      rw [e]
      exact contDiffAt_const
    · have e : frameSlot w V c X (boxSite Z b.1) b.2 = imaginaryQuaternions.subtypeL ∘
          fun τ : Fin k → ℝ => w (boxSite Z b.1, b.2) (leftTranslate (ColdStepAtMirrorFrames.bondSpread c X τ) V) := by
        funext τ
        simp [frameSlot, ht]
      rw [e]
      exact imaginaryQuaternions.subtypeL.contDiff.contDiffAt.comp _ (hs b hb ht)
  · show ContDiffAt ℝ 3 (moveSlot c X (boxSite Z b.1) b.2) 0
    by_cases hc : IsCrossingBond (boxSite Z b.1, b.2)
    · have e : moveSlot c X (boxSite Z b.1) b.2 = ⇑(spreadCLM c X (enclosingCell (boxSite Z b.1)) b.2) := by
        funext τ
        simp [moveSlot, hc]
      rw [e]
      exact ContinuousLinearMap.contDiff _ |>.contDiffAt
    · have e : moveSlot c X (boxSite Z b.1) b.2 = fun _ => 0 := by
        funext τ
        simp [moveSlot, hc]
      rw [e]
      exact contDiffAt_const
  · exact contDiffAt_const
private theorem singles_one {x : Fin k} : (![(Pi.single x 1 : Fin k → ℝ)] : Fin 1 → Fin k → ℝ) =
    fun l => Pi.single ((![x] : Fin 1 → Fin k) l) 1 := by apply _root_.YangMills.Construction.Interpolation.PartMeanDeriv.basisVectors_one <;> assumption
private theorem singles_two {x y : Fin k} :
    (![(Pi.single x 1 : Fin k → ℝ), Pi.single y 1] : Fin 2 → Fin k → ℝ) =
    fun l => Pi.single ((![x, y] : Fin 2 → Fin k) l) 1 := by apply _root_.YangMills.Construction.Interpolation.PartMeanDeriv.basisVectors_two <;> assumption
private theorem BoxMatch.secondOrderClose {L : ℕ}
    {w : F.Site F.depth × Fin 4 → F.GaugeField F.top → imaginaryQuaternions}
    {w' : F'.Site F'.depth × Fin 4 → F'.GaugeField F'.top → imaginaryQuaternions} {Z : F.Cell} {Z' : F'.Cell}
    {V : F.GaugeField F.top} {V' : F'.GaugeField F'.top} {c : Fin k → F.Site F.top × Fin 4}
    {c' : Fin k → F'.Site F'.top × Fin 4} {X : Fin k → imaginaryQuaternions} {ε B : ℝ}
    (h : BoxMatch L w w' Z Z' V V' c c' X ε B) (ι : Fin 2 → Fin k) :
    SecondOrderClose (boxData L w Z V c X) (boxData L w' Z' V' c' X) (Pi.single (ι 0) 1) (Pi.single (ι 1) 1)
      ε B := by
  classical
  have sm := contDiffAt_boxData L w Z V c X h.smooth
  have sm' := contDiffAt_boxData L w' Z' V' c' X h.smooth'
  have key : ∀ (j : ℕ) (ι' : Fin j → Fin k), 1 ≤ j → j ≤ 2 →
      ‖iteratedFDeriv ℝ j (boxData L w Z V c X) 0 (fun l => Pi.single (ι' l) 1) -
        iteratedFDeriv ℝ j (boxData L w' Z' V' c' X) 0 (fun l => Pi.single (ι' l) 1)‖ ≤ ε ∧
      ‖iteratedFDeriv ℝ j (boxData L w Z V c X) 0 (fun l => Pi.single (ι' l) 1)‖ ≤ B ∧
      ‖iteratedFDeriv ℝ j (boxData L w' Z' V' c' X) 0 (fun l => Pi.single (ι' l) 1)‖ ≤ B := by
    intro j ι' h1 h2
    have h3 : j ≤ 3 := by omega
    have slots : ∀ s : BoxSlot L,
        ‖iteratedFDeriv ℝ j (boxData L w Z V c X) 0 (fun l => Pi.single (ι' l) 1) s -
          iteratedFDeriv ℝ j (boxData L w' Z' V' c' X) 0 (fun l => Pi.single (ι' l) 1) s‖ ≤ ε ∧
        ‖iteratedFDeriv ℝ j (boxData L w Z V c X) 0 (fun l => Pi.single (ι' l) 1) s‖ ≤ B ∧
        ‖iteratedFDeriv ℝ j (boxData L w' Z' V' c' X) 0 (fun l => Pi.single (ι' l) 1) s‖ ≤ B := by
      intro s
      rw [iteratedFDeriv_pi_apply sm h3, iteratedFDeriv_pi_apply sm' h3]
      obtain ⟨⟨b, hb⟩, sl⟩ := s
      fin_cases sl
      · show ‖iteratedFDeriv ℝ j (frameSlot w V c X (boxSite Z b.1) b.2) 0 _ -
            iteratedFDeriv ℝ j (frameSlot w' V' c' X (boxSite Z' b.1) b.2) 0 _‖ ≤ ε ∧
          ‖iteratedFDeriv ℝ j (frameSlot w V c X (boxSite Z b.1) b.2) 0 _‖ ≤ B ∧
          ‖iteratedFDeriv ℝ j (frameSlot w' V' c' X (boxSite Z' b.1) b.2) 0 _‖ ≤ B
        by_cases ht : IsAxialTreeBond (boxSite Z b.1, b.2)
        · have ht' := (h.tree b hb).mp ht
          have e : frameSlot w V c X (boxSite Z b.1) b.2 = fun _ => 0 := by
            funext τ
            simp [frameSlot, ht]
          have e' : frameSlot w' V' c' X (boxSite Z' b.1) b.2 = fun _ => 0 := by
            funext τ
            simp [frameSlot, ht']
          rw [e, e', iteratedFDeriv_const_apply' _ h1]
          simp [h.ε_nonneg, h.B_nonneg]
        · have ht' : ¬ IsAxialTreeBond (boxSite Z' b.1, b.2) := fun q => ht ((h.tree b hb).mpr q)
          rw [frameSlot_deriv w V c X ht (h.smooth b hb ht) h3,
            frameSlot_deriv w' V' c' X ht' (h.smooth' b hb ht') h3]
          exact ⟨h.deriv b hb ht j ι' h1 h2, h.size b hb ht j ι' h1 h2, h.size' b hb ht' j ι' h1 h2⟩
      · show ‖iteratedFDeriv ℝ j (moveSlot c X (boxSite Z b.1) b.2) 0 _ -
            iteratedFDeriv ℝ j (moveSlot c' X (boxSite Z' b.1) b.2) 0 _‖ ≤ ε ∧
          ‖iteratedFDeriv ℝ j (moveSlot c X (boxSite Z b.1) b.2) 0 _‖ ≤ B ∧
          ‖iteratedFDeriv ℝ j (moveSlot c' X (boxSite Z' b.1) b.2) 0 _‖ ≤ B
        have e : moveSlot c X (boxSite Z b.1) b.2 = moveSlot c' X (boxSite Z' b.1) b.2 := by
          funext τ
          by_cases hc : IsCrossingBond (boxSite Z b.1, b.2)
          · have hc' := (h.cross b hb).mp hc
            simp only [moveSlot, hc, hc', if_true]
            exact h.spread b hb hc τ
          · have hc' : ¬ IsCrossingBond (boxSite Z' b.1, b.2) := fun q => hc ((h.cross b hb).mpr q)
            simp [moveSlot, hc, hc']
        refine ⟨?_, moveSlot_deriv_le h.B_nonneg h.bound _ _ h1 h2 ι',
          moveSlot_deriv_le h.B_nonneg h.bound' _ _ h1 h2 ι'⟩
        rw [e, sub_self, norm_zero]
        exact h.ε_nonneg
      · show ‖iteratedFDeriv ℝ j (fun _ : Fin k → ℝ => topSlot V (boxSite Z b.1) b.2) 0 _ -
            iteratedFDeriv ℝ j (fun _ : Fin k → ℝ => topSlot V' (boxSite Z' b.1) b.2) 0 _‖ ≤ ε ∧
          ‖iteratedFDeriv ℝ j (fun _ : Fin k → ℝ => topSlot V (boxSite Z b.1) b.2) 0 _‖ ≤ B ∧
          ‖iteratedFDeriv ℝ j (fun _ : Fin k → ℝ => topSlot V' (boxSite Z' b.1) b.2) 0 _‖ ≤ B
        rw [iteratedFDeriv_const_apply' _ h1, iteratedFDeriv_const_apply' _ h1]
        simp [h.ε_nonneg, h.B_nonneg]
    refine ⟨?_, ?_, ?_⟩
    · exact (pi_norm_le_iff_of_nonneg h.ε_nonneg).mpr fun s => (slots s).1
    · exact (pi_norm_le_iff_of_nonneg h.B_nonneg).mpr fun s => (slots s).2.1
    · exact (pi_norm_le_iff_of_nonneg h.B_nonneg).mpr fun s => (slots s).2.2
  have v0 : ‖boxData L w Z V c X 0 - boxData L w' Z' V' c' X 0‖ ≤ ε := by
    refine (pi_norm_le_iff_of_nonneg h.ε_nonneg).mpr fun s => ?_
    obtain ⟨⟨b, hb⟩, sl⟩ := s
    fin_cases sl
    · show ‖frameSlot w V c X (boxSite Z b.1) b.2 0 - frameSlot w' V' c' X (boxSite Z' b.1) b.2 0‖ ≤ ε
      by_cases ht : IsAxialTreeBond (boxSite Z b.1, b.2)
      · have ht' := (h.tree b hb).mp ht
        simp [frameSlot, ht, ht', h.ε_nonneg]
      · have ht' : ¬ IsAxialTreeBond (boxSite Z' b.1, b.2) := fun q => ht ((h.tree b hb).mpr q)
        simp only [frameSlot, ht, ht', if_false, leftTranslate_bondSpread_zero]
        exact h.value b hb ht
    · show ‖moveSlot c X (boxSite Z b.1) b.2 0 - moveSlot c' X (boxSite Z' b.1) b.2 0‖ ≤ ε
      have e : ∀ {G : BlockFrame} (c₁ : Fin k → G.Site G.top × Fin 4) (x : G.Site G.depth) (d : Fin 4),
          moveSlot c₁ X x d 0 = 0 := by
        intro G c₁ x d
        simp [moveSlot]
      rw [e, e, sub_zero, norm_zero]
      exact h.ε_nonneg
    · show ‖topSlot V (boxSite Z b.1) b.2 - topSlot V' (boxSite Z' b.1) b.2‖ ≤ ε
      by_cases hc : IsCrossingBond (boxSite Z b.1, b.2)
      · have hc' := (h.cross b hb).mp hc
        simp only [topSlot, hc, hc', if_true]
        rw [h.top b hb hc, sub_self, norm_zero]
        exact h.ε_nonneg
      · have hc' : ¬ IsCrossingBond (boxSite Z' b.1, b.2) := fun q => hc ((h.cross b hb).mpr q)
        simp [topSlot, hc, hc', h.ε_nonneg]
  have k1 := fun x => key 1 ![x] le_rfl (by norm_num)
  have k2 := key 2 ![ι 0, ι 1] (by norm_num) le_rfl
  simp only [← singles_one, ← singles_two] at k1 k2
  exact ⟨sm, sm', v0, (k1 _).1, (k1 _).1, k2.1, (k1 _).2.1, (k1 _).2.1, k2.2.1, (k1 _).2.2, (k1 _).2.2, k2.2.2⟩
end Slots
section Offsets
open BlockOffsets (halfSide enclosingCell_offset cellOffset_offset isCrossingBond_iff)
private def blockOf (L : ℕ) (z : Offset) : Offset := fun i => (z i + halfSide L) / L
private def offsetIn (L : ℕ) (z : Offset) : Offset := fun i => z i - L * blockOf L z i
private theorem offsetIn_mem {L : ℕ} (hL : Odd L) (z : Offset) : offsetIn L z ∈ centredCube L := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.TwoTopLabels.cellRemainder_mem_centredCube <;> assumption
private theorem blockOf_abs_le {L : ℕ} (hL : Odd L) (z : Offset) (hz : ∀ i, |z i| ≤ 11 * L) (i : Fin 4) :
    |blockOf L z i| ≤ 12 := by
  obtain ⟨k, hk⟩ := hL
  have hLz : (L : ℤ) = 2 * k + 1 := by exact_mod_cast hk
  have hh : halfSide L = k := by
    unfold halfSide
    rw [hLz]
    omega
  have hpos : (0 : ℤ) < L := by omega
  have e := Int.emod_add_mul_ediv (z i + halfSide L) L
  have h0 := Int.emod_nonneg (z i + halfSide L) (ne_of_gt hpos)
  have h1 := Int.emod_lt_of_pos (z i + halfSide L) hpos
  have h2 := abs_le.mp (hz i)
  simp only [blockOf]
  set u := (z i + halfSide L) / (L : ℤ)
  rw [abs_le]
  constructor
  · by_contra hc
    have : u + 1 ≤ -12 := by omega
    nlinarith
  · by_contra hc
    have : 13 ≤ u := by omega
    nlinarith
section Geometry
variable {F : BlockFrame}
private theorem cellCentre_eq_refineSite (y : F.Cell) : cellCentre F.depth y = refineSite y := by apply _root_.YangMills.Construction.BondMeans.cellCentre_eq_refineSite <;> assumption
private theorem refineSite_add_eq (Y : F.Cell) (z : Offset) :
    (refineSite Y + siteOfCoords F.depth z : F.Site F.depth) =
      cellCentre F.depth (Y + siteOfCoords F.top (blockOf F.blockSide z)) +
        siteOfCoords F.depth (offsetIn F.blockSide z) := by
  rw [cellCentre_eq_refineSite, blockRefine_add_siteOfCoords (j := F.depth) le_rfl, add_assoc, ← siteCoords_add]
  congr 2
  funext i
  simp only [Pi.add_apply, offsetIn]
  ring
private def shiftedOffset (L : ℕ) (zb z : Offset) : Offset := fun i => (L : ℤ) * zb i + z i
private theorem boxSite_shift (Y : F.Cell) (zb z : Offset) :
    boxSite (Y + siteOfCoords F.top zb) z = refineSite Y + siteOfCoords F.depth (shiftedOffset F.blockSide zb z) := by
  unfold boxSite
  rw [blockRefine_add_siteOfCoords (j := F.depth) le_rfl, add_assoc, ← siteCoords_add]
  rfl
private theorem add_unitStep_eq (s : F.Site F.depth) (z : Offset) (d : Fin 4) :
    (s + siteOfCoords F.depth z + unitStep F.depth d : F.Site F.depth) =
      s + siteOfCoords F.depth (z + Pi.single d 1) := by
  have e : (unitStep F.depth d : F.Site F.depth) = siteOfCoords F.depth (Pi.single d 1) := rfl
  rw [e, siteCoords_add, add_assoc]
private theorem cellSupDist_add_le (Y : F.Cell) (h : Offset) (hs : ∀ i, 0 < F.extent i) {M : ℕ}
    (hM : ∀ i, |h i| ≤ M) : cellSupDist Y (Y + siteOfCoords F.top h) ≤ M := by
  unfold cellSupDist
  refine Finset.sup_le fun i _ => ?_
  have hne : NeZero (F.period F.top i) := ⟨by
    rw [BlockOffsets.period_top]
    exact (hs i).ne'⟩
  have e : (Y i - (Y + siteOfCoords F.top h : F.Cell) i) = ((-h i : ℤ) : ZMod (F.period F.top i)) := by
    simp [siteOfCoords]
  rw [e]
  have h1 := ZMod.natAbs_min_of_le_div_two (F.period F.top i) (((-h i : ℤ) : ZMod (F.period F.top i)).valMinAbs)
    (-h i) (ZMod.coe_valMinAbs _) (ZMod.natAbs_valMinAbs_le _)
  refine h1.trans ?_
  have := abs_le.mp (hM i)
  omega
private theorem mem_chordBonds (hcov : BlocksCoverLowerLevel) (hodd : Odd F.blockSide) (hs : ∀ i, 0 < F.extent i)
    {b : F.Site F.depth × Fin 4} (ht : ¬ IsAxialTreeBond b) : b ∈ chordBonds (finiteCells F) := by apply _root_.YangMills.Construction.TorusComparison.BondsNearCells.mem_chordBonds <;> assumption
private theorem isCrossingBond_refine_iff (hodd : Odd F.blockSide) (hs : ∀ i, 2 ≤ F.extent i) (Y : F.Cell)
    (z : Offset) (d : Fin 4) :
    IsCrossingBond ((refineSite Y + siteOfCoords F.depth z : F.Site F.depth), d) ↔
      offsetIn F.blockSide z d = halfSide F.blockSide := by
  rw [refineSite_add_eq]
  exact isCrossingBond_iff hodd hs _ _ (offsetIn_mem hodd z) d
private theorem enclosingCell_refine (hodd : Odd F.blockSide) (hs : ∀ i, 2 ≤ F.extent i) (Y : F.Cell)
    (z : Offset) :
    enclosingCell (refineSite Y + siteOfCoords F.depth z : F.Site F.depth) =
      Y + siteOfCoords F.top (blockOf F.blockSide z) := by
  rw [refineSite_add_eq]
  exact enclosingCell_offset hodd hs _ _ (offsetIn_mem hodd z)
private theorem isAxialTreeBond_refine_iff (hodd : Odd F.blockSide) (hs : ∀ i, 2 ≤ F.extent i) (Y : F.Cell)
    (z : Offset) (d : Fin 4) :
    IsAxialTreeBond ((refineSite Y + siteOfCoords F.depth z : F.Site F.depth), d) ↔
      offsetIn F.blockSide z d ≠ halfSide F.blockSide ∧ ∀ l, d < l → offsetIn F.blockSide z l = 0 := by
  unfold IsAxialTreeBond
  simp only
  rw [isCrossingBond_refine_iff hodd hs, refineSite_add_eq,
    cellOffset_offset hodd hs _ _ (offsetIn_mem hodd z)]
end Geometry
section Matching
variable {F F' : BlockFrame}
private def backOffset (i : Fin 4) (back : Bool) : Offset := if back then -Pi.single i 1 else 0
private theorem cellBond_fst (Y : F.Cell) (i : Fin 4) (back : Bool) :
    (cellBond Y i back).1 = Y + siteOfCoords F.top (backOffset i back) := by
  cases back
  · simp [cellBond, backOffset, siteCoords_zero]
  · have e : (unitStep F.top i : F.Cell) = siteOfCoords F.top (Pi.single i 1) := rfl
    simp only [cellBond, backOffset, if_true, sub_eq_add_neg, e, siteCoords_neg]
private theorem backOffset_abs_le (i : Fin 4) (back : Bool) (l : Fin 4) : |backOffset i back l| ≤ 1 := by
  unfold backOffset
  by_cases hl : l = i
  · subst hl
    cases back <;> simp
  · cases back <;> simp [Pi.single_eq_of_ne hl]
private theorem shiftedOffset_abs_le {L : ℕ} (i : Fin 4) (back : Bool) {b : OffsetBond} (hb : b ∈ contourBox L)
    (l : Fin 4) : |shiftedOffset L (backOffset i back) b.1 l| ≤ 10 * L := by
  have h1 := abs_le.mp (backOffset_abs_le i back l)
  have h2 : -(9 * L : ℤ) ≤ b.1 l ∧ b.1 l ≤ 9 * L := by
    have := (Finset.mem_product.mp hb).1
    exact Finset.mem_Icc.mp (Fintype.mem_piFinset.mp this l)
  unfold shiftedOffset
  rw [abs_le]
  constructor <;> nlinarith [h1.1, h1.2, h2.1, h2.2]
private theorem add_single_abs_le {L : ℕ} (hL : Odd L) {z : Offset} (hz : ∀ l, |z l| ≤ 10 * L) (d : Fin 4)
    (l : Fin 4) : |(z + Pi.single d 1 : Offset) l| ≤ 11 * L := by
  have h0 : (1 : ℤ) ≤ L := by exact_mod_cast hL.pos
  have h1 : |(Pi.single d 1 : Offset) l| ≤ 1 := by
    by_cases hl : l = d
    · subst hl; simp
    · simp [Pi.single_eq_of_ne hl]
  refine (abs_add_le _ _).trans ?_
  linarith [hz l]
private theorem abs_le_eleven {L : ℕ} {z : Offset} (hz : ∀ l, |z l| ≤ 10 * L) (l : Fin 4) : |z l| ≤ 11 * L := by
  linarith [hz l]
private theorem siteOfCoords_injOn {Y : F.Cell} {u v : Offset} (h : ∀ i, |u i - v i| < F.extent i)
    (e : (Y + siteOfCoords F.top u : F.Cell) = Y + siteOfCoords F.top v) : u = v := by
  have e1 : (siteOfCoords F.top u : F.Cell) = siteOfCoords F.top v := add_left_cancel e
  funext i
  have e2 := congrFun e1 i
  simp only [siteOfCoords] at e2
  rw [ZMod.intCast_eq_intCast_iff_dvd_sub, BlockOffsets.period_top] at e2
  have h1 := h i
  have h2 : (v i - u i) = 0 := Int.eq_zero_of_abs_lt_dvd e2 (by rw [abs_sub_comm]; exact h1)
  omega
private theorem bond_eq_iff {G : BlockFrame} (y : G.Cell) {e : Offset × Fin 4} {h : Offset} {d : Fin 4}
    (hsmall : ∀ i, |e.1 i - h i| < G.extent i) :
    (((y + siteOfCoords G.top e.1 : G.Cell), e.2) = ((y + siteOfCoords G.top h : G.Cell), d)) ↔
      (e.1 = h ∧ e.2 = d) := by
  constructor
  · intro hh
    have h1 := congrArg Prod.fst hh
    have h2 := congrArg Prod.snd hh
    exact ⟨siteOfCoords_injOn hsmall h1, h2⟩
  · rintro ⟨rfl, rfl⟩
    rfl
private theorem boxMatch (hcov : BlocksCoverLowerLevel) {L : ℕ} (hodd : Odd L) (hF : F.blockSide = L)
    (hF' : F'.blockSide = L) {a ρA δ₂ K C σ : ℝ} {m : ℕ} (hδ : 0 ≤ δ₂) (hC : 0 ≤ C) (hσ0 : 0 ≤ σ) (hσ : σ ≤ 1)
    {Y : F.Cell} {Y' : F'.Cell} {V : F.GaugeField F.top} {V' : F'.GaugeField F'.top} {q : ℕ} (hq : 16 ≤ q)
    (hs : ∀ i, 2 * q + 2 < F.extent i) (hs' : ∀ i, 2 * q + 2 < F'.extent i)
    (sV : InterpolatedFrameSmall 1 a ρA δ₂ C σ m V) (sV' : InterpolatedFrameSmall 1 a ρA δ₂ C σ m V')
    (loc : InterpolatedFrameLocal 1 a ρA δ₂ K C σ m V V' Y Y' q)
    (agree : AgreeOnBall (finiteCells F) V (finiteCells F') V' Y Y' q) (i : Fin 4) (back : Bool) {k : ℕ}
    (hk : k ≤ 3) (bb : Fin k → Offset × Fin 4) (hbb : ∀ l, BondWithinRadius q (bb l))
    (X : Fin k → imaginaryQuaternions) (hX : AreUnitVectors X) :
    BoxMatch L (interpolatedFrame 1 a ρA m) (interpolatedFrame 1 a ρA m) (Y + siteOfCoords F.top (backOffset i back))
      (Y' + siteOfCoords F'.top (backOffset i back)) V V' (bondsAt Y bb) (bondsAt Y' bb) X
      (C * Real.exp (-(δ₂ / 4 * ((q : ℝ) - 13)))) (C + 3) := by
  classical
  subst hF
  have odd' : Odd F'.blockSide := hF' ▸ hodd
  have s2 : ∀ i, 2 ≤ F.extent i := fun i => by have := hs i; omega
  have s2' : ∀ i, 2 ≤ F'.extent i := fun i => by have := hs' i; omega
  have p0 : ∀ i, 0 < F.extent i := fun i => by have := hs i; omega
  have p0' : ∀ i, 0 < F'.extent i := fun i => by have := hs' i; omega
  set zb := backOffset i back with hzb
  set Z : F.Cell := Y + siteOfCoords F.top zb with hZ
  set Z' : F'.Cell := Y' + siteOfCoords F'.top zb with hZ'
  let sh : OffsetBond → Offset := fun b => shiftedOffset F.blockSide zb b.1
  have eS : ∀ b : OffsetBond, boxSite Z b.1 = refineSite Y + siteOfCoords F.depth (sh b) := fun b =>
    boxSite_shift Y zb b.1
  have eS' : ∀ b : OffsetBond, boxSite Z' b.1 = refineSite Y' + siteOfCoords F'.depth (sh b) := fun b => by
    have := boxSite_shift Y' zb b.1
    rw [hF'] at this
    exact this
  have lowF : ∀ b : OffsetBond, (boxSite Z b.1, b.2) =
      fineBondAt Y (blockOf F.blockSide (sh b)) (offsetIn F.blockSide (sh b)) b.2 := fun b => by
    rw [eS, refineSite_add_eq]
    rfl
  have lowF' : ∀ b : OffsetBond, (boxSite Z' b.1, b.2) =
      fineBondAt Y' (blockOf F.blockSide (sh b)) (offsetIn F.blockSide (sh b)) b.2 := fun b => by
    rw [eS', refineSite_add_eq, hF']
    rfl
  have sh10 : ∀ b ∈ contourBox F.blockSide, ∀ l, |sh b l| ≤ 10 * F.blockSide := fun b hb l =>
    shiftedOffset_abs_le i back hb l
  have h12 : ∀ b ∈ contourBox F.blockSide, ∀ l, |blockOf F.blockSide (sh b) l| ≤ 12 := fun b hb l =>
    blockOf_abs_le hodd _ (abs_le_eleven (sh10 b hb)) l
  have h12n : ∀ b ∈ contourBox F.blockSide, ∀ l, |blockOf F.blockSide (sh b + Pi.single b.2 1) l| ≤ 12 :=
    fun b hb l => blockOf_abs_le hodd _ (add_single_abs_le hodd (sh10 b hb) b.2) l
  have q12 : (12 : ℤ) ≤ q := by exact_mod_cast (by omega : 12 ≤ q)
  have box12 : ∀ {h : Offset}, (∀ l, |h l| ≤ 12) → ∀ l, |h l| ≤ (q : ℤ) := fun hh l => (hh l).trans q12
  have dist0 : ∀ b ∈ contourBox F.blockSide, cellSupDist Y
      (enclosingCell (fineBondAt Y (blockOf F.blockSide (sh b)) (offsetIn F.blockSide (sh b)) b.2).1) ≤ 12 := by
    intro b hb
    rw [← lowF b]
    simp only
    rw [eS, enclosingCell_refine hodd s2]
    exact cellSupDist_add_le Y _ p0 (M := 12) (by exact_mod_cast h12 b hb)
  have low : ∀ b ∈ contourBox F.blockSide, ¬ IsAxialTreeBond (boxSite Z b.1, b.2) →
      IsFineBondWithinRadius Y q (blockOf F.blockSide (sh b)) (offsetIn F.blockSide (sh b)) b.2 := by
    intro b hb ht
    refine ⟨offsetIn_mem hodd _, ?_, box12 (h12 b hb), ?_, ?_⟩
    · rw [← lowF b]
      exact mem_chordBonds hcov hodd p0 ht
    · exact (dist0 b hb).trans (by omega)
    · rw [← lowF b]
      simp only
      rw [eS, add_unitStep_eq, enclosingCell_refine hodd s2]
      exact (cellSupDist_add_le Y _ p0 (M := 12) (by exact_mod_cast h12n b hb)).trans (by omega)
  have expo : ∀ b ∈ contourBox F.blockSide, Real.exp (-(δ₂ / 4 * ((q : ℝ) - cellSupDist Y
      (enclosingCell (fineBondAt Y (blockOf F.blockSide (sh b)) (offsetIn F.blockSide (sh b)) b.2).1)))) ≤
      Real.exp (-(δ₂ / 4 * ((q : ℝ) - 13))) := by
    intro b hb
    refine Real.exp_le_exp.mpr ?_
    have h1 : (cellSupDist Y (enclosingCell
        (fineBondAt Y (blockOf F.blockSide (sh b)) (offsetIn F.blockSide (sh b)) b.2).1) : ℝ) ≤ 13 := by
      have := dist0 b hb
      have h2 : cellSupDist Y (enclosingCell
          (fineBondAt Y (blockOf F.blockSide (sh b)) (offsetIn F.blockSide (sh b)) b.2).1) ≤ 13 := by omega
      exact_mod_cast h2
    have : 0 ≤ δ₂ / 4 := by positivity
    nlinarith
  refine ⟨by positivity, by linarith, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro b hb
    rw [eS, eS', isAxialTreeBond_refine_iff hodd s2, isAxialTreeBond_refine_iff odd' s2', hF']
  · intro b hb
    rw [eS, eS', isCrossingBond_refine_iff hodd s2, isCrossingBond_refine_iff odd' s2', hF']
  · intro b hb hc
    rw [eS, eS', enclosingCell_refine hodd s2, enclosingCell_refine odd' s2', hF']
    have h1 := box12 (h12 b hb)
    refine agree.2.2.2 (blockOf F.blockSide (sh b), b.2) ⟨h1, fun l => ?_⟩
    have h2 := abs_le.mp (h12 b hb l)
    have h3 : |(Pi.single b.2 1 : Offset) l| ≤ 1 := by
      by_cases hl : l = b.2
      · subst hl; simp
      · simp [Pi.single_eq_of_ne hl]
    have h4 := abs_le.mp h3
    simp only [Pi.add_apply]
    rw [abs_le]
    constructor <;> linarith [h2.1, h2.2, h4.1, h4.2]
  · intro b hb hc τ
    rw [eS, eS', enclosingCell_refine hodd s2, enclosingCell_refine odd' s2', hF']
    simp only [spreadCLM, _root_.sum_apply]
    refine Finset.sum_congr rfl fun l _ => ?_
    have small : ∀ j, |(bb l).1 j - blockOf F.blockSide (sh b) j| ≤ (q : ℤ) + 12 := fun j => by
      have h1 := abs_le.mp ((hbb l).1 j)
      have h2 := abs_le.mp (h12 b hb j)
      rw [abs_le]
      constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]
    have i1 := bond_eq_iff Y (e := bb l) (h := blockOf F.blockSide (sh b)) (d := b.2) (fun j => by
      have h1 := small j
      have h2 : ((2 * q + 2 : ℕ) : ℤ) < F.extent j := by exact_mod_cast hs j
      push_cast at h2
      have h3 : (16 : ℤ) ≤ q := by exact_mod_cast hq
      linarith)
    have i2 := bond_eq_iff Y' (e := bb l) (h := blockOf F.blockSide (sh b)) (d := b.2) (fun j => by
      have h1 := small j
      have h2 : ((2 * q + 2 : ℕ) : ℤ) < F'.extent j := by exact_mod_cast hs' j
      push_cast at h2
      have h3 : (16 : ℤ) ≤ q := by exact_mod_cast hq
      linarith)
    have e1 : bondsAt Y bb l = ((Y + siteOfCoords F.top (bb l).1 : F.Cell), (bb l).2) := rfl
    have e2 : bondsAt Y' bb l = ((Y' + siteOfCoords F'.top (bb l).1 : F'.Cell), (bb l).2) := rfl
    rw [e1, e2]
    by_cases hh : (bb l).1 = blockOf F.blockSide (sh b) ∧ (bb l).2 = b.2
    · rw [if_pos (i1.mpr hh), if_pos (i2.mpr hh)]
    · rw [if_neg (fun q' => hh (i1.mp q')), if_neg (fun q' => hh (i2.mp q'))]
  · intro b hb ht
    exact (sV.analytic _ (mem_chordBonds hcov hodd p0 ht) k _ X).contDiffAt
  · intro b hb ht
    exact (sV'.analytic _ (mem_chordBonds hcov odd' p0' ht) k _ X).contDiffAt
  · intro b hb ht
    rw [lowF b, lowF' b]
    have h1 := loc.norm_sub_le _ _ _ (low b hb ht)
    refine h1.trans ?_
    have h2 := expo b hb
    have h3 : 0 ≤ C * σ := by positivity
    calc C * σ * Real.exp _ ≤ C * σ * Real.exp (-(δ₂ / 4 * ((q : ℝ) - 13))) := by gcongr
      _ ≤ C * 1 * Real.exp (-(δ₂ / 4 * ((q : ℝ) - 13))) := by gcongr
      _ = _ := by ring
  · intro b hb ht j ι h1 h2
    rw [lowF b, lowF' b]
    have h3 := loc.deriv_sub_le _ _ _ j (bb ∘ ι) (X ∘ ι) (low b hb ht) h1 (by omega) (fun l => hbb (ι l))
      (fun l => hX (ι l))
    exact h3.trans (mul_le_mul_of_nonneg_left (expo b hb) hC)
  · intro b hb ht j ι h1 h2
    have h3 := sV.deriv_decay _ (mem_chordBonds hcov hodd p0 ht) j (bondsAt Y bb ∘ ι) (X ∘ ι) h1 (by omega)
      (fun l => hX (ι l))
    refine h3.trans ?_
    have h4 : Real.exp (-(δ₂ / 4 *
        (bondListDistance (enclosingCell (boxSite Z b.1, b.2).1) (bondsAt Y bb ∘ ι) : ℝ))) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      have : 0 ≤ δ₂ / 4 * (bondListDistance (enclosingCell (boxSite Z b.1, b.2).1) (bondsAt Y bb ∘ ι) : ℝ) := by
        positivity
      linarith
    nlinarith
  · intro b hb ht j ι h1 h2
    have h3 := sV'.deriv_decay _ (mem_chordBonds hcov odd' p0' ht) j (bondsAt Y' bb ∘ ι) (X ∘ ι) h1 (by omega)
      (fun l => hX (ι l))
    refine h3.trans ?_
    have h4 : Real.exp (-(δ₂ / 4 *
        (bondListDistance (enclosingCell (boxSite Z' b.1, b.2).1) (bondsAt Y' bb ∘ ι) : ℝ))) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      have : 0 ≤ δ₂ / 4 *
          (bondListDistance (enclosingCell (boxSite Z' b.1, b.2).1) (bondsAt Y' bb ∘ ι) : ℝ) := by
        positivity
      linarith
    nlinarith
  · intro y j
    have hk' : (k : ℝ) ≤ 3 := by exact_mod_cast hk
    linarith [norm_spreadCLM_le (bondsAt Y bb) hX y j]
  · intro y j
    have hk' : (k : ℝ) ≤ 3 := by exact_mod_cast hk
    linarith [norm_spreadCLM_le (bondsAt Y' bb) hX y j]
end Matching
end Offsets
section Spans
variable {F : BlockFrame}
private theorem cellSupDist_triangle (u v z : F.Cell) : cellSupDist u v ≤ cellSupDist u z + cellSupDist z v := by
  unfold cellSupDist
  refine Finset.sup_le fun i _ => ?_
  have e : u i - v i = (u i - z i) + (z i - v i) := by ring
  rw [e]
  refine (ZMod.natAbs_valMinAbs_add_le _ _).trans ((Int.natAbs_add_le _ _).trans ?_)
  exact Nat.add_le_add (Finset.le_sup (f := fun i => ((u i - z i).valMinAbs).natAbs) (Finset.mem_univ i))
    (Finset.le_sup (f := fun i => ((z i - v i).valMinAbs).natAbs) (Finset.mem_univ i))
private theorem le_cellSetDiameter {P : Finset F.Cell} {u v : F.Cell} (hu : u ∈ P) (hv : v ∈ P) :
    cellSupDist u v ≤ cellSetDiameter P := by apply _root_.YangMills.Construction.Interpolation.ObservableSizes.cellSupDist_le_cellSetDiameter <;> assumption
private theorem cellSetDiameter_insert_union_le (z : F.Cell) (A B : Finset F.Cell) :
    cellSetDiameter (insert z (A ∪ B)) ≤ cellSetDiameter (insert z A) + cellSetDiameter (insert z B) := by
  classical
  unfold cellSetDiameter
  refine Finset.sup_le fun u hu => Finset.sup_le fun v hv => ?_
  have key : ∀ w ∈ insert z (A ∪ B), w ∈ insert z A ∨ w ∈ insert z B := by
    intro w hw
    simp only [Finset.mem_insert, Finset.mem_union] at hw ⊢
    tauto
  have zA : z ∈ insert z A := Finset.mem_insert_self _ _
  have zB : z ∈ insert z B := Finset.mem_insert_self _ _
  change cellSupDist u v ≤ cellSetDiameter (insert z A) + cellSetDiameter (insert z B)
  rcases key u hu with h1 | h1 <;> rcases key v hv with h2 | h2
  · exact (le_cellSetDiameter h1 h2).trans (Nat.le_add_right _ _)
  · exact (cellSupDist_triangle u v z).trans
      (Nat.add_le_add (le_cellSetDiameter h1 zA) (le_cellSetDiameter zB h2))
  · have := Nat.add_le_add (le_cellSetDiameter h1 zB) (le_cellSetDiameter zA h2)
    rw [Nat.add_comm] at this
    exact (cellSupDist_triangle u v z).trans (by omega)
  · exact (le_cellSetDiameter h1 h2).trans (Nat.le_add_left _ _)
private theorem bondSpan_le {k : ℕ} (Y z : F.Cell) (hz : cellSupDist Y z ≤ 1) (c : Fin k → F.Site F.top × Fin 4) :
    bondSpan Y c ≤ cellSetDiameter (insert z (topBondCells c)) + 1 := by
  classical
  have mem : ∀ l, (c l).1 ∈ insert z (topBondCells c) := fun l =>
    Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ (Finset.mem_univ l))
  have zm : z ∈ insert z (topBondCells c) := Finset.mem_insert_self _ _
  unfold bondSpan
  refine max_le (Finset.sup_le fun l _ => ?_) (Finset.sup_le fun l _ => Finset.sup_le fun l' _ => ?_)
  · have h1 : siteSupDist Y (c l).1 = cellSupDist Y (c l).1 := rfl
    rw [h1]
    have h2 := cellSupDist_triangle Y (c l).1 z
    have h3 := le_cellSetDiameter zm (mem l)
    omega
  · have h1 : siteSupDist (c l).1 (c l').1 = cellSupDist (c l).1 (c l').1 := rfl
    rw [h1]
    exact (le_cellSetDiameter (mem l) (mem l')).trans (Nat.le_succ _)
private theorem exp_mul_exp_le {R : ℝ} (hR : 0 ≤ R) {S S₁ S₂ : ℕ} (h : S ≤ S₁ + S₂) :
    Real.exp (-(R * S₁)) * Real.exp (-(R * S₂)) ≤ Real.exp (-(R * S)) := by
  rw [← Real.exp_add]
  refine Real.exp_le_exp.mpr ?_
  have : (S : ℝ) ≤ S₁ + S₂ := by exact_mod_cast h
  nlinarith
end Spans
section Kernel
variable {F : BlockFrame}
private theorem iteratedFDeriv_cast {n j : ℕ} (e : n = j) (f : (Fin n → ℝ) → ℝ) (g : (Fin j → ℝ) → ℝ)
    (hfg : ∀ τ, f τ = g fun i => τ (Fin.cast e.symm i)) :
    iteratedFDeriv ℝ n f 0 (fun l => Pi.single l 1) = iteratedFDeriv ℝ j g 0 (fun l => Pi.single l 1) := by
  subst e
  have : f = g := funext fun τ => by simpa using hfg τ
  rw [this]
private theorem logContour_bondDeriv_le {a ρA κ κ₂ rE x : ℝ} {m : ℕ} {K : ℕ → ℝ} {D : ℕ → ℕ → ℝ}
    {V : F.GaugeField F.top} (h : HasInterpolationKernels 1 a ρA κ κ₂ rE x m K D V 0)
    (c₀ : F.Site F.top × Fin 4) {j : ℕ} (hj : 1 ≤ j) (c : Fin j → F.Site F.top × Fin 4)
    (X : Fin j → imaginaryQuaternions) (hX : AreUnitVectors X) :
    |bondDeriv (logContourNorm 1 a ρA m c₀ 0) V c X| ≤
      D 0 j * Real.exp (-(2 ^ 8 * κ * cellSetDiameter (insert c₀.1 (topBondCells c)))) := by
  classical
  have h1 := (h.logContour c₀ 0 j (fun i => i.elim0) (fun i => i.elim0) c X (by omega) (fun i => i.elim0) hX).2
  have e1 : jointMixedDeriv (logContourNorm 1 a ρA m c₀) 0 V (fun i : Fin 0 => i.elim0)
      (fun i : Fin 0 => i.elim0) c X = bondDeriv (logContourNorm 1 a ρA m c₀ 0) V c X := by
    unfold jointMixedDeriv bondDeriv
    refine iteratedFDeriv_cast (Nat.zero_add j) _ _ fun τ => ?_
    simp only [jointDisplacement, displacedPoint]
    have e2 : (fun i : Fin j => τ (Fin.natAdd 0 i)) = fun i => τ (Fin.cast (Nat.zero_add j).symm i) := by
      funext i
      congr 1
      ext
      simp
    rw [e2]
    simp
  rw [e1] at h1
  have e3 : ({c₀.1} ∪ chordBondCells (fun i : Fin 0 => i.elim0) ∪ topBondCells c : Finset F.Cell) =
      insert c₀.1 (topBondCells c) := by
    ext u
    simp [chordBondCells]
  rw [e3] at h1
  exact h1
end Kernel
section Sizes
variable {F : BlockFrame}
private theorem half_le_norm_contourAverage (hL : Odd F.blockSide) (W : F.GaugeField F.depth)
    (V : F.GaugeField F.top) (c : F.Site F.top × Fin 4)
    (h : ∀ (h : Fin 4 → ℤ) (π : Equiv.Perm (Fin 4)), h ∈ centredCube F.blockSide →
      ‖contourHolonomyDefect W V c h π - 1‖ ≤ 1 / 2) :
    1 / 2 ≤ ‖_root_.YangMills.Construction.BlockAverages.contourAverage W c‖ := by
  classical
  set z : (Fin 4 → ℤ) → Equiv.Perm (Fin 4) → ℍ[ℝ] := fun h π =>
    ((pathHolonomy W (refineSite c.1) (bondContour F.blockSide h π c.2) : UnitQuaternion) : ℍ[ℝ]) with hz
  set v : ℍ[ℝ] := (((V c.1 c.2)⁻¹ : UnitQuaternion) : ℍ[ℝ]) with hv
  have hnv : ‖v‖ = 1 := BlockOffsets.norm_coe_unitQuaternion _
  have hr : ∀ h π, contourHolonomyDefect W V c h π = z h π * v := fun h π => rfl
  have hLpos : (0 : ℝ) < F.blockSide := by
    have := hL.pos
    exact_mod_cast this
  set n : ℝ := 24 * (F.blockSide : ℝ) ^ 4 with hn
  have hn0 : 0 < n := by positivity
  have hcard : ((centredCube F.blockSide).card : ℝ) = (F.blockSide : ℝ) ^ 4 := by
    unfold centredCube
    rw [Fintype.card_piFinset]
    have h : ∀ i : Fin 4,
        (Finset.Icc (-(((F.blockSide : ℤ) - 1) / 2)) (((F.blockSide : ℤ) - 1) / 2)).card = F.blockSide := by
      intro _
      obtain ⟨r, hr'⟩ := hL
      rw [hr']
      have e : (((2 * r + 1 : ℕ) : ℤ) - 1) / 2 = r := by push_cast; omega
      rw [e, Int.card_Icc]
      omega
    rw [Finset.prod_congr rfl (fun i _ => h i)]
    simp
  have hcount : ((centredCube F.blockSide).card : ℝ) * 24 = n := by
    rw [hcard, hn]
    ring
  have hmean : _root_.YangMills.Construction.BlockAverages.contourAverage W c = (1 / n) • ∑ h ∈ centredCube F.blockSide, ∑ π : Equiv.Perm (Fin 4), z h π :=
    rfl
  have hsum1 : ∑ h ∈ centredCube F.blockSide, ∑ _π : Equiv.Perm (Fin 4), (1 : ℝ) = n := by
    simp only [Finset.sum_const, nsmul_eq_mul, mul_one, Finset.card_univ, Fintype.card_perm,
      Fintype.card_fin]
    rw [← hcount]
    norm_num
  have e1 : _root_.YangMills.Construction.BlockAverages.contourAverage W c * v - 1 =
      (1 / n) • ∑ h ∈ centredCube F.blockSide, ∑ π : Equiv.Perm (Fin 4), (z h π * v - 1) := by
    have h1 : (∑ h ∈ centredCube F.blockSide, ∑ _π : Equiv.Perm (Fin 4), (1 : ℍ[ℝ])) = (n : ℝ) • (1 : ℍ[ℝ]) := by
      rw [← hsum1, Finset.sum_smul]
      refine Finset.sum_congr rfl fun h' _ => ?_
      rw [Finset.sum_smul]
      simp
    have h2 : ∑ h ∈ centredCube F.blockSide, ∑ π : Equiv.Perm (Fin 4), (z h π * v - 1) =
        (∑ h ∈ centredCube F.blockSide, ∑ π : Equiv.Perm (Fin 4), z h π) * v - (n : ℝ) • (1 : ℍ[ℝ]) := by
      simp only [Finset.sum_sub_distrib, Finset.sum_mul]
      rw [h1]
    rw [hmean, h2, smul_sub, smul_smul, one_div, inv_mul_cancel₀ hn0.ne', one_smul, smul_mul_assoc]
  have e2 : ‖_root_.YangMills.Construction.BlockAverages.contourAverage W c * v - 1‖ ≤ 1 / 2 := by
    rw [e1, norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity)]
    have h2 : ‖∑ h ∈ centredCube F.blockSide, ∑ π : Equiv.Perm (Fin 4), (z h π * v - 1)‖ ≤ n * (1 / 2) := by
      refine (norm_sum_le _ _).trans ?_
      have : ∀ h ∈ centredCube F.blockSide, ‖∑ π : Equiv.Perm (Fin 4), (z h π * v - 1)‖ ≤
          ∑ _π : Equiv.Perm (Fin 4), (1 / 2 : ℝ) := fun h' hh =>
        (norm_sum_le _ _).trans (Finset.sum_le_sum fun π _ => by
          rw [← hr]; exact h h' π hh)
      refine (Finset.sum_le_sum this).trans (le_of_eq ?_)
      rw [← hsum1]
      simp [Finset.mul_sum]
      ring
    have h3 := mul_le_mul_of_nonneg_left h2 (by positivity : 0 ≤ 1 / n)
    have h4 : 1 / n * (n * (1 / 2)) = 1 / 2 := by field_simp
    linarith
  have e3 : ‖_root_.YangMills.Construction.BlockAverages.contourAverage W c * v‖ = ‖_root_.YangMills.Construction.BlockAverages.contourAverage W c‖ := by rw [norm_mul, hnv, mul_one]
  have e4 : 1 - ‖_root_.YangMills.Construction.BlockAverages.contourAverage W c * v‖ ≤ ‖_root_.YangMills.Construction.BlockAverages.contourAverage W c * v - 1‖ := by
    have := norm_sub_norm_le (1 : ℍ[ℝ]) (_root_.YangMills.Construction.BlockAverages.contourAverage W c * v)
    rw [norm_one, norm_sub_rev] at this
    exact this
  linarith
private theorem contourAverage_norm_bounds {a ρA δ₂ C σ : ℝ} {m : ℕ} {V : F.GaugeField F.top}
    (hodd : Odd F.blockSide) (hS : InterpolatedFrameSmall 1 a ρA δ₂ C σ m V) (hC : C * σ ≤ 1 / 2)
    (c₀ : F.Site F.top × Fin 4) :
    1 / 2 ≤ ‖_root_.YangMills.Construction.BlockAverages.contourAverage (interpolatedField 1 a ρA m V 0) c₀‖ ∧
      ‖_root_.YangMills.Construction.BlockAverages.contourAverage (interpolatedField 1 a ρA m V 0) c₀‖ ≤ 1 := by
  refine ⟨?_, norm_contourAverage_le_one hodd _ _⟩
  rw [interpolatedField_zero]
  exact half_le_norm_contourAverage hodd _ V c₀ fun h π hh => (hS.contour_near_one c₀ h π hh).trans hC
private def sizeSqAlong {k : ℕ} (L : ℕ) (i : Fin 4) (a ρA : ℝ) (m : ℕ) (Z : F.Cell) (V : F.GaugeField F.top)
    (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions) (τ : Fin k → ℝ) : ℝ :=
  boxSizeSq L i (boxData L (interpolatedFrame 1 a ρA m) Z V c X τ)
private theorem sizeSqAlong_eq {k L : ℕ} (hF : F.blockSide = L) (i : Fin 4) (a ρA : ℝ) (m : ℕ) (Z : F.Cell)
    (V : F.GaugeField F.top) (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions)
    (τ : Fin k → ℝ) :
    sizeSqAlong L i a ρA m Z V c X τ =
      ‖_root_.YangMills.Construction.BlockAverages.contourAverage (interpolatedField 1 a ρA m
        (leftTranslate (ColdStepAtMirrorFrames.bondSpread c X τ) V) 0) (Z, i)‖ ^ 2 := by
  rw [contourAverage_eq_box hF]
  rfl
private theorem contDiffAt_sizeSqAlong (hcov : BlocksCoverLowerLevel) {k L : ℕ} (hodd : Odd F.blockSide)
    (hs : ∀ i, 0 < F.extent i) (i : Fin 4) {a ρA δ₂ C σ : ℝ} {m : ℕ} (Z : F.Cell) {V : F.GaugeField F.top}
    (hS : InterpolatedFrameSmall 1 a ρA δ₂ C σ m V) (c : Fin k → F.Site F.top × Fin 4)
    (X : Fin k → imaginaryQuaternions) : ContDiffAt ℝ 3 (sizeSqAlong L i a ρA m Z V c X) 0 :=
  (contDiff_boxSizeSq L i).contDiffAt.comp (0 : Fin k → ℝ) (contDiffAt_boxData L _ Z V c X fun _ _ ht =>
    (hS.analytic _ (mem_chordBonds hcov hodd hs ht) k c X).contDiffAt)
private theorem sizeSqAlong_zero_mem {k L : ℕ} (hF : F.blockSide = L) (hodd : Odd F.blockSide) (i : Fin 4)
    {a ρA δ₂ C σ : ℝ} {m : ℕ} (Z : F.Cell) {V : F.GaugeField F.top}
    (hS : InterpolatedFrameSmall 1 a ρA δ₂ C σ m V) (hC : C * σ ≤ 1 / 2) (c : Fin k → F.Site F.top × Fin 4)
    (X : Fin k → imaginaryQuaternions) :
    sizeSqAlong L i a ρA m Z V c X 0 ∈ Set.Icc (1 / 4 : ℝ) 1 := by
  rw [sizeSqAlong_eq hF, leftTranslate_bondSpread_zero]
  obtain ⟨h1, h2⟩ := contourAverage_norm_bounds hodd hS hC (Z, i)
  exact ⟨by nlinarith, by nlinarith⟩
private theorem scoreRemainderAt_eq_comp {k L : ℕ} (hF : F.blockSide = L) (Q : ColdHalfLaw) (i : Fin 4)
    (Z : F.Cell) (V : F.GaugeField F.top) (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions) :
    (fun τ : Fin k → ℝ =>
      Q.scoreRemainderAt (Z, i) 0 (leftTranslate (ColdStepAtMirrorFrames.bondSpread c X τ) V)) =
      (Q.scoreRemainder ∘ Real.sqrt) ∘ sizeSqAlong L i Q.a Q.chartRadius Q.mirrorRadius Z V c X := by
  funext τ
  simp only [Function.comp, ColdHalfLaw.scoreRemainderAt, ColdHalfLaw.contourAverageSize]
  rw [sizeSqAlong_eq hF, Real.sqrt_sq (norm_nonneg _)]
end Sizes
section Decay
variable {F : BlockFrame}
private theorem cellSetDiameter_mono {P P' : Finset F.Cell} (h : P ⊆ P') :
    cellSetDiameter P ≤ cellSetDiameter P' := by apply _root_.YangMills.SharedProofs.p30422 <;> assumption
private def sublistDiameter {k j : ℕ} (z : F.Cell) (c : Fin k → F.Site F.top × Fin 4) (ι : Fin j → Fin k) : ℕ :=
  cellSetDiameter (insert z (topBondCells (c ∘ ι)))
private theorem sublistDiameter_le {k j j₁ j₂ : ℕ} (z : F.Cell) (c : Fin k → F.Site F.top × Fin 4)
    (ι : Fin j → Fin k) (ι₁ : Fin j₁ → Fin k) (ι₂ : Fin j₂ → Fin k)
    (h : ∀ l, (∃ a, ι₁ a = ι l) ∨ ∃ b, ι₂ b = ι l) :
    sublistDiameter z c ι ≤ sublistDiameter z c ι₁ + sublistDiameter z c ι₂ := by
  classical
  refine (cellSetDiameter_mono ?_).trans (cellSetDiameter_insert_union_le z _ _)
  intro u hu
  simp only [topBondCells, Finset.mem_insert, Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and,
    Function.comp] at hu ⊢
  rcases hu with rfl | ⟨l, rfl⟩
  · exact Or.inl rfl
  · rcases h l with ⟨a, ha⟩ | ⟨b, hb⟩
    · exact Or.inr (Or.inl ⟨a, by rw [ha]⟩)
    · exact Or.inr (Or.inr ⟨b, by rw [hb]⟩)
private theorem scoreRemainderAt_bondDeriv_le (hC : ThirdOrderChainRule) (hcov : BlocksCoverLowerLevel)
    {k L : ℕ} (hF : F.blockSide = L) (hodd : Odd F.blockSide) (hs : ∀ i, 0 < F.extent i) (Q : ColdHalfLaw)
    (i : Fin 4) (Z : F.Cell) {δ₂ C σ κ κ₂ rE x : ℝ} {K : ℕ → ℝ} {D : ℕ → ℕ → ℝ} {V : F.GaugeField F.top}
    (hS : InterpolatedFrameSmall 1 Q.a Q.chartRadius δ₂ C σ Q.mirrorRadius V) (hCσ : C * σ ≤ 1 / 2)
    (hker : HasInterpolationKernels 1 Q.a Q.chartRadius κ κ₂ rE x Q.mirrorRadius K D V 0) {M Dm : ℝ}
    (hφ : DerivBoundedOn (Q.scoreRemainder ∘ Real.exp) (Set.Icc (Real.log (1 / 2)) 0) M) (hκ : 0 ≤ κ)
    (hDm1 : 1 ≤ Dm) (hDm : ∀ j, 1 ≤ j → j ≤ 3 → D 0 j ≤ Dm) (c : Fin k → F.Site F.top × Fin 4)
    (X : Fin k → imaginaryQuaternions) (hX : AreUnitVectors X) (h1 : 1 ≤ k) (h3 : k ≤ 3) :
    |bondDeriv (Q.scoreRemainderAt (Z, i) 0) V c X| ≤
      5 * M * Dm ^ 3 * Real.exp (-(2 ^ 8 * κ * sublistDiameter Z c id)) := by
  classical
  set R : ℝ := 2 ^ 8 * κ with hR
  have hR0 : 0 ≤ R := by positivity
  let ℓf : F.GaugeField F.top → ℝ := logContourNorm 1 Q.a Q.chartRadius Q.mirrorRadius (Z, i) 0
  let ℓτ : (Fin k → ℝ) → ℝ := fun τ => ℓf (leftTranslate (ColdStepAtMirrorFrames.bondSpread c X τ) V)
  have hρ := contDiffAt_sizeSqAlong (L := L) hcov hodd hs i Z hS c X
  have hρ0 := sizeSqAlong_zero_mem (L := L) hF hodd i Z hS hCσ c X
  have eℓ : ℓτ = (fun s => 1 / 2 * Real.log s) ∘ sizeSqAlong L i Q.a Q.chartRadius Q.mirrorRadius Z V c X := by
    funext τ
    simp only [Function.comp, ℓτ, ℓf, logContourNorm]
    rw [sizeSqAlong_eq hF, Real.log_pow]
    push_cast
    ring
  have pos : 0 < sizeSqAlong L i Q.a Q.chartRadius Q.mirrorRadius Z V c X 0 := by linarith [hρ0.1]
  have hℓ : ContDiffAt ℝ 3 ℓτ 0 := by
    rw [eℓ]
    exact (contDiffAt_const.mul (Real.contDiffAt_log.mpr pos.ne')).comp (0 : Fin k → ℝ) hρ
  have mem : ℓτ 0 ∈ Set.Icc (Real.log (1 / 2)) 0 := by
    simp only [ℓτ, ℓf, logContourNorm, leftTranslate_bondSpread_zero]
    obtain ⟨b1, b2⟩ := contourAverage_norm_bounds hodd hS hCσ (Z, i)
    exact ⟨Real.log_le_log (by norm_num) b1, Real.log_nonpos (norm_nonneg _) b2⟩
  have ev : (fun τ : Fin k → ℝ =>
      Q.scoreRemainderAt (Z, i) 0 (leftTranslate (ColdStepAtMirrorFrames.bondSpread c X τ) V)) =ᶠ[𝓝 0]
      (Q.scoreRemainder ∘ Real.exp) ∘ ℓτ := by
    filter_upwards [hρ.continuousAt.eventually (lt_mem_nhds pos)] with τ hτ
    have e1 := sizeSqAlong_eq hF i Q.a Q.chartRadius Q.mirrorRadius Z V c X τ
    have hne : ‖_root_.YangMills.Construction.BlockAverages.contourAverage (interpolatedField 1 Q.a Q.chartRadius Q.mirrorRadius
        (leftTranslate (ColdStepAtMirrorFrames.bondSpread c X τ) V) 0) (Z, i)‖ ≠ 0 := by
      intro h0
      rw [e1, h0] at hτ
      norm_num at hτ
    have hp := lt_of_le_of_ne (norm_nonneg _) hne.symm
    simp only [Function.comp, ℓτ, ℓf, logContourNorm, ColdHalfLaw.scoreRemainderAt,
      ColdHalfLaw.contourAverageSize]
    rw [Real.exp_log hp]
  have eD : bondDeriv (Q.scoreRemainderAt (Z, i) 0) V c X =
      iteratedFDeriv ℝ k ((Q.scoreRemainder ∘ Real.exp) ∘ ℓτ) 0 (fun l => Pi.single l 1) := by
    unfold bondDeriv
    have ev' : (fun τ : Fin k → ℝ =>
        Q.scoreRemainderAt (Z, i) 0 (leftTranslate (ColdStepAtMirrorFrames.bondSpread c X τ) V)) =ᶠ[𝓝[Set.univ] 0]
        (Q.scoreRemainder ∘ Real.exp) ∘ ℓτ := by rwa [nhdsWithin_univ]
    have h0 : (fun τ : Fin k → ℝ =>
        Q.scoreRemainderAt (Z, i) 0 (leftTranslate (ColdStepAtMirrorFrames.bondSpread c X τ) V)) 0 =
        ((Q.scoreRemainder ∘ Real.exp) ∘ ℓτ) 0 := Filter.EventuallyEq.eq_of_nhds ev
    have e := Filter.EventuallyEq.iteratedFDerivWithin_eq (𝕜 := ℝ) ev' h0 k
    simp only [iteratedFDerivWithin_univ] at e
    rw [e]
  obtain ⟨-, c1, c2, c3⟩ := hC _ ℓτ 0 (hφ.smooth _ mem) hℓ
  have hM : 0 ≤ M := (norm_nonneg _).trans (hφ.bound _ mem 0 (by norm_num))
  have m1 := hφ.bound _ mem 1 (by norm_num)
  have m2 := hφ.bound _ mem 2 (by norm_num)
  have m3 := hφ.bound _ mem 3 (by norm_num)
  have Ab : ∀ {j : ℕ} (ι : Fin j → Fin k), 1 ≤ j → j ≤ 3 →
      ‖iteratedFDeriv ℝ j ℓτ 0 (fun l => Pi.single (ι l) 1)‖ ≤
        Dm * Real.exp (-(R * sublistDiameter Z c ι)) := by
    intro j ι g1 g3
    have hj' : (j : WithTop ℕ∞) ≤ 3 := by exact_mod_cast g3
    have e := iteratedFDeriv_single_eq_bondDeriv ℓf V c X ι (hℓ.of_le hj')
    have e' : iteratedFDeriv ℝ j ℓτ 0 (fun l => Pi.single (ι l) 1) = bondDeriv ℓf V (c ∘ ι) (X ∘ ι) := e
    rw [e', Real.norm_eq_abs]
    refine (logContour_bondDeriv_le hker (Z, i) g1 (c ∘ ι) (X ∘ ι) (fun l => hX _)).trans ?_
    exact mul_le_mul_of_nonneg_right (hDm j g1 g3) (Real.exp_pos _).le
  have hDm0 : 0 ≤ Dm := by linarith
  have D2 : Dm ^ 2 ≤ Dm ^ 3 := by nlinarith [mul_nonneg hDm0 hDm0]
  have D1 : Dm ≤ Dm ^ 3 := by nlinarith [mul_nonneg hDm0 hDm0]
  set E := Real.exp (-(R * sublistDiameter Z c id)) with hE
  have hE0 : 0 ≤ E := (Real.exp_pos _).le
  have up2 : ∀ {y : ℝ}, y ≤ E → M * Dm ^ 2 * y ≤ M * Dm ^ 3 * E := fun {y} hy => by
    calc M * Dm ^ 2 * y ≤ M * Dm ^ 2 * E := by gcongr
      _ ≤ M * Dm ^ 3 * E := by gcongr
  have up1 : M * Dm * E ≤ M * Dm ^ 3 * E := by gcongr
  have hq : 0 ≤ M * Dm ^ 3 * E := by positivity
  rw [← Real.norm_eq_abs, eD]
  rcases (by omega : k = 1 ∨ k = 2 ∨ k = 3) with rfl | rfl | rfl
  · have em : (fun l : Fin 1 => (Pi.single l 1 : Fin 1 → ℝ)) = ![Pi.single 0 1] := by
      funext l
      fin_cases l
      rfl
    have a0 : ‖iteratedFDeriv ℝ 1 ℓτ 0 ![Pi.single 0 1]‖ ≤ Dm * E := by
      have := Ab (id : Fin 1 → Fin 1) le_rfl (by norm_num)
      simp only [id] at this
      rwa [em] at this
    rw [em, c1]
    have t : ‖iteratedFDeriv ℝ 1 (Q.scoreRemainder ∘ Real.exp) (ℓτ 0)
        ![iteratedFDeriv ℝ 1 ℓτ 0 ![Pi.single 0 1]]‖ ≤ M * (Dm * E) := (norm_apply_one_le _).trans (by gcongr)
    refine t.trans ?_
    linarith
  · have em : (fun l : Fin 2 => (Pi.single l 1 : Fin 2 → ℝ)) = ![Pi.single 0 1, Pi.single 1 1] := by
      funext l
      fin_cases l <;> rfl
    have a0 := Ab (![0] : Fin 1 → Fin 2) le_rfl (by norm_num)
    have a1 := Ab (![1] : Fin 1 → Fin 2) le_rfl (by norm_num)
    have a01 := Ab (id : Fin 2 → Fin 2) (by norm_num) (by norm_num)
    simp only [id] at a01
    rw [em] at a01
    rw [← singles_one] at a0 a1
    rw [em, c2]
    have P : Real.exp (-(R * sublistDiameter Z c (![0] : Fin 1 → Fin 2))) *
        Real.exp (-(R * sublistDiameter Z c (![1] : Fin 1 → Fin 2))) ≤ E :=
      exp_mul_exp_le hR0 (sublistDiameter_le Z c id _ _ fun l => by fin_cases l <;> simp)
    set e0 := Real.exp (-(R * sublistDiameter Z c (![0] : Fin 1 → Fin 2)))
    set e1 := Real.exp (-(R * sublistDiameter Z c (![1] : Fin 1 → Fin 2)))
    have t1 : ‖iteratedFDeriv ℝ 2 (Q.scoreRemainder ∘ Real.exp) (ℓτ 0)
        ![iteratedFDeriv ℝ 1 ℓτ 0 ![Pi.single 0 1], iteratedFDeriv ℝ 1 ℓτ 0 ![Pi.single 1 1]]‖ ≤
        M * ((Dm * e0) * (Dm * e1)) :=
      (norm_apply_two_le _ _).trans (by gcongr)
    have t2 : ‖iteratedFDeriv ℝ 1 (Q.scoreRemainder ∘ Real.exp) (ℓτ 0)
        ![iteratedFDeriv ℝ 2 ℓτ 0 ![Pi.single 0 1, Pi.single 1 1]]‖ ≤ M * (Dm * E) :=
      (norm_apply_one_le _).trans (by gcongr)
    refine (norm_add_le _ _).trans ((add_le_add t1 t2).trans ?_)
    have u1 := up2 P
    have e : M * ((Dm * e0) * (Dm * e1)) = M * Dm ^ 2 * (e0 * e1) := by ring
    have e' : M * (Dm * E) = M * Dm * E := by ring
    rw [e, e']
    linarith
  · have em : (fun l : Fin 3 => (Pi.single l 1 : Fin 3 → ℝ)) =
        ![Pi.single 0 1, Pi.single 1 1, Pi.single 2 1] := by
      funext l
      fin_cases l <;> rfl
    have a0 := Ab (![0] : Fin 1 → Fin 3) le_rfl (by norm_num)
    have a1 := Ab (![1] : Fin 1 → Fin 3) le_rfl (by norm_num)
    have a2 := Ab (![2] : Fin 1 → Fin 3) le_rfl (by norm_num)
    have a01 := Ab (![0, 1] : Fin 2 → Fin 3) (by norm_num) (by norm_num)
    have a02 := Ab (![0, 2] : Fin 2 → Fin 3) (by norm_num) (by norm_num)
    have a12 := Ab (![1, 2] : Fin 2 → Fin 3) (by norm_num) (by norm_num)
    have a012 := Ab (id : Fin 3 → Fin 3) (by norm_num) le_rfl
    simp only [id] at a012
    rw [em] at a012
    rw [← singles_one] at a0 a1 a2
    rw [← singles_two] at a01 a02 a12
    rw [em, c3]
    have P01 := exp_mul_exp_le hR0 (sublistDiameter_le Z c id (![0, 1] : Fin 2 → Fin 3) (![2] : Fin 1 → Fin 3)
      fun l => by fin_cases l <;> simp)
    have P02 := exp_mul_exp_le hR0 (sublistDiameter_le Z c id (![0, 2] : Fin 2 → Fin 3) (![1] : Fin 1 → Fin 3)
      fun l => by fin_cases l <;> simp)
    have P12 := exp_mul_exp_le hR0 (sublistDiameter_le Z c id (![1, 2] : Fin 2 → Fin 3) (![0] : Fin 1 → Fin 3)
      fun l => by fin_cases l <;> simp)
    have Pa := exp_mul_exp_le hR0 (sublistDiameter_le Z c (![0, 1] : Fin 2 → Fin 3) (![0] : Fin 1 → Fin 3)
      (![1] : Fin 1 → Fin 3) fun l => by fin_cases l <;> simp)
    set e0 := Real.exp (-(R * sublistDiameter Z c (![0] : Fin 1 → Fin 3)))
    set e1 := Real.exp (-(R * sublistDiameter Z c (![1] : Fin 1 → Fin 3)))
    set e2 := Real.exp (-(R * sublistDiameter Z c (![2] : Fin 1 → Fin 3)))
    set e01 := Real.exp (-(R * sublistDiameter Z c (![0, 1] : Fin 2 → Fin 3)))
    set e02 := Real.exp (-(R * sublistDiameter Z c (![0, 2] : Fin 2 → Fin 3)))
    set e12 := Real.exp (-(R * sublistDiameter Z c (![1, 2] : Fin 2 → Fin 3)))
    have p2 : 0 ≤ e2 := (Real.exp_pos _).le
    have P012 : e0 * e1 * e2 ≤ E := (mul_le_mul_of_nonneg_right Pa p2).trans P01
    have t1 : ‖iteratedFDeriv ℝ 3 (Q.scoreRemainder ∘ Real.exp) (ℓτ 0)
        ![iteratedFDeriv ℝ 1 ℓτ 0 ![Pi.single 0 1], iteratedFDeriv ℝ 1 ℓτ 0 ![Pi.single 1 1],
          iteratedFDeriv ℝ 1 ℓτ 0 ![Pi.single 2 1]]‖ ≤
        M * ((Dm * e0) * (Dm * e1) * (Dm * e2)) := (norm_apply_three_le _ _ _).trans (by gcongr)
    have t2 : ‖iteratedFDeriv ℝ 2 (Q.scoreRemainder ∘ Real.exp) (ℓτ 0)
        ![iteratedFDeriv ℝ 2 ℓτ 0 ![Pi.single 0 1, Pi.single 1 1], iteratedFDeriv ℝ 1 ℓτ 0 ![Pi.single 2 1]]‖ ≤
        M * ((Dm * e01) * (Dm * e2)) :=
      (norm_apply_two_le _ _).trans (by gcongr)
    have t3 : ‖iteratedFDeriv ℝ 2 (Q.scoreRemainder ∘ Real.exp) (ℓτ 0)
        ![iteratedFDeriv ℝ 2 ℓτ 0 ![Pi.single 0 1, Pi.single 2 1], iteratedFDeriv ℝ 1 ℓτ 0 ![Pi.single 1 1]]‖ ≤
        M * ((Dm * e02) * (Dm * e1)) :=
      (norm_apply_two_le _ _).trans (by gcongr)
    have t4 : ‖iteratedFDeriv ℝ 2 (Q.scoreRemainder ∘ Real.exp) (ℓτ 0)
        ![iteratedFDeriv ℝ 2 ℓτ 0 ![Pi.single 1 1, Pi.single 2 1], iteratedFDeriv ℝ 1 ℓτ 0 ![Pi.single 0 1]]‖ ≤
        M * ((Dm * e12) * (Dm * e0)) :=
      (norm_apply_two_le _ _).trans (by gcongr)
    have t5 : ‖iteratedFDeriv ℝ 1 (Q.scoreRemainder ∘ Real.exp) (ℓτ 0)
        ![iteratedFDeriv ℝ 3 ℓτ 0 ![Pi.single 0 1, Pi.single 1 1, Pi.single 2 1]]‖ ≤ M * (Dm * E) :=
      (norm_apply_one_le _).trans (by gcongr)
    refine (norm_add_le _ _).trans ((add_le_add ((norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans
      (add_le_add ((norm_add_le _ _).trans (add_le_add t1 t2)) t3)) t4)) t5).trans ?_)
    have u1 : M * ((Dm * e0) * (Dm * e1) * (Dm * e2)) ≤ M * Dm ^ 3 * E := by
      have e : M * ((Dm * e0) * (Dm * e1) * (Dm * e2)) = M * Dm ^ 3 * (e0 * e1 * e2) := by ring
      rw [e]
      gcongr
    have u2 : M * ((Dm * e01) * (Dm * e2)) ≤ M * Dm ^ 3 * E := by
      have e : M * ((Dm * e01) * (Dm * e2)) = M * Dm ^ 2 * (e01 * e2) := by ring
      rw [e]
      exact up2 P01
    have u3 : M * ((Dm * e02) * (Dm * e1)) ≤ M * Dm ^ 3 * E := by
      have e : M * ((Dm * e02) * (Dm * e1)) = M * Dm ^ 2 * (e02 * e1) := by ring
      rw [e]
      exact up2 P02
    have u4 : M * ((Dm * e12) * (Dm * e0)) ≤ M * Dm ^ 3 * E := by
      have e : M * ((Dm * e12) * (Dm * e0)) = M * Dm ^ 2 * (e12 * e0) := by ring
      rw [e]
      exact up2 P12
    linarith
end Decay
section Two
variable {F F' : BlockFrame}
private theorem boxData_mem_closedBall (hcov : BlocksCoverLowerLevel) {k L : ℕ} (hodd : Odd F.blockSide)
    (hs : ∀ i, 0 < F.extent i) {a ρA δ₂ C σ : ℝ} {m : ℕ} (Z : F.Cell) {V : F.GaugeField F.top}
    (hS : InterpolatedFrameSmall 1 a ρA δ₂ C σ m V) (hC : C * σ ≤ 1 / 2) (c : Fin k → F.Site F.top × Fin 4)
    (X : Fin k → imaginaryQuaternions) :
    boxData L (interpolatedFrame 1 a ρA m) Z V c X 0 ∈ Metric.closedBall (0 : BoxData L) 2 := by
  classical
  rw [mem_closedBall_zero_iff]
  refine (pi_norm_le_iff_of_nonneg (by norm_num)).mpr fun s => ?_
  obtain ⟨⟨b, hb⟩, sl⟩ := s
  fin_cases sl
  · show ‖frameSlot (interpolatedFrame 1 a ρA m) V c X (boxSite Z b.1) b.2 0‖ ≤ 2
    by_cases ht : IsAxialTreeBond (boxSite Z b.1, b.2)
    · simp [frameSlot, ht]
    · simp only [frameSlot, ht, if_false, leftTranslate_bondSpread_zero]
      have h1 := hS.norm_le _ (mem_chordBonds hcov hodd hs ht)
      have h2 : ‖((interpolatedFrame 1 a ρA m (boxSite Z b.1, b.2) V : imaginaryQuaternions) : ℍ[ℝ])‖ =
          ‖interpolatedFrame 1 a ρA m (boxSite Z b.1, b.2) V‖ := rfl
      rw [h2]
      linarith
  · show ‖moveSlot c X (boxSite Z b.1) b.2 0‖ ≤ 2
    simp [moveSlot]
  · show ‖topSlot V (boxSite Z b.1) b.2‖ ≤ 2
    by_cases hc : IsCrossingBond (boxSite Z b.1, b.2)
    · simp only [topSlot, hc, if_true]
      rw [BlockOffsets.norm_coe_unitQuaternion]
      norm_num
    · simp [topSlot, hc]
private theorem cellBond_eq (Y : F.Cell) (i : Fin 4) (back : Bool) :
    cellBond Y i back = (Y + siteOfCoords F.top (backOffset i back), i) :=
  Prod.ext (cellBond_fst Y i back) rfl
abbrev _root_.YangMills.DeltaSharedProofs.p501180 := @cellBond_eq
private theorem secondOrderClose_of_agree (hC : ThirdOrderChainRule) (hcov : BlocksCoverLowerLevel) {L : ℕ}
    (hodd : Odd L) (hF : F.blockSide = L) (hF' : F'.blockSide = L) (Q : ColdHalfLaw) {δ₂ K C σ : ℝ}
    (hδ : 0 ≤ δ₂) (hC0 : 0 ≤ C) (hσ0 : 0 ≤ σ) (hσ : σ ≤ 1) (hCσ : C * σ ≤ 1 / 2) {Y : F.Cell} {Y' : F'.Cell}
    {V : F.GaugeField F.top} {V' : F'.GaugeField F'.top} {q : ℕ} (hq : 16 ≤ q)
    (hs : ∀ i, 2 * q + 2 < F.extent i) (hs' : ∀ i, 2 * q + 2 < F'.extent i)
    (sV : InterpolatedFrameSmall 1 Q.a Q.chartRadius δ₂ C σ Q.mirrorRadius V)
    (sV' : InterpolatedFrameSmall 1 Q.a Q.chartRadius δ₂ C σ Q.mirrorRadius V')
    (loc : InterpolatedFrameLocal 1 Q.a Q.chartRadius δ₂ K C σ Q.mirrorRadius V V' Y Y' q)
    (agree : AgreeOnBall (finiteCells F) V (finiteCells F') V' Y Y' q) (i : Fin 4) (back : Bool) {k : ℕ}
    (hk : k ≤ 3) (bb : Fin k → Offset × Fin 4) (hbb : ∀ l, BondWithinRadius q (bb l))
    (X : Fin k → imaginaryQuaternions) (hX : AreUnitVectors X) (ι : Fin 2 → Fin k) {M Mz : ℝ}
    (hψ : DerivBoundedOn (Q.scoreRemainder ∘ Real.sqrt) (Set.Icc (1 / 4) 1) M) (hMz1 : 1 ≤ Mz)
    (hz : DerivBoundedOn (boxSizeSq L i) (Metric.closedBall 0 2) Mz) :
    SecondOrderClose
      (fun τ : Fin k → ℝ => Q.scoreRemainderAt (cellBond Y i back) 0
        (leftTranslate (ColdStepAtMirrorFrames.bondSpread (bondsAt Y bb) X τ) V))
      (fun τ : Fin k → ℝ => Q.scoreRemainderAt (cellBond Y' i back) 0
        (leftTranslate (ColdStepAtMirrorFrames.bondSpread (bondsAt Y' bb) X τ) V'))
      (Pi.single (ι 0) 1) (Pi.single (ι 1) 1)
      (8 * M * (8 * Mz * (C + 3) ^ 2) ^ 2 *
        (8 * Mz * (C + 3) ^ 2 * (C * Real.exp (-(δ₂ / 4 * ((q : ℝ) - 13))))))
      (8 * M * (8 * Mz * (C + 3) ^ 2) ^ 2) := by
  have odd1 : Odd F.blockSide := hF ▸ hodd
  have odd2 : Odd F'.blockSide := hF' ▸ hodd
  have p0 : ∀ i, 0 < F.extent i := fun i => by have := hs i; omega
  have p0' : ∀ i, 0 < F'.extent i := fun i => by have := hs' i; omega
  have h1 := (boxMatch hcov hodd hF hF' hδ hC0 hσ0 hσ hq hs hs' sV sV' loc agree i back hk bb hbb X hX).secondOrderClose ι
  have hB : (1 : ℝ) ≤ C + 3 := by linarith
  have hB2 : 1 ≤ (C + 3) ^ 2 := one_le_pow₀ hB
  have h2 := h1.comp hC hz (convex_closedBall _ _) (boxData_mem_closedBall hcov odd1 p0 _ sV hCσ _ _)
    (boxData_mem_closedBall hcov odd2 p0' _ sV' hCσ _ _) hB
  have hB' : 1 ≤ 8 * Mz * (C + 3) ^ 2 := by nlinarith
  have h3 := h2.comp hC hψ (convex_Icc _ _) (sizeSqAlong_zero_mem hF odd1 i _ sV hCσ _ X)
    (sizeSqAlong_zero_mem hF' odd2 i _ sV' hCσ _ X) hB'
  have e : (fun τ : Fin k → ℝ => Q.scoreRemainderAt (cellBond Y i back) 0
      (leftTranslate (ColdStepAtMirrorFrames.bondSpread (bondsAt Y bb) X τ) V)) =
      (Q.scoreRemainder ∘ Real.sqrt) ∘ boxSizeSq L i ∘ boxData L (interpolatedFrame 1 Q.a Q.chartRadius Q.mirrorRadius)
        (Y + siteOfCoords F.top (backOffset i back)) V (bondsAt Y bb) X := by
    rw [cellBond_eq, scoreRemainderAt_eq_comp hF]
    rfl
  have e' : (fun τ : Fin k → ℝ => Q.scoreRemainderAt (cellBond Y' i back) 0
      (leftTranslate (ColdStepAtMirrorFrames.bondSpread (bondsAt Y' bb) X τ) V')) =
      (Q.scoreRemainder ∘ Real.sqrt) ∘ boxSizeSq L i ∘ boxData L (interpolatedFrame 1 Q.a Q.chartRadius Q.mirrorRadius)
        (Y' + siteOfCoords F'.top (backOffset i back)) V' (bondsAt Y' bb) X := by
    rw [cellBond_eq, scoreRemainderAt_eq_comp hF']
    rfl
  rw [e, e']
  exact h3
end Two
private theorem boxSizeSq_bounded (L : ℕ) :
    ∃ Mz : ℝ, 1 ≤ Mz ∧ ∀ i, DerivBoundedOn (boxSizeSq L i) (Metric.closedBall 0 2) Mz := by
  have h : ∀ i, ∃ M : ℝ, 1 ≤ M ∧ DerivBoundedOn (boxSizeSq L i) (Metric.closedBall 0 2) M := fun i =>
    derivBoundedOn_of_isCompact (isCompact_closedBall _ _) fun y _ => (contDiff_boxSizeSq L i).contDiffAt
  choose M h1 h2 using h
  have p := fun i => h1 i
  refine ⟨M 0 + M 1 + M 2 + M 3, by linarith [p 0, p 1, p 2, p 3], fun i => (h2 i).mono subset_rfl ?_⟩
  fin_cases i <;> simp <;> linarith [p 0, p 1, p 2, p 3]
private def unitImaginary : imaginaryQuaternions := ⟨⟨0, 1, 0, 0⟩, rfl⟩
private theorem norm_unitImaginary : ‖unitImaginary‖ = 1 := by
  have h : Quaternion.normSq ((unitImaginary : imaginaryQuaternions) : ℍ[ℝ]) = 1 := by
    rw [Quaternion.normSq_def' ((unitImaginary : imaginaryQuaternions) : ℍ[ℝ])]
    show (0 : ℝ) ^ 2 + 1 ^ 2 + 0 ^ 2 + 0 ^ 2 = 1
    norm_num
  rw [Quaternion.normSq_eq_norm_mul_self] at h
  have h0 : 0 ≤ ‖((unitImaginary : imaginaryQuaternions) : ℍ[ℝ])‖ := norm_nonneg _
  exact show ‖((unitImaginary : imaginaryQuaternions) : ℍ[ℝ])‖ = 1 from by nlinarith
private structure ParameterFloors (cf : _root_.YangMills.Construction.ColdStepAtMirrorFrames.StepParameters → ℝ) (T : _root_.YangMills.Construction.ColdStepAtMirrorFrames.StepParameters) : Prop where
  a1 : 1 ≤ T.a
  odd : Odd T.L
  n2 : 2 ≤ T.n₀
  κ0 : 0 < T.κ
  κδ : 2 ^ 10 * T.κ ≤ T.chainParams.δ₂
  δ0 : 0 < T.chainParams.δ₂
  Ct0 : 0 ≤ T.Ct
  σ0 : 0 < T.σ
  σ1 : T.σ ≤ 1
  Cσ : T.Ct * T.σ ≤ 1 / 2
  y3 : 3 ≤ T.coupling
  Cs : cf (rateParameters T) ≤ T.Cs
private theorem eventually_parameterFloors (cf : _root_.YangMills.Construction.ColdStepAtMirrorFrames.StepParameters → ℝ) :
    EventuallyInParameters (ParameterFloors cf) := by
  intro a ha
  refine ⟨0, fun L hL _ c hc => ?_⟩
  have hδ : 0 < c.δ₂ := hc.classical.1.2.2.2.1
  refine ⟨0, fun Ct hCt => ?_⟩
  refine ⟨c.δ₂ / 2 ^ 10, by positivity, fun κ h0 hκ => ?_⟩
  refine ⟨1, one_pos, fun η₃ _ _ _ => ?_⟩
  refine ⟨0, fun nss _ => ?_⟩
  refine ⟨min 1 (1 / (2 * (Ct + 1))), lt_min one_pos (by positivity), fun σ hσ0 hσ p hp => ?_⟩
  refine ⟨cf ⟨a, L, c, Ct, κ, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, fun Cs hCs E hE => ?_⟩
  refine ⟨2, fun n₀ hn => ?_⟩
  refine ⟨0, fun CE _ => ?_⟩
  refine ⟨3, fun y₁ hy => ?_⟩
  have h1 : σ ≤ 1 / (2 * (Ct + 1)) := hσ.trans (min_le_right _ _)
  have h2 : Ct * σ ≤ 1 / 2 := by
    have h3 : (Ct + 1) * σ ≤ 1 / 2 := by
      rw [le_div_iff₀ (by positivity)] at h1
      nlinarith
    nlinarith
  refine ⟨ha, hL, hn, h0, ?_, hδ, hCt, hσ0, hσ.trans (min_le_left _ _), h2, hy, hCs⟩
  have := (le_div_iff₀ (by positivity : (0 : ℝ) < 2 ^ 10)).mp hκ
  simpa [mul_comm] using this
private def decayConstant (Mt : ℝ → ℝ) (Mz : ℕ → ℝ) (Dm : _root_.YangMills.Construction.ColdStepAtMirrorFrames.StepParameters → ℝ) (T : _root_.YangMills.Construction.ColdStepAtMirrorFrames.StepParameters) : ℝ :=
  5 * Mt T.a * Dm T ^ 3 * Real.exp (2 ^ 8 * T.κ) +
    8 * Mt T.a * (8 * Mz T.L * (T.Ct + 3) ^ 2) ^ 2 *
      (8 * Mz T.L * (T.Ct + 3) ^ 2 * (T.Ct * Real.exp (13 * (T.chainParams.δ₂ / 4)))) +
    2 * (Mt T.a + 5 * Mt T.a * Dm T ^ 3 * Real.exp (2 ^ 8 * T.κ)) * Real.exp (16 * (2 ^ 8 * T.κ))
private theorem bondDeriv_zero {F : BlockFrame} (G : F.GaugeField F.top → ℝ) (V : F.GaugeField F.top)
    (c : Fin 0 → F.Site F.top × Fin 4) (X : Fin 0 → imaginaryQuaternions) : bondDeriv G V c X = G V := by apply _root_.YangMills.SharedProofs.p1654 <;> assumption
private theorem scoreRemainderDecayAt_of_bounds (hC : ThirdOrderChainRule) (hcov : BlocksCoverLowerLevel)
    {T : _root_.YangMills.Construction.ColdStepAtMirrorFrames.StepParameters} {K : ℕ → ℝ} {D : ℕ → ℕ → ℝ} {Mt : ℝ → ℝ} {Mz : ℕ → ℝ} {Dm : _root_.YangMills.Construction.ColdStepAtMirrorFrames.StepParameters → ℝ}
    (hM1 : 1 ≤ Mt T.a)
    (tail : ∀ Q : ColdHalfLaw, Q.a = T.a → 3 / T.a ≤ Q.coupling →
      DerivBoundedOn Q.scoreRemainder (Set.Icc (1 / 2) 1) (Mt T.a) ∧
      DerivBoundedOn (Q.scoreRemainder ∘ Real.exp) (Set.Icc (Real.log (1 / 2)) 0) (Mt T.a) ∧
      DerivBoundedOn (Q.scoreRemainder ∘ Real.sqrt) (Set.Icc (1 / 4) 1) (Mt T.a))
    (hz1 : 1 ≤ Mz T.L) (hz : ∀ i, DerivBoundedOn (boxSizeSq T.L i) (Metric.closedBall 0 2) (Mz T.L))
    (hD1 : 1 ≤ Dm (rateParameters T)) (hD : ∀ j, 1 ≤ j → j ≤ 3 → D 0 j ≤ Dm (rateParameters T))
    (fl : ParameterFloors (decayConstant Mt Mz Dm) T) (kern : interpolationKernelBoundsAt T K D)
    (near : ∀ (t : ℕ) (x : ℝ), T.coupling ≤ x → InterpolatedFramesControlledAt T t x) :
    ScoreRemainderDecayAt T := by
  intro t x f i back hx
  set Q := coldHalfLawAt T x f with hQ
  set R : ℝ := 2 ^ 8 * T.κ with hR
  set M := Mt T.a with hMdef
  set Dd := Dm (rateParameters T) with hDd
  have hR0 : 0 ≤ R := by have := fl.κ0; positivity
  have hQ3 : 3 / Q.a ≤ Q.coupling := by
    have h1 : 3 / T.a ≤ 3 := div_le_self (by norm_num) fl.a1
    have h2 : Q.coupling = x := rfl
    have h3 : Q.a = T.a := rfl
    rw [h2, h3]
    linarith [fl.y3]
  obtain ⟨t1, t2, t3⟩ := tail Q rfl hQ3
  set c1 : ℝ := 5 * M * Dd ^ 3 * Real.exp R with hc1
  have hc1p : 0 ≤ c1 := by positivity
  have hCs : decayConstant Mt Mz Dm (rateParameters T) ≤ T.Cs := fl.Cs
  have hfl : decayConstant Mt Mz Dm (rateParameters T) = c1 +
      8 * M * (8 * Mz T.L * (T.Ct + 3) ^ 2) ^ 2 *
        (8 * Mz T.L * (T.Ct + 3) ^ 2 * (T.Ct * Real.exp (13 * (T.chainParams.δ₂ / 4)))) +
      2 * (M + c1) * Real.exp (16 * R) := rfl
  have hc3p : 0 ≤ 8 * M * (8 * Mz T.L * (T.Ct + 3) ^ 2) ^ 2 *
      (8 * Mz T.L * (T.Ct + 3) ^ 2 * (T.Ct * Real.exp (13 * (T.chainParams.δ₂ / 4)))) := by
    have := fl.Ct0
    have h2 : 0 ≤ Mz T.L := by linarith
    positivity
  have hc4p : 0 ≤ 2 * (M + c1) * Real.exp (16 * R) := by positivity
  have torus : ∀ {G : BlockFrame}, IsCubicTopTorus T.L t T.n₀ G →
      G.blockSide = T.L ∧ Odd G.blockSide ∧ ∀ l, 2 ≤ G.extent l := by
    intro G h
    obtain ⟨h1, -, n, h3, h4⟩ := h
    refine ⟨h1, h1 ▸ fl.odd, fun l => ?_⟩
    rw [h3 l]
    exact fl.n2.trans h4
  have hρ0 : 0 ≤ T.ballRadius := by
    have := fl.σ0
    unfold StepParameters.ballRadius
    positivity
  have one : ∀ {G : BlockFrame} (Y : G.Cell) (V : G.GaugeField G.top), IsCubicTopTorus T.L t T.n₀ G →
      IsSmallCurvature (5 / 4 * T.σ) V →
      ContDiffThreeAlongBonds (Q.scoreRemainderAt (cellBond Y i back) 0) V ∧
      ‖Q.scoreRemainderAt (cellBond Y i back) 0 V‖ ≤ M ∧
      ∀ (k : ℕ) (c : Fin k → G.Site G.top × Fin 4) (X : Fin k → imaginaryQuaternions), 1 ≤ k → k ≤ 3 →
        AreUnitVectors X →
        |bondDeriv (Q.scoreRemainderAt (cellBond Y i back) 0) V c X| ≤ c1 * Real.exp (-(R * bondSpan Y c)) := by
    intro G Y V hG hV
    obtain ⟨hGL, hodd, hs2⟩ := torus hG
    have p0 : ∀ l, 0 < G.extent l := fun l => by have := hs2 l; omega
    have sV := ((near t x hx).single G V 1 hG hV zero_le_one le_rfl).2
    have hker := kern x t G V 1 0 hx hG hV zero_le_one le_rfl (fun b => by simpa using hρ0)
    rw [cellBond_eq]
    refine ⟨fun k c X => ?_, ?_, fun k c X g1 g3 hX => ?_⟩
    · rw [scoreRemainderAt_eq_comp hGL]
      exact (t3.smooth _ (sizeSqAlong_zero_mem hGL hodd i _ sV fl.Cσ c X)).comp (0 : Fin k → ℝ)
        (contDiffAt_sizeSqAlong hcov hodd p0 i _ sV c X)
    · obtain ⟨b1, b2⟩ := contourAverage_norm_bounds hodd sV fl.Cσ (Y + siteOfCoords G.top (backOffset i back), i)
      have h0 := t1.bound _ ⟨b1, b2⟩ 0 (by norm_num)
      rw [norm_iteratedFDeriv_zero] at h0
      exact h0
    · have d := scoreRemainderAt_bondDeriv_le hC hcov hGL hodd p0 Q i (Y + siteOfCoords G.top (backOffset i back))
        sV fl.Cσ hker t2 fl.κ0.le hD1 hD c X hX g1 g3
      refine d.trans ?_
      have hdist : cellSupDist Y (Y + siteOfCoords G.top (backOffset i back)) ≤ 1 :=
        cellSupDist_add_le Y _ p0 (M := 1) (by exact_mod_cast backOffset_abs_le i back)
      have hsp := bondSpan_le Y _ hdist c
      have hsp' : (bondSpan Y c : ℝ) ≤ (sublistDiameter (Y + siteOfCoords G.top (backOffset i back)) c id : ℝ) + 1 := by
        exact_mod_cast hsp
      have hexp : Real.exp (-(R * (sublistDiameter (Y + siteOfCoords G.top (backOffset i back)) c id : ℝ))) ≤
          Real.exp R * Real.exp (-(R * bondSpan Y c)) := by
        rw [← Real.exp_add]
        refine Real.exp_le_exp.mpr ?_
        nlinarith
      calc 5 * M * Dd ^ 3 * Real.exp (-(R * (sublistDiameter (Y + siteOfCoords G.top (backOffset i back)) c id : ℝ)))
          ≤ 5 * M * Dd ^ 3 * (Real.exp R * Real.exp (-(R * bondSpan Y c))) := by gcongr
        _ = c1 * Real.exp (-(R * bondSpan Y c)) := by rw [hc1]; ring
  refine ⟨fun F Y V k c X hT hV h1 h3 hX => ?_, fun F F' Y Y' V V' q k b X hT hT' hV hV' agree hk hb hX => ?_⟩
  · obtain ⟨o1, -, o3⟩ := one Y V hT hV
    refine ⟨o1, (o3 k c X h1 h3 hX).trans ?_⟩
    have : c1 ≤ T.Cs := by linarith
    exact mul_le_mul_of_nonneg_right this (Real.exp_pos _).le
  · obtain ⟨-, o2, o3⟩ := one Y V hT hV
    obtain ⟨-, o2', o3'⟩ := one Y' V' hT' hV'
    obtain ⟨hFL, hodd, hs2⟩ := torus hT
    obtain ⟨hFL', hodd', hs2'⟩ := torus hT'
    have exp1 : ∀ {G : BlockFrame} (Y : G.Cell) {k : ℕ} (c : Fin k → G.Site G.top × Fin 4),
        Real.exp (-(R * bondSpan Y c)) ≤ 1 := by
      intro G Y k c
      rw [Real.exp_le_one_iff]
      have : 0 ≤ R * (bondSpan Y c : ℝ) := by positivity
      linarith
    have sizeD : ∀ {G : BlockFrame} (Y : G.Cell) (V : G.GaugeField G.top) (c : Fin k → G.Site G.top × Fin 4)
        (X : Fin k → imaginaryQuaternions),
        ‖Q.scoreRemainderAt (cellBond Y i back) 0 V‖ ≤ M →
        (∀ (k : ℕ) (c : Fin k → G.Site G.top × Fin 4) (X : Fin k → imaginaryQuaternions), 1 ≤ k → k ≤ 3 →
          AreUnitVectors X →
          |bondDeriv (Q.scoreRemainderAt (cellBond Y i back) 0) V c X| ≤ c1 * Real.exp (-(R * bondSpan Y c))) →
        AreUnitVectors X → |bondDeriv (Q.scoreRemainderAt (cellBond Y i back) 0) V c X| ≤ M + c1 := by
      intro G Y V c X g2 g3 gX
      rcases Nat.eq_zero_or_pos k with rfl | hpos
      · rw [bondDeriv_zero, ← Real.norm_eq_abs]
        linarith
      · have h1 := g3 k c X hpos (by omega) gX
        have h2 : c1 * Real.exp (-(R * bondSpan Y c)) ≤ c1 * 1 :=
          mul_le_mul_of_nonneg_left (exp1 Y c) hc1p
        linarith
    by_cases hq : q < 16
    · have a1 := sizeD Y V (bondsAt Y b) X o2 o3 hX
      have a2 := sizeD Y' V' (bondsAt Y' b) X o2' o3' hX
      have hqe : Real.exp (-(16 * R)) ≤ Real.exp (-(R * q)) := by
        refine Real.exp_le_exp.mpr ?_
        have : (q : ℝ) ≤ 16 := by exact_mod_cast hq.le
        nlinarith
      have h5 : 2 * (M + c1) ≤ T.Cs * Real.exp (-(16 * R)) := by
        have h6 : 2 * (M + c1) * Real.exp (16 * R) ≤ T.Cs := by linarith
        have h7 := mul_le_mul_of_nonneg_right h6 (Real.exp_pos (-(16 * R))).le
        rwa [mul_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero, mul_one] at h7
      have hCs0 : 0 ≤ T.Cs := by linarith
      have h8 : T.Cs * Real.exp (-(16 * R)) ≤ T.Cs * Real.exp (-(R * q)) :=
        mul_le_mul_of_nonneg_left hqe hCs0
      refine (abs_sub _ _).trans ?_
      linarith
    · have hq16 : 16 ≤ q := by omega
      have hs : ∀ l, 2 * q + 2 < F.extent l := fun l => by
        rcases agree.1 l with h | h
        · have := hs2 l
          omega
        · exact h
      have hs' : ∀ l, 2 * q + 2 < F'.extent l := fun l => by
        rcases agree.2.1 l with h | h
        · have := hs2' l
          omega
        · exact h
      have sV := ((near t x hx).single F V 1 hT hV zero_le_one le_rfl).2
      have sV' := ((near t x hx).single F' V' 1 hT' hV' zero_le_one le_rfl).2
      have loc := (near t x hx).pair F F' V V' Y Y' q 1 hT hT' hV hV' agree zero_le_one le_rfl
      have hδ0 := fl.δ0.le
      have close : ∀ {k' : ℕ} (bb : Fin k' → Offset × Fin 4) (X' : Fin k' → imaginaryQuaternions)
          (ι : Fin 2 → Fin k'), k' ≤ 3 → (∀ l, BondWithinRadius q (bb l)) → AreUnitVectors X' → SecondOrderClose
            (fun τ : Fin k' → ℝ => Q.scoreRemainderAt (cellBond Y i back) 0
              (leftTranslate (ColdStepAtMirrorFrames.bondSpread (bondsAt Y bb) X' τ) V))
            (fun τ : Fin k' → ℝ => Q.scoreRemainderAt (cellBond Y' i back) 0
              (leftTranslate (ColdStepAtMirrorFrames.bondSpread (bondsAt Y' bb) X' τ) V'))
            (Pi.single (ι 0) 1) (Pi.single (ι 1) 1)
            (8 * M * (8 * Mz T.L * (T.Ct + 3) ^ 2) ^ 2 * (8 * Mz T.L * (T.Ct + 3) ^ 2 *
              (T.Ct * Real.exp (-(T.chainParams.δ₂ / 4 * ((q : ℝ) - 13))))))
            (8 * M * (8 * Mz T.L * (T.Ct + 3) ^ 2) ^ 2) := fun bb X' ι g3 gb gX =>
        secondOrderClose_of_agree hC hcov fl.odd hFL hFL' Q hδ0 fl.Ct0 fl.σ0.le fl.σ1 fl.Cσ hq16 hs hs' sV sV'
          loc agree i back g3 bb gb X' gX ι t3 hz1 (hz i)
      have final : 8 * M * (8 * Mz T.L * (T.Ct + 3) ^ 2) ^ 2 * (8 * Mz T.L * (T.Ct + 3) ^ 2 *
          (T.Ct * Real.exp (-(T.chainParams.δ₂ / 4 * ((q : ℝ) - 13))))) ≤ T.Cs * Real.exp (-(2 ^ 8 * T.κ * q)) := by
        have e1 : Real.exp (-(T.chainParams.δ₂ / 4 * ((q : ℝ) - 13))) ≤
            Real.exp (13 * (T.chainParams.δ₂ / 4)) * Real.exp (-(R * q)) := by
          rw [← Real.exp_add]
          refine Real.exp_le_exp.mpr ?_
          have h1 : R ≤ T.chainParams.δ₂ / 4 := by
            have := fl.κδ
            rw [hR]
            linarith
          have h2 : (0 : ℝ) ≤ q := by positivity
          nlinarith
        have hCt := fl.Ct0
        have e2 : 8 * M * (8 * Mz T.L * (T.Ct + 3) ^ 2) ^ 2 * (8 * Mz T.L * (T.Ct + 3) ^ 2 *
            (T.Ct * Real.exp (-(T.chainParams.δ₂ / 4 * ((q : ℝ) - 13))))) ≤
            8 * M * (8 * Mz T.L * (T.Ct + 3) ^ 2) ^ 2 * (8 * Mz T.L * (T.Ct + 3) ^ 2 *
            (T.Ct * (Real.exp (13 * (T.chainParams.δ₂ / 4)) * Real.exp (-(R * q))))) := by gcongr
        refine e2.trans ?_
        have e3 : 8 * M * (8 * Mz T.L * (T.Ct + 3) ^ 2) ^ 2 * (8 * Mz T.L * (T.Ct + 3) ^ 2 *
            (T.Ct * (Real.exp (13 * (T.chainParams.δ₂ / 4)) * Real.exp (-(R * q))))) =
            (8 * M * (8 * Mz T.L * (T.Ct + 3) ^ 2) ^ 2 * (8 * Mz T.L * (T.Ct + 3) ^ 2 *
            (T.Ct * Real.exp (13 * (T.chainParams.δ₂ / 4))))) * Real.exp (-(R * q)) := by ring
        rw [e3]
        refine mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le
        linarith
      rw [← Real.norm_eq_abs]
      refine le_trans ?_ final
      rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2) with rfl | rfl | rfl
      · rw [bondDeriv_zero, bondDeriv_zero]
        have hbox : BondWithinRadius q ((0 : Offset), (0 : Fin 4)) := by
          have hq1 : (1 : ℤ) ≤ q := by exact_mod_cast (by omega : 1 ≤ q)
          refine ⟨fun l => by simp, fun l => ?_⟩
          by_cases hl : l = 0
          · subst hl
            simpa using hq1
          · simp [Pi.single_eq_of_ne hl]
        have hcl := close (fun _ : Fin 1 => ((0 : Offset), (0 : Fin 4))) (fun _ => unitImaginary) (fun _ => 0)
          (by norm_num) (fun _ => hbox) (fun _ => norm_unitImaginary)
        have h0 := hcl.v0
        simp only [leftTranslate_bondSpread_zero] at h0
        exact h0
      · have hcl := close b X (fun _ => 0) (by norm_num) hb hX
        have h0 := hcl.d1u
        have em : (fun l : Fin 1 => (Pi.single l 1 : Fin 1 → ℝ)) = ![Pi.single 0 1] := by
          funext l
          fin_cases l
          rfl
        unfold bondDeriv
        rw [em]
        exact h0
      · have hcl := close b X ![0, 1] (by norm_num) hb hX
        have h0 := hcl.d2
        have em : (fun l : Fin 2 => (Pi.single l 1 : Fin 2 → ℝ)) = ![Pi.single 0 1, Pi.single 1 1] := by
          funext l
          fin_cases l <;> rfl
        unfold bondDeriv
        rw [em]
        exact h0
end ScoreRemainderAux
open ScoreRemainderAux in
theorem scoreRemainderDecay_holds (hK : interpolationKernelBoundsStatement) (hN : interpolatedFramesControlled)
    (hT : ScoreRemainderExpansion) (hC : ThirdOrderChainRule) (hcov : BlocksCoverLowerLevel) :
    ScoreRemainderDecay := by
  obtain ⟨K, D, -, hDp, hk⟩ := hK
  have tb : ∀ a : ℝ, ∃ M : ℝ, 1 ≤ a → 1 ≤ M ∧ ∀ Q : ColdHalfLaw, Q.a = a → 3 / a ≤ Q.coupling →
      DerivBoundedOn Q.scoreRemainder (Set.Icc (1 / 2) 1) M ∧
      DerivBoundedOn (Q.scoreRemainder ∘ Real.exp) (Set.Icc (Real.log (1 / 2)) 0) M ∧
      DerivBoundedOn (Q.scoreRemainder ∘ Real.sqrt) (Set.Icc (1 / 4) 1) M := fun a => by
    by_cases ha : 1 ≤ a
    · obtain ⟨M, h⟩ := scoreRemainder_bounded hC hT ha
      exact ⟨M, fun _ => h⟩
    · exact ⟨0, fun h => absurd h ha⟩
  choose Mt hMt using tb
  choose Mz hz1 hz using boxSizeSq_bounded
  let Dm : _root_.YangMills.Construction.ColdStepAtMirrorFrames.StepParameters → ℝ := fun T' => 1 + D T' 0 1 + D T' 0 2 + D T' 0 3
  refine ((hk.and hN).and (eventually_parameterFloors (decayConstant Mt Mz Dm))).mono fun T h => ?_
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  have p := hDp (rateParameters T) 0
  have p1 := p 1
  have p2 := p 2
  have p3 := p 3
  refine scoreRemainderDecayAt_of_bounds hC hcov (hMt T.a h3.a1).1 (hMt T.a h3.a1).2 (hz1 T.L) (hz T.L) ?_ ?_ h3
    h1 h2
  · simp only [Dm]
    linarith
  · intro j g1 g3
    simp only [Dm]
    interval_cases j <;> linarith
end ResponseInTheExpansion
end YangMills.Construction
end
