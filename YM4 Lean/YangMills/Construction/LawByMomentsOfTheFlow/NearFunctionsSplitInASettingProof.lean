import YangMills.Construction.LawByMomentsOfTheFlow.NearFunctionsSplitInASetting
import YangMills.Construction.LawInAState.CellsOfAPair
import YangMills.Construction.ResponseInTheExpansion.FarVariablesSplitInASettingProof
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction
open StepSettings TorusFields TorusLumps ColdStepAtMirrorFrames ClusterExpansionOfAStep.BallLaws SettingShifts StateLaws BlockOffsets
  TorusBalls WeightedResponses
namespace MomentLaw
namespace NearlyLocalFactorization
set_option linter.unusedSectionVars false
private theorem abs_prod_sub_prod_le {α : Type} [DecidableEq α] {a b P : α → ℝ} {e : ℝ} (he : 0 ≤ e) (J : Finset α)
    (hP : ∀ i ∈ J, 0 ≤ P i)
    (ha : ∀ i ∈ J, |a i| ≤ P i) (hb : ∀ i ∈ J, |b i| ≤ P i) (hab : ∀ i ∈ J, |a i - b i| ≤ e * P i) :
    |∏ i ∈ J, a i - ∏ i ∈ J, b i| ≤ J.card * e * ∏ i ∈ J, P i := by apply _root_.YangMills.Construction.ResponseInTheExpansion.Decorrelation.abs_prod_sub_prod_le <;> assumption
section Laws
variable {ι : Type} [Fintype ι] [DecidableEq ι] {ρ : ℝ} {p : ℝ → ℝ}
private theorem ballExpectation_congr {Ψ f g : BondField ι → ℝ}
    (h : ∀ η : BondField ι, (∀ b, ‖η b‖ < ρ) → f η = g η) :
    ballExpectation (cutoffFactor ρ p) Ψ f = ballExpectation (cutoffFactor ρ p) Ψ g := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.ConvexLaw.ballExpectation_congr <;> assumption
private theorem abs_ballExpectation_sub_le {Ψ f g : BondField ι → ℝ} {Q Q' E : ℝ} (hΨ : Continuous Ψ) (hρ : 0 < ρ)
    (hp : IsCutoff ρ p) (hf : Measurable f) (hg : Measurable g)
    (hfQ : ∀ η : BondField ι, (∀ b, ‖η b‖ < ρ) → |f η| ≤ Q)
    (hgQ : ∀ η : BondField ι, (∀ b, ‖η b‖ < ρ) → |g η| ≤ Q')
    (hE : ∀ η : BondField ι, (∀ b, ‖η b‖ < ρ) → |f η - g η| ≤ E) :
    |ballExpectation (cutoffFactor ρ p) Ψ f - ballExpectation (cutoffFactor ρ p) Ψ g| ≤ E := by apply _root_.YangMills.Construction.ResponseInTheExpansion.FarSupports.abs_ballExpectation_sub_le <;> assumption
private theorem abs_ballExpectation_le {Ψ f : BondField ι → ℝ} {Q : ℝ} (hΨ : Continuous Ψ) (hρ : 0 < ρ)
    (hp : IsCutoff ρ p) (hf : Measurable f) (hfQ : ∀ η : BondField ι, (∀ b, ‖η b‖ < ρ) → |f η| ≤ Q) :
    |ballExpectation (cutoffFactor ρ p) Ψ f| ≤ Q := by apply _root_.YangMills.Construction.ResponseInTheExpansion.FarSupports.abs_ballExpectation_le <;> assumption
end Laws
section Setting
variable {R : StepSetup} {n : ℕ} [NeZero n]
private def bondsNear (s : ChartSetting R n) (k : ℕ) (S : Finset (TorusSite n)) : Finset s.free :=
  open Classical in Finset.univ.filter fun b => ∃ Y ∈ S, _root_.YangMills.Construction.TorusFields.supDist (bondBlock (R := R) b.1) Y ≤ k
private theorem mem_bondsNear {s : ChartSetting R n} {k : ℕ} {S : Finset (TorusSite n)} {b : s.free} :
    b ∈ bondsNear s k S ↔ ∃ Y ∈ S, _root_.YangMills.Construction.TorusFields.supDist (bondBlock (R := R) b.1) Y ≤ k := by
  classical
  simp [bondsNear]
private theorem coordsAgreeNear_restrict (hodd : Odd R.params.side) (s : ChartSetting R n) {k : ℕ}
    {S : Finset (TorusSite n)} {Y : TorusSite n} (hY : Y ∈ S) (η : FreeCoords s.free) :
    CoordsAgreeNear s s Y Y k η (ClusterExpansionOfAStep.restrictToSet (bondsNear s k S) η) := by
  rintro ⟨h, o, i⟩ hq
  simp only [ChartSetting.coordsByIndex]
  by_cases hf : nearBond R.params.side Y (h, o, i) ∈ s.free
  · rw [dif_pos hf, dif_pos hf]
    have : (⟨_, hf⟩ : s.free) ∈ bondsNear s k S := by
      refine mem_bondsNear.mpr ⟨Y, hY, ?_⟩
      have e : bondBlock (R := R) (nearBond R.params.side Y (h, o, i)) = Y + siteOfInt h :=
        parentBlock_fineSite hodd Y h o hq.2
      rw [e, _root_.YangMills.Construction.TorusFields.supDist_comm]
      exact _root_.YangMills.Construction.TorusFields.supDist_add_siteOfInt_le Y h k fun l => by
        have h1 : |h l| ≤ (k : ℤ) := hq.1 l
        rw [Int.abs_eq_natAbs] at h1
        omega
    simp [ClusterExpansionOfAStep.restrictToSet, this]
  · rw [dif_neg hf, dif_neg hf]
private def stateValue (s : ChartSetting R n) (Q : ResponseInTheExpansion.StateFunction R (n * R.params.side))
    (η : FreeCoords s.free) : ℝ :=
  Q (s.field η) s.support s.labelling
private theorem measurable_stateValue (s : ChartSetting R n) {Q : ResponseInTheExpansion.StateFunction R (n * R.params.side)}
    {y : TorusSite (n * R.params.side)} {K ρ : ℝ} (hQ : IsNearlyLocalStateFunction R Q y K ρ) :
    Measurable (stateValue s Q) :=
  (hQ.measurable s.support).comp ((ClusterExpansionOfAStep.ChartSetting.measurable_field s).prodMk measurable_const)
private def onBalls (s : ChartSetting R n) (g : FreeCoords s.free → ℝ) (η : FreeCoords s.free) : ℝ :=
  open Classical in if s.InBalls η then g η else 0
private theorem measurable_onBalls (s : ChartSetting R n) {g : FreeCoords s.free → ℝ} (hg : Measurable g) :
    Measurable (onBalls s g) := by apply _root_.YangMills.Construction.ResponseInTheExpansion.FarSupports.measurable_indicatorBalls <;> assumption
private theorem inBalls_of_forall_lt (s : ChartSetting R n) {η : FreeCoords s.free} (h : ∀ b, ‖η b‖ < R.ballRadius) :
    s.InBalls η := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.LocalMeans.inBalls_of_norm_lt <;> assumption
private theorem weightedMean_eq_ballExpectation {s : ChartSetting R n} {Ψ : BondField s.free → ℝ}
    (e : ∀ η, s.InBalls η → Ψ =ᶠ[nhds η] s.potential) (G : FreeCoords s.free → ℝ) :
    weightedMean (chartDensity s) G = ballExpectation (cutoffFactor R.ballRadius R.barrierFn) Ψ G := by apply _root_.YangMills.Construction.ResponseInTheExpansion.FarSupports.weightedMean_chartDensity_eq <;> assumption
private theorem sum_free_le_blocks (hodd : Odd R.params.side) (s : ChartSetting R n) {g : TorusSite n → ℝ}
    (hg0 : ∀ Z, 0 ≤ g Z) :
    ∑ b : s.free, g (bondBlock (R := R) b.1) ≤ 4 * (R.params.side : ℝ) ^ 4 * ∑ Z, g Z := by apply _root_.YangMills.Construction.ResponseInTheExpansion.FarSupports.sum_free_bondBlock_le <;> assumption
private theorem card_bondsNear_le (hodd : Odd R.params.side) (s : ChartSetting R n) (k : ℕ) (S : Finset (TorusSite n)) :
    ((bondsNear s k S).card : ℝ) ≤ (S.card : ℝ) * ((2 * k + 1 : ℕ) : ℝ) ^ 4 * (4 * (R.params.side : ℝ) ^ 4) := by
  classical
  have h1 : bondsNear s k S ⊆ S.biUnion fun Y => Finset.univ.filter fun b : s.free =>
      _root_.YangMills.Construction.TorusFields.supDist (bondBlock (R := R) b.1) Y ≤ k := by
    intro b hb
    obtain ⟨Y, hY, h⟩ := mem_bondsNear.mp hb
    exact Finset.mem_biUnion.mpr ⟨Y, hY, by simp [h]⟩
  have h2 : ∀ Y : TorusSite n,
      (((Finset.univ.filter fun b : s.free => _root_.YangMills.Construction.TorusFields.supDist (bondBlock (R := R) b.1) Y ≤ k).card : ℕ) : ℝ) ≤
      ((2 * k + 1 : ℕ) : ℝ) ^ 4 * (4 * (R.params.side : ℝ) ^ 4) := by
    intro Y
    have e := sum_free_le_blocks hodd s (g := fun Z => if _root_.YangMills.Construction.TorusFields.supDist Z Y ≤ k then (1 : ℝ) else 0)
      (fun Z => by positivity)
    have e1 : ∑ b : s.free, (if _root_.YangMills.Construction.TorusFields.supDist (bondBlock (R := R) b.1) Y ≤ k then (1 : ℝ) else 0) =
        ((Finset.univ.filter fun b : s.free => _root_.YangMills.Construction.TorusFields.supDist (bondBlock (R := R) b.1) Y ≤ k).card : ℝ) := by
      simp
    have e2 : ∑ Z : TorusSite n, (if _root_.YangMills.Construction.TorusFields.supDist Z Y ≤ k then (1 : ℝ) else 0) ≤ ((2 * k + 1 : ℕ) : ℝ) ^ 4 := by
      have hc := card_thickening_singleton_le k Y
      have : ∑ Z : TorusSite n, (if _root_.YangMills.Construction.TorusFields.supDist Z Y ≤ k then (1 : ℝ) else 0) =
          ((thickening k ({Y} : Finset (TorusSite n))).card : ℝ) := by
        have hw : thickening k ({Y} : Finset (TorusSite n)) = Finset.univ.filter fun Z => _root_.YangMills.Construction.TorusFields.supDist Z Y ≤ k := by
          ext Z
          simp [thickening]
        rw [hw]
        simp
      rw [this]
      exact_mod_cast hc
    rw [e1] at e
    calc _ ≤ 4 * (R.params.side : ℝ) ^ 4 * ∑ Z : TorusSite n, (if _root_.YangMills.Construction.TorusFields.supDist Z Y ≤ k then (1 : ℝ) else 0) := e
      _ ≤ 4 * (R.params.side : ℝ) ^ 4 * ((2 * k + 1 : ℕ) : ℝ) ^ 4 := by gcongr
      _ = _ := by ring
  calc ((bondsNear s k S).card : ℝ) ≤ ((S.biUnion fun Y => Finset.univ.filter fun b : s.free =>
        _root_.YangMills.Construction.TorusFields.supDist (bondBlock (R := R) b.1) Y ≤ k).card : ℝ) := by exact_mod_cast Finset.card_le_card h1
    _ ≤ ∑ Y ∈ S, (((Finset.univ.filter fun b : s.free => _root_.YangMills.Construction.TorusFields.supDist (bondBlock (R := R) b.1) Y ≤ k).card : ℕ) : ℝ) := by
        exact_mod_cast Finset.card_biUnion_le
    _ ≤ ∑ _Y ∈ S, ((2 * k + 1 : ℕ) : ℝ) ^ 4 * (4 * (R.params.side : ℝ) ^ 4) := Finset.sum_le_sum fun Y _ => h2 Y
    _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]; ring
end Setting
section Closing
private theorem abs_le_mul_norm_of_unit {T : BondVector → ℝ} {B : ℝ} (hB : 0 ≤ B) (hl : ∀ (t : ℝ) e, T (t • e) = t * T e)
    (hu : ∀ X : BondVector, ‖X‖ = 1 → |T X| ≤ B) (e : BondVector) : |T e| ≤ B * ‖e‖ := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.LocalMeans.abs_le_of_unit_bound <;> assumption
private theorem bondVariation_smul {ι : Type} [DecidableEq ι] (b : ι) (t : ℝ) (e : BondVector) :
    (bondVariation b (t • e) : BondField ι) = t • bondVariation b e := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.LocalMeans.bondVariation_smul <;> assumption
private theorem deriv_line_eq_fderiv {n : ℕ} {free : Finset (TorusBond n)} {u Ψ : FreeCoords free → ℝ}
    {η : FreeCoords free} (h : Ψ =ᶠ[nhds η] u) (hd : DifferentiableAt ℝ Ψ η) (b : free) (X : EuclideanSpace ℝ (Fin 3)) :
    deriv (fun τ : ℝ => u (Function.update η b (η b + τ • X))) 0 = fderiv ℝ Ψ η (bondVariation b X) := by apply _root_.YangMills.Construction.ResponseInTheExpansion.FarSupports.deriv_update_eq_fderiv <;> assumption
private theorem exp_bound_far {κ Bv M g d : ℝ} (hκ : 0 ≤ κ) (hM : 0 ≤ M) (hd : g ≤ d) (hB : Bv ≤ M) :
    Bv * Real.exp (-(κ * d)) ≤ M * Real.exp (-(κ / 2 * g)) * Real.exp (-(κ / 2 * d)) := by apply _root_.YangMills.Construction.ResponseInTheExpansion.FarSupports.mul_exp_le_of_far <;> assumption
private theorem exp_bound_near {κ Bv M g d : ℝ} (hκ : 0 ≤ κ) (hM : 0 ≤ M) (hd : d ≤ g)
    (hB : Bv ≤ M * Real.exp (-(κ * (g - d)))) :
    Bv * Real.exp (-(κ * d)) ≤ M * Real.exp (-(κ / 2 * g)) * Real.exp (-(κ / 2 * d)) := by apply _root_.YangMills.Construction.ResponseInTheExpansion.FarSupports.mul_exp_le_of_near <;> assumption
end Closing
section Pairs
variable {ι α : Type} [Fintype ι] [DecidableEq ι] [DecidableEq α]
private def splitGradBound (ρ Cc : ℝ) (I : Finset α) (Lam : α → Finset ι) (K : ι → ι → ℝ) (b : ι) : ℝ :=
  open Classical in
  ∑ i ∈ I, (if b ∈ Lam i then ρ * ∑ b' ∈ Finset.univ \ Lam i, K b b' else 0) + if ∀ i ∈ I, b ∉ Lam i then Cc else 0
private theorem splitGradBound_of_mem {ρ Cc : ℝ} {I : Finset α} {Lam : α → Finset ι} {K : ι → ι → ℝ} {b : ι}
    (hdis : ∀ i ∈ I, ∀ j ∈ I, i ≠ j → Disjoint (Lam i) (Lam j)) {i : α} (hi : i ∈ I) (hb : b ∈ Lam i) :
    splitGradBound ρ Cc I Lam K b = ρ * ∑ b' ∈ Finset.univ \ Lam i, K b b' := by
  classical
  unfold splitGradBound
  rw [if_neg (fun h => h i hi hb), add_zero, Finset.sum_eq_single i]
  · rw [if_pos hb]
  · intro j hj hji
    rw [if_neg]
    intro h
    exact Finset.disjoint_left.mp (hdis j hj i hi hji) h hb
  · exact fun hn => absurd hi hn
private theorem splitGradBound_of_not_mem {ρ Cc : ℝ} {I : Finset α} {Lam : α → Finset ι} {K : ι → ι → ℝ} {b : ι}
    (hb : ∀ i ∈ I, b ∉ Lam i) : splitGradBound ρ Cc I Lam K b = Cc := by
  classical
  unfold splitGradBound
  rw [if_pos hb, Finset.sum_eq_zero, zero_add]
  intro i hi
  rw [if_neg (hb i hi)]
private theorem splitGradBound_mul_exp_le {κ ρ Am Gx Cc g : ℝ} {d : ι → ι → ℝ} {K : ι → ι → ℝ} {I : Finset α}
    {Lam Xs : α → Finset ι}
    (hκ : 0 ≤ κ) (hρ : 0 ≤ ρ) (hAm : 0 ≤ Am) (hG : 0 ≤ Gx) (hK : ∀ b b', 0 ≤ K b b') (hd0 : ∀ b b', 0 ≤ d b b')
    (hdis : ∀ i ∈ I, ∀ j ∈ I, i ≠ j → Disjoint (Lam i) (Lam j))
    (hrows : ∀ b, ∑ b' ∈ Finset.univ.erase b, K b b' * Real.exp (κ * d b b') ≤ Am)
    (hG1 : ρ * Am ≤ Gx) (hG2 : Cc ≤ Gx)
    (hoff : ∀ j ∈ I, ∀ b ∈ Xs j, ∀ b', b' ∉ Lam j → g ≤ d b b')
    (hother : ∀ j ∈ I, ∀ i ∈ I, i ≠ j → ∀ b ∈ Xs j, ∀ b' ∈ Lam i, g ≤ d b b')
    (hin : ∀ j ∈ I, ∀ b ∈ Xs j, ∀ b' ∈ Lam j, ∀ b'', b'' ∉ Lam j → g ≤ d b b' + d b' b'')
    {j : α} (hj : j ∈ I) {b : ι} (hb : b ∈ Xs j) (b' : ι) :
    splitGradBound ρ Cc I Lam K b' * Real.exp (-(κ * d b b')) ≤
      Gx * Real.exp (-(κ / 2 * g)) * Real.exp (-(κ / 2 * d b b')) := by
  classical
  by_cases hex : ∃ i ∈ I, b' ∈ Lam i
  · obtain ⟨i, hi, hbi⟩ := hex
    rw [splitGradBound_of_mem hdis hi hbi]
    have hsub : Finset.univ \ Lam i ⊆ Finset.univ.erase b' := by
      intro x hx
      refine Finset.mem_erase.mpr ⟨fun e => ?_, Finset.mem_univ x⟩
      exact (Finset.mem_sdiff.mp hx).2 (e ▸ hbi)
    have hT : ∑ x ∈ Finset.univ \ Lam i, K b' x ≤ Am := by
      refine le_trans ?_ (hrows b')
      refine le_trans (Finset.sum_le_sum fun x _ => ?_)
        (Finset.sum_le_sum_of_subset_of_nonneg hsub fun x _ _ => mul_nonneg (hK _ _) (Real.exp_pos _).le)
      have h1 : 1 ≤ Real.exp (κ * d b' x) := Real.one_le_exp (mul_nonneg hκ (hd0 _ _))
      nlinarith [hK b' x]
    have hM : ρ * ∑ x ∈ Finset.univ \ Lam i, K b' x ≤ Gx :=
      (mul_le_mul_of_nonneg_left hT hρ).trans hG1
    by_cases hij : i = j
    · subst hij
      by_cases hfar : g ≤ d b b'
      · exact exp_bound_far hκ hG hfar hM
      · have hnear := not_le.mp hfar
        refine exp_bound_near hκ hG hnear.le ?_
        have hT2 : ∑ x ∈ Finset.univ \ Lam i, K b' x ≤ Am * Real.exp (-(κ * (g - d b b'))) := by
          have a1 : ∀ x ∈ Finset.univ \ Lam i, K b' x ≤
              (K b' x * Real.exp (κ * d b' x)) * Real.exp (-(κ * (g - d b b'))) := by
            intro x hx
            have hg := hin i hi b hb b' hbi x (Finset.mem_sdiff.mp hx).2
            have : 1 ≤ Real.exp (κ * d b' x) * Real.exp (-(κ * (g - d b b'))) := by
              rw [← Real.exp_add]
              apply Real.one_le_exp
              nlinarith
            calc K b' x = K b' x * 1 := (mul_one _).symm
              _ ≤ K b' x * (Real.exp (κ * d b' x) * Real.exp (-(κ * (g - d b b')))) :=
                  mul_le_mul_of_nonneg_left this (hK _ _)
              _ = _ := by ring
          refine (Finset.sum_le_sum a1).trans ?_
          rw [← Finset.sum_mul]
          apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
          exact (Finset.sum_le_sum_of_subset_of_nonneg hsub fun x _ _ =>
            mul_nonneg (hK _ _) (Real.exp_pos _).le).trans (hrows b')
        calc ρ * ∑ x ∈ Finset.univ \ Lam i, K b' x ≤ ρ * (Am * Real.exp (-(κ * (g - d b b')))) :=
              mul_le_mul_of_nonneg_left hT2 hρ
          _ = (ρ * Am) * Real.exp (-(κ * (g - d b b'))) := by ring
          _ ≤ Gx * Real.exp (-(κ * (g - d b b'))) :=
              mul_le_mul_of_nonneg_right hG1 (Real.exp_pos _).le
    · exact exp_bound_far hκ hG (hother j hj i hi hij b hb b' hbi) hM
  · have hb' : ∀ i ∈ I, b' ∉ Lam i := fun i hi h => hex ⟨i, hi, h⟩
    rw [splitGradBound_of_not_mem hb']
    exact exp_bound_far hκ hG (hoff j hj b hb b' (hb' j hj)) hG2
end Pairs
section Geometry
variable {R : StepSetup} {n : ℕ} [NeZero n] {ι : Type} [DecidableEq ι]
private theorem bondsNear_disjoint (s : ChartSetting R n) {I : Finset ι} {Ap : ι → Finset (TorusSite n)} {k D : ℕ}
    (hkD : 2 * k < D) (hap : ∀ i ∈ I, ∀ j ∈ I, i ≠ j → ∀ Y ∈ Ap i, ∀ Y' ∈ Ap j, D ≤ _root_.YangMills.Construction.TorusFields.supDist Y Y') :
    ∀ i ∈ I, ∀ j ∈ I, i ≠ j → Disjoint (bondsNear s k (Ap i)) (bondsNear s k (Ap j)) := by
  intro i hi j hj hij
  refine Finset.disjoint_left.mpr fun b h1 h2 => ?_
  obtain ⟨Y, hY, a⟩ := mem_bondsNear.mp h1
  obtain ⟨Y', hY', c⟩ := mem_bondsNear.mp h2
  have h3 := hap i hi j hj hij Y hY Y' hY'
  have h4 := _root_.YangMills.Construction.TorusFields.supDist_triangle Y (bondBlock (R := R) b.1) Y'
  rw [_root_.YangMills.Construction.TorusFields.supDist_comm Y (bondBlock (R := R) b.1)] at h4
  omega
private theorem sum_splitGradBound_le (hodd : Odd R.params.side) (s : ChartSetting R n) {κ ρ Am Gx Cc Wb : ℝ}
    {Kk : s.free → s.free → ℝ} {I : Finset ι} {Ap : ι → Finset (TorusSite n)} {e D : ℕ} (hκ : 0 ≤ κ) (hρ : 0 ≤ ρ)
    (hAm : 0 ≤ Am) (hG : 0 ≤ Gx)
    (hK : ∀ b b', 0 ≤ Kk b b')
    (hrows : ∀ b, ∑ b' ∈ Finset.univ.erase b, Kk b b' * Real.exp (κ * s.bondDist b b') ≤ Am)
    (hG1 : ρ * Am ≤ Gx) (hG2 : Cc ≤ Gx) (he8 : 8 * e ≤ D) (he1 : 1 ≤ e)
    (hap : ∀ i ∈ I, ∀ j ∈ I, i ≠ j → ∀ Y ∈ Ap i, ∀ Y' ∈ Ap j, D ≤ _root_.YangMills.Construction.TorusFields.supDist Y Y')
    (hW : ∀ b : s.free, ∑ b', Real.exp (-(κ / 2 * s.bondDist b b')) ≤ Wb) (hW0 : 0 ≤ Wb) :
    ∑ b ∈ I.biUnion fun i => bondsNear s e (Ap i), ∑ b',
        splitGradBound ρ Cc I (fun i => bondsNear s (3 * e) (Ap i)) Kk b' * Real.exp (-(κ * s.bondDist b b')) ≤
      (∑ i ∈ I, ((Ap i).card : ℝ)) * ((2 * e + 1 : ℕ) : ℝ) ^ 4 * (4 * (R.params.side : ℝ) ^ 4) *
        (Gx * Real.exp (-(κ / 2 * ((2 * e + 1 : ℕ) : ℝ))) * Wb) := by
  classical
  set Lam : ι → Finset s.free := fun i => bondsNear s (3 * e) (Ap i) with hLam
  set Xs : ι → Finset s.free := fun i => bondsNear s e (Ap i) with hXs
  set g : ℝ := ((2 * e + 1 : ℕ) : ℝ) with hg
  have hdis : ∀ i ∈ I, ∀ j ∈ I, i ≠ j → Disjoint (Lam i) (Lam j) :=
    bondsNear_disjoint s (by omega) hap
  have hdist : ∀ b b' : s.free,
      s.bondDist b b' = (_root_.YangMills.Construction.TorusFields.supDist (bondBlock (R := R) b.1) (bondBlock (R := R) b'.1) : ℝ) :=
    fun _ _ => rfl
  have hd0 : ∀ b b' : s.free, 0 ≤ s.bondDist b b' := fun b b' => by
    rw [hdist]
    exact Nat.cast_nonneg _
  have hgnat : ∀ {b b' : s.free}, 2 * e + 1 ≤ _root_.YangMills.Construction.TorusFields.supDist (bondBlock (R := R) b.1) (bondBlock (R := R) b'.1) →
      g ≤ s.bondDist b b' := fun {b b'} h => by
    rw [hdist, hg]
    exact_mod_cast h
  have hoff : ∀ j ∈ I, ∀ b ∈ Xs j, ∀ b', b' ∉ Lam j → g ≤ s.bondDist b b' := by
    intro j _ b hb b' hb'
    obtain ⟨Y, hY, h1⟩ := mem_bondsNear.mp hb
    have h2 : ¬ _root_.YangMills.Construction.TorusFields.supDist (bondBlock (R := R) b'.1) Y ≤ 3 * e := fun h => hb' (mem_bondsNear.mpr ⟨Y, hY, h⟩)
    have h3 := _root_.YangMills.Construction.TorusFields.supDist_triangle (bondBlock (R := R) b'.1) (bondBlock (R := R) b.1) Y
    rw [_root_.YangMills.Construction.TorusFields.supDist_comm (bondBlock (R := R) b'.1) (bondBlock (R := R) b.1)] at h3
    exact hgnat (by omega)
  have hother : ∀ j ∈ I, ∀ i ∈ I, i ≠ j → ∀ b ∈ Xs j, ∀ b' ∈ Lam i, g ≤ s.bondDist b b' := by
    intro j hj i hi hij b hb b' hb'
    obtain ⟨Y, hY, h1⟩ := mem_bondsNear.mp hb
    obtain ⟨Y', hY', h2⟩ := mem_bondsNear.mp hb'
    have h3 := hap j hj i hi (Ne.symm hij) Y hY Y' hY'
    have h4 := _root_.YangMills.Construction.TorusFields.supDist_triangle Y (bondBlock (R := R) b.1) Y'
    have h5 := _root_.YangMills.Construction.TorusFields.supDist_triangle (bondBlock (R := R) b.1) (bondBlock (R := R) b'.1) Y'
    rw [_root_.YangMills.Construction.TorusFields.supDist_comm Y (bondBlock (R := R) b.1)] at h4
    exact hgnat (by omega)
  have hin : ∀ j ∈ I, ∀ b ∈ Xs j, ∀ b' ∈ Lam j, ∀ b'', b'' ∉ Lam j →
      g ≤ s.bondDist b b' + s.bondDist b' b'' := by
    intro j _ b hb b' _ b'' hb''
    obtain ⟨Y, hY, h1⟩ := mem_bondsNear.mp hb
    have h2 : ¬ _root_.YangMills.Construction.TorusFields.supDist (bondBlock (R := R) b''.1) Y ≤ 3 * e := fun h => hb'' (mem_bondsNear.mpr ⟨Y, hY, h⟩)
    have h3 := _root_.YangMills.Construction.TorusFields.supDist_triangle (bondBlock (R := R) b''.1) (bondBlock (R := R) b'.1) Y
    have h4 := _root_.YangMills.Construction.TorusFields.supDist_triangle (bondBlock (R := R) b'.1) (bondBlock (R := R) b.1) Y
    rw [_root_.YangMills.Construction.TorusFields.supDist_comm (bondBlock (R := R) b''.1) (bondBlock (R := R) b'.1)] at h3
    rw [_root_.YangMills.Construction.TorusFields.supDist_comm (bondBlock (R := R) b'.1) (bondBlock (R := R) b.1)] at h4
    rw [hdist, hdist, hg]
    have : 2 * e + 1 ≤ _root_.YangMills.Construction.TorusFields.supDist (bondBlock (R := R) b.1) (bondBlock (R := R) b'.1) +
        _root_.YangMills.Construction.TorusFields.supDist (bondBlock (R := R) b'.1) (bondBlock (R := R) b''.1) := by omega
    exact_mod_cast this
  set E₁ := Real.exp (-(κ / 2 * g)) with hE₁
  have hE₁0 : 0 ≤ E₁ := (Real.exp_pos _).le
  have hone : ∀ b ∈ I.biUnion Xs, ∑ b', splitGradBound ρ Cc I Lam Kk b' * Real.exp (-(κ * s.bondDist b b')) ≤
      Gx * E₁ * Wb := by
    intro b hb
    obtain ⟨j, hj, hbj⟩ := Finset.mem_biUnion.mp hb
    have h1 : ∀ b', splitGradBound ρ Cc I Lam Kk b' * Real.exp (-(κ * s.bondDist b b')) ≤
        Gx * E₁ * Real.exp (-(κ / 2 * s.bondDist b b')) := fun b' =>
      splitGradBound_mul_exp_le hκ hρ hAm hG hK hd0 hdis hrows hG1 hG2 hoff hother hin hj hbj b'
    refine (Finset.sum_le_sum fun b' _ => h1 b').trans ?_
    rw [← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left (hW b) (mul_nonneg hG hE₁0)
  have hcard : ((I.biUnion Xs).card : ℝ) ≤
      (∑ i ∈ I, ((Ap i).card : ℝ)) * ((2 * e + 1 : ℕ) : ℝ) ^ 4 * (4 * (R.params.side : ℝ) ^ 4) := by
    calc ((I.biUnion Xs).card : ℝ) ≤ ∑ i ∈ I, ((Xs i).card : ℝ) := by exact_mod_cast Finset.card_biUnion_le
      _ ≤ ∑ i ∈ I, ((Ap i).card : ℝ) * ((2 * e + 1 : ℕ) : ℝ) ^ 4 * (4 * (R.params.side : ℝ) ^ 4) :=
          Finset.sum_le_sum fun i _ => card_bondsNear_le hodd s e (Ap i)
      _ = _ := by rw [← Finset.sum_mul, ← Finset.sum_mul]
  have hGE : 0 ≤ Gx * E₁ * Wb := mul_nonneg (mul_nonneg hG hE₁0) hW0
  calc _ ≤ ∑ _b ∈ I.biUnion Xs, Gx * E₁ * Wb := Finset.sum_le_sum hone
    _ = ((I.biUnion Xs).card : ℝ) * (Gx * E₁ * Wb) := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_right hcard hGE
end Geometry
private theorem numeric_sum_bound {S₁ SA g L4 Gm x Wb rt ee Dr : ℝ} (hS₁ : 0 ≤ S₁) (hS : S₁ ≤ SA) (hg0 : 0 ≤ g)
    (hg : g ≤ 2 * (ee + 1))
    (hg2 : 2 * ee ≤ g) (hee : 0 ≤ ee) (hL4 : 0 ≤ L4) (hGm : 0 ≤ Gm) (hx : 0 ≤ x) (hWb : 0 ≤ Wb) (hrt : 0 ≤ rt)
    (hN : 16 * L4 * Gm * Wb * x ^ 1 * (ee + 1) ^ 4 * Real.exp (-(rt / 2 * ee)) ≤ 1) (hD : Dr ≤ 8 * (ee + 1)) :
    S₁ * g ^ 4 * L4 * (Gm * x * Real.exp (-(rt / 2 * g)) * Wb) ≤
      SA * (Real.exp (rt / 2) * Real.exp (-(rt * Dr / 2 ^ 4))) := by apply _root_.YangMills.Construction.ResponseInTheExpansion.FarSupports.sum_bound_numerics <;> assumption
private theorem numeric_closing_bound {c SA E e16 U Sm Ao ρ xp : ℝ} (hc : 1 ≤ c) (hSA : 1 ≤ SA) (hE0 : 0 ≤ E)
    (hE : E ≤ e16) (hU : 0 ≤ U) (hρ : 0 ≤ ρ) (hAo : 0 ≤ Ao) (hxp : 0 ≤ xp) (he16 : 0 ≤ e16)
    (hSm : Sm ≤ SA * (xp * e16)) :
    c * E * U + 4 * ρ * (1 + Ao) * (2 * (1 + c) * U) * Sm + c * E * U ≤
      (2 + 16 * ρ * (1 + Ao) * xp) * c * SA * e16 * U := by apply _root_.YangMills.Construction.ResponseInTheExpansion.FarSupports.final_bound_numerics <;> assumption
section Main
set_option maxHeartbeats 4000000 in
private theorem factorization_of_components (hconv : ClusterExpansionOfAStep.SettingsUniformlyConvex)
    (htie : ClusterExpansionOfAStep.ChartPotentialConvex) (hsplit : ConvexDecoupling.ProductMeanNearMeanProduct)
    (hnum : PolynomialBelowExponential) (hF : FieldsAgreeOfCoordsAgree) (hPot : PotentialFactorization) :
    nearlyLocalSettingFactorizationStatement := by
  classical
  obtain ⟨r₁, p₁, H1⟩ := hconv
  refine ⟨r₁, p₁, fun T hT hrt => ?_⟩
  obtain ⟨C, y₁, hC, H1⟩ := H1 T hT hrt
  have hrt0 := hT.rt_pos
  have hσ := hT.σ_pos
  have hlam : 0 < T.lam := hT.chain.2.2.1
  have hLone : (1 : ℝ) ≤ T.side := by
    have : 1 ≤ T.side := Nat.pos_of_ne_zero (NeZero.ne T.side)
    exact_mod_cast this
  obtain ⟨A₁, hA₁0, hA₁⟩ := exists_sum_exp_supDist_le (T.rt / 2) (by positivity)
  obtain ⟨ρ, hρd⟩ : ∃ ρ, ρ = T.threshold / 64 := ⟨_, rfl⟩
  have hρ0 : 0 < ρ := by rw [hρd]; positivity
  obtain ⟨Ao, hAod⟩ : ∃ Ao, Ao = 8 * (4 * (2 * (T.side : ℝ)) ^ 4) * C / T.lam + (2 * T.rt)⁻¹ := ⟨_, rfl⟩
  have hAo0 : 0 ≤ Ao := by rw [hAod]; positivity
  obtain ⟨Wb, hWbd⟩ : ∃ Wb, Wb = 4 * (T.side : ℝ) ^ 4 * A₁ := ⟨_, rfl⟩
  have hWb0 : 0 ≤ Wb := by rw [hWbd]; positivity
  obtain ⟨G₀, hG₀d⟩ : ∃ G₀, G₀ = C + T.lam * ρ + 1 := ⟨_, rfl⟩
  have hG₀0 : 0 ≤ G₀ := by rw [hG₀d]; positivity
  obtain ⟨Gm, hGmd⟩ : ∃ Gm, Gm = ρ * Ao * T.lam / 8 + (G₀ + T.lam * ρ) := ⟨_, rfl⟩
  have hGm0 : 0 ≤ Gm := by rw [hGmd]; positivity
  obtain ⟨y₃, hy₃, N⟩ := hnum (16 * (4 * (T.side : ℝ) ^ 4) * Gm * Wb) (T.rt / 2) 1 1 4 (by positivity) one_pos
  refine ⟨max T.floorMin (max y₁ y₃), (2 + 16 * ρ * (1 + Ao) * Real.exp (T.rt / 2)) * 16 * 16, by positivity,
    fun y hy R hRT n _ s hn hs p Q z K ra D hp1 hp16 hra hQ hD hap => ?_⟩
  obtain ⟨hR, hρA, hpc, hyx, hstep⟩ := id hRT
  have hy0 : T.floorMin ≤ y := (le_max_left _ _).trans hy
  have hy1 : y₁ ≤ y := (le_max_left _ _).trans ((le_max_right _ _).trans hy)
  have hy3 : y₃ ≤ R.coupling := ((le_max_right _ _).trans ((le_max_right _ _).trans hy)).trans hyx
  have hx1 : 1 ≤ R.coupling := hy₃.trans hy3
  have hx0 : 0 < R.coupling := by linarith
  have hL : R.params.side = T.side := by rw [hR]; rfl
  have hRrt : R.params.rt = T.rt := by rw [hR]; rfl
  have hRσ : R.params.threshold = T.threshold := by rw [hR]; rfl
  have hRn₀ : R.params.n₀ = T.n₀ := by rw [hR]; rfl
  have hfit : R.params.Admissible := by rw [hR]; exact hT.fits y hy0
  have hodd : Odd R.params.side := by rw [hL]; exact hT.L_odd
  have hRρ : R.ballRadius = ρ := by
    show R.params.threshold / 64 = _
    rw [hRσ, hρd]
  have hρR : 0 < R.ballRadius := by rw [hRρ]; exact hρ0
  have hcut : IsCutoff R.ballRadius R.barrierFn := by
    rw [hRρ, hpc, hρd]
    exact hT.cut
  have hrow := hstep.1
  have hσR : 0 < R.params.threshold := by rw [hRσ]; exact hσ
  have hrtR : 0 < R.params.rt := by rw [hRrt]; exact hrt0
  have hfull := (H1 y hy1 R hRT n (by rw [← hRn₀]; exact hn) s hs).1
  obtain ⟨Ψ, Kk, hΨe, hΨc, -, hΨr⟩ := htie R T.lam C hσR hrtR hx0 hlam n s _ hfull
  have hOff : R.params.offDiagonalBound T.lam C = Ao := by
    rw [hAod]
    simp only [TorusLumps.StepParameters.offDiagonalBound, TorusLumps.StepParameters.blockBondBound, hL, hRrt]
  rw [hOff] at hΨr
  have hCfin : 0 ≤ (2 + 16 * ρ * (1 + Ao) * Real.exp (T.rt / 2)) * 16 * 16 := by positivity
  have hexp0 := Real.exp_pos (-(R.params.rt * D / 2 ^ 4))
  by_cases hcard : p ≤ 1
  · obtain rfl : p = 1 := by omega
    have hK0 : 0 ≤ K := (abs_nonneg _).trans ((hQ 0).abs_le (trivialField _) ∅ (emptyLabelling R.labels.Ω))
    simp only [Fin.prod_univ_one, settingMean, sub_self, abs_zero]
    positivity
  have hp2 : 2 ≤ p := by omega
  have hK0 : 0 ≤ K := (abs_nonneg _).trans ((hQ ⟨0, by omega⟩).abs_le (trivialField _) ∅ (emptyLabelling R.labels.Ω))
  have hr1 : 1 ≤ R.range := by
    show 1 ≤ clusterRange R.coupling
    exact Nat.ceil_pos.mpr (Real.rpow_pos_of_pos hx0 _)
  have hr1' : (1 : ℝ) ≤ R.range := by exact_mod_cast hr1
  have hDr : 2 ^ 10 ≤ (D : ℝ) := by nlinarith
  set e := D / 8 with he
  have hDbig : 2 ^ 10 ≤ D := by exact_mod_cast hDr
  have hrD : R.range ≤ D := by
    have h1 : (R.range : ℝ) ≤ D := by nlinarith
    exact_mod_cast h1
  have he7 : 7 ≤ e := by omega
  have hLbig : 2 ^ 40 ≤ R.params.side := by rw [hL]; exact hT.L_ge
  set mm := R.params.side * e - R.params.side with hmm
  have hmD : 2 ^ 13 * D ≤ mm := by
    have h1 : mm = R.params.side * (e - 1) := by rw [hmm, Nat.mul_sub_one]
    have h2 : D ≤ 16 * (e - 1) := by omega
    rw [h1]
    calc 2 ^ 13 * D ≤ 2 ^ 13 * (16 * (e - 1)) := Nat.mul_le_mul_left _ h2
      _ = 2 ^ 17 * (e - 1) := by ring
      _ ≤ 2 ^ 40 * (e - 1) := Nat.mul_le_mul_right _ (by norm_num)
      _ ≤ _ := Nat.mul_le_mul_right _ hLbig
  have hmD' : (2 : ℝ) ^ 13 * D ≤ mm := by exact_mod_cast hmD
  have hraD : ra ≤ D := by nlinarith
  have hrm : ra + (clusterRange R.coupling : ℝ) / 64 ≤ (mm : ℝ) := by
    have h2 : ((clusterRange R.coupling : ℕ) : ℝ) = R.range := rfl
    rw [h2]
    nlinarith
  set E := Real.exp (-(R.params.rt * D)) with hE
  have hE0 : 0 ≤ E := (Real.exp_pos _).le
  have hexp : Real.exp (-R.params.decayRate * ((mm : ℝ) - ra)) ≤ E := by
    apply Real.exp_le_exp.mpr
    have h2 : R.params.decayRate = R.params.rt / 2 ^ 12 := rfl
    rw [h2]
    have h3 : (2 : ℝ) ^ 12 * D ≤ (mm : ℝ) - ra := by nlinarith
    have h4 := mul_le_mul_of_nonneg_left h3 (by positivity : 0 ≤ R.params.rt / 2 ^ 12)
    have h5 : R.params.rt / 2 ^ 12 * (2 ^ 12 * (D : ℝ)) = R.params.rt * D := by ring
    linarith
  set I : Finset (Fin p) := Finset.univ with hI
  have hsize : ∀ i, ∀ ζ, s.InBalls ζ → |Q i (s.field ζ) s.support s.labelling| ≤ K :=
    fun i ζ _ => (hQ i).abs_le _ _ _
  set G : Fin p → FreeCoords s.free → ℝ := fun i => onBalls s (stateValue s (Q i)) with hG
  have hGm : ∀ i, Measurable (G i) := fun i =>
    measurable_onBalls s (measurable_stateValue s (hQ i))
  have hGeq : ∀ i ζ, s.InBalls ζ → G i ζ = Q i (s.field ζ) s.support s.labelling := by
    intro i ζ hζ
    simp only [hG, onBalls]
    rw [if_pos hζ]
    rfl
  have hGle : ∀ i ζ, s.InBalls ζ → |G i ζ| ≤ K := fun i ζ hζ => by
    rw [hGeq i ζ hζ]
    exact hsize i ζ hζ
  have hcontΨ : Continuous Ψ := hΨc.smooth.continuous
  have hprodnn : 0 ≤ ∏ _i ∈ I, K := Finset.prod_nonneg fun _ _ => hK0
  obtain ⟨i₁, i₂, hi12⟩ : ∃ i₁ i₂ : Fin p, i₁ ≠ i₂ :=
    ⟨⟨0, by omega⟩, ⟨1, by omega⟩, by simp [Fin.ext_iff]⟩
  have hsep := hap i₁ i₂ hi12
  have hhalf := _root_.YangMills.Construction.SettingShifts.two_mul_supDist_le (parentBlock R.params.side (z i₁)) (parentBlock R.params.side (z i₂))
  have hkn : 2 * e + 2 < n := by omega
  set Ap : Fin p → Finset (TorusSite n) := fun i => {parentBlock R.params.side (z i)} with hAp
  have hap' : ∀ i ∈ I, ∀ j ∈ I, i ≠ j → ∀ Y ∈ Ap i, ∀ Y' ∈ Ap j, D ≤ _root_.YangMills.Construction.TorusFields.supDist Y Y' := by
    intro i _ j _ hij Y hY Y' hY'
    rw [Finset.mem_singleton.mp hY, Finset.mem_singleton.mp hY']
    exact hap i j hij
  set Lam : Fin p → Finset s.free := fun i => bondsNear s (3 * e) (Ap i) with hLam
  set Xs : Fin p → Finset s.free := fun i => bondsNear s e (Ap i) with hXs
  have hdis : ∀ i ∈ I, ∀ j ∈ I, i ≠ j → Disjoint (Lam i) (Lam j) := bondsNear_disjoint s (by omega) hap'
  have hXsub : ∀ i ∈ I, Xs i ⊆ Lam i := by
    intro i _ b hb
    obtain ⟨Y, hY, h1⟩ := mem_bondsNear.mp hb
    exact mem_bondsNear.mpr ⟨Y, hY, by omega⟩
  set F : Fin p → BondField s.free → ℝ := fun i η => G i (restrictCLM (Xs i) η) with hFd
  have hcutB : ∀ (S : Finset s.free) (η : BondField s.free), (∀ b, ‖η b‖ < R.ballRadius) →
      s.InBalls (restrictCLM S η) :=
    fun S η h => inBalls_of_forall_lt s (restrictCLM_mem hρR h)
  have hFm : ∀ i ∈ I, Measurable (F i) := fun i _ => (hGm i).comp (restrictCLM (Xs i)).continuous.measurable
  have hFread : ∀ i ∈ I, ∀ η η' : BondField s.free, (∀ b ∈ Xs i, η b = η' b) → F i η = F i η' := by
    intro i _ η η' h
    have : restrictCLM (Xs i) η = restrictCLM (Xs i) η' := by
      funext b
      rw [restrictCLM_apply, restrictCLM_apply]
      unfold ClusterExpansionOfAStep.restrictToSet
      split_ifs with hb
      · exact h b hb
      · rfl
    simp only [hFd, this]
  have hFle : ∀ i ∈ I, ∀ η : BondField s.free, (∀ b, ‖η b‖ < R.ballRadius) → |F i η| ≤ K :=
    fun i _ η h => hGle i _ (hcutB _ η h)
  have hGle' : ∀ i ∈ I, ∀ η : BondField s.free, (∀ b, ‖η b‖ < R.ballRadius) → |G i η| ≤ K :=
    fun i _ η h => hGle i η (inBalls_of_forall_lt s h)
  have hn2 : 2 ≤ n := by omega
  have hm : 2 * mm + 2 < n * R.params.side := by
    have hL1 : 1 ≤ R.params.side := Nat.pos_of_ne_zero (NeZero.ne _)
    have h1 : (2 * e + 3) * R.params.side ≤ n * R.params.side := Nat.mul_le_mul_right _ hkn
    have h2 : R.params.side * e - R.params.side ≤ R.params.side * e := Nat.sub_le _ _
    rw [hmm]
    nlinarith
  have hlive : ∀ η, s.InBalls η → IsLiveState R.params R.coupling R.labelWeight (s.field η) s.support s.labelling := by
    intro η hη
    have hρA' : 0 < R.anchorRadius := by rw [hRT.anchorRadius_eq]; exact hT.chain.2.2.2.1
    have hρπ : R.anchorRadius + R.ballRadius < Real.pi := by
      have h1 : R.ballRadius = R.params.threshold / 64 := rfl
      have h2 : R.params.threshold ≤ 1 := by rw [hRσ]; exact hT.σ_one
      have h3 := Real.pi_gt_three
      have h4 : R.anchorRadius ≤ 1 := by rw [hRT.anchorRadius_eq]; exact hT.chain.2.2.2.2.1
      linarith
    have hblock : IsBlockTorusSide R.params (n * R.params.side) :=
      ⟨Dvd.intro_left n rfl, by rw [mul_comm]; exact Nat.mul_le_mul_right _ hn⟩
    refine ⟨hs.isHull η hη, ?_⟩
    obtain ⟨hD, hk', hj, heq, -⟩ := hPot R hfit hrow hρA' hρπ n hn s hs η hη
    have hΦ : 0 < ∏ X ∈ chainComponents R.range s.support,
        R.clusterFactor (n * R.params.side) (s.field η) s.support s.labelling X :=
      Finset.prod_pos fun X hX =>
        lt_of_le_of_ne (hrow.2.factor_nonneg _ hblock _ _ _ X) (hs.factor_ne_zero η hη X hX).symm
    have hpos := mul_pos (mul_pos hD hΦ) (Real.exp_pos (-s.potential η))
    rw [← heq] at hpos
    exact (mul_pos_iff_of_pos_right hk').mp ((mul_pos_iff_of_pos_right hj).mp hpos)
  have hGF : ∀ i ∈ I, ∀ η : BondField s.free, (∀ b, ‖η b‖ < R.ballRadius) → |G i η - F i η| ≤ E * K := by
    intro i _ η h
    have hin := inBalls_of_forall_lt s h
    have hin' := hcutB (Xs i) η h
    have hFe : F i η = Q i (s.field (restrictCLM (Xs i) η)) s.support s.labelling := hGeq i _ hin'
    rw [hFe, hGeq i η hin]
    have hnear : CoordsAgreeNear s s (parentBlock R.params.side (z i)) (parentBlock R.params.side (z i)) e η
        (restrictCLM (Xs i) η) := by
      rw [restrictCLM_apply]
      exact coordsAgreeNear_restrict hodd s (Finset.mem_singleton_self _) η
    obtain ⟨o, ho, hyo⟩ := exists_fineSite_of_parentBlock hodd (parentBlock R.params.side (z i)) (z i) rfl
    have hfa := hF R n n s s (parentBlock R.params.side (z i)) (parentBlock R.params.side (z i)) e e η
      (restrictCLM (Xs i) η) o hfit hn2 hn2
      hs.subset_chart hs.subset_chart (settingsAgreeNear_refl s hs _ e hkn) (by omega) le_rfl hnear ho
    rw [← hyo] at hfa
    have hst : StatesAgreeNear R.params (s.field η) (s.field (restrictCLM (Xs i) η)) s.support s.support
        s.labelling s.labelling (z i) (z i) mm :=
      ⟨hm, hm, hfa, fun _ _ => Iff.rfl, fun _ _ _ _ _ => rfl, fun _ i => by simp⟩
    have h1 := (hQ i).abs_sub_le _ _ _ _ _ _ mm (hlive η hin) (hlive _ hin') hrm hst
    refine h1.trans ?_
    calc _ ≤ K * E := mul_le_mul_of_nonneg_left hexp hK0
      _ = _ := mul_comm _ _
  have hx8 : 0 < R.coupling * T.lam / 8 := by positivity
  have hd : IsPseudoMetricOnBonds s.bondDist := by
    refine ⟨fun b => ?_, fun b b' => ?_, fun b b' b'' => ?_⟩
    · simp [ChartSetting.bondDist, bondBlockDist, _root_.YangMills.Construction.TorusFields.supDist_self]
    · simp [ChartSetting.bondDist, bondBlockDist, _root_.YangMills.Construction.TorusFields.supDist_comm]
    · simp only [ChartSetting.bondDist, bondBlockDist]
      exact_mod_cast _root_.YangMills.Construction.TorusFields.supDist_triangle _ _ _
  have hC₁0 : 0 ≤ G₀ * R.coupling := by positivity
  have hCG : C ≤ G₀ := by
    rw [hG₀d]
    have : 0 ≤ T.lam * ρ := by positivity
    linarith only [this]
  have hfirst : ∀ η : BondField s.free, (∀ b, ‖η b‖ < R.ballRadius) → ∀ b, bondGradNorm Ψ b η ≤ G₀ * R.coupling := by
    intro η hη b
    refine bondGradNorm_le_of_forall hC₁0 fun X =>
      abs_le_mul_norm_of_unit hC₁0 (T := fun X => fderiv ℝ Ψ η (bondVariation b X))
      (fun t X => by rw [bondVariation_smul, map_smul, smul_eq_mul]) (fun X hX => ?_) X
    have hin := inBalls_of_forall_lt s hη
    have h1 := deriv_line_eq_fderiv (hΨe η hin) (hΨc.smooth.differentiable (by norm_num) η) b X
    show |fderiv ℝ Ψ η (bondVariation b X)| ≤ _
    rw [← h1]
    exact (hfull.firstDeriv_le η hin b X hX).trans (mul_le_mul_of_nonneg_right hCG hx0.le)
  set Cc := G₀ * R.coupling + R.coupling * T.lam * R.ballRadius with hCc
  have hsp := hsplit s.free (Fin p) R.ballRadius (R.coupling * T.lam / 8) R.params.rt Ao (R.coupling * T.lam)
    (G₀ * R.coupling) s.bondDist Ψ Kk R.barrierFn hρR hx8
    hrtR.le hcut hd hΨc hΨr (by linarith only [hx8]) hfirst I Lam Xs F (fun _ => K)
    (splitGradBound R.ballRadius Cc I Lam Kk) hdis hXsub hFm hFread
    hFle (fun i hi b hb => (splitGradBound_of_mem hdis hi hb).ge) (fun b hb => (splitGradBound_of_not_mem hb).ge)
  have hWall : ∀ b : s.free, ∑ b', Real.exp (-(R.params.rt / 2 * s.bondDist b b')) ≤ Wb := by
    intro b
    have h1 := sum_free_le_blocks hodd s
      (g := fun Z => Real.exp (-(R.params.rt / 2 * (_root_.YangMills.Construction.TorusFields.supDist (bondBlock (R := R) b.1) Z : ℝ))))
      (fun _ => (Real.exp_pos _).le)
    have h2 := hA₁ n (bondBlock (R := R) b.1) 0
    have h3 : ∑ Z : TorusSite n, Real.exp (-(R.params.rt / 2 * (_root_.YangMills.Construction.TorusFields.supDist (bondBlock (R := R) b.1) Z : ℝ))) ≤ A₁ := by
      have e1 : (Finset.univ.filter fun Y : TorusSite n => 0 ≤ _root_.YangMills.Construction.TorusFields.supDist Y (bondBlock (R := R) b.1)) = Finset.univ := by
        ext Y
        simp
      rw [e1] at h2
      simp only [Nat.cast_zero, mul_zero, zero_div, neg_zero, Real.exp_zero, mul_one] at h2
      refine le_trans (le_of_eq ?_) h2
      refine Finset.sum_congr rfl fun Z _ => ?_
      rw [hRrt, _root_.YangMills.Construction.TorusFields.supDist_comm]
    have hLr : (R.params.side : ℝ) = T.side := by rw [hL]
    have h4 : (0 : ℝ) ≤ 4 * (R.params.side : ℝ) ^ 4 := by positivity
    calc _ ≤ 4 * (R.params.side : ℝ) ^ 4 *
          ∑ Z : TorusSite n, Real.exp (-(R.params.rt / 2 * (_root_.YangMills.Construction.TorusFields.supDist (bondBlock (R := R) b.1) Z : ℝ))) := h1
      _ ≤ 4 * (R.params.side : ℝ) ^ 4 * A₁ := mul_le_mul_of_nonneg_left h3 h4
      _ = Wb := by rw [hWbd, hLr]
  have hAm0 : 0 ≤ Ao * (R.coupling * T.lam / 8) := by positivity
  have hGx0 : 0 ≤ Gm * R.coupling := by positivity
  have hG1 : R.ballRadius * (Ao * (R.coupling * T.lam / 8)) ≤ Gm * R.coupling := by
    rw [hRρ, hGmd]
    have : 0 ≤ (G₀ + T.lam * ρ) * R.coupling := by positivity
    nlinarith only [this]
  have hG2 : Cc ≤ Gm * R.coupling := by
    rw [hCc, hRρ, hGmd]
    have : 0 ≤ ρ * Ao * T.lam / 8 * R.coupling := by positivity
    nlinarith only [this]
  have hsum := sum_splitGradBound_le hodd s (κ := R.params.rt) (ρ := R.ballRadius) (Am := Ao * (R.coupling * T.lam / 8))
    (Gx := Gm * R.coupling) (Cc := Cc)
    (Wb := Wb) (Kk := Kk) (I := I) (Ap := Ap) (e := e) (D := D) hrtR.le hρR.le hAm0 hGx0
    (fun b b' => kernel_nonneg hρR hΨc b b') hΨr hG1 hG2 (by omega) (by omega) hap' hWall hWb0
  set SA : ℝ := (p : ℝ) with hSAd
  have hS₁ : ∑ i ∈ I, ((Ap i).card : ℝ) ≤ SA := by
    simp [hI, hAp, hSAd]
  have hN := N R.coupling hy3 e (by
    have h1 : R.range ≤ e := by
      have h2 : (2 : ℝ) ^ 10 * R.range ≤ D := by nlinarith
      have h3 : 2 ^ 10 * R.range ≤ D := by exact_mod_cast h2
      omega
    have h2 : ((clusterRange R.coupling : ℕ) : ℝ) ≤ e := by exact_mod_cast h1
    simpa using h2)
  have hLr : (T.side : ℝ) = R.params.side := by rw [hL]
  rw [hLr, ← hRrt] at hN
  have hcast : (((2 * e + 1 : ℕ) : ℝ)) = 2 * (e : ℝ) + 1 := by push_cast; ring
  have hnums := numeric_sum_bound (S₁ := ∑ i ∈ I, ((Ap i).card : ℝ)) (SA := SA) (g := ((2 * e + 1 : ℕ) : ℝ))
    (L4 := 4 * (R.params.side : ℝ) ^ 4) (Gm := Gm) (x := R.coupling) (Wb := Wb) (rt := R.params.rt) (ee := (e : ℝ))
    (Dr := (D : ℝ))
    (Finset.sum_nonneg fun _ _ => by positivity) hS₁ (Nat.cast_nonneg _)
    (by rw [hcast]; linarith only) (by rw [hcast]; linarith only) (Nat.cast_nonneg _) (by positivity) hGm0 hx0.le hWb0
    hrtR.le (by simpa [mul_assoc] using hN) (by
      have h1 : D ≤ 8 * (e + 1) := by omega
      have h2 : (D : ℝ) ≤ ((8 * (e + 1) : ℕ) : ℝ) := by exact_mod_cast h1
      push_cast at h2
      exact h2)
  set e16 := Real.exp (-(R.params.rt * D / 2 ^ 4)) with he16
  set xp := Real.exp (R.params.rt / 2) with hxp
  set Sm := ∑ b ∈ I.biUnion Xs, ∑ b', splitGradBound R.ballRadius Cc I Lam Kk b' *
    Real.exp (-(R.params.rt * s.bondDist b b')) with hSmd
  have hSm : Sm ≤ SA * (xp * e16) := by
    refine hsum.trans ?_
    calc _ = (∑ i ∈ I, ((Ap i).card : ℝ)) * ((2 * e + 1 : ℕ) : ℝ) ^ 4 * (4 * (R.params.side : ℝ) ^ 4) *
          (Gm * R.coupling * Real.exp (-(R.params.rt / 2 * ((2 * e + 1 : ℕ) : ℝ))) * Wb) := rfl
      _ ≤ _ := hnums
  have hSA1 : 1 ≤ SA := by
    have : (2 : ℝ) ≤ p := by exact_mod_cast hp2
    rw [hSAd]
    linarith
  have hIcard : (I.card : ℝ) = p := by simp [hI]
  have hc1 : (1 : ℝ) ≤ I.card := by rw [hIcard]; exact hSA1
  have hEe : E ≤ e16 := by
    apply Real.exp_le_exp.mpr
    have h0 : 0 ≤ R.params.rt * (D : ℝ) := by positivity
    linarith only [h0]
  have hGp : Measurable fun η : BondField s.free => ∏ i ∈ I, G i η :=
    Finset.measurable_fun_prod _ fun i _ => hGm i
  have hFp : Measurable fun η : BondField s.free => ∏ i ∈ I, F i η := Finset.measurable_fun_prod _ hFm
  have hGb : ∀ η : BondField s.free, (∀ b, ‖η b‖ < R.ballRadius) → |∏ i ∈ I, G i η| ≤ ∏ _i ∈ I, K := by
    intro η h
    rw [Finset.abs_prod]
    exact Finset.prod_le_prod (fun _ _ => abs_nonneg _) fun i hi => hGle' i hi η h
  have hFb : ∀ η : BondField s.free, (∀ b, ‖η b‖ < R.ballRadius) → |∏ i ∈ I, F i η| ≤ ∏ _i ∈ I, K := by
    intro η h
    rw [Finset.abs_prod]
    exact Finset.prod_le_prod (fun _ _ => abs_nonneg _) fun i hi => hFle i hi η h
  have T1 := abs_ballExpectation_sub_le (Ψ := Ψ) (E := I.card * E * ∏ _i ∈ I, K) hcontΨ hρR hcut hGp hFp hGb hFb
    (fun η h => abs_prod_sub_prod_le (P := fun _ => K) hE0 I (fun _ _ => hK0) (fun i hi => hGle' i hi η h)
      (fun i hi => hFle i hi η h) (fun i hi => hGF i hi η h))
  have T3 := abs_prod_sub_prod_le (a := fun i => ballExpectation (cutoffFactor R.ballRadius R.barrierFn) Ψ (F i))
    (b := fun i => ballExpectation (cutoffFactor R.ballRadius R.barrierFn) Ψ (G i)) (P := fun _ => K) hE0 I
    (fun _ _ => hK0)
    (fun i hi => abs_ballExpectation_le hcontΨ hρR hcut (hFm i hi) (hFle i hi))
    (fun i hi => abs_ballExpectation_le hcontΨ hρR hcut (hGm i) (hGle' i hi))
    (fun i hi => by
      rw [abs_sub_comm]
      exact abs_ballExpectation_sub_le hcontΨ hρR hcut (hGm i) (hFm i hi) (hGle' i hi) (hFle i hi) (hGF i hi))
  have e1 : weightedMean (chartDensity s) (fun η => ∏ i, Q i (s.field η) s.support s.labelling) =
      ballExpectation (cutoffFactor R.ballRadius R.barrierFn) Ψ (fun η => ∏ i ∈ I, G i η) := by
    rw [weightedMean_eq_ballExpectation hΨe]
    exact ballExpectation_congr fun η h =>
      Finset.prod_congr rfl fun i _ => (hGeq i η (inBalls_of_forall_lt s h)).symm
  have e2 : ∀ i, settingMean s (Q i) = ballExpectation (cutoffFactor R.ballRadius R.barrierFn) Ψ (G i) := by
    intro i
    unfold settingMean
    rw [weightedMean_eq_ballExpectation hΨe]
    exact ballExpectation_congr fun η h => (hGeq i η (inBalls_of_forall_lt s h)).symm
  rw [e1, Finset.prod_congr rfl fun i _ => e2 i]
  have hnum2 := numeric_closing_bound (c := (I.card : ℝ)) (SA := SA) (E := E) (e16 := e16) (U := ∏ _i ∈ I, K)
    (Sm := Sm) (Ao := Ao) (ρ := R.ballRadius) (xp := xp) hc1 hSA1 hE0 hEe hprodnn hρR.le hAo0
    (Real.exp_pos _).le (Real.exp_pos _).le hSm
  have hKp : ∏ _i ∈ I, K = K ^ p := by simp [hI]
  have hp16' : (p : ℝ) ≤ 16 := by exact_mod_cast hp16
  have hp0 : (0 : ℝ) ≤ p := Nat.cast_nonneg _
  have hpp : (p : ℝ) * p ≤ 16 * 16 := mul_le_mul hp16' hp16' hp0 (by norm_num)
  have hfinal : (2 + 16 * R.ballRadius * (1 + Ao) * xp) * (I.card : ℝ) * SA * e16 * ∏ _i ∈ I, K ≤
      (2 + 16 * ρ * (1 + Ao) * Real.exp (T.rt / 2)) * 16 * 16 * K ^ p * e16 := by
    rw [hRρ, hxp, hRrt, hIcard, hKp, hSAd]
    have hB : 0 ≤ 2 + 16 * ρ * (1 + Ao) * Real.exp (T.rt / 2) := by positivity
    have hKe : 0 ≤ K ^ p * e16 := by positivity
    calc (2 + 16 * ρ * (1 + Ao) * Real.exp (T.rt / 2)) * (p : ℝ) * p * e16 * K ^ p =
          (2 + 16 * ρ * (1 + Ao) * Real.exp (T.rt / 2)) * ((p : ℝ) * p) * (K ^ p * e16) := by ring
      _ ≤ (2 + 16 * ρ * (1 + Ao) * Real.exp (T.rt / 2)) * (16 * 16) * (K ^ p * e16) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpp hB) hKe
      _ = _ := by ring
  calc _ ≤ |ballExpectation (cutoffFactor R.ballRadius R.barrierFn) Ψ (fun η => ∏ i ∈ I, G i η) -
          ballExpectation (cutoffFactor R.ballRadius R.barrierFn) Ψ (fun η => ∏ i ∈ I, F i η)| +
        |ballExpectation (cutoffFactor R.ballRadius R.barrierFn) Ψ (fun η => ∏ i ∈ I, F i η) -
          ∏ i ∈ I, ballExpectation (cutoffFactor R.ballRadius R.barrierFn) Ψ (F i)| +
        |∏ i ∈ I, ballExpectation (cutoffFactor R.ballRadius R.barrierFn) Ψ (F i) -
          ∏ i ∈ I, ballExpectation (cutoffFactor R.ballRadius R.barrierFn) Ψ (G i)| :=
        (abs_sub_le _ _ _).trans (add_le_add_left (abs_sub_le _ _ _) _)
    _ ≤ I.card * E * (∏ _i ∈ I, K) + 4 * R.ballRadius * (1 + Ao) * (2 * (1 + I.card) * ∏ _i ∈ I, K) * Sm +
          I.card * E * ∏ _i ∈ I, K := add_le_add (add_le_add T1 hsp) T3
    _ ≤ _ := hnum2
    _ ≤ _ := hfinal
end Main
end NearlyLocalFactorization
theorem nearlyLocalSettingFactorization (hconv : ClusterExpansionOfAStep.SettingsUniformlyConvex)
    (htie : ClusterExpansionOfAStep.ChartPotentialConvex) (hsplit : ConvexDecoupling.ProductMeanNearMeanProduct)
    (hnum : PolynomialBelowExponential) (hF : FieldsAgreeOfCoordsAgree) (hPot : PotentialFactorization) :
    nearlyLocalSettingFactorizationStatement :=
  NearlyLocalFactorization.factorization_of_components hconv htie hsplit hnum hF hPot
end MomentLaw
end YangMills.Construction
end
