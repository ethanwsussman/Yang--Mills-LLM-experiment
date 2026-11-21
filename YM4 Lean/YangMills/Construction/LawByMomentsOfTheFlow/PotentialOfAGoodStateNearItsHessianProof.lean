import YangMills.Construction.ClusterExpansionOfAStep.ConvexityOfASettingProof
import YangMills.Construction.ClusterExpansionOfAStep.ExpansionsOfTheDensitiesOfASetting
import YangMills.Construction.ClusterExpansionOfAStep.ExpansionsOfTheLogarithmsOfASetting
import YangMills.Construction.ColdStepAtMirrorFrames.MirrorFieldIsCold
import YangMills.Construction.ColdStepAtMirrorFrames.SlopeOfAFrameBetween
import YangMills.Construction.LawByMomentsOfTheFlow.ColdLawOfAGoodStateProof
import YangMills.Construction.LawByMomentsOfTheFlow.CostOfTheColdSettingInTheChart
import YangMills.Construction.LawByMomentsOfTheFlow.EnergyToSecondOrderOnAChainTorus
import YangMills.Construction.LawByMomentsOfTheFlow.PotentialOfAGoodStateNearItsHessian
import YangMills.Construction.ResponseInTheExpansion.EntriesAtATopNearOneProof
import YangMills.Construction.ResponseInTheExpansion.StepNearItsHessianProof
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion Topology
open MeasureTheory Filter
namespace YangMills.Construction.MomentLaw
open StepSettings StepGas TorusFields TorusLumps StepCosts RenormalizationStepParameters BlockAverages ColdStepAtMirrorFrames
  LinearResponse MomentMethod Interpolation WeightedResponses ResponseInTheExpansion
namespace PotentialNearHessian
private theorem coordNorm_eq_norm (z : EuclideanSpace ℝ (Fin 3)) : coordNorm z = ‖z‖ := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.coordNorm_eq_norm <;> assumption
section Parameters
private theorem params_mono {Q Q' : MomentParameters → Prop} (h : ForAllParameters Q) (f : ∀ Λ, Q Λ → Q' Λ) : ForAllParameters Q' := by apply _root_.YangMills.SharedProofs.p9549 <;> assumption
private theorem params_and {Q₁ Q₂ : MomentParameters → Prop} (h₁ : ForAllParameters Q₁) (h₂ : ForAllParameters Q₂) :
    ForAllParameters fun Λ => Q₁ Λ ∧ Q₂ Λ := by apply _root_.YangMills.SharedProofs.p2495 <;> assumption
private theorem params_family (hConf : ClusterExpansionOfAStep.GasConfigIsAdmissibleSetting) (hDen : totalDensityPieceBound)
    (hLog : ClusterExpansionOfAStep.LogJacobianIsPotentialPiece) (hCost : coldSettingChartCostStatement) :
    ForAllParameters fun Λ => Λ.table.Admissible ∧ Λ.table.ColdStepHolds ∧ ∃ C c K : ℝ, 0 < C ∧ 0 < c ∧ 0 < K ∧ 200 * Λ.table.B ≤ Λ.floor ∧ 0 ≤ Λ.floor ∧
      (∀ R : StepSetup, R.OnParameters Λ.table Λ.floor → ∀ (n : ℕ) [NeZero n], Λ.table.n₀ ≤ n → ∀ s : ChartSetting R n, s.IsAdmissible →
        s.IsPotentialPiece s.totalDensity (C * (1 + Λ.table.E₃) + R.coupling ^ C * Real.exp (-c * (R.range : ℝ))) ∧
        s.IsPotentialPiece (fun η => ∑ Y : TorusSite n, s.logJacobian (s.field η) η Y) K) ∧
      (∀ R : StepSetup, R.OnParameters Λ.table Λ.floor → R.nextCoupling ≤ 1.01 * R.coupling → ∀ (n : ℕ) [NeZero n] (G : GasGround R n), G.IsAdmissibleGround →
        ∀ σ : G.Config, G.pairConstraint.IsAdmissible σ → (G.settingOf (G.familyOf σ)).IsAdmissible) ∧
      (∀ R : StepSetup, R.OnParameters Λ.table Λ.floor → ∀ (n : ℕ) [NeZero n], Λ.table.n₀ ≤ n → ∀ V : TorusField n, TorusFields.IsCold (9 / 8 * Λ.table.threshold) V →
        ∀ u : ℕ, u = R.depth → ∀ k : BondField (ChartBondIndex R.params.side u n), (∀ b, ‖k b‖ < R.ballRadius) →
          ∑ Y : TorusSite n, (coldSettingOver R V).blockCostAt Y (chartFreeCoords R u V k) =
            chartedEnergyAt R.params.coupling
              (frameCoordField false R.params.coupling R.anchorRadius R.frameReach (readAtLevel (torusFrame R.params.side u n) (torusFrame R.params.side u n).top V))
              (readAtLevel (torusFrame R.params.side u n) (torusFrame R.params.side u n).top V) k) := by
  intro a _
  refine ⟨0, fun _ => 1, 0, fun _ => one_pos, ?_⟩
  intro L _ _ Tb _ _ hD hS _ _ _ _ _
  obtain ⟨C₁, c₁, y₁, hC₁, hc₁, Y₁⟩ := hDen Tb hD
  obtain ⟨C₂, y₂, hC₂, Y₂⟩ := hLog Tb hD
  obtain ⟨y₃, Y₃⟩ := hConf Tb hD
  obtain ⟨y₄, Y₄⟩ := hCost Tb hD
  refine ⟨max (max (max y₁ y₂) (max y₃ y₄)) (max (200 * Tb.B) 0), fun y hy _ _ g _ _ k _ _ _ R d _ => ?_⟩
  have hy₁ : y₁ ≤ y := le_trans (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) (le_max_left _ _)) hy
  have hy₂ : y₂ ≤ y := le_trans (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) (le_max_left _ _)) hy
  have hy₃ : y₃ ≤ y := le_trans (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_max_left _ _)) hy
  have hy₄ : y₄ ≤ y := le_trans (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) (le_max_left _ _)) hy
  have hy₅ : 200 * Tb.B ≤ y := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hy
  have hy₆ : 0 ≤ y := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hy
  refine ⟨hD, hS, C₁, c₁, C₂, hC₁, hc₁, hC₂, hy₅, hy₆, ?_, ?_, ?_⟩
  · intro R hR n _ hn s hs
    exact ⟨Y₁ y hy₁ R hR n hn s hs, Y₂ y hy₂ R hR n hn s hs⟩
  · intro R hR hx n _ G hG σ hσ
    exact Y₃ y hy₃ R hR hx n G hG σ hσ
  · intro R hR n _ hn V hV u hu k hk
    exact Y₄ y hy₄ R hR n hn V hV u hu k hk
end Parameters
section Numbers
private theorem small_number (x σ : ℝ) (hσ : 0 < σ) (hx : (64 / σ + 1) ^ 4 ≤ x) : 64 * x ^ (-(1 / 4) : ℝ) < 9 / 8 * σ := by apply _root_.YangMills.SharedProofs.p21801 <;> assumption
private theorem half_le_of_near {xs x cn : ℝ} (hx2 : 2 ≤ xs) (hcn : 0 ≤ cn) (hxn : 16 * cn ^ 2 ≤ xs)
    (hnear : |x - xs| ≤ cn * Real.log xs) : xs / 2 ≤ x := by apply _root_.YangMills.SharedProofs.p65497 <;> assumption
private theorem range_bounds (C c A δ s : ℝ) (hc : 0 < c) (hδ : 0 < δ) (hs : 0 < s) (hA : 0 ≤ A) :
    ∃ X : ℝ, 1 ≤ X ∧ ∀ x : ℝ, X ≤ x →
      x ^ C * Real.exp (-c * (clusterRange x : ℝ)) ≤ 1 ∧ 16 ≤ clusterRange x / 2 ^ 11 ∧
      A * Real.exp (-(δ / 4 * ((clusterRange x / 2 ^ 11 : ℕ) : ℝ))) ≤ s ∧
      x * (A * Real.exp (-(δ / 4 * ((clusterRange x / 2 ^ 11 : ℕ) : ℝ)))) ≤ 1 := by
  set b : ℝ := δ / 2 ^ 13 with hb
  have hb0 : 0 < b := by positivity
  set A' : ℝ := A * Real.exp (δ / 4) with hA'
  have hA'0 : 0 ≤ A' := by positivity
  have hz : Tendsto (fun x : ℝ => x ^ ((1 : ℝ) / 100)) atTop atTop := tendsto_rpow_atTop (by norm_num)
  have e1 : ∀ᶠ z : ℝ in atTop, z ^ (100 * C) * Real.exp (-c * z) < 1 :=
    (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (100 * C) c hc).eventually_lt_const (by norm_num)
  have e2 : ∀ᶠ z : ℝ in atTop, z ^ (100 : ℝ) * Real.exp (-b * z) < 1 / (A' + 1) :=
    (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 100 b hb0).eventually_lt_const (by positivity)
  have e3 : ∀ᶠ z : ℝ in atTop, z ^ (0 : ℝ) * Real.exp (-b * z) < s / (A' + 1) :=
    (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 0 b hb0).eventually_lt_const (by positivity)
  have e4 : ∀ᶠ z : ℝ in atTop, (2 : ℝ) ^ 16 ≤ z := eventually_ge_atTop _
  obtain ⟨X, hX⟩ := eventually_atTop.1 ((hz.eventually (e1.and (e2.and (e3.and e4)))).and (eventually_ge_atTop (1 : ℝ)))
  refine ⟨max X 1, le_max_right _ _, fun x hx => ?_⟩
  obtain ⟨⟨h1, h2, h3, h4⟩, hx1⟩ := hX x (le_trans (le_max_left _ _) hx)
  set z : ℝ := x ^ ((1 : ℝ) / 100) with hzd
  have hx0 : 0 < x := by linarith
  have hzr : z ≤ (clusterRange x : ℝ) := Nat.le_ceil _
  set r : ℕ := clusterRange x with hr
  set m : ℕ := r / 2 ^ 11 with hm
  have hmr : (r : ℝ) < ((m : ℝ) + 1) * 2 ^ 11 := by
    have h5 : r < (m + 1) * 2 ^ 11 := by
      have := Nat.div_add_mod r (2 ^ 11)
      have h6 := Nat.mod_lt r (show 0 < 2 ^ 11 by norm_num)
      simp only [hm]
      nlinarith
    exact_mod_cast h5
  have hxz : x = z ^ (100 : ℝ) := by
    rw [hzd, ← Real.rpow_mul hx0.le]
    norm_num
  have hexp : Real.exp (-(δ / 4 * (m : ℝ))) ≤ Real.exp (δ / 4) * Real.exp (-b * z) := by
    rw [← Real.exp_add, Real.exp_le_exp]
    have h7 : z ≤ ((m : ℝ) + 1) * 2 ^ 11 := hzr.trans hmr.le
    have h8 : b * z ≤ δ / 4 * ((m : ℝ) + 1) := by
      have : b * z ≤ b * (((m : ℝ) + 1) * 2 ^ 11) := mul_le_mul_of_nonneg_left h7 hb0.le
      refine this.trans (le_of_eq ?_)
      simp only [hb]
      ring
    nlinarith
  have hAe : A * Real.exp (-(δ / 4 * (m : ℝ))) ≤ A' * Real.exp (-b * z) := by
    have := mul_le_mul_of_nonneg_left hexp hA
    simpa [hA', mul_assoc] using this
  have hE0 : 0 < Real.exp (-b * z) := Real.exp_pos _
  refine ⟨?_, ?_, ?_, ?_⟩
  · have hxc : x ^ C = z ^ (100 * C) := by
      rw [hzd, ← Real.rpow_mul hx0.le]
      congr 1
      ring
    rw [hxc]
    have hc1 : Real.exp (-c * (r : ℝ)) ≤ Real.exp (-c * z) := by
      rw [Real.exp_le_exp]
      nlinarith
    exact (mul_le_mul_of_nonneg_left hc1 (by positivity)).trans h1.le
  · rw [Nat.le_div_iff_mul_le (by norm_num)]
    have : ((16 * 2 ^ 11 : ℕ) : ℝ) ≤ (r : ℝ) := by
      push_cast
      have h9 : (2 : ℝ) ^ 16 ≤ r := h4.trans hzr
      norm_num at h9 ⊢
      linarith
    exact_mod_cast this
  · refine hAe.trans ?_
    have h9 : Real.exp (-b * z) < s / (A' + 1) := by simpa using h3
    have h10 : A' * Real.exp (-b * z) ≤ (A' + 1) * Real.exp (-b * z) :=
      mul_le_mul_of_nonneg_right (by linarith) hE0.le
    refine h10.trans ?_
    have h11 : (A' + 1) * Real.exp (-b * z) ≤ (A' + 1) * (s / (A' + 1)) :=
      mul_le_mul_of_nonneg_left h9.le (by positivity)
    refine h11.trans (le_of_eq ?_)
    field_simp
  · rw [← hxz] at h2
    have h12 : x * (A * Real.exp (-(δ / 4 * (m : ℝ)))) ≤ x * (A' * Real.exp (-b * z)) :=
      mul_le_mul_of_nonneg_left hAe hx0.le
    refine h12.trans ?_
    have h13 : x * (A' * Real.exp (-b * z)) ≤ (A' + 1) * (x * Real.exp (-b * z)) := by
      have : 0 ≤ x * Real.exp (-b * z) := by positivity
      nlinarith
    refine h13.trans ?_
    have h14 : (A' + 1) * (x * Real.exp (-b * z)) ≤ (A' + 1) * (1 / (A' + 1)) :=
      mul_le_mul_of_nonneg_left h2.le (by positivity)
    refine h14.trans (le_of_eq ?_)
    field_simp
private theorem abs_deriv_sub_le {x f1 f0 s2 d1 d2 K₁ K₂ Cq Q : ℝ} (hx : 0 ≤ x) (h1 : |f1 - f0 - s2| ≤ Cq * Q) (h0 : x * |f0| ≤ 1)
    (hd1 : |d1| ≤ K₁) (hd2 : |d2| ≤ K₂) (hK₁ : 0 ≤ K₁) (hK₂ : 0 ≤ K₂) (hCq : 0 ≤ Cq) (hQ : 0 ≤ Q) :
    |x * f1 - d1 - d2 - x * s2| ≤ (1 + K₁ + K₂ + Cq) * (1 + x * Q) := by
  have e : x * f1 - d1 - d2 - x * s2 = x * (f1 - f0 - s2) + x * f0 - d1 - d2 := by ring
  rw [e]
  have a1 : |x * (f1 - f0 - s2)| ≤ x * (Cq * Q) := by
    rw [abs_mul, abs_of_nonneg hx]
    exact mul_le_mul_of_nonneg_left h1 hx
  have a2 : |x * f0| ≤ 1 := by
    rw [abs_mul, abs_of_nonneg hx]
    exact h0
  have a3 : |x * (f1 - f0 - s2) + x * f0 - d1 - d2| ≤ x * (Cq * Q) + 1 + K₁ + K₂ := by
    have t1 := abs_sub (x * (f1 - f0 - s2) + x * f0 - d1) d2
    have t2 := abs_sub (x * (f1 - f0 - s2) + x * f0) d1
    have t3 := abs_add_le (x * (f1 - f0 - s2)) (x * f0)
    linarith
  refine a3.trans ?_
  have hxQ : 0 ≤ x * Q := mul_nonneg hx hQ
  nlinarith [mul_nonneg hK₁ hxQ, mul_nonneg hK₂ hxQ]
end Numbers
section Relabel
variable {L u m : ℕ} [NeZero L] [NeZero m]
private abbrev frameBond (L u m : ℕ) (c : TorusBond (m * L)) : (torusFrame L u m).Site (torusFrame L u m).depth × Fin 4 :=
  (torusSiteInFrame (torusFrame L u m) (torusFrame L u m).depth c.1, c.2)
private theorem frameBond_inj (c c' : TorusBond (m * L)) (h : frameBond L u m c = frameBond L u m c') : c = c' := by apply _root_.YangMills.DeltaSharedProofs.p500956 <;> assumption
private theorem mem_chordBonds_of (hodd : Odd L) (h2 : 2 ≤ m) {c : TorusBond (m * L)} (hc : c ∈ StepCosts.chartBonds L m) :
    frameBond L u m c ∈ chordBonds (finiteCells (torusFrame L u m)) := by apply _root_.YangMills.DeltaSharedProofs.p363 <;> assumption
private theorem frameBond_toTorusSite (b : (torusFrame L u m).Site (torusFrame L u m).depth × Fin 4) :
    frameBond L u m (toTorusSite (m * L) b.1, b.2) = b := by apply _root_.YangMills.DeltaSharedProofs.p501604 <;> assumption
private theorem mem_chartBonds_of (hodd : Odd L) (h2 : 2 ≤ m) (b : ChartBondIndex L u m) :
    (toTorusSite (m * L) b.1.1, b.1.2) ∈ StepCosts.chartBonds L m := by apply _root_.YangMills.SharedProofs.p28920 <;> assumption
private def chartBondsEquiv (hodd : Odd L) (h2 : 2 ≤ m) : ↥(StepCosts.chartBonds L m) ≃ ChartBondIndex L u m where
  toFun b := ⟨frameBond L u m b.1, mem_chordBonds_of hodd h2 b.2⟩
  invFun c := ⟨(toTorusSite (m * L) c.1.1, c.1.2), mem_chartBonds_of hodd h2 c⟩
  left_inv b := by
    apply Subtype.ext
    exact frameBond_inj (L := L) (u := u) (m := m) _ _ (frameBond_toTorusSite _)
  right_inv c := by
    apply Subtype.ext
    exact frameBond_toTorusSite _
end Relabel
section Free
variable {R : StepSetup} {n : ℕ} [NeZero n]
private theorem mem_free_coldSetting (V : TorusField n) (b : TorusBond (n * R.params.side)) :
    b ∈ (coldSettingOver R V).free ↔ b ∈ StepCosts.chartBonds R.params.side n := by apply _root_.YangMills.SharedProofs.p28439 <;> assumption
end Free
section Maps
variable {ι κ : Type} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ] (e : ι ≃ κ)
private def reindexMap : BondField κ →L[ℝ] BondField ι :=
  ContinuousLinearMap.pi fun b => ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : κ => BondVector) (e b)
@[simp] private theorem reindexMap_apply (k : BondField κ) (b : ι) : reindexMap e k b = k (e b) := rfl
private theorem reindexMap_bondVariation (c : κ) (x : BondVector) :
    reindexMap e (bondVariation c x) = bondVariation (e.symm c) x := by
  funext b
  simp only [reindexMap_apply, bondVariation, Pi.single_apply]
  by_cases h : e b = c
  · have : b = e.symm c := by rw [← h]; simp
    simp [h, this]
  · have : b ≠ e.symm c := fun h' => h (by rw [h']; simp)
    simp [h, this]
end Maps
section Chart
variable {R : StepSetup} {n : ℕ} [NeZero n]
private def freeEquiv (u : ℕ) (V : TorusField n) (hodd : Odd R.params.side) (h2 : 2 ≤ n) :
    ↥(coldSettingOver R V).free ≃ ChartBondIndex R.params.side u n :=
  (Equiv.subtypeEquivRight (mem_free_coldSetting V)).trans (chartBondsEquiv hodd h2)
private theorem freeEquiv_val (u : ℕ) (V : TorusField n) (hodd : Odd R.params.side) (h2 : 2 ≤ n) (b : ↥(coldSettingOver R V).free) :
    (freeEquiv u V hodd h2 b).1 = frameBond R.params.side u n b.1 := rfl
private theorem chartFreeCoords_eq (u : ℕ) (V : TorusField n) (hodd : Odd R.params.side) (h2 : 2 ≤ n)
    (k : BondField (ChartBondIndex R.params.side u n)) : chartFreeCoords R u V k = reindexMap (freeEquiv u V hodd h2) k := by
  classical
  funext b
  unfold chartFreeCoords
  rw [reindexMap_apply, Finset.sum_eq_single (freeEquiv u V hodd h2 b)]
  · exact if_pos (freeEquiv_val u V hodd h2 b).symm
  · intro c _ hne
    rw [if_neg]
    intro h
    exact hne (Subtype.ext h.symm)
  · simp
end Chart
private theorem settingOf_allVacant {R : StepSetup} {n : ℕ} [NeZero n] (G : GasGround R n) :
    G.settingOf (G.familyOf G.allVacant) = G.groundSetting := by apply _root_.YangMills.SharedProofs.p14309 <;> assumption
section Core
variable {R : StepSetup} {n : ℕ} [NeZero n]
private theorem abs_fderiv_le_of_piece {s : ChartSetting R n} {g : FreeCoords s.free → ℝ} {K : ℝ} (h : s.IsPotentialPiece g K)
    (η : FreeCoords s.free) (hη : s.InBalls η) (b : ↥s.free) (X : BondVector) (hX : ‖X‖ = 1) :
    |fderiv ℝ g η (bondVariation b X)| ≤ K := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.potentialPiece_abs_fderiv_single_le <;> assumption
private theorem eq_sum_coordinates {ι : Type} [Fintype ι] [DecidableEq ι] (η : BondField ι) :
    η = ∑ r : ι × Fin 3, η r.1 r.2 • bondCoordinateVector r := by apply _root_.YangMills.Construction.ResponseInTheExpansion.StepNearHessianProof.eq_sum_bondCoordinateVector <;> assumption
private theorem secondDerivAlong_eq_sum {ι : Type} [Fintype ι] [DecidableEq ι] (E : BondField ι → ℝ) (η : BondField ι) (r : ι × Fin 3) :
    secondDerivAlong E 0 (bondCoordinateVector r) η = ∑ c : ι × Fin 3, bondCoordinateHessian E r c * η c.1 c.2 := by
  have e1 : secondDerivAlong E 0 (bondCoordinateVector r) η =
      fderiv ℝ (fun ζ => fderiv ℝ E ζ (bondCoordinateVector r)) 0 η := rfl
  rw [e1]
  conv_lhs => rw [eq_sum_coordinates η]
  rw [map_sum]
  simp only [bondCoordinateHessian, map_smul, smul_eq_mul]
  refine Finset.sum_congr rfl fun c _ => ?_
  have : secondDerivAlong E 0 (bondCoordinateVector r) (bondCoordinateVector c) =
      fderiv ℝ (fun ζ => fderiv ℝ E ζ (bondCoordinateVector r)) 0 (bondCoordinateVector c) := rfl
  rw [this]
  ring
private theorem potential_near_hessian_core (u : ℕ) (V : TorusField n) (hodd : Odd R.params.side) (h2 : 2 ≤ n) (E : BondField (ChartBondIndex R.params.side u n) → ℝ)
    (κ : ChartBondIndex R.params.side u n → ChartBondIndex R.params.side u n → ℝ) (K₁ K₂ Cq : ℝ)
    (hK₁ : 0 ≤ K₁) (hK₂ : 0 ≤ K₂) (hCq : 0 ≤ Cq) (hx : 0 ≤ R.coupling)
    (hcost : ∀ k : BondField (ChartBondIndex R.params.side u n), (∀ b, ‖k b‖ < R.ballRadius) →
      ∑ Y : TorusSite n, (coldSettingOver R V).blockCostAt Y (chartFreeCoords R u V k) = E k)
    (hD : (coldSettingOver R V).IsPotentialPiece (coldSettingOver R V).totalDensity K₁)
    (hJ : (coldSettingOver R V).IsPotentialPiece
      (fun η => ∑ Y : TorusSite n, (coldSettingOver R V).logJacobian ((coldSettingOver R V).field η) η Y) K₂)
    (hEd : ∀ k : BondField (ChartBondIndex R.params.side u n), (∀ b, ‖k b‖ < R.ballRadius) → DifferentiableAt ℝ E k)
    (h2nd : ∀ k : BondField (ChartBondIndex R.params.side u n), (∀ b, ‖k b‖ < R.ballRadius) → ∀ (b : ChartBondIndex R.params.side u n) (e : BondVector), ‖e‖ = 1 →
      |fderiv ℝ E k (bondVariation b e) - fderiv ℝ E 0 (bondVariation b e) -
        secondDerivAlong E 0 (bondVariation b e) k| ≤ Cq * (∑ b', κ b b' * ‖k b'‖) ^ 2)
    (h0 : ∀ (b : ChartBondIndex R.params.side u n) (e : BondVector), ‖e‖ = 1 → R.coupling * |fderiv ℝ E 0 (bondVariation b e)| ≤ 1)
    (k : BondField (ChartBondIndex R.params.side u n)) (hk : ∀ b, ‖k b‖ < R.ballRadius) (j : Fin 3 × ChartBondIndex R.params.side u n) :
    |fderiv ℝ (chartPotential R u V) k (unitVariation j) -
        R.coupling * ∑ r : ChartBondIndex R.params.side u n × Fin 3, bondCoordinateHessian E (j.2, j.1) r * k r.1 r.2| ≤
      (1 + K₁ + K₂ + Cq) * (1 + R.coupling * (∑ b, κ j.2 b * ‖k b‖) ^ 2) := by
  set e := freeEquiv (R := R) u V hodd h2 with he
  have hcf : ∀ k' : BondField (ChartBondIndex R.params.side u n), chartFreeCoords R u V k' = reindexMap e k' := chartFreeCoords_eq u V hodd h2
  set Dg : BondField (ChartBondIndex R.params.side u n) → ℝ := fun k' => (coldSettingOver R V).totalDensity (reindexMap e k') with hDg
  set Jg : BondField (ChartBondIndex R.params.side u n) → ℝ := fun k' => ∑ Y : TorusSite n,
    (coldSettingOver R V).logJacobian ((coldSettingOver R V).field (reindexMap e k')) (reindexMap e k') Y with hJg
  have hU : IsOpen {k' : BondField (ChartBondIndex R.params.side u n) | ∀ b, ‖k' b‖ < R.ballRadius} := by
    have : {k' : BondField (ChartBondIndex R.params.side u n) | ∀ b, ‖k' b‖ < R.ballRadius} = ⋂ b, {k' | ‖k' b‖ < R.ballRadius} := by
      ext k'
      simp
    rw [this]
    exact isOpen_iInter_of_finite fun b => isOpen_lt (by fun_prop) continuous_const
  have hP : chartPotential R u V =ᶠ[𝓝 k] fun k' => R.coupling * E k' - Dg k' - Jg k' := by
    filter_upwards [hU.mem_nhds hk] with k' hk'
    have e1 := hcost k' hk'
    rw [← e1]
    show (coldSettingOver R V).potential (chartFreeCoords R u V k') = _
    simp only [hDg, hJg]
    rw [← hcf k']
    unfold ChartSetting.potential ChartSetting.totalDensity ChartSetting.blockCostAt
    rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, Finset.mul_sum]
  have hin : (coldSettingOver R V).InBalls (reindexMap e k) := fun b => by
    rw [coordNorm_eq_norm, reindexMap_apply]
    exact (hk _).le
  have hDd : DifferentiableAt ℝ (coldSettingOver R V).totalDensity (reindexMap e k) :=
    (hD.smooth _ hin).differentiableAt (by norm_num)
  have hJd : DifferentiableAt ℝ (fun η => ∑ Y : TorusSite n, (coldSettingOver R V).logJacobian ((coldSettingOver R V).field η) η Y) (reindexMap e k) :=
    (hJ.smooth _ hin).differentiableAt (by norm_num)
  have hDf : HasFDerivAt Dg ((fderiv ℝ (coldSettingOver R V).totalDensity (reindexMap e k)).comp (reindexMap e)) k :=
    hDd.hasFDerivAt.comp k (reindexMap e).hasFDerivAt
  have hJf : HasFDerivAt Jg ((fderiv ℝ (fun η => ∑ Y : TorusSite n, (coldSettingOver R V).logJacobian ((coldSettingOver R V).field η) η Y)
      (reindexMap e k)).comp (reindexMap e)) k :=
    hJd.hasFDerivAt.comp k (reindexMap e).hasFDerivAt
  have hEf := (hEd k hk).hasFDerivAt
  have hall := ((hEf.const_mul R.coupling).sub hDf).sub hJf
  have hfd : fderiv ℝ (chartPotential R u V) k = _ := hP.fderiv_eq.trans hall.fderiv
  rw [hfd]
  have hunit : (unitVariation j : BondField (ChartBondIndex R.params.side u n)) = bondVariation j.2 (EuclideanSpace.single j.1 1) := rfl
  have hnorm : ‖(EuclideanSpace.single j.1 (1 : ℝ) : BondVector)‖ = 1 := by simp
  have hbond := reindexMap_bondVariation e j.2 (EuclideanSpace.single j.1 (1 : ℝ))
  have d1 := abs_fderiv_le_of_piece hD (reindexMap e k) hin (e.symm j.2) _ hnorm
  have d2 := abs_fderiv_le_of_piece hJ (reindexMap e k) hin (e.symm j.2) _ hnorm
  rw [← hbond] at d1 d2
  have hs2 := secondDerivAlong_eq_sum E k (j.2, j.1)
  have hcu : (bondCoordinateVector (j.2, j.1) : BondField (ChartBondIndex R.params.side u n)) = bondVariation j.2 (EuclideanSpace.single j.1 1) := rfl
  rw [← hs2, hcu]
  simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply, smul_eq_mul]
  rw [hunit]
  have hQ : 0 ≤ (∑ b, κ j.2 b * ‖k b‖) ^ 2 := by positivity
  exact abs_deriv_sub_le hx (h2nd k hk j.2 _ hnorm) (h0 j.2 _ hnorm) d1 d2 hK₁ hK₂ hCq hQ
end Core
section Frames
variable {F : BlockFrame}
private theorem toImaginary_smul (c : ℝ) (v : BondVector) : toImaginary (c • v) = c • toImaginary v := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.ImaginaryCoordinates.toImaginary_smul <;> assumption
private theorem toImaginary_zero : toImaginary (0 : BondVector) = 0 := by apply _root_.YangMills.SharedProofs.p2840 <;> assumption
private theorem norm_toImaginary (v : BondVector) : ‖toImaginary v‖ = ‖v‖ := coordNorm_eq_norm v
abbrev ChordBond (F : BlockFrame) : Type := ↥(chordBonds (finiteCells F))
private theorem add_stepCoordinates_eq_update (w : F.Site F.depth → Fin 4 → imaginaryQuaternions) (b : ChordBond F) (e : BondVector) (u : ℝ) :
    (fun x i => w x i + stepCoordinates (u • (bondVariation b e : StepVariable (finiteCells F))) x i) =
      Function.update w b.1.1 (Function.update (w b.1.1) b.1.2 (w b.1.1 b.1.2 + u • toImaginary e)) := by apply _root_.YangMills.Construction.ResponseInTheExpansion.StepNearHessianProof.add_stepCoordinates_eq_update <;> assumption
private theorem chartedSlope_eq_fderiv (a : ℝ) (w : F.Site F.depth → Fin 4 → imaginaryQuaternions) (V : F.GaugeField F.top) (b : ChordBond F) (e : BondVector)
    (hd : DifferentiableAt ℝ (chartedEnergyAt a w V) 0) :
    chartedSlope a w V b.1 (toImaginary e) = fderiv ℝ (chartedEnergyAt a w V) 0 (bondVariation b e) := by apply _root_.YangMills.Construction.ResponseInTheExpansion.StepNearHessianProof.chartedSlope_eq_fderiv <;> assumption
private theorem leftTranslate_bondSpread_empty (V : F.GaugeField F.top) (s : Fin 0 → F.Site F.top × Fin 4) (X : Fin 0 → imaginaryQuaternions) (τ : Fin 0 → ℝ) :
    leftTranslate (ColdStepAtMirrorFrames.bondSpread s X τ) V = V := by
  have h0 : expUnit (0 : imaginaryQuaternions) = 1 := by
    apply Subtype.ext
    simp [expUnit]
  funext y i
  simp [leftTranslate, ColdStepAtMirrorFrames.bondSpread, h0]
private theorem abs_chartedSlope_le_of_interpolated {a ρ : ℝ} {m : ℕ} {V : F.GaugeField F.top} {B : ℝ} (b : ChordBond F) (e : imaginaryQuaternions)
    (h : ∀ (s : Fin 0 → F.Site F.top × Fin 4) (X : Fin 0 → imaginaryQuaternions), |bondDeriv (interpolatedSlope 1 a ρ m b.1 e) V s X| ≤ B) :
    |chartedSlope a (frameCoordField false a ρ m V) V b.1 e| ≤ B := by
  have h1 := h Fin.elim0 Fin.elim0
  have e1 : bondDeriv (interpolatedSlope 1 a ρ m b.1 e) V (Fin.elim0 : Fin 0 → F.Site F.top × Fin 4) Fin.elim0 =
      interpolatedSlope 1 a ρ m b.1 e V := by
    unfold bondDeriv
    rw [iteratedFDeriv_zero_apply, leftTranslate_bondSpread_empty]
  rw [e1] at h1
  have e2 : (fun z i => interpolatedFrame 1 a ρ m (z, i) V) = frameCoordField false a ρ m V := by
    funext z i
    simp [interpolatedFrame, frameCoordField]
  unfold interpolatedSlope at h1
  rwa [e2] at h1
open Classical in
private theorem isAdmissibleChartPoint_of_small (hcov : BlocksCoverLowerLevel) {L : ℕ} {σA s₁ e : ℝ} (hF : IsBlockTorus L F) (hL : Odd L)
    (he0 : 0 ≤ e) (he : e ≤ 1 / (64 * (L : ℝ))) (hs₁ : 0 ≤ s₁) (hlt : s₁ + 8 * e < σA) (w : F.Site F.depth → Fin 4 → imaginaryQuaternions) (V : F.GaugeField F.top)
    (hw : ∀ b ∈ chordBonds (finiteCells F), ‖w b.1 b.2‖ ≤ e) (hV : IsSmallCurvature s₁ V) : IsAdmissibleChartPoint L σA w V := by apply _root_.YangMills.SharedProofs.p28958 (s₁ := s₁) (e := e) <;> assumption
private theorem norm_bondFrameCoord_le (hMF : ReflectedFieldSmallCurvature) {a : ℝ} {L : ℕ} {c : ColdChainParameters} (hL : Odd L) (hc : c.Admissible a L)
    (hρ : c.ρA ≤ 1) {G : BlockFrame} (hG : IsBlockTorus L G) (m : ℕ) (hm : 16 ≤ m) (V : G.GaugeField G.top) (s : ℝ)
    (hs : 0 < s) (hsA : s ≤ c.σA) (hV : IsSmallCurvature s V) (b : G.Site G.depth × Fin 4) :
    ‖bondFrameCoord a c.ρA m b V‖ ≤ c.N 0 * s := by
  have hN : 0 ≤ c.N 0 * s := mul_nonneg (hc.positivity.2.2.2.2.2.1 0).le hs.le
  unfold bondFrameCoord
  by_cases hside : ∀ i, 4 * m + 5 < G.extent i
  · rw [if_pos hside]
    unfold reflectedBondCoord minimizingBondCoordinate
    set G₂ := reflectedFrame G m with hG₂
    set U := reflectedField m (enclosingCell b.1) V with hU
    have hch : IsBlockTorus L G₂ := ⟨hG.1, 4 * m, by omega, fun _ => rfl⟩
    have hU' : IsSmallCurvature s U := hMF G m _ V s (by omega) hV
    have hcl := hc.estimates G₂ s U hch hs hsA hU'
    have hodd : Odd G₂.blockSide := hG.1 ▸ hL
    have hs2 : ∀ i, 2 ≤ G₂.extent i := fun i => by
      show 2 ≤ 4 * m
      omega
    obtain ⟨w, hw, -, he⟩ := TopLevelSites.minimizingCoordinates_eq hodd hs2 (show c.ρA < Real.pi by linarith [Real.pi_gt_three]) le_rfl hcl.minimizer
    rw [he]
    by_cases hb : reflectedBond m b ∈ chordBonds (finiteCells G₂)
    · exact (hw.2.1 _ hb).trans (min_le_right _ _)
    · rw [hw.1 _ hb]
      simpa using hN
  · rw [if_neg hside]
    unfold minimizingBondCoordinate
    have hcl := hc.estimates G s V hG hs hsA hV
    have hodd : Odd G.blockSide := hG.1 ▸ hL
    obtain ⟨hFL, n, hn, hsd⟩ := hG
    have hs2 : ∀ i, 2 ≤ G.extent i := fun i => by rw [hsd i]; omega
    obtain ⟨w, hw, -, he⟩ := TopLevelSites.minimizingCoordinates_eq hodd hs2 (show c.ρA < Real.pi by linarith [Real.pi_gt_three]) le_rfl hcl.minimizer
    rw [he]
    by_cases hb : b ∈ chordBonds (finiteCells G)
    · exact (hw.2.1 _ hb).trans (min_le_right _ _)
    · rw [hw.1 _ hb]
      simpa using hN
end Frames
section Point
variable {R : StepSetup} {n : ℕ} [NeZero n]
private theorem potential_near_hessian_at_point (hMF : ReflectedFieldSmallCurvature) (hcov : BlocksCoverLowerLevel) (c : ColdChainParameters) (u : ℕ) (V : TorusField n)
    (hodd : Odd R.params.side) (h64 : 64 ≤ n) (hc : c.Admissible R.params.coupling R.params.side) (hρc : c.ρA = R.anchorRadius) (hρ1 : R.anchorRadius ≤ 1)
    (σ₀ σ' Cs C2 K₁ Kj : ℝ) (hσ₀ : 0 < σ₀) (hσ₀A : σ₀ ≤ c.σA) (hσ'0 : 0 < σ') (hσ'σ : σ' ≤ σ₀) (hK₁ : 0 ≤ K₁) (hKj : 0 ≤ Kj) (hC2 : 0 ≤ C2)
    (hRρ : 0 < R.ballRadius) (he₀L : c.N 0 * σ₀ + R.ballRadius ≤ 1 / (64 * (R.params.side : ℝ))) (he₀A : σ₀ + 8 * (c.N 0 * σ₀ + R.ballRadius) < c.σA)
    (hVlt : ∀ s : ℝ, σ' ≤ s → IsSmallCurvature s (readAtLevel (torusFrame R.params.side u n) (torusFrame R.params.side u n).top V))
    (hm : 16 ≤ R.frameReach) (hgap : frameDecayBound (frameBoundConstant c) c.δ₂ R.frameReach ≤ 2⁻¹ ^ 10 * σ')
    (hx0 : 0 < R.coupling)
    (hxs : R.coupling * (|Cs * frameBoundConstant c| * Real.exp (-(c.δ₂ / 4 * (R.frameReach : ℝ)))) ≤ 1)
    (hsl : ∀ (σ : ℝ) (m : ℕ) (F : BlockFrame) (V : F.GaugeField F.top), 0 < σ → σ ≤ σ' → 16 ≤ m →
      frameDecayBound (frameBoundConstant c) c.δ₂ m ≤ 2⁻¹ ^ 10 * σ → IsBlockTorus R.params.side F → IsSmallCurvature (5 / 4 * σ) V →
      ∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ b ∈ chordBonds (finiteCells F), ∀ e : imaginaryQuaternions,
        DifferentiableAt ℝ (energyAlongInterpolatedBond s R.params.coupling c.ρA m b e V) 0 ∧
        ContDiffThreeAlongBonds (interpolatedSlope s R.params.coupling c.ρA m b e) V ∧
        (‖e‖ = 1 → ∀ (k : ℕ) (e' : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions), k ≤ 3 → AreUnitVectors X →
          |bondDeriv (interpolatedSlope s R.params.coupling c.ρA m b e) V e' X| ≤
            Cs * frameDecayBound (frameBoundConstant c) c.δ₂ m * Real.exp (-(c.δ₂ / 8 * bondListDistance (enclosingCell b.1) e'))))
    (hEn : ∀ (F : BlockFrame) (V : F.GaugeField F.top) (w : F.Site F.depth → Fin 4 → imaginaryQuaternions), IsBlockTorus R.params.side F →
      (∀ ζ : StepVariable (finiteCells F), IsAdmissibleChartPoint R.params.side c.σA (shiftCoordinates w ζ) V → ContDiffAt ℝ 3 (chartedEnergyAt R.params.coupling w V) ζ) ∧
      ∀ η : StepVariable (finiteCells F), (∀ s : ℝ, 0 ≤ s → s ≤ 1 → IsAdmissibleChartPoint R.params.side c.σA (shiftCoordinates w (s • η)) V) →
        ∀ (b : ↥(chordBonds (finiteCells F))) (e : BondVector), ‖e‖ = 1 →
          |fderiv ℝ (chartedEnergyAt R.params.coupling w V) η (bondVariation b e) - fderiv ℝ (chartedEnergyAt R.params.coupling w V) 0 (bondVariation b e) -
              secondDerivAlong (chartedEnergyAt R.params.coupling w V) 0 (bondVariation b e) η| ≤
            C2 * (∑ b', Real.exp (-(c.δ₁ / 2 * chordBondDist F b b')) * ‖η b'‖) ^ 2)
    (hcost : ∀ k : BondField (ChartBondIndex R.params.side u n), (∀ b, ‖k b‖ < R.ballRadius) →
      ∑ Y : TorusSite n, (coldSettingOver R V).blockCostAt Y (chartFreeCoords R u V k) =
        chartedEnergyAt R.params.coupling (frameCoordField false R.params.coupling R.anchorRadius R.frameReach (readAtLevel (torusFrame R.params.side u n) (torusFrame R.params.side u n).top V))
          (readAtLevel (torusFrame R.params.side u n) (torusFrame R.params.side u n).top V) k)
    (hD : (coldSettingOver R V).IsPotentialPiece (coldSettingOver R V).totalDensity K₁)
    (hJ : (coldSettingOver R V).IsPotentialPiece
      (fun η => ∑ Y : TorusSite n, (coldSettingOver R V).logJacobian ((coldSettingOver R V).field η) η Y) Kj)
    (k : BondField (ChartBondIndex R.params.side u n)) (hk : ∀ b, ‖k b‖ < R.ballRadius) (j : Fin 3 × ChartBondIndex R.params.side u n) :
    |fderiv ℝ (chartPotential R u V) k (unitVariation j) -
        R.coupling * ∑ r : ChartBondIndex R.params.side u n × Fin 3,
          bondCoordinateHessian (chartedEnergyAt R.params.coupling (frameCoordField false R.params.coupling R.anchorRadius R.frameReach (readAtLevel (torusFrame R.params.side u n) (torusFrame R.params.side u n).top V))
            (readAtLevel (torusFrame R.params.side u n) (torusFrame R.params.side u n).top V)) (j.2, j.1) r * k r.1 r.2| ≤
      (1 + K₁ + Kj + C2) * (1 + R.coupling * (∑ b, Real.exp (-(c.δ₁ / 2 * chordBondDist (torusFrame R.params.side u n) j.2 b)) * ‖k b‖) ^ 2) := by
  have hCT : IsBlockTorus R.params.side (torusFrame R.params.side u n) := ⟨rfl, n, h64, fun _ => rfl⟩
  have hfs : ∀ b ∈ chordBonds (finiteCells (torusFrame R.params.side u n)),
      ‖frameCoordField false R.params.coupling R.anchorRadius R.frameReach (readAtLevel (torusFrame R.params.side u n) (torusFrame R.params.side u n).top V) b.1 b.2‖ ≤ c.N 0 * σ₀ := by
    intro b _
    have h := norm_bondFrameCoord_le hMF hodd hc (hρc.trans_le hρ1) hCT R.frameReach hm (readAtLevel (torusFrame R.params.side u n) (torusFrame R.params.side u n).top V) σ₀ hσ₀ hσ₀A (hVlt _ hσ'σ) b
    rw [hρc] at h
    exact h
  have hN0 : 0 < c.N 0 := hc.positivity.2.2.2.2.2.1 0
  have he₀0 : 0 ≤ c.N 0 * σ₀ + R.ballRadius := by positivity
  have hpt : ∀ ζ : StepVariable (finiteCells (torusFrame R.params.side u n)), (∀ b, ‖ζ b‖ ≤ R.ballRadius) →
      IsAdmissibleChartPoint R.params.side c.σA (shiftCoordinates (frameCoordField false R.params.coupling R.anchorRadius R.frameReach (readAtLevel (torusFrame R.params.side u n) (torusFrame R.params.side u n).top V)) ζ)
        (readAtLevel (torusFrame R.params.side u n) (torusFrame R.params.side u n).top V) := by
    intro ζ hζ
    refine isAdmissibleChartPoint_of_small hcov hCT hodd he₀0 he₀L hσ₀.le he₀A _ _ (fun b hb => ?_) (hVlt _ hσ'σ)
    have e1 : stepCoordinates ζ b.1 b.2 = toImaginary (ζ ⟨b, hb⟩) := by
      unfold stepCoordinates
      rw [dif_pos hb]
    show ‖frameCoordField false R.params.coupling R.anchorRadius R.frameReach (readAtLevel (torusFrame R.params.side u n) (torusFrame R.params.side u n).top V) b.1 b.2 + stepCoordinates ζ b.1 b.2‖ ≤ _
    rw [e1]
    refine (norm_add_le _ _).trans ?_
    rw [norm_toImaginary]
    exact add_le_add (hfs b hb) (hζ _)
  obtain ⟨hsm, h2o⟩ := hEn (torusFrame R.params.side u n) (readAtLevel (torusFrame R.params.side u n) (torusFrame R.params.side u n).top V)
    (frameCoordField false R.params.coupling R.anchorRadius R.frameReach (readAtLevel (torusFrame R.params.side u n) (torusFrame R.params.side u n).top V)) hCT
  have hd0 := (hsm 0 (hpt 0 fun b => by simpa using hRρ.le)).differentiableAt (by norm_num)
  have hδ₂ : 0 < c.δ₂ := hc.classical.1.2.2.2.1
  have h0 : ∀ (b : ChartBondIndex R.params.side u n) (e : BondVector), ‖e‖ = 1 →
      R.coupling * |fderiv ℝ (chartedEnergyAt R.params.coupling (frameCoordField false R.params.coupling R.anchorRadius R.frameReach (readAtLevel (torusFrame R.params.side u n) (torusFrame R.params.side u n).top V))
        (readAtLevel (torusFrame R.params.side u n) (torusFrame R.params.side u n).top V)) 0 (bondVariation b e)| ≤ 1 := by
    intro b e he
    have hunit : ‖toImaginary e‖ = 1 := by rw [norm_toImaginary, he]
    have hs3 := (hsl σ' R.frameReach (torusFrame R.params.side u n) (readAtLevel (torusFrame R.params.side u n) (torusFrame R.params.side u n).top V) hσ'0 le_rfl hm hgap hCT
      (hVlt _ (by linarith)) 1 ⟨zero_le_one, le_rfl⟩ b.1 b.2 (toImaginary e)).2.2 hunit
    have hs4 : ∀ (s : Fin 0 → (torusFrame R.params.side u n).Site (torusFrame R.params.side u n).top × Fin 4) (X : Fin 0 → imaginaryQuaternions),
        |bondDeriv (interpolatedSlope 1 R.params.coupling R.anchorRadius R.frameReach b.1 (toImaginary e)) (readAtLevel (torusFrame R.params.side u n) (torusFrame R.params.side u n).top V) s X| ≤
          |Cs * frameBoundConstant c| * Real.exp (-(c.δ₂ / 4 * (R.frameReach : ℝ))) := by
      intro s X
      have h1 := hs3 0 s X (by omega) (fun l => l.elim0)
      rw [hρc] at h1
      refine h1.trans ?_
      have hE1 : Real.exp (-(c.δ₂ / 8 * (bondListDistance (enclosingCell b.1.1) s : ℝ))) ≤ 1 := by
        rw [Real.exp_le_one_iff]
        have : 0 ≤ c.δ₂ / 8 * (bondListDistance (enclosingCell b.1.1) s : ℝ) := by positivity
        linarith
      unfold frameDecayBound
      have hE0 : 0 < Real.exp (-(c.δ₂ / 4 * (R.frameReach : ℝ))) := Real.exp_pos _
      calc _ ≤ |Cs * frameBoundConstant c| * Real.exp (-(c.δ₂ / 4 * (R.frameReach : ℝ))) *
              Real.exp (-(c.δ₂ / 8 * (bondListDistance (enclosingCell b.1.1) s : ℝ))) := by
            refine mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le
            rw [← mul_assoc]
            exact mul_le_mul_of_nonneg_right (le_abs_self _) hE0.le
        _ ≤ _ := by
            have : 0 ≤ |Cs * frameBoundConstant c| * Real.exp (-(c.δ₂ / 4 * (R.frameReach : ℝ))) := by positivity
            nlinarith
    have hs5 := abs_chartedSlope_le_of_interpolated b (toImaginary e) hs4
    rw [chartedSlope_eq_fderiv _ _ _ b e hd0] at hs5
    exact (mul_le_mul_of_nonneg_left hs5 hx0.le).trans hxs
  have hball : ∀ k : BondField (ChartBondIndex R.params.side u n), (∀ b, ‖k b‖ < R.ballRadius) →
      ∀ s : ℝ, 0 ≤ s → s ≤ 1 → ∀ b, ‖(s • k) b‖ ≤ R.ballRadius := by
    intro k hk s h0 h1 b
    have h2 : ‖k b‖ ≤ R.ballRadius := (hk b).le
    rw [Pi.smul_apply, norm_smul, Real.norm_eq_abs, abs_of_nonneg h0]
    have h3 := norm_nonneg (k b)
    nlinarith
  exact potential_near_hessian_core u V hodd (by omega) _
    (fun b b' => Real.exp (-(c.δ₁ / 2 * chordBondDist (torusFrame R.params.side u n) b b'))) K₁ Kj C2 hK₁ hKj hC2 hx0.le
    hcost hD hJ
    (fun k hk => (hsm k (hpt k fun b => (hk b).le)).differentiableAt (by norm_num))
    (fun k hk b e he => h2o k (fun s h0 h1 => hpt _ (hball k hk s h0 h1)) b e he)
    h0 k hk j
end Point
end PotentialNearHessian
open PotentialNearHessian in
set_option maxHeartbeats 1000000 in
theorem goodStatePotentialNearHessian (hE2 : chartEnergySecondOrderStatement)
    (hCost : coldSettingChartCostStatement) (hCutS : goodConfigCutoffStatement) (hWin : scaleWindowStatement)
    (hConf : ClusterExpansionOfAStep.GasConfigIsAdmissibleSetting) (hDen : totalDensityPieceBound)
    (hLog : ClusterExpansionOfAStep.LogJacobianIsPotentialPiece) (hSlope : interpolatedSlopeBounds)
    (hMF : ReflectedFieldSmallCurvature) (hcov : BlocksCoverLowerLevel) :
    goodStatePotentialNearHessianStatement := by
  unfold goodConfigCutoffStatement ForAllPoints at hCutS
  unfold scaleWindowStatement ForAllPoints at hWin
  unfold goodStatePotentialNearHessianStatement ForAllPoints
  refine params_mono (params_and (params_family hConf hDen hLog hCost) (params_and hCutS hWin)) ?_
  rintro Λ ⟨⟨hD, hCS, Cd, cd, Kj, hCd, hcd, hKj, hB, hy0, hParts, hSet, hCst⟩, ⟨_, _, Xc, _, hyc, hcutS⟩, ⟨Cw, _, Xw, _, _, hwin⟩⟩
  obtain ⟨c, nss, hties, -⟩ := hCS
  obtain ⟨t1, -, t3, t4, -, t6, -, hc⟩ := hties
  obtain ⟨C2, hC2, hEn⟩ := hE2 Λ.stepParams.coupling Λ.stepParams.side c hD.a_ge hD.L_odd hD.L_ge hc
  obtain ⟨Cs, σ₁, hCs1, hσ₁, hsl⟩ := hSlope Λ.stepParams.coupling Λ.stepParams.side c hD.a_ge hD.L_odd hD.L_ge hc
  have hσ : 0 < Λ.table.threshold := hD.σ_pos
  have hδ₂ : 0 < c.δ₂ := hc.classical.1.2.2.2.1
  obtain ⟨σ', hσ'd⟩ : ∃ σ' : ℝ, σ' = min σ₁ Λ.table.threshold := ⟨_, rfl⟩
  have hσ'0 : 0 < σ' := by rw [hσ'd]; exact lt_min hσ₁ hσ
  have hσ'1 : σ' ≤ σ₁ := by rw [hσ'd]; exact min_le_left _ _
  have hσ'σ : σ' ≤ Λ.table.threshold := by rw [hσ'd]; exact min_le_right _ _
  obtain ⟨Xa, hXa1, hXa⟩ := range_bounds Cd cd |Cs * frameBoundConstant c| c.δ₂ 1 hcd hδ₂ one_pos (abs_nonneg _)
  obtain ⟨Xb, hXb1, hXb⟩ := range_bounds Cd cd |frameBoundConstant c| c.δ₂ (2⁻¹ ^ 10 * σ') hcd hδ₂ (by positivity) (abs_nonneg _)
  obtain ⟨cn, hcn⟩ : ∃ cn : ℝ, cn = |Cw 0| := ⟨_, rfl⟩
  obtain ⟨K₁, hK₁d⟩ : ∃ K₁ : ℝ, K₁ = |Cd * (1 + Λ.table.E₃)| + 1 := ⟨_, rfl⟩
  have hK₁ : 0 ≤ K₁ := by rw [hK₁d]; positivity
  refine ⟨fun _ => 1 + K₁ + Kj + C2, 1, max (max (max (2 * Xa) (2 * Xb)) (max Xc Xw)) (max (max 2 (16 * cn ^ 2)) ((64 / (8 / 9 * σ') + 1) ^ 4)),
    one_pos, le_trans hyc (le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_max_left _ _))), ?_⟩
  intro S hx d n _ hd hn V Y hg k hk j
  have hxA : 2 * Xa ≤ S.scaleCoupling := le_trans (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) (le_max_left _ _)) hx
  have hxB : 2 * Xb ≤ S.scaleCoupling := le_trans (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) (le_max_left _ _)) hx
  have hxc : Xc ≤ S.scaleCoupling := le_trans (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_max_left _ _)) hx
  have hxw : Xw ≤ S.scaleCoupling := le_trans (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) (le_max_left _ _)) hx
  have hx2 : 2 ≤ S.scaleCoupling := le_trans (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) (le_max_right _ _)) hx
  have hxn : 16 * cn ^ 2 ≤ S.scaleCoupling := le_trans (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) (le_max_right _ _)) hx
  have hx64 : (64 / (8 / 9 * σ') + 1) ^ 4 ≤ S.scaleCoupling := le_trans (le_max_right _ _) (le_trans (le_max_right _ _) hx)
  have hx0 : 0 < S.scaleCoupling := by linarith
  obtain ⟨-, -, -, -, -, hKle, hwn⟩ := hwin S hxw
  have hnear := (hwn (S.lastSeparated + d) (by omega) (by omega)).1
  have hcn0 : 0 ≤ cn := by rw [hcn]; exact abs_nonneg _
  have hlog0 : 0 ≤ Real.log S.scaleCoupling := Real.log_nonneg (by linarith)
  have hnear' : |S.coupling (S.lastSeparated + d) - S.scaleCoupling| ≤ cn * Real.log S.scaleCoupling := by
    rw [hcn]
    exact le_trans hnear (mul_le_mul_of_nonneg_right (le_abs_self _) hlog0)
  have hhalf : S.scaleCoupling / 2 ≤ S.coupling (S.lastSeparated + d) := half_le_of_near hx2 hcn0 hxn hnear'
  have hK : S.lastSeparated + d ≤ S.data.windowLevel := by omega
  have hstand : StageOnFlow Λ.table Λ.response Λ.floor S.β (S.lastSeparated + d) ⟨S.tower.stage (S.lastSeparated + d), S.resp (S.lastSeparated + d)⟩ := by
    have h := S.onFlow (S.lastSeparated + d) hK
    rwa [← S.stage_eq (S.lastSeparated + d) hK] at h
  have hon : (S.tower.stage (S.lastSeparated + d)).toStepSetup.OnParameters Λ.table Λ.floor := hstand.onFamily.onFamily
  have hmv : |(S.tower.stage (S.lastSeparated + d)).toStepSetup.nextCoupling - (S.tower.stage (S.lastSeparated + d)).toStepSetup.coupling| ≤ 2 * Λ.table.B := hstand.onFamily.abs_sub_le
  have hxx : (S.tower.stage (S.lastSeparated + d)).toStepSetup.nextCoupling ≤ 1.01 * (S.tower.stage (S.lastSeparated + d)).toStepSetup.coupling := by
    have h1 := (abs_le.mp hmv).2
    have h2 := hon.le_coupling
    linarith only [h1, h2, hB, hy0]
  have hRx : (S.tower.stage (S.lastSeparated + d)).toStepSetup.coupling = S.coupling (S.lastSeparated + d) := hstand.coupling_eq
  have hRt : S.lastSeparated + d = (S.tower.stage (S.lastSeparated + d)).toStepSetup.depth := hstand.depth_eq.symm
  have hρA : (S.tower.stage (S.lastSeparated + d)).toStepSetup.anchorRadius = Λ.table.ρA := hon.anchorRadius_eq
  have hLge : 2 ^ 40 ≤ Λ.stepParams.side := hD.L_ge
  have hside : Λ.table.n₀ ≤ n := by
    have h1 : Λ.stepParams.side * Λ.stepParams.n₀ ≤ S.data.period Λ.stepParams.side := S.side_le
    have h2 : S.data.period Λ.stepParams.side ≤ n := by
      rw [hn]
      exact Nat.le_mul_of_pos_right _ (Nat.pow_pos (by omega))
    have h3 : Λ.stepParams.n₀ ≤ Λ.stepParams.side * Λ.stepParams.n₀ := Nat.le_mul_of_pos_left _ (by omega)
    exact h3.trans (h1.trans h2)
  have hn₀ : 4096 ≤ Λ.table.n₀ := hD.n₀_ge
  have h64 : 64 ≤ n := by omega
  have hcold' : ∀ (z : TorusSite n) (μ ν : Fin 4), μ < ν → curvature (S.smoothedField (S.lastSeparated + d + 1) n V) z μ ν < σ' := by
    intro z μ ν hμ
    obtain ⟨-, -, h3, -⟩ := hcutS S hxc (S.lastSeparated + d + 1) (by omega) (by omega) n hn V Y hg
    have h4 := h3 1 zero_le_one le_rfl z μ ν hμ
    have h5 := small_number S.scaleCoupling (8 / 9 * σ') (by positivity) hx64
    have h6 := hg.curvature_le
    have h7 : 9 / 8 * (8 / 9 * σ') = σ' := by ring
    rw [h7] at h5
    exact lt_of_le_of_lt (h4.trans (by linarith only [h6])) h5
  have hcold : TorusFields.IsCold (9 / 8 * Λ.stepParams.threshold) (S.smoothedField (S.lastSeparated + d + 1) n V) := by
    intro z μ ν hμ
    have h1 := hcold' z μ ν hμ
    have h2 : σ' ≤ Λ.stepParams.threshold := hσ'σ
    have h3 : 0 < Λ.stepParams.threshold := hσ
    linarith
  have hgr : (coldGroundOver (S.tower.stage (S.lastSeparated + d)).toStepSetup (S.smoothedField (S.lastSeparated + d + 1) n V)).IsAdmissibleGround :=
    Or.inl ⟨hside, hcold, rfl, rfl, rfl⟩
  have hset : (coldSettingOver (S.tower.stage (S.lastSeparated + d)).toStepSetup (S.smoothedField (S.lastSeparated + d + 1) n V)).IsAdmissible := by
    have h := hSet _ hon hxx n _ hgr (GasGround.allVacant _) (fun i j _ => GasGround.pairConstraint _ |>.vacant_compatible i j _)
    have e : (coldGroundOver (S.tower.stage (S.lastSeparated + d)).toStepSetup (S.smoothedField (S.lastSeparated + d + 1) n V)).settingOf
        ((coldGroundOver (S.tower.stage (S.lastSeparated + d)).toStepSetup (S.smoothedField (S.lastSeparated + d + 1) n V)).familyOf (GasGround.allVacant _)) =
        (coldGroundOver (S.tower.stage (S.lastSeparated + d)).toStepSetup (S.smoothedField (S.lastSeparated + d + 1) n V)).groundSetting := settingOf_allVacant _
    rwa [e] at h
  obtain ⟨hPD, hPJ⟩ := hParts _ hon n hside _ hset
  have hxa : Xa ≤ (S.tower.stage (S.lastSeparated + d)).toStepSetup.coupling := by rw [hRx]; linarith
  have hxb : Xb ≤ (S.tower.stage (S.lastSeparated + d)).toStepSetup.coupling := by rw [hRx]; linarith
  have hRx0 : 0 < (S.tower.stage (S.lastSeparated + d)).toStepSetup.coupling := by linarith
  obtain ⟨hA1, hA2, -, hA4⟩ := hXa _ hxa
  obtain ⟨-, -, hB3, -⟩ := hXb _ hxb
  have hPD' : (coldSettingOver (S.tower.stage (S.lastSeparated + d)).toStepSetup (S.smoothedField (S.lastSeparated + d + 1) n V)).IsPotentialPiece (coldSettingOver (S.tower.stage (S.lastSeparated + d)).toStepSetup (S.smoothedField (S.lastSeparated + d + 1) n V)).totalDensity K₁ := by
    rw [hK₁d]
    exact hPD.mono (add_le_add (le_abs_self _) hA1)
  have hpT : ∀ i, (torusFrame Λ.stepParams.side (S.lastSeparated + d) n).period (torusFrame Λ.stepParams.side (S.lastSeparated + d) n).top i = n := TopLevelSites.period_top_of_extent (fun _ => rfl)
  have hVlt : ∀ s : ℝ, σ' ≤ s → IsSmallCurvature s (readAtLevel (torusFrame Λ.stepParams.side (S.lastSeparated + d) n) (torusFrame Λ.stepParams.side (S.lastSeparated + d) n).top (S.smoothedField (S.lastSeparated + d + 1) n V)) := by
    intro s hs p hp
    obtain ⟨z, μ, ν⟩ := p
    rw [TopLevelSites.plaquetteDefect_readAtLevel_eq hpT]
    exact lt_of_lt_of_le (hcold' _ μ ν hp) hs
  have hρ1 : Λ.table.ρA ≤ 1 := hD.chain.2.2.2.2.1
  have hσA : Λ.table.threshold ≤ c.σA := by
    have := hD.σ_le
    rw [t4]
    linarith
  have hN0 : 0 < c.N 0 := hc.positivity.2.2.2.2.2.1 0
  have hρT : (S.tower.stage (S.lastSeparated + d)).toStepSetup.ballRadius = Λ.table.threshold / 64 := rfl
  have hLp : (0 : ℝ) < Λ.table.side := by
    have : 0 < Λ.table.side := by have := hD.L_ge; omega
    exact_mod_cast this
  have he₀L : c.N 0 * Λ.table.threshold + (S.tower.stage (S.lastSeparated + d)).toStepSetup.ballRadius ≤ 1 / (64 * ((S.tower.stage (S.lastSeparated + d)).toStepSetup.params.side : ℝ)) := by
    have h1 := hD.σ_L
    rw [← t6] at h1
    show _ ≤ 1 / (64 * (Λ.table.side : ℝ))
    rw [le_div_iff₀ (by positivity), hρT]
    have h2 : 0 < (Λ.table.side : ℝ) * Λ.table.threshold := mul_pos hLp hσ
    nlinarith [mul_pos h2 hN0]
  have he₀A : Λ.table.threshold + 8 * (c.N 0 * Λ.table.threshold + (S.tower.stage (S.lastSeparated + d)).toStepSetup.ballRadius) < c.σA := by
    have h1 := hD.cold_le
    rw [← t6, ← t4] at h1
    have hρ2 : Λ.table.ballRadius = Λ.table.threshold / 64 := rfl
    rw [hρ2] at h1
    rw [hρT]
    linarith
  have hcostE := hCst _ hon n hside (S.smoothedField (S.lastSeparated + d + 1) n V) hcold (S.lastSeparated + d) hRt
  have hρc : c.ρA = (S.tower.stage (S.lastSeparated + d)).toStepSetup.anchorRadius := t3.trans hρA.symm
  have hgap : frameDecayBound (frameBoundConstant c) c.δ₂ (S.tower.stage (S.lastSeparated + d)).toStepSetup.frameReach ≤ 2⁻¹ ^ 10 * σ' := by
    unfold frameDecayBound
    exact (mul_le_mul_of_nonneg_right (le_abs_self _) (Real.exp_pos _).le).trans hB3
  have hfin := potential_near_hessian_at_point (R := (S.tower.stage (S.lastSeparated + d)).toStepSetup) hMF hcov c (S.lastSeparated + d) (S.smoothedField (S.lastSeparated + d + 1) n V) hD.L_odd h64 hc hρc (hρA.trans_le hρ1) Λ.table.threshold σ' Cs C2 K₁ Kj hσ hσA hσ'0 hσ'σ hK₁ hKj.le hC2.le
    (show 0 < Λ.table.threshold / 64 by positivity) he₀L he₀A hVlt hA2 hgap hRx0 hA4
    (fun σ m F V' h0 h1 => hsl σ m F V' h0 (h1.trans hσ'1)) hEn hcostE hPD' hPJ k hk j
  rw [hRx, hρA, t1] at hfin
  exact hfin
end YangMills.Construction.MomentLaw
end
