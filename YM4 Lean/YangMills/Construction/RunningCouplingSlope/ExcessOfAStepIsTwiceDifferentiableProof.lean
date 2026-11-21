import YangMills.Construction.ClusterExpansionOfAStep.AdmissionEqualInBoxes
import YangMills.Construction.ClusterExpansionOfAStep.LocalLogarithmOfTheGroup
import YangMills.Construction.ColdStepAtMirrorFrames.LeastActionAcrossFrames
import YangMills.Construction.RunningCouplingSlope.ExcessOfAStepIsTwiceDifferentiable
import YangMills.Construction.RunningCouplingSlope.LeastPointReadsTheChainProof
import Mathlib
set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
open Filter
open scoped Topology Quaternion
noncomputable section
namespace YangMills.Construction.RunningCouplingSlope
open BlockAverages ColdStepAtMirrorFrames TorusFields QuaternionLog SlopeCoefficient Conventions
namespace ExcessEnergyContDiff
section Families
variable {Y : Type} [NormedAddCommGroup Y] [NormedSpace ℝ Y] {y₀ : Y}
private def quatStarCLM : ℍ[ℝ] →L[ℝ] ℍ[ℝ] := LinearMap.toContinuousLinearMap
  { toFun := star
    map_add' := star_add
    map_smul' := fun c q => by simp [Quaternion.star_smul] }
private def quatReCLM : ℍ[ℝ] →L[ℝ] ℝ := LinearMap.toContinuousLinearMap
  { toFun := fun q => q.re
    map_add' := fun p q => by simp
    map_smul' := fun c q => by simp }
private theorem contDiffAt_inv_family {g : Y → UnitQuaternion}
    (h : ContDiffAt ℝ 2 (fun y => ((g y : UnitQuaternion) : ℍ[ℝ])) y₀) :
    ContDiffAt ℝ 2 (fun y => (((g y)⁻¹ : UnitQuaternion) : ℍ[ℝ])) y₀ :=
  (quatStarCLM.contDiff.contDiffAt.comp y₀ h :
    ContDiffAt ℝ 2 (quatStarCLM ∘ fun y => ((g y : UnitQuaternion) : ℍ[ℝ])) y₀)
private theorem contDiffAt_pathHolonomy_family {F : BlockFrame} {j : ℕ} {Z : Y → F.GaugeField j}
    (hZ : ∀ x i, ContDiffAt ℝ 2 (fun y => ((Z y x i : UnitQuaternion) : ℍ[ℝ])) y₀)
    (x : F.Site j) (l : List PathStep) :
    ContDiffAt ℝ 2 (fun y => ((pathHolonomy (Z y) x l : UnitQuaternion) : ℍ[ℝ])) y₀ := by
  induction l generalizing x with
  | nil => exact contDiffAt_const
  | cons st r ih =>
    have h1 : ContDiffAt ℝ 2 (fun y => ((linkValue (Z y) x st : UnitQuaternion) : ℍ[ℝ])) y₀ := by
      unfold linkValue
      by_cases hs : st.2 = true
      · simp only [hs, if_true]
        exact hZ _ _
      · simp only [hs, Bool.false_eq_true, if_false]
        exact contDiffAt_inv_family (hZ _ _)
    exact h1.mul (ih _)
private theorem contDiffAt_contourAverage_family {F : BlockFrame} {j : ℕ} {Z : Y → F.GaugeField j}
    (hZ : ∀ x i, ContDiffAt ℝ 2 (fun y => ((Z y x i : UnitQuaternion) : ℍ[ℝ])) y₀)
    (c : F.Site (j + 1) × Fin 4) :
    ContDiffAt ℝ 2 (fun y => _root_.YangMills.Construction.BlockAverages.contourAverage (Z y) c) y₀ := by
  unfold _root_.YangMills.Construction.BlockAverages.contourAverage
  exact ContDiffAt.const_smul _
    (ContDiffAt.sum fun h _ => ContDiffAt.sum fun π _ => contDiffAt_pathHolonomy_family hZ _ _)
private theorem contDiffAt_re_family {f : Y → ℍ[ℝ]} (h : ContDiffAt ℝ 2 f y₀) :
    ContDiffAt ℝ 2 (fun y => (f y).re) y₀ :=
  (quatReCLM.contDiff.contDiffAt.comp y₀ h : ContDiffAt ℝ 2 (quatReCLM ∘ f) y₀)
private theorem contDiffAt_blockFit_family {F : BlockFrame} {j : ℕ} {Z : Y → F.GaugeField j}
    {Z' : Y → F.GaugeField (j + 1)}
    (hZ : ∀ x i, ContDiffAt ℝ 2 (fun y => ((Z y x i : UnitQuaternion) : ℍ[ℝ])) y₀)
    (hZ' : ∀ x i, ContDiffAt ℝ 2 (fun y => ((Z' y x i : UnitQuaternion) : ℍ[ℝ])) y₀)
    (c : F.Site (j + 1) × Fin 4) (h0 : _root_.YangMills.Construction.BlockAverages.contourAverage (Z y₀) c ≠ 0) :
    ContDiffAt ℝ 2 (fun y => blockFit (Z y) (Z' y) c) y₀ := by
  unfold blockFit
  have hm := contDiffAt_contourAverage_family hZ c
  exact (hm.norm ℝ h0).sub (contDiffAt_re_family (hm.mul (contDiffAt_inv_family (hZ' _ _))))
private theorem contDiffAt_wilsonAction_family {F : BlockFrame} (S : Finset F.Cell)
    {Z : Y → F.GaugeField 0}
    (hZ : ∀ x i, ContDiffAt ℝ 2 (fun y => ((Z y x i : UnitQuaternion) : ℍ[ℝ])) y₀) :
    ContDiffAt ℝ 2 (fun y => BlockAverages.wilsonAction S (Z y)) y₀ := by
  unfold BlockAverages.wilsonAction
  refine ContDiffAt.sum fun p _ => contDiffAt_const.sub (contDiffAt_re_family ?_)
  exact contDiffAt_pathHolonomy_family hZ _ _
private theorem contDiffAt_analytic_family {F : BlockFrame} [Finite F.Cell]
    {G : F.GaugeField F.top → ℝ} {V : F.GaugeField F.top}
    (hG : IsBondAnalyticAt G V) {Z : Y → F.GaugeField F.top} (h0 : Z y₀ = V)
    (hZ : ∀ x i, ContDiffAt ℝ 2 (fun y => ((Z y x i : UnitQuaternion) : ℍ[ℝ])) y₀) :
    ContDiffAt ℝ 2 (fun y => G (Z y)) y₀ := by
  classical
  let b := Module.finBasis ℝ imaginaryQuaternions
  let D := Module.finrank ℝ imaginaryQuaternions
  let B := F.Cell × Fin 4
  let _ : Fintype B := Fintype.ofFinite B
  obtain ⟨k, ⟨e⟩⟩ := Finite.exists_equiv_fin (B × Fin D)
  let c : Fin k → F.Site F.top × Fin 4 := fun l => (e.symm l).1
  let X : Fin k → imaginaryQuaternions := fun l => b (e.symm l).2
  let q : B → Y → ℍ[ℝ] := fun p y => ((Z y p.1 p.2 * (V p.1 p.2)⁻¹ : UnitQuaternion) : ℍ[ℝ])
  let w : B → Y → imaginaryQuaternions := fun p y => logNearOne (q p y)
  have hq : ∀ p, ContDiffAt ℝ 2 (q p) y₀ := fun p =>
    (hZ p.1 p.2).mul contDiffAt_const
  have hq0 : ∀ p, q p y₀ = 1 := fun p => by
    show ((Z y₀ p.1 p.2 * (V p.1 p.2)⁻¹ : UnitQuaternion) : ℍ[ℝ]) = 1
    rw [h0, mul_inv_cancel]
    rfl
  have hw : ∀ p, ContDiffAt ℝ 2 (w p) y₀ := fun p => by
    have h1 : ContDiffAt ℝ 2 logNearOne (q p y₀) := by
      rw [hq0]
      exact contDiffAt_logNearOne.of_le (by norm_num)
    exact h1.comp y₀ (hq p)
  have hw0 : ∀ p, w p y₀ = 0 := fun p => by
    show logNearOne (q p y₀) = 0
    rw [hq0, logNearOne_one]
  let co : Fin D → imaginaryQuaternions →L[ℝ] ℝ := fun d => LinearMap.toContinuousLinearMap (b.coord d)
  let σ : Y → Fin k → ℝ := fun y l => co (e.symm l).2 (w (e.symm l).1 y)
  have hσ : ContDiffAt ℝ 2 σ y₀ := by
    refine contDiffAt_pi.2 fun l => ?_
    exact (co (e.symm l).2).contDiff.contDiffAt.comp y₀ (hw _)
  have hσ0 : σ y₀ = 0 := by
    funext l
    show co (e.symm l).2 (w (e.symm l).1 y₀) = 0
    rw [hw0, map_zero]
  have hspread : ∀ y x i, BlockAverages.bondSpread c X (σ y) x i = w (x, i) y := by
    intro y x i
    unfold BlockAverages.bondSpread
    have e1 : (∑ l : Fin k, if c l = (x, i) then σ y l • X l else 0) =
        ∑ r : B × Fin D, if r.1 = (x, i) then co r.2 (w r.1 y) • b r.2 else 0 := by
      refine Fintype.sum_equiv e.symm _ _ fun l => ?_
      rfl
    rw [e1, Fintype.sum_prod_type, Finset.sum_eq_single ((x, i) : B)]
    · simp only [if_true]
      exact b.sum_repr (w (x, i) y)
    · intro p _ hp
      exact Finset.sum_eq_zero fun d _ => if_neg hp
    · intro hp
      exact absurd (Finset.mem_univ _) hp
  have hnear : ∀ᶠ y in 𝓝 y₀, ∀ p : B,
      NormedSpace.exp ((w p y : imaginaryQuaternions) : ℍ[ℝ]) = q p y := by
    refine eventually_all.2 fun p => ?_
    have ht : Tendsto (q p) (𝓝 y₀) (𝓝 1) := by
      have := (hq p).continuousAt.tendsto
      rwa [hq0] at this
    filter_upwards [ht.eventually exp_logNearOne] with y hy
    exact hy (norm_unitQuaternion _)
  have heq : (fun y => G (Z y)) =ᶠ[𝓝 y₀] fun y => G (rotatedField (BlockAverages.bondSpread c X (σ y)) V) := by
    filter_upwards [hnear] with y hy
    congr 1
    funext x i
    show Z y x i = expUnit (BlockAverages.bondSpread c X (σ y) x i) * V x i
    rw [hspread]
    have h1 : expUnit (w (x, i) y) = Z y x i * (V x i)⁻¹ := Subtype.ext (hy (x, i))
    rw [h1, inv_mul_cancel_right]
  have hH : ContDiffAt ℝ 2 (fun τ : Fin k → ℝ => G (rotatedField (BlockAverages.bondSpread c X τ) V)) (σ y₀) := by
    rw [hσ0]
    exact (hG k c X).contDiffAt
  exact (hH.comp y₀ hσ).congr_of_eventuallyEq heq
end Families
private theorem intCast_zmod_cast_congr {p q : ℕ} (h : p = q) (z : ℤ) :
    ((((z : ZMod p)).cast : ℤ) : ZMod q) = (z : ZMod q) := by apply _root_.YangMills.Construction.FrameTorusAction.intCast_cast_intCast <;> assumption
private theorem torusFrame_period_depth (L t m : ℕ) (k : Fin 4) :
    (torusFrame L t m).period (torusFrame L t m).depth k = m * L := by apply _root_.YangMills.Construction.CongruentAdmission.torusFrame_period_depth <;> assumption
private theorem stepMinimizer_readAtLevel (a ρ : ℝ) (L t m : ℕ) (V : TorusField m) :
    stepMinimizer (F := torusFrame L t m) a ρ (readAtLevel (torusFrame L t m) (torusFrame L t m).top V) =
      readAtLevel (torusFrame L t m) (torusFrame L t m).depth (minimizerOnFinerTorus a ρ L t m V) := by
  funext x i
  show _ = fieldAboveFrame (F := torusFrame L t m) true a ρ 0
    (readAtLevel (torusFrame L t m) (torusFrame L t m).top V) 0
    (siteOfCoords (torusFrame L t m).depth fun k => ((((siteCoords x k : ℤ) : ZMod (m * L))).cast : ℤ)) i
  congr 1
  funext k
  show x k = ((((((siteCoords x k : ℤ) : ZMod (m * L))).cast : ℤ)) :
    ZMod ((torusFrame L t m).period (torusFrame L t m).depth k))
  rw [intCast_zmod_cast_congr (torusFrame_period_depth L t m k).symm]
  simp [siteCoords]
private theorem continuous_pathHolonomy_readAtLevel {F : BlockFrame} {j m : ℕ} (x : F.Site j)
    (l : List PathStep) :
    Continuous fun V : TorusField m => pathHolonomy (readAtLevel F j V) x l := by apply _root_.YangMills.SharedProofs.p11593 <;> assumption
private theorem pathHolonomy_trivial {F : BlockFrame} {j : ℕ} (x : F.Site j) (l : List PathStep) :
    pathHolonomy (fun _ _ => (1 : UnitQuaternion) : F.GaugeField j) x l = 1 := by apply _root_.YangMills.SharedProofs.p3325 <;> assumption
private theorem eventually_contourAverage_ne_zero {F : BlockFrame} {j m : ℕ} (hL : 0 < F.blockSide)
    (c : F.Site (j + 1) × Fin 4) :
    ∀ᶠ U in 𝓝 (trivialField m), _root_.YangMills.Construction.BlockAverages.contourAverage (readAtLevel F j U) c ≠ 0 := by
  have hcont : Continuous fun U : TorusField m => _root_.YangMills.Construction.BlockAverages.contourAverage (readAtLevel F j U) c := by
    have h1 : ∀ (h : Fin 4 → ℤ) (π : Equiv.Perm (Fin 4)), Continuous fun U : TorusField m =>
        ((pathHolonomy (readAtLevel F j U) (_root_.YangMills.Construction.BlockAverages.refineSite c.1) (bondContour F.blockSide h π c.2) :
          UnitQuaternion) : ℍ[ℝ]) :=
      fun h π => continuous_subtype_val.comp (continuous_pathHolonomy_readAtLevel _ _)
    unfold _root_.YangMills.Construction.BlockAverages.contourAverage
    exact Continuous.const_smul (c := (1 / (24 * (F.blockSide : ℝ) ^ 4)))
      (continuous_finsetSum _ fun h _ => continuous_finsetSum _ fun π _ => h1 h π)
  refine hcont.continuousAt.eventually_ne ?_
  have htriv : readAtLevel F j (trivialField m) = fun _ _ => (1 : UnitQuaternion) := rfl
  have hne : (centredCube F.blockSide).Nonempty := by
    refine ⟨0, ?_⟩
    unfold centredCube
    rw [Fintype.mem_piFinset]
    intro i
    simp only [Pi.zero_apply, Finset.mem_Icc]
    have : (0 : ℤ) ≤ ((F.blockSide : ℤ) - 1) / 2 := by
      have : (1 : ℤ) ≤ F.blockSide := by exact_mod_cast hL
      omega
    omega
  have hS : ∑ h ∈ centredCube F.blockSide, ∑ π : Equiv.Perm (Fin 4), ((1 : UnitQuaternion) : ℍ[ℝ]) =
      (((centredCube F.blockSide).card : ℝ) * (24 : ℝ)) • (1 : ℍ[ℝ]) := by
    rw [Finset.sum_const, Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin,
      ← Nat.cast_smul_eq_nsmul ℝ, ← Nat.cast_smul_eq_nsmul ℝ, smul_smul]
    simp [Nat.factorial]
  simp only [_root_.YangMills.Construction.BlockAverages.contourAverage, htriv, pathHolonomy_trivial]
  rw [hS, smul_smul]
  refine smul_ne_zero ?_ one_ne_zero
  positivity
private theorem finite_torusFrame_cell {L t m : ℕ} (hm : 0 < m) : Finite (torusFrame L t m).Cell := by
  have : ∀ i, Finite (ZMod ((torusFrame L t m).period (torusFrame L t m).top i)) := fun i => by
    have : NeZero ((torusFrame L t m).period (torusFrame L t m).top i) :=
      ⟨by simp [BlockFrame.period, torusFrame, BlockFrame.top]; exact hm.ne'⟩
    exact inferInstance
  exact Pi.finite
private theorem eventually_contDiffAt_minimalAction_below (hLF : MinimizerNearTrivialField)
    (hLA : MinimalActionTransfer)
    {a ρ : ℝ} (ha : 0 < a) {L : ℕ} (hL : IsAdmissibleBlockingFactor L) (t : ℕ) {m : ℕ} (hm : 2 * L ≤ m)
    (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) :
    ∀ᶠ V₀ in 𝓝 (trivialField m),
      ∀ (Y : Type) [NormedAddCommGroup Y] [NormedSpace ℝ Y] (y₀ : Y)
        (Z : Y → (torusFrame L t m).GaugeField (torusFrame L t m).depth),
        Z y₀ = stepMinimizer a ρ (readAtLevel (torusFrame L t m) (torusFrame L t m).top V₀) →
        (∀ x i, ContDiffAt ℝ 2 (fun y => ((Z y x i : UnitQuaternion) : ℍ[ℝ])) y₀) →
        ContDiffAt ℝ 2 (fun y => minimalAction a (finiteCells (torusFrame L t m))
          (torusFrame L t m).depth (Z y)) y₀ := by
  have hL0 : 0 < L := by have := hL.2; omega
  have hm0 : 0 < m := by omega
  cases t with
  | zero =>
    refine Eventually.of_forall fun V₀ Y _ _ y₀ Z _ hZ => ?_
    exact contDiffAt_wilsonAction_family _ hZ
  | succ s =>
    have hmL : 2 * L ≤ m * L := by nlinarith
    have hnear := (hLF a ha L hL s (m * L) ρ hmL hρ hρ1).2
    filter_upwards [(hLF a ha L hL (s + 1) m ρ hm hρ hρ1).1.eventually hnear] with V₀ hV Y _ _ y₀ Z h0 hZ
    obtain ⟨-, -, -, hAn, -⟩ := hV
    have hper : ∀ k, k ≤ s + 1 → ∀ i,
        (torusFrame L (s + 1) m).period k i = (torusFrame L s (m * L)).period k i := by
      intro k hk i
      have e1 : s + 1 + 1 - k = (s + 1 - k) + 1 := by omega
      simp only [BlockFrame.period, torusFrame, BlockFrame.top]
      rw [e1, pow_succ]
      ring
    have hshare : SharePeriods (torusFrame L (s + 1) m) (torusFrame L s (m * L)) (s + 1) :=
      ⟨rfl, hL.1, fun _ => hm0, fun _ => Nat.mul_pos hm0 hL0, by simp [torusFrame, BlockFrame.top],
        by simp [torusFrame, BlockFrame.top], hper⟩
    have hcross := (hLA _ _ (s + 1) a hshare).1
    have hfin : Finite (torusFrame L s (m * L)).Cell := finite_torusFrame_cell (Nat.mul_pos hm0 hL0)
    have hacross : transferField (torusFrame L s (m * L)) (Z y₀) =
        readAtLevel (torusFrame L s (m * L)) (torusFrame L s (m * L)).top
          (minimizerOnFinerTorus a ρ L (s + 1) m V₀) := by
      rw [h0, stepMinimizer_readAtLevel]
      funext x i
      show minimizerOnFinerTorus a ρ L (s + 1) m V₀
          (fun k => ((siteCoords (transferSite (torusFrame L (s + 1) m) x) k : ℤ) : ZMod (m * L))) i =
        minimizerOnFinerTorus a ρ L (s + 1) m V₀ (fun k => ((siteCoords x k : ℤ) : ZMod (m * L))) i
      congr 1
      funext k
      exact intCast_zmod_cast_congr (torusFrame_period_depth L (s + 1) m k) (siteCoords x k)
    have hfam := contDiffAt_analytic_family (F := torusFrame L s (m * L)) (y₀ := y₀) hAn
      (Z := fun y => transferField (torusFrame L s (m * L)) (Z y)) hacross (fun x i => hZ _ _)
    have e : (fun y => minimalAction a (finiteCells (torusFrame L (s + 1) m))
        (torusFrame L (s + 1) m).depth (Z y)) =
        fun y => minimalAction a (finiteCells (torusFrame L s (m * L))) (torusFrame L s (m * L)).top
          (transferField (torusFrame L s (m * L)) (Z y)) :=
      funext fun y => hcross (s + 1) (Z y) le_rfl
    rw [e]
    exact hfam
end ExcessEnergyContDiff
open ExcessEnergyContDiff in
theorem ExcessEnergyIsContDiffTwo.proof (hLF : MinimizerNearTrivialField)
    (hLA : MinimalActionTransfer) : ExcessEnergyIsContDiffTwo := by
  intro a ha L hL t m ρ hm hρ hρ1
  have hL0 : 0 < L := by have := hL.2; omega
  have hm0 : 0 < m := by omega
  have hA := hLF a ha L hL t m ρ hm hρ hρ1
  have hmean : ∀ᶠ V₀ in 𝓝 (trivialField m),
      ∀ c ∈ innerBonds (finiteCells (torusFrame L t m)) (torusFrame L t m).top,
        _root_.YangMills.Construction.BlockAverages.contourAverage (stepMinimizer (F := torusFrame L t m) a ρ
          (readAtLevel (torusFrame L t m) (torusFrame L t m).top V₀)) c ≠ 0 := by
    refine (eventually_all_finset _).2 fun c _ => ?_
    filter_upwards [hA.1.eventually
      (eventually_contourAverage_ne_zero (F := torusFrame L t m) (j := t) hL0 c)] with V₀ hV
    rw [stepMinimizer_readAtLevel]
    exact hV
  filter_upwards [hA.2, hmean, eventually_contDiffAt_minimalAction_below hLF hLA ha hL t hm hρ hρ1]
    with V₀ hV hM hlo
  intro Y _ _ _ y₀ Z Z' h0 h0' hZ hZ'
  obtain ⟨-, -, -, hAn, -⟩ := hV
  have hfin : Finite (torusFrame L t m).Cell := finite_torusFrame_cell hm0
  have hfit : ContDiffAt ℝ 2 (fun y => ∑ c ∈ innerBonds (finiteCells (torusFrame L t m)) (torusFrame L t m).top,
      blockFit (Z y) (Z' y) c) y₀ :=
    ContDiffAt.sum fun c hc => contDiffAt_blockFit_family hZ hZ' c (by rw [h0]; exact hM c hc)
  have htop := contDiffAt_analytic_family (F := torusFrame L t m) (y₀ := y₀) hAn (Z := Z') h0' hZ'
  exact ((hlo Y y₀ Z h0 hZ).add (contDiffAt_const.mul hfit)).sub htop
end YangMills.Construction.RunningCouplingSlope
end
