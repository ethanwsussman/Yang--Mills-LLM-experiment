import YangMills.Construction.ClusterExpansionOfAStep.TopFamiliesOnToriProof
import YangMills.Construction.ClusterExpansionOfAStep.AMoveReadAtZero
import YangMills.Construction.ClusterExpansionOfAStep.LeastLogNearOne
import YangMills.Construction.ClusterExpansionOfAStep.MovesAlongLinearDirections
import YangMills.Construction.ColdStepAtMirrorFrames.FramesOnTheParameters
import YangMills.Construction.SummableBoundsOfTheFlow.TheFamilyAtTheLeastFieldIsAnalytic
import YangMills.Construction.SummableBoundsOfTheFlow.TheReferenceIsAFamilyBelowProof
import YangMills.Construction.SummableBoundsOfTheFlow.ValuesAboveTheLeastField
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion Topology
open Filter
namespace YangMills.Construction
open BlockAverages hiding bondSpread IsCold
open ColdStepAtMirrorFrames TorusFields TorusLumps StepCosts
namespace ReferenceDensity
namespace FrameTransfer
section Sites
variable {F : BlockFrame} {m : ℕ}
private theorem isCold_restrictToTorus (hp : ∀ i, F.period F.depth i = m) {s : ℝ} {W : F.GaugeField F.depth}
    (h : IsSmallCurvature s W) : IsCold s (restrictToTorus m W) := by apply _root_.YangMills.Construction.FrameTorus.isCold_restrictToTorus <;> assumption
end Sites
private theorem period_facts_of_cubic {L t n₀ : ℕ} {F : BlockFrame} (h : IsCubicTorusAbove L t n₀ F) :
    (∀ i, F.period F.depth i = F.period F.depth 0) ∧ n₀ ≤ F.period F.depth 0 := by apply _root_.YangMills.Construction.FrameTorus.period_eq_of_isCubicTorusAbove <;> assumption
end FrameTransfer
namespace MinimizerAnalytic
open FrameTransfer
private def basisQuaternion (e : Fin 3) : ℍ[ℝ] := ((BondMoves.imaginaryBasis e : imaginaryQuaternions) : ℍ[ℝ])
private theorem imaginary_eq_sum_basis (v : imaginaryQuaternions) :
    v = ∑ e, (inner ℝ (basisQuaternion e) (v : ℍ[ℝ])) • BondMoves.imaginaryBasis e := by
  have hv : (v : ℍ[ℝ]).re = 0 := v.2
  have h₀ : inner ℝ (basisQuaternion 0) (v : ℍ[ℝ]) = (v : ℍ[ℝ]).imI := by
    rw [Quaternion.inner_def, Quaternion.re_mul]
    simp [basisQuaternion, BondMoves.imaginaryBasis]
  have h₁ : inner ℝ (basisQuaternion 1) (v : ℍ[ℝ]) = (v : ℍ[ℝ]).imJ := by
    rw [Quaternion.inner_def, Quaternion.re_mul]
    simp [basisQuaternion, BondMoves.imaginaryBasis]
  have h₂ : inner ℝ (basisQuaternion 2) (v : ℍ[ℝ]) = (v : ℍ[ℝ]).imK := by
    rw [Quaternion.inner_def, Quaternion.re_mul]
    simp [basisQuaternion, BondMoves.imaginaryBasis]
  rw [Fin.sum_univ_three, h₀, h₁, h₂]
  apply Subtype.ext
  apply Quaternion.ext
  · show (v : ℍ[ℝ]).re = (v : ℍ[ℝ]).imI * 0 + (v : ℍ[ℝ]).imJ * 0 + (v : ℍ[ℝ]).imK * 0
    simp [hv]
  · show (v : ℍ[ℝ]).imI = (v : ℍ[ℝ]).imI * 1 + (v : ℍ[ℝ]).imJ * 0 + (v : ℍ[ℝ]).imK * 0
    simp
  · show (v : ℍ[ℝ]).imJ = (v : ℍ[ℝ]).imI * 0 + (v : ℍ[ℝ]).imJ * 1 + (v : ℍ[ℝ]).imK * 0
    simp
  · show (v : ℍ[ℝ]).imK = (v : ℍ[ℝ]).imI * 0 + (v : ℍ[ℝ]).imJ * 0 + (v : ℍ[ℝ]).imK * 1
    simp
private theorem expUnit_zero_eq_one : expUnit (0 : imaginaryQuaternions) = 1 := by apply _root_.YangMills.Construction.TorusFields.expUnit_zero <;> assumption
private theorem analyticAt_of_perturb (hLog : QuaternionLog.MinimalLogAnalyticNearOne) {m k : ℕ} [NeZero m]
    (G : TorusField m → ℝ) (Wt : (Fin k → ℝ) → TorusField m)
    (hG : ∀ (q : ℕ) (c : Fin q → TorusBond m) (X : Fin q → imaginaryQuaternions),
      AnalyticAt ℝ (fun s : Fin q → ℝ => G (perturb c X s (Wt 0))) 0)
    (hW : ∀ x i, AnalyticAt ℝ (fun τ => ((Wt τ x i : UnitQuaternion) : ℍ[ℝ])) 0) :
    AnalyticAt ℝ (fun τ => G (Wt τ)) 0 := by
  classical
  obtain ⟨Lg, hLg, hLe⟩ := hLog
  let e := Fintype.equivFin (TorusBond m × Fin 3)
  let g : (Fin k → ℝ) → TorusBond m → ℍ[ℝ] := fun τ b =>
    ((Wt τ b.1 b.2 : UnitQuaternion) : ℍ[ℝ]) * (((Wt 0 b.1 b.2)⁻¹ : UnitQuaternion) : ℍ[ℝ])
  have hg0 : ∀ b, g 0 b = 1 := by
    intro b
    show (((Wt 0 b.1 b.2 * (Wt 0 b.1 b.2)⁻¹ : UnitQuaternion)) : ℍ[ℝ]) = 1
    rw [mul_inv_cancel]
    rfl
  have hga : ∀ b, AnalyticAt ℝ (fun τ => g τ b) 0 := fun b => (hW b.1 b.2).mul analyticAt_const
  have h1mem : (1 : ℍ[ℝ]) ∈ Metric.ball (1 : ℍ[ℝ]) 1 := Metric.mem_ball_self one_pos
  have hLa : ∀ b, AnalyticAt ℝ (fun τ => Lg (g τ b)) 0 := by
    intro b
    have h1 : AnalyticAt ℝ Lg ((fun τ => g τ b) 0) := by
      show AnalyticAt ℝ Lg (g 0 b)
      rw [hg0]
      exact hLg 1 h1mem
    exact AnalyticAt.comp (g := Lg) (f := fun τ => g τ b) h1 (hga b)
  let s : (Fin k → ℝ) → Fin (Fintype.card (TorusBond m × Fin 3)) → ℝ := fun τ l =>
    inner ℝ (basisQuaternion (e.symm l).2) (Lg (g τ (e.symm l).1))
  have hs : AnalyticAt ℝ s 0 := by
    rw [analyticAt_pi_iff]
    intro l
    exact ((innerSL ℝ (basisQuaternion (e.symm l).2)).analyticAt _).comp (hLa _)
  have hLg1 : Lg 1 = 0 := by
    have h := hLe 1 (by simp)
    have h2 : LumpContours.minimalLog (1 : UnitQuaternion) = 0 := by
      have := GaugeFixing.norm_minimalLog_le (1 : UnitQuaternion)
      simp only [OneMemClass.coe_one, sub_self, norm_zero, mul_zero] at this
      have h3 := norm_le_zero_iff.mp this
      exact Subtype.ext h3
    rw [h2] at h
    simpa using h.symm
  have hs0 : s 0 = 0 := by
    funext l
    simp [s, hg0, hLg1]
  have hnear : ∀ᶠ τ in 𝓝 (0 : Fin k → ℝ), ∀ b, ‖g τ b - 1‖ < 1 := by
    rw [eventually_all]
    intro b
    have hc : ContinuousAt (fun τ => ‖g τ b - 1‖) 0 := ((hga b).continuousAt.sub continuousAt_const).norm
    have h0 : ‖g 0 b - 1‖ = 0 := by simp [hg0]
    have := hc.tendsto
    rw [h0] at this
    exact this.eventually (gt_mem_nhds one_pos)
  have heq : ∀ᶠ τ in 𝓝 (0 : Fin k → ℝ),
      perturb (fun l => (e.symm l).1) (fun l => BondMoves.imaginaryBasis (e.symm l).2) (s τ) (Wt 0) = Wt τ := by
    filter_upwards [hnear] with τ hτ
    funext x i
    have hL : ((LumpContours.minimalLog (Wt τ x i * (Wt 0 x i)⁻¹) : imaginaryQuaternions) : ℍ[ℝ]) =
        Lg (g τ (x, i)) :=
      hLe (Wt τ x i * (Wt 0 x i)⁻¹) (hτ (x, i))
    have hsum : (∑ l, if (e.symm l).1 = (x, i) then s τ l • BondMoves.imaginaryBasis (e.symm l).2 else 0) =
        LumpContours.minimalLog (Wt τ x i * (Wt 0 x i)⁻¹) := by
      have h1 := Equiv.sum_comp e
        (fun l => if (e.symm l).1 = (x, i) then s τ l • BondMoves.imaginaryBasis (e.symm l).2 else 0)
      rw [← h1, Fintype.sum_prod_type]
      simp only [Equiv.symm_apply_apply, s]
      rw [Finset.sum_eq_single (x, i)]
      · simp only [if_true]
        conv_rhs => rw [imaginary_eq_sum_basis (LumpContours.minimalLog (Wt τ x i * (Wt 0 x i)⁻¹)), hL]
      · intro b _ hb
        simp [hb]
      · simp
    show expUnit (∑ l, if (e.symm l).1 = (x, i) then s τ l • BondMoves.imaginaryBasis (e.symm l).2 else 0) *
      Wt 0 x i = Wt τ x i
    rw [hsum, GaugeFixing.expUnit_minimalLog, inv_mul_cancel_right]
  have hcomp : AnalyticAt ℝ (fun τ => G (perturb (fun l => (e.symm l).1)
      (fun l => BondMoves.imaginaryBasis (e.symm l).2) (s τ) (Wt 0))) 0 := by
    have h1 : AnalyticAt ℝ (fun u => G (perturb (fun l => (e.symm l).1)
        (fun l => BondMoves.imaginaryBasis (e.symm l).2) u (Wt 0))) (s 0) := by
      rw [hs0]
      exact hG _ _ _
    exact h1.comp hs
  exact hcomp.congr (heq.mono fun τ h => by simp only [h])
section Top
variable {L t n : ℕ}
private theorem torusFrame_period_top (i : Fin 4) :
    (torusFrame L t n).period (torusFrame L t n).top i = n := TopLevelSites.period_top i
private def bondsInTopFrame {k : ℕ} (L t : ℕ) (c : Fin k → TorusBond n) :
    Fin k → (torusFrame L t n).Site (torusFrame L t n).top × Fin 4 :=
  fun l => (torusSiteInFrame (torusFrame L t n) (torusFrame L t n).top (c l).1, (c l).2)
private theorem readAtLevel_perturb [NeZero n] {k : ℕ} (c : Fin k → TorusBond n) (X : Fin k → imaginaryQuaternions)
    (σ : Fin k → ℝ) (V : TorusField n) :
    readAtLevel (torusFrame L t n) (torusFrame L t n).top (perturb c X σ V) =
      leftTranslate (bondSpread (bondsInTopFrame L t c) X σ) (readAtLevel (torusFrame L t n) (torusFrame L t n).top V) := by apply _root_.YangMills.Construction.TopFamilyEvaluations.readAtLevel_perturb <;> assumption
end Top
private theorem stepCoordinates_zero {F : BlockFrame} (x : F.Site F.depth) (i : Fin 4) :
    stepCoordinates (0 : StepVariable (finiteCells F)) x i = 0 := by
  unfold stepCoordinates
  split_ifs
  · apply Subtype.ext
    ext <;> simp [toImaginary]
  · rfl
private def bondSpreadLinear {F : BlockFrame} {j k : ℕ} (c : Fin k → F.Site j × Fin 4)
    (X : Fin k → imaginaryQuaternions) (y : F.Site j) (i : Fin 4) :
    (Fin k → ℝ) →L[ℝ] imaginaryQuaternions :=
  ∑ l, if c l = (y, i) then
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin k => ℝ) l).smulRight (X l) else 0
private theorem bondSpreadLinear_apply {F : BlockFrame} {j k : ℕ} (c : Fin k → F.Site j × Fin 4)
    (X : Fin k → imaginaryQuaternions) (y : F.Site j) (i : Fin 4) (τ : Fin k → ℝ) :
    bondSpreadLinear c X y i τ = bondSpread c X τ y i := by
  simp only [bondSpreadLinear, bondSpread, ContinuousLinearMap.coe_sum', Finset.sum_apply]
  refine Finset.sum_congr rfl fun l _ => ?_
  split_ifs <;> simp
private theorem analyticAt_expUnit_comp {k : ℕ} {h : (Fin k → ℝ) → imaginaryQuaternions} (hh : AnalyticAt ℝ h 0) :
    AnalyticAt ℝ (fun τ => ((expUnit (h τ) : UnitQuaternion) : ℍ[ℝ])) 0 := by
  have h1 : AnalyticAt ℝ (fun τ => ((h τ : imaginaryQuaternions) : ℍ[ℝ])) 0 :=
    (imaginaryQuaternions.subtypeL.analyticAt _).comp hh
  exact (NormedSpace.exp_analytic (𝕂 := ℝ) _).comp h1
private theorem fieldAboveFrame_analyticAt {F : BlockFrame} (a ρA : ℝ) (V : F.GaugeField F.top)
    (hL : Odd F.blockSide) (hs : ∀ i, 2 ≤ F.extent i)
    (hc : ∀ b ∈ chordBonds (finiteCells F),
      IsBondAnalyticAt (minimizingBondCoordinate a ρA (finiteCells F) b) V)
    {k : ℕ} (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions) (x : F.Site F.depth) (i : Fin 4) :
    AnalyticAt ℝ (fun τ =>
      ((fieldAboveFrame true a ρA 0 (leftTranslate (bondSpread c X τ) V) 0 x i : UnitQuaternion) : ℍ[ℝ])) 0 := by
  classical
  have hw : ¬ IsAxialTreeBond (x, i) → AnalyticAt ℝ (fun τ : Fin k → ℝ =>
      coordsAboveFrame true a ρA 0 (leftTranslate (bondSpread c X τ) V) 0 x i) 0 := by
    intro hnt
    have hb := LinearDirections.mem_chordBonds_finiteCells hL hs x i hnt
    have h := hc _ hb k c X
    refine h.congr (Eventually.of_forall fun τ => ?_)
    show minimizingBondCoordinate a ρA (finiteCells F) (x, i) (leftTranslate (bondSpread c X τ) V) = _
    simp [coordsAboveFrame, ColdStepAtMirrorFrames.stepFrame, stepCoordinates_zero]
  have hm : ∀ (y : F.Cell) (i' : Fin 4), AnalyticAt ℝ (fun τ : Fin k → ℝ => bondSpread c X τ y i') 0 := by
    intro y i'
    refine ((bondSpreadLinear c X y i').analyticAt 0).congr (Eventually.of_forall fun τ => ?_)
    exact bondSpreadLinear_apply c X y i' τ
  by_cases hcr : IsCrossingBond (x, i)
  · have hnt : ¬ IsAxialTreeBond (x, i) := fun h => h.1 hcr
    have hcst : AnalyticAt ℝ (fun _ : Fin k → ℝ => ((V (enclosingCell x) i : UnitQuaternion) : ℍ[ℝ])) 0 :=
      analyticAt_const
    refine ((analyticAt_expUnit_comp (hw hnt)).mul
      ((analyticAt_expUnit_comp (hm (enclosingCell x) i)).mul hcst)).congr (Eventually.of_forall fun τ => ?_)
    simp only [fieldAboveFrame, chartedField, if_pos hcr, leftTranslate]
    rfl
  · by_cases ht : IsAxialTreeBond (x, i)
    · have hcst : AnalyticAt ℝ (fun _ : Fin k → ℝ => (((1 : UnitQuaternion)) : ℍ[ℝ])) 0 := analyticAt_const
      refine hcst.congr (Eventually.of_forall fun τ => ?_)
      simp only [fieldAboveFrame, chartedField, if_neg hcr, if_pos ht]
    · refine (analyticAt_expUnit_comp (hw ht)).congr (Eventually.of_forall fun τ => ?_)
      simp only [fieldAboveFrame, chartedField, if_neg hcr, if_neg ht]
private theorem localFamily_analyticAt (hLog : QuaternionLog.MinimalLogAnalyticNearOne) {F : BlockFrame}
    {L t n₀ : ℕ} (a ρA σ : ℝ)
    (V : F.GaugeField F.top) (hL : Odd F.blockSide) (hs : ∀ i, 2 ≤ F.extent i) (hn₀ : 1 ≤ n₀)
    (hc : ∀ b ∈ chordBonds (finiteCells F),
      IsBondAnalyticAt (minimizingBondCoordinate a ρA (finiteCells F) b) V)
    (hlow : IsCubicTorusAbove L t n₀ F) (hcold : IsSmallCurvature σ (fieldAboveFrame true a ρA 0 V 0))
    (f : LocalDensity)
    (hf : ∀ n [NeZero n], n₀ ≤ n → ∀ (y : TorusSite n) (W : TorusField n), IsCold σ W →
      ∀ (k : ℕ) (c : Fin k → TorusBond n) (X : Fin k → imaginaryQuaternions),
        AnalyticAt ℝ (fun τ : Fin k → ℝ => f n y (perturb c X τ W)) 0)
    {k : ℕ} (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions) (y : F.Site F.depth) :
    AnalyticAt ℝ (fun τ =>
      localFamilyOfDensity f F y (fieldAboveFrame true a ρA 0 (leftTranslate (bondSpread c X τ) V) 0)) 0 := by
  obtain ⟨hp, hmm⟩ := period_facts_of_cubic hlow
  have : NeZero (F.period F.depth 0) := ⟨by omega⟩
  have hV0 : leftTranslate (bondSpread c X (0 : Fin k → ℝ)) V = V := by
    funext z i
    simp [leftTranslate, bondSpread, expUnit_zero_eq_one]
  refine analyticAt_of_perturb hLog (f (F.period F.depth 0) (toTorusSite _ y))
    (fun τ => restrictToTorus (F.period F.depth 0)
      (fieldAboveFrame true a ρA 0 (leftTranslate (bondSpread c X τ) V) 0)) ?_ ?_
  · intro q c₂ X₂
    have hco : IsCold σ (restrictToTorus (F.period F.depth 0)
        (fieldAboveFrame true a ρA 0 (leftTranslate (bondSpread c X (0 : Fin k → ℝ)) V) 0)) := by
      rw [hV0]
      exact isCold_restrictToTorus hp hcold
    exact hf _ hmm _ _ hco q c₂ X₂
  · intro x i
    exact fieldAboveFrame_analyticAt a ρA V hL hs hc c X _ i
end MinimizerAnalytic
open MinimizerAnalytic FrameTransfer in
theorem familyAtMinimizerAnalytic_proof (hFr : FrameBoundsEventually)
    (hVal : StepDensities.valuesAboveFrameBoundedStatement) (hLog : QuaternionLog.MinimalLogAnalyticNearOne) :
    FamilyAtMinimizerAnalytic := by
  have hVal' : EventuallyOrdered _ := hVal
  have hFr' : EventuallyInParameters FrameBoundsForParameters := hFr
  unfold FamilyAtMinimizerAnalytic EventuallyOrdered
  refine EventuallyInParameters.mono (EventuallyInParameters.and hFr' hVal') ?_
  rintro T ⟨hF, hV⟩ hdr hn ℓ hm hfits t f hf n _ hnn y W hW k c X
  obtain ⟨R₀, -, hvals⟩ := hV hdr hn
  obtain ⟨Cf, C, -, -, -, -, hL40, h64, -, -, -, -, hσA, -, -, -⟩ := hF
  have hσ := hdr.σ_pos
  have hWc : IsCold (5 / 4 * T.σ) W := fun x μ ν h => lt_of_lt_of_le (hW x μ ν h) (by linarith)
  have hVc : IsSmallCurvature (F := torusFrame T.L t n) (5 / 4 * T.σ)
      (readAtLevel (torusFrame T.L t n) (torusFrame T.L t n).top W) := by
    rintro ⟨x, μ, ν⟩ hlt
    rw [TopLevelSites.plaquetteDefect_readAtLevel_eq (fun i => TopLevelSites.period_top i)]
    exact hWc _ μ ν hlt
  have hTop : IsCubicTopTorus T.L t T.n₀ (torusFrame T.L t n) := ⟨rfl, rfl, n, fun _ => rfl, hnn⟩
  have hCl := hdr.chain_admissible.estimates (torusFrame T.L t n) (5 / 4 * T.σ) _
    ⟨rfl, n, by omega, fun _ => rfl⟩ (by positivity) hσA hVc
  have hcoord := fun b hb => (hCl.coordinates b hb).1
  have hs : ∀ i, 2 ≤ (torusFrame T.L t n).extent i := fun _ => by
    show 2 ≤ n
    omega
  have hLpos : 1 ≤ T.L := hdr.odd_L.pos
  have hlow : IsCubicTorusAbove T.L t T.n₀ (torusFrame T.L t n) :=
    ⟨rfl, rfl, n, fun _ => rfl, hnn.trans (Nat.le_mul_of_pos_right _ hLpos)⟩
  have hcold := (hvals t (torusFrame T.L t n) _ 0 hTop hVc (fun b => by
    simpa using (show (0 : ℝ) ≤ T.ballRadius by unfold StepParameters.ballRadius; positivity))).1
  have hread : ∀ τ : Fin k → ℝ, readAtLevel (torusFrame T.L t n) (torusFrame T.L t n).top (perturb c X τ W) =
      leftTranslate (bondSpread (bondsInTopFrame T.L t c) X τ)
        (readAtLevel (torusFrame T.L t n) (torusFrame T.L t n).top W) := fun τ => readAtLevel_perturb c X τ W
  show AnalyticAt ℝ (fun τ : Fin k → ℝ => cellCentredExpansion true T.a T.ρA 0 (localFamilyOfDensity f)
    (torusSiteInFrame (torusFrame T.L t n) (torusFrame T.L t n).top y) 0
    (readAtLevel (torusFrame T.L t n) (torusFrame T.L t n).top (perturb c X τ W))) 0
  simp only [hread, cellCentredExpansion, centredExpansion, ColdStepAtMirrorFrames.subtractTrivial]
  refine Finset.analyticAt_fun_sum _ fun y' _ => ?_
  exact (localFamily_analyticAt hLog T.a T.ρA T.σ _ hdr.odd_L hs (by omega) hcoord hlow hcold f hf _ X y').sub
    analyticAt_const
end ReferenceDensity
end YangMills.Construction
end
