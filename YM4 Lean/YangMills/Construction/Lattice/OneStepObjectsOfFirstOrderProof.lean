import YangMills.Construction.Coordinates.PowerSeriesHolomorphy
import YangMills.Construction.Lattice.LayerBondsCoarseSpacesAndAverages
import YangMills.Construction.Lattice.OneStepObjectsNearSmallPlaquettes
import YangMills.Construction.Lattice.OneStepObjectsOfFirstOrder
import YangMills.Construction.Lattice.PathsOfBlocksAndDoubleBlocks
import YangMills.Construction.Lattice.SchemeAverageDependsOnTheDoubleBlockAlone
import YangMills.Construction.Matrices.RestatedElementaryInequalities
import YangMills.Construction.PeriodicLattice.TriplesOnFiniteBondSets
import Mathlib
set_option autoImplicit false
open scoped Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction.PeriodicLattice
namespace FirstOrderSteps
open Matrices Coordinates
open ComplexCoordinates GroupLieProduct
theorem tracelessPart_coe (v : ↥ComplexMatrix2.traceless) :
    tracelessPart (v : ComplexMatrix2) = v := by
  unfold tracelessPart
  rw [dif_pos v.2]
section Slices
variable {ι : Type}
theorem supOperatorNorm_smul (z : ℂ) (a : ι → ↥ComplexMatrix2.traceless) :
    supOperatorNorm (z • a) = ‖z‖ * supOperatorNorm a := by
  unfold supOperatorNorm
  rw [Real.mul_iSup_of_nonneg (norm_nonneg z)]
  refine iSup_congr fun i => ?_
  exact norm_smul z ((a i : ComplexMatrix2))
def matrixContinuousEquiv : ComplexMatrix2 ≃L[ℂ] ComplexCoordinates 4 :=
  LinearEquiv.toContinuousLinearEquiv
    { matrixEquiv with
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
variable [Fintype ι]
theorem differentiableAt_smul_line (hH : ComplexCoordinates.PowerSeriesHolomorphy.Properties)
    (β : Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless) {ρ : ℝ}
    {G : (ι → ↥ComplexMatrix2.traceless) → ComplexMatrix2}
    (hF : IsHolomorphicOnTraceless β matrixEquiv (supBall ι ρ)
      fun A => G fun b => tracelessPart (A b))
    (a : ι → ↥ComplexMatrix2.traceless) (z : ℂ) (hz : supOperatorNorm (z • a) < ρ) :
    DifferentiableAt ℂ (fun t : ℂ => G (t • a)) z := by
  let ν := Fintype.equivFin ι
  have h := hF.2 ν
  let w₀ : ComplexCoordinates (Fintype.card ι * 3) := fun k =>
    β.repr (a (ν.symm (finProdFinEquiv.symm k).1)) (finProdFinEquiv.symm k).2
  have hT : ∀ t : ℂ, tupleOfCoords β ν (t • w₀) =
      fun i => (((t • a) i : ↥ComplexMatrix2.traceless) : ComplexMatrix2) := by
    intro t
    funext i
    have hw : ∀ c : Fin 3, (t • w₀) (finProdFinEquiv (ν i, c)) = t * β.repr (a i) c := by
      intro c
      show t * β.repr (a (ν.symm (finProdFinEquiv.symm (finProdFinEquiv (ν i, c))).1))
        (finProdFinEquiv.symm (finProdFinEquiv (ν i, c))).2 = _
      rw [Equiv.symm_apply_apply]
      simp
    have hs := congrArg (fun v : ↥ComplexMatrix2.traceless => (v : ComplexMatrix2))
      (β.sum_repr (a i))
    simp only [Submodule.coe_sum, Submodule.coe_smul] at hs
    simp only [tupleOfCoords, tracelessTuple, hw]
    show _ = t • (a i : ComplexMatrix2)
    rw [← hs, Finset.smul_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [mul_smul]
  have hG : ∀ t : ℂ, (fun A : ι → ComplexMatrix2 => G fun b => tracelessPart (A b))
      (tupleOfCoords β ν (t • w₀)) = G (t • a) := by
    intro t
    rw [hT]
    show G (fun b => tracelessPart (((t • a) b : ↥ComplexMatrix2.traceless) : ComplexMatrix2)) = _
    simp only [tracelessPart_coe]
  have hmem : z • w₀ ∈ tupleOfCoords β ν ⁻¹' supBall ι ρ := by
    show tupleOfCoords β ν (z • w₀) ∈ supBall ι ρ
    rw [hT]
    exact ⟨fun i => ((z • a) i).2, hz⟩
  obtain ⟨D, hD⟩ := ((hH.1 _ _ h.1).1 4 _ h).2.2.1 (z • w₀) hmem
  have hdiff := (hasFDerivAt_of_restrictScalars ℝ hD rfl).differentiableAt
  have hline : DifferentiableAt ℂ (fun t : ℂ => t • w₀) z :=
    differentiableAt_id.smul_const w₀
  have hcomp := matrixContinuousEquiv.symm.differentiableAt.comp z (hdiff.comp z hline)
  have heq : (⇑matrixContinuousEquiv.symm ∘
      ((matrixEquiv ∘ (fun A : ι → ComplexMatrix2 => G fun b => tracelessPart (A b)) ∘
        tupleOfCoords β ν) ∘ fun t : ℂ => t • w₀)) = fun t : ℂ => G (t • a) := by
    funext t
    exact (matrixEquiv.symm_apply_apply _).trans (hG t)
  rw [heq] at hcomp
  exact hcomp
theorem operatorNorm_le_of_map_zero (hH : ComplexCoordinates.PowerSeriesHolomorphy.Properties)
    (hE : ComplexMatrix2.RestatedElementaryInequalitiesStatement)
    (β : Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless) {ρ : ℝ}
    {G : (ι → ↥ComplexMatrix2.traceless) → ComplexMatrix2}
    (hF : IsHolomorphicOnTraceless β matrixEquiv (supBall ι ρ)
      fun A => G fun b => tracelessPart (A b))
    (hB : ∀ a : ι → ↥ComplexMatrix2.traceless, supOperatorNorm a < ρ →
      ComplexMatrix2.operatorNorm (G a) ≤ 1) (h0 : G 0 = 0)
    (hρ : 0 < ρ) (a : ι → ↥ComplexMatrix2.traceless) (ha : supOperatorNorm a < ρ) :
    ComplexMatrix2.operatorNorm (G a) ≤ 1 / ρ * supOperatorNorm a := by
  have hs0 : 0 ≤ supOperatorNorm a := Real.iSup_nonneg fun _ => norm_nonneg _
  rcases hs0.eq_or_lt with hs | hs
  · have hz : a = 0 := by
      funext i
      have hle : ComplexMatrix2.operatorNorm (a i : ComplexMatrix2) ≤ supOperatorNorm a :=
        le_ciSup (f := fun i => ComplexMatrix2.operatorNorm (a i : ComplexMatrix2))
          (Set.finite_range _).bddAbove i
      rw [← hs] at hle
      exact Subtype.ext (norm_le_zero_iff.mp hle)
    have hGa : G a = 0 := by rw [hz]; exact h0
    have hnn : 0 ≤ 1 / ρ * supOperatorNorm a := mul_nonneg (by positivity) hs0
    rw [hGa]
    show ‖(0 : ComplexMatrix2)‖ ≤ _
    rw [norm_zero]
    exact hnn
  · set R := ρ / supOperatorNorm a with hRdef
    have hR : 1 < R := (one_lt_div hs).2 ha
    have hin : ∀ z ∈ Metric.ball (0 : ℂ) R, supOperatorNorm (z • a) < ρ := by
      intro z hz
      rw [supOperatorNorm_smul]
      have hz' : ‖z‖ < R := by simpa using hz
      exact (lt_div_iff₀ hs).1 hz'
    have hd : DifferentiableOn ℂ (fun t : ℂ => G (t • a)) (Metric.ball 0 R) := fun z hz =>
      (differentiableAt_smul_line hH β hF a z (hin z hz)).differentiableWithinAt
    have hb : ∀ z ∈ Metric.ball (0 : ℂ) R, ‖G (z • a)‖ ≤ 1 := fun z hz => hB _ (hin z hz)
    have h1 : (1 : ℂ) ∈ Metric.ball (0 : ℂ) R := by simpa using hR
    have hS := (hE.2.2.2.2.2.1 ℂ ComplexMatrix2 R 1 (fun t : ℂ => G (t • a)) hd hb 1 h1).2.2
      (by simpa using h0)
    simp only [one_smul, norm_one, mul_one] at hS
    refine hS.trans_eq ?_
    rw [hRdef]
    field_simp
end Slices
section Zero
theorem logSeries_one : ComplexMatrix2.logSeries 1 = 0 := by
  simp [ComplexMatrix2.logSeries]
theorem mul_inv_eq_one_of_near {X : ComplexMatrix2}
    (h : ComplexMatrix2.operatorNorm (X * X⁻¹ - 1) < 1) : X * X⁻¹ = 1 := by
  by_cases hd : IsUnit X.det
  · exact Matrix.mul_nonsing_inv X hd
  · exfalso
    rw [Matrix.nonsing_inv_apply_not_isUnit X hd] at h
    simp at h
variable {L m K n : ℕ}
theorem lieBondField_eval_zero {P : SymmetricBondSet L m K n} (b : BondAtLevel L m K n) :
    LieBondField.eval (0 : LieBondField P) b = 0 := by
  unfold LieBondField.eval
  split_ifs <;> simp
theorem twistedConfig_zero_eqOn (c : BondAtLevel L m K (n + 1))
    {W₀ : BondAtLevel L m K n → ComplexMatrix2}
    (hW : IsGaugeField compactGaugeGroup (doubleBlockSymmetricSet c).bonds W₀) :
    Set.EqOn (twistedConfig c 0 W₀) W₀ (bondsInDoubleBlock c) := by
  intro b hb
  unfold twistedConfig expTwist
  simp only [lieBondField_eval_zero]
  split_ifs with hp
  · simp [NormedSpace.exp_zero]
  · have hr : b.opposite ∈ (doubleBlockSymmetricSet c).bonds :=
      (doubleBlockSymmetricSet c).opposite_mem b hb
    have := hW.2 b.opposite hr
    simp only [ZeroMemClass.coe_zero, smul_zero, NormedSpace.exp_zero, one_mul]
    exact this.symm
theorem contourHolonomy_eq_of_eqOn {W W' : BondAtLevel L m K n → ComplexMatrix2}
    {c : BondAtLevel L m K (n + 1)} (hP : PathsInsideDoubleBlock (levelDepth K n) c)
    (hE : Set.EqOn W W' (bondsInDoubleBlock c)) (s : AveragingScheme)
    {y : SiteAtLevel L m K (n + 1)} (hy : y = c.source ∨ y = c.target)
    {x : SiteAtLevel L m K n} (hx : x ∈ sitesInBlock (levelDepth K n) y) :
    contourHolonomy s W y x = contourHolonomy s W' y x := by
  have hol : ∀ Γ : List (BondAtLevel L m K n), (∀ b ∈ Γ, W b = W' b) →
      pathHolonomy W Γ = pathHolonomy W' Γ := by
    intro Γ h
    unfold pathHolonomy
    rw [List.map_congr_left h]
  cases s with
  | centred =>
    have hv : contourHolonomies W y x = contourHolonomies W' y x :=
      funext fun σ => hol _ fun b hb => hE ((hP.1 y hy x hx).1 _ ⟨σ, rfl⟩ b hb)
    simp only [contourHolonomy, complexMeanContourHolonomy]
    rw [hv]
  | cornered =>
    simp only [contourHolonomy]
    exact hol _ fun b hb => hE ((hP.1 y hy x hx).2 b hb)
end Zero
end FirstOrderSteps
open FirstOrderSteps Matrices Coordinates Matrices.GroupLieProduct
theorem stepQuantitiesFirstOrder_proof
    (hN : StepObjectsNearSmallCurvature)
    (hP : BlockPaths.Statement)
    (hA : OneStepAverageIsLocal)
    (hH : ComplexCoordinates.PowerSeriesHolomorphy.Properties)
    (hE : ComplexMatrix2.RestatedElementaryInequalitiesStatement) :
    StepQuantitiesFirstOrder := by
  intro L hL r hr m K n hm hn s c hc W₀ hW hS a ha
  obtain ⟨hb, hh⟩ := hN L hL r hr m K n hm hn s c hc W₀ hW hS
  have hfinS : Finite (SiteAtLevel L m K n) :=
    SeparatedSequences.BaseParameters.site_finite (lt_of_lt_of_le (by norm_num) hL.2) m _
  have hfinB : Finite (BondAtLevel L m K n) := by
    refine Finite.of_injective (fun b : BondAtLevel L m K n => (b.source, b.target)) ?_
    intro b b' hbb
    exact Bond.ext (congrArg Prod.fst hbb) (congrArg Prod.snd hbb)
  let _ : Fintype (PositiveBondsOf (doubleBlockSymmetricSet c)) := Fintype.ofFinite _
  have hr0 : 0 < r := hr.radius_pos
  obtain ⟨hol₁, hol₂, hol₃⟩ := hh r le_rfl inferInstance OneLoop.pauliBasis
  have hz : supOperatorNorm (0 : LieBondField (doubleBlockSymmetricSet c)) < r := by
    have : supOperatorNorm (0 : LieBondField (doubleBlockSymmetricSet c)) = 0 := by
      simp [supOperatorNorm]
    rw [this]
    exact hr0
  have hb0 := hb 0 hz
  have hEq := twistedConfig_zero_eqOn c hW
  have hPaths : PathsInsideDoubleBlock (levelDepth K n) c := by
    obtain ⟨μ, hμ⟩ := hc
    obtain ⟨-, hbond⟩ := hP L m K hL.1 hL.2 hm n hn
    obtain ⟨-, -, -, -, hPc⟩ := hbond c μ hμ
    exact hPc
  have hlog0 : ∀ y ∈ ({c.source, c.target} : Set (SiteAtLevel L m K (n + 1))),
      ∀ x ∈ sitesInBlock (levelDepth K n) y, stepLog s c 0 W₀ y x = 0 := by
    intro y hy x hx
    obtain ⟨⟨-, -, hnear⟩, -⟩ := hb0.log_bound y hy x hx
    have hcv := contourHolonomy_eq_of_eqOn hPaths hEq s hy hx
    have hone : stepRatio s c 0 W₀ y x = 1 := by
      unfold stepRatio at hnear ⊢
      rw [hcv] at hnear ⊢
      exact mul_inv_eq_one_of_near hnear
    simp [stepLog, hone, logSeries_one]
  have hgauge1 : ∀ y ∈ ({c.source, c.target} : Set (SiteAtLevel L m K (n + 1))),
      stepGauge s c 0 W₀ y = 1 := by
    intro y hy
    have hsum : (∑ᶠ x ∈ sitesInBlock (levelDepth K n) y, stepLog s c 0 W₀ y x) = 0 := by
      have : (∑ᶠ x ∈ sitesInBlock (levelDepth K n) y, stepLog s c 0 W₀ y x) =
          ∑ᶠ x ∈ sitesInBlock (levelDepth K n) y, (0 : ComplexMatrix2) :=
        finsum_mem_congr rfl fun x hx => hlog0 y hy x hx
      rw [this]
      simp
    unfold stepGauge
    rw [hsum]
    simp [NormedSpace.exp_zero]
  have hgl0 : ∀ y ∈ ({c.source, c.target} : Set (SiteAtLevel L m K (n + 1))),
      stepGaugeLogarithm s c 0 W₀ y = 0 := by
    intro y hy
    simp [stepGaugeLogarithm, hgauge1 y hy, logSeries_one]
  have hvar0 : stepVariable s c 0 W₀ = 0 := by
    obtain ⟨-, hdP, hdW, hnear⟩ := hb0.variable_bound.1
    have hav := ((hA L hL m K n hm hn s c hc (twistedConfig c 0 W₀) W₀ hdP.1 hdW.1
      hEq).2 hdP).1
    have hav' : schemeBlockAverage s (twistedConfig c 0 W₀) c = schemeBlockAverage s W₀ c := hav
    have hform : stepProduct s c 0 W₀ =
        schemeBlockAverage s W₀ c * (schemeBlockAverage s W₀ c)⁻¹ := by
      unfold stepProduct
      rw [hgauge1 c.source (Or.inl rfl), hgauge1 c.target (Or.inr rfl), hav']
      simp
    have hone : stepProduct s c 0 W₀ = 1 := by
      rw [hform] at hnear ⊢
      exact mul_inv_eq_one_of_near hnear
    simp [stepVariable, hone, logSeries_one]
  refine ⟨fun y hy x hx => ?_, fun y hy => ?_, ?_⟩
  · exact operatorNorm_le_of_map_zero (G := fun a => stepLog s c a W₀ y x) hH hE _
      (hol₁ y hy x hx) (fun a' ha' => ((hb a' ha').log_bound y hy x hx).2) (hlog0 y hy x hx)
      hr0 a ha
  · exact operatorNorm_le_of_map_zero (G := fun a => stepGaugeLogarithm s c a W₀ y) hH hE _
      (hol₂ y hy) (fun a' ha' => ((hb a' ha').gauge_bound y hy).2.2) (hgl0 y hy) hr0 a ha
  · exact operatorNorm_le_of_map_zero (G := fun a => stepVariable s c a W₀) hH hE _
      hol₃ (fun a' ha' => (hb a' ha').variable_bound.2) hvar0 hr0 a ha
end YangMills.Construction.PeriodicLattice
