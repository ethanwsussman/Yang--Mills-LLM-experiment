import YangMills.Construction.OneLoopLaw.CovarianceOfASymbolProof
import YangMills.Construction.PeriodicOperators.IndexSetsOfATower
import YangMills.Construction.PeriodicOperators.QuotientsTransposesAndNorm
import YangMills.Construction.Towers.SecondDifferentialsOnTheToriOfALocalSetting
import YangMills.Construction.Towers.TheAbelianOperatorsAsValuesOfTheOperatorFunctions
import YangMills.Construction.Towers.TheAbelianOperatorsGiveLocalSettings
import YangMills.Construction.Towers.TheFormsOfBondsAsFieldsOnTheClasses
import YangMills.Construction.Towers.TheOperatorFunctionsOfTheMassiveFunctionalAreLocal
import YangMills.Construction.Towers.ThePolarisationOfTheMassiveFamilyBySecondDifferentials
import YangMills.Construction.Towers.TheSecondDerivativesOfTheDensityByLogarithmicDensities
import YangMills.Construction.Towers.TheSumOverTheSitesOfTheSecondDerivativesOfTheDensity
import Mathlib
set_option autoImplicit false
open Filter Topology YangMills.Construction.OperatorCalculus
open YangMills.Construction.Tower.UnitLatticeL2 YangMills.Construction.Tower.LocalFamilies
open YangMills.Construction.Tower.MassiveOpFunctions
open YangMills.Construction.PeriodicOperators YangMills.Construction.PeriodicOperators.UnitFieldTraces
open YangMills.Construction.PeriodicOperators.LogDetSecondDerivs
noncomputable section
namespace YangMills.Construction.Tower.AbelianFieldDensity.SiteSum
variable {L : ℕ}
theorem exists_forall_ge_of_eventuallyForSides (hL : 2 ≤ L) {P : ℕ → Prop}
    (h : PeriodicOperators.Tempered.EventuallyForSides L P) :
    ∃ n₀, 1 ≤ n₀ ∧ ∀ n, n₀ ≤ n → P n := by apply _root_.YangMills.Construction.OneLoopLaw.SymbolCovariance.eventually_of_eventuallyForSides <;> assumption
def latticeVertex (L : ℕ) (n : Fin 4 → ℤ) : FullSpace.Vertex L 0 0 :=
  FullSpace.vertexImage (intShift n) (0 : FullSpace.Vertex L 0 0)
theorem latticeVertex_coe (hS : IsPeriodic (colourVertices L 0 0)) (n : Fin 4 → ℤ) :
    (latticeVertex L n : InfiniteLattice.AmbientSpace) = castVec n := by
  have h := hS.pos_translate n ((0 : Fin 3), (0 : FullSpace.Vertex L 0 0))
  have h' : (latticeVertex L n : InfiniteLattice.AmbientSpace) =
      ((0 : FullSpace.Vertex L 0 0) : InfiniteLattice.AmbientSpace) + castVec n := h
  rw [h']
  simp
theorem latticeVertex_bijective (hS : IsPeriodic (colourVertices L 0 0))
    (hint : ∀ y : FullSpace.Vertex L 0 0, ∃ n : Fin 4 → ℤ,
      (y : InfiniteLattice.AmbientSpace) = castVec n) :
    Function.Bijective (latticeVertex L) := by
  constructor
  · intro m n h
    have h' := congrArg (fun y : FullSpace.Vertex L 0 0 => (y : InfiniteLattice.AmbientSpace)) h
    simp only [latticeVertex_coe hS] at h'
    funext μ
    have := congrFun h' μ
    simpa [castVec] using this
  · intro y
    obtain ⟨n, hn⟩ := hint y
    exact ⟨n, Subtype.ext ((latticeVertex_coe hS n).trans hn.symm)⟩
open Classical in
theorem smul_siteIndicator_add_eq_thirdPauliField (c c' : FullSpace.PositiveEdge (meshAt L 0 0))
    (s t : ℝ) :
    (s : ℂ) • siteIndicator (colourEdges L 0 0) ((2 : Fin 3), c) +
        (t : ℂ) • siteIndicator (colourEdges L 0 0) ((2 : Fin 3), c') =
      thirdPauliField (twoBondField c c' s t) := by
  funext κ
  obtain ⟨a, d⟩ := κ
  have hu : ∀ c₀ : FullSpace.PositiveEdge (meshAt L 0 0),
      siteIndicator (colourEdges L 0 0) ((2 : Fin 3), c₀) (a, d) =
        if a = 2 ∧ d = c₀ then 1 else 0 := by
    intro c₀
    unfold siteIndicator
    by_cases h : a = 2 ∧ d = c₀
    · rw [if_pos h, if_pos]
      exact Prod.ext h.1 h.2
    · rw [if_neg h, if_neg]
      exact fun h' => h ⟨congrArg Prod.fst h', congrArg Prod.snd h'⟩
  show (s : ℂ) * siteIndicator (colourEdges L 0 0) ((2 : Fin 3), c) (a, d) +
      (t : ℂ) * siteIndicator (colourEdges L 0 0) ((2 : Fin 3), c') (a, d) =
    thirdPauliField (twoBondField c c' s t) (a, d)
  rw [hu, hu]
  by_cases ha : a = 2
  · subst ha
    by_cases h₁ : d = c <;> by_cases h₂ : d = c' <;>
      simp [thirdPauliField, twoBondField, bondIndicator, h₁, h₂] <;> split_ifs <;> simp
  · simp [thirdPauliField, ha]
theorem secondDerivativeSiteSum_holds (hSum : LogDensityHessianSum)
    (hTori : PeriodicHessianLimit)
    (hValues : AbelianOperatorsAreOpFunValues)
    (hForms : MassiveOperators.EdgeFormIsQuotIndicator)
    (hPolar : HessianBySecondDerivs.HessianIdentity)
    (hLocal : Locality.OpFunsLocal)
    (hIndex : TowerIndexSets.Claim)
    (hQuot : Quotients.QuotientTransposeNorm)
    (hSettings : AbelianOperatorsLocalExpansion)
    (hSplit : SecondDerivViaLogTraces.Statement) : SecondDerivativeSiteSum := by
  classical
  intro z hz L hL q q' x x' hx hx'
  have hL2 : 2 ≤ L := by
    have := hL.2
    omega
  obtain ⟨hS, hBd, -⟩ := hIndex L hL 0 0 le_rfl
  obtain ⟨loc₁, loc₂, -⟩ := (hLocal L hL z hz).1
  obtain ⟨C, hC, hset⟩ := hSettings z hz
  obtain ⟨setS, setB⟩ := hset L hL
  have hbij := latticeVertex_bijective hS fun y => setS.space.placement.on_lattice ((0 : Fin 3), y)
  generalize hb : FullSpace.forwardEdge x q.2 = b
  generalize hb' : FullSpace.forwardEdge x' q'.2 = b'
  set A₁ := variationTrace (laplacianOp (L := L)) z b b' with hA₁
  set A₂ := variationTrace (AbelianFieldDensity.massiveOp (L := L)) z b b' with hA₂
  have hsum : HasSum (fun y : FullSpace.Vertex L 0 0 => AbelianFieldDensity.secondDerivative z y b b')
      (A₁ - (1 / 2 : ℂ) * A₂) := by
    have H₁ := hSum (VertexIndex L) _ (vertexPos L) (positiveEdgeInitial (L := L)) 3 4 z C
      (laplacianOp (L := L)) hz hC setS b b'
    have H₂ := hSum (EdgeIndex L) _ (edgePos L) (positiveEdgeInitial (L := L)) 12 4 z C
      (AbelianFieldDensity.massiveOp (L := L)) hz hC setB b b'
    have H := H₁.sub (H₂.mul_left (1 / 2 : ℂ))
    refine ((Equiv.ofBijective _ hbij).hasSum_iff).1 ?_
    have e : (fun y : FullSpace.Vertex L 0 0 => AbelianFieldDensity.secondDerivative z y b b') ∘
        ⇑(Equiv.ofBijective _ hbij) = fun n =>
          logTraceHessian (vertexPos L) (laplacianOp (L := L)) z (castVec n) b b' -
            (1 / 2 : ℂ) * logTraceHessian (edgePos L) (AbelianFieldDensity.massiveOp (L := L)) z
              (castVec n) b b' := by
      funext n
      simp only [Function.comp_apply, Equiv.ofBijective_apply]
      rw [hSplit z hz L hL (latticeVertex L n) b b', latticeVertex_coe hS n]
    rw [e]
    exact H
  rw [hsum.tsum_eq, Metric.tendsto_atTop]
  intro ε hε
  have hread₁ : ∀ (c c' : FullSpace.PositiveEdge (meshAt L 0 0)) (s t : ℝ)
      (ι' ι : (colourVertices L 0 0).Carrier),
      vertexOpFun L z ((s : ℂ) • siteIndicator (colourEdges L 0 0) ((2 : Fin 3), c) +
          (t : ℂ) • siteIndicator (colourEdges L 0 0) ((2 : Fin 3), c')) ι' ι =
        matrixEntry (addScalar (laplacianOp (twoBondField c c' s t)) z) ι' ι := by
    intro c c' s t ι' ι
    rw [smul_siteIndicator_add_eq_thirdPauliField c c' s t]
    exact (hValues L hL z hz _).1 ι' ι
  have hread₂ : ∀ (c c' : FullSpace.PositiveEdge (meshAt L 0 0)) (s t : ℝ)
      (ι' ι : (colourEdges L 0 0).Carrier),
      edgeOpFun L z ((s : ℂ) • siteIndicator (colourEdges L 0 0) ((2 : Fin 3), c) +
          (t : ℂ) • siteIndicator (colourEdges L 0 0) ((2 : Fin 3), c')) ι' ι =
        matrixEntry (addScalar (AbelianFieldDensity.massiveOp (twoBondField c c' s t)) z) ι' ι := by
    intro c c' s t ι' ι
    rw [smul_siteIndicator_add_eq_thirdPauliField c c' s t]
    exact (hValues L hL z hz _).2 ι' ι
  obtain ⟨s₁, hs₁⟩ := hTori (colourEdges L 0 0) (colourVertices L 0 0) _
    (fun c : FullSpace.PositiveEdge (meshAt L 0 0) => ((2 : Fin 3), c)) (positiveEdgeInitial (L := L))
    3 4 z C (laplacianOp (L := L)) (vertexOpFun L z) hBd hS hz hC loc₁ setS hread₁ b b' (ε / 2)
    (by positivity)
  obtain ⟨s₂, hs₂⟩ := hTori (colourEdges L 0 0) (colourEdges L 0 0) _
    (fun c : FullSpace.PositiveEdge (meshAt L 0 0) => ((2 : Fin 3), c)) (positiveEdgeInitial (L := L))
    12 4 z C (AbelianFieldDensity.massiveOp (L := L)) (edgeOpFun L z) hBd hBd hz hC loc₂ setB hread₂
    b b' (ε / 2) (by positivity)
  obtain ⟨n₀, hn₀, hpol⟩ := exists_forall_ge_of_eventuallyForSides hL2 (hPolar L hL z hz)
  refine ⟨max n₀ (max s₁ s₂), fun n hn => ?_⟩
  have hn₁ : n₀ ≤ n := le_trans (le_max_left _ _) hn
  have hn₂ : max s₁ s₂ ≤ n := le_trans (le_max_right _ _) hn
  have hn0 : 0 < n := lt_of_lt_of_le hn₀ hn₁
  have hbig : n ≤ 2 * L ^ n := by
    have := (Nat.lt_pow_self (n := n) (by omega : 1 < L))
    omega
  have hside : 0 < 2 * L ^ n := by positivity
  have : Finite ((colourEdges L 0 0).QuotMod (2 * L ^ n)) :=
    (hQuot _ _ hBd hBd _ hside).1.2.1
  obtain ⟨N, ⟨e'⟩⟩ := Finite.exists_equiv_fin ((colourEdges L 0 0).QuotMod (2 * L ^ n))
  have e := e'.symm
  obtain ⟨f₁, g₁⟩ := hForms L hL n hn0 q x hx
  obtain ⟨f₂, g₂⟩ := hForms L hL n hn0 q' x' hx'
  have hp := hpol n hn₁ N e _ f₁ _ f₂
  rw [dist_eq_norm, hp, g₁, g₂, hb, hb']
  set D₁ := logDetSecondDeriv (colourEdges L 0 0) (colourVertices L 0 0) (vertexOpFun L z) e
    (quotIndicator (colourEdges L 0 0) (2 * L ^ n) ((2 : Fin 3), b))
    (quotIndicator (colourEdges L 0 0) (2 * L ^ n) ((2 : Fin 3), b'))
  set D₂ := logDetSecondDeriv (colourEdges L 0 0) (colourEdges L 0 0) (edgeOpFun L z) e
    (quotIndicator (colourEdges L 0 0) (2 * L ^ n) ((2 : Fin 3), b))
    (quotIndicator (colourEdges L 0 0) (2 * L ^ n) ((2 : Fin 3), b'))
  have b₁ : ‖D₁ - A₁‖ < ε / 2 :=
    hs₁ (2 * L ^ n) (le_trans (le_trans (le_max_left _ _) hn₂) hbig) N e
  have b₂ : ‖D₂ - A₂‖ < ε / 2 :=
    hs₂ (2 * L ^ n) (le_trans (le_trans (le_max_right _ _) hn₂) hbig) N e
  have hdec : D₁ - 1 / 2 * D₂ - (A₁ - 1 / 2 * A₂) = (D₁ - A₁) - (1 / 2 : ℂ) * (D₂ - A₂) := by ring
  rw [hdec]
  calc ‖(D₁ - A₁) - (1 / 2 : ℂ) * (D₂ - A₂)‖
      ≤ ‖D₁ - A₁‖ + ‖(1 / 2 : ℂ) * (D₂ - A₂)‖ := norm_sub_le _ _
    _ = ‖D₁ - A₁‖ + 1 / 2 * ‖D₂ - A₂‖ := by simp
    _ < ε := by linarith
end YangMills.Construction.Tower.AbelianFieldDensity.SiteSum
end
