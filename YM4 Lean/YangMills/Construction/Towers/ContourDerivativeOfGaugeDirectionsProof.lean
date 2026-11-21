import YangMills.Construction.Lattice.BareBaseSitesOfTheSchemesProof
import YangMills.Construction.Towers.CompositesOfTheLiftsAndLayersOfSites
import YangMills.Construction.Towers.ContourDerivativeOfGaugeDirections
import YangMills.Construction.Towers.CovariantDifferenceRelationsOfAStepOfASideProof
import YangMills.Construction.Towers.DerivativeOfTheContourLogarithmAlongCurves
import YangMills.Construction.Towers.GaugeAndIsometricImagesAreConfigurations
import YangMills.Construction.Towers.GaugeDirectionsInTheLeftChartProof
import YangMills.Construction.Towers.RealAndCovariantDifferentialsOfTheChain
import YangMills.Construction.Towers.TheChainOfABlockField
import Mathlib
set_option autoImplicit false
open Set Filter
open scoped Topology Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction.Tower
namespace GaugeCurveLemmas
open Matrices ComplexMatrix2
variable {L n k : ℕ}
private theorem isPositivelyOriented_or_opposite {m : ℕ} {j : ℤ} (b : PeriodicLattice.Bond L m j) :
    b.IsPositivelyOriented ∨ b.opposite.IsPositivelyOriented := by apply _root_.YangMills.SharedProofs.p7155 <;> assumption
private theorem complexBlockAverage_of_meanOfDefined {i : ℕ}
    {w : Edge L n k i → Option ComplexMatrix2}
    {c : Edge L n k (i + 1)} {v : ComplexMatrix2}
    (h : LevelwiseMeans.meanOfDefined w c = some v) :
    PeriodicLattice.complexBlockAverage (LevelwiseMeans.valuesOrOne w) c = v := by
  unfold LevelwiseMeans.meanOfDefined at h
  split_ifs at h
  exact Option.some.inj h
private theorem complexBlockFieldAtLevel_eq_smoothingIter {U : Edge L n k 0 → ComplexMatrix2}
    (h : ∀ i ≤ k, ∀ c : Edge L n k i, LevelwiseMeans.levelwiseMean U i c =
      some (smoothingIter L n k i U c)) :
    ∀ i ≤ k, PeriodicLattice.complexBlockFieldAtLevel i U = smoothingIter L n k i U := by
  intro i
  induction i with
  | zero =>
    intro hi
    funext c
    exact Option.some.inj (h 0 hi c)
  | succ i ih =>
    intro hi
    have hprev := ih (by omega)
    have hf : LevelwiseMeans.valuesOrOne (LevelwiseMeans.levelwiseMean U i) =
        PeriodicLattice.complexBlockFieldAtLevel i U := by
      funext b
      simp only [LevelwiseMeans.valuesOrOne, h i (by omega) b, hprev, Option.getD_some]
    have hstep : PeriodicLattice.complexBlockFieldAtLevel (i + 1) U =
        PeriodicLattice.complexBlockAverage (PeriodicLattice.complexBlockFieldAtLevel i U) := rfl
    funext c
    have e := h (i + 1) hi c
    rw [hstep]
    by_cases hc : c.IsPositivelyOriented
    · simp only [LevelwiseMeans.levelwiseMean, if_pos hc] at e
      have := complexBlockAverage_of_meanOfDefined e
      rwa [hf] at this
    · have hr : c.opposite.IsPositivelyOriented :=
        (isPositivelyOriented_or_opposite c).resolve_left hc
      simp only [LevelwiseMeans.levelwiseMean, if_neg hc] at e
      obtain ⟨a, ha, hav⟩ := Option.map_eq_some_iff.1 e
      have hval := complexBlockAverage_of_meanOfDefined ha
      rw [hf] at hval
      have e₁ : PeriodicLattice.complexBlockAverage (PeriodicLattice.complexBlockFieldAtLevel i U)
            c.opposite =
          PeriodicLattice.complexBlockAverageOnPositive
            (PeriodicLattice.complexBlockFieldAtLevel i U) c.opposite :=
        if_pos hr
      have e₂ : PeriodicLattice.complexBlockAverage (PeriodicLattice.complexBlockFieldAtLevel i U) c =
          (PeriodicLattice.complexBlockAverageOnPositive
            (PeriodicLattice.complexBlockFieldAtLevel i U) c.opposite)⁻¹ := if_neg hc
      rw [e₂, ← e₁, hval]
      exact hav
private theorem covDiff_neg {j : ℕ} (V : Edge L n k j → ComplexMatrix2)
    (l : Vertex L n k j → ComplexMatrix2) : covDiff V (-l) = -covDiff V l := by apply _root_.YangMills.Construction.Tower.CovDiffStep.covDiff_neg <;> assumption
private theorem matExp_inv (Z : ComplexMatrix2) : (matExp Z)⁻¹ = matExp (-Z) := by apply _root_.YangMills.SharedProofs.p3399 <;> assumption
private theorem hasDerivAt_matExp_I_smul (a : ComplexMatrix2) (s : ℝ) :
    HasDerivAt (fun t : ℝ => matExp (Complex.I • ((t : ℂ) • a)))
      (matExp ((s : ℂ) • (Complex.I • a)) * (Complex.I • a)) s := by apply _root_.YangMills.Construction.Tower.CovDiffStep.hasDerivAt_matExp_I_smul <;> assumption
private theorem hasDerivAt_matExp_mul_inv_zero (a c : ComplexMatrix2) :
    HasDerivAt (fun t : ℝ => matExp (Complex.I • ((t : ℂ) • a)) *
      (matExp (Complex.I • ((t : ℂ) • c)))⁻¹) (Complex.I • (a - c)) 0 := by
  have h₁ := hasDerivAt_matExp_I_smul a 0
  have h₂ := hasDerivAt_matExp_I_smul (-c) 0
  have h := h₁.mul h₂
  have e : (fun t : ℝ => matExp (Complex.I • ((t : ℂ) • a)) *
      (matExp (Complex.I • ((t : ℂ) • c)))⁻¹) =
      (fun t : ℝ => matExp (Complex.I • ((t : ℂ) • a))) *
        (fun t : ℝ => matExp (Complex.I • ((t : ℂ) • (-c)))) := by
    funext t
    simp only [Pi.mul_apply]
    rw [matExp_inv, smul_neg, smul_neg]
  rw [e]
  refine HasDerivAt.congr_deriv h ?_
  have he : ∀ z : ComplexMatrix2, z = 0 → matExp z = 1 := by
    rintro _ rfl
    exact NormedSpace.exp_zero
  rw [he (((0 : ℝ) : ℂ) • (Complex.I • a)) (by simp),
    he (Complex.I • (((0 : ℝ) : ℂ) • a)) (by simp),
    he (((0 : ℝ) : ℂ) • (Complex.I • (-c))) (by simp),
    he (Complex.I • (((0 : ℝ) : ℂ) • (-c))) (by simp)]
  simp only [one_mul, mul_one, smul_neg, smul_sub]
  abel
private theorem differentiable_gaugeCurve (a c V : ComplexMatrix2) :
    Differentiable ℝ (fun t : ℝ => matExp (Complex.I • ((t : ℂ) • a)) * V *
      (matExp (Complex.I • ((t : ℂ) • c)))⁻¹) := by
  intro s
  have e : (fun t : ℝ => matExp (Complex.I • ((t : ℂ) • a)) * V *
      (matExp (Complex.I • ((t : ℂ) • c)))⁻¹) =
      (fun t : ℝ => matExp (Complex.I • ((t : ℂ) • a)) * V) *
        (fun t : ℝ => matExp (Complex.I • ((t : ℂ) • (-c)))) := by
    funext t
    simp only [Pi.mul_apply]
    rw [matExp_inv, smul_neg, smul_neg]
  rw [e]
  exact (((hasDerivAt_matExp_I_smul a s).mul_const V).mul
    (hasDerivAt_matExp_I_smul (-c) s)).differentiableAt
private theorem coe_toSublattice {L m : ℕ} (hL : 0 < L) {j j' : ℤ} (h : j ≤ j')
    (y : PeriodicLattice.Site L m j) :
    ((y.toSublattice j' : PeriodicLattice.Site L m j') : PeriodicLattice.FourTorus L m) = y := by apply _root_.YangMills.SharedProofs.p9023 <;> assumption
private theorem restrictVertexFunction_succ (hL : 0 < L) (i : ℕ)
    (l : Vertex L n k 0 → ComplexMatrix2) (y : Vertex L n k (i + 1)) :
    restrictVertexFunction i l (y.toSublattice (PeriodicLattice.levelDepth k i)) =
      restrictVertexFunction (i + 1) l y := by
  have h₁ : PeriodicLattice.levelDepth k (i + 1) ≤ PeriodicLattice.levelDepth k i := by
    simp only [PeriodicLattice.levelDepth]; push_cast; omega
  have h₂ : PeriodicLattice.levelDepth k i ≤ PeriodicLattice.levelDepth k 0 := by
    simp only [PeriodicLattice.levelDepth]; push_cast; omega
  have h₃ : PeriodicLattice.levelDepth k (i + 1) ≤ PeriodicLattice.levelDepth k 0 := h₁.trans h₂
  simp only [restrictVertexFunction, PeriodicLattice.restrictGaugeMap]
  congr 1
  apply Subtype.ext
  rw [coe_toSublattice hL h₂, coe_toSublattice hL h₁, coe_toSublattice hL h₃]
abbrev _root_.YangMills.SharedProofs.p11078 := @restrictVertexFunction_succ
end GaugeCurveLemmas
open Matrices ComplexMatrix2 GaugeCurveLemmas in
theorem gaugeDirectionContourDerivative_holds
    (hR : RealDerivEqComplexAtChainBottom)
    (hC : TrivialFieldAverages.AtTrivialField)
    (hChain : BlockFieldChainProperties)
    (hComp : ProlongCompositesAndVertexLayers.Statement)
    (hLev : LevelwiseMeans.LevelwiseMeansHold)
    (hExp : IterLeftChartExpansion)
    (hAvg : _root_.YangMills.Construction.Tower.SmoothingNearIdentity)
    (hDer : ContourLogDerivAlongCurves.Statement)
    (hGD : GaugeOrbitTangentInLeftChart.Statement)
    (hImg : GaugeAndSymmetryImages.statement)
    (hBlk : BlockStructure)
    (hLog : LeftChartFields.Claim)
    (hI : UnitaryLogarithmProperties) :
    GaugeDirectionContourDerivative := by
  intro L n k hL hn hk
  have hL0 : 0 < L := by have := hL.2; omega
  obtain ⟨hTop, -, -⟩ := hComp.1 L n k hL hn hk
  have hside := ((hLev L hL k hk).1 n hn)
  have hchain := (hChain L n k hL hn hk hL0).1
  have toBase : ∀ {P : (Edge L n k 0 → ComplexMatrix2) → Prop},
      EventuallyNearIdentity (fieldSpace L n k 0) P →
      EventuallyNearIdentity (fieldSpace L n k k) fun W => P (chainBottom W) := by
    intro P hP
    have h₁ : ∀ᶠ W in 𝓝[fieldSpace L n k k] trivialField L n k k,
        P (chosenProlongIter L n k (Nat.zero_le k) W) :=
      (hTop.tendsto 0 (Nat.zero_le k)).eventually hP
    have h₂ : ∀ᶠ W in 𝓝[fieldSpace L n k k] trivialField L n k k,
        chosenProlongIter L n k (Nat.zero_le k) W = chosenProlongComp L n k k W :=
      hTop.comp_zero_eq
    show ∀ᶠ W in 𝓝[fieldSpace L n k k] trivialField L n k k, P (chainBottom W)
    filter_upwards [h₁, h₂] with W a b
    rw [chainBottom_eq, ← b]
    exact a
  have toLevel : ∀ (i : ℕ), i ≤ k → ∀ {P : (Edge L n k i → ComplexMatrix2) → Prop},
      EventuallyNearIdentity (fieldSpace L n k i) P →
      EventuallyNearIdentity (fieldSpace L n k k)
        fun W => P (smoothingIter L n k i (chainBottom W)) := by
    intro i hi P hP
    exact toBase ((hside.iterate_tendsto i hi).eventually hP)
  have hlevels : ∀ i : Fin k, EventuallyNearIdentity (fieldSpace L n k k) fun W =>
      (smoothingIter L n k i (chainBottom W) ∈ fieldSpace L n k i) ∧
      (∀ u ∈ gaugeGroupAt L n k i,
        ∀ (y : Vertex L n k ((i : ℕ) + 1)),
          ∀ x ∈ PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k i) y,
          PeriodicLattice.meanContourHolonomy
              (PeriodicLattice.gaugeTransform u (smoothingIter L n k i (chainBottom W))) y x =
            u (y.toSublattice (PeriodicLattice.levelDepth k i)) *
              PeriodicLattice.meanContourHolonomy (smoothingIter L n k i (chainBottom W)) y x *
              (u x)⁻¹) ∧
      (∀ (I : Set ℝ) (γ : ℝ → Edge L n k i → ComplexMatrix2),
        IsDifferentiableFieldCurve PeriodicLattice.compactGaugeGroup I γ →
          γ 0 = smoothingIter L n k i (chainBottom W) →
          ∀ x : FineOnlyVertex L n k i,
            HasDerivAt
              (fun t => Complex.I⁻¹ •
                logSeries (PeriodicLattice.meanContourHolonomy (γ t) (cubeCentre x) x.1))
              (contourLogDeriv L n k i (smoothingIter L n k i (chainBottom W))
                (curveTangent γ) x) 0 ∧
            contourLogDeriv L n k i (smoothingIter L n k i (chainBottom W))
              (curveTangent γ) x ∈ hermitianTraceless) := by
    intro i
    have hi := i.is_lt
    have a₁ : EventuallyNearIdentity (fieldSpace L n k i) fun V => V ∈ fieldSpace L n k i :=
      eventually_mem_nhdsWithin
    have a₂ := (((hAvg.1 L hL).1 n k i hn hi).1).gauge_covariant
    have a₃ := hDer L n k i hL hn hi
    have b₁ := toLevel i hi.le a₁
    have b₂ := toLevel i hi.le a₂
    have b₃ := toLevel i hi.le a₃
    show ∀ᶠ W in 𝓝[fieldSpace L n k k] trivialField L n k k, _
    filter_upwards [b₁, b₂, b₃] with W c₁ c₂ c₃
    exact ⟨c₁, fun u hu y x hx => (c₂ u hu).2 y x hx, c₃⟩
  have hall : ∀ᶠ W in 𝓝[fieldSpace L n k k] trivialField L n k k, ∀ i : Fin k, _ :=
    Filter.eventually_all.2 hlevels
  have e₁ : ∀ᶠ W in 𝓝[fieldSpace L n k k] trivialField L n k k, _ := hchain
  have e₂ : ∀ᶠ W in 𝓝[fieldSpace L n k k] trivialField L n k k, _ :=
    toBase (hExp L n k hL hn hk)
  have e₃ : ∀ᶠ W in 𝓝[fieldSpace L n k k] trivialField L n k k, _ :=
    toBase hside.iterates_defined
  have e₄ : ∀ᶠ W in 𝓝[fieldSpace L n k k] trivialField L n k k, _ :=
    hR L n k hL hn hk
  show ∀ᶠ W in 𝓝[fieldSpace L n k k] trivialField L n k k, _
  filter_upwards [hall, e₁, e₂, e₃, e₄] with W hlev hW hexp hform hreal κ D hD i y x hxy hne
  have hi := i.is_lt
  obtain ⟨hVmem, hcov, hder⟩ := hlev i
  have hmember : descendingChain W hi.le = smoothingIter L n k i (chainBottom W) :=
    (hW.1 i hi.le).2
  have hax : PeriodicLattice.IsBlockAxialGauge k i univ (descendingChain W hi.le) := hW.2.1 i hi
  set V := smoothingIter L n k i (chainBottom W) with hVdef
  rw [hmember] at hax
  have hcb : PeriodicLattice.complexBlockFieldAtLevel i (chainBottom W) = V :=
    complexBlockFieldAtLevel_eq_smoothingIter (fun i hi c => (hform i hi).2.2.1 c) i hi.le
  have hsmall := hexp.1.1
  have hκ : ∀ z, (κ : Vertex L n k 0 → ComplexMatrix2) z ∈ hermitianTraceless :=
    fun z => κ.2.1 z (mem_univ z)
  set r : Vertex L n k i → ComplexMatrix2 :=
    restrictVertexFunction (i : ℕ) (κ : Vertex L n k 0 → ComplexMatrix2) with hr
  have hrsu : ∀ z, r z ∈ hermitianTraceless := fun z => hκ _
  have hform₁ : (smoothingIterDifferential L n k i (chainBottom W) D : Edge L n k i → ComplexMatrix2) =
      covDiff V r := by
    rw [hreal i hi.le D, hD,
      ((hC L hL).1 n k hn hk).2.2.2 i hi.le (chainBottom W) hsmall κ
        (fun z _ => (hκ z).2), hcb]
  set l : Vertex L n k i → ComplexMatrix2 := -r with hl
  have hlsu : ∀ z, l z ∈ hermitianTraceless := fun z => hermitianTraceless.neg_mem (hrsu z)
  let γ : ℝ → Edge L n k i → ComplexMatrix2 := fun t =>
    PeriodicLattice.gaugeTransform (expVertexFn ((t : ℂ) • l)) V
  have hVc : V ∈ fieldsIn L n k i PeriodicLattice.complexGaugeGroup :=
    ⟨fun b hb => (Matrix.mem_specialUnitaryGroup_iff.1 (hVmem.1 b hb)).2, hVmem.2⟩
  have hgt : ∀ t : ℝ, expVertexFn ((t : ℂ) • l) ∈ gaugeGroupAt L n k i := by
    intro t z
    have hz : (t : ℂ) • l z ∈ hermitianTraceless := by
      have := hermitianTraceless.smul_mem t (hlsu z)
      simpa [Complex.coe_smul] using this
    exact (hI.1 _ hz).2.2.2
  have hgd := ((hGD L k i hL hi.le).1 n hn).1 V hVc l
    (fun z => (hlsu z).2)
  obtain ⟨-, -, htan, -⟩ := hgd
  have htan' : curveTangent γ = covDiff V r := by
    show curveTangent (fun t : ℝ => PeriodicLattice.gaugeTransform
      (expVertexFn ((t : ℂ) • l)) V) = _
    rw [htan, hl, covDiff_neg, neg_neg]
  have hcurve : IsDifferentiableFieldCurve PeriodicLattice.compactGaugeGroup univ γ := by
    refine ⟨⟨isOpen_univ, ordConnected_univ, mem_univ 0⟩, fun t _ => ?_, fun b _ => ?_⟩
    · have himg := (hImg L k i hL hi.le).1 n hn V (expVertexFn ((t : ℂ) • l)) id hVc
        (fun z => (Matrix.mem_specialUnitaryGroup_iff.1 (hgt t z)).2)
        (fun _ _ => rfl) (by simp [MapsSublatticeOnto])
      exact himg.2.2.1 hVmem (hgt t)
    · exact (differentiable_gaugeCurve _ _ _).differentiableOn
  have hγ0 : γ 0 = V := by
    funext b
    simp [γ, PeriodicLattice.gaugeTransform, expVertexFn]
  have hd := (hder univ γ hcurve hγ0 x).1
  have hcentre : cubeCentre x = y := by
    have hblocks := ((hBlk L k ((i : ℕ) + 1) hL hk (by omega) hi).1 n hn).2.1
    have hun := hblocks.2.2 x.1 x.2
    have hs : x.1 ∈ PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k i) (cubeCentre x) ∧
        (x.1 : PeriodicLattice.FourTorus L n) ≠ cubeCentre x :=
      Classical.epsilon_spec (p := fun y : Vertex L n k ((i : ℕ) + 1) =>
        x.1 ∈ PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k i) y ∧
          (x.1 : PeriodicLattice.FourTorus L n) ≠ y) ⟨y, hxy, hne⟩
    exact hun.unique ⟨hs.1, hs.2⟩ ⟨hxy, hne⟩
  rw [hcentre] at hd
  set a := restrictVertexFunction ((i : ℕ) + 1) (κ : Vertex L n k 0 → ComplexMatrix2) y with ha
  set c := r x.1 with hc
  have hval : ∀ t : ℝ, PeriodicLattice.meanContourHolonomy (γ t) y x.1 =
      matExp (Complex.I • ((t : ℂ) • (-a))) * (matExp (Complex.I • ((t : ℂ) • (-c))))⁻¹ := by
    intro t
    have h := hcov _ (hgt t) y x.1 hxy
    have h1 : PeriodicLattice.meanContourHolonomy V y x.1 = 1 :=
      hax.2 y (mem_univ y) x.1 hxy hne
    have h2 : r (y.toSublattice (PeriodicLattice.levelDepth k i)) = a :=
      restrictVertexFunction_succ hL0 i _ y
    show PeriodicLattice.meanContourHolonomy (PeriodicLattice.gaugeTransform
      (expVertexFn ((t : ℂ) • l)) V) y x.1 = _
    rw [h, h1, mul_one]
    simp only [expVertexFn, Pi.smul_apply, hl, Pi.neg_apply, h2]
    rfl
  let Wt : ℝ → ComplexMatrix2 := fun t =>
    matExp (Complex.I • ((t : ℂ) • (-a))) * (matExp (Complex.I • ((t : ℂ) • (-c))))⁻¹
  have hW0 : Wt 0 = 1 := by simp [Wt]
  have hWd := hasDerivAt_matExp_mul_inv_zero (-a) (-c)
  have hWmem : MapsTo Wt univ PeriodicLattice.compactGaugeGroup := by
    intro t _
    have hu := hgt t
    have h₁ : matExp (Complex.I • ((t : ℂ) • (-a))) ∈ specialUnitary := by
      have h2 : r (y.toSublattice (PeriodicLattice.levelDepth k i)) = a :=
        restrictVertexFunction_succ hL0 i _ y
      have := hu (y.toSublattice (PeriodicLattice.levelDepth k i))
      simpa [expVertexFn, hl, h2] using this
    have h₂ : matExp (Complex.I • ((t : ℂ) • (-c))) ∈ specialUnitary := by
      have := hu x.1
      simpa [expVertexFn, hl, hc] using this
    have h₃ : (matExp (Complex.I • ((t : ℂ) • (-c))))⁻¹ ∈ specialUnitary := by
      rw [matExp_inv, ← smul_neg, ← smul_neg]
      have h4 : (t : ℂ) • (- -c) ∈ hermitianTraceless := by
        have := hermitianTraceless.smul_mem t (hermitianTraceless.neg_mem (hlsu x.1))
        simpa [Complex.coe_smul, hl, hc] using this
      exact (hI.1 _ h4).2.2.2
    exact Submonoid.mul_mem _ h₁ h₃
  obtain ⟨-, hdiff, hderiv, -⟩ := (hLog.1 univ ⟨isOpen_univ, ordConnected_univ, mem_univ 0⟩).1
    Wt hWmem hWd.differentiableAt
  simp only [hW0, inv_one, mul_one] at hdiff hderiv
  have hlogd : HasDerivAt (fun t => Complex.I⁻¹ • logSeries (Wt t))
      (Complex.I⁻¹ • deriv (fun t => logSeries (Wt t)) 0) 0 :=
    hdiff.hasDerivAt.const_smul (Complex.I⁻¹ : ℂ)
  have hfun : (fun t => Complex.I⁻¹ • logSeries (PeriodicLattice.meanContourHolonomy (γ t) y x.1)) =
      fun t => Complex.I⁻¹ • logSeries (Wt t) := by
    funext t
    rw [hval t]
  rw [hfun] at hd
  have hfinal := hd.unique hlogd
  rw [hderiv, hWd.deriv, smul_smul, inv_mul_cancel₀ Complex.I_ne_zero, one_smul] at hfinal
  have hgoal : contourFamily W D i x =
      contourLogDeriv L n k i V (curveTangent γ) x := by
    show contourLogDeriv L n k i (descendingChain W hi.le)
      (smoothingIterDifferential L n k i (chainBottom W) D : edgeFormSpace L n k i).1 x = _
    rw [hmember, htan']
    exact congrArg (fun B => contourLogDeriv L n k i V B x) hform₁
  rw [hgoal, hfinal]
  abel
end YangMills.Construction.Tower
end
