import YangMills.Construction.PeriodicOperators.IndexSetsOfATower
import YangMills.Construction.PeriodicOperators.InterpolationOfTheLogarithmicNumber
import YangMills.Construction.PeriodicOperators.LocalOperatorFunctionsAndTheirJets
import YangMills.Construction.Towers.TheDeterminantsWithoutConstraint
import YangMills.Construction.Towers.TheFormulaOfTheRemainder
import YangMills.Construction.Towers.TheMiddleJetsOfTheRemainderAreInvertible
import Mathlib
set_option autoImplicit false
open Set
open scoped ENNReal
noncomputable section
namespace YangMills.Construction.Tower.FullSpace.BackgroundJets.RemainderJets.Formula
open YangMills.Construction.PeriodicOperators
open YangMills.Construction.PeriodicOperators.JetQuad
section Path
variable {I : PeriodicData}
theorem correction_eq_path_sub (A W : JetQuad I I) :
    W = add (unitShiftedPath A W 1) (smul (-1) (unitShiftedPath A W 0)) := by
  obtain ⟨w0, w1, w2, w3⟩ := W
  simp only [unitShiftedPath, JetNormsAffine.affinePath, add, smul]
  congr 1 <;> (funext κ; simp; module)
theorem operator_eq_path_sub_one (A W : JetQuad I I) :
    A = add (unitShiftedPath A W 0) (smul (-1) (one I)) := by
  obtain ⟨a0, a1, a2, a3⟩ := A
  simp only [unitShiftedPath, JetNormsAffine.affinePath,
    addScalarJet, add, smul, one]
  congr 1 <;> (funext κ; simp <;> module)
theorem isJet_of_path_ends (hLoc : JetDomains.OpFunJetTheory)
    (hI : IsPeriodic I) {δ : ℝ} {p : Fin 4 → ℂ} (A W : JetQuad I I)
    (h0 : IsJet δ p (unitShiftedPath A W 0)) (h1 : IsJet δ p (unitShiftedPath A W 1)) :
    IsJet δ p A ∧ IsJet δ p W := by
  have F := hLoc.2.2 I I I hI hI hI δ p h0.pos_width h0.mem_imStrip
  constructor
  · rw [operator_eq_path_sub_one A W]
    exact F.add_isJet _ _ h0 (F.smul_isJet _ _ F.one_isJet)
  · rw [correction_eq_path_sub A W]
    exact F.add_isJet _ _ h1 (F.smul_isJet _ _ h0)
theorem uniformlyBoundedInverses_of_invertibleOnStrip {C : ℝ} {p : Fin 4 → ℂ} (T : ℝ → JetQuad I I)
    (h : ∀ s ∈ Icc (0 : ℝ) 1, MiddleJetsInvertible.InvertibleOnStrip C p (T s)) :
    LogNumberInterpolation.UniformlyBoundedInverses stripHalfWidth T :=
  ⟨ENNReal.ofReal C, ENNReal.ofReal_lt_top, fun s hs => iSup₂_le fun κ hκ => (h s hs).2 κ hκ⟩
end Path
theorem one_mem_Ioi_threshold {z : ℝ} (hpos : 0 < stripHalfWidth)
    (h : massWidth (1 / 40) = stripHalfWidth) (hz : z = 1) : z ∈ Ioi (25 * stripHalfWidth ^ 2) := by
  subst hz
  have hle : stripHalfWidth ≤ 1 / 5 * Real.sqrt (1 / 40) := by
    have := min_le_right stripHalfWidth (1 / 5 * Real.sqrt (1 / 40))
    rwa [show min stripHalfWidth (1 / 5 * Real.sqrt (1 / 40)) = stripHalfWidth from h] at this
  have hsq : Real.sqrt (1 / 40) ^ 2 = 1 / 40 := Real.sq_sqrt (by norm_num)
  have h2 : stripHalfWidth ^ 2 ≤ (1 / 5 * Real.sqrt (1 / 40)) ^ 2 :=
    pow_le_pow_left₀ hpos.le hle 2
  have h3 : (1 / 5 * Real.sqrt (1 / 40)) ^ 2 = 1 / 1000 := by
    rw [mul_pow, hsq]; norm_num
  show 25 * stripHalfWidth ^ 2 < 1
  nlinarith
theorem massiveLogFnSharp_eq (L k : ℕ) (p : Fin 4 → ℂ) (μPlus μMinus : Fin 4)
    (h1 : (1 : ℝ) ∈ Ioi (25 * stripHalfWidth ^ 2))
    (hK : MassJets.MassDerivatives p (edgeOperatorJet L k p μPlus μMinus))
    (hS : MassJets.MassDerivatives p (vertexOperatorJet L k p μPlus μMinus)) :
    massiveLogFnSharp L k p μPlus μMinus =
      logNumber p (addScalarJet (vertexOperatorJet L k p μPlus μMinus) 1) -
        1 / 2 * logNumber p (addScalarJet (edgeOperatorJet L k p μPlus μMinus) 1) -
        (traceNumber (invJet p (addScalarJet (vertexOperatorJet L k p μPlus μMinus) 1)) -
          1 / 2 * traceNumber (invJet p (addScalarJet (edgeOperatorJet L k p μPlus μMinus) 1))) +
        1 / 2 * (-traceNumber (invJetSq p (addScalarJet (vertexOperatorJet L k p μPlus μMinus) 1)) -
          1 / 2 * -traceNumber (invJetSq p (addScalarJet (edgeOperatorJet L k p μPlus μMinus) 1))) := by
  set f : ℝ → ℂ := fun y => logNumber p (addScalarJet (vertexOperatorJet L k p μPlus μMinus) y)
    with hf
  set g : ℝ → ℂ := fun y => logNumber p (addScalarJet (edgeOperatorJet L k p μPlus μMinus) y)
    with hg
  have hopen : IsOpen (Ioi (25 * stripHalfWidth ^ 2)) := isOpen_Ioi
  have hfd : ∀ z ∈ Ioi (25 * stripHalfWidth ^ 2), DifferentiableAt ℝ f z := fun z hz =>
    (hS.1.differentiableOn (by norm_num)).differentiableAt (hopen.mem_nhds hz)
  have hgd : ∀ z ∈ Ioi (25 * stripHalfWidth ^ 2), DifferentiableAt ℝ g z := fun z hz =>
    (hK.1.differentiableOn (by norm_num)).differentiableAt (hopen.mem_nhds hz)
  have hfd' : DifferentiableAt ℝ (deriv f) 1 :=
    ((hS.1.deriv_of_isOpen (m := 1) hopen (by norm_num)).differentiableOn
      (by norm_num)).differentiableAt (hopen.mem_nhds h1)
  have hgd' : DifferentiableAt ℝ (deriv g) 1 :=
    ((hK.1.deriv_of_isOpen (m := 1) hopen (by norm_num)).differentiableOn
      (by norm_num)).differentiableAt (hopen.mem_nhds h1)
  have hM : massiveLogFn L k p μPlus μMinus = fun z => f z - 1 / 2 * g z := rfl
  have hderiv : ∀ z ∈ Ioi (25 * stripHalfWidth ^ 2),
      deriv (massiveLogFn L k p μPlus μMinus) z = deriv f z - 1 / 2 * deriv g z := by
    intro z hz
    rw [hM]
    exact ((hfd z hz).hasDerivAt.sub ((hgd z hz).hasDerivAt.const_mul (1 / 2 : ℂ))).deriv
  have hderiv2 : deriv (deriv (massiveLogFn L k p μPlus μMinus)) 1 =
      deriv (deriv f) 1 - 1 / 2 * deriv (deriv g) 1 := by
    have hev : deriv (massiveLogFn L k p μPlus μMinus) =ᶠ[nhds 1]
        fun z => deriv f z - 1 / 2 * deriv g z :=
      Filter.eventuallyEq_of_mem (hopen.mem_nhds h1) fun z hz => hderiv z hz
    rw [hev.deriv_eq]
    exact (hfd'.hasDerivAt.sub (hgd'.hasDerivAt.const_mul (1 / 2 : ℂ))).deriv
  have h1f := hS.2 1 h1
  have h1g := hK.2 1 h1
  unfold massiveLogFnSharp
  rw [hderiv2, hderiv 1 h1, h1f.1, h1g.1, h1f.2, h1g.2]
  rfl
theorem remainderFormula_holds
    (hInterp : LogNumberInterpolation.Claim)
    (hDet : UnconstrainedDeterminants.PolarizationLogDetFormula)
    (hMiddle : MiddleJetsInvertible.MiddleJetsInvertibleClaim)
    (hMass : MassJets.MassJetsClaim)
    (hTower : TowerIndexSets.Claim)
    (hLoc : JetDomains.OpFunJetTheory) :
    RemainderFormula := by
  intro L hL hStd k hk p hp μPlus μMinus
  obtain ⟨C, hC⟩ := hMiddle
  obtain ⟨hfam, -, -, -, -⟩ := hC L hStd k hk p hp μPlus μMinus
  obtain ⟨-, -, h40, hmass⟩ := hMass L hStd k hk
  obtain ⟨hDK, hDS⟩ := hmass p hp μPlus μMinus
  have hZero : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := by norm_num
  have hOne : (1 : ℝ) ∈ Icc (0 : ℝ) 1 := by norm_num
  obtain ⟨hVert, hEdge, -⟩ := hTower L hStd k 0 (Nat.zero_le k)
  have hjetE0 := (hfam 0 hZero).1.1.isJet
  have hpos : 0 < stripHalfWidth := hjetE0.pos_width
  have hstrip : p ∈ imStrip stripHalfWidth := hjetE0.mem_imStrip
  obtain ⟨hKjet, hVjet⟩ := isJet_of_path_ends hLoc hEdge
    (edgeOperatorJet L k p μPlus μMinus) (edgeCorrectionJet L k p μPlus μMinus)
    hjetE0 (hfam 1 hOne).1.1.isJet
  obtain ⟨hSjet, hRjet⟩ := isJet_of_path_ends hLoc hVert
    (vertexOperatorJet L k p μPlus μMinus) (vertexCorrectionJet L k p μPlus μMinus)
    (hfam 0 hZero).2.1.1.isJet (hfam 1 hOne).2.1.1.isJet
  have hedge : logNumber p (edgeMiddleJet L k p μPlus μMinus) = _ :=
    (hInterp stripHalfWidth p hpos hstrip _ hEdge _ _ hKjet hVjet
      (fun t ht => (hfam t ht).1.1) (fun t ht => (hfam t ht).2.2.1.1)
      (uniformlyBoundedInverses_of_invertibleOnStrip _ fun t ht => (hfam t ht).1)
      (uniformlyBoundedInverses_of_invertibleOnStrip _ fun t ht => (hfam t ht).2.2.1)).2
  have hvertex : logNumber p (vertexMiddleJet L k p μPlus μMinus) = _ :=
    (hInterp stripHalfWidth p hpos hstrip _ hVert _ _ hSjet hRjet
      (fun t ht => (hfam t ht).2.1.1) (fun t ht => (hfam t ht).2.2.2.1)
      (uniformlyBoundedInverses_of_invertibleOnStrip _ fun t ht => (hfam t ht).2.1)
      (uniformlyBoundedInverses_of_invertibleOnStrip _ fun t ht => (hfam t ht).2.2.2)).2
  have hthreshold : (1 : ℝ) ∈ Ioi (25 * stripHalfWidth ^ 2) :=
    one_mem_Ioi_threshold hpos (h40 (1 / 40) le_rfl) rfl
  have hsharp := massiveLogFnSharp_eq L k p μPlus μMinus hthreshold hDK hDS
  have hformula := (hDet L hL hStd k hk).2 p hp μPlus μMinus
  rw [hformula, hsharp, hedge, hvertex]
  simp only [unitShiftedInverse, edgeRemainder, vertexRemainder]
  ring
end YangMills.Construction.Tower.FullSpace.BackgroundJets.RemainderJets.Formula
end
