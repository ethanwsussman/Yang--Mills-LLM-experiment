import YangMills.Construction.ClusterExpansionOfAStep.PlaquettesUnderGaugesAndMoves
import YangMills.Construction.ColdChainAtEveryLevel.FirstOrderOnAPlaquette
import Mathlib
set_option autoImplicit false
set_option linter.style.haveILetI false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction
namespace GaugeMotions
open BlockAverages BlockAverages.ChartCoordinates LatticePaths QuaternionLog PlaquetteLinearization
variable {F : BlockFrame}
section Exact
variable {j : ℕ}
theorem pathHolonomy_gaugeTransform (γ : F.Site j → UnitQuaternion) (X : F.GaugeField j) (x0 : F.Site j)
    (l : List PathStep) :
    ∀ v : LatticeFractionalIntegration.Lattice4,
      pathHolonomy (gaugeTransform γ X) (x0 + siteOfCoords j v) l =
        γ (x0 + siteOfCoords j v) * pathHolonomy X (x0 + siteOfCoords j v) l *
          (γ (x0 + siteOfCoords j (endpoint v l)))⁻¹ := by apply _root_.YangMills.Construction.BlockAverages.GaugeChange.pathHolonomy_gaugeTransform <;> assumption
theorem pathHolonomy_gaugeTransform_of_base (γ : F.Site j → UnitQuaternion) (X : F.GaugeField j)
    (x0 : F.Site j) (l : List PathStep) :
    pathHolonomy (gaugeTransform γ X) x0 l =
      γ x0 * pathHolonomy X x0 l * (γ (x0 + siteOfCoords j (endpoint 0 l)))⁻¹ := by
  have := pathHolonomy_gaugeTransform γ X x0 l 0
  rwa [add_siteOfCoords_zero] at this
def gaugedPathAverage (γ : F.Site j → UnitQuaternion) (X R : F.GaugeField j) (y : F.Site (j + 1)) : ℍ[ℝ] :=
  (1 / (24 * (F.blockSide : ℝ) ^ 4)) • ∑ h ∈ centredCube F.blockSide, ∑ π : Equiv.Perm (Fin 4),
    ((pathHolonomy X (refineSite y) (axisPath h π) * (γ (refineSite y + siteOfCoords j h))⁻¹ *
      (pathHolonomy R (refineSite y) (axisPath h π))⁻¹ : UnitQuaternion) : ℍ[ℝ])
theorem relativePathAverage_gaugeTransform (γ : F.Site j → UnitQuaternion) (X R : F.GaugeField j)
    (y : F.Site (j + 1)) :
    relativePathAverage (gaugeTransform γ X) R y = (γ (refineSite y) : ℍ[ℝ]) * gaugedPathAverage γ X R y := by
  unfold relativePathAverage gaugedPathAverage
  rw [mul_smul_comm, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun h _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun π _ => ?_
  rw [pathHolonomy_gaugeTransform_of_base, (axisPath_spec h π).2]
  simp only [Submonoid.coe_mul, mul_assoc]
theorem contourAverage_gaugeTransform (hodd : Odd F.blockSide) (hj : j + 1 ≤ F.top)
    (γ : F.Site j → UnitQuaternion) (X : F.GaugeField j) (c : F.Site (j + 1) × Fin 4) :
    contourAverage (gaugeTransform γ X) c = (γ (refineSite c.1) : ℍ[ℝ]) * contourAverage X c *
      (((γ (refineSite (c.1 + unitStep (j + 1) c.2)))⁻¹ : UnitQuaternion) : ℍ[ℝ]) := by
  unfold contourAverage
  rw [mul_smul_comm, smul_mul_assoc, Finset.mul_sum, Finset.sum_mul]
  congr 1
  refine Finset.sum_congr rfl fun h hh => ?_
  rw [Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun π _ => ?_
  rw [pathHolonomy_gaugeTransform_of_base, (bondContour_spec π c.2 hodd.pos hh).2]
  have e : refineSite c.1 + siteOfCoords j ((F.blockSide : ℤ) • LatticeFractionalIntegration.basisVector c.2) =
      refineSite (c.1 + unitStep (j + 1) c.2) := by
    rw [unitStep_eq, refineSite_add j hj]
    congr 2
  rw [e]
  simp only [Submonoid.coe_mul]
def liftGauge (X R : F.GaugeField j) (γ : F.Site j → UnitQuaternion) (y : F.Site (j + 1)) : UnitQuaternion :=
  balancingGauge (gaugeTransform γ X) R y * γ (refineSite y) * (balancingGauge X R y)⁻¹
theorem gaugedContourAverage_gaugeTransform (hodd : Odd F.blockSide) (hj : j + 1 ≤ F.top)
    (X R : F.GaugeField j) (γ : F.Site j → UnitQuaternion) (c : F.Site (j + 1) × Fin 4) :
    gaugedContourAverage (gaugeTransform γ X) (balancingGauge (gaugeTransform γ X) R) c =
      (liftGauge X R γ c.1 : ℍ[ℝ]) * gaugedContourAverage X (balancingGauge X R) c *
        (((liftGauge X R γ (c.1 + unitStep (j + 1) c.2))⁻¹ : UnitQuaternion) : ℍ[ℝ]) := by
  unfold gaugedContourAverage liftGauge
  rw [contourAverage_gaugeTransform hodd hj]
  simp only [mul_inv_rev, inv_inv, Submonoid.coe_mul, mul_assoc, inv_coe_mul_coe_mul]
theorem polarUnit_coe (g : UnitQuaternion) : polarUnit (g : ℍ[ℝ]) = g := by apply _root_.YangMills.Construction.BlockLines.polarUnit_coe <;> assumption
theorem polarUnit_coe_mul_mul_coe_inv (a b : UnitQuaternion) {q : ℍ[ℝ]} (hq : q ≠ 0) :
    polarUnit ((a : ℍ[ℝ]) * q * ((b⁻¹ : UnitQuaternion) : ℍ[ℝ])) = a * polarUnit q * b⁻¹ := by
  rw [polarUnit_mul (mul_ne_zero (coe_unitQuaternion_ne_zero a) hq) (coe_unitQuaternion_ne_zero _),
    polarUnit_mul (coe_unitQuaternion_ne_zero a) hq, polarUnit_coe, polarUnit_coe]
end Exact
section Levels
variable (R : F.FieldChain) (U : ChainChart F) (ξ : F.Site 0 → imaginaryQuaternions)
def gaugeAtLevel : (j : ℕ) → ℝ → F.Site j → UnitQuaternion
  | 0, τ, x => expUnit (τ • ξ x)
  | j + 1, τ, y => liftGauge (chartField R U j) (R j) (gaugeAtLevel j τ) y
theorem expUnit_zero : expUnit (0 : imaginaryQuaternions) = 1 := by apply _root_.YangMills.Construction.TorusFields.expUnit_zero <;> assumption
theorem gaugeAtLevel_zero : ∀ (j : ℕ) (y : F.Site j), gaugeAtLevel R U ξ j 0 y = 1 := by
  intro j
  induction j with
  | zero =>
    intro y
    simp [gaugeAtLevel, expUnit_zero]
  | succ j ih =>
    intro y
    have h1 : gaugeAtLevel R U ξ j 0 = fun _ => 1 := funext ih
    have h2 : gaugeTransform (fun _ => (1 : UnitQuaternion)) (chartField R U j) = chartField R U j := by
      funext x i
      simp [gaugeTransform]
    simp only [gaugeAtLevel, liftGauge, h1, h2]
    simp
theorem re_pureComponent (q : ℍ[ℝ]) : (pureComponent q).re = 0 := by apply _root_.YangMills.Construction.BlockAverages.re_pureComponent <;> assumption
def pureComponentCLM : ℍ[ℝ] →L[ℝ] imaginaryQuaternions :=
  ⟨{ toFun := fun q => ⟨pureComponent q, re_pureComponent q⟩
     map_add' := fun a b => Subtype.ext (pureComponent_add a b)
     map_smul' := fun r a => Subtype.ext (pureComponent_smul r a) },
    by
      refine Continuous.subtype_mk ?_ _
      unfold pureComponent
      fun_prop⟩
theorem coe_pureComponentCLM (q : ℍ[ℝ]) :
    ((pureComponentCLM q : imaginaryQuaternions) : ℍ[ℝ]) = pureComponent q := rfl
theorem pureComponent_of_re_eq_zero {q : ℍ[ℝ]} (h : q.re = 0) : pureComponent q = q := by apply _root_.YangMills.Construction.BlockAverages.pureComponent_of_re_eq_zero <;> assumption
def logUnit (g : UnitQuaternion) : imaginaryQuaternions := pureComponentCLM (qlog (g : ℍ[ℝ]))
theorem coe_logUnit {g : UnitQuaternion} (hg : ‖(g : ℍ[ℝ]) - 1‖ < rightRadius) :
    ((logUnit g : imaginaryQuaternions) : ℍ[ℝ]) = qlog g := by
  rw [logUnit, coe_pureComponentCLM, pureComponent_of_re_eq_zero (re_qlog (norm_coe_unitQuaternion g) hg)]
theorem expUnit_logUnit {g : UnitQuaternion} (hg : ‖(g : ℍ[ℝ]) - 1‖ < rightRadius) :
    expUnit (logUnit g) = g := by
  apply Subtype.ext
  show NormedSpace.exp ((logUnit g : imaginaryQuaternions) : ℍ[ℝ]) = g
  rw [coe_logUnit hg, qlogRadii_spec.exp_qlog _ hg]
theorem logUnit_expUnit {w : imaginaryQuaternions} (hw : ‖(w : ℍ[ℝ])‖ < leftRadius) :
    logUnit (expUnit w) = w := by
  apply Subtype.ext
  have h1 : qlog ((expUnit w : UnitQuaternion) : ℍ[ℝ]) = w := qlogRadii_spec.qlog_exp _ hw
  rw [logUnit, coe_pureComponentCLM, h1]
  exact pureComponent_of_re_eq_zero w.2
def bottomBondElement (τ : ℝ) (x : F.Site 0) (i : Fin 4) : UnitQuaternion :=
  gaugeAtLevel R U ξ 0 τ x * expUnit (U.fine x i) * R 0 x i *
    (gaugeAtLevel R U ξ 0 τ (x + unitStep 0 i))⁻¹ * (R 0 x i)⁻¹
def upperBondElement (τ : ℝ) (j : ℕ) (y : F.Site (j + 1)) (i : Fin 4) : UnitQuaternion :=
  gaugeAtLevel R U ξ (j + 1) τ y * expUnit (U.coarse j y i) * referenceDefect R j (y, i) *
    (gaugeAtLevel R U ξ (j + 1) τ y)⁻¹ * (referenceDefect R j (y, i))⁻¹
def gaugedChart (τ : ℝ) : ChainChart F :=
  ⟨fun x i => logUnit (bottomBondElement R U ξ τ x i), fun j y i => logUnit (upperBondElement R U ξ τ j y i)⟩
end Levels
section Curve
theorem star_pureComponent (q : ℍ[ℝ]) : star (pureComponent q) = - pureComponent q := by
  simp only [pureComponent, quaternion_star_real_smul, star_sub, star_star, ← smul_neg, neg_sub]
theorem star_coe_imaginary (w : imaginaryQuaternions) :
    star ((w : imaginaryQuaternions) : ℍ[ℝ]) = - (w : ℍ[ℝ]) := by
  have := star_pureComponent (w : ℍ[ℝ])
  rwa [pureComponent_of_re_eq_zero w.2] at this
theorem hasDerivAt_polarUnit_inv_mul {P : ℝ → ℍ[ℝ]} {dP : ℍ[ℝ]} (hP : HasDerivAt P dP 0) (h0 : P 0 ≠ 0) :
    HasDerivAt (fun τ => (((polarUnit (P τ))⁻¹ * polarUnit (P 0) : UnitQuaternion) : ℍ[ℝ]))
      (‖P 0‖⁻¹ • pureComponent ((((polarUnit (P 0))⁻¹ : UnitQuaternion) : ℍ[ℝ]) * (-dP))) 0 := by
  have hne : ∀ᶠ τ in nhds (0 : ℝ), P τ ≠ 0 := hP.continuousAt.eventually_ne h0
  set κ : ℍ[ℝ] := ((polarUnit (P 0) : UnitQuaternion) : ℍ[ℝ]) with hκ
  have hN : DifferentiableAt ℝ (fun τ => ‖P τ‖) 0 := hP.differentiableAt.norm ℝ h0
  set dN := deriv (fun τ => ‖P τ‖) 0
  have hN' : HasDerivAt (fun τ => ‖P τ‖) dN 0 := hN.hasDerivAt
  have hn0 : ‖P 0‖ ≠ 0 := norm_ne_zero_iff.2 h0
  have hinv : HasDerivAt (fun τ => ‖P τ‖⁻¹) (-dN / ‖P 0‖ ^ 2) 0 := hN'.fun_inv hn0
  have hu : HasDerivAt (fun τ => ‖P τ‖⁻¹ • P τ) (‖P 0‖⁻¹ • dP + (-dN / ‖P 0‖ ^ 2) • P 0) 0 :=
    hinv.smul hP
  have hs : HasDerivAt (fun τ => star (‖P τ‖⁻¹ • P τ) * κ)
      (star (‖P 0‖⁻¹ • dP + (-dN / ‖P 0‖ ^ 2) • P 0) * κ) 0 :=
    (starCLM.hasFDerivAt.comp_hasDerivAt (0 : ℝ) hu).mul_const κ
  have hev : (fun τ => (((polarUnit (P τ))⁻¹ * polarUnit (P 0) : UnitQuaternion) : ℍ[ℝ])) =ᶠ[nhds 0]
      fun τ => star (‖P τ‖⁻¹ • P τ) * κ := by
    filter_upwards [hne] with τ hτ
    rw [Submonoid.coe_mul, coe_unitQuaternion_inv, coe_polarUnit hτ]
  have hg := hs.congr_of_eventuallyEq hev
  set D := star (‖P 0‖⁻¹ • dP + (-dN / ‖P 0‖ ^ 2) • P 0) * κ with hD
  have hre : D.re = 0 := by
    have hr : HasDerivAt (fun τ => (((polarUnit (P τ))⁻¹ * polarUnit (P 0) : UnitQuaternion) : ℍ[ℝ]).re)
        D.re 0 :=
      reCLM.hasFDerivAt.comp_hasDerivAt (0 : ℝ) hg
    have hmax : IsLocalMax (fun τ => (((polarUnit (P τ))⁻¹ * polarUnit (P 0) : UnitQuaternion) : ℍ[ℝ]).re) 0 := by
      refine Filter.Eventually.of_forall fun τ => ?_
      have e0 : ((((polarUnit (P 0))⁻¹ * polarUnit (P 0) : UnitQuaternion) : ℍ[ℝ])).re = 1 := by simp
      show _ ≤ _
      simp only [e0]
      calc _ ≤ ‖(((polarUnit (P τ))⁻¹ * polarUnit (P 0) : UnitQuaternion) : ℍ[ℝ])‖ := quaternion_re_le_norm _
        _ = 1 := norm_coe_unitQuaternion _
    exact hmax.hasDerivAt_eq_zero hr
  have hpure : D = ‖P 0‖⁻¹ • pureComponent ((((polarUnit (P 0))⁻¹ : UnitQuaternion) : ℍ[ℝ]) * (-dP)) := by
    have e1 : D = ‖P 0‖⁻¹ • (star dP * κ) + ((-dN / ‖P 0‖ ^ 2) * ‖P 0‖ : ℝ) • (1 : ℍ[ℝ]) := by
      have e2 : star (P 0) * κ = (‖P 0‖ : ℝ) • (1 : ℍ[ℝ]) := by
        rw [hκ, coe_polarUnit h0, mul_smul_comm, Quaternion.star_mul_self,
          Quaternion.normSq_eq_norm_mul_self]
        ext <;> simp <;> field_simp
      rw [hD, star_add, quaternion_star_real_smul, quaternion_star_real_smul, add_mul, smul_mul_assoc,
        smul_mul_assoc, e2, smul_smul]
    have e3 : pureComponent D = D := pureComponent_of_re_eq_zero hre
    rw [← e3, e1, pureComponent_add, pureComponent_smul, pureComponent_smul, pureComponent_one, smul_zero,
      add_zero]
    congr 1
    have e4 : star dP * κ = star ((((polarUnit (P 0))⁻¹ : UnitQuaternion) : ℍ[ℝ]) * dP) := by
      rw [star_mul, coe_unitQuaternion_inv, star_star]
    rw [e4, pureComponent_star, mul_neg]
    exact (pureComponentHom.map_neg _).symm
  rw [← hpure]
  exact hg
theorem star_gaugeGeneratorAtLevel (R : F.FieldChain) (U : ChainChart F) (ξ : F.Site 0 → imaginaryQuaternions)
    (j : ℕ) (y : F.Site j) :
    star (gaugeGeneratorAtLevel R U ξ j y) = - gaugeGeneratorAtLevel R U ξ j y := by
  cases j with
  | zero => exact star_coe_imaginary _
  | succ j =>
    simp only [gaugeGeneratorAtLevel, quaternion_star_real_smul, star_pureComponent, smul_neg]
theorem hasDerivAt_gaugeAtLevel {S : Finset F.Cell} (hodd : Odd F.blockSide) (R : F.FieldChain)
    (U : ChainChart F) (ξ : F.Site 0 → imaginaryQuaternions)
    (hreg : ChartIsRegular S R U) : ∀ j, j ≤ F.top → ∀ y ∈ sitesOfCells S j,
    HasDerivAt (fun τ => ((gaugeAtLevel R U ξ j τ y : UnitQuaternion) : ℍ[ℝ]))
      (gaugeGeneratorAtLevel R U ξ j y) 0 := by
  intro j
  induction j with
  | zero =>
    intro _ y _
    have h := hasDerivAt_exp_smul_const (𝕂 := ℝ) ((ξ y : imaginaryQuaternions) : ℍ[ℝ]) (0 : ℝ)
    simpa [gaugeAtLevel, expUnit, gaugeGeneratorAtLevel] using h
  | succ j ih =>
    intro hj y hy
    have hj' : j ≤ F.top := by omega
    have hjn : j < F.top := by omega
    set X := chartField R U j with hX
    set P : ℝ → ℍ[ℝ] := fun τ => gaugedPathAverage (gaugeAtLevel R U ξ j τ) X (R j) y with hP
    have hP0 : P 0 = relativePathAverage X (R j) y := by
      simp only [hP, gaugedPathAverage, relativePathAverage]
      congr 1
      refine Finset.sum_congr rfl fun h _ => Finset.sum_congr rfl fun π _ => ?_
      rw [gaugeAtLevel_zero]
      simp
    have hne0 : P 0 ≠ 0 := by rw [hP0]; exact (hreg j hjn).1 y hy
    set M : ℍ[ℝ] := (1 / (24 * (F.blockSide : ℝ) ^ 4)) • ∑ h ∈ centredCube F.blockSide,
      ∑ π : Equiv.Perm (Fin 4),
        ((pathHolonomy X (refineSite y) (axisPath h π) : UnitQuaternion) : ℍ[ℝ]) *
          gaugeGeneratorAtLevel R U ξ j (refineSite y + siteOfCoords j h) *
          (((pathHolonomy (R j) (refineSite y) (axisPath h π))⁻¹ : UnitQuaternion) : ℍ[ℝ]) with hM
    have hdP : HasDerivAt P (-M) 0 := by
      have hterm : ∀ h ∈ centredCube F.blockSide, ∀ π : Equiv.Perm (Fin 4),
          HasDerivAt (fun τ => ((pathHolonomy X (refineSite y) (axisPath h π) *
            (gaugeAtLevel R U ξ j τ (refineSite y + siteOfCoords j h))⁻¹ *
            (pathHolonomy (R j) (refineSite y) (axisPath h π))⁻¹ : UnitQuaternion) : ℍ[ℝ]))
            (-(((pathHolonomy X (refineSite y) (axisPath h π) : UnitQuaternion) : ℍ[ℝ]) *
              gaugeGeneratorAtLevel R U ξ j (refineSite y + siteOfCoords j h) *
              (((pathHolonomy (R j) (refineSite y) (axisPath h π))⁻¹ : UnitQuaternion) : ℍ[ℝ]))) 0 := by
        intro h hh π
        have d := ih hj' _ (refineSite_add_mem_sitesOfCells hodd hj hy hh)
        have d2 : HasDerivAt
            (fun τ => star ((gaugeAtLevel R U ξ j τ (refineSite y + siteOfCoords j h) : UnitQuaternion) : ℍ[ℝ]))
            (star (gaugeGeneratorAtLevel R U ξ j (refineSite y + siteOfCoords j h))) 0 :=
          starCLM.hasFDerivAt.comp_hasDerivAt (0 : ℝ) d
        have d3 := (d2.const_mul ((pathHolonomy X (refineSite y) (axisPath h π) : UnitQuaternion) : ℍ[ℝ])).mul_const
          (((pathHolonomy (R j) (refineSite y) (axisPath h π))⁻¹ : UnitQuaternion) : ℍ[ℝ])
        rw [star_gaugeGeneratorAtLevel, mul_neg, neg_mul] at d3
        simp only [Submonoid.coe_mul, coe_unitQuaternion_inv] at d3 ⊢
        exact d3
      have hs : HasDerivAt (fun τ => ∑ h ∈ centredCube F.blockSide, ∑ π : Equiv.Perm (Fin 4),
          ((pathHolonomy X (refineSite y) (axisPath h π) *
            (gaugeAtLevel R U ξ j τ (refineSite y + siteOfCoords j h))⁻¹ *
            (pathHolonomy (R j) (refineSite y) (axisPath h π))⁻¹ : UnitQuaternion) : ℍ[ℝ]))
          (∑ h ∈ centredCube F.blockSide, ∑ π : Equiv.Perm (Fin 4),
            -(((pathHolonomy X (refineSite y) (axisPath h π) : UnitQuaternion) : ℍ[ℝ]) *
              gaugeGeneratorAtLevel R U ξ j (refineSite y + siteOfCoords j h) *
              (((pathHolonomy (R j) (refineSite y) (axisPath h π))⁻¹ : UnitQuaternion) : ℍ[ℝ]))) 0 :=
        HasDerivAt.fun_sum fun h hh => HasDerivAt.fun_sum fun π _ => hterm h hh π
      have hc := hs.const_smul (1 / (24 * (F.blockSide : ℝ) ^ 4) : ℝ)
      have e : (1 / (24 * (F.blockSide : ℝ) ^ 4) : ℝ) • (∑ h ∈ centredCube F.blockSide,
            ∑ π : Equiv.Perm (Fin 4),
            -(((pathHolonomy X (refineSite y) (axisPath h π) : UnitQuaternion) : ℍ[ℝ]) *
              gaugeGeneratorAtLevel R U ξ j (refineSite y + siteOfCoords j h) *
              (((pathHolonomy (R j) (refineSite y) (axisPath h π))⁻¹ : UnitQuaternion) : ℍ[ℝ]))) = -M := by
        simp only [hM, Finset.sum_neg_distrib, smul_neg]
      rw [e] at hc
      exact hc
    have hc := hasDerivAt_polarUnit_inv_mul hdP hne0
    have hev : (fun τ => ((gaugeAtLevel R U ξ (j + 1) τ y : UnitQuaternion) : ℍ[ℝ])) =ᶠ[nhds 0]
        fun τ => (((polarUnit (P τ))⁻¹ * polarUnit (P 0) : UnitQuaternion) : ℍ[ℝ]) := by
      have hne : ∀ᶠ τ in nhds (0 : ℝ), P τ ≠ 0 := hdP.continuousAt.eventually_ne hne0
      filter_upwards [hne] with τ hτ
      have e1 : balancingGauge (gaugeTransform (gaugeAtLevel R U ξ j τ) X) (R j) y =
          (polarUnit (P τ))⁻¹ * (gaugeAtLevel R U ξ j τ (refineSite y))⁻¹ := by
        unfold balancingGauge
        rw [relativePathAverage_gaugeTransform, polarUnit_mul (coe_unitQuaternion_ne_zero _) hτ, polarUnit_coe,
          mul_inv_rev]
      have e2 : (balancingGauge X (R j) y)⁻¹ = polarUnit (P 0) := by
        unfold balancingGauge
        rw [inv_inv, hP0]
      simp only [gaugeAtLevel, liftGauge]
      rw [e1, e2]
      simp [mul_assoc]
    have := hc.congr_of_eventuallyEq hev
    have hval : ‖P 0‖⁻¹ • pureComponent ((((polarUnit (P 0))⁻¹ : UnitQuaternion) : ℍ[ℝ]) * (- -M)) =
        gaugeGeneratorAtLevel R U ξ (j + 1) y := by
      simp only [gaugeGeneratorAtLevel, neg_neg]
      rw [hP0]
      rfl
    rw [hval] at this
    exact this
theorem hasDerivAt_logUnit_comp {g : ℝ → UnitQuaternion} {dg : ℍ[ℝ]}
    (hd : HasDerivAt (fun τ => ((g τ : UnitQuaternion) : ℍ[ℝ])) dg 0)
    (h : ‖((g 0 : UnitQuaternion) : ℍ[ℝ]) - 1‖ < rightRadius) :
    HasDerivAt (fun τ => logUnit (g τ)) (pureComponentCLM (fderiv ℝ qlog (g 0 : ℍ[ℝ]) dg)) 0 := by
  have h1 : HasFDerivAt qlog (fderiv ℝ qlog (g 0 : ℍ[ℝ])) ((g 0 : UnitQuaternion) : ℍ[ℝ]) :=
    (differentiableAt_qlog h).hasFDerivAt
  have h2 := h1.comp_hasDerivAt (0 : ℝ) hd
  exact pureComponentCLM.hasFDerivAt.comp_hasDerivAt (0 : ℝ) h2
section Along
variable {S : Finset F.Cell} (R : F.FieldChain) (U : ChainChart F) (ξ : F.Site 0 → imaginaryQuaternions)
theorem bottomBondElement_zero (x : F.Site 0) (i : Fin 4) :
    bottomBondElement R U ξ 0 x i = expUnit (U.fine x i) := by
  simp [bottomBondElement, gaugeAtLevel_zero]
theorem upperBondElement_zero (j : ℕ) (y : F.Site (j + 1)) (i : Fin 4) :
    upperBondElement R U ξ 0 j y i = expUnit (U.coarse j y i) := by
  simp [upperBondElement, gaugeAtLevel_zero]
theorem hasDerivAt_bottomBondElement (hodd : Odd F.blockSide) (hreg : ChartIsRegular S R U)
    {b : F.Site 0 × Fin 4} (hb : b ∈ innerBonds S 0) :
    HasDerivAt (fun τ => ((bottomBondElement R U ξ τ b.1 b.2 : UnitQuaternion) : ℍ[ℝ]))
      ((ξ b.1 : ℍ[ℝ]) * ((expUnit (U.fine b.1 b.2) : UnitQuaternion) : ℍ[ℝ]) -
        ((expUnit (U.fine b.1 b.2) : UnitQuaternion) : ℍ[ℝ]) *
          adjointAction (R 0 b.1 b.2) (ξ (b.1 + unitStep 0 b.2))) 0 := by
  have d1 := hasDerivAt_gaugeAtLevel hodd R U ξ hreg 0 (Nat.zero_le _) b.1 (innerBonds_ends hb).1
  have d2 := hasDerivAt_gaugeAtLevel hodd R U ξ hreg 0 (Nat.zero_le _) _ (innerBonds_ends hb).2
  have d3 : HasDerivAt (fun τ => star ((gaugeAtLevel R U ξ 0 τ (b.1 + unitStep 0 b.2) : UnitQuaternion) : ℍ[ℝ]))
      (star (gaugeGeneratorAtLevel R U ξ 0 (b.1 + unitStep 0 b.2))) 0 :=
    starCLM.hasFDerivAt.comp_hasDerivAt (0 : ℝ) d2
  set E : ℍ[ℝ] := ((expUnit (U.fine b.1 b.2) : UnitQuaternion) : ℍ[ℝ]) with hE
  set r : ℍ[ℝ] := ((R 0 b.1 b.2 : UnitQuaternion) : ℍ[ℝ]) with hr
  have d4 := (((d1.mul_const E).mul_const r).mul d3).mul_const (star r)
  have e : (fun τ => ((bottomBondElement R U ξ τ b.1 b.2 : UnitQuaternion) : ℍ[ℝ])) =
      fun τ => ((gaugeAtLevel R U ξ 0 τ b.1 : UnitQuaternion) : ℍ[ℝ]) * E * r *
        star ((gaugeAtLevel R U ξ 0 τ (b.1 + unitStep 0 b.2) : UnitQuaternion) : ℍ[ℝ]) * star r := by
    funext τ
    simp only [bottomBondElement, Submonoid.coe_mul, coe_unitQuaternion_inv, hE, hr]
  rw [e]
  refine HasDerivAt.congr_deriv d4 ?_
  have g1 : ((gaugeAtLevel R U ξ 0 0 b.1 : UnitQuaternion) : ℍ[ℝ]) = 1 := by rw [gaugeAtLevel_zero]; rfl
  have g2 : star ((gaugeAtLevel R U ξ 0 0 (b.1 + unitStep 0 b.2) : UnitQuaternion) : ℍ[ℝ]) = 1 := by
    rw [gaugeAtLevel_zero]; simp
  have rr : r * star r = 1 := mul_star_self_of_norm_eq_one (norm_coe_unitQuaternion _)
  rw [g1, g2, star_gaugeGeneratorAtLevel]
  simp only [gaugeGeneratorAtLevel, adjointAction, one_mul, mul_one]
  rw [coe_unitQuaternion_inv, ← hr]
  have e5 : (ξ b.1 : ℍ[ℝ]) * E * r * star r = (ξ b.1 : ℍ[ℝ]) * E := by
    rw [mul_assoc _ r, rr, mul_one]
  rw [add_mul, e5]
  simp only [mul_neg, neg_mul, mul_assoc, sub_eq_add_neg]
theorem eventually_norm_sub_one_lt_of_hasDerivAt {g : ℝ → UnitQuaternion} {dg : ℍ[ℝ]}
    (hd : HasDerivAt (fun τ => ((g τ : UnitQuaternion) : ℍ[ℝ])) dg 0)
    (h : ‖((g 0 : UnitQuaternion) : ℍ[ℝ]) - 1‖ < rightRadius) :
    ∀ᶠ τ in nhds (0 : ℝ), ‖((g τ : UnitQuaternion) : ℍ[ℝ]) - 1‖ < rightRadius := by
  have hc : ContinuousAt (fun τ => ‖((g τ : UnitQuaternion) : ℍ[ℝ]) - 1‖) 0 := by
    have := hd.continuousAt
    fun_prop
  exact hc.eventually (gt_mem_nhds h)
theorem exists_hasDerivAt_upperBondElement (hodd : Odd F.blockSide) (hreg : ChartIsRegular S R U) {j : ℕ}
    (hj : j + 1 < F.top) {b : F.Site (j + 1) × Fin 4} (hb : b ∈ innerBonds S (j + 1)) :
    ∃ dg, HasDerivAt (fun τ => ((upperBondElement R U ξ τ j b.1 b.2 : UnitQuaternion) : ℍ[ℝ])) dg 0 := by
  have d1 := hasDerivAt_gaugeAtLevel hodd R U ξ hreg (j + 1) hj.le b.1 (innerBonds_ends hb).1
  have d3 : HasDerivAt (fun τ => star ((gaugeAtLevel R U ξ (j + 1) τ b.1 : UnitQuaternion) : ℍ[ℝ]))
      (star (gaugeGeneratorAtLevel R U ξ (j + 1) b.1)) 0 :=
    starCLM.hasFDerivAt.comp_hasDerivAt (0 : ℝ) d1
  set E : ℍ[ℝ] := ((expUnit (U.coarse j b.1 b.2) : UnitQuaternion) : ℍ[ℝ]) with hE
  set r : ℍ[ℝ] := ((referenceDefect R j (b.1, b.2) : UnitQuaternion) : ℍ[ℝ]) with hr
  have d4 := (((d1.mul_const E).mul_const r).mul d3).mul_const (star r)
  have e : (fun τ => ((upperBondElement R U ξ τ j b.1 b.2 : UnitQuaternion) : ℍ[ℝ])) =
      fun τ => ((gaugeAtLevel R U ξ (j + 1) τ b.1 : UnitQuaternion) : ℍ[ℝ]) * E * r *
        star ((gaugeAtLevel R U ξ (j + 1) τ b.1 : UnitQuaternion) : ℍ[ℝ]) * star r := by
    funext τ
    simp only [upperBondElement, Submonoid.coe_mul, coe_unitQuaternion_inv, hE, hr]
  rw [e]
  exact ⟨_, d4⟩
theorem eventually_chartField_gaugedChart (hodd : Odd F.blockSide) (hreg : ChartIsRegular S R U)
    (hU : ∀ b ∈ innerBonds S 0, ‖((expUnit (U.fine b.1 b.2) : UnitQuaternion) : ℍ[ℝ]) - 1‖ < rightRadius)
    (hM : ∀ j, j + 1 < F.top → ∀ b ∈ innerBonds S (j + 1),
      ‖((expUnit (U.coarse j b.1 b.2) : UnitQuaternion) : ℍ[ℝ]) - 1‖ < rightRadius) :
    ∀ j, j < F.top → ∀ᶠ τ in nhds (0 : ℝ), GaugeAgreeOnBonds S j (chartField R (gaugedChart R U ξ τ) j)
      (gaugeTransform (gaugeAtLevel R U ξ j τ) (chartField R U j)) := by
  intro j
  induction j with
  | zero =>
    intro _
    have h1 : ∀ b ∈ innerBonds S 0, ∀ᶠ τ in nhds (0 : ℝ),
        ‖((bottomBondElement R U ξ τ b.1 b.2 : UnitQuaternion) : ℍ[ℝ]) - 1‖ < rightRadius := by
      intro b hb
      refine eventually_norm_sub_one_lt_of_hasDerivAt (hasDerivAt_bottomBondElement R U ξ hodd hreg hb) ?_
      rw [bottomBondElement_zero]
      exact hU b hb
    have h2 := (Filter.eventually_all_finset (innerBonds S 0)).2 h1
    filter_upwards [h2] with τ hτ x i hx hx'
    have hb := mem_innerBonds hx hx'
    have e := expUnit_logUnit (hτ (x, i) hb)
    simp only [chartField, gaugedChart, gaugeTransform]
    rw [show logUnit (bottomBondElement R U ξ τ x i) =
      logUnit (bottomBondElement R U ξ τ (x, i).1 (x, i).2) from rfl, e]
    simp [bottomBondElement, mul_assoc]
  | succ j ih =>
    intro hj
    have hjn : j < F.top := by omega
    have h1 : ∀ b ∈ innerBonds S (j + 1), ∀ᶠ τ in nhds (0 : ℝ),
        ‖((upperBondElement R U ξ τ j b.1 b.2 : UnitQuaternion) : ℍ[ℝ]) - 1‖ < rightRadius := by
      intro b hb
      obtain ⟨dg, hdg⟩ := exists_hasDerivAt_upperBondElement R U ξ hodd hreg hj hb
      refine eventually_norm_sub_one_lt_of_hasDerivAt hdg ?_
      rw [upperBondElement_zero]
      exact hM j hj b hb
    have h2 := (Filter.eventually_all_finset (innerBonds S (j + 1))).2 h1
    filter_upwards [h2, ih hjn] with τ hτ hagree x i hx hx'
    have hb := mem_innerBonds hx hx'
    have e := expUnit_logUnit (hτ (x, i) hb)
    have hfm := gaugedContourAverage_congr hodd hjn (R j) hagree hb
    have hq := (hreg j hjn).2 _ hb
    have hup := gaugedContourAverage_gaugeTransform hodd hjn (chartField R U j) (R j)
      (gaugeAtLevel R U ξ j τ) (x, i)
    set g1 := gaugeAtLevel R U ξ (j + 1) τ x with hg1
    set g2 := gaugeAtLevel R U ξ (j + 1) τ (x + unitStep (j + 1) i) with hg2
    have hup' : gaugedContourAverage (gaugeTransform (gaugeAtLevel R U ξ j τ) (chartField R U j))
        (balancingGauge (gaugeTransform (gaugeAtLevel R U ξ j τ) (chartField R U j)) (R j)) (x, i) =
        (g1 : ℍ[ℝ]) * gaugedContourAverage (chartField R U j) (balancingGauge (chartField R U j) (R j)) (x, i) *
          ((g2⁻¹ : UnitQuaternion) : ℍ[ℝ]) := hup
    have l1 : chartField R (gaugedChart R U ξ τ) (j + 1) x i =
        expUnit (logUnit (upperBondElement R U ξ τ j (x, i).1 (x, i).2)) * referenceDefect R j (x, i) *
          polarUnit (gaugedContourAverage (chartField R (gaugedChart R U ξ τ) j)
            (balancingGauge (chartField R (gaugedChart R U ξ τ) j) (R j)) (x, i)) := rfl
    have l2 : gaugeTransform (gaugeAtLevel R U ξ (j + 1) τ) (chartField R U (j + 1)) x i =
        g1 * (expUnit (U.coarse j x i) * referenceDefect R j (x, i) *
          polarUnit (gaugedContourAverage (chartField R U j) (balancingGauge (chartField R U j) (R j)) (x, i))) *
            g2⁻¹ := rfl
    have l3 : upperBondElement R U ξ τ j (x, i).1 (x, i).2 =
        g1 * expUnit (U.coarse j x i) * referenceDefect R j (x, i) * g1⁻¹ * (referenceDefect R j (x, i))⁻¹ := rfl
    rw [l1, l2, e, hfm, hup', polarUnit_coe_mul_mul_coe_inv _ _ hq, l3]
    group
theorem wilsonAction_gaugeTransform (γ : F.Site 0 → UnitQuaternion) (X : F.GaugeField 0) :
    wilsonAction S (gaugeTransform γ X) = wilsonAction S X := by
  unfold wilsonAction
  refine Finset.sum_congr rfl fun p _ => ?_
  unfold plaquetteHolonomy
  have hend : endpoint (0 : LatticeFractionalIntegration.Lattice4)
      [(p.2.1, true), (p.2.2, true), (p.2.1, false), (p.2.2, false)] = 0 := by
    simp [endpoint, FlatPairing.stepDisplacement]
  rw [pathHolonomy_gaugeTransform_of_base, hend, add_siteOfCoords_zero]
  congr 1
  simp only [Submonoid.coe_mul]
  exact re_coe_mul_mul_coe_inv _ _
theorem norm_sub_re_conj (g g' : UnitQuaternion) (Q : ℍ[ℝ]) (X : UnitQuaternion) :
    ‖(g : ℍ[ℝ]) * Q * ((g'⁻¹ : UnitQuaternion) : ℍ[ℝ])‖ -
      ((g : ℍ[ℝ]) * Q * ((g'⁻¹ : UnitQuaternion) : ℍ[ℝ]) *
        (((g * X * g'⁻¹)⁻¹ : UnitQuaternion) : ℍ[ℝ])).re =
      ‖Q‖ - (Q * ((X⁻¹ : UnitQuaternion) : ℍ[ℝ])).re := by
  rw [norm_coe_mul_mul_coe_inv]
  congr 1
  have : (g : ℍ[ℝ]) * Q * ((g'⁻¹ : UnitQuaternion) : ℍ[ℝ]) * (((g * X * g'⁻¹)⁻¹ : UnitQuaternion) : ℍ[ℝ]) =
      (g : ℍ[ℝ]) * (Q * ((X⁻¹ : UnitQuaternion) : ℍ[ℝ])) * ((g⁻¹ : UnitQuaternion) : ℍ[ℝ]) := by
    simp only [mul_inv_rev, inv_inv, Submonoid.coe_mul, mul_assoc, inv_coe_mul_coe_mul]
  rw [this, re_coe_mul_mul_coe_inv]
theorem hasDerivAt_chartAction_gaugedChart (hodd : Odd F.blockSide) (hreg : ChartIsRegular S R U)
    (hU : ∀ b ∈ innerBonds S 0, ‖((expUnit (U.fine b.1 b.2) : UnitQuaternion) : ℍ[ℝ]) - 1‖ < rightRadius)
    (hM : ∀ j, j + 1 < F.top → ∀ b ∈ innerBonds S (j + 1),
      ‖((expUnit (U.coarse j b.1 b.2) : UnitQuaternion) : ℍ[ℝ]) - 1‖ < rightRadius)
    (a : ℝ) (W : F.GaugeField F.top) (htop : ∀ y ∈ S, gaugeGeneratorAtLevel R U ξ F.top y = 0) :
    HasDerivAt (fun τ => chartAction a S R (gaugedChart R U ξ τ) W) 0 0 := by
  set Q : F.Site F.top × Fin 4 → ℍ[ℝ] := fun c =>
    gaugedContourAverage (chartField R U F.depth) (balancingGauge (chartField R U F.depth) (R F.depth)) c with hQ
  set Aconst : ℝ := wilsonAction S (chartField R U 0) + a * ∑ j ∈ Finset.range F.depth,
    ∑ c ∈ innerBonds S (j + 1),
    gaugedBlockFit (chartField R U j) (balancingGauge (chartField R U j) (R j)) (chartField R U (j + 1)) c
  have hall : ∀ᶠ τ in nhds (0 : ℝ), ∀ j ∈ Finset.range F.top,
      GaugeAgreeOnBonds S j (chartField R (gaugedChart R U ξ τ) j)
        (gaugeTransform (gaugeAtLevel R U ξ j τ) (chartField R U j)) :=
    (Filter.eventually_all_finset _).2 fun j hj =>
      eventually_chartField_gaugedChart R U ξ hodd hreg hU hM j (Finset.mem_range.1 hj)
  have hev : (fun τ => chartAction a S R (gaugedChart R U ξ τ) W) =ᶠ[nhds 0] fun τ =>
      Aconst + a * ∑ c ∈ innerBonds S F.top, (‖Q c‖ -
        (((gaugeAtLevel R U ξ F.top τ c.1 : UnitQuaternion) : ℍ[ℝ]) * Q c *
          (((gaugeAtLevel R U ξ F.top τ (c.1 + unitStep F.top c.2))⁻¹ : UnitQuaternion) : ℍ[ℝ]) *
            (((W c.1 c.2)⁻¹ : UnitQuaternion) : ℍ[ℝ])).re) := by
    filter_upwards [hall] with τ hτ
    have h0 : 0 < F.top := Nat.succ_pos _
    have hag : ∀ j, j < F.top → GaugeAgreeOnBonds S j (chartField R (gaugedChart R U ξ τ) j)
        (gaugeTransform (gaugeAtLevel R U ξ j τ) (chartField R U j)) :=
      fun j hj => hτ j (Finset.mem_range.2 hj)
    have hmean : ∀ j, j < F.top → ∀ c ∈ innerBonds S (j + 1),
        gaugedContourAverage (chartField R (gaugedChart R U ξ τ) j)
          (balancingGauge (chartField R (gaugedChart R U ξ τ) j) (R j)) c =
        ((gaugeAtLevel R U ξ (j + 1) τ c.1 : UnitQuaternion) : ℍ[ℝ]) *
          gaugedContourAverage (chartField R U j) (balancingGauge (chartField R U j) (R j)) c *
          (((gaugeAtLevel R U ξ (j + 1) τ (c.1 + unitStep (j + 1) c.2))⁻¹ : UnitQuaternion) : ℍ[ℝ]) := by
      intro j hj c hc
      rw [gaugedContourAverage_congr hodd hj (R j) (hag j hj) hc]
      exact gaugedContourAverage_gaugeTransform hodd hj _ _ _ c
    have hmid : ∑ j ∈ Finset.range F.depth, ∑ c ∈ innerBonds S (j + 1),
        gaugedBlockFit (chartChain R (gaugedChart R U ξ τ) W j)
          (chartGauge R (gaugedChart R U ξ τ) (j + 1))
          (chartChain R (gaugedChart R U ξ τ) W (j + 1)) c =
        ∑ j ∈ Finset.range F.depth, ∑ c ∈ innerBonds S (j + 1),
          gaugedBlockFit (chartField R U j) (balancingGauge (chartField R U j) (R j))
            (chartField R U (j + 1)) c := by
      refine Finset.sum_congr rfl fun j hj => Finset.sum_congr rfl fun c hc => ?_
      have hj1 : j + 1 < F.top := by
        have := Finset.mem_range.1 hj
        have hn : F.top = F.depth + 1 := rfl
        omega
      have hjn : j < F.top := by omega
      rw [chartChain_of_lt R _ W hjn, chartChain_of_lt R _ W hj1]
      unfold gaugedBlockFit chartGauge
      rw [hmean j hjn c hc, hag (j + 1) hj1 c.1 c.2 (innerBonds_ends hc).1 (innerBonds_ends hc).2]
      exact norm_sub_re_conj _ _ _ _
    have htp : ∑ c ∈ innerBonds S (F.depth + 1),
        gaugedBlockFit (chartChain R (gaugedChart R U ξ τ) W F.depth)
          (chartGauge R (gaugedChart R U ξ τ) (F.depth + 1))
          (chartChain R (gaugedChart R U ξ τ) W (F.depth + 1)) c =
        ∑ c ∈ innerBonds S F.top, (‖Q c‖ - (((gaugeAtLevel R U ξ F.top τ c.1 : UnitQuaternion) : ℍ[ℝ]) * Q c *
          (((gaugeAtLevel R U ξ F.top τ (c.1 + unitStep F.top c.2))⁻¹ : UnitQuaternion) : ℍ[ℝ]) *
            (((W c.1 c.2)⁻¹ : UnitQuaternion) : ℍ[ℝ])).re) := by
      refine Finset.sum_congr rfl fun c hc => ?_
      have htn : F.depth < F.top := Nat.lt_succ_self _
      rw [chartChain_of_lt R _ W htn, chartChain_top R _ W]
      unfold gaugedBlockFit chartGauge
      rw [hmean F.depth htn c hc, norm_coe_mul_mul_coe_inv]
    have hA : Aconst = wilsonAction S (chartField R U 0) + a * ∑ j ∈ Finset.range F.depth,
      ∑ c ∈ innerBonds S (j + 1),
      gaugedBlockFit (chartField R U j) (balancingGauge (chartField R U j) (R j))
        (chartField R U (j + 1)) c := rfl
    show gaugedChainAction a S (chartChain R (gaugedChart R U ξ τ) W)
      (chartGauge R (gaugedChart R U ξ τ)) = _
    unfold gaugedChainAction
    rw [chartChain_of_lt R _ W h0, wilsonAction_congr (hag 0 h0), wilsonAction_gaugeTransform,
      Finset.sum_range_succ, mul_add, ← add_assoc, hmid, htp, hA]
  refine HasDerivAt.congr_of_eventuallyEq ?_ hev
  have hterm : ∀ c ∈ innerBonds S F.top, HasDerivAt (fun τ => ‖Q c‖ -
        (((gaugeAtLevel R U ξ F.top τ c.1 : UnitQuaternion) : ℍ[ℝ]) * Q c *
          (((gaugeAtLevel R U ξ F.top τ (c.1 + unitStep F.top c.2))⁻¹ : UnitQuaternion) : ℍ[ℝ]) *
            (((W c.1 c.2)⁻¹ : UnitQuaternion) : ℍ[ℝ])).re) 0 0 := by
    intro c hc
    have y1 := (innerBonds_ends hc).1
    have y2 := (innerBonds_ends hc).2
    have d1 := hasDerivAt_gaugeAtLevel hodd R U ξ hreg F.top le_rfl c.1 y1
    have d2 := hasDerivAt_gaugeAtLevel hodd R U ξ hreg F.top le_rfl _ y2
    rw [htop _ (mem_sitesOfCells_top.1 y1)] at d1
    rw [htop _ (mem_sitesOfCells_top.1 y2)] at d2
    have d3 : HasDerivAt
        (fun τ => (((gaugeAtLevel R U ξ F.top τ (c.1 + unitStep F.top c.2))⁻¹ : UnitQuaternion) : ℍ[ℝ])) 0 0 := by
      have h1 : HasDerivAt
          (fun τ => star ((gaugeAtLevel R U ξ F.top τ (c.1 + unitStep F.top c.2) : UnitQuaternion) : ℍ[ℝ]))
          (star (0 : ℍ[ℝ])) 0 := starCLM.hasFDerivAt.comp_hasDerivAt (0 : ℝ) d2
      rw [star_zero] at h1
      simp only [coe_unitQuaternion_inv]
      exact h1
    have d4 := ((d1.mul_const (Q c)).mul d3).mul_const (((W c.1 c.2)⁻¹ : UnitQuaternion) : ℍ[ℝ])
    have d5 : HasDerivAt (fun τ => ((gaugeAtLevel R U ξ F.top τ c.1 : UnitQuaternion) : ℍ[ℝ]) * Q c *
        (((gaugeAtLevel R U ξ F.top τ (c.1 + unitStep F.top c.2))⁻¹ : UnitQuaternion) : ℍ[ℝ]) *
          (((W c.1 c.2)⁻¹ : UnitQuaternion) : ℍ[ℝ])) 0 0 := by
      refine HasDerivAt.congr_deriv d4 ?_
      simp
    have d6 := reCLM.hasFDerivAt.comp_hasDerivAt (0 : ℝ) d5
    have d7 := (hasDerivAt_const (0 : ℝ) ‖Q c‖).sub d6
    exact HasDerivAt.congr_deriv d7 (by simp)
  have hs := (HasDerivAt.fun_sum hterm).const_mul a
  have hf := hs.const_add Aconst
  simpa using hf
end Along
end Curve
end GaugeMotions
end YangMills.Construction
end
