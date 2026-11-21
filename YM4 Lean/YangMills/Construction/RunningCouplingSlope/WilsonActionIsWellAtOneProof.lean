import YangMills.Construction.ColdChainAtEveryLevel.PlaquettesNearAPoint
import YangMills.Construction.RunningCouplingSlope.ClosedFieldOnTheLatticeIsPure
import YangMills.Construction.RunningCouplingSlope.LeastActionIsWellAtTheTopProof
import YangMills.Construction.RunningCouplingSlope.WilsonActionIsWellAtOne
import Mathlib
set_option autoImplicit false
open Filter
open scoped Topology Quaternion
noncomputable section
namespace YangMills.Construction.RunningCouplingSlope
open YangMills.Construction.BlockAverages YangMills.Construction.ColdStepAtMirrorFrames YangMills.Construction.TorusFields YangMills.Construction.LumpContours YangMills.Construction.GaugeFixing YangMills.Construction.LatticeCohomology
variable {F : BlockFrame}
private theorem analyticAt_component {F : BlockFrame} {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X] {k : ℕ}
    [Fintype (F.Site k)] {q : X → F.Site k → Fin 4 → ℍ[ℝ]} {e : X} (hq : AnalyticAt ℝ q e) (x : F.Site k) (i : Fin 4) :
    AnalyticAt ℝ (fun y => q y x i) e :=
  analyticAt_pi_iff.1 (analyticAt_pi_iff.1 hq x) i
private def plaquetteLoop (μ ν : Fin 4) : List PathStep := [(μ, true), (ν, true), (μ, false), (ν, false)]
private theorem plaquetteHolonomy_eq_mul {k : ℕ} (U : F.GaugeField k) (x : F.Site k) (μ ν : Fin 4) :
    plaquetteHolonomy U (x, μ, ν) =
      U x μ * U (x + BlockAverages.unitStep k μ) ν * (U (x + BlockAverages.unitStep k ν) μ)⁻¹ * (U x ν)⁻¹ := by apply _root_.YangMills.Construction.PlaquetteExpansion.plaquetteHolonomy_eq <;> assumption
private theorem formAlongPath_plaquetteLoop {k : ℕ} (A : F.Site k → Fin 4 → imaginaryQuaternions) (x : F.Site k)
    (μ ν : Fin 4) :
    formAlongPath A x (plaquetteLoop μ ν) =
      A x μ + A (x + BlockAverages.unitStep k μ) ν - A (x + BlockAverages.unitStep k ν) μ - A x ν := by
  have e1 : x + BlockAverages.unitStep k μ + BlockAverages.unitStep k ν - BlockAverages.unitStep k μ =
      x + BlockAverages.unitStep k ν := by abel
  have e2 : x + BlockAverages.unitStep k μ + BlockAverages.unitStep k ν + -BlockAverages.unitStep k μ -
      BlockAverages.unitStep k ν = x := by abel
  simp [formAlongPath, plaquetteLoop, linkForm, stepDisplacement, e1, e2]
  abel
private theorem im_coe_imaginary (b : imaginaryQuaternions) : (b : ℍ[ℝ]).im = (b : ℍ[ℝ]) := by
  have hre : (b : ℍ[ℝ]).re = 0 := b.2
  ext <;> simp [hre]
private theorem minimalAction_eq_sum_reDefect (S : Finset F.Cell) (a : ℝ) (U : F.GaugeField 0) :
    minimalAction a S 0 U = ∑ p ∈ innerPlaquettes S 0, reDefect ((plaquetteHolonomy U p : UnitQuaternion) : ℍ[ℝ]) := by
  show BlockAverages.wilsonAction S U = _
  unfold BlockAverages.wilsonAction
  exact Finset.sum_congr rfl fun p _ => one_sub_re_eq_reDefect _
private theorem eq_one_of_reDefect_eq_zero {g : UnitQuaternion} (hg : reDefect (g : ℍ[ℝ]) = 0) : g = 1 := by apply _root_.YangMills.SharedProofs.p24246 <;> assumption
theorem wilsonActionNondegenerate_of_flatConnectionIsPureGauge (hpure : FlatConnectionIsPureGauge) :
    WilsonActionNondegenerate := by
  intro a L n _ hL hn
  have hext : ∀ i, 2 ≤ (torusFrame L 0 n).extent i := fun _ => hn
  have hmem : ∀ (x : (torusFrame L 0 n).Site 0) (μ ν : Fin 4), μ < ν →
      (x, μ, ν) ∈ innerPlaquettes (finiteCells (torusFrame L 0 n)) 0 := by
    intro x μ ν hμν
    have hall : ∀ y : (torusFrame L 0 n).Site 0, y ∈ sitesOfCells (finiteCells (torusFrame L 0 n)) 0 := fun y =>
      (BlockLevels.mem_sitesOfCells_iff (Nat.zero_le _) hL).2 (BlockOffsets.mem_finiteCells hext _)
    simp only [innerPlaquettes, Finset.mem_filter, Finset.mem_product, Finset.mem_univ, and_true]
    exact ⟨hall x, hμν, fun y _ => hall y⟩
  have hsum : ∀ (ψ : (torusFrame L 0 n).Site 0 × Fin 4 × Fin 4 → ℝ), (∀ p, 0 ≤ ψ p) →
      ∑ p ∈ innerPlaquettes (finiteCells (torusFrame L 0 n)) 0, ψ p = 0 →
      ∀ (x : (torusFrame L 0 n).Site 0) (μ ν : Fin 4), μ < ν → ψ (x, μ, ν) = 0 := by
    intro ψ hψ hzero x μ ν hμν
    exact (Finset.sum_eq_zero_iff_of_nonneg fun p _ => hψ p).1 hzero _ (hmem x μ ν hμν)
  have hstep : ∀ (z : Fin 4 → ℤ) (μ : Fin 4), siteOfCoords (F := torusFrame L 0 n) 0 (z + Pi.single μ 1) =
      siteOfCoords 0 z + BlockAverages.unitStep 0 μ := fun z μ => by
    rw [BlockAverages.siteOfCoords_add]
    rfl
  refine ⟨fun U => ?_, ?_, ?_, fun U hU => ?_, ?_, fun A hA => ?_⟩
  · rw [minimalAction_eq_sum_reDefect]
    exact Finset.sum_nonneg fun p _ => reDefect_nonneg _
  · rw [minimalAction_eq_sum_reDefect]
    refine Finset.sum_eq_zero fun p _ => ?_
    have : plaquetteHolonomy (trivialBlockField (torusFrame L 0 n) 0) p = 1 := pathHolonomy_trivial _ _
    simp [this, reDefect]
  · have e : minimalAction a (finiteCells (torusFrame L 0 n)) 0 = fun U =>
        ∑ p ∈ innerPlaquettes (finiteCells (torusFrame L 0 n)) 0,
          (1 - ((plaquetteHolonomy U p : UnitQuaternion) : ℍ[ℝ]).re) := rfl
    rw [e]
    exact continuous_finsetSum _ fun p _ => continuous_const.sub
      (Quaternion.continuous_re.comp (continuous_pathHolonomy continuous_id _ _))
  · rw [minimalAction_eq_sum_reDefect] at hU
    have h1 := hsum _ (fun p => reDefect_nonneg _) hU
    obtain ⟨g, hg⟩ := hpure UnitQuaternion (fun z i => U (siteOfCoords 0 z) i) (fun z μ ν hμν => by
      have h2 := eq_one_of_reDefect_eq_zero (h1 (siteOfCoords 0 z) μ ν hμν)
      rw [plaquetteHolonomy_eq_mul, mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at h2
      rw [hstep, hstep]
      exact h2)
    exact ⟨g, hg⟩
  · have hfam : IsAnalyticFieldFamily (fun Y : (torusFrame L 0 n).Site 0 → Fin 4 → ℍ[ℝ] => fieldOfQuaternions Y)
        (quaternionsOfField (trivialBlockField (torusFrame L 0 n) 0)) := fun x i =>
      analyticAt_normalize (analyticAt_component analyticAt_id x i)
        (by simp [quaternionsOfField, trivialBlockField])
    have e : (fun Y : (torusFrame L 0 n).Site 0 → Fin 4 → ℍ[ℝ] =>
        minimalAction a (finiteCells (torusFrame L 0 n)) 0 (fieldOfQuaternions Y)) =
        fun Y => ∑ p ∈ innerPlaquettes (finiteCells (torusFrame L 0 n)) 0,
          (1 - ((plaquetteHolonomy (fieldOfQuaternions Y) p : UnitQuaternion) : ℍ[ℝ]).re) := rfl
    rw [e]
    exact Finset.analyticAt_fun_sum _ fun p _ => analyticAt_const.sub (analyticAt_quat_re (hfam.analyticAt_path _ _))
  · have hcurve := isCurveThroughTrivial_fieldAlongLine (F := torusFrame L 0 n) (k := 0) A
    have hline : IsAnalyticFieldFamily (fieldAlongLine (F := torusFrame L 0 n) A) 0 := fun x i =>
      analyticAt_normalize (analyticAt_const.add (analyticAt_id.smul analyticAt_const)) (by simp)
    have hψ : ∀ p, AnalyticAt ℝ (fun τ =>
        reDefect ((plaquetteHolonomy (fieldAlongLine (F := torusFrame L 0 n) A τ) p : UnitQuaternion) : ℍ[ℝ])) 0 := by
      intro p
      have h1 : AnalyticAt ℝ (fun τ =>
          1 - ((plaquetteHolonomy (fieldAlongLine (F := torusFrame L 0 n) A τ) p : UnitQuaternion) : ℍ[ℝ]).re) 0 :=
        analyticAt_const.sub (analyticAt_quat_re (hline.analyticAt_path _ _))
      simpa only [one_sub_re_eq_reDefect] using h1
    have h2 : secondDerivZero (fun τ =>
        minimalAction a (finiteCells (torusFrame L 0 n)) 0 (fieldAlongLine A τ)) = 0 := hA
    simp only [minimalAction_eq_sum_reDefect] at h2
    rw [secondDerivZero_sum _ _ fun p _ => hψ p] at h2
    have hval : ∀ (x : (torusFrame L 0 n).Site 0) (μ ν : Fin 4), secondDerivZero (fun τ =>
        reDefect ((plaquetteHolonomy (fieldAlongLine (F := torusFrame L 0 n) A τ) (x, μ, ν) : UnitQuaternion) : ℍ[ℝ])) =
        ‖((formAlongPath A x (plaquetteLoop μ ν) : imaginaryQuaternions) : ℍ[ℝ])‖ ^ 2 := by
      intro x μ ν
      have h3 := secondDerivZero_reDefect (hcurve.hasDerivAt_path (plaquetteLoop μ ν) x) (by
        show ((pathHolonomy (fieldAlongLine A 0) x (plaquetteLoop μ ν) : UnitQuaternion) : ℍ[ℝ]) = 1
        rw [hcurve.at_zero, pathHolonomy_trivial]
        rfl) (hψ (x, μ, ν))
      rw [im_coe_imaginary] at h3
      exact h3
    have h3 := hsum (fun p => secondDerivZero (fun τ =>
        reDefect ((plaquetteHolonomy (fieldAlongLine (F := torusFrame L 0 n) A τ) p : UnitQuaternion) : ℍ[ℝ])))
      (fun p => secondDerivZero_nonneg (hψ p) (Eventually.of_forall fun τ => reDefect_nonneg _) (by
        show reDefect ((plaquetteHolonomy (fieldAlongLine A 0) p : UnitQuaternion) : ℍ[ℝ]) = 0
        rw [hcurve.at_zero]
        have : plaquetteHolonomy (trivialBlockField (torusFrame L 0 n) 0) p = 1 := pathHolonomy_trivial _ _
        simp [this, reDefect])) h2
    have hclosed : ∀ (z : Fin 4 → ℤ) (μ ν : Fin 4), μ < ν →
        A (siteOfCoords 0 z) μ + A (siteOfCoords 0 (z + Pi.single μ 1)) ν =
          A (siteOfCoords 0 z) ν + A (siteOfCoords 0 (z + Pi.single ν 1)) μ := by
      intro z μ ν hμν
      have h4 := h3 (siteOfCoords 0 z) μ ν hμν
      simp only [hval] at h4
      have h5 : formAlongPath A (siteOfCoords 0 z) (plaquetteLoop μ ν) = 0 := by
        apply Subtype.ext
        simpa using h4
      rw [formAlongPath_plaquetteLoop] at h5
      rw [hstep, hstep]
      have h6 := sub_eq_zero.1 h5
      have h7 := sub_eq_iff_eq_add.1 h6
      rw [h7]
    obtain ⟨g, hg⟩ := hpure (Multiplicative imaginaryQuaternions)
      (fun z i => Multiplicative.ofAdd (A (siteOfCoords 0 z) i)) (fun z μ ν hμν => by
        rw [← ofAdd_add, ← ofAdd_add, hclosed z μ ν hμν])
    refine ⟨fun z => Multiplicative.toAdd (g z), fun z i => ?_⟩
    have h4 := congrArg Multiplicative.toAdd (hg z i)
    simp only [toAdd_ofAdd, toAdd_mul, toAdd_inv] at h4
    rw [h4, sub_eq_add_neg]
end YangMills.Construction.RunningCouplingSlope
end
