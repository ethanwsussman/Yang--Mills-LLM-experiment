import YangMills.Construction.InfiniteLattice.ExpansionsMeetTheConditionsOfTheReconstruction
import YangMills.Construction.InfiniteLattice.OperatorsAndMatrixElementsOfTheTwoCoordinatePictures
import YangMills.Construction.InfiniteLattice.ReflectionPositivityAndOneTranslation
import Mathlib
set_option autoImplicit false
open MeasureTheory
open scoped InnerProductSpace
noncomputable section
namespace YangMills.Construction
open OneLoopNotation ComplexHilbert ContractionUnitary
open FormCompletion
namespace LatticeConventions.CoordinatePictures
open NormalHyperplane
open InfiniteLattice (GaugeField IsBoundedObservable IsShiftInvariant LatticePoint axisStep shift)
theorem exists_ne_direction (μ : Direction) : ∃ l : Direction, l ≠ μ := by
  revert μ
  decide
theorem rowOperators_properties (hComp : FormCompletionIsHilbertSpace)
    (hRP : ReflectionPositivityWithTranslation)
    (hRec : MirrorReconstruction) (a : Spacing) (μ : Direction)
    {S S' : NormalHyperplane} (hS : S.IsLatticeMirror (a : ℝ))
    (hS' : S'.IsLatticeMirror (a : ℝ)) (h : LatticePoint (a : ℝ))
    (ν : Measure (GaugeField (a : ℝ))) [IsProbabilityMeasure ν]
    (hmid : S'.IsMidPlaneOf (a : ℝ) S (h : Point))
    (horth : ∀ lam : {l : Direction // l ≠ μ}, euclidDot S.normal (axisStep (a : ℝ) lam.1 : Point) = 0)
    (hinv : IsShiftInvariant ν) (hrp : IsReflectionPositiveAcrossMirror hS ν)
    (hrp' : IsReflectionPositiveAcrossMirror hS' ν) (lam₀ : {l : Direction // l ≠ μ}) :
    IsSymmetricOp (stepOperator hS ν h) ∧
    OpGE (stepOperator hS ν h) 0 ∧
    OpLE (stepOperator hS ν h) (idOp (MirrorHilbertSpace hS ν)) ∧
    (∀ lam : {l : Direction // l ≠ μ},
      IsUnitaryMap (vectorUnitary hS ν (axisStep (a : ℝ) lam.1) :
        MirrorHilbertSpace hS ν →ₗ[ℂ] MirrorHilbertSpace hS ν)) ∧
    (∀ lam : {l : Direction // l ≠ μ}, Commute (stepOperator hS ν h)
      (vectorUnitary hS ν (axisStep (a : ℝ) lam.1))) ∧
    (∀ lam lam' : {l : Direction // l ≠ μ},
      Commute (vectorUnitary hS ν (axisStep (a : ℝ) lam.1))
        (vectorUnitary hS ν (axisStep (a : ℝ) lam'.1))) ∧
    DenseRange (mirrorClass hS ν) ∧
    ∀ (F F' : upperObservables (a : ℝ) S) (lam : {l : Direction // l ≠ μ}) (n : ℕ) (y : ℤ),
      ⟪mirrorClass hS ν F,
          (stepOperator hS ν h ^ n *
            zpowOp (vectorUnitary hS ν (axisStep (a : ℝ) lam.1)) y)
            (mirrorClass hS ν F')⟫_ℂ =
        ∫ U, conjFun ((reflectSymmetry hS).actOn F.1) U *
          (shift (n • h + y • axisStep (a : ℝ) lam.1)).actOn F'.1 U ∂ν := by
  have recon : ∀ (k : ℕ) (w : Fin k → LatticePoint (a : ℝ)), 1 ≤ k →
      (∀ i, euclidDot S.normal (w i : Point) = 0) →
      StepIsPositiveContraction hS ν h ∧ (∀ i, VectorIsUnitary hS ν (w i)) ∧
        CommuteWithMatrixElements hS ν h w := by
    intro k w hk hw
    have hc : MirrorReconstructionHyps (a : ℝ) S (h : Point) S'
        (fun i => (w i : Point)) :=
      ⟨hmid, hS', by simpa using hk, fun i => (w i).2, hw⟩
    obtain ⟨-, hb, hc', hd⟩ :=
      hRec a S S' hS hS' h k w ν hc (hinv h) (fun i => hinv (w i)) hrp hrp'
    exact ⟨hb, hc', hd⟩
  have single := fun lam : {l : Direction // l ≠ μ} =>
    recon 1 (fun _ => axisStep (a : ℝ) lam.1) le_rfl (fun _ => horth lam)
  have pair := fun lam lam' : {l : Direction // l ≠ μ} =>
    recon 2 ![axisStep (a : ℝ) lam.1, axisStep (a : ℝ) lam'.1] (by norm_num) (by
      intro i
      fin_cases i
      · exact horth lam
      · exact horth lam')
  obtain ⟨⟨-, -, hsym, hge, hle⟩, -, -⟩ := single lam₀
  have hpos := (hRP a _ hS ν hrp).1.1
  obtain ⟨-, hB, -⟩ := hComp _ _ hpos
  refine ⟨hsym, hge, hle, fun lam => ((single lam).2.1 0).2.1, fun lam => (single lam).2.2.1 0,
    fun lam lam' => (pair lam lam').2.2.2.1 0 1, hB.2.2.2.2.2.2.2.2, ?_⟩
  intro F F' lam n y
  have hm := (single lam).2.2.2.2 F F' n (fun _ => y)
  simp only [List.ofFn_succ, List.ofFn_zero, List.prod_cons, List.prod_nil, mul_one,
    Fin.sum_univ_one] at hm
  exact hm
theorem linkReflection_eq_siteReflection_comp_shift (a : Spacing) (μ : Direction) :
    LinkReflectionEqShiftedSite a μ := by
  have hcoord : ∀ x : Point, (x + (a : ℝ) • basisVector μ) μ = x μ + (a : ℝ) := fun x => by
    simp [basisVector]
  have hform : ∀ x : Point,
      x + (a : ℝ) • basisVector μ - (2 * (x μ + (a : ℝ))) • basisVector μ =
        x - (2 * x μ + (a : ℝ)) • basisVector μ := fun x => by
    funext κ
    by_cases hκ : κ = μ
    · subst hκ
      simp [basisVector]
      ring
    · simp [basisVector, Pi.single_eq_of_ne hκ]
  have hfun : (LinkFrame.linkReflection a μ).toFun =
      ((SiteFrame.siteReflection a μ).comp (shift (axisStep (a : ℝ) μ))).toFun := by
    rw [LinkFrame.linkReflection_toFun]
    change LinkFrame.linkReflectionMap a μ =
      fun x => (SiteFrame.siteReflection a μ).toFun (x + (axisStep (a : ℝ) μ : Point))
    rw [SiteFrame.siteReflection_toFun]
    funext x κ
    by_cases hκ : κ = μ
    · subst hκ
      simp [LinkFrame.linkReflectionMap, SiteFrame.siteReflectionMap, axisStep, basisVector]
      ring
    · simp [LinkFrame.linkReflectionMap, SiteFrame.siteReflectionMap, axisStep, basisVector,
        Pi.single_eq_of_ne hκ]
  have heq : LinkFrame.linkReflection a μ =
      (SiteFrame.siteReflection a μ).comp (shift (axisStep (a : ℝ) μ)) := by
    generalize LinkFrame.linkReflection a μ = r at hfun
    generalize (SiteFrame.siteReflection a μ).comp (shift (axisStep (a : ℝ) μ)) = r'
      at hfun
    cases r
    cases r'
    cases hfun
    rfl
  refine ⟨fun x => ⟨?_, hform x⟩, heq, fun F _ => ?_⟩
  · rw [SiteFrame.siteReflection_toFun]
    simp only [SiteFrame.siteReflectionMap, hcoord]
  · rw [heq]
    rfl
theorem coordinatePictureOperators_holds (hComp : FormCompletionIsHilbertSpace)
    (hRP : ReflectionPositivityWithTranslation)
    (hRec : MirrorReconstruction)
    (hRows : MirrorExpansions.Statement) :
    CoordinatePictureOperators := by
  intro a μ ν _ hst
  obtain ⟨l₀, hl₀⟩ := exists_ne_direction μ
  refine ⟨linkReflection_eq_siteReflection_comp_shift a μ, ?_, ?_⟩
  · have row := (hRows.2.1 a μ l₀ hl₀.symm 0 ⟨0, by simp⟩).1
    have hmid := row.midPlane_isMid
    rw [LinkFrame.linkPicture_normalStep] at hmid
    exact rowOperators_properties hComp hRP hRec a μ (LinkFrame.linkPlane_isLatticeMirror a μ)
      row.midPlane_isLatticeMirror (axisStep (a : ℝ) μ) ν hmid
      (fun lam => by
        have hd := row.euclidDot_tangentStep lam
        rw [LinkFrame.linkPicture_tangentStep] at hd
        exact hd)
      hst.shiftInvariant hst.reflectionPositive_linkPlane
      (hst.reflectionPositive_sitePlane row.midPlane_isLatticeMirror) ⟨l₀, hl₀⟩
  · have row := (hRows.2.1 a μ l₀ hl₀.symm 0 ⟨0, by simp⟩).2.1
    have hmid := row.midPlane_isMid
    rw [SiteFrame.sitePicture_normalStep] at hmid
    exact rowOperators_properties hComp hRP hRec a μ (SiteFrame.vertexPlane_isLatticeMirror a μ)
      row.midPlane_isLatticeMirror (axisStep (a : ℝ) μ) ν hmid
      (fun lam => by
        have hd := row.euclidDot_tangentStep lam
        rw [SiteFrame.sitePicture_tangentStep] at hd
        exact hd)
      hst.shiftInvariant (SiteFrame.reflectionPositive_vertexPlane hst)
      (SiteFrame.reflectionPositive_midPlane hst row.midPlane_isLatticeMirror)
      ⟨l₀, hl₀⟩
end LatticeConventions.CoordinatePictures
end YangMills.Construction
end
