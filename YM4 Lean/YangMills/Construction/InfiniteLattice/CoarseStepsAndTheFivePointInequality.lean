import YangMills.Construction.InfiniteLattice.SitePictures
import Mathlib
set_option autoImplicit false
open MeasureTheory
open YangMills.Construction.ComplexHilbert YangMills.Construction.ContractionUnitary
open scoped ComplexOrder
noncomputable section
namespace YangMills.Construction.LatticeConventions
open YangMills.Construction.InfiniteLattice (GaugeField IsBoundedObservable LatticePoint
  localRegionObservables axisStep shift)
def mixState {a : ℝ} (t : ℝ) (ν₁ ν₂ : Measure (GaugeField a)) : Measure (GaugeField a) :=
  ENNReal.ofReal t • ν₁ + ENNReal.ofReal (1 - t) • ν₂
def IsAffineInState {a : ℝ} (w : Measure (GaugeField a) → ℂ) : Prop :=
  ∀ (ν₁ ν₂ : Measure (GaugeField a)) [IsProbabilityMeasure ν₁] [IsProbabilityMeasure ν₂] (t : ℝ),
    0 ≤ t → t ≤ 1 → w (mixState t ν₁ ν₂) = (t : ℂ) * w ν₁ + (1 - (t : ℂ)) * w ν₂
namespace SiteFrame
variable (a : Spacing) (μ : Direction)
def reflectedCorrelationFun (F : GaugeField (a : ℝ) → ℂ) (v : LatticePoint (a : ℝ)) :
    GaugeField (a : ℝ) → ℂ :=
  fun U => conjFun ((siteReflection a μ).actOn F) U *
    (shift v).actOn F U
def reflectedCorrelation (ν : Measure (GaugeField (a : ℝ))) (F : GaugeField (a : ℝ) → ℂ)
    (v : LatticePoint (a : ℝ)) : ℂ :=
  ∫ U, reflectedCorrelationFun a μ F v U ∂ν
def ConeInequalityAtMultiple (lam : {l : Direction // l ≠ μ})
    (ν : Measure (GaugeField (a : ℝ))) [IsProbabilityMeasure ν] (k : ℕ) : Prop :=
  OpGE ((idOp (SiteHilbertSpace a μ ν) - transferOperator a μ ν ^ k) ^ 2)
    (transferOperator a μ ν ^ k *
      ((2 : ℂ) • idOp (SiteHilbertSpace a μ ν) - zpowOp (transverseShift a μ ν lam) (k : ℤ) -
        zpowOp (transverseShift a μ ν lam) (-(k : ℤ))))
def FivePointBound (lam : Direction) (ν : Measure (GaugeField (a : ℝ)))
    (F : GaugeField (a : ℝ) → ℂ) (k : ℕ) : Prop :=
  0 ≤ reflectedCorrelation a μ ν F 0 - 4 * reflectedCorrelation a μ ν F (k • axisStep (a : ℝ) μ) +
    reflectedCorrelation a μ ν F ((2 * k) • axisStep (a : ℝ) μ) +
    reflectedCorrelation a μ ν F (k • axisStep (a : ℝ) μ + k • axisStep (a : ℝ) lam) +
    reflectedCorrelation a μ ν F (k • axisStep (a : ℝ) μ - k • axisStep (a : ℝ) lam)
def FivePointTermsAffine (lam : Direction) (F : GaugeField (a : ℝ) → ℂ) (k : ℕ) : Prop :=
  IsAffineInState (fun ν => reflectedCorrelation a μ ν F 0) ∧
  IsAffineInState (fun ν => -4 * reflectedCorrelation a μ ν F (k • axisStep (a : ℝ) μ)) ∧
  IsAffineInState (fun ν => reflectedCorrelation a μ ν F ((2 * k) • axisStep (a : ℝ) μ)) ∧
  IsAffineInState (fun ν =>
    reflectedCorrelation a μ ν F (k • axisStep (a : ℝ) μ + k • axisStep (a : ℝ) lam)) ∧
  IsAffineInState (fun ν =>
    reflectedCorrelation a μ ν F (k • axisStep (a : ℝ) μ - k • axisStep (a : ℝ) lam))
end SiteFrame
open SiteFrame in
def CoarseStepFivePointBound : Prop :=
  ∀ (a : Spacing) (μ lam : Direction) (hne : μ ≠ lam) (ν : Measure (GaugeField (a : ℝ)))
    [IsProbabilityMeasure ν],
    PairConditions hne ν →
      (∀ k : ℕ, 1 ≤ k → ConeInequalityAtMultiple a μ ⟨lam, hne.symm⟩ ν k) ∧
      (∀ F ∈ localRegionObservables (a : ℝ) {x : Point | 0 ≤ x μ}, ∀ k : ℕ, 1 ≤ k →
        FivePointBound a μ lam ν F k) ∧
      (∀ F ∈ localRegionObservables (a : ℝ) {x : Point | 0 ≤ x μ},
        (∀ v : LatticePoint (a : ℝ), 0 ≤ (v : Point) μ →
          IsBoundedObservable (reflectedCorrelationFun a μ F v) ∧
            reflectedCorrelation a μ ν F v = ∫ U, reflectedCorrelationFun a μ F v U ∂ν) ∧
        ∀ k : ℕ, 1 ≤ k → FivePointTermsAffine a μ lam F k)
end YangMills.Construction.LatticeConventions
end
