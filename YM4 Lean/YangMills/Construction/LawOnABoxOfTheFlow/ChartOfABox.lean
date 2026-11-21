import YangMills.Construction.LawOnABoxOfTheFlow.BoxDefs
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped Quaternion
namespace YangMills.Construction
namespace BoxGaussian
open YangMills.Construction.TorusFields YangMills.Construction.TorusLumps
open YangMills.Construction.WeightedResponses YangMills.Construction.ResponseInTheExpansion
open YangMills.Construction.BlockAverages
variable {ℓ : StepParameters} {n : ℕ} [NeZero n]
structure BoxChart (T : StageTower ℓ) (k : ℕ) (o : TorusSite n) (R : ℕ) where
  goodOuter : Set (OuterData T k o R)
  orbitSet : Set (OuterData T k o R × InnerField o R)
  axialGauge : OuterData T k o R → TorusSite n → UnitQuaternion
  background : OuterData T k o R → TorusBond n → imaginaryQuaternions
  coord : OuterData T k o R → InnerField o R → TorusBond n → imaginaryQuaternions
  weight : OuterData T k o R → (TorusBond n → imaginaryQuaternions) → ℝ
  meanCurl : OuterData T k o R → TorusPlaquette n → imaginaryQuaternions
variable {T : StageTower ℓ} {k : ℕ} {o : TorusSite n} {R : ℕ}
def BoxChart.event (c : BoxChart T k o R) : Set (MarkedSample ℓ k n) :=
  {u | (outerData T k o R (stageState T k n u), restrictInner o R (stageState T k n u).1) ∈ c.orbitSet}
def BoxChart.coordLaw (c : BoxChart T k o R) (x c₀ : ℝ) (q : OuterData T k o R) :
    Measure (TorusBond n → imaginaryQuaternions) :=
  normalize (((sliceGaussian ℓ.coupling ℓ.side k o R x (c.background q)).restrict
    (sliceEllipsoid ℓ.coupling ℓ.side k o R (c.background q) c₀)).withDensity
      fun ζ => ENNReal.ofReal (c.weight q ζ))
structure BoxChart.IsMeasurable (c : BoxChart T k o R) : Prop where
  measurableSet_goodOuter : MeasurableSet c.goodOuter
  measurableSet_orbitSet : MeasurableSet c.orbitSet
  fst_mem_goodOuter : ∀ p ∈ c.orbitSet, p.1 ∈ c.goodOuter
  measurable_axialGauge : Measurable fun q : c.goodOuter => c.axialGauge q
  measurable_background : Measurable fun q : c.goodOuter => c.background q
  measurable_coord : Measurable fun p : c.orbitSet => c.coord p.1.1 p.1.2
  measurable_weight : Measurable fun p : c.goodOuter × (TorusBond n → imaginaryQuaternions) => c.weight p.1 p.2
  measurable_meanCurl : Measurable fun q : c.goodOuter => c.meanCurl q
  gauge_mem : ∀ p ∈ c.orbitSet, ∀ γ : TorusSite n → UnitQuaternion, IsSupportedGauge o R γ →
    (p.1, restrictInner o R (gaugeTransform γ (glueField p.1.1 p.2))) ∈ c.orbitSet
structure BoxChart.IsInGauge (c : BoxChart T k o R) (C δ c₀ : ℝ) : Prop where
  mem_chart : ∀ p ∈ c.orbitSet, ∃ γ : TorusSite n → UnitQuaternion, IsSupportedGauge o R γ ∧
    c.coord p.1 p.2 ∈ sliceEllipsoid ℓ.coupling ℓ.side k o R (c.background p.1) c₀ ∧
    IsInChart (supBall o (2 * R)) (c.background p.1) (c.coord p.1 p.2)
      (gaugeTransform (c.axialGauge p.1 * γ) (glueField p.1.1 p.2))
  coord_unique : ∀ p ∈ c.orbitSet, ∀ (γ : TorusSite n → UnitQuaternion)
    (ζ : TorusBond n → imaginaryQuaternions), IsSupportedGauge o R γ →
    ζ ∈ sliceEllipsoid ℓ.coupling ℓ.side k o R (c.background p.1) c₀ →
    IsInChart (supBall o (2 * R)) (c.background p.1) ζ
      (gaugeTransform (c.axialGauge p.1 * γ) (glueField p.1.1 p.2)) →
    ζ = c.coord p.1 p.2
  bounds : ∀ p ∈ c.orbitSet, ∃ (γ : TorusSite n → UnitQuaternion) (v β : TorusBond n → imaginaryQuaternions),
    IsSupportedGauge o R γ ∧
    (∀ b ∈ bondsWithin (supBall o (2 * R)),
      gaugeTransform (c.axialGauge p.1 * γ) (glueField p.1.1 p.2) b.1 b.2 = expUnit (v b) ∧
      v b = c.background p.1 b + c.coord p.1 p.2 b + β b ∧
      ‖β b‖ ≤ 2 * (‖c.background p.1 b‖ ^ 2 + ‖c.coord p.1 p.2 b‖ ^ 2) ∧ ‖v b‖ ≤ C * (R : ℝ) ^ 3 * δ ∧
      ‖c.background p.1 b‖ ≤ C * (R : ℝ) ^ 3 * δ ∧ ‖c.coord p.1 p.2 b‖ ≤ C * (R : ℝ) ^ 3 * δ) ∧
    bondNormSq (supBall o (2 * R)) v ≤ C * (R : ℝ) ^ 6 * δ ^ 2 ∧
    (∀ q ∈ plaquettesIn (supBall o (2 * R)),
      curvature (glueField p.1.1 p.2) q.1 q.2.1 q.2.2 ≤ C * (R : ℝ) ^ 2 * δ) ∧
    curlNormSq (supBall o (2 * R)) (c.background p.1 + c.coord p.1 p.2) ≤ C * (R : ℝ) ^ 4 * δ ^ 2
structure BoxChart.HasLaw (c : BoxChart T k o R) (P : Measure (MarkedSample ℓ k n)) (x c₀ ε : ℝ) : Prop where
  integral_eq : ∀ F : OuterData T k o R × (TorusBond n → imaginaryQuaternions) → ℝ, Measurable F →
    (∃ M : ℝ, ∀ z, |F z| ≤ M) →
    ∫ u in c.event, F (outerData T k o R (stageState T k n u),
        c.coord (outerData T k o R (stageState T k n u)) (restrictInner o R (stageState T k n u).1)) ∂P =
      ∫ u in c.event, ∫ ζ, F (outerData T k o R (stageState T k n u), ζ)
        ∂(c.coordLaw x c₀ (outerData T k o R (stageState T k n u))) ∂P
  weight_bounds : ∀ q ∈ c.goodOuter, ∀ ζ ∈ sliceEllipsoid ℓ.coupling ℓ.side k o R (c.background q) c₀,
    0 < c.weight q ζ ∧ |Real.log (c.weight q ζ)| ≤ ε
  ellipsoid_mass : ∀ q ∈ c.goodOuter,
    IsProbabilityMeasure (sliceGaussian ℓ.coupling ℓ.side k o R x (c.background q)) ∧
    1 - Real.exp (-((R : ℝ) ^ 4)) ≤
      (sliceGaussian ℓ.coupling ℓ.side k o R x (c.background q)).real
        (sliceEllipsoid ℓ.coupling ℓ.side k o R (c.background q) c₀)
structure BoxChart.HasCurl (c : BoxChart T k o R) (x C δ φ₀ : ℝ) (Cj : ℕ → ℝ) : Prop where
  map_eq_gaussian : ∀ q ∈ c.goodOuter, ∀ u : TorusPlaquette n → Fin 3 → ℝ,
    (sliceGaussian ℓ.coupling ℓ.side k o R x (c.background q)).map
        (fun ζ => colourPairing (supBall o (2 * R)) u
          fun p => lieFormCurl (c.background q + ζ) p - c.meanCurl q p) =
      gaussianReal 0 (x⁻¹ * curlQuadForm ℓ.coupling ℓ.side k o R u).toNNReal
  meanCurl_le : ∀ q ∈ c.goodOuter, ∀ p ∈ plaquettesIn (supBall o (2 * R)),
    ‖c.meanCurl q p‖ ≤ C * (R : ℝ) ^ 2 * δ
  iteratedDiff_le : ∀ q ∈ c.goodOuter, ∀ (l : List (Fin 4)), ∀ p ∈ plaquettesIn (supBall o ((R : ℝ) / 4)),
    ‖iteratedDiff l (c.meanCurl q) p‖ ≤ Cj l.length * ((R : ℝ) ^ l.length)⁻¹ * δ
  meanCurl_le_inner : ∀ q ∈ c.goodOuter, ∀ p ∈ plaquettesIn (supBall o ((R : ℝ) / 8)), ‖c.meanCurl q p‖ ≤ φ₀
end BoxGaussian
end YangMills.Construction
end
