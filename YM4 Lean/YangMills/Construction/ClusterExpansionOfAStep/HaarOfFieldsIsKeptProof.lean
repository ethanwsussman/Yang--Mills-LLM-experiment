import YangMills.Construction.ClusterExpansionOfAStep.StatesOfGivenShapes
import YangMills.Construction.ClusterExpansionOfAStep.HaarOfFieldsIsKept
import YangMills.Construction.ResponseInTheExpansion.ElementsOfABond
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory Measure
namespace YangMills.Construction
open BlockAverages TorusFields
namespace FieldHaar
theorem eq_haarUnit_of_isMulLeftInvariant (μ : Measure UnitQuaternion) [IsProbabilityMeasure μ]
    [IsMulLeftInvariant μ] : μ = haarUnit := by apply _root_.YangMills.Construction.WeightedResponses.eq_haarUnit_of_isMulLeftInvariant <;> assumption
instance haarUnit_isMulRightInvariant : IsMulRightInvariant haarUnit := by
  constructor
  intro g
  have : IsMulLeftInvariant (map (· * g) haarUnit) := isMulLeftInvariant_map_mul_right g
  have : IsProbabilityMeasure (map (· * g) haarUnit) :=
    Measure.isProbabilityMeasure_map (measurable_mul_const g).aemeasurable
  exact eq_haarUnit_of_isMulLeftInvariant _
instance haarUnit_isInvInvariant : IsInvInvariant haarUnit := by
  constructor
  have : IsProbabilityMeasure haarUnit.inv := by
    unfold Measure.inv
    exact Measure.isProbabilityMeasure_map measurable_inv.aemeasurable
  exact eq_haarUnit_of_isMulLeftInvariant haarUnit.inv
theorem measurePreserving_mul_mul (g h : UnitQuaternion) :
    MeasurePreserving (fun u : UnitQuaternion => g * u * h) haarUnit haarUnit :=
  (measurePreserving_mul_right haarUnit h).comp (measurePreserving_mul_left haarUnit g)
theorem measurePreserving_inv_unit :
    MeasurePreserving (fun u : UnitQuaternion => u⁻¹) haarUnit haarUnit :=
  Measure.measurePreserving_inv haarUnit
variable {n : ℕ} [NeZero n]
def bondProductHaar (n : ℕ) [NeZero n] : Measure (TorusBond n → UnitQuaternion) :=
  Measure.pi fun _ : TorusBond n => haarUnit
theorem map_uncurry_fieldHaar :
    (fieldHaar n).map (MeasurableEquiv.curry (TorusSite n) (Fin 4) UnitQuaternion).symm =
      bondProductHaar n := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.map_uncurry_fieldHaar <;> assumption
theorem measurePreserving_uncurry :
    MeasurePreserving (MeasurableEquiv.curry (TorusSite n) (Fin 4) UnitQuaternion).symm
      (fieldHaar n) (bondProductHaar n) := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.measurePreserving_uncurry_fieldHaar <;> assumption
theorem measurePreserving_bondwise (σ : TorusBond n ≃ TorusBond n)
    (φ : TorusBond n → UnitQuaternion → UnitQuaternion)
    (hφ : ∀ b, MeasurePreserving (φ b) haarUnit haarUnit) :
    MeasurePreserving (fun (A : TorusField n) x i => φ (x, i) (A (σ (x, i)).1 (σ (x, i)).2))
      (fieldHaar n) (fieldHaar n) := by
  have hperm : MeasurePreserving (fun (w : TorusBond n → UnitQuaternion) b => w (σ b))
      (bondProductHaar n) (bondProductHaar n) := by
    have hpi := measurePreserving_piCongrLeft (fun _ : TorusBond n => haarUnit) σ.symm
    have hfun : (fun (w : TorusBond n → UnitQuaternion) b => w (σ b)) =
        MeasurableEquiv.piCongrLeft (fun _ : TorusBond n => UnitQuaternion) σ.symm := by
      funext w b
      have happ := Equiv.piCongrLeft_apply_apply (fun _ : TorusBond n => UnitQuaternion) σ.symm w (σ b)
      simp only [Equiv.symm_apply_apply] at happ
      exact happ.symm
    rw [hfun]
    exact hpi
  have hmap : MeasurePreserving (fun (w : TorusBond n → UnitQuaternion) b => φ b (w b))
      (bondProductHaar n) (bondProductHaar n) :=
    measurePreserving_pi _ _ hφ
  have hback := (measurePreserving_uncurry (n := n)).symm
  have hall := (hback.comp (hmap.comp (hperm.comp measurePreserving_uncurry)))
  exact hall
def siteEquiv (g : TorusIsometry) : TorusSite n ≃ TorusSite n :=
  Equiv.ofBijective (g.mapSite (n := n))
    ((Finite.injective_iff_bijective).mp fun x x' hxx => by
      have hcoord : ∀ i, x (g.axisPerm i) = x' (g.axisPerm i) := by
        intro i
        have hi := congrFun hxx i
        simp only [TorusIsometry.mapSite] at hi
        rcases g.axisSign_unit i with hs | hs
        · simpa [hs] using hi
        · simpa [hs] using hi
      funext k
      have hk := hcoord (g.axisPerm.symm k)
      simpa using hk)
theorem siteEquiv_apply (g : TorusIsometry) (x : TorusSite n) : siteEquiv g x = g.mapSite x := rfl
def preimageBond (g : TorusIsometry) (b : TorusBond n) : TorusBond n :=
  ((siteEquiv g).symm (if g.axisSign b.2 = 1 then b.1 else b.1 + TorusFields.unitStep n b.2), g.axisPerm b.2)
def imageBond (g : TorusIsometry) (b : TorusBond n) : TorusBond n :=
  (if g.axisSign (g.axisPerm.symm b.2) = 1 then g.mapSite b.1
    else g.mapSite b.1 - TorusFields.unitStep n (g.axisPerm.symm b.2),
    g.axisPerm.symm b.2)
def bondEquiv (g : TorusIsometry) : TorusBond n ≃ TorusBond n where
  toFun := preimageBond g
  invFun := imageBond g
  left_inv := by
    rintro ⟨y, i⟩
    by_cases hs : g.axisSign i = 1
    · simp [preimageBond, imageBond, hs, ← siteEquiv_apply g]
    · simp [preimageBond, imageBond, hs, ← siteEquiv_apply g]
  right_inv := by
    rintro ⟨x, k⟩
    by_cases hs : g.axisSign (g.axisPerm.symm k) = 1
    · simp [preimageBond, imageBond, hs, ← siteEquiv_apply g]
    · simp [preimageBond, imageBond, hs, ← siteEquiv_apply g]
theorem haarInvariantUnderSymmetries_holds : HaarInvariantUnderSymmetries := by
  intro n _
  refine ⟨fun g => ?_, fun g => ?_⟩
  · have hg := measurePreserving_bondwise (n := n) (Equiv.refl _)
      (fun b u => g b.1 * u * (g (b.1 + TorusFields.unitStep n b.2))⁻¹)
      (fun b => measurePreserving_mul_mul _ _)
    exact hg
  · let φ : TorusBond n → UnitQuaternion → UnitQuaternion :=
      fun b u => if g.axisSign b.2 = 1 then u else u⁻¹
    have hφ : ∀ b, MeasurePreserving (φ b) haarUnit haarUnit := by
      intro b
      by_cases hs : g.axisSign b.2 = 1
      · simp only [φ, hs, if_true]
        exact MeasurePreserving.id _
      · simp only [φ, hs, if_false]
        exact measurePreserving_inv_unit
    refine ⟨_, measurePreserving_bondwise (bondEquiv g) φ hφ, fun A x k => ?_⟩
    by_cases hs : g.axisSign (g.axisPerm.symm k) = 1
    · simp [hs, φ, bondEquiv, preimageBond, ← siteEquiv_apply g]
    · simp [hs, φ, bondEquiv, preimageBond, ← siteEquiv_apply g]
end FieldHaar
end YangMills.Construction
end
