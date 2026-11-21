import YangMills.Construction.InfiniteLattice.PeriodicGibbsStatesAndCopies
import Mathlib
set_option autoImplicit false
open MeasureTheory Set
noncomputable section
namespace YangMills.Construction.InfiniteLattice
variable {a : ℝ}
theorem one_eq_inv_mul_spacing (ha : 0 < a) : (1 : ℝ) = a⁻¹ * a :=
  (inv_mul_cancel₀ ha.ne').symm
def scaleByInv (a : ℝ) (x : AmbientSpace) : AmbientSpace := a⁻¹ • x
def scaleByInvImage (a : ℝ) (S : Set AmbientSpace) : Set AmbientSpace := scaleByInv a '' S
def pointRescale (ha : 0 < a) : LatticePoint a →+ LatticePoint 1 :=
  AddMonoidHom.mk' (pointScale a⁻¹ (one_eq_inv_mul_spacing ha))
    fun x y => Subtype.ext (smul_add a⁻¹ (x : AmbientSpace) y)
theorem coe_pointRescale (ha : 0 < a) (x : LatticePoint a) :
    ((pointRescale ha x : LatticePoint 1) : AmbientSpace) = scaleByInv a x := rfl
def subgroupRescale (ha : 0 < a) (Q : AddSubgroup (LatticePoint a)) :
    AddSubgroup (LatticePoint 1) :=
  Q.map (pointRescale ha)
def rescaledLink (ha : 0 < a) (b : Link a) : Link 1 :=
  linkScale a⁻¹ (one_eq_inv_mul_spacing ha) b
def rescaledPlaquette (ha : 0 < a) (p : ElementaryPlaquette a) : ElementaryPlaquette 1 :=
  plaquetteScale a⁻¹ (one_eq_inv_mul_spacing ha) p
theorem rescaledPlaquette_eq (ha : 0 < a) (p : ElementaryPlaquette a) :
    rescaledPlaquette ha p =
      ⟨pointRescale ha p.corner, p.lowAxis, p.highAxis, p.lowAxis_lt_highAxis⟩ := rfl
def fieldRescale (ha : 0 < a) (U : GaugeField a) : GaugeField 1 :=
  gaugeFieldScale (inv_pos.2 ha) (one_eq_inv_mul_spacing ha) U
theorem fieldRescale_rescaledLink (ha : 0 < a) (U : GaugeField a) (b : Link a) :
    fieldRescale ha U (rescaledLink ha b) = U b :=
  gaugeFieldScale_linkScale (inv_pos.2 ha) (one_eq_inv_mul_spacing ha) U b
theorem fieldRescale_apply (ha : 0 < a) (U : GaugeField a) (b : Link 1) :
    fieldRescale ha U b = U (linkScale a (mul_one a).symm b) := by
  refine congrArg U.1 (Link.ext (Subtype.ext ?_) (Subtype.ext ?_)) <;>
    simp [linkScale, pointScale]
theorem measurable_fieldRescale (ha : 0 < a) :
    Measurable (fieldRescale ha) :=
  measurable_gaugeFieldScale (inv_pos.2 ha) (one_eq_inv_mul_spacing ha)
end YangMills.Construction.InfiniteLattice
