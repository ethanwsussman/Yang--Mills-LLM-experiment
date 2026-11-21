import YangMills.Construction.Towers.CurvesAtTheSideInfinityInTheLeftChartProof
import YangMills.Construction.Towers.GaugeConditionsOfTheAlgebraOfTheLeftChartOnASideProof
import YangMills.Construction.Towers.GaugeCovarianceOfTheDerivativesOfTheActionAtTheSideInfinityProof
import YangMills.Construction.Towers.LinearMapsOfTheWholeLatticeAreOntoProof
import YangMills.Construction.Towers.MatrixFactsOfTheAlgebraOfTheLeftChart
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.Tower.LeftChartAlgebra.InfiniteSideGaugeProof
open Matrices
theorem isUnit_det_of_det_eq_one {V : ComplexMatrix2} (h : V.det = 1) : IsUnit V.det := by apply _root_.YangMills.SharedProofs.p11557 <;> assumption
open Matrices
theorem conjugateBy_sub (V X Y : ComplexMatrix2) :
    ComplexMatrix2.conjugateBy V (X - Y) = ComplexMatrix2.conjugateBy V X - ComplexMatrix2.conjugateBy V Y := by
  simp only [ComplexMatrix2.conjugateBy, mul_sub, sub_mul]
theorem conjugateBy_smul (V X : ComplexMatrix2) (c : ℂ) :
    ComplexMatrix2.conjugateBy V (c • X) = c • ComplexMatrix2.conjugateBy V X := by
  simp only [ComplexMatrix2.conjugateBy, Matrix.mul_smul, Matrix.smul_mul]
theorem conjugateBy_inv_conjugateBy (V X : ComplexMatrix2) (hV : V.det = 1) :
    ComplexMatrix2.conjugateBy V⁻¹ (ComplexMatrix2.conjugateBy V X) = X := by apply _root_.YangMills.Construction.Tower.LeftChartGauge.conjugateBy_inv_conjugateBy <;> assumption
theorem conjugateBy_conjugateBy_inv (V X : ComplexMatrix2) (hV : V.det = 1) :
    ComplexMatrix2.conjugateBy V (ComplexMatrix2.conjugateBy V⁻¹ X) = X := by apply _root_.YangMills.Construction.Tower.LeftChartGauge.conjugateBy_conjugateBy_inv <;> assumption
theorem conjugateBy_gauge_mul (A U B X : ComplexMatrix2) (hB : B.det = 1) :
    ComplexMatrix2.conjugateBy (A * U * B⁻¹) (ComplexMatrix2.conjugateBy B X) =
      ComplexMatrix2.conjugateBy A (ComplexMatrix2.conjugateBy U X) := by apply _root_.YangMills.Construction.Tower.LeftChartAlgebra.GaugeRequirements.conjugateBy_gauged <;> assumption
theorem fullTrace_conj (V X : ComplexMatrix2) (hV : V.det = 1) :
    ComplexMatrix2.fullTrace (V * X * V⁻¹) = ComplexMatrix2.fullTrace X := by apply _root_.YangMills.Construction.Tower.LeftChartAlgebra.GaugeRequirements.trace_conj_eq <;> assumption
theorem conjugateBy_mem_traceless {V X : ComplexMatrix2} (hV : V.det = 1)
    (hX : X ∈ ComplexMatrix2.traceless) : ComplexMatrix2.conjugateBy V X ∈ ComplexMatrix2.traceless := by apply _root_.YangMills.Construction.Tower.TrivialFieldAverages.conjugateBy_mem_traceless_of_det <;> assumption
theorem det_eq_one_of_mem_specialUnitary {V : ComplexMatrix2} (hV : V ∈ ComplexMatrix2.specialUnitary) :
    V.det = 1 :=
  (Matrix.mem_specialUnitaryGroup_iff.1 hV).2
theorem inv_mem_specialUnitary {V : ComplexMatrix2} (hV : V ∈ ComplexMatrix2.specialUnitary) :
    V⁻¹ ∈ ComplexMatrix2.specialUnitary := by apply _root_.YangMills.Construction.Tower.WilsonAnalyticity.inv_mem_specialUnitary <;> assumption
theorem conjugateBy_mem_hermitianTraceless_of {V X : ComplexMatrix2}
    (hV : V ∈ ComplexMatrix2.specialUnitary) (hX : X ∈ ComplexMatrix2.hermitianTraceless) :
    ComplexMatrix2.conjugateBy V X ∈ ComplexMatrix2.hermitianTraceless := by apply _root_.YangMills.Construction.Tower.LeftChartGauge.conjugateBy_mem_hermitianTraceless <;> assumption
theorem prod_four_conj_cancel (A B C D X Y Z W : ComplexMatrix2) (hB : B.det = 1) (hC : C.det = 1)
    (hD : D.det = 1) :
    (A * X * B⁻¹) * ((B * Y * C⁻¹) * ((C * Z * D⁻¹) * (D * W * A⁻¹))) =
      A * (X * (Y * (Z * W))) * A⁻¹ := by apply _root_.YangMills.Construction.Tower.LeftChartAlgebra.GaugeRequirements.gauged_loop_product <;> assumption
theorem isUnitaryOnSet_of_conjugateBy {α ι : Type*} [AddCommGroup α] [Module ℂ α] {S : Set α}
    {r : α → ι → ComplexMatrix2} {T T' : α → α} {v : ι → ComplexMatrix2}
    (hv : ∀ g ∈ PeriodicLattice.compactGaugeGroup, ∀ X ∈ ComplexMatrix2.traceless,
      ∀ Y ∈ ComplexMatrix2.traceless,
      halfTraceProduct (ComplexMatrix2.conjugateBy g X) (ComplexMatrix2.conjugateBy g Y) =
        halfTraceProduct X Y)
    (hvG : ∀ i, v i ∈ PeriodicLattice.compactGaugeGroup)
    (hS : MapsTo T S S) (hS' : MapsTo T' S S)
    (h₁ : ∀ f ∈ S, T (T' f) = f) (h₂ : ∀ f ∈ S, T' (T f) = f)
    (hadd : ∀ f f', T (f + f') = T f + T f') (hsmul : ∀ (c : ℂ) f, T (c • f) = c • T f)
    (hval : ∀ f i, r (T f) i = ComplexMatrix2.conjugateBy (v i) (r f i))
    (hsl : ∀ f ∈ S, ∀ i, r f i ∈ ComplexMatrix2.traceless) : IsUnitaryOnSet S r T where
  bijOn := Set.InvOn.bijOn ⟨h₂, h₁⟩ hS hS'
  map_add := fun f _ f' _ => hadd f f'
  map_smul := fun c f _ => hsmul c f
  inner_eq := fun f hf f' hf' => by
    unfold hermitianInner
    refine tsum_congr fun i => ?_
    rw [hval, hval]
    exact hv _ (hvG i) _ (hsl f hf i) _ (hsl f' hf' i)
theorem isL2Traceless_conjugateBy {ι : Type*} {f g v : ι → ComplexMatrix2}
    (hv : ∀ g ∈ PeriodicLattice.compactGaugeGroup, ∀ X ∈ ComplexMatrix2.traceless,
      ∀ Y ∈ ComplexMatrix2.traceless,
      halfTraceProduct (ComplexMatrix2.conjugateBy g X) (ComplexMatrix2.conjugateBy g Y) =
        halfTraceProduct X Y)
    (hvG : ∀ i, v i ∈ PeriodicLattice.compactGaugeGroup) (hf : IsL2Traceless f)
    (hg : ∀ i, g i = ComplexMatrix2.conjugateBy (v i) (f i)) : IsL2Traceless g := by
  refine ⟨fun i => ?_, ?_⟩
  · rw [hg]
    exact conjugateBy_mem_traceless (det_eq_one_of_mem_specialUnitary (hvG i)) (hf.1 i)
  · refine hf.2.congr fun i => ?_
    rw [hg, hv _ (hvG i) _ (hf.1 i) _ (hf.1 i)]
section Lattice
variable {a : ℝ}
theorem extendOddly_of_pos (f : InfiniteLattice.Link a → ComplexMatrix2) {b : InfiniteLattice.Link a}
    (hb : b.IsPositivelyOriented) : FullSpace.extendOddly f b = f b := by apply _root_.YangMills.Construction.Tower.FullSpace.Translations.extendOddly_of_pos <;> assumption
theorem extendOddly_opposite (ha : 0 < a) (f : InfiniteLattice.Link a → ComplexMatrix2)
    (b : InfiniteLattice.Link a) :
    FullSpace.extendOddly f b.opposite = -FullSpace.extendOddly f b := by apply _root_.YangMills.Construction.Tower.FullSpace.CurveDerivatives.extendOddly_opposite <;> assumption
theorem extendOddly_congr {f g : InfiniteLattice.Link a → ComplexMatrix2}
    (h : ∀ b : InfiniteLattice.Link a, b.IsPositivelyOriented → f b = g b) :
    FullSpace.extendOddly f = FullSpace.extendOddly g := by apply _root_.YangMills.Construction.Tower.FullSpace.Translations.extendOddly_congr <;> assumption
theorem odd_ext_of_pos {B B' : InfiniteLattice.Link a → ComplexMatrix2}
    (r : ∀ b : InfiniteLattice.Link a, B b.opposite = -B b)
    (r' : ∀ b : InfiniteLattice.Link a, B' b.opposite = -B' b)
    (h : ∀ b : InfiniteLattice.Link a, b.IsPositivelyOriented → B b = B' b) : B = B' := by apply _root_.YangMills.Construction.Tower.FullSpace.Surjectivity.eq_of_eq_on_positive <;> assumption
theorem adjointForm_of_pos (u : InfiniteLattice.LatticePoint a → ComplexMatrix2)
    (B : InfiniteLattice.Link a → ComplexMatrix2) {b : InfiniteLattice.Link a}
    (hb : b.IsPositivelyOriented) :
    FullSpace.adjointForm u B b = ComplexMatrix2.conjugateBy (u b.initial) (B b) :=
  extendOddly_of_pos _ hb
theorem adjointForm_add (u : InfiniteLattice.LatticePoint a → ComplexMatrix2)
    (B B' : InfiniteLattice.Link a → ComplexMatrix2) :
    FullSpace.adjointForm u (B + B') = FullSpace.adjointForm u B + FullSpace.adjointForm u B' := by apply _root_.YangMills.Construction.Tower.FullSpace.CovarianceProof.adjointForm_add <;> assumption
theorem adjointForm_smul (u : InfiniteLattice.LatticePoint a → ComplexMatrix2) (c : ℂ)
    (B : InfiniteLattice.Link a → ComplexMatrix2) :
    FullSpace.adjointForm u (c • B) = c • FullSpace.adjointForm u B := by apply _root_.YangMills.Construction.Tower.FullSpace.ActionDerivativeCovariance.adjointForm_smul <;> assumption
theorem adjointVertexFn_add (u l l' : InfiniteLattice.LatticePoint a → ComplexMatrix2) :
    FullSpace.adjointVertexFn u (l + l') =
      FullSpace.adjointVertexFn u l + FullSpace.adjointVertexFn u l' := by apply _root_.YangMills.Construction.Tower.FullSpace.CovarianceProof.adjointVertexFn_add <;> assumption
theorem adjointVertexFn_smul (u : InfiniteLattice.LatticePoint a → ComplexMatrix2) (c : ℂ)
    (l : InfiniteLattice.LatticePoint a → ComplexMatrix2) :
    FullSpace.adjointVertexFn u (c • l) = c • FullSpace.adjointVertexFn u l := by
  funext x
  exact conjugateBy_smul _ _ _
theorem covDiff_gaugeAct (u l : InfiniteLattice.LatticePoint a → ComplexMatrix2)
    (U : InfiniteLattice.Link a → ComplexMatrix2) (hu : ∀ x, (u x).det = 1) :
    FullSpace.covDiff (FullSpace.gaugeAct u U) (FullSpace.adjointVertexFn u l) =
      FullSpace.adjointForm u (FullSpace.covDiff U l) := by
  refine extendOddly_congr fun b hb => ?_
  have e : FullSpace.covDiff U l b =
      ComplexMatrix2.conjugateBy (U b) (l b.terminal) - l b.initial := extendOddly_of_pos _ hb
  rw [e, conjugateBy_sub]
  change ComplexMatrix2.conjugateBy (u b.initial * U b * (u b.terminal)⁻¹)
      (ComplexMatrix2.conjugateBy (u b.terminal) (l b.terminal)) -
    ComplexMatrix2.conjugateBy (u b.initial) (l b.initial) = _
  rw [conjugateBy_gauge_mul _ _ _ _ (hu _)]
theorem faceVariable_gaugeAct (u : InfiniteLattice.LatticePoint a → ComplexMatrix2)
    (U : InfiniteLattice.Link a → ComplexMatrix2) (hu : ∀ x, (u x).det = 1)
    (p : InfiniteLattice.ElementaryPlaquette a) :
    FullSpace.faceVariable (FullSpace.gaugeAct u U) p =
      u p.corner * FullSpace.faceVariable U p * (u p.corner)⁻¹ := by
  have hc : p.corner + InfiniteLattice.axisStep a p.highAxis + InfiniteLattice.axisStep a p.lowAxis =
      p.corner + InfiniteLattice.axisStep a p.lowAxis + InfiniteLattice.axisStep a p.highAxis := by
    abel
  simp only [FullSpace.faceVariable, FullSpace.linkHolonomy, FullSpace.faceBoundary, List.map_cons,
    List.map_nil, List.prod_cons, List.prod_nil, mul_one]
  change (u p.corner * _ * (u (p.corner + InfiniteLattice.axisStep a p.lowAxis))⁻¹) *
    ((u (p.corner + InfiniteLattice.axisStep a p.lowAxis) * _ *
        (u (p.corner + InfiniteLattice.axisStep a p.lowAxis +
          InfiniteLattice.axisStep a p.highAxis))⁻¹) *
      ((u (p.corner + InfiniteLattice.axisStep a p.highAxis +
          InfiniteLattice.axisStep a p.lowAxis) * _ *
          (u (p.corner + InfiniteLattice.axisStep a p.highAxis))⁻¹) *
        (u (p.corner + InfiniteLattice.axisStep a p.highAxis) * _ * (u p.corner)⁻¹))) = _
  rw [hc]
  exact prod_four_conj_cancel _ _ _ _ _ _ _ _ (hu _) (hu _) (hu _)
end Lattice
theorem meshAt_pos {L : ℕ} (hL : Conventions.IsAdmissibleBlockingFactor L) (k j : ℕ) :
    0 < meshAt L k j := by apply _root_.YangMills.Construction.Tower.BlockPathContourPivotProof.Periodic.meshAt_pos <;> assumption
theorem gaugeCovariance_holds (L k j : ℕ) : FullSpace.LeftChartAlgebra.GaugeCovariance L k j := by
  intro U u _ hu
  have hd : ∀ x, (u x).det = 1 := hu
  refine ⟨fun l _ => covDiff_gaugeAct u l U hd, fun p => ?_⟩
  have hp := faceVariable_gaugeAct u U hd p
  refine ⟨hp, ?_⟩
  unfold FullSpace.complexFaceTerm
  rw [hp, fullTrace_conj _ _ (hd _)]
theorem gaugeUnitarity_holds (hM : MatrixIdentities.Statement) {L : ℕ}
    (hL : Conventions.IsAdmissibleBlockingFactor L) (k j : ℕ) :
    FullSpace.LeftChartAlgebra.GaugeUnitarity L k j := by
  obtain ⟨-, -, hS, hv⟩ := hM
  have ha := meshAt_pos hL k j
  refine ⟨hS _, hS _, fun u hu => ?_⟩
  have hG : ∀ x, u x ∈ ComplexMatrix2.specialUnitary := hu
  have hd : ∀ x, (u x).det = 1 := fun x => det_eq_one_of_mem_specialUnitary (hG x)
  have hG' : ∀ x, (u x)⁻¹ ∈ ComplexMatrix2.specialUnitary := fun x => inv_mem_specialUnitary (hG x)
  have hformS : ∀ w : FullSpace.Vertex L k j → ComplexMatrix2,
      (∀ x, w x ∈ ComplexMatrix2.specialUnitary) →
      MapsTo (FullSpace.adjointForm w) (FullSpace.l2Forms (meshAt L k j))
        (FullSpace.l2Forms (meshAt L k j)) := by
    intro w hw B hB
    refine ⟨⟨fun b hb => ?_, fun b => extendOddly_opposite ha _ b⟩, ?_⟩
    · rw [adjointForm_of_pos _ _ hb]
      exact conjugateBy_mem_traceless (det_eq_one_of_mem_specialUnitary (hw _)) (hB.1.1 b hb)
    · exact isL2Traceless_conjugateBy hv
        (v := fun b : FullSpace.PositiveEdge (meshAt L k j) => w b.1.initial)
        (fun b => hw _) hB.2 fun b => adjointForm_of_pos w B b.2
  have hsiteS : ∀ w : FullSpace.Vertex L k j → ComplexMatrix2,
      (∀ x, w x ∈ ComplexMatrix2.specialUnitary) →
      MapsTo (FullSpace.adjointVertexFn w) {l : FullSpace.Vertex L k j → ComplexMatrix2 | IsL2Traceless l}
        {l : FullSpace.Vertex L k j → ComplexMatrix2 | IsL2Traceless l} :=
    fun w hw l hl => isL2Traceless_conjugateBy hv hw hl fun _ => rfl
  refine ⟨fun B hB => ⟨fun b hb => ?_, fun b => extendOddly_opposite ha _ b⟩,
    fun l hl x _ => ?_, ?_, ?_⟩
  · rw [adjointForm_of_pos _ _ hb]
    exact conjugateBy_mem_hermitianTraceless_of (hG _) (hB.1 b hb)
  · exact conjugateBy_mem_hermitianTraceless_of (hG _) (hl x trivial)
  · refine isUnitaryOnSet_of_conjugateBy (T' := FullSpace.adjointForm fun x => (u x)⁻¹)
      (v := fun b : FullSpace.PositiveEdge (meshAt L k j) => u b.1.initial) hv (fun b => hG _)
      (hformS u hG) (hformS _ hG') ?_ ?_ (adjointForm_add u) (adjointForm_smul u)
      (fun B b => adjointForm_of_pos u B b.2) (fun B hB b => hB.1.1 b.1 b.2)
    · intro B hB
      refine odd_ext_of_pos (extendOddly_opposite ha _) hB.1.2 fun b hb => ?_
      rw [adjointForm_of_pos _ _ hb, adjointForm_of_pos _ _ hb]
      exact conjugateBy_conjugateBy_inv _ _ (hd _)
    · intro B hB
      refine odd_ext_of_pos (extendOddly_opposite ha _) hB.1.2 fun b hb => ?_
      rw [adjointForm_of_pos _ _ hb, adjointForm_of_pos _ _ hb]
      exact conjugateBy_inv_conjugateBy _ _ (hd _)
  · refine isUnitaryOnSet_of_conjugateBy (T' := FullSpace.adjointVertexFn fun x => (u x)⁻¹) (v := u)
      hv hG (hsiteS u hG) (hsiteS _ hG') ?_ ?_ (adjointVertexFn_add u) (adjointVertexFn_smul u)
      (fun _ _ => rfl) (fun l hl x => hl.1 x)
    · intro l _
      funext x
      exact conjugateBy_conjugateBy_inv _ _ (hd _)
    · intro l _
      funext x
      exact conjugateBy_inv_conjugateBy _ _ (hd _)
theorem gaugeIdentitiesInfiniteSide_holds (hM : MatrixIdentities.Statement) : GaugeConditionsInfiniteSide :=
  fun L k j hL _ => ⟨gaugeCovariance_holds L k j, gaugeUnitarity_holds hM hL k j⟩
end YangMills.Construction.Tower.LeftChartAlgebra.InfiniteSideGaugeProof
end
