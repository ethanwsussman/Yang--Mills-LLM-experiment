import YangMills.Construction.InfiniteLattice.ActionOfTheLatticeIsometriesOnObservables
import YangMills.Construction.InfiniteLattice.AllLatticeIsometriesAndTheMeanOfThePlaquetteFunction
import YangMills.Construction.InfiniteLattice.ReflectionPositivityContainsReflectionInvariance
import Mathlib
set_option autoImplicit false
open MeasureTheory
open scoped Matrix
noncomputable section
namespace YangMills.Construction
namespace LatticeConventions
namespace SymmetryGeneration
open InfiniteLattice (Link GaugeField IsSymmetricUnder IsBoundedObservable LatticeSymmetry
  ElementaryPlaquette LatticePoint AmbientSpace faceEnergy faceHolonomy latticeSubgroup axisStep shift)
open NormalHyperplane (reflectSymmetry)
variable {a : ℝ}
theorem symmetry_ext {r s : LatticeSymmetry a} (h : r.toFun = s.toFun) : r = s := by apply _root_.YangMills.Construction.ReflectionPositivity.MirrorHyperplanes.latticeSymmetry_ext <;> assumption
theorem dotProduct_sub_map_self (r : LatticeSymmetry a) (x y : Point) :
    (r.toFun x - r.toFun y) ⬝ᵥ (r.toFun x - r.toFun y) = (x - y) ⬝ᵥ (x - y) := by
  have h := r.preservesDist x y
  unfold TorusMetric.euclidNormVec at h
  have h' := (Real.sqrt_inj (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    (Finset.sum_nonneg fun _ _ => sq_nonneg _)).mp h
  simpa only [dotProduct, sq] using h'
theorem dotProduct_map_of_fix_zero {r : LatticeSymmetry a} (h0 : r.toFun 0 = 0) (x y : Point) :
    r.toFun x ⬝ᵥ r.toFun y = x ⬝ᵥ y := by
  have hx : ∀ z, r.toFun z ⬝ᵥ r.toFun z = z ⬝ᵥ z := fun z => by
    have := dotProduct_sub_map_self r z 0
    simpa [h0] using this
  have h := dotProduct_sub_map_self r x y
  simp only [sub_dotProduct, dotProduct_sub, hx] at h
  rw [dotProduct_comm (r.toFun y), dotProduct_comm y x] at h
  linarith
theorem reflect_of_orthogonal (Q : NormalHyperplane) (h0 : Q.level = 0) {x : Point}
    (h : Q.normal ⬝ᵥ x = 0) : Q.reflect x = x := by
  rw [Q.reflect_eq_hyperplaneReflect, InfiniteLattice.hyperplaneReflect, h, h0]
  simp
theorem reflect_of_sub_eq_smul (Q : NormalHyperplane) (h0 : Q.level = 0) {u w : Point}
    {t : ℝ} (huw : u - w = t • Q.normal) (hne : u ≠ w) (hn : u ⬝ᵥ u = w ⬝ᵥ w) :
    Q.reflect w = u := by
  have ht : t ≠ 0 := by
    rintro rfl
    rw [zero_smul] at huw
    exact hne (sub_eq_zero.mp huw)
  have hnn : Q.normal ⬝ᵥ Q.normal ≠ 0 := by
    intro h
    rw [dotProduct_self_eq_zero] at h
    rw [h, smul_zero] at huw
    exact hne (sub_eq_zero.mp huw)
  have hu : u = w + t • Q.normal := by rw [← huw]; abel
  have h1 : t * (2 * (Q.normal ⬝ᵥ w) + t * (Q.normal ⬝ᵥ Q.normal)) = 0 := by
    rw [hu] at hn
    simp only [add_dotProduct, dotProduct_add, smul_dotProduct, dotProduct_smul, smul_eq_mul] at hn
    rw [dotProduct_comm w Q.normal] at hn
    linarith
  have h2 : 2 * (Q.normal ⬝ᵥ w) + t * (Q.normal ⬝ᵥ Q.normal) = 0 :=
    (mul_eq_zero.mp h1).resolve_left ht
  have h3 : 2 * (Q.normal ⬝ᵥ w) / (Q.normal ⬝ᵥ Q.normal) = -t := by
    rw [div_eq_iff hnn]
    linarith
  rw [Q.reflect_eq_hyperplaneReflect, InfiniteLattice.hyperplaneReflect, h0, sub_zero, h3, hu,
    neg_smul, sub_neg_eq_add]
theorem isLatticeMirror_of_level_eq_zero (Q : NormalHyperplane) (h0 : Q.level = 0) :
    Q.IsLatticeMirror a :=
  ⟨fun _ => ⟨0, by simp [h0]⟩, fun _ => ⟨0, by simp [h0]⟩⟩
theorem exists_normal_of_moves_basis {r : LatticeSymmetry a} (h0 : r.toFun 0 = 0) (μ : Direction)
    (hw : r.toFun (Pi.single μ a) ≠ Pi.single μ a) :
    ∃ (Q : NormalHyperplane) (t : ℝ), Q.level = 0 ∧
      (Pi.single μ a : Point) - r.toFun (Pi.single μ a) = t • Q.normal := by
  have hdist : TorusMetric.euclidNormVec
      (((r.pointMap (axisStep a μ) : LatticePoint a) : AmbientSpace) -
        ((0 : LatticePoint a) : AmbientSpace)) = |a| := by
    have h := r.preservesDist (Pi.single μ a) 0
    rw [h0, sub_zero, sub_zero, InfiniteLattice.euclidNormVec_single] at h
    simpa [LatticeSymmetry.pointMap, axisStep] using h
  obtain ⟨κ, h | h⟩ := InfiniteLattice.isAdjacent_of_euclidNormVec _ _ hdist
  · rw [sub_zero] at h
    have h' : r.toFun (Pi.single μ a) = Pi.single κ a := congrArg Subtype.val h
    have hκ : μ ≠ κ := by
      rintro rfl
      exact hw h'
    refine ⟨⟨basisVector μ - basisVector κ, 0, Or.inr ⟨μ, κ, hκ, Or.inr rfl⟩⟩, a, rfl, ?_⟩
    rw [h']
    funext ν
    simp only [basisVector, Pi.sub_apply, Pi.smul_apply, Pi.single_apply, smul_eq_mul]
    split_ifs <;> ring
  · rw [sub_zero] at h
    have h' : r.toFun (Pi.single μ a) = -Pi.single κ a := congrArg Subtype.val h
    by_cases hκ : μ = κ
    · subst hκ
      refine ⟨NormalHyperplane.axial μ 0, 2 * a, rfl, ?_⟩
      rw [h']
      funext ν
      simp only [NormalHyperplane.axial, basisVector, Pi.sub_apply, Pi.neg_apply,
        Pi.smul_apply, Pi.single_apply, smul_eq_mul]
      split_ifs <;> ring
    · refine ⟨⟨basisVector μ + basisVector κ, 0, Or.inr ⟨μ, κ, hκ, Or.inl rfl⟩⟩, a, rfl, ?_⟩
      rw [h']
      funext ν
      simp only [basisVector, Pi.sub_apply, Pi.neg_apply, Pi.add_apply, Pi.smul_apply,
        Pi.single_apply, smul_eq_mul]
      split_ifs <;> ring
theorem induction_of_fix_zero (ha : a ≠ 0) (G : LatticeSymmetry a → Prop)
    (hcomp : ∀ r s, G r → G s → G (r.comp s)) (hid : G (shift 0))
    (hrefl : ∀ (Q : NormalHyperplane) (hQ : Q.IsLatticeMirror a), G (reflectSymmetry hQ))
    (S : Finset Direction) :
    ∀ r : LatticeSymmetry a, r.toFun 0 = 0 →
      (∀ μ, μ ∉ S → r.toFun (Pi.single μ a) = Pi.single μ a) → G r := by
  induction S using Finset.induction_on with
  | empty =>
    intro r h0 hfix
    have hr : r = shift 0 := by
      refine symmetry_ext (funext fun x => funext fun μ => ?_)
      have h := dotProduct_map_of_fix_zero h0 x (Pi.single μ a)
      rw [hfix μ (by simp), dotProduct_single, dotProduct_single] at h
      simpa [shift] using mul_right_cancel₀ ha h
    rw [hr]
    exact hid
  | insert μ S hμ ih =>
    intro r h0 hfix
    by_cases hw : r.toFun (Pi.single μ a) = Pi.single μ a
    · refine ih r h0 fun j hj => ?_
      by_cases hjμ : j = μ
      · rw [hjμ]
        exact hw
      · exact hfix j (by simp [hjμ, hj])
    obtain ⟨Q, t, hQ0, huw⟩ := exists_normal_of_moves_basis h0 μ hw
    have hQ : Q.IsLatticeMirror a := isLatticeMirror_of_level_eq_zero Q hQ0
    have hne : (Pi.single μ a : Point) ≠ r.toFun (Pi.single μ a) := fun h => hw h.symm
    have hlen := dotProduct_map_of_fix_zero h0 (Pi.single μ a) (Pi.single μ a)
    have hsend : Q.reflect (r.toFun (Pi.single μ a)) = Pi.single μ a :=
      reflect_of_sub_eq_smul Q hQ0 huw hne hlen.symm
    have ht : t ≠ 0 := by
      rintro rfl
      rw [zero_smul] at huw
      exact hne (sub_eq_zero.mp huw)
    have hnn : Q.normal ⬝ᵥ Q.normal ≠ 0 := by
      intro h
      rw [dotProduct_self_eq_zero] at h
      rw [h, smul_zero] at huw
      exact hne (sub_eq_zero.mp huw)
    have hinv : ∀ x, Q.reflect (Q.reflect x) = x := fun x => by
      rw [Q.reflect_eq_hyperplaneReflect]
      exact InfiniteLattice.hyperplaneReflect_hyperplaneReflect hnn _ x
    have hfixes : ∀ j, j ∉ insert μ S →
        Q.reflect (Pi.single j a) = (Pi.single j a : Point) := fun j hj => by
      have hrj := hfix j hj
      have hd := dotProduct_map_of_fix_zero h0 (Pi.single μ a) (Pi.single j a)
      rw [hrj] at hd
      refine reflect_of_orthogonal Q hQ0 ?_
      have h1 : ((Pi.single μ a : Point) - r.toFun (Pi.single μ a)) ⬝ᵥ (Pi.single j a : Point) = 0 := by
        rw [sub_dotProduct, hd, sub_self]
      rw [huw, smul_dotProduct, smul_eq_mul] at h1
      exact (mul_eq_zero.mp h1).resolve_left ht
    have hkey : G ((reflectSymmetry hQ).comp r) := by
      refine ih _ ?_ fun j hj => ?_
      · change Q.reflect (r.toFun 0) = 0
        rw [h0]
        exact reflect_of_orthogonal Q hQ0 (dotProduct_zero _)
      · change Q.reflect (r.toFun (Pi.single j a)) = Pi.single j a
        by_cases hjμ : j = μ
        · rw [hjμ]
          exact hsend
        · have hj' : j ∉ insert μ S := by simp [hjμ, hj]
          rw [hfix j hj']
          exact hfixes j hj'
    have hr : r = (reflectSymmetry hQ).comp ((reflectSymmetry hQ).comp r) :=
      symmetry_ext (funext fun x => (hinv (r.toFun x)).symm)
    rw [hr]
    exact hcomp _ _ (hrefl Q hQ) hkey
theorem induction_on_generators (ha : a ≠ 0) (G : LatticeSymmetry a → Prop)
    (hcomp : ∀ r s, G r → G s → G (r.comp s)) (htrans : ∀ v, G (shift v))
    (hrefl : ∀ (Q : NormalHyperplane) (hQ : Q.IsLatticeMirror a), G (reflectSymmetry hQ))
    (r : LatticeSymmetry a) : G r := by
  let v : LatticePoint a := r.pointMap 0
  have hv : (v : AmbientSpace) = r.toFun 0 := rfl
  have h1 : G ((shift (-v)).comp r) := by
    refine induction_of_fix_zero ha G hcomp (htrans 0) hrefl Finset.univ _ ?_ fun μ hμ =>
      absurd (Finset.mem_univ μ) hμ
    change r.toFun 0 + -(v : AmbientSpace) = 0
    rw [hv]
    abel
  have hr : r = (shift v).comp ((shift (-v)).comp r) := by
    refine symmetry_ext (funext fun x => ?_)
    change r.toFun x = r.toFun x + -(v : AmbientSpace) + (v : AmbientSpace)
    abel
  rw [hr]
  exact hcomp _ _ (htrans v) h1
theorem exists_perm_of_ne {m l m' l' : Direction} (h : m ≠ l) (h' : m' ≠ l') :
    ∃ w : Equiv.Perm Direction, w m' = m ∧ w l' = l := by
  refine ⟨Equiv.swap (Equiv.swap m' m l') l * Equiv.swap m' m, ?_, ?_⟩
  · rw [Equiv.Perm.mul_apply, Equiv.swap_apply_left]
    refine Equiv.swap_apply_of_ne_of_ne (fun hc => h' ?_) h
    apply (Equiv.swap m' m).injective
    rw [Equiv.swap_apply_left]
    exact hc
  · rw [Equiv.Perm.mul_apply, Equiv.swap_apply_left]
def permuteShift (w : Equiv.Perm Direction) (x x' : LatticePoint a) : LatticeSymmetry a where
  toFun z := fun κ => z (w.symm κ) - (x' : AmbientSpace) (w.symm κ) + (x : AmbientSpace) κ
  preservesDist z y := by
    unfold TorusMetric.euclidNormVec
    congr 1
    simp only [Pi.sub_apply, add_sub_add_right_eq_sub, sub_sub_sub_cancel_right]
    exact Equiv.sum_comp w.symm fun κ => (z κ - y κ) ^ 2
  image_eq := by
    obtain ⟨n', hn'⟩ := x'.2
    obtain ⟨m, hm⟩ := x.2
    ext y
    constructor
    · rintro ⟨z, ⟨n, hn⟩, rfl⟩
      refine ⟨fun κ => n (w.symm κ) - n' (w.symm κ) + m κ, fun κ => ?_⟩
      simp only [hn, hn', hm]
      push_cast
      ring
    · rintro ⟨n, hn⟩
      refine ⟨fun κ => y (w κ) - (x : AmbientSpace) (w κ) + (x' : AmbientSpace) κ,
        ⟨fun κ => n (w κ) - m (w κ) + n' κ, fun κ => ?_⟩, ?_⟩
      · simp only [hn, hn', hm]
        push_cast
        ring
      · funext κ
        simp
theorem permuteShift_pointMap_corner (w : Equiv.Perm Direction) (x x' : LatticePoint a) :
    (permuteShift w x x').pointMap x' = x := by
  refine Subtype.ext (funext fun κ => ?_)
  change (x' : AmbientSpace) (w.symm κ) - (x' : AmbientSpace) (w.symm κ) + (x : AmbientSpace) κ =
    (x : AmbientSpace) κ
  ring
theorem permuteShift_pointMap_add_axisStep (w : Equiv.Perm Direction) (x x' y : LatticePoint a)
    (μ : Direction) :
    (permuteShift w x x').pointMap (y + axisStep a μ) =
      (permuteShift w x x').pointMap y + axisStep a (w μ) := by
  refine Subtype.ext (funext fun κ => ?_)
  change (y : AmbientSpace) (w.symm κ) + (Pi.single μ a : AmbientSpace) (w.symm κ) -
      (x' : AmbientSpace) (w.symm κ) + (x : AmbientSpace) κ =
    (y : AmbientSpace) (w.symm κ) - (x' : AmbientSpace) (w.symm κ) + (x : AmbientSpace) κ +
      (Pi.single (w μ) a : AmbientSpace) κ
  have h : (Pi.single μ a : AmbientSpace) (w.symm κ) = (Pi.single (w μ) a : AmbientSpace) κ := by
    simp only [Pi.single_apply, Equiv.symm_apply_eq]
  rw [h]
  ring
theorem permuteShift_linkMap_forwardFrom (w : Equiv.Perm Direction) (x x' y : LatticePoint a)
    (μ : Direction) :
    (permuteShift w x x').linkMap (Link.forwardFrom y μ) =
      Link.forwardFrom ((permuteShift w x x').pointMap y) (w μ) :=
  Link.ext rfl (permuteShift_pointMap_add_axisStep w x x' y μ)
theorem faceEnergy_pullbackField_permuteShift (w : Equiv.Perm Direction)
    (p p' : ElementaryPlaquette a) (h1 : w p'.lowAxis = p.lowAxis) (h2 : w p'.highAxis = p.highAxis)
    (U : GaugeField a) :
    faceEnergy ((permuteShift w p.corner p'.corner).pullbackField U) p' = faceEnergy U p := by
  have h : faceHolonomy ((permuteShift w p.corner p'.corner).pullbackField U) p' =
      faceHolonomy U p := by
    change U ((permuteShift w p.corner p'.corner).linkMap _) *
        U ((permuteShift w p.corner p'.corner).linkMap _) *
        (U ((permuteShift w p.corner p'.corner).linkMap _))⁻¹ *
        (U ((permuteShift w p.corner p'.corner).linkMap _))⁻¹ = _
    simp only [permuteShift_linkMap_forwardFrom, permuteShift_pointMap_add_axisStep,
      permuteShift_pointMap_corner, h1, h2]
    rfl
  unfold faceEnergy
  rw [h]
theorem continuous_faceEnergy (p : ElementaryPlaquette a) :
    Continuous fun U : GaugeField a => faceEnergy U p := by
  have hb : ∀ b : Link a, Continuous fun U : GaugeField a => U b := fun b =>
    (continuous_apply b).comp
      (continuous_subtype_val
        (p := fun U : Link a → Matrices.ComplexMatrix2.specialUnitary =>
          ∀ b, U b.opposite = (U b)⁻¹))
  have hv : Continuous fun U : GaugeField a => faceHolonomy U p := by
    unfold faceHolonomy
    exact (((hb _).mul (hb _)).mul (hb _).inv).mul (hb _).inv
  unfold faceEnergy
  have ht : Continuous fun U : GaugeField a =>
      Matrices.ComplexMatrix2.fullTrace (faceHolonomy U p : Matrices.ComplexMatrix2) :=
    (continuous_subtype_val.comp hv).matrix_trace
  exact continuous_const.sub (continuous_const.mul (Complex.continuous_re.comp ht))
theorem abs_faceEnergy_le (U : GaugeField a) (p : ElementaryPlaquette a) :
    |faceEnergy U p| ≤ 2 := by
  have hu : (faceHolonomy U p : Matrices.ComplexMatrix2) ∈ Matrix.unitaryGroup (Fin 2) ℂ :=
    (Matrix.mem_specialUnitaryGroup_iff.mp (faceHolonomy U p).2).1
  have hn : ‖Matrices.ComplexMatrix2.fullTrace (faceHolonomy U p : Matrices.ComplexMatrix2)‖ ≤ 2 := by
    have h0 := entry_norm_bound_of_unitary hu 0 0
    have h1 := entry_norm_bound_of_unitary hu 1 1
    have ht : Matrices.ComplexMatrix2.fullTrace (faceHolonomy U p : Matrices.ComplexMatrix2) =
        (faceHolonomy U p : Matrices.ComplexMatrix2) 0 0 +
          (faceHolonomy U p : Matrices.ComplexMatrix2) 1 1 := by
      simp [Matrices.ComplexMatrix2.fullTrace, Matrix.trace, Fin.sum_univ_two]
    rw [ht]
    exact (norm_add_le _ _).trans (by linarith)
  have hre := Complex.abs_re_le_norm
    (Matrices.ComplexMatrix2.fullTrace (faceHolonomy U p : Matrices.ComplexMatrix2))
  unfold faceEnergy
  rw [abs_le]
  have := abs_le.mp (hre.trans hn)
  constructor <;> linarith [this.1, this.2]
theorem isBoundedObservable_faceEnergy (p : ElementaryPlaquette a) :
    IsBoundedObservable fun U : GaugeField a => ((faceEnergy U p : ℝ) : ℂ) :=
  ⟨(Complex.continuous_ofReal.comp (continuous_faceEnergy p)).measurable,
    2, fun U => by simpa using abs_faceEnergy_le U p⟩
end SymmetryGeneration
open SymmetryGeneration in
theorem latticeSymmetryInvarianceAndEqualFaceMeans_holds
    (hInvariance : ReflectionPositivityGivesReflectionInvariance.Statement)
    (hAction : InfiniteLattice.SymmetryActionOnObservables) :
    LatticeSymmetryInvarianceAndEqualFaceMeans := by
  intro a ν _ hT hRP
  have hall : ∀ r : InfiniteLattice.LatticeSymmetry (a : ℝ), InfiniteLattice.IsSymmetricUnder ν r :=
    induction_on_generators a.2.ne' (fun r => InfiniteLattice.IsSymmetricUnder ν r)
      (fun r s hr hs => ((hAction a).2.2.2.2.2.2.2.2.2.2 ν inferInstance).1 r s hr hs) hT
      (fun Q hQ => (((hInvariance a Q hQ).2 ν hT (hRP Q hQ))).1)
  refine ⟨hall, fun p p' => ?_⟩
  obtain ⟨w, h1, h2⟩ := exists_perm_of_ne (m := p.lowAxis) (l := p.highAxis)
    (m' := p'.lowAxis) (l' := p'.highAxis) p.lowAxis_lt_highAxis.ne p'.lowAxis_lt_highAxis.ne
  have h := hall (permuteShift w p.corner p'.corner) _ (isBoundedObservable_faceEnergy p')
  have h' : (fun U : InfiniteLattice.GaugeField (a : ℝ) =>
      (permuteShift w p.corner p'.corner).actOn
        (fun U : InfiniteLattice.GaugeField (a : ℝ) =>
          ((InfiniteLattice.faceEnergy U p' : ℝ) : ℂ)) U) =
      fun U : InfiniteLattice.GaugeField (a : ℝ) =>
        ((InfiniteLattice.faceEnergy U p : ℝ) : ℂ) := by
    funext U
    change ((InfiniteLattice.faceEnergy
      ((permuteShift w p.corner p'.corner).pullbackField U) p' : ℝ) : ℂ) = _
    rw [faceEnergy_pullbackField_permuteShift w p p' h1 h2]
  have hc : ∀ q : InfiniteLattice.ElementaryPlaquette (a : ℝ),
      ∫ U : InfiniteLattice.GaugeField (a : ℝ), ((InfiniteLattice.faceEnergy U q : ℝ) : ℂ) ∂ν =
        ((∫ U : InfiniteLattice.GaugeField (a : ℝ), InfiniteLattice.faceEnergy U q ∂ν : ℝ) : ℂ) :=
    fun q => integral_complex_ofReal
      (f := fun U : InfiniteLattice.GaugeField (a : ℝ) => InfiniteLattice.faceEnergy U q)
  rw [h', hc, hc] at h
  exact Complex.ofReal_injective h
end LatticeConventions
end YangMills.Construction
end
