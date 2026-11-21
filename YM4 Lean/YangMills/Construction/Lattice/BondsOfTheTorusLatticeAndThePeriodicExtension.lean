import YangMills.Construction.InfiniteLattice.PositiveLinksAndCylinderFunctions
import YangMills.Construction.Lattice.EuclideanIsometries
import YangMills.Construction.Lattice.MatrixValuedFormOperators
import YangMills.Construction.Lattice.ObservablesAndTestNorms
import YangMills.Construction.Lattice.ToriLatticesNormsAndFunctionsOfFinitelyManyVariables
import Mathlib
set_option autoImplicit false
open MeasureTheory Set
noncomputable section
namespace YangMills.Construction
namespace PeriodicLattice
variable {L m : ℕ} {j : ℤ}
def pointsPerAxis (L m K : ℕ) : ℝ := torusSide L m / meshSize L (K : ℤ)
theorem pointsPerAxis_eq (L m K : ℕ) :
    pointsPerAxis L m K = 2 * (L : ℝ) ^ (m + K) := by
  simp only [pointsPerAxis, torusSide, meshSize, zpow_neg, zpow_natCast, div_inv_eq_mul, pow_add]
  ring
def torusProjHom (L m : ℕ) : (Fin 4 → ℝ) →+ FourTorus L m where
  toFun := TorusMetric.torusProj (torusSide L m)
  map_zero' := by
    funext μ
    simp [TorusMetric.torusProj]
  map_add' x y := by
    funext μ
    simp [TorusMetric.torusProj]
theorem sublattice_eq_map_latticeSubgroup (L m : ℕ) (j : ℤ) :
    sublattice L m j = (InfiniteLattice.latticeSubgroup (meshSize L j)).map (torusProjHom L m) := by
  ext z
  constructor
  · rintro ⟨n, hn⟩
    exact ⟨fun μ => (n μ : ℝ) * meshSize L j, ⟨n, fun _ => rfl⟩, funext fun μ => (hn μ).symm⟩
  · rintro ⟨x, ⟨n, hn⟩, rfl⟩
    exact ⟨n, fun μ => by simp [torusProjHom, TorusMetric.torusProj, hn]⟩
def forwardBonds (L m : ℕ) (j : ℤ) : Set (Bond L m j) :=
  {b | ∃ (z : Site L m j) (κ : Fin 4), b = Bond.forwardFrom z κ}
theorem mem_positiveBonds_iff {b : Bond L m j} :
    b ∈ forwardBonds L m j ↔ b.IsPositivelyOriented := by
  constructor
  · rintro ⟨x, κ, rfl⟩
    exact ⟨κ, by simp [Bond.forwardFrom]⟩
  · rintro ⟨κ, h⟩
    exact ⟨b.source, κ, Bond.ext rfl (by
      change b.target = b.source + unitStep L m j κ
      rw [← h]
      abel)⟩
theorem xor_mem_positiveBonds (hL : 2 ≤ L) (hj : -(m : ℤ) < j) (b : Bond L m j) :
    Xor (b ∈ forwardBonds L m j)
      (b.opposite ∈ forwardBonds L m j) := by
  simpa only [mem_positiveBonds_iff] using MatrixValued.xor_isPositivelyOriented_opposite hL hj b
theorem opposite_notMem_positiveBonds (hL : 2 ≤ L) (hj : -(m : ℤ) < j)
    {b : Bond L m j} (hb : b ∈ forwardBonds L m j) :
    b.opposite ∉ forwardBonds L m j := by
  rcases xor_mem_positiveBonds hL hj b with h | h
  · exact h.2
  · exact absurd hb h.2
theorem torusEuclidDist_torusProj (L m : ℕ) (x y : Fin 4 → ℝ) :
    torusEuclidDist L m (TorusMetric.torusProj (torusSide L m) x)
        (TorusMetric.torusProj (torusSide L m) y) =
      sInf (range fun k : Fin 4 → ℤ =>
        TorusMetric.euclidNormVec (x - y - TestFunctions.latticeTranslate (torusSide L m) k)) := by
  have hsub : TorusMetric.torusProj (torusSide L m) x - TorusMetric.torusProj (torusSide L m) y =
      TorusMetric.torusProj (torusSide L m) (x - y) := by
    funext μ
    simp [TorusMetric.torusProj]
  unfold torusEuclidDist TorusMetric.torusEuclidNorm
  rw [hsub]
  congr 1
  ext r
  constructor
  · rintro ⟨v, hv, rfl⟩
    obtain ⟨k, rfl⟩ := TestFunctions.exists_latticeTranslate_of_torusProj_eq hv
    refine ⟨-k, ?_⟩
    have hk : TestFunctions.latticeTranslate (torusSide L m) (-k) =
        -TestFunctions.latticeTranslate (torusSide L m) k := by
      funext μ
      simp [TestFunctions.latticeTranslate]
    simp only [hk, sub_neg_eq_add]
  · rintro ⟨k, rfl⟩
    refine ⟨x - y - TestFunctions.latticeTranslate (torusSide L m) k, ?_, rfl⟩
    have hk : x - y = (x - y - TestFunctions.latticeTranslate (torusSide L m) k) +
        TestFunctions.latticeTranslate (torusSide L m) k := by abel
    change TorusMetric.torusProj (torusSide L m) _ = TorusMetric.torusProj (torusSide L m) (x - y)
    conv_rhs => rw [hk]
    exact (TestFunctions.torusProj_add_latticeTranslate _ _ _).symm
namespace CompactGaugeField
theorem linkValue_opposite (U : CompactGaugeField L m j) (b : Bond L m j) :
    U.linkValue b.opposite = (U.linkValue b)⁻¹ :=
  Subtype.ext (by
    rw [InfiniteLattice.specialUnitary_coe_inv]
    exact U.2.2 b (mem_univ b))
def ofLinkValues (f : Bond L m j → Matrices.ComplexMatrix2.specialUnitary)
    (hf : ∀ b, f b.opposite = (f b)⁻¹) : CompactGaugeField L m j :=
  ⟨fun b => f b, fun b _ => (f b).2, fun b _ => by
    change ((f b.opposite : Matrices.ComplexMatrix2.specialUnitary) : Matrices.ComplexMatrix2) = _
    rw [hf, InfiniteLattice.specialUnitary_coe_inv]⟩
theorem linkValue_ofLinkValues (f : Bond L m j → Matrices.ComplexMatrix2.specialUnitary)
    (hf : ∀ b, f b.opposite = (f b)⁻¹) (b : Bond L m j) : (ofLinkValues f hf).linkValue b = f b :=
  rfl
def identity (L m : ℕ) (j : ℤ) : CompactGaugeField L m j :=
  ofLinkValues (fun _ => 1) fun _ => by simp
def restrictTo (U : CompactGaugeField L m j) (S : Set (Bond L m j)) :
    InfiniteLattice.LinkVariables S :=
  fun b => U.linkValue b
def glue (hL : 2 ≤ L) (hj : -(m : ℤ) < j) {S : Set (Bond L m j)}
    (hS : S ⊆ forwardBonds L m j) (V : InfiniteLattice.LinkVariables S)
    (ω : CompactGaugeField L m j) : CompactGaugeField L m j :=
  open Classical in
  ofLinkValues (fun b => if h : b ∈ S then V ⟨b, h⟩ else
      if h' : b.opposite ∈ S then (V ⟨b.opposite, h'⟩)⁻¹ else ω.linkValue b) fun b => by
    by_cases h : b ∈ S
    · have h' : b.opposite ∉ S := fun h' =>
        opposite_notMem_positiveBonds hL hj (hS h) (hS h')
      simp only [h, h', dite_true, dite_false]
      exact dif_pos h
    · by_cases h' : b.opposite ∈ S
      · simp only [h, h', dite_true, dite_false, inv_inv]
      · have h'' : b.opposite.opposite ∉ S := h
        simp only [h, h', h'', dite_false]
        exact ω.linkValue_opposite b
theorem glue_of_mem (hL : 2 ≤ L) (hj : -(m : ℤ) < j) {S : Set (Bond L m j)}
    (hS : S ⊆ forwardBonds L m j) (V : InfiniteLattice.LinkVariables S)
    (ω : CompactGaugeField L m j) (b : S) :
    (glue hL hj hS V ω).linkValue b = V b :=
  dif_pos b.2
theorem glue_of_notMem (hL : 2 ≤ L) (hj : -(m : ℤ) < j) {S : Set (Bond L m j)}
    (hS : S ⊆ forwardBonds L m j) (V : InfiniteLattice.LinkVariables S)
    (ω : CompactGaugeField L m j) {b : Bond L m j}
    (hb : b ∈ forwardBonds L m j \ S) :
    (glue hL hj hS V ω).linkValue b = ω.linkValue b := by
  have h' : b.opposite ∉ S := fun h' =>
    opposite_notMem_positiveBonds hL hj hb.1 (hS h')
  classical
  change (if h : b ∈ S then V ⟨b, h⟩ else
    if h' : b.opposite ∈ S then (V ⟨b.opposite, h'⟩)⁻¹ else ω.linkValue b) = ω.linkValue b
  rw [dif_neg hb.2, dif_neg h']
theorem eq_glue (hL : 2 ≤ L) (hj : -(m : ℤ) < j) {S : Set (Bond L m j)}
    (hS : S ⊆ forwardBonds L m j) (V : InfiniteLattice.LinkVariables S)
    (ω U : CompactGaugeField L m j) (h₁ : ∀ b : S, U.linkValue b = V b)
    (h₂ : ∀ b ∈ forwardBonds L m j \ S, U.linkValue b = ω.linkValue b) :
    U = glue hL hj hS V ω := by
  have key : ∀ b ∈ forwardBonds L m j,
      U.linkValue b = (glue hL hj hS V ω).linkValue b := fun b hb => by
    by_cases h : b ∈ S
    · rw [h₁ ⟨b, h⟩]
      exact (glue_of_mem hL hj hS V ω ⟨b, h⟩).symm
    · rw [h₂ b ⟨hb, h⟩, glue_of_notMem hL hj hS V ω ⟨hb, h⟩]
  have all : ∀ b, U.linkValue b = (glue hL hj hS V ω).linkValue b := fun b => by
    rcases xor_mem_positiveBonds hL hj b with h | h
    · exact key b h.1
    · have hU := U.linkValue_opposite b.opposite
      have hW := (glue hL hj hS V ω).linkValue_opposite b.opposite
      have hb : b.opposite.opposite = b := rfl
      rw [hb] at hU hW
      rw [hU, hW, key _ h.1]
  exact Subtype.ext (funext fun b => congrArg Subtype.val (all b))
end CompactGaugeField
def DependsOnlyOn {E : Type*} (S : Set (Bond L m j)) (F : CompactGaugeField L m j → E) :
    Prop :=
  ∀ U U' : CompactGaugeField L m j, U.restrictTo S = U'.restrictTo S → F U = F U'
theorem isClosed_compactGaugeFields (L m : ℕ) (j : ℤ) :
    IsClosed (compactGaugeFields L m j) := by
  have hG : IsClosed (compactGaugeGroup : Set Matrices.ComplexMatrix2) := by
    have h := isCompact_iff_compactSpace.mpr
      (inferInstance : CompactSpace Matrices.ComplexMatrix2.specialUnitary)
    exact h.isClosed
  have hinv : ∀ A ∈ compactGaugeGroup, A⁻¹ = star A := fun A hA =>
    Matrix.inv_eq_right_inv (Matrix.mem_unitaryGroup_iff.mp
      (Matrix.specialUnitaryGroup_le_unitaryGroup hA))
  have hset : compactGaugeFields L m j =
      ⋂ b : Bond L m j, {U | U b ∈ compactGaugeGroup} ∩ {U | U b.opposite = star (U b)} := by
    ext U
    simp only [compactGaugeFields, IsGaugeField, mem_ofPred_eq, mem_univ, forall_const,
      mem_iInter, mem_inter_iff]
    constructor
    · rintro ⟨h₁, h₂⟩ b
      exact ⟨h₁ b, (h₂ b).trans (hinv _ (h₁ b))⟩
    · intro h
      exact ⟨fun b => (h b).1, fun b => (h b).2.trans (hinv _ (h b).1).symm⟩
  rw [hset]
  exact isClosed_iInter fun b =>
    (hG.preimage (continuous_apply b)).inter
      (isClosed_eq (continuous_apply _) (continuous_star.comp (continuous_apply b)))
end PeriodicLattice
namespace InfiniteLattice
open PeriodicLattice (CompactGaugeField)
variable {L m : ℕ} {j : ℤ}
theorem projectLink_opposite (b : Link (PeriodicLattice.meshSize L j)) :
    projectLink L m j b.opposite = (projectLink L m j b).opposite := rfl
def liftCompactField (U : CompactGaugeField L m j) : GaugeField (PeriodicLattice.meshSize L j) :=
  liftField L m j U.1
theorem liftField_of_mem {U : PeriodicLattice.Bond L m j → Matrices.ComplexMatrix2}
    (hU : U ∈ PeriodicLattice.compactGaugeFields L m j) :
    liftField L m j U =
      (⟨fun b => ⟨U (projectLink L m j b), hU.1 _ (mem_univ _)⟩, fun b => Subtype.ext (by
        rw [specialUnitary_coe_inv]
        exact hU.2 (projectLink L m j b) (mem_univ _))⟩ :
        GaugeField (PeriodicLattice.meshSize L j)) :=
  dif_pos hU
theorem liftField_of_notMem {U : PeriodicLattice.Bond L m j → Matrices.ComplexMatrix2}
    (hU : U ∉ PeriodicLattice.compactGaugeFields L m j) :
    liftField L m j U = trivialField (PeriodicLattice.meshSize L j) :=
  dif_neg hU
theorem liftField_apply_of_mem {U : PeriodicLattice.Bond L m j → Matrices.ComplexMatrix2}
    (hU : U ∈ PeriodicLattice.compactGaugeFields L m j) (b : Link (PeriodicLattice.meshSize L j)) :
    (liftField L m j U b : Matrices.ComplexMatrix2) = U (projectLink L m j b) := by
  rw [liftField_of_mem hU]
theorem liftCompactField_apply (U : CompactGaugeField L m j)
    (b : Link (PeriodicLattice.meshSize L j)) :
    liftCompactField U b = U.linkValue (projectLink L m j b) :=
  Subtype.ext (liftField_apply_of_mem U.2 b)
theorem continuous_liftCompactField :
    Continuous (liftCompactField : CompactGaugeField L m j → _) := by
  have h : (liftCompactField : CompactGaugeField L m j → _) = fun U =>
      ⟨fun b => U.linkValue (projectLink L m j b),
        fun b => U.linkValue_opposite (projectLink L m j b)⟩ := by
    funext U
    exact Subtype.ext (funext fun b => liftCompactField_apply U b)
  rw [h]
  exact Continuous.subtype_mk (continuous_pi fun b =>
    continuous_iInf_dom continuous_induced_dom) _
theorem measurable_liftField (L m : ℕ) (j : ℤ) : Measurable (liftField L m j) := by
  classical
  have : SecondCountableTopology Matrices.ComplexMatrix2 :=
    inferInstanceAs (SecondCountableTopology (Fin 2 → Fin 2 → ℂ))
  have hR : MeasurableSet (PeriodicLattice.compactGaugeFields L m j) :=
    (PeriodicLattice.isClosed_compactGaugeFields L m j).measurableSet
  have hf : Measurable fun U : PeriodicLattice.compactGaugeFields L m j =>
      liftField L m j U.1 := by
    have hc : Continuous fun U : PeriodicLattice.compactGaugeFields L m j =>
        liftField L m j U.1 := by
      have h : (fun U : PeriodicLattice.compactGaugeFields L m j => liftField L m j U.1) =
          fun U => ⟨fun b => ⟨U.1 (projectLink L m j b), U.2.1 _ (mem_univ _)⟩, fun b =>
            Subtype.ext (by
              rw [specialUnitary_coe_inv]
              exact U.2.2 (projectLink L m j b) (mem_univ _))⟩ :=
        funext fun U => liftField_of_mem U.2
      rw [h]
      exact Continuous.subtype_mk (continuous_pi fun b => Continuous.subtype_mk
        ((continuous_apply _).comp continuous_subtype_val) _) _
    exact hc.measurable
  have hg : Measurable fun _ : ((PeriodicLattice.compactGaugeFields L m j)ᶜ : Set _) =>
      trivialField (PeriodicLattice.meshSize L j) :=
    measurable_const
  have h := Measurable.dite hf hg hR
  convert h using 1
  funext U
  by_cases hU : U ∈ PeriodicLattice.compactGaugeFields L m j
  · simp only [hU, dite_true]
  · simp only [hU, dite_false]
    exact liftField_of_notMem hU
theorem liftedWilsonMeasure_apply (L m K : ℕ) (β : ℝ)
    {E : Set (GaugeField (PeriodicLattice.meshSize L (K : ℤ)))} (hE : MeasurableSet E) :
    liftedWilsonMeasure L m K β E =
      PeriodicLattice.wilsonGibbsMeasure L m K β (liftField L m (K : ℤ) ⁻¹' E) :=
  Measure.map_apply (measurable_liftField L m (K : ℤ)) hE
end InfiniteLattice
end YangMills.Construction
