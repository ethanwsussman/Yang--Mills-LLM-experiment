import YangMills.Construction.InfiniteLattice.PositiveLinksAndCylinderFunctions
import Mathlib
set_option autoImplicit false
open MeasureTheory Set
noncomputable section
namespace YangMills.Construction
namespace InfiniteLattice
namespace WilsonOperator
variable {a : ℝ}
abbrev cutoffLinks (L K : ℕ) : Set (Link (PeriodicLattice.meshSize L (K : ℤ))) :=
  positiveLinkSet (PeriodicLattice.meshSize L (K : ℤ))
theorem gaugeField_apply_opposite (U : GaugeField a) (e : Link a) :
    U e = (U e.opposite)⁻¹ := by
  have h := U.2 e.opposite
  rw [Link.opposite_opposite] at h
  exact h
def gaugeFieldHomeomorph (ha : 0 < a) :
    GaugeField a ≃ₜ LinkVariables (positiveLinkSet a) where
  toFun U := restrictField U (positiveLinkSet a)
  invFun v := gluedField ha subset_rfl v (trivialField a)
  left_inv U := (eq_gluedField ha subset_rfl _ _ U (fun _ => rfl)
    fun _ he => absurd he.1 he.2).symm
  right_inv v := funext fun e => gluedField_apply_of_mem ha subset_rfl v _ e
  continuous_toFun := continuous_pi fun e =>
    (continuous_apply (e : Link a)).comp
      (continuous_subtype_val
        (p := fun U : Link a → Matrices.ComplexMatrix2.specialUnitary =>
          ∀ e, U e.opposite = (U e)⁻¹))
  continuous_invFun := by
    have key : Continuous fun v : LinkVariables (positiveLinkSet a) =>
        ((gluedField ha subset_rfl v (trivialField a) : GaugeField a) :
          Link a → Matrices.ComplexMatrix2.specialUnitary) := by
      refine continuous_pi fun e => ?_
      rcases mem_positiveLinks_or_opposite_mem e with h | h
      · have hv : ∀ v : LinkVariables (positiveLinkSet a),
            gluedField ha subset_rfl v (trivialField a) e = v ⟨e, h⟩ :=
          fun v => gluedField_apply_of_mem ha subset_rfl v _ ⟨e, h⟩
        simp only [hv]
        exact continuous_apply _
      · have hv : ∀ v : LinkVariables (positiveLinkSet a),
            gluedField ha subset_rfl v (trivialField a) e =
              (v ⟨e.opposite, h⟩)⁻¹ := fun v => by
          rw [gaugeField_apply_opposite,
            gluedField_apply_of_mem ha subset_rfl v _ ⟨e.opposite, h⟩]
        simp only [hv]
        exact (continuous_apply _).inv
    exact Continuous.subtype_mk key _
@[reducible] def linkSigmaAlgebra (S : Set (Link a)) : MeasurableSpace (GaugeField a) :=
  linkSigma S
theorem secondCountable_specialUnitary :
    SecondCountableTopology Matrices.ComplexMatrix2.specialUnitary :=
  have : SecondCountableTopology Matrices.ComplexMatrix2 :=
    inferInstanceAs (SecondCountableTopology (Fin 2 → Fin 2 → ℂ))
  TopologicalSpace.Subtype.secondCountableTopology _
theorem countable_link : Countable (Link a) :=
  have : Countable (LatticePoint a) := Function.Surjective.countable
    (f := fun n : Fin 4 → ℤ => (⟨fun μ => (n μ : ℝ) * a, n, fun _ => rfl⟩ : LatticePoint a))
    fun x => by
      obtain ⟨n, hn⟩ := x.2
      exact ⟨n, Subtype.ext (funext fun μ => (hn μ).symm)⟩
  Function.Injective.countable (f := fun e : Link a => (e.initial, e.terminal)) fun _ _ h =>
    Link.ext (congrArg Prod.fst h) (congrArg Prod.snd h)
theorem borel_eq_linkSigmaAlgebra (ha : 0 < a) :
    (inferInstance : MeasurableSpace (GaugeField a)) =
      linkSigmaAlgebra (positiveLinkSet a) := by
  have := secondCountable_specialUnitary
  have : Countable (Link a) := countable_link
  have h := (gaugeFieldHomeomorph ha).toMeasurableEquiv.measurableEmbedding.comap_eq
  rw [← h]
  simp only [MeasurableSpace.pi, MeasurableSpace.comap_iSup, MeasurableSpace.comap_comp]
  exact iSup_subtype' (f := fun (e : Link a) (_ : e ∈ positiveLinkSet a) =>
    MeasurableSpace.comap (fun U : GaugeField a => U e) inferInstance) |>.symm
def edgeList (p : ElementaryPlaquette a) : List (Link a) :=
  [Link.forwardFrom p.corner p.lowAxis,
    Link.forwardFrom (p.corner + axisStep a p.lowAxis) p.highAxis,
    Link.forwardFrom (p.corner + axisStep a p.highAxis) p.lowAxis,
    Link.forwardFrom p.corner p.highAxis]
def periodicEdgeList {L m : ℕ} {j : ℤ} (p : PeriodicLattice.Plaquette L m j) :
    List (PeriodicLattice.Bond L m j) :=
  [PeriodicLattice.Bond.forwardFrom p.origin p.firstAxis,
    PeriodicLattice.Bond.forwardFrom (p.origin + PeriodicLattice.unitStep L m j p.firstAxis)
      p.secondAxis,
    PeriodicLattice.Bond.forwardFrom (p.origin + PeriodicLattice.unitStep L m j p.secondAxis)
      p.firstAxis,
    PeriodicLattice.Bond.forwardFrom p.origin p.secondAxis]
theorem mem_positiveLinks_of_mem_edgeList (p : ElementaryPlaquette a) {e : Link a}
    (he : e ∈ edgeList p) : e ∈ positiveLinkSet a := by
  simp only [edgeList, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl <;> exact ⟨_, _, rfl⟩
theorem faceHolonomy_congr {U U' : Link a → Matrices.ComplexMatrix2.specialUnitary}
    (p : ElementaryPlaquette a) (h : ∀ e ∈ edgeList p, U e = U' e) :
    faceHolonomy U p = faceHolonomy U' p := by
  simp only [edgeList, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
    forall_eq] at h
  obtain ⟨h₁, h₂, h₃, h₄⟩ := h
  simp only [faceHolonomy, h₁, h₂, h₃, h₄]
theorem faceEnergy_congr {U U' : Link a → Matrices.ComplexMatrix2.specialUnitary}
    (p : ElementaryPlaquette a) (h : ∀ e ∈ edgeList p, U e = U' e) :
    faceEnergy U p = faceEnergy U' p := by
  simp only [faceEnergy, faceHolonomy_congr p h]
theorem periodic_plaquetteHolonomy_congr {L m : ℕ} {j : ℤ}
    {U U' : PeriodicLattice.Bond L m j → Matrices.ComplexMatrix2}
    (hU : U ∈ PeriodicLattice.compactGaugeFields L m j)
    (hU' : U' ∈ PeriodicLattice.compactGaugeFields L m j) (p : PeriodicLattice.Plaquette L m j)
    (h : ∀ e ∈ periodicEdgeList p, U e = U' e) :
    PeriodicLattice.plaquetteHolonomy U p = PeriodicLattice.plaquetteHolonomy U' p := by
  simp only [periodicEdgeList, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
    forall_eq] at h
  obtain ⟨h₁, h₂, h₃, h₄⟩ := h
  simp only [PeriodicLattice.plaquetteHolonomy, PeriodicLattice.pathHolonomy,
    PeriodicLattice.Plaquette.boundaryBonds, List.map_cons, List.map_nil,
    hU.2 _ (mem_univ _), hU'.2 _ (mem_univ _), h₁, h₂, h₃, h₄]
theorem periodic_plaquetteEnergy_congr {L m : ℕ} {j : ℤ}
    {U U' : PeriodicLattice.Bond L m j → Matrices.ComplexMatrix2}
    (hU : U ∈ PeriodicLattice.compactGaugeFields L m j)
    (hU' : U' ∈ PeriodicLattice.compactGaugeFields L m j) (p : PeriodicLattice.Plaquette L m j)
    (h : ∀ e ∈ periodicEdgeList p, U e = U' e) :
    PeriodicLattice.plaquetteCost U p = PeriodicLattice.plaquetteCost U' p := by
  simp only [PeriodicLattice.plaquetteCost, periodic_plaquetteHolonomy_congr hU hU' p h]
theorem corner_of_mem_edgeList {p : ElementaryPlaquette a} {e : Link a} (he : e ∈ edgeList p) :
    p.corner = e.initial ∨ p.corner = e.initial - axisStep a p.lowAxis ∨
      p.corner = e.initial - axisStep a p.highAxis := by
  simp only [edgeList, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl
  · exact Or.inl rfl
  · exact Or.inr (Or.inl (add_sub_cancel_right _ _).symm)
  · exact Or.inr (Or.inr (add_sub_cancel_right _ _).symm)
  · exact Or.inl rfl
theorem facesTouching_finite (Λ : Finset (Link a)) : (facesTouching Λ).Finite := by
  have hfin : (⋃ e ∈ (Λ : Set (Link a)), ⋃ κ : Fin 4, ⋃ ν : Fin 4, ⋃ h : κ < ν,
      ({⟨e.initial, κ, ν, h⟩, ⟨e.initial - axisStep a κ, κ, ν, h⟩,
        ⟨e.initial - axisStep a ν, κ, ν, h⟩} : Set (ElementaryPlaquette a))).Finite :=
    Λ.finite_toSet.biUnion fun e _ => finite_iUnion fun κ => finite_iUnion fun ν =>
      finite_iUnion fun h => by simp
  refine hfin.subset ?_
  rintro ⟨z, κ, ν, h⟩ ⟨e, he, hΛ⟩
  simp only [mem_iUnion]
  refine ⟨e, hΛ, κ, ν, h, ?_⟩
  rcases corner_of_mem_edgeList he with q | q | q <;> simp only at q <;> subst q <;> simp
def touchingFaceCount (Λ : Finset (Link a)) : ℕ := (facesTouching Λ).ncard
def thickenedLinks (Λ : Finset (Link a)) : Set (Link a) :=
  (Λ : Set (Link a)) ∪ ⋃ p ∈ facesTouching Λ, {e | e ∈ edgeList p}
theorem thickenedLinks_finite (Λ : Finset (Link a)) : (thickenedLinks Λ).Finite :=
  Λ.finite_toSet.union ((facesTouching_finite Λ).biUnion fun p _ => (edgeList p).finite_toSet)
theorem thickenedLinks_subset {Λ : Finset (Link a)}
    (hΛ : (Λ : Set (Link a)) ⊆ positiveLinkSet a) :
    thickenedLinks Λ ⊆ positiveLinkSet a := by
  refine union_subset hΛ (iUnion₂_subset fun p _ => ?_)
  exact fun e he => mem_positiveLinks_of_mem_edgeList p he
def splice (ha : 0 < a) {Λ : Finset (Link a)} (hΛ : (Λ : Set (Link a)) ⊆ positiveLinkSet a)
    (V : Λ → Matrices.ComplexMatrix2.specialUnitary) (U : GaugeField a) : GaugeField a :=
  gluedField ha hΛ V U
def localWeight (β : ℝ) (Λ : Finset (Link a)) (U : GaugeField a) : ℝ :=
  Real.exp (-β * ∑ᶠ p ∈ facesTouching Λ, faceEnergy U p)
def localPartition (ha : 0 < a) (β : ℝ) {Λ : Finset (Link a)}
    (hΛ : (Λ : Set (Link a)) ⊆ positiveLinkSet a) (U : GaugeField a) : ℝ :=
  ∫ V, localWeight β Λ (splice ha hΛ V U) ∂Matrices.ComplexMatrix2.haarPi Λ
def kernelOperator (ha : 0 < a) (β : ℝ) {Λ : Finset (Link a)}
    (hΛ : (Λ : Set (Link a)) ⊆ positiveLinkSet a) (F : GaugeField a → ℂ)
    (U : GaugeField a) : ℂ :=
  (localPartition ha β hΛ U : ℂ)⁻¹ *
    ∫ V, F (splice ha hΛ V U) * (localWeight β Λ (splice ha hΛ V U) : ℂ)
      ∂Matrices.ComplexMatrix2.haarPi Λ
section Facts
variable (ha : 0 < a) {Λ : Finset (Link a)}
  (hΛ : (Λ : Set (Link a)) ⊆ positiveLinkSet a)
include ha hΛ
theorem splice_apply_of_mem (V : Λ → Matrices.ComplexMatrix2.specialUnitary) (U : GaugeField a)
    (e : Λ) : splice ha hΛ V U e = V e :=
  gluedField_apply_of_mem ha hΛ V U ⟨e.1, e.2⟩
theorem splice_apply_of_notMem (V : Λ → Matrices.ComplexMatrix2.specialUnitary)
    (U : GaugeField a) {e : Link a}
    (he : e ∈ positiveLinkSet a \ (Λ : Set (Link a))) : splice ha hΛ V U e = U e :=
  gluedField_apply_of_notMem ha hΛ V U he
theorem eq_splice (V : Λ → Matrices.ComplexMatrix2.specialUnitary) (U U' : GaugeField a)
    (h₁ : ∀ e : Λ, U' e = V e)
    (h₂ : ∀ e ∈ positiveLinkSet a \ (Λ : Set (Link a)), U' e = U e) :
    U' = splice ha hΛ V U :=
  eq_gluedField ha hΛ V U U' (fun e => h₁ ⟨e.1, e.2⟩) h₂
theorem splice_eq_patch (V : Λ → Matrices.ComplexMatrix2.specialUnitary) (U : GaugeField a)
    {e : Link a} (he : e ∈ positiveLinkSet a) : splice ha hΛ V U e = patch Λ V U e := by
  classical
  by_cases h : e ∈ Λ
  · rw [splice_apply_of_mem ha hΛ V U ⟨e, h⟩]
    simp only [patch, dif_pos h]
  · rw [splice_apply_of_notMem ha hΛ V U ⟨he, h⟩]
    simp only [patch, dif_neg h]
theorem localWeight_splice (β : ℝ) (V : Λ → Matrices.ComplexMatrix2.specialUnitary)
    (U : GaugeField a) :
    localWeight β Λ (splice ha hΛ V U) = boltzmannWeight β Λ U V := by
  have h : ∀ p : ElementaryPlaquette a, faceEnergy (splice ha hΛ V U) p =
      faceEnergy (patch Λ V U) p := fun p =>
    faceEnergy_congr p fun e he =>
      splice_eq_patch ha hΛ V U (mem_positiveLinks_of_mem_edgeList p he)
  simp only [localWeight, boltzmannWeight, h]
theorem localPartition_eq (β : ℝ) (U : GaugeField a) :
    localPartition ha β hΛ U = partitionFunction β Λ U := by
  unfold localPartition partitionFunction
  simp only [localWeight_splice ha hΛ]
omit ha hΛ in
theorem continuous_patch_apply (U : Link a → Matrices.ComplexMatrix2.specialUnitary)
    (e : Link a) :
    Continuous fun v : Λ → Matrices.ComplexMatrix2.specialUnitary => patch Λ v U e := by
  classical
  by_cases h : e ∈ Λ
  · simp only [patch, dif_pos h]
    exact continuous_apply _
  · simp only [patch, dif_neg h]
    exact continuous_const
omit ha hΛ in
theorem continuous_boltzmannWeight (β : ℝ) (U : GaugeField a) :
    Continuous (boltzmannWeight β Λ U) := by
  have hp : ∀ p : ElementaryPlaquette a,
      Continuous fun v : Λ → Matrices.ComplexMatrix2.specialUnitary =>
        faceEnergy (patch Λ v U) p := fun p => by
    have hv : Continuous fun v : Λ → Matrices.ComplexMatrix2.specialUnitary =>
        faceHolonomy (patch Λ v U) p := by
      unfold faceHolonomy
      exact (((continuous_patch_apply _ _).mul (continuous_patch_apply _ _)).mul
        (continuous_patch_apply _ _).inv).mul (continuous_patch_apply _ _).inv
    unfold faceEnergy
    have ht : Continuous fun v : Λ → Matrices.ComplexMatrix2.specialUnitary =>
        Matrices.ComplexMatrix2.fullTrace
          (faceHolonomy (patch Λ v U) p : Matrices.ComplexMatrix2) :=
      (continuous_subtype_val.comp hv).matrix_trace
    exact continuous_const.sub (continuous_const.mul (Complex.continuous_re.comp ht))
  unfold boltzmannWeight
  have hs : (fun v : Λ → Matrices.ComplexMatrix2.specialUnitary =>
      ∑ᶠ p ∈ facesTouching Λ, faceEnergy (patch Λ v U) p) =
      fun v => ∑ p ∈ (facesTouching_finite Λ).toFinset, faceEnergy (patch Λ v U) p := by
    funext v
    exact finsum_mem_eq_finite_toFinset_sum _ _
  refine Real.continuous_exp.comp (continuous_const.mul ?_)
  rw [hs]
  exact continuous_finsetSum _ fun p _ => hp p
theorem kernelOperator_eq_integral (β : ℝ) (F : GaugeField a → ℂ) (U : GaugeField a) :
    kernelOperator ha β hΛ F U = ∫ V, F (splice ha hΛ V U) ∂wilsonSpecification β Λ U := by
  have := secondCountable_specialUnitary
  have hm : Measurable fun V : Λ → Matrices.ComplexMatrix2.specialUnitary =>
      ENNReal.ofReal (boltzmannWeight β Λ U V) :=
    ENNReal.measurable_ofReal.comp (continuous_boltzmannWeight β U).measurable
  have hZ : 0 ≤ partitionFunction β Λ U :=
    integral_nonneg fun _ => (Real.exp_pos _).le
  unfold wilsonSpecification kernelOperator
  rw [integral_smul_measure,
    integral_withDensity_eq_integral_toReal_smul hm (ae_of_all _ fun _ => ENNReal.ofReal_lt_top),
    localPartition_eq ha hΛ, ENNReal.toReal_inv, ENNReal.toReal_ofReal hZ]
  have hi : ∀ V : Λ → Matrices.ComplexMatrix2.specialUnitary,
      F (splice ha hΛ V U) * (localWeight β Λ (splice ha hΛ V U) : ℂ) =
        (ENNReal.ofReal (boltzmannWeight β Λ U V)).toReal • F (splice ha hΛ V U) := fun V => by
    have hw : 0 ≤ boltzmannWeight β Λ U V := (Real.exp_pos _).le
    rw [ENNReal.toReal_ofReal hw, localWeight_splice ha hΛ, Complex.real_smul, mul_comm]
  simp only [hi, Complex.real_smul, Complex.ofReal_inv]
end Facts
end WilsonOperator
end InfiniteLattice
end YangMills.Construction
