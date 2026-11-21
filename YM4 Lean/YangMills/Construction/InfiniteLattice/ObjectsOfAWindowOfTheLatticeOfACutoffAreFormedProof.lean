import YangMills.Construction.InfiniteLattice.ObjectsOfAWindowOfTheLatticeOfACutoffAreFormed
import YangMills.Construction.InfiniteLattice.WilsonKernelOnObservables
import Mathlib
set_option autoImplicit false
open MeasureTheory
noncomputable section
namespace YangMills.Construction
open InfiniteLattice Conventions Matrices
namespace CutoffLattice.WindowObjects
variable {a : ℝ} {L K : ℕ}
theorem finite_faces_containing_link (b : Link a) :
    {p : ElementaryPlaquette a | b ∈ p.edges}.Finite := by
  have hS : (({b.initial} ∪ Set.range fun ν : Fin 4 => b.initial - axisStep a ν) :
      Set (LatticePoint a)).Finite :=
    (Set.finite_singleton _).union (Set.finite_range _)
  have hT := hS.prod (Set.finite_univ (α := Fin 4 × Fin 4))
  refine Set.Finite.of_finite_image
    (f := fun p : ElementaryPlaquette a => (p.corner, p.lowAxis, p.highAxis)) (hT.subset ?_) ?_
  · rintro _ ⟨p, hp, rfl⟩
    refine ⟨?_, Set.mem_univ _⟩
    simp only [Set.mem_ofPred_eq, ElementaryPlaquette.edges, List.mem_cons, List.not_mem_nil,
      or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr ⟨p.lowAxis, by simp [Link.forwardFrom]⟩
    · exact Or.inr ⟨p.highAxis, by simp [Link.forwardFrom]⟩
    · exact Or.inl rfl
  · intro p _ q _ h
    simp only [Prod.mk.injEq] at h
    exact ElementaryPlaquette.ext h.1 h.2.1 h.2.2
theorem faces_finite (W : LinkWindow a) : W.faces.Finite := by
  have h : W.faces ⊆ ⋃ b ∈ (W.links : Set (Link a)), {p : ElementaryPlaquette a | b ∈ p.edges} := by
    rintro p ⟨b, hb, hW⟩
    exact Set.mem_biUnion (Finset.mem_coe.mpr hW) hb
  exact (W.links.finite_toSet.biUnion fun b _ => finite_faces_containing_link b).subset h
theorem rim_finite (W : LinkWindow a) : W.rim.Finite := by
  have h : W.rim ⊆ ⋃ p ∈ W.faces, {b : Link a | b ∈ p.edges} := by
    rintro b ⟨⟨p, hp, hb⟩, -⟩
    exact Set.mem_biUnion hp hb
  exact ((faces_finite W).biUnion fun p _ => List.finite_toSet p.edges).subset h
theorem restrictRim_fieldOfRimValues (ha : 0 < a) (W : LinkWindow a)
    (ξ : LinkVariables W.rim) :
    W.restrictRim (W.fieldOfRimValues ha ξ) = ξ := by
  funext b
  exact gluedField_apply_of_mem ha W.rim_subset_positiveLinks _ _ b
theorem plaquetteActionSum_congr (hL : IsAdmissibleBlockingFactor L) (W : WindowAt L K)
    (V : W.Assignments) {U U' : FieldsAt L K} (h : W.restrictRim U = W.restrictRim U') :
    W.plaquetteActionSum hL V U = W.plaquetteActionSum hL V U' := by
  unfold WindowAt.plaquetteActionSum
  refine finsum_mem_congr rfl fun p hp => ?_
  have key : ∀ b ∈ p.edges, W.glue (spacingAt_pos hL K) V U b =
      W.glue (spacingAt_pos hL K) V U' b :=
    fun b hb => LinkWindow.glue_congr_of_mem_edges W (spacingAt_pos hL K) V h hp hb
  simp only [ElementaryPlaquette.edges, List.mem_cons, List.not_mem_nil, or_false,
    forall_eq_or_imp, forall_eq] at key
  obtain ⟨h1, h2, h3, h4⟩ := key
  simp only [faceHolonomy, h1, h2, h3, h4]
theorem localEnergy_restrictRim (hL : IsAdmissibleBlockingFactor L) (W : WindowAt L K)
    (V : W.Assignments) (U : FieldsAt L K) :
    W.localEnergy hL V (W.restrictRim U) = W.plaquetteActionSum hL V U :=
  plaquetteActionSum_congr hL W V
    (restrictRim_fieldOfRimValues (spacingAt_pos hL K) W _)
theorem continuous_glue_apply (ha : 0 < a) (W : LinkWindow a) (U : GaugeField a) (b : Link a) :
    Continuous fun V : W.Assignments => W.glue ha V U b := by
  by_cases h : b ∈ W.links
  · have e : (fun V : W.Assignments => W.glue ha V U b) = fun V => V ⟨b, h⟩ :=
      funext fun V => dif_pos h
    rw [e]
    exact continuous_apply _
  · by_cases h' : b.opposite ∈ W.links
    · have e : (fun V : W.Assignments => W.glue ha V U b) = fun V => (V ⟨b.opposite, h'⟩)⁻¹ :=
        funext fun V => (dif_neg h).trans (dif_pos h')
      rw [e]
      exact (continuous_apply _).inv
    · have e : (fun V : W.Assignments => W.glue ha V U b) = fun _ => U b :=
        funext fun V => (dif_neg h).trans (dif_neg h')
      rw [e]
      exact continuous_const
theorem continuous_localEnergy (hL : IsAdmissibleBlockingFactor L) (W : WindowAt L K)
    (ξ : LinkVariables W.rim) : Continuous fun V : W.Assignments => W.localEnergy hL V ξ := by
  have hb := continuous_glue_apply (spacingAt_pos hL K) W
    (W.fieldOfRimValues (spacingAt_pos hL K) ξ)
  simp only [WindowAt.localEnergy, WindowAt.plaquetteActionSum,
    finsum_mem_eq_finite_toFinset_sum _ (faces_finite W)]
  refine continuous_finsetSum _ fun p _ => continuous_const.mul ?_
  have hv : Continuous fun V : W.Assignments => faceHolonomy (W.glue (spacingAt_pos hL K) V
      (W.fieldOfRimValues (spacingAt_pos hL K) ξ)) p := by
    unfold faceHolonomy
    exact (((hb _).mul (hb _)).mul (hb _).inv).mul (hb _).inv
  have hm : Continuous fun V : W.Assignments => (faceHolonomy (W.glue (spacingAt_pos hL K) V
      (W.fieldOfRimValues (spacingAt_pos hL K) ξ)) p : ComplexMatrix2) :=
    continuous_subtype_val.comp hv
  exact Complex.continuous_re.comp hm.matrix_trace
theorem secondCountable_specialUnitary : SecondCountableTopology ComplexMatrix2.specialUnitary := by apply _root_.YangMills.Construction.InfiniteLattice.WilsonOperator.secondCountable_specialUnitary <;> assumption
theorem integrable_exp_localEnergy (hL : IsAdmissibleBlockingFactor L) (W : WindowAt L K) (β : ℝ)
    (ξ : LinkVariables W.rim) :
    Integrable (fun V' : W.Assignments => Real.exp (β * W.localEnergy hL V' ξ)) W.haarProd := by
  have : IsProbabilityMeasure W.haarProd := ⟨WindowAt.haarProd_univ W⟩
  have := secondCountable_specialUnitary
  have hc : Continuous fun V' : W.Assignments => Real.exp (β * W.localEnergy hL V' ξ) :=
    Real.continuous_exp.comp (continuous_const.mul (continuous_localEnergy hL W ξ))
  exact hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
theorem integral_exp_localEnergy_ne_zero (hL : IsAdmissibleBlockingFactor L) (W : WindowAt L K)
    (β : ℝ) (ξ : LinkVariables W.rim) :
    ∫ V', Real.exp (β * W.localEnergy hL V' ξ) ∂W.haarProd ≠ 0 := by
  have : IsProbabilityMeasure W.haarProd := ⟨WindowAt.haarProd_univ W⟩
  exact (integral_exp_pos (integrable_exp_localEnergy hL W β ξ)).ne'
theorem wellDefined : WindowObjectsWellDefined := by
  intro L K hL _ β _ W
  have hP := faces_finite W
  refine ⟨⟨hP, hP.cast_ncard_eq.symm, rim_finite W⟩, ?_,
    fun V U U' h => plaquetteActionSum_congr hL W V h,
    fun ξ => ⟨_, restrictRim_fieldOfRimValues (spacingAt_pos hL K) W ξ⟩,
    fun V U => localEnergy_restrictRim hL W V U,
    fun ξ => ⟨integrable_exp_localEnergy hL W β ξ, integral_exp_localEnergy_ne_zero hL W β ξ⟩,
    fun V U => ?_⟩
  · intro p hp b hb
    by_cases hW : b ∈ W.links
    · exact Or.inl (Finset.mem_coe.mpr hW)
    · exact Or.inr ⟨⟨p, hp, hb⟩, hW⟩
  · have hE : ∀ V' : W.Assignments,
        W.localEnergy hL V' (W.restrictRim U) = W.plaquetteActionSum hL V' U :=
      fun V' => localEnergy_restrictRim hL W V' U
    simp only [WindowAt.boltzmannKernel, hE]
end CutoffLattice.WindowObjects
end YangMills.Construction
