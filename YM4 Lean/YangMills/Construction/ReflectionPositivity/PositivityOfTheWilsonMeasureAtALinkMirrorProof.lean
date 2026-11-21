import YangMills.Construction.InfiniteLattice.WilsonKernelOnObservables
import YangMills.Construction.PassageToTheLimit.LatticeFunctionalsAreBoundedFormsProof
import YangMills.Construction.ReflectionPositivity.ActionInTheDoubledVariablesOfALinkMirror
import YangMills.Construction.ReflectionPositivity.DoublingOfTheCrossingVariables
import YangMills.Construction.ReflectionPositivity.IntegrandOfAFunctionalOfALinkMirrorIsBoundedAndBorel
import YangMills.Construction.ReflectionPositivity.PositivityOfTheWilsonMeasureAtALinkMirror
import YangMills.Construction.ReflectionPositivity.ReflectionInALinkMirror
import Mathlib
set_option autoImplicit false
open MeasureTheory Set
open scoped ComplexOrder
noncomputable section
namespace YangMills.Construction.ReflectionPositivity.CutoffMirrors.LinkPositivity
open IntegrandBounded (linkIntegrand)
variable {D : MirrorData}
theorem borel_fieldSpace (hA : D.FieldSpaceIsProduct) :
    borel D.FieldSpace = (inferInstance : MeasurableSpace D.FieldSpace) := by
  obtain ⟨-, -, -, -, -, -, htop, hσ, -, -⟩ := hA
  have h : borel D.FieldSpace = @borel D.FieldSpace D.productTopology :=
    congrArg (fun t => @borel D.FieldSpace t) htop.symm
  rw [h, ← hσ]
  exact borel_comap
theorem measurableSet_compactGaugeFields (hA : D.FieldSpaceIsProduct) :
    MeasurableSet (PeriodicLattice.compactGaugeFields D.L D.m ((D.K : ℕ) : ℤ)) := by apply _root_.YangMills.Construction.LimitSpaces.BoundedForms.measurableSet_compactGaugeFields <;> assumption
theorem fieldExpectation_eq_integral (hA : D.FieldSpaceIsProduct)
    (hE : D.EnergiesBoundedAndMeasureProbability) (g : D.FieldSpace → ℂ) :
    D.fieldExpectation g =
      (((PeriodicLattice.partitionFunction D.L D.m D.K D.coupling)⁻¹ : ℝ) : ℂ) *
        ∫ U : D.FieldSpace, ((PeriodicLattice.boltzmannWeight D.coupling U.1 : ℝ) : ℂ) * g U
          ∂D.fieldHaar := by
  classical
  have hS := measurableSet_compactGaugeFields hA
  obtain ⟨-, -, -, -, -, -, -, -, hZ, hI, -, -⟩ := hE
  let ν := PeriodicLattice.productHaarMeasure D.L D.m ((D.K : ℕ) : ℤ)
  let h : (PeriodicLattice.Bond D.L D.m ((D.K : ℕ) : ℤ) → Matrices.ComplexMatrix2) → ℂ := fun U =>
    if hU : U ∈ PeriodicLattice.compactGaugeFields D.L D.m ((D.K : ℕ) : ℤ) then g ⟨U, hU⟩ else 0
  let k : (PeriodicLattice.Bond D.L D.m ((D.K : ℕ) : ℤ) → Matrices.ComplexMatrix2) → ℂ := fun U =>
    ((PeriodicLattice.boltzmannWeight D.coupling U : ℝ) : ℂ) * h U
  have h₁ : ∫ U : D.FieldSpace, ((PeriodicLattice.boltzmannWeight D.coupling U.1 : ℝ) : ℂ) * g U
      ∂D.fieldHaar = ∫ y, k y ∂ν := by
    have e₁ : ∫ U : D.FieldSpace, ((PeriodicLattice.boltzmannWeight D.coupling U.1 : ℝ) : ℂ) * g U
        ∂D.fieldHaar = ∫ U : D.FieldSpace, k U.1 ∂D.fieldHaar := by
      refine integral_congr_ae (Filter.Eventually.of_forall fun U => ?_)
      have hU : h U.1 = g ⟨U.1, U.2⟩ := dif_pos U.2
      change _ = ((PeriodicLattice.boltzmannWeight D.coupling U.1 : ℝ) : ℂ) * h U.1
      rw [hU]
    rw [e₁]
    have e₂ := integral_subtype_comap (μ := ν) hS k
    have e₃ : ∫ y in PeriodicLattice.compactGaugeFields D.L D.m ((D.K : ℕ) : ℤ), k y ∂ν =
        ∫ y, k y ∂ν :=
      setIntegral_eq_integral_of_forall_compl_eq_zero fun U hU => by
        have : h U = 0 := dif_neg hU
        change ((PeriodicLattice.boltzmannWeight D.coupling U : ℝ) : ℂ) * h U = 0
        rw [this, mul_zero]
    rw [← e₃, ← e₂]
    rfl
  have hdens : ∀ U : PeriodicLattice.Bond D.L D.m ((D.K : ℕ) : ℤ) → Matrices.ComplexMatrix2,
      0 ≤ PeriodicLattice.boltzmannWeight D.coupling U := fun U => (Real.exp_pos _).le
  have hm : AEMeasurable (fun U => ENNReal.ofReal (PeriodicLattice.boltzmannWeight D.coupling U)) ν :=
    hI.aestronglyMeasurable.aemeasurable.ennreal_ofReal
  have h₂ : PeriodicLattice.gibbsExpectation D.L D.m D.K D.coupling h =
      (((PeriodicLattice.partitionFunction D.L D.m D.K D.coupling)⁻¹ : ℝ) : ℂ) * ∫ y, k y ∂ν := by
    unfold PeriodicLattice.gibbsExpectation PeriodicLattice.wilsonGibbsMeasure
    rw [integral_smul_measure, integral_withDensity_eq_integral_toReal_smul₀ hm
      (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
    have e₄ : ∫ U, (ENNReal.ofReal (PeriodicLattice.boltzmannWeight D.coupling U)).toReal • h U ∂ν =
        ∫ y, k y ∂ν := by
      refine integral_congr_ae (Filter.Eventually.of_forall fun U => ?_)
      change (ENNReal.ofReal (PeriodicLattice.boltzmannWeight D.coupling U)).toReal • h U =
        ((PeriodicLattice.boltzmannWeight D.coupling U : ℝ) : ℂ) * h U
      rw [ENNReal.toReal_ofReal (hdens U), Complex.real_smul]
    rw [e₄, ENNReal.toReal_inv, ENNReal.toReal_ofReal hZ.le, Complex.real_smul]
  rw [h₁, ← h₂]
  rfl
theorem fieldExpectation_conj (g : D.FieldSpace → ℂ) :
    D.fieldExpectation (fun U => starRingEnd ℂ (g U)) =
      starRingEnd ℂ (D.fieldExpectation g) := by
  classical
  unfold MirrorData.fieldExpectation PeriodicLattice.gibbsExpectation
  rw [← integral_conj]
  refine integral_congr_ae (Filter.Eventually.of_forall fun U => ?_)
  by_cases hU : U ∈ PeriodicLattice.compactGaugeFields D.L D.m ((D.K : ℕ) : ℤ)
  · simp only [dif_pos hU]
  · simp only [dif_neg hU, map_zero]
instance instIsProbabilityMeasureHaarPi (ι : Type) [Countable ι] :
    IsProbabilityMeasure (Matrices.ComplexMatrix2.haarPi ι) := by
  unfold Matrices.ComplexMatrix2.haarPi
  infer_instance
section Spaces
variable (C : LinkLevel D)
instance instIsProbabilityMeasureHalfHaar (σ : SlabSide) : IsProbabilityMeasure (C.halfHaar σ) := by
  unfold LinkLevel.halfHaar
  infer_instance
instance instIsProbabilityMeasureTransversalHaar : IsProbabilityMeasure C.transversalHaar := by
  unfold LinkLevel.transversalHaar
  infer_instance
instance instIsProbabilityMeasureDoubleHaar : IsProbabilityMeasure C.doubleHaar := by
  unfold LinkLevel.doubleHaar
  infer_instance
instance instIsProbabilityMeasureQuadrupleHaar : IsProbabilityMeasure C.quadrupleHaar := by
  unfold LinkLevel.quadrupleHaar
  infer_instance
theorem secondCountableTopology_specialUnitary :
    SecondCountableTopology Matrices.ComplexMatrix2.specialUnitary := by apply _root_.YangMills.Construction.InfiniteLattice.WilsonOperator.secondCountable_specialUnitary <;> assumption
theorem borelSpace_edgeFamily (ℬ : Set D.Edge) (hB : Finite D.Edge) :
    BorelSpace (ℬ → Matrices.ComplexMatrix2.specialUnitary) := by
  have := hB
  have := secondCountableTopology_specialUnitary
  infer_instance
theorem borelSpace_doubleSpace (hB : Finite D.Edge) : BorelSpace C.DoubleSpace := by
  have := hB
  have := secondCountableTopology_specialUnitary
  infer_instance
theorem borelSpace_quadrupleSpace (hB : Finite D.Edge) : BorelSpace C.QuadrupleSpace := by
  have := hB
  have := secondCountableTopology_specialUnitary
  infer_instance
theorem borelSpace_doubleSpace_prod (hB : Finite D.Edge) :
    BorelSpace (C.DoubleSpace × C.DoubleSpace) := by
  have := hB
  have := secondCountableTopology_specialUnitary
  infer_instance
end Spaces
structure LinkHypotheses (C : LinkLevel D) : Prop where
  product : D.FieldSpaceIsProduct
  energies : D.EnergiesBoundedAndMeasureProbability
  coords : DoubledTransversal.SplitCoordsHomeomorph C
  slab : ∀ σ : SlabSide, DoubledTransversal.HalfAlgebraEqSlabFunctions C σ
  algebra : ∀ σ : SlabSide, DoubledTransversal.HalfAlgebraClosed C σ
  linear : ∀ σ : SlabSide, DoubledTransversal.HalfFunctionLinearIsometric C σ
  transfer : DoubledTransversal.TransferIsReflection C
  doubled : DoubledTransversal.IntegralDoubled C ℂ
  independent : DoubledTransversal.PairPointsIndependent C
  halfAction : DoubledAction.HalfActionFacts C
  kernelSum : DoubledAction.KernelSumIdentity C
  series : DoubledAction.ExpSeries C
  verticesDisjoint : Disjoint (C.halfVertices .pos) (C.halfVertices .neg)
  integrand : IntegrandBounded.LinkIntegrandBoundedMeasurable C
  reflected : IntegrandBounded.ReflectPreservesBoundedMeasurable C
  symmetry : ∃ s : D.Symmetry, s.toFun = C.refl ∧
    ∀ U : D.FieldSpace, MirrorData.Symmetry.pullback s (MirrorData.Symmetry.pullback s U.1) = U.1
variable {C : LinkLevel D}
theorem reflectField_involutive (H : LinkHypotheses C) (U : D.FieldSpace) :
    C.reflectField (C.reflectField U) = U := by
  obtain ⟨s, hs, hinv⟩ := H.symmetry
  apply Subtype.ext
  rw [C.reflectField_val s hs, C.reflectField_val s hs]
  exact hinv U
theorem fieldOfCoords_hasCoords (H : LinkHypotheses C)
    (uPos : C.halfEdges .pos → Matrices.ComplexMatrix2.specialUnitary)
    (uNeg : C.halfEdges .neg → Matrices.ComplexMatrix2.specialUnitary)
    (v : C.transversalEdges → Matrices.ComplexMatrix2.specialUnitary) :
    C.HasCoords (C.fieldOfCoords uPos uNeg v) uPos uNeg v := by
  have hex : ∃ U, C.HasCoords U uPos uNeg v := by
    obtain ⟨U, hU⟩ := H.coords.1.bijective.surjective (uPos, uNeg, v)
    have h₁ : C.halfCoords .pos U = uPos := congrArg Prod.fst hU
    have h₂ : C.halfCoords .neg U = uNeg := congrArg (fun x => x.2.1) hU
    have h₃ : C.transversalCoords U = v := congrArg (fun x => x.2.2) hU
    exact ⟨U, h₁, h₂, h₃⟩
  exact Classical.epsilon_spec hex
theorem wilsonAction_eq_split (H : LinkHypotheses C) (U : D.FieldSpace) :
    PeriodicLattice.wilsonAction U.1 =
      C.halfAction (C.halfCoords .pos U) +
        C.halfAction (C.transfer (C.halfCoords .neg U)) +
          ∑ᶠ p ∈ C.transversalFaces, PeriodicLattice.plaquetteCost U.1 p := by
  classical
  have hfin : Finite D.Face := H.product.2.2.1
  obtain ⟨hp, -, -, hchain⟩ := H.halfAction
  obtain ⟨s, hs, -⟩ := H.symmetry
  obtain ⟨e₁, e₂, e₃⟩ := hchain s hs U
  have hpos : C.halfAction (C.halfCoords .pos U) =
      ∑ᶠ p ∈ C.halfFaces .pos, PeriodicLattice.plaquetteCost U.1 p :=
    finsum_mem_congr rfl fun p hp' => ((hp p hp').2 U).symm
  have hneg : C.halfAction (C.transfer (C.halfCoords .neg U)) =
      ∑ᶠ p ∈ C.halfFaces .neg, PeriodicLattice.plaquetteCost U.1 p :=
    (e₁.trans (e₂.trans e₃)).symm
  have hdis : Disjoint (C.halfFaces .pos) (C.halfFaces .neg) := by
    refine Set.disjoint_left.mpr fun p h₁ h₂ => ?_
    have hx : p.origin ∈ p.vertices := by simp [PeriodicLattice.Plaquette.vertices]
    exact Set.disjoint_left.mp H.verticesDisjoint (h₁ _ hx) (h₂ _ hx)
  have hdis' : Disjoint (C.halfFaces .pos ∪ C.halfFaces .neg) C.transversalFaces := by
    refine Set.disjoint_left.mpr fun p h₁ h₂ => ?_
    rcases h₁ with h₁ | h₁
    · exact h₂.1 h₁
    · exact h₂.2 h₁
  have huniv : (Set.univ : Set D.Face) =
      (C.halfFaces .pos ∪ C.halfFaces .neg) ∪ C.transversalFaces := by
    ext p
    simp only [mem_univ, mem_union, true_iff]
    by_cases h₁ : p ∈ C.halfFaces .pos
    · exact Or.inl (Or.inl h₁)
    by_cases h₂ : p ∈ C.halfFaces .neg
    · exact Or.inl (Or.inr h₂)
    · exact Or.inr ⟨h₁, h₂⟩
  unfold PeriodicLattice.wilsonAction
  rw [← finsum_mem_univ, huniv, finsum_mem_union hdis' (Set.toFinite _) (Set.toFinite _),
    finsum_mem_union hdis (Set.toFinite _) (Set.toFinite _), hpos, hneg]
theorem uniformNorm_nonneg (F : D.FieldSpace → ℂ) : 0 ≤ TestFunctions.uniformNorm F :=
  Real.iSup_nonneg fun _ => norm_nonneg _
theorem linkIntegrand_norm_le (H : LinkHypotheses C) {F : D.FieldSpace → ℂ}
    (hF : F ∈ C.halfAlgebra .pos) {n : ℕ} (γ : Fin n → C.KernelLabel) (ω : C.DoubleSpace) :
    ‖linkIntegrand C γ F ω‖ ≤ TestFunctions.uniformNorm F := by
  obtain ⟨B, hB⟩ := ((H.slab .pos).2 F hF).1
  have h₁ : ‖C.halfFunction .pos F ω.1‖ ≤ TestFunctions.uniformNorm F := by
    unfold TestFunctions.uniformNorm
    rw [← (H.linear .pos).2.2 F hF]
    exact le_ciSup (f := fun u => ‖C.halfFunction .pos F u‖)
      ⟨B, by rintro _ ⟨u, rfl⟩; exact hB u⟩ ω.1
  have h₂ : ‖((Real.exp (-D.coupling * C.halfAction ω.1) : ℝ) : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le, Real.exp_le_one_iff]
    have := mul_nonneg D.coupling_pos.le (H.halfAction.2.2.1 ω.1)
    linarith
  have h₃ : ‖C.kernelProd γ ω‖ ≤ 1 := by
    unfold LinkLevel.kernelProd
    rw [norm_prod]
    exact Finset.prod_le_one (fun _ _ => norm_nonneg _) fun j _ => (H.kernelSum.1 (γ j)).2 ω
  unfold linkIntegrand
  rw [norm_mul, norm_mul]
  have hs := uniformNorm_nonneg F
  calc ‖C.halfFunction .pos F ω.1‖ * ‖((Real.exp (-D.coupling * C.halfAction ω.1) : ℝ) : ℂ)‖ *
        ‖C.kernelProd γ ω‖
      ≤ TestFunctions.uniformNorm F * 1 * 1 :=
        mul_le_mul (mul_le_mul h₁ h₂ (norm_nonneg _) hs) h₃ (norm_nonneg _) (by simpa using hs)
    _ = TestFunctions.uniformNorm F := by ring
theorem integrable_linkIntegrand (H : LinkHypotheses C) {F : D.FieldSpace → ℂ}
    (hF : F ∈ C.halfAlgebra .pos) {n : ℕ} (γ : Fin n → C.KernelLabel) :
    Integrable (linkIntegrand C γ F) C.doubleHaar := by
  have hB := borelSpace_doubleSpace C H.product.2.1
  have hm : Measurable (linkIntegrand C γ F) := by
    have h := (H.integrand γ F hF).2
    rwa [hB.measurable_eq.symm] at h
  exact Integrable.of_bound hm.aestronglyMeasurable (TestFunctions.uniformNorm F)
    (Filter.Eventually.of_forall (linkIntegrand_norm_le H hF γ))
theorem summable_seriesCoeff (H : LinkHypotheses C) :
    Summable fun s : C.KernelWord => C.seriesCoeff s.1 := by
  classical
  have hfin : Finite D.Face := H.product.2.2.1
  have hβ := D.coupling_pos
  let _ : Fintype C.KernelLabel := Fintype.ofFinite _
  have hnn : ∀ n, 0 ≤ C.seriesCoeff n := fun n => by
    unfold LinkLevel.seriesCoeff
    positivity
  refine (summable_sigma_of_nonneg fun s => hnn s.1).mpr
    ⟨fun n => (hasSum_fintype _).summable, ?_⟩
  have h : ∀ n : ℕ, ∑' _ : Fin n → C.KernelLabel, C.seriesCoeff n =
      (D.coupling * (Fintype.card C.KernelLabel : ℝ) / 4) ^ n / (n.factorial : ℝ) := by
    intro n
    rw [tsum_fintype, Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin,
      nsmul_eq_mul]
    unfold LinkLevel.seriesCoeff
    push_cast
    rw [show D.coupling * (Fintype.card C.KernelLabel : ℝ) / 4 =
      (Fintype.card C.KernelLabel : ℝ) * (D.coupling / 4) by ring, mul_pow]
    ring
  simp only [h]
  exact Real.summable_pow_div_factorial _
def pairTerm (C : LinkLevel D) (F F' : D.FieldSpace → ℂ) (s : C.KernelWord)
    (x : C.QuadrupleSpace) : ℂ :=
  (C.seriesCoeff s.1 : ℂ) * (linkIntegrand C s.2 F' (C.pairPoints x).1 *
    starRingEnd ℂ (linkIntegrand C s.2 F (C.pairPoints x).2))
theorem pairTerm_norm_le (H : LinkHypotheses C) {F F' : D.FieldSpace → ℂ}
    (hF : F ∈ C.halfAlgebra .pos) (hF' : F' ∈ C.halfAlgebra .pos) (s : C.KernelWord)
    (x : C.QuadrupleSpace) :
    ‖pairTerm C F F' s x‖ ≤
      C.seriesCoeff s.1 * (TestFunctions.uniformNorm F' * TestFunctions.uniformNorm F) := by
  have hβ := D.coupling_pos
  have hnn : 0 ≤ C.seriesCoeff s.1 := by
    unfold LinkLevel.seriesCoeff
    positivity
  unfold pairTerm
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hnn, norm_mul, RCLike.norm_conj]
  exact mul_le_mul_of_nonneg_left
    (mul_le_mul (linkIntegrand_norm_le H hF' _ _) (linkIntegrand_norm_le H hF _ _) (norm_nonneg _)
      (uniformNorm_nonneg F')) hnn
theorem integrable_pairTerm (H : LinkHypotheses C) {F F' : D.FieldSpace → ℂ}
    (hF : F ∈ C.halfAlgebra .pos) (hF' : F' ∈ C.halfAlgebra .pos) (s : C.KernelWord) :
    Integrable (pairTerm C F F' s) C.quadrupleHaar := by
  have hB := borelSpace_doubleSpace C H.product.2.1
  have hB₄ := borelSpace_quadrupleSpace C H.product.2.1
  have hB₂ := borelSpace_doubleSpace_prod C H.product.2.1
  have hp : Measurable C.pairPoints := H.independent.1.measurable
  have hm₁ : Measurable (linkIntegrand C s.2 F') := by
    have h := (H.integrand s.2 F' hF').2
    rwa [hB.measurable_eq.symm] at h
  have hm₂ : Measurable (linkIntegrand C s.2 F) := by
    have h := (H.integrand s.2 F hF).2
    rwa [hB.measurable_eq.symm] at h
  have hm : Measurable (pairTerm C F F' s) :=
    measurable_const.mul ((hm₁.comp (measurable_fst.comp hp)).mul
      (Complex.continuous_conj.measurable.comp (hm₂.comp (measurable_snd.comp hp))))
  exact Integrable.of_bound hm.aestronglyMeasurable _
    (Filter.Eventually.of_forall (pairTerm_norm_le H hF hF' s))
theorem integral_pairTerm (H : LinkHypotheses C) {F F' : D.FieldSpace → ℂ}
    (hF : F ∈ C.halfAlgebra .pos) (hF' : F' ∈ C.halfAlgebra .pos) (s : C.KernelWord) :
    ∫ x, pairTerm C F F' s x ∂C.quadrupleHaar =
      (C.seriesCoeff s.1 : ℂ) *
        (C.transferFunctional s.2 F' * starRingEnd ℂ (C.transferFunctional s.2 F)) := by
  unfold pairTerm
  rw [integral_const_mul]
  have h₁ := H.integrand s.2 F' hF'
  have h₂ := H.integrand s.2 F hF
  rw [H.independent.2.2 _ _ h₁.1 h₁.2 h₂.1 h₂.2]
  rfl
theorem liftToQuadruple_eq_tsum (H : LinkHypotheses C) {F F' : D.FieldSpace → ℂ}
    (hF : F ∈ C.halfAlgebra .pos) (hF' : F' ∈ C.halfAlgebra .pos) (x : C.QuadrupleSpace) :
    C.liftToQuadruple (fun U : D.FieldSpace =>
        ((PeriodicLattice.boltzmannWeight D.coupling U.1 : ℝ) : ℂ) *
          (starRingEnd ℂ (F (C.reflectField U)) * F' U)) x =
      ((Real.exp (-D.coupling * (C.transversalFaces.ncard : ℝ)) : ℝ) : ℂ) *
        ∑' s, pairTerm C F F' s x := by
  classical
  have hfin : Finite D.Face := H.product.2.2.1
  let _ : Fintype C.KernelLabel := Fintype.ofFinite _
  set U := C.doubledField x.1 x.2.1 x.2.2.1 x.2.2.2 with hU
  have hco := fieldOfCoords_hasCoords H x.1 x.2.1 (C.transversalQuot x.2.2.1 x.2.2.2)
  have h₁ : C.halfCoords .pos U = x.1 := hco.1
  have h₂ : C.halfCoords .neg U = x.2.1 := hco.2.1
  have hF'U : F' U = C.halfFunction .pos F' x.1 := by
    rw [C.halfFunction_spec hF' U, h₁]
  have hFU : F (C.reflectField U) =
      C.halfFunction .pos F (C.transfer x.2.1) := by
    rw [H.transfer.2.2.2 F hF U, h₂]
  set ePos : ℝ := Real.exp (-D.coupling * C.halfAction x.1) with hePos
  set eNeg : ℝ := Real.exp (-D.coupling * C.halfAction (C.transfer x.2.1)) with heNeg
  have hdens : ((PeriodicLattice.boltzmannWeight D.coupling U.1 : ℝ) : ℂ) =
      (ePos : ℂ) * (eNeg : ℂ) *
      (((Real.exp (-D.coupling * (C.transversalFaces.ncard : ℝ)) : ℝ) : ℂ) *
        ∑' n : ℕ, C.seriesTerm n (C.posPoint x.1 x.2.2.1) (C.negPoint x.2.1 x.2.2.2)) := by
    rw [← H.series.1 x.1 x.2.1 x.2.2.1 x.2.2.2]
    unfold PeriodicLattice.boltzmannWeight
    rw [wilsonAction_eq_split H U, h₁, h₂, hePos, heNeg, ← Complex.ofReal_mul,
      ← Complex.ofReal_mul, ← Real.exp_add, ← Real.exp_add]
    congr 2
    ring
  have hsum : Summable fun s => pairTerm C F F' s x :=
    Summable.of_norm_bounded
      ((summable_seriesCoeff H).mul_right
        (TestFunctions.uniformNorm F' * TestFunctions.uniformNorm F))
      fun s => pairTerm_norm_le H hF hF' s x
  have hinner : ∀ n : ℕ, ∑' γ : Fin n → C.KernelLabel, pairTerm C F F' ⟨n, γ⟩ x =
      (C.halfFunction .pos F' x.1 * starRingEnd ℂ (C.halfFunction .pos F (C.transfer x.2.1)) *
        ((ePos : ℂ) * (eNeg : ℂ))) *
      C.seriesTerm n (C.posPoint x.1 x.2.2.1) (C.negPoint x.2.1 x.2.2.2) := by
    intro n
    rw [tsum_fintype]
    unfold LinkLevel.seriesTerm
    rw [finsum_eq_sum_of_fintype, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun γ _ => ?_
    have e₁ : (C.pairPoints x).1 = C.posPoint x.1 x.2.2.1 := rfl
    have e₂ : (C.pairPoints x).2 = C.negPoint x.2.1 x.2.2.2 := rfl
    unfold pairTerm
    rw [e₁, e₂]
    unfold linkIntegrand
    simp only [LinkLevel.posPoint, LinkLevel.negPoint, map_mul, Complex.conj_ofReal]
    rw [← hePos, ← heNeg]
    ring
  have hexp : ∑' s, pairTerm C F F' s x =
      (C.halfFunction .pos F' x.1 * starRingEnd ℂ (C.halfFunction .pos F (C.transfer x.2.1)) *
        ((ePos : ℂ) * (eNeg : ℂ))) *
      ∑' n : ℕ, C.seriesTerm n (C.posPoint x.1 x.2.2.1) (C.negPoint x.2.1 x.2.2.2) := by
    rw [hsum.tsum_sigma, ← tsum_mul_left]
    exact tsum_congr hinner
  change ((PeriodicLattice.boltzmannWeight D.coupling U.1 : ℝ) : ℂ) *
    (starRingEnd ℂ (F (C.reflectField U)) * F' U) = _
  rw [hexp, hdens, hF'U, hFU]
  ring
theorem weightedProduct_bounded_measurable (H : LinkHypotheses C) {F F' : D.FieldSpace → ℂ}
    (hF : F ∈ C.halfAlgebra .pos) (hF' : F' ∈ C.halfAlgebra .pos) :
    TestFunctions.IsBoundedFun (fun U : D.FieldSpace =>
        ((PeriodicLattice.boltzmannWeight D.coupling U.1 : ℝ) : ℂ) *
          (starRingEnd ℂ (F (C.reflectField U)) * F' U)) ∧
      Measurable[borel D.FieldSpace] (fun U : D.FieldSpace =>
        ((PeriodicLattice.boltzmannWeight D.coupling U.1 : ℝ) : ℂ) *
          (starRingEnd ℂ (F (C.reflectField U)) * F' U)) := by
  have hb := borel_fieldSpace H.product
  have ha := (H.algebra .pos).1
  obtain ⟨⟨B, hB⟩, hm⟩ := H.reflected F (ha F hF).1 (ha F hF).2
  obtain ⟨⟨B', hB'⟩, hm'⟩ := ha F' hF'
  rw [hb] at hm hm' ⊢
  have hcont : Continuous fun U : D.FieldSpace => PeriodicLattice.boltzmannWeight D.coupling U.1 := by
    have h := H.energies.2.2.2.2.1
    rw [MirrorData.ContinuousForProduct, H.product.2.2.2.2.2.2.1] at h
    exact h
  have hsp : OpensMeasurableSpace D.FieldSpace := by
    have : BorelSpace D.FieldSpace := ⟨hb.symm⟩
    infer_instance
  have hd : Measurable fun U : D.FieldSpace => PeriodicLattice.boltzmannWeight D.coupling U.1 :=
    hcont.measurable
  refine ⟨⟨1 * (B * B'), fun U => ?_⟩, (Complex.measurable_ofReal.comp hd).mul
    ((Complex.continuous_conj.measurable.comp hm).mul hm')⟩
  have hd₁ : ‖((PeriodicLattice.boltzmannWeight D.coupling U.1 : ℝ) : ℂ)‖ ≤ 1 := by
    unfold PeriodicLattice.boltzmannWeight
    rw [Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le, Real.exp_le_one_iff]
    have := mul_nonneg D.coupling_pos.le (H.energies.2.2.2.2.2.1 U).1
    linarith
  rw [norm_mul, norm_mul, RCLike.norm_conj]
  have hBn : 0 ≤ B := (norm_nonneg _).trans (hB U)
  exact mul_le_mul hd₁ (mul_le_mul (hB U) (hB' U) (norm_nonneg _) hBn)
    (mul_nonneg (norm_nonneg _) (norm_nonneg _)) zero_le_one
theorem hasSum_thetaForm (H : LinkHypotheses C) {F F' : D.FieldSpace → ℂ}
    (hF : F ∈ C.halfAlgebra .pos) (hF' : F' ∈ C.halfAlgebra .pos) :
    HasSum (sumTerm C F F') (C.thetaForm F F') := by
  have hfin : Finite D.Face := H.product.2.2.1
  obtain ⟨hbd, hms⟩ := weightedProduct_bounded_measurable H hF hF'
  have hint := (H.doubled _ hbd hms).2.2
  have hnorm : Summable fun s => ∫ x, ‖pairTerm C F F' s x‖ ∂C.quadrupleHaar := by
    refine Summable.of_nonneg_of_le (fun s => integral_nonneg fun _ => norm_nonneg _) (fun s => ?_)
      ((summable_seriesCoeff H).mul_right
        (TestFunctions.uniformNorm F' * TestFunctions.uniformNorm F))
    have h := norm_integral_le_of_norm_le_const (μ := C.quadrupleHaar)
      (f := fun x => ‖pairTerm C F F' s x‖) (C := C.seriesCoeff s.1 *
        (TestFunctions.uniformNorm F' * TestFunctions.uniformNorm F))
      (Filter.Eventually.of_forall fun x => by
        simpa using pairTerm_norm_le H hF hF' s x)
    simp only [probReal_univ, mul_one] at h
    exact (le_abs_self _).trans h
  have hs := hasSum_integral_of_summable_integral_norm (F := pairTerm C F F')
    (integrable_pairTerm H hF hF') hnorm
  have hform : C.thetaForm F F' =
      (((PeriodicLattice.partitionFunction D.L D.m D.K D.coupling)⁻¹ : ℝ) : ℂ) *
        ((Real.exp (-D.coupling * (C.transversalFaces.ncard : ℝ)) : ℝ) : ℂ) *
          ∫ x, ∑' s, pairTerm C F F' s x ∂C.quadrupleHaar := by
    have e : ∫ x, C.liftToQuadruple (fun U : D.FieldSpace =>
        ((PeriodicLattice.boltzmannWeight D.coupling U.1 : ℝ) : ℂ) *
          (starRingEnd ℂ (F (C.reflectField U)) * F' U)) x ∂C.quadrupleHaar =
        ((Real.exp (-D.coupling * (C.transversalFaces.ncard : ℝ)) : ℝ) : ℂ) *
          ∫ x, ∑' s, pairTerm C F F' s x ∂C.quadrupleHaar := by
      rw [← integral_const_mul]
      exact integral_congr_ae
        (Filter.Eventually.of_forall fun x => liftToQuadruple_eq_tsum H hF hF' x)
    unfold LinkLevel.thetaForm
    rw [fieldExpectation_eq_integral H.product H.energies, hint, e, mul_assoc]
  have hterm : sumTerm C F F' = fun s =>
      (((PeriodicLattice.partitionFunction D.L D.m D.K D.coupling)⁻¹ : ℝ) : ℂ) *
        ((Real.exp (-D.coupling * (C.transversalFaces.ncard : ℝ)) : ℝ) : ℂ) *
          ∫ x, pairTerm C F F' s x ∂C.quadrupleHaar := by
    funext s
    rw [integral_pairTerm H hF hF' s]
    unfold sumTerm LinkLevel.seriesWeight LinkLevel.seriesCoeff
    push_cast
    ring
  rw [hform, hterm]
  exact hs.mul_left _
theorem countable_kernelWord (H : LinkHypotheses C) : Countable C.KernelWord := by
  have hfin : Finite D.Face := H.product.2.2.1
  infer_instance
theorem seriesWeight_pos (H : LinkHypotheses C) {n : ℕ} (γ : Fin n → C.KernelLabel) :
    0 < C.seriesWeight γ := by
  have hZ := H.energies.2.2.2.2.2.2.2.2.1
  have hβ := D.coupling_pos
  unfold LinkLevel.seriesWeight
  positivity
theorem linearCombination_mem (H : LinkHypotheses C) (σ : SlabSide) (a b : ℂ)
    {F₁ F₂ : D.FieldSpace → ℂ} (h₁ : F₁ ∈ C.halfAlgebra σ) (h₂ : F₂ ∈ C.halfAlgebra σ) :
    a • F₁ + b • F₂ ∈ C.halfAlgebra σ := by
  obtain ⟨-, -, hadd, hsmul, -, -⟩ := H.algebra σ
  exact hadd _ (hsmul a _ h₁) _ (hsmul b _ h₂)
theorem transferFunctional_linear (H : LinkHypotheses C) {n : ℕ} (γ : Fin n → C.KernelLabel)
    (a b : ℂ) {F₁ F₂ : D.FieldSpace → ℂ} (h₁ : F₁ ∈ C.halfAlgebra .pos)
    (h₂ : F₂ ∈ C.halfAlgebra .pos) :
    C.transferFunctional γ (a • F₁ + b • F₂) =
      a * C.transferFunctional γ F₁ + b * C.transferFunctional γ F₂ := by
  obtain ⟨-, -, hadd, hsmul, -, -⟩ := H.algebra .pos
  obtain ⟨hladd, hlsmul, -⟩ := H.linear .pos
  have hhalf : C.halfFunction .pos (a • F₁ + b • F₂) =
      a • C.halfFunction .pos F₁ + b • C.halfFunction .pos F₂ := by
    rw [hladd _ (hsmul a _ h₁) _ (hsmul b _ h₂), hlsmul a _ h₁, hlsmul b _ h₂]
  have hpt : ∀ ω, linkIntegrand C γ (a • F₁ + b • F₂) ω =
      a * linkIntegrand C γ F₁ ω + b * linkIntegrand C γ F₂ ω := by
    intro ω
    unfold linkIntegrand
    rw [hhalf]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  rw [IntegrandBounded.transferFunctional_eq_integral,
    IntegrandBounded.transferFunctional_eq_integral,
    IntegrandBounded.transferFunctional_eq_integral,
    integral_congr_ae (Filter.Eventually.of_forall hpt),
    integral_add ((integrable_linkIntegrand H h₁ γ).const_mul a)
      ((integrable_linkIntegrand H h₂ γ).const_mul b),
    integral_const_mul, integral_const_mul]
theorem transferFunctional_norm_le (H : LinkHypotheses C) {n : ℕ} (γ : Fin n → C.KernelLabel)
    {F : D.FieldSpace → ℂ} (hF : F ∈ C.halfAlgebra .pos) :
    ‖C.transferFunctional γ F‖ ≤ TestFunctions.uniformNorm F := by
  rw [IntegrandBounded.transferFunctional_eq_integral]
  have h := norm_integral_le_of_norm_le_const (μ := C.doubleHaar)
    (f := linkIntegrand C γ F) (C := TestFunctions.uniformNorm F)
    (Filter.Eventually.of_forall (linkIntegrand_norm_le H hF γ))
  simpa using h
theorem sesquilinearOn_pos (H : LinkHypotheses C) : FormSesquilinearOn C (C.halfAlgebra .pos) := by
  intro a b F₁ h₁ F₂ h₂ G hG
  have hc := linearCombination_mem H .pos a b h₁ h₂
  refine ⟨hc, ?_, ?_⟩
  · refine (hasSum_thetaForm H hc hG).unique ?_
    have h := ((hasSum_thetaForm H h₁ hG).mul_left (starRingEnd ℂ a)).add
      ((hasSum_thetaForm H h₂ hG).mul_left (starRingEnd ℂ b))
    refine h.congr_fun ?_
    intro s
    unfold sumTerm
    rw [transferFunctional_linear H s.2 a b h₁ h₂]
    simp only [map_add, map_mul]
    ring
  · refine (hasSum_thetaForm H hG hc).unique ?_
    have h := ((hasSum_thetaForm H hG h₁).mul_left a).add ((hasSum_thetaForm H hG h₂).mul_left b)
    refine h.congr_fun ?_
    intro s
    unfold sumTerm
    rw [transferFunctional_linear H s.2 a b h₁ h₂]
    ring
theorem hermitianOn_pos (H : LinkHypotheses C) : FormHermitianOn C (C.halfAlgebra .pos) := by
  intro F hF F' hF'
  refine (hasSum_thetaForm H hF' hF).unique ?_
  have h := (Complex.hasSum_conj' ).mpr (hasSum_thetaForm H hF hF')
  refine h.congr_fun ?_
  intro s
  unfold sumTerm
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_conj]
  ring
theorem nonnegOn_pos (H : LinkHypotheses C) : FormNonnegOn C (C.halfAlgebra .pos) := by
  intro F hF
  refine (hasSum_thetaForm H hF hF).nonneg fun s => ?_
  have hw := (seriesWeight_pos H s.2).le
  have e : sumTerm C F F s =
      ((C.seriesWeight s.2 * Complex.normSq (C.transferFunctional s.2 F) : ℝ) : ℂ) := by
    unfold sumTerm
    rw [mul_assoc, mul_comm (starRingEnd ℂ _), Complex.mul_conj]
    push_cast
    ring
  rw [e]
  exact_mod_cast mul_nonneg hw (Complex.normSq_nonneg _)
theorem cauchySchwarzOn_of {𝔄 : Set (D.FieldSpace → ℂ)} (hs : FormSesquilinearOn C 𝔄)
    (hh : FormHermitianOn C 𝔄) (hp : FormNonnegOn C 𝔄) : FormCauchySchwarzOn C 𝔄 := by
  intro F hF F' hF'
  set y := C.thetaForm F F' with hy
  have hx := hp F hF
  have hz := hp F' hF'
  obtain ⟨hxr, hxi⟩ := Complex.le_def.mp hx
  obtain ⟨hzr, hzi⟩ := Complex.le_def.mp hz
  simp only [Complex.zero_re, Complex.zero_im] at hxr hxi hzr hzi
  set x := (C.thetaForm F F).re with hxdef
  set z := (C.thetaForm F' F').re with hzdef
  have hxc : C.thetaForm F F = (x : ℂ) := Complex.ext rfl (by simpa using hxi.symm)
  have hzc : C.thetaForm F' F' = (z : ℂ) := Complex.ext rfl (by simpa using hzi.symm)
  have hyc : C.thetaForm F' F = starRingEnd ℂ y := hh F hF F' hF'
  have hquad : ∀ r : ℝ, 0 ≤ (‖y‖ ^ 2 * z) * (r * r) + (-2 * ‖y‖ ^ 2) * r + x := by
    intro r
    set t : ℂ := -((r : ℂ) * starRingEnd ℂ y) with ht
    obtain ⟨hG, e₁, -⟩ := hs 1 t F hF F' hF' F hF
    obtain ⟨-, e₂, -⟩ := hs 1 t F hF F' hF' F' hF'
    obtain ⟨-, e₃, -⟩ := hs 1 t F hF F' hF' ((1 : ℂ) • F + t • F') hG
    obtain ⟨-, -, e₄⟩ := hs 1 t F hF F' hF' F hF
    obtain ⟨-, -, e₅⟩ := hs 1 t F hF F' hF' F' hF'
    have hpos := hp _ hG
    rw [e₃, e₄, e₅, hxc, hzc, hyc, ← hy] at hpos
    have hre := (Complex.le_def.mp hpos).1
    have hnorm : ‖y‖ ^ 2 = y.re * y.re + y.im * y.im := by
      rw [Complex.sq_norm, Complex.normSq_apply]
    rw [hnorm]
    simp only [ht, map_one, map_neg, map_mul, Complex.conj_ofReal, Complex.conj_conj, one_mul,
      Complex.add_re, Complex.mul_re, Complex.mul_im, Complex.add_im, Complex.neg_re,
      Complex.neg_im, Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.zero_re] at hre
    nlinarith [hre]
  have hdisc := discrim_le_zero hquad
  unfold discrim at hdisc
  have hle : ‖y‖ ^ 2 ≤ x * z := by
    by_cases h0 : ‖y‖ = 0
    · rw [h0]
      simpa using mul_nonneg hxr hzr
    · have hpos : 0 < ‖y‖ ^ 2 := by positivity
      have : ‖y‖ ^ 2 * (‖y‖ ^ 2 - x * z) ≤ 0 := by nlinarith
      have := nonpos_of_mul_nonpos_right this hpos
      linarith
  rw [hxc, hzc]
  exact_mod_cast hle
theorem posHermitianFormOn_pos (H : LinkHypotheses C) :
    IsPosHermitianFormOn C (C.halfAlgebra .pos) :=
  ⟨sesquilinearOn_pos H, hermitianOn_pos H, nonnegOn_pos H,
    cauchySchwarzOn_of (sesquilinearOn_pos H) (hermitianOn_pos H) (nonnegOn_pos H)⟩
theorem summable_norm_sumTerm (H : LinkHypotheses C) {F F' : D.FieldSpace → ℂ}
    (hF : F ∈ C.halfAlgebra .pos) (hF' : F' ∈ C.halfAlgebra .pos) :
    Summable fun s => ‖sumTerm C F F' s‖ := by
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun s => ?_)
    (((summable_seriesCoeff H).mul_left
      ((PeriodicLattice.partitionFunction D.L D.m D.K D.coupling)⁻¹ *
        Real.exp (-D.coupling * (C.transversalFaces.ncard : ℝ)))).mul_right
      (TestFunctions.uniformNorm F * TestFunctions.uniformNorm F'))
  have hw := (seriesWeight_pos H s.2).le
  have hwe : C.seriesWeight s.2 = (PeriodicLattice.partitionFunction D.L D.m D.K D.coupling)⁻¹ *
      Real.exp (-D.coupling * (C.transversalFaces.ncard : ℝ)) * C.seriesCoeff s.1 := rfl
  unfold sumTerm
  rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg hw, RCLike.norm_conj, mul_assoc,
    ← hwe]
  exact mul_le_mul_of_nonneg_left
    (mul_le_mul (transferFunctional_norm_le H s.2 hF) (transferFunctional_norm_le H s.2 hF')
      (norm_nonneg _) (uniformNorm_nonneg F)) hw
theorem comp_reflectField_mem_pos (H : LinkHypotheses C) {F : D.FieldSpace → ℂ}
    (hF : F ∈ C.halfAlgebra .neg) : F ∘ C.reflectField ∈ C.halfAlgebra .pos := by
  obtain ⟨Φ, hm, ⟨B, hB⟩, rfl⟩ := hF
  have hbPos := borelSpace_edgeFamily (C.halfEdges .pos) H.product.2.1
  have hbNeg := borelSpace_edgeFamily (C.halfEdges .neg) H.product.2.1
  let e := H.transfer.1.homeomorph C.transfer
  have hm' : Measurable Φ := by
    rwa [hbNeg.measurable_eq.symm] at hm
  refine ⟨Φ ∘ e.symm, ?_, ⟨B, fun v => hB _⟩, ?_⟩
  · have h : Measurable (Φ ∘ e.symm) := hm'.comp e.symm.continuous.measurable
    rwa [hbPos.measurable_eq.symm]
  · funext U
    have key : e (C.halfCoords .neg (C.reflectField U)) = C.halfCoords .pos U := by
      change C.transfer _ = _
      rw [← H.transfer.2.2.1, reflectField_involutive H]
    have h : e.symm (C.halfCoords .pos U) = C.halfCoords .neg (C.reflectField U) := by
      rw [← key, e.symm_apply_apply]
    change Φ (C.halfCoords .neg (C.reflectField U)) = Φ (e.symm (C.halfCoords .pos U))
    rw [h]
theorem thetaForm_neg_eq (H : LinkHypotheses C) {F F' : D.FieldSpace → ℂ}
    (hF : F ∈ C.halfAlgebra .neg) (hF' : F' ∈ C.halfAlgebra .neg) :
    C.thetaForm F F' = C.thetaForm (F ∘ C.reflectField) (F' ∘ C.reflectField) := by
  rw [hermitianOn_pos H _ (comp_reflectField_mem_pos H hF') _ (comp_reflectField_mem_pos H hF)]
  unfold LinkLevel.thetaForm
  rw [← fieldExpectation_conj]
  congr 1
  funext U
  simp only [Function.comp_apply, reflectField_involutive H, map_mul, Complex.conj_conj]
  ring
theorem sesquilinearOn_neg (H : LinkHypotheses C) : FormSesquilinearOn C (C.halfAlgebra .neg) := by
  intro a b F₁ h₁ F₂ h₂ G hG
  have hc := linearCombination_mem H .neg a b h₁ h₂
  obtain ⟨-, e₁, e₂⟩ := sesquilinearOn_pos H a b _ (comp_reflectField_mem_pos H h₁) _
    (comp_reflectField_mem_pos H h₂) _ (comp_reflectField_mem_pos H hG)
  refine ⟨hc, ?_, ?_⟩
  · rw [thetaForm_neg_eq H hc hG, thetaForm_neg_eq H h₁ hG, thetaForm_neg_eq H h₂ hG]
    exact e₁
  · rw [thetaForm_neg_eq H hG hc, thetaForm_neg_eq H hG h₁, thetaForm_neg_eq H hG h₂]
    exact e₂
theorem hermitianOn_neg (H : LinkHypotheses C) : FormHermitianOn C (C.halfAlgebra .neg) := by
  intro F hF F' hF'
  rw [thetaForm_neg_eq H hF' hF, thetaForm_neg_eq H hF hF']
  exact hermitianOn_pos H _ (comp_reflectField_mem_pos H hF) _ (comp_reflectField_mem_pos H hF')
theorem nonnegOn_neg (H : LinkHypotheses C) : FormNonnegOn C (C.halfAlgebra .neg) := by
  intro F hF
  rw [thetaForm_neg_eq H hF hF]
  exact nonnegOn_pos H _ (comp_reflectField_mem_pos H hF)
theorem negHalfProperties_holds (H : LinkHypotheses C) : NegHalfProperties C := by
  refine ⟨fun F hF => comp_reflectField_mem_pos H hF, fun F hF F' hF' => thetaForm_neg_eq H hF hF',
    ⟨sesquilinearOn_neg H, hermitianOn_neg H, nonnegOn_neg H,
      cauchySchwarzOn_of (sesquilinearOn_neg H) (hermitianOn_neg H) (nonnegOn_neg H)⟩, ?_⟩
  intro σ Φ hΦ
  have hmem : Φ ∈ C.halfAlgebra σ := ((H.slab σ).1 Φ).mp hΦ
  cases σ
  · exact nonnegOn_pos H Φ hmem
  · exact nonnegOn_neg H Φ hmem
theorem reflectionPositivityAtLink_holds (hS : FieldSpaceAndFaceEnergies.Statement)
    (hD : DoubledTransversal.DoublingProperties)
    (hK : DoubledAction.DoubledActionProperties)
    (hG : HalfSpaces.HalfSpaceStructure)
    (hR : LinkReflection.LinkReflectionProperties)
    (hI : IntegrandBounded.BoundedMeasurableFacts) : ReflectionPositivityAtLink := by
  intro D C
  obtain ⟨hA, -, hE⟩ := hS D
  obtain ⟨-, hco, hhalf, hrel, -, hdc, hind⟩ := hD D C
  obtain ⟨ho, -, hks, hex⟩ := hK D C
  obtain ⟨hverts, -⟩ := hG D C
  obtain ⟨-, s, hs, -, hconf, -, -⟩ := hR D C
  obtain ⟨hi₁, hi₂⟩ := hI D C
  have H : LinkHypotheses C :=
    { product := hA
      energies := hE
      coords := hco
      slab := fun σ => (hhalf σ).1
      algebra := fun σ => (hhalf σ).2.1
      linear := fun σ => (hhalf σ).2.2
      transfer := hrel
      doubled := hdc
      independent := hind
      halfAction := ho
      kernelSum := hks
      series := hex
      verticesDisjoint := hverts.2.2.2.2.2.1
      integrand := hi₁
      reflected := hi₂
      symmetry := ⟨s, hs, fun U => (hconf.1 U.1 U.2).2.2⟩ }
  refine ⟨⟨countable_kernelWord H, fun γ => seriesWeight_pos H γ,
    fun γ a b F₁ h₁ F₂ h₂ =>
      ⟨linearCombination_mem H .pos a b h₁ h₂, transferFunctional_linear H γ a b h₁ h₂⟩,
    fun γ F hF => transferFunctional_norm_le H γ hF, fun F hF => ?_,
    fun F hF F' hF' => ⟨summable_norm_sumTerm H hF hF', hasSum_thetaForm H hF hF'⟩⟩,
    posHermitianFormOn_pos H, negHalfProperties_holds H⟩
  obtain ⟨hb, hm⟩ := (H.algebra .pos).1 F hF
  obtain ⟨hb', hm'⟩ := H.reflected F hb hm
  exact ⟨hb', hm'⟩
end YangMills.Construction.ReflectionPositivity.CutoffMirrors.LinkPositivity
end
