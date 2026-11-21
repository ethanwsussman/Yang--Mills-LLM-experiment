import YangMills.Construction.EuclideanFunctionals.ReconstructionOfASystem
import YangMills.Construction.SpectralTheory.FactsOnResolvedOperators
import YangMills.Construction.SpectralTheory.JointSpectralMeasuresGeneratorsAndCommutation
import YangMills.Construction.SpectralTheory.MeasuresIntegralsProductsImagesAndTransportOfAProjectionValuedMeasure
import YangMills.Construction.SpectralTheory.OperatorsAndMeasuresOfTheEarlierSettings
import Mathlib
set_option autoImplicit false
open MeasureTheory Set
noncomputable section
namespace YangMills.Construction.EuclideanFunctionals.ReconOfOSData
open DefinitionComparison
open BorelSpectral
open SpectralTheorem (spectralIntegralOp pushforwardToLine spectralMeasure)
open SettingsComparison
open ResolvedFacts (realSpectralIntegral)
open SelfAdjointFunctions (FullSpace)
open ResolvedOps (IsJointSpectralMeasure boxSet expComplex)
variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
def coordProj (i : Fin 4) (x : (FullSpace 4)) : ℝ := x.1 i
theorem measurable_coordProj (i : Fin 4) : Measurable (coordProj i) :=
  (measurable_pi_apply i).comp measurable_subtype_coe
def coordIntegral (μ : SpectralMeasure (FullSpace 4) H) (i : Fin 4) :
    HilbertSpaceBasics.UnboundedOp H :=
  realSpectralIntegral μ (coordProj i)
def toEuclideanSet (S : BorelSubsets (FullSpace 4)) : EuclideanSpectral.BorelSubset 4 :=
  ⟨{p | (⟨WithLp.ofLp p, mem_univ _⟩ : (FullSpace 4)) ∈ S.1},
    (Measurable.subtype_mk (MeasurableEquiv.toLp 2 (Fin 4 → ℝ)).symm.measurable) S.2⟩
theorem exists_isSameMeasure (hA : BorelSetMeasuresAgree H (FullSpace 4)) (hB : FullSpaceMeasuresAgree H 4)
    (ν : EuclideanSpectral.ProjMeasure H 4) :
    ∃ μ : SpectralMeasure (FullSpace 4) H, IsSameMeasure μ ν := by
  have hinv : ∀ T, toEuclideanSet (euclideanToCoords T) = T := fun T => Subtype.ext (by
    ext p
    simp [toEuclideanSet, euclideanToCoords])
  have hP : IsProjValuedBorelMeasure fun S : BorelSubsets (FullSpace 4) => ⇑(ν (toEuclideanSet S)) :=
    (hB.isProjValued_iff _).2 ⟨ν, fun T => by rw [hinv]⟩
  obtain ⟨μ, hμ⟩ := (hA.isProjValued_iff _).1 hP
  refine ⟨μ, fun T => ?_⟩
  have h := congrFun hμ (euclideanToCoords T)
  simp only [hinv] at h
  exact h.symm
theorem integralOp_pushforwardToLine (hCalc : SpectralMeasureCalculus.CalculusTheorem)
    (μ : SpectralMeasure (FullSpace 4) H) (f : (FullSpace 4) → ℝ) (hf : Measurable f) (φ : ℝ → ℂ)
    (hφ : Measurable φ) (M : ℝ) (hM : ∀ x, ‖φ x‖ ≤ M) :
    (pushforwardToLine μ f hf).integralOp (fun x => φ (x.1 0)) =
      μ.integralOp fun x => φ (f x) := by
  obtain ⟨-, -, -, -, hPush, -⟩ := hCalc H 4 (FullSpace 4) μ
  have hmap : Measurable fun x : (FullSpace 4) => (⟨fun _ => f x, mem_univ _⟩ : (univ : Set (Fin 1 → ℝ))) :=
    Measurable.subtype_mk (measurable_pi_iff.mpr fun _ => hf)
  have hcomp : Measurable fun x : (univ : Set (Fin 1 → ℝ)) => φ (x.1 0) :=
    hφ.comp ((measurable_pi_apply 0).comp measurable_subtype_coe)
  have h := hPush.integral_image le_rfl MeasurableSet.univ _ hmap _ hcomp
  ext v
  have hval := h.2 v (by
    rw [SpectralMeasure.integralDom_eq_univ _ (c := M) fun x => hM _]
    trivial)
  have a₁ := SpectralMeasure.integralApply_eq_integralOp (pushforwardToLine μ f hf)
    (g := fun x => φ (x.1 0)) (c := M) (fun x => hM _) v
  have a₂ := SpectralMeasure.integralApply_eq_integralOp μ
    (g := fun x => φ (f x)) (c := M) (fun x => hM _) v
  exact a₁.symm.trans (hval.trans a₂)
theorem spectralMeasure_coordIntegral (hDiag : ResolvedFacts.RealIntegralsDiagonalized H)
    (μ : SpectralMeasure (FullSpace 4) H) (i : Fin 4) :
    spectralMeasure (coordIntegral μ i) =
      pushforwardToLine μ (coordProj i) (measurable_coordProj i) :=
  ((hDiag 4 (FullSpace 4) μ ⟨0, mem_univ _⟩).1 _ (measurable_coordProj i)).2.1
theorem spectralMeasure_coordIntegral_realLineSet (hDiag : ResolvedFacts.RealIntegralsDiagonalized H)
    (μ : SpectralMeasure (FullSpace 4) H) (i : Fin 4) (S : BorelSubsets ℝ) :
    spectralMeasure (coordIntegral μ i) (realLineSet S) =
      μ ⟨{x | x.1 i ∈ S.1}, ((measurable_pi_apply i).comp measurable_subtype_coe) S.2⟩ := by
  rw [spectralMeasure_coordIntegral hDiag]
  rfl
theorem list_prod_ofFn_four {M : Type*} [Monoid M] (f : Fin 4 → M) :
    (List.ofFn f).prod = f 0 * (f 1 * (f 2 * f 3)) := by
  simp [List.ofFn_succ]
theorem isJointSpectralMeasure_coordIntegral (hDiag : ResolvedFacts.RealIntegralsDiagonalized H)
    (μ : SpectralMeasure (FullSpace 4) H) : IsJointSpectralMeasure (coordIntegral μ) μ := by
  intro S
  rw [list_prod_ofFn_four, spectralMeasure_coordIntegral_realLineSet hDiag,
    spectralMeasure_coordIntegral_realLineSet hDiag, spectralMeasure_coordIntegral_realLineSet hDiag,
    spectralMeasure_coordIntegral_realLineSet hDiag, ← μ.map_inter, ← μ.map_inter, ← μ.map_inter]
  congr 1
  refine Subtype.ext ?_
  ext x
  simp [boxSet, Fin.forall_fin_succ]
theorem hamMomFamily_coordIntegral (μ : SpectralMeasure (FullSpace 4) H) :
    hamMomFamily (coordIntegral μ 0) (fun a : Fin 3 => coordIntegral μ a.succ) =
      coordIntegral μ := by
  funext i
  refine Fin.cases rfl (fun a => rfl) i
theorem hamMomMeasure_coordIntegral
    (hDiag : ResolvedFacts.RealIntegralsDiagonalized H)
    (hJoint : ∀ (n : ℕ) (hn : 1 ≤ n) (T : Fin n → HilbertSpaceBasics.UnboundedOp H),
      (∀ i, ResolvedOps.IsDiagonalized (T i)) →
      (∀ a i, a ≠ i → ResolvedOps.StronglyCommute (T a) (T i)) →
      (∃! ρ : SpectralMeasure (univ : Set (Fin n → ℝ)) H, IsJointSpectralMeasure T ρ) ∧
      IsJointSpectralMeasure T (ResolvedOps.jointSpectralMeasure hn T))
    (μ : SpectralMeasure (FullSpace 4) H) :
    hamMomMeasure (coordIntegral μ 0) (fun a : Fin 3 => coordIntegral μ a.succ) =
      μ := by
  have hd := hDiag 4 (FullSpace 4) μ ⟨0, mem_univ _⟩
  have h := hJoint 4 (by norm_num) (coordIntegral μ)
    (fun i => (hd.1 _ (measurable_coordProj i)).1)
    (fun a i _ => hd.2 _ _ (measurable_coordProj a) (measurable_coordProj i))
  unfold hamMomMeasure
  rw [hamMomFamily_coordIntegral]
  exact h.1.unique h.2 (isJointSpectralMeasure_coordIntegral hDiag μ)
theorem expComplex_coordIntegral_eq (hCalc : SpectralMeasureCalculus.CalculusTheorem)
    (hDiag : ResolvedFacts.RealIntegralsDiagonalized H)
    (hB : FullSpaceMeasuresAgree H 4) (μ : SpectralMeasure (FullSpace 4) H)
    (ν : EuclideanSpectral.ProjMeasure H 4) (hμν : IsSameMeasure μ ν)
    (s : ℝ) (hs : 0 ≤ s) :
    ⇑(expComplex (coordIntegral μ 0) (s : ℂ)) = ⇑(semigroupOp ν s) := by
  let φ : ℝ → ℂ := (Ici (0 : ℝ)).indicator fun x => Complex.exp (-(s : ℂ) * (x : ℂ))
  have hφm : Measurable φ := Measurable.indicator (by fun_prop) measurableSet_Ici
  have hφb : ∀ x, ‖φ x‖ ≤ 1 := by
    intro x
    by_cases hx : x ∈ Ici (0 : ℝ)
    · have hx0 : (0 : ℝ) ≤ x := hx
      simp only [φ, indicator_of_mem hx]
      rw [Complex.norm_exp]
      have : (-(s : ℂ) * (x : ℂ)).re = -s * x := by simp
      rw [this, Real.exp_le_one_iff]
      nlinarith [mul_nonneg hs hx0]
    · simp [φ, indicator_of_notMem hx]
  have a₁ : expComplex (coordIntegral μ 0) (s : ℂ) =
      μ.integralOp fun x => φ (coordProj 0 x) := by
    rw [← integralOp_pushforwardToLine hCalc μ _ (measurable_coordProj 0) φ hφm 1 hφb,
      ← spectralMeasure_coordIntegral hDiag]
    rfl
  have hind : (nonnegEnergySet.1.indicator fun q => ((Real.exp (-s * energyCoord q) : ℝ) : ℂ)) =
      fun q => φ (energyCoord q) := by
    funext q
    by_cases hq : 0 ≤ energyCoord q
    · have m₁ : q ∈ nonnegEnergySet.1 := hq
      have m₂ : energyCoord q ∈ Ici (0 : ℝ) := hq
      simp only [φ, indicator_of_mem m₁, indicator_of_mem m₂]
      push_cast
      rfl
    · have m₁ : q ∉ nonnegEnergySet.1 := hq
      have m₂ : energyCoord q ∉ Ici (0 : ℝ) := hq
      simp only [φ, indicator_of_notMem m₁, indicator_of_notMem m₂]
  have a₂ := hB.integralOp_eq μ ν hμν (fun q => φ (energyCoord q))
    (hφm.comp measurable_energyCoord) ⟨1, fun q => hφb _⟩
  have a₃ : semigroupOp ν s = ν.boundedIntegral fun q => φ (energyCoord q) := by
    rw [← hind]
    rfl
  rw [a₁, a₃]
  exact a₂
theorem spatialTranslOp_eq_spatialShiftOp (hB : FullSpaceMeasuresAgree H 4)
    (μ : SpectralMeasure (FullSpace 4) H)
    (ν : EuclideanSpectral.ProjMeasure H 4) (hμν : IsSameMeasure μ ν)
    (a : R4) : ⇑(spatialTranslOp μ a) = ⇑(spatialShiftOp ν a) := by
  have hcont : Continuous fun q : MomSpace => spatialDot a q := by
    unfold spatialDot momCoord
    fun_prop
  have hmeas : Measurable fun q : MomSpace => Complex.exp (Complex.I * (spatialDot a q : ℂ)) :=
    (Complex.continuous_exp.comp (continuous_const.mul
      (Complex.continuous_ofReal.comp hcont))).measurable
  exact hB.integralOp_eq μ ν hμν _ hmeas ⟨1, fun q => by
    rw [Complex.norm_exp_I_mul_ofReal]⟩
def finCombToSpan : finCombIn upperHalf →ₗ[ℂ] freeSpanIn upperHalf :=
  Submodule.inclusion (finCombIn_eq_freeSpanIn upperHalf).le
omit [CompleteSpace H] in
theorem classOrZero_comp_finCombToSpan (q : freeSpanIn upperHalf →ₗ[ℂ] H) (Φ : FreeSep) :
    readClass (q ∘ₗ finCombToSpan) Φ = classOrZero q Φ := by
  unfold readClass classOrZero
  by_cases h : Φ ∈ freeSpanIn upperHalf
  · have h' : Φ ∈ finCombIn upperHalf := by
      rw [finCombIn_eq_freeSpanIn]
      exact h
    rw [dif_pos h, dif_pos h']
    rfl
  · have h' : Φ ∉ finCombIn upperHalf := by
      rw [finCombIn_eq_freeSpanIn]
      exact h
    rw [dif_neg h, dif_neg h']
theorem exists_corresponding_recon (hDF : ResolvedFacts.DiagonalizedFacts)
    (hJG : JointSpectralGenerators.JointMeasureGeneratorsCommutation)
    (hSet : AllSettingsAgree)
    (hCalc : SpectralMeasureCalculus.CalculusTheorem) {𝒜 : ConnFamily}
    (d : OSData H 𝒜) :
    ∃ R : OSReconstruction H 𝒜, Corresponds R d := by
  obtain ⟨hBdd, -, hBor, hFull, -, -⟩ := hSet H
  obtain ⟨-, -, -, -, -, hDiag, -⟩ := hDF H
  have hB : FullSpaceMeasuresAgree H 4 := hFull 4
  obtain ⟨μ, hμν⟩ := exists_isSameMeasure
    (hBor 4 (FullSpace 4) (by norm_num) MeasurableSet.univ ⟨0, mem_univ _⟩) hB d.pvm
  obtain ⟨-, -, -, -, -, -, hRe, -⟩ := hCalc H 4 (FullSpace 4) μ
  have hJoint := fun (n : ℕ) (hn : 1 ≤ n) (T : Fin n → HilbertSpaceBasics.UnboundedOp H)
      (t₁ : ∀ i, ResolvedOps.IsDiagonalized (T i))
      (t₂ : ∀ a i, a ≠ i → ResolvedOps.StronglyCommute (T a) (T i)) =>
    (And.intro ((hJG H).1 n hn T t₁ t₂).1 ((hJG H).1 n hn T t₁ t₂).2.1)
  have hd := hDiag 4 (FullSpace 4) μ ⟨0, mem_univ _⟩
  have hcm : ∀ i, Measurable fun x : (FullSpace 4) => ((coordProj i x : ℝ) : ℂ) := fun i =>
    Complex.measurable_ofReal.comp (measurable_coordProj i)
  have hsa : ∀ i, OperatorTransport.IsSelfAdjointUnbounded (coordIntegral μ i) := fun i =>
    hRe.isSelfAdjoint _ (hcm i) fun x => Complex.ofReal_im _
  have hsc : ∀ a i, ResolvedOps.StronglyCommute (coordIntegral μ a)
      (coordIntegral μ i) := fun a i =>
    hd.2 _ _ (measurable_coordProj a) (measurable_coordProj i)
  have hnegz : μ (euclideanToCoords negEnergySet) = 0 := by
    apply DFunLike.coe_injective
    rw [← hμν negEnergySet, d.pvm_negEnergy]
    rfl
  have hcar : μ.IsCarriedBy (euclideanToCoords nonnegEnergySet) := by
    have : (⟨(euclideanToCoords nonnegEnergySet).1ᶜ, (euclideanToCoords nonnegEnergySet).2.compl⟩ :
        BorelSubsets (FullSpace 4)) = euclideanToCoords negEnergySet := Subtype.ext (by
      ext x
      simp [euclideanToCoords, nonnegEnergySet, negEnergySet])
    unfold SpectralMeasure.IsCarriedBy
    rw [this, hnegz]
  have hpos : OperatorTransport.IsNonnegUnbounded (coordIntegral μ 0) :=
    hRe.isNonnegative _ (euclideanToCoords nonnegEnergySet) (hcm 0)
      (fun x => Complex.ofReal_im _) hcar fun x hx => Complex.zero_le_real.2 hx
  have hHM := hamMomMeasure_coordIntegral hDiag hJoint μ
  have hU : ∀ g, OperatorTransport.IsUnitaryMap (d.rotOp g) := by
    intro g
    have hu := hBdd.unitary_iff ⇑(d.rotOp g)
    obtain ⟨W, hW, hWu⟩ := hu.1.2 (hu.2.2 ⟨_, rfl, d.rotOp_unitary g⟩)
    obtain rfl : W = d.rotOp g := DFunLike.coe_injective hW
    exact hWu
  have hE := expComplex_coordIntegral_eq hCalc hDiag hB μ d.pvm hμν
  have hT := spatialTranslOp_eq_spatialShiftOp hB μ d.pvm hμν
  have hT' : ∀ a, ⇑(spatialTranslOp (hamMomMeasure (coordIntegral μ 0)
      (fun b : Fin 3 => coordIntegral μ b.succ)) a) =
      ⇑(spatialShiftOp d.pvm a) := by
    intro a
    rw [hHM]
    exact hT a
  have hJM : IsJointSpectralMeasure (hamMomFamily (coordIntegral μ 0)
      (fun b : Fin 3 => coordIntegral μ b.succ))
      (hamMomMeasure (coordIntegral μ 0)
        (fun b : Fin 3 => coordIntegral μ b.succ)) := by
    rw [hHM, hamMomFamily_coordIntegral]
    exact isJointSpectralMeasure_coordIntegral hDiag μ
  have hSame : IsSameMeasure (hamMomMeasure (coordIntegral μ 0)
      (fun b : Fin 3 => coordIntegral μ b.succ)) d.pvm := by
    rw [hHM]
    exact hμν
  have hIn : ∀ X Y : finCombIn upperHalf,
      inner ℂ ((d.cls ∘ₗ finCombToSpan) X) ((d.cls ∘ₗ finCombToSpan) Y) =
        osForm 𝒜 X.1 Y.1 := fun X Y => d.inner_cls _ _
  refine ⟨{ cls := d.cls ∘ₗ finCombToSpan
            inner_cls := hIn
            denseRange_cls := d.denseRange_cls.mono ?_
            ham := coordIntegral μ 0
            ham_selfAdjoint := hsa 0
            ham_nonneg := hpos
            mom := fun b => coordIntegral μ b.succ
            mom_selfAdjoint := fun b => hsa _
            mom_commute := fun a b _ => hsc _ _
            mom_commute_ham := fun b => hsc _ _
            rotOp := d.rotOp
            rotOp_unitary := hU
            expHam_cls := ?_
            transl_cls := ?_
            rotOp_cls := ?_ }, ?_⟩
  · rintro _ ⟨X, rfl⟩
    refine ⟨⟨X.1, ?_⟩, rfl⟩
    rw [finCombIn_eq_freeSpanIn]
    exact X.2
  · intro s hs X
    rw [classOrZero_comp_finCombToSpan, hE s hs]
    exact d.semigroup_cls s hs _
  · intro a ha X
    rw [classOrZero_comp_finCombToSpan]
    exact (congrFun (hT' a) _).trans (d.shift_cls a ha _)
  · intro g X
    rw [classOrZero_comp_finCombToSpan]
    exact d.rotOp_cls g _
  · refine
      { cls_eq := fun X => classOrZero_comp_finCombToSpan _ _
        isJointSpectralMeasure := hJM
        measure_eq := hSame
        rotOp_eq := fun g => rfl
        vac_eq := rfl
        ham_eq := ?_
        mom_eq := ?_
        exp_eq := hE
        spatial_eq := fun a _ => hT' a }
    · exact hB.spectralIntegralOp_eq μ d.pvm hμν energyFn
        (Complex.measurable_ofReal.comp measurable_energyCoord)
    · intro b
      refine hB.spectralIntegralOp_eq μ d.pvm hμν (fun q => (momCoord b q : ℂ)) ?_
      exact Complex.measurable_ofReal.comp
        ((EuclideanSpace.proj (𝕜 := ℝ) b.succ).continuous.measurable)
theorem holds (hDF : ResolvedFacts.DiagonalizedFacts)
    (hJG : JointSpectralGenerators.JointMeasureGeneratorsCommutation)
    (hSet : AllSettingsAgree)
    (hCalc : SpectralMeasureCalculus.CalculusTheorem) : Holds :=
  fun _ _ τ => exists_corresponding_recon hDF hJG hSet hCalc τ.osData
end YangMills.Construction.EuclideanFunctionals.ReconOfOSData
