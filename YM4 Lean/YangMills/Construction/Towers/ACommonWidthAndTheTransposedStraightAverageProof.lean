import YangMills.Construction.PeriodicOperators.IndexSetsOfATower
import YangMills.Construction.PeriodicOperators.LocalOperatorFunctionsAndTheirJets
import YangMills.Construction.PeriodicOperators.SymbolsOnStrips
import YangMills.Construction.Towers.ACommonWidthAndTheTransposedStraightAverage
import YangMills.Construction.Towers.CovariantAveragesAsDifferentialsProof
import YangMills.Construction.Towers.IndexSetsArePeriodic
import YangMills.Construction.Towers.StraightAverageOnTheFormsOfTheWholeLattice
import YangMills.Construction.Towers.TheFreeOperatorsArePeriodicOperators
import YangMills.Construction.Towers.TheTwoOperatorFunctions
import YangMills.Construction.Towers.TransposesAndRelationsOfTheScaledPicture
import YangMills.Construction.Towers.TransposesBetweenFormsOfTheWholeLattice
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.Tower.FullSpace.JointWidthProof
open YangMills.Construction.PeriodicOperators
open YangMills.Construction.Tower.LeftChartFields
theorem isPeriodic_disjSum {I I' : PeriodicData} (h : IsPeriodic I)
    (h' : IsPeriodic I') : IsPeriodic (I.disjSum I') where
  translate_zero x := by
    cases x with
    | inl i => exact congrArg Sum.inl (h.translate_zero i)
    | inr i => exact congrArg Sum.inr (h'.translate_zero i)
  translate_add a b x := by
    cases x with
    | inl i => exact congrArg Sum.inl (h.translate_add a b i)
    | inr i => exact congrArg Sum.inr (h'.translate_add a b i)
  free a x hx := by
    cases x with
    | inl i => exact h.free a i (Sum.inl.inj hx)
    | inr i => exact h'.free a i (Sum.inr.inj hx)
  finite_quot := by
    have := h.finite_quot
    have := h'.finite_quot
    let g : I.UnitQuot ⊕ I'.UnitQuot → (I.disjSum I').UnitQuot := Sum.elim
      (Quot.lift (fun i => (I.disjSum I').mkQuot 1 (Sum.inl i)) (by
        rintro i _ ⟨a, rfl⟩
        exact Quot.sound ⟨a, rfl⟩))
      (Quot.lift (fun i => (I.disjSum I').mkQuot 1 (Sum.inr i)) (by
        rintro i _ ⟨a, rfl⟩
        exact Quot.sound ⟨a, rfl⟩))
    refine Finite.of_surjective g fun c => ?_
    induction c using Quot.ind with
    | mk x =>
      cases x with
      | inl i => exact ⟨Sum.inl (I.mkQuot 1 i), rfl⟩
      | inr i => exact ⟨Sum.inr (I'.mkQuot 1 i), rfl⟩
  pos_translate a x := by
    cases x with
    | inl i => exact h.pos_translate a i
    | inr i => exact h'.pos_translate a i
  finite_components := by
    have := h.finite_components
    have := h'.finite_components
    exact inferInstanceAs (Finite (I.Component ⊕ I'.Component))
  componentOf_translate a x := by
    cases x with
    | inl i => exact congrArg Sum.inl (h.componentOf_translate a i)
    | inr i => exact congrArg Sum.inr (h'.componentOf_translate a i)
  weight_pos c := by
    cases c with
    | inl q => exact h.weight_pos q
    | inr q => exact h'.weight_pos q
theorem hasInvertibleJetsAtWidth_of_le (hJ : JetDomains.OpFunJetTheory) {F I : PeriodicData}
    (hF : IsPeriodic F) (hI : IsPeriodic I)
    {T : (F.Carrier → ℂ) → I.Carrier → I.Carrier → ℂ} (hT : IsLocalOpFun F I I T)
    {δ₀ δ : ℝ} (hδ : 0 < δ) (hle : δ ≤ δ₀)
    (h₀ : ∀ p ∈ imStrip δ₀, ∀ εPlus εMinus : F.UnitQuot → ℂ,
      JetQuad.IsInvertibleJet δ₀ p (jetAlong F I I T p εPlus εMinus)) :
    HasInvertibleJetsAtWidth F I T δ := by
  have facts := hJ.2.1 F I I hF hI hI T hT
  refine ⟨hδ, fun p hp εPlus εMinus => ?_⟩
  have h := h₀ p (fun μ => (hp μ).trans hle) εPlus εMinus
  have hsub : imStrip (2 * δ) ⊆ imStrip (2 * δ₀) := fun κ hκ μ =>
    (hκ μ).trans (by linarith)
  exact
    { isJet := facts.isJet δ hδ p hp εPlus εMinus
      isUnit_f00 := fun κ hκ => h.isUnit_f00 κ (hsub hκ)
      bdd_inverse := lt_of_le_of_lt (biSup_mono hsub) h.bdd_inverse }
theorem isUnit_symbolHom {I : PeriodicData} {T : I.Carrier → I.Carrier → ℂ}
    (h : SymbolInvertibleOnReals I T) (κ : InfiniteLattice.AmbientSpace) :
    IsUnit (symbolHom I I T (toComplexVec κ) : Module.End ℂ (I.UnitQuot → ℂ)) := by
  have hκ : toComplexVec κ ∈ realDualPoints := fun j => by simp [toComplexVec]
  have hinv := h _ hκ
  rw [Module.End.isUnit_iff]
  constructor
  · intro f f' e
    obtain ⟨_, _, u⟩ := hinv (symbolHom I I T (toComplexVec κ) f)
    exact (u f rfl).trans (u f' e.symm).symm
  · intro g
    exact (hinv g).exists
theorem exists_jointWidth (hLog : LogDetSecondDerivs.Claim)
    (hJ : JetDomains.OpFunJetTheory) (hIdx : PeriodicOperators.TowerIndexSets.Claim)
    (hPer : LocalKernels.IndexSetPeriodicity.Statement)
    (hTwo : OperatorFunctions.OperatorFunctionsTheorem) {L k : ℕ} (hL : 0 < L)
    (hs : Conventions.IsAdmissibleBlockingFactor L) (hk : 1 ≤ k) :
    ∃ δ, IsJointInvertibilityWidth L k hL δ := by
  obtain ⟨⟨_, _, _, hv, hg⟩, -, hsv, hsg⟩ := hTwo L hL hs k hk
  have hF : IsPeriodic (fieldPeriodicData L k hL) :=
    ((hPer L hs k).2 (LocalKernels.fieldIndices L k hL)).1
  have hV : IsPeriodic (vectorIndices L k) :=
    isPeriodic_disjSum (hIdx L hs k 0 (Nat.zero_le k)).2.1 (hIdx L hs k k le_rfl).2.1
  have hG : IsPeriodic (ghostIndices L k) :=
    isPeriodic_disjSum (hIdx L hs k 0 (Nat.zero_le k)).1 (hIdx L hs k k le_rfl).1
  obtain ⟨δv, hδv, hv', -⟩ := hLog (fieldPeriodicData L k hL) (vectorIndices L k) hF hV
    (vectorOpFn L k hL) hv (fun κ => isUnit_symbolHom hsv κ)
  obtain ⟨δg, hδg, hg', -⟩ := hLog (fieldPeriodicData L k hL) (ghostIndices L k) hF hG
    (ghostOpFn L k hL) hg (fun κ => isUnit_symbolHom hsg κ)
  exact ⟨min δv δg,
    hasInvertibleJetsAtWidth_of_le hJ hF hV hv (lt_min hδv hδg) (min_le_left _ _) hv',
    hasInvertibleJetsAtWidth_of_le hJ hF hG hg (lt_min hδv hδg) (min_le_right _ _) hg'⟩
section Maps
variable {L k : ℕ}
theorem crossingSmoothingComplex_apply (hStr : StraightSmoothingOnForms)
    (hs : Conventions.IsAdmissibleBlockingFactor L) (hk : 1 ≤ k)
    (f : (fineFormSpace L k).complexSubmodule) :
    (crossingSmoothingComplex L k f : (coarseFormSpace L k).index → Matrices.ComplexMatrix2) =
      crossingSmoothingIter L k k f.1 := by
  obtain ⟨h₁, -, h₃, -⟩ := hStr L hs k k hk le_rfl
  have h₀ : crossingSmoothingIter L k k 0 = 0 := by
    have e := h₃ 0 (Submodule.zero_mem _) 0 (Submodule.zero_mem _) (-1)
    simpa using e
  have hadd : ∀ B ∈ complexEdgeForms (meshAt L k 0), ∀ B' ∈ complexEdgeForms (meshAt L k 0),
      crossingSmoothingIter L k k (B + B') =
        crossingSmoothingIter L k k B + crossingSmoothingIter L k k B' := by
    intro B hB B' hB'
    have e := h₃ B hB B' hB' 1
    rwa [one_smul, one_smul] at e
  have hsmul : ∀ (z : ℂ), ∀ B ∈ complexEdgeForms (meshAt L k 0),
      crossingSmoothingIter L k k (z • B) = z • crossingSmoothingIter L k k B := by
    intro z B hB
    have e := h₃ B hB 0 (Submodule.zero_mem _) z
    rwa [add_zero, h₀, add_zero] at e
  let A : (fineFormSpace L k).complexSubmodule →ₗ[ℂ] (coarseFormSpace L k).complexSubmodule :=
    { toFun := fun f => ⟨crossingSmoothingIter L k k f.1, h₁ f.1 f.2⟩
      map_add' := fun f g => Subtype.ext (hadd f.1 f.2 g.1 g.2)
      map_smul' := fun z f => Subtype.ext (hsmul z f.1 f.2) }
  exact Classical.epsilon_spec
    (p := fun T : (fineFormSpace L k).complexSubmodule →ₗ[ℂ]
        (coarseFormSpace L k).complexSubmodule =>
      ∀ f : (fineFormSpace L k).complexSubmodule,
        (T f : (coarseFormSpace L k).index → Matrices.ComplexMatrix2) =
          crossingSmoothingIter L k k f.1)
    ⟨A, fun _ => rfl⟩ f
theorem crossingSmoothingTranspose_eq (hStr : StraightSmoothingOnForms)
    (hs : Conventions.IsAdmissibleBlockingFactor L) (hk : 1 ≤ k) :
    crossingSmoothingTranspose L k =
      PauliComponentsOfSymmetricKernel.transposeOnCoeffs (edgePauliCoordinates L k 0) (edgePauliCoordinates L k k)
        (iterCovariantDeriv L k (fun _ => 1) k) := by
  obtain ⟨-, -, -, h₄⟩ := hStr L hs k k hk le_rfl
  have e : PairedFunctionSpace.linearOfValues (fineFormSpace L k) (coarseFormSpace L k)
        (crossingSmoothingIter L k k) =
      PairedFunctionSpace.linearOfValues (fineFormSpace L k) (coarseFormSpace L k)
        (iterCovariantDeriv L k (fun _ => 1) k) := by
    unfold PairedFunctionSpace.linearOfValues
    congr 1
    funext T
    refine propext (forall_congr' fun f => ?_)
    rw [h₄ f.1 f.2]
  have e₂ : PairedFunctionSpace.transposeOfValues (fineFormSpace L k) (coarseFormSpace L k)
        (crossingSmoothingIter L k k) =
      PairedFunctionSpace.transposeOfValues (fineFormSpace L k) (coarseFormSpace L k)
        (iterCovariantDeriv L k (fun _ => 1) k) := by
    funext g
    unfold PairedFunctionSpace.transposeOfValues
    rw [e]
  unfold crossingSmoothingTranspose PauliComponentsOfSymmetricKernel.transposeOnCoeffs
  exact congrArg (PauliComponentsOfSymmetricKernel.mapOnCoeffs (edgePauliCoordinates L k k) (edgePauliCoordinates L k 0)) e₂
def cubedMeshTranspose (L k : ℕ) :
    (colourEdges L k 0).Carrier → (colourEdges L k k).Carrier → ℂ :=
  fun x x' => ((finestMesh L k : ℂ) ^ 3) * (rescaledOperators L k fun _ => 1).Qt x x'
theorem finestMesh_ne_zero (hs : Conventions.IsAdmissibleBlockingFactor L) :
    (finestMesh L k : ℂ) ≠ 0 := by
  have hL : (0 : ℝ) < L := by
    have := hs.2
    exact_mod_cast (by omega : 0 < L)
  exact_mod_cast (zpow_pos hL _).ne'
theorem represents_cubedMeshTranspose (hS : RescaledConditions.Holds)
    (hStr : StraightSmoothingOnForms)
    (hs : Conventions.IsAdmissibleBlockingFactor L) (hk : 1 ≤ k) :
    Represents (cubedMeshTranspose L k) (crossingSmoothingTranspose L k) := by
  have h := (hS L hs k hk).2
  have hg := (h.2.2.1 _ h.2.2.2.1).1.2.1
  rw [← crossingSmoothingTranspose_eq hStr hs hk] at hg
  have hc := finestMesh_ne_zero (L := L) (k := k) hs
  intro f
  obtain ⟨h₁, h₂⟩ := hg f
  refine ⟨fun x => ?_, ?_⟩
  · have e := (h₁ x).mul_left ‖(finestMesh L k : ℂ) ^ 3‖
    refine e.congr fun i => ?_
    simp only [cubedMeshTranspose, norm_mul, mul_assoc]
    rfl
  · funext x
    have e : applyKernel (rescaledOperators L k fun _ => 1).Qt f x =
        ((finestMesh L k : ℂ) ^ 3)⁻¹ * crossingSmoothingTranspose L k f x := congrFun h₂ x
    change ∑' i, ((finestMesh L k : ℂ) ^ 3 * (rescaledOperators L k fun _ => 1).Qt x i) * f i = _
    simp_rw [mul_assoc]
    rw [tsum_mul_left]
    change (finestMesh L k : ℂ) ^ 3 * applyKernel (rescaledOperators L k fun _ => 1).Qt f x = _
    rw [e]
    field_simp
theorem transposeKernel_eq (hS : RescaledConditions.Holds)
    (hStr : StraightSmoothingOnForms)
    (hKer : ThreeMapKernels.Claim)
    (hs : Conventions.IsAdmissibleBlockingFactor L) (hk : 1 ≤ k) :
    crossingSmoothingTransposeKernel L k = cubedMeshTranspose L k := by
  have hg := represents_cubedMeshTranspose hS hStr hs hk
  have hE : Represents (crossingSmoothingTransposeKernel L k) (crossingSmoothingTranspose L k) :=
    Classical.epsilon_spec (p := fun T => Represents T (crossingSmoothingTranspose L k)) ⟨_, hg⟩
  exact ((hKer L hs k hk).2.1 k 0 le_rfl (Nat.zero_le k)).2.2.2 _ _ _ hE hg
theorem norm_exp_I_bilinDot_le {υ : ℝ} {κ : Fin 4 → ℂ} (hκ : κ ∈ imStrip υ)
    (y : InfiniteLattice.AmbientSpace) :
    ‖Complex.exp (Complex.I * bilinDot κ (toComplexVec y))‖ ≤ Real.exp (υ * ∑ μ, |y μ|) := by
  rw [Complex.norm_exp]
  refine Real.exp_le_exp.2 ?_
  have e : (Complex.I * bilinDot κ (toComplexVec y)).re = ∑ μ, -((κ μ).im * y μ) := by
    simp [bilinDot, toComplexVec, Complex.mul_re, Complex.mul_im, Complex.re_sum, Complex.im_sum]
  rw [e, Finset.mul_sum]
  refine Finset.sum_le_sum fun μ _ => ?_
  have h₁ : |(κ μ).im * y μ| ≤ υ * |y μ| := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_right (hκ μ) (abs_nonneg _)
  exact (neg_le_abs _).trans h₁
theorem transposeKernelProps (hCov : CovariantFiniteRange.Claim)
    (hStrips : StripSymbols.Claim) (hIdx : PeriodicOperators.TowerIndexSets.Claim)
    (hFree : FreeOperators.FreeOperatorsArePeriodic) (hS : RescaledConditions.Holds)
    (hStr : StraightSmoothingOnForms)
    (hKer : ThreeMapKernels.Claim)
    (hs : Conventions.IsAdmissibleBlockingFactor L) (hk : 1 ≤ k) : TransposeKernelProps L k := by
  have hE := transposeKernel_eq hS hStr hKer hs hk
  have hg := represents_cubedMeshTranspose hS hStr hs hk
  have hI : IsPeriodic (colourEdges L k k) := (hIdx L hs k k le_rfl).2.1
  have hI' : IsPeriodic (colourEdges L k 0) := (hIdx L hs k 0 (Nat.zero_le k)).2.1
  obtain ⟨⟨hcovQ, -⟩, ⟨ϱ, hϱ⟩, -⟩ := ((hFree.2 L hs k hk).2).edgeAverage_transpose
  have hcov : IsPhaseCovariant (colourEdges L k k) (colourEdges L k 0) 0
      (cubedMeshTranspose L k) := by
    intro a x' x
    have e := hcovQ a x' x
    simp only [bilinDot, Pi.zero_apply, zero_mul, Finset.sum_const_zero, mul_zero,
      Complex.exp_zero, one_mul]
    exact congrArg (fun z => (finestMesh L k : ℂ) ^ 3 * z) e
  have hvan : VanishesOutsideRadius (colourEdges L k k) (colourEdges L k 0) ϱ
      (cubedMeshTranspose L k) := by
    intro x' x h
    have e := hϱ x' x h
    exact (congrArg (fun z => (finestMesh L k : ℂ) ^ 3 * z) e).trans (mul_zero _)
  have hrem : dephasedKernel (colourEdges L k k) (colourEdges L k 0) 0
      (cubedMeshTranspose L k) = cubedMeshTranspose L k := by
    funext x' x
    simp [dephasedKernel, bilinDot]
  obtain ⟨hop, hexp, hent, hact⟩ := hCov.2 _ _ hI hI' 0 ϱ (cubedMeshTranspose L k) hcov hvan
  rw [hrem] at hop hexp hent
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hE]
    exact hg
  · rw [hE]
    exact hop.periodic
  · rw [hE]
    exact hop.finiteRange
  · rw [hE]
    exact ⟨hop.summable, fun x' x => ⟨by norm_num, hent x' x⟩⟩
  · intro υ _
    rw [hE]
    rintro ⟨c', c⟩
    obtain ⟨x', rfl⟩ := Quot.exists_rep c'
    obtain ⟨x, rfl⟩ := Quot.exists_rep c
    obtain ⟨m, a, y, hsum⟩ := hexp x' x
    refine ⟨∑ j, ‖a j‖ * Real.exp (υ * ∑ μ, |y j μ|), fun κ hκ => ?_⟩
    have hfacts := (hStrips.2.1 _ _ hI hI').2.1 (cubedMeshTranspose L k) κ hop.periodic
      (hop.summable κ (mem_univ _))
    have he : quotHomEntries (symbolHom (colourEdges L k k) (colourEdges L k 0)
        (cubedMeshTranspose L k) κ) (Quot.mk _ x', Quot.mk _ x) =
        fourierSymbol (colourEdges L k k) (colourEdges L k 0) (cubedMeshTranspose L k) κ x' x :=
      hfacts.carrierEntry_symbolHom x' x
    rw [he, hsum κ]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (norm_exp_I_bilinDot_le hκ (y j)) (norm_nonneg _)
  · intro κ φ x'
    rw [hE]
    obtain ⟨hfin, heq⟩ := hact κ φ x'
    rw [hrem, add_zero] at heq
    refine ⟨summable_of_hasFiniteSupport (hfin.subset fun i hi => ?_), heq⟩
    simpa using hi
theorem ofReal_smul_eq {α : Type} (r : ℝ) (X : α → Matrices.ComplexMatrix2) :
    (r : ℂ) • X = r • X := by apply _root_.YangMills.Construction.Tower.AsDifferentials.ofReal_smul_pi <;> assumption
theorem complexProps (hTr : EdgeFormTransposes)
    (hS : RescaledConditions.Holds)
    (hStr : StraightSmoothingOnForms)
    (hKer : ThreeMapKernels.Claim)
    (hs : Conventions.IsAdmissibleBlockingFactor L) (hk : 1 ≤ k) :
    CrossingSmoothingComplexProps L k := by
  have hvals := crossingSmoothingComplex_apply hStr hs hk
  obtain ⟨-, -, -, h₄⟩ := hStr L hs k k hk le_rfl
  have hOne := (hS L hs k hk).2.2.2.2.1
  have hfin : PairedFunctionSpace.PreservesFiniteSupport (crossingSmoothingComplex L k) := by
    intro f hf
    have e := ((hKer L hs k hk).2.2.2.2 _ hOne).1.finitely_supported f.1 f.2 hf
    rw [h₄ f.1 f.2, ← hvals f] at e
    exact e
  obtain ⟨T', hT', -⟩ := (hTr L k 0 k hs (Nat.zero_le k) le_rfl).1 _ hfin
  exact ⟨hvals, hfin,
    Classical.epsilon_spec (p := PairedFunctionSpace.IsTransposeMap _) ⟨T', hT'⟩⟩
theorem realProps (hTr : EdgeFormTransposes)
    (hS : RescaledConditions.Holds)
    (hStr : StraightSmoothingOnForms)
    (hKer : ThreeMapKernels.Claim)
    (hs : Conventions.IsAdmissibleBlockingFactor L) (hk : 1 ≤ k) :
    CrossingSmoothingRealProps L k := by
  have hC := complexProps hTr hS hStr hKer hs hk
  obtain ⟨-, h₂, h₃, -⟩ := hStr L hs k k hk le_rfl
  have hle : ∀ {j : ℕ} {x : Edge L k j → Matrices.ComplexMatrix2}, x ∈ edgeFormSpace (meshAt L k j) →
      x ∈ complexEdgeForms (meshAt L k j) := fun hx => ⟨fun b hb => (hx.1 b hb).2, hx.2⟩
  have h₀ : crossingSmoothingIter L k k 0 = 0 := by
    have e := h₃ 0 (Submodule.zero_mem _) 0 (Submodule.zero_mem _) (-1)
    simpa using e
  have hadd : ∀ B ∈ complexEdgeForms (meshAt L k 0), ∀ B' ∈ complexEdgeForms (meshAt L k 0),
      crossingSmoothingIter L k k (B + B') =
        crossingSmoothingIter L k k B + crossingSmoothingIter L k k B' := by
    intro B hB B' hB'
    have e := h₃ B hB B' hB' 1
    rwa [one_smul, one_smul] at e
  have hsmul : ∀ (z : ℂ), ∀ B ∈ complexEdgeForms (meshAt L k 0),
      crossingSmoothingIter L k k (z • B) = z • crossingSmoothingIter L k k B := by
    intro z B hB
    have e := h₃ B hB 0 (Submodule.zero_mem _) z
    rwa [add_zero, h₀, add_zero] at e
  have hsmulR : ∀ (r : ℝ), ∀ B ∈ edgeFormSpace (meshAt L k 0),
      crossingSmoothingIter L k k (r • B) = r • crossingSmoothingIter L k k B := by
    intro r B hB
    have e := hsmul (r : ℂ) B (hle hB)
    rwa [ofReal_smul_eq, ofReal_smul_eq] at e
  let A : (fineFormSpace L k).realSubmodule →ₗ[ℝ] (coarseFormSpace L k).realSubmodule :=
    { toFun := fun f => ⟨crossingSmoothingIter L k k f.1, h₂ f.1 f.2⟩
      map_add' := fun f g => Subtype.ext (hadd f.1 (hle f.2) g.1 (hle g.2))
      map_smul' := fun r f => Subtype.ext (hsmulR r f.1 f.2) }
  have hvals : ∀ f : (fineFormSpace L k).realSubmodule,
      (crossingSmoothingReal L k f : (coarseFormSpace L k).index → Matrices.ComplexMatrix2) =
        crossingSmoothingIter L k k f.1 :=
    Classical.epsilon_spec
      (p := fun T : (fineFormSpace L k).realSubmodule →ₗ[ℝ]
          (coarseFormSpace L k).realSubmodule =>
        ∀ f : (fineFormSpace L k).realSubmodule,
          (T f : (coarseFormSpace L k).index → Matrices.ComplexMatrix2) =
            crossingSmoothingIter L k k f.1)
      ⟨A, fun _ => rfl⟩
  have hfin : PairedFunctionSpace.PreservesRealFiniteSupport (crossingSmoothingReal L k) := by
    intro f hf
    have e := hC.finite_support ⟨f.1, hle f.2⟩ hf
    rw [hC.values] at e
    rw [hvals]
    exact e
  have hTR : PairedFunctionSpace.AdmitsRealTransposes (fineFormSpace L k) (coarseFormSpace L k) :=
    (hTr L k 0 k hs (Nat.zero_le k) le_rfl).2
  have hsplit := hTR.1
  obtain ⟨hcont, -, -, hrt, -, -⟩ := hTR.2 (crossingSmoothingReal L k) hfin
  refine ⟨hvals, hfin, hrt, fun g => ?_⟩
  have hg : g.1 ∈ (coarseFormSpace L k).complexSubmodule := hle g.2
  have e : PairedFunctionSpace.complexification (crossingSmoothingReal L k) =
      crossingSmoothingComplex L k := by
    refine LinearMap.ext fun h => Subtype.ext ?_
    obtain ⟨⟨p, q⟩, hp, -⟩ := hsplit h
    refine (hcont p q h hp).trans ?_
    have e₁ : ((crossingSmoothingReal L k p).1 : Edge L k k → Matrices.ComplexMatrix2) =
        crossingSmoothingIter L k k p.1 := hvals p
    have e₂ : ((crossingSmoothingReal L k q).1 : Edge L k k → Matrices.ComplexMatrix2) =
        crossingSmoothingIter L k k q.1 := hvals q
    have e₃ : ((crossingSmoothingComplex L k h).1 : Edge L k k → Matrices.ComplexMatrix2) =
        crossingSmoothingIter L k k h.1 := hC.values h
    have hh : (h.1 : Edge L k 0 → Matrices.ComplexMatrix2) =
        Complex.I • (q.1 : Edge L k 0 → Matrices.ComplexMatrix2) +
          (p.1 : Edge L k 0 → Matrices.ComplexMatrix2) :=
      hp.trans (add_comm _ _)
    have key : ∀ P ∈ edgeFormSpace (meshAt L k 0), ∀ Q ∈ edgeFormSpace (meshAt L k 0),
        crossingSmoothingIter L k k P + Complex.I • crossingSmoothingIter L k k Q =
          crossingSmoothingIter L k k (Complex.I • Q + P) := by
      intro P hP Q hQ
      rw [h₃ Q (hle hQ) P (hle hP) Complex.I, add_comm]
    change ((crossingSmoothingReal L k p).1 : Edge L k k → Matrices.ComplexMatrix2) +
        Complex.I • ((crossingSmoothingReal L k q).1 : Edge L k k → Matrices.ComplexMatrix2) =
      ((crossingSmoothingComplex L k h).1 : Edge L k k → Matrices.ComplexMatrix2)
    rw [e₁, e₂, e₃, hh]
    exact key p.1 p.2 q.1 q.2
  have r : (PairedFunctionSpace.realTransposeMap (crossingSmoothingReal L k) g :
      (fineFormSpace L k).index → Matrices.ComplexMatrix2) =
      PairedFunctionSpace.transposeMap
        (PairedFunctionSpace.complexification (crossingSmoothingReal L k)) ⟨g.1, hg⟩ :=
    hrt g ⟨g.1, hg⟩ rfl
  rw [e] at r
  unfold PairedFunctionSpace.transposeOfValues
  rw [dif_pos hg]
  exact r.symm
end Maps
theorem jointWidthAndTranspose (hLog : LogDetSecondDerivs.Claim)
    (hJ : JetDomains.OpFunJetTheory)
    (hCov : CovariantFiniteRange.Claim) (hStrips : StripSymbols.Claim)
    (hIdx : PeriodicOperators.TowerIndexSets.Claim)
    (hPer : LocalKernels.IndexSetPeriodicity.Statement)
    (hKer : ThreeMapKernels.Claim) (hFree : FreeOperators.FreeOperatorsArePeriodic)
    (hTwo : OperatorFunctions.OperatorFunctionsTheorem)
    (hS : RescaledConditions.Holds)
    (hTr : EdgeFormTransposes)
    (hStr : StraightSmoothingOnForms) : JointWidthAndTransposeTheorem := by
  intro L hL hs k hk
  exact ⟨Classical.epsilon_spec (p := IsJointInvertibilityWidth L k hL)
      (exists_jointWidth hLog hJ hIdx hPer hTwo hL hs hk),
    complexProps hTr hS hStr hKer hs hk,
    transposeKernelProps hCov hStrips hIdx hFree hS hStr hKer hs hk,
    realProps hTr hS hStr hKer hs hk⟩
end YangMills.Construction.Tower.FullSpace.JointWidthProof
end
