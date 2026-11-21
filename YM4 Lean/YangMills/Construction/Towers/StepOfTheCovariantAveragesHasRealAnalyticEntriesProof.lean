import YangMills.Construction.Towers.AveragingOnSmallFamiliesOfTheChartAtOneProof
import YangMills.Construction.Lattice.ContourVariableAtTheCentreOfABlock
import YangMills.Construction.Matrices.LogarithmicChartsOfASpaceOfConfigurationsProof
import YangMills.Construction.Towers.CovariantAveragesAsDifferentials
import YangMills.Construction.Towers.EntriesOfTheSaddleOperatorAreRealAnalyticNearOneProof
import YangMills.Construction.Towers.StepOfTheCovariantAveragesHasRealAnalyticEntries
import Mathlib
set_option autoImplicit false
open Set Filter
open scoped Topology Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction
open YangMills.Construction.Matrices
namespace Tower
namespace StepAnalyticEntries
open YangMills.Construction.Matrices.GroupLieProduct YangMills.Construction.Matrices.GroupLieProduct.Subspaces
private theorem exists_analytic_germ {R : Type} [Fintype R] {D : Set (R → ComplexMatrix2)}
    {G : (R → ComplexMatrix2) → ComplexMatrix2}
    (hG : ComplexMatrix2.IsRealAnalyticBetween (fun _ : R => ComplexMatrix2.FactorKind.group)
      (fun _ : Fin 1 => ComplexMatrix2.FactorKind.group) D fun v _ => G v)
    {x : R → ComplexMatrix2} (hx : x ∈ D) :
    ∃ (O : Set (R → ComplexMatrix2)) (F : (R → ComplexMatrix2) → ComplexMatrix2), IsOpen O ∧ x ∈ O ∧
      AnalyticOnNhd ℂ F O ∧ (∀ y ∈ O ∩ D, G y = F y) ∧
      ∀ y ∈ O, y ∈ ComplexMatrix2.complexifiedProduct (fun _ : R => ComplexMatrix2.FactorKind.group) →
        F y ∈ ComplexMatrix2.unitDeterminant := by
  obtain ⟨⟨OD, hOD, rfl⟩, hloc⟩ := hG
  obtain ⟨W, h, hxW, hW, hfh⟩ := hloc x hx
  obtain ⟨⟨OW, hOW, rfl⟩, hmaps, hF⟩ := hW
  obtain ⟨F, hFa, hFe⟩ := hF x hxW
  obtain ⟨U₁, hU₁, hxU₁, hfU₁⟩ := mem_nhdsWithin.1 hfh
  obtain ⟨U₂, hU₂, hxU₂, hFU₂⟩ := mem_nhdsWithin.1 hFe
  obtain ⟨U₃, hU₃sub, hU₃, hxU₃⟩ := mem_nhds_iff.1 hFa.eventually_analyticAt
  refine ⟨U₁ ∩ U₂ ∩ U₃ ∩ OW, fun y => F y 0, ((hU₁.inter hU₂).inter hU₃).inter hOW,
    ⟨⟨⟨hxU₁, hxU₂⟩, hxU₃⟩, hxW.1⟩, fun y hy => ?_, ?_, ?_⟩
  · exact ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 1 => ComplexMatrix2) 0).analyticAt _).comp
      (hU₃sub hy.1.2)
  · rintro y ⟨⟨⟨⟨hy₁, hy₂⟩, -⟩, hyW⟩, hyD⟩
    have hc : y ∈ ComplexMatrix2.complexifiedProduct fun _ : R => ComplexMatrix2.FactorKind.group := fun r =>
      (Matrix.mem_specialUnitaryGroup_iff.1 (hyD.2 r)).2
    have e₁ : (fun _ : Fin 1 => G y) = h y := hfU₁ ⟨hy₁, hyD⟩
    have e₂ : h y = F y := hFU₂ ⟨hy₂, hyW, hc⟩
    exact congrFun (e₁.trans e₂) 0
  · rintro y ⟨⟨⟨-, hy₂⟩, -⟩, hyW⟩ hc
    have e₂ : h y = F y := hFU₂ ⟨hy₂, hyW, hc⟩
    have hm := hmaps (show y ∈ OW ∩ _ from ⟨hyW, hc⟩) 0
    rw [e₂] at hm
    exact hm
private def familyEntriesEquiv {σ : Type} [Fintype σ] {k : ℕ} (ν : σ ≃ Fin k) :
    (σ → ComplexMatrix2) ≃L[ℂ]
    Coordinates.ComplexCoordinates
      (Coordinates.ComplexCoordinates.productDim
        fun _ : Fin k => Coordinates.ComplexCoordinates.Component.matrix) :=
  LinearEquiv.toContinuousLinearEquiv
    { matrixPiEquiv ν with
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
private theorem isHolomorphic_of_differentiableOn {R E : Type} [Fintype R] {l : ℕ}
    (hE : GroupLieProduct.ExpChartHolomorphy.ExpChartTheory) (e : E ≃ Coordinates.ComplexCoordinates l)
    {O : Set (R → ComplexMatrix2)} (hO : IsOpen O) {Φ : (R → ComplexMatrix2) → E}
    (hΦ : DifferentiableOn ℂ (fun v => e (Φ v)) O) :
    ComplexMatrix2.IsRelativelyOpen (GroupLieProduct R Empty)
        ((groupComponent ⁻¹' O : Set (R ⊕ Empty → ComplexMatrix2)) ∩ GroupLieProduct R Empty) ∧
      ∀ b : Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless,
        IsHolomorphicToCoords b e
          ((groupComponent ⁻¹' O : Set (R ⊕ Empty → ComplexMatrix2)) ∩ GroupLieProduct R Empty)
          fun q => Φ (groupComponent q) := by
  let ν : R ⊕ Empty ≃ Fin (Fintype.card (R ⊕ Empty)) := Fintype.equivFin _
  have hcont : Continuous (groupComponent : (R ⊕ Empty → ComplexMatrix2) → R → ComplexMatrix2) :=
    continuous_pi fun r => continuous_apply _
  have hdiff : Differentiable ℂ (groupComponent : (R ⊕ Empty → ComplexMatrix2) → R → ComplexMatrix2) :=
    differentiable_pi.2 fun r => differentiable_apply _
  have hO' : IsOpen (groupComponent ⁻¹' O : Set (R ⊕ Empty → ComplexMatrix2)) := hO.preimage hcont
  refine ((hE.2.2.2.1 R Empty).2.2) E l _ e ν _ _ ?_
  unfold Coordinates.ComplexCoordinates.IsHolomorphicVia
  have himg : matrixPiEquiv ν '' (groupComponent ⁻¹' O) =
      (familyEntriesEquiv ν).symm ⁻¹' (groupComponent ⁻¹' O) := by
    ext z
    constructor
    · rintro ⟨x, hx, rfl⟩
      have : (familyEntriesEquiv ν).symm (matrixPiEquiv ν x) = x :=
        (matrixPiEquiv ν).symm_apply_apply x
      simpa [this] using hx
    · intro hz
      exact ⟨(familyEntriesEquiv ν).symm z, hz, (matrixPiEquiv ν).apply_symm_apply z⟩
  have hfun : (e ∘ (fun q => Φ (groupComponent q)) ∘ (matrixPiEquiv ν).symm) =
      fun z => e (Φ (groupComponent ((familyEntriesEquiv ν).symm z))) := rfl
  rw [himg, hfun]
  have hopen : IsOpen ((familyEntriesEquiv ν).symm ⁻¹' (groupComponent ⁻¹' O)) :=
    hO'.preimage (familyEntriesEquiv ν).symm.continuous
  have hd : DifferentiableOn ℂ (fun z => e (Φ (groupComponent ((familyEntriesEquiv ν).symm z))))
      ((familyEntriesEquiv ν).symm ⁻¹' (groupComponent ⁻¹' O)) := fun z hz => by
    have h₁ : DifferentiableAt ℂ (fun v => e (Φ v)) (groupComponent ((familyEntriesEquiv ν).symm z)) :=
      hΦ.differentiableAt (hO.mem_nhds hz)
    have h₂ : DifferentiableAt ℂ (fun z => groupComponent ((familyEntriesEquiv ν).symm z)) z :=
      (hdiff _).comp z (familyEntriesEquiv ν).symm.differentiableAt
    exact (h₁.comp z h₂).differentiableWithinAt
  refine ⟨hopen, hd.continuousOn, fun a ha j => ?_⟩
  have hline : Continuous fun ζ : ℂ => a + ζ • Coordinates.ComplexCoordinates.stdBasisVector j := by
    fun_prop
  have hmem : ∀ᶠ ζ in 𝓝 (0 : ℂ), a + ζ • Coordinates.ComplexCoordinates.stdBasisVector j ∈
      (familyEntriesEquiv ν).symm ⁻¹' (groupComponent ⁻¹' O) :=
    hline.continuousAt.eventually_mem (by simpa using hopen.mem_nhds ha)
  filter_upwards [hmem] with ζ hζ
  have h2 : DifferentiableAt ℂ
      (fun ζ : ℂ => a + ζ • Coordinates.ComplexCoordinates.stdBasisVector j) ζ := by
    fun_prop
  exact DifferentiableAt.comp
    (f := fun ζ : ℂ => a + ζ • Coordinates.ComplexCoordinates.stdBasisVector j) ζ
    (hd.differentiableAt (hopen.mem_nhds hζ)) h2
section Fields
variable {L n k j : ℕ}
private theorem fieldOfPositiveValues_restrict {V : Edge L n k j → ComplexMatrix2}
    (hV : V ∈ fieldSpace L n k j) : fieldOfPositiveValues (restrictToPositiveEdges V) = V := by apply _root_.YangMills.SharedProofs.p407 <;> assumption
private theorem restrict_fieldOfPositiveValues
    (w : PositiveEdge L n k j → ComplexMatrix2) :
    restrictToPositiveEdges (fieldOfPositiveValues w) = w := by apply _root_.YangMills.SharedProofs.p777 <;> assumption
private theorem su2_inv_eq_conjTranspose {U : ComplexMatrix2}
    (hU : U ∈ (ComplexMatrix2.specialUnitary : Set ComplexMatrix2)) :
    U⁻¹ = U.conjTranspose := by
  have hU' := Matrix.mem_specialUnitaryGroup_iff.1 hU
  exact Matrix.inv_eq_right_inv (Matrix.mem_unitaryGroup_iff.1 hU'.1)
private theorem su2_inv_mem {U : ComplexMatrix2}
    (hU : U ∈ (ComplexMatrix2.specialUnitary : Set ComplexMatrix2)) :
    U⁻¹ ∈ (ComplexMatrix2.specialUnitary : Set ComplexMatrix2) := by apply _root_.YangMills.SharedProofs.p33390 <;> assumption
private theorem fieldOfPositiveValues_mem_fieldSpace {w : PositiveEdge L n k j → ComplexMatrix2}
    (hx : ∀ b : Edge L n k j, Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented)
    (hw : ∀ b, w b ∈ (ComplexMatrix2.specialUnitary : Set ComplexMatrix2)) :
    fieldOfPositiveValues w ∈ fieldSpace L n k j := by
  have hrr : ∀ b : Edge L n k j, b.opposite.opposite = b := fun b => PeriodicLattice.Bond.ext rfl rfl
  refine ⟨fun b _ => ?_, fun b _ => ?_⟩
  · by_cases hb : b.IsPositivelyOriented
    · simpa [fieldOfPositiveValues, hb] using hw ⟨b, hb⟩
    · have hb' := PeriodicLattice.Bond.opposite_isPositivelyOriented hb
      simpa [fieldOfPositiveValues, hb, hb'] using su2_inv_mem (hw ⟨b.opposite, hb'⟩)
  · by_cases hb : b.IsPositivelyOriented
    · have hb' : ¬ b.opposite.IsPositivelyOriented := by
        rcases hx b with h | h
        · exact h.2
        · exact absurd hb h.2
      have hb'' : b.opposite.opposite.IsPositivelyOriented := by rw [hrr]; exact hb
      simp [fieldOfPositiveValues, hb, hb', hrr]
    · have hb' := PeriodicLattice.Bond.opposite_isPositivelyOriented hb
      have hdet : (w ⟨b.opposite, hb'⟩).det = 1 :=
        (Matrix.mem_specialUnitaryGroup_iff.1 (hw ⟨b.opposite, hb'⟩)).2
      have hinv : ((w ⟨b.opposite, hb'⟩)⁻¹)⁻¹ = w ⟨b.opposite, hb'⟩ :=
        Matrix.nonsing_inv_nonsing_inv _ (by simp [hdet])
      simp [fieldOfPositiveValues, hb, hb', hinv]
private theorem exists_open_positive_representation {𝒰 : Set (Edge L n k j → ComplexMatrix2)}
    (h𝒰 : IsOpenFieldSet PeriodicLattice.compactGaugeGroup 𝒰) :
    ∃ O₀ : Set (PositiveEdge L n k j → ComplexMatrix2), IsOpen O₀ ∧
      {q : PositiveEdge L n k j ⊕ Empty → ComplexMatrix2 |
          fieldOfPositiveValues (groupComponent q) ∈ 𝒰} =
        groupComponent ⁻¹' O₀ ∩ subspaceTimesGroup ⊥ (PositiveEdge L n k j) := by
  obtain ⟨hsub, O₀, hO₀, hD⟩ := id h𝒰
  refine ⟨O₀, hO₀, ?_⟩
  ext q
  constructor
  · intro hq
    have hmem : groupComponent q ∈ restrictToPositiveEdges '' 𝒰 :=
      ⟨_, hq, restrict_fieldOfPositiveValues _⟩
    rw [hD] at hmem
    exact ⟨hmem.1, (Submodule.mem_bot ℝ).2 (Subsingleton.elim _ _), hmem.2⟩
  · rintro ⟨hq₀, -, hq₂⟩
    have hmem : groupComponent q ∈ restrictToPositiveEdges '' 𝒰 := by
      rw [hD]
      exact ⟨hq₀, hq₂⟩
    obtain ⟨U, hU, hUq⟩ := hmem
    change fieldOfPositiveValues (groupComponent q) ∈ 𝒰
    rw [← hUq, fieldOfPositiveValues_restrict (hsub hU)]
    exact hU
private theorem isAnalyticFieldFunction_of_local
    (hE : GroupLieProduct.ExpChartHolomorphy.ExpChartTheory)
    [inst : Fintype (PositiveEdge L n k j)] {𝒰 : Set (Edge L n k j → ComplexMatrix2)}
    (h𝒰 : IsOpenFieldSet PeriodicLattice.compactGaugeGroup 𝒰)
    {F : (Edge L n k j → ComplexMatrix2) → ℝ}
    (hg : ∀ V ∈ 𝒰, ∃ (O : Set (PositiveEdge L n k j → ComplexMatrix2))
      (Φ : (PositiveEdge L n k j → ComplexMatrix2) → ℂ), IsOpen O ∧ restrictToPositiveEdges V ∈ O ∧
        AnalyticOnNhd ℂ Φ O ∧
        ∀ W ∈ 𝒰, restrictToPositiveEdges W ∈ O → Φ (restrictToPositiveEdges W) = (F W : ℂ)) :
    IsAnalyticFieldFunction 𝒰 F := by
  obtain ⟨O₀, hO₀, hW⟩ := exists_open_positive_representation h𝒰
  have hcont : Continuous
      (groupComponent : (PositiveEdge L n k j ⊕ Empty → ComplexMatrix2) →
        PositiveEdge L n k j → ComplexMatrix2) :=
    continuous_pi fun r => continuous_apply _
  refine ⟨h𝒰, inst, ⟨bot_le, groupComponent ⁻¹' O₀, hO₀.preimage hcont, hW⟩, fun p hp => ?_⟩
  obtain ⟨O, Φ, hO, hxO, hΦ, hΦe⟩ := hg _ hp
  rw [restrict_fieldOfPositiveValues] at hxO
  have hd : DifferentiableOn ℂ
      (fun (v : PositiveEdge L n k j → ComplexMatrix2) (_ : Fin 1) => Φ v) (O ∩ O₀) :=
    differentiableOn_pi.2 fun _ => hΦ.differentiableOn.mono inter_subset_left
  obtain ⟨hX, hhol⟩ := isHolomorphic_of_differentiableOn hE
    (Equiv.refl (Coordinates.ComplexCoordinates 1)) (hO.inter hO₀) hd
  have hp' := hp
  rw [hW] at hp'
  refine ⟨groupComponent ⁻¹' (O ∩ O₀) ∩ GroupLieProduct (PositiveEdge L n k j) Empty,
    ⟨⟨hxO, hp'.1⟩, ?_⟩, hX, fun q hq => ?_, fun q _ => Φ (groupComponent q), hhol, ?_⟩
  · rintro (r | e)
    · exact (Matrix.mem_specialUnitaryGroup_iff.1 (hp'.2.2 r)).2
    · exact e.elim
  · rw [hW]
    exact ⟨hq.1.1.2, hq.2⟩
  · intro q hq
    have hqW : fieldOfPositiveValues (groupComponent q) ∈ 𝒰 := by
      have : q ∈ {q : PositiveEdge L n k j ⊕ Empty → ComplexMatrix2 |
          fieldOfPositiveValues (groupComponent q) ∈ 𝒰} := by
        rw [hW]
        exact ⟨hq.1.1.2, hq.2⟩
      exact this
    funext _
    have h := hΦe _ hqW (by rw [restrict_fieldOfPositiveValues]; exact hq.1.1.1)
    rw [restrict_fieldOfPositiveValues] at h
    exact h
private theorem isAnalyticFieldMap_of_constant
    (hE : GroupLieProduct.ExpChartHolomorphy.ExpChartTheory)
    [inst : Fintype (PositiveEdge L n k j)]
    (hx : ∀ b : Edge L n k j, Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented)
    {𝒰 : Set (Edge L n k j → ComplexMatrix2)}
    (h𝒰 : IsOpenFieldSet PeriodicLattice.compactGaugeGroup 𝒰)
    {C : (Edge L n k j → ComplexMatrix2) → ComplexMatrix2}
    (hC : ComplexMatrix2.IsRealAnalyticBetween
      (fun _ : PositiveEdge L n k j => ComplexMatrix2.FactorKind.group)
      (fun _ : Fin 1 => ComplexMatrix2.FactorKind.group) (restrictToPositiveEdges '' 𝒰)
      fun v _ => C (fieldOfPositiveValues v))
    (hmem : ∀ V ∈ 𝒰, C V ∈ (ComplexMatrix2.specialUnitary : Set ComplexMatrix2)) :
    IsAnalyticFieldMap 𝒰 fun V =>
      (fieldOfPositiveValues fun _ => C V : Edge L n k j → ComplexMatrix2) := by
  obtain ⟨O₀, hO₀, hW⟩ := exists_open_positive_representation h𝒰
  have hcont : Continuous
      (groupComponent : (PositiveEdge L n k j ⊕ Empty → ComplexMatrix2) →
        PositiveEdge L n k j → ComplexMatrix2) :=
    continuous_pi fun r => continuous_apply _
  refine ⟨h𝒰, fun V hV => fieldOfPositiveValues_mem_fieldSpace hx fun _ => hmem V hV, inst, inst,
    ⟨bot_le, groupComponent ⁻¹' O₀, hO₀.preimage hcont, hW⟩, bot_le, fun q hq => ?_,
    fun p hp => ?_⟩
  · refine ⟨(Submodule.mem_bot ℝ).2 (Subsingleton.elim _ _), fun r => ?_⟩
    change restrictToPositiveEdges (fieldOfPositiveValues fun _ => C _) r ∈
      (ComplexMatrix2.specialUnitary : Set ComplexMatrix2)
    rw [restrict_fieldOfPositiveValues]
    exact hmem _ hq
  · have hxD : groupComponent p ∈ restrictToPositiveEdges '' 𝒰 :=
      ⟨_, hp, restrict_fieldOfPositiveValues _⟩
    obtain ⟨O, F, hO, hxO, hF, hFe, hFg⟩ :=
      exists_analytic_germ (G := fun v => C (fieldOfPositiveValues v)) hC hxD
    have hd : DifferentiableOn ℂ
        (fun v => Coordinates.ComplexCoordinates.matrixEquiv (F v)) (O ∩ O₀) := by
      let ε : ComplexMatrix2 →L[ℂ] Coordinates.ComplexCoordinates 4 :=
        LinearMap.toContinuousLinearMap
          { toFun := Coordinates.ComplexCoordinates.matrixEquiv
            map_add' := fun _ _ => rfl
            map_smul' := fun _ _ => rfl }
      exact ε.differentiable.comp_differentiableOn
        (hF.differentiableOn.mono inter_subset_left)
    obtain ⟨hX, hhol⟩ := isHolomorphic_of_differentiableOn hE
      Coordinates.ComplexCoordinates.matrixEquiv (hO.inter hO₀) hd
    have hp' := hp
    rw [hW] at hp'
    have hmaps : MapsTo (fun q : PositiveEdge L n k j ⊕ Empty → ComplexMatrix2 => F (groupComponent q))
        (groupComponent ⁻¹' (O ∩ O₀) ∩ GroupLieProduct (PositiveEdge L n k j) Empty)
        ComplexMatrix2.unitDeterminant := fun q hq => hFg _ hq.1.1 fun r => hq.2 (.inl r)
    refine ⟨groupComponent ⁻¹' (O ∩ O₀) ∩ GroupLieProduct (PositiveEdge L n k j) Empty,
      ⟨⟨hxO, hp'.1⟩, ?_⟩, hX, fun q hq => ?_,
      fun q => ofParts (fun _ => F (groupComponent q)) Empty.elim, fun b => ?_, fun q hq => ?_⟩
    · rintro (r | e)
      · exact (Matrix.mem_specialUnitaryGroup_iff.1 (hp'.2.2 r)).2
      · exact e.elim
    · rw [hW]
      exact ⟨hq.1.1.2, hq.2⟩
    · exact ⟨hX, fun _ => ((hE.2.2.2.1 _ _).2.1 b _ _ hX hmaps).2 (hhol b), fun e => e.elim⟩
    · have hqW : fieldOfPositiveValues (groupComponent q) ∈ 𝒰 := by
        have : q ∈ {q : PositiveEdge L n k j ⊕ Empty → ComplexMatrix2 |
            fieldOfPositiveValues (groupComponent q) ∈ 𝒰} := by
          rw [hW]
          exact ⟨hq.1.1.2, hq.2⟩
        exact this
      have hqD : groupComponent q ∈ restrictToPositiveEdges '' 𝒰 :=
        ⟨_, hqW, restrict_fieldOfPositiveValues _⟩
      have h := hFe _ ⟨hq.1.1.1, hqD⟩
      funext r
      rcases r with r | e
      · change F (groupComponent q) =
          restrictToPositiveEdges (fieldOfPositiveValues fun _ => C _) r
        rw [restrict_fieldOfPositiveValues]
        exact h.symm
      · exact e.elim
end Fields
private def hermitianProjection : ComplexMatrix2 →ₗ[ℝ] ComplexMatrix2 where
  toFun X := (1 / 2 : ℝ) • (X + X.conjTranspose)
  map_add' X Y := by
    rw [Matrix.conjTranspose_add, ← smul_add]
    congr 1
    abel
  map_smul' c X := by
    change (1 / 2 : ℝ) • (c • X + (c • X).conjTranspose) =
      c • ((1 / 2 : ℝ) • (X + X.conjTranspose))
    rw [Matrix.conjTranspose_smul, star_trivial, ← smul_add, smul_comm]
private def complexifyDual (φ : ComplexMatrix2 →ₗ[ℝ] ℝ) : ComplexMatrix2 →L[ℂ] ℂ :=
  LinearMap.toContinuousLinearMap
    (Module.Dual.extendRCLike (𝕜 := ℂ) (φ ∘ₗ hermitianProjection))
private theorem complexifyDual_apply_of_isHermitian (φ : ComplexMatrix2 →ₗ[ℝ] ℝ) {X : ComplexMatrix2}
    (hX : X.conjTranspose = X) : complexifyDual φ X = (φ X : ℂ) := by
  have h₁ : hermitianProjection X = X := by
    change (1 / 2 : ℝ) • (X + X.conjTranspose) = X
    rw [hX, ← two_smul ℝ X, smul_smul]
    norm_num
  have h₂ : hermitianProjection (Complex.I • X) = 0 := by
    change (1 / 2 : ℝ) • (Complex.I • X + (Complex.I • X).conjTranspose) = 0
    rw [Matrix.conjTranspose_smul, hX]
    simp
  change Module.Dual.extendRCLike (𝕜 := ℂ) (φ ∘ₗ hermitianProjection) X = _
  rw [Module.Dual.extendRCLike_apply]
  simp [h₁, h₂]
private def adjugateCLM : ComplexMatrix2 →L[ℂ] ComplexMatrix2 :=
  LinearMap.toContinuousLinearMap
    { toFun := Matrix.adjugate
      map_add' := fun X Y => by
        simp only [Matrix.adjugate_fin_two]
        ext a b
        fin_cases a <;> fin_cases b <;> simp <;> ring
      map_smul' := fun c X => by
        simp only [Matrix.adjugate_fin_two, RingHom.id_apply]
        ext a b
        fin_cases a <;> fin_cases b <;> simp }
private theorem adjugateCLM_apply (X : ComplexMatrix2) : adjugateCLM X = X.adjugate := rfl
private theorem su2_inv_eq_adjugate {U : ComplexMatrix2}
    (hU : U ∈ (ComplexMatrix2.specialUnitary : Set ComplexMatrix2)) :
    U⁻¹ = U.adjugate := by apply _root_.YangMills.Construction.Tower.IdentityLieBallSmoothing.inv_eq_adjugate_of_mem <;> assumption
private theorem conjugateBy_conjTranspose_eq {U A : ComplexMatrix2}
    (hU : U ∈ (ComplexMatrix2.specialUnitary : Set ComplexMatrix2))
    (hA : A.conjTranspose = A) :
    (ComplexMatrix2.conjugateBy U A).conjTranspose = ComplexMatrix2.conjugateBy U A := by
  simp only [ComplexMatrix2.conjugateBy]
  rw [su2_inv_eq_conjTranspose hU, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose, hA, mul_assoc]
section Conjugation
variable {L n k j : ℕ}
private theorem isAnalyticFieldFunction_conjugateBy
    (hE : GroupLieProduct.ExpChartHolomorphy.ExpChartTheory)
    [inst : Fintype (PositiveEdge L n k j)] {𝒰 : Set (Edge L n k j → ComplexMatrix2)}
    (h𝒰 : IsOpenFieldSet PeriodicLattice.compactGaugeGroup 𝒰)
    {C : (Edge L n k j → ComplexMatrix2) → ComplexMatrix2}
    (hC : ComplexMatrix2.IsRealAnalyticBetween
      (fun _ : PositiveEdge L n k j => ComplexMatrix2.FactorKind.group)
      (fun _ : Fin 1 => ComplexMatrix2.FactorKind.group) (restrictToPositiveEdges '' 𝒰)
      fun v _ => C (fieldOfPositiveValues v))
    (hmem : ∀ V ∈ 𝒰, C V ∈ (ComplexMatrix2.specialUnitary : Set ComplexMatrix2))
    {A : ComplexMatrix2} (hA : A.conjTranspose = A) (φ : ComplexMatrix2 →ₗ[ℝ] ℝ) :
    IsAnalyticFieldFunction 𝒰 fun V => φ (ComplexMatrix2.conjugateBy (C V) A) := by
  refine isAnalyticFieldFunction_of_local hE h𝒰 fun V hV => ?_
  obtain ⟨O, F, hO, hxO, hF, hFe, -⟩ :=
    exists_analytic_germ (G := fun v => C (fieldOfPositiveValues v)) hC (mem_image_of_mem _ hV)
  refine ⟨O, fun v => complexifyDual φ (F v * A * adjugateCLM (F v)), hO, hxO,
    fun v hv => ?_, fun W hW hWO => ?_⟩
  · have h₁ : AnalyticAt ℂ F v := hF v hv
    have h₂ : AnalyticAt ℂ (fun v => adjugateCLM (F v)) v :=
      (adjugateCLM.analyticAt _).comp h₁
    have h₃ : AnalyticAt ℂ (fun v => F v * A * adjugateCLM (F v)) v :=
      (h₁.mul analyticAt_const).mul h₂
    exact (complexifyDual φ).analyticAt _ |>.comp h₃
  · have e : C (fieldOfPositiveValues (restrictToPositiveEdges W)) = F (restrictToPositiveEdges W) :=
      hFe _ ⟨hWO, mem_image_of_mem _ hW⟩
    rw [fieldOfPositiveValues_restrict (h𝒰.1 hW)] at e
    change complexifyDual φ (F (restrictToPositiveEdges W) * A *
      adjugateCLM (F (restrictToPositiveEdges W))) = _
    rw [← e, adjugateCLM_apply, ← su2_inv_eq_adjugate (hmem W hW)]
    exact complexifyDual_apply_of_isHermitian φ (conjugateBy_conjTranspose_eq (hmem W hW) hA)
private theorem exists_open_nhd_of_eventually (hE : BondSetFields.ProductStructureHolds)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) (hj : j ≤ k)
    {𝒰₀ : Set (Edge L n k j → ComplexMatrix2)} {P : (Edge L n k j → ComplexMatrix2) → Prop}
    (h : IsOpenNhdOfOne 𝒰₀) (hne : EventuallyNearIdentity (fieldSpace L n k j) P) :
    ∃ 𝒰 : Set (Edge L n k j → ComplexMatrix2), IsOpenNhdOfOne 𝒰 ∧ 𝒰 ⊆ 𝒰₀ ∧ ∀ W ∈ 𝒰, P W := by apply _root_.YangMills.Construction.Tower.SaddleAnalytic.exists_isOpenNhdOfOne_of_eventually <;> assumption
end Conjugation
private theorem hasDerivAt_comp_ofReal_zero {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {f : ℂ → E} {D : E} (h : HasDerivAt f D 0) : HasDerivAt (fun t : ℝ => f (t : ℂ)) D 0 := by
  have h₀ : HasDerivAt f D (((0 : ℝ) : ℂ)) := by simpa using h
  have h₁ := HasDerivAt.scomp (0 : ℝ) h₀ Complex.ofRealCLM.hasDerivAt
  simpa [Function.comp_def] using h₁
abbrev _root_.YangMills.SharedProofs.p1580 := @hasDerivAt_comp_ofReal_zero
end StepAnalyticEntries
open StepAnalyticEntries in
theorem smoothingStepAnalyticEntries_holds
    (hAv : _root_.YangMills.Construction.Tower.SmoothingNearIdentity)
    (hTay : LeftChartTaylorCoefficientsAnalytic)
    (hDiff : AsDifferentials.CovariantMeansAreDerivatives)
    (hForm : LevelwiseMeans.LevelwiseMeansHold)
    (hExp : GroupLieProduct.ExpChartHolomorphy.ExpChartTheory)
    (hCfg : BondSetFields.ProductStructureHolds)
    (hPath : diffAtZeroPathsStatement)
    (hSp : FiniteSideFormSpaces)
    (hAlg : AnalyticFieldFunctionsClosed)
    (hCentre : PeriodicLattice.ContourHolonomyAtBlockCentre) :
    SmoothingStepAnalyticEntries := by
  classical
  intro L n k i hL hn hik
  have hik' : i ≤ k := hik.le
  have hk : 1 ≤ k := by omega
  have hpos : 0 < L := by have := hL.2; omega
  have : Finite (Vertex L n k i) := SeparatedSequences.BaseParameters.site_finite hpos _ _
  have : Finite (Vertex L n k (i + 1)) := SeparatedSequences.BaseParameters.site_finite hpos _ _
  have : Finite (PositiveEdge L n k (i + 1)) := (hSp L n k (i + 1) hL hn hik).1
  have : Finite (Edge L n k i) := Set.finite_univ_iff.1 ((hCfg L hL k i hik').1 n hn).2.1
  obtain ⟨𝒰₁, h𝒰₁, hMap, hcontour⟩ := ((hAv.1 L hL).1 n k i hn hik).1.analytic
  obtain ⟨-, -, instR, -, -⟩ := id hMap
  have hρ : 0 < polydiscRadius L := (hAv.1 L hL).2.2.pos
  have hx : ∀ b : Edge L n k i, Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented :=
    fun b => PeriodicLattice.MatrixValued.xor_isPositivelyOriented_opposite
      (by have := hL.2; omega) (by show -(n : ℤ) < (k : ℤ) - (i : ℤ); omega) b
  have hSide := (hForm L hL k hk).1 n hn
  have hStep := (hDiff L hL k hk).1 n hn
  let P : (Edge L n k i → ComplexMatrix2) → Prop := fun V =>
    V ∈ smallComplexFields L n k i ∧
      ∀ (c : PositiveEdge L n k (i + 1)) (y : Vertex L n k (i + 1)) (x : Vertex L n k i),
        y ∈ ({c.1.source, c.1.target} : Set (Vertex L n k (i + 1))) →
        x ∈ PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k i) y →
        PeriodicLattice.complexBlockAverage V c.1 = smoothingStep L n k i V c.1 ∧
          PeriodicLattice.complexMeanContourHolonomy V y x =
            PeriodicLattice.meanContourHolonomy V y x
  have hnear : EventuallyNearIdentity (fieldSpace L n k i) P := by
    have h₁ : ∀ᶠ V in 𝓝[fieldSpace L n k i] (fun _ => (1 : ComplexMatrix2)),
        ∀ b, ComplexMatrix2.operatorNorm (V b - 1) < polydiscRadius L := by
      rw [eventually_all]
      intro b
      have hc : ContinuousAt (fun V : Edge L n k i → ComplexMatrix2 => ‖V b - 1‖) (fun _ => 1) :=
        ((continuous_apply b).sub continuous_const).norm.continuousAt
      have h0 : ‖((fun _ => (1 : ComplexMatrix2)) : Edge L n k i → ComplexMatrix2) b - 1‖ <
          polydiscRadius L := by simpa using hρ
      exact (hc.eventually (gt_mem_nhds h0)).filter_mono nhdsWithin_le_nhds
    have h₂ : ∀ᶠ V in 𝓝[fieldSpace L n k i] (fun _ => (1 : ComplexMatrix2)),
        ∀ (c : PositiveEdge L n k (i + 1)) (y : Vertex L n k (i + 1)) (x : Vertex L n k i),
          y ∈ ({c.1.source, c.1.target} : Set (Vertex L n k (i + 1))) →
          x ∈ PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k i) y →
          PeriodicLattice.complexBlockAverage V c.1 = smoothingStep L n k i V c.1 ∧
            PeriodicLattice.complexMeanContourHolonomy V y x =
              PeriodicLattice.meanContourHolonomy V y x := by
      rw [eventually_all]
      intro c
      rw [eventually_all]
      intro y
      rw [eventually_all]
      intro x
      refine eventually_imp_distrib_left.2 fun hy => eventually_imp_distrib_left.2 fun hx' => ?_
      exact (hSide.agree_near_identity i hik c.1 c.2 y hy x hx').mono fun V h => ⟨h.2.1, h.2.2.2.1⟩
    filter_upwards [h₁, h₂, eventually_mem_nhdsWithin] with V a₁ a₂ a₃
    exact ⟨⟨⟨fun b hb => (Matrix.mem_specialUnitaryGroup_iff.1 (a₃.1 b hb)).2, a₃.2⟩, a₁⟩, a₂⟩
  obtain ⟨𝒰, h𝒰, hsub, hPU⟩ := exists_open_nhd_of_eventually hCfg hL hn hik' h𝒰₁ hnear
  have hAvg : ∀ V ∈ 𝒰, ∀ c : PositiveEdge L n k (i + 1),
      PeriodicLattice.complexBlockAverage V c.1 = smoothingStep L n k i V c.1 := by
    intro V hV c
    have hcentre := (hCentre L n k i hL hn hik c.1.source (fun _ => 1)
      ⟨fun _ _ => by simp [ComplexMatrix2.unitDeterminant], fun _ _ => by simp⟩).1
    exact ((hPU V hV).2 c _ _ (Or.inl rfl) hcentre).1
  have hCon : ∀ V ∈ 𝒰, ∀ (y : Vertex L n k (i + 1)) (x : Vertex L n k i),
      x ∈ PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k i) y →
      PeriodicLattice.complexMeanContourHolonomy V y x =
        PeriodicLattice.meanContourHolonomy V y x := by
    intro V hV y x hxy
    exact ((hPU V hV).2
      ⟨PeriodicLattice.Bond.forwardFrom y 0, 0, by simp [PeriodicLattice.Bond.forwardFrom]⟩
      y x (Or.inl rfl) hxy).2
  have hcurve : ∀ V ∈ 𝒰, ∀ B ∈ edgeFormSpace L n k i, ∀ᶠ t : ℝ in 𝓝 0,
      PeriodicLattice.expTwist ((t : ℂ) • B) V ∈ 𝒰 := by
    intro V hV B hB
    have hP := hPath L n k i hL hn hik'
    obtain ⟨h₁, h₂, -⟩ := hP.2.2 V (h𝒰.1.1 hV) B hB
    have ht := (hP.1 _ h₁).2
    simp only [h₂] at ht
    exact ht.eventually (hP.2.1 𝒰 h𝒰.1 V hV)
  obtain ⟨U₀, hU₀⟩ : ∃ U₀, U₀ ∈ smallIterateFields L n k := by
    have h1 : (fun _ => (1 : ComplexMatrix2)) ∈ fieldSpace L n k 0 :=
      ⟨fun _ _ => one_mem _, fun _ _ => by simp⟩
    exact ⟨_, (Filter.Eventually.self_of_nhdsWithin hStep.2.2 h1).1⟩
  have hAt : ∀ V ∈ 𝒰, AsDifferentials.StepConditions i V U₀ := fun V hV =>
    hStep.1 i hik V (hPU V hV).1 U₀ hU₀
  have hcomplex : ∀ B ∈ edgeFormSpace L n k i, B ∈ complexEdgeForms L n k i := fun B hB =>
    ⟨fun b hb => (hB.1 b hb).2, hB.2⟩
  obtain ⟨hconst, hadd, hmono, hcongr, -⟩ := hAlg L n k i i hL hn hik' hik'
  have hsum : ∀ {ι : Type} (S : Finset ι) (f : ι → (Edge L n k i → ComplexMatrix2) → ℝ),
      (∀ x ∈ S, IsAnalyticFieldFunction 𝒰 (f x)) →
      IsAnalyticFieldFunction 𝒰 fun V => ∑ x ∈ S, f x V := by
    intro ι S f
    induction S using Finset.induction_on with
    | empty =>
      intro _
      simpa using hconst 𝒰 0 h𝒰.1
    | insert a S ha ih =>
      intro h
      have h₁ := h a (Finset.mem_insert_self a S)
      have h₂ := ih fun x hx => h x (Finset.mem_insert_of_mem hx)
      simpa [Finset.sum_insert ha] using (hadd 𝒰 _ _ h₁ h₂).1
  let r : ℝ := (L : ℝ) ^ (-4 : ℤ)
  have hblock : ∀ (φ : ComplexMatrix2 →ₗ[ℝ] ℝ) (Z : ComplexMatrix2),
      φ (PeriodicLattice.inverseFourthPowerWeight L • Z) = r * φ Z := by
    intro φ Z
    have e : PeriodicLattice.inverseFourthPowerWeight L • Z = r • Z := by
      change ((r : ℝ) : ℂ) • Z = r • Z
      exact Complex.coe_smul r Z
    rw [e, map_smul, smul_eq_mul]
  have hmem : ∀ V ∈ 𝒰₁, ∀ (y : Vertex L n k (i + 1)) (x : Vertex L n k i),
      x ∈ PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k i) y →
      PeriodicLattice.meanContourHolonomy V y x ∈
        (ComplexMatrix2.specialUnitary : Set ComplexMatrix2) := fun V hV y x hxy =>
    (Classical.epsilon_spec ((hcontour y x hxy).1 V hV).exists).1
  have hC : ∀ (y : Vertex L n k (i + 1)) (x : Vertex L n k i),
      x ∈ PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k i) y →
      ComplexMatrix2.IsRealAnalyticBetween
        (fun _ : PositiveEdge L n k i => ComplexMatrix2.FactorKind.group)
        (fun _ : Fin 1 => ComplexMatrix2.FactorKind.group) (restrictToPositiveEdges '' 𝒰₁)
        fun v _ => PeriodicLattice.meanContourHolonomy (fieldOfPositiveValues v) y x := by
    intro y x hxy
    obtain ⟨-, inst', h⟩ := (hcontour y x hxy).2
    obtain rfl : inst' = instR := Subsingleton.elim _ _
    exact h
  refine ⟨𝒰, h𝒰, ?_, ?_, ?_⟩
  · intro B c φ
    have h := ((hTay L n k i (i + 1) hL hn hik' hik).2 𝒰₁ _ hMap B B.2 c φ).1
    refine hcongr 𝒰 _ _ (hmono 𝒰₁ 𝒰 _ h h𝒰.1 hsub) fun V hV => ?_
    have hd := (hAt V hV).deriv_mean c.1 c.2 B (hcomplex B B.2)
    have hr := hasDerivAt_comp_ofReal_zero hd
    have e : deriv (lineLogarithm (smoothingStep L n k i) V B c) 0 =
        complexSmoothingDeriv V (B : Edge L n k i → ComplexMatrix2) c.1 := by
      refine (hr.congr_of_eventuallyEq ?_).deriv
      filter_upwards [hcurve V hV B B.2] with t ht
      simp only [lineLogarithm, AsDifferentials.meanLogRatio,
        AsDifferentials.meanRatio, hAvg _ ht c, hAvg V hV c]
    simp only [e]
  · intro B y φ
    have hfin := Set.toFinite (PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k i) y)
    obtain ⟨c₀⟩ : Nonempty (PositiveEdge L n k i) :=
      ⟨⟨PeriodicLattice.Bond.forwardFrom 0 0, 0, by simp [PeriodicLattice.Bond.forwardFrom]⟩⟩
    let constField : Vertex L n k i → (Edge L n k i → ComplexMatrix2) →
        Edge L n k i → ComplexMatrix2 := fun x V =>
      fieldOfPositiveValues fun _ => PeriodicLattice.meanContourHolonomy V y x
    have hm : ∀ x W, constField x W c₀.1 = PeriodicLattice.meanContourHolonomy W y x := by
      intro x W
      have hb : (c₀ : Edge L n k i).IsPositivelyOriented := c₀.2
      simp [constField, fieldOfPositiveValues, hb]
    have hterm : ∀ x ∈ hfin.toFinset, IsAnalyticFieldFunction 𝒰 fun V =>
        (r • φ) (deriv (lineLogarithm (constField x) V B c₀) 0) := by
      intro x hxf
      have hxy := hfin.mem_toFinset.1 hxf
      have hmap : IsAnalyticFieldMap 𝒰₁ (constField x) :=
        isAnalyticFieldMap_of_constant hExp hx h𝒰₁.1 (hC y x hxy) fun V hV => hmem V hV y x hxy
      have h := ((hTay L n k i i hL hn hik' hik').2 𝒰₁ _ hmap B B.2 c₀ (r • φ)).1
      exact hmono 𝒰₁ 𝒰 _ h h𝒰.1 hsub
    refine hcongr 𝒰 _ _ (hsum hfin.toFinset _ hterm) fun V hV => ?_
    have hs : ∀ x ∈ hfin.toFinset, deriv (lineLogarithm (constField x) V B c₀) 0 =
        logDirectionalDeriv ℂ
          (fun X => PeriodicLattice.complexMeanContourHolonomy (PeriodicLattice.expTwist X V) y x)
          (PeriodicLattice.complexMeanContourHolonomy V y x) B := by
      intro x hxf
      have hxy := hfin.mem_toFinset.1 hxf
      have hd := (hAt V hV).deriv_contour y x hxy B (hcomplex B B.2)
      have hr := hasDerivAt_comp_ofReal_zero hd
      refine (hr.congr_of_eventuallyEq ?_).deriv
      filter_upwards [hcurve V hV B B.2] with t ht
      simp only [lineLogarithm, AsDifferentials.contourLogRatio,
        AsDifferentials.contourRatio, hm, hCon _ ht y x hxy,
        hCon V hV y x hxy]
    change _ = φ (PeriodicLattice.inverseFourthPowerWeight L • ∑ᶠ x ∈ PeriodicLattice.sitesInBlock
      (PeriodicLattice.levelDepth k i) y, _)
    rw [hblock, finsum_mem_eq_finite_toFinset_sum _ hfin, map_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun x hxf => ?_
    rw [hs x hxf, LinearMap.smul_apply, smul_eq_mul]
  · intro l y φ
    have hfin := Set.toFinite (PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k i) y)
    have hl : ∀ x, ((l : Vertex L n k i → ComplexMatrix2) x).conjTranspose =
        (l : Vertex L n k i → ComplexMatrix2) x :=
      fun x => ((l.2 x (mem_univ x)).1).symm
    have hterm : ∀ x ∈ hfin.toFinset, IsAnalyticFieldFunction 𝒰 fun V =>
        (r • φ) (ComplexMatrix2.conjugateBy (PeriodicLattice.meanContourHolonomy V y x)
          ((l : Vertex L n k i → ComplexMatrix2) x)) := by
      intro x hxf
      have hxy := hfin.mem_toFinset.1 hxf
      have h := isAnalyticFieldFunction_conjugateBy hExp h𝒰₁.1 (hC y x hxy)
        (fun V hV => hmem V hV y x hxy) (hl x) (r • φ)
      exact hmono 𝒰₁ 𝒰 _ h h𝒰.1 hsub
    refine hcongr 𝒰 _ _ (hsum hfin.toFinset _ hterm) fun V hV => ?_
    change _ = φ (PeriodicLattice.inverseFourthPowerWeight L • ∑ᶠ x ∈ PeriodicLattice.sitesInBlock
      (PeriodicLattice.levelDepth k i) y, _)
    rw [hblock, finsum_mem_eq_finite_toFinset_sum _ hfin, map_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun x hxf => ?_
    rw [hCon V hV y x (hfin.mem_toFinset.1 hxf), LinearMap.smul_apply, smul_eq_mul]
end Tower
end YangMills.Construction
end
