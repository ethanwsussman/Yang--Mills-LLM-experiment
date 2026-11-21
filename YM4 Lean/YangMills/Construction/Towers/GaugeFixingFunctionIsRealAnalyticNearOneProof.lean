import YangMills.Construction.Lattice.LayerBondsCoarseSpacesAndAverages
import YangMills.Construction.Matrices.ExpChartHolomorphy
import YangMills.Construction.Towers.AveragingIsAnalyticAndCovariantOnTheSidesProof
import YangMills.Construction.Towers.GaugeFixingFunctionIsRealAnalyticNearOne
import Mathlib
set_option autoImplicit false
open Set Filter
open scoped Matrix.Norms.L2Operator Topology
noncomputable section
namespace YangMills.Construction.Tower.AxialFunctionAnalyticNearOne
open YangMills.Construction.Matrices YangMills.Construction.Coordinates
open GroupLieProduct GroupLieProduct.Subspaces
private theorem ofReal_re_fullTrace {U : ComplexMatrix2}
    (hU : U ∈ (ComplexMatrix2.specialUnitary : Set ComplexMatrix2)) :
    (((ComplexMatrix2.fullTrace U).re : ℝ) : ℂ) = ComplexMatrix2.fullTrace U := by
  have hmem := Matrix.mem_specialUnitaryGroup_iff.1 hU
  have hunit : star U * U = 1 := Matrix.mem_unitaryGroup_iff'.1 hmem.1
  have hstar_adj : star U = U.adjugate := by
    calc star U = star U * (U * U.adjugate) := by rw [Matrix.mul_adjugate, hmem.2]; simp
      _ = U.adjugate := by rw [← mul_assoc, hunit, one_mul]
  have htr : Matrix.trace (star U) = star (Matrix.trace U) := Matrix.trace_conjTranspose U
  have htr_adj : Matrix.trace U.adjugate = Matrix.trace U := by
    rw [Matrix.adjugate_fin_two]
    simp [Matrix.trace_fin_two]
    ring
  rw [hstar_adj, htr_adj] at htr
  exact Complex.conj_eq_iff_re.1 htr.symm
private theorem meanContourHolonomy_mem {L m : ℕ} {j j' : ℤ}
    {V : PeriodicLattice.Bond L m j' → ComplexMatrix2}
    {y : PeriodicLattice.Site L m j} {x : PeriodicLattice.Site L m j'}
    (h : PeriodicLattice.HasContourMean V y x) :
    PeriodicLattice.meanContourHolonomy V y x ∈
      (ComplexMatrix2.specialUnitary : Set ComplexMatrix2) :=
  (Classical.epsilon_spec h.exists).1
private theorem exists_analytic_germ {ι : Type} [Fintype ι] {D : Set (ι → ComplexMatrix2)}
    {f : (ι → ComplexMatrix2) → ComplexMatrix2}
    (hf : ComplexMatrix2.IsRealAnalyticBetween (fun _ : ι => ComplexMatrix2.FactorKind.group)
      (fun _ : Fin 1 => ComplexMatrix2.FactorKind.group) D fun v _ => f v)
    {x : ι → ComplexMatrix2} (hx : x ∈ D) :
    ∃ (O : Set (ι → ComplexMatrix2)) (F : (ι → ComplexMatrix2) → ComplexMatrix2), IsOpen O ∧
      x ∈ O ∧ AnalyticOnNhd ℂ F O ∧ ∀ y ∈ O ∩ D, f y = F y := by
  obtain ⟨⟨OD, hOD, rfl⟩, hloc⟩ := hf
  obtain ⟨W, g, hxW, hW, hfg⟩ := hloc x hx
  obtain ⟨⟨OW, hOW, rfl⟩, -, hF⟩ := hW
  obtain ⟨F, hFa, hFe⟩ := hF x hxW
  obtain ⟨N₁, hN₁, hxN₁, hfN₁⟩ := mem_nhdsWithin.1 hfg
  obtain ⟨N₂, hN₂, hxN₂, hFN₂⟩ := mem_nhdsWithin.1 hFe
  obtain ⟨N₃, hN₃sub, hN₃, hxN₃⟩ := mem_nhds_iff.1 hFa.eventually_analyticAt
  refine ⟨N₁ ∩ N₂ ∩ N₃ ∩ OW, fun y => F y 0, ((hN₁.inter hN₂).inter hN₃).inter hOW,
    ⟨⟨⟨hxN₁, hxN₂⟩, hxN₃⟩, hxW.1⟩, fun y hy => ?_, ?_⟩
  · exact ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 1 => ComplexMatrix2) 0).analyticAt
      _).comp (hN₃sub hy.1.2)
  · rintro y ⟨⟨⟨⟨hy₁, hy₂⟩, -⟩, hyW⟩, hyD⟩
    have hc : y ∈ ComplexMatrix2.complexifiedProduct
        fun _ : ι => ComplexMatrix2.FactorKind.group := fun r =>
      (Matrix.mem_specialUnitaryGroup_iff.1 (hyD.2 r)).2
    have e₁ : (fun _ : Fin 1 => f y) = g y := hfN₁ ⟨hy₁, hyD⟩
    have e₂ : g y = F y := hFN₂ ⟨hy₂, hyW, hc⟩
    exact congrFun (e₁.trans e₂) 0
private theorem exists_sum_analytic_germ {ι κ : Type} [Fintype ι] [Fintype κ]
    {D : Set (ι → ComplexMatrix2)} {f : κ → (ι → ComplexMatrix2) → ComplexMatrix2}
    (hf : ∀ t, ComplexMatrix2.IsRealAnalyticBetween
      (fun _ : ι => ComplexMatrix2.FactorKind.group)
      (fun _ : Fin 1 => ComplexMatrix2.FactorKind.group) D fun v _ => f t v)
    {x : ι → ComplexMatrix2} (hx : x ∈ D) :
    ∃ (O : Set (ι → ComplexMatrix2)) (Φ : (ι → ComplexMatrix2) → ℂ), IsOpen O ∧ x ∈ O ∧
      AnalyticOnNhd ℂ Φ O ∧
      ∀ y ∈ O ∩ D, Φ y = ∑ t, (1 - (1 / 2) * ComplexMatrix2.fullTrace (f t y)) := by
  choose O F hO hxO hF hFe using fun t => exists_analytic_germ (hf t) hx
  let τ : ComplexMatrix2 →L[ℂ] ℂ :=
    LinearMap.toContinuousLinearMap (Matrix.traceLinearMap (Fin 2) ℂ ℂ)
  refine ⟨⋂ t, O t, fun y => ∑ t, (1 - (1 / 2) * τ (F t y)), isOpen_iInter_of_finite hO,
    mem_iInter.2 hxO, fun y hy => ?_, fun y hy => ?_⟩
  · refine Finset.analyticAt_fun_sum _ fun t _ => ?_
    exact analyticAt_const.sub (analyticAt_const.mul
      ((τ.analyticAt _).comp (hF t y (mem_iInter.1 hy t))))
  · refine Finset.sum_congr rfl fun t _ => ?_
    rw [hFe t y ⟨mem_iInter.1 hy.1 t, hy.2⟩]
    rfl
private def matrixFamilyCoords {σ : Type} [Fintype σ] {k : ℕ} (ν : σ ≃ Fin k) :
    (σ → ComplexMatrix2) ≃L[ℂ]
      ComplexCoordinates
        (ComplexCoordinates.productDim fun _ : Fin k => ComplexCoordinates.Component.matrix) :=
  LinearEquiv.toContinuousLinearEquiv
    { matrixPiEquiv ν with
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
private theorem holomorphicToCoords_of_analyticOnNhd {ι : Type} [Fintype ι]
    (hE : GroupLieProduct.ExpChartHolomorphy.ExpChartTheory) {O : Set (ι → ComplexMatrix2)}
    (hO : IsOpen O) {Φ : (ι → ComplexMatrix2) → ℂ} (hΦ : AnalyticOnNhd ℂ Φ O) :
    ComplexMatrix2.IsRelativelyOpen (GroupLieProduct ι Empty)
        ((groupComponent ⁻¹' O : Set (ι ⊕ Empty → ComplexMatrix2)) ∩
          GroupLieProduct ι Empty) ∧
      ∀ b : Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless,
        IsHolomorphicToCoords b (Equiv.refl (ComplexCoordinates 1))
          ((groupComponent ⁻¹' O : Set (ι ⊕ Empty → ComplexMatrix2)) ∩
            GroupLieProduct ι Empty)
          fun q _ => Φ (groupComponent q) := by
  let ν : ι ⊕ Empty ≃ Fin (Fintype.card (ι ⊕ Empty)) := Fintype.equivFin _
  have hcont : Continuous
      (groupComponent : (ι ⊕ Empty → ComplexMatrix2) → ι → ComplexMatrix2) :=
    continuous_pi fun r => continuous_apply _
  have hdiff : Differentiable ℂ
      (groupComponent : (ι ⊕ Empty → ComplexMatrix2) → ι → ComplexMatrix2) :=
    differentiable_pi.2 fun r => differentiable_apply _
  have hO' : IsOpen (groupComponent ⁻¹' O : Set (ι ⊕ Empty → ComplexMatrix2)) :=
    hO.preimage hcont
  refine ((hE.2.2.2.1 ι Empty).2.2) (ComplexCoordinates 1) 1 _ (Equiv.refl _) ν _ _ ?_
  unfold ComplexCoordinates.IsHolomorphicVia
  have himg : matrixPiEquiv ν '' (groupComponent ⁻¹' O) =
      (matrixFamilyCoords ν).symm ⁻¹' (groupComponent ⁻¹' O) := by
    ext z
    constructor
    · rintro ⟨x, hx, rfl⟩
      have : (matrixFamilyCoords ν).symm (matrixPiEquiv ν x) = x :=
        (matrixPiEquiv ν).symm_apply_apply x
      simpa [this] using hx
    · intro hz
      exact ⟨(matrixFamilyCoords ν).symm z, hz, (matrixPiEquiv ν).apply_symm_apply z⟩
  have hfun : ((Equiv.refl (ComplexCoordinates 1)) ∘ (fun q _ => Φ (groupComponent q)) ∘
        (matrixPiEquiv ν).symm) =
      fun z _ => Φ (groupComponent ((matrixFamilyCoords ν).symm z)) := rfl
  rw [himg, hfun]
  have hopen : IsOpen ((matrixFamilyCoords ν).symm ⁻¹' (groupComponent ⁻¹' O)) :=
    hO'.preimage (matrixFamilyCoords ν).symm.continuous
  have hd : DifferentiableOn ℂ (fun z => Φ (groupComponent ((matrixFamilyCoords ν).symm z)))
      ((matrixFamilyCoords ν).symm ⁻¹' (groupComponent ⁻¹' O)) := fun z hz =>
    ((hΦ _ hz).differentiableAt.comp z
      ((hdiff _).comp z (matrixFamilyCoords ν).symm.differentiableAt)).differentiableWithinAt
  have hd' : DifferentiableOn ℂ
      (fun z (_ : Fin 1) => Φ (groupComponent ((matrixFamilyCoords ν).symm z)))
      ((matrixFamilyCoords ν).symm ⁻¹' (groupComponent ⁻¹' O)) :=
    differentiableOn_pi.2 fun _ => hd
  refine ⟨hopen, hd'.continuousOn, fun a ha j => ?_⟩
  have hline : Continuous fun ζ : ℂ => a + ζ • ComplexCoordinates.stdBasisVector j := by
    fun_prop
  have hmem : ∀ᶠ ζ in 𝓝 (0 : ℂ), a + ζ • ComplexCoordinates.stdBasisVector j ∈
      (matrixFamilyCoords ν).symm ⁻¹' (groupComponent ⁻¹' O) :=
    hline.continuousAt.eventually_mem (by simpa using hopen.mem_nhds ha)
  filter_upwards [hmem] with ζ hζ
  have hlineAt : DifferentiableAt ℂ
      (fun ζ : ℂ => a + ζ • ComplexCoordinates.stdBasisVector j) ζ := by
    fun_prop
  exact DifferentiableAt.comp (f := fun ζ : ℂ => a + ζ • ComplexCoordinates.stdBasisVector j) ζ
    (hd'.differentiableAt (hopen.mem_nhds hζ)) hlineAt
private theorem finsum_finsum_eq_sum_sigma {α β : Type} [Finite α] [Finite β] (S : α → Set β)
    (g : α → β → ℝ) [Fintype (Σ a, S a)] :
    ∑ᶠ a ∈ (univ : Set α), ∑ᶠ b ∈ S a, g a b = ∑ t : Σ a, S a, g t.1 t.2 := by
  classical
  let _ : Fintype α := Fintype.ofFinite α
  let _ : ∀ a, Fintype (S a) := fun a => Fintype.ofFinite _
  have hinner : ∀ a, ∑ᶠ b ∈ S a, g a b = ∑ b : S a, g a b := fun a => by
    rw [← finsum_set_coe_eq_finsum_mem, finsum_eq_sum_of_fintype]
  simp only [finsum_mem_univ, hinner]
  rw [finsum_eq_sum_of_fintype]
  rw [← Fintype.sum_sigma' (fun a (b : S a) => g a b)]
  refine Finset.sum_congr ?_ fun _ _ => rfl
  ext t
  simp
private theorem fieldOfPositiveValues_restrict {L n k j : ℕ} {V : Edge L n k j → ComplexMatrix2}
    (hV : V ∈ fieldSpace L n k j) : fieldOfPositiveValues (restrictToPositiveEdges V) = V := by apply _root_.YangMills.SharedProofs.p407 <;> assumption
private theorem restrict_fieldOfPositiveValues {L n k j : ℕ}
    (w : PositiveEdge L n k j → ComplexMatrix2) :
    restrictToPositiveEdges (fieldOfPositiveValues w) = w := by apply _root_.YangMills.SharedProofs.p777 <;> assumption
theorem of_smoothingNearIdentity (hE : GroupLieProduct.ExpChartHolomorphy.ExpChartTheory)
    (hA : _root_.YangMills.Construction.Tower.SmoothingNearIdentity) : AxialFunctionAnalyticNearOne := by
  intro L n k i hL hn hik
  obtain ⟨𝒰, h𝒰, hMap, hcontour⟩ := ((hA.1 L hL).1 n k i hn hik).1.analytic
  obtain ⟨-, -, instR, -, -⟩ := hMap
  have hpos : 0 < L := by have := hL.2; omega
  have : Finite (PeriodicLattice.Site L n (PeriodicLattice.levelDepth k (i + 1))) :=
    SeparatedSequences.BaseParameters.site_finite hpos _ _
  have : Finite (PeriodicLattice.Site L n (PeriodicLattice.levelDepth k i)) :=
    SeparatedSequences.BaseParameters.site_finite hpos _ _
  classical
  let S : PeriodicLattice.Site L n (PeriodicLattice.levelDepth k (i + 1)) →
      Set (PeriodicLattice.Site L n (PeriodicLattice.levelDepth k i)) :=
    fun y => PeriodicLattice.blockSitesExceptCenter k i y
  let T : Type := Σ y, S y
  let _ : Fintype T := Fintype.ofFinite T
  let f : T → (PositiveEdge L n k i → ComplexMatrix2) → ComplexMatrix2 := fun t w =>
    PeriodicLattice.meanContourHolonomy (fieldOfPositiveValues w) t.1 t.2.1
  have hopen := h𝒰.1
  have hf : ∀ t, ComplexMatrix2.IsRealAnalyticBetween
      (fun _ : PositiveEdge L n k i => ComplexMatrix2.FactorKind.group)
      (fun _ : Fin 1 => ComplexMatrix2.FactorKind.group) (restrictToPositiveEdges '' 𝒰)
      fun v _ => f t v := by
    intro t
    obtain ⟨-, inst', h⟩ := (hcontour t.1 t.2.1 t.2.2.1).2
    obtain rfl : inst' = instR := Subsingleton.elim _ _
    exact h
  have hsum : ∀ V ∈ 𝒰, ((axialFunction L n k i V : ℝ) : ℂ) =
      ∑ t : T, (1 - (1 / 2) *
        ComplexMatrix2.fullTrace (PeriodicLattice.meanContourHolonomy V t.1 t.2.1)) := by
    intro V hV
    have e : axialFunction L n k i V =
        ∑ t : T, PeriodicLattice.traceDeficit
          (PeriodicLattice.meanContourHolonomy V t.1 t.2.1) :=
      finsum_finsum_eq_sum_sigma S fun y z =>
        PeriodicLattice.traceDeficit (PeriodicLattice.meanContourHolonomy V y z)
    rw [e, Complex.ofReal_sum]
    refine Finset.sum_congr rfl fun t _ => ?_
    have hre := ofReal_re_fullTrace
      (meanContourHolonomy_mem ((hcontour t.1 t.2.1 t.2.2.1).1 V hV))
    simp only [PeriodicLattice.traceDeficit]
    push_cast
    rw [hre]
  obtain ⟨hsub, O₀, hO₀, hD⟩ := id hopen
  have hcont : Continuous
      (groupComponent :
        (PositiveEdge L n k i ⊕ Empty → ComplexMatrix2) → PositiveEdge L n k i → ComplexMatrix2) :=
    continuous_pi fun r => continuous_apply _
  have hW : {q : PositiveEdge L n k i ⊕ Empty → ComplexMatrix2 |
      fieldOfPositiveValues (groupComponent q) ∈ 𝒰} =
      groupComponent ⁻¹' O₀ ∩ subspaceTimesGroup ⊥ (PositiveEdge L n k i) := by
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
  refine ⟨𝒰, h𝒰, fun V hV => ⟨hsub hV, fun y _ z hz => (hcontour y z hz.1).1 V hV⟩, hopen,
    instR, ⟨bot_le, groupComponent ⁻¹' O₀, hO₀.preimage hcont, hW⟩, fun p hp => ?_⟩
  have hxD : groupComponent p ∈ restrictToPositiveEdges '' 𝒰 :=
    ⟨_, hp, restrict_fieldOfPositiveValues _⟩
  obtain ⟨O, Φ, hO, hxO, hΦ, hΦe⟩ := exists_sum_analytic_germ hf hxD
  obtain ⟨hX, hhol⟩ := holomorphicToCoords_of_analyticOnNhd hE (hO.inter hO₀)
    (hΦ.mono inter_subset_left)
  have hp' := hp
  rw [hW] at hp'
  refine ⟨groupComponent ⁻¹' (O ∩ O₀) ∩ GroupLieProduct (PositiveEdge L n k i) Empty,
    ⟨⟨hxO, hp'.1⟩, ?_⟩, hX, fun q hq => ?_, fun q _ => Φ (groupComponent q), hhol, ?_⟩
  · rintro (r | e)
    · exact (Matrix.mem_specialUnitaryGroup_iff.1 (hp'.2.2 r)).2
    · exact e.elim
  · rw [hW]
    exact ⟨hq.1.1.2, hq.2⟩
  · intro q hq
    have hqW : fieldOfPositiveValues (groupComponent q) ∈ 𝒰 := by
      have : q ∈ {q : PositiveEdge L n k i ⊕ Empty → ComplexMatrix2 |
          fieldOfPositiveValues (groupComponent q) ∈ 𝒰} := by
        rw [hW]
        exact ⟨hq.1.1.2, hq.2⟩
      exact this
    have hqD : groupComponent q ∈ restrictToPositiveEdges '' 𝒰 :=
      ⟨_, hqW, restrict_fieldOfPositiveValues _⟩
    funext _
    exact (hΦe _ ⟨hq.1.1.1, hqD⟩).trans (hsum _ hqW).symm
end YangMills.Construction.Tower.AxialFunctionAnalyticNearOne
end
