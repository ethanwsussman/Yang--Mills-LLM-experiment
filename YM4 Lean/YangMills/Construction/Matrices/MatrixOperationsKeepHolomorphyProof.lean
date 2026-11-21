import YangMills.Construction.Matrices.CalculusOfHolomorphicMapsProof
import YangMills.Construction.Matrices.LinearMapsCompositesAndCoordinatesOfRealAnalyticMapsProof
import Mathlib
open Set Filter
open scoped Matrix.Norms.L2Operator Topology
noncomputable section
namespace YangMills.Construction.Matrices.GroupLieProduct.HolomorphyClosure
variable {ι κ : Type}
private theorem isHolomorphicIn_iff_differentiableOn
    (hH : Coordinates.ComplexCoordinates.PowerSeriesHolomorphy.Properties) {n m : ℕ}
    {S : Set (Coordinates.ComplexCoordinates n)}
    {f : Coordinates.ComplexCoordinates n → Coordinates.ComplexCoordinates m} :
    Coordinates.ComplexCoordinates.IsHolomorphicIn S f ↔ IsOpen S ∧ DifferentiableOn ℂ f S := by apply _root_.YangMills.SharedProofs.p123 <;> assumption
private def entryEquiv : ComplexMatrix2 ≃L[ℂ] Coordinates.ComplexCoordinates 4 :=
  LinearEquiv.toContinuousLinearEquiv
    { Coordinates.ComplexCoordinates.matrixEquiv with
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
private theorem differentiableOn_matrixEquiv_comp_iff {n : ℕ}
    {S : Set (Coordinates.ComplexCoordinates n)} {F : Coordinates.ComplexCoordinates n → ComplexMatrix2} :
    DifferentiableOn ℂ (Coordinates.ComplexCoordinates.matrixEquiv ∘ F) S ↔ DifferentiableOn ℂ F S :=
  entryEquiv.comp_differentiableOn_iff
private theorem continuousOn_matrixEquiv_comp_iff {X : Type} [TopologicalSpace X] {S : Set X}
    {F : X → ComplexMatrix2} :
    ContinuousOn (Coordinates.ComplexCoordinates.matrixEquiv ∘ F) S ↔ ContinuousOn F S :=
  entryEquiv.toHomeomorph.comp_continuousOn_iff F S
private theorem differentiableOn_of_isHolomorphicVia
    (hH : Coordinates.ComplexCoordinates.PowerSeriesHolomorphy.Properties)
    {S : Set ComplexMatrix2} {g : ComplexMatrix2 → ComplexMatrix2}
    (h : Coordinates.ComplexCoordinates.IsHolomorphicVia Coordinates.ComplexCoordinates.matrixEquiv
      Coordinates.ComplexCoordinates.matrixEquiv S g) : DifferentiableOn ℂ g S := by apply _root_.YangMills.SharedProofs.p53137 <;> assumption
private theorem isSupOpen_inter {σ : Type} {S T : Set (σ → ComplexMatrix2)} (h : IsSupOpen S)
    (h' : IsSupOpen T) : IsSupOpen (S ∩ T) := by apply _root_.YangMills.SharedProofs.p44648 <;> assumption
variable [Fintype ι] [Fintype κ]
private def chartPreimage (p : ι ⊕ κ → ComplexMatrix2) (W : Set (ι ⊕ κ → ComplexMatrix2)) :
    Set (ι ⊕ κ → ComplexMatrix2) :=
  {A ∈ tracelessPi (ι ⊕ κ) | expChartAt p A ∈ W}
private theorem chartPreimage_isSupOpen_zero_mem (hX : ExpChartHolomorphy.ExpChartTheory)
    {W : Set (ι ⊕ κ → ComplexMatrix2)}
    (hW : ComplexMatrix2.IsRelativelyOpen (GroupLieProduct ι κ) W) {p : ι ⊕ κ → ComplexMatrix2}
    (hp : p ∈ W) :
    IsSupOpen (chartPreimage p W) ∧ (0 : ι ⊕ κ → ComplexMatrix2) ∈ chartPreimage p W := by
  obtain ⟨U, hU, rfl⟩ := hW
  obtain ⟨-, hc, hm, h0, -⟩ := (hX.2.2.2.1 ι κ).1 p hp.2
  obtain ⟨u, hu, e⟩ := continuousOn_iff'.1 hc U hU
  constructor
  · refine (((hX.2.1 (ι ⊕ κ)).1 _ (sep_subset _ _)).1).2 ⟨u, hu, ?_⟩
    ext A
    constructor
    · rintro ⟨hA, hA'⟩
      have : A ∈ expChartAt p ⁻¹' U ∩ tracelessPi (ι ⊕ κ) := ⟨hA'.1, hA⟩
      rw [e] at this
      exact this
    · intro hA
      have hA' : A ∈ expChartAt p ⁻¹' U ∩ tracelessPi (ι ⊕ κ) := by
        rw [e]
        exact hA
      exact ⟨hA'.2, hA'.1, hm hA'.2⟩
  · refine ⟨fun _ => Submodule.zero_mem _, ?_⟩
    rw [h0]
    exact hp
private def DifferentiableInCharts (b : Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless)
    (W : Set (ι ⊕ κ → ComplexMatrix2)) (Φ : (ι ⊕ κ → ComplexMatrix2) → ComplexMatrix2) : Prop :=
  ∀ p ∈ W, ∃ O : Set (ι ⊕ κ → ComplexMatrix2), 0 ∈ O ∧ (∀ A ∈ O, expChartAt p A ∈ W) ∧
    IsSupOpen O ∧ ∀ ν : ι ⊕ κ ≃ Fin (Fintype.card (ι ⊕ κ)),
      DifferentiableOn ℂ ((Φ ∘ expChartAt p) ∘ tupleOfCoords b ν)
        (tupleOfCoords b ν ⁻¹' O)
private theorem isHolomorphicToMatrixEntries_iff
    (hH : Coordinates.ComplexCoordinates.PowerSeriesHolomorphy.Properties)
    (hX : ExpChartHolomorphy.ExpChartTheory)
    {b : Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless} {W : Set (ι ⊕ κ → ComplexMatrix2)}
    {Φ : (ι ⊕ κ → ComplexMatrix2) → ComplexMatrix2}
    (hW : ComplexMatrix2.IsRelativelyOpen (GroupLieProduct ι κ) W) :
    IsHolomorphicToMatrixEntries b W Φ ↔ ContinuousOn Φ W ∧ DifferentiableInCharts b W Φ := by
  constructor
  · rintro ⟨-, hc, hp⟩
    refine ⟨continuousOn_matrixEquiv_comp_iff.1 hc, fun p hpW => ?_⟩
    obtain ⟨O, h0, hA, hO, hh⟩ := hp p hpW
    exact ⟨O, h0, hA, hO, fun ν =>
      differentiableOn_matrixEquiv_comp_iff.1
        ((isHolomorphicIn_iff_differentiableOn hH).1 (hh ν)).2⟩
  · rintro ⟨hc, hp⟩
    refine ⟨hW, continuousOn_matrixEquiv_comp_iff.2 hc, fun p hpW => ?_⟩
    obtain ⟨O, h0, hA, hO, hh⟩ := hp p hpW
    refine ⟨O, h0, hA, hO, fun ν => (isHolomorphicIn_iff_differentiableOn hH).2 ⟨?_, ?_⟩⟩
    · exact (((hX.2.1 (ι ⊕ κ)).1 O hO.1).2 b ν).1 hO
    · exact differentiableOn_matrixEquiv_comp_iff.2 (hh ν)
private theorem comp_pair (hH : Coordinates.ComplexCoordinates.PowerSeriesHolomorphy.Properties)
    (hX : ExpChartHolomorphy.ExpChartTheory)
    {b : Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless} {W : Set (ι ⊕ κ → ComplexMatrix2)}
    (hW : ComplexMatrix2.IsRelativelyOpen (GroupLieProduct ι κ) W)
    {Φ Ψ : (ι ⊕ κ → ComplexMatrix2) → ComplexMatrix2}
    {g : ComplexMatrix2 × ComplexMatrix2 → ComplexMatrix2} {U : Set (ComplexMatrix2 × ComplexMatrix2)}
    (hg : DifferentiableOn ℂ g U)
    (hm : ∀ p ∈ W, (Φ p, Ψ p) ∈ U) (hΦ : IsHolomorphicToMatrixEntries b W Φ)
    (hΨ : IsHolomorphicToMatrixEntries b W Ψ) :
    IsHolomorphicToMatrixEntries b W fun p => g (Φ p, Ψ p) := by
  obtain ⟨c₁, h₁⟩ := (isHolomorphicToMatrixEntries_iff hH hX hW).1 hΦ
  obtain ⟨c₂, h₂⟩ := (isHolomorphicToMatrixEntries_iff hH hX hW).1 hΨ
  refine (isHolomorphicToMatrixEntries_iff hH hX hW).2
    ⟨hg.continuousOn.comp (c₁.prodMk c₂) hm, fun p hp => ?_⟩
  obtain ⟨O₁, a₁, b₁, t₁, d₁⟩ := h₁ p hp
  obtain ⟨O₂, a₂, -, t₂, d₂⟩ := h₂ p hp
  refine ⟨O₁ ∩ O₂, ⟨a₁, a₂⟩, fun A hA => b₁ A hA.1, isSupOpen_inter t₁ t₂, fun ν => ?_⟩
  have e₁ := (d₁ ν).mono (preimage_mono (inter_subset_left (s := O₁) (t := O₂)))
  have e₂ := (d₂ ν).mono (preimage_mono (inter_subset_right (s := O₁) (t := O₂)))
  exact hg.comp (e₁.prodMk e₂) fun w hw => hm _ (b₁ _ hw.1)
private theorem comp_single (hH : Coordinates.ComplexCoordinates.PowerSeriesHolomorphy.Properties)
    (hX : ExpChartHolomorphy.ExpChartTheory)
    {b : Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless} {W : Set (ι ⊕ κ → ComplexMatrix2)}
    (hW : ComplexMatrix2.IsRelativelyOpen (GroupLieProduct ι κ) W)
    {Φ : (ι ⊕ κ → ComplexMatrix2) → ComplexMatrix2}
    {g : ComplexMatrix2 → ComplexMatrix2} {U : Set ComplexMatrix2} (hg : DifferentiableOn ℂ g U)
    (hm : ∀ p ∈ W, Φ p ∈ U) (hΦ : IsHolomorphicToMatrixEntries b W Φ) :
    IsHolomorphicToMatrixEntries b W fun p => g (Φ p) :=
  comp_pair hH hX hW (g := fun q => g q.1) (U := U ×ˢ univ)
    (hg.comp differentiableOn_fst fun _ hq => hq.1) (fun p hp => ⟨hm p hp, mem_univ _⟩) hΦ hΦ
private theorem differentiable_tupleOfCoords_apply
    (b : Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless)
    (ν : ι ⊕ κ ≃ Fin (Fintype.card (ι ⊕ κ))) (x : ι ⊕ κ) :
    Differentiable ℂ fun w => tupleOfCoords b ν w x := by
  simp only [tupleOfCoords, Coordinates.ComplexCoordinates.tracelessTuple]
  exact Differentiable.fun_sum fun c _ => (differentiable_apply _).smul_const _
private theorem differentiable_matExp
    (hH : Coordinates.ComplexCoordinates.PowerSeriesHolomorphy.Properties) :
    Differentiable ℂ ComplexMatrix2.matExp := by apply _root_.YangMills.SharedProofs.p11731 <;> assumption
private theorem const (hH : Coordinates.ComplexCoordinates.PowerSeriesHolomorphy.Properties)
    (hX : ExpChartHolomorphy.ExpChartTheory)
    {b : Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless} {W : Set (ι ⊕ κ → ComplexMatrix2)}
    (hW : ComplexMatrix2.IsRelativelyOpen (GroupLieProduct ι κ) W) (C : ComplexMatrix2) :
    IsHolomorphicToMatrixEntries b W fun _ => C := by
  refine (isHolomorphicToMatrixEntries_iff hH hX hW).2 ⟨continuousOn_const, fun p hp => ?_⟩
  obtain ⟨t, h0⟩ := chartPreimage_isSupOpen_zero_mem hX hW hp
  exact ⟨_, h0, fun A hA => hA.2, t, fun ν => differentiableOn_const _⟩
private theorem coordinate (hH : Coordinates.ComplexCoordinates.PowerSeriesHolomorphy.Properties)
    (hX : ExpChartHolomorphy.ExpChartTheory)
    {b : Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless} {W : Set (ι ⊕ κ → ComplexMatrix2)}
    (hW : ComplexMatrix2.IsRelativelyOpen (GroupLieProduct ι κ) W) (x : ι ⊕ κ) :
    IsHolomorphicToMatrixEntries b W fun p => p x := by
  refine (isHolomorphicToMatrixEntries_iff hH hX hW).2
    ⟨(continuous_apply x).continuousOn, fun p hp => ?_⟩
  obtain ⟨t, h0⟩ := chartPreimage_isSupOpen_zero_mem hX hW hp
  refine ⟨_, h0, fun A hA => hA.2, t, fun ν => Differentiable.differentiableOn ?_⟩
  rcases x with i | k
  · exact ((differentiable_matExp hH).comp
      (differentiable_tupleOfCoords_apply b ν (.inl i))).mul_const _
  · exact (differentiable_tupleOfCoords_apply b ν (.inr k)).const_add _
theorem holomorphyClosureStatement_holds
    (hH : Coordinates.ComplexCoordinates.PowerSeriesHolomorphy.Properties)
    (hX : ExpChartHolomorphy.ExpChartTheory) : HolomorphyClosureStatement := by
  intro ι κ _ _ b W hW
  refine ⟨const hH hX hW, coordinate hH hX hW, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro Φ Ψ hΦ hΨ
    exact comp_pair hH hX hW (g := fun q => q.1 + q.2) (U := univ)
      (differentiable_fst.add differentiable_snd).differentiableOn (fun _ _ => mem_univ _) hΦ hΨ
  · intro Φ Ψ hΦ hΨ
    exact comp_pair hH hX hW (g := fun q => q.1 * q.2) (U := univ)
      (differentiable_fst.mul differentiable_snd).differentiableOn (fun _ _ => mem_univ _) hΦ hΨ
  · intro l Φ hΦ
    exact comp_single hH hX hW (g := fun M => l M) (U := univ)
      (LinearMap.toContinuousLinearMap l).differentiable.differentiableOn
      (fun _ _ => mem_univ _) hΦ
  · intro Φ hΦ hu
    exact comp_single hH hX hW (g := fun M => M⁻¹) (U := {M : ComplexMatrix2 | IsUnit M})
      (differentiableOn_of_isHolomorphicVia hH hH.2.2.2.1)
      (fun p hp => (Matrix.isUnit_iff_isUnit_det _).2 (hu p hp)) hΦ
  · intro Φ hΦ
    exact comp_single hH hX hW (g := ComplexMatrix2.matExp) (U := univ)
      (differentiable_matExp hH).differentiableOn (fun _ _ => mem_univ _) hΦ
  · intro Φ hΦ hm
    exact comp_single hH hX hW (g := ComplexMatrix2.logSeries) (U := ComplexMatrix2.logBall)
      (differentiableOn_of_isHolomorphicVia hH hH.2.2.2.2.2) (fun p hp => hm hp) hΦ
  · intro Φ hΦ O hO
    have hc := ((isHolomorphicToMatrixEntries_iff hH hX hW).1 hΦ).1
    obtain ⟨V, hV, rfl⟩ := hW
    obtain ⟨u, hu, e⟩ := continuousOn_iff'.1 hc O hO
    refine ⟨u ∩ V, hu.inter hV, ?_⟩
    ext p
    constructor
    · rintro ⟨hp, hpO⟩
      have : p ∈ Φ ⁻¹' O ∩ (V ∩ GroupLieProduct ι κ) := ⟨hpO, hp⟩
      rw [e] at this
      exact ⟨⟨this.1, hp.1⟩, hp.2⟩
    · rintro ⟨⟨hpu, hpV⟩, hpG⟩
      have : p ∈ u ∩ (V ∩ GroupLieProduct ι κ) := ⟨hpu, hpV, hpG⟩
      rw [← e] at this
      exact ⟨this.2, this.1⟩
  · intro W' hsub hW' Φ hΦ
    obtain ⟨hc, hp⟩ := (isHolomorphicToMatrixEntries_iff hH hX hW).1 hΦ
    refine (isHolomorphicToMatrixEntries_iff hH hX hW').2 ⟨hc.mono hsub, fun p hpW => ?_⟩
    obtain ⟨O, a, -, t, d⟩ := hp p (hsub hpW)
    obtain ⟨t', h0⟩ := chartPreimage_isSupOpen_zero_mem hX hW' hpW
    exact ⟨O ∩ chartPreimage p W', ⟨a, h0⟩, fun A hA => hA.2.2, isSupOpen_inter t t', fun ν =>
      (d ν).mono (preimage_mono inter_subset_left)⟩
  · intro Φ Ψ hΦ he
    obtain ⟨hc, hp⟩ := (isHolomorphicToMatrixEntries_iff hH hX hW).1 hΦ
    refine (isHolomorphicToMatrixEntries_iff hH hX hW).2 ⟨hc.congr he, fun p hpW => ?_⟩
    obtain ⟨O, a, m, t, d⟩ := hp p hpW
    exact ⟨O, a, m, t, fun ν => (d ν).congr fun w hw => he (m _ hw)⟩
end YangMills.Construction.Matrices.GroupLieProduct.HolomorphyClosure
