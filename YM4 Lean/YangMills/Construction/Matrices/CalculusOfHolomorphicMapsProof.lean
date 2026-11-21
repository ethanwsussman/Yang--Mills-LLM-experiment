import YangMills.Construction.Matrices.CalculusOfHolomorphicMaps
import YangMills.Construction.Matrices.ExpChartHolomorphy
import Mathlib
open Set Filter
open scoped Topology
noncomputable section
namespace YangMills.Construction.Matrices.GroupLieProduct.HolomorphicCalculus
open YangMills.Construction.Coordinates
variable {σ ι κ ι' κ' E : Type}
private theorem holoIn_mono {N N' : ℕ} {U U' : Set (ComplexCoordinates N)}
    {f : ComplexCoordinates N → ComplexCoordinates N'} (hf : ComplexCoordinates.IsHolomorphicIn U f)
    (hU' : IsOpen U') (hsub : U' ⊆ U) : ComplexCoordinates.IsHolomorphicIn U' f :=
  ⟨hU', hf.2.1.mono hsub, fun a ha j => hf.2.2 a (hsub ha) j⟩
private theorem holoIn_toZero {N : ℕ} {U : Set (ComplexCoordinates N)} (hU : IsOpen U)
    (f : ComplexCoordinates N → ComplexCoordinates 0) : ComplexCoordinates.IsHolomorphicIn U f := by
  obtain rfl : f = fun _ => 0 := funext fun _ => Subsingleton.elim _ _
  exact ⟨hU, continuousOn_const, fun _ _ _ => Eventually.of_forall fun _ => differentiableAt_const _⟩
private theorem supOpen_inter {U U' : Set (σ → ComplexMatrix2)} (hU : IsSupOpen U)
    (hU' : IsSupOpen U') : IsSupOpen (U ∩ U') := by
  refine ⟨inter_subset_left.trans hU.1, fun X hX => ?_⟩
  obtain ⟨r, hr, hball⟩ := hU.2 X hX.1
  obtain ⟨r', hr', hball'⟩ := hU'.2 X hX.2
  exact ⟨min r r', lt_min hr hr', fun Y hY hd =>
    ⟨hball Y hY (hd.trans_le (min_le_left _ _)), hball' Y hY (hd.trans_le (min_le_right _ _))⟩⟩
abbrev _root_.YangMills.SharedProofs.p44648 := @supOpen_inter
private theorem holoTraceless_mono (T : ExpChartHolomorphy.ExpChartTheory)
    [Fintype σ] {n : ℕ} {v : Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless}
    {c : E ≃ ComplexCoordinates n}
    {U U' : Set (σ → ComplexMatrix2)} {f : (σ → ComplexMatrix2) → E}
    (hf : IsHolomorphicOnTraceless v c U f)
    (hU' : IsSupOpen U') (hsub : U' ⊆ U) : IsHolomorphicOnTraceless v c U' f :=
  ⟨hU', fun μ => holoIn_mono (hf.2 μ) ((((T.2.1 σ).1 U' hU'.1).2 v μ).1 hU')
    (preimage_mono hsub)⟩
private theorem subset_of_relOpen {P D : Set (ι ⊕ κ → ComplexMatrix2)}
    (hD : ComplexMatrix2.IsRelativelyOpen P D) : D ⊆ P := by
  obtain ⟨V, -, rfl⟩ := hD
  exact inter_subset_right
private theorem relOpen_iUnion {J : Type} {P : Set (ι ⊕ κ → ComplexMatrix2)}
    {U : J → Set (ι ⊕ κ → ComplexMatrix2)}
    (hU : ∀ j, ComplexMatrix2.IsRelativelyOpen P (U j)) :
    ComplexMatrix2.IsRelativelyOpen P (⋃ j, U j) := by
  choose V hV hUV using hU
  refine ⟨⋃ j, V j, isOpen_iUnion hV, ?_⟩
  rw [iUnion_inter]
  exact iUnion_congr hUV
private theorem supOpen_chartPreimage (T : ExpChartHolomorphy.ExpChartTheory)
    [Fintype ι] [Fintype κ] {W : Set (ι ⊕ κ → ComplexMatrix2)}
    (hW : ComplexMatrix2.IsRelativelyOpen (GroupLieProduct ι κ) W) {x : ι ⊕ κ → ComplexMatrix2}
    (hx : x ∈ GroupLieProduct ι κ) :
    IsSupOpen (tracelessPi (ι ⊕ κ) ∩ expChartAt x ⁻¹' W) := by
  obtain ⟨V, hV, rfl⟩ := hW
  obtain ⟨-, hcont, hmaps, -, -⟩ := (T.2.2.2.1 ι κ).1 x hx
  obtain ⟨u, hu, hpre⟩ := continuousOn_iff'.1 hcont V hV
  have hEq : tracelessPi (ι ⊕ κ) ∩ expChartAt x ⁻¹' (V ∩ GroupLieProduct ι κ) =
      u ∩ tracelessPi (ι ⊕ κ) := by
    ext X
    constructor
    · rintro ⟨hX, hXV, -⟩
      have hmem : X ∈ expChartAt x ⁻¹' V ∩ tracelessPi (ι ⊕ κ) := ⟨hXV, hX⟩
      rwa [hpre] at hmem
    · intro hX
      rw [← hpre] at hX
      exact ⟨hX.2, hX.1, hmaps hX.2⟩
  rw [hEq]
  exact ((T.2.1 (ι ⊕ κ)).1 _ inter_subset_right).1.2 ⟨u, hu, rfl⟩
private theorem zero_mem_tracelessPi : (0 : σ → ComplexMatrix2) ∈ tracelessPi σ :=
  fun _ => ComplexMatrix2.traceless.zero_mem
private theorem holoToCoords_zero
    (T : ExpChartHolomorphy.ExpChartTheory) [Fintype ι] [Fintype κ]
    (v : Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless) {W : Set (ι ⊕ κ → ComplexMatrix2)}
    (hW : ComplexMatrix2.IsRelativelyOpen (GroupLieProduct ι κ) W) :
    IsHolomorphicToCoords v (Equiv.refl (ComplexCoordinates 0)) W fun _ => 0 := by
  refine ⟨hW, continuousOn_const, fun x hx => ?_⟩
  have hxP := subset_of_relOpen hW hx
  have hsup := supOpen_chartPreimage T hW hxP
  have hx0 : expChartAt x 0 = x := ((T.2.2.2.1 ι κ).1 x hxP).2.2.2.1
  refine ⟨tracelessPi (ι ⊕ κ) ∩ expChartAt x ⁻¹' W, ⟨zero_mem_tracelessPi, ?_⟩,
    fun X hX => hX.2, hsup, fun μ =>
    holoIn_toZero ((((T.2.1 (ι ⊕ κ)).1 _ hsup.1).2 v μ).1 hsup) _⟩
  rw [mem_preimage, hx0]
  exact hx
private theorem holoToCoords_mono
    (T : ExpChartHolomorphy.ExpChartTheory) [Fintype ι] [Fintype κ]
    {v : Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless} {n : ℕ} {c : E ≃ ComplexCoordinates n}
    {W W₀ : Set (ι ⊕ κ → ComplexMatrix2)} {Φ : (ι ⊕ κ → ComplexMatrix2) → E}
    (hΦ : IsHolomorphicToCoords v c W Φ)
    (hW₀ : ComplexMatrix2.IsRelativelyOpen (GroupLieProduct ι κ) W₀) (hsub : W₀ ⊆ W) :
    IsHolomorphicToCoords v c W₀ Φ := by
  refine ⟨hW₀, hΦ.2.1.mono hsub, fun x hx => ?_⟩
  obtain ⟨U, hU0, -, hU⟩ := hΦ.2.2 x (hsub hx)
  have hxP := subset_of_relOpen hW₀ hx
  have hx0 : expChartAt x 0 = x := ((T.2.2.2.1 ι κ).1 x hxP).2.2.2.1
  refine ⟨U ∩ (tracelessPi (ι ⊕ κ) ∩ expChartAt x ⁻¹' W₀),
    ⟨hU0, zero_mem_tracelessPi, ?_⟩, fun X hX => hX.2.2,
    holoTraceless_mono T hU (supOpen_inter hU.1 (supOpen_chartPreimage T hW₀ hxP))
      inter_subset_left⟩
  rw [mem_preimage, hx0]
  exact hx
private theorem holoToCoords_iUnion [Fintype ι] [Fintype κ]
    {v : Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless} {n : ℕ} {c : E ≃ ComplexCoordinates n}
    {J : Type} {U : J → Set (ι ⊕ κ → ComplexMatrix2)} {Φ : (ι ⊕ κ → ComplexMatrix2) → E}
    (hU : ∀ j, ComplexMatrix2.IsRelativelyOpen (GroupLieProduct ι κ) (U j))
    (hΦ : ∀ j, IsHolomorphicToCoords v c (U j) Φ) :
    IsHolomorphicToCoords v c (⋃ j, U j) Φ := by
  refine ⟨relOpen_iUnion hU, fun x hx => ?_, fun x hx => ?_⟩
  · obtain ⟨j, hj⟩ := mem_iUnion.1 hx
    refine ((hΦ j).2.1 x hj).mono_of_mem_nhdsWithin ?_
    obtain ⟨V, hV, hUV⟩ := hU j
    refine mem_nhdsWithin.2 ⟨V, hV, ?_, fun y hy => ?_⟩
    · rw [hUV] at hj
      exact hj.1
    · obtain ⟨j', hj'⟩ := mem_iUnion.1 hy.2
      rw [hUV]
      exact ⟨hy.1, subset_of_relOpen (hU j') hj'⟩
  · obtain ⟨j, hj⟩ := mem_iUnion.1 hx
    obtain ⟨V, hV0, hVW, hV⟩ := (hΦ j).2.2 x hj
    exact ⟨V, hV0, fun X hX => mem_iUnion.2 ⟨j, hVW X hX⟩, hV⟩
private theorem holoToProduct_iff (T : ExpChartHolomorphy.ExpChartTheory)
    [Fintype ι] [Fintype κ] {v : Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless}
    {W : Set (ι ⊕ κ → ComplexMatrix2)}
    {Ψ : (ι ⊕ κ → ComplexMatrix2) → ι' ⊕ κ' → ComplexMatrix2} :
    IsHolomorphicToProduct v W Ψ ↔ ComplexMatrix2.IsRelativelyOpen (GroupLieProduct ι κ) W ∧
      MapsTo Ψ W (GroupLieProduct ι' κ') ∧
      ∀ s, IsHolomorphicToCoords v ComplexCoordinates.matrixEquiv W fun x => Ψ x s := by
  have hgrp := fun Φ hW hmaps => (T.2.2.2.1 ι κ).2.1 v W Φ hW hmaps
  constructor
  · rintro ⟨hW, hleft, hright⟩
    refine ⟨hW, fun x hx s => ?_, fun s => ?_⟩
    · cases s with
      | inl i => exact (hleft i).2.1 hx
      | inr k => exact (hright k).1 hx
    · cases s with
      | inl i => exact (hgrp _ hW (hleft i).2.1).1 (hleft i)
      | inr k => exact (hright k).2
  · rintro ⟨hW, hmaps, hcoord⟩
    exact ⟨hW, fun i => (hgrp _ hW fun x hx => hmaps hx (.inl i)).2 (hcoord (.inl i)),
      fun k => ⟨fun x hx => hmaps hx (.inr k), hcoord (.inr k)⟩⟩
private def entryIndex {m : ℕ} (μ : σ ≃ Fin m) :
    Fin (ComplexCoordinates.productDim fun _ : Fin m => ComplexCoordinates.Component.matrix) ≃
      σ × Fin 4 :=
  (finSigmaFinEquiv (m := m) (n := fun _ => 4)).symm.trans
    ((Equiv.sigmaEquivProd (Fin m) (Fin 4)).trans (Equiv.prodCongr μ.symm (Equiv.refl _)))
private theorem matrixPiEquiv_apply' {m : ℕ} (μ : σ ≃ Fin m) (X : σ → ComplexMatrix2)
    (j : Fin (ComplexCoordinates.productDim fun _ : Fin m => ComplexCoordinates.Component.matrix)) :
    matrixPiEquiv μ X j =
      ComplexCoordinates.matrixEquiv (X (entryIndex μ j).1) (entryIndex μ j).2 :=
  rfl
private theorem component_holoVia {τ : Type} {m m' : ℕ} (μ : σ ≃ Fin m) (μ' : τ ≃ Fin m')
    {U : Set (σ → ComplexMatrix2)} {F : (σ → ComplexMatrix2) → τ → ComplexMatrix2}
    (hF : ComplexCoordinates.IsHolomorphicVia (matrixPiEquiv μ)
      (matrixPiEquiv μ') U F) (s : τ) :
    ComplexCoordinates.IsHolomorphicVia (matrixPiEquiv μ)
      ComplexCoordinates.matrixEquiv U fun x => F x s := by
  obtain ⟨hU, hcont, hdiff⟩ := hF
  have hentry : ∀ (Y : τ → ComplexMatrix2) (q : Fin 4), ComplexCoordinates.matrixEquiv (Y s) q =
      matrixPiEquiv μ' Y ((entryIndex μ').symm (s, q)) := by
    intro Y q
    rw [matrixPiEquiv_apply', Equiv.apply_symm_apply]
  have hfun : ComplexCoordinates.matrixEquiv ∘ (fun x => F x s) ∘
      (matrixPiEquiv μ).symm = fun z q =>
        (matrixPiEquiv μ' ∘ F ∘ (matrixPiEquiv μ).symm) z
          ((entryIndex μ').symm (s, q)) := by
    funext z q
    exact hentry _ q
  unfold ComplexCoordinates.IsHolomorphicVia
  rw [hfun]
  exact ⟨hU, continuousOn_pi.2 fun q => (continuous_apply _).comp_continuousOn hcont,
    fun a ha j => (hdiff a ha j).mono fun w hw =>
      differentiableAt_pi.2 fun q => differentiableAt_pi.1 hw _⟩
private theorem funUnique_symm_apply' (z : ℂ) (i : Fin 1) :
    (Equiv.funUnique (Fin 1) ℂ).symm z i = z := by
  simp
abbrev _root_.YangMills.DeltaSharedProofs.p23888 := @funUnique_symm_apply'
private theorem funUnique_symm_comp {X : Type} (g : X → ℂ) :
    (Equiv.funUnique (Fin 1) ℂ).symm ∘ g = fun x _ => g x := by
  funext x i
  exact funUnique_symm_apply' _ _
private theorem continuousOn_funUnique_iff {X : Type} [TopologicalSpace X] {S : Set X}
    {g : X → ℂ} :
    ContinuousOn ((Equiv.funUnique (Fin 1) ℂ).symm ∘ g) S ↔ ContinuousOn g S := by
  rw [funUnique_symm_comp]
  exact ⟨fun hg => continuousOn_pi.1 hg 0, fun hg => continuousOn_pi.2 fun _ => hg⟩
private theorem holoIn_funUnique_iff {N : ℕ} {U : Set (ComplexCoordinates N)}
    {g : ComplexCoordinates N → ℂ} :
    ComplexCoordinates.IsHolomorphicIn U ((Equiv.funUnique (Fin 1) ℂ).symm ∘ g) ↔
      IsOpen U ∧ ContinuousOn g U ∧ ∀ a ∈ U, ∀ j : Fin N, ∀ᶠ w in 𝓝 (0 : ℂ),
        DifferentiableAt ℂ (fun w : ℂ => g (a + w • ComplexCoordinates.stdBasisVector j)) w := by
  unfold ComplexCoordinates.IsHolomorphicIn
  rw [continuousOn_funUnique_iff, funUnique_symm_comp]
  refine and_congr_right fun _ => and_congr_right fun _ => ?_
  exact ⟨fun hg a ha j => (hg a ha j).mono fun w hw => differentiableAt_pi.1 hw 0,
    fun hg a ha j => (hg a ha j).mono fun w hw => differentiableAt_pi.2 fun _ => hw⟩
abbrev _root_.YangMills.DeltaSharedProofs.p501560 := @holoIn_funUnique_iff
private theorem holoIn_add {N : ℕ} {U : Set (ComplexCoordinates N)}
    {g₁ g₂ : ComplexCoordinates N → ℂ}
    (h₁ : ComplexCoordinates.IsHolomorphicIn U ((Equiv.funUnique (Fin 1) ℂ).symm ∘ g₁))
    (h₂ : ComplexCoordinates.IsHolomorphicIn U ((Equiv.funUnique (Fin 1) ℂ).symm ∘ g₂)) :
    ComplexCoordinates.IsHolomorphicIn U
      ((Equiv.funUnique (Fin 1) ℂ).symm ∘ fun z => g₁ z + g₂ z) := by
  obtain ⟨hU, c₁, d₁⟩ := holoIn_funUnique_iff.1 h₁
  obtain ⟨-, c₂, d₂⟩ := holoIn_funUnique_iff.1 h₂
  exact holoIn_funUnique_iff.2 ⟨hU, c₁.add c₂, fun a ha j =>
    ((d₁ a ha j).and (d₂ a ha j)).mono fun w hw => hw.1.add hw.2⟩
abbrev _root_.YangMills.DeltaSharedProofs.p502577 := @holoIn_add
private theorem holoIn_mul {N : ℕ} {U : Set (ComplexCoordinates N)}
    {g₁ g₂ : ComplexCoordinates N → ℂ}
    (h₁ : ComplexCoordinates.IsHolomorphicIn U ((Equiv.funUnique (Fin 1) ℂ).symm ∘ g₁))
    (h₂ : ComplexCoordinates.IsHolomorphicIn U ((Equiv.funUnique (Fin 1) ℂ).symm ∘ g₂)) :
    ComplexCoordinates.IsHolomorphicIn U
      ((Equiv.funUnique (Fin 1) ℂ).symm ∘ fun z => g₁ z * g₂ z) := by
  obtain ⟨hU, c₁, d₁⟩ := holoIn_funUnique_iff.1 h₁
  obtain ⟨-, c₂, d₂⟩ := holoIn_funUnique_iff.1 h₂
  exact holoIn_funUnique_iff.2 ⟨hU, c₁.mul c₂, fun a ha j =>
    ((d₁ a ha j).and (d₂ a ha j)).mono fun w hw => hw.1.mul hw.2⟩
private theorem exists_common_chartNhd (T : ExpChartHolomorphy.ExpChartTheory)
    [Fintype ι] [Fintype κ] {v : Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless} {n : ℕ}
    {c : E ≃ ComplexCoordinates n} {W : Set (ι ⊕ κ → ComplexMatrix2)}
    {f g : (ι ⊕ κ → ComplexMatrix2) → E}
    (hf : IsHolomorphicToCoords v c W f) (hg : IsHolomorphicToCoords v c W g)
    {x : ι ⊕ κ → ComplexMatrix2} (hx : x ∈ W) :
    ∃ U : Set (ι ⊕ κ → ComplexMatrix2), 0 ∈ U ∧ (∀ X ∈ U, expChartAt x X ∈ W) ∧
      IsHolomorphicOnTraceless v c U (f ∘ expChartAt x) ∧
      IsHolomorphicOnTraceless v c U (g ∘ expChartAt x) := by
  obtain ⟨U, hU0, hUW, hU⟩ := hf.2.2 x hx
  obtain ⟨U', hU0', -, hU'⟩ := hg.2.2 x hx
  have hsup := supOpen_inter hU.1 hU'.1
  exact ⟨U ∩ U', ⟨hU0, hU0'⟩, fun X hX => hUW X hX.1,
    holoTraceless_mono T hU hsup inter_subset_left,
    holoTraceless_mono T hU' hsup inter_subset_right⟩
private theorem compToProduct_holds (T : ExpChartHolomorphy.ExpChartTheory)
    (ι κ ι' κ' ι'' κ'' : Type) [Fintype ι] [Fintype κ] [Fintype ι'] [Fintype κ'] :
    CompToProduct ι κ ι' κ' ι'' κ'' := by
  intro v W Ψ hW hΨ W' Φ hΦ
  obtain ⟨hW', hmaps, hcoord⟩ := (holoToProduct_iff T).1 hΦ
  have hcomp := T.2.2.2.2.1 ι κ ι' κ' v W Ψ hW hΨ
  obtain ⟨hcont, hopen, -⟩ := hcomp (ComplexCoordinates 0) 0 (Equiv.refl _) W' (fun _ => 0)
    (holoToCoords_zero T v hW')
  exact ⟨hcont, hopen, (holoToProduct_iff T).2 ⟨hopen, fun x hx => hmaps hx.2, fun s =>
    (hcomp ComplexMatrix2 4 ComplexCoordinates.matrixEquiv W' (fun x => Φ x s) (hcoord s)).2.2⟩⟩
private theorem restrictToProduct_holds (T : ExpChartHolomorphy.ExpChartTheory)
    (ι κ ι' κ' : Type) [Fintype ι] [Fintype κ] : RestrictToProduct ι κ ι' κ' := by
  intro m m' μ μ' U F hF hmaps v
  have hrestr := (T.2.2.2.1 ι κ).2.2
  have hopen := (hrestr (ComplexCoordinates 0) 0 m (Equiv.refl _) μ U (fun _ => 0)
    (holoIn_toZero hF.1 _)).1
  exact (holoToProduct_iff T).2 ⟨hopen, hmaps, fun s =>
    (hrestr ComplexMatrix2 4 m ComplexCoordinates.matrixEquiv μ U (fun x => F x s)
      (component_holoVia μ μ' hF s)).2 v⟩
private theorem addMul_holds (T : ExpChartHolomorphy.ExpChartTheory)
    (ι κ : Type) [Fintype ι] [Fintype κ] : AddMul ι κ := by
  intro v W f g hf hg
  have cf := continuousOn_funUnique_iff.1 hf.2.1
  have cg := continuousOn_funUnique_iff.1 hg.2.1
  refine ⟨⟨hf.1, continuousOn_funUnique_iff.2 (cf.add cg), fun x hx => ?_⟩,
    ⟨hf.1, continuousOn_funUnique_iff.2 (cf.mul cg), fun x hx => ?_⟩⟩
  · obtain ⟨U, hU0, hUW, h₁, h₂⟩ := exists_common_chartNhd T hf hg hx
    exact ⟨U, hU0, hUW, h₁.1, fun μ => holoIn_add (h₁.2 μ) (h₂.2 μ)⟩
  · obtain ⟨U, hU0, hUW, h₁, h₂⟩ := exists_common_chartNhd T hf hg hx
    exact ⟨U, hU0, hUW, h₁.1, fun μ => holoIn_mul (h₁.2 μ) (h₂.2 μ)⟩
private theorem iUnionToCoords_holds (T : ExpChartHolomorphy.ExpChartTheory)
    (ι κ : Type) [Fintype ι] [Fintype κ] : IUnionToCoords ι κ := by
  intro v J U hU E n c Φ
  exact ⟨fun hΦ j => holoToCoords_mono T hΦ (hU j) (subset_iUnion U j),
    holoToCoords_iUnion hU⟩
private theorem iUnionToProduct_holds (T : ExpChartHolomorphy.ExpChartTheory)
    (ι κ ι' κ' : Type) [Fintype ι] [Fintype κ] : IUnionToProduct ι κ ι' κ' := by
  intro v J U hU Φ
  constructor
  · intro hΦ j
    obtain ⟨-, hmaps, hcoord⟩ := (holoToProduct_iff T).1 hΦ
    exact (holoToProduct_iff T).2 ⟨hU j, hmaps.mono_left (subset_iUnion U j), fun s =>
      holoToCoords_mono T (hcoord s) (hU j) (subset_iUnion U j)⟩
  · intro hΦ
    have hparts := fun j => (holoToProduct_iff T).1 (hΦ j)
    refine (holoToProduct_iff T).2 ⟨relOpen_iUnion hU, fun x hx => ?_, fun s =>
      holoToCoords_iUnion hU fun j => (hparts j).2.2 s⟩
    obtain ⟨j, hj⟩ := mem_iUnion.1 hx
    exact (hparts j).2.1 hj
private theorem monoToProduct_holds
    (T : ExpChartHolomorphy.ExpChartTheory) (ι κ ι' κ' : Type) [Fintype ι] [Fintype κ] :
    MonoToProduct ι κ ι' κ' := by
  intro v W W₀ Φ hΦ hW₀ hsub
  obtain ⟨-, hmaps, hcoord⟩ := (holoToProduct_iff T).1 hΦ
  exact (holoToProduct_iff T).2 ⟨hW₀, hmaps.mono_left hsub, fun s =>
    holoToCoords_mono T (hcoord s) hW₀ hsub⟩
private theorem ofLieCoords_holds (T : ExpChartHolomorphy.ExpChartTheory)
    (ι κ : Type) [Fintype ι] [Fintype κ] [IsEmpty ι] : OfLieCoords ι κ := by
  intro W hW
  have hprod : GroupLieProduct ι κ = tracelessPi (ι ⊕ κ) := by
    ext X
    constructor
    · intro hX s
      cases s with
      | inl i => exact isEmptyElim i
      | inr k => exact hX (.inr k)
    · intro hX s
      cases s with
      | inl i => exact isEmptyElim i
      | inr k => exact hX (.inr k)
  have hsub : W ⊆ tracelessPi (ι ⊕ κ) := hprod ▸ subset_of_relOpen hW
  have hsame := (T.2.1 (ι ⊕ κ)).1 W hsub
  have hsup : IsSupOpen W := hsame.1.2 (hprod ▸ hW)
  refine ⟨fun E n c v v' Φ => ?_, fun v μ => (hsame.2 v μ).1 hsup⟩
  rw [T.2.2.2.2.2.2 ι κ E n c v W Φ hW, (T.2.1 (ι ⊕ κ)).2.1 E n c v v' W Φ]
  exact ⟨fun hΦ => hΦ.2, fun hΦ => ⟨hsup, hΦ⟩⟩
theorem properties_of_expChartTheory (T : ExpChartHolomorphy.ExpChartTheory) : Properties :=
  ⟨fun ι κ ι' κ' _ _ _ _ => T.2.2.2.2.1 ι κ ι' κ',
    fun ι κ ι' κ' ι'' κ'' _ _ _ _ _ _ => compToProduct_holds T ι κ ι' κ' ι'' κ'',
    fun ι κ _ _ => (T.2.2.2.1 ι κ).2.2,
    fun ι κ ι' κ' _ _ _ _ => restrictToProduct_holds T ι κ ι' κ',
    fun ι κ _ _ => addMul_holds T ι κ,
    fun ι κ _ _ => iUnionToCoords_holds T ι κ,
    fun ι κ ι' κ' _ _ _ _ => iUnionToProduct_holds T ι κ ι' κ',
    fun _ _ _ _ _ _ _ _ _ _ _ hΦ hW₀ hsub => holoToCoords_mono T hΦ hW₀ hsub,
    fun ι κ ι' κ' _ _ _ _ => monoToProduct_holds T ι κ ι' κ',
    fun ι κ _ _ _ => ofLieCoords_holds T ι κ⟩
end YangMills.Construction.Matrices.GroupLieProduct.HolomorphicCalculus
