import YangMills.Construction.Lattice.ActionOfABareGaugeTransformation
import YangMills.Construction.Towers.AveragingIsAnalyticAndCovariantOnTheSidesProof
import YangMills.Construction.Gaussian.KernelGaussianIntegral
import YangMills.Construction.Lattice.AveragingMapContinuousOnEachCaseSetProof
import YangMills.Construction.Lattice.LevelBondOrientationDichotomy
import YangMills.Construction.Matrices.LinearMapsCompositesAndCoordinatesOfRealAnalyticMapsProof
import YangMills.Construction.Towers.AveragingOnSmallFamiliesOfTheChartAtOneProof
import YangMills.Construction.Towers.CompositesOfTheLiftsAndLayersOfSites
import YangMills.Construction.Towers.DerivativeOfTheContourLogarithmAlongCurvesProof
import YangMills.Construction.Towers.TheCriticalBranch
import Mathlib
set_option autoImplicit false
open Filter Set
open scoped Topology Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction
open Matrices
namespace Tower.ProlongCompositesProof
open Matrices.GroupLieProduct Matrices.GroupLieProduct.Subspaces
theorem gaussian_kernel_integral (hI : Gaussian.KernelIntegral.GaussianIntegralOnKernel) :
    ∀ (E F : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
      [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F] (M : E →ₗ[ℝ] F)
      (T : QuadraticForm ℝ (LinearMap.ker M)), Function.Surjective M → T.PosDef →
        GaussianConstraint.IntegrableGaussianOnKernel M T ∧
          0 < GaussianConstraint.constrainedGaussianNumber M T := by
  intro E F _ _ _ _ _ _ M T hM hT
  obtain ⟨hdet, d, -, -, hint, hpos, -⟩ := hI E F M hM T hT
  exact ⟨hint, mul_pos (Real.rpow_pos_of_pos hdet _) hpos⟩
section Layers
variable {L m k : ℕ}
theorem sublattice_antitone (hL : 0 < L) {i j : ℕ} (h : i ≤ j) :
    PeriodicLattice.sublattice L m (PeriodicLattice.levelDepth k j) ≤
      PeriodicLattice.sublattice L m (PeriodicLattice.levelDepth k i) :=
  PeriodicLattice.sublattice_mono hL m (by simp only [PeriodicLattice.levelDepth]; omega)
def toBase {i : ℕ} (x : Vertex L m k i) : Vertex L m k 0 :=
  x.toSublattice (PeriodicLattice.levelDepth k 0)
theorem coe_toBase (hL : 0 < L) {i : ℕ} (x : Vertex L m k i) :
    ((toBase x : Vertex L m k 0) : PeriodicLattice.FourTorus L m) = x := by apply _root_.YangMills.Construction.PeriodicLattice.coe_toSublattice_finest <;> assumption
theorem existsUnique_vertexLayer (hL : 0 < L) (x : Vertex L m k 0)
    (hx : (x : PeriodicLattice.FourTorus L m) ∉
      PeriodicLattice.sublattice L m (PeriodicLattice.levelDepth k k)) :
    ∃! i : Fin k, IsInVertexLayer L m k i (x : PeriodicLattice.FourTorus L m) := by
  classical
  have hex : ∃ j : ℕ, (x : PeriodicLattice.FourTorus L m) ∉
      PeriodicLattice.sublattice L m (PeriodicLattice.levelDepth k j) := ⟨k, hx⟩
  have hle : Nat.find hex ≤ k := Nat.find_min' hex hx
  have hne : Nat.find hex ≠ 0 := fun h0 => by
    have := Nat.find_spec hex
    rw [h0] at this
    exact this x.2
  obtain ⟨i, hi⟩ := Nat.exists_eq_succ_of_ne_zero hne
  have hik : i < k := by omega
  have hin : (x : PeriodicLattice.FourTorus L m) ∈
      PeriodicLattice.sublattice L m (PeriodicLattice.levelDepth k i) := by
    by_contra h
    have := Nat.find_min' hex h
    omega
  have hout : (x : PeriodicLattice.FourTorus L m) ∉
      PeriodicLattice.sublattice L m (PeriodicLattice.levelDepth k (i + 1)) := by
    have := Nat.find_spec hex
    rwa [hi] at this
  refine ⟨⟨i, hik⟩, ⟨hin, hout⟩, ?_⟩
  rintro ⟨i', hi'⟩ ⟨hin', hout'⟩
  refine Fin.ext ?_
  simp only
  rcases lt_trichotomy i' i with h | h | h
  · exact absurd (sublattice_antitone hL h hin) hout'
  · exact h
  · exact absurd (sublattice_antitone hL h hin') hout
theorem fineOnly_not_mem_top (hL : 0 < L) {i : ℕ} (hi : i < k) (y : FineOnlyVertex L m k i) :
    (y.1 : PeriodicLattice.FourTorus L m) ∉
      PeriodicLattice.sublattice L m (PeriodicLattice.levelDepth k k) :=
  fun h => y.2 (sublattice_antitone hL hi h)
abbrev OffTopVertex (L m k : ℕ) : Type :=
  {x : Vertex L m k 0 //
    (x : PeriodicLattice.FourTorus L m) ∉
      PeriodicLattice.sublattice L m (PeriodicLattice.levelDepth k k)}
def layerIndex (hL : 0 < L) (x : OffTopVertex L m k) : Fin k :=
  (existsUnique_vertexLayer hL x.1 x.2).choose
theorem layerIndex_spec (hL : 0 < L) (x : OffTopVertex L m k) :
    IsInVertexLayer L m k (layerIndex hL x)
      ((x.1 : Vertex L m k 0) : PeriodicLattice.FourTorus L m) :=
  (existsUnique_vertexLayer hL x.1 x.2).choose_spec.1
def asLayerVertex (hL : 0 < L) (x : OffTopVertex L m k) :
    FineOnlyVertex L m k (layerIndex hL x) :=
  ⟨⟨x.1, (layerIndex_spec hL x).1⟩, (layerIndex_spec hL x).2⟩
def offTopEquivSigma (hL : 0 < L) : OffTopVertex L m k ≃ Σ i : Fin k, FineOnlyVertex L m k i where
  toFun x := ⟨layerIndex hL x, asLayerVertex hL x⟩
  invFun p := ⟨toBase p.2.1, by
    rw [coe_toBase hL]
    exact fineOnly_not_mem_top hL p.1.2 p.2⟩
  left_inv x := by
    refine Subtype.ext (Subtype.ext ?_)
    exact coe_toBase hL _
  right_inv := by
    rintro ⟨i, y⟩
    set x : OffTopVertex L m k := ⟨toBase y.1, by
      rw [coe_toBase hL]
      exact fineOnly_not_mem_top hL i.2 y⟩ with hx
    have hc : ((x.1 : Vertex L m k 0) : PeriodicLattice.FourTorus L m) = y.1 := coe_toBase hL _
    have hlay : IsInVertexLayer L m k i
        ((x.1 : Vertex L m k 0) : PeriodicLattice.FourTorus L m) := by
      rw [hc]
      exact ⟨y.1.2, y.2⟩
    have hi : layerIndex hL x = i :=
      (existsUnique_vertexLayer hL x.1 x.2).unique (layerIndex_spec hL x) hlay
    have key : ∀ (i' : Fin k) (hi' : i' = i) (z : FineOnlyVertex L m k i'),
        ((z.1 : Vertex L m k i') : PeriodicLattice.FourTorus L m) = y.1 →
        (⟨i', z⟩ : Σ i : Fin k, FineOnlyVertex L m k i) = ⟨i, y⟩ := by
      rintro i' rfl z hz
      exact congrArg (Sigma.mk i') (Subtype.ext (Subtype.ext hz))
    exact key _ hi _ hc
theorem toBase_offTopEquivSigma (hL : 0 < L) (x : OffTopVertex L m k) :
    toBase (offTopEquivSigma hL x).2.1 = x.1 :=
  congrArg Subtype.val ((offTopEquivSigma hL).symm_apply_apply x)
def glueLayers (hL : 0 < L) (f : ∀ i : Fin k, FineOnlyVertex L m k i → ComplexMatrix2) :
    Vertex L m k 0 → ComplexMatrix2 :=
  open Classical in fun x =>
    if h : (x : PeriodicLattice.FourTorus L m) ∈
        PeriodicLattice.sublattice L m (PeriodicLattice.levelDepth k k) then 0
    else f (offTopEquivSigma hL ⟨x, h⟩).1 (offTopEquivSigma hL ⟨x, h⟩).2
theorem glueLayers_toBase (hL : 0 < L) (f : ∀ i : Fin k, FineOnlyVertex L m k i → ComplexMatrix2)
    (i : Fin k) (y : FineOnlyVertex L m k i) : glueLayers hL f (toBase y.1) = f i y := by
  have hnot : ((toBase y.1 : Vertex L m k 0) : PeriodicLattice.FourTorus L m) ∉
      PeriodicLattice.sublattice L m (PeriodicLattice.levelDepth k k) := by
    rw [coe_toBase hL]
    exact fineOnly_not_mem_top hL i.2 y
  have he : offTopEquivSigma hL (⟨toBase y.1, hnot⟩ : OffTopVertex L m k) = ⟨i, y⟩ :=
    (offTopEquivSigma hL).apply_symm_apply ⟨i, y⟩
  simp only [glueLayers, dif_neg hnot]
  have key : ∀ p : (Σ i : Fin k, FineOnlyVertex L m k i), p = ⟨i, y⟩ → f p.1 p.2 = f i y := by
    rintro _ rfl
    rfl
  exact key _ he
theorem eq_zero_of_restrictToLayer_eq_zero (hL : 0 < L) {l : Vertex L m k 0 → ComplexMatrix2}
    (hl : l ∈ vertexFunctionsVanishingOnTop L m k)
    (h : ∀ (i : Fin k) (y : FineOnlyVertex L m k i), l (toBase y.1) = 0) : l = 0 := by
  funext x
  by_cases hx : (x : PeriodicLattice.FourTorus L m) ∈
      PeriodicLattice.sublattice L m (PeriodicLattice.levelDepth k k)
  · exact hl.2 x hx
  · have hb : ((offTopEquivSigma hL).symm (offTopEquivSigma hL ⟨x, hx⟩)) = ⟨x, hx⟩ :=
      (offTopEquivSigma hL).symm_apply_apply _
    have := h (offTopEquivSigma hL ⟨x, hx⟩).1 (offTopEquivSigma hL ⟨x, hx⟩).2
    have hx' : toBase (offTopEquivSigma hL ⟨x, hx⟩).2.1 = x := congrArg Subtype.val hb
    rw [hx'] at this
    exact this
theorem vertexLayer_decomposition (hL : 0 < L) : VertexLayerDecomposition L m k := by
  classical
  refine ⟨fun x hx => existsUnique_vertexLayer hL x hx, ?_, ?_⟩
  · let Φ : vertexFunctionsVanishingOnTop L m k →ₗ[ℝ] ∀ i : Fin k, fineOnlyFunctions L m k i :=
      { toFun := fun l i => ⟨restrictToLayer i (l : Vertex L m k 0 → ComplexMatrix2),
          fun y _ => l.2.1 (toBase y.1) (mem_univ _)⟩
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl }
    have hinj : Function.Injective Φ := by
      refine (injective_iff_map_eq_zero Φ).mpr fun l hl => ?_
      refine Subtype.ext (eq_zero_of_restrictToLayer_eq_zero hL l.2 fun i y => ?_)
      have := congrArg (fun g => ((g i : fineOnlyFunctions L m k i) :
        FineOnlyVertex L m k i → ComplexMatrix2) y) hl
      exact this
    have hsurj : Function.Surjective Φ := by
      intro f
      let g := glueLayers hL (fun i => ((f i : fineOnlyFunctions L m k i) :
        FineOnlyVertex L m k i → ComplexMatrix2))
      have hg : g ∈ vertexFunctionsVanishingOnTop L m k := by
        refine ⟨fun x _ => ?_, fun x hx => ?_⟩
        · by_cases hx : (x : PeriodicLattice.FourTorus L m) ∈
              PeriodicLattice.sublattice L m (PeriodicLattice.levelDepth k k)
          · simp only [g, glueLayers, dif_pos hx]
            exact ComplexMatrix2.hermitianTraceless.zero_mem
          · simp only [g, glueLayers, dif_neg hx]
            exact (f _).2 _ (mem_univ _)
        · simp only [g, glueLayers, dif_pos hx]
      refine ⟨⟨g, hg⟩, ?_⟩
      funext i
      refine Subtype.ext (funext fun y => ?_)
      exact glueLayers_toBase hL (fun i => ((f i : fineOnlyFunctions L m k i) :
        FineOnlyVertex L m k i → ComplexMatrix2)) i y
    exact ⟨LinearEquiv.ofBijective Φ ⟨hinj, hsurj⟩, fun _ _ => rfl⟩
  · intro l hl l' hl'
    have : Finite (Vertex L m k 0) := SeparatedSequences.BaseParameters.site_finite hL m _
    have : Fintype (Vertex L m k 0) := Fintype.ofFinite _
    have : ∀ i : Fin k, Finite (FineOnlyVertex L m k i) := fun i =>
      have : Finite (Vertex L m k i) := SeparatedSequences.BaseParameters.site_finite hL m _
      inferInstance
    have : ∀ i : Fin k, Fintype (FineOnlyVertex L m k i) := fun i => Fintype.ofFinite _
    let g : Vertex L m k 0 → ℂ := fun x => ComplexMatrix2.halfTrace (l x * l' x)
    have hg0 : ∀ x : Vertex L m k 0, (x : PeriodicLattice.FourTorus L m) ∈
        PeriodicLattice.sublattice L m (PeriodicLattice.levelDepth k k) → g x = 0 := by
      intro x hx
      simp only [g, hl.2 x hx, zero_mul]
      simp [ComplexMatrix2.halfTrace]
    have hsum : ∑ x, g x = ∑ x : OffTopVertex L m k, g x.1 := by
      rw [← Fintype.sum_subtype_add_sum_subtype (fun x : Vertex L m k 0 =>
        (x : PeriodicLattice.FourTorus L m) ∉
          PeriodicLattice.sublattice L m (PeriodicLattice.levelDepth k k)) g]
      have : ∑ x : {x : Vertex L m k 0 // ¬ (x : PeriodicLattice.FourTorus L m) ∉
          PeriodicLattice.sublattice L m (PeriodicLattice.levelDepth k k)}, g x.1 = 0 :=
        Finset.sum_eq_zero fun x _ => hg0 x.1 (not_not.mp x.2)
      rw [this, add_zero]
    have h₁ : ∑ x : OffTopVertex L m k, g x.1 =
        ∑ p : (Σ i : Fin k, FineOnlyVertex L m k i), g (toBase p.2.1) :=
      Fintype.sum_equiv (offTopEquivSigma hL) _ _ fun x => by rw [toBase_offTopEquivSigma]
    have h₂ : ∑ p : (Σ i : Fin k, FineOnlyVertex L m k i), g (toBase p.2.1) =
        ∑ i : Fin k, ∑ y : FineOnlyVertex L m k i, g (toBase y.1) :=
      Fintype.sum_sigma _
    have hp : traceFinsumPairing l l' = ∑ x, g x := finsum_eq_sum_of_fintype _
    have hq : ∀ i : Fin k, fineOnlyPairing (restrictToLayer (L := L) (n := m) (k := k) i l)
        (restrictToLayer i l') = ∑ y : FineOnlyVertex L m k i, g (toBase y.1) := fun i =>
      finsum_eq_sum_of_fintype _
    rw [hp, hsum, h₁, h₂]
    exact Finset.sum_congr rfl fun i _ => (hq i).symm
end Layers
section Plumbing
variable {L m k i j : ℕ}
theorem isPositive_or_opposite (b : Edge L m k i) :
    b.IsPositivelyOriented ∨ b.opposite.IsPositivelyOriented := by apply _root_.YangMills.Construction.Tower.TrivialFieldAverages.edge_positive_or_opposite <;> assumption
theorem inv_mem_compactGaugeGroup {X : ComplexMatrix2}
    (hX : X ∈ PeriodicLattice.compactGaugeGroup) :
    X⁻¹ ∈ PeriodicLattice.compactGaugeGroup := by apply _root_.YangMills.Construction.PeriodicLattice.BlockAverageContinuity.inv_mem_compactGaugeGroup <;> assumption
theorem continuousWithinAt_of_positiveEdges {Y : Type} [TopologicalSpace Y]
    {φ : Y → Edge L m k j → ComplexMatrix2} {s : Set Y} {y : Y} (hy : y ∈ s)
    (hconf : MapsTo φ s (fieldSpace L m k j))
    (hpos : ∀ c : Edge L m k j, c.IsPositivelyOriented →
      ContinuousWithinAt (fun y => φ y c) s y) :
    ContinuousWithinAt φ s y := by apply _root_.YangMills.Construction.Tower.IdentityLieBallSmoothing.continuousWithinAt_of_positivelyOriented <;> assumption
theorem fieldOfPositiveValues_restrict {V : Edge L m k i → ComplexMatrix2}
    (hV : V ∈ fieldSpace L m k i) : fieldOfPositiveValues (restrictToPositiveEdges V) = V := by apply _root_.YangMills.SharedProofs.p407 <;> assumption
theorem subset_of_isRelativelyOpen {Y : Type} [TopologicalSpace Y] {P D : Set Y}
    (h : ComplexMatrix2.IsRelativelyOpen P D) : D ⊆ P := by apply _root_.YangMills.SharedProofs.p9583 <;> assumption
theorem exists_isOpen_restrict {𝒰 : Set (Edge L m k i → ComplexMatrix2)}
    (h : IsOpenFieldSet PeriodicLattice.compactGaugeGroup 𝒰) :
    ∃ O : Set (PositiveEdge L m k i → ComplexMatrix2), IsOpen O ∧
      ∀ V ∈ fieldSpace L m k i, V ∈ 𝒰 ↔ restrictToPositiveEdges V ∈ O := by apply _root_.YangMills.SharedProofs.p1531 <;> assumption
theorem continuous_restrictToPositiveEdges :
    Continuous (restrictToPositiveEdges :
      (Edge L m k i → ComplexMatrix2) → PositiveEdge L m k i → ComplexMatrix2) :=
  continuous_pi fun _ => continuous_apply _
theorem eventually_mem_of_isOpenNhdOfOne {𝒰 : Set (Edge L m k i → ComplexMatrix2)}
    (h : IsOpenNhdOfOne 𝒰) :
    ∀ᶠ V in 𝓝[fieldSpace L m k i] trivialField L m k i, V ∈ 𝒰 := by apply _root_.YangMills.DeltaSharedProofs.p501856 <;> assumption
def tracelessEntries : ComplexMatrix2.traceless ≃ₗ[ℂ] (Fin 3 → ℂ) where
  toFun X := ![(X : ComplexMatrix2) 0 0, (X : ComplexMatrix2) 0 1, (X : ComplexMatrix2) 1 0]
  map_add' X Y := by
    ext a
    fin_cases a <;> simp
  map_smul' c X := by
    ext a
    fin_cases a <;> simp
  invFun z := ⟨!![z 0, z 1; z 2, -z 0], by
    change Matrix.trace _ = 0
    simp [Matrix.trace_fin_two]⟩
  left_inv X := by
    have h : Matrix.trace (X : ComplexMatrix2) = 0 := X.2
    rw [Matrix.trace_fin_two] at h
    apply Subtype.ext
    ext a b
    fin_cases a <;> fin_cases b <;> simp
    linear_combination -h
  right_inv z := by
    ext a
    fin_cases a <;> simp
theorem continuousOn_of_isAnalyticFieldMap {𝒰 : Set (Edge L m k j → ComplexMatrix2)}
    {φ : (Edge L m k j → ComplexMatrix2) → Edge L m k i → ComplexMatrix2}
    (h : IsAnalyticFieldMap 𝒰 φ) :
    ContinuousOn φ 𝒰 := by
  have b : Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless :=
    Module.Basis.ofEquivFun tracelessEntries
  have h𝒰 : 𝒰 ⊆ fieldSpace L m k j := h.1.1
  obtain ⟨-, hφ, i₁, i₂, hA⟩ := h
  intro V hV
  refine continuousWithinAt_of_positiveEdges hV hφ fun c hc => ?_
  let ρ : (Edge L m k j → ComplexMatrix2) → (PositiveEdge L m k j ⊕ Empty → ComplexMatrix2) :=
    fun V' => ofParts (restrictToPositiveEdges V') Empty.elim
  have hρ : Continuous ρ := by
    refine continuous_pi fun r => ?_
    rcases r with r | e
    · exact continuous_apply _
    · exact e.elim
  have hρ𝒲 : ∀ V' ∈ 𝒰, ρ V' ∈ {q | fieldOfPositiveValues (groupComponent q) ∈ 𝒰} := by
    intro V' h'
    change fieldOfPositiveValues (restrictToPositiveEdges V') ∈ 𝒰
    rw [fieldOfPositiveValues_restrict (h𝒰 h')]
    exact h'
  obtain ⟨𝒳, hp, ⟨Ω, hΩ, hX⟩, hin, Ψ, hΨ, heq⟩ := hA.2.2.2 (ρ V) (hρ𝒲 V hV)
  have hΨc : ContinuousOn (fun q => Ψ q (.inl ⟨c, hc⟩)) 𝒳 := ((hΨ b).2.1 ⟨c, hc⟩).2.2.1
  have hpΩ : ρ V ∈ Ω := by
    rw [hX] at hp
    exact hp.1
  have hSP : ∀ V' ∈ 𝒰, ρ V' ∈ subspaceTimesGroup ⊥ (PositiveEdge L m k j) :=
    fun V' h' => subset_of_isRelativelyOpen hA.1.2 (hρ𝒲 V' h')
  have hP : ∀ V' ∈ 𝒰, ρ V' ∈ Matrices.GroupLieProduct (PositiveEdge L m k j) Empty := by
    intro V' h' r
    rcases r with r | e
    · exact (Matrix.mem_specialUnitaryGroup_iff.1 ((hSP V' h').2 r)).2
    · exact e.elim
  have hval : ∀ V' ∈ 𝒰, ρ V' ∈ 𝒳 → φ V' c = Ψ (ρ V') (.inl ⟨c, hc⟩) := by
    intro V' h' hX'
    rw [heq ⟨hX', hSP V' h'⟩]
    change φ V' c =
      restrictToPositiveEdges (φ (fieldOfPositiveValues (restrictToPositiveEdges V'))) ⟨c, hc⟩
    rw [fieldOfPositiveValues_restrict (h𝒰 h')]
    rfl
  have hev : ∀ᶠ V' in 𝓝[𝒰] V, V' ∈ 𝒰 ∧ ρ V' ∈ 𝒳 := by
    filter_upwards [self_mem_nhdsWithin,
      mem_nhdsWithin_of_mem_nhds (hρ.continuousAt (hΩ.mem_nhds hpΩ))] with V' h1 h2
    refine ⟨h1, ?_⟩
    rw [hX]
    exact ⟨h2, hP V' h1⟩
  have hcomp : ContinuousWithinAt (fun V' => Ψ (ρ V') (.inl ⟨c, hc⟩)) 𝒰 V :=
    (hΨc _ hp).tendsto.comp (tendsto_nhdsWithin_iff.2
      ⟨hρ.continuousWithinAt.tendsto, hev.mono fun _ h => h.2⟩)
  exact hcomp.congr_of_eventuallyEq (hev.mono fun V' h => hval V' h.1 h.2) (hval V hV hp)
end Plumbing
section Composites
variable {L m k : ℕ}
theorem prolongIter_self (b : CriticalBranchData L m k) {j : ℕ} (h : j ≤ j) :
    b.prolongIter h = id := by
  simp [CriticalBranchData.prolongIter, Nat.leRec_self]
theorem prolongIter_succ (b : CriticalBranchData L m k) {j t : ℕ} (h : j ≤ t) (h' : j ≤ t + 1) :
    b.prolongIter h' = b.prolongIter h ∘ b.prolong t := by
  simp [CriticalBranchData.prolongIter, Nat.leRec_succ _ _ h]
theorem prolongComp_prolongIter (b : CriticalBranchData L m k) {j t : ℕ} (h : j ≤ t) :
    ∀ W : Edge L m k t → ComplexMatrix2, b.prolongComp j (b.prolongIter h W) = b.prolongComp t W := by
  induction t, h using Nat.le_induction with
  | base =>
    intro W
    rw [prolongIter_self]
    rfl
  | succ t h ih =>
    intro W
    rw [prolongIter_succ b h]
    exact ih (b.prolong t W)
theorem tendsto_prolongIter (b : CriticalBranchData L m k)
    (hlift : ∀ i < k, Tendsto (b.prolong i)
      (𝓝[fieldSpace L m k (i + 1)] trivialField L m k (i + 1))
      (𝓝[fieldSpace L m k i] trivialField L m k i)) {j t : ℕ} (h : j ≤ t) :
    t ≤ k → Tendsto (b.prolongIter h)
      (𝓝[fieldSpace L m k t] trivialField L m k t)
      (𝓝[fieldSpace L m k j] trivialField L m k j) := by
  induction t, h using Nat.le_induction with
  | base =>
    intro _
    rw [prolongIter_self]
    exact tendsto_id
  | succ t h ih =>
    intro ht
    rw [prolongIter_succ b h]
    exact (ih (by omega)).comp (hlift t (by omega))
theorem tendsto_prolong {b : CriticalBranchData L m k} (hb : b.IsCritical) {i : ℕ} (hi : i < k) :
    Tendsto (b.prolong i) (𝓝[fieldSpace L m k (i + 1)] trivialField L m k (i + 1))
      (𝓝[fieldSpace L m k i] trivialField L m k i) := by
  obtain ⟨𝒰, hU, hA⟩ := hb.analytic_prolong i hi
  have hnear := eventually_mem_of_isOpenNhdOfOne hU
  have hc := continuousOn_of_isAnalyticFieldMap hA _ hU.2
  refine tendsto_nhdsWithin_iff.mpr ⟨?_, hnear.mono fun W hW => hA.2.1 hW⟩
  have h := hc.tendsto.mono_left (nhdsWithin_le_of_mem (Filter.mem_of_superset hnear fun _ h => h))
  rwa [hb.prolong_trivial i hi] at h
theorem prolongIter_spec (hB : CriticalBranchExists)
    (hL : Conventions.IsAdmissibleBlockingFactor L)
    (hm : 0 < m) : ProlongItersNearIdentity L m k := by
  have hb : (chosenCriticalBranch L m k).IsCritical := Classical.epsilon_spec (hB L m k hL hm)
  refine ⟨fun j h => tendsto_prolongIter _ (fun i hi => tendsto_prolong hb hi) h le_rfl,
    fun j h => Eventually.of_forall fun W => prolongComp_prolongIter _ h W,
    Eventually.of_forall fun W => prolongComp_prolongIter _ (Nat.zero_le k) W⟩
end Composites
section Derivatives
open YangMills.Construction.Tower.ContourLogarithms (expCurve vertexCubePairs)
theorem exists_analyticAt_eventuallyEq {ι : Type} [Fintype ι] {D : Set (ι → ComplexMatrix2)}
    {f : (ι → ComplexMatrix2) → Fin 1 → ComplexMatrix2}
    (hf : ComplexMatrix2.IsRealAnalyticBetween (fun _ : ι => ComplexMatrix2.FactorKind.group)
      (fun _ : Fin 1 => ComplexMatrix2.FactorKind.group) D f) {x : ι → ComplexMatrix2}
    (hx : x ∈ D) :
    ∃ Φ : (ι → ComplexMatrix2) → Fin 1 → ComplexMatrix2,
      AnalyticAt ℂ Φ x ∧ ∀ᶠ y in 𝓝[D] x, f y = Φ y := by apply _root_.YangMills.SharedProofs.p99213 <;> assumption
theorem differentiableAt_logSeries
    (hH : Coordinates.ComplexCoordinates.PowerSeriesHolomorphy.Properties) {X : ComplexMatrix2}
    (hX : ComplexMatrix2.operatorNorm (X - 1) < 1) :
    DifferentiableAt ℝ ComplexMatrix2.logSeries X := by apply _root_.YangMills.SharedProofs.p25178 <;> assumption
theorem logSeries_mem (hExp : ComplexMatrix2.ExpLogEstimates) {X : ComplexMatrix2}
    (hX : X ∈ PeriodicLattice.compactGaugeGroup) (hs : ComplexMatrix2.operatorNorm (X - 1) < 1) :
    Complex.I⁻¹ • ComplexMatrix2.logSeries X ∈ ComplexMatrix2.hermitianTraceless := by apply _root_.YangMills.SharedProofs.p12580 <;> assumption
theorem hasDerivAt_mem_hermitianTraceless {f : ℝ → ComplexMatrix2} {d : ComplexMatrix2}
    (hf : HasDerivAt f d 0)
    (hmem : ∀ᶠ t in 𝓝 (0 : ℝ), f t ∈ ComplexMatrix2.hermitianTraceless) :
    d ∈ ComplexMatrix2.hermitianTraceless := by apply _root_.YangMills.SharedProofs.p35912 <;> assumption
variable {L m k i j : ℕ}
theorem expCurve_eq_expTwist (V B : Edge L m k i → ComplexMatrix2) (t : ℝ) :
    expCurve V B t = PeriodicLattice.expTwist (t • B) V := by apply _root_.YangMills.SharedProofs.p66923 <;> assumption
theorem expCurve_zero {V : Edge L m k i → ComplexMatrix2} (B : Edge L m k i → ComplexMatrix2)
    (hV : V ∈ fieldSpace L m k i) : expCurve V B 0 = V := by apply _root_.YangMills.SharedProofs.p30759 <;> assumption
theorem meanContourHolonomy_mem {W : Edge L m k i → ComplexMatrix2} {y : Vertex L m k (i + 1)}
    {x : Vertex L m k i} (h : PeriodicLattice.HasContourMean W y x) :
    PeriodicLattice.meanContourHolonomy W y x ∈ PeriodicLattice.compactGaugeGroup := by apply _root_.YangMills.SharedProofs.p41932 <;> assumption
theorem hasDerivAt_logSeries_comp [Fintype (PositiveEdge L m k i)]
    {𝒰 : Set (Edge L m k i → ComplexMatrix2)}
    (hopen : IsOpenFieldSet PeriodicLattice.compactGaugeGroup 𝒰)
    {F : (Edge L m k i → ComplexMatrix2) → ComplexMatrix2}
    {Φ : (PositiveEdge L m k i → ComplexMatrix2) → Fin 1 → ComplexMatrix2}
    {V : Edge L m k i → ComplexMatrix2} (hV : V ∈ 𝒰)
    (hfΦ : ∀ᶠ y in 𝓝[restrictToPositiveEdges '' 𝒰] restrictToPositiveEdges V,
      (fun _ : Fin 1 => F (fieldOfPositiveValues y)) = Φ y)
    (hdg : DifferentiableAt ℝ (fun y => ComplexMatrix2.logSeries (Φ y 0))
      (restrictToPositiveEdges V))
    {η : ℝ → Edge L m k i → ComplexMatrix2} {D : PositiveEdge L m k i → ComplexMatrix2}
    (hconf : ∀ᶠ t in 𝓝 (0 : ℝ), η t ∈ fieldSpace L m k i)
    (hd : HasDerivAt (fun t => restrictToPositiveEdges (η t)) D 0) (h0 : η 0 = V) :
    HasDerivAt (fun t => ComplexMatrix2.logSeries (F (η t)))
      (fderiv ℝ (fun y => ComplexMatrix2.logSeries (Φ y 0)) (restrictToPositiveEdges V) D) 0 := by apply _root_.YangMills.SharedProofs.p678 <;> assumption
theorem contourLogDeriv_linear_of_differentiable
    (hG : ContourLogarithms.ContourLogDifferentiable)
    (hAvg : SmoothingNearIdentity)
    (hVal : SmoothingNearTrivialField)
    (hChart : LeftChartFields.Claim)
    (hBlocks : BlockStructure)
    (hH : Coordinates.ComplexCoordinates.PowerSeriesHolomorphy.Properties)
    (hExp : ComplexMatrix2.ExpLogEstimates) (hL : Conventions.IsAdmissibleBlockingFactor L)
    (hm : 0 < m) (hi : i < k) :
    EventuallyNearIdentity (fieldSpace L m k i) fun V =>
      ∃ T : edgeFormSpace L m k i →ₗ[ℝ] fineOnlyFunctions L m k i, ∀ B : edgeFormSpace L m k i,
        (T B : FineOnlyVertex L m k i → ComplexMatrix2) =
          contourLogDeriv L m k i V (B : Edge L m k i → ComplexMatrix2) := by
  obtain ⟨-, hnear⟩ := hG L m k hL hm i hi
  obtain ⟨𝒰, hU, -, hcontour⟩ := ((hAvg.1 L hL).1 m k i hm hi).1.analytic
  have hclauses := ((hChart.2.2 L k i hL hi.le).1 m hm).1
  have hfinite : Finite (PositiveEdge L m k i) := ((hChart.2.2 L k i hL hi.le).1 m hm).2.1.1
  have hfin : Fintype (PositiveEdge L m k i) := Fintype.ofFinite _
  have hcurve : ∀ V ∈ fieldSpace L m k i, ∀ B ∈ edgeFormSpace L m k i, ∀ t : ℝ,
      expCurve V B t ∈ fieldSpace L m k i := by
    intro V hV B hB t
    rw [expCurve_eq_expTwist]
    exact (hVal L m k hL hm (by omega)).2 i hi.le (t • B) ((edgeFormSpace L m k i).smul_mem t hB)
      V hV
  have hderiv : ∀ V ∈ fieldSpace L m k i, ∀ B ∈ edgeFormSpace L m k i,
      ∀ b : PositiveEdge L m k i,
      HasDerivAt (fun t : ℝ => expCurve V B t b) (Complex.I • B b * V b) 0 := by
    intro V hV B hB b
    have hd := (hclauses.1.1 V hV B hB b).2
    refine hd.congr_of_eventuallyEq (Eventually.of_forall fun t => ?_)
    have hb : (b : Edge L m k i).IsPositivelyOriented := b.2
    simp [expCurve, PeriodicLattice.expTwist, hb, LeftChartFields.leftExpMul,
      LeftChartFields.LatticeData.onPositive, LeftChartFields.finiteData]
  have hcentre : ∀ x : FineOnlyVertex L m k i, (cubeCentre x, x.1) ∈ vertexCubePairs L m k i := by
    intro x
    obtain ⟨-, hsort, -⟩ := (hBlocks L k (i + 1) hL (by omega) (by omega) hi).1 m hm
    obtain ⟨y, hy, -⟩ := hsort.2.2 x.1 x.2
    have hex : ∃ y : Vertex L m k (i + 1),
        x.1 ∈ PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k i) y ∧
        (x.1 : PeriodicLattice.FourTorus L m) ≠ y := ⟨y, hy.1, hy.2⟩
    exact (Classical.epsilon_spec hex).1
  refine (hnear.and ((eventually_mem_of_isOpenNhdOfOne hU).and self_mem_nhdsWithin)).mono ?_
  rintro V ⟨hVnear, hVU, hVconf⟩
  have key : ∀ x : FineOnlyVertex L m k i,
      ∃ A : (PositiveEdge L m k i → ComplexMatrix2) →L[ℝ] ComplexMatrix2,
      ∀ B ∈ edgeFormSpace L m k i, contourLogDeriv L m k i V B x =
          Complex.I⁻¹ • A (fun b : PositiveEdge L m k i => Complex.I • B b * V b) ∧
        contourLogDeriv L m k i V B x ∈ ComplexMatrix2.hermitianTraceless := by
    intro x
    have hp := hcentre x
    obtain ⟨hdef, hopen, inst, hra⟩ := hcontour (cubeCentre x) x.1 hp
    have e : hfin = inst := Subsingleton.elim _ _
    subst e
    obtain ⟨Φ, hΦ, hfΦ⟩ :=
      exists_analyticAt_eventuallyEq hra (mem_image_of_mem restrictToPositiveEdges hVU)
    have hval : Φ (restrictToPositiveEdges V) 0 =
        PeriodicLattice.meanContourHolonomy V (cubeCentre x) x.1 := by
      have h₁ := hfΦ.self_of_nhdsWithin (mem_image_of_mem restrictToPositiveEdges hVU)
      have h₂ := congrFun h₁ 0
      rw [← h₂]
      simp only [fieldOfPositiveValues_restrict hVconf]
    have hsmall : ComplexMatrix2.operatorNorm
        (PeriodicLattice.meanContourHolonomy V (cubeCentre x) x.1 - 1) < 1 := by
      have hz := expCurve_zero (0 : Edge L m k i → ComplexMatrix2) hVconf
      have := ((hVnear _ hp 0 (edgeFormSpace L m k i).zero_mem).1).self_of_nhds.2
      rwa [hz] at this
    have hdg : DifferentiableAt ℝ (fun y => ComplexMatrix2.logSeries (Φ y 0))
        (restrictToPositiveEdges V) := by
      have hlog : DifferentiableAt ℝ ComplexMatrix2.logSeries (Φ (restrictToPositiveEdges V) 0) := by
        rw [hval]
        exact differentiableAt_logSeries hH hsmall
      have hΦr : DifferentiableAt ℝ (fun y => Φ y 0) (restrictToPositiveEdges V) :=
        differentiableAt_pi.mp (hΦ.differentiableAt.restrictScalars ℝ) 0
      exact DifferentiableAt.comp (g := ComplexMatrix2.logSeries) (f := fun y => Φ y 0) _ hlog hΦr
    refine ⟨fderiv ℝ (fun y => ComplexMatrix2.logSeries (Φ y 0)) (restrictToPositiveEdges V),
      fun B hB => ?_⟩
    obtain ⟨hev, -⟩ := hVnear _ hp B hB
    have hz := expCurve_zero B hVconf
    have hdc : HasDerivAt (fun t => restrictToPositiveEdges (expCurve V B t))
        (fun b : PositiveEdge L m k i => Complex.I • B b * V b) 0 :=
      hasDerivAt_pi.mpr (hderiv V hVconf B hB)
    have hAc := hasDerivAt_logSeries_comp
      (F := fun W => PeriodicLattice.meanContourHolonomy W (cubeCentre x) x.1) hopen
      hVU hfΦ hdg (Eventually.of_forall (hcurve V hVconf B hB)) hdc hz
    have hvalue : contourLogDeriv L m k i V B x =
        Complex.I⁻¹ • fderiv ℝ (fun y => ComplexMatrix2.logSeries (Φ y 0))
          (restrictToPositiveEdges V)
          (fun b : PositiveEdge L m k i => Complex.I • B b * V b) := by
      have := hAc.deriv
      simp only [contourLogDeriv]
      rw [← this]
      rfl
    refine ⟨hvalue, ?_⟩
    rw [hvalue]
    refine hasDerivAt_mem_hermitianTraceless (hAc.const_smul Complex.I⁻¹) ?_
    filter_upwards [hev] with t ht
    exact logSeries_mem hExp (meanContourHolonomy_mem ht.1) ht.2
  choose A hA using key
  refine ⟨{ toFun := fun B => ⟨contourLogDeriv L m k i V (B : Edge L m k i → ComplexMatrix2),
              fun x _ => (hA x B B.2).2⟩
            map_add' := ?_
            map_smul' := ?_ }, fun _ => rfl⟩
  · intro B B'
    refine Subtype.ext (funext fun x => ?_)
    change contourLogDeriv L m k i V
        ((B + B' : edgeFormSpace L m k i) : Edge L m k i → ComplexMatrix2) x =
      contourLogDeriv L m k i V B x + contourLogDeriv L m k i V B' x
    have hadd : (fun b : PositiveEdge L m k i => Complex.I •
          ((B + B' : edgeFormSpace L m k i) : Edge L m k i → ComplexMatrix2) b * V b) =
        (fun b : PositiveEdge L m k i =>
            Complex.I • (B : Edge L m k i → ComplexMatrix2) b * V b) +
          fun b : PositiveEdge L m k i =>
            Complex.I • (B' : Edge L m k i → ComplexMatrix2) b * V b := by
      funext b
      change Complex.I • ((B : Edge L m k i → ComplexMatrix2) b +
        (B' : Edge L m k i → ComplexMatrix2) b) * V b = _
      rw [smul_add, add_mul]
      rfl
    rw [(hA x _ (B + B').2).1, (hA x B B.2).1, (hA x B' B'.2).1, hadd, map_add, smul_add]
  · intro r B
    refine Subtype.ext (funext fun x => ?_)
    change contourLogDeriv L m k i V
        ((r • B : edgeFormSpace L m k i) : Edge L m k i → ComplexMatrix2) x =
      r • contourLogDeriv L m k i V B x
    have hsm : (fun b : PositiveEdge L m k i => Complex.I •
          ((r • B : edgeFormSpace L m k i) : Edge L m k i → ComplexMatrix2) b * V b) =
        r • fun b : PositiveEdge L m k i =>
          Complex.I • (B : Edge L m k i → ComplexMatrix2) b * V b := by
      funext b
      change Complex.I • (r • (B : Edge L m k i → ComplexMatrix2) b) * V b = r • _
      rw [smul_comm, smul_mul_assoc]
    rw [(hA x _ (r • B).2).1, (hA x B B.2).1, hsm, ContinuousLinearMap.map_smul, smul_comm]
end Derivatives
section Differentials
open YangMills.Construction.Tower.ContourLogarithms (expCurve)
variable {L m k i j : ℕ}
instance instNonemptyPositiveEdge : Nonempty (PositiveEdge L m k i) :=
  ⟨⟨PeriodicLattice.Bond.forwardFrom 0 0, 0, by
    change (0 + _) - 0 = _
    simp⟩⟩
theorem exists_linear_hasDerivAt [Fintype (PositiveEdge L m k i)]
    (hC : Matrices.PowerExpCharts.ExpChartsStatement)
    (hform : ∀ B ∈ edgeFormSpace L m k i, ∀ V ∈ fieldSpace L m k i,
      PeriodicLattice.expTwist B V ∈ fieldSpace L m k i)
    {𝔇 : Set (Edge L m k i → ComplexMatrix2)}
    (hopen : IsOpenFieldSet PeriodicLattice.compactGaugeGroup 𝔇)
    {F : (Edge L m k i → ComplexMatrix2) → ComplexMatrix2}
    (hF : Matrices.EmbeddedSubmanifold.DifferentiableOnOpen
      (Matrices.specialUnitaryPower (PositiveEdge L m k i))
      (restrictToPositiveEdges '' 𝔇) fun w => F (fieldOfPositiveValues w))
    {U : Edge L m k i → ComplexMatrix2} (hU : U ∈ 𝔇) :
    ∃ T : edgeFormSpace L m k i →ₗ[ℝ] ComplexMatrix2, ∀ B : edgeFormSpace L m k i,
      HasDerivAt (fun t : ℝ => F (expCurve U B t)) (T B) 0 := by
  obtain ⟨hcharts, -, -, hread, -⟩ := hC (PositiveEdge L m k i) (PositiveEdge L m k i)
  have hUc : U ∈ fieldSpace L m k i := hopen.1 hU
  have hp₀ : restrictToPositiveEdges U ∈ restrictToPositiveEdges '' 𝔇 := mem_image_of_mem _ hU
  have hp₀G : restrictToPositiveEdges U ∈ Matrices.specialUnitaryPower (PositiveEdge L m k i) :=
    fun s => hUc.1 s.1 (mem_univ _)
  have hY := (hread (restrictToPositiveEdges '' 𝔇) _ hopen.2).2.2.1 hF
    (restrictToPositiveEdges U) hp₀
  let Yof : edgeFormSpace L m k i → PositiveEdge L m k i → ComplexMatrix2.LieElement := fun B s =>
    (⟨(B : Edge L m k i → ComplexMatrix2) s.1, B.2.1 s.1 s.2⟩ : ComplexMatrix2.hermitianTraceless)
  let τ : edgeFormSpace L m k i →ₗ[ℝ] (PositiveEdge L m k i → ComplexMatrix2) :=
    { toFun := fun B =>
        Matrices.PowerExpCharts.tangentVectorAt (restrictToPositiveEdges U) (Yof B)
      map_add' := fun B B' => by
        funext s
        change Complex.I • ((B : Edge L m k i → ComplexMatrix2) s.1 +
          (B' : Edge L m k i → ComplexMatrix2) s.1) * restrictToPositiveEdges U s = _
        rw [smul_add, add_mul]
        rfl
      map_smul' := fun r B => by
        funext s
        change Complex.I • (r • (B : Edge L m k i → ComplexMatrix2) s.1) *
          restrictToPositiveEdges U s = r • _
        rw [smul_comm, smul_mul_assoc]
        rfl }
  have hτ : ∀ B, τ B ∈ Matrices.EmbeddedSubmanifold.tangentSpace
      (Matrices.specialUnitaryPower (PositiveEdge L m k i)) (restrictToPositiveEdges U) :=
    fun B => by
      obtain ⟨h, -⟩ := (hY (Yof B)).2
      exact h
  refine ⟨(Matrices.EmbeddedSubmanifold.tangentDifferential
    (Matrices.specialUnitaryPower (PositiveEdge L m k i))
    (fun w => F (fieldOfPositiveValues w)) (restrictToPositiveEdges U)) ∘ₗ τ.codRestrict _ hτ,
    fun B => ?_⟩
  obtain ⟨h, hd⟩ := (hY (Yof B)).2
  refine hd.congr_of_eventuallyEq (Eventually.of_forall fun t => ?_)
  have hc : expCurve U (B : Edge L m k i → ComplexMatrix2) t ∈ fieldSpace L m k i := by
    rw [expCurve_eq_expTwist]
    exact hform _ ((edgeFormSpace L m k i).smul_mem t B.2) U hUc
  have hval : restrictToPositiveEdges (expCurve U (B : Edge L m k i → ComplexMatrix2) t) =
      Matrices.PowerExpCharts.expChartI (restrictToPositiveEdges U) (t • Yof B) := by
    rw [((hcharts _ hp₀G).2.1 (t • Yof B)).2.1]
    funext s
    have hs : (s.1 : Edge L m k i).IsPositivelyOriented := s.2
    have hsm : ((t : ℂ) • (B : Edge L m k i → ComplexMatrix2) s.1) =
        t • (B : Edge L m k i → ComplexMatrix2) s.1 := by
      ext r q
      simp
    simp only [restrictToPositiveEdges, expCurve, PeriodicLattice.expTwist, if_pos hs,
      Pi.smul_apply, hsm]
    rfl
  change F _ = F (fieldOfPositiveValues _)
  rw [← hval, fieldOfPositiveValues_restrict hc]
theorem leftDifferential_apply
    (hLog : ∀ I : Set ℝ, IsOpenIntervalAroundZero I →
      LeftChartFields.CurveLogDerivative ℝ I PeriodicLattice.compactGaugeGroup
        PeriodicLattice.compactLieAlgebra)
    {φ : (Edge L m k i → ComplexMatrix2) → Edge L m k j → ComplexMatrix2}
    {U B : Edge L m k i → ComplexMatrix2}
    (hU : U ∈ fieldSpace L m k i) {c : Edge L m k j} (hc : c.IsPositivelyOriented)
    {d : ComplexMatrix2}
    (hmem : ∀ᶠ t in 𝓝 (0 : ℝ), φ (expCurve U B t) c ∈ PeriodicLattice.compactGaugeGroup)
    (hd : HasDerivAt (fun t : ℝ => φ (expCurve U B t) c) d 0) :
    leftDifferential φ U B c = Complex.I⁻¹ • (d * (φ U c)⁻¹) ∧
      Complex.I⁻¹ • (d * (φ U c)⁻¹) ∈ ComplexMatrix2.hermitianTraceless := by
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff_ball.mp hmem
  have hI : IsOpenIntervalAroundZero (Metric.ball (0 : ℝ) ε) :=
    ⟨Metric.isOpen_ball, (convex_ball _ _).ordConnected, Metric.mem_ball_self hε⟩
  obtain ⟨-, -, h₁, h₂⟩ := hLog _ hI (fun t : ℝ => φ (expCurve U B t) c)
    (fun t ht => hball t ht) hd.differentiableAt
  have hz : φ (expCurve U B 0) c = φ U c := by rw [expCurve_zero B hU]
  simp only [hz, hd.deriv] at h₁ h₂
  refine ⟨?_, h₂⟩
  rw [← h₁]
  simp only [leftDifferential, extendOddly, if_pos hc, logDirectionalDeriv, expCurve]
  rfl
theorem extendOddly_opposite
    (hX : ∀ b : Edge L m k j, Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented)
    (f : Edge L m k j → ComplexMatrix2) (c : Edge L m k j) :
    extendOddly f c.opposite = -extendOddly f c := by
  have hrr : c.opposite.opposite = c := PeriodicLattice.Bond.ext rfl rfl
  rcases hX c with ⟨h, h'⟩ | ⟨h, h'⟩
  · simp only [extendOddly, if_pos h, if_neg h', hrr]
  · simp only [extendOddly, if_pos h, if_neg h', neg_neg]
theorem exists_linear_leftDifferential (hC : Matrices.PowerExpCharts.ExpChartsStatement)
    (hLog : ∀ I : Set ℝ, IsOpenIntervalAroundZero I →
      LeftChartFields.CurveLogDerivative ℝ I PeriodicLattice.compactGaugeGroup
        PeriodicLattice.compactLieAlgebra)
    (hform : ∀ B ∈ edgeFormSpace L m k i, ∀ V ∈ fieldSpace L m k i,
      PeriodicLattice.expTwist B V ∈ fieldSpace L m k i)
    (hderiv : ∀ V ∈ fieldSpace L m k i, ∀ B ∈ edgeFormSpace L m k i,
      ∀ b : PositiveEdge L m k i,
      HasDerivAt (fun t : ℝ => expCurve V B t b) (Complex.I • B b * V b) 0)
    (hX : ∀ b : Edge L m k j, Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented)
    {𝒰 : Set (Edge L m k i → ComplexMatrix2)}
    {φ : (Edge L m k i → ComplexMatrix2) → Edge L m k j → ComplexMatrix2}
    (hdiff : IsDifferentiableFieldMap 𝒰 φ) {U : Edge L m k i → ComplexMatrix2} (hU : U ∈ 𝒰) :
    ∃ T : edgeFormSpace L m k i →ₗ[ℝ] edgeFormSpace L m k j, ∀ B : edgeFormSpace L m k i,
      (T B : Edge L m k j → ComplexMatrix2) =
        leftDifferential φ U (B : Edge L m k i → ComplexMatrix2) := by
  obtain ⟨hop, hmaps, i₁, i₂, hd⟩ := hdiff
  have hUc : U ∈ fieldSpace L m k i := hop.1 hU
  obtain ⟨-, -, -, -, -, -, hinto, -⟩ := hC (PositiveEdge L m k i) (PositiveEdge L m k j)
  have hmem := (hinto _ (fun w => restrictToPositiveEdges (φ (fieldOfPositiveValues w)))
    hop.2 hd.2).mp hd
  have hT : ∀ c : PositiveEdge L m k j, ∃ T : edgeFormSpace L m k i →ₗ[ℝ] ComplexMatrix2,
      ∀ B : edgeFormSpace L m k i,
      HasDerivAt (fun t : ℝ => φ (expCurve U B t) c.1) (T B) 0 := fun c =>
    exists_linear_hasDerivAt (F := fun V => φ V c.1) hC hform hop (hmem c) hU
  choose T hT using hT
  obtain ⟨O, hO, hOU⟩ := exists_isOpen_restrict hop
  have hin : ∀ B : edgeFormSpace L m k i, ∀ᶠ t in 𝓝 (0 : ℝ),
      expCurve U (B : Edge L m k i → ComplexMatrix2) t ∈ 𝒰 := by
    intro B
    have hcont : ContinuousAt (fun t : ℝ => restrictToPositiveEdges
        (expCurve U (B : Edge L m k i → ComplexMatrix2) t)) 0 :=
      continuousAt_pi.2 fun b => (hderiv U hUc B B.2 b).continuousAt
    have h0 : restrictToPositiveEdges (expCurve U (B : Edge L m k i → ComplexMatrix2) 0) ∈ O := by
      rw [expCurve_zero _ hUc]
      exact (hOU U hUc).mp hU
    filter_upwards [hcont.eventually_mem (hO.mem_nhds h0)] with t ht
    refine (hOU _ ?_).mpr ht
    rw [expCurve_eq_expTwist]
    exact hform _ ((edgeFormSpace L m k i).smul_mem t B.2) U hUc
  have hval : ∀ (B : edgeFormSpace L m k i) (c : PositiveEdge L m k j),
      leftDifferential φ U (B : Edge L m k i → ComplexMatrix2) c.1 =
          Complex.I⁻¹ • (T c B * (φ U c.1)⁻¹) ∧
        Complex.I⁻¹ • (T c B * (φ U c.1)⁻¹) ∈ ComplexMatrix2.hermitianTraceless := fun B c =>
    leftDifferential_apply hLog hUc c.2
      ((hin B).mono fun t ht => (hmaps ht).1 c.1 (mem_univ _)) (hT c B)
  have hmemf : ∀ B : edgeFormSpace L m k i,
      leftDifferential φ U (B : Edge L m k i → ComplexMatrix2) ∈ edgeFormSpace L m k j :=
    fun B =>
    ⟨fun c hc => by
      rw [(hval B ⟨c, hc⟩).1]
      exact (hval B ⟨c, hc⟩).2, fun c => extendOddly_opposite hX _ c⟩
  have hneg : ∀ (B : edgeFormSpace L m k i) (c : Edge L m k j),
      leftDifferential φ U (B : Edge L m k i → ComplexMatrix2) c =
        -leftDifferential φ U (B : Edge L m k i → ComplexMatrix2) c.opposite := fun B c => by
    rw [(hmemf B).2 c, neg_neg]
  refine ⟨{ toFun := fun B => ⟨leftDifferential φ U (B : Edge L m k i → ComplexMatrix2), hmemf B⟩
            map_add' := ?_
            map_smul' := ?_ }, fun _ => rfl⟩
  · intro B B'
    have hp : ∀ c : PositiveEdge L m k j,
        leftDifferential φ U ((B + B' : edgeFormSpace L m k i) : Edge L m k i → ComplexMatrix2)
            c.1 =
          leftDifferential φ U (B : Edge L m k i → ComplexMatrix2) c.1 +
            leftDifferential φ U (B' : Edge L m k i → ComplexMatrix2) c.1 := fun c => by
      rw [(hval _ c).1, (hval B c).1, (hval B' c).1, map_add, add_mul, smul_add]
    refine Subtype.ext (funext fun c => ?_)
    change leftDifferential φ U ((B + B' : edgeFormSpace L m k i) : Edge L m k i → ComplexMatrix2)
        c =
      leftDifferential φ U (B : Edge L m k i → ComplexMatrix2) c +
        leftDifferential φ U (B' : Edge L m k i → ComplexMatrix2) c
    rcases isPositive_or_opposite c with hc | hc
    · exact hp ⟨c, hc⟩
    · rw [hneg _ c, hneg B c, hneg B' c, hp ⟨c.opposite, hc⟩, neg_add]
  · intro r B
    have hp : ∀ c : PositiveEdge L m k j,
        leftDifferential φ U ((r • B : edgeFormSpace L m k i) : Edge L m k i → ComplexMatrix2)
            c.1 =
          r • leftDifferential φ U (B : Edge L m k i → ComplexMatrix2) c.1 := fun c => by
      rw [(hval _ c).1, (hval B c).1, map_smul, smul_mul_assoc, smul_comm]
    refine Subtype.ext (funext fun c => ?_)
    change leftDifferential φ U ((r • B : edgeFormSpace L m k i) : Edge L m k i → ComplexMatrix2)
        c =
      r • leftDifferential φ U (B : Edge L m k i → ComplexMatrix2) c
    rcases isPositive_or_opposite c with hc | hc
    · exact hp ⟨c, hc⟩
    · rw [hneg _ c, hneg B c, hp ⟨c.opposite, hc⟩, smul_neg]
theorem leftDifferential_smoothingIter_zero
    (hLog : ∀ I : Set ℝ, IsOpenIntervalAroundZero I →
      LeftChartFields.CurveLogDerivative ℝ I PeriodicLattice.compactGaugeGroup
        PeriodicLattice.compactLieAlgebra)
    (hform : ∀ B ∈ edgeFormSpace L m k 0, ∀ V ∈ fieldSpace L m k 0,
      PeriodicLattice.expTwist B V ∈ fieldSpace L m k 0)
    (hderiv : ∀ V ∈ fieldSpace L m k 0, ∀ B ∈ edgeFormSpace L m k 0,
      ∀ b : PositiveEdge L m k 0,
      HasDerivAt (fun t : ℝ => expCurve V B t b) (Complex.I • B b * V b) 0)
    {U : Edge L m k 0 → ComplexMatrix2} (hU : U ∈ fieldSpace L m k 0)
    {B : Edge L m k 0 → ComplexMatrix2}
    (hB : B ∈ edgeFormSpace L m k 0) : leftDifferential (smoothingIter L m k 0) U B = B := by
  have hpos : ∀ c : Edge L m k 0, c.IsPositivelyOriented →
      leftDifferential (smoothingIter L m k 0) U B c = B c := by
    intro c hc
    have hu : IsUnit (U c).det := by
      have := (Matrix.mem_specialUnitaryGroup_iff.mp (hU.1 c (mem_univ _))).2
      rw [this]
      exact isUnit_one
    have h := (leftDifferential_apply (φ := smoothingIter L m k 0) hLog hU hc
      (Eventually.of_forall fun t => ?_) (hderiv U hU B hB ⟨c, hc⟩)).1
    · rw [h]
      change Complex.I⁻¹ • (Complex.I • B c * U c * (U c)⁻¹) = B c
      rw [mul_assoc, Matrix.mul_nonsing_inv _ hu, mul_one, smul_smul,
        inv_mul_cancel₀ Complex.I_ne_zero, one_smul]
    · have : expCurve U B t ∈ fieldSpace L m k 0 := by
        rw [expCurve_eq_expTwist]
        exact hform _ ((edgeFormSpace L m k 0).smul_mem t hB) U hU
      exact this.1 c (mem_univ _)
  funext b
  rcases isPositive_or_opposite b with h | h
  · exact hpos b h
  · by_cases h' : b.IsPositivelyOriented
    · exact hpos b h'
    · have hrr : b.opposite.opposite = b := PeriodicLattice.Bond.ext rfl rfl
      simp only [leftDifferential, extendOddly, if_neg h']
      have := hpos b.opposite h
      simp only [leftDifferential, extendOddly, if_pos h] at this
      rw [this, hB.2 b, neg_neg]
end Differentials
section Objects
open YangMills.Construction.Tower.ContourLogarithms (expCurve)
variable {L m k : ℕ}
theorem smoothingStep_bound (hG : ContourLogarithms.ContourLogDifferentiable)
    (hAvg : SmoothingNearIdentity)
    (hVal : SmoothingNearTrivialField)
    (hChart : LeftChartFields.Claim)
    (hBlocks : BlockStructure)
    (hH : Coordinates.ComplexCoordinates.PowerSeriesHolomorphy.Properties)
    (hExp : ComplexMatrix2.ExpLogEstimates)
    (hFib : SmoothingFibres)
    (hCh : Matrices.PowerExpCharts.ExpChartsStatement)
    (hOr : PeriodicLattice.LevelBondOrientationDichotomy)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hm : 0 < m) (hk : 1 ≤ k) :
    SmoothingStepWellDefined L m k := by
  have hV := hVal L m k hL hm hk
  have hdom : ∀ i < k, ∀ᶠ V in 𝓝[fieldSpace L m k i] trivialField L m k i,
      V ∈ commonSmoothingDomain L m k i := fun i hi => eventually_mem_of_isOpenNhdOfOne (hV.1 i hi).1
  have hvalues : ∀ i < k, ∀ V ∈ commonSmoothingDomain L m k i,
      ∀ c : Edge L m k (i + 1), c.IsPositivelyOriented → SmoothingValuesAt i V c :=
    fun i hi => (hV.1 i hi).2
  refine ⟨fun i hi => (hdom i hi).mono fun V hV c => mem_iInter.mp hV c, ?_, ?_,
    fun i hi => contourLogDeriv_linear_of_differentiable hG hAvg hVal hChart hBlocks hH hExp hL hm hi,
    ?_⟩
  · refine fun i hi => (hdom i hi).mono fun V hV y x hx => ?_
    have hc : (PeriodicLattice.Bond.forwardFrom y 0).IsPositivelyOriented := ⟨0, by
      change (y + _) - y = _
      simp⟩
    have hw := hvalues i hi V hV _ hc
    have hy : y ∈ ({(PeriodicLattice.Bond.forwardFrom y 0).source,
        (PeriodicLattice.Bond.forwardFrom y 0).target} : Set (Vertex L m k (i + 1))) := Or.inl rfl
    exact ⟨hw.hasContourMean y hy x hx, hw.contourMean_mem y hy x hx⟩
  · refine fun i hi => (hdom i hi).mono fun V hV c => ?_
    by_cases hc : c.IsPositivelyOriented
    · exact (hvalues i hi V hV c hc).smoothing_mem
    · have hr := (isPositive_or_opposite c).resolve_left hc
      have hmm := (hvalues i hi V hV _ hr).smoothing_mem
      have he : smoothingStep L m k i V c = (smoothingStep L m k i V c.opposite)⁻¹ := by
        simp only [smoothingStep, PeriodicLattice.blockAverageStep, PeriodicLattice.blockAverage,
          if_neg hc, if_pos hr]
      rw [he]
      exact inv_mem_compactGaugeGroup hmm
  · intro j hj
    have hlogs : ∀ I : Set ℝ, IsOpenIntervalAroundZero I →
        LeftChartFields.CurveLogDerivative ℝ I PeriodicLattice.compactGaugeGroup
          PeriodicLattice.compactLieAlgebra := fun I hI => (hChart.1 I hI).1
    have hform : ∀ B ∈ edgeFormSpace L m k 0, ∀ V ∈ fieldSpace L m k 0,
        PeriodicLattice.expTwist B V ∈ fieldSpace L m k 0 := hV.2 0 (Nat.zero_le k)
    have hclauses := ((hChart.2.2 L k 0 hL (Nat.zero_le k)).1 m hm).1
    have hderiv : ∀ V ∈ fieldSpace L m k 0, ∀ B ∈ edgeFormSpace L m k 0,
        ∀ b : PositiveEdge L m k 0,
        HasDerivAt (fun t : ℝ => expCurve V B t b) (Complex.I • B b * V b) 0 := by
      intro V hV B hB b
      have hd := (hclauses.1.1 V hV B hB b).2
      refine hd.congr_of_eventuallyEq (Eventually.of_forall fun t => ?_)
      have hb : (b : Edge L m k 0).IsPositivelyOriented := b.2
      simp [expCurve, PeriodicLattice.expTwist, hb, LeftChartFields.leftExpMul,
        LeftChartFields.LatticeData.onPositive, LeftChartFields.finiteData]
    rcases j with _ | i
    · refine Eventually.mono self_mem_nhdsWithin fun U hU => ?_
      exact ⟨LinearMap.id, fun B =>
        (leftDifferential_smoothingIter_zero hlogs hform hderiv hU B.2).symm⟩
    · have hi : i < k := by omega
      obtain ⟨𝒰, hU, hdiff, -, -⟩ := (hFib L m k i hL hm hi).2.2.2.2.1
      refine (eventually_mem_of_isOpenNhdOfOne hU).mono fun U hU' => ?_
      exact exists_linear_leftDifferential hCh hlogs hform hderiv
        (fun b => hOr L m k hL hm (by omega) (i + 1) hj b) hdiff hU'
end Objects
end Tower.ProlongCompositesProof
open Tower Tower.ProlongCompositesProof in
theorem ProlongCompositesAndVertexLayers.proof
    (hB : CriticalBranchExists)
    (hG : ContourLogarithms.ContourLogDifferentiable)
    (hAvg : SmoothingNearIdentity)
    (hVal : SmoothingNearTrivialField)
    (hChart : LeftChartFields.Claim)
    (hBlocks : BlockStructure)
    (hH : Coordinates.ComplexCoordinates.PowerSeriesHolomorphy.Properties)
    (hExp : ComplexMatrix2.ExpLogEstimates)
    (hFib : SmoothingFibres)
    (hCh : Matrices.PowerExpCharts.ExpChartsStatement)
    (hOr : PeriodicLattice.LevelBondOrientationDichotomy)
    (hI : Gaussian.KernelIntegral.GaussianIntegralOnKernel) :
    ProlongCompositesAndVertexLayers.Statement := by
  refine ⟨fun L m k hL hm hk => ⟨prolongIter_spec hB hL hm,
    smoothingStep_bound hG hAvg hVal hChart hBlocks hH hExp hFib hCh hOr hL hm hk, ?_⟩,
    gaussian_kernel_integral hI⟩
  exact vertexLayer_decomposition (by have := hL.2; omega)
end YangMills.Construction
end
