import YangMills.Construction.Towers.DilationNearTheTrivialConfigurationProof
import YangMills.Construction.Lattice.IsometryCovarianceOfHolonomiesAndActionsProof
import YangMills.Construction.Lattice.IsometryCovarianceOfRegularSetsAndAxialRepresentatives
import YangMills.Construction.Lattice.IsometryCovarianceOfTowersAndCubesOfAStep
import YangMills.Construction.Lattice.TowerConfigurationsOfTheContinuationUnderIsometriesProof
import YangMills.Construction.Lattice.TranslationsCarryTheContinuationOfTheMinimiser
import YangMills.Construction.Matrices.RepresentationsFieldsAndSmoothFunctionsOnG
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction
open Matrices Coordinates
namespace PeriodicLattice
namespace MinimizerTranslation
variable {L m K : ℕ}
section EvaluationMaps
variable {k : ℕ} {Ω : ℕ → Set (FourTorus L m)} {V V' : ∀ j : ℕ, BondAtLevel L m K j → ComplexMatrix2}
theorem regularConstrainedCriticalSet_congr (ε : ℝ)
    (h : ∀ q ∈ activeBondSet K k Ω, V q.1 q.2 = V' q.1 q.2) :
    regularConstrainedCriticalSet (Averaging.smoothingRadius L) ε K k Ω (activeBondSet K k Ω) V =
      regularConstrainedCriticalSet (Averaging.smoothingRadius L) ε K k Ω (activeBondSet K k Ω) V' := by apply _root_.YangMills.Construction.PeriodicLattice.ContinuedTowerFieldIsometry.regularConstrainedCriticalSet_congr <;> assumption
theorem hasActiveCriticalOrbit_congr (ε : ℝ)
    (h : ∀ q ∈ activeBondSet K k Ω, V q.1 q.2 = V' q.1 q.2) :
    HasActiveCriticalOrbit ε K k Ω V = HasActiveCriticalOrbit ε K k Ω V' := by apply _root_.YangMills.Construction.PeriodicLattice.ContinuedTowerFieldIsometry.hasActiveCriticalOrbit_congr <;> assumption
theorem mem_activeRegularRealFields_of_eq {εBar : ℝ} (h : ∀ j ≤ k, V j = V' j)
    (hV : V ∈ activeRegularRealFields εBar K k Ω) :
    V' ∈ activeRegularRealFields εBar K k Ω := by apply _root_.YangMills.Construction.PeriodicLattice.ContinuedTowerFieldIsometry.mem_activeRegularRealFields_of_eqOn <;> assumption
theorem level_le_of_mem {q : Σ j : ℕ, BondAtLevel L m K j} (hq : q ∈ activeBondSet K k Ω) :
    q.1 ≤ k :=
  hq.1.1
theorem inv_inv_of_mem_compact {g : ComplexMatrix2} (hg : g ∈ compactGaugeGroup) : g⁻¹⁻¹ = g := by apply _root_.YangMills.Construction.PeriodicLattice.BlockAverageContinuity.inv_inv_of_mem_compactGaugeGroup <;> assumption
theorem inv_mem_compact {g : ComplexMatrix2} (hg : g ∈ compactGaugeGroup) :
    g⁻¹ ∈ compactGaugeGroup := by apply _root_.YangMills.Construction.PeriodicLattice.BlockAverageContinuity.inv_mem_compactGaugeGroup <;> assumption
theorem isLinkDatum_of_gaugeFields
    (hV : ∀ j ≤ k, IsGaugeField compactGaugeGroup (activeBondsAt K k Ω j) (V j)) :
    IsLinkDatum (activeBondSet K k Ω) V := by
  rintro ⟨j, b⟩ hq
  have hb : b ∈ activeBondsAt K k Ω j := ⟨hq.1.2, hq.2⟩
  exact ⟨(hV j (level_le_of_mem hq)).1 b hb, fun _ => (hV j (level_le_of_mem hq)).2 b hb⟩
theorem opposite_mem_active {j : ℕ} {b : BondAtLevel L m K j}
    (hq : (⟨j, b⟩ : Σ j : ℕ, BondAtLevel L m K j) ∈ activeBondSet K k Ω) :
    (⟨j, b.opposite⟩ : Σ j : ℕ, BondAtLevel L m K j) ∈ activeBondSet K k Ω := by apply _root_.YangMills.Construction.PeriodicLattice.ContinuedTowerFieldIsometry.opposite_mem_activeBondSet <;> assumption
theorem endpointFixingOrbit_trans {B : Set (Σ j : ℕ, BondAtLevel L m K j)}
    {U₀ U₁ W : BondAtLevel L m K 0 → ComplexMatrix2}
    (h₁ : U₁ ∈ endpointFixingOrbit Ω B U₀) (h₂ : W ∈ endpointFixingOrbit Ω B U₁) :
    W ∈ endpointFixingOrbit Ω B U₀ := by
  classical
  obtain ⟨u, hu, rfl⟩ := h₁
  obtain ⟨v, hv, rfl⟩ := h₂
  refine ⟨v * u, ⟨fun x hx => ?_, fun x hx => ?_, fun x hx => ?_⟩, ?_⟩
  · exact mul_mem (hv.1 x hx) (hu.1 x hx)
  · simp [hv.2.1 x hx, hu.2.1 x hx]
  · simp [hv.2.2 x hx, hu.2.2 x hx]
  · funext b
    simp only [extendByOne, gaugeTransform, Pi.mul_apply]
    split_ifs with hb
    · rw [Matrix.mul_inv_rev]
      simp only [mul_assoc]
    · rfl
end EvaluationMaps
structure IsometryData (σ : FourTorus L m ≃ FourTorus L m) (i : ℤ) : Prop where
  ends_image : ∀ j : ℤ, i ≤ j → ∀ b : Bond L m j,
    ((bondImage σ b).source : FourTorus L m) = σ b.source ∧
      ((bondImage σ b).target : FourTorus L m) = σ b.target
  ends_preimage : ∀ j : ℤ, i ≤ j → ∀ b : Bond L m j,
    ((bondPreimage σ b).source : FourTorus L m) = σ.symm b.source ∧
      ((bondPreimage σ b).target : FourTorus L m) = σ.symm b.target
  chains : PreservesChainObjects i σ
  blockFields : ∀ K : ℕ, BlockFieldEquivariant K i σ
  sites : ∀ j : ℤ, i ≤ j → ∀ y : Site L m j,
    ((siteImage σ y : Site L m j) : FourTorus L m) = σ y
section Bonds
variable {σ : FourTorus L m ≃ FourTorus L m} {i j : ℤ}
theorem preimage_image (h : IsometryData σ i) (hj : i ≤ j) (c : Bond L m j) :
    bondPreimage σ (bondImage σ c) = c := by
  have e := h.ends_image j hj c
  have p := h.ends_preimage j hj (bondImage σ c)
  apply Bond.ext <;> apply Subtype.ext
  · rw [p.1, e.1]; simp
  · rw [p.2, e.2]; simp
theorem image_preimage (h : IsometryData σ i) (hj : i ≤ j) (b : Bond L m j) :
    bondImage σ (bondPreimage σ b) = b := by
  have e := h.ends_image j hj (bondPreimage σ b)
  have p := h.ends_preimage j hj b
  apply Bond.ext <;> apply Subtype.ext
  · rw [e.1, p.1]; simp
  · rw [e.2, p.2]; simp
theorem transport_apply_image (h : IsometryData σ i) (hj : i ≤ j) (U : Bond L m j → ComplexMatrix2)
    (c : Bond L m j) : transportGaugeField σ U (bondImage σ c) = U c :=
  congrArg U (preimage_image h hj c)
theorem preimage_opposite (h : IsometryData σ i) (hj : i ≤ j) (b : Bond L m j) :
    bondPreimage σ b.opposite = (bondPreimage σ b).opposite := by
  have p := h.ends_preimage j hj b
  have q := h.ends_preimage j hj b.opposite
  apply Bond.ext <;> apply Subtype.ext
  · exact q.1.trans p.2.symm
  · exact q.2.trans p.1.symm
theorem mem_image_iff_symm (X : Set (FourTorus L m)) (t : FourTorus L m) :
    t ∈ σ '' X ↔ σ.symm t ∈ X := by apply _root_.YangMills.Construction.PeriodicLattice.IsometryInvariance.mem_image_equiv_iff <;> assumption
theorem mem_bondsInside_image (h : IsometryData σ i) (hj : i ≤ j) (X : Set (FourTorus L m))
    (b : Bond L m j) :
    b ∈ (bondsInside (σ '' X) : Set (Bond L m j)) ↔
      bondPreimage σ b ∈ (bondsInside X : Set (Bond L m j)) := by
  have p := h.ends_preimage j hj b
  show ((b.source : FourTorus L m) ∈ σ '' X ∧ (b.target : FourTorus L m) ∈ σ '' X) ↔
    (((bondPreimage σ b).source : FourTorus L m) ∈ X ∧
      ((bondPreimage σ b).target : FourTorus L m) ∈ X)
  rw [p.1, p.2, mem_image_iff_symm, mem_image_iff_symm]
theorem extendByOne_transport (h : IsometryData σ i) (hj : i ≤ j) (X : Set (FourTorus L m))
    (U : Bond L m j → ComplexMatrix2) :
    extendByOne (bondsInside (σ '' X)) (transportGaugeField σ U) =
      transportGaugeField σ (extendByOne (bondsInside X) U) := by
  funext b
  have hiff := mem_bondsInside_image h hj X b
  simp only [extendByOne, transportGaugeField]
  by_cases hb : b ∈ (bondsInside (σ '' X) : Set (Bond L m j))
  · rw [if_pos hb, if_pos (hiff.1 hb)]
  · rw [if_neg hb, if_neg (mt hiff.2 hb)]
theorem bondsInside_reversalClosed (X : Set (FourTorus L m)) :
    IsReversalClosed (bondsInside X : Set (Bond L m j)) :=
  fun _ hb => ⟨hb.2, hb.1⟩
theorem transport_isGaugeField (h : IsometryData σ i) (hj : i ≤ j) {𝒢 : Set ComplexMatrix2}
    {X : Set (FourTorus L m)} {U : Bond L m j → ComplexMatrix2}
    (hU : IsGaugeField 𝒢 (bondsInside X) U) :
    IsGaugeField 𝒢 (bondsInside (σ '' X)) (transportGaugeField σ U) := by
  refine ⟨fun b hb => hU.1 _ ((mem_bondsInside_image h hj X b).1 hb), fun b hb => ?_⟩
  show U (bondPreimage σ b.opposite) = (U (bondPreimage σ b))⁻¹
  rw [preimage_opposite h hj]
  exact hU.2 _ ((mem_bondsInside_image h hj X b).1 hb)
theorem transport_symm_transport (h : IsometryData σ i) (hj : i ≤ j)
    (U : Bond L m j → ComplexMatrix2) :
    transportGaugeField σ.symm (transportGaugeField σ U) = U :=
  funext fun b => congrArg U (preimage_image h hj b)
theorem levelDepth_anti {j n : ℕ} (hj : j ≤ n) : levelDepth K n ≤ levelDepth K j := by apply _root_.YangMills.Construction.PeriodicLattice.EquivarianceProof.levelDepth_anti <;> assumption
theorem averaging_transport (h : IsometryData σ i) {j : ℕ} (hjK : j ≤ K)
    (hij : i ≤ levelDepth K j) (X : Set (FourTorus L m)) {U : BondAtLevel L m K 0 → ComplexMatrix2}
    (hU : IsGaugeField compactGaugeGroup (bondsInside X) U) :
    (averagingOnDeterminingSet (Averaging.smoothingRadius L) K (σ '' X)
        (transportGaugeField σ U) j : BondAtLevel L m K j → ComplexMatrix2) =
      transportGaugeField σ (averagingOnDeterminingSet (Averaging.smoothingRadius L) K X U j) := by
  have hi0 : i ≤ levelDepth K 0 := hij.trans (levelDepth_anti (Nat.zero_le j))
  show blockFieldAtLevel _ j (extendByOne (bondsInside (σ '' X)) (transportGaugeField σ U)) = _
  rw [extendByOne_transport h hi0]
  exact h.blockFields K j hjK hij _
    (extendByOne_mem_compactGaugeFields (bondsInside_reversalClosed X) hU)
end Bonds
section Paths
variable {σ : FourTorus L m ≃ FourTorus L m} {i j : ℤ}
theorem isTorusTranslation_symm (hσ : IsTorusTranslation σ) : IsTorusTranslation σ.symm := by apply _root_.YangMills.Construction.PeriodicLattice.ContinuedTowerFieldIsometry.isTorusTranslation_symm <;> assumption
theorem toFourTorus_add (x y : Fin 4 → ℝ) :
    toFourTorus L m (x + y) = toFourTorus L m x + toFourTorus L m y := by apply _root_.YangMills.Construction.PeriodicLattice.IsometryCovariance.toFourTorus_add <;> assumption
theorem toFourTorus_surjective : Function.Surjective (toFourTorus L m) := by apply _root_.YangMills.Construction.PeriodicLattice.IsometryCovariance.toFourTorus_surjective <;> assumption
theorem exists_add_of_translation (hσ : IsTorusTranslation σ) :
    ∃ c : FourTorus L m, ∀ t, σ t = t + c := by
  obtain ⟨v, hv⟩ := hσ
  have h1 : ∀ y : Fin 4 → ℝ, (1 : SignedFrame).actOnVector y = y := by
    intro y
    funext μ
    simp [SignedFrame.actOnVector]
  refine ⟨toFourTorus L m v, fun t => ?_⟩
  obtain ⟨x, rfl⟩ := toFourTorus_surjective t
  rw [hv, h1, toFourTorus_add]
theorem image_forwardFrom (h : IsometryData σ i) (hj : i ≤ j) {c : FourTorus L m}
    (hc : ∀ t, σ t = t + c) {x y : Site L m j} (hxy : (y : FourTorus L m) = σ x) (μ : Fin 4) :
    bondImage σ (Bond.forwardFrom x μ) = Bond.forwardFrom y μ := by
  have e := h.ends_image j hj (Bond.forwardFrom x μ)
  apply Bond.ext <;> apply Subtype.ext
  · rw [e.1]; exact hxy.symm
  · rw [e.2]
    show σ ((x + unitStep L m j μ : Site L m j) : FourTorus L m) =
      ((y + unitStep L m j μ : Site L m j) : FourTorus L m)
    rw [hc]
    simp only [AddSubgroup.coe_add, hxy, hc]
    abel
theorem image_backwardFrom (h : IsometryData σ i) (hj : i ≤ j) {c : FourTorus L m}
    (hc : ∀ t, σ t = t + c) {x y : Site L m j} (hxy : (y : FourTorus L m) = σ x) (μ : Fin 4) :
    bondImage σ (Bond.backwardFrom x μ) = Bond.backwardFrom y μ := by
  have e := h.ends_image j hj (Bond.backwardFrom x μ)
  apply Bond.ext <;> apply Subtype.ext
  · rw [e.1]; exact hxy.symm
  · rw [e.2]
    show σ ((x - unitStep L m j μ : Site L m j) : FourTorus L m) =
      ((y - unitStep L m j μ : Site L m j) : FourTorus L m)
    rw [hc]
    simp only [AddSubgroup.coe_sub, hxy, hc]
    abel
theorem image_forwardFlow (h : IsometryData σ i) (hj : i ≤ j) {c : FourTorus L m}
    (hc : ∀ t, σ t = t + c) (μ : Fin 4) (n : ℕ) {x y : Site L m j}
    (hxy : (y : FourTorus L m) = σ x) :
    pathImage σ (forwardAxisPath x μ n) = forwardAxisPath y μ n := by
  induction n generalizing x y with
  | zero => rfl
  | succ n ih =>
    have hn : ((y + unitStep L m j μ : Site L m j) : FourTorus L m) =
        σ ((x + unitStep L m j μ : Site L m j) : FourTorus L m) := by
      rw [hc]
      simp only [AddSubgroup.coe_add, hxy, hc]
      abel
    have := ih hn
    simp only [pathImage, forwardAxisPath, List.map_cons] at this ⊢
    rw [image_forwardFrom h hj hc hxy, this]
theorem image_backwardFlow (h : IsometryData σ i) (hj : i ≤ j) {c : FourTorus L m}
    (hc : ∀ t, σ t = t + c) (μ : Fin 4) (n : ℕ) {x y : Site L m j}
    (hxy : (y : FourTorus L m) = σ x) :
    pathImage σ (backwardAxisPath x μ n) = backwardAxisPath y μ n := by
  induction n generalizing x y with
  | zero => rfl
  | succ n ih =>
    have hn : ((y - unitStep L m j μ : Site L m j) : FourTorus L m) =
        σ ((x - unitStep L m j μ : Site L m j) : FourTorus L m) := by
      rw [hc]
      simp only [AddSubgroup.coe_sub, hxy, hc]
      abel
    have := ih hn
    simp only [pathImage, backwardAxisPath, List.map_cons] at this ⊢
    rw [image_backwardFrom h hj hc hxy, this]
theorem image_stepsThroughAxes (h : IsometryData σ i) (hj : i ≤ j) {c : FourTorus L m}
    (hc : ∀ t, σ t = t + c) (n : Fin 4 → ℤ) (l : List (Fin 4)) {x y : Site L m j}
    (hxy : (y : FourTorus L m) = σ x) :
    pathImage σ (stepsThroughAxes n x l) = stepsThroughAxes n y l := by
  induction l generalizing x y with
  | nil => rfl
  | cons μ l ih =>
    have hn : ((y + n μ • unitStep L m j μ : Site L m j) : FourTorus L m) =
        σ ((x + n μ • unitStep L m j μ : Site L m j) : FourTorus L m) := by
      rw [hc]
      simp only [AddSubgroup.coe_add, hxy, hc]
      abel
    have h₁ : pathImage σ (flowAlong x μ (n μ)) = flowAlong y μ (n μ) := by
      simp only [flowAlong]
      split_ifs
      · exact image_forwardFlow h hj hc μ _ hxy
      · exact image_backwardFlow h hj hc μ _ hxy
    have h₂ := ih hn
    simp only [pathImage, stepsThroughAxes, List.map_append] at h₁ h₂ ⊢
    rw [h₁, h₂]
theorem coordinateComb_image (h : IsometryData σ i) (hj : i ≤ j) (ht : IsTorusTranslation σ)
    {y₀ x₀ y x : Site L m j} (hy : (y : FourTorus L m) = σ y₀)
    (hx : (x : FourTorus L m) = σ x₀) :
    coordinateComb y x = pathImage σ (coordinateComb y₀ x₀) := by
  obtain ⟨c, hc⟩ := exists_add_of_translation ht
  have hd : x - y = x₀ - y₀ := by
    apply Subtype.ext
    simp only [AddSubgroup.coe_sub, hy, hx, hc]
    abel
  have hp : IsChartOffset y x = IsChartOffset y₀ x₀ := by
    funext d
    simp only [IsChartOffset, hd]
  have hdisp : chartOffset y x = chartOffset y₀ x₀ := by
    simp only [chartOffset, hp]
  simp only [coordinateComb, hdisp]
  exact (image_stepsThroughAxes h hj hc _ _ hy).symm
theorem coe_toSublattice (hL : 0 < L) {j' : ℤ} (hjj : j ≤ j') (y : Site L m j) :
    ((y.toSublattice j' : Site L m j') : FourTorus L m) = y := by apply _root_.YangMills.Construction.PeriodicLattice.CornerBoxes.coe_toSublattice <;> assumption
theorem pathHolonomy_image (h : IsometryData σ i) (hj : i ≤ j) (U : Bond L m j → ComplexMatrix2)
    (Γ : List (Bond L m j)) :
    pathHolonomy (transportGaugeField σ U) (pathImage σ Γ) = pathHolonomy U Γ := by
  simp only [pathHolonomy, pathImage, List.map_map]
  congr 1
  exact List.map_congr_left fun b _ => transport_apply_image h hj U b
end Paths
section Holomorphy
variable {α α' τ τ' : Type}
def IsHolomorphicInNumbering (b : Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless) {n l : ℕ}
    (μ : α ≃ Fin n) (ν : τ ≃ Fin l) (O : Set (α → ComplexMatrix2))
    (f : (α → ComplexMatrix2) → τ → ComplexMatrix2) : Prop :=
  ComplexCoordinates.IsHolomorphicIn
    ((fun (w : ComplexCoordinates (n * 3)) (i : α) =>
      ComplexCoordinates.tracelessTuple b w (μ i)) ⁻¹' O)
    (GroupLieProduct.matrixPiEquiv ν ∘ f ∘
      fun (w : ComplexCoordinates (n * 3)) (i : α) => ComplexCoordinates.tracelessTuple b w (μ i))
theorem IsHolomorphicInNumbering.castCard {b : Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless}
    {n n' l l' : ℕ} (hn : n = n') (hl : l = l') {μ : α ≃ Fin n} {ν : τ ≃ Fin l}
    {O : Set (α → ComplexMatrix2)} {f : (α → ComplexMatrix2) → τ → ComplexMatrix2}
    (h : IsHolomorphicInNumbering b μ ν O f) :
    IsHolomorphicInNumbering b (μ.trans (finCongr hn)) (ν.trans (finCongr hl)) O f := by
  subst hn hl
  have e₁ : μ.trans (finCongr rfl) = μ := Equiv.ext fun i => by simp
  have e₂ : ν.trans (finCongr rfl) = ν := Equiv.ext fun i => by simp
  rw [e₁, e₂]
  exact h
theorem IsHolomorphicInNumbering.reindex {b : Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless}
    {n l : ℕ} {μ : α ≃ Fin n} {ν : τ ≃ Fin l} {O : Set (α → ComplexMatrix2)}
    {f : (α → ComplexMatrix2) → τ → ComplexMatrix2} (e : α ≃ α') (t : τ' ≃ τ)
    (h : IsHolomorphicInNumbering b μ ν O f) :
    IsHolomorphicInNumbering b (e.symm.trans μ) (t.trans ν)
      ((fun B : α' → ComplexMatrix2 => B ∘ e) ⁻¹' O) (fun B c => f (B ∘ e) (t c)) := by
  have hT : ∀ w : ComplexCoordinates (n * 3),
      (fun i' : α' => ComplexCoordinates.tracelessTuple b w ((e.symm.trans μ) i')) ∘ e =
        fun i : α => ComplexCoordinates.tracelessTuple b w (μ i) := by
    intro w
    funext i
    simp
  have hS : ((fun (w : ComplexCoordinates (n * 3)) (i : α') =>
        ComplexCoordinates.tracelessTuple b w ((e.symm.trans μ) i)) ⁻¹'
          ((fun B : α' → ComplexMatrix2 => B ∘ e) ⁻¹' O)) =
      ((fun (w : ComplexCoordinates (n * 3)) (i : α) =>
        ComplexCoordinates.tracelessTuple b w (μ i)) ⁻¹' O) := by
    ext w
    simp only [mem_preimage]
    rw [hT]
  have key : ∀ g : τ → ComplexMatrix2, GroupLieProduct.matrixPiEquiv (t.trans ν)
      (fun c => g (t c)) = GroupLieProduct.matrixPiEquiv ν g := by
    intro g
    show ComplexCoordinates.productEquiv (fun _ : Fin l => ComplexCoordinates.Component.matrix)
        (Equiv.arrowCongr (t.trans ν) (Equiv.refl ComplexMatrix2) fun c => g (t c)) =
      ComplexCoordinates.productEquiv (fun _ : Fin l => ComplexCoordinates.Component.matrix)
        (Equiv.arrowCongr ν (Equiv.refl ComplexMatrix2) g)
    congr 1
    funext i
    simp [Equiv.arrowCongr]
  have hF : (GroupLieProduct.matrixPiEquiv (t.trans ν) ∘
        (fun B c => f (B ∘ e) (t c)) ∘ fun (w : ComplexCoordinates (n * 3)) (i : α') =>
          ComplexCoordinates.tracelessTuple b w ((e.symm.trans μ) i)) =
      (GroupLieProduct.matrixPiEquiv ν ∘ f ∘
        fun (w : ComplexCoordinates (n * 3)) (i : α) =>
          ComplexCoordinates.tracelessTuple b w (μ i)) := by
    funext w
    simp only [Function.comp_apply]
    rw [hT]
    exact key _
  unfold IsHolomorphicInNumbering at h ⊢
  rw [hS, hF]
  exact h
theorem isSupOpen_comp (e : α ≃ α') {O : Set (α → ComplexMatrix2)}
    (hO : GroupLieProduct.IsSupOpen O) :
    GroupLieProduct.IsSupOpen ((fun B : α' → ComplexMatrix2 => B ∘ e) ⁻¹' O) := by apply _root_.YangMills.Construction.Tower.ScalingTransport.isSupOpen_precomp <;> assumption
theorem isHolomorphicMatrixValued_reindex [Fintype α] [Fintype α'] [Fintype τ] [Fintype τ']
    (e : α ≃ α') (t : τ' ≃ τ) {O : Set (α → ComplexMatrix2)}
    {f : (α → ComplexMatrix2) → τ → ComplexMatrix2} (hf : IsHolomorphicMatrixValued O f) :
    IsHolomorphicMatrixValued ((fun B : α' → ComplexMatrix2 => B ∘ e) ⁻¹' O)
      (fun B c => f (B ∘ e) (t c)) := by
  intro b ν'
  have hτ : Fintype.card τ' = Fintype.card τ := Fintype.card_congr t
  have hα : Fintype.card α' = Fintype.card α := (Fintype.card_congr e).symm
  have hf₀ := hf b ((t.symm.trans ν').trans (finCongr hτ))
  refine ⟨isSupOpen_comp e hf₀.1, fun μ' => ?_⟩
  have h₁ : IsHolomorphicInNumbering b ((e.trans μ').trans (finCongr hα))
      ((t.symm.trans ν').trans (finCongr hτ)) O f := hf₀.2 _
  have h₂ := (h₁.castCard hα.symm hτ.symm).reindex e t
  have e₁ : e.symm.trans (((e.trans μ').trans (finCongr hα)).trans (finCongr hα.symm)) = μ' :=
    Equiv.ext fun i => by simp
  have e₂ : t.trans (((t.symm.trans ν').trans (finCongr hτ)).trans (finCongr hτ.symm)) = ν' :=
    Equiv.ext fun i => by simp
  rw [e₁, e₂] at h₂
  exact h₂
theorem mem_supBall_comp {f : α → α'} (hf : Function.Surjective f) (A : α' → ComplexMatrix2)
    (r : ℝ) : A ∘ f ∈ GroupLieProduct.supBall α r ↔ A ∈ GroupLieProduct.supBall α' r := by apply _root_.YangMills.Construction.PeriodicLattice.ContinuedTowerFieldIsometry.supBall_comp_surjective <;> assumption
theorem mem_selfAdjoint_comp (e : α ≃ α') (A : α' → ComplexMatrix2) :
    A ∘ e ∈ selfAdjointFunctions α ↔ A ∈ selfAdjointFunctions α' := by
  constructor
  · rintro ⟨h₁, h₂⟩
    refine ⟨fun b => ?_, funext fun b => ?_⟩
    · obtain ⟨a, rfl⟩ := e.surjective b
      exact h₁ a
    · obtain ⟨a, rfl⟩ := e.surjective b
      exact congrFun h₂ a
  · rintro ⟨h₁, h₂⟩
    exact ⟨fun a => h₁ (e a), funext fun a => congrFun h₂ (e a)⟩
end Holomorphy
theorem matExp_smul_I_mem {A : ComplexMatrix2}
    (hA : A ∈ (ComplexMatrix2.traceless : Set ComplexMatrix2))
    (hs : ComplexMatrix2.algebraConjMatrix A = A) :
    ComplexMatrix2.matExp (Complex.I • A) ∈ compactGaugeGroup := by
  refine SpinHarmonics.matExp_mem_of_skewAdjoint ?_ ?_
  · have hstar : star A = A := hs
    rw [star_smul, hstar]
    simp
  · have ht : ComplexMatrix2.fullTrace A = 0 := hA
    simp only [ComplexMatrix2.fullTrace] at ht ⊢
    rw [Matrix.trace_smul, ht, smul_zero]
structure TranslationSetting (σ : FourTorus L m ≃ FourTorus L m) (i : ℤ) (K k : ℕ)
    (Ω Ω' : ℕ → Set (FourTorus L m)) : Prop where
  L_pos : 0 < L
  fwd : IsometryData σ i
  bwd : IsometryData σ.symm i
  translation : IsTorusTranslation σ
  image_eq : Ω' = imageChain σ Ω
  preimage_eq : Ω = imageChain σ.symm Ω'
  k_le : k ≤ K
  depth_ge : ∀ q ≤ k, i ≤ levelDepth K q
  pos_image : ∀ a ≤ k, ∀ b : BondAtLevel L m K a, b.IsPositivelyOriented →
    (bondImage σ b).IsPositivelyOriented
  pos_preimage : ∀ a ≤ k, ∀ b : BondAtLevel L m K a, b.IsPositivelyOriented →
    (bondImage σ.symm b).IsPositivelyOriented
  dichotomy : ∀ a ≤ k, ∀ b : BondAtLevel L m K a,
    Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented
  isDetermining : IsDeterminingChainFrom K k i Ω
  isDetermining_image : IsDeterminingChainFrom K k i Ω'
  orbitFns : PreservesOrbitFunctions K i σ
  orbitFns_symm : PreservesOrbitFunctions K i σ.symm
  mapsBlocks : ∀ j : ℤ, i ≤ j → IsometryInvariance.MapsBlocks σ j
  mapsBlocks_symm : ∀ j : ℤ, i ≤ j → IsometryInvariance.MapsBlocks σ.symm j
section Setting
variable {σ : FourTorus L m ≃ FourTorus L m} {i : ℤ} {k : ℕ} {Ω Ω' : ℕ → Set (FourTorus L m)}
  {V V' : ∀ j : ℕ, BondAtLevel L m K j → ComplexMatrix2}
theorem TranslationSetting.symm (s : TranslationSetting σ i K k Ω Ω') :
    TranslationSetting σ.symm i K k Ω' Ω where
  L_pos := s.L_pos
  fwd := s.bwd
  bwd := s.fwd
  translation := isTorusTranslation_symm s.translation
  image_eq := s.preimage_eq
  preimage_eq := s.image_eq
  k_le := s.k_le
  depth_ge := s.depth_ge
  pos_image := s.pos_preimage
  pos_preimage := s.pos_image
  dichotomy := s.dichotomy
  isDetermining := s.isDetermining_image
  isDetermining_image := s.isDetermining
  orbitFns := s.orbitFns_symm
  orbitFns_symm := s.orbitFns
  mapsBlocks := s.mapsBlocks_symm
  mapsBlocks_symm := s.mapsBlocks
theorem TranslationSetting.active_eq_image (s : TranslationSetting σ i K k Ω Ω') :
    activeBondSet K k Ω' = bondSetImage σ (activeBondSet K k Ω) :=
  (s.fwd.chains K k Ω Ω' s.depth_ge fun q _ => congrFun s.image_eq q).2.2.2.2.2.2.2.1
theorem TranslationSetting.region_zero (s : TranslationSetting σ i K k Ω Ω') : Ω' 0 = σ '' Ω 0 :=
  congrFun s.image_eq 0
theorem TranslationSetting.depth_zero (s : TranslationSetting σ i K k Ω Ω') :
    i ≤ levelDepth K 0 :=
  s.depth_ge 0 (Nat.zero_le k)
theorem TranslationSetting.mem_active_iff (s : TranslationSetting σ i K k Ω Ω') {a : ℕ}
    (ha : a ≤ k) (b : BondAtLevel L m K a) :
    (⟨a, b⟩ : Σ j : ℕ, BondAtLevel L m K j) ∈ activeBondSet K k Ω' ↔
      (⟨a, bondPreimage σ b⟩ : Σ j : ℕ, BondAtLevel L m K j) ∈ activeBondSet K k Ω := by
  rw [s.active_eq_image]
  constructor
  · rintro ⟨⟨a', b'⟩, hq, he⟩
    cases he
    rwa [preimage_image s.fwd (s.depth_ge _ ha)]
  · intro h
    exact ⟨_, h, congrArg (Sigma.mk a) (image_preimage s.fwd (s.depth_ge a ha) b)⟩
theorem TranslationSetting.positive_preimage_iff (s : TranslationSetting σ i K k Ω Ω') {a : ℕ}
    (ha : a ≤ k) (b : BondAtLevel L m K a) :
    (bondPreimage σ b).IsPositivelyOriented ↔ b.IsPositivelyOriented := by
  constructor
  · intro h
    have := s.pos_image a ha _ h
    rwa [image_preimage s.fwd (s.depth_ge a ha)] at this
  · exact s.pos_preimage a ha b
theorem TranslationSetting.transport_expTwist (s : TranslationSetting σ i K k Ω Ω') {a : ℕ}
    (ha : a ≤ k) (A U : BondAtLevel L m K a → ComplexMatrix2) :
    expTwist (transportForm σ A) (transportGaugeField σ U) =
      transportGaugeField σ (expTwist A U) := by
  classical
  funext b
  simp only [transportGaugeField, transportForm, expTwist]
  by_cases hb : b.IsPositivelyOriented
  · rw [if_pos hb, if_pos ((s.positive_preimage_iff ha b).2 hb)]
  · rw [if_neg hb, if_neg (mt (s.positive_preimage_iff ha b).1 hb),
      preimage_opposite s.fwd (s.depth_ge a ha)]
def TranslationSetting.positiveEquiv (s : TranslationSetting σ i K k Ω Ω') :
    PositiveBondIn (activeBondSet K k Ω) ≃ PositiveBondIn (activeBondSet K k Ω') where
  toFun p := ⟨⟨p.1.1, bondImage σ p.1.2⟩, by
      rw [s.active_eq_image]
      exact ⟨p.1, p.2.1, rfl⟩, s.pos_image _ (level_le_of_mem p.2.1) _ p.2.2⟩
  invFun p := ⟨⟨p.1.1, bondPreimage σ p.1.2⟩, (s.mem_active_iff (level_le_of_mem p.2.1) _).1 p.2.1,
    (s.positive_preimage_iff (level_le_of_mem p.2.1) _).2 p.2.2⟩
  left_inv := by
    rintro ⟨⟨a, b⟩, h⟩
    exact Subtype.ext (congrArg (Sigma.mk a)
      (preimage_image s.fwd (s.depth_ge a (level_le_of_mem h.1)) b))
  right_inv := by
    rintro ⟨⟨a, b⟩, h⟩
    exact Subtype.ext (congrArg (Sigma.mk a)
      (image_preimage s.fwd (s.depth_ge a (level_le_of_mem h.1)) b))
theorem TranslationSetting.mem_inside_iff (s : TranslationSetting σ i K k Ω Ω')
    (b : BondAtLevel L m K 0) :
    b ∈ (bondsInside (Ω' 0) : Set (BondAtLevel L m K 0)) ↔
      bondPreimage σ b ∈ (bondsInside (Ω 0) : Set (BondAtLevel L m K 0)) := by
  rw [s.region_zero]
  exact mem_bondsInside_image s.fwd s.depth_zero (Ω 0) b
def TranslationSetting.insideEquiv (s : TranslationSetting σ i K k Ω Ω') :
    ↥(bondsInside (Ω' 0) : Set (BondAtLevel L m K 0)) ≃
      ↥(bondsInside (Ω 0) : Set (BondAtLevel L m K 0)) where
  toFun c := ⟨bondPreimage σ c.1, (s.mem_inside_iff c.1).1 c.2⟩
  invFun c := ⟨bondImage σ c.1, (s.mem_inside_iff _).2 (by
    rw [preimage_image s.fwd s.depth_zero]
    exact c.2)⟩
  left_inv c := Subtype.ext (image_preimage s.fwd s.depth_zero c.1)
  right_inv c := Subtype.ext (preimage_image s.fwd s.depth_zero c.1)
theorem TranslationSetting.familyAtLevel_eq (s : TranslationSetting σ i K k Ω Ω')
    (B' : ActiveFamily L m K k Ω') {a : ℕ} (ha : a ≤ k) :
    familyAtLevel B' a = transportForm σ (familyAtLevel (B' ∘ s.positiveEquiv) a) := by
  classical
  funext b
  have hj := s.depth_ge a ha
  simp only [transportForm, familyAtLevel]
  by_cases h : (⟨a, b⟩ : Σ j : ℕ, BondAtLevel L m K j) ∈ activeBondSet K k Ω' ∧
      b.IsPositivelyOriented
  · have h' : (⟨a, bondPreimage σ b⟩ : Σ j : ℕ, BondAtLevel L m K j) ∈ activeBondSet K k Ω ∧
        (bondPreimage σ b).IsPositivelyOriented :=
      ⟨(s.mem_active_iff ha b).1 h.1, (s.positive_preimage_iff ha b).2 h.2⟩
    rw [dif_pos h, dif_pos h']
    exact congrArg B' (Subtype.ext (congrArg (Sigma.mk a) (image_preimage s.fwd hj b).symm))
  · have h' : ¬((⟨a, bondPreimage σ b⟩ : Σ j : ℕ, BondAtLevel L m K j) ∈ activeBondSet K k Ω ∧
        (bondPreimage σ b).IsPositivelyOriented) :=
      fun g => h ⟨(s.mem_active_iff ha b).2 g.1, (s.positive_preimage_iff ha b).1 g.2⟩
    rw [dif_neg h, dif_neg h']
theorem TranslationSetting.expTwistedDatum_eq (s : TranslationSetting σ i K k Ω Ω')
    (hV : ∀ j ≤ k, V' j = transportGaugeField σ (V j)) (B' : ActiveFamily L m K k Ω') :
    ∀ j ≤ k, expTwistedDatum B' V' j =
      transportGaugeField σ (expTwistedDatum (B' ∘ s.positiveEquiv) V j) := by
  intro j hj
  show expTwist (familyAtLevel B' j) (V' j) =
    transportGaugeField σ (expTwist (familyAtLevel (B' ∘ s.positiveEquiv) j) (V j))
  rw [s.familyAtLevel_eq B' hj, hV j hj, s.transport_expTwist hj]
theorem TranslationSetting.isLinkDatum_image (s : TranslationSetting σ i K k Ω Ω')
    (hV : ∀ j ≤ k, V' j = transportGaugeField σ (V j))
    (hD : IsLinkDatum (activeBondSet K k Ω) V) : IsLinkDatum (activeBondSet K k Ω') V' := by
  rintro ⟨a, b⟩ hq
  have ha : a ≤ k := level_le_of_mem hq
  have hj := s.depth_ge a ha
  have hp := (s.mem_active_iff ha b).1 hq
  have e : V' a b = V a (bondPreimage σ b) := by
    rw [hV a ha]
    rfl
  have e' : V' a b.opposite = V a (bondPreimage σ b).opposite := by
    rw [hV a ha]
    show V a (bondPreimage σ b.opposite) = _
    rw [preimage_opposite s.fwd hj]
  refine ⟨?_, fun hr => ?_⟩
  · show V' a b ∈ _
    rw [e]
    exact (hD _ hp).1
  · show V' a b.opposite = (V' a b)⁻¹
    rw [e, e']
    refine (hD _ hp).2 ?_
    have := (s.mem_active_iff ha b.opposite).1 hr
    rwa [preimage_opposite s.fwd hj] at this
theorem TranslationSetting.datum_eq_symm (s : TranslationSetting σ i K k Ω Ω')
    (hV : ∀ j ≤ k, V' j = transportGaugeField σ (V j)) :
    ∀ j ≤ k, V j = transportGaugeField σ.symm (V' j) := by
  intro j hj
  rw [hV j hj, transport_symm_transport s.fwd (s.depth_ge j hj)]
theorem TranslationSetting.critical_image (s : TranslationSetting σ i K k Ω Ω') {ε : ℝ}
    (hε : 0 < ε) (hV : ∀ j ≤ k, V' j = transportGaugeField σ (V j))
    (hD : IsLinkDatum (activeBondSet K k Ω) V) (hM : HasActiveCriticalOrbit ε K k Ω V)
    {U : BondAtLevel L m K 0 → ComplexMatrix2}
    (hU : U ∈ regularConstrainedCriticalSet (Averaging.smoothingRadius L) ε K k Ω
      (activeBondSet K k Ω) V) :
    HasActiveCriticalOrbit ε K k Ω' V' ∧
      transportGaugeField σ U ∈
        regularConstrainedCriticalSet (Averaging.smoothingRadius L) ε K k Ω'
          (activeBondSet K k Ω') V' := by
  have hset : ∀ q ∈ activeBondSet K k Ω', datumImage σ V q.1 q.2 = V' q.1 q.2 := fun q hq => by
    rw [hV q.1 (level_le_of_mem hq)]
    rfl
  have hf := s.orbitFns ε k Ω V hε s.isDetermining hD
  rw [← s.image_eq] at hf
  have hM' : HasActiveCriticalOrbit ε K k Ω' (datumImage σ V) := hf.1.1 hM
  obtain ⟨U₀, hU₀, hE⟩ := id hM'
  have hinv : IsResidualInvariant ε K k Ω' (datumImage σ V) (fun X => X ∈
      regularConstrainedCriticalSet (Averaging.smoothingRadius L) ε K k Ω' (activeBondSet K k Ω')
        (datumImage σ V)) := by
    intro U₁ h₁ W hW
    have h₁' := h₁
    rw [hE] at h₁'
    have hWm : W ∈ regularConstrainedCriticalSet (Averaging.smoothingRadius L) ε K k Ω'
        (activeBondSet K k Ω') (datumImage σ V) := by
      rw [hE]
      exact endpointFixingOrbit_trans h₁' hW
    exact propext ⟨fun _ => h₁, fun _ => hWm⟩
  have key : (U₀ ∈ regularConstrainedCriticalSet (Averaging.smoothingRadius L) ε K k Ω'
        (activeBondSet K k Ω') (datumImage σ V)) =
      (transportGaugeField σ U ∈ regularConstrainedCriticalSet (Averaging.smoothingRadius L) ε K k Ω'
        (activeBondSet K k Ω') (datumImage σ V)) := hf.2 hM Prop _ hinv U₀ hU₀ U hU
  refine ⟨by rw [← hasActiveCriticalOrbit_congr ε hset]; exact hM', ?_⟩
  rw [← regularConstrainedCriticalSet_congr ε hset]
  exact key.mp hU₀
theorem TranslationSetting.combToBlockSite_image (s : TranslationSetting σ i K k Ω Ω') {n : ℕ}
    (hn : n + 1 ≤ k) {z₀ z : SiteAtLevel L m K (n + 1)} {x₀ x : SiteAtLevel L m K n}
    (hz : (z : FourTorus L m) = σ z₀) (hx : (x : FourTorus L m) = σ x₀) :
    combToBlockSite z x = pathImage σ (combToBlockSite z₀ x₀) := by
  have hjj : levelDepth K (n + 1) ≤ levelDepth K n := levelDepth_anti (Nat.le_succ n)
  refine coordinateComb_image s.fwd (s.depth_ge n (by omega)) s.translation ?_ hx
  rw [coe_toSublattice s.L_pos hjj, coe_toSublattice s.L_pos hjj, hz]
theorem TranslationSetting.axialGauge_image (s : TranslationSetting σ i K k Ω Ω')
    {U : BondAtLevel L m K 0 → ComplexMatrix2}
    (hU : U ∈ towerAxialGaugeAwayFromEndpoints K k Ω (activeBondSet K k Ω)) :
    transportGaugeField σ U ∈ towerAxialGaugeAwayFromEndpoints K k Ω' (activeBondSet K k Ω') := by
  obtain ⟨hin, hg⟩ := hU
  have hobj := s.fwd.chains K k Ω Ω' s.depth_ge fun q _ => congrFun s.image_eq q
  have hnodes : ∀ t, IsEndpointOf (activeBondSet K k Ω') (σ t) ↔
      IsEndpointOf (activeBondSet K k Ω) t := hobj.2.2.2.2.2.2.2.2.2.1
  refine ⟨?_, ?_⟩
  · rw [s.region_zero]
    exact ⟨transport_isGaugeField s.fwd s.depth_zero hin.1,
      fun b hb => hin.2 _ (mt (mem_bondsInside_image s.fwd s.depth_zero (Ω 0) b).2 hb)⟩
  · intro a ha1 hak xa hxa n hna z hz x hx hnode
    rw [hobj.2.2.1 a hak] at hxa
    obtain ⟨y, hy, rfl⟩ := hxa
    have hnk : n + 1 ≤ k := by omega
    have hdn := s.depth_ge (n + 1) hnk
    have hdn' := s.depth_ge n (by omega)
    have hjj : levelDepth K (n + 1) ≤ levelDepth K n := levelDepth_anti (Nat.le_succ n)
    have hz₀c := s.bwd.sites _ hdn z
    have hx₀c := s.bwd.sites _ hdn' x
    have hz₀ : ((siteImage σ.symm z : SiteAtLevel L m K (n + 1)) : FourTorus L m) ∈
        refinedBlock (a - n - 1) y := by
      rw [hz₀c]
      refine (mem_image_iff_symm _ _).1 ?_
      rw [s.mapsBlocks _ (s.depth_ge a hak)]
      exact hz
    have hzz : siteImage σ (siteImage σ.symm z : SiteAtLevel L m K (n + 1)) = z := by
      apply Subtype.ext
      rw [s.fwd.sites _ hdn, hz₀c]
      simp
    have hx₀ : siteImage σ.symm x ∈
        sitesInBlock (levelDepth K n) (siteImage σ.symm z : SiteAtLevel L m K (n + 1)) := by
      show ((siteImage σ.symm x : SiteAtLevel L m K n) : FourTorus L m) ∈ refinedBlock 1 _
      rw [hx₀c]
      refine (mem_image_iff_symm _ _).1 ?_
      rw [s.mapsBlocks _ hdn]
      show (x : FourTorus L m) ∈ refinedBlock 1 (siteImage σ (siteImage σ.symm z))
      rw [hzz]
      exact hx
    have hn₀ : ¬IsEndpointOf (activeBondSet K k Ω)
        ((siteImage σ.symm x : SiteAtLevel L m K n) : FourTorus L m) := fun h => hnode (by
      have := (hnodes _).2 h
      rwa [hx₀c, Equiv.apply_symm_apply] at this)
    have hres := hg a ha1 hak y hy n hna _ hz₀ _ hx₀ hn₀
    have hzc : (z : FourTorus L m) =
        σ ((siteImage σ.symm z : SiteAtLevel L m K (n + 1)) : FourTorus L m) := by
      rw [hz₀c]
      simp
    have hxc : (x : FourTorus L m) =
        σ ((siteImage σ.symm x : SiteAtLevel L m K n) : FourTorus L m) := by
      rw [hx₀c]
      simp
    rw [s.region_zero, averaging_transport s.fwd ((by omega : n ≤ k).trans s.k_le) hdn' (Ω 0) hin.1,
      s.combToBlockSite_image hnk hzc hxc, pathHolonomy_image s.fwd hdn']
    exact hres
theorem TranslationSetting.isRepresentative_image (s : TranslationSetting σ i K k Ω Ω') {ε : ℝ}
    (hε : 0 < ε) (hV : ∀ j ≤ k, V' j = transportGaugeField σ (V j))
    (hD : IsLinkDatum (activeBondSet K k Ω) V) (hM : HasActiveCriticalOrbit ε K k Ω V)
    {U : BondAtLevel L m K 0 → ComplexMatrix2} (hU : IsActiveGaugeRepresentative ε K k Ω V U) :
    IsActiveGaugeRepresentative ε K k Ω' V' (transportGaugeField σ U) :=
  ⟨(s.critical_image hε hV hD hM hU.1).2, s.axialGauge_image hU.2⟩
theorem TranslationSetting.hasRepresentative_image (s : TranslationSetting σ i K k Ω Ω') {ε : ℝ}
    (hε : 0 < ε) (hV : ∀ j ≤ k, V' j = transportGaugeField σ (V j))
    (hD : IsLinkDatum (activeBondSet K k Ω) V) (hR : HasActiveGaugeRepresentative ε K k Ω V) :
    HasActiveGaugeRepresentative ε K k Ω' V' ∧
      activeGaugeRepresentative ε K k Ω' V' =
        transportGaugeField σ (activeGaugeRepresentative ε K k Ω V) := by
  obtain ⟨hM, U, hU, huniq⟩ := hR
  have hrep := s.isRepresentative_image hε hV hD hM hU
  have hM' := (s.critical_image hε hV hD hM hU.1).1
  have hD' := s.isLinkDatum_image hV hD
  have hback := s.datum_eq_symm hV
  have huniq' : ∀ W, IsActiveGaugeRepresentative ε K k Ω' V' W →
      W = transportGaugeField σ U := by
    intro W hW
    have h₂ := huniq _ (s.symm.isRepresentative_image hε hback hD' hM' hW)
    rw [← h₂]
    exact (transport_symm_transport s.bwd s.depth_zero W).symm
  refine ⟨⟨hM', _, hrep, huniq'⟩, ?_⟩
  have e₁ : activeGaugeRepresentative ε K k Ω V = U := huniq _ (Classical.epsilon_spec ⟨U, hU⟩)
  rw [e₁]
  exact huniq' _ (Classical.epsilon_spec ⟨_, hrep⟩)
theorem TranslationSetting.isLinkDatum_expTwisted (s : TranslationSetting σ i K k Ω Ω')
    (hreal : ∀ j ≤ k, IsGaugeField compactGaugeGroup (activeBondsAt K k Ω j) (V j))
    {B : ActiveFamily L m K k Ω}
    (hB : B ∈ selfAdjointFunctions (PositiveBondIn (activeBondSet K k Ω))) :
    IsLinkDatum (activeBondSet K k Ω) (expTwistedDatum B V) := by
  classical
  rintro ⟨j, b⟩ hq
  have hjk : j ≤ k := level_le_of_mem hq
  have hq' := opposite_mem_active hq
  have hrr : b.opposite.opposite = b := Bond.ext rfl rfl
  have hval : ∀ c : BondAtLevel L m K j,
      (⟨j, c⟩ : Σ j : ℕ, BondAtLevel L m K j) ∈ activeBondSet K k Ω →
      c.IsPositivelyOriented → expTwist (familyAtLevel B j) (V j) c ∈ compactGaugeGroup := by
    intro c hc hp
    simp only [expTwist]
    rw [if_pos hp, familyAtLevel, dif_pos ⟨hc, hp⟩]
    exact mul_mem (matExp_smul_I_mem (hB.1 _) (congrFun hB.2 _))
      ((hreal j hjk).1 c ⟨hc.1.2, hc.2⟩)
  show expTwist (familyAtLevel B j) (V j) b ∈ compactGaugeGroup ∧ (_ →
    expTwist (familyAtLevel B j) (V j) b.opposite =
      (expTwist (familyAtLevel B j) (V j) b)⁻¹)
  rcases s.dichotomy j hjk b with ⟨hp, hn⟩ | ⟨hp, hn⟩
  · refine ⟨hval b hq hp, fun _ => ?_⟩
    simp only [expTwist]
    rw [if_neg hn, if_pos hp, hrr]
  · have hv := hval _ hq' hp
    have e : expTwist (familyAtLevel B j) (V j) b =
        (expTwist (familyAtLevel B j) (V j) b.opposite)⁻¹ := by
      conv_lhs => simp only [expTwist]
      rw [if_neg hn]
      conv_rhs => simp only [expTwist]
      rw [if_pos hp]
    refine ⟨by rw [e]; exact inv_mem_compact hv, fun _ => ?_⟩
    rw [e, inv_inv_of_mem_compact hv]
def TranslationSetting.pushForward (s : TranslationSetting σ i K k Ω Ω')
    (Φ : ActiveFamily L m K k Ω → BondAtLevel L m K 0 → ComplexMatrix2) :
    ActiveFamily L m K k Ω' → BondAtLevel L m K 0 → ComplexMatrix2 :=
  fun B' => transportGaugeField σ (Φ (B' ∘ s.positiveEquiv))
theorem TranslationSetting.mem_ball_iff (s : TranslationSetting σ i K k Ω Ω') (rB : ℝ)
    (B' : ActiveFamily L m K k Ω') :
    B' ∘ s.positiveEquiv ∈ complexFamilyBall (activeBondSet K k Ω) rB ↔
      B' ∈ complexFamilyBall (activeBondSet K k Ω') rB :=
  mem_supBall_comp s.positiveEquiv.surjective B' rB
theorem TranslationSetting.pushForward_isContinuation (s : TranslationSetting σ i K k Ω Ω')
    {ε εBar rB : ℝ} (hε : 0 < ε) (hV : ∀ j ≤ k, V' j = transportGaugeField σ (V j))
    (hF : IsBallDatum ε εBar K k Ω' V')
    {Φ : ActiveFamily L m K k Ω → BondAtLevel L m K 0 → ComplexMatrix2}
    (hΦ : IsMinimizerContinuation ε εBar rB K k Ω V Φ) :
    IsMinimizerContinuation ε εBar rB K k Ω' V' (s.pushForward Φ) := by
  obtain ⟨hF₀, ⟨f₁, f₂, hh⟩, hval, N, ⟨hNsub, D, hD, h0, hDN⟩, hN⟩ := hΦ
  have hreal := hF₀.1.1
  have hsetball : complexFamilyBall (activeBondSet K k Ω') rB =
      (fun B' : ActiveFamily L m K k Ω' => B' ∘ s.positiveEquiv) ⁻¹'
        complexFamilyBall (activeBondSet K k Ω) rB := by
    ext B'
    exact (s.mem_ball_iff rB B').symm
  have hP : ∀ B' : ActiveFamily L m K k Ω', B' ∘ s.positiveEquiv ∈ realFamilyBall rB K k Ω ↔
      B' ∈ realFamilyBall rB K k Ω' := fun B' =>
    and_congr (s.mem_ball_iff rB B') (mem_selfAdjoint_comp s.positiveEquiv B')
  have hHol : ∃ (_ : Fintype (PositiveBondIn (activeBondSet K k Ω')))
      (_ : Fintype (bondsInside (Ω' 0) : Set (BondAtLevel L m K 0))),
      IsHolomorphicMatrixValued (complexFamilyBall (activeBondSet K k Ω') rB)
        fun (B : ActiveFamily L m K k Ω') (c : (bondsInside (Ω' 0) :
          Set (BondAtLevel L m K 0))) => s.pushForward Φ B c := by
    let g₁ : Fintype (PositiveBondIn (activeBondSet K k Ω')) :=
      Fintype.ofEquiv _ s.positiveEquiv
    let g₂ : Fintype (bondsInside (Ω' 0) : Set (BondAtLevel L m K 0)) :=
      Fintype.ofEquiv _ s.insideEquiv.symm
    have hr := isHolomorphicMatrixValued_reindex s.positiveEquiv s.insideEquiv hh
    rw [← hsetball] at hr
    exact ⟨g₁, g₂, hr⟩
  refine ⟨hF, hHol, ?_,
    (fun B' : ActiveFamily L m K k Ω' => B' ∘ s.positiveEquiv) ⁻¹' N,
    ⟨?_, (fun B' : ActiveFamily L m K k Ω' => B' ∘ s.positiveEquiv) ⁻¹' D, ?_, ?_, ?_⟩, ?_⟩
  · intro B' hB'
    obtain ⟨h₁, h₂⟩ := hval _ ((s.mem_ball_iff rB B').2 hB')
    refine ⟨?_, fun c hc => h₂ _ (mt (s.mem_inside_iff c).2 hc)⟩
    rw [s.region_zero]
    exact transport_isGaugeField s.fwd s.depth_zero h₁
  · exact fun B' hB' => (hP B').1 (hNsub hB')
  · obtain ⟨O, hO, rfl⟩ := hD
    refine ⟨(fun B' : ActiveFamily L m K k Ω' => B' ∘ s.positiveEquiv) ⁻¹' O,
      hO.preimage (continuous_pi fun p => continuous_apply (s.positiveEquiv p)), ?_⟩
    ext B'
    exact and_congr Iff.rfl (hP B')
  · exact h0
  · exact fun B' hB' => hDN hB'
  · intro B' hB'
    obtain ⟨hr, he⟩ := hN _ hB'
    have hD₀ := s.isLinkDatum_expTwisted hreal (hNsub hB').2
    obtain ⟨h₁, h₂⟩ := s.hasRepresentative_image hε (s.expTwistedDatum_eq hV B') hD₀ hr
    refine ⟨h₁, ?_⟩
    show transportGaugeField σ (Φ (B' ∘ s.positiveEquiv)) = _
    rw [he, h₂]
theorem TranslationSetting.hasUnique_image (s : TranslationSetting σ i K k Ω Ω')
    {ε εBar rB : ℝ} (hε : 0 < ε) (hV : ∀ j ≤ k, V' j = transportGaugeField σ (V j))
    (hF : IsBallDatum ε εBar K k Ω' V')
    (h : HasUniqueMinimizerContinuation ε εBar rB K k Ω V) :
    HasUniqueMinimizerContinuation ε εBar rB K k Ω' V' := by
  obtain ⟨Φ, hΦ, huniq⟩ := h
  refine ⟨s.pushForward Φ, s.pushForward_isContinuation hε hV hF hΦ, fun Φ'' h'' B' hB' => ?_⟩
  have hb := s.symm.pushForward_isContinuation hε (s.datum_eq_symm hV) hΦ.1 h''
  have he := huniq _ hb ((s.mem_ball_iff rB B').2 hB')
  show Φ'' B' = transportGaugeField σ (Φ (B' ∘ s.positiveEquiv))
  rw [← he]
  show Φ'' B' = transportGaugeField σ (transportGaugeField σ.symm
    (Φ'' ((B' ∘ s.positiveEquiv) ∘ s.symm.positiveEquiv)))
  have hcomp : (B' ∘ s.positiveEquiv) ∘ s.symm.positiveEquiv = B' := by
    funext p
    obtain ⟨⟨a, b⟩, h⟩ := p
    exact congrArg B' (Subtype.ext (congrArg (Sigma.mk a)
      (image_preimage s.fwd (s.depth_ge a (level_le_of_mem h.1)) b)))
  rw [hcomp]
  exact (transport_symm_transport s.bwd s.depth_zero (Φ'' B')).symm
end Setting
theorem symm_mem_latticeIsometries (hG : LatticeIsometryGroupActionStatement)
    (hs : Conventions.IsAdmissibleBlockingFactor L) (hm : 0 < m) {i : ℤ} (hi : -(m : ℤ) ≤ i)
    {σ : FourTorus L m ≃ FourTorus L m} (hσ : σ ∈ latticeIsometries L m i) :
    σ.symm ∈ latticeIsometries L m i := by apply _root_.YangMills.Construction.PeriodicLattice.EquivarianceProof.symm_mem_latticeIsometries <;> assumption
theorem isometryData_of_mem (hG : LatticeIsometryGroupActionStatement)
    (hO : IsometryPreservesChainObjects) (hA : AveragingMapsEquivariant)
    (hS : IsometriesPreserveCells)
    (hs : Conventions.IsAdmissibleBlockingFactor L) (hm : 0 < m)
    {i : ℤ} (hi : -(m : ℤ) ≤ i) {σ : FourTorus L m ≃ FourTorus L m}
    (hσ : σ ∈ latticeIsometries L m i) :
    IsometryData σ i where
  ends_image := fun j hj => ((hG L m i hs hm hi).2.2.2.2 σ hσ j hj).1.2.2.2.1
  ends_preimage := fun j hj =>
    ((hG L m i hs hm hi).2.2.2.2 σ.symm (symm_mem_latticeIsometries hG hs hm hi hσ) j hj).1.2.2.2.1
  chains := hO L m i σ hs hm hi hσ
  blockFields := fun K => (hA L m hs hm i hi σ hσ K).2.1
  sites := fun j hj => (hS L m i j σ hs hm hi hσ hj).1
end MinimizerTranslation
open MinimizerTranslation in
theorem translationPreservesUniqueContinuation
    (hG : LatticeIsometryGroupActionStatement)
    (hO : IsometryPreservesChainObjects)
    (hA : AveragingMapsEquivariant)
    (hS : IsometriesPreserveCells)
    (hT : TwistedTransportIsometryInvariance)
    (hR : IsometryCovariantRegularSetsAndAxialGauge)
    (hTow : IsometriesPreserveTowersAndStepCubes)
    (hBl : IsometryInvariance.InvariantUnderIsometries)
    (horient : BondOrientationDichotomy) :
    TranslationPreservesUniqueContinuation := by
  intro L m hL hm i hi σ hσ ε εBar rB hε hεB hrB K k e r Ω hseq hsep V₀ ht
  have hσ' := symm_mem_latticeIsometries hG hL hm hi hσ
  have hkK : k ≤ K := hseq.2.2.1
  have hK : 0 < K := by have := hseq.2.1; omega
  have hin : i ≤ levelDepth K k := hseq.index_le_levelDepth
  have hdep : ∀ q ≤ k, i ≤ levelDepth K q := fun q hq => hin.trans (levelDepth_anti hq)
  have hdet : IsDeterminingChainFrom K k i Ω :=
    ⟨hseq.2.2.1, hseq.2.2.2.1, hseq.2.2.2.2⟩
  have hdet' := ((hTow.1 L m i σ hL hm hi hσ).2.1 K k Ω hdet).1
  have hlevel : ∀ a ≤ k, -(m : ℤ) < levelDepth K a := by
    intro a ha
    simp only [levelDepth]
    omega
  have hRσ := hR L m K hL hm hK i σ hi hσ
  have hfn := hRσ.1
  have s : TranslationSetting σ i K k Ω (imageChain σ Ω) :=
    { L_pos := by have := hL.2; omega
      fwd := isometryData_of_mem hG hO hA hS hL hm hi hσ
      bwd := isometryData_of_mem hG hO hA hS hL hm hi hσ'
      translation := ht
      image_eq := rfl
      preimage_eq := by
        funext q
        exact (Equiv.symm_image_image σ (Ω q)).symm
      k_le := hkK
      depth_ge := hdep
      pos_image := fun a ha b hb =>
        (hT L m i σ hL hm hi hσ).1 (Or.inl ht) _ (hlevel a ha) (hdep a ha) b hb
      pos_preimage := fun a ha b hb =>
        (hT L m i σ.symm hL hm hi hσ').1 (Or.inl (isTorusTranslation_symm ht)) _ (hlevel a ha)
          (hdep a ha) b hb
      dichotomy := fun a ha b => horient L m hL hm _ (hlevel a ha) b
      isDetermining := hdet
      isDetermining_image := hdet'
      orbitFns := hfn
      orbitFns_symm := (hR L m K hL hm hK i σ.symm hi hσ').1
      mapsBlocks := fun j hj => ((hBl L m hL hm i hi σ hσ).1 j hj).1
      mapsBlocks_symm := fun j hj => ((hBl L m hL hm i hi σ.symm hσ').1 j hj).1 }
  have hreg := hRσ.2.2.1 εBar e r k Ω hεB hdet hsep
  have hV : ∀ j ≤ k, datumImage σ V₀ j = transportGaugeField σ (V₀ j) := fun _ _ => rfl
  constructor
  · intro hone
    obtain ⟨Φ, hΦ, -⟩ := id hone
    obtain ⟨h₁, h₂⟩ := hΦ.1
    exact s.hasUnique_image hε hV ⟨hreg.1 _ h₁,
      (hfn ε k Ω V₀ hε hdet (isLinkDatum_of_gaugeFields h₁.1)).1.1 h₂⟩ hone
  · intro hone
    obtain ⟨Φ, hΦ, -⟩ := id hone
    obtain ⟨h₁, h₂⟩ := hΦ.1
    obtain ⟨V, hVr, hVe⟩ := hreg.2 _ h₁
    have heq : ∀ j ≤ k, V j = V₀ j := by
      intro j hj
      have := congrArg (transportGaugeField σ.symm) (hVe j hj)
      simp only [datumImage] at this
      rwa [transport_symm_transport s.fwd (hdep j hj),
        transport_symm_transport s.fwd (hdep j hj)] at this
    have hr₀ := mem_activeRegularRealFields_of_eq heq hVr
    exact s.symm.hasUnique_image hε (s.datum_eq_symm hV) ⟨hr₀,
      (hfn ε k Ω V₀ hε hdet (isLinkDatum_of_gaugeFields hr₀.1)).1.2 h₂⟩ hone
end PeriodicLattice
end YangMills.Construction
