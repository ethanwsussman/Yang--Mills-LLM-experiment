import YangMills.Construction.Towers.DilationCarriesSetsAtAStepOfTheWholeSpaceProof
import YangMills.Construction.Towers.LinearMapsOnFormsSupportedOnPivotBondsOfTheWholeLatticeProof
import Mathlib
set_option autoImplicit false
namespace YangMills.Construction.Tower.FullSpace
open YangMills.Construction.InfiniteLattice
namespace AnyOrientation
variable {a a' : ℝ}
theorem toFiner_coe (L : ℕ) (h : a = L * a') (y : InfiniteLattice.LatticePoint a) :
    ((toFiner a' y : InfiniteLattice.LatticePoint a') : AmbientSpace) = y := by apply _root_.YangMills.Construction.Tower.FullSpace.PivotSupportedForms.toFiner_coe <;> assumption
theorem isAxisDisplacement_toFiner (L : ℕ) (h : a = L * a') (c : InfiniteLattice.Link a)
    (μ : Fin 4) (n : ℤ) (hc : c.terminal - c.initial = n • axisStep a μ) :
    IsAxisDisplacement (toFiner a' c.initial) (toFiner a' c.terminal) μ (n * L) := by
  apply Subtype.ext
  funext ρ
  have e1 := congrArg (fun s : InfiniteLattice.LatticePoint a => (s : AmbientSpace) ρ) hc
  have e2 : ((toFiner a' c.terminal : InfiniteLattice.LatticePoint a') : AmbientSpace) ρ =
      (c.terminal : AmbientSpace) ρ := by
    rw [toFiner_coe L h]
  have e3 : ((toFiner a' c.initial : InfiniteLattice.LatticePoint a') : AmbientSpace) ρ =
      (c.initial : AmbientSpace) ρ := by
    rw [toFiner_coe L h]
  simp only [AddSubgroup.coe_sub, Pi.sub_apply, AddSubgroup.coe_zsmul, Pi.smul_apply, axisStep,
    zsmul_eq_mul] at e1 ⊢
  rw [e2, e3, e1]
  by_cases hρ : ρ = μ
  · subst hρ
    simp only [Pi.single_eq_same, h]
    push_cast
    ring
  · simp [Pi.single_eq_of_ne hρ]
theorem axisPath_eq_signedSteps (ha : a ≠ 0) {x x' : InfiniteLattice.LatticePoint a} {μ : Fin 4}
    {n : ℤ} (h : IsAxisDisplacement x x' μ n) : axisPath x x' = signedSteps x μ n := by apply _root_.YangMills.Construction.Tower.FullSpace.ScalingOfStepSets.axisPath_eq_signedSteps <;> assumption
theorem terminal_sub_initial_of_mem_forwardSteps {x : InfiniteLattice.LatticePoint a} {μ : Fin 4}
    {n : ℕ} {b : InfiniteLattice.Link a} (h : b ∈ forwardSteps x μ n) :
    b.terminal - b.initial = axisStep a μ := by
  induction n generalizing x with
  | zero => simp [forwardSteps] at h
  | succ n ih =>
    rw [forwardSteps, List.mem_cons] at h
    rcases h with rfl | h
    · simp [InfiniteLattice.Link.forwardFrom]
    · exact ih h
theorem terminal_sub_initial_of_mem_axisPath (ha : a ≠ 0) {x x' : InfiniteLattice.LatticePoint a}
    {μ : Fin 4} {n : ℕ} (hd : IsAxisDisplacement x x' μ n) {b : InfiniteLattice.Link a}
    (hb : b ∈ axisPath x x') : b.terminal - b.initial = axisStep a μ := by
  rw [axisPath_eq_signedSteps ha hd, signedSteps, if_pos (Int.natCast_nonneg n)] at hb
  exact terminal_sub_initial_of_mem_forwardSteps hb
theorem eq_of_axisStep_eq_or_neg (ha : a ≠ 0) {μ ν : Fin 4}
    (h : axisStep a μ = axisStep a ν ∨ axisStep a μ = -axisStep a ν) : μ = ν := by apply _root_.YangMills.Construction.Tower.FullSpace.PivotSupportedForms.axis_eq_of_axisStep_eq <;> assumption
theorem neg_axisStep_ne_axisStep (ha : a ≠ 0) (μ ν : Fin 4) : -axisStep a μ ≠ axisStep a ν := by
  intro h
  have hμν : ν = μ := eq_of_axisStep_eq_or_neg ha (Or.inr h.symm)
  subst hμν
  have hv : (axisStep a ν : AmbientSpace) ν = a := by simp [axisStep]
  have hw := congrArg (fun s : InfiniteLattice.LatticePoint a => (s : AmbientSpace) ν) h
  simp only [AddSubgroup.coe_neg, Pi.neg_apply, hv] at hw
  apply ha
  linarith
theorem linkHasAxis_iff_of_pos (ha : a ≠ 0) {b : InfiniteLattice.Link a} {μ : Fin 4}
    (h : b.terminal - b.initial = axisStep a μ) (ν : Fin 4) : LinkHasAxis b ν ↔ μ = ν := by
  constructor
  · intro hν
    rcases hν with hν | hν
    · exact eq_of_axisStep_eq_or_neg ha (Or.inl (h.symm.trans hν))
    · exact eq_of_axisStep_eq_or_neg ha (Or.inr (h.symm.trans hν))
  · rintro rfl
    exact Or.inl h
theorem linkHasAxis_iff_of_neg (ha : a ≠ 0) {b : InfiniteLattice.Link a} {μ : Fin 4}
    (h : b.terminal - b.initial = -axisStep a μ) (ν : Fin 4) : LinkHasAxis b ν ↔ μ = ν := by
  constructor
  · intro hν
    rcases hν with hν | hν
    · exact eq_of_axisStep_eq_or_neg ha (Or.inr (neg_eq_iff_eq_neg.mp (h.symm.trans hν)))
    · exact eq_of_axisStep_eq_or_neg ha (Or.inl (neg_injective (h.symm.trans hν)))
  · rintro rfl
    exact Or.inr h
theorem not_isPositivelyOriented_of_neg (ha : a ≠ 0) {b : InfiniteLattice.Link a} {μ : Fin 4}
    (h : b.terminal - b.initial = -axisStep a μ) : ¬b.IsPositivelyOriented := by
  rintro ⟨ν, hν⟩
  exact neg_axisStep_ne_axisStep ha μ ν (h.symm.trans hν)
theorem isPivotLink_opposite (L : ℕ) {c : InfiniteLattice.Link a} {b : InfiniteLattice.Link a'}
    (hpath : axisPath (toFiner a' c.terminal) (toFiner a' c.initial) =
      ((axisPath (toFiner a' c.initial) (toFiner a' c.terminal)).map
        InfiniteLattice.Link.opposite).reverse)
    (h : IsPivotLink L a' c b) : IsPivotLink L a' c.opposite b.opposite := by
  refine ⟨⟨h.1.2, h.1.1⟩, ?_⟩
  change b.opposite ∈ axisPath (toFiner a' c.terminal) (toFiner a' c.initial)
  rw [hpath, List.mem_reverse]
  exact List.mem_map.mpr ⟨b, h.2, rfl⟩
theorem pivotLinkProperties_of_forward (L : ℕ) (ha : a ≠ 0) (ha' : a' ≠ 0) (hs : a = L * a')
    (hE : ∀ (c : InfiniteLattice.Link a) (μ : Fin 4), c.terminal - c.initial = axisStep a μ →
      ∃! b : InfiniteLattice.Link a', IsPivotLink L a' c b)
    (hR : ∀ (x x' : InfiniteLattice.LatticePoint a') (μ : Fin 4) (n : ℤ),
      IsAxisDisplacement x x' μ n →
        axisPath x' x = ((axisPath x x').map InfiniteLattice.Link.opposite).reverse)
    (c : InfiniteLattice.Link a) : PivotLinkProperties L a' c := by
  have hpath : ∀ c : InfiniteLattice.Link a,
      axisPath (toFiner a' c.terminal) (toFiner a' c.initial) =
        ((axisPath (toFiner a' c.initial) (toFiner a' c.terminal)).map
          InfiniteLattice.Link.opposite).reverse := by
    intro c
    obtain ⟨μ, h | h⟩ := c.isAdjacent
    · exact hR _ _ μ _ (isAxisDisplacement_toFiner L hs c μ 1 (by simpa using h))
    · exact hR _ _ μ _ (isAxisDisplacement_toFiner L hs c μ (-1) (by simpa using h))
  have hopp : ∀ (c : InfiniteLattice.Link a) (b : InfiniteLattice.Link a'),
      IsPivotLink L a' c b → IsPivotLink L a' c.opposite b.opposite :=
    fun c b h => isPivotLink_opposite L (hpath c) h
  have hstep : ∀ (c : InfiniteLattice.Link a) (μ : Fin 4), c.terminal - c.initial = axisStep a μ →
      ∀ b : InfiniteLattice.Link a', IsPivotLink L a' c b →
        b.terminal - b.initial = axisStep a' μ := by
    intro c μ hc b hb
    have hd : IsAxisDisplacement (toFiner a' c.initial) (toFiner a' c.terminal) μ (L : ℕ) := by
      simpa using isAxisDisplacement_toFiner L hs c μ 1 (by simpa using hc)
    exact terminal_sub_initial_of_mem_axisPath ha' hd hb.2
  have hopppos : ∀ (c : InfiniteLattice.Link a) (μ : Fin 4),
      c.terminal - c.initial = -axisStep a μ →
        c.opposite.terminal - c.opposite.initial = axisStep a μ := by
    intro c μ hc
    change c.initial - c.terminal = axisStep a μ
    rw [← neg_sub, hc, neg_neg]
  have huniq : ∀ c : InfiniteLattice.Link a,
      ∃! b : InfiniteLattice.Link a', IsPivotLink L a' c b := by
    intro c
    obtain ⟨μ, h | h⟩ := c.isAdjacent
    · exact hE c μ h
    · obtain ⟨b, hb, hu⟩ := hE c.opposite μ (hopppos c μ h)
      refine ⟨b.opposite, hopp c.opposite b hb, fun b' hb' => ?_⟩
      have hb'' : b'.opposite = b := hu b'.opposite (hopp c b' hb')
      rw [← hb'']
      rfl
  have hspec : ∀ c : InfiniteLattice.Link a, IsPivotLink L a' c (pivotLink L a' c) :=
    fun c => Classical.epsilon_spec (huniq c).exists
  have hpivopp : pivotLink L a' c.opposite = (pivotLink L a' c).opposite :=
    (huniq c.opposite).unique (hspec c.opposite) (hopp c _ (hspec c))
  have hdir : (∀ μ : Fin 4, LinkHasAxis (pivotLink L a' c) μ ↔ LinkHasAxis c μ) ∧
      ((pivotLink L a' c).IsPositivelyOriented ↔ c.IsPositivelyOriented) := by
    obtain ⟨μ, h | h⟩ := c.isAdjacent
    · have hb := hstep c μ h _ (hspec c)
      refine ⟨fun ν => ?_, ⟨fun _ => ⟨μ, h⟩, fun _ => ⟨μ, hb⟩⟩⟩
      rw [linkHasAxis_iff_of_pos ha' hb, linkHasAxis_iff_of_pos ha h]
    · have hb : (pivotLink L a' c).terminal - (pivotLink L a' c).initial = -axisStep a' μ := by
        have e1 := hstep c.opposite μ (hopppos c μ h) _ (hspec c.opposite)
        rw [hpivopp] at e1
        change (pivotLink L a' c).initial - (pivotLink L a' c).terminal = axisStep a' μ at e1
        rw [← e1, neg_sub]
      refine ⟨fun ν => ?_, ⟨fun hp => absurd hp (not_isPositivelyOriented_of_neg ha' hb),
        fun hp => absurd hp (not_isPositivelyOriented_of_neg ha h)⟩⟩
      rw [linkHasAxis_iff_of_neg ha' hb, linkHasAxis_iff_of_neg ha h]
  refine
    { mem_linkCorridor_iff := fun b => ⟨fun h => ⟨h.2, h.1⟩, fun h => ⟨h.2, h.1⟩⟩
      existsUnique_mem_axisPath := ?_
      isPivotLink := hspec c
      pivotLink_opposite := hpivopp
      linkHasAxis_iff := hdir.1
      isPositivelyOriented_iff := hdir.2 }
  obtain ⟨b, hb, hu⟩ := huniq c
  exact ⟨b, ⟨hb.2, hb.1⟩, fun b' h => hu b' ⟨h.2, h.1⟩⟩
end AnyOrientation
open AnyOrientation in
theorem pivotLinkOfAnyOrientation_holds
    (hY : CubesCorridorsPivotEdgesAndPaths) (hR : AxisPathReversal.statement) :
    PivotLinkOfAnyOrientation := by
  intro L hL k i hik c
  have hLpos : (0 : ℝ) < L := by
    have : 0 < L := by
      have := hL.2
      omega
    exact_mod_cast this
  have ha' : meshAt L k i ≠ 0 := (zpow_pos hLpos _).ne'
  have ha : meshAt L k (i + 1) ≠ 0 := (zpow_pos hLpos _).ne'
  have hs : meshAt L k (i + 1) = L * meshAt L k i := by
    unfold meshAt
    rw [← zpow_one_add₀ hLpos.ne']
    congr 1
    push_cast
    ring
  have hS : StepsEdgesAndCorridors L k (i + 1) :=
    (hY L hL k (i + 1) 1 (by omega) (by omega) (by omega) le_rfl (by omega)).2.2.1
  refine pivotLinkProperties_of_forward L ha ha' hs ?_ ?_ c
  · intro c μ hc
    obtain ⟨b, hb, hu⟩ := hS.existsUnique_corridorEdge c μ hc
    exact ⟨b, ⟨hb.2, hb.1⟩, fun b' h => hu b' ⟨h.2, h.1⟩⟩
  · intro x x' μ n hd
    exact (hR L k i hL (by omega) x x' μ n hd).2.1
end YangMills.Construction.Tower.FullSpace
