import YangMills.Construction.PassageToTheLimit.SeparatedTuplesMultilinearFunctionalsCentredFunctionalTensors
import YangMills.Construction.ReflectionPositivity.CentredFunctionalOfAFamilyOfFunctionals
import YangMills.Construction.ReflectionPositivity.SupportsTranslationsSeparationAndTransportOfTuples
import YangMills.Construction.Torus.PointsAndTuplesOfTorusOrFourSpace
import Mathlib
set_option autoImplicit false
open Filter Set
open scoped Topology
noncomputable section
namespace YangMills.Construction.ReflectionPositivity.AxisMirror.Ambient
def SideSequence (D : MirrorData) : Ambient → (ℕ+ → ℝ) → Prop
  | torus, ℓ => ∀ j, ℓ j = D.side
  | euclidean, ℓ => Tendsto ℓ atTop atTop
structure LatticeDataSeq (D : MirrorData) (E : Ambient) where
  K : ℕ+ → ℕ+
  ℓ : ℕ+ → ℝ
  β : ℕ+ → ℝ
  ℓ_mem : ∀ j, ℓ j ∈ PeriodicLattice.torusSides D.L
  β_pos : ∀ j, 0 < β j
  K_tendsto : Tendsto (fun j => (K j : ℕ)) atTop atTop
  isSideSequence : SideSequence D E ℓ
def IsSepLipList (D : MirrorData) : (E : Ambient) → FnList D E → Prop
  | torus, X =>
    LimitSpaces.Ambient.periodic.IsSepLipTuple D.toStandingParameters univ X.get
  | euclidean, X =>
    LimitSpaces.Ambient.euclidean.IsSepLipTuple D.toStandingParameters univ X.get
def listOnEqTorus {L : ℕ} {m m' : ℕ+} (h : m = m') (X : List (PeriodicLattice.FourTorus L m → ℝ)) :
    List (PeriodicLattice.FourTorus L m' → ℝ) :=
  h ▸ X
namespace LatticeDataSeq
variable {D : MirrorData}
section Index
variable {E : Ambient} (S : LatticeDataSeq D E)
def exp (j : ℕ+) : ℕ+ :=
  ⟨Classical.choose (S.ℓ_mem j), (Classical.choose_spec (S.ℓ_mem j)).1⟩
theorem ℓ_eq_torusSide (j : ℕ+) : S.ℓ j = PeriodicLattice.torusSide D.L (S.exp j) :=
  (Classical.choose_spec (S.ℓ_mem j)).2
def standingAtExp (j m : ℕ+) : Conventions.StandingParameters :=
  ⟨D.L, D.isAdmissible, S.K j, m⟩
def mirrorDataAtExp (j m : ℕ+) : CutoffMirrors.MirrorData :=
  ⟨S.standingAtExp j m, S.β j, S.β_pos j, 0⟩
def standingAt (j : ℕ+) : Conventions.StandingParameters := S.standingAtExp j (S.exp j)
def mirrorDataAt (j : ℕ+) : CutoffMirrors.MirrorData := S.mirrorDataAtExp j (S.exp j)
theorem side_standingAt (j : ℕ+) : (S.standingAt j).side = S.ℓ j :=
  (S.ℓ_eq_torusSide j).symm
end Index
theorem exp_eq_of_torusSide_eq {L : ℕ} (hL : Conventions.IsAdmissibleBlockingFactor L) {m m' : ℕ+}
    (h : PeriodicLattice.torusSide L m = PeriodicLattice.torusSide L m') : m = m' := by
  have hL1 : 1 < (L : ℝ) := by
    have := hL.2
    exact_mod_cast (by omega : 1 < L)
  have hp : (L : ℝ) ^ (m : ℕ) = (L : ℝ) ^ (m' : ℕ) := by
    simpa [PeriodicLattice.torusSide] using h
  exact PNat.eq (pow_right_injective₀ (by linarith) hL1.ne' hp)
theorem exp_eq (S : LatticeDataSeq D torus) (j : ℕ+) : S.exp j = D.m :=
  exp_eq_of_torusSide_eq D.isAdmissible ((S.ℓ_eq_torusSide j).symm.trans (S.isSideSequence j))
def listAt : {E : Ambient} → (S : LatticeDataSeq D E) → (j : ℕ+) → FnList D E →
    List ((S.standingAt j).Torus → ℝ)
  | torus, S, j, X => listOnEqTorus (S.exp_eq j).symm X
  | euclidean, S, j, X => LimitSpaces.periodizeList (S.standingAt j) X
def ReadsAt : {E : Ambient} → LatticeDataSeq D E → ℕ+ → FnList D E → Prop
  | torus, _, _, X => IsSepLipList D torus X
  | euclidean, S, j, X =>
    IsSepLipList D euclidean X ∧ LimitSpaces.FitsInTorus (S.standingAt j) X
variable {E : Ambient} (S : LatticeDataSeq D E)
def connectedAt (j : ℕ+) (X : FnList D E) : ℂ :=
  SchwingerFunctions.connectedSchwinger D.L (S.exp j) (S.K j) (S.β j) (S.listAt j X).get
def centredAt (j : ℕ+) (X : FnList D E) : ℝ :=
  (S.mirrorDataAt j).gibbsFunctionalList (S.listAt j X)
def TendsToFamily (T : FunctionalFamily D E) : Prop :=
  ∀ (n : ℕ) (hn : 2 ≤ n) (X : separatedN D E n),
    Tendsto (fun j => S.connectedAt j X.1) atTop (𝓝 ((T n hn X : ℝ) : ℂ))
theorem connected_listOnEqTorus {L : ℕ} {m m' : ℕ+} (h : m = m') (K : ℕ) (β : ℝ)
    (X : List (PeriodicLattice.FourTorus L m → ℝ)) :
    SchwingerFunctions.connectedSchwinger L m' K β (listOnEqTorus h X).get =
      SchwingerFunctions.connectedSchwinger L m K β X.get := by
  subst h
  rfl
theorem connectedAt_torus (S : LatticeDataSeq D torus) (j : ℕ+) (X : FnList D torus) :
    S.connectedAt j X = SchwingerFunctions.connectedSchwinger D.L D.m (S.K j) (S.β j) X.get :=
  connected_listOnEqTorus (S.exp_eq j).symm _ _ X
theorem centredAt_torus (S : LatticeDataSeq D torus) (j : ℕ+) (X : FnList D torus) :
    S.centredAt j X = (S.mirrorDataAtExp j D.m).gibbsFunctionalList X := by
  have key : ∀ (m : ℕ+) (h : D.m = m), (S.mirrorDataAtExp j m).gibbsFunctionalList
      (listOnEqTorus h X) = (S.mirrorDataAtExp j D.m).gibbsFunctionalList X := by
    rintro m rfl
    rfl
  exact key _ (S.exp_eq j).symm
theorem euclidNormVec_eq_norm (v : Fin 4 → ℝ) :
    TorusMetric.euclidNormVec v = ‖(WithLp.toLp 2 v : EuclideanSpace ℝ (Fin 4))‖ := by apply _root_.YangMills.Construction.AmbientPoints.euclidNormVec_eq_norm <;> assumption
theorem exists_bound_of_isCompactWrt {Z : Set (Fin 4 → ℝ)}
    (hZ : MetricNotions.IsCompactWrt InfiniteLattice.euclidDist Z) :
    ∃ R : ℝ, ∀ x ∈ Z, TorusMetric.euclidNormVec x ≤ R := by
  let ball : ℕ → Set (Fin 4 → ℝ) := fun r => {x | TorusMetric.euclidNormVec x < r}
  have hopen : ∀ U ∈ range ball, MetricNotions.IsOpenWrt InfiniteLattice.euclidDist U := by
    rintro _ ⟨r, rfl⟩ x hx
    refine ⟨r - TorusMetric.euclidNormVec x, sub_pos.2 hx, fun y hy => ?_⟩
    have h₁ : TorusMetric.euclidNormVec y ≤
        TorusMetric.euclidNormVec x + TorusMetric.euclidNormVec (x - y) := by
      have e : y = x - (x - y) := by abel
      conv_lhs => rw [e]
      simp only [euclidNormVec_eq_norm, WithLp.toLp_sub]
      exact norm_sub_le _ _
    have h₂ : TorusMetric.euclidNormVec (x - y) < r - TorusMetric.euclidNormVec x := hy
    show TorusMetric.euclidNormVec y < r
    linarith
  have hcover : Z ⊆ ⋃₀ range ball := fun x _ => by
    obtain ⟨r, hr⟩ := exists_nat_gt (TorusMetric.euclidNormVec x)
    exact ⟨ball r, ⟨r, rfl⟩, hr⟩
  obtain ⟨𝒰, hsub, hfin, hZ𝒰⟩ := hZ _ hopen hcover
  have hr : ∀ U ∈ 𝒰, ∃ r, ball r = U := fun U hU => hsub hU
  choose! r hr using hr
  obtain ⟨M, hM⟩ := (hfin.image r).bddAbove
  refine ⟨M, fun x hx => ?_⟩
  obtain ⟨U, hU, hxU⟩ := hZ𝒰 hx
  rw [← hr U hU] at hxU
  have h₁ : TorusMetric.euclidNormVec x < r U := hxU
  have h₂ : ((r U : ℕ) : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM (mem_image_of_mem r hU)
  exact h₁.le.trans h₂
theorem eventually_fitsInTorus (S : LatticeDataSeq D euclidean) {X : FnList D euclidean}
    (hX : X ∈ separatedAll D euclidean) :
    ∀ᶠ j in atTop, LimitSpaces.FitsInTorus (S.standingAt j) X := by
  obtain ⟨n, -, hsep⟩ := mem_iUnion.1 hX
  have hcompact : ∀ f ∈ X, MetricNotions.IsCompactWrt InfiniteLattice.euclidDist
      (closedSupport D euclidean f) := fun f hf => (hsep.1 f hf).2
  have hbound : ∀ Y : FnList D euclidean, (∀ f ∈ Y, MetricNotions.IsCompactWrt
      InfiniteLattice.euclidDist (closedSupport D euclidean f)) →
      ∃ R : ℝ, ∀ f ∈ Y, ∀ x ∈ closedSupport D euclidean f, TorusMetric.euclidNormVec x ≤ R := by
    intro Y
    induction Y with
    | nil => exact fun _ => ⟨0, by simp⟩
    | cons f Y ih =>
      intro h
      obtain ⟨R₁, h₁⟩ := exists_bound_of_isCompactWrt (h f (by simp))
      obtain ⟨R₂, h₂⟩ := ih fun g hg => h g (by simp [hg])
      refine ⟨max R₁ R₂, fun g hg x hx => ?_⟩
      rcases List.mem_cons.1 hg with rfl | hg
      · exact (h₁ x hx).trans (le_max_left _ _)
      · exact (h₂ g hg x hx).trans (le_max_right _ _)
  obtain ⟨R, hR⟩ := hbound X hcompact
  have hℓ : Tendsto S.ℓ atTop atTop := S.isSideSequence
  filter_upwards [hℓ.eventually_ge_atTop (4 * R)] with j hj
  refine ⟨fun f hf => hcompact f hf, fun x hx y hy => ?_⟩
  have hmem : ∀ z ∈ LimitSpaces.Ambient.euclidean.listSupport (S.standingAt j) X,
      TorusMetric.euclidNormVec z ≤ R := fun z hz => by
    obtain ⟨f, hf, hzf⟩ := mem_iUnion₂.1
      (hz : z ∈ ⋃ f ∈ X, LimitSpaces.Ambient.euclidean.closedSupport (S.standingAt j) f)
    exact hR f hf z hzf
  have h₁ : TorusMetric.euclidNormVec x ≤ R := hmem x hx
  have h₂ : TorusMetric.euclidNormVec y ≤ R := hmem y hy
  have h₃ : TorusMetric.euclidNormVec (x - y) ≤
      TorusMetric.euclidNormVec x + TorusMetric.euclidNormVec y := by
    simp only [euclidNormVec_eq_norm, WithLp.toLp_sub]
    exact norm_sub_le _ _
  rw [side_standingAt]
  linarith
end LatticeDataSeq
end YangMills.Construction.ReflectionPositivity.AxisMirror.Ambient
end
