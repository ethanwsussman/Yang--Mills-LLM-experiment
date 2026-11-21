import YangMills.Construction.Towers.DerivativesOfTheActionOnFinitePlaquetteSetsAtTheSideInfinity
import YangMills.Construction.Towers.SecondDifferentialOfTheActionAsAKernelProof
import Mathlib
set_option autoImplicit false
open Set Filter
open scoped Topology Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction.Tower.FullSpace.ActionDerivsOnFiniteFaces
open Matrices (ComplexMatrix2)
open YangMills.Construction.Tower.FaceEdgeFinsets.Unbounded (facesMeeting)
open YangMills.Construction.Tower.FaceSum (faceSum faceTerm faceSumOfFamily)
variable {L k j : ℕ}
theorem forwardFrom_isPositivelyOriented {a : ℝ} (x : InfiniteLattice.LatticePoint a) (μ : Fin 4) :
    (InfiniteLattice.Link.forwardFrom x μ).IsPositivelyOriented :=
  ⟨μ, by simp [InfiniteLattice.Link.forwardFrom]⟩
theorem meshAt_pos (hL : Conventions.IsAdmissibleBlockingFactor L) : 0 < meshAt L k j := by apply _root_.YangMills.Construction.Tower.TrivialFieldAverages.meshAt_pos <;> assumption
theorem opposite_isPositivelyOriented_iff {a : ℝ} (ha : 0 < a) (b : InfiniteLattice.Link a) :
    b.opposite.IsPositivelyOriented ↔ ¬ b.IsPositivelyOriented := by apply _root_.YangMills.Construction.Tower.TrivialFieldAverages.link_opposite_positive_iff <;> assumption
def sideEdge (p : Face L k j) : Fin 4 → Edge L k j :=
  ![InfiniteLattice.Link.forwardFrom p.corner p.lowAxis,
    InfiniteLattice.Link.forwardFrom (p.corner + InfiniteLattice.axisStep _ p.lowAxis) p.highAxis,
    InfiniteLattice.Link.forwardFrom (p.corner + InfiniteLattice.axisStep _ p.highAxis) p.lowAxis,
    InfiniteLattice.Link.forwardFrom p.corner p.highAxis]
theorem sideEdge_mem (p : Face L k j) (i : Fin 4) : sideEdge p i ∈ faceEdges p := by
  fin_cases i <;> simp [sideEdge, faceEdges]
theorem sideEdge_isPositivelyOriented (p : Face L k j) (i : Fin 4) :
    (sideEdge p i).IsPositivelyOriented := by
  fin_cases i <;> simp [sideEdge, forwardFrom_isPositivelyOriented]
abbrev expI (Y : ComplexMatrix2) : ComplexMatrix2 := ComplexMatrix2.matExp (Complex.I • Y)
abbrev expNegI (Y : ComplexMatrix2) : ComplexMatrix2 := ComplexMatrix2.matExp (-(Complex.I • Y))
def faceTermOf (X U : Edge L k j → ComplexMatrix2) (p : Face L k j) : ℂ :=
  1 - (1 / 2) * ComplexMatrix2.fullTrace (expI (X (sideEdge p 0)) * U (sideEdge p 0) *
    (expI (X (sideEdge p 1)) * U (sideEdge p 1)) *
    ((U (sideEdge p 2))⁻¹ * expNegI (X (sideEdge p 2))) *
    ((U (sideEdge p 3))⁻¹ * expNegI (X (sideEdge p 3))))
theorem inv_expI_mul (Y V : ComplexMatrix2) :
    (ComplexMatrix2.matExp (Complex.I • Y) * V)⁻¹ = V⁻¹ * ComplexMatrix2.matExp (-(Complex.I • Y)) := by apply _root_.YangMills.Construction.Tower.HessianKernel.inv_matExp_smul_mul <;> assumption
theorem complexFaceTerm_expTwist
    (hrev : ∀ b : Edge L k j, b.IsPositivelyOriented → ¬ b.opposite.IsPositivelyOriented)
    (X U : Edge L k j → ComplexMatrix2) (p : Face L k j) :
    complexFaceTerm (expTwist X U) p = faceTermOf X U p := by
  have e : ∀ b : Edge L k j, b.IsPositivelyOriented →
      expTwist X U b = ComplexMatrix2.matExp (Complex.I • X b) * U b := fun b hb => if_pos hb
  have r : ∀ b : Edge L k j, b.IsPositivelyOriented →
      expTwist X U b.opposite = (ComplexMatrix2.matExp (Complex.I • X b) * U b)⁻¹ :=
    fun b hb => if_neg (hrev b hb)
  simp only [complexFaceTerm, faceVariable, linkHolonomy, faceBoundary, List.map_cons,
    List.map_nil, List.prod_cons, List.prod_nil, mul_one]
  rw [e _ (forwardFrom_isPositivelyOriented _ _), e _ (forwardFrom_isPositivelyOriented _ _),
    r _ (forwardFrom_isPositivelyOriented _ _), r _ (forwardFrom_isPositivelyOriented _ _),
    inv_expI_mul, inv_expI_mul]
  simp [faceTermOf, sideEdge, mul_assoc]
theorem faceTermOf_congr {X X' U : Edge L k j → ComplexMatrix2} {p : Face L k j}
    (h : ∀ i, X (sideEdge p i) = X' (sideEdge p i)) : faceTermOf X U p = faceTermOf X' U p := by
  simp only [faceTermOf, h]
theorem faceTermSum_expTwist {Ω : Set (Face L k j)} (hΩ : Ω.Finite)
    (hrev : ∀ b : Edge L k j, b.IsPositivelyOriented → ¬ b.opposite.IsPositivelyOriented)
    (X U : Edge L k j → ComplexMatrix2) :
    faceTermSum Ω (expTwist X U) = ∑ p ∈ hΩ.toFinset, faceTermOf X U p := by
  rw [faceTermSum, finsum_mem_eq_finite_toFinset_sum _ hΩ]
  exact Finset.sum_congr rfl fun p _ => complexFaceTerm_expTwist hrev X U p
theorem differentiable_matExp :
    Differentiable ℂ (fun Z : ComplexMatrix2 => ComplexMatrix2.matExp Z) := fun Z =>
  (NormedSpace.exp_analytic (𝕂 := ℂ) Z).differentiableAt
def extendByZero (F : Finset (Edge L k j)) (Y : F → ComplexMatrix2) (b : Edge L k j) :
    ComplexMatrix2 :=
  open Classical in if h : b ∈ F then Y ⟨b, h⟩ else 0
theorem differentiable_extendByZero (F : Finset (Edge L k j)) (b : Edge L k j) :
    Differentiable ℂ (fun Y : F → ComplexMatrix2 => extendByZero F Y b) := by
  by_cases h : b ∈ F
  · simpa [extendByZero, h] using differentiable_apply (𝕜 := ℂ) (⟨b, h⟩ : F)
  · simp [extendByZero, h]
theorem differentiable_faceTermOf (F : Finset (Edge L k j))
    (U : Edge L k j → ComplexMatrix2) (p : Face L k j) :
    Differentiable ℂ (fun Y : F → ComplexMatrix2 => faceTermOf (extendByZero F Y) U p) := by
  have hl : ∀ i, Differentiable ℂ (fun Y : F → ComplexMatrix2 =>
      expI (extendByZero F Y (sideEdge p i))) := fun i =>
    differentiable_matExp.comp ((differentiable_extendByZero F _).const_smul Complex.I)
  have hi : ∀ i, Differentiable ℂ (fun Y : F → ComplexMatrix2 =>
      expNegI (extendByZero F Y (sideEdge p i))) := fun i =>
    differentiable_matExp.comp ((differentiable_extendByZero F _).const_smul Complex.I).neg
  have htr : Differentiable ℂ (fun X : ComplexMatrix2 => ComplexMatrix2.fullTrace X) :=
    (LinearMap.toContinuousLinearMap (Matrix.traceLinearMap (Fin 2) ℂ ℂ)).differentiable
  have hP := ((((hl 0).mul (differentiable_const (U (sideEdge p 0)))).mul
    ((hl 1).mul (differentiable_const (U (sideEdge p 1))))).mul
    ((differentiable_const (U (sideEdge p 2))⁻¹).mul (hi 2))).mul
    ((differentiable_const (U (sideEdge p 3))⁻¹).mul (hi 3))
  exact (differentiable_const _).sub ((differentiable_const _).mul (htr.comp hP))
def ExpTwistInComplexGroup (L k j : ℕ) : Prop :=
  ∀ U ∈ fieldsValuedIn L k j PeriodicLattice.complexGaugeGroup,
    ∀ X ∈ complexEdgeForms (meshAt L k j), ∀ b : Edge L k j, b.IsPositivelyOriented →
      ComplexMatrix2.matExp (Complex.I • X b) * U b ∈ PeriodicLattice.complexGaugeGroup
theorem expTwist_mem (hl : ExpTwistInComplexGroup L k j)
    (hiff : ∀ b : Edge L k j, b.opposite.IsPositivelyOriented ↔ ¬ b.IsPositivelyOriented)
    {U X : Edge L k j → ComplexMatrix2}
    (hU : U ∈ fieldsValuedIn L k j PeriodicLattice.complexGaugeGroup)
    (hX : X ∈ complexEdgeForms (meshAt L k j)) :
    expTwist X U ∈ fieldsValuedIn L k j PeriodicLattice.complexGaugeGroup := by
  have hdet : ∀ b : Edge L k j, b.IsPositivelyOriented →
      (ComplexMatrix2.matExp (Complex.I • X b) * U b).det = 1 := fun b hb => hl U hU X hX b hb
  refine ⟨fun b => ?_, fun b => ?_⟩
  · by_cases hb : b.IsPositivelyOriented
    · have e : expTwist X U b = ComplexMatrix2.matExp (Complex.I • X b) * U b := if_pos hb
      rw [e]
      exact hdet b hb
    · have e : expTwist X U b =
          (ComplexMatrix2.matExp (Complex.I • X b.opposite) * U b.opposite)⁻¹ := if_neg hb
      rw [e]
      change Matrix.det _ = 1
      rw [Matrix.det_nonsing_inv, hdet _ ((hiff b).2 hb)]
      simp
  · by_cases hb : b.IsPositivelyOriented
    · have h' : ¬ b.opposite.IsPositivelyOriented := fun h => (hiff b).1 h hb
      have e : expTwist X U b = ComplexMatrix2.matExp (Complex.I • X b) * U b := if_pos hb
      have e' : expTwist X U b.opposite =
          (ComplexMatrix2.matExp (Complex.I • X b) * U b)⁻¹ := if_neg h'
      rw [e, e']
    · have h' : b.opposite.IsPositivelyOriented := (hiff b).2 hb
      have e : expTwist X U b =
          (ComplexMatrix2.matExp (Complex.I • X b.opposite) * U b.opposite)⁻¹ := if_neg hb
      have e' : expTwist X U b.opposite =
          ComplexMatrix2.matExp (Complex.I • X b.opposite) * U b.opposite := if_pos h'
      rw [e, e', Matrix.nonsing_inv_nonsing_inv]
      simp [hdet _ h']
theorem exists_presentation (hN : FaceEdgeFinsets.Unbounded.HoldsOnFullSpace L k j)
    (hW : FaceSum.HoldsOnFullSpace L k j) {S : Set (Edge L k j)}
    (hS : S.Finite) (hpos : ∀ b ∈ S, b.IsPositivelyOriented) {U : Edge L k j → ComplexMatrix2}
    (hU : U ∈ fieldsValuedIn L k j PeriodicLattice.complexGaugeGroup) :
    ∃ w : LocalData L k j ℂ,
      IsLocalPresentation PeriodicLattice.complexGaugeGroup
          (fieldsValuedIn L k j PeriodicLattice.complexGaugeGroup)
          (faceTermSum (facesMeeting S)) U w.support w.region w.fn ∧
        holomorphicPresentations L k j OneLoop.pauliBasis
          (Equiv.funUnique (Fin 1) ℂ).symm w.support w.region w.fn := by apply _root_.YangMills.Construction.Tower.HessianKernel.exists_local_presentation <;> assumption
theorem presentation_eventually_eq {h : (Edge L k j → ComplexMatrix2) → ℂ}
    {U B B' : Edge L k j → ComplexMatrix2} (hl : ExpTwistInComplexGroup L k j)
    (hiff : ∀ b : Edge L k j, b.opposite.IsPositivelyOriented ↔ ¬ b.IsPositivelyOriented)
    (hU : U ∈ fieldsValuedIn L k j PeriodicLattice.complexGaugeGroup)
    (hB : B ∈ complexEdgeForms (meshAt L k j))
    (hB' : B' ∈ complexEdgeForms (meshAt L k j))
    (F : Finset (Edge L k j)) (O : Set (F → ComplexMatrix2)) (f : (F → ComplexMatrix2) → ℂ)
    (hw : IsLocalPresentation PeriodicLattice.complexGaugeGroup
      (fieldsValuedIn L k j PeriodicLattice.complexGaugeGroup) h U F O f) :
    ∀ᶠ q : ℂ × ℂ in 𝓝 ((0 : ℂ), (0 : ℂ)),
      f (fun b => ComplexMatrix2.matExp (Complex.I • (q.1 • B + q.2 • B') b) * U b) =
        h (expTwist (q.1 • B + q.2 • B') U) := by
  obtain ⟨hFb, ⟨O', hO', hdom⟩, h0, hval⟩ := hw
  have hcont : Continuous (fun q : ℂ × ℂ => fun b : F =>
      ComplexMatrix2.matExp (Complex.I • (q.1 • B + q.2 • B') b) * U b) := by
    refine continuous_pi fun b => ?_
    refine Continuous.mul (differentiable_matExp.continuous.comp ?_) continuous_const
    change Continuous fun q : ℂ × ℂ => Complex.I • (q.1 • B b + q.2 • B' b)
    fun_prop
  have h00 : (fun b : F => ComplexMatrix2.matExp (Complex.I •
      (((0 : ℂ), (0 : ℂ)).1 • B + ((0 : ℂ), (0 : ℂ)).2 • B') b) * U b) ∈ O' := by
    have : (fun b : F => ComplexMatrix2.matExp (Complex.I •
        (((0 : ℂ), (0 : ℂ)).1 • B + ((0 : ℂ), (0 : ℂ)).2 • B') b) * U b) =
        restrictToEdges F U := by
      funext b
      simp [restrictToEdges, NormedSpace.exp_zero]
    rw [this]
    rw [hdom] at h0
    exact h0.1
  filter_upwards [hcont.continuousAt.eventually (hO'.mem_nhds h00)] with q hq
  have hX : q.1 • B + q.2 • B' ∈ complexEdgeForms (meshAt L k j) :=
    (complexEdgeForms _).add_mem ((complexEdgeForms _).smul_mem _ hB)
      ((complexEdgeForms _).smul_mem _ hB')
  have hU' := expTwist_mem hl hiff hU hX
  have hbv : restrictToEdges F (expTwist (q.1 • B + q.2 • B') U) =
      fun b : F => ComplexMatrix2.matExp (Complex.I • (q.1 • B + q.2 • B') b) * U b :=
    funext fun b => if_pos (hFb.2 b b.2)
  have hd : restrictToEdges F (expTwist (q.1 • B + q.2 • B') U) ∈ O := by
    rw [hdom]
    exact ⟨hbv ▸ hq, fun b => hU'.1 b⟩
  rw [hval _ hU' hd, hbv]
abbrev presentedValue (h : (Edge L k j → ComplexMatrix2) → ℂ) (U X : Edge L k j → ComplexMatrix2) :
    ℂ :=
  valueViaPresentation PeriodicLattice.complexGaugeGroup
    (fieldsValuedIn L k j PeriodicLattice.complexGaugeGroup)
    (holomorphicPresentations L k j OneLoop.pauliBasis (Equiv.funUnique (Fin 1) ℂ).symm) h U X
theorem presentedValue_eventually_eq (hN : FaceEdgeFinsets.Unbounded.HoldsOnFullSpace L k j)
    (hW : FaceSum.HoldsOnFullSpace L k j) (hl : ExpTwistInComplexGroup L k j)
    (hiff : ∀ b : Edge L k j, b.opposite.IsPositivelyOriented ↔ ¬ b.IsPositivelyOriented)
    {S : Set (Edge L k j)} (hS : S.Finite) (hpos : ∀ b ∈ S, b.IsPositivelyOriented)
    {U B B' : Edge L k j → ComplexMatrix2}
    (hU : U ∈ fieldsValuedIn L k j PeriodicLattice.complexGaugeGroup)
    (hB : B ∈ complexEdgeForms (meshAt L k j))
    (hB' : B' ∈ complexEdgeForms (meshAt L k j)) :
    ∀ᶠ q : ℂ × ℂ in 𝓝 ((0 : ℂ), (0 : ℂ)),
      presentedValue (faceTermSum (facesMeeting S)) U (q.1 • B + q.2 • B') =
        faceTermSum (facesMeeting S) (expTwist (q.1 • B + q.2 • B') U) := by
  have hspec := Classical.epsilon_spec (exists_presentation hN hW hS hpos hU)
  exact presentation_eventually_eq hl hiff hU hB hB' _ _ _ hspec.1
theorem exists_const_eventually_eq (hN : FaceEdgeFinsets.Unbounded.HoldsOnFullSpace L k j)
    (hW : FaceSum.HoldsOnFullSpace L k j) (hl : ExpTwistInComplexGroup L k j)
    (hiff : ∀ b : Edge L k j, b.opposite.IsPositivelyOriented ↔ ¬ b.IsPositivelyOriented)
    {S : Set (Edge L k j)} (hS : S.Finite) (hpos : ∀ b ∈ S, b.IsPositivelyOriented)
    {Ω : Set (Face L k j)} (hΩ : Ω.Finite) (hsub : facesMeeting S ⊆ Ω)
    {U B B' : Edge L k j → ComplexMatrix2}
    (hU : U ∈ fieldsValuedIn L k j PeriodicLattice.complexGaugeGroup)
    (hB : B ∈ complexEdgeForms (meshAt L k j))
    (hB' : B' ∈ complexEdgeForms (meshAt L k j))
    (hzB : ∀ b : Edge L k j, b.IsPositivelyOriented → b ∉ S → B b = 0)
    (hzB' : ∀ b : Edge L k j, b.IsPositivelyOriented → b ∉ S → B' b = 0) :
    ∃ c : ℂ, ∀ᶠ q : ℂ × ℂ in 𝓝 ((0 : ℂ), (0 : ℂ)),
      actionAtExpTwist Ω U (q.1 • B + q.2 • B') =
        presentedValue (faceTermSum (facesMeeting S)) U (q.1 • B + q.2 • B') + c := by
  classical
  have hrev : ∀ b : Edge L k j, b.IsPositivelyOriented → ¬ b.opposite.IsPositivelyOriented :=
    fun b hb h => (hiff b).1 h hb
  have hP := (hN.2.1 S hS hpos).1
  refine ⟨∑ p ∈ hΩ.toFinset \ hP.toFinset, faceTermOf 0 U p, ?_⟩
  filter_upwards [presentedValue_eventually_eq hN hW hl hiff hS hpos hU hB hB'] with q hq'
  have hsubF : hP.toFinset ⊆ hΩ.toFinset := fun p hp =>
    hΩ.mem_toFinset.2 (hsub (hP.mem_toFinset.1 hp))
  have key : ∑ p ∈ hΩ.toFinset \ hP.toFinset, faceTermOf (q.1 • B + q.2 • B') U p =
      ∑ p ∈ hΩ.toFinset \ hP.toFinset, faceTermOf 0 U p := by
    refine Finset.sum_congr rfl fun p hp => faceTermOf_congr fun i => ?_
    have hnot : sideEdge p i ∉ S := fun hi =>
      (Finset.mem_sdiff.1 hp).2 (hP.mem_toFinset.2 ⟨_, hi, sideEdge_mem p i⟩)
    have h1 := hzB _ (sideEdge_isPositivelyOriented p i) hnot
    have h2 := hzB' _ (sideEdge_isPositivelyOriented p i) hnot
    change q.1 • B (sideEdge p i) + q.2 • B' (sideEdge p i) = 0
    rw [h1, h2, smul_zero, smul_zero, add_zero]
  rw [hq', actionAtExpTwist, faceTermSum_expTwist hΩ hrev, faceTermSum_expTwist hP hrev,
    ← Finset.sum_sdiff hsubF, key, add_comm]
theorem mixed_deriv_congr {φ ψ : ℂ × ℂ → ℂ} (h : ∀ᶠ q in 𝓝 ((0 : ℂ), (0 : ℂ)), φ q = ψ q) :
    deriv (fun s : ℂ => deriv (fun t : ℂ => φ (s, t)) 0) 0 =
      deriv (fun s : ℂ => deriv (fun t : ℂ => ψ (s, t)) 0) 0 := by apply _root_.YangMills.Construction.Tower.HessianKernel.mixedDeriv_congr_nhds <;> assumption
theorem eq_zero_of_not_mem {B : Edge L k j → ComplexMatrix2} {S : Set (Edge L k j)}
    (hS : edgeSupport B ⊆ S) (b : Edge L k j) (hb : b.IsPositivelyOriented) (hn : b ∉ S) :
    B b = 0 := by
  by_contra h
  exact hn (hS ⟨hb, h⟩)
theorem facesMeeting_mono {S S' : Set (Edge L k j)} (h : S ⊆ S') :
    facesMeeting S ⊆ facesMeeting S' := fun _ ⟨b, hb, hp⟩ => ⟨b, h hb, hp⟩
theorem derivsMatchFaceSum (hN : FaceEdgeFinsets.Unbounded.HoldsOnFullSpace L k j)
    (hW : FaceSum.HoldsOnFullSpace L k j) (hl : ExpTwistInComplexGroup L k j)
    (hiff : ∀ b : Edge L k j, b.opposite.IsPositivelyOriented ↔ ¬ b.IsPositivelyOriented)
    {Ω : Set (Face L k j)} (hΩ : Ω.Finite) {U : Edge L k j → ComplexMatrix2}
    (hU : U ∈ fieldsValuedIn L k j PeriodicLattice.complexGaugeGroup) :
    DerivsMatchFaceSum Ω U := by
  intro B B' hB hB' hfB hfB' hsub
  have hposB : ∀ b ∈ edgeSupport B, b.IsPositivelyOriented := fun b h => h.1
  have hposB' : ∀ b ∈ edgeSupport B', b.IsPositivelyOriented := fun b h => h.1
  constructor
  · obtain ⟨c, hc⟩ := exists_const_eventually_eq hN hW hl hiff hfB hposB hΩ
      ((facesMeeting_mono subset_union_left).trans hsub) hU hB (complexEdgeForms _).zero_mem
      (eq_zero_of_not_mem subset_rfl) (fun _ _ _ => rfl)
    have ht : Tendsto (fun t : ℂ => (t, (0 : ℂ))) (𝓝 0) (𝓝 ((0 : ℂ), (0 : ℂ))) :=
      (continuous_id.prodMk continuous_const).tendsto' _ _ rfl
    have h4 : (fun t : ℂ => actionAtExpTwist Ω U (t • B)) =ᶠ[𝓝 0]
        fun t : ℂ => presentedValue (faceTermSum (facesMeeting (edgeSupport B))) U (t • B) + c := by
      filter_upwards [ht.eventually hc] with t h
      simpa using h
    change deriv (fun t : ℂ => presentedValue (faceTermSum (facesMeeting (edgeSupport B))) U
        (t • B)) 0 = deriv (fun t : ℂ => actionAtExpTwist Ω U (t • B)) 0
    rw [h4.deriv_eq, deriv_add_const]
  · obtain ⟨c, hc⟩ := exists_const_eventually_eq hN hW hl hiff (hfB.union hfB')
      (fun b h => h.elim (hposB b) (hposB' b)) hΩ hsub hU hB hB'
      (eq_zero_of_not_mem subset_union_left) (eq_zero_of_not_mem subset_union_right)
    have h := mixed_deriv_congr hc
    simp only [deriv_add_const] at h
    exact h.symm
theorem exists_entireRepresentation (hN : FaceEdgeFinsets.Unbounded.HoldsOnFullSpace L k j)
    (hrev : ∀ b : Edge L k j, b.IsPositivelyOriented → ¬ b.opposite.IsPositivelyOriented)
    {Ω : Set (Face L k j)} (hΩ : Ω.Finite) (hne : Ω.Nonempty)
    (U : Edge L k j → ComplexMatrix2) :
    ∃ (F : Finset (Edge L k j)) (Φ : (F → ComplexMatrix2) → ℂ),
      IsEntireRepresentation Ω U F Φ := by
  classical
  have hmem : ∀ b, b ∈ hΩ.toFinset.biUnion (fun p => (faceEdges p).toFinset) ↔
      ∃ p ∈ Ω, b ∈ faceEdges p := fun b => by simp
  refine ⟨hΩ.toFinset.biUnion fun p => (faceEdges p).toFinset,
    fun Y => ∑ p ∈ hΩ.toFinset, faceTermOf (extendByZero _ Y) U p, ⟨?_, ?_⟩, hmem, ?_, ?_⟩
  · obtain ⟨p, hp⟩ := hne
    exact ⟨sideEdge p 0, (hmem _).2 ⟨p, hp, sideEdge_mem p 0⟩⟩
  · intro b hb
    obtain ⟨p, -, hbp⟩ := (hmem b).1 hb
    exact hN.1.2 p b hbp
  · exact Differentiable.fun_sum fun p _ => differentiable_faceTermOf _ U p
  · intro C _
    rw [actionAtExpTwist, faceTermSum_expTwist hΩ hrev]
    refine Finset.sum_congr rfl fun p hp => faceTermOf_congr fun i => ?_
    exact dif_pos ((hmem _).2 ⟨p, hΩ.mem_toFinset.1 hp, sideEdge_mem p i⟩)
theorem onLevel (hN : FaceEdgeFinsets.Unbounded.HoldsOnFullSpace L k j)
    (hW : FaceSum.HoldsOnFullSpace L k j) (hl : ExpTwistInComplexGroup L k j)
    (hL : Conventions.IsAdmissibleBlockingFactor L) : OnLevel L k j := by
  intro U hU Ω hΩ hne
  have hiff : ∀ b : Edge L k j, b.opposite.IsPositivelyOriented ↔ ¬ b.IsPositivelyOriented :=
    opposite_isPositivelyOriented_iff (meshAt_pos hL)
  exact ⟨derivsMatchFaceSum hN hW hl hiff hΩ hU,
    exists_entireRepresentation hN (fun b hb h => (hiff b).1 h hb) hΩ hne U⟩
theorem claim_holds (hN : FaceEdgeFinsets.FacesAndEdgesFinite)
    (hW : FaceSum.holomorphy_statement)
    (hC : LeftChartFields.Claim) : Claim := by
  intro L k j hL hj
  refine onLevel (hN L hL k j hj).2 (hW L hL k j hj).2 ?_ hL
  intro U hU X hX b hb
  have h := (((hC.2.2 L k j hL hj).2.1).1.2 U hU X hX ⟨b, hb⟩).1 1
  simpa [LeftChartFields.leftExpMul, LeftChartFields.LatticeData.onPositive,
    LeftChartFields.fullData] using h
end YangMills.Construction.Tower.FullSpace.ActionDerivsOnFiniteFaces
end
