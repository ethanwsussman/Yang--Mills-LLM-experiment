import YangMills.Construction.Towers.ComplexFormsUnderTheMapsOfOneStepOnASide
import YangMills.Construction.Towers.ComplexFormsUnderTheMapsOfOneStepOnTheWhole
import YangMills.Construction.Towers.ContourDriftIsLocalWithACounterpartProof
import YangMills.Construction.Towers.CrossingAverageOfATowerIsAMapOfPeriodicFunctions
import YangMills.Construction.Towers.QuotientOfATowerCarriesSets
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.Tower.UnitScale.CrossingSmoothingPeriodic
open YangMills.Construction.Tower.UnitScale.OneStepChart
open YangMills.Construction.InfiniteLattice (AmbientSpace)
section Translations
variable {a a' : ℝ}
theorem forwardFrom_add (x v : InfiniteLattice.LatticePoint a) (μ : Fin 4) :
    InfiniteLattice.Link.forwardFrom (x + v) μ =
      linkTranslate (InfiniteLattice.Link.forwardFrom x μ) v := by
  refine InfiniteLattice.Link.ext rfl ?_
  show x + v + InfiniteLattice.axisStep a μ = x + InfiniteLattice.axisStep a μ + v
  abel
theorem backwardLink_add (x v : InfiniteLattice.LatticePoint a) (μ : Fin 4) :
    Tower.FullSpace.backwardLink (x + v) μ =
      linkTranslate (Tower.FullSpace.backwardLink x μ) v := by
  refine InfiniteLattice.Link.ext rfl ?_
  show x + v - InfiniteLattice.axisStep a μ = x - InfiniteLattice.axisStep a μ + v
  abel
theorem forwardSteps_add (v : InfiniteLattice.LatticePoint a) (μ : Fin 4) (n : ℕ) :
    ∀ x, Tower.FullSpace.forwardSteps (x + v) μ n =
      (Tower.FullSpace.forwardSteps x μ n).map fun b => linkTranslate b v := by
  induction n with
  | zero => intro x; rfl
  | succ n ih =>
    intro x
    simp only [Tower.FullSpace.forwardSteps, List.map_cons]
    rw [forwardFrom_add, ← ih, add_right_comm]
theorem backwardSteps_add (v : InfiniteLattice.LatticePoint a) (μ : Fin 4) (n : ℕ) :
    ∀ x, Tower.FullSpace.backwardSteps (x + v) μ n =
      (Tower.FullSpace.backwardSteps x μ n).map fun b => linkTranslate b v := by
  induction n with
  | zero => intro x; rfl
  | succ n ih =>
    intro x
    simp only [Tower.FullSpace.backwardSteps, List.map_cons]
    rw [backwardLink_add, ← ih, add_sub_right_comm]
theorem signedSteps_add (x v : InfiniteLattice.LatticePoint a) (μ : Fin 4) (n : ℤ) :
    Tower.FullSpace.signedSteps (x + v) μ n =
      (Tower.FullSpace.signedSteps x μ n).map fun b => linkTranslate b v := by
  unfold Tower.FullSpace.signedSteps
  split_ifs
  · exact forwardSteps_add v μ _ x
  · exact backwardSteps_add v μ _ x
theorem exists_choose_congr {α : Type*} {p q : α → Prop} (hp : ∃ x, p x) (hq : ∃ x, q x)
    (h : p = q) : hp.choose = hq.choose := by
  subst h
  rfl
theorem axisPath_add (x x' v : InfiniteLattice.LatticePoint a) :
    Tower.FullSpace.axisPath (x + v) (x' + v) =
      (Tower.FullSpace.axisPath x x').map fun b => linkTranslate b v := by
  have e : (fun q : Fin 4 × ℤ => Tower.FullSpace.IsAxisDisplacement (x + v) (x' + v) q.1 q.2) =
      fun q => Tower.FullSpace.IsAxisDisplacement x x' q.1 q.2 := by
    funext q
    simp only [Tower.FullSpace.IsAxisDisplacement, add_sub_add_right_eq_sub]
  unfold Tower.FullSpace.axisPath
  by_cases h : ∃ q : Fin 4 × ℤ, Tower.FullSpace.IsAxisDisplacement x x' q.1 q.2
  · have h' : ∃ q : Fin 4 × ℤ, Tower.FullSpace.IsAxisDisplacement (x + v) (x' + v) q.1 q.2 := by
      obtain ⟨q, hq⟩ := h
      exact ⟨q, congrFun e.symm q ▸ hq⟩
    rw [dif_pos h, dif_pos h', exists_choose_congr h' h e]
    exact signedSteps_add x v _ _
  · have h' : ¬∃ q : Fin 4 × ℤ, Tower.FullSpace.IsAxisDisplacement (x + v) (x' + v) q.1 q.2 := by
      rintro ⟨q, hq⟩
      exact h ⟨q, congrFun e q ▸ hq⟩
    rw [dif_neg h, dif_neg h']
    rfl
theorem crossingPath_add (c : InfiniteLattice.Link a) (x v' : InfiniteLattice.LatticePoint a')
    (v : InfiniteLattice.LatticePoint a) :
    Tower.FullSpace.crossingPath (linkTranslate c v) (x + v') =
      (Tower.FullSpace.crossingPath c x).map fun b => linkTranslate b v' := by
  have e : Tower.FullSpace.shifted (linkTranslate c v) (x + v') =
      Tower.FullSpace.shifted c x + v' := by
    have e' : (linkTranslate c v).terminal - (linkTranslate c v).initial =
        c.terminal - c.initial :=
      add_sub_add_right_eq_sub _ _ _
    unfold Tower.FullSpace.shifted
    rw [e', add_right_comm]
  unfold Tower.FullSpace.crossingPath
  rw [e, axisPath_add]
theorem mem_cubeVertices_add_iff (L : ℕ) (y v : InfiniteLattice.LatticePoint a)
    (v' x : InfiniteLattice.LatticePoint a') (h : (v : AmbientSpace) = v') :
    x + v' ∈ Tower.FullSpace.cubeVertices L a' (y + v) ↔
      x ∈ Tower.FullSpace.cubeVertices L a' y := by
  constructor
  · rintro ⟨ν, hν, e⟩
    refine ⟨ν, hν, add_right_cancel (b := (v' : AmbientSpace)) ?_⟩
    have e' : (x : AmbientSpace) + (v' : AmbientSpace) =
        (y : AmbientSpace) + (v : AmbientSpace) + ∑ μ, Pi.single μ ((ν μ : ℝ) * a') := e
    rw [e', h]
    abel
  · rintro ⟨ν, hν, e⟩
    refine ⟨ν, hν, ?_⟩
    have e' : (x : AmbientSpace) = (y : AmbientSpace) + ∑ μ, Pi.single μ ((ν μ : ℝ) * a') := e
    show (x : AmbientSpace) + (v' : AmbientSpace) = (y : AmbientSpace) + (v : AmbientSpace) + _
    rw [e', h]
    abel
theorem edgeFormPathSum_map (f : InfiniteLattice.Link a → Matrices.ComplexMatrix2)
    (T : InfiniteLattice.Link a → InfiniteLattice.Link a)
    (Γ : List (InfiniteLattice.Link a)) :
    Tower.FullSpace.edgeFormPathSum (fun b => f (T b)) Γ =
      Tower.FullSpace.edgeFormPathSum f (Γ.map T) := by
  simp only [Tower.FullSpace.edgeFormPathSum, Tower.FullSpace.sumAlong, List.map_map,
    Function.comp_def]
theorem crossingSmoothing_shift (L : ℕ) (v : InfiniteLattice.LatticePoint a)
    (v' : InfiniteLattice.LatticePoint a') (h : (v : AmbientSpace) = v')
    (f : InfiniteLattice.Link a' → Matrices.ComplexMatrix2) (c : InfiniteLattice.Link a) :
    Tower.FullSpace.crossingSmoothing L (a := a) (fun b => f (linkTranslate b v')) c =
      Tower.FullSpace.crossingSmoothing L f (linkTranslate c v) := by
  unfold Tower.FullSpace.crossingSmoothing
  congr 1
  refine finsum_mem_eq_of_bijOn (Equiv.addRight v')
    ((Equiv.addRight v').bijOn fun x => mem_cubeVertices_add_iff L c.initial v v' x h) fun x _ => ?_
  show _ = Tower.FullSpace.edgeFormPathSum f (Tower.FullSpace.crossingPath (linkTranslate c v) (x + v'))
  rw [crossingPath_add, edgeFormPathSum_map]
theorem integerPoint_coe {L : ℕ} (hL : 0 < L) {k j : ℕ} (hj : j ≤ k) (z : Fin 4 → ℤ) :
    ((integerPoint (Tower.meshAt L k j) z : InfiniteLattice.LatticePoint (Tower.meshAt L k j)) :
        AmbientSpace) = fun μ => (z μ : ℝ) := by
  have hL' : (L : ℝ) ≠ 0 := by positivity
  have hex : ∃ x : InfiniteLattice.LatticePoint (Tower.meshAt L k j),
      (x : AmbientSpace) = fun μ => (z μ : ℝ) := by
    refine ⟨⟨fun μ => (z μ : ℝ), fun μ => z μ * (L : ℤ) ^ (k - j), fun μ => ?_⟩, rfl⟩
    have e : (L : ℝ) ^ (k - j) * Tower.meshAt L k j = 1 := by
      unfold Tower.meshAt
      rw [← zpow_natCast, ← zpow_add₀ hL', Nat.cast_sub hj]
      simp
    push_cast
    rw [mul_assoc, e, mul_one]
  exact Classical.epsilon_spec hex
end Translations
section EvaluationMaps
variable {a' : ℝ}
def ReadsFinitelyManyEdges (F : (InfiniteLattice.Link a' → Matrices.ComplexMatrix2) → Matrices.ComplexMatrix2) :
    Prop :=
  ∃ K : Tower.FullSpace.PositiveEdge a' → ℝ, {p | K p ≠ 0}.Finite ∧
    ∀ f ∈ Tower.FullSpace.complexEdgeForms a',
      F f = ∑ᶠ p, K p • Tower.FullSpace.restrictToPositiveEdges f p
theorem smul_support_finite {K : Tower.FullSpace.PositiveEdge a' → ℝ} (hK : {p | K p ≠ 0}.Finite)
    (g : Tower.FullSpace.PositiveEdge a' → Matrices.ComplexMatrix2) :
    (Function.support fun p => K p • g p).Finite :=
  hK.subset fun p hp h => hp (by simp [h])
theorem readsFinitelyManyEdges_zero : ReadsFinitelyManyEdges (a' := a') fun _ => 0 :=
  ⟨0, by simp, by simp⟩
theorem readsFinitelyManyEdges_add
    {F G : (InfiniteLattice.Link a' → Matrices.ComplexMatrix2) → Matrices.ComplexMatrix2}
    (hF : ReadsFinitelyManyEdges F) (hG : ReadsFinitelyManyEdges G) :
    ReadsFinitelyManyEdges fun f => F f + G f := by
  obtain ⟨K, hK, eK⟩ := hF
  obtain ⟨K', hK', eK'⟩ := hG
  refine ⟨K + K', (hK.union hK').subset fun p hp => ?_, fun f hf => ?_⟩
  · by_contra h
    have h1 : K p = 0 := by_contra fun e => h (Or.inl e)
    have h2 : K' p = 0 := by_contra fun e => h (Or.inr e)
    exact hp (by simp [h1, h2])
  · show F f + G f = _
    rw [eK f hf, eK' f hf,
      ← finsum_add_distrib (smul_support_finite hK _) (smul_support_finite hK' _)]
    simp only [Pi.add_apply, add_smul]
theorem readsFinitelyManyEdges_smul
    {F : (InfiniteLattice.Link a' → Matrices.ComplexMatrix2) → Matrices.ComplexMatrix2} (r : ℝ)
    (hF : ReadsFinitelyManyEdges F) : ReadsFinitelyManyEdges fun f => r • F f := by
  obtain ⟨K, hK, eK⟩ := hF
  refine ⟨r • K, hK.subset fun p hp h => hp (by simp [h]), fun f hf => ?_⟩
  show r • F f = _
  rw [eK f hf, smul_finsum' r (smul_support_finite hK _)]
  simp only [Pi.smul_apply, smul_eq_mul, mul_smul]
theorem readsFinitelyManyEdges_positive (p : Tower.FullSpace.PositiveEdge a') :
    ReadsFinitelyManyEdges fun f => f p.1 := by
  classical
  refine ⟨Pi.single p 1, (finite_singleton p).subset fun q hq => ?_, fun f _ => ?_⟩
  · by_contra h
    exact hq (Pi.single_eq_of_ne h 1)
  · rw [finsum_eq_single _ p fun q hq => by simp [Pi.single_eq_of_ne hq]]
    simp [Tower.FullSpace.restrictToPositiveEdges]
theorem positive_or_opposite_positive (b : InfiniteLattice.Link a') :
    b.IsPositivelyOriented ∨ b.opposite.IsPositivelyOriented := by apply _root_.YangMills.Construction.InfiniteLattice.GibbsForms.isPositivelyOriented_or_opposite <;> assumption
theorem readsFinitelyManyEdges_link (b : InfiniteLattice.Link a') :
    ReadsFinitelyManyEdges fun f => f b := by
  by_cases hb : b.IsPositivelyOriented
  · exact readsFinitelyManyEdges_positive ⟨b, hb⟩
  · obtain ⟨K, hK, e⟩ := readsFinitelyManyEdges_smul (-1)
      (readsFinitelyManyEdges_positive ⟨b.opposite, (positive_or_opposite_positive b).resolve_left hb⟩)
    refine ⟨K, hK, fun f hf => ?_⟩
    rw [← e f hf]
    show f b = (-1 : ℝ) • f b.opposite
    rw [hf.2 b]
    simp
theorem readsFinitelyManyEdges_pathSum (Γ : List (InfiniteLattice.Link a')) :
    ReadsFinitelyManyEdges fun f => Tower.FullSpace.edgeFormPathSum f Γ := by
  induction Γ with
  | nil => exact readsFinitelyManyEdges_zero
  | cons b Γ ih => exact readsFinitelyManyEdges_add (readsFinitelyManyEdges_link b) ih
theorem readsFinitelyManyEdges_finsum_mem {ι : Type*} {s : Set ι} (hs : s.Finite)
    {G : ι → (InfiniteLattice.Link a' → Matrices.ComplexMatrix2) → Matrices.ComplexMatrix2}
    (hG : ∀ x ∈ s, ReadsFinitelyManyEdges (G x)) :
    ReadsFinitelyManyEdges fun f => ∑ᶠ x ∈ s, G x f := by
  induction s, hs using Set.Finite.induction_on with
  | empty => simpa using readsFinitelyManyEdges_zero
  | @insert x s hx hs ih =>
    have e : (fun f => ∑ᶠ y ∈ insert x s, G y f) = fun f => G x f + ∑ᶠ y ∈ s, G y f :=
      funext fun f => finsum_mem_insert _ hx hs
    rw [e]
    exact readsFinitelyManyEdges_add (hG x (mem_insert _ _))
      (ih fun y hy => hG y (mem_insert_of_mem _ hy))
theorem cubeVertices_finite {a : ℝ} (L : ℕ) (y : InfiniteLattice.LatticePoint a) :
    (Tower.FullSpace.cubeVertices L a' y).Finite := by
  have hbox : {ν : Fin 4 → ℤ | ∀ μ, 2 * |ν μ| ≤ (L : ℤ) ^ 1 - 1}.Finite :=
    (Set.Finite.pi' fun _ : Fin 4 => Set.finite_Icc (-(L : ℤ)) L).subset fun ν h μ => by
      have h1 := h μ
      rw [pow_one] at h1
      exact mem_Icc.2 (abs_le.1 (by linarith [abs_nonneg (ν μ)]))
  have himg := hbox.image fun ν => (y : AmbientSpace) + ∑ μ, Pi.single μ ((ν μ : ℝ) * a')
  refine (himg.preimage Subtype.val_injective.injOn).subset ?_
  rintro x ⟨ν, h, e⟩
  exact ⟨ν, h, e.symm⟩
theorem readsFinitelyManyEdges_crossingSmoothing {a : ℝ} (L : ℕ) (c : InfiniteLattice.Link a) :
    ReadsFinitelyManyEdges fun f : InfiniteLattice.Link a' → Matrices.ComplexMatrix2 =>
      Tower.FullSpace.crossingSmoothing L f c := by
  obtain ⟨K, hK, e⟩ := readsFinitelyManyEdges_smul ((L : ℝ) ^ (-4 : ℤ))
    (readsFinitelyManyEdges_finsum_mem (cubeVertices_finite (a' := a') L c.initial)
      fun x _ => readsFinitelyManyEdges_pathSum (Tower.FullSpace.crossingPath c x))
  refine ⟨K, hK, fun f hf => ?_⟩
  rw [← e f hf]
  show PeriodicLattice.inverseFourthPowerWeight L • _ = _
  unfold PeriodicLattice.inverseFourthPowerWeight
  exact Complex.coe_smul _ _
end EvaluationMaps
section Periodic
variable {L m k j : ℕ}
theorem crossingSmoothing_extend_of_positive (hS : Tower.ProjectionCarriesSetsStatement)
    (hB : Tower.FullSpace.CubesCorridorsPivotEdgesAndPaths)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hm : 0 < m) (hj : j < k)
    (f : Tower.Edge L m k j → Matrices.ComplexMatrix2)
    {c : Tower.FullSpace.Edge L k (j + 1)} (hc : c.IsPositivelyOriented) :
    Tower.FullSpace.crossingSmoothing L (fun b => f (Tower.FullSpace.projEdge L m k j b)) c =
      Tower.crossingSmoothing L m k j f (Tower.FullSpace.projEdge L m k (j + 1) c) := by
  have hL0 : 0 < L := by have := hL.2; omega
  have hk : 1 ≤ k := by omega
  have Q : Tower.FullSpace.ProjPreservesSets L m k j c := (hS L hL0 hL k hk m hm).2 j hj c hc
  have hpart : Tower.FullSpace.CubesOfOrderPartition L k (j + 1) 1 :=
    (hB L hL k (j + 1) 1 hk (by omega) hj le_rfl (by omega)).1
  have hbij : BijOn (Tower.FullSpace.projVertex L m k j)
      (Tower.FullSpace.cubeVertices L (Tower.meshAt L k j) c.initial)
      (PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k j)
        (Tower.FullSpace.projEdge L m k (j + 1) c).source) := by
    refine ⟨fun x hx => ?_, fun x hx x' hx' h => ?_, fun x' hx' => ?_⟩
    · show ((Tower.FullSpace.projVertex L m k j x : Tower.Vertex L m k j) :
          PeriodicLattice.FourTorus L m) ∈
            PeriodicLattice.unitBlock (Tower.FullSpace.projEdge L m k (j + 1) c).source
      rw [← Q.cube_initial]
      exact ⟨_, hx, rfl⟩
    · exact Subtype.ext (Q.injOn_doubleCube (Or.inl hx) (Or.inl hx') (congrArg Subtype.val h))
    · have hx'' : (x' : PeriodicLattice.FourTorus L m) ∈
          PeriodicLattice.unitBlock (Tower.FullSpace.projEdge L m k (j + 1) c).source := hx'
      rw [← Q.cube_initial] at hx''
      obtain ⟨p, hp, he⟩ := hx''
      have hps : p ∈ (InfiniteLattice.latticeSubgroup (Tower.meshAt L k j) : Set AmbientSpace) := by
        have hu := hpart.iUnion_cube
        have : p ∈ ⋃ y : Tower.FullSpace.Vertex L k (j + 1),
            Tower.FullSpace.cubeOfOrder L (Tower.meshAt L k j) 1 y :=
          mem_iUnion.2 ⟨c.initial, hp⟩
        exact hu ▸ this
      exact ⟨⟨p, hps⟩, hp, Subtype.ext he⟩
  unfold Tower.FullSpace.crossingSmoothing Tower.crossingSmoothing
  congr 1
  refine finsum_mem_eq_of_bijOn _ hbij fun x hx => ?_
  have hc' := Q.crossingPath_eq x hx
  rw [← hc']
  simp only [Tower.FullSpace.edgeFormPathSum, Tower.edgeFormPathSum, Tower.FullSpace.sumAlong,
    PeriodicLattice.bondFormSumAlong, Tower.FullSpace.projPath, List.map_map, Function.comp_def]
theorem extend_mem_complexEdgeForms (hQ : Tower.EdgeProjectionProperties)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hm : 0 < m) (hj : j ≤ k)
    {f : Tower.Edge L m k j → Matrices.ComplexMatrix2} (hf : f ∈ Tower.complexEdgeForms L m k j) :
    (fun b => f (Tower.FullSpace.projEdge L m k j b)) ∈
      Tower.FullSpace.complexEdgeForms (Tower.meshAt L k j) := by apply _root_.YangMills.Construction.LocalKernels.ContourDriftLocality.comp_projEdge_mem_complexEdgeForms <;> assumption
theorem crossingSmoothing_extend (hS : Tower.ProjectionCarriesSetsStatement)
    (hQ : Tower.EdgeProjectionProperties)
    (hB : Tower.FullSpace.CubesCorridorsPivotEdgesAndPaths)
    (hW : Tower.FullSpace.OneStepComplexForms.OneStepClaim)
    (hT : Tower.PeriodicCoarseningStep.Holds)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hm : 0 < m) (hj : j < k)
    {f : Tower.Edge L m k j → Matrices.ComplexMatrix2}
    (hf : f ∈ Tower.complexEdgeForms L m k j) (c : Tower.FullSpace.Edge L k (j + 1)) :
    Tower.FullSpace.crossingSmoothing L (fun b => f (Tower.FullSpace.projEdge L m k j b)) c =
      Tower.crossingSmoothing L m k j f (Tower.FullSpace.projEdge L m k (j + 1) c) := by
  by_cases hc : c.IsPositivelyOriented
  · exact crossingSmoothing_extend_of_positive hS hB hL hm hj f hc
  · have hr := (positive_or_opposite_positive c).resolve_left hc
    have e := crossingSmoothing_extend_of_positive hS hB hL hm hj f hr
    have hw : Tower.FullSpace.crossingSmoothing L (a := Tower.meshAt L k (j + 1))
        (fun b => f (Tower.FullSpace.projEdge L m k j b)) ∈
        Tower.FullSpace.complexEdgeForms (Tower.meshAt L k (j + 1)) :=
      (hW L hL k j hj).crossingSmoothing_mapsTo (extend_mem_complexEdgeForms hQ hL hm hj.le hf)
    have hs : Tower.crossingSmoothing L m k j f ∈ Tower.complexEdgeForms L m k (j + 1) :=
      (hT L hL m k j hm hj).crossingSmoothing_mapsTo hf
    have h2 := hs.2 (Tower.FullSpace.projEdge L m k (j + 1) c)
    rw [((hQ L m k (j + 1) hL hm hj).1 c).2.2.2] at h2
    rw [hw.2 c, h2] at e
    exact neg_injective e
end Periodic
theorem crossingSmoothingIsPeriodicOperator_holds (hS : Tower.ProjectionCarriesSetsStatement)
    (hQ : Tower.EdgeProjectionProperties)
    (hB : Tower.FullSpace.CubesCorridorsPivotEdgesAndPaths)
    (hW : Tower.FullSpace.OneStepComplexForms.OneStepClaim)
    (hT : Tower.PeriodicCoarseningStep.Holds) : CrossingSmoothingIsPeriodicOperator := by
  intro L hL m k j hm hj
  have hL0 : 0 < L := by have := hL.2; omega
  refine ⟨fun f hf => (hW L hL k j hj).crossingSmoothing_mapsTo hf,
    fun f hf => (hT L hL m k j hm hj).crossingSmoothing_mapsTo hf, fun f hf => ?_,
    fun z f _ => ?_, ?_⟩
  · funext c
    exact crossingSmoothing_extend hS hQ hB hW hT hL hm hj hf c
  · funext c
    refine crossingSmoothing_shift L (integerPoint _ (-z)) (integerPoint _ (-z)) ?_ f c
    rw [integerPoint_coe hL0 hj, integerPoint_coe hL0 hj.le]
  · choose K hK e using fun q : Tower.FullSpace.PositiveEdge (Tower.meshAt L k (j + 1)) =>
      readsFinitelyManyEdges_crossingSmoothing (a' := Tower.meshAt L k j) L q.1
    exact ⟨K, hK, fun f hf q => e q f hf⟩
end YangMills.Construction.Tower.UnitScale.CrossingSmoothingPeriodic
end
