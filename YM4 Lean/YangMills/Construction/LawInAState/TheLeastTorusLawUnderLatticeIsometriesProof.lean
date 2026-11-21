import YangMills.Construction.InfiniteLattice.AllLatticeIsometriesAndTheMeanOfThePlaquetteFunctionProof
import YangMills.Construction.InfiniteLattice.CubicToriAmongTheToriOfAnyShape
import YangMills.Construction.InfiniteLattice.LatticeIsometriesOfASpacingAsMotionsAndTheirAction
import YangMills.Construction.InfiniteLattice.MovesOfBondsSupportsAndPlaquettes
import YangMills.Construction.InfiniteLattice.OrbitsAndPeriodicExtensions
import YangMills.Construction.InfiniteLattice.PeriodicExtensionOfTheWilsonMeasureIsInvariantUnderMotionsKeepingThePeriods
import YangMills.Construction.InfiniteLattice.WilsonMeasuresOfATorusAreProbabilities
import YangMills.Construction.LawInAState.TheLeastTorusLawUnderLatticeIsometries
import YangMills.Construction.ReflectionPositivity.SpaceOfConfigurationsAndPlaquetteEnergiesAtOneCutoff
import YangMills.Construction.SourcesAndGluing.LatticeIsometriesAndTheirAction
import Mathlib
set_option autoImplicit false
open MeasureTheory Set Function
noncomputable section
namespace YangMills.Construction
namespace InfiniteLattice.CubicSublatticeFineMesh
section
open GibbsAtFixedSpacing TestFunctions
open PeriodicLattice (meshSize torusSide)
variable {L m K : ℕ}
private theorem meshSize_pos (hL : 0 < L) (j : ℤ) : 0 < meshSize L j := by
  have : (0 : ℝ) < L := by exact_mod_cast hL
  exact zpow_pos this _
abbrev _root_.YangMills.SharedProofs.p6250 := @meshSize_pos
private theorem torusSide_pos (hL : 0 < L) (m : ℕ) : 0 < torusSide L m := by
  have : (0 : ℝ) < L := by exact_mod_cast hL
  unfold torusSide
  positivity
abbrev _root_.YangMills.SharedProofs.p34445 := @torusSide_pos
private theorem torusSide_eq_mul (hL : 0 < L) (m K : ℕ) :
    torusSide L m = ((2 * (L : ℤ) ^ (m + K) : ℤ) : ℝ) * meshSize L (K : ℤ) := by apply _root_.YangMills.Construction.SourcesAndGluing.torusSide_eq_intCast_mul_meshSize <;> assumption
private theorem three_mul_meshSize_lt_torusSide (hL : 13 ≤ L) (hK : 0 < K) :
    3 * meshSize L (K : ℤ) < torusSide L m := by
  have h2 : (13 : ℝ) ≤ L := by exact_mod_cast hL
  have h3 : (L : ℝ) ≤ (L : ℝ) ^ K := le_self_pow₀ (by linarith) hK.ne'
  have h4 : (1 : ℝ) ≤ (L : ℝ) ^ m := one_le_pow₀ (by linarith)
  have h5 : ((L : ℝ) ^ K)⁻¹ ≤ 13⁻¹ := inv_anti₀ (by norm_num) (by linarith)
  simp only [meshSize, zpow_neg, zpow_natCast]
  unfold torusSide
  linarith
private def periodPoint (hL : 0 < L) (m K : ℕ) (k : Fin 4 → ℤ) : LatticePoint (meshSize L (K : ℤ)) :=
  ⟨latticeTranslate (torusSide L m) k, fun μ => 2 * (L : ℤ) ^ (m + K) * k μ, fun μ => by
    simp only [latticeTranslate]
    rw [torusSide_eq_mul hL m K]
    push_cast
    ring⟩
private theorem le_norm_latticeTranslate {ℓ : ℝ} (hℓ : 0 < ℓ) {k : Fin 4 → ℤ} (hk : k ≠ 0) :
    ℓ ≤ ‖(latticeTranslate ℓ k : AmbientSpace)‖ := by
  obtain ⟨μ, hμ⟩ : ∃ μ, k μ ≠ 0 := Function.ne_iff.mp hk
  have h1 : (1 : ℝ) ≤ |(k μ : ℝ)| := by
    have : (1 : ℤ) ≤ |k μ| := Int.one_le_abs hμ
    exact_mod_cast this
  have h2 := norm_le_pi_norm (latticeTranslate ℓ k : AmbientSpace) μ
  simp only [latticeTranslate, Real.norm_eq_abs, abs_mul, abs_of_pos hℓ] at h2
  nlinarith
abbrev _root_.YangMills.SharedProofs.p106002 := @le_norm_latticeTranslate
private def cubicSublattice (hL : 13 ≤ L) (hK : 0 < K) :
    PeriodSublattice (meshSize L (K : ℤ)) where
  periods :=
    { carrier := {x | ∃ k, latticeTranslate (torusSide L m) k = (x : AmbientSpace)}
      add_mem' := by
        rintro x y ⟨k, hk⟩ ⟨k', hk'⟩
        exact ⟨k + k', by rw [latticeTranslate_add, hk, hk']; rfl⟩
      zero_mem' := ⟨0, by funext μ; simp [latticeTranslate]⟩
      neg_mem' := by
        rintro x ⟨k, hk⟩
        refine ⟨-k, ?_⟩
        funext μ
        have := congrFun hk μ
        simp only [latticeTranslate, Pi.neg_apply, Int.cast_neg, mul_neg] at this ⊢
        rw [this]
        rfl }
  exists_linearIndependent := by
    have h0 : 0 < L := by omega
    refine ⟨fun i => periodPoint h0 m K (Pi.single i 1), fun i => ⟨_, rfl⟩, ?_⟩
    rw [Fintype.linearIndependent_iff]
    intro g hg i
    have h := congrFun hg i
    simp only [periodPoint, latticeTranslate, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
      Pi.zero_apply] at h
    rw [Finset.sum_eq_single i] at h
    · have := (torusSide_pos h0 m).ne'
      simpa [this] using h
    · intro ν _ hν
      simp [Pi.single_eq_of_ne hν.symm]
    · simp
  le_norm_of_ne_zero := by
    rintro γ ⟨k, hk⟩ hγ
    have h0 : 0 < L := by omega
    have hk0 : k ≠ 0 := by
      rintro rfl
      apply hγ
      apply Subtype.ext
      rw [← hk]
      funext μ
      simp [latticeTranslate]
    have := le_norm_latticeTranslate (torusSide_pos h0 m) hk0
    have h3 := three_mul_meshSize_lt_torusSide (m := m) hL hK
    rw [hk] at this
    unfold minimalPeriodRatio
    linarith
private theorem hasCubicPeriods_cubicSublattice (hL : 13 ≤ L) (hK : 0 < K) :
    (cubicSublattice (m := m) hL hK).HasCubicPeriods (torusSide L m) := by
  have h0 : 0 < L := by omega
  ext x
  constructor
  · rintro ⟨γ, ⟨k, hk⟩, rfl⟩
    exact ⟨k, hk⟩
  · rintro ⟨k, rfl⟩
    exact ⟨periodPoint h0 m K k, ⟨k, rfl⟩, rfl⟩
section Cubic
variable {Γ : PeriodSublattice (meshSize L (K : ℤ))}
private theorem mem_periods_iff (h : Γ.HasCubicPeriods (torusSide L m)) (γ : LatticePoint (meshSize L (K : ℤ))) :
    γ ∈ Γ.periods ↔ ∃ k, latticeTranslate (torusSide L m) k = (γ : AmbientSpace) := by
  constructor
  · intro hγ
    have : (γ : AmbientSpace) ∈ cubicPeriodSet (torusSide L m) := by
      rw [← h]
      exact ⟨γ, hγ, rfl⟩
    exact this
  · rintro ⟨k, hk⟩
    have : (γ : AmbientSpace) ∈ (fun γ : LatticePoint (meshSize L (K : ℤ)) => (γ : AmbientSpace)) '' (Γ.periods : Set _) := by
      rw [h]
      exact ⟨k, hk⟩
    obtain ⟨γ', hγ', e⟩ := this
    rwa [← Subtype.ext e]
private theorem projectPoint_eq_iff (h : Γ.HasCubicPeriods (torusSide L m))
    (x y : LatticePoint (meshSize L (K : ℤ))) :
    projectPoint L m (K : ℤ) x = projectPoint L m (K : ℤ) y ↔ x - y ∈ Γ.periods := by
  rw [mem_periods_iff h]
  constructor
  · intro e
    have e' : TorusMetric.torusProj (torusSide L m) (y : AmbientSpace) =
        TorusMetric.torusProj (torusSide L m) (x : AmbientSpace) := (congrArg Subtype.val e).symm
    obtain ⟨k, hk⟩ := exists_latticeTranslate_of_torusProj_eq e'
    refine ⟨-k, ?_⟩
    funext μ
    have := congrFun hk μ
    simp only [latticeTranslate, Pi.add_apply, Pi.neg_apply, Int.cast_neg, mul_neg] at this ⊢
    change _ = (x : AmbientSpace) μ - (y : AmbientSpace) μ
    linarith
  · rintro ⟨k, hk⟩
    apply Subtype.ext
    change TorusMetric.torusProj (torusSide L m) (x : AmbientSpace) = TorusMetric.torusProj (torusSide L m) (y : AmbientSpace)
    have : (x : AmbientSpace) = (y : AmbientSpace) + latticeTranslate (torusSide L m) k := by
      rw [hk]
      funext μ
      change (x : AmbientSpace) μ = (y : AmbientSpace) μ + ((x : AmbientSpace) μ - (y : AmbientSpace) μ)
      ring
    rw [this, torusProj_add_latticeTranslate]
abbrev _root_.YangMills.SharedProofs.p44398 := @projectPoint_eq_iff
private theorem cubicProperties (hL : 0 < L) (h : Γ.HasCubicPeriods (torusSide L m)) :
    CubicPeriodSublatticeProperties Γ (torusSide L m) := by
  refine ⟨?_, ?_⟩
  · have hℓ := torusSide_pos hL m
    apply IsLeast.csInf_eq
    constructor
    · let k : Fin 4 → ℤ := Pi.single 0 1
      refine ⟨periodPoint hL m K k, (mem_periods_iff h _).2 ⟨k, rfl⟩, ?_, ?_⟩
      · intro h0
        have : latticeTranslate (torusSide L m) k = 0 := congrArg Subtype.val h0
        have h1 := congrFun this 0
        simp [latticeTranslate, k, hℓ.ne'] at h1
      · rw [← norm_eq_linfNorm]
        refine le_antisymm ?_ ?_
        · have hk0 : k ≠ 0 := fun e => by simpa [k] using congrFun e 0
          exact le_norm_latticeTranslate hℓ hk0
        · refine (pi_norm_le_iff_of_nonneg hℓ.le).2 fun μ => ?_
          change ‖torusSide L m * ((k μ : ℤ) : ℝ)‖ ≤ _
          by_cases hμ : μ = 0
          · subst hμ
            simp [k, abs_of_pos hℓ]
          · simp [k, Pi.single_eq_of_ne hμ, hℓ.le]
    · rintro _ ⟨γ, hγ, hne, rfl⟩
      obtain ⟨k, hk⟩ := (mem_periods_iff h γ).1 hγ
      rw [← norm_eq_linfNorm, ← hk]
      refine le_norm_latticeTranslate hℓ ?_
      rintro rfl
      apply hne
      apply Subtype.ext
      rw [← hk]
      funext μ
      simp [latticeTranslate]
  · intro w hw
    have key : ∀ w' ∈ hyperoctahedralLinearGroup, ∀ x ∈ cubicPeriodSet (torusSide L m),
        w' x ∈ cubicPeriodSet (torusSide L m) := by
      rintro w' hw' _ ⟨k, rfl⟩
      obtain ⟨π, t, ht⟩ := (mem_hyperoctahedralLinearGroup_iff w').1 hw'
      refine ⟨fun μ => (t μ : ℤ) * k (π μ), ?_⟩
      funext μ
      rw [ht]
      simp only [latticeTranslate]
      push_cast
      ring
    apply Subset.antisymm
    · rintro _ ⟨x, hx, rfl⟩
      exact key w hw x hx
    · intro x hx
      refine ⟨w.symm x, key _ (inv_mem hw) x hx, ?_⟩
      simp
abbrev _root_.YangMills.SharedProofs.p73080 := @cubicProperties
end Cubic
private theorem projectPoint_add (x y : LatticePoint (meshSize L (K : ℤ))) :
    projectPoint L m (K : ℤ) (x + y) = projectPoint L m (K : ℤ) x + projectPoint L m (K : ℤ) y := by
  refine Subtype.ext (funext fun μ => ?_)
  simp [projectPoint, TorusMetric.torusProj]
private theorem projectPoint_surjective : Surjective (projectPoint L m (K : ℤ)) := by
  intro z
  obtain ⟨n, hn⟩ := z.2
  refine ⟨⟨fun μ => (n μ : ℝ) * meshSize L (K : ℤ), n, fun _ => rfl⟩, ?_⟩
  refine Subtype.ext (funext fun μ => ?_)
  simp [projectPoint, TorusMetric.torusProj, hn]
private theorem projectLink_forwardFrom (x : LatticePoint (meshSize L (K : ℤ))) (κ : Fin 4) :
    projectLink L m (K : ℤ) (Link.forwardFrom x κ) =
      PeriodicLattice.Bond.forwardFrom (projectPoint L m (K : ℤ) x) κ :=
  PeriodicLattice.Bond.ext rfl (by
    change projectPoint L m (K : ℤ) (x + axisStep _ κ) = _ + _
    rw [projectPoint_add, projectPoint_axisStep])
private theorem norm_axisStep_le {a : ℝ} (ha : 0 ≤ a) (μ : Fin 4) : ‖(axisStep a μ : AmbientSpace)‖ ≤ a := by
  refine (pi_norm_le_iff_of_nonneg ha).2 fun ν => ?_
  by_cases h : ν = μ
  · subst h
    simp [axisStep, abs_of_nonneg ha]
  · simp [axisStep, Pi.single_eq_of_ne h, ha]
abbrev _root_.YangMills.DeltaSharedProofs.p1897 := @norm_axisStep_le
private theorem norm_terminal_sub_initial_le {a : ℝ} (ha : 0 ≤ a) (b : Link a) :
    ‖((b.terminal - b.initial : LatticePoint a) : AmbientSpace)‖ ≤ a := by
  obtain ⟨μ, h | h⟩ := b.isAdjacent
  · rw [h]
    exact norm_axisStep_le ha μ
  · rw [h]
    have : ((-axisStep a μ : LatticePoint a) : AmbientSpace) = -(axisStep a μ : AmbientSpace) := rfl
    rw [this, norm_neg]
    exact norm_axisStep_le ha μ
section Cubic
variable {Γ : PeriodSublattice (meshSize L (K : ℤ))}
private theorem eq_of_projectPoint_eq (hL : 0 < L) (h : Γ.HasCubicPeriods (torusSide L m))
    {u v : LatticePoint (meshSize L (K : ℤ))} (hu : ‖(u : AmbientSpace)‖ ≤ meshSize L (K : ℤ))
    (hv : ‖(v : AmbientSpace)‖ ≤ meshSize L (K : ℤ))
    (e : projectPoint L m (K : ℤ) u = projectPoint L m (K : ℤ) v) : u = v := by
  by_contra hne
  have hmem := (projectPoint_eq_iff h u v).1 e
  have h3 := Γ.le_norm_of_ne_zero _ hmem (sub_ne_zero.2 hne)
  have hle : ‖((u - v : LatticePoint _) : AmbientSpace)‖ ≤ 2 * meshSize L (K : ℤ) := by
    have : ((u - v : LatticePoint (meshSize L (K : ℤ))) : AmbientSpace) = (u : AmbientSpace) - (v : AmbientSpace) := rfl
    rw [this]
    refine (norm_sub_le _ _).trans ?_
    linarith
  have ha := meshSize_pos hL (K : ℤ)
  unfold minimalPeriodRatio at h3
  linarith
private theorem projectLink_isPositivelyOriented_iff (hL : 0 < L) (h : Γ.HasCubicPeriods (torusSide L m))
    (b : Link (meshSize L (K : ℤ))) :
    (projectLink L m (K : ℤ) b).IsPositivelyOriented ↔ b.IsPositivelyOriented := by
  constructor
  · rintro ⟨ν, hν⟩
    refine ⟨ν, ?_⟩
    have ha := (meshSize_pos hL (K : ℤ)).le
    refine eq_of_projectPoint_eq (m := m) hL h (norm_terminal_sub_initial_le ha b) (norm_axisStep_le ha ν) ?_
    rw [projectPoint_sub, projectPoint_axisStep]
    exact hν
  · rintro ⟨μ, hμ⟩
    refine ⟨μ, ?_⟩
    change projectPoint L m (K : ℤ) b.terminal - projectPoint L m (K : ℤ) b.initial = _
    rw [← projectPoint_sub, hμ, projectPoint_axisStep]
abbrev _root_.YangMills.SharedProofs.p7324 := @projectLink_isPositivelyOriented_iff
private theorem projectLink_translate (h : Γ.HasCubicPeriods (torusSide L m))
    (b : PositiveLink (meshSize L (K : ℤ))) {γ : LatticePoint (meshSize L (K : ℤ))} (hγ : γ ∈ Γ.periods) :
    projectLink L m (K : ℤ) (b.translate γ).1 = projectLink L m (K : ℤ) b.1 := by
  refine PeriodicLattice.Bond.ext ?_ ?_
  · exact (projectPoint_eq_iff h _ _).2 (by simpa [PositiveLink.translate] using hγ)
  · exact (projectPoint_eq_iff h _ _).2 (by simpa [PositiveLink.translate] using hγ)
private theorem positiveLink_translate_zero (b : PositiveLink (meshSize L (K : ℤ))) : b.translate 0 = b :=
  Subtype.ext (Link.ext (add_zero _) (add_zero _))
private theorem positiveLink_translate_translate (b : PositiveLink (meshSize L (K : ℤ)))
    (γ δ : LatticePoint (meshSize L (K : ℤ))) : (b.translate γ).translate δ = b.translate (γ + δ) :=
  Subtype.ext (Link.ext (add_assoc _ _ _) (add_assoc _ _ _))
private theorem linkOrbit_translate (b : PositiveLink (meshSize L (K : ℤ)))
    {γ : LatticePoint (meshSize L (K : ℤ))} (hγ : γ ∈ Γ.periods) :
    Γ.linkOrbit (b.translate γ) = Γ.linkOrbit b := by
  ext c
  constructor
  · rintro ⟨δ, hδ, rfl⟩
    exact ⟨γ + δ, add_mem hγ hδ, positiveLink_translate_translate b γ δ⟩
  · rintro ⟨δ, hδ, rfl⟩
    refine ⟨-γ + δ, add_mem (neg_mem hγ) hδ, ?_⟩
    rw [positiveLink_translate_translate, add_neg_cancel_left]
private theorem orbitLink_linkClass (h : Γ.HasCubicPeriods (torusSide L m))
    (b : PositiveLink (meshSize L (K : ℤ))) :
    Γ.orbitLink m (Γ.linkClass b) = projectLink L m (K : ℤ) b.1 := by
  unfold PeriodSublattice.orbitLink
  have hc := (mem_range.1 (Γ.linkClass b).2).choose_spec
  set c := (mem_range.1 (Γ.linkClass b).2).choose
  have hb : b ∈ Γ.linkOrbit c := by
    rw [hc]
    exact ⟨0, zero_mem _, (positiveLink_translate_zero b).symm⟩
  obtain ⟨γ, hγ, e⟩ := hb
  rw [e, projectLink_translate h c hγ]
abbrev _root_.YangMills.SharedProofs.p27953 := @orbitLink_linkClass
private theorem linkClass_eq_of_projectLink_eq (hL : 0 < L) (h : Γ.HasCubicPeriods (torusSide L m))
    (b b' : PositiveLink (meshSize L (K : ℤ)))
    (e : projectLink L m (K : ℤ) b.1 = projectLink L m (K : ℤ) b'.1) :
    Γ.linkClass b = Γ.linkClass b' := by
  have et : projectPoint L m (K : ℤ) b.1.initial = projectPoint L m (K : ℤ) b'.1.initial :=
    congrArg PeriodicLattice.Bond.source e
  have eh : projectPoint L m (K : ℤ) b.1.terminal = projectPoint L m (K : ℤ) b'.1.terminal :=
    congrArg PeriodicLattice.Bond.target e
  have hγ : b'.1.initial - b.1.initial ∈ Γ.periods := (projectPoint_eq_iff h _ _).1 et.symm
  obtain ⟨μ, hμ⟩ := b.2
  obtain ⟨μ', hμ'⟩ := b'.2
  have ha := (meshSize_pos hL (K : ℤ)).le
  have hs : axisStep (meshSize L (K : ℤ)) μ = axisStep _ μ' := by
    refine eq_of_projectPoint_eq (m := m) hL h (norm_axisStep_le ha μ) (norm_axisStep_le ha μ') ?_
    rw [← hμ, ← hμ', projectPoint_sub, projectPoint_sub, et, eh]
  have hb' : b' = b.translate (b'.1.initial - b.1.initial) := by
    refine Subtype.ext (Link.ext ?_ ?_)
    · change b'.1.initial = b.1.initial + (b'.1.initial - b.1.initial)
      abel
    · change b'.1.terminal = b.1.terminal + (b'.1.initial - b.1.initial)
      have h1 : b'.1.terminal = b'.1.initial + axisStep _ μ' := by rw [← hμ']; abel
      have h2 : b.1.terminal = b.1.initial + axisStep _ μ := by rw [← hμ]; abel
      rw [h1, h2, hs]
      abel
  apply Subtype.ext
  change Γ.linkOrbit b = Γ.linkOrbit b'
  rw [hb', linkOrbit_translate b hγ]
private theorem orbitLink_isPositivelyOriented (hL : 0 < L) (h : Γ.HasCubicPeriods (torusSide L m))
    (ω : Γ.QuotientLink) : (Γ.orbitLink m ω).IsPositivelyOriented :=
  (projectLink_isPositivelyOriented_iff hL h _).2 (mem_range.1 ω.2).choose.2
private theorem bijOn_orbitLink (hL : 0 < L) (h : Γ.HasCubicPeriods (torusSide L m)) :
    BijOn (Γ.orbitLink m) univ (PeriodicLattice.forwardBonds L m (K : ℤ)) := by
  refine ⟨fun ω _ => PeriodicLattice.mem_positiveBonds_iff.2
    (orbitLink_isPositivelyOriented hL h ω), ?_, ?_⟩
  · rintro ⟨_, b, rfl⟩ - ⟨_, b', rfl⟩ - e
    have e' : Γ.orbitLink m (Γ.linkClass b) = Γ.orbitLink m (Γ.linkClass b') := e
    rw [orbitLink_linkClass h, orbitLink_linkClass h] at e'
    exact linkClass_eq_of_projectLink_eq hL h b b' e'
  · rintro c ⟨z, κ, rfl⟩
    obtain ⟨x, rfl⟩ := projectPoint_surjective (m := m) (K := K) z
    have hp : (Link.forwardFrom x κ).IsPositivelyOriented := ⟨κ, by simp [Link.forwardFrom]⟩
    refine ⟨Γ.linkClass ⟨Link.forwardFrom x κ, hp⟩, mem_univ _, ?_⟩
    rw [orbitLink_linkClass h, projectLink_forwardFrom]
abbrev _root_.YangMills.SharedProofs.p56004 := @bijOn_orbitLink
private def orbitLinkEquiv (hL : 0 < L) (h : Γ.HasCubicPeriods (torusSide L m)) :
    Γ.QuotientLink ≃ PeriodicLattice.PositivelyOrientedBond L m (K : ℤ) :=
  Equiv.ofBijective (fun ω => ⟨Γ.orbitLink m ω, orbitLink_isPositivelyOriented hL h ω⟩) (by
    constructor
    · intro ω ω' e
      exact (bijOn_orbitLink hL h).injOn (mem_univ _) (mem_univ _) (congrArg Subtype.val e)
    · rintro ⟨c, hc⟩
      obtain ⟨ω, -, e⟩ := (bijOn_orbitLink hL h).surjOn
        (PeriodicLattice.mem_positiveBonds_iff.2 hc)
      exact ⟨ω, Subtype.ext e⟩)
private theorem lift_pullbackConfig (h : Γ.HasCubicPeriods (torusSide L m))
    (U : PeriodicLattice.CompactGaugeField L m (K : ℤ)) :
    Γ.lift (Γ.pullbackConfig m U) = liftCompactField U := by
  apply Subtype.ext
  funext b
  change Γ.liftValue (Γ.pullbackConfig m U) b = liftCompactField U b
  rw [liftCompactField_apply]
  unfold PeriodSublattice.liftValue
  by_cases hb : b.IsPositivelyOriented
  · rw [dif_pos hb]
    change U.linkValue (Γ.orbitLink m (Γ.linkClass ⟨b, hb⟩)) = _
    rw [orbitLink_linkClass h]
  · have hr := PeriodSublattice.isPositivelyOriented_opposite_of_not hb
    rw [dif_neg hb, dif_pos hr]
    change (U.linkValue (Γ.orbitLink m (Γ.linkClass ⟨b.opposite, hr⟩)))⁻¹ = _
    rw [orbitLink_linkClass h, projectLink_opposite, U.linkValue_opposite, inv_inv]
abbrev _root_.YangMills.SharedProofs.p44760 := @lift_pullbackConfig
private theorem gaugeFieldOfPositive_mem (hL : 2 ≤ L) (hK : 0 < K)
    (v : PeriodicLattice.PositivelyOrientedBond L m (K : ℤ) → Matrices.ComplexMatrix2.specialUnitary) :
    PeriodicLattice.gaugeFieldOfPositive v ∈ PeriodicLattice.compactGaugeFields L m (K : ℤ) := by
  have hj : -(m : ℤ) < (K : ℤ) := by omega
  refine ⟨fun b _ => ?_, fun b _ => ?_⟩
  · unfold PeriodicLattice.gaugeFieldOfPositive
    rcases PeriodicLattice.MatrixValued.xor_isPositivelyOriented_opposite hL hj b with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [dif_pos h1]
      exact (v _).2
    · rw [dif_neg h2, dif_pos h1, ← specialUnitary_coe_inv]
      exact (_ : Matrices.ComplexMatrix2.specialUnitary).2
  · unfold PeriodicLattice.gaugeFieldOfPositive
    rcases PeriodicLattice.MatrixValued.xor_isPositivelyOriented_opposite hL hj b with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · have h3 : b.opposite.opposite.IsPositivelyOriented := h1
      rw [dif_neg h2, dif_pos h3, dif_pos h1]
      rfl
    · rw [dif_pos h1, dif_neg h2, dif_pos h1, ← specialUnitary_coe_inv, ← specialUnitary_coe_inv, inv_inv]
private theorem measurable_pullbackFun : Measurable (Γ.pullbackFun m) := by
  classical
  have : SecondCountableTopology Matrices.ComplexMatrix2 :=
    inferInstanceAs (SecondCountableTopology (Fin 2 → Fin 2 → ℂ))
  have hR : MeasurableSet (PeriodicLattice.compactGaugeFields L m (K : ℤ)) :=
    (PeriodicLattice.isClosed_compactGaugeFields L m (K : ℤ)).measurableSet
  refine measurable_pi_iff.2 fun ω => ?_
  have hf : Measurable fun U : PeriodicLattice.compactGaugeFields L m (K : ℤ) =>
      Γ.pullbackFun m U.1 ω := by
    have hc : Continuous fun U : PeriodicLattice.compactGaugeFields L m (K : ℤ) =>
        Γ.pullbackFun m U.1 ω := by
      have e : (fun U : PeriodicLattice.compactGaugeFields L m (K : ℤ) =>
          Γ.pullbackFun m U.1 ω) = fun U => ⟨U.1 (Γ.orbitLink m ω), U.2.1 _ (mem_univ _)⟩ := by
        funext U
        simp only [PeriodSublattice.pullbackFun, dif_pos U.2]
        rfl
      rw [e]
      exact Continuous.subtype_mk ((continuous_apply _).comp continuous_subtype_val) _
    exact hc.measurable
  have hg : Measurable fun _ : ((PeriodicLattice.compactGaugeFields L m (K : ℤ))ᶜ : Set _) =>
      (1 : Matrices.ComplexMatrix2.specialUnitary) := measurable_const
  have hd := Measurable.dite hf hg hR
  convert hd using 1
  funext U
  by_cases hU : U ∈ PeriodicLattice.compactGaugeFields L m (K : ℤ)
  · simp only [hU, dite_true]
  · simp only [hU, dite_false, PeriodSublattice.pullbackFun]
abbrev _root_.YangMills.SharedProofs.p17634 := @measurable_pullbackFun
private theorem measurable_gaugeFieldOfPositive (hL : 2 ≤ L) (hK : 0 < K) :
    Measurable (PeriodicLattice.gaugeFieldOfPositive (L := L) (m := m) (j := (K : ℤ))) := by
  have hs : SecondCountableTopology Matrices.ComplexMatrix2 :=
    inferInstanceAs (SecondCountableTopology (Fin 2 → Fin 2 → ℂ))
  have hs' : SecondCountableTopology Matrices.ComplexMatrix2.specialUnitary :=
    TopologicalSpace.Subtype.secondCountableTopology _
  have hj : -(m : ℤ) < (K : ℤ) := by omega
  refine measurable_pi_iff.2 fun b => Continuous.measurable ?_
  unfold PeriodicLattice.gaugeFieldOfPositive
  rcases PeriodicLattice.MatrixValued.xor_isPositivelyOriented_opposite hL hj b with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · simp only [dif_pos h1]
    exact continuous_subtype_val.comp (continuous_apply _)
  · simp only [dif_neg h2, dif_pos h1, ← specialUnitary_coe_inv]
    exact continuous_subtype_val.comp (continuous_apply _).inv
private theorem map_productHaarMeasure (hL : 13 ≤ L) (hK : 0 < K)
    (h : Γ.HasCubicPeriods (torusSide L m)) [Finite Γ.QuotientLink]
    (hR : ReflectionPositivity.CutoffMirrors.RelabelInvertMeasurePreserving) :
    (PeriodicLattice.productHaarMeasure L m (K : ℤ)).map (Γ.pullbackFun m) = Γ.quotientHaar := by
  have h0 : 0 < L := by omega
  have hf : Finite (PeriodicLattice.PositivelyOrientedBond L m (K : ℤ)) := Finite.of_equiv _ (orbitLinkEquiv h0 h)
  unfold PeriodicLattice.productHaarMeasure PeriodicLattice.gaugeFieldHaar
  rw [Measure.map_map measurable_pullbackFun (measurable_gaugeFieldOfPositive (by omega) hK)]
  have e : Γ.pullbackFun m ∘ PeriodicLattice.gaugeFieldOfPositive =
      ReflectionPositivity.CutoffMirrors.relabelInvert (orbitLinkEquiv h0 h) (fun _ => 1) := by
    funext v ω
    apply Subtype.ext
    have hv := gaugeFieldOfPositive_mem (K := K) (by omega) hK v
    simp only [comp_apply, PeriodSublattice.pullbackFun, dif_pos hv]
    change PeriodicLattice.gaugeFieldOfPositive v (Γ.orbitLink m ω) = _
    unfold PeriodicLattice.gaugeFieldOfPositive ReflectionPositivity.CutoffMirrors.relabelInvert
    rw [dif_pos (orbitLink_isPositivelyOriented h0 h ω)]
    simp
    rfl
  rw [e]
  exact (hR _ _ (orbitLinkEquiv h0 h) (fun _ => 1)).2.1
section Plaquettes
variable {a : ℝ}
private def plaquetteShift (p : ElementaryPlaquette a) (γ : LatticePoint a) : ElementaryPlaquette a :=
  ⟨p.corner + γ, p.lowAxis, p.highAxis, p.lowAxis_lt_highAxis⟩
private theorem cornerSet_plaquetteShift (p : ElementaryPlaquette a) (γ : LatticePoint a) :
    (plaquetteShift p γ).cornerSet = (shift γ).pointMap '' p.cornerSet := by
  have hs : ∀ x, (shift γ).pointMap x = x + γ := fun x => Subtype.ext rfl
  simp only [ElementaryPlaquette.cornerSet, image_insert_eq, image_singleton, hs, plaquetteShift]
  have e1 : p.corner + γ + axisStep a p.lowAxis = p.corner + axisStep a p.lowAxis + γ := by abel
  have e3 : p.corner + γ + axisStep a p.highAxis = p.corner + axisStep a p.highAxis + γ := by abel
  have e2' : p.corner + axisStep a p.lowAxis + γ + axisStep a p.highAxis =
      p.corner + axisStep a p.lowAxis + axisStep a p.highAxis + γ := by abel
  rw [e1, e2', e3]
abbrev _root_.YangMills.DeltaSharedProofs.p501596 := @cornerSet_plaquetteShift
private theorem plaquetteMap_shift (hmv : SymmetriesTransportPlaquettes a) (p : ElementaryPlaquette a)
    (γ : LatticePoint a) : (shift γ).plaquetteMap p = plaquetteShift p γ :=
  ((hmv (shift γ)).1 p).1.unique ((hmv (shift γ)).1 p).2
    (cornerSet_plaquetteShift p γ)
private theorem plaquetteShift_plaquetteShift (p : ElementaryPlaquette a) (γ δ : LatticePoint a) :
    plaquetteShift (plaquetteShift p γ) δ = plaquetteShift p (γ + δ) :=
  ElementaryPlaquette.ext (add_assoc _ _ _) rfl rfl
abbrev _root_.YangMills.DeltaSharedProofs.p502013 := @plaquetteShift_plaquetteShift
private theorem continuous_faceEnergy (p : ElementaryPlaquette a) :
    Continuous fun U : GaugeField a => faceEnergy U p := by apply _root_.YangMills.Construction.LatticeConventions.SymmetryGeneration.continuous_faceEnergy <;> assumption
end Plaquettes
private theorem projectPlaquette_plaquetteShift (h : Γ.HasCubicPeriods (torusSide L m))
    (p : ElementaryPlaquette (meshSize L (K : ℤ))) {γ : LatticePoint (meshSize L (K : ℤ))} (hγ : γ ∈ Γ.periods) :
    TorusLifts.projectPlaquette L m (K : ℤ) (plaquetteShift p γ) =
      TorusLifts.projectPlaquette L m (K : ℤ) p :=
  PeriodicLattice.Plaquette.ext
    ((projectPoint_eq_iff h _ _).2 (by simpa [plaquetteShift] using hγ)) rfl rfl
private theorem plaquetteOrbit_plaquetteShift (hmv : SymmetriesTransportPlaquettes (meshSize L (K : ℤ)))
    (p : ElementaryPlaquette (meshSize L (K : ℤ))) {γ : LatticePoint (meshSize L (K : ℤ))} (hγ : γ ∈ Γ.periods) :
    Γ.plaquetteOrbit (plaquetteShift p γ) = Γ.plaquetteOrbit p := by
  ext r
  constructor
  · rintro ⟨δ, hδ, rfl⟩
    refine ⟨γ + δ, add_mem hγ hδ, ?_⟩
    rw [plaquetteMap_shift hmv, plaquetteMap_shift hmv,
      plaquetteShift_plaquetteShift]
  · rintro ⟨δ, hδ, rfl⟩
    refine ⟨-γ + δ, add_mem (neg_mem hγ) hδ, ?_⟩
    rw [plaquetteMap_shift hmv, plaquetteMap_shift hmv,
      plaquetteShift_plaquetteShift, add_neg_cancel_left]
private theorem orbitPlaquette_mk (h : Γ.HasCubicPeriods (torusSide L m))
    (hmv : SymmetriesTransportPlaquettes (meshSize L (K : ℤ)))
    (p : ElementaryPlaquette (meshSize L (K : ℤ))) :
    Γ.orbitPlaquette m ⟨Γ.plaquetteOrbit p, p, rfl⟩ =
      TorusLifts.projectPlaquette L m (K : ℤ) p := by
  unfold PeriodSublattice.orbitPlaquette
  obtain ⟨γ, hγ, e⟩ := (Γ.quotientPlaquette_nonempty ⟨Γ.plaquetteOrbit p, p, rfl⟩).some_mem
  rw [e, plaquetteMap_shift hmv, projectPlaquette_plaquetteShift h p hγ]
private theorem bijective_orbitPlaquette (h : Γ.HasCubicPeriods (torusSide L m))
    (hmv : SymmetriesTransportPlaquettes (meshSize L (K : ℤ))) :
    Bijective (Γ.orbitPlaquette m) := by
  constructor
  · rintro ⟨_, p, rfl⟩ ⟨_, q, rfl⟩ e
    rw [orbitPlaquette_mk h hmv, orbitPlaquette_mk h hmv] at e
    have eb : projectPoint L m (K : ℤ) p.corner = projectPoint L m (K : ℤ) q.corner :=
      congrArg PeriodicLattice.Plaquette.origin e
    have e1 : p.lowAxis = q.lowAxis := congrArg PeriodicLattice.Plaquette.firstAxis e
    have e2 : p.highAxis = q.highAxis := congrArg PeriodicLattice.Plaquette.secondAxis e
    have hγ : q.corner - p.corner ∈ Γ.periods := (projectPoint_eq_iff h _ _).1 eb.symm
    have hq : q = plaquetteShift p (q.corner - p.corner) :=
      ElementaryPlaquette.ext (by simp [plaquetteShift]) e1.symm e2.symm
    apply Subtype.ext
    change Γ.plaquetteOrbit p = Γ.plaquetteOrbit q
    have key : Γ.plaquetteOrbit q = Γ.plaquetteOrbit p := by
      conv_lhs => rw [hq]
      exact plaquetteOrbit_plaquetteShift hmv p hγ
    exact key.symm
  · intro p'
    obtain ⟨x, hx⟩ := projectPoint_surjective (m := m) (K := K) p'.origin
    let p : ElementaryPlaquette (meshSize L (K : ℤ)) := ⟨x, p'.firstAxis, p'.secondAxis, p'.firstAxis_lt_secondAxis⟩
    refine ⟨⟨Γ.plaquetteOrbit p, p, rfl⟩, ?_⟩
    rw [orbitPlaquette_mk h hmv]
    exact PeriodicLattice.Plaquette.ext hx rfl rfl
abbrev _root_.YangMills.SharedProofs.p33208 := @bijective_orbitPlaquette
private theorem faceEnergy_liftCompactField (U : PeriodicLattice.CompactGaugeField L m (K : ℤ))
    (p : ElementaryPlaquette (meshSize L (K : ℤ))) :
    faceEnergy (liftCompactField U) p =
      PeriodicLattice.plaquetteCost U.1 (TorusLifts.projectPlaquette L m (K : ℤ) p) := by
  have e : ∀ (x : LatticePoint (meshSize L (K : ℤ))) (κ : Fin 4),
      liftCompactField U (Link.forwardFrom x κ) =
        U.linkValue (PeriodicLattice.Bond.forwardFrom (projectPoint L m (K : ℤ) x) κ) := fun x κ => by
    rw [liftCompactField_apply, projectLink_forwardFrom]
  have hv : ((faceHolonomy (liftCompactField U) p : Matrices.ComplexMatrix2.specialUnitary) : Matrices.ComplexMatrix2) =
      PeriodicLattice.plaquetteHolonomy U.1 (TorusLifts.projectPlaquette L m (K : ℤ) p) := by
    have hr : ∀ b : PeriodicLattice.Bond L m (K : ℤ),
        (((U.linkValue b)⁻¹ : Matrices.ComplexMatrix2.specialUnitary) : Matrices.ComplexMatrix2) = U.1 b.opposite := fun b => by
      rw [← U.linkValue_opposite b]
      rfl
    simp only [faceHolonomy, e, projectPoint_add, projectPoint_axisStep,
      PeriodicLattice.plaquetteHolonomy, PeriodicLattice.pathHolonomy, PeriodicLattice.Plaquette.boundaryBonds,
      TorusLifts.projectPlaquette, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
      mul_one, Submonoid.coe_mul, hr]
    simp only [mul_assoc]
    rfl
  simp only [faceEnergy, PeriodicLattice.plaquetteCost, hv]
private theorem measureMap_withDensity_comp {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y] (μ : Measure X)
    {f : X → Y} (hf : Measurable f) {g : Y → ENNReal} (hg : Measurable g) :
    (μ.withDensity (g ∘ f)).map f = (μ.map f).withDensity g := by
  ext S hS
  rw [Measure.map_apply hf hS, withDensity_apply _ (hf hS), withDensity_apply _ hS,
    setLIntegral_map hS hg hf]
  rfl
abbrev _root_.YangMills.SharedProofs.p22819 := @measureMap_withDensity_comp
private theorem continuous_boltzmannWeight [Finite Γ.QuotientPlaquette]
    (hper : ∀ F : GaugeField (meshSize L (K : ℤ)) → ℝ, Continuous F → Continuous (Γ.periodize F))
    (β : ℝ) : Continuous (Γ.boltzmannWeight β) := by
  unfold PeriodSublattice.boltzmannWeight
  refine Real.continuous_exp.comp (continuous_const.mul ?_)
  cases nonempty_fintype Γ.QuotientPlaquette
  simp only [finsum_eq_sum_of_fintype]
  exact continuous_finsetSum _ fun p _ => hper _ (continuous_faceEnergy _)
abbrev _root_.YangMills.SharedProofs.p17687 := @continuous_boltzmannWeight
private theorem boltzmannWeight_eq (h : Γ.HasCubicPeriods (torusSide L m))
    (hmv : SymmetriesTransportPlaquettes (meshSize L (K : ℤ)))
    (hpl : ∀ (U : PeriodicLattice.CompactGaugeField L m (K : ℤ))
      (p : ElementaryPlaquette (meshSize L (K : ℤ))), faceEnergy (liftCompactField U) p =
        PeriodicLattice.plaquetteCost U.1 (TorusLifts.projectPlaquette L m (K : ℤ) p))
    (β : ℝ) {U : PeriodicLattice.Bond L m (K : ℤ) → Matrices.ComplexMatrix2}
    (hU : U ∈ PeriodicLattice.compactGaugeFields L m (K : ℤ)) :
    PeriodicLattice.boltzmannWeight β U = Γ.boltzmannWeight β (Γ.pullbackFun m U) := by
  unfold PeriodicLattice.boltzmannWeight PeriodSublattice.boltzmannWeight PeriodicLattice.wilsonAction
  congr 2
  rw [← finsum_comp_equiv (Equiv.ofBijective _ (bijective_orbitPlaquette h hmv))]
  refine finsum_congr fun p => ?_
  obtain ⟨U', rfl⟩ : ∃ U' : PeriodicLattice.CompactGaugeField L m (K : ℤ), U'.1 = U :=
    ⟨⟨U, hU⟩, rfl⟩
  have e : Γ.pullbackFun m U'.1 = Γ.pullbackConfig m U' := dif_pos U'.2
  rw [e]
  unfold PeriodSublattice.quotientFaceEnergy
  rw [lift_pullbackConfig h, hpl]
  rfl
abbrev _root_.YangMills.SharedProofs.p63838 := @boltzmannWeight_eq
private theorem lift_comp_pullbackFun (h : Γ.HasCubicPeriods (torusSide L m)) :
    Γ.lift ∘ Γ.pullbackFun m = liftField L m (K : ℤ) := by
  classical
  funext U
  by_cases hU : U ∈ PeriodicLattice.compactGaugeFields L m (K : ℤ)
  · obtain ⟨U', rfl⟩ : ∃ U' : PeriodicLattice.CompactGaugeField L m (K : ℤ), U'.1 = U :=
      ⟨⟨U, hU⟩, rfl⟩
    have e : Γ.pullbackFun m U'.1 = Γ.pullbackConfig m U' := dif_pos U'.2
    rw [comp_apply, e, lift_pullbackConfig h]
    rfl
  · have e : Γ.pullbackFun m U = fun _ => 1 := dif_neg hU
    rw [comp_apply, e]
    have e' : liftField L m (K : ℤ) U = ⟨fun _ => 1, fun _ => by simp⟩ := dif_neg hU
    rw [e']
    apply Subtype.ext
    funext b
    change Γ.liftValue (fun _ => 1) b = 1
    unfold PeriodSublattice.liftValue
    split_ifs <;> simp
abbrev _root_.YangMills.SharedProofs.p23053 := @lift_comp_pullbackFun
private theorem liftedGibbsMeasure_eq_liftedWilsonMeasure (hL : 13 ≤ L) (hK : 0 < K) (β : ℝ)
    (ho : GibbsAtFixedSpacing.PeriodSublatticeQuotientFacts)
    (hmv : SymmetriesTransportPlaquettes (meshSize L (K : ℤ)))
    (hR : ReflectionPositivity.CutoffMirrors.RelabelInvertMeasurePreserving)
    (h : Γ.HasCubicPeriods (torusSide L m)) :
    Γ.liftedGibbsMeasure β = liftedWilsonMeasure L m K β := by
  have h0 : 0 < L := by omega
  have ha := meshSize_pos h0 (K : ℤ)
  obtain ⟨⟨-, -, hFB, hFP, -⟩, ⟨hcont, -, -⟩, ⟨-, -, hper⟩⟩ := ho _ ha Γ
  have := hFB
  have := hFP
  have hs : SecondCountableTopology Matrices.ComplexMatrix2 :=
    inferInstanceAs (SecondCountableTopology (Fin 2 → Fin 2 → ℂ))
  have hs' : SecondCountableTopology Matrices.ComplexMatrix2.specialUnitary :=
    TopologicalSpace.Subtype.secondCountableTopology _
  have hae : ∀ᵐ U ∂PeriodicLattice.productHaarMeasure L m (K : ℤ),
      U ∈ PeriodicLattice.compactGaugeFields L m (K : ℤ) := by
    unfold PeriodicLattice.productHaarMeasure PeriodicLattice.gaugeFieldHaar
    have hset : MeasurableSet {U | U ∈ PeriodicLattice.compactGaugeFields L m (K : ℤ)} :=
      (PeriodicLattice.isClosed_compactGaugeFields L m (K : ℤ)).measurableSet
    exact (ae_map_iff (measurable_gaugeFieldOfPositive (by omega) hK).aemeasurable hset).2
      (ae_of_all _ fun v => gaugeFieldOfPositive_mem (by omega) hK v)
  have hmeas : Measurable (Γ.pullbackFun m) := measurable_pullbackFun
  have hmap := map_productHaarMeasure hL hK h hR
  have hwc := continuous_boltzmannWeight (fun F hF => hper ℝ F hF) β
  have hwm : Measurable (Γ.boltzmannWeight β) := hwc.measurable
  have hpl := faceEnergy_liftCompactField (L := L) (m := m) (K := K)
  have hZ : PeriodicLattice.partitionFunction L m K β = Γ.partitionFunction β := by
    have e : Γ.partitionFunction β = ∫ V, Γ.boltzmannWeight β V ∂(PeriodicLattice.productHaarMeasure L m (K : ℤ)).map
        (Γ.pullbackFun m) := by
      rw [hmap]
      rfl
    rw [e, integral_map hmeas.aemeasurable hwm.aestronglyMeasurable]
    exact integral_congr_ae (hae.mono fun U hU => boltzmannWeight_eq h hmv hpl β hU)
  have hdens : (PeriodicLattice.productHaarMeasure L m (K : ℤ)).withDensity
      (fun U => ENNReal.ofReal (PeriodicLattice.boltzmannWeight β U)) =
      (PeriodicLattice.productHaarMeasure L m (K : ℤ)).withDensity
        ((fun V => ENNReal.ofReal (Γ.boltzmannWeight β V)) ∘ Γ.pullbackFun m) :=
    withDensity_congr_ae (hae.mono fun U hU => by
      simp only [comp_apply]
      rw [boltzmannWeight_eq h hmv hpl β hU])
  have hWm : Γ.gibbsMeasure β = (PeriodicLattice.wilsonGibbsMeasure L m K β).map (Γ.pullbackFun m) := by
    unfold PeriodicLattice.wilsonGibbsMeasure PeriodSublattice.gibbsMeasure
    rw [Measure.map_smul, hdens, measureMap_withDensity_comp _ hmeas hwm.ennreal_ofReal, hmap, hZ]
  unfold PeriodSublattice.liftedGibbsMeasure liftedWilsonMeasure
  rw [hWm, Measure.map_map hcont.measurable hmeas, lift_comp_pullbackFun h]
end Cubic
end
end InfiniteLattice.CubicSublatticeFineMesh
namespace StateLaws
open ChessboardTori InfiniteLattice
theorem unitTorusMeasureSymmetricStatement_holds
    (ho : GibbsAtFixedSpacing.PeriodSublatticeQuotientFacts)
    (hv : GibbsAtFixedSpacing.SymmetriesTransportLinksSupportsAndPlaquettes)
    (hS : ReflectionPositivity.CutoffMirrors.FieldSpaceAndFaceEnergies.Statement)
    (hA : InfiniteLattice.SymmetriesAsMotions.Statement)
    (hI : InfiniteLattice.PeriodicGibbsSymmetricUnderPeriodPreservingMotions)
    (hP : InfiniteLattice.QuotientGibbsMeasuresProbability.Statement) :
    unitTorusMeasureSymmetricStatement := by
  intro D
  have hL : 13 ≤ D.L := D.isAdmissible.2
  have hK : 0 < (D.K : ℕ) := D.K.pos
  have h0 : 0 < D.L := by omega
  have ha : 0 < PeriodicLattice.meshSize D.L ((D.K : ℕ) : ℤ) := CubicSublatticeFineMesh.meshSize_pos h0 _
  let Γ := CubicSublatticeFineMesh.cubicSublattice (m := 0) hL hK
  have hc : Γ.HasCubicPeriods (PeriodicLattice.torusSide D.L 0) :=
    CubicSublatticeFineMesh.hasCubicPeriods_cubicSublattice hL hK
  have hmv := (hv _ ha).2.2
  have hR : ReflectionPositivity.CutoffMirrors.RelabelInvertMeasurePreserving :=
    (hS ⟨D.toStandingParameters, D.β, D.beta_pos, 0⟩).2.1
  have hE : Γ.liftedGibbsMeasure D.β = unitTorusMeasure D.L D.K D.β :=
    CubicSublatticeFineMesh.liftedGibbsMeasure_eq_liftedWilsonMeasure hL hK D.β ho hmv hR hc
  refine ⟨hE ▸ (hP D.β D.beta_pos _ ha Γ).isProbabilityMeasure_lifted, fun r => ?_⟩
  obtain ⟨⟨R, hRW, v, hrv⟩, -⟩ := (hA _ ha r r).1
  have himg := (CubicSublatticeFineMesh.cubicProperties h0 hc).image_cubicPeriodSet R hRW
  have hΓ : R '' (Subtype.val '' (Γ.periods : Set (LatticePoint (PeriodicLattice.meshSize D.L ((D.K : ℕ) : ℤ))))) =
      Subtype.val '' (Γ.periods : Set (LatticePoint (PeriodicLattice.meshSize D.L ((D.K : ℕ) : ℤ)))) := by
    have e : Subtype.val '' (Γ.periods : Set (LatticePoint (PeriodicLattice.meshSize D.L ((D.K : ℕ) : ℤ)))) =
        cubicPeriodSet (PeriodicLattice.torusSide D.L 0) := hc
    rw [e]
    exact himg
  have := hI _ D.β ha D.beta_pos Γ r R hRW v hrv hΓ
  rwa [hE] at this
end StateLaws
end YangMills.Construction
end
