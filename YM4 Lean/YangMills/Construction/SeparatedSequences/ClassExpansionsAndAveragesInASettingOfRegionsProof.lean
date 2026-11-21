import YangMills.Construction.DirichletOperator.FactsOfTheSettingInLevelUnitsProof
import YangMills.Construction.SeparatedSequences.SettingsOfOneSequence
import Mathlib
set_option autoImplicit false
open Set YangMills.Construction.TorusMetric YangMills.Construction.PeriodicLattice.DirichletOperators
open scoped Pointwise
noncomputable section
namespace YangMills.Construction.SeparatedClasses.SingleSequence.NestedRescale
open SequenceData
variable (s : SequenceData) (𝒮 : RegionSequence.NestedRegions)
def torusRescale : s.data.Point ≃+ 𝒮.Point :=
  AddEquiv.piCongrRight fun _ =>
    AddCircle.equivAddCircle _ _ s.torusSide_ne_zero 𝒮.side_pos.ne'
theorem toTorus_eq_rescale (x : s.data.Point) : s.toTorus 𝒮.side x = torusRescale s 𝒮 x := by
  unfold SequenceData.toTorus
  rw [dif_pos 𝒮.side_pos.ne']
  rfl
def rescaleFactor : ℝ := (PeriodicLattice.torusSide s.data.L s.data.m)⁻¹ * 𝒮.side
theorem rescale_coe (v : Fin 4 → ℝ) :
    torusRescale s 𝒮 (fun μ => ((v μ : ℝ) : AddCircle (PeriodicLattice.torusSide s.data.L s.data.m))) =
      fun μ => ((v μ * rescaleFactor s 𝒮 : ℝ) : AddCircle 𝒮.side) := by
  funext μ
  exact AddCircle.equivAddCircle_apply_mk _ _ s.torusSide_ne_zero 𝒮.side_pos.ne' (v μ)
variable {s 𝒮}
theorem blockFactor_pos : (0 : ℝ) < s.data.L := by
  have := s.data.isAdmissible.2
  exact_mod_cast (by omega : 0 < s.data.L)
theorem rescaleFactor_eq (hs : s.IsNestedRegions 𝒮) :
    rescaleFactor s 𝒮 = (s.data.L : ℝ) ^ (((s.data.K : ℕ) : ℤ) - (s.data.t : ℤ)) := by
  have hL := (blockFactor_pos (s := s)).ne'
  have hp : (s.data.L : ℝ) ^ (((s.data.m : ℕ) : ℤ) + ((s.data.K : ℕ) : ℤ) - (s.data.t : ℤ)) =
      (s.data.L : ℝ) ^ (s.data.m : ℕ) *
        (s.data.L : ℝ) ^ (((s.data.K : ℕ) : ℤ) - (s.data.t : ℤ)) := by
    rw [← zpow_natCast, ← zpow_add₀ hL]
    congr 1
    ring
  have hside : 𝒮.side = 2 * ((s.data.L : ℝ) ^ (s.data.m : ℕ) *
      (s.data.L : ℝ) ^ (((s.data.K : ℕ) : ℤ) - (s.data.t : ℤ))) := by
    rw [hs.side_eq, ← hp]
    rfl
  rw [rescaleFactor, hside, PeriodicLattice.torusSide]
  have h1 : (s.data.L : ℝ) ^ (s.data.m : ℕ) ≠ 0 := pow_ne_zero _ hL
  field_simp
theorem rescaleFactor_pos (hs : s.IsNestedRegions 𝒮) : 0 < rescaleFactor s 𝒮 := by
  rw [rescaleFactor_eq hs]
  exact zpow_pos blockFactor_pos _
theorem meshSize_mul_rescaleFactor (hs : s.IsNestedRegions 𝒮) (n : ℕ) :
    PeriodicLattice.meshSize s.data.L (PeriodicLattice.levelDepth s.data.cutoff n) * rescaleFactor s 𝒮 =
      𝒮.scale n := by
  have hL := (blockFactor_pos (s := s)).ne'
  have hξ : 𝒮.ξ = (s.data.L : ℝ) ^ (-(s.data.t : ℤ)) := hs.ξ_eq
  rw [rescaleFactor_eq hs, RegionSequence.NestedRegions.scale, Torus.scaleSpacing, hs.L_eq, hξ,
    PeriodicLattice.meshSize, ← zpow_add₀ hL, ← zpow_add₀ hL]
  congr 1
  simp only [PeriodicLattice.levelDepth]
  ring
theorem meshSize_zero_mul_rescaleFactor (hs : s.IsNestedRegions 𝒮) :
    PeriodicLattice.meshSize s.data.L (PeriodicLattice.levelDepth s.data.cutoff 0) * rescaleFactor s 𝒮 = 𝒮.ξ := by
  rw [meshSize_mul_rescaleFactor hs]
  simp [RegionSequence.NestedRegions.scale, Torus.scaleSpacing]
section Lattices
variable {n : ℕ} {σ : ℝ}
theorem rescale_lattice
    (hσ : PeriodicLattice.meshSize s.data.L (PeriodicLattice.levelDepth s.data.cutoff n) * rescaleFactor s 𝒮 = σ)
    (k : Fin 4 → ℤ) :
    torusRescale s 𝒮 (fun μ => (((k μ : ℝ) *
        PeriodicLattice.meshSize s.data.L (PeriodicLattice.levelDepth s.data.cutoff n) : ℝ) :
          AddCircle (PeriodicLattice.torusSide s.data.L s.data.m))) =
      Torus.torusProj 4 𝒮.side fun μ => (k μ : ℝ) * σ := by
  rw [rescale_coe]
  funext μ
  simp only [Torus.torusProj]
  rw [mul_assoc, hσ]
theorem exists_coords (x : s.data.LatticeSite n) : ∃ k : Fin 4 → ℤ, (x : s.data.Point) = fun μ =>
    (((k μ : ℝ) * PeriodicLattice.meshSize s.data.L (PeriodicLattice.levelDepth s.data.cutoff n) : ℝ) :
      AddCircle (PeriodicLattice.torusSide s.data.L s.data.m)) := by
  obtain ⟨k, hk⟩ := x.2
  exact ⟨k, funext hk⟩
theorem rescale_unitStep
    (hσ : PeriodicLattice.meshSize s.data.L (PeriodicLattice.levelDepth s.data.cutoff n) * rescaleFactor s 𝒮 = σ)
    (μ : Fin 4) :
    torusRescale s 𝒮 (PeriodicLattice.unitStep s.data.L s.data.m (PeriodicLattice.levelDepth s.data.cutoff n) μ :
        s.data.Point) =
      (Dirichlet.unitStep 4 𝒮.side σ μ : Torus.PeriodicTorus 4 𝒮.side) := by
  have h : (PeriodicLattice.unitStep s.data.L s.data.m (PeriodicLattice.levelDepth s.data.cutoff n) μ :
      s.data.Point) = fun ν =>
        ((((Pi.single μ (1 : ℤ) : Fin 4 → ℤ) ν : ℝ) *
          PeriodicLattice.meshSize s.data.L (PeriodicLattice.levelDepth s.data.cutoff n) : ℝ) :
            AddCircle (PeriodicLattice.torusSide s.data.L s.data.m)) := by
    funext ν
    by_cases hν : ν = μ
    · subst hν
      simp [PeriodicLattice.unitStep, PeriodicLattice.pointOnAxis]
    · simp [PeriodicLattice.unitStep, PeriodicLattice.pointOnAxis, Pi.single_eq_of_ne hν]
  rw [h, rescale_lattice hσ]
  funext ν
  by_cases hν : ν = μ
  · subst hν
    simp [Dirichlet.unitStep, Torus.torusProj]
  · simp [Dirichlet.unitStep, Torus.torusProj, Pi.single_eq_of_ne hν]
theorem meshSize_lt_torusSide (hn : n ≤ s.data.t) :
    PeriodicLattice.meshSize s.data.L (PeriodicLattice.levelDepth s.data.cutoff n) <
      PeriodicLattice.torusSide s.data.L s.data.m := by
  have hL1 : (1 : ℝ) ≤ s.data.L := by
    have := s.data.isAdmissible.2
    exact_mod_cast (by omega : 1 ≤ s.data.L)
  have ht := s.data.t_le_cutoff
  have h1 : PeriodicLattice.meshSize s.data.L (PeriodicLattice.levelDepth s.data.cutoff n) ≤ 1 := by
    rw [PeriodicLattice.meshSize]
    apply zpow_le_one_of_nonpos₀ hL1
    have hK : s.data.cutoff = (s.data.K : ℕ) := rfl
    simp only [PeriodicLattice.levelDepth, hK]
    omega
  have h2 : (1 : ℝ) ≤ (s.data.L : ℝ) ^ (s.data.m : ℕ) := one_le_pow₀ hL1
  rw [PeriodicLattice.torusSide]
  linarith
theorem meshSize_pos :
    0 < PeriodicLattice.meshSize s.data.L (PeriodicLattice.levelDepth s.data.cutoff n) :=
  zpow_pos blockFactor_pos _
theorem unitStep_injective (hs : s.IsNestedRegions 𝒮) (hn : n ≤ s.data.t)
    (hσ : PeriodicLattice.meshSize s.data.L (PeriodicLattice.levelDepth s.data.cutoff n) * rescaleFactor s 𝒮 = σ)
    {μ ν : Fin 4}
    (h : (Dirichlet.unitStep 4 𝒮.side σ μ : Torus.PeriodicTorus 4 𝒮.side) =
      Dirichlet.unitStep 4 𝒮.side σ ν) : μ = ν := by
  by_contra hne
  have hr := rescaleFactor_pos hs
  have hpos : 0 < σ := hσ ▸ mul_pos (meshSize_pos (s := s) (n := n)) hr
  have hlt : σ < 𝒮.side := by
    have h1 := mul_lt_mul_of_pos_right (meshSize_lt_torusSide hn) hr
    have h2 : PeriodicLattice.torusSide s.data.L s.data.m * rescaleFactor s 𝒮 = 𝒮.side := by
      rw [rescaleFactor]
      field_simp [s.torusSide_ne_zero]
    rw [hσ, h2] at h1
    exact h1
  have h0 := congrFun h μ
  simp only [Dirichlet.unitStep, Torus.torusProj, Pi.single_eq_same,
    Pi.single_eq_of_ne hne] at h0
  obtain ⟨k, hk⟩ := (AddCircle.coe_eq_zero_iff 𝒮.side).1 (h0.trans (by simp))
  rw [zsmul_eq_mul] at hk
  have h1 : (0 : ℝ) < k := by
    by_contra hc
    have hc' := not_lt.mp hc
    nlinarith
  have h2 : (k : ℝ) < 1 := by
    by_contra hc
    have hc' := not_lt.mp hc
    nlinarith
  have h3 : 0 < k := by exact_mod_cast h1
  have h4 : k < 1 := by exact_mod_cast h2
  omega
end Lattices
theorem supNormVec_eq_norm (w : Fin 4 → ℝ) : TorusMetric.supNormVec w = ‖w‖ := by apply _root_.YangMills.Construction.LevelUnitFacts.supNormVec_eq_norm <;> assumption
theorem supNorm_rescale (hs : s.IsNestedRegions 𝒮) (p : s.data.Point) :
    Torus.supNorm (torusRescale s 𝒮 p : Torus.PeriodicTorus 4 𝒮.side) =
      rescaleFactor s 𝒮 * TorusMetric.torusSupNorm p := by
  have hr := rescaleFactor_pos hs
  have hset : {r | ∃ v : Fin 4 → ℝ, Torus.torusProj 4 𝒮.side v = torusRescale s 𝒮 p ∧
      r = ‖v‖} = rescaleFactor s 𝒮 •
        (TorusMetric.supNormVec ''
          (TorusMetric.torusProj (PeriodicLattice.torusSide s.data.L s.data.m) ⁻¹' {p})) := by
    ext r
    constructor
    · rintro ⟨v, hv, rfl⟩
      refine Set.mem_smul_set.2 ⟨TorusMetric.supNormVec ((rescaleFactor s 𝒮)⁻¹ • v),
        ⟨_, ?_, rfl⟩, ?_⟩
      · apply (torusRescale s 𝒮).injective
        refine Eq.trans ?_ hv
        refine (rescale_coe s 𝒮 _).trans ?_
        funext μ
        simp only [Pi.smul_apply, smul_eq_mul, Torus.torusProj]
        rw [show (rescaleFactor s 𝒮)⁻¹ * v μ * rescaleFactor s 𝒮 = v μ by field_simp]
      · rw [supNormVec_eq_norm, norm_smul, smul_eq_mul, norm_inv, Real.norm_of_nonneg hr.le,
          mul_inv_cancel_left₀ hr.ne']
    · intro h
      obtain ⟨_, ⟨w, hw, rfl⟩, rfl⟩ := Set.mem_smul_set.1 h
      refine ⟨rescaleFactor s 𝒮 • w, ?_, ?_⟩
      · have hw' : TorusMetric.torusProj (PeriodicLattice.torusSide s.data.L s.data.m) w = p := hw
        rw [← hw']
        refine Eq.trans ?_ (rescale_coe s 𝒮 _).symm
        funext μ
        simp only [Pi.smul_apply, smul_eq_mul, Torus.torusProj]
        rw [mul_comm]
      · rw [supNormVec_eq_norm, norm_smul, smul_eq_mul, Real.norm_of_nonneg hr.le]
  simp only [Torus.supNorm, TorusMetric.torusSupNorm]
  rw [hset, Real.sInf_smul_of_nonneg hr.le]
  rfl
theorem mem_cubeAround_iff (hs : s.IsNestedRegions 𝒮) {n : ℕ} (y : s.data.LatticeSite n)
    (x : s.data.Point) :
    x ∈ PeriodicLattice.cubeAround y ↔ torusRescale s 𝒮 x ∈
      Torus.cubeAt (torusRescale s 𝒮 (y : s.data.Point)) (𝒮.scale n) := by
  change TorusMetric.torusSupNorm (x - (y : s.data.Point)) ≤ _ ↔
    Torus.supNorm (torusRescale s 𝒮 x - torusRescale s 𝒮 (y : s.data.Point)) ≤ _
  rw [← map_sub, supNorm_rescale hs, ← meshSize_mul_rescaleFactor hs]
  have hr := rescaleFactor_pos hs
  constructor
  · intro h
    have := mul_le_mul_of_nonneg_left h hr.le
    linarith
  · intro h
    refine le_of_mul_le_mul_left ?_ hr
    linarith
def SameEndpoints {n : ℕ} (b : s.params.LevelBond n) (c : 𝒮.BondAt n) : Prop :=
  torusRescale s 𝒮 (b.1.source : s.data.Point) = (c.source : 𝒮.Point) ∧
    torusRescale s 𝒮 (b.1.target : s.data.Point) = (c.target : 𝒮.Point)
theorem target_coe {n : ℕ} (b : s.params.LevelBond n) {μ : Fin 4}
    (hμ : b.1.target - b.1.source = PeriodicLattice.unitStep s.data.L s.data.m
      (PeriodicLattice.levelDepth s.data.cutoff n) μ) :
    (b.1.target : s.data.Point) = (b.1.source : s.data.Point) +
      (PeriodicLattice.unitStep s.data.L s.data.m (PeriodicLattice.levelDepth s.data.cutoff n) μ :
        s.data.Point) := by
  rw [← hμ]
  simp
theorem rescale_target (hs : s.IsNestedRegions 𝒮) {n : ℕ} (b : s.params.LevelBond n)
    {μ : Fin 4} (hμ : b.1.target - b.1.source = PeriodicLattice.unitStep s.data.L s.data.m
      (PeriodicLattice.levelDepth s.data.cutoff n) μ) :
    torusRescale s 𝒮 (b.1.target : s.data.Point) = torusRescale s 𝒮 (b.1.source : s.data.Point) +
      (Dirichlet.unitStep 4 𝒮.side (𝒮.scale n) μ : Torus.PeriodicTorus 4 𝒮.side) := by
  rw [target_coe b hμ, map_add, rescale_unitStep (meshSize_mul_rescaleFactor hs n)]
theorem dir_eq (hs : s.IsNestedRegions 𝒮) {n : ℕ} (hn : n ≤ s.data.t)
    {b : s.params.LevelBond n} {c : 𝒮.BondAt n} (h : SameEndpoints b c) {μ : Fin 4}
    (hμ : b.1.target - b.1.source = PeriodicLattice.unitStep s.data.L s.data.m
      (PeriodicLattice.levelDepth s.data.cutoff n) μ) : c.dir = μ := by
  refine unitStep_injective hs hn (meshSize_mul_rescaleFactor hs n) ?_
  have h1 := rescale_target hs b hμ
  rw [h.1, h.2] at h1
  exact add_left_cancel (a := (c.source : 𝒮.Point)) h1
theorem mem_bonds_iff (hs : s.IsNestedRegions 𝒮) {b : s.data.BareBond} {c : 𝒮.FineBond}
    (h1 : torusRescale s 𝒮 (b.1.source : s.data.Point) = (c.source : 𝒮.Point))
    (h2 : torusRescale s 𝒮 (b.1.target : s.data.Point) = (c.target : 𝒮.Point)) :
    c ∈ 𝒮.bonds ↔ b ∈ s.data.frameSet s.Ω s.frame := by
  have hinj := (torusRescale s 𝒮).injective
  rw [hs.bonds_iff c]
  constructor
  · rintro ⟨c', hc', he⟩
    change (s.toTorus 𝒮.side (c'.1.source : s.data.Point), s.toTorus 𝒮.side (c'.1.target : s.data.Point)) =
      ((c.source : 𝒮.Point), (c.target : 𝒮.Point)) at he
    rw [toTorus_eq_rescale, toTorus_eq_rescale, Prod.mk.injEq] at he
    obtain ⟨e1, e2⟩ := he
    have ht : (c'.1.source : s.data.Point) = (b.1.source : s.data.Point) :=
      hinj (e1.trans h1.symm)
    have hh : (c'.1.target : s.data.Point) = (b.1.target : s.data.Point) :=
      hinj (e2.trans h2.symm)
    have : c' = b := Subtype.ext (PeriodicLattice.Bond.ext (Subtype.ext ht) (Subtype.ext hh))
    exact this ▸ hc'
  · intro hb
    refine ⟨b, hb, ?_⟩
    change (s.toTorus 𝒮.side (b.1.source : s.data.Point), s.toTorus 𝒮.side (b.1.target : s.data.Point)) =
      ((c.source : 𝒮.Point), (c.target : 𝒮.Point))
    rw [toTorus_eq_rescale, toTorus_eq_rescale]
    exact Prod.ext h1 h2
theorem expansionRel_iff (n : ℕ) (b : s.params.LevelBond n)
    (hb : (⟨n, b⟩ : Σ n : ℕ, s.params.LevelBond n) ∈
      s.params.principalBonds s.Ω s.frame) (c : 𝒮.BondAt n)
    (hc : (⟨n, c⟩ : Σ n : ℕ, 𝒮.BondAt n) ∈ {c : Σ n : ℕ, 𝒮.BondAt n |
      c.1 ≤ 𝒮.s ∧ c.2 ∈ 𝒮.coarseBonds c.1}) :
    s.oneFormData.RowRel (oneFormDataOfNested 𝒮) (s.toTorus 𝒮.side) ⟨⟨n, b⟩, hb⟩ ⟨⟨n, c⟩, hc⟩ ↔
      SameEndpoints b c := by
  change (n, s.toTorus 𝒮.side (b.1.source : s.data.Point), s.toTorus 𝒮.side (b.1.target : s.data.Point)) =
    (n, (c.source : 𝒮.Point), (c.target : 𝒮.Point)) ↔ _
  simp only [toTorus_eq_rescale s 𝒮, Prod.mk.injEq, true_and]
  rfl
theorem bondRel_of {b : s.data.BareBond} {c : 𝒮.FineBond}
    (h1 : torusRescale s 𝒮 (b.1.source : s.data.Point) = (c.source : 𝒮.Point))
    (h2 : torusRescale s 𝒮 (b.1.target : s.data.Point) = (c.target : 𝒮.Point)) :
    s.oneFormData.BondRel (oneFormDataOfNested 𝒮) (s.toTorus 𝒮.side) b c := by
  change (s.toTorus 𝒮.side (b.1.source : s.data.Point), s.toTorus 𝒮.side (b.1.target : s.data.Point)) = _
  rw [toTorus_eq_rescale, toTorus_eq_rescale]
  exact Prod.ext h1 h2
theorem pathBond_succ (μ : Fin 4) (x : 𝒮.FineSite) (i : ℕ) :
    RegionSequence.NestedRegions.pathBond μ x (i + 1) =
      RegionSequence.NestedRegions.pathBond μ (x + Dirichlet.unitStep 4 𝒮.side 𝒮.ξ μ) i := by
  simp only [RegionSequence.NestedRegions.pathBond]
  congr 1
  rw [add_nsmul, one_nsmul]
  abel
theorem lineSum_forwardFlow (hs : s.IsNestedRegions 𝒮) {A : s.data.BondFn} {B : 𝒮.FineBond → ℝ}
    (hAB : AgreeAlong (s.oneFormData.BondRel (oneFormDataOfNested 𝒮) (s.toTorus 𝒮.side)) A B)
    (μ : Fin 4) (N : ℕ) : ∀ (x : s.data.BareSite) (x' : 𝒮.FineSite),
      torusRescale s 𝒮 (x : s.data.Point) = (x' : 𝒮.Point) →
      lineSum A (PeriodicLattice.forwardAxisPath x μ N) =
        ∑ i ∈ Finset.range N, B (RegionSequence.NestedRegions.pathBond μ x' i) := by
  induction N with
  | zero =>
    intro x x' _
    simp [lineSum, PeriodicLattice.forwardAxisPath]
  | succ N ih =>
    intro x x' hx
    have hstep := rescale_unitStep (n := 0) (meshSize_zero_mul_rescaleFactor hs) μ
    have hnext : torusRescale s 𝒮 ((x + PeriodicLattice.unitStep s.data.L s.data.m
        (PeriodicLattice.levelDepth s.data.cutoff 0) μ : s.data.BareSite) : s.data.Point) =
        ((x' + Dirichlet.unitStep 4 𝒮.side 𝒮.ξ μ : 𝒮.FineSite) : 𝒮.Point) := by
      rw [AddSubgroup.coe_add, map_add, hx, hstep, AddSubgroup.coe_add]
    have hpos : (PeriodicLattice.Bond.forwardFrom x μ).IsPositivelyOriented := ⟨μ, by
      simp [PeriodicLattice.Bond.forwardFrom]⟩
    have hfirst : orientedValue A (PeriodicLattice.Bond.forwardFrom x μ) =
        B (RegionSequence.NestedRegions.pathBond μ x' 0) := by
      rw [orientedValue, dif_pos hpos]
      refine hAB _ _ (bondRel_of ?_ ?_)
      · simpa [RegionSequence.NestedRegions.pathBond, PeriodicLattice.Bond.forwardFrom] using hx
      · refine hnext.trans ?_
        simp [RegionSequence.NestedRegions.pathBond, Dirichlet.LatticeBond.target]
    have hcons : lineSum A (PeriodicLattice.forwardAxisPath x μ (N + 1)) =
        orientedValue A (PeriodicLattice.Bond.forwardFrom x μ) + lineSum A
          (PeriodicLattice.forwardAxisPath (x + PeriodicLattice.unitStep s.data.L s.data.m
            (PeriodicLattice.levelDepth s.data.cutoff 0) μ) μ N) := by
      simp [lineSum, PeriodicLattice.forwardAxisPath]
    rw [hcons, hfirst, ih _ _ hnext, Finset.sum_range_succ', add_comm]
    simp only [pathBond_succ]
theorem extendByZero_of_mem {X Y : Type} (E : Submodule ℝ (X → ℝ)) (T : ↥E → Y → ℝ) {f : X → ℝ}
    (h : f ∈ E) : extendByZero E T f = T ⟨f, h⟩ := dif_pos h
end YangMills.Construction.SeparatedClasses.SingleSequence.NestedRescale
