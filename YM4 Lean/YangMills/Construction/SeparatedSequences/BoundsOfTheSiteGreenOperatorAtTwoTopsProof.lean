import YangMills.Construction.DirichletOperator.AveragingOperatorsAgreeOnTheLocalTorusProof
import YangMills.Construction.DirichletOperator.FactsOfTheSettingInLevelUnitsProof
import YangMills.Construction.SeparatedSequences.ChosenConstantsOfTheConditions
import YangMills.Construction.SeparatedSequences.ClassSiteFunctionsInASettingOfTheTorusOfLevelSideProof
import YangMills.Construction.SeparatedSequences.OneSequenceOneSetOfObjects
import Mathlib
set_option autoImplicit false
namespace YangMills.Construction
open Set PeriodicLattice PeriodicLattice.DirichletOperators TorusMetric
open scoped Pointwise
noncomputable section
namespace SeparatedClasses
namespace ApexGreen
open SingleSequence SingleSequence.SequenceData
section EvaluationMaps
variable (s : SequenceData)
theorem Lreal_pos : (0 : ℝ) < s.Lreal := by apply _root_.YangMills.Construction.SeparatedClasses.BlockSettingScalarData.Lreal_pos <;> assumption
theorem one_lt_Lreal : (1 : ℝ) < s.Lreal := by apply _root_.YangMills.Construction.SeparatedClasses.BlockSettingScalarData.one_lt_Lreal <;> assumption
theorem unitTorusSide_ne_zero : s.unitTorusSide ≠ 0 := by apply _root_.YangMills.Construction.SeparatedClasses.BlockSettingScalarData.unitTorusSide_ne_zero <;> assumption
theorem toTorus_apply (x : s.data.Point) (μ : Fin 4) :
    s.toTorus s.unitTorusSide x μ =
      AddCircle.equivAddCircle _ s.unitTorusSide s.torusSide_ne_zero (unitTorusSide_ne_zero s)
        (x μ) := by
  simp only [SequenceData.toTorus, dif_pos (unitTorusSide_ne_zero s)]
theorem toTorus_injective : Function.Injective (s.toTorus s.unitTorusSide) := by apply _root_.YangMills.Construction.SeparatedClasses.BlockSettingScalarData.toTorus_injective <;> assumption
theorem toTorus_sub (x y : s.data.Point) :
    s.toTorus s.unitTorusSide (x - y) =
      s.toTorus s.unitTorusSide x - s.toTorus s.unitTorusSide y := by apply _root_.YangMills.Construction.SeparatedClasses.BlockSettingScalarData.toTorus_sub <;> assumption
theorem toTorus_add (x y : s.data.Point) :
    s.toTorus s.unitTorusSide (x + y) =
      s.toTorus s.unitTorusSide x + s.toTorus s.unitTorusSide y := by apply _root_.YangMills.Construction.SeparatedClasses.BlockSettingScalarData.toTorus_add <;> assumption
def scaleFactor : ℝ := (PeriodicLattice.torusSide s.data.L s.data.m)⁻¹ * s.unitTorusSide
theorem scaleFactor_eq : scaleFactor s = s.Lreal ^ levelDepth s.data.cutoff s.data.t := by
  have hL := (Lreal_pos s).ne'
  simp only [scaleFactor, SequenceData.unitTorusSide, Torus.unitSide,
    PeriodicLattice.torusSide, levelDepth]
  have hL' : ((s.data.L : ℕ) : ℝ) ≠ 0 := hL
  rw [show ((s.data.m : ℕ) : ℤ) + ((s.data.cutoff : ℕ) : ℤ) - ((s.data.t : ℕ) : ℤ) =
    ((s.data.m : ℕ) : ℤ) + (((s.data.cutoff : ℕ) : ℤ) - ((s.data.t : ℕ) : ℤ)) by ring,
    zpow_add₀ hL', zpow_natCast]
  have h2 : ((s.data.L : ℝ) ^ (s.data.m : ℕ)) ≠ 0 := pow_ne_zero _ hL'
  field_simp
theorem scaleFactor_pos : 0 < scaleFactor s := by
  rw [scaleFactor_eq]
  exact zpow_pos (Lreal_pos s) _
theorem toTorus_torusProj (v : Fin 4 → ℝ) :
    s.toTorus s.unitTorusSide (TorusMetric.torusProj (PeriodicLattice.torusSide s.data.L s.data.m) v) =
      Torus.torusProj 4 s.unitTorusSide fun μ => v μ * scaleFactor s := by
  funext μ
  rw [toTorus_apply]
  simp only [TorusMetric.torusProj, Torus.torusProj]
  rw [AddCircle.equivAddCircle_apply_mk]
  rfl
theorem supNormVec_eq_norm (w : Fin 4 → ℝ) : TorusMetric.supNormVec w = ‖w‖ := by apply _root_.YangMills.Construction.LevelUnitFacts.supNormVec_eq_norm <;> assumption
end EvaluationMaps
theorem supNorm_eq_norm {S : ℝ} (x : Torus.PeriodicTorus 4 S) :
    Torus.supNorm x = ‖x‖ := by apply _root_.YangMills.Construction.PartitionCubes.CubeTorusAveraging.supNorm_eq_norm <;> assumption
section Setting
variable {s : SequenceData} {𝒮 : s.BlockSettingType}
theorem toTorus_unitStep (h : s.IsBlockSetting 𝒮) (μ : Fin 4) :
    s.toTorus s.unitTorusSide ((unitStep s.data.L s.data.m (levelDepth s.data.cutoff 0) μ :
        Site s.data.L s.data.m (levelDepth s.data.cutoff 0)) : s.data.Point) =
      ((Dirichlet.unitStep 4 s.unitTorusSide 𝒮.ξ μ : Dirichlet.LatticeSite 4 s.unitTorusSide 𝒮.ξ) :
        Torus4 s.unitTorusSide) := by apply _root_.YangMills.Construction.SeparatedClasses.BlockSettingScalarData.toTorus_unitStep <;> assumption
theorem mem_zeroFormsOn {Ω₀ : Set s.data.Point} {f : s.data.SiteFn} :
    f ∈ zeroFormsOn s.data.cutoff Ω₀ ↔
      ∀ x : s.data.BareSite, (x : s.data.Point) ∉ Ω₀ → f x = 0 := by apply _root_.YangMills.Construction.SeparatedClasses.BlockSettingScalarData.mem_zeroFormsOn_iff <;> assumption
theorem image_sublattice (g : s.BlockSettingGeometry 𝒮) :
    s.toTorus s.unitTorusSide '' (PeriodicLattice.sublattice s.data.L s.data.m
        (levelDepth s.data.cutoff 0) : Set s.data.Point) =
      (Torus.spacingLattice 4 s.unitTorusSide 𝒮.ξ : Set (Torus4 s.unitTorusSide)) := by apply _root_.YangMills.Construction.SeparatedClasses.BlockSettingScalarData.image_sublattice <;> assumption
def latticeSiteEquiv (g : s.BlockSettingGeometry 𝒮) :
    s.data.BareSite ≃ Dirichlet.LatticeSite 4 s.unitTorusSide 𝒮.ξ :=
  Equiv.ofBijective
    (fun x => ⟨s.toTorus s.unitTorusSide (x : s.data.Point), by
      have : s.toTorus s.unitTorusSide (x : s.data.Point) ∈
          (Torus.spacingLattice 4 s.unitTorusSide 𝒮.ξ : Set (Torus4 s.unitTorusSide)) := by
        rw [← image_sublattice g]
        exact ⟨x, x.2, rfl⟩
      exact this⟩)
    ⟨fun x y hxy => Subtype.ext (toTorus_injective s (congrArg Subtype.val hxy)), fun x' => by
      have : (x' : Torus4 s.unitTorusSide) ∈
          s.toTorus s.unitTorusSide '' (PeriodicLattice.sublattice s.data.L s.data.m
            (levelDepth s.data.cutoff 0) : Set s.data.Point) := by
        rw [image_sublattice g]
        exact x'.2
      obtain ⟨x, hx, hxx⟩ := this
      exact ⟨⟨x, hx⟩, Subtype.ext hxx⟩⟩
theorem coe_latticeSiteEquiv (g : s.BlockSettingGeometry 𝒮) (x : s.data.BareSite) :
    ((latticeSiteEquiv g x : Dirichlet.LatticeSite 4 s.unitTorusSide 𝒮.ξ) :
      Torus4 s.unitTorusSide) = s.toTorus s.unitTorusSide (x : s.data.Point) := rfl
theorem latticeSiteEquiv_mem_iff (h : s.IsBlockSetting 𝒮) (g : s.BlockSettingGeometry 𝒮)
    (x : s.data.BareSite) :
    ((latticeSiteEquiv g x : Dirichlet.LatticeSite 4 s.unitTorusSide 𝒮.ξ) :
        Torus4 s.unitTorusSide) ∈ 𝒮.Ω 0 ↔
      (x : s.data.Point) ∈ s.Ω 0 := by
  rw [coe_latticeSiteEquiv, h.Ω_eq 0]
  exact (toTorus_injective s).mem_set_image
theorem siteRel_iff (g : s.BlockSettingGeometry 𝒮) (x : s.data.BareSite)
    (x' : Dirichlet.LatticeSite 4 s.unitTorusSide 𝒮.ξ) :
    s.scalarData.SiteRel (scalarDataOfBlockSetting 𝒮) (s.toTorus s.unitTorusSide) x x' ↔
      x' = latticeSiteEquiv g x := by
  constructor
  · intro hx
    exact Subtype.ext hx.symm
  · rintro rfl
    rfl
theorem vanishesOff_iff (h : s.IsBlockSetting 𝒮) (g : s.BlockSettingGeometry 𝒮)
    (f' : Dirichlet.LatticeSite 4 s.unitTorusSide 𝒮.ξ → ℝ) :
    Dirichlet.VanishesOff (𝒮.Ω 0) f' ↔
      (f' ∘ latticeSiteEquiv g) ∈ zeroFormsOn s.data.cutoff (s.Ω 0) := by
  rw [mem_zeroFormsOn]
  constructor
  · intro hf x hx
    exact hf _ (fun hm => hx ((latticeSiteEquiv_mem_iff h g x).1 hm))
  · intro hf x' hx'
    obtain ⟨x, rfl⟩ := (latticeSiteEquiv g).surjective x'
    exact hf x (fun hm => hx' ((latticeSiteEquiv_mem_iff h g x).2 hm))
def pushSite (g : s.BlockSettingGeometry 𝒮) (f : s.data.SiteFn) :
    Dirichlet.LatticeSite 4 s.unitTorusSide 𝒮.ξ → ℝ := f ∘ (latticeSiteEquiv g).symm
@[simp] theorem pushSite_apply (g : s.BlockSettingGeometry 𝒮) (f : s.data.SiteFn)
    (x : s.data.BareSite) : pushSite g f (latticeSiteEquiv g x) = f x := by
  simp [pushSite]
def pushBond (g : s.BlockSettingGeometry 𝒮) (lam : s.data.BondFn) :
    Dirichlet.BondField 4 s.unitTorusSide 𝒮.ξ :=
  fun μ x' => lam (bondFrom ((latticeSiteEquiv g).symm x') μ)
@[simp] theorem pushBond_apply (g : s.BlockSettingGeometry 𝒮) (lam : s.data.BondFn)
    (μ : Fin 4) (x : s.data.BareSite) :
    pushBond g lam μ (latticeSiteEquiv g x) = lam (bondFrom x μ) := by
  simp [pushBond]
end Setting
section Seminorms
variable {s : SequenceData} {𝒮 : s.BlockSettingType}
theorem finite_bareSite (C : ClassData) : Finite C.BareSite :=
  C.unitSpacingParameters.instFiniteLatticeSite 0
theorem finite_latticeSite (g : s.BlockSettingGeometry 𝒮) :
    Finite (Dirichlet.LatticeSite 4 s.unitTorusSide 𝒮.ξ) :=
  have := finite_bareSite s.data
  Finite.of_equiv _ (latticeSiteEquiv g)
theorem supNormAll_nonneg {ξ : ℝ} (f : Dirichlet.LatticeSite 4 s.unitTorusSide ξ → ℝ) :
    0 ≤ Dirichlet.supNormAll f := by
  refine Real.sSup_nonneg ?_
  rintro _ ⟨x, -, rfl⟩
  exact abs_nonneg _
theorem fieldSupNorm_nonneg {ξ : ℝ} (F : Dirichlet.BondField 4 s.unitTorusSide ξ) :
    0 ≤ Dirichlet.fieldSupNorm F :=
  Real.iSup_nonneg fun _ => supNormAll_nonneg _
theorem scaledHolderSeminorm_nonneg {ξ α l : ℝ}
    (D : Dirichlet.LatticeSite 4 s.unitTorusSide ξ → ℝ) :
    0 ≤ Dirichlet.scaledHolderSeminorm α l D := by
  refine Real.sSup_nonneg ?_
  rintro _ ⟨x, x', h0, h1, rfl⟩
  exact mul_nonneg (Real.rpow_nonneg (div_nonneg (h0.le.trans h1) h0.le) _) (abs_nonneg _)
end Seminorms
section Apexes
variable {s : SequenceData} {𝒮 : s.BlockSettingType}
theorem apex_mem_centres (g : s.BlockSettingGeometry 𝒮) (y : s.data.Apex s.Ω) :
    s.toTorus s.unitTorusSide y.point ∈ 𝒮.centres := by
  rw [← g.allLayerSites]
  exact ⟨y.point, y.point_mem_allLayerPoints, rfl⟩
theorem centreSpacing_apex (g : s.BlockSettingGeometry 𝒮) (y : s.data.Apex s.Ω) :
    𝒮.centreSpacing (s.toTorus s.unitTorusSide y.point) = y.mesh := g.meshes y
theorem mesh_pos (y : s.data.Apex s.Ω) : 0 < y.mesh := zpow_pos (Lreal_pos s) _
theorem norm_unitStep_le (μ : Fin 4) :
    ‖((Dirichlet.unitStep 4 s.unitTorusSide 𝒮.ξ μ : Dirichlet.LatticeSite 4 s.unitTorusSide 𝒮.ξ) :
      Torus4 s.unitTorusSide)‖ ≤ 𝒮.ξ := by
  have hξ : 0 < 𝒮.ξ := 𝒮.isSeparatedChain.scale_pos
  have e := supNorm_eq_norm (S := s.unitTorusSide)
    ((Dirichlet.unitStep 4 s.unitTorusSide 𝒮.ξ μ : Dirichlet.LatticeSite 4 s.unitTorusSide 𝒮.ξ) :
      Torus.PeriodicTorus 4 s.unitTorusSide)
  refine e.symm.le.trans ?_
  have h1 : Torus.supNorm ((Dirichlet.unitStep 4 s.unitTorusSide 𝒮.ξ μ :
      Dirichlet.LatticeSite 4 s.unitTorusSide 𝒮.ξ) : Torus.PeriodicTorus 4 s.unitTorusSide) ≤
      ‖(Pi.single μ 𝒮.ξ : Fin 4 → ℝ)‖ := by
    refine csInf_le ⟨0, ?_⟩ ⟨Pi.single μ 𝒮.ξ, rfl, rfl⟩
    rintro _ ⟨v, -, rfl⟩
    exact norm_nonneg v
  refine h1.trans ?_
  · refine (pi_norm_le_iff_of_nonneg hξ.le).2 fun ν => ?_
    by_cases hν : ν = μ
    · subst hν
      simp [abs_of_pos hξ]
    · simp [Pi.single_eq_of_ne hν, hξ.le]
theorem blockDist_nonneg {L : ℕ} {aMinus aPlus S : ℝ} (hL : 0 < L)
    (𝒮 : Dirichlet.BlockSetting 4 L aMinus aPlus S) (hξ : 0 < 𝒮.ξ)
    (p q : Torus.PeriodicTorus 4 S) : 0 ≤ 𝒮.blockDist p q := by
  refine Real.sInf_nonneg ?_
  rintro _ ⟨Γ, -, -, -, rfl⟩
  have hlen : ∀ X : Set (Torus.PeriodicTorus 4 S), 0 ≤ Torus.lengthWithin Γ X := by
    intro X
    refine List.sum_nonneg fun r hr => ?_
    obtain ⟨s, -, rfl⟩ := List.mem_map.1 hr
    exact mul_nonneg (Finset.sum_nonneg fun _ _ => abs_nonneg _) ENNReal.toReal_nonneg
  have hsp : ∀ n : ℤ, 0 < Torus.scaleSpacing L 𝒮.ξ n := fun n =>
    mul_pos (zpow_pos (by exact_mod_cast hL) n) hξ
  refine add_nonneg (Finset.sum_nonneg fun n _ => ?_) ?_
  · exact mul_nonneg (inv_nonneg.2 (hsp _).le) (hlen _)
  · exact mul_nonneg (inv_nonneg.2 (hsp _).le) (hlen _)
theorem expDecay_eq (g : s.BlockSettingGeometry 𝒮) (κ : ℝ) (y y' : s.data.Apex s.Ω) :
    DirichletGreen.GreenConstants.expDecay 𝒮 κ (s.toTorus s.unitTorusSide y.point)
        (s.toTorus s.unitTorusSide y'.point) =
      ClassData.expDecay κ y y' := by
  have hL : 0 < s.data.L := by
    have := s.data.isAdmissible.2
    omega
  simp only [DirichletGreen.GreenConstants.expDecay, ClassData.expDecay]
  rw [← g.distances y.point y'.point,
    ENNReal.toReal_ofReal (blockDist_nonneg hL 𝒮 𝒮.isSeparatedChain.scale_pos _ _)]
end Apexes
section Bounds
variable {s : SequenceData} {𝒮 : s.BlockSettingType}
  (h : s.IsBlockSetting 𝒮) (g : s.BlockSettingGeometry 𝒮)
  {c : DirichletGreen.GreenConstants} (hb : c.PointBounds 𝒮) (hfl : c.LargeEnough 𝒮)
theorem abs_le_fieldModulusAt (g' : Dirichlet.BondField 4 s.unitTorusSide 𝒮.ξ)
    (x : Dirichlet.LatticeSite 4 s.unitTorusSide 𝒮.ξ) (μ : Fin 4) :
    |g' μ x| ≤ DirichletGreen.fieldModulusAt g' x :=
  le_ciSup (f := fun μ => |g' μ x|) (Set.finite_range _).bddAbove μ
include g hb hfl in
theorem B_nonneg (y : s.data.Apex s.Ω) : 0 ≤ c.B := by
  classical
  have hle : levelDepth s.data.cutoff y.level ≤ levelDepth s.data.cutoff 0 := by
    simp only [levelDepth]
    omega
  have hLn : 0 < s.data.L := by
    have := s.data.isAdmissible.2
    omega
  let x₀ : s.data.BareSite := ⟨y.site.1, sublattice_mono hLn s.data.m hle y.site.2⟩
  have hp : ((latticeSiteEquiv g x₀ : Dirichlet.LatticeSite 4 s.unitTorusSide 𝒮.ξ) :
      Torus4 s.unitTorusSide) = s.toTorus s.unitTorusSide y.point := rfl
  have hy := mesh_pos y
  have hzero : Torus.supNorm (((latticeSiteEquiv g x₀ :
      Dirichlet.LatticeSite 4 s.unitTorusSide 𝒮.ξ) : Torus4 s.unitTorusSide) -
        s.toTorus s.unitTorusSide y.point) = 0 := by
    rw [hp, sub_self, supNorm_eq_norm, norm_zero]
  have hmem : ((latticeSiteEquiv g x₀ : Dirichlet.LatticeSite 4 s.unitTorusSide 𝒮.ξ) :
      Torus4 s.unitTorusSide) ∈ 𝒮.cell (s.toTorus s.unitTorusSide y.point) := by
    change Torus.supNorm _ ≤ 𝒮.centreSpacing (s.toTorus s.unitTorusSide y.point) / 2
    rw [hzero, centreSpacing_apex g y]
    positivity
  let f : Dirichlet.LatticeSite 4 s.unitTorusSide 𝒮.ξ → ℝ := Pi.single (latticeSiteEquiv g x₀) 1
  have hf : Dirichlet.VanishesOff (𝒮.cell (s.toTorus s.unitTorusSide y.point)) f := by
    intro x hx
    refine Pi.single_eq_of_ne ?_ _
    rintro rfl
    exact hx hmem
  have hT : DirichletGreen.IsAdmissibleData 𝒮 (s.toTorus s.unitTorusSide y.point)
      (s.toTorus s.unitTorusSide y.point) f 0 0 :=
    ⟨apex_mem_centres g y, apex_mem_centres g y, hf, fun _ _ _ => rfl, fun _ _ => rfl⟩
  have h1 := (hb.at_sites hfl _ _ f 0 0 hT (latticeSiteEquiv g x₀)
    (by rw [hzero, centreSpacing_apex g y]; positivity)).1
  rw [centreSpacing_apex g y, expDecay_eq g] at h1
  have hA : 1 ≤ Dirichlet.supNormAll f := by
    have := finite_latticeSite g
    have h2 : BddAbove {r | ∃ x : Dirichlet.LatticeSite 4 s.unitTorusSide 𝒮.ξ,
        (x : Torus4 s.unitTorusSide) ∈ (Set.univ : Set (Torus.PeriodicTorus 4 s.unitTorusSide)) ∧
          r = |f x|} :=
      ((Set.finite_range fun x => |f x|).subset (by
        rintro _ ⟨x, -, rfl⟩
        exact ⟨x, rfl⟩)).bddAbove
    have h3 := le_csSup h2 ⟨latticeSiteEquiv g x₀, Set.mem_univ _, rfl⟩
    have h4 : f (latticeSiteEquiv g x₀) = 1 := Pi.single_eq_same _ _
    rw [h4, abs_one] at h3
    exact h3
  by_contra hneg
  have hc : c.B < 0 := not_le.mp hneg
  have hE : 0 < ClassData.expDecay (c.δ₀ / 2) y y := Real.exp_pos _
  have h4 : c.B * y.mesh ^ 2 * ClassData.expDecay (c.δ₀ / 2) y y * Dirichlet.supNormAll f < 0 :=
    mul_neg_of_neg_of_pos (mul_neg_of_neg_of_pos (mul_neg_of_neg_of_pos hc (by positivity)) hE)
      (by linarith)
  exact absurd ((abs_nonneg _).trans h1) (not_le.mpr h4)
end Bounds
section Members
variable {s : SequenceData} {𝒮 : s.BlockSettingType}
end Members
end ApexGreen
end SeparatedClasses
end
end YangMills.Construction
