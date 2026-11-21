import YangMills.Construction.Continuum.MomentFunctionalsOnSymbols
import YangMills.Construction.GrowingTori.InducedIsometriesNestedLatticesAndTheMirrorsOfATorus
import Mathlib
set_option autoImplicit false
open YangMills.Construction.TorusMetric YangMills.Construction.TorusTransport YangMills.Construction.TimeAxisSymbols
noncomputable section
namespace YangMills.Construction.GrowingTori.LatticeMotions
theorem affineMotions_isGroup_holds : affineMotions_isGroup := by
  refine ⟨⟨1, 0, funext fun x => ?_⟩, ?_, ?_, fun a => ⟨1, a, funext fun x => rfl⟩,
    coe_mem_affineHyperoctahedral, hyperplaneReflect_mem_affineHyperoctahedral⟩
  · simp [affinePair]
  · rintro _ ⟨g, t, rfl⟩ _ ⟨g', t', rfl⟩
    refine ⟨g * g', g.1 t' + t, funext fun x => ?_⟩
    have hadd := map_add (hyperoctahedralLinear g) (g'.1 x) t'
    simp only [coe_hyperoctahedralLinear] at hadd
    simp only [Function.comp, affinePair, hadd, add_assoc]
    rfl
  · rintro _ ⟨g, t, rfl⟩
    refine ⟨affinePair (-(g⁻¹ : hyperoctahedral).1 t) g⁻¹, ⟨g⁻¹, _, rfl⟩, funext fun x => ?_,
      funext fun x => ?_⟩
    · have hadd := map_add (hyperoctahedralLinear g) ((g⁻¹ : hyperoctahedral).1 x)
        (-(g⁻¹ : hyperoctahedral).1 t)
      have hneg := map_neg (hyperoctahedralLinear g) ((g⁻¹ : hyperoctahedral).1 t)
      simp only [coe_hyperoctahedralLinear] at hadd hneg
      have hinv : ∀ y, g.1 ((g⁻¹ : hyperoctahedral).1 y) = y := fun y => by
        change (g * g⁻¹ : hyperoctahedral).1 y = y
        simp
      simp only [Function.comp, affinePair, hadd, hneg, hinv]
      simp
    · have hadd := map_add (hyperoctahedralLinear (g⁻¹ : hyperoctahedral)) (g.1 x) t
      simp only [coe_hyperoctahedralLinear] at hadd
      have hinv : (g⁻¹ : hyperoctahedral).1 (g.1 x) = x := by
        change (g⁻¹ * g : hyperoctahedral).1 x = x
        simp
      simp only [Function.comp, affinePair, hadd, hinv]
      simp
theorem euclidNormVec_hyperoctahedral (g : hyperoctahedral) (z : Fin 4 → ℝ) :
    euclidNormVec (g.1 z) = euclidNormVec z := by
  obtain ⟨_, σ, ε, rfl⟩ := g
  simp only [euclidNormVec]
  congr 1
  have hsq : ∀ i, (TorusLifts.signedCoordinateEquiv σ ε z i) ^ 2 = z (σ i) ^ 2 := fun i => by
    rw [signedCoordinateEquiv_apply, mul_pow]
    rcases Int.units_eq_one_or (ε i) with hε | hε <;> simp [hε]
  simp only [hsq]
  exact Equiv.sum_comp σ fun i => z i ^ 2
theorem torusProj_hyperoctahedral_eq (r : ℝ) (g : hyperoctahedral) {x y : Fin 4 → ℝ}
    (hxy : torusProj r x = torusProj r y) : torusProj r (g.1 x) = torusProj r (g.1 y) := by
  have hproj := fun z => TorusPeriodization.torusMotion_torusProj r
    ⟨g.1, hyperoctahedral_le_euclideanMotions g.2⟩ z
  simp only at hproj
  rw [← hproj, ← hproj, hxy]
theorem liftNorms_subset (r : ℝ) (g : hyperoctahedral) (z : Fin 4 → ℝ) :
    euclidNormVec '' (torusProj r ⁻¹' {torusProj r z}) ⊆
      euclidNormVec '' (torusProj r ⁻¹' {torusProj r (g.1 z)}) := by
  rintro _ ⟨t, ht, rfl⟩
  exact ⟨g.1 t, torusProj_hyperoctahedral_eq r g ht, euclidNormVec_hyperoctahedral g t⟩
theorem torusEuclidNorm_torusProj_hyperoctahedral (r : ℝ) (g : hyperoctahedral)
    (z : Fin 4 → ℝ) :
    torusEuclidNorm (torusProj r (g.1 z)) = torusEuclidNorm (torusProj r z) := by
  have hinv : (g⁻¹ : hyperoctahedral).1 (g.1 z) = z := by
    change (g⁻¹ * g : hyperoctahedral).1 z = z
    simp
  have hsub := liftNorms_subset r g⁻¹ (g.1 z)
  rw [hinv] at hsub
  simp only [torusEuclidNorm]
  rw [Set.Subset.antisymm hsub (liftNorms_subset r g z)]
theorem periodicMotion_isIsometry_holds (L : ℕ) : periodicMotion_isIsometry L := by
  intro s m
  refine ⟨⟨periodicMotion L m s,
      periodicMotion_comp_torusProj L m s,
      fun Φ hΦ => eq_periodicMotion hΦ⟩,
    (periodicMotion L m s).bijective, fun u v => ?_⟩
  obtain ⟨x, rfl⟩ := TestFunctions.torusProj_surjective _ u
  obtain ⟨y, rfl⟩ := TestFunctions.torusProj_surjective _ v
  obtain ⟨A, hA, b, hb⟩ := (SourcesAndGluing.mem_euclideanMotions_iff _).1 s.2
  have hcomp := fun z => congrFun (periodicMotion_comp_torusProj L m s) z
  simp only [Function.comp] at hcomp
  rw [hcomp, hcomp]
  have hdiff : ∀ p q : Fin 4 → ℝ, torusProj (PeriodicLattice.torusSide L m) p -
      torusProj (PeriodicLattice.torusSide L m) q =
        torusProj (PeriodicLattice.torusSide L m) (p - q) :=
    fun p q => rfl
  have hlin := map_sub (hyperoctahedralLinear ⟨A, hA⟩) x y
  simp only [coe_hyperoctahedralLinear] at hlin
  rw [hdiff, hdiff, hb x, hb y, add_sub_add_right_eq_sub, ← hlin]
  exact torusEuclidNorm_torusProj_hyperoctahedral _ ⟨A, hA⟩ _
theorem meshLattices_nested_holds (L : ℕ) (hL : L ≠ 0) : meshLattices_nested L := by
  rintro j K hjK _ ⟨n, rfl⟩
  have hLr : (L : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hL
  obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le (PNat.coe_le_coe _ _ |>.2 hjK)
  refine ⟨n * (L : ℤ) ^ d, ?_⟩
  simp only [PeriodicLattice.meshSize, hd]
  push_cast
  rw [neg_add, zpow_add₀ hLr, zpow_neg (L : ℝ) (d : ℤ), zpow_natCast]
  have : (L : ℝ) ^ d ≠ 0 := pow_ne_zero _ hLr
  field_simp
theorem adicGridPoints_dense_holds (L : ℕ) (hL : 2 ≤ L) : adicGridPoints_dense L := by
  have hL1 : (1 : ℝ) < L := by exact_mod_cast (by omega : 1 < L)
  have hL0 : (0 : ℝ) < L := by linarith
  refine Metric.dense_iff.2 fun x ε hε => ?_
  obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one hε (inv_lt_one_of_one_lt₀ hL1)
  have hk' : ((L : ℝ) ^ (k + 1))⁻¹ < ε := by
    refine lt_of_le_of_lt ?_ hk
    rw [← inv_pow]
    exact pow_le_pow_of_le_one (inv_nonneg.2 hL0.le) (inv_le_one_of_one_le₀ hL1.le) k.le_succ
  have hpos : (0 : ℝ) < (L : ℝ) ^ (k + 1) := pow_pos hL0 _
  refine ⟨(⌊x * (L : ℝ) ^ (k + 1)⌋ : ℝ) * ((L : ℝ) ^ (k + 1))⁻¹, ?_, ?_⟩
  · rw [Metric.mem_ball, Real.dist_eq, abs_sub_comm]
    have hfl := Int.floor_le (x * (L : ℝ) ^ (k + 1))
    have hlt := Int.lt_floor_add_one (x * (L : ℝ) ^ (k + 1))
    have hx : x = x * (L : ℝ) ^ (k + 1) * ((L : ℝ) ^ (k + 1))⁻¹ := by field_simp
    have hinv : 0 < ((L : ℝ) ^ (k + 1))⁻¹ := inv_pos.2 hpos
    rw [abs_lt]
    constructor
    · nlinarith
    · nlinarith
  · refine (PeriodicLattice.mem_adicGridPointsPositive_iff L _).2
      ⟨⟨k + 1, k.succ_pos⟩, ⌊x * (L : ℝ) ^ (k + 1)⌋, ?_⟩
    simp only [PeriodicLattice.meshSize, PNat.mk_coe]
    rw [zpow_neg, zpow_natCast]
theorem timeAxisStabilizer_isSubgroup_holds : timeAxisStabilizer_isSubgroup :=
  ⟨timeAxisStabilizer.one_mem,
    fun g g' hg hg' => timeAxisStabilizer.mul_mem ((mem_timeAxisStabilizer_iff g).2 hg)
      ((mem_timeAxisStabilizer_iff g').2 hg'),
    fun g hg => timeAxisStabilizer.inv_mem ((mem_timeAxisStabilizer_iff g).2 hg)⟩
theorem timeAxisStabilizer_apply_last (g : timeAxisStabilizer) (x : Fin 4 → ℝ) :
    g.1.1 x 3 = x 3 := by apply _root_.YangMills.Construction.TimeAxisSymbols.timeAxisStabilizer_apply_last <;> assumption
theorem image_lastCoord_set (g : timeAxisStabilizer) (T : Set ℝ) :
    ⇑g.1.1 '' {x : Fin 4 → ℝ | x 3 ∈ T} = {x : Fin 4 → ℝ | x 3 ∈ T} := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    change g.1.1 x 3 ∈ T
    rw [timeAxisStabilizer_apply_last]
    exact hx
  · intro hy
    refine ⟨(g⁻¹ : timeAxisStabilizer).1.1 y, ?_, ?_⟩
    · change (g⁻¹ : timeAxisStabilizer).1.1 y 3 ∈ T
      rw [timeAxisStabilizer_apply_last]
      exact hy
    · change (g * g⁻¹ : timeAxisStabilizer).1.1 y = y
      simp
theorem timeAxisStabilizer_fixesTime_holds : timeAxisStabilizer_fixesTime := by
  intro g
  refine ⟨timeAxisStabilizer_apply_last g, image_lastCoord_set g (Set.Ioi 0),
    image_lastCoord_set g {0}, ?_, fun a => ?_⟩
  · funext x
    have hvec : g.1.1 timeAxisVec = timeAxisVec := g.2
    have hadd := map_add (hyperoctahedralLinear g.1) x ((2 * (0 - x 3)) • timeAxisVec)
    have hsmul := map_smul (hyperoctahedralLinear g.1) (2 * (0 - x 3)) timeAxisVec
    simp only [coe_hyperoctahedralLinear] at hadd hsmul
    simp only [Function.comp, timeReflect, hyperplaneReflect]
    rw [hadd, hsmul, hvec, timeAxisStabilizer_apply_last]
  · have hpt := spaceTimePoint_init (g.1.1 (spaceTimePoint a 0))
    rw [timeAxisStabilizer_apply_last, spaceTimePoint_last] at hpt
    exact hpt.symm
theorem torusReflection_eq_mirror_holds (L : ℕ) (hL : L ≠ 0) :
    torusReflection_eq_mirror L := by
  intro K m μ c hc
  have hLr : (L : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hL
  have hc' : AxisReflection.IsLinkLevel L K (c + (L : ℝ) ^ (m : ℕ)) := by
    obtain ⟨q, hq⟩ := hc
    refine ⟨q + (L : ℤ) ^ (m : ℕ) * (L : ℤ) ^ (K : ℕ), ?_⟩
    rw [hq]
    simp only [PeriodicLattice.meshSize]
    push_cast
    rw [zpow_neg, zpow_natCast]
    have : (L : ℝ) ^ (K : ℕ) ≠ 0 := pow_ne_zero _ hLr
    field_simp
    ring
  refine ⟨hc', ⟨μ, c, hc, rfl⟩, ⟨μ, _, hc', rfl⟩, ?_⟩
  obtain ⟨q, hq⟩ := hc
  let P : InfiniteLattice.PeriodicMirror L m ((K : ℕ) : ℤ) :=
    ⟨μ, c, 2 * q + 1, by
      rw [hq]
      push_cast
      ring⟩
  exact ⟨P, rfl, rfl, rfl, AxisReflection.torusCoordReflect_eq_reflectEquiv P⟩
theorem motions_lattices_mirrors_holds : motions_lattices_mirrors := by
  intro L hL
  have h0 : L ≠ 0 := by
    have := hL.2
    omega
  exact ⟨⟨affineMotions_isGroup_holds, periodicMotion_isIsometry_holds L⟩,
    meshLattices_nested_holds L h0,
    adicGridPoints_dense_holds L (by have := hL.2; omega),
    ⟨timeAxisStabilizer_isSubgroup_holds, timeAxisStabilizer_fixesTime_holds⟩,
    torusReflection_eq_mirror_holds L h0⟩
end YangMills.Construction.GrowingTori.LatticeMotions
end
