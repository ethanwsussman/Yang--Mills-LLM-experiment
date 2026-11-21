import YangMills.Construction.ChessboardTori.ThreeEvaluationRules
import YangMills.Construction.InequalityOnMirroredCopies.ObservableOffTheFacesIsInTheCellProof
import YangMills.Construction.InfiniteLattice.LatticeIsometriesAndPeriodicRealizationOnATorusProof
import YangMills.Construction.InfiniteLattice.ObjectsOfAMirrorGridOnTheTorus
import YangMills.Construction.InfiniteLattice.SmearedDensityOfAFunctionCarriedWellInsideACell
import YangMills.Construction.Lattice.WilsonWeightGaugeInvariance
import YangMills.Construction.Torus.GeometryAndFreeKernelOfATestPairProof
import Mathlib
set_option autoImplicit false
namespace YangMills.Construction
open InfiniteLattice (AmbientSpace ElementaryPlaquette)
open TorusMetric
open TestFunctions (periodicSum latticeTranslate periodize closedBallR4 closedBallTorus IsBoundedFun
  uniformNorm IsLipschitzFor bestLipschitzConstant liftPoint torusProj_add_latticeTranslate
  torusProj_liftPoint periodize_torusProj)
open MeasureTheory
noncomputable section
namespace MultipleReflections.SmearedEnergyWellInsideTile
theorem euclidNormVec_add_le (v w : Fin 4 → ℝ) :
    euclidNormVec (v + w) ≤ euclidNormVec v + euclidNormVec w := by apply _root_.YangMills.Construction.LimitSpaces.AmbientMetric.euclidNormVec_add_le <;> assumption
theorem euclidNormVec_neg (v : Fin 4 → ℝ) : euclidNormVec (-v) = euclidNormVec v := by apply _root_.YangMills.Construction.LimitSpaces.AmbientMetric.euclidNormVec_neg <;> assumption
theorem abs_apply_le_euclidNormVec (v : Fin 4 → ℝ) (μ : Fin 4) : |v μ| ≤ euclidNormVec v := by apply _root_.YangMills.Construction.Parametrix.UnitKernelSupport.abs_apply_le_euclidNormVec <;> assumption
theorem torusEuclidNorm_torusProj_le (S : ℝ) (v : Fin 4 → ℝ) :
    torusEuclidNorm (torusProj S v) ≤ euclidNormVec v := by apply _root_.YangMills.Construction.SourcesAndGluing.torusEuclidNorm_torusProj_le <;> assumption
theorem exists_minimal_lift {S : ℝ} (hS : 0 < S) (x : Torus4 S) :
    ∃ b, torusProj S b = x ∧ euclidNormVec b = torusEuclidNorm x ∧ ∀ μ, |b μ| ≤ S / 2 := by
  have : Fact (0 < S) := ⟨hS⟩
  choose b hb hb' using fun μ => exists_coe_eq_abs_eq_norm (x μ)
  have hproj : torusProj S b = x := funext hb
  refine ⟨b, hproj, ?_, fun μ => ?_⟩
  · have hleast : IsLeast (euclidNormVec '' (torusProj S ⁻¹' {x})) (euclidNormVec b) := by
      refine ⟨⟨b, hproj, rfl⟩, ?_⟩
      rintro _ ⟨v, hv, rfl⟩
      have hv' : torusProj S v = x := hv
      refine Real.sqrt_le_sqrt (Finset.sum_le_sum fun μ _ => ?_)
      rw [← sq_abs (b μ), ← sq_abs (v μ), hb' μ]
      refine pow_le_pow_left₀ (norm_nonneg _) ?_ 2
      rw [← hv']
      exact addCircle_norm_coe_le_abs _
    exact hleast.csInf_eq.symm
  · rw [hb' μ]
    have h := AddCircle.norm_le_half_period S hS.ne' (x := x μ)
    simpa [abs_of_pos hS] using h
theorem torusProj_add (S : ℝ) (v w : Fin 4 → ℝ) :
    torusProj S (v + w) = torusProj S v + torusProj S w := by apply _root_.YangMills.Construction.TestPairs.torusProj_map_add <;> assumption
theorem torusProj_sub (S : ℝ) (v w : Fin 4 → ℝ) :
    torusProj S (v - w) = torusProj S v - torusProj S w := by apply _root_.YangMills.Construction.TestPairs.torusProj_map_sub <;> assumption
section Periodization
variable {ℓ r : ℝ} {f : AmbientSpace → ℝ} {c : AmbientSpace}
theorem periodicSum_eq_of_near (hr : 4 * r < ℓ) (hℓ : 0 < ℓ)
    (hf : ∀ x, x ∉ closedBallR4 c r → f x = 0) {v : AmbientSpace}
    (hv : ∀ μ, |v μ - c μ| ≤ 3 * ℓ / 4) :
    periodicSum ℓ f v = f v := by
  unfold periodicSum
  refine (tsum_eq_single (0 : Fin 4 → ℤ) ?_).trans ?_
  · intro n hn
    apply hf
    intro hb
    obtain ⟨μ, hμ⟩ := Function.ne_iff.1 hn
    have h1 : |(v + latticeTranslate ℓ n - c) μ| ≤ r := (abs_apply_le_euclidNormVec _ μ).trans hb
    simp only [Pi.sub_apply, Pi.add_apply, latticeTranslate] at h1
    have h3 := abs_le.1 h1
    have h4 := abs_le.1 (hv μ)
    have h5 : |ℓ * (n μ : ℝ)| < ℓ := by
      refine abs_lt.2 ⟨?_, ?_⟩ <;> linarith [h3.1, h3.2, h4.1, h4.2]
    have h6 : (1 : ℝ) ≤ |(n μ : ℝ)| := by
      have : (1 : ℤ) ≤ |n μ| := Int.one_le_abs hμ
      exact_mod_cast this
    rw [abs_mul, abs_of_pos hℓ] at h5
    nlinarith
  · have h0 : v + latticeTranslate ℓ 0 = v := by
      funext μ
      simp [latticeTranslate]
    rw [h0]
theorem exists_lift_mem_of_periodize_ne_zero (hf : ∀ x, x ∉ closedBallR4 c r → f x = 0)
    {u : Torus4 ℓ} (hu : periodize ℓ f u ≠ 0) : ∃ x ∈ closedBallR4 c r, torusProj ℓ x = u := by
  have h : periodicSum ℓ f (liftPoint u) ≠ 0 := hu
  obtain ⟨n, hn⟩ : ∃ n, f (liftPoint u + latticeTranslate ℓ n) ≠ 0 := by
    by_contra hne
    have hz : ∀ n, f (liftPoint u + latticeTranslate ℓ n) = 0 := fun n =>
      by_contra fun hn => hne ⟨n, hn⟩
    exact h (by simp [periodicSum, hz])
  exact ⟨_, by_contra fun hx => hn (hf _ hx),
    by rw [torusProj_add_latticeTranslate, torusProj_liftPoint]⟩
theorem periodize_torusProj_of_near (hr : 4 * r < ℓ) (hℓ : 0 < ℓ)
    (hf : ∀ x, x ∉ closedBallR4 c r → f x = 0) {v : AmbientSpace}
    (hv : ∀ μ, |v μ - c μ| ≤ 3 * ℓ / 4) :
    periodize ℓ f (torusProj ℓ v) = f v := by
  rw [periodize_torusProj, periodicSum_eq_of_near hr hℓ hf hv]
theorem abs_add_sub_center_le (hr : 4 * r < ℓ) {x b : AmbientSpace} (hx : x ∈ closedBallR4 c r)
    (hb : ∀ μ, |b μ| ≤ ℓ / 2) (μ : Fin 4) : |(x + b) μ - c μ| ≤ 3 * ℓ / 4 := by
  have h1 : |(x - c) μ| ≤ r := (abs_apply_le_euclidNormVec _ μ).trans hx
  simp only [Pi.sub_apply] at h1
  have h3 := abs_le.1 h1
  have h4 := abs_le.1 (hb μ)
  simp only [Pi.add_apply]
  refine abs_le.2 ⟨?_, ?_⟩ <;> linarith [h3.1, h3.2, h4.1, h4.2]
theorem norm_periodize_sub_le (hr : 4 * r < ℓ) (hℓ : 0 < ℓ)
    (hf : ∀ x, x ∉ closedBallR4 c r → f x = 0) {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ x y, ‖f x - f y‖ ≤ C * TestFunctions.euclidDistR4 x y) (u w : Torus4 ℓ) :
    ‖periodize ℓ f u - periodize ℓ f w‖ ≤ C * TestFunctions.euclidDistTorus u w := by
  obtain ⟨b, hb, hbe, hbℓ⟩ := exists_minimal_lift hℓ (u - w)
  have hd : TestFunctions.euclidDistTorus u w = euclidNormVec b := hbe.symm
  rw [hd]
  by_cases hu : periodize ℓ f u = 0
  · by_cases hw : periodize ℓ f w = 0
    · rw [hu, hw, sub_zero, norm_zero]
      exact mul_nonneg hC0 (Real.sqrt_nonneg _)
    · obtain ⟨x, hx, rfl⟩ := exists_lift_mem_of_periodize_ne_zero hf hw
      have hxu : u = torusProj ℓ (x + b) := by rw [torusProj_add, hb]; abel
      have hb0 : ∀ μ, |(0 : AmbientSpace) μ| ≤ ℓ / 2 := fun μ => by simpa using by positivity
      have e1 : periodize ℓ f (torusProj ℓ x) = f x := by
        have := abs_add_sub_center_le hr hx hb0
        simp only [add_zero] at this
        exact periodize_torusProj_of_near hr hℓ hf this
      have e2 : periodize ℓ f u = f (x + b) := by
        rw [hxu]
        exact periodize_torusProj_of_near hr hℓ hf (abs_add_sub_center_le hr hx hbℓ)
      rw [e1, e2]
      refine (hC _ _).trans (le_of_eq ?_)
      simp [TestFunctions.euclidDistR4]
  · obtain ⟨x, hx, rfl⟩ := exists_lift_mem_of_periodize_ne_zero hf hu
    have hxw : w = torusProj ℓ (x + -b) := by
      rw [← sub_eq_add_neg, torusProj_sub, hb]
      abel
    have hb0 : ∀ μ, |(0 : AmbientSpace) μ| ≤ ℓ / 2 := fun μ => by simpa using by positivity
    have hbn : ∀ μ, |(-b) μ| ≤ ℓ / 2 := fun μ => by simpa using hbℓ μ
    have e1 : periodize ℓ f (torusProj ℓ x) = f x := by
      have := abs_add_sub_center_le hr hx hb0
      simp only [add_zero] at this
      exact periodize_torusProj_of_near hr hℓ hf this
    have e2 : periodize ℓ f w = f (x + -b) := by
      rw [hxw]
      exact periodize_torusProj_of_near hr hℓ hf (abs_add_sub_center_le hr hx hbn)
    rw [e1, e2]
    refine (hC _ _).trans (le_of_eq ?_)
    simp [TestFunctions.euclidDistR4]
theorem norm_periodize_le_uniformNorm (hr : 4 * r < ℓ) (hℓ : 0 < ℓ)
    (hf : ∀ x, x ∉ closedBallR4 c r → f x = 0) (hb : IsBoundedFun f) (u : Torus4 ℓ) :
    ‖periodize ℓ f u‖ ≤ uniformNorm f := by
  obtain ⟨C, hC⟩ := hb
  have hle : ∀ x, ‖f x‖ ≤ uniformNorm f := fun x =>
    le_ciSup (f := fun x => ‖f x‖) ⟨C, by rintro _ ⟨y, rfl⟩; exact hC y⟩ x
  by_cases hu : periodize ℓ f u = 0
  · rw [hu, norm_zero]
    exact (norm_nonneg _).trans (hle 0)
  · obtain ⟨x, hx, rfl⟩ := exists_lift_mem_of_periodize_ne_zero hf hu
    have hb0 : ∀ μ, |(0 : AmbientSpace) μ| ≤ ℓ / 2 := fun μ => by simpa using by positivity
    have := abs_add_sub_center_le hr hx hb0
    simp only [add_zero] at this
    rw [periodize_torusProj_of_near hr hℓ hf this]
    exact hle x
theorem periodize_eq_zero_of_not_mem (hf : ∀ x, x ∉ closedBallR4 c r → f x = 0) {y : Torus4 ℓ}
    (hy : y ∉ closedBallTorus (torusProj ℓ c) r) : periodize ℓ f y = 0 := by
  by_contra h
  obtain ⟨x, hx, rfl⟩ := exists_lift_mem_of_periodize_ne_zero hf h
  apply hy
  show torusEuclidNorm (torusProj ℓ x - torusProj ℓ c) ≤ r
  rw [← torusProj_sub]
  exact (torusEuclidNorm_torusProj_le ℓ _).trans hx
theorem isLipschitzFor_periodize (hr : 4 * r < ℓ) (hℓ : 0 < ℓ)
    (hf : ∀ x, x ∉ closedBallR4 c r → f x = 0)
    (hL : IsLipschitzFor TestFunctions.euclidDistR4 f) :
    IsLipschitzFor TestFunctions.euclidDistTorus (periodize ℓ f) := by
  obtain ⟨C, hC0, hC⟩ := hL
  exact ⟨C, hC0, norm_periodize_sub_le hr hℓ hf hC0 hC⟩
theorem sharpNormTorus_periodize_le (hr : 4 * r < ℓ) (hℓ : 0 < ℓ)
    (hf : ∀ x, x ∉ closedBallR4 c r → f x = 0) (hb : IsBoundedFun f)
    (hL : IsLipschitzFor TestFunctions.euclidDistR4 f) {M : ℝ} (hM : 0 < M) :
    TestFunctions.sharpNormTorus M (periodize ℓ f) ≤ TestFunctions.sharpNormR4 M f := by
  refine max_le_max ?_ ?_
  · exact ciSup_le (norm_periodize_le_uniformNorm hr hℓ hf hb)
  · refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    refine csInf_le_csInf ⟨0, fun C hC => hC.1⟩ ?_ ?_
    · obtain ⟨C, hC0, hC⟩ := hL
      exact ⟨C, hC0, hC⟩
    · rintro C ⟨hC0, hC⟩
      exact ⟨hC0, norm_periodize_sub_le hr hℓ hf hC0 hC⟩
end Periodization
section Tile
variable {D : Setup}
theorem mesh_pos (D : Setup) : 0 < D.mesh := by apply _root_.YangMills.Construction.MultipleReflections.TorusPullback.mesh_pos <;> assumption
theorem four_mul_mesh_le_edge (G : D.Grid) : 4 * D.mesh ≤ G.edge := by
  have h := (Setup.Grid.isTileEdge_edge G).2
  have hL : (2 : ℝ) ≤ D.L := by
    have := D.isAdmissible.2
    exact_mod_cast (by omega : 2 ≤ D.L)
  have h4 : (4 : ℝ) ≤ (D.L : ℝ) ^ 2 := by nlinarith
  nlinarith [mul_le_mul_of_nonneg_right h4 (mesh_pos D).le]
theorem tileCenter_apply (G : D.Grid) (k : Fin 4 → ℤ) (μ : Fin 4) :
    G.tileCenter k μ = G.cornerAt k μ + G.edge / 2 := by
  simp [InfiniteLattice.ReflectionGrid.tileCenter, InfiniteLattice.ReflectionGrid.basisVec,
    Finset.sum_apply, Pi.single_apply]
theorem abs_corner_sub_center_le (p : ElementaryPlaquette D.mesh)
    {y : InfiniteLattice.LatticePoint D.mesh} (hy : y ∈ p.cornerSet) (μ : Fin 4) :
    |(y : AmbientSpace) μ - p.center μ| ≤ D.mesh / 2 := by
  have hne : ¬(μ = p.lowAxis ∧ μ = p.highAxis) := fun h =>
    p.lowAxis_lt_highAxis.ne (h.1.symm.trans h.2)
  have ha := mesh_pos D
  have hs : ∀ ν, ((InfiniteLattice.axisStep D.mesh ν : InfiniteLattice.LatticePoint D.mesh) :
      AmbientSpace) μ = if μ = ν then D.mesh else 0 := fun ν => by
    simp [InfiniteLattice.axisStep, Pi.single_apply]
  have hb : p.center μ = (p.corner : AmbientSpace) μ + (if μ = p.lowAxis then D.mesh / 2 else 0) +
      (if μ = p.highAxis then D.mesh / 2 else 0) := by
    simp [ElementaryPlaquette.center, Pi.single_apply]
  simp only [InfiniteLattice.ElementaryPlaquette.cornerSet, Set.mem_insert_iff,
    Set.mem_singleton_iff] at hy
  rcases hy with rfl | rfl | rfl | rfl <;>
    simp only [AddSubgroup.coe_add, Pi.add_apply, hs, hb] <;> split_ifs <;>
    first
    | exact absurd ⟨by assumption, by assumption⟩ hne
    | (rw [abs_le]; constructor <;> linarith)
theorem corners_mem_tileInterior (G : D.Grid) (k : Fin 4 → ℤ) (p : ElementaryPlaquette D.mesh)
    (hp : p.center ∈ closedBallR4 (G.tileCenter k) (G.edge / 4)) :
    ∀ y ∈ p.cornerSet, (y : AmbientSpace) ∈ G.tileInterior k := by
  intro y hy μ
  have h1 := abs_le.1 (abs_corner_sub_center_le p hy μ)
  have h2 : |(p.center - G.tileCenter k) μ| ≤ G.edge / 4 :=
    (abs_apply_le_euclidNormVec _ μ).trans hp
  simp only [Pi.sub_apply, tileCenter_apply] at h2
  have h3 := abs_le.1 h2
  have h4 := four_mul_mesh_le_edge G
  have ha := mesh_pos D
  constructor <;> linarith [h1.1, h1.2, h3.1, h3.2]
theorem isBounded_closedBallR4 (c : AmbientSpace) {r : ℝ} (hr : 0 ≤ r) :
    Bornology.IsBounded (closedBallR4 c r) := by apply _root_.YangMills.SharedProofs.p53483 <;> assumption
theorem ofReal_smearedEnergy {a : ℝ} (h : AmbientSpace → ℝ) (U : InfiniteLattice.GaugeField a)
    (hfin : (Function.support fun p : ElementaryPlaquette a =>
      InfiniteLattice.faceEnergy U p • h p.center).Finite) :
    ((InfiniteLattice.smearedEnergy h U : ℝ) : ℂ) =
      InfiniteLattice.smearedEnergy (fun x => (h x : ℂ)) U := by apply _root_.YangMills.SharedProofs.p21788 <;> assumption
theorem smearedEnergy_isTileObservable (hF : FieldsAtSpacing.LinkFunctionsStatement)
    (G : D.Grid) (k : Fin 4 → ℤ) {h : AmbientSpace → ℝ} (hm : Measurable h) (hb : IsBoundedFun h)
    (hv : ∀ x, x ∉ closedBallR4 (G.tileCenter k) (G.edge / 4) → h x = 0) :
    G.IsTileObservable k fun U : D.GaugeField =>
      ((InfiniteLattice.smearedEnergy h U : ℝ) : ℂ) := by
  obtain ⟨-, hfinB, hsum, -, -⟩ := (hF D.mesh (mesh_pos D) ∅ (Set.empty_subset _)).2.2.2.2.2
  have hl : 0 ≤ G.edge / 4 := by
    have := four_mul_mesh_le_edge G
    have := mesh_pos D
    linarith
  have hv' : InfiniteLattice.IsBoundedBorelCompactlySupported (fun x => (h x : ℂ)) := by
    refine ⟨Complex.measurable_ofReal.comp hm, ?_, ?_⟩
    · obtain ⟨C, hC⟩ := hb
      exact ⟨C, fun x => by simpa using hC x⟩
    · refine HasCompactSupport.intro (isCompact_closedBall (G.tileCenter k) (G.edge / 4))
        fun x hx => ?_
      have hx' : x ∉ closedBallR4 (G.tileCenter k) (G.edge / 4) := fun hb' => hx <| by
        refine Metric.mem_closedBall.2 ((dist_pi_le_iff hl).2 fun μ => ?_)
        rw [Real.dist_eq]
        exact (abs_apply_le_euclidNormVec (x - G.tileCenter k) μ).trans hb'
      simp [hv x hx']
  have hc := ((hsum _ hv').2.2.2 (G.tileInterior k) fun p hp => corners_mem_tileInterior G k p
    (by_contra fun hn => hp (by simp [hv _ hn]))).1
  have e : (fun U : D.GaugeField => ((InfiniteLattice.smearedEnergy h U : ℝ) : ℂ)) =
      InfiniteLattice.smearedEnergy (fun x => (h x : ℂ)) := by
    funext U
    refine ofReal_smearedEnergy h U
      ((hfinB _ (isBounded_closedBallR4 (G.tileCenter k) hl)).subset ?_)
    intro p hp
    exact by_contra fun hn => hp (by simp [hv _ hn])
  rw [e]
  exact hc
theorem exp_isTileObservable (G : D.Grid) (k : Fin 4 → ℤ) {A : D.GaugeField → ℂ}
    (hA : G.IsTileObservable k A) (z c : ℂ) :
    G.IsTileObservable k fun U => Complex.exp (z * A U - c) := by
  obtain ⟨⟨hm, C, hC⟩, hS⟩ := hA
  refine ⟨⟨Complex.measurable_exp.comp ((hm.const_mul z).sub_const c),
    Real.exp (‖z‖ * C + ‖c‖), fun U => ?_⟩,
    Complex.measurable_exp.comp ((Measurable.const_mul hS z).sub_const c)⟩
  rw [Complex.norm_exp]
  refine Real.exp_le_exp.2 ((Complex.re_le_norm _).trans ((norm_sub_le _ _).trans ?_))
  rw [norm_mul]
  have := mul_le_mul_of_nonneg_left (hC U) (norm_nonneg z)
  linarith
end Tile
section Agreement
open PeriodicLattice (compactGaugeFields)
theorem ae_mem_compactGaugeFields (hW : PeriodicLattice.WilsonWeightGaugeInvariance.statement)
    (s : Conventions.StandingParameters) (β : ℝ) :
    ∀ᵐ U ∂PeriodicLattice.wilsonGibbsMeasure s.L s.m s.K β,
      U ∈ compactGaugeFields s.L s.m ((s.K : ℕ) : ℤ) := by
  have hL : 1 < s.L := by
    have := s.isAdmissible.2
    omega
  obtain ⟨-, -, -, -, -, -, -, -, hnull, -⟩ := hW s.L s.m s.K β hL s.m.pos s.K.pos
  exact ae_iff.2 hnull
theorem transportGaugeField_mem {L m : ℕ} {n : ℤ}
    (σ : PeriodicLattice.FourTorus L m ≃ PeriodicLattice.FourTorus L m)
    {U : PeriodicLattice.Bond L m n → Matrices.ComplexMatrix2} (hU : U ∈ compactGaugeFields L m n) :
    PeriodicLattice.transportGaugeField σ U ∈ compactGaugeFields L m n := by
  refine ⟨fun b _ => hU.1 _ (Set.mem_univ _), fun b _ => ?_⟩
  have key : PeriodicLattice.bondPreimage σ b.opposite =
      (PeriodicLattice.bondPreimage σ b).opposite := by
    unfold PeriodicLattice.bondPreimage
    by_cases h : ∃ b' : PeriodicLattice.Bond L m n,
        (b'.source : PeriodicLattice.FourTorus L m) = σ.symm b.source ∧
        (b'.target : PeriodicLattice.FourTorus L m) = σ.symm b.target
    · have h' : ∃ b' : PeriodicLattice.Bond L m n,
          (b'.source : PeriodicLattice.FourTorus L m) = σ.symm b.opposite.source ∧
          (b'.target : PeriodicLattice.FourTorus L m) = σ.symm b.opposite.target :=
        ⟨h.choose.opposite, h.choose_spec.2, h.choose_spec.1⟩
      rw [dif_pos h', dif_pos h]
      exact PeriodicLattice.Bond.ext (Subtype.ext (h'.choose_spec.1.trans h.choose_spec.2.symm))
        (Subtype.ext (h'.choose_spec.2.trans h.choose_spec.1.symm))
    · have h' : ¬∃ b' : PeriodicLattice.Bond L m n,
          (b'.source : PeriodicLattice.FourTorus L m) = σ.symm b.opposite.source ∧
          (b'.target : PeriodicLattice.FourTorus L m) = σ.symm b.opposite.target :=
        fun ⟨x, h1, h2⟩ => h ⟨x.opposite, h2, h1⟩
      rw [dif_neg h', dif_neg h]
  show U (PeriodicLattice.bondPreimage σ b.opposite) = (U (PeriodicLattice.bondPreimage σ b))⁻¹
  rw [key]
  exact hU.2 _ (Set.mem_univ _)
theorem pullbackField_mem {D : ChessboardTori.ChessboardSetup} {r' : D.Torus → D.Torus}
    (hex : ∀ b : D.PeriodicLink, ∃ b' : D.PeriodicLink,
      (b'.source : D.Torus) = r' b.source ∧ (b'.target : D.Torus) = r' b.target)
    {U : D.PeriodicLink → Matrices.ComplexMatrix2} (hU : U ∈ D.compactFields) :
    D.pullbackField r' U ∈ D.compactFields := by
  refine ⟨fun b _ => hU.1 _ (Set.mem_univ _), fun b _ => ?_⟩
  have spec : ∀ b : D.PeriodicLink, ((D.imageLink r' b).source : D.Torus) = r' b.source ∧
      ((D.imageLink r' b).target : D.Torus) = r' b.target := fun b =>
    Classical.epsilon_spec (hex b)
  have key : D.imageLink r' b.opposite = (D.imageLink r' b).opposite :=
    PeriodicLattice.Bond.ext (Subtype.ext ((spec b.opposite).1.trans (spec b).2.symm))
      (Subtype.ext ((spec b.opposite).2.trans (spec b).1.symm))
  show U (D.imageLink r' b.opposite) = (U (D.imageLink r' b))⁻¹
  rw [key]
  exact hU.2 _ (Set.mem_univ _)
theorem torusProduct_congr (hT : ChessboardTori.LiftingRules.Statement)
    {D : ChessboardTori.ChessboardSetup} (g : ChessboardTori.ReflectionGrid D)
    {F F' : (D.PeriodicLink → Matrices.ComplexMatrix2) → ℂ}
    (hFF : ∀ U ∈ D.compactFields, F U = F' U) {U : D.PeriodicLink → Matrices.ComplexMatrix2}
    (hU : U ∈ D.compactFields) : g.torusProduct F U = g.torusProduct F' U := by
  refine finprod_mem_congr rfl fun r' hr' => ?_
  obtain ⟨r, hr, hrr⟩ := hr'
  have hex : ∀ b : D.PeriodicLink, ∃ b' : D.PeriodicLink,
      (b'.source : D.Torus) = r' b.source ∧ (b'.target : D.Torus) = r' b.target := fun b => by
    obtain ⟨b', h1, h2, -⟩ := (((hT D).2.2.2 (g.toLatticeSym ⟨r, hr⟩) r' hrr).2 U hU).2 b
    exact ⟨b', h1, h2⟩
  show Conventions.signedConj _ (F (D.pullbackField r' U)) =
    Conventions.signedConj _ (F' (D.pullbackField r' U))
  rw [hFF _ (pullbackField_mem hex hU)]
theorem torusChessboardNorm_congr (hT : ChessboardTori.LiftingRules.Statement)
    (hW : PeriodicLattice.WilsonWeightGaugeInvariance.statement)
    {D : ChessboardTori.ChessboardSetup} (g : ChessboardTori.ReflectionGrid D)
    {F F' : (D.PeriodicLink → Matrices.ComplexMatrix2) → ℂ}
    (hFF : ∀ U ∈ D.compactFields, F U = F' U) :
    g.torusChessboardNorm F = g.torusChessboardNorm F' := by
  have e : D.periodicExpectation (g.torusProduct F) = D.periodicExpectation (g.torusProduct F') :=
    integral_congr_ae ((ae_mem_compactGaugeFields hW D.toStandingParameters D.β).mono fun U hU =>
      torusProduct_congr hT g hFF hU)
  rw [ChessboardTori.ReflectionGrid.torusChessboardNorm,
    ChessboardTori.ReflectionGrid.torusChessboardNorm, e]
theorem chessboardNormOnTorus_congr (hW : PeriodicLattice.WilsonWeightGaugeInvariance.statement)
    {D : SourcesAndGluing.GluingSetup} (g : SourcesAndGluing.CubicGrid D)
    {F F' : (D.PeriodicLink → Matrices.ComplexMatrix2) → ℂ}
    (hFF : ∀ U ∈ compactGaugeFields D.L D.m ((D.K : ℕ) : ℤ), F U = F' U) :
    g.chessboardNormOnTorus F = g.chessboardNormOnTorus F' := by
  have e : D.expectation (g.reflectionProductOnTorus F) =
      D.expectation (g.reflectionProductOnTorus F') :=
    integral_congr_ae ((ae_mem_compactGaugeFields hW D.toStandingParameters D.β).mono fun U hU => by
      refine finprod_congr fun r => ?_
      show Conventions.signedConj _
          (F (PeriodicLattice.transportGaugeField (r : Equiv.Perm D.Torus).symm U)) =
        Conventions.signedConj _
          (F' (PeriodicLattice.transportGaugeField (r : Equiv.Perm D.Torus).symm U))
      rw [hFF _ (transportGaugeField_mem _ hU)])
  rw [SourcesAndGluing.CubicGrid.chessboardNormOnTorus,
    SourcesAndGluing.CubicGrid.chessboardNormOnTorus, e]
end Agreement
theorem pullbackObs_expSmeared (hR : SymmetriesAndTorusPullback)
    (D : Setup) {S : Set AmbientSpace} {h : AmbientSpace → ℝ} (hm : Measurable h)
    (hb : IsBoundedFun h) (ht : TestFunctions.IsPeriodizable D.side S h) (z c : ℂ)
    (U : D.TorusField) :
    D.pullbackObs (D.expSmeared h z c) U =
      D.torusExpSmeared (periodize (PeriodicLattice.torusSide D.L D.m) h) z c U.1 := by
  have e := ((hR D).2.2.2.2.2.2.2 S).2 h hm hb ht U
  have e' : ((InfiniteLattice.smearedEnergy h (D.lift U) : ℝ) : ℂ) =
      ((PeriodicLattice.smearedObservable (periodize (PeriodicLattice.torusSide D.L D.m) h) U.1 :
        ℝ) : ℂ) := e
  show Complex.exp (z * ((InfiniteLattice.smearedEnergy h (D.lift U) : ℝ) : ℂ) - c) = _
  rw [e']
  rfl
theorem holds (hB : TorusGridObjectsAgree)
    (hR : SymmetriesAndTorusPullback)
    (hT : ChessboardTori.LiftingRules.Statement)
    (hW : PeriodicLattice.WilsonWeightGaugeInvariance.statement)
    (hF : FieldsAtSpacing.LinkFunctionsStatement) : Statement := by
  intro D G k h hm hb hv
  have hobs := smearedEnergy_isTileObservable hF G k hm hb hv
  have hexp : ∀ z c : ℂ, D.expSmeared h z c ∈ G.tileAlgebra k := fun z c =>
    exp_isTileObservable G k hobs z c
  refine ⟨corners_mem_tileInterior G k, hobs, hexp, ?_⟩
  intro hedge hL M hM
  have hl := Setup.Grid.edge_pos G
  have hedge' : 2 * G.edge ≤ PeriodicLattice.torusSide D.L D.m := hedge
  have hℓ0 : 0 < PeriodicLattice.torusSide D.L D.m := by linarith
  have hr : 4 * (G.edge / 4) < PeriodicLattice.torusSide D.L D.m := by linarith
  have htr : TestFunctions.IsPeriodizable (PeriodicLattice.torusSide D.L D.m)
      (closedBallR4 (G.tileCenter k) (G.edge / 4)) h := by
    refine ⟨fun x hx y hy => ?_, fun x hx => by_contra fun hn => hx (hv x hn)⟩
    have e : x - y = (x - G.tileCenter k) + -(y - G.tileCenter k) := by abel
    have h1 : euclidNormVec (x - G.tileCenter k) ≤ G.edge / 4 := hx
    have h2 : euclidNormVec (y - G.tileCenter k) ≤ G.edge / 4 := hy
    rw [e]
    refine (euclidNormVec_add_le _ _).trans ?_
    rw [euclidNormVec_neg]
    linarith
  refine ⟨htr, isLipschitzFor_periodize hr hℓ0 hv hL,
    fun y hy => periodize_eq_zero_of_not_mem hv hy,
    sharpNormTorus_periodize_le hr hℓ0 hv hb hL hM, ?_⟩
  intro z c
  have hread := pullbackObs_expSmeared hR D hm hb htr z c
  have hagree : ∀ U ∈ PeriodicLattice.compactGaugeFields D.L D.m ((D.K : ℕ) : ℤ),
      D.liftToLinks (D.expSmeared h z c) U =
        D.torusExpSmeared (periodize (PeriodicLattice.torusSide D.L D.m) h) z c U :=
    fun U hU => hread ⟨U, hU⟩
  obtain ⟨-, -, hArr, -, hS⟩ := hB D G hedge
  refine ⟨hread, ⟨G.toChessboardGrid, G.cellSide_toChessboardGrid, rfl, ?_⟩,
    fun i => ⟨G.toCubicGrid i hedge, rfl, rfl, ?_⟩⟩
  · obtain ⟨-, hC, hFm, hval⟩ := hArr k _ (hexp z c)
    obtain ⟨f, hf1, hf2, hf3⟩ := id hFm
    refine ⟨G.two_mul_cellSide_le_torusSide hedge, hC,
      ⟨f, hf1, hf2, fun U => (hagree U.1 U.2).symm.trans (hf3 U)⟩, ?_⟩
    rw [hval]
    exact torusChessboardNorm_congr hT hW _ hagree
  · obtain ⟨-, -, -, hS'⟩ := hS i
    obtain ⟨hread', -, hval⟩ := hS' k _ (hexp z c)
    rw [← hval]
    refine (SourcesAndGluing.CubicGrid.chessboardNormOnTorus_pullToTorus _ _).symm.trans ?_
    rw [hread']
    exact chessboardNormOnTorus_congr hW _ hagree
end MultipleReflections.SmearedEnergyWellInsideTile
end
end YangMills.Construction
