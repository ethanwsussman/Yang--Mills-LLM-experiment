import YangMills.Construction.ReflectionPositivity.AxisMirrorData
import YangMills.Construction.SourcesAndGluing.LatticeIsometriesAndTheirAction
import Mathlib
set_option autoImplicit false
namespace YangMills.Construction
open Set TorusMetric TestFunctions
open ReflectionPositivity.AxisMirror (Ambient)
open scoped ENNReal
noncomputable section
namespace AmbientPoints
section NormFacts
variable {S : ℝ}
theorem euclidNormVec_eq_norm (v : Fin 4 → ℝ) :
    euclidNormVec v = ‖(WithLp.toLp 2 v : PiLp 2 fun _ : Fin 4 => ℝ)‖ := by
  rw [PiLp.norm_eq_of_L2]
  simp [euclidNormVec]
theorem torusEuclidNorm_eq_sqrt (x : Torus4 S) :
    torusEuclidNorm x = Real.sqrt (∑ μ, ‖x μ‖ ^ 2) := by
  choose b hb hb' using fun μ => exists_coe_eq_abs_eq_norm (x μ)
  have hproj : torusProj S b = x := funext hb
  apply le_antisymm
  · refine csInf_le ⟨0, ?_⟩ ⟨b, hproj, ?_⟩
    · rintro _ ⟨v, -, rfl⟩
      exact Real.sqrt_nonneg _
    · simp [euclidNormVec, ← hb', sq_abs]
  · refine le_csInf ⟨_, b, hproj, rfl⟩ ?_
    rintro _ ⟨v, hv, rfl⟩
    have hv' : torusProj S v = x := hv
    refine Real.sqrt_le_sqrt (Finset.sum_le_sum fun μ _ => ?_)
    rw [← hv', ← sq_abs (v μ)]
    exact pow_le_pow_left₀ (norm_nonneg _) (addCircle_norm_coe_le_abs _) 2
theorem torusEuclidNorm_eq_norm (x : Torus4 S) :
    torusEuclidNorm x = ‖(WithLp.toLp 2 x : PiLp 2 fun _ : Fin 4 => AddCircle S)‖ := by
  rw [PiLp.norm_eq_of_L2, torusEuclidNorm_eq_sqrt]
theorem torusEuclidNorm_torusProj_le (v : Fin 4 → ℝ) :
    torusEuclidNorm (torusProj S v) ≤ euclidNormVec v := by apply _root_.YangMills.Construction.SourcesAndGluing.torusEuclidNorm_torusProj_le <;> assumption
theorem exists_torusProj_eq_euclidNormVec_eq (x : Torus4 S) :
    ∃ b, torusProj S b = x ∧ euclidNormVec b = torusEuclidNorm x := by
  choose b hb hb' using fun μ => exists_coe_eq_abs_eq_norm (x μ)
  refine ⟨b, funext hb, ?_⟩
  rw [torusEuclidNorm_eq_sqrt]
  simp [euclidNormVec, ← hb', sq_abs]
theorem torusEuclidNorm_sub_self (x : Torus4 S) : torusEuclidNorm (x - x) = 0 := by
  simp [torusEuclidNorm_eq_sqrt]
theorem torusEuclidNorm_sub_comm (x y : Torus4 S) :
    torusEuclidNorm (x - y) = torusEuclidNorm (y - x) := by
  rw [torusEuclidNorm_eq_sqrt, torusEuclidNorm_eq_sqrt]
  congr 1
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [Pi.sub_apply, Pi.sub_apply, norm_sub_rev]
theorem torusEuclidNorm_sub_le (x y z : Torus4 S) :
    torusEuclidNorm (x - z) ≤ torusEuclidNorm (x - y) + torusEuclidNorm (y - z) := by
  simp only [torusEuclidNorm_eq_norm]
  have h : (WithLp.toLp 2 (x - z) : PiLp 2 fun _ : Fin 4 => AddCircle S) =
      WithLp.toLp 2 (x - y) + WithLp.toLp 2 (y - z) := by
    rw [← WithLp.toLp_add, sub_add_sub_cancel]
  rw [h]
  exact norm_add_le _ _
theorem eq_of_torusEuclidNorm_sub_eq_zero (x y : Torus4 S) (h : torusEuclidNorm (x - y) = 0) :
    x = y := by
  rw [torusEuclidNorm_eq_norm, norm_eq_zero] at h
  exact sub_eq_zero.mp (congrArg WithLp.ofLp h)
theorem euclidNormVec_sub_self (x : Fin 4 → ℝ) : euclidNormVec (x - x) = 0 := by
  simp [euclidNormVec]
theorem euclidNormVec_sub_comm (x y : Fin 4 → ℝ) :
    euclidNormVec (x - y) = euclidNormVec (y - x) := by
  simp only [euclidNormVec, Pi.sub_apply]
  congr 1
  refine Finset.sum_congr rfl fun μ _ => ?_
  ring
theorem euclidNormVec_sub_le (x y z : Fin 4 → ℝ) :
    euclidNormVec (x - z) ≤ euclidNormVec (x - y) + euclidNormVec (y - z) := by
  simp only [euclidNormVec_eq_norm]
  have h : (WithLp.toLp 2 (x - z) : PiLp 2 fun _ : Fin 4 => ℝ) =
      WithLp.toLp 2 (x - y) + WithLp.toLp 2 (y - z) := by
    rw [← WithLp.toLp_add, sub_add_sub_cancel]
  rw [h]
  exact norm_add_le _ _
theorem eq_of_euclidNormVec_sub_eq_zero (x y : Fin 4 → ℝ) (h : euclidNormVec (x - y) = 0) :
    x = y := by
  rw [euclidNormVec_eq_norm, norm_eq_zero] at h
  exact sub_eq_zero.mp (congrArg WithLp.ofLp h)
end NormFacts
variable (s : Conventions.StandingParameters)
def Pt : Ambient → Type
  | .torus => s.Torus
  | .euclidean => Fin 4 → ℝ
def proj : (E : Ambient) → (Fin 4 → ℝ) → Pt s E
  | .torus, x => torusProj (PeriodicLattice.torusSide s.L s.m) x
  | .euclidean, x => x
def pointDist : (E : Ambient) → Pt s E → Pt s E → ℝ
  | .torus, y, y' => euclidDistTorus (ℓ := PeriodicLattice.torusSide s.L s.m) y y'
  | .euclidean, y, y' => euclidDistR4 y y'
variable {s}
theorem pointDist_self (E : Ambient) (y : Pt s E) : pointDist s E y y = 0 := by
  cases E
  · exact torusEuclidNorm_sub_self y
  · exact euclidNormVec_sub_self y
theorem pointDist_comm (E : Ambient) (y y' : Pt s E) : pointDist s E y y' = pointDist s E y' y := by
  cases E
  · exact torusEuclidNorm_sub_comm y y'
  · exact euclidNormVec_sub_comm y y'
theorem pointDist_triangle (E : Ambient) (y y' y'' : Pt s E) :
    pointDist s E y y'' ≤ pointDist s E y y' + pointDist s E y' y'' := by
  cases E
  · exact torusEuclidNorm_sub_le y y' y''
  · exact euclidNormVec_sub_le y y' y''
theorem eq_of_pointDist_eq_zero (E : Ambient) {y y' : Pt s E} (h : pointDist s E y y' = 0) :
    y = y' := by
  cases E
  · exact eq_of_torusEuclidNorm_sub_eq_zero y y' h
  · exact eq_of_euclidNormVec_sub_eq_zero y y' h
instance (E : Ambient) : MetricSpace (Pt s E) where
  dist := pointDist s E
  dist_self := pointDist_self E
  dist_comm := pointDist_comm E
  dist_triangle := pointDist_triangle E
  eq_of_dist_eq_zero := eq_of_pointDist_eq_zero E
variable (s)
theorem isLeast_pointDist_proj (x x' : Fin 4 → ℝ) :
    IsLeast (range fun k : Fin 4 → ℤ =>
        euclidNormVec (x - x' - latticeTranslate (PeriodicLattice.torusSide s.L s.m) k))
      (pointDist s .torus (proj s .torus x) (proj s .torus x')) := by
  set ℓ := PeriodicLattice.torusSide s.L s.m
  have hdiff : pointDist s .torus (proj s .torus x) (proj s .torus x') =
      torusEuclidNorm (torusProj ℓ (x - x')) := by
    have hc : torusProj ℓ x - torusProj ℓ x' = torusProj ℓ (x - x') := by
      funext μ
      simp [torusProj]
    change torusEuclidNorm (torusProj ℓ x - torusProj ℓ x') = _
    rw [hc]
  rw [hdiff]
  constructor
  · obtain ⟨b, hb, hb'⟩ := exists_torusProj_eq_euclidNormVec_eq (torusProj ℓ (x - x'))
    obtain ⟨k, hk⟩ := exists_latticeTranslate_of_torusProj_eq hb
    refine ⟨-k, ?_⟩
    have hneg : x - x' - latticeTranslate ℓ (-k) = b := by
      rw [hk]
      funext μ
      simp [latticeTranslate]
    simpa only [hneg] using hb'
  · rintro _ ⟨k, rfl⟩
    have hproj : torusProj ℓ (x - x' - latticeTranslate ℓ k) = torusProj ℓ (x - x') := by
      have h := torusProj_add_latticeTranslate ℓ (x - x' - latticeTranslate ℓ k) k
      rw [sub_add_cancel] at h
      exact h.symm
    exact hproj ▸ torusEuclidNorm_torusProj_le _
def setDist (E : Ambient) (A B : Set (Pt s E)) : ℝ≥0∞ :=
  ⨅ a ∈ A, ⨅ b ∈ B, ENNReal.ofReal (pointDist s E a b)
theorem setDist_empty_left (E : Ambient) (B : Set (Pt s E)) : setDist s E ∅ B = ⊤ := by
  simp [setDist]
theorem setDist_empty_right (E : Ambient) (A : Set (Pt s E)) : setDist s E A ∅ = ⊤ := by
  simp [setDist]
def setDiam (E : Ambient) (A : Set (Pt s E)) : ℝ≥0∞ :=
  ⨆ a ∈ A, ⨆ b ∈ A, ENNReal.ofReal (pointDist s E a b)
def injRadius : Ambient → ℝ≥0∞
  | .torus => ENNReal.ofReal (s.side / 4)
  | .euclidean => ⊤
theorem two_mul_injRadius_torus : 2 * injRadius s .torus = ENNReal.ofReal (s.side / 2) := by
  have h2 : (2 : ℝ≥0∞) = ENNReal.ofReal 2 := by simp
  rw [injRadius, h2, ← ENNReal.ofReal_mul (by norm_num)]
  congr 1
  ring
theorem two_mul_injRadius_euclidean : 2 * injRadius s .euclidean = ⊤ := by
  simp [injRadius]
def IsLift (E : Ambient) (y : Pt s E) (x : Fin 4 → ℝ) : Prop := proj s E x = y
def openBall (E : Ambient) (y : Pt s E) (r : ℝ) : Set (Pt s E) := {y' | pointDist s E y' y < r}
def closedBall (E : Ambient) (y : Pt s E) (r : ℝ) : Set (Pt s E) :=
  {y' | pointDist s E y' y ≤ r}
theorem openBall_eq_ball (E : Ambient) (y : Pt s E) (r : ℝ) :
    openBall s E y r = Metric.ball y r := rfl
abbrev Tuple (E : Ambient) (p : ℕ) : Type := Fin p → Pt s E
def flattenCoords (p : ℕ) : (Fin p → Fin 4 → ℝ) ≃ (Fin (4 * p) → ℝ) :=
  (Equiv.curry (Fin p) (Fin 4) ℝ).symm.trans
    (Equiv.arrowCongr (finProdFinEquiv.trans (finCongr (Nat.mul_comm p 4))) (Equiv.refl ℝ))
theorem flattenCoords_apply {p : ℕ} (u : Fin p → Fin 4 → ℝ) (i : Fin p) (μ : Fin 4)
    (h : 4 * (i : ℕ) + μ < 4 * p) : flattenCoords p u ⟨4 * i + μ, h⟩ = u i μ := by
  have hidx : (finProdFinEquiv.trans (finCongr (Nat.mul_comm p 4))) (i, μ) =
      (⟨4 * i + μ, h⟩ : Fin (4 * p)) := by
    ext
    simp [finProdFinEquiv, Nat.add_comm]
  rw [← hidx]
  simp [flattenCoords, Equiv.arrowCongr]
variable {s}
def supDist {E : Ambient} {p : ℕ} (y y' : Tuple s E p) : ℝ := ⨆ i, pointDist s E (y i) (y' i)
def supNorm {p : ℕ} (u : Fin p → Fin 4 → ℝ) : ℝ := ⨆ i, euclidNormVec (u i)
theorem dist_eq_supDist {E : Ambient} {p : ℕ} (y y' : Tuple s E p) :
    dist y y' = supDist y y' := by
  apply le_antisymm
  · have h0 : 0 ≤ supDist y y' :=
      Real.iSup_nonneg fun i => (dist_nonneg : 0 ≤ dist (y i) (y' i))
    refine (dist_pi_le_iff h0).mpr fun i => ?_
    exact le_ciSup (f := fun i => pointDist s E (y i) (y' i)) (Set.finite_range _).bddAbove i
  · exact Real.iSup_le (fun i => dist_le_pi_dist y y' i) dist_nonneg
def IsNhdOfSet {E : Ambient} {p : ℕ} (N A : Set (Tuple s E p)) : Prop :=
  ∃ O, IsOpen O ∧ A ⊆ O ∧ O ⊆ N
end AmbientPoints
end
end YangMills.Construction
