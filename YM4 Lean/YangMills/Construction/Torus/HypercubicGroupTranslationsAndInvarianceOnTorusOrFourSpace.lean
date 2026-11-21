import YangMills.Construction.Continuum.SymbolsOfFourSpaceWithATimeAxis
import YangMills.Construction.ReflectionPositivity.SeparatedTuplesOnOneTorusIsometriesAndSymmetricFunctions
import YangMills.Construction.Torus.SeparatedTuplesAndIsometriesOfTorusOrFourSpace
import Mathlib
set_option autoImplicit false
open YangMills.Construction.ReflectionPositivity.AxisMirror (Ambient)
open YangMills.Construction.AmbientPoints
open YangMills.Construction.TorusTransport (hyperoctahedral hyperoctahedralLinear coordNegation translationEquiv)
open YangMills.Construction.TimeAxisSymbols (timeAxisVec)
open Matrix
noncomputable section
namespace YangMills.Construction
namespace TorusSymmetries
abbrev timeVecStabilizer : Subgroup hyperoctahedral := TimeAxisSymbols.timeAxisStabilizer
def toMatrix (g : hyperoctahedral) : Matrix (Fin 4) (Fin 4) ℝ :=
  LinearMap.toMatrix' (hyperoctahedralLinear g)
theorem toMatrix_mulVec (g : hyperoctahedral) (x : Fin 4 → ℝ) :
    toMatrix g *ᵥ x = g.1 x := by
  rw [toMatrix, LinearMap.toMatrix'_mulVec, TorusTransport.coe_hyperoctahedralLinear]
theorem toMatrix_mem (g : hyperoctahedral) :
    toMatrix g ∈ PeriodicLattice.signedPermMatrices := by
  obtain ⟨r, hr⟩ := (TorusTransport.mem_hyperoctahedral_iff_signedFrame g.1).1 g.2
  refine (PeriodicLattice.mem_signedPermMatrices_iff _).2 ⟨r, ?_⟩
  apply Matrix.mulVec_injective
  funext x
  rw [toMatrix_mulVec, PeriodicLattice.SignedFrame.toMatrix_mulVec, hr]
def actOn (s : Conventions.StandingParameters) :
    (E : Ambient) → hyperoctahedral → (Pt s E ≃ Pt s E)
  | .torus, g => ReflectionPositivity.TorusTuples.signedMatrixEquiv s (toMatrix_mem g)
  | .euclidean, g => g.1
theorem actOn_proj (s : Conventions.StandingParameters) (E : Ambient) (g : hyperoctahedral)
    (y : Fin 4 → ℝ) :
    actOn s E g (proj s E y) = proj s E (g.1 y) := by
  cases E
  · exact (ReflectionPositivity.TorusTuples.signedMatrixMap_proj s (toMatrix_mem g) y).trans
      (congrArg _ (toMatrix_mulVec g y))
  · rfl
def translateOn (s : Conventions.StandingParameters) :
    (E : Ambient) → Pt s E → (Pt s E ≃ Pt s E)
  | .torus, v => ReflectionPositivity.TorusTuples.shiftBy v
  | .euclidean, v => translationEquiv v
theorem isDistIsometry_translateOn (s : Conventions.StandingParameters) (E : Ambient)
    (v : Pt s E) : IsDistIsometry (translateOn s E v) := by
  intro x y
  cases E
  · change TorusMetric.torusEuclidNorm _ = TorusMetric.torusEuclidNorm _
    congr 1
    exact add_sub_add_right_eq_sub _ _ _
  · change TorusMetric.euclidNormVec _ = TorusMetric.euclidNormVec _
    congr 1
    exact add_sub_add_right_eq_sub _ _ _
theorem torusEuclidNorm_signedCoordinatePerm (s : Conventions.StandingParameters)
    (π : Equiv.Perm (Fin 4)) (ε : Fin 4 → ℤˣ) (x : s.Torus) :
    TorusMetric.torusEuclidNorm (PeriodicLattice.signedCoordinatePerm s.L s.m π ε x) =
      TorusMetric.torusEuclidNorm x := by
  rw [torusEuclidNorm_eq_sqrt, torusEuclidNorm_eq_sqrt]
  congr 1
  rw [← Equiv.sum_comp π fun μ => ‖x μ‖ ^ 2]
  refine Finset.sum_congr rfl fun μ _ => ?_
  change ‖((ε μ : ℤˣ) : ℤ) • x (π μ)‖ ^ 2 = ‖x (π μ)‖ ^ 2
  rcases Int.units_eq_one_or (ε μ) with h | h <;> simp [h]
theorem torusEuclidNorm_sub_signedCoordinatePerm (s : Conventions.StandingParameters)
    (π : Equiv.Perm (Fin 4)) (ε : Fin 4 → ℤˣ) (x y : s.Torus) :
    TorusMetric.torusEuclidNorm (PeriodicLattice.signedCoordinatePerm s.L s.m π ε x -
      PeriodicLattice.signedCoordinatePerm s.L s.m π ε y) =
      TorusMetric.torusEuclidNorm (x - y) := by
  have e : PeriodicLattice.signedCoordinatePerm s.L s.m π ε x -
      PeriodicLattice.signedCoordinatePerm s.L s.m π ε y =
      PeriodicLattice.signedCoordinatePerm s.L s.m π ε (x - y) := by
    funext μ
    simp [PeriodicLattice.signedCoordinatePerm, smul_sub]
  rw [e, torusEuclidNorm_signedCoordinatePerm]
theorem euclidNormVec_sub_apply (g : hyperoctahedral) (x y : Fin 4 → ℝ) :
    TorusMetric.euclidNormVec (g.1 x - g.1 y) = TorusMetric.euclidNormVec (x - y) := by
  obtain ⟨π, ε, h⟩ := g.2
  rw [h]
  simp only [TorusMetric.euclidNormVec]
  congr 1
  rw [← Equiv.sum_comp π fun μ => (x - y) μ ^ 2]
  refine Finset.sum_congr rfl fun μ _ => ?_
  simp only [Pi.sub_apply, TorusTransport.signedCoordinateEquiv_apply]
  rcases Int.units_eq_one_or (ε μ) with h' | h' <;> simp [h'] <;> ring
theorem isDistIsometry_actOn (s : Conventions.StandingParameters) (E : Ambient)
    (g : hyperoctahedral) : IsDistIsometry (actOn s E g) := by
  intro x y
  cases E
  · obtain ⟨π, ε, h⟩ :=
      ReflectionPositivity.TorusTuples.signedMatrixEquiv_mem_hyperoctahedralGroup s (toMatrix_mem g)
    have hx : ∀ z : Pt s .torus, actOn s .torus g z =
        PeriodicLattice.signedCoordinatePerm s.L s.m π ε z := fun z => congrArg (fun k => k z) h
    rw [hx, hx]
    exact torusEuclidNorm_sub_signedCoordinatePerm s π ε x y
  · exact euclidNormVec_sub_apply g x y
def groupOn (s : Conventions.StandingParameters) :
    (E : Ambient) → Subgroup (Equiv.Perm (Pt s E))
  | .torus => PeriodicLattice.hyperoctahedralGroup s.L s.m
  | .euclidean => hyperoctahedral
theorem mem_groupOn_iff (s : Conventions.StandingParameters) (E : Ambient)
    (r : Equiv.Perm (Pt s E)) :
    r ∈ groupOn s E ↔ ∃ g : hyperoctahedral, r = actOn s E g := by
  cases E
  · constructor
    · intro hr
      obtain ⟨S, hS, h⟩ := TorusLifts.exists_hyperoctahedralEuclidean_torusProj s.L s.m hr
      refine ⟨⟨S, hS⟩, Equiv.ext fun x => ?_⟩
      obtain ⟨y, rfl⟩ := ReflectionPositivity.TorusCutoffs.exists_proj_eq s x
      exact (h y).symm.trans (actOn_proj s .torus ⟨S, hS⟩ y).symm
    · rintro ⟨g, rfl⟩
      exact ReflectionPositivity.TorusTuples.signedMatrixEquiv_mem_hyperoctahedralGroup s
        (toMatrix_mem g)
  · exact ⟨fun hr => ⟨⟨r, hr⟩, rfl⟩, fun ⟨g, h⟩ => h ▸ g.2⟩
variable {s : Conventions.StandingParameters} {E : Ambient}
def transportAnyTuple (r : Pt s E ≃ Pt s E) (X : FunctionTuple s E) : FunctionTuple s E :=
  ⟨X.1, transportTuple r X.2⟩
def IsInvariantOnLength {Y : Type*} {n : ℕ} (r : Pt s E ≃ Pt s E)
    (φ : separatedTuples s E n → Y) : Prop :=
  ∀ X : separatedTuples s E n,
    ∃ h : transportTuple r X.1 ∈ separatedTuples s E n, φ ⟨transportTuple r X.1, h⟩ = φ X
def IsInvariantOnLengthGroup {Y : Type*} {n : ℕ} (Γ : Subgroup (Equiv.Perm (Pt s E)))
    (φ : separatedTuples s E n → Y) : Prop :=
  ∀ r ∈ Γ, IsInvariantOnLength r φ
end TorusSymmetries
end YangMills.Construction
