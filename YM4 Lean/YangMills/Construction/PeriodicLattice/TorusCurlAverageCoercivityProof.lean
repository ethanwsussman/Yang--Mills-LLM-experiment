import YangMills.Construction.Lattice.TwoScaleOperatorDefs
import YangMills.Construction.TorusForms.CurlAndAverageBoundOnIntegerLattice
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.PeriodicLattice.TorusCurlAverage
open IntegerLattice renaming ScaledSite → ZSite, Edge → ZEdge, Face → ZFace,
  EdgeForm → ZForm, discreteCurl → zcurl, cube → zcube, coordinateContour → zcontour,
  blockAverage → zaverage, edgesMeeting → zedgesMeeting, edgeNormSq → zNormSq
open IntegerLattice (unitCubesOver edgesMeeting_finite_of_finite)
section Coordinates
variable {d N : ℕ}
def latticePoint (s : Mesh N) (a : Fin d → ℤ) : GridPoint d s :=
  ⟨fun μ => a μ • ((s.h : ℝ) : AddCircle (N : ℝ)), fun _ _ =>
    AddSubgroup.mem_zmultiples_iff.mpr ⟨_, rfl⟩⟩
theorem latticePoint_add (s : Mesh N) (a b : Fin d → ℤ) :
    latticePoint s (a + b) = latticePoint s a + latticePoint s b :=
  Subtype.ext (funext fun μ => add_zsmul _ (a μ) (b μ))
theorem latticePoint_zero (s : Mesh N) : latticePoint s (0 : Fin d → ℤ) = 0 :=
  Subtype.ext (funext fun _ => zero_zsmul _)
theorem latticePoint_sub (s : Mesh N) (a b : Fin d → ℤ) :
    latticePoint s (a - b) = latticePoint s a - latticePoint s b :=
  Subtype.ext (funext fun μ => sub_zsmul _ (a μ) (b μ))
theorem zsmul_mesh_eq_zero_iff (s : Mesh N) (k : ℤ) :
    k • ((s.h : ℝ) : AddCircle (N : ℝ)) = 0 ↔ (s.count : ℤ) ∣ k := by
  have hh := s.h_pos.ne'
  have hz : k • ((s.h : ℝ) : AddCircle (N : ℝ)) = (((k : ℝ) * s.h : ℝ) : AddCircle (N : ℝ)) := by
    rw [← AddCircle.coe_zsmul, zsmul_eq_mul]
  rw [hz, AddCircle.coe_eq_zero_iff]
  constructor
  · rintro ⟨n, hn⟩
    refine ⟨n, ?_⟩
    rw [zsmul_eq_mul, s.period_eq] at hn
    have h2 : (n : ℝ) * s.count = k := by
      apply mul_right_cancel₀ hh
      rw [← hn]
      ring
    have : n * (s.count : ℤ) = k := by exact_mod_cast h2
    rw [← this]
    ring
  · rintro ⟨n, rfl⟩
    refine ⟨n, ?_⟩
    rw [zsmul_eq_mul, s.period_eq]
    push_cast
    ring
theorem latticePoint_eq_zero_iff (s : Mesh N) (a : Fin d → ℤ) :
    latticePoint s a = 0 ↔ ∀ μ, (s.count : ℤ) ∣ a μ := by
  constructor
  · intro h μ
    have := congrArg (fun x : GridPoint d s => (x : Torus d N) μ) h
    exact (zsmul_mesh_eq_zero_iff s (a μ)).mp this
  · intro h
    exact Subtype.ext (funext fun μ => (zsmul_mesh_eq_zero_iff s (a μ)).mpr (h μ))
theorem latticePoint_eq_iff (s : Mesh N) (a b : Fin d → ℤ) :
    latticePoint s a = latticePoint s b ↔ ∀ μ, (s.count : ℤ) ∣ a μ - b μ := by
  rw [← sub_eq_zero, ← latticePoint_sub, latticePoint_eq_zero_iff]
  rfl
theorem latticePoint_surjective (s : Mesh N) : Function.Surjective (latticePoint (d := d) s) := by
  intro x
  have h : ∀ μ, ∃ k : ℤ, k • ((s.h : ℝ) : AddCircle (N : ℝ)) = (x : Torus d N) μ := fun μ =>
    AddSubgroup.mem_zmultiples_iff.mp (x.2 μ (Set.mem_univ μ))
  choose a ha using h
  exact ⟨a, Subtype.ext (funext ha)⟩
def intCube (d : ℕ) (n : ℤ) : Finset (Fin d → ℤ) := Fintype.piFinset fun _ => Finset.Ico 0 n
theorem mem_intCube {n : ℤ} {a : Fin d → ℤ} : a ∈ intCube d n ↔ ∀ μ, 0 ≤ a μ ∧ a μ < n := by
  simp [intCube, Fintype.mem_piFinset]
def intBox (d : ℕ) (l r : ℤ) : Finset (Fin d → ℤ) := Fintype.piFinset fun _ => Finset.Ico l r
theorem mem_intBox {l r : ℤ} {a : Fin d → ℤ} :
    a ∈ intBox d l r ↔ ∀ μ, l ≤ a μ ∧ a μ < r := by
  simp [intBox, Fintype.mem_piFinset]
theorem card_intBox (l r : ℤ) (h : l ≤ r) :
    ((intBox d l r).card : ℝ) = ((r : ℝ) - l) ^ d := by
  simp only [intBox, Fintype.card_piFinset, Int.card_Ico, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin]
  have h1 : (((r - l).toNat : ℤ) : ℝ) = ((r - l : ℤ) : ℝ) := by
    rw [Int.toNat_of_nonneg (by omega)]
  push_cast at h1 ⊢
  rw [h1]
theorem coe_latticePoint (s : Mesh N) (a : Fin d → ℤ) (μ : Fin d) :
    (latticePoint s a : Torus d N) μ = (((a μ : ℝ) * s.h : ℝ) : AddCircle (N : ℝ)) := by
  change a μ • ((s.h : ℝ) : AddCircle (N : ℝ)) = _
  rw [← AddCircle.coe_zsmul, zsmul_eq_mul]
end Coordinates
section IntegerCoordinates
variable {d L : ℕ}
def toPoint (v : Fin d → ℤ) : ZSite d 1 := ⟨v, IntegerLattice.mem_scaledLattice_one v⟩
def coarseCoords (y : ZSite d L) : Fin d → ℤ := fun μ => (y : Fin d → ℤ) μ / (L : ℤ)
theorem coe_basisStep (s : ℕ) (μ : Fin d) :
    ((IntegerLattice.basisStep d s μ : ZSite d s) : Fin d → ℤ) = (s : ℤ) • Pi.single μ 1 := by
  funext ν
  by_cases h : ν = μ
  · subst h
    simp [IntegerLattice.basisStep]
  · simp [IntegerLattice.basisStep, Pi.single_eq_of_ne h]
end IntegerCoordinates
section Projection
variable (T : Lattice.LatticeParameters) {j N : ℕ} (S : Scales T.d T.L j N)
theorem blockSide_pos : 0 < T.L := by
  have := T.two_le_L
  omega
theorem unitCount_eq : (S.unitMesh.count : ℤ) = N := rfl
def coarseSite (y : ZSite T.d T.L) : GridPoint T.d S.coarseMesh :=
  latticePoint S.coarseMesh (coarseCoords y)
def projectEdge (b : ZEdge T.d 1) : Link T.d S.unitMesh :=
  (b.2, latticePoint S.unitMesh (b.1 : Fin T.d → ℤ))
theorem mem_coarseCell_iff (a : Fin T.d → ℤ) (u : GridPoint T.d S.unitMesh) :
    u ∈ S.coarseCell (latticePoint S.coarseMesh a) ↔
      ∃ w ∈ intCube T.d (T.L : ℤ), u = latticePoint S.unitMesh ((T.L : ℤ) • a + w) := by
  have h1 : S.coarseMesh.h = T.L := rfl
  have h2 : S.unitMesh.h = 1 := rfl
  simp only [Scales.coarseCell, sitesInCube, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨r, hr, hu⟩
    obtain ⟨b, rfl⟩ := latticePoint_surjective S.unitMesh u
    have hμ : ∀ μ, ∃ n : ℤ, n • (N : ℝ) = (b μ : ℝ) - T.L * a μ - r μ := by
      intro μ
      have h := congrFun hu μ
      rw [Pi.add_apply, coe_latticePoint, coe_latticePoint, h1, h2, eq_comm, ← AddCircle.coe_add,
        ← sub_eq_zero, ← AddCircle.coe_sub] at h
      obtain ⟨n, hn⟩ := (AddCircle.coe_eq_zero_iff (N : ℝ)).mp h
      exact ⟨-n, by rw [neg_smul, hn]; ring⟩
    choose n hn using hμ
    refine ⟨fun μ => b μ - T.L * a μ - n μ * N, ?_, ?_⟩
    · rw [mem_intCube]
      intro μ
      have hr' : r μ = ((b μ - T.L * a μ - n μ * N : ℤ) : ℝ) := by
        have := hn μ
        rw [zsmul_eq_mul] at this
        push_cast
        linarith
      have h0 := (hr μ).1
      have h3 := (hr μ).2
      rw [hr'] at h0 h3
      exact ⟨by exact_mod_cast h0, by exact_mod_cast h3⟩
    · rw [latticePoint_eq_iff, unitCount_eq]
      intro μ
      exact ⟨n μ, by simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring⟩
  · rintro ⟨w, hw, rfl⟩
    rw [mem_intCube] at hw
    refine ⟨fun μ => (w μ : ℝ), fun μ => ⟨?_, ?_⟩, ?_⟩
    · change (0 : ℝ) ≤ (w μ : ℝ)
      exact_mod_cast (hw μ).1
    · change (w μ : ℝ) < T.L
      exact_mod_cast (hw μ).2
    · funext μ
      rw [Pi.add_apply, coe_latticePoint, coe_latticePoint, h1, h2, ← AddCircle.coe_add]
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      push_cast
      congr 1
      ring
variable {T}
theorem inBlockIndexRange_iff (hT : T.offset = 0) (σ : Fin T.d → ℤ) :
    BlockSpin.InBlockIndexRange T 1 σ ↔ σ ∈ intCube T.d (T.L : ℤ) := by
  have h0 : BlockSpin.blockOffset T 1 = 0 := by
    simp [BlockSpin.blockOffset, hT]
  rw [mem_intCube]
  simp only [BlockSpin.InBlockIndexRange, h0]
  constructor
  · intro h μ
    have := h μ
    simp only [Nat.cast_zero, neg_zero, pow_one, sub_zero] at this
    omega
  · intro h μ
    have := h μ
    simp only [Nat.cast_zero, neg_zero, pow_one, sub_zero]
    omega
theorem mem_zcube_iff (hT : T.offset = 0) (y : ZSite T.d T.L) (x : ZSite T.d 1) :
    x ∈ zcube T y ↔ ∃ w ∈ intCube T.d (T.L : ℤ), (x : Fin T.d → ℤ) = (y : Fin T.d → ℤ) + w := by
  constructor
  · rintro ⟨σ, hσ, hx⟩
    exact ⟨σ, (inBlockIndexRange_iff hT σ).mp hσ, hx⟩
  · rintro ⟨σ, hσ, hx⟩
    exact ⟨σ, (inBlockIndexRange_iff hT σ).mpr hσ, hx⟩
end Projection
section Paths
variable {d : ℕ}
end Paths
section Lift
variable {T : Lattice.LatticeParameters} {j N : ℕ} (S : Scales T.d T.L j N)
end Lift
section Periodic
variable {T : Lattice.LatticeParameters} {j N : ℕ} (S : Scales T.d T.L j N)
  (Λ' : Set (GridPoint T.d S.coarseMesh)) (B : OneForm T.d S.unitMesh)
def liftedCoarseSites (n : ℤ) : Set (ZSite T.d T.L) :=
  {y | (y : Fin T.d → ℤ) ∈ intCube T.d n ∧ coarseSite T S y ∈ Λ'}
theorem liftedCoarseSites_finite (n : ℤ) : (liftedCoarseSites S Λ' n).Finite :=
  ((intCube T.d n).finite_toSet.preimage Subtype.val_injective.injOn).subset fun _ hy => hy.1
theorem unionOfCubes_finite (hT : T.offset = 0) {X : Set (ZSite T.d T.L)} (hX : X.Finite) :
    (unitCubesOver T X).Finite := by
  refine (hX.biUnion fun y _ => IntegerLattice.cube_finite T y).subset ?_
  rintro x ⟨y, hy, hx⟩
  refine Set.mem_biUnion hy ((mem_zcube_iff hT y x).mpr ⟨(x : Fin T.d → ℤ) - y, ?_, by simp⟩)
  rw [mem_intCube]
  intro μ
  have := hx μ
  simp only [Pi.sub_apply]
  omega
open Classical in
def periodicLift (hT : T.offset = 0) (n : ℤ) : ZForm T.d 1 :=
  Finsupp.ofSupportFinite
    (fun b => if b ∈ zedgesMeeting (unitCubesOver T (liftedCoarseSites S Λ' n)) then
      B (projectEdge T S b) else 0)
    ((edgesMeeting_finite_of_finite
      (unionOfCubes_finite hT (liftedCoarseSites_finite S Λ' n))).subset fun b hb => by
      by_contra h
      exact hb (if_neg h))
omit S in
theorem coe_target (b : ZEdge T.d 1) :
    ((b.head : ZSite T.d 1) : Fin T.d → ℤ) = (b.1 : Fin T.d → ℤ) + Pi.single b.2 1 := by
  simp [IntegerLattice.Edge.head, coe_basisStep]
end Periodic
section Estimates
variable {T : Lattice.LatticeParameters} {j N : ℕ} (S : Scales T.d T.L j N)
  (Λ' : Set (GridPoint T.d S.coarseMesh)) (B : OneForm T.d S.unitMesh)
def boundaryShell (d : ℕ) (R n : ℤ) : Finset (Fin d → ℤ) :=
  intBox d (-R) (n + R) \ intBox d R (n - R)
theorem single_apply_zero_or_one {d : ℕ} (μ ν : Fin d) :
    (Pi.single (M := fun _ => ℤ) μ 1 ν : ℤ) = 0 ∨ (Pi.single (M := fun _ => ℤ) μ 1 ν : ℤ) = 1 := by
  by_cases h : ν = μ
  · subst h
    simp
  · simp [Pi.single_eq_of_ne h]
theorem card_intCube (d L : ℕ) : ((intCube d (L : ℤ)).card : ℝ) = (L : ℝ) ^ d := by
  have := card_intBox (d := d) 0 (L : ℤ) (by positivity)
  simp only [intBox, Int.cast_zero, sub_zero, Int.cast_natCast] at this
  exact this
end Estimates
end YangMills.Construction.PeriodicLattice.TorusCurlAverage
