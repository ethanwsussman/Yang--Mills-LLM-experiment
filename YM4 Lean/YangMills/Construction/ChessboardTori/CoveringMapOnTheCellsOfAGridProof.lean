import YangMills.Construction.ChessboardTori.ChessboardEstimateAndSubadditivityProof
import YangMills.Construction.ChessboardTori.CoveringMapOnTheCellsOfAGrid
import YangMills.Construction.ChessboardTori.DistanceToFacePlanesAndOpenCells
import YangMills.Construction.ChessboardTori.MirrorPeriodicWeightsAsCellFunctionsProof
import Mathlib
set_option autoImplicit false
open Set
open scoped ENNReal
noncomputable section
namespace YangMills.Construction.ChessboardTori
open InfiniteLattice (AmbientSpace)
open TorusMetric (euclidNormVec torusEuclidNorm setEuclidDist)
namespace ProjOnGridCellsProof
theorem int_eq_zero_of_mul_bounds {l : ℝ} (hl : 0 < l) (j : ℤ) (hup : l * j < l) (hlo : -l < l * j) :
    j = 0 := by
  have r1 : (j : ℝ) < 1 := by
    by_contra h
    rw [not_lt] at h
    nlinarith
  have r2 : (-1 : ℝ) < j := by
    by_contra h
    rw [not_lt] at h
    nlinarith
  have z1 : j < 1 := by exact_mod_cast r1
  have z2 : -1 < j := by exact_mod_cast r2
  omega
theorem abs_le_abs_add_int_mul {l d : ℝ} (hl : 0 < l) (hd : 2 * |d| ≤ l) (j : ℤ) :
    |d| ≤ |d + l * j| := by
  by_cases hj : j = 0
  · simp [hj]
  have h1 : (1 : ℝ) ≤ |(j : ℝ)| := by
    have : 1 ≤ |j| := Int.one_le_abs hj
    exact_mod_cast this
  have h2 : l ≤ |l * j| := by
    rw [abs_mul, abs_of_pos hl]
    nlinarith
  have h3 := abs_sub_abs_le_abs_sub (l * (j : ℝ)) (-d)
  rw [abs_neg, sub_neg_eq_add, add_comm (l * (j : ℝ)) d] at h3
  linarith
theorem euclidNormVec_mono {x y : Fin 4 → ℝ} (h : ∀ μ, |x μ| ≤ |y μ|) :
    euclidNormVec x ≤ euclidNormVec y :=
  Real.sqrt_le_sqrt (Finset.sum_le_sum fun μ _ => sq_le_sq.2 (h μ))
theorem interior_cube_eq (a : AmbientSpace) (c : ℝ) :
    interior {x : AmbientSpace | ∀ μ, x μ - a μ ∈ Icc 0 c} =
      {x : AmbientSpace | ∀ μ, x μ - a μ ∈ Ioo 0 c} := by
  have h : {x : AmbientSpace | ∀ μ, x μ - a μ ∈ Icc 0 c} =
      Set.pi univ fun μ => Icc (a μ) (a μ + c) := by
    ext x
    simp only [mem_ofPred_eq, mem_pi, mem_univ, true_implies, mem_Icc]
    exact forall_congr' fun μ => by constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith
  rw [h, interior_pi_set finite_univ]
  ext x
  simp only [interior_Icc, mem_pi, mem_univ, true_implies, mem_Ioo, mem_ofPred_eq]
  exact forall_congr' fun μ => by constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith
variable {D : ChessboardSetup}
theorem proj_sub (u v : AmbientSpace) :
    D.proj (u - v) = D.proj u - D.proj v := by
  funext μ
  simp [ChessboardSetup.proj, TorusMetric.torusProj]
theorem proj_eq_proj_iff (u v : AmbientSpace) :
    D.proj u = D.proj v ↔
      ∃ j : Fin 4 → ℤ, ∀ μ, u μ = v μ + PeriodicLattice.torusSide D.L D.m * j μ := by
  constructor
  · intro h
    have h' : ∀ μ, ∃ n : ℤ, n • PeriodicLattice.torusSide D.L D.m = u μ - v μ := fun μ => by
      have h1 := congrFun h μ
      simp only [ChessboardSetup.proj, TorusMetric.torusProj] at h1
      rw [← sub_eq_zero, ← AddCircle.coe_sub, AddCircle.coe_eq_zero_iff] at h1
      exact h1
    choose j hj using h'
    refine ⟨j, fun μ => ?_⟩
    have h2 := hj μ
    simp only [zsmul_eq_mul] at h2
    rw [mul_comm]
    linarith
  · rintro ⟨j, hj⟩
    funext μ
    simp only [ChessboardSetup.proj, TorusMetric.torusProj]
    rw [← sub_eq_zero, ← AddCircle.coe_sub, AddCircle.coe_eq_zero_iff]
    refine ⟨j μ, ?_⟩
    rw [hj μ, zsmul_eq_mul]
    ring
variable (g : ReflectionGrid D)
theorem cellSide_pos : 0 < g.cellSide := by apply _root_.YangMills.Construction.ChessboardTori.ChessboardEstimateAndSubadditivity.cellSide_pos <;> assumption
theorem mem_interior_cell (k : Fin 4 → ℤ) (x : AmbientSpace) :
    x ∈ interior (g.cell k) ↔ ∀ μ, x μ - (g.origin μ + g.cellSide * k μ) ∈ Ioo 0 g.cellSide := by apply _root_.YangMills.Construction.ChessboardTori.ReflectionPeriodicWeightsAsCellFunctions.mem_interior_cell_iff <;> assumption
theorem mem_interior_block (k : Fin 4 → ℤ) (x : AmbientSpace) :
    x ∈ interior (g.block k) ↔
      ∀ μ, x μ - (g.origin μ + g.cellSide * k μ) ∈ Ioo 0 (PeriodicLattice.torusSide D.L D.m) :=
  Set.ext_iff.mp
    (interior_cube_eq (fun μ => g.origin μ + g.cellSide * k μ)
      (PeriodicLattice.torusSide D.L D.m)) x
theorem translate_mem_walls {n : ℤ} (hn : PeriodicLattice.torusSide D.L D.m = n * g.cellSide)
    (j : Fin 4 → ℤ) {w : AmbientSpace} (hw : w ∈ g.walls) :
    (fun μ => w μ + PeriodicLattice.torusSide D.L D.m * j μ) ∈ g.walls := by
  simp only [ReflectionGrid.walls, mem_iUnion, ReflectionGrid.wall, mem_ofPred_eq] at hw ⊢
  obtain ⟨μ, k, hk⟩ := hw
  refine ⟨μ, k + n * j μ, ?_⟩
  rw [hk, hn]
  push_cast
  ring
theorem translate_mem_cell {n : ℤ} (hn : PeriodicLattice.torusSide D.L D.m = n * g.cellSide)
    (j k : Fin 4 → ℤ) {x : AmbientSpace} (hx : x ∈ g.cell k) :
    (fun μ => x μ + PeriodicLattice.torusSide D.L D.m * j μ) ∈
      g.cell (fun μ => k μ + n * j μ) := by
  intro μ
  have h := hx μ
  have e : x μ + PeriodicLattice.torusSide D.L D.m * j μ -
      (g.origin μ + g.cellSide * ((k μ + n * j μ : ℤ) : ℝ)) =
        x μ - (g.origin μ + g.cellSide * k μ) := by
    rw [hn]
    push_cast
    ring
  simpa only [e] using h
theorem proj_image_translated_cell {n : ℤ}
    (hn : PeriodicLattice.torusSide D.L D.m = n * g.cellSide) (j k : Fin 4 → ℤ) :
    D.proj '' g.cell (fun μ => k μ + n * j μ) = D.proj '' g.cell k := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    have h := translate_mem_cell g hn (-j) _ hx
    have e : (fun μ => (k μ + n * j μ) + n * (-j) μ) = k := by
      funext μ
      simp
    rw [e] at h
    refine ⟨_, h, (proj_eq_proj_iff _ _).2 ⟨-j, fun μ => rfl⟩⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨_, translate_mem_cell g hn j k hx, (proj_eq_proj_iff _ _).2 ⟨j, fun μ => rfl⟩⟩
theorem euclidInfDist_nonneg (y : AmbientSpace) (A : Set AmbientSpace) :
    0 ≤ euclidInfDist y A := by
  refine Real.sInf_nonneg ?_
  rintro _ ⟨w, -, rfl⟩
  exact Real.sqrt_nonneg _
theorem setEuclidDist_proj_walls {n : ℤ}
    (hn : PeriodicLattice.torusSide D.L D.m = n * g.cellSide) (u : AmbientSpace) :
    setEuclidDist {D.proj u} (D.proj '' g.walls) =
      ENNReal.ofReal (euclidInfDist u g.walls) := by
  have hne : g.walls.Nonempty := ⟨g.origin, by
    simp only [ReflectionGrid.walls, mem_iUnion, ReflectionGrid.wall, mem_ofPred_eq]
    exact ⟨0, 0, by simp⟩⟩
  have bdd : BddBelow ((fun w => euclidNormVec (u - w)) '' g.walls) :=
    ⟨0, by rintro _ ⟨w, -, rfl⟩; exact Real.sqrt_nonneg _⟩
  have lower : ∀ w ∈ g.walls, euclidInfDist u g.walls ≤
      torusEuclidNorm (D.proj u - D.proj w) := by
    intro w hw
    refine le_csInf ⟨_, u - w, proj_sub (D := D) u w, rfl⟩ ?_
    rintro _ ⟨z, hz, rfl⟩
    have hz' : D.proj z = D.proj (u - w) := by
      rw [proj_sub]
      exact hz
    obtain ⟨j, hj⟩ := (proj_eq_proj_iff z (u - w)).1 hz'
    refine csInf_le bdd ⟨_, translate_mem_walls g hn (-j) hw, ?_⟩
    have e : u - (fun μ => w μ + PeriodicLattice.torusSide D.L D.m * ((-j) μ : ℤ)) = z := by
      funext μ
      have := hj μ
      simp only [Pi.sub_apply, Pi.neg_apply, Int.cast_neg] at this ⊢
      rw [this]
      ring
    simp only [e]
  have upper : ∀ w : AmbientSpace, torusEuclidNorm (D.proj u - D.proj w) ≤
      euclidNormVec (u - w) := by
    intro w
    refine csInf_le ⟨0, ?_⟩ ⟨u - w, proj_sub (D := D) u w, rfl⟩
    rintro _ ⟨v, -, rfl⟩
    exact Real.sqrt_nonneg _
  simp only [setEuclidDist, mem_singleton_iff, iInf_iInf_eq_left, iInf_image]
  apply le_antisymm
  · have hI : ∀ w ∈ g.walls,
        (⨅ w ∈ g.walls, ENNReal.ofReal (torusEuclidNorm (D.proj u - D.proj w))) ≤
        ENNReal.ofReal (euclidNormVec (u - w)) := fun w hw =>
      (iInf₂_le w hw).trans (ENNReal.ofReal_le_ofReal (upper w))
    obtain ⟨w0, hw0⟩ := hne
    have htop := ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hI w0 hw0)
    rw [← ENNReal.ofReal_toReal htop]
    apply ENNReal.ofReal_le_ofReal
    refine le_csInf ⟨_, w0, hw0, rfl⟩ ?_
    rintro _ ⟨w, hw, rfl⟩
    exact ENNReal.toReal_le_of_le_ofReal (Real.sqrt_nonneg _) (hI w hw)
  · exact le_iInf₂ fun w hw => ENNReal.ofReal_le_ofReal (lower w hw)
end ProjOnGridCellsProof
open ProjOnGridCellsProof in
theorem ProjOnGridCells.statement_holds (hW : WallDistanceAndOpenCells.Statement)
    (hR : ReflectionGridArithmetic.Statement) : ProjOnGridCells.Statement := by
  intro D g hl
  have hs := cellSide_pos g
  have hlpos : 0 < PeriodicLattice.torusSide D.L D.m := by linarith
  obtain ⟨⟨-, hcount, -, -⟩, -⟩ := ((hR D).2.2.2 g).2 hl
  have hn : PeriodicLattice.torusSide D.L D.m = (g.cellsPerTorusSide : ℝ) * g.cellSide := by
    rw [← hcount, ReflectionGrid.cellsAcross, div_mul_cancel₀ _ hs.ne']
  refine ⟨?_, ?_, setEuclidDist_proj_walls g hn, ?_⟩
  · rintro _ ⟨k, rfl⟩ u hu v hv huv
    obtain ⟨j, hj⟩ := (proj_eq_proj_iff u v).1 huv
    funext μ
    have a := ((mem_interior_block g k u).1 hu μ)
    have b := ((mem_interior_block g k v).1 hv μ)
    have e := hj μ
    have hz : j μ = 0 := int_eq_zero_of_mul_bounds hlpos _ (by linarith [a.1, a.2, b.1, b.2])
      (by linarith [a.1, a.2, b.1, b.2])
    rw [e, hz]
    simp
  · rintro _ ⟨k, rfl⟩ u hu v hv
    have hd : ∀ μ, 2 * |(u - v) μ| ≤ PeriodicLattice.torusSide D.L D.m := by
      intro μ
      have a := hu μ
      have b := hv μ
      have : |(u - v) μ| ≤ g.cellSide := by
        rw [Pi.sub_apply, abs_le]
        constructor <;> linarith [a.1, a.2, b.1, b.2]
      linarith
    apply le_antisymm
    · refine csInf_le ⟨0, ?_⟩ ⟨u - v, proj_sub (D := D) u v, rfl⟩
      rintro _ ⟨w, -, rfl⟩
      exact Real.sqrt_nonneg _
    · refine le_csInf ⟨_, u - v, proj_sub (D := D) u v, rfl⟩ ?_
      rintro _ ⟨z, hz, rfl⟩
      have hz' : D.proj z = D.proj (u - v) := by
        rw [proj_sub]
        exact hz
      obtain ⟨j, hj⟩ := (proj_eq_proj_iff z (u - v)).1 hz'
      refine euclidNormVec_mono fun μ => ?_
      rw [hj μ]
      exact abs_le_abs_add_int_mul hlpos (hd μ) (j μ)
  · rintro _ ⟨k, rfl⟩ _ ⟨k', rfl⟩ hne _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    rw [setEuclidDist_proj_walls g hn, setEuclidDist_proj_walls g hn,
      ← ENNReal.ofReal_add (euclidInfDist_nonneg _ _) (euclidInfDist_nonneg _ _)]
    apply ENNReal.ofReal_le_ofReal
    refine le_csInf ⟨_, a - b, proj_sub (D := D) a b, rfl⟩ ?_
    rintro _ ⟨z, hz, rfl⟩
    have hz' : D.proj z = D.proj (a - b) := by
      rw [proj_sub]
      exact hz
    obtain ⟨j, hj⟩ := (proj_eq_proj_iff z (a - b)).1 hz'
    set a' : AmbientSpace := fun μ => a μ + PeriodicLattice.torusSide D.L D.m * j μ with ha'
    have hproj : D.proj a' = D.proj a :=
      (proj_eq_proj_iff _ _).2 ⟨j, fun μ => rfl⟩
    have hint : a' ∈ interior (g.cell (fun μ => k μ + g.cellsPerTorusSide * j μ)) := by
      rw [mem_interior_cell]
      intro μ
      have h := (mem_interior_cell g k a).1 ha μ
      have e : a' μ - (g.origin μ +
          g.cellSide * ((k μ + g.cellsPerTorusSide * j μ : ℤ) : ℝ)) =
          a μ - (g.origin μ + g.cellSide * k μ) := by
        simp only [ha']
        rw [hn]
        push_cast
        ring
      rw [e]
      exact h
    have hcell : g.cell (fun μ => k μ + g.cellsPerTorusSide * j μ) ≠ g.cell k' := fun h =>
      hne (by rw [← h, proj_image_translated_cell g hn])
    have h3 := ((hW D g).2.2.1 _ ⟨_, rfl⟩ _ ⟨k', rfl⟩ hcell a' hint b hb).2
    have hsame : euclidInfDist a' g.walls = euclidInfDist a g.walls := by
      have h := (setEuclidDist_proj_walls g hn a').symm.trans ((congrArg (fun x =>
        setEuclidDist {x} (D.proj '' g.walls)) hproj).trans (setEuclidDist_proj_walls g hn a))
      exact (ENNReal.ofReal_eq_ofReal_iff (euclidInfDist_nonneg _ _)
        (euclidInfDist_nonneg _ _)).1 h
    have e : a' - b = z := by
      funext μ
      have h := hj μ
      simp only [Pi.sub_apply] at h ⊢
      rw [h]
      simp only [ha']
      ring
    rw [hsame, e] at h3
    exact h3
end YangMills.Construction.ChessboardTori
end
