import YangMills.Construction.Continuum.MomentFunctionalsOnSymbolsProof
import YangMills.Construction.Continuum.TuplesInTheTwoScalesOfClasses
import Mathlib
set_option autoImplicit false
open YangMills.Construction.TorusTransport YangMills.Construction.TorusTransport.TupleVectors
open YangMills.Construction.TorusLifts (signedCoordinateEquiv)
noncomputable section
namespace YangMills.Construction.TimeAxisSymbols.StabilizerAction
theorem spaceTimePoint_apply_last (a : Fin 3 → ℝ) (t : ℝ) : spaceTimePoint a t (Fin.last 3) = t :=
  spaceTimePoint_last a t
theorem fin4_ext {x y : Fin 4 → ℝ} (hx : ∀ i : Fin 3, x i.castSucc = y i.castSucc)
    (hlast : x 3 = y 3) : x = y := by
  funext ν
  induction ν using Fin.lastCases with
  | last => exact hlast
  | cast i => exact hx i
theorem spaceTimePoint_add (a b : Fin 3 → ℝ) (t u : ℝ) :
    spaceTimePoint a t + spaceTimePoint b u = spaceTimePoint (a + b) (t + u) := by
  refine fin4_ext (fun i => ?_) ?_
  · simp only [Pi.add_apply, spaceTimePoint_castSucc]
  · simp only [Pi.add_apply, spaceTimePoint_last]
theorem smul_spaceTimePoint_zero (c : ℝ) (a : Fin 3 → ℝ) :
    c • spaceTimePoint a 0 = spaceTimePoint (c • a) 0 := by
  refine fin4_ext (fun i => ?_) ?_
  · simp only [Pi.smul_apply, spaceTimePoint_castSucc]
  · simp only [Pi.smul_apply, spaceTimePoint_last, smul_eq_mul, mul_zero]
theorem smul_timeAxisVec (t : ℝ) : t • timeAxisVec = spaceTimePoint 0 t := by
  refine fin4_ext (fun i => ?_) ?_
  · have hne : i.castSucc ≠ (3 : Fin 4) := (Fin.castSucc_lt_last i).ne
    rw [spaceTimePoint_castSucc]
    simp [PeriodicLattice.coordVec, Pi.single_eq_of_ne hne]
  · rw [spaceTimePoint_last]
    simp [PeriodicLattice.coordVec]
theorem spaceTimePoint_inj_left {a b : Fin 3 → ℝ} {t : ℝ}
    (hab : spaceTimePoint a t = spaceTimePoint b t) : a = b := by
  funext i
  have e := congrFun hab i.castSucc
  rwa [spaceTimePoint_castSucc, spaceTimePoint_castSucc] at e
theorem dotProduct_spaceTimePoint (a b : Fin 3 → ℝ) (t u : ℝ) :
    dotProduct (spaceTimePoint a t) (spaceTimePoint b u) = dotProduct a b + t * u := by
  simp only [dotProduct]
  rw [Fin.sum_univ_castSucc]
  simp only [spaceTimePoint_castSucc, spaceTimePoint_apply_last]
theorem timeReflect_apply_castSucc (x : Fin 4 → ℝ) (i : Fin 3) :
    timeReflect x i.castSucc = x i.castSucc := by
  rw [timeReflect_apply]
  fin_cases i <;> rfl
theorem timeReflect_apply_three (x : Fin 4 → ℝ) : timeReflect x 3 = -x 3 := by apply _root_.YangMills.Construction.TimeAxisSymbols.MomentFunctionals.timeReflect_last <;> assumption
theorem timeReflect_spaceTimePoint (a : Fin 3 → ℝ) (t : ℝ) :
    timeReflect (spaceTimePoint a t) = spaceTimePoint a (-t) := by
  refine fin4_ext (fun i => ?_) ?_
  · rw [timeReflect_apply_castSucc, spaceTimePoint_castSucc, spaceTimePoint_castSucc]
  · rw [timeReflect_apply_three, spaceTimePoint_last, spaceTimePoint_last]
theorem dotProduct_hyperoctahedral (w : hyperoctahedral) (x y : Fin 4 → ℝ) :
    dotProduct (w.1 x) (w.1 y) = dotProduct x y := by
  obtain ⟨_, σ, ε, rfl⟩ := w
  have hsq : ∀ μ, (((ε μ : ℤˣ) : ℤ) : ℝ) * (((ε μ : ℤˣ) : ℤ) : ℝ) = 1 := fun μ => by
    rcases Int.units_eq_one_or (ε μ) with h | h <;> simp [h]
  simp only [dotProduct, signedCoordinateEquiv_apply]
  calc ∑ μ, (((ε μ : ℤˣ) : ℤ) : ℝ) * x (σ μ) * ((((ε μ : ℤˣ) : ℤ) : ℝ) * y (σ μ))
      = ∑ μ, x (σ μ) * y (σ μ) := Finset.sum_congr rfl fun μ _ => by
        linear_combination (x (σ μ) * y (σ μ)) * hsq μ
    _ = ∑ μ, x μ * y μ := Equiv.sum_comp σ fun μ => x μ * y μ
theorem stabilizer_apply_three (w : timeAxisStabilizer) (x : Fin 4 → ℝ) : w.1.1 x 3 = x 3 := by apply _root_.YangMills.Construction.TimeAxisSymbols.timeAxisStabilizer_apply_last <;> assumption
theorem restrictsTo_spatialPart (w : timeAxisStabilizer) : RestrictsTo w (spatialPart w) := by
  intro a
  refine fin4_ext (fun i => ?_) ?_
  · rw [spaceTimePoint_castSucc]
    rfl
  · rw [stabilizer_apply_three, spaceTimePoint_last, spaceTimePoint_last]
theorem hyperoctahedral_map_add (w : hyperoctahedral) (x y : Fin 4 → ℝ) :
    w.1 (x + y) = w.1 x + w.1 y :=
  (hyperoctahedralLinear w).map_add x y
theorem hyperoctahedral_map_smul (w : hyperoctahedral) (c : ℝ) (x : Fin 4 → ℝ) :
    w.1 (c • x) = c • w.1 x :=
  (hyperoctahedralLinear w).map_smul c x
theorem spatialPart_add (w : timeAxisStabilizer) (a b : Fin 3 → ℝ) :
    spatialPart w (a + b) = spatialPart w a + spatialPart w b := by
  have e : spaceTimePoint (a + b) 0 = spaceTimePoint a 0 + spaceTimePoint b 0 := by
    rw [spaceTimePoint_add, add_zero]
  funext i
  show w.1.1 (spaceTimePoint (a + b) 0) i.castSucc = _
  rw [e, hyperoctahedral_map_add]
  rfl
theorem spatialPart_smul (w : timeAxisStabilizer) (c : ℝ) (a : Fin 3 → ℝ) :
    spatialPart w (c • a) = c • spatialPart w a := by
  funext i
  show w.1.1 (spaceTimePoint (c • a) 0) i.castSucc = _
  rw [← smul_spaceTimePoint_zero, hyperoctahedral_map_smul]
  rfl
theorem dotProduct_spatialPart (w : timeAxisStabilizer) (a b : Fin 3 → ℝ) :
    dotProduct (spatialPart w a) (spatialPart w b) = dotProduct a b := by
  have h := dotProduct_hyperoctahedral w.1 (spaceTimePoint a 0) (spaceTimePoint b 0)
  rw [restrictsTo_spatialPart w a, restrictsTo_spatialPart w b, dotProduct_spaceTimePoint,
    dotProduct_spaceTimePoint] at h
  simpa using h
theorem spatialPart_mul (w w' : timeAxisStabilizer) (a : Fin 3 → ℝ) :
    spatialPart (w * w') a = spatialPart w (spatialPart w' a) := by
  funext i
  show w.1.1 (w'.1.1 (spaceTimePoint a 0)) i.castSucc =
    w.1.1 (spaceTimePoint (spatialPart w' a) 0) i.castSucc
  rw [restrictsTo_spatialPart w' a]
theorem spatialPart_one (a : Fin 3 → ℝ) : spatialPart 1 a = a := by
  funext i
  exact spaceTimePoint_castSucc a 0 i
theorem exists_orthogonal_matrix_spatialPart (w : timeAxisStabilizer) :
    ∃ S ∈ Matrix.orthogonalGroup (Fin 3) ℝ, spatialPart w = Matrix.mulVec S := by
  let f : (Fin 3 → ℝ) →ₗ[ℝ] Fin 3 → ℝ :=
    { toFun := spatialPart w
      map_add' := spatialPart_add w
      map_smul' := spatialPart_smul w }
  have hmat : ∀ a, Matrix.mulVec (LinearMap.toMatrix' f) a = spatialPart w a := fun a =>
    LinearMap.toMatrix'_mulVec f a
  refine ⟨LinearMap.toMatrix' f, ?_, funext fun a => (hmat a).symm⟩
  rw [Matrix.mem_orthogonalGroup_iff']
  ext i j
  have hcol : ∀ (j k : Fin 3), LinearMap.toMatrix' f k j = spatialPart w (Pi.single j 1) k := by
    intro j k
    rw [← hmat]
    simp
  have h := dotProduct_spatialPart w (Pi.single i 1) (Pi.single j 1)
  simp only [dotProduct] at h
  simp only [Matrix.mul_apply, Matrix.transpose_apply, hcol]
  rw [h]
  simp [Pi.single_apply, Matrix.one_apply]
  by_cases e : i = j
  · simp [e]
  · simp [e, Ne.symm e]
theorem threeSpace_part :
    StabilizerSubgroup ∧ PreservesTimeCoord ∧ SpatialPartUnique ∧
      SpatialPartOrthogonal ∧ ActionOnPoints ∧ SpatialPartMul ∧ SpatialPartAdjoint := by
  have hpts : ∀ (w : timeAxisStabilizer) (a : Fin 3 → ℝ) (t : ℝ),
      w.1.1 (spaceTimePoint a t) = spaceTimePoint (spatialPart w a) t := by
    intro w a t
    have e : spaceTimePoint a t = spaceTimePoint a 0 + t • timeAxisVec := by
      rw [smul_timeAxisVec, spaceTimePoint_add, add_zero, zero_add]
    refine fin4_ext (fun i => ?_) ?_
    · rw [spaceTimePoint_castSucc]
      have hfix : w.1.1 timeAxisVec = timeAxisVec := w.2
      rw [e, hyperoctahedral_map_add, hyperoctahedral_map_smul, hfix, restrictsTo_spatialPart w a,
        smul_timeAxisVec, spaceTimePoint_add, spaceTimePoint_castSucc]
      simp
    · rw [stabilizer_apply_three, spaceTimePoint_last, spaceTimePoint_last]
  refine ⟨⟨timeAxisStabilizer, rfl, rfl⟩, stabilizer_apply_three,
    fun w => ⟨?_, restrictsTo_spatialPart w⟩,
    fun w => ⟨⟨spatialPart_add w, spatialPart_smul w⟩, exists_orthogonal_matrix_spatialPart w⟩, hpts,
    spatialPart_mul, fun w a p => ?_⟩
  · refine ExistsUnique.intro _ (restrictsTo_spatialPart w) fun φ hφ => funext fun a => ?_
    exact spaceTimePoint_inj_left ((hφ a).symm.trans (restrictsTo_spatialPart w a))
  · have e : spatialPart w (spatialPart w⁻¹ p) = p := by
      rw [← spatialPart_mul, mul_inv_cancel, spatialPart_one]
    calc dotProduct (spatialPart w a) p
        = dotProduct (spatialPart w a) (spatialPart w (spatialPart w⁻¹ p)) := by rw [e]
      _ = dotProduct a (spatialPart w⁻¹ p) := dotProduct_spatialPart w _ _
theorem reflection_translation_part (hact : ActionOnPoints) :
    CommRelations ∧ PreserveUpperHalf ∧ ReflectSwapsHalves := by
  refine ⟨fun w a t => ?_, fun w a t ht => ⟨fun x hx => ?_, fun x hx => ?_, fun x hx => ?_⟩, ?_, ?_⟩
  · refine ⟨funext fun x => ?_, funext fun x => ?_, funext fun x => ?_, funext fun x => ?_,
      funext fun x => ?_⟩ <;>
      rw [← spaceTimePoint_init x] <;>
      simp only [Function.comp_apply, translationEquiv_apply, smul_timeAxisVec, spaceTimePoint_add,
        timeReflect_spaceTimePoint, hact w, add_zero]
    · congr 1
      ring
    · have e : spatialPart w ((fun i => x i.castSucc) + a) =
          spatialPart w (fun i => x i.castSucc) + spatialPart w a :=
        spatialPart_add w _ _
      rw [e]
  · have h : (x + t • timeAxisVec) 3 = x 3 + t := by
      rw [smul_timeAxisVec, Pi.add_apply, spaceTimePoint_last]
    have hx' : 0 < x 3 := hx
    show 0 < (translationEquiv (t • timeAxisVec) x) 3
    rw [translationEquiv_apply, h]
    linarith
  · have h : (x + spaceTimePoint a 0) 3 = x 3 := by
      rw [Pi.add_apply, spaceTimePoint_last, add_zero]
    show 0 < (translationEquiv (spaceTimePoint a 0) x) 3
    rw [translationEquiv_apply, h]
    exact hx
  · show 0 < w.1.1 x 3
    rw [stabilizer_apply_three]
    exact hx
  · ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      have hy' : 0 < y 3 := hy
      show timeReflect y 3 < 0
      rw [timeReflect_apply_three]
      linarith
    · intro hx
      have hx' : x 3 < 0 := hx
      refine ⟨timeReflect x, ?_, timeReflect_timeReflect x⟩
      show 0 < timeReflect x 3
      rw [timeReflect_apply_three]
      linarith
  · ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      have hy' : y 3 < 0 := hy
      show 0 < timeReflect y 3
      rw [timeReflect_apply_three]
      linarith
    · intro hx
      have hx' : 0 < x 3 := hx
      refine ⟨timeReflect x, ?_, timeReflect_timeReflect x⟩
      show timeReflect x 3 < 0
      rw [timeReflect_apply_three]
      linarith
theorem isEuclideanMotion_comp {f g : (Fin 4 → ℝ) → Fin 4 → ℝ} (hf : IsEuclideanMotion f)
    (hg : IsEuclideanMotion g) : IsEuclideanMotion (f ∘ g) := by
  obtain ⟨A, hA, v, rfl⟩ := hf
  obtain ⟨B, hB, u, rfl⟩ := hg
  refine ⟨A * B, mul_mem hA hB, Matrix.mulVec A u + v, funext fun x => ?_⟩
  simp [orthoAffine, Matrix.mulVec_add, Matrix.mulVec_mulVec, add_assoc]
theorem toPerm_symm_comp_apply {f g : (Fin 4 → ℝ) → Fin 4 → ℝ} (hf : IsEuclideanMotion f)
    (hg : IsEuclideanMotion g) (hfg : IsEuclideanMotion (f ∘ g))
    (x : Fin 4 → ℝ) : hfg.toPerm.symm x = hg.toPerm.symm (hf.toPerm.symm x) := by
  refine (Equiv.symm_apply_eq _).mpr ?_
  have e₁ : g (hg.toPerm.symm (hf.toPerm.symm x)) = hf.toPerm.symm x :=
    hg.toPerm.apply_symm_apply _
  have e₂ : f (hf.toPerm.symm x) = x := hf.toPerm.apply_symm_apply x
  show x = f (g (hg.toPerm.symm (hf.toPerm.symm x)))
  rw [e₁, e₂]
theorem familyAct_append {E : Type*} {f : (Fin 4 → ℝ) → Fin 4 → ℝ} (hf : IsEuclideanMotion f)
    {m n : ℕ} (φ : Fin m → (Fin 4 → ℝ) → E) (ψ : Fin n → (Fin 4 → ℝ) → E) :
    Fin.append (familyAct hf φ) (familyAct hf ψ) = familyAct hf (Fin.append φ ψ) := by
  funext i
  induction i using Fin.addCases with
  | left i => simp only [Fin.append_left, familyAct]
  | right j => simp only [Fin.append_right, familyAct]
theorem symbols_part (D : TransportData)
    (hmove : TwoScaleMembership.MotionsPreserveTuples D) : MotionsOnSymbols D := by
  intro f g hf hg X Y
  have hsupp : ∀ (Z : SpaceTimeSymbol D) (i : Fin Z.1.1),
      entrySupp D (familyAct hf Z.1.2 i) = f '' entrySupp D (Z.1.2 i) := fun Z =>
    (hmove f hf Z.1 Z.2).2.2.1
  refine ⟨actAny_mem_spaceTimeSymbols hf X.2, hsupp X, ⟨isEuclideanMotion_comp hf hg, ?_⟩,
    fun hd => ?_⟩
  · refine Subtype.ext (Sigma.ext rfl (heq_of_eq (funext fun i => funext fun x => ?_)))
    show X.1.2 i (hg.toPerm.symm (hf.toPerm.symm x)) =
      X.1.2 i ((isEuclideanMotion_comp hf hg).toPerm.symm x)
    rw [toPerm_symm_comp_apply hf hg]
  · have hd' : AppendDefined D (motionSymbol hf X).1 (motionSymbol hf Y).1 := by
      refine (appendDefined_iff (motionSymbol hf X).2 (motionSymbol hf Y).2).mpr
        fun (i : Fin X.1.1) (j : Fin Y.1.1) => ?_
      have e := (appendDefined_iff X.2 Y.2).mp hd i j
      show Disjoint (entrySupp D (familyAct hf X.1.2 i)) (entrySupp D (familyAct hf Y.1.2 j))
      rw [hsupp X, hsupp Y]
      exact (Set.disjoint_image_iff hf.bijective.injective).mpr e
    exact ⟨hd', Subtype.ext (Sigma.ext rfl (heq_of_eq (familyAct_append hf X.1.2 Y.1.2)))⟩
theorem statement_holds (htwo : TwoScaleMembership.Statement) : Statement := by
  have hthree := threeSpace_part
  exact ⟨hthree, reflection_translation_part hthree.2.2.2.2.1,
    fun D => symbols_part D (htwo D).1⟩
end YangMills.Construction.TimeAxisSymbols.StabilizerAction
end
