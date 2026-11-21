import YangMills.Construction.TorusOrFourSpace.IteratedPartialsOfFunctionsWithContinuousPartialsProof
import YangMills.Construction.GrowingTori.LimitsAlongGrowingVolumes.FifthPartProof
import YangMills.Construction.TorusOrFourSpace.DistanceOpenSetsDerivativesAndTensorsOfSeveralPoints
import YangMills.Construction.TorusOrFourSpace.PartialsOfSumsAndProductsProof
import YangMills.Construction.TorusOrFourSpace.RulesForTensorsProof
import YangMills.Construction.TorusOrFourSpace.SmallFactsOnLiftsProductsAndDistributions
import YangMills.Construction.TorusOrFourSpace.TwoNormsOfClassC1
import Mathlib
set_option autoImplicit false
open Filter
open scoped ENNReal Topology
noncomputable section
namespace YangMills.Construction.PeriodicSpace.LiftsProductsDistributions
open YangMills.Construction.PeriodicSpace.Kind.Tuple
open YangMills.Construction.PeriodicSpace.Coords (partialAlong iterPartial ContPartialsUpTo)
open YangMills.Construction.TorusMetric (euclidNormVec)
open YangMills.Construction.PeriodicSpace.TupleFacts (unitCoord unitIndex)
section Leibniz
variable {p : ℕ+}
theorem contPartialsUpTo_succ_iff {n : ℕ} {G : Coords p → ℂ} :
    ContPartialsUpTo (n + 1) G ↔ Continuous G ∧ ∀ j : Fin (4 * (p : ℕ)),
      (∀ x, LineDifferentiableAt ℝ G x (Pi.single j 1)) ∧
        ContPartialsUpTo n (partialAlong j G) :=
  Iff.rfl
theorem contPartialsUpTo_of_succ {n : ℕ} {G : Coords p → ℂ}
    (h : ContPartialsUpTo (n + 1) G) : ContPartialsUpTo n G := by apply _root_.YangMills.Construction.PeriodicSpace.TensorRules.contPartialsUpTo_of_succ <;> assumption
theorem hasLineDerivAt_sum_of_lineDiff {G K : Coords p → ℂ} {x v : Coords p}
    (hG : LineDifferentiableAt ℝ G x v) (hK : LineDifferentiableAt ℝ K x v) :
    HasLineDerivAt ℝ (G + K) (lineDeriv ℝ G x v + lineDeriv ℝ K x v) x v :=
  HasDerivAt.add (f := fun t : ℝ => G (x + t • v)) (g := fun t : ℝ => K (x + t • v))
    hG.hasLineDerivAt hK.hasLineDerivAt
theorem hasLineDerivAt_prod_of_lineDiff {G K : Coords p → ℂ} {x v : Coords p}
    (hG : LineDifferentiableAt ℝ G x v) (hK : LineDifferentiableAt ℝ K x v) :
    HasLineDerivAt ℝ (G * K) (lineDeriv ℝ G x v * K x + G x * lineDeriv ℝ K x v) x v := by apply _root_.YangMills.Construction.PeriodicSpace.SumsProductsPartials.hasLineDerivAt_prod <;> assumption
theorem partialAlong_add_eq {G K : Coords p → ℂ} {j : Fin (4 * (p : ℕ))}
    (hG : ∀ x, LineDifferentiableAt ℝ G x (Pi.single j 1))
    (hK : ∀ x, LineDifferentiableAt ℝ K x (Pi.single j 1)) :
    partialAlong j (G + K) = partialAlong j G + partialAlong j K :=
  funext fun x => (hasLineDerivAt_sum_of_lineDiff (hG x) (hK x)).lineDeriv
theorem partialAlong_mul_eq {G K : Coords p → ℂ} {j : Fin (4 * (p : ℕ))}
    (hG : ∀ x, LineDifferentiableAt ℝ G x (Pi.single j 1))
    (hK : ∀ x, LineDifferentiableAt ℝ K x (Pi.single j 1)) :
    partialAlong j (G * K) = partialAlong j G * K + G * partialAlong j K :=
  funext fun x => (hasLineDerivAt_prod_of_lineDiff (hG x) (hK x)).lineDeriv
theorem contPartialsUpTo_add {n : ℕ} {G K : Coords p → ℂ}
    (hG : ContPartialsUpTo n G) (hK : ContPartialsUpTo n K) :
    ContPartialsUpTo n (G + K) := by apply _root_.YangMills.Construction.PeriodicSpace.SumsProductsPartials.contPartialsUpTo_add <;> assumption
theorem contPartialsUpTo_mul {n : ℕ} {G K : Coords p → ℂ}
    (hG : ContPartialsUpTo n G) (hK : ContPartialsUpTo n K) :
    ContPartialsUpTo n (G * K) := by
  induction n generalizing G K with
  | zero => exact Continuous.mul hG hK
  | succ n ih =>
    obtain ⟨hGc, hGj⟩ := contPartialsUpTo_succ_iff.1 hG
    obtain ⟨hKc, hKj⟩ := contPartialsUpTo_succ_iff.1 hK
    refine contPartialsUpTo_succ_iff.2 ⟨hGc.mul hKc, fun j => ⟨fun x =>
      (hasLineDerivAt_prod_of_lineDiff ((hGj j).1 x) ((hKj j).1 x)).lineDifferentiableAt, ?_⟩⟩
    rw [partialAlong_mul_eq (hGj j).1 (hKj j).1]
    exact contPartialsUpTo_add (ih (hGj j).2 (contPartialsUpTo_of_succ hK))
      (ih (contPartialsUpTo_of_succ hG) (hKj j).2)
def derivAlongList (l : List (Fin (4 * (p : ℕ)))) (G : Coords p → ℂ) : Coords p → ℂ :=
  l.foldl (fun H j => partialAlong j H) G
theorem derivAlongList_cons (j : Fin (4 * (p : ℕ))) (l : List (Fin (4 * (p : ℕ))))
    (G : Coords p → ℂ) :
    derivAlongList (j :: l) G = derivAlongList l (partialAlong j G) := by apply _root_.YangMills.Construction.PeriodicSpace.SumsProductsPartials.wordDeriv_cons <;> assumption
theorem derivAlongList_add (l : List (Fin (4 * (p : ℕ)))) {n : ℕ} {G K : Coords p → ℂ}
    (hl : l.length ≤ n) (hG : ContPartialsUpTo n G)
    (hK : ContPartialsUpTo n K) :
    derivAlongList l (G + K) = derivAlongList l G + derivAlongList l K := by
  induction l generalizing n G K with
  | nil => rfl
  | cons j l ih =>
    cases n with
    | zero => simp at hl
    | succ n =>
      obtain ⟨-, hGj⟩ := contPartialsUpTo_succ_iff.1 hG
      obtain ⟨-, hKj⟩ := contPartialsUpTo_succ_iff.1 hK
      rw [derivAlongList_cons, derivAlongList_cons, derivAlongList_cons,
        partialAlong_add_eq (hGj j).1 (hKj j).1]
      exact ih (by simpa using hl) (hGj j).2 (hKj j).2
theorem norm_derivAlongList_mul_le (l : List (Fin (4 * (p : ℕ)))) {n : ℕ}
    {G K : Coords p → ℂ} {A C : ℝ} (hl : l.length ≤ n)
    (hG : ContPartialsUpTo n G) (hK : ContPartialsUpTo n K)
    (hA : ∀ s : List (Fin (4 * (p : ℕ))), s.Sublist l → ∀ x, ‖derivAlongList s G x‖ ≤ A)
    (hC : ∀ s : List (Fin (4 * (p : ℕ))), s.Sublist l → ∀ x, ‖derivAlongList s K x‖ ≤ C)
    (x : Coords p) :
    ‖derivAlongList l (G * K) x‖ ≤ 2 ^ l.length * A * C := by
  induction l generalizing n G K x with
  | nil =>
    have h1 := hA [] (List.Sublist.refl _) x
    have h2 := hC [] (List.Sublist.refl _) x
    have h3 : ‖derivAlongList [] (G * K) x‖ = ‖derivAlongList [] G x‖ * ‖derivAlongList [] K x‖ :=
      norm_mul (G x) (K x)
    rw [h3]
    simpa using mul_le_mul h1 h2 (norm_nonneg _) ((norm_nonneg _).trans h1)
  | cons j l ih =>
    cases n with
    | zero => simp at hl
    | succ n =>
      have hl' : l.length ≤ n := by simpa using hl
      obtain ⟨-, hGj⟩ := contPartialsUpTo_succ_iff.1 hG
      obtain ⟨-, hKj⟩ := contPartialsUpTo_succ_iff.1 hK
      have hG' := contPartialsUpTo_of_succ hG
      have hK' := contPartialsUpTo_of_succ hK
      rw [derivAlongList_cons, partialAlong_mul_eq (hGj j).1 (hKj j).1,
        derivAlongList_add l hl' (contPartialsUpTo_mul (hGj j).2 hK')
          (contPartialsUpTo_mul hG' (hKj j).2)]
      have b1 := ih hl' (hGj j).2 hK'
        (fun s hs y => hA (j :: s) (hs.cons_cons j) y) (fun s hs y => hC s (hs.cons j) y) x
      have b2 := ih hl' hG' (hKj j).2
        (fun s hs y => hA s (hs.cons j) y) (fun s hs y => hC (j :: s) (hs.cons_cons j) y) x
      calc ‖(derivAlongList l (partialAlong j G * K) +
              derivAlongList l (G * partialAlong j K)) x‖
          ≤ ‖derivAlongList l (partialAlong j G * K) x‖ +
              ‖derivAlongList l (G * partialAlong j K) x‖ := norm_add_le _ _
        _ ≤ 2 ^ l.length * A * C + 2 ^ l.length * A * C := add_le_add b1 b2
        _ = 2 ^ (j :: l).length * A * C := by
          rw [List.length_cons, pow_succ]
          ring
def expandedCoords (r : List (Fin (4 * (p : ℕ)))) (a : CoordIndex p) :
    List (Fin (4 * (p : ℕ))) :=
  r.flatMap fun j => List.replicate (a j) j
theorem foldr_replicate_partialAlong (j : Fin (4 * (p : ℕ))) (n : ℕ) (H : Coords p → ℂ) :
    (List.replicate n j).foldr (fun i H' => partialAlong i H') H =
      (partialAlong j)^[n] H := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.replicate_succ, List.foldr_cons, ih, Function.iterate_succ_apply']
theorem foldr_iterate_eq_foldr_expanded (r : List (Fin (4 * (p : ℕ))))
    (a : CoordIndex p) (G : Coords p → ℂ) :
    r.foldr (fun j H => (partialAlong j)^[a j] H) G =
      (expandedCoords r a).foldr (fun i H' => partialAlong i H') G := by
  induction r with
  | nil => rfl
  | cons j r ih =>
    rw [List.foldr_cons, ih]
    simp only [expandedCoords, List.flatMap_cons, List.foldr_append]
    rw [foldr_replicate_partialAlong]
theorem iterPartial_eq_derivAlongList (α : CoordIndex p) (G : Coords p → ℂ) :
    iterPartial α G =
      derivAlongList (expandedCoords (List.finRange (4 * (p : ℕ))) α).reverse G := by
  rw [derivAlongList, List.foldl_reverse]
  exact foldr_iterate_eq_foldr_expanded _ α G
theorem length_expandedCoords (α : CoordIndex p) :
    (expandedCoords (List.finRange (4 * (p : ℕ))) α).length = α.degree := by apply _root_.YangMills.Construction.PeriodicSpace.IteratedPartials.length_multiIndexToList <;> assumption
theorem exists_eq_expandedCoords_of_sublist (r : List (Fin (4 * (p : ℕ)))) (hr : r.Nodup)
    (a : CoordIndex p) (s : List (Fin (4 * (p : ℕ))))
    (hs : s.Sublist (expandedCoords r a)) :
    ∃ b : CoordIndex p, s = expandedCoords r b ∧ ∀ j, b j ≤ a j := by
  induction r generalizing s with
  | nil =>
    refine ⟨0, ?_, fun j => Nat.zero_le _⟩
    simpa [expandedCoords] using hs
  | cons j r ih =>
    obtain ⟨hj, hr'⟩ := List.nodup_cons.1 hr
    have hs' : s.Sublist (List.replicate (a j) j ++ expandedCoords r a) := by
      simpa [expandedCoords, List.flatMap_cons] using hs
    obtain ⟨s₁, s₂, rfl, h₁, h₂⟩ := List.sublist_append_iff.1 hs'
    obtain ⟨m, hm, rfl⟩ := List.sublist_replicate_iff.1 h₁
    obtain ⟨b, rfl, hb⟩ := ih hr' s₂ h₂
    refine ⟨Function.update b j m, ?_, fun i => ?_⟩
    · have hcongr : expandedCoords r (Function.update b j m) = expandedCoords r b := by
        refine List.flatMap_congr fun i hi => ?_
        have hij : i ≠ j := fun h => hj (h ▸ hi)
        rw [Function.update_of_ne hij]
      simp only [expandedCoords, List.flatMap_cons, Function.update_self] at hcongr ⊢
      rw [hcongr]
    · by_cases hij : i = j
      · subst hij
        simpa using hm
      · rw [Function.update_of_ne hij]
        exact hb i
theorem exists_iterPartial_of_sublist (α : CoordIndex p)
    (s : List (Fin (4 * (p : ℕ))))
    (hs : s.Sublist (expandedCoords (List.finRange (4 * (p : ℕ))) α).reverse) :
    ∃ β : CoordIndex p, β.degree ≤ α.degree ∧
      ∀ G : Coords p → ℂ, derivAlongList s G = iterPartial β G := by
  have hs' : s.reverse.Sublist (expandedCoords (List.finRange (4 * (p : ℕ))) α) := by
    simpa using List.reverse_sublist.2 hs
  obtain ⟨β, hβ, hle⟩ :=
    exists_eq_expandedCoords_of_sublist _ (List.nodup_finRange _) α _ hs'
  refine ⟨β, Finset.sum_le_sum fun j _ => hle j, fun G => ?_⟩
  rw [iterPartial_eq_derivAlongList, ← hβ, List.reverse_reverse]
theorem degree_zero (p : ℕ+) : (0 : CoordIndex p).degree = 0 :=
  Finset.sum_eq_zero fun _ _ => rfl
theorem norm_iterPartial_mul_le {ν : ℕ} {G K : Coords p → ℂ} {A C : ℝ}
    (hG : ContPartialsUpTo ν G) (hK : ContPartialsUpTo ν K)
    (hA : ∀ β : CoordIndex p, β.degree ≤ ν → ∀ x, ‖iterPartial β G x‖ ≤ A)
    (hC : ∀ β : CoordIndex p, β.degree ≤ ν → ∀ x, ‖iterPartial β K x‖ ≤ C)
    (α : CoordIndex p) (hα : α.degree ≤ ν) (x : Coords p) :
    ‖iterPartial α (G * K) x‖ ≤ 2 ^ ν * A * C := by
  have hA0 : 0 ≤ A := (norm_nonneg _).trans (hA 0 (by rw [degree_zero p]; exact Nat.zero_le _) x)
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 0 (by rw [degree_zero p]; exact Nat.zero_le _) x)
  have hlen : (expandedCoords (List.finRange (4 * (p : ℕ))) α).reverse.length = α.degree := by
    rw [List.length_reverse, length_expandedCoords]
  rw [iterPartial_eq_derivAlongList]
  have h := norm_derivAlongList_mul_le
    (expandedCoords (List.finRange (4 * (p : ℕ))) α).reverse (n := ν) (G := G) (K := K)
    (A := A) (C := C) (hlen.le.trans hα) hG hK
    (fun s hs y => by
      obtain ⟨β, hβ, hs'⟩ := exists_iterPartial_of_sublist α s hs
      rw [hs']
      exact hA β (hβ.trans hα) y)
    (fun s hs y => by
      obtain ⟨β, hβ, hs'⟩ := exists_iterPartial_of_sublist α s hs
      rw [hs']
      exact hC β (hβ.trans hα) y) x
  refine h.trans ?_
  rw [hlen]
  have h2 : (2 : ℝ) ^ α.degree ≤ 2 ^ ν := pow_le_pow_right₀ (by norm_num) hα
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h2 hA0) hC0
theorem iterPartial_zero (G : Coords p → ℂ) : iterPartial 0 G = G := by apply _root_.YangMills.Construction.ToriLimits.GrowingVolumeLimits.ProofSteps.MirrorStep.FlatReading.iterPartial_zero <;> assumption
end Leibniz
section Norms
variable (D : Params) (E : Kind) {p : ℕ+}
theorem ofReal_norm_partialDeriv_le_cNorm {ν : ℕ} (F : E.Tuple D p → ℂ)
    (α : CoordIndex p) (hα : α.degree ≤ ν) (y : E.Tuple D p) :
    ENNReal.ofReal ‖partialDeriv D E α F y‖ ≤ cNorm D E ν F :=
  le_iSup_of_le α (le_iSup_of_le hα
    (le_iSup (fun y => ENNReal.ofReal ‖partialDeriv D E α F y‖) y))
theorem cNorm_le_of_forall {ν : ℕ} (F : E.Tuple D p → ℂ) {c : ℝ≥0∞}
    (h : ∀ α : CoordIndex p, α.degree ≤ ν → ∀ y,
      ENNReal.ofReal ‖partialDeriv D E α F y‖ ≤ c) :
    cNorm D E ν F ≤ c :=
  iSup_le fun α => iSup_le fun hα => iSup_le fun y => h α hα y
end Norms
section Facts
variable (D : Params) (E : Kind)
theorem abs_apply_le_euclidNormVec (v : Fin 4 → ℝ) (μ : Fin 4) : |v μ| ≤ euclidNormVec v := by apply _root_.YangMills.Construction.Parametrix.UnitKernelSupport.abs_apply_le_euclidNormVec <;> assumption
theorem euclidNormVec_add_le (v w : Fin 4 → ℝ) :
    euclidNormVec (v + w) ≤ euclidNormVec v + euclidNormVec w := by apply _root_.YangMills.Construction.LimitSpaces.AmbientMetric.euclidNormVec_add_le <;> assumption
theorem euclidNormVec_neg (v : Fin 4 → ℝ) : euclidNormVec (-v) = euclidNormVec v := by apply _root_.YangMills.Construction.LimitSpaces.AmbientMetric.euclidNormVec_neg <;> assumption
theorem side_le_euclidNormVec_of_mem_lattice {k : Fin 4 → ℝ} (hs : 0 ≤ D.side)
    (hk : k ∈ InfiniteLattice.latticeSubgroup D.side) (hk0 : k ≠ 0) :
    D.side ≤ euclidNormVec k := by
  obtain ⟨n, hn⟩ := hk
  have hex : ∃ μ, n μ ≠ 0 := by
    by_contra h
    have h' : ∀ μ, n μ = 0 := fun μ => by_contra fun hμ => h ⟨μ, hμ⟩
    exact hk0 (funext fun μ => by simp [hn, h'])
  obtain ⟨μ, hμ⟩ := hex
  have h1 : (1 : ℝ) ≤ |(n μ : ℝ)| := by
    have h2 : (1 : ℤ) ≤ |n μ| := Int.one_le_abs hμ
    exact_mod_cast h2
  calc D.side ≤ |(n μ : ℝ)| * D.side := le_mul_of_one_le_left hs h1
    _ = |k μ| := by rw [hn, abs_mul, abs_of_nonneg hs]
    _ ≤ euclidNormVec k := abs_apply_le_euclidNormVec k μ
theorem quotMapDistLE_holds
    (hw : WellPosedness.WellPosed)
    (hq : Kind.QuotientCompactC1.Claim) :
    QuotMapDistLE D E := by
  intro x x'
  obtain ⟨⟨-, -, -, -, hle, -⟩, -⟩ := hq D E
  refine ⟨hle x x', fun hlt => ?_⟩
  cases E with
  | euclidean =>
    obtain ⟨-, -, -, -, -, -, -, hfour, -⟩ := hw D Kind.euclidean
    exact hfour x x'
  | torus =>
    obtain ⟨-, -, -, -, -, -, hleast, -⟩ := hw D Kind.torus
    obtain ⟨⟨k, hk, hr⟩, -⟩ := hleast x x'
    have hq4 : Kind.periodQuarter D Kind.torus = ENNReal.ofReal (D.side / 4) := rfl
    have h2 : (2 : ℝ≥0∞) * ENNReal.ofReal (D.side / 4) = ENNReal.ofReal (D.side / 2) := by
      rw [show D.side / 2 = 2 * (D.side / 4) by ring, ENNReal.ofReal_mul (by norm_num)]
      simp
    rw [hq4, h2, ENNReal.ofReal_lt_ofReal_iff'] at hlt
    obtain ⟨hlt, hpos⟩ := hlt
    by_cases hk0 : k = 0
    · rw [hr, hk0, sub_zero]
    · exfalso
      obtain ⟨-, hlb⟩ := hleast x x'
      have hle0 := hlb ⟨0, AddSubgroup.zero_mem _, by rw [sub_zero]⟩
      have hside := side_le_euclidNormVec_of_mem_lattice D (by linarith) hk hk0
      have htri := euclidNormVec_add_le (x - x') (-(x - x' - k))
      rw [euclidNormVec_neg, ← hr, show x - x' + -(x - x' - k) = k by abel] at htri
      linarith
theorem existsLiftAtDist_holds
    (hq : Kind.QuotientCompactC1.Claim) :
    ExistsLiftAtDist D E := by
  intro x y
  obtain ⟨⟨-, -, -, -, -, hlift⟩, -⟩ := hq D E
  exact hlift (E.quotMap D x) y x rfl
theorem leibnizBound_holds (hP : TupleFacts.AllFacts)
    (p : ℕ+) (ν : ℕ) : LeibnizBound D E p ν := by
  intro F H hF hH hFn hHn
  obtain ⟨hOnto, -, -, -, -, -, -, -, -, -, -, -, -, -, hDer, -, -, -, hClass, -⟩ := hP D E p
  have hFH : IsClassC D E ν (F * H) := (hClass ν F H hF hH).2.1
  have key : ∀ Z : E.Tuple D p → ℂ, IsClassC D E ν Z → cNorm D E ν Z < ⊤ →
      ∀ β : CoordIndex p, β.degree ≤ ν → ∀ x,
        ‖iterPartial β (Z ∘ proj D E) x‖ ≤ (cNorm D E ν Z).toReal := by
    intro Z hZ hZn β hβ x
    rw [← (hDer ν Z hZ β hβ).2.1]
    exact (ENNReal.ofReal_le_iff_le_toReal hZn.ne).1
      (ofReal_norm_partialDeriv_le_cNorm D E Z β hβ _)
  refine cNorm_le_of_forall D E _ fun α hα y => ?_
  obtain ⟨x, rfl⟩ := hOnto.1 y
  have e : partialDeriv D E α (F * H) (proj D E x) =
      iterPartial α ((F ∘ proj D E) * (H ∘ proj D E)) x :=
    congrFun (hDer ν (F * H) hFH α hα).2.1 x
  rw [e]
  have hb := norm_iterPartial_mul_le (G := F ∘ proj D E) (K := H ∘ proj D E)
    hF hH (key F hF hFn) (key H hH hHn) α hα x
  have hFt := ENNReal.toReal_nonneg (a := cNorm D E ν F)
  have hHt := ENNReal.toReal_nonneg (a := cNorm D E ν H)
  calc ENNReal.ofReal ‖iterPartial α ((F ∘ proj D E) * (H ∘ proj D E)) x‖
      ≤ ENNReal.ofReal (2 ^ ν * (cNorm D E ν F).toReal * (cNorm D E ν H).toReal) :=
        ENNReal.ofReal_le_ofReal hb
    _ = 2 ^ ν * cNorm D E ν F * cNorm D E ν H := by
        rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity),
          ENNReal.ofReal_toReal hFn.ne, ENNReal.ofReal_toReal hHn.ne,
          ENNReal.ofReal_pow (by norm_num)]
        simp
theorem reImC1NormLE_holds
    (hP : TupleFacts.AllFacts) :
    ReImC1NormLE D E := by
  intro g hg _
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hClass, -⟩ := hP D E 1
  obtain ⟨-, -, -, -, hparts⟩ := hClass 1 _ _ hg hg
  constructor
  · refine cNorm_le_of_forall D E _ fun α hα y => ?_
    have e : partialDeriv D E α (ofSingle D E fun y => ((g y).re : ℂ)) =
        TupleFacts.rePart (partialDeriv D E α (ofSingle D E g)) := (hparts α hα).1
    rw [e]
    refine le_trans (ENNReal.ofReal_le_ofReal ?_)
      (ofReal_norm_partialDeriv_le_cNorm D E (ofSingle D E g) α hα y)
    simpa [TupleFacts.rePart] using
      Complex.abs_re_le_norm (partialDeriv D E α (ofSingle D E g) y)
  · refine cNorm_le_of_forall D E _ fun α hα y => ?_
    have e : partialDeriv D E α (ofSingle D E fun y => ((g y).im : ℂ)) =
        TupleFacts.imPart (partialDeriv D E α (ofSingle D E g)) := (hparts α hα).2
    rw [e]
    refine le_trans (ENNReal.ofReal_le_ofReal ?_)
      (ofReal_norm_partialDeriv_le_cNorm D E (ofSingle D E g) α hα y)
    simpa [TupleFacts.imPart] using
      Complex.abs_im_le_norm (partialDeriv D E α (ofSingle D E g) y)
theorem c1NormQ_le_c1NormSingleReal
    (hP : TupleFacts.AllFacts)
    {u : E.Pt D → ℝ} (hu : u ∈ Kind.c1Set D E) :
    Kind.c1NormQ D E u ≤ c1NormSingleReal D E u := by
  obtain ⟨hOnto, -, -, -, -, -, -, -, -, -, -, -, -, -, hDer, -, hTwo, -⟩ := hP D E 1
  have hF := ((hTwo u).1).2 hu
  refine max_le (iSup_le fun y => ?_) (iSup_le fun μ => iSup_le fun y => ?_)
  · obtain ⟨x, hx⟩ := hOnto.1 (fun _ => y)
    have h0 : (0 : CoordIndex 1).degree ≤ 1 := by rw [degree_zero 1]; exact Nat.zero_le _
    have e := congrFun (hDer 1 _ hF 0 h0).2.1 x
    rw [iterPartial_zero] at e
    have e' : partialDeriv D E 0 (ofSingle D E fun y => (u y : ℂ)) (fun _ => y) = (u y : ℂ) := by
      simpa [hx, ofSingle] using e
    have hb := ofReal_norm_partialDeriv_le_cNorm D E (ν := 1)
      (ofSingle D E fun y => (u y : ℂ)) 0 h0 (fun _ => y)
    rw [e', Complex.norm_real, Real.norm_eq_abs] at hb
    exact hb
  · have e := ((hTwo u).2 hu).1 μ
    have hμ : (unitIndex μ).degree ≤ 1 := by
      unfold CoordIndex.degree unitIndex
      rw [Finset.sum_eq_single (unitCoord μ)]
      · exact (Pi.single_eq_same _ _).le
      · intro b _ hb
        exact Pi.single_eq_of_ne hb _
      · intro h
        exact absurd (Finset.mem_univ _) h
    have hb := ofReal_norm_partialDeriv_le_cNorm D E (ν := 1)
      (ofSingle D E fun y => (u y : ℂ)) (unitIndex μ) hμ (fun _ => y)
    rw [e] at hb
    exact show ENNReal.ofReal |Kind.partialDeriv D E μ u y| ≤
        cNorm D E 1 (ofSingle D E fun y => (u y : ℂ)) from by
      simpa [ofSingle, Complex.norm_real, Real.norm_eq_abs] using hb
theorem c1ClassLipschitz_holds
    (hP : TupleFacts.AllFacts)
    (hq : Kind.QuotientCompactC1.Claim)
    (hT : C1NormComparison.statement) :
    C1ClassLipschitz D E := by
  intro g hg
  obtain ⟨hc, hcomp, -⟩ := hg
  obtain ⟨-, -, -, -, hC⟩ := hq D E
  obtain ⟨-, -, -, -, hLip, hLipEq, -, -⟩ := hC g hc hcomp
  obtain ⟨-, ⟨-, hcmp⟩, hfin⟩ := (hT D E).1 g hc
  obtain ⟨-, -, hs₁, hs₂⟩ := hfin hcomp
  have hle := c1NormQ_le_c1NormSingleReal D E hP hc
  refine ⟨hLip, ?_, hs₁.trans (hs₂.trans (mul_le_mul' le_rfl hle))⟩
  rw [hLipEq]
  exact (le_max_right _ _).trans (hcmp.trans (mul_le_mul' le_rfl hle))
theorem restrictDistrib_holds (p : ℕ+) : RestrictDistrib D E p := by
  intro Ω' Ω _ _ h T hT
  have hdist : IsDistrib (restrictDistrib h T) :=
    ⟨⟨fun F G H e => hT.1.1 _ _ _ e, fun c F H e => hT.1.2 c _ _ e⟩, fun K hK hKΩ => by
      obtain ⟨ν, C, hC⟩ := hT.2 K hK (hKΩ.trans h)
      exact ⟨ν, C, fun F hF => hC _ hF⟩⟩
  refine ⟨fun F hF => ⟨hF.1, hF.2.1, hF.2.2.trans h⟩, hdist, fun ν₀ hν₀ => ⟨hdist, ?_⟩⟩
  intro K hK hKΩ
  obtain ⟨C, hC⟩ := hν₀.2 K hK (hKΩ.trans h)
  exact ⟨C, fun F hF => hC _ hF⟩
theorem distribSeqContinuous_holds
    (hP : TupleFacts.AllFacts) (p : ℕ+) :
    DistribSeqContinuous D E p := by
  intro Ω hΩ T hT Fs F hconv
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hSupp, -, hStable, -⟩ := hP D E p
  obtain ⟨⟨K, hK, hKΩ, hFK, hFsK⟩, hnorm⟩ := hconv
  obtain ⟨ν, C, hC⟩ := hT.2 K hK hKΩ
  obtain ⟨S, hS⟩ := (hStable Ω hΩ).1
  have hSm : ∀ Z, Z ∈ testFns D E Ω ↔ Z ∈ S := fun Z => by
    rw [← hS]
    exact SetLike.mem_coe
  have hmem : ∀ t, (Fs t).1 - F.1 ∈ testFns D E Ω := fun t =>
    (hSm _).2 (S.sub_mem ((hSm _).1 (Fs t).2) ((hSm _).1 F.2))
  have hsupp : ∀ t, supportT D E ((Fs t).1 - F.1) ⊆ K := fun t => by
    have e : (Fs t).1 - F.1 = (1 : ℂ) • (Fs t).1 + (-1 : ℂ) • F.1 := by
      simp [sub_eq_add_neg]
    rw [e]
    exact ((hSupp (Fs t).1 F.1 1 (-1)).1).trans (Set.union_subset (hFsK t) hFK)
  have hbound : ∀ t, ENNReal.ofReal ‖T ⟨_, hmem t⟩‖ ≤
      (C : ℝ≥0∞) * cNorm D E ν ((Fs t).1 - F.1) := fun t => hC ⟨_, hmem t⟩ (hsupp t)
  have hadd : ∀ t, T (Fs t) - T F = T ⟨_, hmem t⟩ := fun t => by
    have h := hT.1.1 ⟨_, hmem t⟩ F (Fs t) (by simp)
    rw [h]
    ring
  have hlim : Tendsto (fun t => (C : ℝ≥0∞) * cNorm D E ν ((Fs t).1 - F.1)) atTop (𝓝 0) := by
    simpa using ENNReal.Tendsto.const_mul (hnorm ν) (Or.inr ENNReal.coe_ne_top)
  have h0 : Tendsto (fun t => ENNReal.ofReal ‖T ⟨_, hmem t⟩‖) atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim
      (fun _ => zero_le) hbound
  have h1 := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp h0
  rw [tendsto_iff_norm_sub_tendsto_zero]
  simpa [Function.comp_def, ENNReal.toReal_ofReal, hadd] using h1
end Facts
theorem statement_holds (h₁ : TupleFacts.AllFacts)
    (h₂ : WellPosedness.WellPosed)
    (h₃ : Kind.QuotientCompactC1.Claim)
    (h₄ : C1NormComparison.statement) : Statement := fun D E =>
  ⟨quotMapDistLE_holds D E h₂ h₃, existsLiftAtDist_holds D E h₃,
    fun p ν => leibnizBound_holds D E h₁ p ν, reImC1NormLE_holds D E h₁,
    c1ClassLipschitz_holds D E h₁ h₃ h₄, fun p => restrictDistrib_holds D E p,
    fun p => distribSeqContinuous_holds D E h₁ p⟩
end YangMills.Construction.PeriodicSpace.LiftsProductsDistributions
