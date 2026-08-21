/-
**Dirac's simplicial-vertex theorem** (Dirac 1961), discharging the single
classical gap left open in `Ste.ConverseFull`.

`Ste.ConverseFull.DiracHypothesis E` says: whenever a nonempty vertex set
`S` has *no simplicial vertex* for the primal graph of `E` — every
`v ∈ S` has two `S`-neighbours that are not adjacent — then `S` carries a
chordless cycle of length `≥ 4`.  This file proves it.

**Route.**  The contrapositive, in the strong form that actually inducts:

> a finite vertex set with no chordless cycle of length `≥ 4` is either a
> clique, or contains two non-adjacent simplicial vertices.

The induction is on `S.card`.  Given non-adjacent `a, b ∈ S`, look at the
far set `D = S \ N[a]`, the connected component `C ⊆ D` of `b`, and the
attachment `A = N(a) ∩ N(C)`.  `A` is a clique — two non-adjacent
vertices of `A` are joined by a shortest walk through `C`, and `a`
together with that walk is a chordless cycle of length `≥ 4`.  The set
`T = C ∪ A` misses `a`, so the induction hypothesis applies to it, and
because `A` is a clique it hands back a simplicial vertex *inside* `C`,
whose whole `S`-neighbourhood lies in `T`; it is therefore simplicial in
`S` and non-adjacent to `a`.  Iterating once more gives the second
simplicial vertex.

Everything is elementary and self-contained: walks are functions
`ℕ → Fin (n + 1)`, cycles are the same data read modulo their length, and
the final step transports a cyclic `ℕ`-indexed cycle into the
`Fin (p + 4)`-indexed shape `DiracHypothesis` consumes.
-/
import Ste.ConverseFull

namespace STE
namespace Dirac

open scoped Classical

variable {m n : ℕ} {E : Fin m → Finset (Fin (n + 1))}

/-! ### Primal adjacency is symmetric and quasi-reflexive -/

theorem padj_symm {u w : Fin (n + 1)} (h : PrimalAdj E u w) : PrimalAdj E w u := by
  obtain ⟨k, h1, h2⟩ := h; exact ⟨k, h2, h1⟩

theorem padj_refl_of {u w : Fin (n + 1)} (h : PrimalAdj E u w) : PrimalAdj E u u := by
  obtain ⟨k, h1, _⟩ := h; exact ⟨k, h1, h1⟩

/-! ### Cliques and simplicial vertices -/

/-- Every pair of `S` is primal adjacent. -/
def Clique (E : Fin m → Finset (Fin (n + 1))) (S : Finset (Fin (n + 1))) : Prop :=
  ∀ u ∈ S, ∀ w ∈ S, PrimalAdj E u w

/-- `v` is simplicial in `S`: its `S`-neighbours are pairwise adjacent.
This is exactly the negation of the local hypothesis `DiracHypothesis`
places on every vertex. -/
def Simplicial (E : Fin m → Finset (Fin (n + 1))) (S : Finset (Fin (n + 1)))
    (v : Fin (n + 1)) : Prop :=
  ∀ u ∈ S, ∀ w ∈ S, PrimalAdj E v u → PrimalAdj E v w → PrimalAdj E u w

/-! ### Chordless cycles, indexed by `ℕ` modulo their length -/

/-- A chordless cycle of length `N ≥ 4` inside `S`, read cyclically:
`f 0, …, f (N-1)` are distinct vertices of `S`, consecutive ones (mod `N`)
are adjacent, and non-consecutive ones are not. -/
structure IsCycN (E : Fin m → Finset (Fin (n + 1))) (S : Finset (Fin (n + 1)))
    (N : ℕ) (f : ℕ → Fin (n + 1)) : Prop where
  four : 4 ≤ N
  mem : ∀ i < N, f i ∈ S
  inj : ∀ i < N, ∀ j < N, f i = f j → i = j
  adj : ∀ i < N, PrimalAdj E (f i) (f ((i + 1) % N))
  ind : ∀ i < N, ∀ j < N, j ≠ i → j ≠ (i + 1) % N → i ≠ (j + 1) % N →
    ¬ PrimalAdj E (f i) (f j)

/-- `S` carries a chordless cycle of length `≥ 4`. -/
def HasCyc (E : Fin m → Finset (Fin (n + 1))) (S : Finset (Fin (n + 1))) : Prop :=
  ∃ (N : ℕ) (f : ℕ → Fin (n + 1)), IsCycN E S N f

theorem hasCyc_mono {S T : Finset (Fin (n + 1))} (hST : T ⊆ S) (h : HasCyc E T) :
    HasCyc E S := by
  obtain ⟨N, f, hc⟩ := h
  exact ⟨N, f, { hc with mem := fun i hi => hST (hc.mem i hi) }⟩

/-! ### Walks through a vertex set

`CWalk E C x y L` is a walk `x = f 0, …, f L = y` of length `L` all of
whose *interior* vertices lie in `C`.  A walk of minimal length has no
repeated vertex and no chord; both follow from one shortcut. -/

/-- A walk of length `L` from `x` to `y` whose interior lies in `C`. -/
def CWalk (E : Fin m → Finset (Fin (n + 1))) (C : Finset (Fin (n + 1)))
    (x y : Fin (n + 1)) (L : ℕ) : Prop :=
  ∃ f : ℕ → Fin (n + 1), f 0 = x ∧ f L = y ∧
    (∀ i < L, PrimalAdj E (f i) (f (i + 1))) ∧ (∀ i, 0 < i → i < L → f i ∈ C)

/-- **Shortcutting a walk.**  An edge from `f i` to `f (i + 1 + d)` with
`d ≥ 1` splices out `d` steps. -/
theorem cwalk_shortcut {C : Finset (Fin (n + 1))} {x y : Fin (n + 1)} {L : ℕ}
    {f : ℕ → Fin (n + 1)} (h0 : f 0 = x) (hL : f L = y)
    (hadj : ∀ i < L, PrimalAdj E (f i) (f (i + 1)))
    (hC : ∀ i, 0 < i → i < L → f i ∈ C)
    {i d : ℕ} (hd : 0 < d) (hiL : i + 1 + d ≤ L)
    (hchord : PrimalAdj E (f i) (f (i + 1 + d))) :
    CWalk E C x y (L - d) := by
  refine ⟨fun r => if r ≤ i then f r else f (r + d), by simpa using h0, ?_, ?_, ?_⟩
  · have h1 : ¬ (L - d ≤ i) := by omega
    simp only [h1, if_false]
    have : L - d + d = L := by omega
    rw [this, hL]
  · intro r hr
    rcases lt_trichotomy r i with h | h | h
    · have e1 : r ≤ i := by omega
      have e2 : r + 1 ≤ i := by omega
      simp only [e1, e2, if_true]
      exact hadj r (by omega)
    · subst h
      have e1 : r ≤ r := le_refl r
      have e2 : ¬ (r + 1 ≤ r) := by omega
      simp only [e1, e2, if_true, if_false]
      exact hchord
    · have e1 : ¬ (r ≤ i) := by omega
      have e2 : ¬ (r + 1 ≤ i) := by omega
      simp only [e1, e2, if_false]
      have : r + 1 + d = r + d + 1 := by omega
      rw [this]
      exact hadj (r + d) (by omega)
  · intro r hr0 hr
    by_cases hri : r ≤ i
    · simp only [hri, if_true]
      exact hC r hr0 (by omega)
    · simp only [hri, if_false]
      exact hC (r + d) (by omega) (by omega)

/-- **A shortest walk is an induced path.**  Between two distinct
non-adjacent endpoints, a walk of minimal length repeats no vertex and
has no chord. -/
theorem exists_min_cwalk {C : Finset (Fin (n + 1))} {x y : Fin (n + 1)} {L₀ : ℕ}
    (hw : CWalk E C x y L₀) (hxy : x ≠ y) (hnadj : ¬ PrimalAdj E x y) :
    ∃ (L : ℕ) (f : ℕ → Fin (n + 1)), 2 ≤ L ∧ f 0 = x ∧ f L = y ∧
      (∀ i < L, PrimalAdj E (f i) (f (i + 1))) ∧
      (∀ i, 0 < i → i < L → f i ∈ C) ∧
      (∀ i ≤ L, ∀ j ≤ L, f i = f j → i = j) ∧
      (∀ i ≤ L, ∀ j ≤ L, i + 1 < j → ¬ PrimalAdj E (f i) (f j)) := by
  classical
  have hex : ∃ L, CWalk E C x y L := ⟨L₀, hw⟩
  obtain ⟨f, h0, hL, hadj, hC⟩ := Nat.find_spec hex
  set L := Nat.find hex with hLdef
  have hmin : ∀ L', L' < L → ¬ CWalk E C x y L' := fun L' h => Nat.find_min hex h
  -- no chord
  have hchord : ∀ i ≤ L, ∀ j ≤ L, i + 1 < j → ¬ PrimalAdj E (f i) (f j) := by
    intro i _ j hj hij hadjij
    refine hmin (L - (j - i - 1)) (by omega) ?_
    have e : i + 1 + (j - i - 1) = j := by omega
    exact cwalk_shortcut h0 hL hadj hC (i := i) (d := j - i - 1) (by omega) (by omega)
      (by rw [e]; exact hadjij)
  -- no repeated vertex
  have hrep : ∀ i ≤ L, ∀ j ≤ L, f i = f j → i = j := by
    have key : ∀ i ≤ L, ∀ j ≤ L, i < j → f i ≠ f j := by
      intro i hi j hj hij he
      rcases lt_or_eq_of_le hj with hjL | hjL
      · refine hmin (L - (j - i)) (by omega) ?_
        have e : i + 1 + (j - i) = j + 1 := by omega
        refine cwalk_shortcut h0 hL hadj hC (i := i) (d := j - i) (by omega) (by omega) ?_
        rw [e, he]
        exact hadj j hjL
      · refine hmin i (by omega) ⟨f, h0, ?_, fun r hr => hadj r (by omega),
          fun r hr0 hr => hC r hr0 (by omega)⟩
        rw [he, hjL, hL]
    intro i hi j hj he
    rcases lt_trichotomy i j with h | h | h
    · exact absurd he (key i hi j hj h)
    · exact h
    · exact absurd he.symm (key j hj i hi h)
  -- length at least two
  have h2 : 2 ≤ L := by
    by_contra hlt
    have hcases : L = 0 ∨ L = 1 := by omega
    rcases hcases with h | h
    · apply hxy
      have e : f 0 = f L := by congr 1; omega
      rw [← h0, e]; exact hL
    · have e : f 1 = f L := by congr 1; omega
      have hh := hadj 0 (by omega)
      rw [h0, Nat.zero_add, e, hL] at hh
      exact hnadj hh
  exact ⟨L, f, h2, h0, hL, hadj, hC, hrep, hchord⟩

/-! ### The cycle produced by two non-adjacent attachment points -/

/-- **The key construction.**  If `v` is adjacent to `x` and to `y`, if
`x, y` are *not* adjacent, if `C` is a set of vertices none of which is
adjacent to `v`, and if some walk joins `x` to `y` through `C`, then `S`
carries a chordless cycle of length `≥ 4`: take a shortest such walk and
close it up through `v`. -/
theorem hasCyc_of_attached {S C : Finset (Fin (n + 1))} {v x y : Fin (n + 1)}
    (hvS : v ∈ S) (hCS : C ⊆ S) (hCfar : ∀ c ∈ C, ¬ PrimalAdj E v c)
    (hxS : x ∈ S) (hyS : y ∈ S)
    (hvx : PrimalAdj E v x) (hvy : PrimalAdj E v y) (hxy : ¬ PrimalAdj E x y)
    {L₀ : ℕ} (hw : CWalk E C x y L₀) : HasCyc E S := by
  have hvv : PrimalAdj E v v := padj_refl_of hvx
  have hxx : PrimalAdj E x x := padj_refl_of (padj_symm hvx)
  have hxy' : x ≠ y := fun hcon => hxy (by rw [← hcon]; exact hxx)
  obtain ⟨L, f, hL2, h0, hL, hadj, hC, hrep, hchord⟩ := exists_min_cwalk hw hxy' hxy
  -- the endpoints are distinct from `v`, because both have a neighbour in `C`
  have hxv : x ≠ v := by
    intro hcon
    refine hCfar (f 1) (hC 1 one_pos (by omega)) ?_
    have hh := hadj 0 (by omega)
    rw [h0, hcon, Nat.zero_add] at hh
    exact hh
  have hyv : y ≠ v := by
    intro hcon
    refine hCfar (f (L - 1)) (hC (L - 1) (by omega) (by omega)) ?_
    have hh := hadj (L - 1) (by omega)
    have e : L - 1 + 1 = L := by omega
    rw [e, hL, hcon] at hh
    exact padj_symm hh
  have hfS : ∀ i, i ≤ L → f i ∈ S := by
    intro i hi
    rcases Nat.eq_zero_or_pos i with rfl | hi0
    · rw [h0]; exact hxS
    · rcases lt_or_eq_of_le hi with hlt | he
      · exact hCS (hC i hi0 hlt)
      · rw [he, hL]; exact hyS
  have hfv : ∀ i, i ≤ L → f i ≠ v := by
    intro i hi
    rcases Nat.eq_zero_or_pos i with rfl | hi0
    · rw [h0]; exact hxv
    · rcases lt_or_eq_of_le hi with hlt | he
      · intro hcon
        exact hCfar (f i) (hC i hi0 hlt) (by rw [hcon]; exact hvv)
      · rw [he, hL]; exact hyv
  -- close the walk into a cycle through `v`
  set F : ℕ → Fin (n + 1) := fun r => if r = 0 then v else f (r - 1) with hFdef
  have hF0 : F 0 = v := by simp [hFdef]
  have hFp : ∀ r, 0 < r → F r = f (r - 1) := by
    intro r hr; simp only [hFdef]; rw [if_neg (by omega)]
  have hlast : (L + 1 + 1) % (L + 2) = 0 := by
    rw [show L + 1 + 1 = L + 2 by omega]; exact Nat.mod_self _
  refine ⟨L + 2, F, by omega, ?_, ?_, ?_, ?_⟩
  · intro r hr
    rcases Nat.eq_zero_or_pos r with rfl | hr0
    · rw [hF0]; exact hvS
    · rw [hFp r hr0]; exact hfS (r - 1) (by omega)
  · intro r hr r' hr' he
    rcases Nat.eq_zero_or_pos r with rfl | hr0
    · rcases Nat.eq_zero_or_pos r' with rfl | hr0'
      · rfl
      · rw [hF0, hFp r' hr0'] at he
        exact absurd he.symm (hfv (r' - 1) (by omega))
    · rcases Nat.eq_zero_or_pos r' with rfl | hr0'
      · rw [hF0, hFp r hr0] at he
        exact absurd he (hfv (r - 1) (by omega))
      · rw [hFp r hr0, hFp r' hr0'] at he
        have := hrep (r - 1) (by omega) (r' - 1) (by omega) he
        omega
  · intro r hr
    rcases Nat.eq_zero_or_pos r with rfl | hr0
    · have e : (0 + 1) % (L + 2) = 1 := Nat.mod_eq_of_lt (by omega)
      rw [hF0, e, hFp 1 one_pos, show (1 : ℕ) - 1 = 0 by omega, h0]
      exact hvx
    · rcases Nat.lt_or_ge r (L + 1) with hlt | hge
      · have e : (r + 1) % (L + 2) = r + 1 := Nat.mod_eq_of_lt (by omega)
        rw [e, hFp r hr0, hFp (r + 1) (by omega), show r + 1 - 1 = r - 1 + 1 by omega]
        exact hadj (r - 1) (by omega)
      · have hre : r = L + 1 := by omega
        subst hre
        rw [hlast, hF0, hFp (L + 1) (by omega), show L + 1 - 1 = L by omega, hL]
        exact padj_symm hvy
  · intro r hr r' hr' hne1 hne2 hne3 hadjF
    rcases Nat.eq_zero_or_pos r with rfl | hr0
    · rw [Nat.mod_eq_of_lt (show 0 + 1 < L + 2 by omega)] at hne2
      have hr'L : r' ≠ L + 1 := by
        intro h; rw [h, hlast] at hne3; exact hne3 rfl
      rw [hF0, hFp r' (by omega)] at hadjF
      exact hCfar _ (hC (r' - 1) (by omega) (by omega)) hadjF
    · rcases Nat.eq_zero_or_pos r' with rfl | hr0'
      · rw [Nat.mod_eq_of_lt (show 0 + 1 < L + 2 by omega)] at hne3
        have hrL : r ≠ L + 1 := by
          intro h; rw [h, hlast] at hne2; exact hne2 rfl
        rw [hF0, hFp r (by omega)] at hadjF
        exact hCfar _ (hC (r - 1) (by omega) (by omega)) (padj_symm hadjF)
      · rw [hFp r hr0, hFp r' hr0'] at hadjF
        have key : (r - 1) + 1 < (r' - 1) ∨ (r' - 1) + 1 < (r - 1) := by
          rcases Nat.lt_or_ge r (L + 1) with h | h
          · rw [Nat.mod_eq_of_lt (show r + 1 < L + 2 by omega)] at hne2
            rcases Nat.lt_or_ge r' (L + 1) with h' | h'
            · rw [Nat.mod_eq_of_lt (show r' + 1 < L + 2 by omega)] at hne3
              omega
            · omega
          · have hre : r = L + 1 := by omega
            subst hre
            rcases Nat.lt_or_ge r' (L + 1) with h' | h'
            · rw [Nat.mod_eq_of_lt (show r' + 1 < L + 2 by omega)] at hne3
              omega
            · omega
        rcases key with hk | hk
        · exact hchord (r - 1) (by omega) (r' - 1) (by omega) hk hadjF
        · exact hchord (r' - 1) (by omega) (r - 1) (by omega) hk (padj_symm hadjF)

/-! ### Connectivity inside a vertex set -/

/-- `b` is reachable from `a` by a walk staying inside `D`. -/
def ReachIn (E : Fin m → Finset (Fin (n + 1))) (D : Finset (Fin (n + 1)))
    (a b : Fin (n + 1)) : Prop :=
  Relation.ReflTransGen (fun p q => p ∈ D ∧ q ∈ D ∧ PrimalAdj E p q) a b

theorem reachIn_symm {D : Finset (Fin (n + 1))} {a b : Fin (n + 1)}
    (h : ReachIn E D a b) : ReachIn E D b a := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | @tail c d _ hcd ih =>
      exact Relation.ReflTransGen.trans
        (Relation.ReflTransGen.single ⟨hcd.2.1, hcd.1, padj_symm hcd.2.2⟩) ih

/-- A reachability certificate unrolls into an explicit walk, every
vertex of which is again reachable from the source. -/
theorem walk_of_reachIn {D : Finset (Fin (n + 1))} {a b : Fin (n + 1)}
    (h : ReachIn E D a b) (ha : a ∈ D) :
    ∃ (M : ℕ) (g : ℕ → Fin (n + 1)), g 0 = a ∧ g M = b ∧
      (∀ i < M, PrimalAdj E (g i) (g (i + 1))) ∧
      (∀ i ≤ M, g i ∈ D ∧ ReachIn E D a (g i)) := by
  induction h with
  | refl => exact ⟨0, fun _ => a, rfl, rfl, by omega, fun i hi => ⟨ha, Relation.ReflTransGen.refl⟩⟩
  | @tail c d hac hcd ih =>
      obtain ⟨M, g, hg0, hgM, hgadj, hgD⟩ := ih
      refine ⟨M + 1, fun r => if r ≤ M then g r else d, by simpa using hg0, by simp, ?_, ?_⟩
      · intro i hi
        dsimp only
        rcases Nat.lt_or_ge i M with h1 | h1
        · rw [if_pos (by omega), if_pos (by omega)]
          exact hgadj i h1
        · have hiM : i = M := by omega
          subst hiM
          rw [if_pos (by omega), if_neg (by omega), hgM]
          exact hcd.2.2
      · intro i hi
        dsimp only
        rcases Nat.lt_or_ge i (M + 1) with h1 | h1
        · rw [if_pos (by omega)]
          exact hgD i (by omega)
        · have hiM : i = M + 1 := by omega
          subst hiM
          rw [if_neg (by omega)]
          exact ⟨hcd.2.1, Relation.ReflTransGen.tail (hgD M (le_refl M)).2 (by rw [hgM]; exact hcd)⟩

/-- Prepending and appending one edge to a walk through `C`. -/
theorem cwalk_extend {C : Finset (Fin (n + 1))} {x y cx cy : Fin (n + 1)} {M : ℕ}
    {g : ℕ → Fin (n + 1)} (hg0 : g 0 = cx) (hgM : g M = cy)
    (hgadj : ∀ i < M, PrimalAdj E (g i) (g (i + 1))) (hgC : ∀ i ≤ M, g i ∈ C)
    (hx : PrimalAdj E x cx) (hy : PrimalAdj E cy y) :
    CWalk E C x y (M + 2) := by
  refine ⟨fun r => if r = 0 then x else if r ≤ M + 1 then g (r - 1) else y, by simp,
    by dsimp only; rw [if_neg (by omega), if_neg (by omega)], ?_, ?_⟩
  · intro r hr
    dsimp only
    rcases Nat.eq_zero_or_pos r with rfl | hr0
    · rw [if_pos rfl, if_neg (by omega), if_pos (by omega), show (0 : ℕ) + 1 - 1 = 0 by omega, hg0]
      exact hx
    · rcases Nat.lt_or_ge r (M + 1) with h1 | h1
      · rw [if_neg (by omega), if_pos (by omega), if_neg (by omega), if_pos (by omega),
          show r + 1 - 1 = r - 1 + 1 by omega]
        exact hgadj (r - 1) (by omega)
      · have hrM : r = M + 1 := by omega
        subst hrM
        rw [if_neg (by omega), if_pos (by omega), if_neg (by omega), if_neg (by omega),
          show M + 1 - 1 = M by omega, hgM]
        exact hy
  · intro r hr0 hr
    dsimp only
    rw [if_neg (by omega), if_pos (by omega)]
    exact hgC (r - 1) (by omega)

/-! ### The induction

`Strong E k` is Dirac's theorem in the strong form that inducts: a vertex
set of at most `k` vertices carrying no chordless cycle of length `≥ 4`
is a clique, or has two non-adjacent simplicial vertices. -/

/-- The inductive statement. -/
def Strong (E : Fin m → Finset (Fin (n + 1))) (k : ℕ) : Prop :=
  ∀ S : Finset (Fin (n + 1)), S.card ≤ k → ¬ HasCyc E S →
    Clique E S ∨ ∃ x ∈ S, ∃ y ∈ S,
      ¬ PrimalAdj E x y ∧ Simplicial E S x ∧ Simplicial E S y

/-- **The inductive step.**  Given a vertex `v` and a vertex `w` not
adjacent to it, the component `C` of `w` in `S \ N[v]` contains a vertex
that is simplicial in the whole of `S`.  The attachment set
`A = N(v) ∩ N(C)` is a clique — otherwise a shortest walk through `C`
closes into a chordless cycle through `v` — so the induction hypothesis,
applied to `C ∪ A`, must return a simplicial vertex inside `C`, and the
`S`-neighbourhood of a vertex of `C` is contained in `C ∪ A`. -/
theorem exists_simplicial_far {k : ℕ} (IH : Strong E k) {S : Finset (Fin (n + 1))}
    (hcard : S.card ≤ k + 1) (hnc : ¬ HasCyc E S)
    {v w : Fin (n + 1)} (hvS : v ∈ S) (hwS : w ∈ S) (hwv : w ≠ v)
    (hvw : ¬ PrimalAdj E v w) :
    ∃ z ∈ S, ¬ PrimalAdj E v z ∧ Simplicial E S z := by
  classical
  set D : Finset (Fin (n + 1)) := (S.erase v).filter (fun u => ¬ PrimalAdj E v u) with hD
  have hmemD : ∀ u, u ∈ D ↔ (u ∈ S ∧ u ≠ v ∧ ¬ PrimalAdj E v u) := by
    intro u; simp only [hD, Finset.mem_filter, Finset.mem_erase]; tauto
  have hwD : w ∈ D := (hmemD w).2 ⟨hwS, hwv, hvw⟩
  set C : Finset (Fin (n + 1)) := D.filter (fun u => ReachIn E D w u) with hCdef
  have hmemC : ∀ u, u ∈ C ↔ (u ∈ D ∧ ReachIn E D w u) := by
    intro u; simp only [hCdef, Finset.mem_filter]
  have hwC : w ∈ C := (hmemC w).2 ⟨hwD, Relation.ReflTransGen.refl⟩
  have hCD : C ⊆ D := Finset.filter_subset _ _
  have hCS : C ⊆ S := fun u hu => ((hmemD u).1 (hCD hu)).1
  have hCfar : ∀ c ∈ C, ¬ PrimalAdj E v c := fun c hc => ((hmemD c).1 (hCD hc)).2.2
  set A : Finset (Fin (n + 1)) :=
    S.filter (fun u => PrimalAdj E v u ∧ ∃ c ∈ C, PrimalAdj E u c) with hAdef
  have hmemA : ∀ u, u ∈ A ↔ (u ∈ S ∧ PrimalAdj E v u ∧ ∃ c ∈ C, PrimalAdj E u c) := by
    intro u; simp only [hAdef, Finset.mem_filter]
  have hAS : A ⊆ S := Finset.filter_subset _ _
  have hAv : ∀ u ∈ A, u ≠ v := by
    intro u hu hcon
    obtain ⟨-, -, c, hc, hadj⟩ := (hmemA u).1 hu
    exact hCfar c hc (by rw [← hcon]; exact hadj)
  set T : Finset (Fin (n + 1)) := C ∪ A with hTdef
  have hTS : T ⊆ S.erase v := by
    intro u hu
    rcases Finset.mem_union.1 hu with h | h
    · exact Finset.mem_erase.2 ⟨((hmemD u).1 (hCD h)).2.1, hCS h⟩
    · exact Finset.mem_erase.2 ⟨hAv u h, hAS h⟩
  have hTcard : T.card ≤ k := by
    have h1 : T.card ≤ (S.erase v).card := Finset.card_le_card hTS
    have h2 : (S.erase v).card = S.card - 1 := Finset.card_erase_of_mem hvS
    have h3 : 1 ≤ S.card := Finset.card_pos.2 ⟨v, hvS⟩
    omega
  -- the `S`-neighbours of a vertex of `C` lie in `T`
  have hclosed : ∀ c ∈ C, ∀ u ∈ S, PrimalAdj E c u → u ∈ T := by
    intro c hc u huS hadj
    by_cases hvu : PrimalAdj E v u
    · exact Finset.mem_union.2 (Or.inr ((hmemA u).2 ⟨huS, hvu, c, hc, padj_symm hadj⟩))
    · have huv : u ≠ v := by
        intro hcon
        exact hCfar c hc (by rw [← hcon]; exact padj_symm hadj)
      have huD : u ∈ D := (hmemD u).2 ⟨huS, huv, hvu⟩
      exact Finset.mem_union.2 (Or.inl ((hmemC u).2 ⟨huD,
        Relation.ReflTransGen.tail ((hmemC c).1 hc).2 ⟨hCD hc, huD, hadj⟩⟩))
  -- the attachment set is a clique
  have hAclique : Clique E A := by
    intro x hx y hy
    by_contra hxy
    obtain ⟨hxS, hvx, cx, hcx, hxcx⟩ := (hmemA x).1 hx
    obtain ⟨hyS, hvy, cy, hcy, hycy⟩ := (hmemA y).1 hy
    have hreach : ReachIn E D cx cy :=
      Relation.ReflTransGen.trans (reachIn_symm ((hmemC cx).1 hcx).2) ((hmemC cy).1 hcy).2
    obtain ⟨M, g, hg0, hgM, hgadj, hgD⟩ := walk_of_reachIn hreach (hCD hcx)
    have hgC : ∀ i ≤ M, g i ∈ C := fun i hi =>
      (hmemC (g i)).2 ⟨(hgD i hi).1,
        Relation.ReflTransGen.trans ((hmemC cx).1 hcx).2 (hgD i hi).2⟩
    exact hnc (hasCyc_of_attached hvS hCS hCfar hxS hyS hvx hvy hxy
      (cwalk_extend hg0 hgM hgadj hgC hxcx (padj_symm hycy)))
  -- feed `T` to the induction hypothesis
  have hncT : ¬ HasCyc E T := fun h =>
    hnc (hasCyc_mono (fun u hu => Finset.mem_of_mem_erase (hTS hu)) h)
  have lift : ∀ z ∈ C, Simplicial E T z → ∃ z ∈ S, ¬ PrimalAdj E v z ∧ Simplicial E S z := by
    intro z hzC hz
    refine ⟨z, hCS hzC, hCfar z hzC, ?_⟩
    intro u huS z' hz'S hzu hzz'
    exact hz u (hclosed z hzC u huS hzu) z' (hclosed z hzC z' hz'S hzz') hzu hzz'
  rcases IH T hTcard hncT with hcl | ⟨p, hpT, q, hqT, hpq, hsp, hsq⟩
  · exact lift w hwC (fun u huT z hzT _ _ => hcl u huT z hzT)
  · have hone : p ∈ C ∨ q ∈ C := by
      by_contra hcon
      push Not at hcon
      exact hpq (hAclique p ((Finset.mem_union.1 hpT).resolve_left hcon.1)
        q ((Finset.mem_union.1 hqT).resolve_left hcon.2))
    rcases hone with h | h
    · exact lift p h hsp
    · exact lift q h hsq

/-- **Dirac's theorem, strong form.**  A vertex set carrying no chordless
cycle of length `≥ 4` is a clique or has two non-adjacent simplicial
vertices.  Induction on the number of vertices. -/
theorem strong (E : Fin m → Finset (Fin (n + 1))) (k : ℕ) : Strong E k := by
  induction k with
  | zero =>
      intro S hcard _
      have hS : S = ∅ := Finset.card_eq_zero.1 (Nat.le_zero.1 hcard)
      subst hS
      refine Or.inl ?_
      intro u hu w _
      exact absurd hu (by simp)
  | succ k IH =>
      intro S hcard hnc
      by_cases hcl : Clique E S
      · exact Or.inl hcl
      · refine Or.inr ?_
        rw [Clique] at hcl
        push Not at hcl
        obtain ⟨a, haS, b, hbS, hab⟩ := hcl
        have iso : ∀ c : Fin (n + 1), ¬ PrimalAdj E c c → Simplicial E S c := by
          intro c hc u _ z _ h1 _
          exact absurd (padj_refl_of h1) hc
        by_cases hba : b = a
        · have hab' : ¬ PrimalAdj E a a := by rw [hba] at hab; exact hab
          exact ⟨a, haS, a, haS, hab', iso a hab', iso a hab'⟩
        · obtain ⟨z₁, hz₁S, hz₁, hs₁⟩ := exists_simplicial_far IH hcard hnc haS hbS hba hab
          by_cases hz₁a : z₁ = a
          · have hz₁' : ¬ PrimalAdj E a a := by rw [hz₁a] at hz₁; exact hz₁
            exact ⟨a, haS, a, haS, hz₁', iso a hz₁', iso a hz₁'⟩
          · obtain ⟨z₂, hz₂S, hz₂, hs₂⟩ :=
              exists_simplicial_far IH hcard hnc hz₁S haS (Ne.symm hz₁a)
                (fun h => hz₁ (padj_symm h))
            exact ⟨z₁, hz₁S, z₂, hz₂S, hz₂, hs₁, hs₂⟩

/-- **Dirac's theorem, contrapositive form.**  A nonempty vertex set with
no simplicial vertex carries a chordless cycle of length `≥ 4`. -/
theorem hasCyc_of_no_simplicial {S : Finset (Fin (n + 1))} (hne : S.Nonempty)
    (h : ∀ v ∈ S, ¬ Simplicial E S v) : HasCyc E S := by
  by_contra hnc
  rcases strong E S.card S (le_refl _) hnc with hcl | ⟨x, hxS, y, hyS, -, hsx, -⟩
  · obtain ⟨v, hv⟩ := hne
    exact h v hv (fun u hu z hz _ _ => hcl u hu z hz)
  · exact h x hxS hsx

/-! ### Transport to the `Fin (p + 4)` indexing of `DiracHypothesis` -/

theorem hasIndCycle_of_hasCyc {S : Finset (Fin (n + 1))} (h : HasCyc E S) :
    ∃ (p : ℕ) (c : Fin (p + 4) → Fin (n + 1)),
      (∀ i, c i ∈ S) ∧ Function.Injective c ∧
      (∀ i, PrimalAdj E (c (i - 1)) (c i)) ∧
      ∀ i j : Fin (p + 4), i ≠ j → i ≠ j + 1 → j ≠ i + 1 →
        ¬ PrimalAdj E (c i) (c j) := by
  obtain ⟨N, f, hcyc⟩ := h
  have h4 : 4 ≤ N := hcyc.four
  obtain ⟨p, rfl⟩ : ∃ p, N = p + 4 := ⟨N - 4, by omega⟩
  have hadd : ∀ i : Fin (p + 4), (i + 1).val = (i.val + 1) % (p + 4) := by
    intro i
    rw [Fin.val_add, Fin.val_one', Nat.mod_eq_of_lt (show 1 < p + 4 by omega)]
  refine ⟨p, fun i => f i.val, fun i => hcyc.mem i.val i.isLt,
    fun i j hij => Fin.ext (hcyc.inj i.val i.isLt j.val j.isLt hij), ?_, ?_⟩
  · intro i
    have hsub : ((i - 1).val + 1) % (p + 4) = i.val := by
      rw [Fin.coe_sub_one]
      split_ifs with h
      · subst h
        have e : (p + 3 + 1) % (p + 4) = 0 := by
          rw [show p + 3 + 1 = p + 4 from by omega]; exact Nat.mod_self _
        rw [e]
        rfl
      · have hv : i.val ≠ 0 := fun hz => h (Fin.ext hz)
        rw [Nat.sub_add_cancel (by omega), Nat.mod_eq_of_lt i.isLt]
    have hstep := hcyc.adj (i - 1).val (i - 1).isLt
    rwa [hsub] at hstep
  · intro i j hij hij1 hji1 hadjF
    refine hcyc.ind i.val i.isLt j.val j.isLt (fun h => hij (Fin.ext h).symm)
      (fun h => hji1 (Fin.ext (by rw [h, hadd i])))
      (fun h => hij1 (Fin.ext (by rw [h, hadd j]))) hadjF

/-! ### The discharge -/

/-- **Dirac's simplicial-vertex theorem**, in exactly the form
`Ste.ConverseFull` isolates it: the hypothesis threaded through
`extraction_of_dirac`,
`not_gyoReducible_exists_pairwiseConsistent_not_solvable` and
`gyoReducible_iff_pairwiseConsistent_solvable_of_dirac` holds for every
hypergraph.  Those results are therefore unconditional. -/
theorem dirac_hypothesis_holds {m n : ℕ} (E : Fin m → Finset (Fin (n + 1))) :
    DiracHypothesis E := by
  intro S hne hsimp
  refine hasIndCycle_of_hasCyc (hasCyc_of_no_simplicial hne ?_)
  intro v hv hsv
  obtain ⟨u, huS, w, hwS, h1, h2, h3⟩ := hsimp v hv
  exact h3 (hsv u huS w hwS h1 h2)

/-! ### The conditional results of `Ste.ConverseFull`, now unconditional -/

/-- `extraction_of_dirac`, with the hypothesis discharged. -/
theorem extraction {m n : ℕ} {E : Fin m → Finset (Fin (n + 1))}
    (hcov : ∀ v, ∃ k, v ∈ E k) (h : ¬ GYOReducible E) :
    ¬ Conformal E ∨ ¬ Chordal E :=
  extraction_of_dirac hcov (dirac_hypothesis_holds E) h

/-- **The full converse BFMY direction**, unconditionally. -/
theorem not_gyoReducible_exists_pairwiseConsistent_not_solvable {m n : ℕ}
    {E : Fin m → Finset (Fin (n + 1))} (hcov : ∀ v, ∃ k, v ∈ E k)
    (h : ¬ GYOReducible E) :
    ∃ Rel : Fin m → (Fin (n + 1) → ℕ) → Prop,
      EdgeSupported E Rel ∧
      PairwiseConsistent (fun _ => (Set.univ : Set ℕ)) E Rel ∧
      (∀ k, ∃ t : Fin (n + 1) → ℕ,
        (∀ u, t u ∈ (Set.univ : Set ℕ)) ∧ Rel k t) ∧
      ¬ ∃ f : Fin (n + 1) → ℕ,
        (∀ u, f u ∈ (Set.univ : Set ℕ)) ∧ ∀ k, Rel k f :=
  STE.not_gyoReducible_exists_pairwiseConsistent_not_solvable hcov
    (dirac_hypothesis_holds E) h

/-- **The BFMY equivalence**, unconditionally. -/
theorem gyoReducible_iff_pairwiseConsistent_solvable {m n : ℕ}
    {E : Fin m → Finset (Fin (n + 1))} (hcov : ∀ v, ∃ k, v ∈ E k) :
    GYOReducible E ↔
      ∀ Rel : Fin m → (Fin (n + 1) → ℕ) → Prop, EdgeSupported E Rel →
        PairwiseConsistent (fun _ => (Set.univ : Set ℕ)) E Rel →
        (∀ k, ∃ t : Fin (n + 1) → ℕ,
          (∀ u, t u ∈ (Set.univ : Set ℕ)) ∧ Rel k t) →
        ∃ f : Fin (n + 1) → ℕ,
          (∀ u, f u ∈ (Set.univ : Set ℕ)) ∧ ∀ k, Rel k f :=
  gyoReducible_iff_pairwiseConsistent_solvable_of_dirac hcov (dirac_hypothesis_holds E)

end Dirac
end STE
