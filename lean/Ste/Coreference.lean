/-
Multi-document coreference, mechanized as a `Setoid` lattice operation.

`Ste.PartitionRank` reads the STE dynamic-frame development in Shannon's
lattice-of-partitions terms: `mustSetoid D`, the must-coreference relation
forced by a corpus `D`, is the *meet* (`sInf`) of the exact coreference
partitions of the individually feasible hypotheses (`mustSetoid_eq_sInf`).
That picture is single-document: every claim lives in one shared `Claim`
type and coreference is a single partition of it.

This module mechanizes the case that picture brackets: coreference across
*several* documents, each with its own local mention space, stitched
together by explicit cross-document links. The natural object is the same
complete lattice `Setoid Mention` used in `PartitionRank`, but now the
"forced" relation is read the other way: not the meet of what every
hypothesis agrees on, but the *join* (closure) of what the evidence
(per-document local coreference decisions, plus asserted cross-document
links) directly asserts. We show:

* `forcedCoref_eq_sInf` — the join reading and the "smallest adequate
  setoid" reading of the corpus-forced coreference coincide, the dual of
  `mustSetoid_eq_sInf`.
* `forcedCoref_mono_docs` / `forcedCoref_mono_link` — monotonicity in the
  active document set and in the link relation, the analogue of
  `mustSetoid_mono` / `rank_mustSetoid_mono`.
* `forcedCoref_no_links_same_doc` — a locality/separation lemma: absent any
  cross-document link, the forced coreference never crosses a document
  boundary.
* `witness_cross_doc_forced` — a concrete `Fin`-based witness: a *chain* of
  two cross-document links forces an identification that no single link
  asserts directly.
* `rank_forcedCoref_mono_docs` — the partition-rank (`PartitionRank.rank`)
  corollary of `forcedCoref_mono_docs`.
-/
import Ste.PartitionRank
import Mathlib.Data.Setoid.Basic
import Mathlib.Logic.Relation
import Mathlib.Data.Fintype.Sigma

namespace STE.Coreference

universe uDoc uLocal

variable {Doc : Type uDoc} (Local : Doc → Type uLocal)

/-- A mention: a document index together with a mention id local to that
document. -/
def Mention := Σ d : Doc, Local d

variable {Local}

/-! ## Part A: per-document local contributions

Each document contributes its own local coreference decisions. We embed
document `d`'s local coreference `loc d : Setoid (Local d)` as a setoid on
the whole `Mention` type that relates two mentions of document `d` exactly
as `loc d` does, and otherwise only ever relates a mention to itself — "a
setoid that only relates mentions within one document." -/

/-- The setoid on `Mention` contributed by a single document `d`'s local
coreference `loc d`. -/
def docSetoid (loc : ∀ d, Setoid (Local d)) (d : Doc) : Setoid (Mention Local) where
  r x y := x = y ∨ ∃ hx : x.1 = d, ∃ hy : y.1 = d, loc d (hx ▸ x.2) (hy ▸ y.2)
  iseqv := by
    refine ⟨fun _ => Or.inl rfl, ?_, ?_⟩
    · rintro x y (rfl | ⟨hx, hy, hxy⟩)
      · exact Or.inl rfl
      · exact Or.inr ⟨hy, hx, (loc d).symm' hxy⟩
    · rintro x y z hxy hyz
      rcases hxy with rfl | ⟨hx, hy, hxy'⟩
      · exact hyz
      rcases hyz with rfl | ⟨hy', hz, hyz'⟩
      · exact Or.inr ⟨hx, hy, hxy'⟩
      · exact Or.inr ⟨hx, hz, (loc d).trans' hxy' hyz'⟩

/-- `docSetoid` never merges mentions outside its own document: it is below
the "same document" kernel setoid, the pullback of equality along
`Sigma.fst`. -/
def sameDocSetoid : Setoid (Mention Local) := Setoid.ker (Sigma.fst : Mention Local → Doc)

theorem docSetoid_le_sameDoc (loc : ∀ d, Setoid (Local d)) (d : Doc) :
    docSetoid loc d ≤ sameDocSetoid := by
  rintro x y (rfl | ⟨hx, hy, -⟩)
  · rfl
  · show x.1 = y.1
    rw [hx, hy]

/-! ## Part B: cross-document links and the corpus-forced coreference

Cross-document links are additional evidence: a raw relation `Link` on
`Mention` (not assumed to be an equivalence relation itself — a single
asserted link need not be transitive or even hold between mentions of the
same document). The corpus-forced coreference is the join, in the
complete lattice `Setoid Mention`, of every active document's contribution
together with the equivalence closure of `Link`. -/

/-- The corpus-forced coreference over the active document set `S`: the
join of every active document's local contribution (`docSetoid loc d` for
`d ∈ S`) with the cross-document `Link` relation, closed under
transitivity. This is "what the corpus forces us to identify": the
coarsest merges needed to respect (a) every active document's own
coreference decisions and (b) every asserted cross-document link. -/
def forcedCoref (loc : ∀ d, Setoid (Local d)) (Link : Mention Local → Mention Local → Prop)
    (S : Set Doc) : Setoid (Mention Local) :=
  sSup (docSetoid loc '' S) ⊔ Relation.EqvGen.setoid Link

/-- The corpus-forced coreference is exactly the smallest setoid dominating
every active document's contribution and containing every cross-document
link: the join over "what's given" equals the infimum over "what's
adequate." This is the dual of `mustSetoid_eq_sInf`: there `sInf` reads off
the meet of the feasible partitions (the "must" reading, true in every
surviving hypothesis); here `sInf` reads off the universal property of the
join (the smallest partition consistent with all the evidence).

**Pattern note (U4).** The proof below and
`STE.FrameCoref.posSetoid_eq_sInf` are the same argument: the constructed
relation is the *least* element of the set of "adequate" setoids
(adequacy being an upward-closed predicate in the complete lattice
`Setoid _`), and a least element of a set is its `sInf`.  The general
fact is already Mathlib's `IsLeast.isGLB` composed with `IsGLB.sInf_eq`;
the `le_antisymm` / `le_sInf` / `sInf_le` proof below is that composition
inlined, so no STE-specific abstraction of it is offered.
`STE.DynamicFrame.Model.mustSetoid_eq_sInf` looks similar but is a
*different* fact: an `sInf` of an image family unfolded pointwise by
`Setoid.sInf_iff`, not a least-element characterization.  See the module
docstring of `Ste.InfoFrame`. -/
theorem forcedCoref_eq_sInf (loc : ∀ d, Setoid (Local d))
    (Link : Mention Local → Mention Local → Prop) (S : Set Doc) :
    forcedCoref loc Link S =
      sInf {s : Setoid (Mention Local) |
        (∀ d ∈ S, docSetoid loc d ≤ s) ∧ (∀ x y, Link x y → s x y)} := by
  apply le_antisymm
  · apply le_sInf
    rintro s ⟨hdocs, hlink⟩
    apply sup_le
    · apply sSup_le
      rintro t ⟨d, hd, rfl⟩
      exact hdocs d hd
    · exact Setoid.eqvGen_le hlink
  · apply sInf_le
    refine ⟨fun d hd => ?_, fun x y hxy => ?_⟩
    · exact le_trans (le_sSup (Set.mem_image_of_mem _ hd)) le_sup_left
    · exact Setoid.le_def.mp le_sup_right (Relation.EqvGen.rel x y hxy)

/-- Adding an active document can only add forced identifications: the
corpus-forced coreference is monotone in the active document set, in the
`Setoid` refinement order. Same conclusion shape as `mustSetoid_mono`, for
a different reason — there monotonicity comes from intersecting fewer
feasible hypotheses, here it comes from joining in more evidence. -/
theorem forcedCoref_mono_docs (loc : ∀ d, Setoid (Local d))
    (Link : Mention Local → Mention Local → Prop) {S S' : Set Doc} (h : S ⊆ S') :
    forcedCoref loc Link S ≤ forcedCoref loc Link S' :=
  sup_le_sup_right (sSup_le_sSup (Set.image_mono h)) _

/-- Adding cross-document links can only add forced identifications: the
corpus-forced coreference is monotone in the link relation. -/
theorem forcedCoref_mono_link (loc : ∀ d, Setoid (Local d))
    {Link Link' : Mention Local → Mention Local → Prop}
    (h : ∀ x y, Link x y → Link' x y) (S : Set Doc) :
    forcedCoref loc Link S ≤ forcedCoref loc Link' S :=
  sup_le_sup_left (Setoid.eqvGen_mono h) _

/-! ## Part C: locality / separation

Documents are coreference-independent absent linking evidence: with no
cross-document links at all, the corpus-forced coreference never crosses a
document boundary. -/

theorem forcedCoref_no_links_le_sameDoc (loc : ∀ d, Setoid (Local d)) (S : Set Doc) :
    forcedCoref loc (fun _ _ => False) S ≤ sameDocSetoid := by
  apply sup_le
  · apply sSup_le
    rintro t ⟨d, -, rfl⟩
    exact docSetoid_le_sameDoc loc d
  · exact Setoid.eqvGen_le fun _ _ h => h.elim

/-- Separation: a purely intra-document coreference — no cross-document
links present — never forces a cross-document identification. The forced
coreference relates two mentions only if they belong to the same
document. -/
theorem forcedCoref_no_links_same_doc (loc : ∀ d, Setoid (Local d)) (S : Set Doc)
    {x y : Mention Local} (h : forcedCoref loc (fun _ _ => False) S x y) : x.1 = y.1 :=
  Setoid.le_def.mp (forcedCoref_no_links_le_sameDoc loc S) h

/-! ## Part D: a concrete cross-document witness

Three documents, one mention apiece, and a *chain* of two links
(doc 0 – doc 1, doc 1 – doc 2, but never doc 0 – doc 2 directly): the
corpus-forced coreference identifies the document-0 and document-2
mentions purely by transitivity. -/

section Witness

/-- Three documents, each with a single local mention. -/
abbrev WitnessDoc := Fin 3

/-- Exactly one local mention per document. -/
abbrev WitnessLocal : WitnessDoc → Type := fun _ => Fin 1

/-- No document has any internal coreference to contribute here: the
cross-document links alone do the work. -/
def witnessLoc : ∀ d : WitnessDoc, Setoid (WitnessLocal d) := fun _ => ⊥

/-- A chain of two cross-document links: document 0 to document 1, and
document 1 to document 2 — but never a direct link from document 0 to
document 2. -/
def chainLink : Mention WitnessLocal → Mention WitnessLocal → Prop :=
  fun x y => (x.1 = 0 ∧ y.1 = 1) ∨ (x.1 = 1 ∧ y.1 = 2)

/-- The lone mention of document 0. -/
def m0 : Mention WitnessLocal := ⟨0, 0⟩

/-- The lone mention of document 1. -/
def m1 : Mention WitnessLocal := ⟨1, 0⟩

/-- The lone mention of document 2. -/
def m2 : Mention WitnessLocal := ⟨2, 0⟩

/-- The chain is not itself a direct link: no asserted link runs straight
from document 0 to document 2. -/
theorem chainLink_not_direct : ¬ chainLink m0 m2 := by
  unfold chainLink m0 m2
  decide

/-- The two witness mentions genuinely live in different documents. -/
theorem m0_ne_m2_doc : (m0 : Mention WitnessLocal).1 ≠ (m2 : Mention WitnessLocal).1 := by decide

/-- The corpus-forced coreference over the whole three-document corpus. -/
def witnessCoref : Setoid (Mention WitnessLocal) := forcedCoref witnessLoc chainLink Set.univ

/-- The witness: a chain of two cross-document links forces the
identification of a mention in document 0 with a mention in document 2,
even though (`chainLink_not_direct`) no direct 0–2 link was ever asserted,
and (`m0_ne_m2_doc`) they are genuinely different documents. Non-vacuous:
`witnessCoref` is not the discrete setoid on these two mentions. -/
theorem witness_cross_doc_forced : witnessCoref m0 m2 := by
  have h01 : witnessCoref m0 m1 :=
    Setoid.le_def.mp le_sup_right (Relation.EqvGen.rel m0 m1 (Or.inl ⟨rfl, rfl⟩))
  have h12 : witnessCoref m1 m2 :=
    Setoid.le_def.mp le_sup_right (Relation.EqvGen.rel m1 m2 (Or.inr ⟨rfl, rfl⟩))
  exact witnessCoref.trans' h01 h12

end Witness

/-! ## Part E: a partition-rank corollary -/

section Rank

variable [Fintype Doc] [∀ d, Fintype (Local d)]

instance instFintypeMention : Fintype (Mention Local) :=
  inferInstanceAs (Fintype (Σ d, Local d))

/-- Coreference information is monotone in the active document set, read
off on the combinatorial partition-lattice rank of `PartitionRank`: adding
documents can only raise the rank of the corpus-forced coreference. The
direct analogue of `rank_mustSetoid_mono`. -/
theorem rank_forcedCoref_mono_docs (loc : ∀ d, Setoid (Local d))
    (Link : Mention Local → Mention Local → Prop) {S S' : Set Doc} (h : S ⊆ S') :
    PartitionRank.rank (forcedCoref loc Link S) ≤ PartitionRank.rank (forcedCoref loc Link S') :=
  PartitionRank.rank_le_rank (forcedCoref_mono_docs loc Link h)

end Rank

end STE.Coreference
