# Multidocument Frame Coreference: A Topological & STE Perspective

## Motivation
Standard NLP cross-document event coreference models rely on probabilistic neural models (LLMs) and heuristic agglomerative clustering. We take extraction as a given and replace the probabilistic resolution with a strict, deterministically topological algebra. 

## 1. Graph Clusters & Algebraic Topology
We view the universe of frames $F$ as vertices of a graph.
* **Positive Edges**: Two frames are coreferent within a document.
* **Negative Edges**: Discourse-aware modeling (e.g., temporal mismatch or mutually exclusive events) dictates two frames contradict.

In an algebraically topological sense, if we only have positive edges, the coreference clusters are precisely the **connected components** of the graph, which corresponds to the 0-th Homology group $H_0$. 

## 2. Sheaf Theory & Multidocument Fusion
We map multiple documents to a **Sheaf** over this graph:
* **Local Sections**: Each document provides a local view of coreference (its positive and negative edges).
* **Global Sections**: Resolving the coref is finding a universal partition (equivalence relation) that aligns with all local document constraints.

If Document A links $f_1 = f_2$, B links $f_2 = f_3$, but Discourse extracts $f_1 \neq f_3$, the documents cannot be merged. This manifests as a **failure of local sections to glue**: there is no global section, i.e. an $H^0$-level emptiness. For presheaves of *sets* (as here), $H^1$ is not even defined — a genuine $H^1$ class requires abelian-group or torsor coefficients (Abramsky–Mansfield–Barbosa).

Two clarifications, since earlier drafts blurred them.

*It is not a cycle.* The mechanized criterion for infeasibility is "a negative edge inside a positive connected component" (`multidocFeasibility_nonempty_iff` in `Ste/FrameCoref.lean`). The example above happens to close a triangle, but the triangle is incidental: a negative edge joining any two frames already forced together by a chain of positive edges is enough, of any length. There is no cycle condition, and nothing here detects cycles.

*It is not what `CechObstruction` counts.* That module's count lives in a different setting: a two-bit product hypothesis space under the singleton cover, where the gluing defect is the number of compatible-but-non-gluing families. The setting here is `Setoid F` — equivalence relations constrained by per-document positive and negative edges — and infeasibility is plain emptiness of an intersection, with no analogous count mechanized. The two are the same *shape* of failure (local data that does not assemble), not the same invariant.

## 3. Set Theoretic Estimation (STE) Formulation
This topological problem perfectly instantiates a Set Theoretic Estimation.
* **Solution Space ($\Xi$)**: The set of all valid equivalence relations over $F$ (`Setoid F`).
* **Property Set ($S_d$)**: For a document $d$, $S_d$ is the subset of relations containing all positive edges and excluding all negative edges of $d$.
* **Feasibility Set ($\Phi$)**: The multidocument merge state is the intersection $\bigcap S_d$.

When the gluing obstruction occurs, the feasibility set $\Phi = \emptyset$. This triggers Combettes' validity detection, indicating "unfair" information that must be algebraically reconciled — e.g. via a **Signed Graph Laplacian eigenspace relaxation**, which is a heuristic repair *outside* the STE algebra proper (a projection/relaxation applied only in the inconsistent case, cf. Combettes), not part of the feasibility calculus itself. Because it relies on set intersection, **insertion** of documents is order-independent (intersection is commutative, associative, and idempotent); **removal** has no inverse operation within the algebra and requires recomputing $\Phi$ from the surviving documents.
