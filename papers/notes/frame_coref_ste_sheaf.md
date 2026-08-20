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

If Document A links $f_1 = f_2$, B links $f_2 = f_3$, but Discourse extracts $f_1 \neq f_3$, this creates an unresolvable graph cycle. In Sheaf theory, this contradiction is a **cohomological obstruction** (a non-zero element in the first cohomology group $H^1$). 

## 3. Set Theoretic Estimation (STE) Formulation
This topological problem perfectly instantiates a Set Theoretic Estimation.
* **Solution Space ($\Xi$)**: The set of all valid equivalence relations over $F$ (`Setoid F`).
* **Property Set ($S_d$)**: For a document $d$, $S_d$ is the subset of relations containing all positive edges and excluding all negative edges of $d$.
* **Feasibility Set ($\Phi$)**: The multidocument merge state is the intersection $\bigcap S_d$.

When an obstruction $H^1 \neq 0$ occurs, the feasibility set $\Phi = \emptyset$. This triggers Combettes' validity detection, indicating "unfair" information that must be algebraically reconciled (e.g., using a Signed Graph Laplacian eigenspace relaxation). Because it relies on set intersection, the insertion and removal of documents perfectly commute.
