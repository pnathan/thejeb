# Uncertain Frames & Topological Holes

Assuming an extracted frame is always precisely identified is a brittle assumption. Often, NLP extraction yields an ambiguous entity—we know a frame exists, but it could be one of several plausible canonical frames.

This requires us to upgrade our mathematical space from a simple graph to a **Simplicial Complex** (or Hypergraph), allowing uncertainty to manifest as literal, computable "holes" in the topology.

## 1. Frames as Regions, Not Points
Instead of an extracted claim mapping to a precise vertex $f \in F$, it maps to a subset of plausible frames $U \subseteq F$. 
* In a graph, $U$ is not a point; it is a **region** or a **simplex**.
* A coreference link between two uncertain claims is no longer an edge between two points, but an edge between two *regions*.

## 2. The Topological "Hole"
In algebraic topology, when you have a set of plausible states connected by relationships, but you don't know the exact "interior" truth, you have a **topological hole** (specifically, non-trivial Homology $H_n \neq 0$).

You don't need to force a decision. You can "run the computation with holes." 
The holes simply persist in the algebra as uncollapsed simplices. They act as placeholders in the multidocument merge.

## 3. How the STE Hyperopinions Handle Holes
Our Set Theoretic Estimation (STE) math using **Hyperopinions** and **Plural Feasible Sets** is practically built for this:

1. **The Disjunction**: If Claim 1 is $\{f_A \text{ or } f_B\}$ and Claim 2 is $f_C$, and the document says they corefer, the document's hyperopinion expands to:
   $\mathcal{H}_d = \{ (f_A \text{ corefers with } f_C), (f_B \text{ corefers with } f_C) \}$
2. **Plural Propagation**: We don't pick one. Both property sets distribute into our Cartesian product. This creates two distinct parallel feasible sets ($\Phi_1$ and $\Phi_2$). 
3. **Filling the Hole**: The hole remains in the graph (represented by the active plural feasible sets) until a later document $d_{later}$ arrives. 
   Suppose $d_{later}$ proves that $f_B$ cannot corefer with $f_C$ (e.g., temporal contradiction). 
   When we intersect $\Phi_2 \cap S_{later}$, the result is $\emptyset$. That entire universe of possibilities vanishes.
   The topological hole "fills in" and collapses exclusively to $f_A$.

## Conclusion
By treating uncertain frames as subsets (simplices) rather than exact points, the coreference engine becomes a lazy-evaluation topology. 
* "Holes" are just unresolved sets of plural feasible sets.
* New documents act as boundary operators that "fill" the holes by zeroing out the incorrect branches via $\emptyset$ intersections.
* The system never makes a brittle, premature guess. It algebraically carries the uncertainty forward until the data necessitates a collapse.
