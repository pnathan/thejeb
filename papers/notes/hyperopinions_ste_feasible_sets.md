# Hyperopinions and Plural Feasible Sets in STE

When we move from rigid, binary constraints to **Hyperopinions**, we fundamentally shift the algebra of our multidocument coreference merge. 

As noted, a hyperopinion is not a strict binary assertion, nor is it a probabilistic (Dirichlet) mass distribution. In the Set Theoretic Estimation (STE) framework, a hyperopinion maps to uncertainty over the exact constraint, meaning a document does not yield a single property set, but rather a *collection* of possible property sets.

This is precisely the **crisp / possibilistic specialization** of Jøsang's hyperopinions (Jøsang, 2016, *Subjective Logic*): belief mass is concentrated entirely on a small number of subsets (here, the $S_{d,i}$) with a vacuous base rate, rather than spread continuously over the full opinion simplex.

## 1. The Mathematical Definition of a Hyperopinion
In standard STE, document $d$ provides a single property set $S_d \subseteq \Xi$ (the set of valid global equivalence relations).

With hyperopinions, document $d$ provides a set of valid alternatives (a disjunction of constraints). We define the hyperopinion of document $d$ as:
$$ \mathcal{H}_d = \{ S_{d,1}, S_{d,2}, \dots, S_{d,k} \} $$
where each $S_{d,i} \subseteq \Xi$ is a distinct property set. 

The true global state must reside in *at least one* of these property sets:
$$ Information(d) = \bigcup_{S \in \mathcal{H}_d} S $$

## 2. Reducing to Feasible Sets (Plural)
When we merge multiple documents $D = \{d_1, d_2, \dots\}$, the global multidocument state is the intersection of their hyperopinions:
$$ \Phi_{global} = \bigcap_{d \in D} \left( \bigcup_{S \in \mathcal{H}_d} S \right) $$

Because set intersection distributes over set union, this Cartesian product mathematically expands into a **plurality of feasible sets**:
$$ \Phi_{global} = \bigcup_{ \vec{S} \in \prod_{d \in D} \mathcal{H}_d } \left( S_{1} \cap S_{2} \cap \dots \cap S_{|D|} \right) $$

Instead of a single feasibility set $\Phi$, our system naturally collapses into a set of distinct, parallel feasible sets:
$$ \mathbf{\Phi} = \{ \Phi_1, \Phi_2, \dots, \Phi_m \} $$
where each $\Phi_i$ represents a valid global hypothesis for frame coreference.

Worth flagging: the number of branches is $\prod_d |\mathcal{H}_d|$, which blows up combinatorially in the number of documents — connecting to the repo's `RepresentationBounds`/`CouplingRank` line on how tightly coupled constraints inflate representation size.

## 3. The Implicit Resolution of Contradictions
Notice that **we no longer need explicit binary contradictions**. 

If we choose branch $S_{A,1}$ from Document A and branch $S_{B,2}$ from Document B, and those two views are incompatible, their intersection is trivially the empty set:
$$ S_{A,1} \cap S_{B,2} = \emptyset $$

In our distributive expansion, any incompatible combination automatically evaluates to $\emptyset$ and vanishes from the union. 
* We do not have to explicitly flag "this contradicts that." 
* We simply compute the algebraic intersections across the hyperopinions. 
* The branches that contradict die off as $\emptyset$. 
* The branches that survive form our **feasible sets (plural)**.

## 4. Commutativity and Operations
This formulation preserves our commutative requirements perfectly.
When we insert a new document $d_{new}$ with hyperopinion $\mathcal{H}_{new}$, we simply distribute it across our existing plural feasible sets:
$$ \mathbf{\Phi}_{updated} = \{ \Phi_i \cap S_j \mid \Phi_i \in \mathbf{\Phi}_{old}, S_j \in \mathcal{H}_{new} \} \setminus \{ \emptyset \} $$

*Correction:* the update rule (intersect, then discard $\emptyset$ branches) is non-injective, so this does not invert cleanly — **removal** of a document requires recomputation from the surviving documents, not an "any order" replay. Only **insertion** is order-independent. The underlying algebra is entirely set-theoretic, non-probabilistic, and — for insertion — deterministic. It maintains a branching universe of valid coreference states until the surviving branches shrink to at most a singleton, if the data suffices; note that surviving branches may overlap rather than partition $\Xi$. See `lean/Ste/PluralFeasibility.lean` for the mechanized distributivity identity underlying this expansion, given in choice-function form (which needs the Axiom of Choice in general).
