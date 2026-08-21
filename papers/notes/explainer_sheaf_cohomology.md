# A CS Guide to Sheaf Cohomology

If you have a BS/MS in Computer Science, you're already familiar with the core intuition behind Sheaf Cohomology, even if the math terminology sounds alien. You likely know it under names like **distributed consensus**, **circular dependencies**, or **satisfiability**.

Here is the translation from abstract topology to computer science.

## 1. What is a Sheaf? (It's a Distributed Data Structure)
Imagine a graph (or a network of sensors). 
* A **Sheaf** is simply an assignment of *data spaces* to every node and edge in that graph. 
* It also includes **Restriction Maps**, which are just functions (or type-casts) that tell you how to compare the data at Node A with the data at Edge A-B.

**CS Analogy**: Think of a sheaf as a distributed database. Each node is a shard that holds local beliefs about the world. The edges are the network links. The restriction maps are the protocols that check if Node A's belief matches Node B's belief when they talk over the edge.

## 2. What is a Global Section? (It's Global Consistency)
If every node in the graph holds a piece of data, and *every single edge check passes* (Node A agrees with Node B, B agrees with C, etc.), you have a **Global Section**.

**CS Analogy**: A global section is a globally consistent state. It means your distributed database has reached consensus. In our frame coreference problem, a global section is a perfect, contradiction-free clustering of all frames across all documents.

## 3. What is Cohomology? (It's the Debugger)
Often, you can't reach a globally consistent state. But *why*? 
**Cohomology** is a mathematical tool that detects and measures *obstructions* to global consistency.

We care specifically about the first cohomology group, denoted **$H^1$**.
* If **$H^1 = 0$**, your system is perfectly fine. Any locally consistent data can be stitched together into a global section.
* If **$H^1 \neq 0$**, you have a **Cohomological Obstruction**. 

**Caveat.** The "$H^1=0 \Rightarrow$ stitchable" statement is true for **sheaves of abelian groups** relative to a fixed cover. For **set-valued** data (no group structure) the right statement is contextuality-style: overlap-compatible local families may still fail to extend to a global section, with no $H^1$ available to blame. When the coefficients happen to be abelian, that failure-to-glue *is* classified by $H^1$; otherwise it is just "no global section," an $H^0$-level fact, not a cohomology class.

### The CS Translation of $H^1 \neq 0$: The Unresolvable Cycle
An obstruction in $H^1$ means you have a situation where locally, everything seems fine, but globally, there is a paradox. 

Imagine three documents (nodes A, B, C):
1. A and B agree: $f_1 = f_2$
2. B and C agree: $f_2 = f_3$
3. C and A agree: $f_3 \neq f_1$ (Discourse contradiction)

If you look at any two nodes, you can resolve them. But if you walk the cycle $A \rightarrow B \rightarrow C \rightarrow A$, you get a logical contradiction. 

In computer science, this is a **circular dependency** or an unsolvable Constraint Satisfaction Problem (CSP). This particular example is detectable by plain union-find plus one negative-edge check — it is an *analogy* for contextuality, not itself a non-trivial cohomology class absent abelian coefficients. A topologist working with abelian coefficients would say, *"Ah, the local sections cannot be extended to a global section because there is a non-trivial cohomology class in $H^1$"* — but for set-valued data like this one, the honest statement is just that no global section exists.

## Summary for the Engineer
* **Sheaf**: The data structure tracking local beliefs (documents) and the rules for comparing them (coreference links).
* **Global Section**: A valid, contradiction-free merge of all documents.
* **Detecting the clash**: The check that finds contradictions preventing a clean merge is *not* sheaf cohomology. For set-valued data like this, $H^1$ is not available at all (it needs abelian coefficients), and the worked example above is decided by union-find plus one negative-edge check. The honest summary: **no global section exists** — an $H^0$-level statement. "Sheaf cohomology" is the analogy, not the algorithm.
