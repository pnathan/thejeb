# Annotated Bibliography: Frame Coreference and Underspecification

This document catalogs the state-of-the-art scientific references regarding cross-document frame/event coreference and semantic underspecification, directly supporting the STE topological algebra framework.

## 1. Semantic Underspecification (Computing with "Holes")
The NLP and Computational Semantics communities explicitly advocate for maintaining "holes" (underspecified sets of plausible candidates) rather than forcing early disambiguation.

*   **Pinkal, M. (1999). "On Semantic Underspecification."** 
    *Relevance:* The foundational mathematical text defining semantic underspecification as a formal structure where ambiguity is preserved in the logic until context resolves it.
*   **Wildenburg, et al. (2024). "Do Pre-trained Language Models Detect and Understand Semantic Underspecification? Ask the DUST!"** *Findings of the Association for Computational Linguistics (ACL) 2024.*
    *Relevance:* Recent work finding that models largely struggle to *detect* underspecification in the first place — a weaker and more specific claim than "fail to maintain" underspecified states.
*   **Schlangen, D. (2023). "Dealing with Semantic Underspecification in Multimodal NLP."** *ACL 2023.*
    *Relevance:* A major position paper arguing that modern NLP pipelines must compute over underspecified representations rather than forcing brittle, deterministic extractions.

## 2. Cross-Document Event/Frame Coreference (Graph Clustering)
When moving from single documents to multidocument merge, the state of the art relies heavily on graph structures and agglomerative clustering (the probabilistic cousin to our STE intersections).

*   **Cattan, A., et al. (2021). "Cross-document Coreference Resolution over Predicted Mentions."** *Findings of ACL.*
    *Relevance:* Demonstrates the current standard architecture: extracting mentions (frames) and using graph-based agglomerative clustering to resolve transitive closures across multiple documents.
*   **Barhom, S., et al. (2019). "Revisiting Joint Modeling of Cross-document Entity and Event Coreference Resolution."** *Proceedings of the 57th Annual Meeting of the ACL.*
    *Relevance:* Proves that "discourse awareness" (specifically the mutual dependence of entity coreference and frame/event coreference) strictly constrains the graph clusters.
*   **Kenyon-Dean, K., et al. (2018). "Resolving Event Coreference with Supervised Representation Learning and Clustering-Oriented Regularization."** *\*SEM 2018.*
    *Relevance:* Details the exact mathematical mechanisms used by the NLP community to force extracted frames into globally consistent coreference clusters.

## 3. Frame-Semantic Parsing & Extraction Limitations
*   **Das, D., et al. (2014). "Frame-Semantic Parsing."** *Computational Linguistics, 40(1), 9-56.*
    *Relevance:* The definitive reference for FrameNet extraction systems. It highlights the inherent ambiguity in trigger identification, fundamentally justifying why extractions must be treated as simplices (hyperopinions) rather than exact vertices.
