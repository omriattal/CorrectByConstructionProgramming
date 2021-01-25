# CorrectByConstructionProgramming
**This is an advanced course teaching how to design algorithms and programs that are guaranteed to meet their specification.** Starting with a mathematical description of the program's requirements, the course presents a formal method for turning such specifications into actual code, in a stepwise approach known as refinement. Techniques of algorithm refinement are presented, for the derivation of loops and recursive procedures from invariants. The developed algorithms are typically very short, but challenging, as we aim to construct correct and efficient code. The taught material is mainly based on the textbook "Programming from Specifications" by Carroll Morgan.

The programming throughout this course is done using a development environment that enables the annotation of programs with their specifications. The environment includes an automatic verifier, such that the functional correctness of a program (with respect to its specification) can be established ahead of the generation of an executable file. At the end of the course students are expected to be able to construct correct 
programs. More concretely, you will be able to:
- Specify program requirements abstractly.
- Perform rigorous and formal derivations of efficient programs from their abstract specifications.
- Understand the criteria for algorithm refinement.

The following topics will be covered, along with a range of examples and case
studies:
1. Program specification using predicates and assertions: predicate notation, preconditions and postconditions, specification statements.
2. A language based on guarded commands (featuring an assignment statement, sequential composition and conditional statements, blocks, local variables, and arrays) with proof rules for each program construct.
3. Basic techniques for finding invariants.
4. Constructed types: from sets, bags, and lists to functions and relations.
5. Procedures, parameter passing, and reuse.
6. Recursive procedures: rigorous derivation of sorting and search algorithms.
7. Recursive types: linked lists and binary trees.

This repository includes the assignment of the course written in Dafny (Microsoft research language).
