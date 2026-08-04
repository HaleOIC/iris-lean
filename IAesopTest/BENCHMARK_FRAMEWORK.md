## A Triangular Resource-Allocation Benchmark Family

We propose a synthetic benchmark based on a triangular family of resource-allocation problems.

Given spatial resources $R_0,\ldots,R_{n-1}$ and target propositions $T_0,\ldots,T_{n-1}$, the canonical rules are:

$$
R_i \vdash T_i
\qquad\text{for } 0 \leq i < n.
$$

In addition, the benchmark may contain decoy rules of the form:

$$
R_j \vdash T_i
\qquad\text{where } j > i.
$$

The generated proof obligation is:

$$
R_0 * \cdots * R_{n-1}
\vdash
T_0 * \cdots * T_{n-1}.
$$

This family has two useful properties:

1. Every generated instance is provable: the canonical assignment maps each resource $R_i$ to its corresponding target $T_i$.
2. The canonical assignment is the unique complete resource assignment.

The second property follows by backward induction:

- The final target $T_{n-1}$ can only be proved using $R_{n-1}$, since no decoy rule can target $T_{n-1}$.
- Once $R_{n-1}$ has been consumed, $T_{n-2}$ can only use $R_{n-2}$.
- The same argument applies inductively to all preceding targets.

Nevertheless, earlier targets may admit many locally applicable decoy rules:

$$
R_{i+1},\ldots,R_{n-1} \vdash T_i.
$$

Choosing one of these rules produces a locally valid proof but consumes a resource required by a later, more constrained target. Such a choice therefore cannot participate in a complete proof and must eventually be reconsidered.

By varying the number and presentation order of the decoy rules, the benchmark provides a controlled way to measure how robustly proof search handles competing spatial-resource assignments without changing the provability or unique global solution of the generated obligation.
