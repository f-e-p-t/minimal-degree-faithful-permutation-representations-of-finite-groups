# minimal-degree-faithful-permutation-representations-of-finite-groups

## Overview
An investigation of the minimal faithful permutation degree function $\mu$. The paper collects and explains new results, as well as established ones from the existing literature, reimagining certain proofs. The paper also discusses the results of an algorithmic implementation of a constructive proof by John Cossey (reference 13), the GAP code for which is found in /cossey-proof-implementation.

## Summary and Key Results
For a finite group $G$, $\mu(G)$ is the smallest positive integer $n$ such that $G$ admits a faithful permutation representation of degree $n$. In other words, $n$ is minimal such that the symmetric group $\text{Sym}(n)$ contains a subgroup isomorphic to $G$. A helpful pre-reading exercise is to find $\mu(\mathbb{Z}/6\mathbb{Z})$.
The paper discusses direct products and the general solution when $\mu$ is applied to any finite abelian group. It explores applying $\mu$ to simple groups and the ratio between $|G|$ and $\mu(G)$, called the *compression ratio*. The paper's final section discusses quotient groups and an optimised algorithm inspired by Cossey's proof.

## Code
GAP must be installed to run the program. Once in the GAP terminal, run the program as usual:
gap> Read(path-to-repo/cossey-proof-implementation/algorithm.g);
